//! Owned phase cancellation, separate from the external run interruption token.

use std::sync::atomic::Ordering;
use std::sync::{Arc, Mutex};

use tokio::task::JoinHandle;
use tokio::time::Instant;

use super::CancellationToken;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PhaseStop {
    Interrupted,
    DeadlineExpired,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct PhaseCompletion {
    pub(crate) completed_at: Instant,
    pub(crate) stop: Option<PhaseStop>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct InvalidExternalRoot;

#[derive(Debug)]
struct PhaseState {
    external: CancellationToken,
    child: CancellationToken,
    completed: Mutex<Option<PhaseCompletion>>,
}

impl PhaseState {
    fn deadline(&self) -> Option<Instant> {
        *self
            .child
            .state
            .absolute_deadline
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
    }

    // Classify using the actual signal times, never the relay's scheduling time
    // or a phase token's Boolean. Equal times belong to the deadline, matching
    // CancellationToken::cancelled_before.
    fn cause_at(&self, observed_at: Instant) -> Option<(PhaseStop, Instant)> {
        let external_at = *self
            .external
            .state
            .first_cancelled_at
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let deadline = self.deadline();
        match (external_at.filter(|at| *at <= observed_at), deadline) {
            (Some(at), Some(deadline)) if at >= deadline && deadline <= observed_at => {
                Some((PhaseStop::DeadlineExpired, deadline))
            }
            (Some(at), _) => Some((PhaseStop::Interrupted, at)),
            (None, Some(deadline)) if deadline <= observed_at => {
                Some((PhaseStop::DeadlineExpired, deadline))
            }
            _ => None,
        }
    }

    fn signal_if_stopped(&self) -> Option<PhaseStop> {
        let completed = self
            .completed
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        if let Some(completed) = *completed {
            return completed.stop;
        }
        let (cause, at) = self.cause_at(Instant::now())?;
        self.child.cancel_at(at);
        Some(cause)
    }
}

/// An owner must finish and join this relay at its phase boundary, before
/// cleanup or untimed publication can change the observed outcome.
///
/// Search may bind the child's deadline later, at its existing constructor.
/// The relay notices that binding and actively signals expiry so subprocess
/// waits on `cancelled()` wake even though generic token behavior is unchanged.
#[derive(Debug)]
pub(crate) struct PhaseCancellation {
    state: Arc<PhaseState>,
    finish_signal: CancellationToken,
    relay: Option<JoinHandle<()>>,
}

impl PhaseCancellation {
    pub(crate) fn new(external: &CancellationToken) -> Result<Self, InvalidExternalRoot> {
        {
            let _role_guard = external
                .state
                .wait_lock
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner());
            if external.state.linked_phase_child.load(Ordering::Acquire)
                || external
                    .state
                    .absolute_deadline
                    .lock()
                    .unwrap_or_else(|poisoned| poisoned.into_inner())
                    .is_some()
            {
                return Err(InvalidExternalRoot);
            }
            // Claims and later deadline bindings serialize through wait_lock.
            // Every clone now denotes the same permanently deadline-free root.
            external
                .state
                .external_phase_root
                .store(true, Ordering::Release);
        }
        let child = CancellationToken::new();
        child
            .state
            .linked_phase_child
            .store(true, Ordering::Release);
        let state = Arc::new(PhaseState {
            external: external.clone(),
            child,
            completed: Mutex::new(None),
        });
        let finish_signal = CancellationToken::new();
        let relay_state = Arc::clone(&state);
        let relay_finish = finish_signal.clone();
        let relay = tokio::spawn(async move {
            loop {
                // Register before inspecting the deadline: binding between the
                // inspection and the select cannot lose its notification.
                let changed = relay_state.child.state.async_waiters.notified();
                tokio::pin!(changed);
                changed.as_mut().enable();
                if relay_finish.is_cancelled() || relay_state.signal_if_stopped().is_some() {
                    return;
                }
                let deadline = relay_state.deadline();
                let expiry = async move {
                    match deadline {
                        Some(deadline) => tokio::time::sleep_until(deadline).await,
                        None => std::future::pending::<()>().await,
                    }
                };
                tokio::select! {
                    biased;
                    _ = relay_finish.cancelled() => return,
                    _ = relay_state.external.cancelled() => {},
                    _ = expiry => {},
                    _ = changed => {},
                }
            }
        });
        Ok(Self {
            state,
            finish_signal,
            relay: Some(relay),
        })
    }

    pub(crate) fn token(&self) -> &CancellationToken {
        &self.state.child
    }

    pub(crate) fn stop_reason(&self) -> Option<PhaseStop> {
        self.state.signal_if_stopped()
    }

    /// Record the end boundary and latch the outcome before relay shutdown.
    /// The caller owns the start boundary, which can follow worker admission;
    /// constructing a cancellation link does not start the search clock.
    /// A passed audit calls this immediately; final publication stays outside
    /// the allowance. Failure paths call it before resource cleanup as well.
    pub(crate) async fn finish(mut self) -> Result<PhaseCompletion, tokio::task::JoinError> {
        let observed_at = Instant::now();
        let completion = {
            let mut completed = self
                .state
                .completed
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner());
            let cause = self.state.cause_at(observed_at);
            if let Some((_, at)) = cause {
                self.state.child.cancel_at(at);
            }
            let completion = PhaseCompletion {
                completed_at: observed_at,
                stop: cause.map(|(cause, _)| cause),
            };
            *completed = Some(completion);
            completion
        };
        self.finish_signal.cancel();
        if let Some(relay) = self.relay.as_mut() {
            // Keep abort ownership in self if this finish future is cancelled.
            // The relay does not run caller code and recovers poisoned locks;
            // finish owns and joins it on both successful and failed phases.
            relay.await?;
        }
        self.relay.take();
        Ok(completion)
    }
}

impl Drop for PhaseCancellation {
    fn drop(&mut self) {
        self.finish_signal.cancel();
        if let Some(relay) = self.relay.take() {
            // Unwinding/runtime shutdown cannot await. Ordinary exits must use
            // finish; dropping a phase cannot leave an active detached relay.
            relay.abort();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    async fn observe_cancelled(token: &CancellationToken) {
        tokio::time::timeout(Duration::from_secs(3), token.cancelled())
            .await
            .expect("phase relay did not signal cancellation");
    }

    #[tokio::test]
    async fn expired_search_does_not_cancel_certification_or_external_root() {
        let external = CancellationToken::new();
        let search = PhaseCancellation::new(&external).unwrap();
        let certification = PhaseCancellation::new(&external).unwrap();
        assert!(!search.token().shares_state_with(certification.token()));
        assert!(!search.token().shares_state_with(&external));
        let deadline = Instant::now() - Duration::from_secs(1);
        assert!(search.token().bind_absolute_deadline(deadline));
        observe_cancelled(search.token()).await;
        assert_eq!(search.stop_reason(), Some(PhaseStop::DeadlineExpired));
        assert!(!certification.token().should_stop());
        assert!(!external.should_stop());
        assert_eq!(
            search.finish().await.unwrap().stop,
            Some(PhaseStop::DeadlineExpired)
        );
        assert_eq!(certification.finish().await.unwrap().stop, None);
    }

    #[tokio::test]
    async fn already_signalled_search_still_allows_new_certification() {
        let external = CancellationToken::new();
        let search = PhaseCancellation::new(&external).unwrap();
        let deadline = Instant::now() - Duration::from_secs(1);
        assert!(search.token().bind_absolute_deadline(deadline));
        search.token().cancel_for_deadline(deadline);
        let certification = PhaseCancellation::new(&external).unwrap();
        assert!(!certification.token().should_stop());
        external.cancel();
        observe_cancelled(certification.token()).await;
        assert_eq!(certification.stop_reason(), Some(PhaseStop::Interrupted));
        assert_eq!(
            certification.finish().await.unwrap().stop,
            Some(PhaseStop::Interrupted)
        );
        assert_eq!(
            search.finish().await.unwrap().stop,
            Some(PhaseStop::DeadlineExpired)
        );
    }

    #[tokio::test]
    async fn preexisting_external_cancellation_reaches_new_phase() {
        let external = CancellationToken::new();
        external.cancel();
        let phase = PhaseCancellation::new(&external).unwrap();
        observe_cancelled(phase.token()).await;
        assert_eq!(
            phase.finish().await.unwrap().stop,
            Some(PhaseStop::Interrupted)
        );
    }

    #[tokio::test]
    async fn delayed_relay_preserves_external_signal_before_deadline() {
        let external = CancellationToken::new();
        let phase = PhaseCancellation::new(&external).unwrap();
        let deadline = Instant::now() - Duration::from_secs(1);
        assert!(phase.token().bind_absolute_deadline(deadline));
        external.cancel_at(deadline - Duration::from_millis(1));
        assert_eq!(phase.stop_reason(), Some(PhaseStop::Interrupted));
        assert!(phase.token().cancelled_before(deadline));
        assert_eq!(
            phase.finish().await.unwrap().stop,
            Some(PhaseStop::Interrupted)
        );
    }

    #[tokio::test]
    async fn external_signal_after_deadline_does_not_relabel_expiry() {
        let external = CancellationToken::new();
        let phase = PhaseCancellation::new(&external).unwrap();
        let deadline = Instant::now() - Duration::from_secs(1);
        assert!(phase.token().bind_absolute_deadline(deadline));
        external.cancel();
        assert_eq!(phase.stop_reason(), Some(PhaseStop::DeadlineExpired));
        assert_eq!(
            phase.finish().await.unwrap().stop,
            Some(PhaseStop::DeadlineExpired)
        );
    }

    #[tokio::test]
    async fn late_deadline_binding_actively_wakes_subprocess_waiters() {
        let external = CancellationToken::new();
        let phase = PhaseCancellation::new(&external).unwrap();
        // Let the relay first register while there is no deadline.
        tokio::task::yield_now().await;
        let deadline = Instant::now() + Duration::from_millis(20);
        assert!(phase.token().bind_absolute_deadline(deadline));
        assert_eq!(phase.state.deadline(), Some(deadline));
        observe_cancelled(phase.token()).await;
        assert_eq!(
            phase.finish().await.unwrap().stop,
            Some(PhaseStop::DeadlineExpired)
        );
    }

    #[tokio::test]
    async fn finishing_audit_disarms_deadline_before_publication() {
        let external = CancellationToken::new();
        let phase = PhaseCancellation::new(&external).unwrap();
        let child = phase.token().clone();
        let deadline = Instant::now() + Duration::from_secs(1);
        assert!(child.bind_absolute_deadline(deadline));
        let relay_state = Arc::downgrade(&phase.state);
        let completed = phase.finish().await.unwrap();
        assert_eq!(completed.stop, None);
        assert!(
            relay_state.upgrade().is_none(),
            "finish did not join its relay"
        );
        external.cancel();
        tokio::task::yield_now().await;
        assert!(!child.is_cancelled());
        assert_eq!(completed.stop, None);
        // The child's immutable deadline remains valid. Publication must not
        // consult it after the owner's successful audit completion boundary.
    }

    #[tokio::test]
    async fn dropping_pending_finish_retains_abort_ownership() {
        use std::sync::atomic::{AtomicBool, Ordering};
        struct MarkDrop(Arc<AtomicBool>);
        impl Drop for MarkDrop {
            fn drop(&mut self) {
                self.0.store(true, Ordering::Release);
            }
        }
        let external = CancellationToken::new();
        let mut phase = PhaseCancellation::new(&external).unwrap();
        let dropped = Arc::new(AtomicBool::new(false));
        let marker = Arc::clone(&dropped);
        let (ready_tx, ready_rx) = tokio::sync::oneshot::channel();
        let stalled = tokio::spawn(async move {
            let _guard = MarkDrop(marker);
            let _ = ready_tx.send(());
            std::future::pending::<()>().await;
        });
        let original = phase.relay.replace(stalled).unwrap();
        original.abort();
        let _ = original.await;
        ready_rx.await.unwrap();
        let mut finishing = Box::pin(phase.finish());
        std::future::poll_fn(|cx| {
            assert!(matches!(
                std::future::Future::poll(finishing.as_mut(), cx),
                std::task::Poll::Pending
            ));
            std::task::Poll::Ready(())
        })
        .await;
        drop(finishing);
        tokio::time::timeout(Duration::from_secs(3), async {
            while !dropped.load(Ordering::Acquire) {
                tokio::task::yield_now().await;
            }
        })
        .await
        .expect("dropping finish detached its relay");
    }

    #[tokio::test]
    async fn unexpected_relay_failure_cannot_silently_pass_audit() {
        let external = CancellationToken::new();
        let phase = PhaseCancellation::new(&external).unwrap();
        phase.relay.as_ref().unwrap().abort();
        assert!(phase.finish().await.is_err());
    }

    #[tokio::test]
    async fn unbound_phase_children_cannot_masquerade_as_external_roots() {
        let external = CancellationToken::new();
        let search = PhaseCancellation::new(&external).unwrap();
        assert!(matches!(
            PhaseCancellation::new(search.token()),
            Err(InvalidExternalRoot)
        ));
        search.finish().await.unwrap();
    }

    #[tokio::test]
    async fn claiming_external_root_pins_no_deadline_for_every_clone() {
        let external = CancellationToken::new();
        let alias = external.clone();
        let phase = PhaseCancellation::new(&external).unwrap();
        assert!(!alias.bind_absolute_deadline(Instant::now()));
        phase.finish().await.unwrap();
        assert!(!external.bind_absolute_deadline(Instant::now()));
        let certification = PhaseCancellation::new(&alias).unwrap();
        alias.cancel();
        observe_cancelled(certification.token()).await;
        assert_eq!(
            certification.finish().await.unwrap().stop,
            Some(PhaseStop::Interrupted)
        );
    }

    #[tokio::test]
    async fn an_already_bound_token_is_refused_as_external_root() {
        let phase_token = CancellationToken::new();
        assert!(phase_token.bind_absolute_deadline(Instant::now()));
        assert!(matches!(
            PhaseCancellation::new(&phase_token),
            Err(InvalidExternalRoot)
        ));
    }
}
