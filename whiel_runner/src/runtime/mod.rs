//! Shared cancellation, admission, and cooperative entry-wrapper mechanics.
//!
//! Arbitrary process-tree termination belongs to the Vampire runtime. This
//! module supplies run-scoped admission and cooperative in-process control.

use std::any::Any;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Condvar, Mutex, mpsc};
use std::thread;
use std::time::Duration;

use crate::artifact::{ArtifactBackendOwner, ArtifactStore};
use crate::failure::FailureReport;

mod admission;
mod cpu_job;
pub mod interrupt;
pub(crate) mod owned_path;
pub(crate) mod phase;
#[cfg(any(target_os = "macos", target_os = "linux"))]
pub(crate) mod process_tree;

pub(crate) use admission::SolverPermit;
pub(crate) use cpu_job::{CpuJobError, RetainedCpuJobs};

// ------------------------------------------------------------
// Cooperative Cancellation
// ------------------------------------------------------------
pub use admission::{
    AdmissionError, CpuWorkerPermit, ResourcePolicyError, RuntimeResourcePolicy, SolverAdmission,
    SolverAdmissionClass, create_general_solver_admission, create_symbolic_solver_admissions,
};

#[derive(Clone, Debug)]
pub struct CancellationToken {
    state: Arc<CancellationState>,
}

#[derive(Debug)]
struct CancellationState {
    cancelled: AtomicBool,
    // Set by every cancellation which closes the run's side-effect window,
    // and left clear by a cooperative scope-local stop. Side-effect
    // boundaries need that distinction: a run stop must fail closed, while
    // a scope owner stopping its own peers is ordinary control flow.
    run_stopped: AtomicBool,
    // Set only by the explicit linked-phase helper. Ordinary tokens retain
    // their existing behavior until assigned a phase or external-root role.
    external_phase_root: AtomicBool,
    linked_phase_child: AtomicBool,
    first_cancelled_at: Mutex<Option<tokio::time::Instant>>,
    absolute_deadline: Mutex<Option<tokio::time::Instant>>,
    wait_lock: Mutex<()>,
    wait_condition: Condvar,
    async_waiters: tokio::sync::Notify,
}

impl CancellationToken {
    pub fn new() -> Self {
        Self {
            state: Arc::new(CancellationState {
                cancelled: AtomicBool::new(false),
                run_stopped: AtomicBool::new(false),
                external_phase_root: AtomicBool::new(false),
                linked_phase_child: AtomicBool::new(false),
                first_cancelled_at: Mutex::new(None),
                absolute_deadline: Mutex::new(None),
                wait_lock: Mutex::new(()),
                wait_condition: Condvar::new(),
                async_waiters: tokio::sync::Notify::new(),
            }),
        }
    }

    pub fn cancel(&self) {
        self.cancel_at(tokio::time::Instant::now());
    }

    /// Stop this scope's in-flight work as ordinary control flow, leaving the
    /// run's side-effect window open.
    ///
    /// Only the owner of a scope-local token may call this, once its own
    /// linearization point has selected a result: work which observes the
    /// stop has merely lost that race, so a side-effect boundary may discard
    /// a late result instead of failing closed. Every other cancellation
    /// keeps its run-stop meaning, and cooperativeness never propagates —
    /// [`Self::cancel_from`] marks its receiver run-stopped like any relay.
    pub(crate) fn cancel_cooperatively(&self) {
        self.stop_at(tokio::time::Instant::now(), false);
    }

    /// Exercise a cooperative stop from an integration test, which cannot
    /// own a scope-local token of its own.
    #[cfg(feature = "test-hooks")]
    #[doc(hidden)]
    pub fn cancel_cooperatively_for_tests(&self) {
        self.cancel_cooperatively();
    }

    fn cancel_at(&self, cancelled_at: tokio::time::Instant) {
        self.stop_at(cancelled_at, true);
    }

    fn stop_at(&self, cancelled_at: tokio::time::Instant, stops_run: bool) {
        let _guard = self
            .state
            .wait_lock
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let mut first_cancelled_at = self
            .state
            .first_cancelled_at
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        if first_cancelled_at.is_none_or(|current| cancelled_at < current) {
            *first_cancelled_at = Some(cancelled_at);
        }
        // Publish the run stop before the cancellation it accompanies, so an
        // observer of the cancellation never reads a stale open window. That
        // pairing binds the reader too: a boundary must sample the
        // cancellation first and the window second.
        if stops_run {
            self.state.run_stopped.store(true, Ordering::Release);
        }
        if !self.state.cancelled.swap(true, Ordering::AcqRel) {
            self.state.wait_condition.notify_all();
            self.state.async_waiters.notify_waiters();
        }
    }

    pub fn is_cancelled(&self) -> bool {
        self.state.cancelled.load(Ordering::Acquire)
    }

    /// Bind one immutable wall-clock deadline to every clone of this token.
    ///
    /// This is crate-private because only the run owner may establish the
    /// absolute deadline. Side-effect boundaries use [`Self::should_stop`] to
    /// observe expiry even after monopolizing one async poll, while ordinary
    /// cancellation checks retain their external-cancellation semantics.
    pub(crate) fn bind_absolute_deadline(&self, deadline: tokio::time::Instant) -> bool {
        let _wait_guard = self
            .state
            .wait_lock
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        // Claiming a token as the external root permanently pins the absence
        // of a deadline. This shares the wait lock with the role claim.
        if self.state.external_phase_root.load(Ordering::Acquire) {
            return false;
        }
        let mut current = self
            .state
            .absolute_deadline
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let matches = match *current {
            Some(current) => current == deadline,
            None => {
                *current = Some(deadline);
                true
            }
        };
        drop(current);
        if matches {
            self.state.wait_condition.notify_all();
            self.state.async_waiters.notify_waiters();
        }
        matches
    }

    /// Whether the run owner's separately classified absolute deadline passed.
    pub(crate) fn deadline_elapsed(&self) -> bool {
        self.state
            .absolute_deadline
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .is_some_and(|deadline| tokio::time::Instant::now() >= deadline)
    }

    /// Signal the owner's absolute deadline at its exact clock boundary.
    ///
    /// Recording the boundary rather than the delayed poll time lets outcome
    /// arbitration preserve an external cancellation which happened strictly
    /// before the deadline, even when cleanup finishes after it.
    pub(crate) fn cancel_for_deadline(&self, deadline: tokio::time::Instant) {
        self.cancel_at(deadline);
    }

    /// Forward the owner's cancellation instant, not the delayed observer time.
    /// The receiving request keeps its own already-bound (possibly earlier)
    /// deadline; an unbound child inherits the owner's immutable deadline.
    pub(crate) fn cancel_from(&self, owner: &Self) {
        let deadline = *owner
            .state
            .absolute_deadline
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let cancelled_at = *owner
            .state
            .first_cancelled_at
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        if let Some(deadline) = deadline {
            let _ = self.bind_absolute_deadline(deadline);
        }
        self.cancel_at(cancelled_at.unwrap_or_else(tokio::time::Instant::now));
    }

    /// Classify a recorded cancellation by the owner's clock boundary. This
    /// deliberately ignores the current clock, so slow cleanup cannot turn an
    /// earlier external cancellation into a timeout.
    pub(crate) fn cancelled_at_or_after_deadline(&self) -> bool {
        let deadline = *self
            .state
            .absolute_deadline
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let cancelled_at = *self
            .state
            .first_cancelled_at
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        matches!((deadline, cancelled_at), (Some(deadline), Some(at)) if at >= deadline)
    }

    /// Whether the first observed cancellation preceded `deadline`.
    pub(crate) fn cancelled_before(&self, deadline: tokio::time::Instant) -> bool {
        self.state
            .first_cancelled_at
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .is_some_and(|cancelled_at| cancelled_at < deadline)
    }

    /// Close a side-effect boundary on cancellation or absolute expiry.
    ///
    /// The caller which owns outcome classification still compares its exact
    /// clock and distinguishes `OverallTimeout` from external interruption.
    pub(crate) fn should_stop(&self) -> bool {
        self.is_cancelled() || self.deadline_elapsed()
    }

    /// Whether a side-effect boundary must fail closed rather than discard a
    /// late result: the run itself stopped, or its absolute deadline passed.
    ///
    /// This is the strict part of [`Self::should_stop`]. A cooperative
    /// scope-local stop closes no window, so a boundary observing only that
    /// reports the cancellation its caller already handles.
    ///
    /// A boundary which consults both flags reads [`Self::is_cancelled`]
    /// first and this second. The writer publishes the stop before the
    /// cancellation, so only that order can tell the two apart.
    pub(crate) fn publication_closed(&self) -> bool {
        self.state.run_stopped.load(Ordering::Acquire) || self.deadline_elapsed()
    }

    /// Whether two handles control the same run-scoped cancellation state.
    pub(crate) fn shares_state_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.state, &other.state)
    }

    /// Block until cancellation without polling.
    pub fn wait_cancelled(&self) {
        if self.is_cancelled() {
            return;
        }
        let mut guard = self
            .state
            .wait_lock
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        while !self.is_cancelled() {
            guard = self
                .state
                .wait_condition
                .wait(guard)
                .unwrap_or_else(|poisoned| poisoned.into_inner());
        }
    }

    /// Await cancellation without blocking an async orchestration thread.
    pub async fn cancelled(&self) {
        loop {
            let notified = self.state.async_waiters.notified();
            tokio::pin!(notified);
            notified.as_mut().enable();
            if self.is_cancelled() {
                return;
            }
            notified.await;
        }
    }
}

impl Default for CancellationToken {
    fn default() -> Self {
        Self::new()
    }
}

// ------------------------------------------------------------
// Phase 1C Timed Child Harness
// ------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChildPanic {
    detail: String,
}

impl ChildPanic {
    pub fn detail(&self) -> &str {
        &self.detail
    }
}

#[derive(Debug)]
pub enum TimedChildOutcome<T> {
    Completed(T),
    TimedOut,
    Panicked(ChildPanic),
}

#[derive(Debug)]
pub struct TimedChildRun<T> {
    pub outcome: TimedChildOutcome<T>,
    pub settlement: Result<(), FailureReport>,
}

/// Run cooperative child work, join it, and only then settle artifacts.
///
/// A child which ignores cancellation can delay this function beyond the
/// requested limit. Phase 2 owns forceful subprocess-tree cleanup.
pub fn run_timed_child<T, F>(
    owner: ArtifactBackendOwner,
    limit: Duration,
    child: F,
) -> TimedChildRun<T>
where
    T: Send + 'static,
    F: FnOnce(CancellationToken, ArtifactStore) -> T + Send + 'static,
{
    let child_artifacts = owner.root_store();
    let cancellation = CancellationToken::new();
    let child_cancellation = cancellation.clone();
    let (done_sender, done_receiver) = mpsc::sync_channel(1);
    let handle = thread::spawn(move || {
        let value = child(child_cancellation, child_artifacts);
        let _ = done_sender.send(());
        value
    });

    let timed_out = match done_receiver.recv_timeout(limit) {
        Ok(()) => false,
        Err(mpsc::RecvTimeoutError::Timeout) => {
            cancellation.cancel();
            true
        }
        Err(mpsc::RecvTimeoutError::Disconnected) => false,
    };

    let joined = handle.join();
    let outcome = if timed_out {
        TimedChildOutcome::TimedOut
    } else {
        match joined {
            Ok(value) => TimedChildOutcome::Completed(value),
            Err(payload) => TimedChildOutcome::Panicked(ChildPanic {
                detail: panic_detail(payload),
            }),
        }
    };
    let settlement = owner.settle();
    TimedChildRun {
        outcome,
        settlement,
    }
}

fn panic_detail(payload: Box<dyn Any + Send>) -> String {
    if let Some(message) = payload.downcast_ref::<&str>() {
        (*message).to_string()
    } else if let Some(message) = payload.downcast_ref::<String>() {
        message.clone()
    } else {
        "child panicked with a non-string payload".to_string()
    }
}

// ------------------------------------------------------------
// Tests
// ------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Barrier;

    #[test]
    fn cancellation_is_idempotent() {
        let token = CancellationToken::new();
        assert!(!token.is_cancelled());
        token.cancel();
        token.cancel();
        assert!(token.is_cancelled());
        token.wait_cancelled();
    }

    #[test]
    fn cancellation_has_no_lost_wakeup() {
        for _ in 0..1000 {
            let token = CancellationToken::new();
            let waiter = token.clone();
            let barrier = Arc::new(Barrier::new(2));
            let child_barrier = Arc::clone(&barrier);
            let handle = thread::spawn(move || {
                child_barrier.wait();
                waiter.wait_cancelled();
            });
            barrier.wait();
            token.cancel();
            handle.join().unwrap();
        }
    }

    #[tokio::test]
    async fn async_cancellation_has_no_lost_wakeup() {
        for _ in 0..1000 {
            let token = CancellationToken::new();
            let waiter = token.clone();
            let handle = tokio::spawn(async move { waiter.cancelled().await });
            token.cancel();
            tokio::time::timeout(Duration::from_secs(1), handle)
                .await
                .expect("async cancellation waiter lost its wakeup")
                .unwrap();
        }
    }

    #[tokio::test]
    async fn bound_deadline_closes_gate_without_relabeling_external_cancellation() {
        let token = CancellationToken::new();
        let deadline = tokio::time::Instant::now() + Duration::from_millis(10);
        assert!(token.bind_absolute_deadline(deadline));
        assert!(token.bind_absolute_deadline(deadline));
        assert!(!token.bind_absolute_deadline(deadline + Duration::from_millis(1)));

        tokio::time::sleep_until(deadline).await;
        assert!(token.deadline_elapsed());
        assert!(token.should_stop());
        assert!(!token.is_cancelled());

        token.cancel_for_deadline(deadline);
        assert!(token.is_cancelled());
        assert!(!token.cancelled_before(deadline));
    }

    #[tokio::test]
    async fn a_cooperative_stop_leaves_the_publication_window_open() {
        let token = CancellationToken::new();
        token.cancel_cooperatively();
        assert!(token.is_cancelled());
        assert!(token.should_stop());
        assert!(!token.publication_closed());

        // A later run stop closes the window a cooperative stop left open.
        token.cancel();
        assert!(token.publication_closed());
    }

    #[tokio::test]
    async fn an_expired_deadline_closes_a_cooperatively_stopped_scope() {
        let token = CancellationToken::new();
        let deadline = tokio::time::Instant::now() + Duration::from_millis(10);
        assert!(token.bind_absolute_deadline(deadline));
        token.cancel_cooperatively();
        assert!(!token.publication_closed());

        tokio::time::sleep_until(deadline).await;
        assert!(token.publication_closed());
    }

    #[tokio::test]
    async fn first_external_cancellation_time_survives_deadline_cleanup() {
        let token = CancellationToken::new();
        let deadline = tokio::time::Instant::now() + Duration::from_millis(20);
        assert!(token.bind_absolute_deadline(deadline));
        token.cancel();
        assert!(token.cancelled_before(deadline));

        tokio::time::sleep_until(deadline).await;
        token.cancel_for_deadline(deadline);
        assert!(token.cancelled_before(deadline));
    }
}
