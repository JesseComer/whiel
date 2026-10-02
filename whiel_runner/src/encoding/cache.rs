//! Cancellation-aware exact-key asynchronous memoization.

use std::collections::HashMap;
use std::future::Future;
use std::hash::Hash;
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use tokio::sync::Notify;
use tokio::task::{JoinError, JoinHandle};

use crate::runtime::CancellationToken;

#[derive(Clone)]
pub(crate) struct AsyncMemo<K, V, E> {
    inner: Arc<MemoInner<K, V, E>>,
}

struct MemoInner<K, V, E> {
    entries: Mutex<HashMap<K, Entry<V, E>>>,
    closed: AtomicBool,
    active_fills: AtomicUsize,
    next_supervisor: AtomicU64,
    supervisors: Mutex<HashMap<u64, JoinHandle<()>>>,
    producer_failure: Mutex<Option<E>>,
    shutdown_started: AtomicBool,
    shutdown_supervisor: Mutex<Option<JoinHandle<()>>>,
    shutdown_result: Mutex<Option<Result<(), E>>>,
    shutdown_complete: AtomicBool,
    shutdown_settled: Notify,
}

enum Entry<V, E> {
    Ready(Arc<V>),
    Filling(Arc<Fill<V, E>>),
}

struct Fill<V, E> {
    state: Mutex<FillState<V, E>>,
    notify: Notify,
    cancellation: CancellationToken,
}

enum FillState<V, E> {
    Running { consumers: usize },
    Complete(Result<Arc<V>, E>),
}

struct ConsumerGuard<V, E> {
    fill: Arc<Fill<V, E>>,
    active: bool,
}

impl<K, V, E> AsyncMemo<K, V, E>
where
    K: Clone + Eq + Hash + Send + 'static,
    V: Send + Sync + 'static,
    E: Clone + Send + 'static,
{
    pub(crate) fn new() -> Self {
        Self {
            inner: Arc::new(MemoInner {
                entries: Mutex::new(HashMap::new()),
                closed: AtomicBool::new(false),
                active_fills: AtomicUsize::new(0),
                next_supervisor: AtomicU64::new(0),
                supervisors: Mutex::new(HashMap::new()),
                producer_failure: Mutex::new(None),
                shutdown_started: AtomicBool::new(false),
                shutdown_supervisor: Mutex::new(None),
                shutdown_result: Mutex::new(None),
                shutdown_complete: AtomicBool::new(false),
                shutdown_settled: Notify::new(),
            }),
        }
    }

    pub(crate) fn ready(&self, key: &K) -> Option<Arc<V>> {
        let entries = self
            .inner
            .entries
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        match entries.get(key) {
            Some(Entry::Ready(value)) => Some(Arc::clone(value)),
            _ => None,
        }
    }

    /// Publish one caller-computed exact value if the key is still vacant.
    ///
    /// This is used only to alias values already established by another
    /// context-owned memo path. It never replaces a ready or in-flight fill.
    pub(crate) fn insert_ready_if_vacant(&self, key: K, value: Arc<V>) {
        if self.inner.closed.load(Ordering::Acquire) {
            return;
        }
        let mut entries = self
            .inner
            .entries
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        if !self.inner.closed.load(Ordering::Acquire) {
            entries.entry(key).or_insert(Entry::Ready(value));
        }
    }

    pub(crate) async fn get_or_fill<F, Fut, J, S>(
        &self,
        key: K,
        waiter_cancellation: &CancellationToken,
        cancelled: E,
        producer_join_failure: J,
        sticky_producer_error: S,
        producer: F,
    ) -> Result<Arc<V>, E>
    where
        F: FnOnce(CancellationToken) -> Fut + Send + 'static,
        Fut: Future<Output = Result<V, E>> + Send + 'static,
        J: FnOnce(JoinError) -> E + Send + 'static,
        S: Fn(&E) -> bool + Send + 'static,
    {
        self.reap_finished_supervisors().await;
        let fill = {
            let mut entries = self
                .inner
                .entries
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner());
            if self.inner.closed.load(Ordering::Acquire) {
                return Err(cancelled);
            }
            match entries.get(&key) {
                Some(Entry::Ready(value)) => return Ok(Arc::clone(value)),
                Some(Entry::Filling(fill)) => {
                    add_consumer(fill);
                    Arc::clone(fill)
                }
                None => {
                    let fill = Arc::new(Fill {
                        state: Mutex::new(FillState::Running { consumers: 1 }),
                        notify: Notify::new(),
                        cancellation: CancellationToken::new(),
                    });
                    entries.insert(key.clone(), Entry::Filling(Arc::clone(&fill)));
                    self.inner.active_fills.fetch_add(1, Ordering::AcqRel);
                    self.start_fill_supervisor(
                        key,
                        Arc::clone(&fill),
                        cancelled.clone(),
                        producer_join_failure,
                        sticky_producer_error,
                        producer,
                    );
                    fill
                }
            }
        };
        let mut consumer = ConsumerGuard {
            fill: Arc::clone(&fill),
            active: true,
        };

        loop {
            let notified = fill.notify.notified();
            tokio::pin!(notified);
            notified.as_mut().enable();
            if let Some(result) = completed(&fill) {
                return result;
            }
            tokio::select! {
                biased;
                _ = waiter_cancellation.cancelled() => {
                    return match consumer.detach_and_join_last().await {
                        Some(result) => result,
                        None => Err(cancelled),
                    };
                },
                _ = &mut notified => {}
            }
        }
    }

    /// Stop new fills, cancel every active fill, and join their supervisors.
    ///
    /// A dropped waiter cannot block in `Drop`. Its guard still cancels the
    /// last-consumer fill immediately; this context-owned join point makes
    /// that supervisor structured rather than detached from run settlement.
    /// The cleanup itself runs in a retained context-owned task, so aborting
    /// the caller that starts shutdown cannot abandon the shutdown protocol.
    pub(crate) async fn shutdown(&self) -> Result<(), E> {
        self.inner.closed.store(true, Ordering::Release);
        self.start_shutdown_supervisor();

        loop {
            let notified = self.inner.shutdown_settled.notified();
            tokio::pin!(notified);
            notified.as_mut().enable();
            if self.inner.shutdown_complete.load(Ordering::Acquire) {
                self.reap_shutdown_supervisor().await;
                return self
                    .inner
                    .shutdown_result
                    .lock()
                    .unwrap_or_else(|poisoned| poisoned.into_inner())
                    .clone()
                    .expect("completed memo shutdown must retain its result");
            }
            notified.await;
        }
    }

    fn start_shutdown_supervisor(&self) {
        if self
            .inner
            .shutdown_started
            .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
            .is_err()
        {
            return;
        }

        let inner = Arc::clone(&self.inner);
        let supervisor = tokio::spawn(async move {
            let result = Self::settle_shutdown(Arc::clone(&inner)).await;
            *inner
                .shutdown_result
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner()) = Some(result);
            inner.shutdown_complete.store(true, Ordering::Release);
            inner.shutdown_settled.notify_waiters();
        });
        *self
            .inner
            .shutdown_supervisor
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner()) = Some(supervisor);
    }

    async fn settle_shutdown(inner: Arc<MemoInner<K, V, E>>) -> Result<(), E> {
        let fills = {
            let entries = inner
                .entries
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner());
            entries
                .values()
                .filter_map(|entry| match entry {
                    Entry::Ready(_) => None,
                    Entry::Filling(fill) => Some(Arc::clone(fill)),
                })
                .collect::<Vec<_>>()
        };
        for fill in fills {
            fill.cancellation.cancel();
        }
        let supervisors = {
            let mut supervisors = inner
                .supervisors
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner());
            supervisors
                .drain()
                .map(|(_, task)| task)
                .collect::<Vec<_>>()
        };
        for supervisor in supervisors {
            let _ = supervisor.await;
        }
        debug_assert_eq!(inner.active_fills.load(Ordering::Acquire), 0);
        match inner
            .producer_failure
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .clone()
        {
            Some(failure) => Err(failure),
            None => Ok(()),
        }
    }

    async fn reap_shutdown_supervisor(&self) {
        loop {
            let supervisor = {
                let mut retained = self
                    .inner
                    .shutdown_supervisor
                    .lock()
                    .unwrap_or_else(|poisoned| poisoned.into_inner());
                match retained.as_ref() {
                    Some(supervisor) if supervisor.is_finished() => retained.take(),
                    Some(_) => None,
                    None => return,
                }
            };
            if let Some(supervisor) = supervisor {
                let _ = supervisor.await;
                return;
            }
            tokio::task::yield_now().await;
        }
    }

    fn start_fill_supervisor<F, Fut, J, S>(
        &self,
        key: K,
        fill: Arc<Fill<V, E>>,
        cancelled: E,
        producer_join_failure: J,
        sticky_producer_error: S,
        producer: F,
    ) where
        F: FnOnce(CancellationToken) -> Fut + Send + 'static,
        Fut: Future<Output = Result<V, E>> + Send + 'static,
        J: FnOnce(JoinError) -> E + Send + 'static,
        S: Fn(&E) -> bool + Send + 'static,
    {
        let inner = Arc::clone(&self.inner);
        let fill_task = Arc::clone(&fill);
        let producer_cancellation = fill.cancellation.clone();
        let supervisor = tokio::spawn(async move {
            let producer_task =
                tokio::spawn(async move { producer(producer_cancellation).await.map(Arc::new) });
            let (produced, joined_failure) = match producer_task.await {
                Ok(result) => (result, None),
                Err(error) => {
                    let failure = producer_join_failure(error);
                    (Err(failure.clone()), Some(failure))
                }
            };
            let sticky_failure = joined_failure.clone().or_else(|| match &produced {
                Err(error) if sticky_producer_error(error) => Some(error.clone()),
                _ => None,
            });
            if let Some(failure) = &sticky_failure {
                let mut retained = inner
                    .producer_failure
                    .lock()
                    .unwrap_or_else(|poisoned| poisoned.into_inner());
                retained.get_or_insert_with(|| failure.clone());
            }
            let mut entries = inner
                .entries
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner());
            let mut state = fill_task
                .state
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner());
            let publish = matches!(*state, FillState::Running { consumers } if consumers > 0)
                && !fill_task.cancellation.is_cancelled();
            let result = if sticky_failure.is_some() || publish {
                produced
            } else {
                Err(cancelled)
            };
            let current_fill = matches!(
                entries.get(&key),
                Some(Entry::Filling(current)) if Arc::ptr_eq(current, &fill_task)
            );
            if current_fill {
                match &result {
                    Ok(value) => {
                        entries.insert(key, Entry::Ready(Arc::clone(value)));
                    }
                    Err(_) => {
                        entries.remove(&key);
                    }
                }
            }
            *state = FillState::Complete(result);
            drop(state);
            drop(entries);
            fill_task.notify.notify_waiters();
            inner.active_fills.fetch_sub(1, Ordering::AcqRel);
        });
        let supervisor_id = self.inner.next_supervisor.fetch_add(1, Ordering::Relaxed);
        self.inner
            .supervisors
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .insert(supervisor_id, supervisor);
    }

    async fn reap_finished_supervisors(&self) {
        let finished = {
            let mut supervisors = self
                .inner
                .supervisors
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner());
            let ids = supervisors
                .iter()
                .filter_map(|(id, task)| task.is_finished().then_some(*id))
                .collect::<Vec<_>>();
            ids.into_iter()
                .filter_map(|id| supervisors.remove(&id))
                .collect::<Vec<_>>()
        };
        for supervisor in finished {
            let _ = supervisor.await;
        }
    }
}

fn add_consumer<V, E>(fill: &Fill<V, E>) {
    let mut state = fill
        .state
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    if let FillState::Running { consumers } = &mut *state {
        *consumers += 1;
    }
}

fn completed<V, E: Clone>(fill: &Fill<V, E>) -> Option<Result<Arc<V>, E>> {
    let state = fill
        .state
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    match &*state {
        FillState::Running { .. } => None,
        FillState::Complete(result) => Some(result.clone()),
    }
}

impl<V, E> Drop for ConsumerGuard<V, E> {
    fn drop(&mut self) {
        if self.release() {
            self.fill.cancellation.cancel();
        }
    }
}

impl<V, E> ConsumerGuard<V, E> {
    fn release(&mut self) -> bool {
        if !self.active {
            return false;
        }
        self.active = false;
        {
            let mut state = self
                .fill
                .state
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner());
            match &mut *state {
                FillState::Running { consumers } => {
                    *consumers = consumers.saturating_sub(1);
                    *consumers == 0
                }
                FillState::Complete(_) => false,
            }
        }
    }

    async fn detach_and_join_last(&mut self) -> Option<Result<Arc<V>, E>>
    where
        E: Clone,
    {
        if !self.active {
            return None;
        }
        self.active = false;
        let last = {
            let mut state = self
                .fill
                .state
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner());
            match &mut *state {
                FillState::Running { consumers } => {
                    *consumers = consumers.saturating_sub(1);
                    *consumers == 0
                }
                FillState::Complete(result) => return Some(result.clone()),
            }
        };
        if !last {
            return None;
        }
        self.fill.cancellation.cancel();
        loop {
            let notified = self.fill.notify.notified();
            tokio::pin!(notified);
            notified.as_mut().enable();
            let result = {
                let state = self
                    .fill
                    .state
                    .lock()
                    .unwrap_or_else(|poisoned| poisoned.into_inner());
                match &*state {
                    FillState::Running { .. } => None,
                    FillState::Complete(result) => Some(result.clone()),
                }
            };
            if let Some(result) = result {
                return Some(result);
            }
            notified.await;
        }
    }
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::time::Duration;

    use super::*;

    fn producer_error_is_sticky(error: &&'static str) -> bool {
        *error == "producer failed"
    }

    #[tokio::test]
    async fn concurrent_misses_share_one_fill() {
        let memo = AsyncMemo::<u64, u64, &'static str>::new();
        let calls = Arc::new(AtomicUsize::new(0));
        let mut tasks = Vec::new();
        for _ in 0..8 {
            let memo = memo.clone();
            let calls = Arc::clone(&calls);
            tasks.push(tokio::spawn(async move {
                memo.get_or_fill(
                    1,
                    &CancellationToken::new(),
                    "cancelled",
                    |_| "producer failed",
                    producer_error_is_sticky,
                    move |_| async move {
                        calls.fetch_add(1, Ordering::SeqCst);
                        tokio::time::sleep(Duration::from_millis(20)).await;
                        Ok(9)
                    },
                )
                .await
                .unwrap()
            }));
        }
        for task in tasks {
            assert_eq!(*task.await.unwrap(), 9);
        }
        assert_eq!(calls.load(Ordering::SeqCst), 1);
    }

    #[tokio::test]
    async fn one_cancelled_waiter_does_not_cancel_another() {
        let memo = AsyncMemo::<u64, u64, &'static str>::new();
        let first_cancel = CancellationToken::new();
        let first = {
            let memo = memo.clone();
            let cancellation = first_cancel.clone();
            tokio::spawn(async move {
                memo.get_or_fill(
                    1,
                    &cancellation,
                    "cancelled",
                    |_| "producer failed",
                    producer_error_is_sticky,
                    |_| async move {
                        tokio::time::sleep(Duration::from_millis(40)).await;
                        Ok(7)
                    },
                )
                .await
            })
        };
        tokio::task::yield_now().await;
        let second = {
            let memo = memo.clone();
            tokio::spawn(async move {
                memo.get_or_fill(
                    1,
                    &CancellationToken::new(),
                    "cancelled",
                    |_| "producer failed",
                    producer_error_is_sticky,
                    |_| async move { panic!("the second waiter must join the first fill") },
                )
                .await
            })
        };
        first_cancel.cancel();
        assert_eq!(first.await.unwrap(), Err("cancelled"));
        assert_eq!(*second.await.unwrap().unwrap(), 7);
    }

    #[tokio::test]
    async fn completed_result_wins_cancellation_during_detachment() {
        let fill = Arc::new(Fill::<u64, &'static str> {
            state: Mutex::new(FillState::Complete(Err("producer failed"))),
            notify: Notify::new(),
            cancellation: CancellationToken::new(),
        });
        let mut consumer = ConsumerGuard {
            fill: Arc::clone(&fill),
            active: true,
        };

        let result = consumer.detach_and_join_last().await;
        assert_eq!(result, Some(Err("producer failed")));
        assert!(!consumer.active);
        assert!(!fill.cancellation.is_cancelled());
    }

    #[tokio::test]
    async fn nonfinal_running_consumer_detaches_as_ordinary_cancellation() {
        let fill = Arc::new(Fill::<u64, &'static str> {
            state: Mutex::new(FillState::Running { consumers: 2 }),
            notify: Notify::new(),
            cancellation: CancellationToken::new(),
        });
        let mut consumer = ConsumerGuard {
            fill: Arc::clone(&fill),
            active: true,
        };

        assert_eq!(consumer.detach_and_join_last().await, None);
        assert!(!consumer.active);
        assert!(!fill.cancellation.is_cancelled());
        let state = fill
            .state
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        assert!(matches!(*state, FillState::Running { consumers: 1 }));
    }

    #[tokio::test]
    async fn last_cancelled_waiter_joins_fill_and_clears_cell() {
        let memo = AsyncMemo::<u64, u64, &'static str>::new();
        let started = Arc::new(Notify::new());
        let stopped = Arc::new(AtomicUsize::new(0));
        let cancellation = CancellationToken::new();
        let waiter = {
            let memo = memo.clone();
            let started = Arc::clone(&started);
            let stopped = Arc::clone(&stopped);
            let cancellation = cancellation.clone();
            tokio::spawn(async move {
                memo.get_or_fill(
                    1,
                    &cancellation,
                    "cancelled",
                    |_| "producer failed",
                    producer_error_is_sticky,
                    move |fill_cancel| async move {
                        started.notify_one();
                        fill_cancel.cancelled().await;
                        stopped.store(1, Ordering::SeqCst);
                        Err("cancelled")
                    },
                )
                .await
            })
        };
        started.notified().await;
        cancellation.cancel();
        assert_eq!(waiter.await.unwrap(), Err("cancelled"));
        assert_eq!(stopped.load(Ordering::SeqCst), 1);
        assert!(memo.ready(&1).is_none());

        let value = memo
            .get_or_fill(
                1,
                &CancellationToken::new(),
                "cancelled",
                |_| "producer failed",
                producer_error_is_sticky,
                |_| async { Ok(11) },
            )
            .await
            .unwrap();
        assert_eq!(*value, 11);
    }

    #[tokio::test]
    async fn dropped_last_waiter_is_joined_by_structured_shutdown() {
        let memo = AsyncMemo::<u64, u64, &'static str>::new();
        let started = Arc::new(Notify::new());
        let stopped = Arc::new(AtomicUsize::new(0));
        let waiter = {
            let memo = memo.clone();
            let started = Arc::clone(&started);
            let stopped = Arc::clone(&stopped);
            tokio::spawn(async move {
                memo.get_or_fill(
                    1,
                    &CancellationToken::new(),
                    "cancelled",
                    |_| "producer failed",
                    producer_error_is_sticky,
                    move |fill_cancel| async move {
                        started.notify_one();
                        fill_cancel.cancelled().await;
                        tokio::time::sleep(Duration::from_millis(20)).await;
                        stopped.store(1, Ordering::SeqCst);
                        Err("cancelled")
                    },
                )
                .await
            })
        };
        started.notified().await;
        waiter.abort();
        assert!(waiter.await.unwrap_err().is_cancelled());

        memo.shutdown().await.unwrap();
        assert_eq!(stopped.load(Ordering::SeqCst), 1);
        assert!(memo.ready(&1).is_none());
    }

    #[tokio::test]
    async fn panicking_producer_settles_the_cell_and_supervisor() {
        let memo = AsyncMemo::<u64, u64, &'static str>::new();
        let result = memo
            .get_or_fill(
                1,
                &CancellationToken::new(),
                "cancelled",
                |_| "producer failed",
                producer_error_is_sticky,
                |_| async { panic!("producer panic") },
            )
            .await;
        assert_eq!(result, Err("producer failed"));
        assert!(memo.ready(&1).is_none());

        let replacement = memo
            .get_or_fill(
                1,
                &CancellationToken::new(),
                "cancelled",
                |_| "producer failed",
                producer_error_is_sticky,
                |_| async { Ok(13) },
            )
            .await
            .unwrap();
        assert_eq!(*replacement, 13);
        let shutdown = tokio::time::timeout(Duration::from_secs(1), memo.shutdown())
            .await
            .expect("shutdown must join every retained supervisor");
        assert_eq!(shutdown, Err("producer failed"));
    }

    #[tokio::test]
    async fn concurrent_shutdown_callers_wait_for_the_same_supervisor_set() {
        let memo = AsyncMemo::<u64, u64, &'static str>::new();
        let started = Arc::new(Notify::new());
        let stopped = Arc::new(AtomicUsize::new(0));
        let waiter = {
            let memo = memo.clone();
            let started = Arc::clone(&started);
            let stopped = Arc::clone(&stopped);
            tokio::spawn(async move {
                memo.get_or_fill(
                    1,
                    &CancellationToken::new(),
                    "cancelled",
                    |_| "producer failed",
                    producer_error_is_sticky,
                    move |fill_cancel| async move {
                        started.notify_one();
                        fill_cancel.cancelled().await;
                        tokio::time::sleep(Duration::from_millis(20)).await;
                        stopped.store(1, Ordering::SeqCst);
                        Err("cancelled")
                    },
                )
                .await
            })
        };
        started.notified().await;
        let (first, second) = tokio::join!(memo.shutdown(), memo.shutdown());
        assert_eq!(first, Ok(()));
        assert_eq!(second, Ok(()));
        assert_eq!(stopped.load(Ordering::SeqCst), 1);
        assert_eq!(waiter.await.unwrap(), Err("cancelled"));
    }

    #[tokio::test]
    async fn aborting_first_shutdown_caller_does_not_abandon_cleanup() {
        let memo = AsyncMemo::<u64, u64, &'static str>::new();
        let fill_started = Arc::new(Notify::new());
        let cleanup_started = Arc::new(Notify::new());
        let release_cleanup = Arc::new(Notify::new());
        let cleanup_complete = Arc::new(AtomicUsize::new(0));
        let waiter = {
            let memo = memo.clone();
            let fill_started = Arc::clone(&fill_started);
            let cleanup_started = Arc::clone(&cleanup_started);
            let release_cleanup = Arc::clone(&release_cleanup);
            let cleanup_complete = Arc::clone(&cleanup_complete);
            tokio::spawn(async move {
                memo.get_or_fill(
                    1,
                    &CancellationToken::new(),
                    "cancelled",
                    |_| "producer failed",
                    producer_error_is_sticky,
                    move |fill_cancel| async move {
                        fill_started.notify_one();
                        fill_cancel.cancelled().await;
                        cleanup_started.notify_one();
                        release_cleanup.notified().await;
                        cleanup_complete.store(1, Ordering::SeqCst);
                        Err("cancelled")
                    },
                )
                .await
            })
        };
        fill_started.notified().await;

        let first_shutdown = {
            let memo = memo.clone();
            tokio::spawn(async move { memo.shutdown().await })
        };
        cleanup_started.notified().await;
        first_shutdown.abort();
        assert!(first_shutdown.await.unwrap_err().is_cancelled());

        let later_shutdown = {
            let memo = memo.clone();
            tokio::spawn(async move { memo.shutdown().await })
        };
        tokio::task::yield_now().await;
        assert!(!later_shutdown.is_finished());
        release_cleanup.notify_one();

        tokio::time::timeout(Duration::from_secs(1), later_shutdown)
            .await
            .expect("a later shutdown caller must observe shared completion")
            .expect("the later shutdown task must not panic")
            .expect("cooperative cancellation must settle cleanly");
        assert_eq!(waiter.await.unwrap(), Err("cancelled"));
        assert_eq!(cleanup_complete.load(Ordering::SeqCst), 1);
        assert_eq!(memo.inner.active_fills.load(Ordering::Acquire), 0);
        assert!(
            memo.inner
                .supervisors
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner())
                .is_empty()
        );
        assert!(
            memo.inner
                .shutdown_supervisor
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner())
                .is_none()
        );
    }

    #[tokio::test]
    async fn producer_panic_dominates_explicit_final_waiter_cancellation() {
        let memo = AsyncMemo::<u64, u64, &'static str>::new();
        let started = Arc::new(Notify::new());
        let cancellation = CancellationToken::new();
        let waiter = {
            let memo = memo.clone();
            let started = Arc::clone(&started);
            let cancellation = cancellation.clone();
            tokio::spawn(async move {
                memo.get_or_fill(
                    1,
                    &cancellation,
                    "cancelled",
                    |_| "producer failed",
                    producer_error_is_sticky,
                    move |fill_cancel| async move {
                        started.notify_one();
                        fill_cancel.cancelled().await;
                        panic!("producer panic after final-waiter cancellation")
                    },
                )
                .await
            })
        };
        started.notified().await;
        cancellation.cancel();

        assert_eq!(waiter.await.unwrap(), Err("producer failed"));
        assert_eq!(memo.shutdown().await, Err("producer failed"));
        assert_eq!(memo.inner.active_fills.load(Ordering::Acquire), 0);
    }

    #[tokio::test]
    async fn sticky_producer_error_dominates_explicit_final_waiter_cancellation() {
        let memo = AsyncMemo::<u64, u64, &'static str>::new();
        let started = Arc::new(Notify::new());
        let cancellation = CancellationToken::new();
        let waiter = {
            let memo = memo.clone();
            let started = Arc::clone(&started);
            let cancellation = cancellation.clone();
            tokio::spawn(async move {
                memo.get_or_fill(
                    1,
                    &cancellation,
                    "cancelled",
                    |_| "join failed",
                    |error| *error == "run-global failure",
                    move |fill_cancel| async move {
                        started.notify_one();
                        fill_cancel.cancelled().await;
                        Err("run-global failure")
                    },
                )
                .await
            })
        };
        started.notified().await;
        cancellation.cancel();

        assert_eq!(waiter.await.unwrap(), Err("run-global failure"));
        assert_eq!(memo.shutdown().await, Err("run-global failure"));
        assert_eq!(memo.inner.active_fills.load(Ordering::Acquire), 0);
    }

    #[tokio::test]
    async fn aborted_final_waiter_cannot_hide_producer_panic_from_shutdown() {
        let memo = AsyncMemo::<u64, u64, &'static str>::new();
        let started = Arc::new(Notify::new());
        let waiter = {
            let memo = memo.clone();
            let started = Arc::clone(&started);
            tokio::spawn(async move {
                memo.get_or_fill(
                    1,
                    &CancellationToken::new(),
                    "cancelled",
                    |_| "producer failed",
                    producer_error_is_sticky,
                    move |fill_cancel| async move {
                        started.notify_one();
                        fill_cancel.cancelled().await;
                        panic!("producer panic after final waiter abort")
                    },
                )
                .await
            })
        };
        started.notified().await;
        waiter.abort();
        assert!(waiter.await.unwrap_err().is_cancelled());

        assert_eq!(memo.shutdown().await, Err("producer failed"));
        assert_eq!(memo.inner.active_fills.load(Ordering::Acquire), 0);
        assert!(
            memo.inner
                .supervisors
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner())
                .is_empty()
        );
    }
}
