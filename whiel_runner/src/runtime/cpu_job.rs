//! Retained ownership for admitted in-process CPU jobs.

use std::fmt;
use std::sync::{Arc, Mutex};

use tokio::sync::oneshot;
use tokio::task::{Id, JoinError, JoinSet};

use crate::failure::{FailureReport, FailureScope};

use super::{AdmissionError, CancellationToken, SolverAdmission};

// ------------------------------------------------------------
// Public-To-The-Crate Job Boundary
// ------------------------------------------------------------

#[derive(Clone, Debug)]
pub(crate) enum CpuJobError {
    Cancelled,
    Admission(AdmissionError),
    OwnerClosed,
    WorkerFailed(String),
    SupervisorFailed(String),
    Failure(FailureReport),
}

impl fmt::Display for CpuJobError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Cancelled => formatter.write_str("CPU job was cancelled"),
            Self::Admission(error) => write!(formatter, "CPU job admission failed: {error}"),
            Self::OwnerClosed => formatter.write_str("CPU job owner is closed"),
            Self::WorkerFailed(detail) => write!(formatter, "CPU worker failed: {detail}"),
            Self::SupervisorFailed(detail) => {
                write!(formatter, "CPU-job supervisor failed: {detail}")
            }
            Self::Failure(report) => write!(
                formatter,
                "CPU job context failed: {}",
                report.detail().unwrap_or("unspecified failure")
            ),
        }
    }
}

impl std::error::Error for CpuJobError {}

pub(crate) struct RetainedCpuJobs {
    registry: Mutex<RetainedCpuJobRegistry>,
    sticky_failure: Arc<Mutex<Option<CpuJobError>>>,
}

struct RetainedCpuJobRegistry {
    closed: bool,
    jobs: JoinSet<Result<(), CpuJobError>>,
    cancellations: std::collections::HashMap<Id, CancellationToken>,
}

impl RetainedCpuJobs {
    pub(crate) fn new() -> Self {
        Self {
            registry: Mutex::new(RetainedCpuJobRegistry {
                closed: false,
                jobs: JoinSet::new(),
                cancellations: std::collections::HashMap::new(),
            }),
            sticky_failure: Arc::new(Mutex::new(None)),
        }
    }

    /// Run one admitted blocking job under context-retained supervision.
    ///
    /// The caller owns only the result wait. The retained supervisor owns and
    /// joins the blocking task, while the blocking closure owns the CPU permit.
    /// Dropping the caller cancels the child token but cannot detach ownership
    /// from this group. Any run-global work failure is retained before its
    /// supervisor exits, so it remains visible to shutdown even when the
    /// result receiver vanishes.
    pub(crate) async fn run<T, F>(
        &self,
        admission: &SolverAdmission,
        caller_cancellation: &CancellationToken,
        work: F,
    ) -> Result<T, CpuJobError>
    where
        T: Send + 'static,
        F: FnOnce(CancellationToken) -> Result<T, CpuJobError> + Send + 'static,
    {
        let child_cancellation = CancellationToken::new();
        let mut cancellation_guard = CancellationGuard::new(child_cancellation.clone());
        let (result_sender, result_receiver) = oneshot::channel();
        let admission = admission.clone();
        let caller_cancellation = caller_cancellation.clone();
        let supervisor_cancellation = child_cancellation.clone();
        let sticky_failure = Arc::clone(&self.sticky_failure);

        let supervisor_id = {
            let mut registry = self
                .registry
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner());
            reap_finished(&mut registry, &self.sticky_failure);
            if let Some(error) = retained_failure(&self.sticky_failure) {
                return Err(error);
            }
            if caller_cancellation.is_cancelled() {
                return Err(CpuJobError::Cancelled);
            }
            if registry.closed {
                return Err(CpuJobError::OwnerClosed);
            }
            let supervisor = registry.jobs.spawn(async move {
                supervise_cpu_job(
                    admission,
                    caller_cancellation,
                    supervisor_cancellation,
                    work,
                    result_sender,
                    sticky_failure,
                )
                .await
            });
            let supervisor_id = supervisor.id();
            registry
                .cancellations
                .insert(supervisor_id, child_cancellation);
            supervisor_id
        };

        let result = match result_receiver.await {
            Ok(result) => result,
            Err(_) => Err(CpuJobError::SupervisorFailed(
                "supervisor stopped before publishing its terminal result".to_string(),
            )),
        };
        self.reap_completed_supervisor(supervisor_id).await;
        cancellation_guard.disarm();
        result
    }

    /// Reap this caller's completed supervisor before returning its result.
    ///
    /// The supervisor publishes through the oneshot immediately before its
    /// task returns. A rapid next launch can therefore observe the result
    /// before `JoinSet::try_join_next_with_id` observes the completed task.
    /// Yield and retry that nonblocking reap until this exact supervisor has
    /// left the retained registry. If the caller itself is dropped while
    /// waiting, its armed cancellation guard preserves the existing retained
    /// cleanup path.
    async fn reap_completed_supervisor(&self, supervisor_id: Id) {
        loop {
            let reaped = {
                let mut registry = self
                    .registry
                    .lock()
                    .unwrap_or_else(|poisoned| poisoned.into_inner());
                reap_finished(&mut registry, &self.sticky_failure);
                !registry.cancellations.contains_key(&supervisor_id)
            };
            if reaped {
                return;
            }
            tokio::task::yield_now().await;
        }
    }

    /// Stop admission, cancel every child, and join every retained supervisor.
    pub(crate) async fn shutdown(&self) -> Result<(), CpuJobError> {
        let mut jobs = {
            let mut registry = self
                .registry
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner());
            registry.closed = true;
            for cancellation in registry.cancellations.values() {
                cancellation.cancel();
            }
            registry.cancellations.clear();
            std::mem::take(&mut registry.jobs)
        };

        while let Some(joined) = jobs.join_next().await {
            retain_supervisor_result(&self.sticky_failure, joined);
        }
        match retained_failure(&self.sticky_failure) {
            Some(error) => Err(error),
            None => Ok(()),
        }
    }

    #[cfg(test)]
    fn retained_job_count(&self) -> usize {
        self.registry
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .jobs
            .len()
    }
}

impl Drop for RetainedCpuJobs {
    fn drop(&mut self) {
        let registry = self
            .registry
            .get_mut()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        for cancellation in registry.cancellations.values() {
            cancellation.cancel();
        }
        // Explicit context shutdown joins these supervisors. If the context is
        // dropped without shutdown, let them finish cooperative cleanup rather
        // than letting JoinSet::drop abort them around a blocking child. The
        // context's owned-work registration remains intentionally undischarged.
        registry.jobs.detach_all();
    }
}

fn reap_finished(
    registry: &mut RetainedCpuJobRegistry,
    sticky_failure: &Mutex<Option<CpuJobError>>,
) {
    while let Some(joined) = registry.jobs.try_join_next_with_id() {
        let id = match &joined {
            Ok((id, _)) => *id,
            Err(error) => error.id(),
        };
        registry.cancellations.remove(&id);
        retain_supervisor_result(sticky_failure, joined.map(|(_, result)| result));
    }
}

fn retain_supervisor_result(
    sticky_failure: &Mutex<Option<CpuJobError>>,
    joined: Result<Result<(), CpuJobError>, JoinError>,
) {
    match joined {
        Ok(Ok(())) => {}
        Ok(Err(error)) => retain_sticky_failure(sticky_failure, error),
        Err(error) => retain_sticky_failure(
            sticky_failure,
            CpuJobError::SupervisorFailed(error.to_string()),
        ),
    }
}

fn retain_sticky_failure(sticky_failure: &Mutex<Option<CpuJobError>>, error: CpuJobError) {
    let mut retained = sticky_failure
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    retained.get_or_insert(error);
}

fn retained_failure(sticky_failure: &Mutex<Option<CpuJobError>>) -> Option<CpuJobError> {
    sticky_failure
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
        .clone()
}

fn error_is_sticky(error: &CpuJobError) -> bool {
    match error {
        CpuJobError::Failure(report) => report.scope() == FailureScope::RunGlobal,
        CpuJobError::Admission(AdmissionError::Closed(_))
        | CpuJobError::WorkerFailed(_)
        | CpuJobError::SupervisorFailed(_) => true,
        CpuJobError::Cancelled
        | CpuJobError::Admission(AdmissionError::Cancelled)
        | CpuJobError::Admission(AdmissionError::InsufficientCapacity)
        | CpuJobError::OwnerClosed => false,
    }
}

async fn supervise_cpu_job<T, F>(
    admission: SolverAdmission,
    caller_cancellation: CancellationToken,
    child_cancellation: CancellationToken,
    work: F,
    result_sender: oneshot::Sender<Result<T, CpuJobError>>,
    sticky_failure: Arc<Mutex<Option<CpuJobError>>>,
) -> Result<(), CpuJobError>
where
    T: Send + 'static,
    F: FnOnce(CancellationToken) -> Result<T, CpuJobError> + Send + 'static,
{
    let permit = tokio::select! {
        biased;
        result = admission.acquire_cpu_worker(&child_cancellation) => result,
        _ = caller_cancellation.cancelled() => {
            child_cancellation.cancel();
            Err(AdmissionError::Cancelled)
        }
    };
    let permit = match permit {
        Ok(permit) => permit,
        Err(AdmissionError::Cancelled) => {
            let _ = result_sender.send(Err(CpuJobError::Cancelled));
            return Ok(());
        }
        Err(error @ AdmissionError::InsufficientCapacity) => {
            let _ = result_sender.send(Err(CpuJobError::Admission(error)));
            return Ok(());
        }
        Err(AdmissionError::Closed(report)) => {
            let error = CpuJobError::Admission(AdmissionError::Closed(report));
            retain_sticky_failure(&sticky_failure, error.clone());
            let _ = result_sender.send(Err(error.clone()));
            return Err(error);
        }
    };
    if caller_cancellation.is_cancelled() || child_cancellation.is_cancelled() {
        child_cancellation.cancel();
        drop(permit);
        let _ = result_sender.send(Err(CpuJobError::Cancelled));
        return Ok(());
    }

    let worker_cancellation = child_cancellation.clone();
    let mut worker = tokio::task::spawn_blocking(move || {
        let _permit = permit;
        if worker_cancellation.is_cancelled() {
            BlockingOutcome::Cancelled
        } else {
            BlockingOutcome::Complete(work(worker_cancellation))
        }
    });
    let (joined, cancellation_won) = tokio::select! {
        biased;
        result = &mut worker => (result, false),
        _ = caller_cancellation.cancelled() => {
            child_cancellation.cancel();
            (worker.await, true)
        }
        _ = child_cancellation.cancelled() => (worker.await, true),
    };
    publish_supervisor_outcome(joined, cancellation_won, result_sender, &sticky_failure)
}

fn publish_supervisor_outcome<T>(
    joined: Result<BlockingOutcome<T>, JoinError>,
    cancellation_won: bool,
    result_sender: oneshot::Sender<Result<T, CpuJobError>>,
    sticky_failure: &Mutex<Option<CpuJobError>>,
) -> Result<(), CpuJobError> {
    match joined {
        Ok(BlockingOutcome::Complete(Err(error))) if error_is_sticky(&error) => {
            retain_sticky_failure(sticky_failure, error.clone());
            let _ = result_sender.send(Err(error.clone()));
            Err(error)
        }
        Ok(BlockingOutcome::Complete(result)) if !cancellation_won => {
            let _ = result_sender.send(result);
            Ok(())
        }
        Ok(BlockingOutcome::Complete(_)) | Ok(BlockingOutcome::Cancelled) => {
            let _ = result_sender.send(Err(CpuJobError::Cancelled));
            Ok(())
        }
        Err(error) => {
            let error = CpuJobError::WorkerFailed(error.to_string());
            retain_sticky_failure(sticky_failure, error.clone());
            let _ = result_sender.send(Err(error.clone()));
            Err(error)
        }
    }
}

enum BlockingOutcome<T> {
    Cancelled,
    Complete(Result<T, CpuJobError>),
}

struct CancellationGuard {
    cancellation: CancellationToken,
    armed: bool,
}

impl CancellationGuard {
    fn new(cancellation: CancellationToken) -> Self {
        Self {
            cancellation,
            armed: true,
        }
    }

    fn disarm(&mut self) {
        self.armed = false;
    }
}

impl Drop for CancellationGuard {
    fn drop(&mut self) {
        if self.armed {
            self.cancellation.cancel();
        }
    }
}

// ------------------------------------------------------------
// Tests
// ------------------------------------------------------------

#[cfg(test)]
mod tests {
    use std::sync::{Arc, Condvar, Mutex};
    use std::time::Duration;

    use tokio::sync::oneshot;

    use super::*;
    use crate::runtime::{RuntimeResourcePolicy, create_general_solver_admission};

    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn dropped_caller_cancels_child_and_capacity_survives_until_worker_exit() {
        let jobs = Arc::new(RetainedCpuJobs::new());
        let policy = RuntimeResourcePolicy::agent_only(1, 1).unwrap();
        let admission = create_general_solver_admission(policy).unwrap();
        let release = Arc::new((Mutex::new(false), Condvar::new()));
        let (started_sender, started_receiver) = oneshot::channel();
        let (cancelled_sender, cancelled_receiver) = oneshot::channel();

        let waiter_jobs = Arc::clone(&jobs);
        let waiter_admission = admission.clone();
        let worker_release = Arc::clone(&release);
        let waiter = tokio::spawn(async move {
            let caller_cancellation = CancellationToken::new();
            waiter_jobs
                .run(
                    &waiter_admission,
                    &caller_cancellation,
                    move |child_cancellation| {
                        let _ = started_sender.send(());
                        child_cancellation.wait_cancelled();
                        let _ = cancelled_sender.send(());
                        let (lock, condition) = &*worker_release;
                        let mut released =
                            lock.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
                        while !*released {
                            released = condition
                                .wait(released)
                                .unwrap_or_else(|poisoned| poisoned.into_inner());
                        }
                        Ok(17_u64)
                    },
                )
                .await
        });

        started_receiver.await.unwrap();
        waiter.abort();
        assert!(waiter.await.unwrap_err().is_cancelled());
        tokio::time::timeout(Duration::from_secs(1), cancelled_receiver)
            .await
            .expect("dropping the caller must cancel its blocking child")
            .unwrap();
        assert_eq!(jobs.retained_job_count(), 1);

        let successor = tokio::time::timeout(
            Duration::from_millis(30),
            admission.acquire_cpu_worker(&CancellationToken::new()),
        )
        .await;
        assert!(
            successor.is_err(),
            "the blocking closure must retain its CPU permit through cleanup"
        );

        {
            let (lock, condition) = &*release;
            *lock.lock().unwrap_or_else(|poisoned| poisoned.into_inner()) = true;
            condition.notify_all();
        }
        tokio::time::timeout(Duration::from_secs(1), jobs.shutdown())
            .await
            .expect("shutdown must join the retained supervisor")
            .unwrap();
        let permit = tokio::time::timeout(
            Duration::from_secs(1),
            admission.acquire_cpu_worker(&CancellationToken::new()),
        )
        .await
        .expect("capacity must return after retained cleanup")
        .unwrap();
        drop(permit);
    }

    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn cancellation_while_queued_launches_no_blocking_work() {
        let jobs = Arc::new(RetainedCpuJobs::new());
        let policy = RuntimeResourcePolicy::agent_only(1, 1).unwrap();
        let admission = create_general_solver_admission(policy).unwrap();
        let holder = admission
            .acquire_cpu_worker(&CancellationToken::new())
            .await
            .unwrap();
        let launched = Arc::new(std::sync::atomic::AtomicBool::new(false));

        let waiter_jobs = Arc::clone(&jobs);
        let waiter_admission = admission.clone();
        let worker_launched = Arc::clone(&launched);
        let waiter = tokio::spawn(async move {
            waiter_jobs
                .run(&waiter_admission, &CancellationToken::new(), move |_| {
                    worker_launched.store(true, std::sync::atomic::Ordering::Release);
                    Ok(())
                })
                .await
        });
        tokio::time::timeout(Duration::from_secs(1), async {
            while jobs.retained_job_count() == 0 {
                tokio::task::yield_now().await;
            }
        })
        .await
        .expect("the queued job must enter retained supervision");
        waiter.abort();
        assert!(waiter.await.unwrap_err().is_cancelled());
        jobs.shutdown().await.unwrap();
        assert!(!launched.load(std::sync::atomic::Ordering::Acquire));
        drop(holder);
    }

    #[tokio::test(flavor = "current_thread")]
    async fn queued_cancellation_and_released_capacity_launch_no_blocking_work() {
        let jobs = Arc::new(RetainedCpuJobs::new());
        let policy = RuntimeResourcePolicy::agent_only(1, 1).unwrap();
        let admission = create_general_solver_admission(policy).unwrap();
        let holder = admission
            .acquire_cpu_worker(&CancellationToken::new())
            .await
            .unwrap();
        let caller_cancellation = CancellationToken::new();
        let launched = Arc::new(std::sync::atomic::AtomicBool::new(false));

        let waiter_jobs = Arc::clone(&jobs);
        let waiter_admission = admission.clone();
        let waiter_cancellation = caller_cancellation.clone();
        let worker_launched = Arc::clone(&launched);
        let waiter = tokio::spawn(async move {
            waiter_jobs
                .run(&waiter_admission, &waiter_cancellation, move |_| {
                    worker_launched.store(true, std::sync::atomic::Ordering::Release);
                    Ok(())
                })
                .await
        });
        while jobs.retained_job_count() == 0 {
            tokio::task::yield_now().await;
        }

        // Make both admission and caller cancellation ready before the
        // single-threaded executor polls the retained supervisor again.
        caller_cancellation.cancel();
        drop(holder);

        assert!(matches!(waiter.await.unwrap(), Err(CpuJobError::Cancelled)));
        jobs.shutdown().await.unwrap();
        assert!(!launched.load(std::sync::atomic::Ordering::Acquire));
    }

    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn completed_job_returns_generic_value_and_reaps_its_supervisor() {
        let jobs = RetainedCpuJobs::new();
        let policy = RuntimeResourcePolicy::agent_only(1, 1).unwrap();
        let admission = create_general_solver_admission(policy).unwrap();
        let value = jobs
            .run(&admission, &CancellationToken::new(), |_| {
                Ok(String::from("ready"))
            })
            .await
            .unwrap();
        assert_eq!(value, "ready");
        assert_eq!(jobs.retained_job_count(), 0);
        jobs.shutdown().await.unwrap();
        assert_eq!(jobs.retained_job_count(), 0);
    }

    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn dropped_caller_cannot_hide_a_run_global_work_failure() {
        let jobs = Arc::new(RetainedCpuJobs::new());
        let policy = RuntimeResourcePolicy::agent_only(1, 1).unwrap();
        let admission = create_general_solver_admission(policy).unwrap();
        let (started_sender, started_receiver) = oneshot::channel();
        let (failed_sender, failed_receiver) = oneshot::channel();

        let waiter_jobs = Arc::clone(&jobs);
        let waiter_admission = admission.clone();
        let waiter = tokio::spawn(async move {
            waiter_jobs
                .run(
                    &waiter_admission,
                    &CancellationToken::new(),
                    move |child_cancellation| {
                        let _ = started_sender.send(());
                        child_cancellation.wait_cancelled();
                        let report = FailureReport::admission_authority(
                            "dropped CPU-job caller failure fixture",
                        );
                        let _ = failed_sender.send(());
                        Err::<(), _>(CpuJobError::Failure(report))
                    },
                )
                .await
        });

        started_receiver.await.unwrap();
        waiter.abort();
        assert!(waiter.await.unwrap_err().is_cancelled());
        tokio::time::timeout(Duration::from_secs(1), failed_receiver)
            .await
            .expect("the cancelled child must finish with its run-global failure")
            .unwrap();

        let Err(CpuJobError::Failure(report)) = jobs.shutdown().await else {
            panic!("shutdown must retain the dropped caller's run-global failure")
        };
        assert_eq!(report.scope(), FailureScope::RunGlobal);
    }

    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn later_launches_reap_completed_supervisors() {
        let jobs = RetainedCpuJobs::new();
        let policy = RuntimeResourcePolicy::agent_only(1, 1).unwrap();
        let admission = create_general_solver_admission(policy).unwrap();

        for expected in 0_u64..128 {
            let value = jobs
                .run(&admission, &CancellationToken::new(), move |_| Ok(expected))
                .await
                .unwrap();
            assert_eq!(value, expected);
            assert_eq!(
                jobs.retained_job_count(),
                0,
                "a returning caller must reap its own completed supervisor"
            );
        }
        jobs.shutdown().await.unwrap();
    }

    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn completed_worker_branch_is_not_stolen_by_later_cancellation() {
        let (result_sender, mut result_receiver) = oneshot::channel();
        let sticky_failure = Mutex::new(None);
        let later_cancellation = CancellationToken::new();

        // The worker-result select branch is the linearization point. A token
        // becoming cancelled after that branch won cannot change its outcome.
        later_cancellation.cancel();
        publish_supervisor_outcome(
            Ok(BlockingOutcome::Complete(Ok(23_u64))),
            false,
            result_sender,
            &sticky_failure,
        )
        .unwrap();
        assert_eq!(result_receiver.try_recv().unwrap().unwrap(), 23);
    }
}
