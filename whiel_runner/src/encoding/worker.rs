//! Persistent owned worker processes and a bounded request pool.

use std::collections::{HashSet, VecDeque};
use std::ffi::OsString;
use std::io::Read;
#[cfg(any(target_os = "macos", target_os = "linux"))]
use std::os::fd::AsRawFd;
use std::path::PathBuf;
use std::process::{Child, ChildStderr, ChildStdin, ChildStdout, Command, Stdio};
use std::sync::atomic::{AtomicBool, AtomicU32, AtomicU64, Ordering};
use std::sync::mpsc;
use std::sync::{Arc, Mutex};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

use tokio::sync::Notify;

#[cfg(any(target_os = "macos", target_os = "linux"))]
use crate::runtime::process_tree::{ProcessRegistry, signal_group, signal_identity};
use crate::runtime::{AdmissionError, CancellationToken, CpuWorkerPermit, SolverAdmission};

use super::context::{EncodingError, EncodingFailureClass, encoding_failure};
use super::names::{NameEnvDelta, NameEnvRevision, NameEnvSync, NameMappingKind};
use super::proposal::{
    PROPOSAL_PAGE_PROTOCOL_VERSION, ProposalDelta, ProposalRealization, ProposalRevision,
    ProposalSync, canonical_value_sha256,
};
use super::protocol::{
    FIXED_AMBIENT_WORKER_FORMAT_VERSION, FixedAmbientNameBinding, FixedAmbientWorkerOperation,
    FixedAmbientWorkerRequestEnvelope, FixedAmbientWorkerResponseEnvelope,
    FixedAmbientWorkerTaskIdentity, MAX_ENCODING_FRAME_BYTES, NameBinding, WORKER_FORMAT_VERSION,
    WorkerOperation, WorkerRequestEnvelope, WorkerResponseEnvelope, WorkerResponseStatus,
    read_frame, write_frame,
};

const MAX_STDERR_BYTES: usize = 64 * 1024;
const PROCESS_POLL_INTERVAL: Duration = Duration::from_millis(10);
const PROCESS_CLEANUP_GRACE: Duration = Duration::from_millis(750);

// ------------------------------------------------------------
// Dynamic W-Layer Replay
// ------------------------------------------------------------

/// One exact committed W-layer response replayed after worker restart.
#[derive(Clone, Debug)]
pub(crate) struct WLayerReplay {
    pub(crate) index: u64,
    pub(crate) expected_digest: Arc<str>,
}

/// Immutable replay plan through one committed W-layer prefix.
#[derive(Clone, Debug)]
pub(crate) struct WLayerSync {
    pub(crate) entries: Arc<Vec<WLayerReplay>>,
}

impl WLayerSync {
    pub(crate) fn empty() -> Self {
        Self {
            entries: Arc::new(Vec::new()),
        }
    }

    pub(crate) fn target_count(&self) -> usize {
        self.entries.len()
    }
}

// ------------------------------------------------------------
// Worker Configuration
// ------------------------------------------------------------

#[derive(Clone, Debug)]
pub struct EncodingWorkerCommand {
    executable: PathBuf,
    arguments: Arc<[OsString]>,
    current_directory: PathBuf,
}

impl EncodingWorkerCommand {
    pub fn new(executable: impl Into<PathBuf>, current_directory: impl Into<PathBuf>) -> Self {
        Self {
            executable: executable.into(),
            arguments: Arc::from([]),
            current_directory: current_directory.into(),
        }
    }

    pub fn arguments(mut self, arguments: impl IntoIterator<Item = OsString>) -> Self {
        self.arguments = arguments.into_iter().collect::<Vec<_>>().into();
        self
    }

    fn for_context(&self, context_id: &str) -> Self {
        let mut arguments = self.arguments.to_vec();
        arguments.push(OsString::from(context_id));
        Self {
            executable: self.executable.clone(),
            arguments: arguments.into(),
            current_directory: self.current_directory.clone(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct EncodingWorkerPoolConfig {
    pub command: EncodingWorkerCommand,
    pub workers: usize,
    pub max_frame_bytes: usize,
    pub proposal_realization: ProposalRealization,
}

impl EncodingWorkerPoolConfig {
    pub fn new(command: EncodingWorkerCommand, workers: usize) -> Result<Self, &'static str> {
        if workers == 0 {
            return Err("the encoding worker pool must contain at least one worker");
        }
        Ok(Self {
            command,
            workers,
            max_frame_bytes: MAX_ENCODING_FRAME_BYTES,
            proposal_realization: ProposalRealization::default(),
        })
    }

    /// Select one compiled proposal realization for the lifetime of a context.
    pub fn proposal_realization(mut self, realization: ProposalRealization) -> Self {
        self.proposal_realization = realization;
        self
    }

    pub fn max_frame_bytes(mut self, maximum: usize) -> Result<Self, &'static str> {
        if maximum == 0 || maximum > MAX_ENCODING_FRAME_BYTES {
            return Err("the worker frame maximum is outside the supported range");
        }
        self.max_frame_bytes = maximum;
        Ok(self)
    }
}

/// Command for the independent fixed-ambient Lean worker.
#[derive(Clone, Debug)]
pub struct FixedAmbientWorkerCommand {
    executable: PathBuf,
    arguments: Arc<[OsString]>,
    current_directory: PathBuf,
}

impl FixedAmbientWorkerCommand {
    pub fn new(executable: impl Into<PathBuf>, current_directory: impl Into<PathBuf>) -> Self {
        Self {
            executable: executable.into(),
            arguments: Arc::from([]),
            current_directory: current_directory.into(),
        }
    }

    /// Arguments placed before the worker's required `worker` subcommand.
    pub fn arguments(mut self, arguments: impl IntoIterator<Item = OsString>) -> Self {
        self.arguments = arguments.into_iter().collect::<Vec<_>>().into();
        self
    }

    fn worker_arguments(&self) -> Vec<OsString> {
        let mut arguments = self.arguments.to_vec();
        arguments.push(OsString::from("worker"));
        arguments
    }

    pub fn executable(&self) -> &std::path::Path {
        &self.executable
    }

    pub fn argument_prefix(&self) -> &[OsString] {
        &self.arguments
    }

    pub fn current_directory(&self) -> &std::path::Path {
        &self.current_directory
    }

    fn as_encoding_command(&self) -> EncodingWorkerCommand {
        EncodingWorkerCommand {
            executable: self.executable.clone(),
            arguments: self.worker_arguments().into(),
            current_directory: self.current_directory.clone(),
        }
    }
}

/// Threads one spawned Lean worker may use. One: the pool provides the run's
/// parallelism, and threads inside a worker would only compete with the
/// concurrent checks for the same cores.
pub const LEAN_WORKER_THREADS: usize = 1;

/// How long one fixed-ambient exchange may take before the worker counts as
/// lost. Generous by design: a healthy exchange is milliseconds to seconds
/// even on the largest committed-clause snapshot, so this can only fire on a
/// worker that has stopped answering.
pub const FIXED_AMBIENT_ROUND_TRIP_TIMEOUT: Duration = Duration::from_secs(300);

/// Bounded pool configuration for the fixed-ambient protocol.
#[derive(Clone, Debug)]
pub struct FixedAmbientWorkerPoolConfig {
    command: FixedAmbientWorkerCommand,
    workers: usize,
    max_frame_bytes: usize,
    round_trip_timeout: Duration,
}

impl FixedAmbientWorkerPoolConfig {
    pub fn new(command: FixedAmbientWorkerCommand, workers: usize) -> Result<Self, &'static str> {
        if workers == 0 {
            return Err("the fixed-ambient worker pool must contain at least one worker");
        }
        Ok(Self {
            command,
            workers,
            max_frame_bytes: MAX_ENCODING_FRAME_BYTES,
            round_trip_timeout: FIXED_AMBIENT_ROUND_TRIP_TIMEOUT,
        })
    }

    pub fn max_frame_bytes(mut self, maximum: usize) -> Result<Self, &'static str> {
        if maximum == 0 || maximum > MAX_ENCODING_FRAME_BYTES {
            return Err("the worker frame maximum is outside the supported range");
        }
        self.max_frame_bytes = maximum;
        Ok(self)
    }

    /// Only a shorter allowance than the default is accepted, so a caller can
    /// exercise the fail-closed path without being able to disarm it.
    pub fn round_trip_timeout(mut self, allowance: Duration) -> Result<Self, &'static str> {
        if allowance.is_zero() || allowance > FIXED_AMBIENT_ROUND_TRIP_TIMEOUT {
            return Err("the worker round-trip allowance is outside the supported range");
        }
        self.round_trip_timeout = allowance;
        Ok(self)
    }

    pub fn command(&self) -> &FixedAmbientWorkerCommand {
        &self.command
    }

    pub fn worker_count(&self) -> usize {
        self.workers
    }

    pub fn frame_limit(&self) -> usize {
        self.max_frame_bytes
    }

    pub fn round_trip_allowance(&self) -> Duration {
        self.round_trip_timeout
    }
}

// ------------------------------------------------------------
// Bounded Pool
// ------------------------------------------------------------

pub(crate) struct EncodingWorkerPool {
    slots: Arc<[Arc<WorkerSlot>]>,
    available: Arc<AvailableWorkers>,
    lifecycle: Arc<WorkerPoolLifecycle>,
    maximum: usize,
    closed: AtomicBool,
    shutdown: Arc<WorkerPoolShutdown>,
}

/// A non-owning hint for the worker which retains one incremental frontier.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct WorkerAffinity {
    index: usize,
}

struct AvailableWorkers {
    queue: Mutex<VecDeque<usize>>,
    preferred: Mutex<HashSet<usize>>,
    notify: Notify,
}

struct PreferredReservation {
    available: Arc<AvailableWorkers>,
    index: usize,
    active: bool,
}

impl PreferredReservation {
    fn new(available: Arc<AvailableWorkers>, index: usize) -> Result<Self, EncodingError> {
        if !available
            .preferred
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .insert(index)
        {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "encoding worker already has a preferred waiter",
            )));
        }
        Ok(Self {
            available,
            index,
            active: true,
        })
    }

    fn disarm(&mut self) {
        self.available
            .preferred
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .remove(&self.index);
        self.active = false;
    }
}

impl Drop for PreferredReservation {
    fn drop(&mut self) {
        if self.active {
            self.available
                .preferred
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner())
                .remove(&self.index);
            self.available.notify.notify_waiters();
        }
    }
}

struct WorkerPoolShutdown {
    started: AtomicBool,
    result: Mutex<Option<Result<(), EncodingError>>>,
    settled: Notify,
}

struct WorkerPoolLifecycle {
    state: Mutex<WorkerPoolLifecycleState>,
    settled: Notify,
}

struct WorkerPoolLifecycleState {
    closed: bool,
    active: usize,
}

struct WorkerExecution {
    lifecycle: Arc<WorkerPoolLifecycle>,
}

impl WorkerPoolLifecycle {
    fn new() -> Self {
        Self {
            state: Mutex::new(WorkerPoolLifecycleState {
                closed: false,
                active: 0,
            }),
            settled: Notify::new(),
        }
    }

    fn begin(self: &Arc<Self>, slot: &WorkerSlot) -> Option<WorkerExecution> {
        let mut state = self
            .state
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        if state.closed {
            return None;
        }
        slot.begin_request();
        state.active += 1;
        Some(WorkerExecution {
            lifecycle: Arc::clone(self),
        })
    }

    fn begin_fixed_ambient(
        self: &Arc<Self>,
        slot: &FixedAmbientWorkerSlot,
    ) -> Option<WorkerExecution> {
        let mut state = self
            .state
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        if state.closed {
            return None;
        }
        slot.begin_request();
        state.active += 1;
        Some(WorkerExecution {
            lifecycle: Arc::clone(self),
        })
    }

    fn close(&self) {
        self.state
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .closed = true;
    }

    async fn wait(&self) {
        loop {
            let notified = self.settled.notified();
            tokio::pin!(notified);
            notified.as_mut().enable();
            if self
                .state
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner())
                .active
                == 0
            {
                return;
            }
            notified.await;
        }
    }
}

impl Drop for WorkerExecution {
    fn drop(&mut self) {
        let mut state = self
            .lifecycle
            .state
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        state.active = state
            .active
            .checked_sub(1)
            .expect("registered worker execution remains active");
        if state.active == 0 {
            self.lifecycle.settled.notify_waiters();
        }
    }
}

impl EncodingWorkerPool {
    pub(crate) fn new(config: EncodingWorkerPoolConfig, context_id: &str) -> Self {
        let mut slots = Vec::with_capacity(config.workers);
        let command = config.command.for_context(context_id);
        for _ in 0..config.workers {
            slots.push(Arc::new(WorkerSlot::new(
                command.clone(),
                config.max_frame_bytes,
            )));
        }
        Self {
            slots: slots.into(),
            available: Arc::new(AvailableWorkers {
                queue: Mutex::new((0..config.workers).collect()),
                preferred: Mutex::new(HashSet::new()),
                notify: Notify::new(),
            }),
            lifecycle: Arc::new(WorkerPoolLifecycle::new()),
            maximum: config.max_frame_bytes,
            closed: AtomicBool::new(false),
            shutdown: Arc::new(WorkerPoolShutdown {
                started: AtomicBool::new(false),
                result: Mutex::new(None),
                settled: Notify::new(),
            }),
        }
    }

    pub(crate) fn capacity(&self) -> usize {
        self.slots.len()
    }

    pub(crate) fn max_frame_bytes(&self) -> usize {
        self.maximum
    }

    #[cfg(test)]
    pub(crate) fn inject_cleanup_failure(&self, detail: &str) {
        record_cleanup_failure(&self.slots[0].cleanup_failure, detail);
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) async fn execute(
        &self,
        admission: &SolverAdmission,
        name_sync: NameEnvSync,
        proposal_sync: ProposalSync,
        w_sync: WLayerSync,
        request: WorkerRequestEnvelope,
        next_request: Arc<AtomicU64>,
        cancellation: &CancellationToken,
    ) -> Result<WorkerResponseEnvelope, EncodingError> {
        Ok(self
            .execute_retained(
                admission,
                name_sync,
                proposal_sync,
                w_sync,
                request,
                next_request,
                cancellation,
            )
            .await?
            .accept())
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) async fn execute_retained(
        &self,
        admission: &SolverAdmission,
        name_sync: NameEnvSync,
        proposal_sync: ProposalSync,
        w_sync: WLayerSync,
        request: WorkerRequestEnvelope,
        next_request: Arc<AtomicU64>,
        cancellation: &CancellationToken,
    ) -> Result<RetainedWorkerResponse, EncodingError> {
        self.execute_retained_with_affinity(
            None,
            admission,
            name_sync,
            proposal_sync,
            w_sync,
            request,
            next_request,
            cancellation,
        )
        .await
    }

    /// Execute on the worker which most recently committed this frontier.
    #[allow(clippy::too_many_arguments)]
    pub(crate) async fn execute_retained_with_affinity(
        &self,
        affinity: Option<WorkerAffinity>,
        admission: &SolverAdmission,
        name_sync: NameEnvSync,
        proposal_sync: ProposalSync,
        w_sync: WLayerSync,
        request: WorkerRequestEnvelope,
        next_request: Arc<AtomicU64>,
        cancellation: &CancellationToken,
    ) -> Result<RetainedWorkerResponse, EncodingError> {
        if self.closed.load(Ordering::Acquire) {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "encoding worker pool is closed",
            )));
        }
        let slot_lease = match affinity {
            Some(affinity) => self.acquire_preferred_slot(affinity, cancellation).await?,
            None => self.acquire_slot(cancellation).await?,
        };
        let slot = Arc::clone(&self.slots[slot_lease.index]);
        let cpu = match admission.acquire_cpu_worker(cancellation).await {
            Ok(permit) => permit,
            Err(AdmissionError::Cancelled) => return Err(EncodingError::Cancelled),
            Err(AdmissionError::Closed(report)) => return Err(EncodingError::Failure(report)),
            Err(AdmissionError::InsufficientCapacity) => {
                return Err(EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::LocalInfrastructure,
                    "encoding work exceeds the configured CPU-worker capacity",
                )));
            }
        };
        self.launch_retained(
            slot,
            slot_lease,
            cpu,
            name_sync,
            proposal_sync,
            w_sync,
            request,
            next_request,
            cancellation,
        )
        .await
    }

    /// Continue one accepted paginated operation on its exact worker slot.
    ///
    /// The session retains no CPU permit between pages. It retains only the
    /// worker slot whose private Lean state caches the generated stage.
    #[allow(clippy::too_many_arguments)]
    pub(crate) async fn execute_retained_in(
        &self,
        session: RetainedWorkerSession,
        admission: &SolverAdmission,
        name_sync: NameEnvSync,
        proposal_sync: ProposalSync,
        w_sync: WLayerSync,
        request: WorkerRequestEnvelope,
        next_request: Arc<AtomicU64>,
        cancellation: &CancellationToken,
    ) -> Result<RetainedWorkerResponse, EncodingError> {
        if self.closed.load(Ordering::Acquire) {
            let error = EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "encoding worker pool is closed",
            ));
            return reject_retained_session(session, error).await;
        }
        let cpu = match admission.acquire_cpu_worker(cancellation).await {
            Ok(permit) => permit,
            Err(AdmissionError::Cancelled) => {
                return reject_retained_session(session, EncodingError::Cancelled).await;
            }
            Err(AdmissionError::Closed(report)) => {
                return reject_retained_session(session, EncodingError::Failure(report)).await;
            }
            Err(AdmissionError::InsufficientCapacity) => {
                let error = EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::LocalInfrastructure,
                    "encoding work exceeds the configured CPU-worker capacity",
                ));
                return reject_retained_session(session, error).await;
            }
        };
        let (slot, slot_lease) = session.into_parts();
        self.launch_retained(
            slot,
            slot_lease,
            cpu,
            name_sync,
            proposal_sync,
            w_sync,
            request,
            next_request,
            cancellation,
        )
        .await
    }

    #[allow(clippy::too_many_arguments)]
    async fn launch_retained(
        &self,
        slot: Arc<WorkerSlot>,
        slot_lease: AvailableSlot,
        cpu: CpuWorkerPermit,
        name_sync: NameEnvSync,
        proposal_sync: ProposalSync,
        w_sync: WLayerSync,
        request: WorkerRequestEnvelope,
        next_request: Arc<AtomicU64>,
        cancellation: &CancellationToken,
    ) -> Result<RetainedWorkerResponse, EncodingError> {
        if self.closed.load(Ordering::Acquire) {
            let error = EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "encoding worker pool closed before request launch",
            ));
            return reject_retained_parts(slot, slot_lease, error).await;
        }
        let Some(execution) = self.lifecycle.begin(&slot) else {
            let error = EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "encoding worker pool closed before request registration",
            ));
            return reject_retained_parts(slot, slot_lease, error).await;
        };
        let abandonment = CancellationToken::new();
        let mut abandonment_guard = ExecutionAbandonmentGuard::new(abandonment.clone());
        let request_cancellation = cancellation.clone();
        let supervisor = tokio::spawn(supervise_worker_execution(
            slot,
            slot_lease,
            cpu,
            name_sync,
            proposal_sync,
            w_sync,
            request,
            next_request,
            request_cancellation,
            abandonment,
            execution,
        ));
        let result = match supervisor.await {
            Ok(result) => result.map(|(response, slot_lease)| RetainedWorkerResponse {
                response: Some(response),
                slot: Some(Arc::clone(&self.slots[slot_lease.index])),
                slot_lease: Some(slot_lease),
            }),
            Err(error) => Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                format!("encoding worker supervisor failed: {error}"),
            ))),
        };
        abandonment_guard.disarm();
        result
    }

    pub(crate) async fn shutdown(&self) -> Result<(), EncodingError> {
        self.lifecycle.close();
        self.closed.store(true, Ordering::Release);
        self.available.notify.notify_waiters();
        for slot in self.slots.iter() {
            slot.kill_active();
        }
        if self
            .shutdown
            .started
            .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
            .is_ok()
        {
            let slots = Arc::clone(&self.slots);
            let lifecycle = Arc::clone(&self.lifecycle);
            let shutdown = Arc::clone(&self.shutdown);
            tokio::spawn(async move {
                let cleanup = tokio::spawn(async move {
                    lifecycle.wait().await;
                    shutdown_worker_slots(slots).await
                })
                .await;
                let result = match cleanup {
                    Ok(result) => result,
                    Err(error) => Err(EncodingError::Failure(encoding_failure(
                        EncodingFailureClass::SharedInfrastructure,
                        format!("Lean encoding-worker pool shutdown task failed: {error}"),
                    ))),
                };
                *shutdown
                    .result
                    .lock()
                    .unwrap_or_else(|poisoned| poisoned.into_inner()) = Some(result);
                shutdown.settled.notify_waiters();
            });
        }
        self.shutdown.wait().await
    }

    async fn acquire_slot(
        &self,
        cancellation: &CancellationToken,
    ) -> Result<AvailableSlot, EncodingError> {
        loop {
            let notified = self.available.notify.notified();
            tokio::pin!(notified);
            notified.as_mut().enable();
            if self.closed.load(Ordering::Acquire) {
                return Err(EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::SharedInfrastructure,
                    "encoding worker pool closed while a request waited",
                )));
            }
            let index = {
                let preferred = self
                    .available
                    .preferred
                    .lock()
                    .unwrap_or_else(|poisoned| poisoned.into_inner());
                let mut queue = self
                    .available
                    .queue
                    .lock()
                    .unwrap_or_else(|poisoned| poisoned.into_inner());
                queue
                    .iter()
                    .position(|index| !preferred.contains(index))
                    .and_then(|position| queue.remove(position))
            };
            if let Some(index) = index {
                return Ok(AvailableSlot {
                    available: Arc::clone(&self.available),
                    index,
                });
            }
            tokio::select! {
                biased;
                _ = cancellation.cancelled() => return Err(EncodingError::Cancelled),
                _ = &mut notified => {}
            }
        }
    }

    async fn acquire_preferred_slot(
        &self,
        affinity: WorkerAffinity,
        cancellation: &CancellationToken,
    ) -> Result<AvailableSlot, EncodingError> {
        if affinity.index >= self.slots.len() {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "encoding-worker affinity is outside this pool",
            )));
        }
        let mut reservation =
            PreferredReservation::new(Arc::clone(&self.available), affinity.index)?;
        loop {
            let notified = self.available.notify.notified();
            tokio::pin!(notified);
            notified.as_mut().enable();
            if self.closed.load(Ordering::Acquire) {
                return Err(EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::SharedInfrastructure,
                    "encoding worker pool closed while a preferred request waited",
                )));
            }
            let index = {
                let mut queue = self
                    .available
                    .queue
                    .lock()
                    .unwrap_or_else(|poisoned| poisoned.into_inner());
                queue
                    .iter()
                    .position(|index| *index == affinity.index)
                    .and_then(|position| queue.remove(position))
            };
            if let Some(index) = index {
                reservation.disarm();
                return Ok(AvailableSlot {
                    available: Arc::clone(&self.available),
                    index,
                });
            }
            tokio::select! {
                biased;
                _ = cancellation.cancelled() => return Err(EncodingError::Cancelled),
                _ = &mut notified => {}
            }
        }
    }
}

// ------------------------------------------------------------
// Fixed-Ambient Bounded Pool
// ------------------------------------------------------------

pub(crate) struct FixedAmbientWorkerPool {
    slots: Arc<[Arc<FixedAmbientWorkerSlot>]>,
    available: Arc<AvailableWorkers>,
    lifecycle: Arc<WorkerPoolLifecycle>,
    maximum: usize,
    round_trip_timeout: Duration,
    closed: AtomicBool,
    shutdown: Arc<WorkerPoolShutdown>,
}

impl FixedAmbientWorkerPool {
    pub(crate) fn new(config: FixedAmbientWorkerPoolConfig) -> Self {
        let slots = (0..config.workers)
            .map(|_| {
                Arc::new(FixedAmbientWorkerSlot::new(
                    config.command.clone(),
                    config.max_frame_bytes,
                ))
            })
            .collect::<Vec<_>>()
            .into();
        Self {
            slots,
            available: Arc::new(AvailableWorkers {
                queue: Mutex::new((0..config.workers).collect()),
                preferred: Mutex::new(HashSet::new()),
                notify: Notify::new(),
            }),
            lifecycle: Arc::new(WorkerPoolLifecycle::new()),
            maximum: config.max_frame_bytes,
            round_trip_timeout: config.round_trip_timeout,
            closed: AtomicBool::new(false),
            shutdown: Arc::new(WorkerPoolShutdown {
                started: AtomicBool::new(false),
                result: Mutex::new(None),
                settled: Notify::new(),
            }),
        }
    }

    pub(crate) fn capacity(&self) -> usize {
        self.slots.len()
    }

    pub(crate) fn max_frame_bytes(&self) -> usize {
        self.maximum
    }

    /// A fixed-ambient exchange takes no CPU permit. The exchange is one
    /// synchronous round trip to a worker process that is already bounded by
    /// this pool's own slots, so charging a permit for it would gate the same
    /// work twice and let the narrower of the two budgets decide the run's
    /// preparation throughput. CPU permits stay for real CPU jobs.
    ///
    /// The same argument would apply to the retained exchanges of the other
    /// pool, which still take a permit. They are left alone because no campaign
    /// uses that pool, and narrowing a gate on a path nothing exercises is a
    /// change with no evidence behind it.
    pub(crate) async fn execute(
        &self,
        name_sync: NameEnvSync,
        request: FixedAmbientWorkerRequestEnvelope,
        next_request: Arc<AtomicU64>,
        cancellation: &CancellationToken,
    ) -> Result<FixedAmbientWorkerResponseEnvelope, EncodingError> {
        if self.closed.load(Ordering::Acquire) {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "fixed-ambient worker pool is closed",
            )));
        }
        let slot_lease = self.acquire_slot(cancellation).await?;
        let slot = Arc::clone(&self.slots[slot_lease.index]);
        let Some(execution) = self.lifecycle.begin_fixed_ambient(&slot) else {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "fixed-ambient worker pool closed before request registration",
            )));
        };
        let abandonment = CancellationToken::new();
        let mut guard = ExecutionAbandonmentGuard::new(abandonment.clone());
        let supervisor = tokio::spawn(supervise_fixed_ambient_execution(
            slot,
            slot_lease,
            name_sync,
            request,
            next_request,
            cancellation.clone(),
            abandonment,
            self.round_trip_timeout,
            execution,
        ));
        let result = match supervisor.await {
            Ok(result) => result,
            Err(error) => Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                format!("fixed-ambient worker supervisor failed: {error}"),
            ))),
        };
        guard.disarm();
        result
    }

    pub(crate) async fn shutdown(&self) -> Result<(), EncodingError> {
        self.lifecycle.close();
        self.closed.store(true, Ordering::Release);
        self.available.notify.notify_waiters();
        for slot in self.slots.iter() {
            slot.kill_active();
        }
        if self
            .shutdown
            .started
            .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
            .is_ok()
        {
            let slots = Arc::clone(&self.slots);
            let lifecycle = Arc::clone(&self.lifecycle);
            let shutdown = Arc::clone(&self.shutdown);
            tokio::spawn(async move {
                lifecycle.wait().await;
                let result = shutdown_fixed_ambient_slots(slots).await;
                *shutdown
                    .result
                    .lock()
                    .unwrap_or_else(|poisoned| poisoned.into_inner()) = Some(result);
                shutdown.settled.notify_waiters();
            });
        }
        self.shutdown.wait().await
    }

    async fn acquire_slot(
        &self,
        cancellation: &CancellationToken,
    ) -> Result<AvailableSlot, EncodingError> {
        loop {
            let notified = self.available.notify.notified();
            tokio::pin!(notified);
            notified.as_mut().enable();
            if self.closed.load(Ordering::Acquire) {
                return Err(EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::SharedInfrastructure,
                    "fixed-ambient worker pool closed while a request waited",
                )));
            }
            let index = self
                .available
                .queue
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner())
                .pop_front();
            if let Some(index) = index {
                return Ok(AvailableSlot {
                    available: Arc::clone(&self.available),
                    index,
                });
            }
            tokio::select! {
                biased;
                _ = cancellation.cancelled() => return Err(EncodingError::Cancelled),
                _ = &mut notified => {}
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
async fn supervise_fixed_ambient_execution(
    slot: Arc<FixedAmbientWorkerSlot>,
    slot_lease: AvailableSlot,
    name_sync: NameEnvSync,
    request: FixedAmbientWorkerRequestEnvelope,
    next_request: Arc<AtomicU64>,
    request_cancellation: CancellationToken,
    abandonment: CancellationToken,
    round_trip_timeout: Duration,
    _execution: WorkerExecution,
) -> Result<FixedAmbientWorkerResponseEnvelope, EncodingError> {
    if request_cancellation.is_cancelled() || abandonment.is_cancelled() {
        return Err(EncodingError::Cancelled);
    }
    let execution_slot = Arc::clone(&slot);
    let mut execution = tokio::task::spawn_blocking(move || {
        let result = execution_slot.execute(name_sync, request, &next_request);
        (result, slot_lease)
    });
    let cancelled = async {
        tokio::select! {
            biased;
            _ = request_cancellation.cancelled() => {}
            _ = abandonment.cancelled() => {}
        }
    };
    tokio::pin!(cancelled);
    // A worker that never answers would otherwise hold its pool slot for the
    // whole run. The allowance is far above any healthy exchange, so reaching
    // it means the worker is lost, and the run is told so rather than waiting.
    let expired = tokio::time::sleep(round_trip_timeout);
    tokio::pin!(expired);
    tokio::select! {
        biased;
        _ = &mut cancelled => {
            slot.kill_active();
            let execution_result = (&mut execution).await;
            let cleanup_slot = Arc::clone(&slot);
            let cleanup_failure = Arc::clone(&slot.cleanup_failure);
            let cleanup = tokio::task::spawn_blocking(move || cleanup_slot.shutdown()).await;
            match cleanup {
                Ok(Ok(())) => match execution_result {
                    Err(error) => Err(EncodingError::Failure(encoding_failure(
                        EncodingFailureClass::SharedInfrastructure,
                        format!("fixed-ambient worker failed during cancellation: {error}"),
                    ))),
                    Ok((result, _slot_lease)) => match result {
                        Err(EncodingError::Failure(report))
                            if report.scope() == crate::failure::FailureScope::RunGlobal =>
                        {
                            Err(EncodingError::Failure(report))
                        }
                        _ => Err(EncodingError::Cancelled),
                    },
                },
                Ok(Err(error)) => Err(EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::SharedInfrastructure,
                    error,
                ))),
                Err(error) => {
                    let detail = format!(
                        "fixed-ambient worker cleanup supervisor failed: {error}"
                    );
                    record_cleanup_failure(&cleanup_failure, &detail);
                    Err(EncodingError::Failure(encoding_failure(
                        EncodingFailureClass::SharedInfrastructure,
                        detail,
                    )))
                }
            }
        }
        result = &mut execution => match result {
            Ok((result, _slot_lease)) => result,
            Err(error) => Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                format!("fixed-ambient worker blocking task failed: {error}"),
            ))),
        },
        _ = &mut expired => {
            // Fail closed. The worker is killed and replaced, and the next
            // request on this slot replays the name environment exactly as it
            // does after any other worker loss.
            //
            // The slot lease is held until the replacement is settled. Dropping
            // it earlier returns the slot to the queue while this cleanup is
            // still pending, and a request that took the slot in that window
            // would spawn a worker of its own only for this cleanup to stop it:
            // one wasted Lean spawn and name-environment replay, and a timeout
            // that cannot report until that unrelated exchange has finished.
            // `joined` owns the lease, so nothing can take the slot until the
            // worker this exchange owned is gone.
            slot.kill_active();
            let joined = (&mut execution).await;
            let cleanup_slot = Arc::clone(&slot);
            let cleanup = tokio::task::spawn_blocking(move || cleanup_slot.shutdown()).await;
            drop(joined);
            let detail = match cleanup {
                Ok(Ok(())) => String::new(),
                Ok(Err(error)) => format!("; {error}"),
                Err(error) => format!("; worker replacement supervisor failed: {error}"),
            };
            Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::LocalInfrastructure,
                format!(
                    "fixed-ambient Lean worker did not answer within {} seconds{detail}",
                    round_trip_timeout.as_secs_f64()
                ),
            )))
        }
    }
}

#[allow(clippy::too_many_arguments)]
async fn supervise_worker_execution(
    slot: Arc<WorkerSlot>,
    slot_lease: AvailableSlot,
    cpu: CpuWorkerPermit,
    name_sync: NameEnvSync,
    proposal_sync: ProposalSync,
    w_sync: WLayerSync,
    request: WorkerRequestEnvelope,
    next_request: Arc<AtomicU64>,
    request_cancellation: CancellationToken,
    abandonment: CancellationToken,
    _execution: WorkerExecution,
) -> Result<(WorkerResponseEnvelope, AvailableSlot), EncodingError> {
    if request_cancellation.is_cancelled() || abandonment.is_cancelled() {
        return Err(EncodingError::Cancelled);
    }
    let execution_slot = Arc::clone(&slot);
    let mut execution = tokio::task::spawn_blocking(move || {
        // Capacity belongs to the blocking operation, not to its async waiter.
        // A dropped waiter therefore cannot release either lease early.
        let result =
            execution_slot.execute(name_sync, proposal_sync, w_sync, request, &next_request);
        (result, slot_lease, cpu)
    });
    let cancelled = async {
        tokio::select! {
            biased;
            _ = request_cancellation.cancelled() => {}
            _ = abandonment.cancelled() => {}
        }
    };
    tokio::pin!(cancelled);
    tokio::select! {
        biased;
        _ = &mut cancelled => {
            slot.kill_active();
            let execution_result = (&mut execution).await;
            let cleanup_slot = Arc::clone(&slot);
            let cleanup_failure = Arc::clone(&slot.cleanup_failure);
            let cleanup_result = tokio::task::spawn_blocking(move || cleanup_slot.shutdown()).await;
            match cleanup_result {
                Ok(Err(error)) => Err(EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::SharedInfrastructure,
                    error,
                ))),
                Err(error) => {
                    let detail = format!(
                        "cancelled encoding-worker cleanup supervisor failed: {error}"
                    );
                    record_cleanup_failure(&cleanup_failure, &detail);
                    Err(EncodingError::Failure(encoding_failure(
                        EncodingFailureClass::SharedInfrastructure,
                        detail,
                    )))
                }
                Ok(Ok(())) => match execution_result {
                    Err(error) => Err(EncodingError::Failure(encoding_failure(
                        EncodingFailureClass::SharedInfrastructure,
                        format!("encoding worker supervisor failed during cancellation: {error}"),
                    ))),
                    Ok((result, _slot_lease, _cpu)) => arbitrate_cancelled_execution(result),
                },
            }
        }
        result = &mut execution => match result {
            Ok((result, slot_lease, _cpu)) => {
                result.map(|response| (response, slot_lease))
            }
            Err(error) => Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                format!("encoding worker blocking task failed: {error}"),
            ))),
        }
    }
}

struct ExecutionAbandonmentGuard {
    cancellation: CancellationToken,
    armed: bool,
}

impl ExecutionAbandonmentGuard {
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

impl Drop for ExecutionAbandonmentGuard {
    fn drop(&mut self) {
        if self.armed {
            self.cancellation.cancel();
        }
    }
}

fn arbitrate_cancelled_execution(
    execution: Result<WorkerResponseEnvelope, EncodingError>,
) -> Result<(WorkerResponseEnvelope, AvailableSlot), EncodingError> {
    match execution {
        Err(EncodingError::Failure(report))
            if report.scope() == crate::failure::FailureScope::RunGlobal =>
        {
            Err(EncodingError::Failure(report))
        }
        _ => Err(EncodingError::Cancelled),
    }
}

pub(crate) struct RetainedWorkerResponse {
    response: Option<WorkerResponseEnvelope>,
    slot: Option<Arc<WorkerSlot>>,
    slot_lease: Option<AvailableSlot>,
}

impl RetainedWorkerResponse {
    pub(crate) fn response(&self) -> &WorkerResponseEnvelope {
        self.response
            .as_ref()
            .expect("retained worker response remains available")
    }

    pub(crate) fn accept(mut self) -> WorkerResponseEnvelope {
        self.slot.take();
        self.slot_lease.take();
        self.response
            .take()
            .expect("accepted worker response remains available")
    }

    /// Accept a terminal response and remember its reusable worker frontier.
    pub(crate) fn accept_with_affinity(mut self) -> (WorkerResponseEnvelope, WorkerAffinity) {
        self.slot.take();
        let slot_lease = self
            .slot_lease
            .take()
            .expect("retained worker lease remains available");
        let affinity = WorkerAffinity {
            index: slot_lease.index,
        };
        drop(slot_lease);
        (
            self.response
                .take()
                .expect("accepted worker response remains available"),
            affinity,
        )
    }

    /// Accept this page while retaining its exact worker for the next page.
    pub(crate) fn accept_and_retain_slot(mut self) -> RetainedWorkerSession {
        self.response
            .take()
            .expect("accepted worker response remains available");
        RetainedWorkerSession {
            slot: self.slot.take(),
            slot_lease: self.slot_lease.take(),
        }
    }

    /// Reject this response only after its exact worker is stopped and reaped.
    pub(crate) async fn reject(mut self, error: EncodingError) -> EncodingError {
        let slot = self.slot.take().expect("retained worker remains available");
        let slot_lease = self
            .slot_lease
            .take()
            .expect("retained worker lease remains available");
        reject_retained_parts::<()>(slot, slot_lease, error)
            .await
            .expect_err("retiring a rejected response always returns its error")
    }
}

impl Drop for RetainedWorkerResponse {
    fn drop(&mut self) {
        let (Some(slot), Some(slot_lease)) = (self.slot.take(), self.slot_lease.take()) else {
            return;
        };
        retire_retained_slot(slot, slot_lease);
    }
}

/// One accepted page's exact worker, pinned until the stage terminates.
pub(crate) struct RetainedWorkerSession {
    slot: Option<Arc<WorkerSlot>>,
    slot_lease: Option<AvailableSlot>,
}

impl RetainedWorkerSession {
    fn into_parts(mut self) -> (Arc<WorkerSlot>, AvailableSlot) {
        (
            self.slot.take().expect("retained worker remains available"),
            self.slot_lease
                .take()
                .expect("retained worker lease remains available"),
        )
    }

    /// Stop and reap the pinned worker before returning the supplied error.
    pub(crate) async fn reject(self, error: EncodingError) -> EncodingError {
        let (slot, slot_lease) = self.into_parts();
        reject_retained_parts::<()>(slot, slot_lease, error)
            .await
            .expect_err("retiring a rejected session always returns its error")
    }
}

impl Drop for RetainedWorkerSession {
    fn drop(&mut self) {
        let (Some(slot), Some(slot_lease)) = (self.slot.take(), self.slot_lease.take()) else {
            return;
        };
        retire_retained_slot(slot, slot_lease);
    }
}

fn retire_retained_slot(slot: Arc<WorkerSlot>, slot_lease: AvailableSlot) {
    slot.kill_active();
    match tokio::runtime::Handle::try_current() {
        Ok(runtime) => {
            runtime.spawn(async move {
                let _ =
                    reject_retained_parts::<()>(slot, slot_lease, EncodingError::Cancelled).await;
            });
        }
        Err(_) => {
            let _ = slot.shutdown();
            drop(slot_lease);
        }
    }
}

async fn reject_retained_session<T>(
    session: RetainedWorkerSession,
    error: EncodingError,
) -> Result<T, EncodingError> {
    Err(session.reject(error).await)
}

async fn reject_retained_parts<T>(
    slot: Arc<WorkerSlot>,
    slot_lease: AvailableSlot,
    error: EncodingError,
) -> Result<T, EncodingError> {
    slot.kill_active();
    let cleanup = tokio::task::spawn_blocking(move || {
        let result = slot.shutdown();
        drop(slot_lease);
        result
    })
    .await;
    match cleanup {
        Ok(Ok(())) => Err(error),
        Ok(Err(detail)) => Err(EncodingError::Failure(encoding_failure(
            EncodingFailureClass::SharedInfrastructure,
            detail,
        ))),
        Err(join_error) => Err(EncodingError::Failure(encoding_failure(
            EncodingFailureClass::SharedInfrastructure,
            format!("retained encoding-worker cleanup supervisor failed: {join_error}"),
        ))),
    }
}

impl WorkerPoolShutdown {
    async fn wait(&self) -> Result<(), EncodingError> {
        loop {
            let notified = self.settled.notified();
            tokio::pin!(notified);
            notified.as_mut().enable();
            if let Some(result) = self
                .result
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner())
                .clone()
            {
                return result;
            }
            notified.await;
        }
    }
}

async fn shutdown_worker_slots(slots: Arc<[Arc<WorkerSlot>]>) -> Result<(), EncodingError> {
    for slot in slots.iter() {
        slot.kill_active();
    }
    let mut tasks = Vec::new();
    for slot in slots.iter() {
        let slot = Arc::clone(slot);
        tasks.push(tokio::task::spawn_blocking(move || slot.shutdown()));
    }
    let mut errors = Vec::new();
    for task in tasks {
        match task.await {
            Ok(Ok(())) => {}
            Ok(Err(error)) => errors.push(error),
            Err(error) => errors.push(format!(
                "Lean encoding-worker cleanup supervisor failed: {error}"
            )),
        }
    }
    if errors.is_empty() {
        Ok(())
    } else {
        Err(EncodingError::Failure(encoding_failure(
            EncodingFailureClass::SharedInfrastructure,
            format!(
                "persistent Lean encoding-worker cleanup failed: {}",
                errors.join("; ")
            ),
        )))
    }
}

async fn shutdown_fixed_ambient_slots(
    slots: Arc<[Arc<FixedAmbientWorkerSlot>]>,
) -> Result<(), EncodingError> {
    for slot in slots.iter() {
        slot.kill_active();
    }
    let mut tasks = Vec::new();
    for slot in slots.iter() {
        let slot = Arc::clone(slot);
        tasks.push(tokio::task::spawn_blocking(move || slot.shutdown()));
    }
    let mut errors = Vec::new();
    for task in tasks {
        match task.await {
            Ok(Ok(())) => {}
            Ok(Err(error)) => errors.push(error),
            Err(error) => errors.push(format!(
                "fixed-ambient worker cleanup supervisor failed: {error}"
            )),
        }
    }
    if errors.is_empty() {
        Ok(())
    } else {
        Err(EncodingError::Failure(encoding_failure(
            EncodingFailureClass::SharedInfrastructure,
            format!(
                "persistent fixed-ambient worker cleanup failed: {}",
                errors.join("; ")
            ),
        )))
    }
}

struct AvailableSlot {
    available: Arc<AvailableWorkers>,
    index: usize,
}

impl Drop for AvailableSlot {
    fn drop(&mut self) {
        self.available
            .queue
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .push_back(self.index);
        self.available.notify.notify_waiters();
    }
}

// ------------------------------------------------------------
// Persistent Process Slot
// ------------------------------------------------------------

struct FixedAmbientWorkerSlot {
    command: FixedAmbientWorkerCommand,
    maximum: usize,
    process: Mutex<Option<WorkerProcess>>,
    active_pid: AtomicU32,
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    active_tree: Mutex<Option<ProcessTreeHandle>>,
    cleanup_failure: Arc<Mutex<Option<String>>>,
    cancel_requested: AtomicBool,
}

impl FixedAmbientWorkerSlot {
    fn new(command: FixedAmbientWorkerCommand, maximum: usize) -> Self {
        Self {
            command,
            maximum,
            process: Mutex::new(None),
            active_pid: AtomicU32::new(0),
            #[cfg(any(target_os = "macos", target_os = "linux"))]
            active_tree: Mutex::new(None),
            cleanup_failure: Arc::new(Mutex::new(None)),
            cancel_requested: AtomicBool::new(false),
        }
    }

    fn execute(
        &self,
        name_sync: NameEnvSync,
        mut request: FixedAmbientWorkerRequestEnvelope,
        next_request: &AtomicU64,
    ) -> Result<FixedAmbientWorkerResponseEnvelope, EncodingError> {
        let mut process = self
            .process
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        if process.is_none() {
            *process = Some(WorkerProcess::spawn(
                &self.command.as_encoding_command(),
                Arc::clone(&self.cleanup_failure),
            )?);
        }
        let child = process.as_mut().expect("worker was initialized");
        self.active_pid.store(child.pid(), Ordering::Release);
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        {
            *self
                .active_tree
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner()) =
                Some(child.process_tree.handle.clone());
        }
        if self.cancel_requested.load(Ordering::Acquire) {
            child.kill_owned_tree();
        }
        let result = child
            .synchronize_fixed_ambient(&name_sync, &request, next_request, self.maximum)
            .and_then(|()| {
                request.name_env_revision = child.name_env_revision;
                child.exchange_fixed_ambient(&request, self.maximum)
            })
            .and_then(|response| {
                validate_fixed_ambient_response_envelope(&request, &response)?;
                Ok(response)
            });
        self.active_pid.store(0, Ordering::Release);
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        {
            self.active_tree
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner())
                .take();
        }
        if result.is_err() {
            let cleanup = process
                .take()
                .expect("completed fixed-ambient worker remains owned")
                .stop();
            if let Err(error) = cleanup {
                return Err(EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::SharedInfrastructure,
                    error,
                )));
            }
        }
        result
    }

    fn kill_active(&self) {
        self.cancel_requested.store(true, Ordering::Release);
        let pid = self.active_pid.load(Ordering::Acquire);
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        if let Some(tree) = self
            .active_tree
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .as_ref()
        {
            tree.signal_all(libc::SIGKILL, &mut Vec::new());
        }
        if pid != 0 {
            kill_process_group(pid);
        }
    }

    fn begin_request(&self) {
        self.cancel_requested.store(false, Ordering::Release);
    }

    fn shutdown(&self) -> Result<(), String> {
        let mut process = self
            .process
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        if let Some(mut child) = process.take() {
            let _ = child.stop();
        }
        self.active_pid.store(0, Ordering::Release);
        match self
            .cleanup_failure
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .clone()
        {
            Some(error) => Err(error),
            None => Ok(()),
        }
    }
}

struct WorkerSlot {
    command: EncodingWorkerCommand,
    maximum: usize,
    process: Mutex<Option<WorkerProcess>>,
    active_pid: AtomicU32,
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    active_tree: Mutex<Option<ProcessTreeHandle>>,
    cleanup_failure: Arc<Mutex<Option<String>>>,
    cancel_requested: AtomicBool,
}

impl WorkerSlot {
    fn new(command: EncodingWorkerCommand, maximum: usize) -> Self {
        Self {
            command,
            maximum,
            process: Mutex::new(None),
            active_pid: AtomicU32::new(0),
            #[cfg(any(target_os = "macos", target_os = "linux"))]
            active_tree: Mutex::new(None),
            cleanup_failure: Arc::new(Mutex::new(None)),
            cancel_requested: AtomicBool::new(false),
        }
    }

    fn execute(
        &self,
        name_sync: NameEnvSync,
        proposal_sync: ProposalSync,
        w_sync: WLayerSync,
        mut request: WorkerRequestEnvelope,
        next_request: &AtomicU64,
    ) -> Result<WorkerResponseEnvelope, EncodingError> {
        let mut process = self
            .process
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        if process
            .as_ref()
            .is_some_and(|child| child.proposal_page_count > proposal_sync.authority_page_count)
        {
            let cleanup = process
                .take()
                .expect("speculative worker process remains owned")
                .stop();
            if let Err(error) = cleanup {
                return Err(EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::SharedInfrastructure,
                    error,
                )));
            }
        }
        if process.is_none() {
            *process = Some(WorkerProcess::spawn(
                &self.command,
                Arc::clone(&self.cleanup_failure),
            )?);
        }
        let child = process.as_mut().expect("worker was initialized");
        self.active_pid.store(child.pid(), Ordering::Release);
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        {
            *self
                .active_tree
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner()) =
                Some(child.process_tree.handle.clone());
        }
        if self.cancel_requested.load(Ordering::Acquire) {
            child.kill_owned_tree();
        }
        let result = child
            .synchronize(
                &name_sync,
                &proposal_sync,
                &w_sync,
                &request,
                next_request,
                self.maximum,
            )
            .and_then(|()| {
                // An older request can reach a worker already synchronized to
                // a later append-only revision.  Render under that extension;
                // the caller validates all referenced mappings.
                request.name_env_revision = child.name_env_revision;
                request.proposal_revision = child.proposal_revision;
                child.exchange(&request, self.maximum)
            })
            .and_then(|response| {
                validate_logical_response_envelope(&request, &response)?;
                if request.operation == WorkerOperation::RegisterReferenceProposal
                    && response.status == WorkerResponseStatus::Ok
                {
                    child.record_live_proposal_page(&request, &response)?;
                }
                if request.operation == WorkerOperation::EnsureWLayer
                    && response.status == WorkerResponseStatus::Ok
                {
                    child.record_live_w_layer(&request, &response)?;
                }
                Ok(response)
            });
        self.active_pid.store(0, Ordering::Release);
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        {
            self.active_tree
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner())
                .take();
        }
        if result.is_err()
            || result.as_ref().is_ok_and(|response| {
                matches!(
                    request.operation,
                    WorkerOperation::RegisterReferenceProposal | WorkerOperation::EnsureWLayer
                ) && response.status == WorkerResponseStatus::Error
            })
        {
            let cleanup = process
                .take()
                .expect("completed worker process remains owned")
                .stop();
            if let Err(error) = cleanup {
                return Err(EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::SharedInfrastructure,
                    error,
                )));
            }
        }
        result
    }

    fn kill_active(&self) {
        self.cancel_requested.store(true, Ordering::Release);
        let pid = self.active_pid.load(Ordering::Acquire);
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        if let Some(tree) = self
            .active_tree
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .as_ref()
        {
            tree.signal_all(libc::SIGKILL, &mut Vec::new());
        }
        if pid != 0 {
            kill_process_group(pid);
        }
    }

    fn begin_request(&self) {
        self.cancel_requested.store(false, Ordering::Release);
    }

    fn shutdown(&self) -> Result<(), String> {
        let mut process = self
            .process
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        if let Some(mut child) = process.take() {
            let _ = child.stop();
        }
        self.active_pid.store(0, Ordering::Release);
        match self
            .cleanup_failure
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .clone()
        {
            Some(error) => Err(error),
            None => Ok(()),
        }
    }
}

struct WorkerProcess {
    child: Child,
    stdin: Option<ChildStdin>,
    stdout: Option<ChildStdout>,
    stderr_capture: Option<StderrCapture>,
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    process_tree: ProcessTreeObserver,
    cleanup_failure: Arc<Mutex<Option<String>>>,
    name_env_revision: NameEnvRevision,
    proposal_revision: ProposalRevision,
    proposal_cursor: u64,
    proposal_page_count: usize,
    proposal_realization: Option<ProposalRealization>,
    w_layer_count: usize,
}

impl WorkerProcess {
    fn spawn(
        command: &EncodingWorkerCommand,
        cleanup_failure: Arc<Mutex<Option<String>>>,
    ) -> Result<Self, EncodingError> {
        #[cfg(not(any(target_os = "macos", target_os = "linux")))]
        return Err(EncodingError::Failure(encoding_failure(
            EncodingFailureClass::SharedInfrastructure,
            "owned Lean encoding-worker process-tree supervision is unavailable on this platform",
        )));

        let mut child_command = Command::new(&command.executable);
        child_command
            .args(command.arguments.iter())
            .current_dir(&command.current_directory)
            // A worker's own thread count is pinned rather than inherited: a
            // pool already provides the run's parallelism, and threads inside
            // each worker would compete with the concurrent checks for the
            // same cores while an inherited value would make one run's timing
            // depend on the shell that started it.
            .env("LEAN_NUM_THREADS", LEAN_WORKER_THREADS.to_string())
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        configure_process_group(&mut child_command);
        let mut child = child_command.spawn().map_err(|error| {
            EncodingError::Failure(encoding_failure(
                EncodingFailureClass::Process,
                format!("start persistent Lean encoding worker: {error}"),
            ))
        })?;
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        let mut process_tree = match ProcessTreeObserver::start(child.id()) {
            Ok(process_tree) => process_tree,
            Err(error) => {
                let mut cleanup_errors = Vec::new();
                if let Err(signal_error) = signal_group(child.id(), libc::SIGKILL)
                    && signal_error.raw_os_error() != Some(libc::ESRCH)
                {
                    cleanup_errors.push(format!("kill unobserved worker group: {signal_error}"));
                }
                if let Err(kill_error) = child.kill()
                    && kill_error.kind() != std::io::ErrorKind::InvalidInput
                {
                    cleanup_errors.push(format!("kill unobserved worker child: {kill_error}"));
                }
                if let Err(wait_error) = child.wait() {
                    cleanup_errors.push(format!("reap unobserved worker child: {wait_error}"));
                }
                let detail = if cleanup_errors.is_empty() {
                    format!(
                        "start persistent Lean worker process-tree observer: {error}; descendant ownership could not be verified"
                    )
                } else {
                    format!(
                        "start persistent Lean worker process-tree observer: {error}; descendant ownership could not be verified; {}",
                        cleanup_errors.join("; ")
                    )
                };
                record_cleanup_failure(&cleanup_failure, &detail);
                return Err(EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::SharedInfrastructure,
                    detail,
                )));
            }
        };
        let stdin = child.stdin.take().expect("piped worker stdin exists");
        let stdout = child.stdout.take().expect("piped worker stdout exists");
        let stderr = child.stderr.take().expect("piped worker stderr exists");
        let stderr_capture = match StderrCapture::start(stderr) {
            Ok(capture) => capture,
            Err(error) => {
                #[cfg(any(target_os = "macos", target_os = "linux"))]
                {
                    let mut cleanup_errors = vec![error];
                    process_tree
                        .handle
                        .signal_all(libc::SIGKILL, &mut cleanup_errors);
                    if let Err(kill_error) = child.kill()
                        && kill_error.kind() != std::io::ErrorKind::InvalidInput
                    {
                        cleanup_errors.push(format!(
                            "kill worker after stderr-capture startup failure: {kill_error}"
                        ));
                    }
                    drop(stdin);
                    drop(stdout);
                    process_tree.stop_owned_tree(&mut child, &mut cleanup_errors);
                    let detail = cleanup_errors.join("; ");
                    record_cleanup_failure(&cleanup_failure, &detail);
                    return Err(EncodingError::Failure(encoding_failure(
                        EncodingFailureClass::SharedInfrastructure,
                        detail,
                    )));
                }
                #[cfg(not(any(target_os = "macos", target_os = "linux")))]
                return Err(EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::SharedInfrastructure,
                    error,
                )));
            }
        };
        Ok(Self {
            child,
            stdin: Some(stdin),
            stdout: Some(stdout),
            stderr_capture: Some(stderr_capture),
            #[cfg(any(target_os = "macos", target_os = "linux"))]
            process_tree,
            cleanup_failure,
            name_env_revision: NameEnvRevision::INITIAL,
            proposal_revision: ProposalRevision::INITIAL,
            proposal_cursor: 0,
            proposal_page_count: 0,
            proposal_realization: None,
            w_layer_count: 0,
        })
    }

    fn pid(&self) -> u32 {
        self.child.id()
    }

    fn exchange(
        &mut self,
        request: &WorkerRequestEnvelope,
        maximum: usize,
    ) -> Result<WorkerResponseEnvelope, EncodingError> {
        write_frame(
            self.stdin.as_mut().expect("live worker stdin exists"),
            request,
            maximum,
        )
        .map_err(|error| {
            let class = if error.kind() == std::io::ErrorKind::InvalidData {
                EncodingFailureClass::ProtocolIncompatibility
            } else {
                EncodingFailureClass::Process
            };
            EncodingError::Failure(encoding_failure(
                class,
                format!("write encoding-worker request: {error}"),
            ))
        })?;
        read_frame(
            self.stdout.as_mut().expect("live worker stdout exists"),
            maximum,
        )
        .map_err(|error| {
            let class = if error.kind() == std::io::ErrorKind::InvalidData {
                EncodingFailureClass::MalformedResponse
            } else {
                EncodingFailureClass::Process
            };
            EncodingError::Failure(encoding_failure(
                class,
                format!("read encoding-worker response: {error}"),
            ))
        })
    }

    fn exchange_fixed_ambient(
        &mut self,
        request: &FixedAmbientWorkerRequestEnvelope,
        maximum: usize,
    ) -> Result<FixedAmbientWorkerResponseEnvelope, EncodingError> {
        write_frame(
            self.stdin.as_mut().expect("live worker stdin exists"),
            request,
            maximum,
        )
        .map_err(|error| {
            let class = if error.kind() == std::io::ErrorKind::InvalidData {
                EncodingFailureClass::ProtocolIncompatibility
            } else {
                EncodingFailureClass::Process
            };
            EncodingError::Failure(encoding_failure(
                class,
                format!("write fixed-ambient worker request: {error}"),
            ))
        })?;
        read_frame(
            self.stdout.as_mut().expect("live worker stdout exists"),
            maximum,
        )
        .map_err(|error| {
            let class = if error.kind() == std::io::ErrorKind::InvalidData {
                EncodingFailureClass::ProtocolIncompatibility
            } else {
                EncodingFailureClass::Process
            };
            EncodingError::Failure(encoding_failure(
                class,
                format!("read fixed-ambient worker response: {error}"),
            ))
        })
    }

    fn synchronize_fixed_ambient(
        &mut self,
        name_sync: &NameEnvSync,
        logical_request: &FixedAmbientWorkerRequestEnvelope,
        next_request: &AtomicU64,
        maximum: usize,
    ) -> Result<(), EncodingError> {
        for delta in name_sync.deltas.iter() {
            if delta.revision <= self.name_env_revision {
                continue;
            }
            if delta.base_revision != self.name_env_revision {
                return Err(EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::SharedInfrastructure,
                    "fixed-ambient worker cannot replay a noncontiguous NameEnv delta",
                )));
            }
            let extension = fixed_ambient_extension_request(logical_request, delta, next_request)?;
            let response = self.exchange_fixed_ambient(&extension, maximum)?;
            validate_fixed_ambient_extension_response(&extension, delta, &response)?;
            self.name_env_revision = delta.revision;
        }
        if self.name_env_revision < name_sync.target_revision
            || logical_request.name_env_revision != name_sync.target_revision
        {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "fixed-ambient worker did not reach the requested NameEnv revision",
            )));
        }
        Ok(())
    }

    fn synchronize(
        &mut self,
        name_sync: &NameEnvSync,
        proposal_sync: &ProposalSync,
        w_sync: &WLayerSync,
        logical_request: &WorkerRequestEnvelope,
        next_request: &AtomicU64,
        maximum: usize,
    ) -> Result<(), EncodingError> {
        if self
            .proposal_realization
            .is_some_and(|realization| realization != proposal_sync.realization)
        {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "encoding worker cannot switch proposal realizations",
            )));
        }
        for delta in name_sync.deltas.iter() {
            if delta.revision <= self.name_env_revision {
                continue;
            }
            if delta.base_revision != self.name_env_revision {
                return Err(EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::SharedInfrastructure,
                    "encoding worker cannot replay a noncontiguous NameEnv delta",
                )));
            }
            let extension =
                extension_request(logical_request, delta, self.proposal_revision, next_request)?;
            let response = self.exchange(&extension, maximum)?;
            validate_extension_response(&extension, delta, &response)?;
            self.name_env_revision = delta.revision;
        }
        if self.name_env_revision < name_sync.target_revision
            || logical_request.name_env_revision != name_sync.target_revision
        {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "encoding worker did not reach the requested NameEnv revision",
            )));
        }
        for (page_index, delta) in proposal_sync.deltas.iter().enumerate() {
            if page_index < self.proposal_page_count {
                continue;
            }
            if page_index != self.proposal_page_count
                || delta.realization != proposal_sync.realization
                || delta.base_revision != self.proposal_revision
                || delta.cursor != self.proposal_cursor
            {
                return Err(EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::SharedInfrastructure,
                    "encoding worker cannot replay a noncontiguous proposal page",
                )));
            }
            let registration =
                proposal_request(logical_request, delta, self.name_env_revision, next_request)?;
            let response = self.exchange(&registration, maximum)?;
            validate_proposal_response(&registration, delta, &response)?;
            self.proposal_revision = delta.revision;
            self.proposal_cursor = if delta.complete { 0 } else { delta.next_cursor };
            self.proposal_page_count += 1;
            self.proposal_realization = Some(delta.realization);
        }
        if self.proposal_revision < proposal_sync.target_revision
            || self.proposal_page_count < proposal_sync.target_page_count
            || logical_request.proposal_revision != proposal_sync.target_revision
        {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "encoding worker did not reach the requested proposal revision",
            )));
        }
        for entry in w_sync.entries.iter().skip(self.w_layer_count) {
            if usize::try_from(entry.index).ok() != Some(self.w_layer_count) {
                return Err(EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::SharedInfrastructure,
                    "encoding worker cannot replay a noncontiguous W-layer prefix",
                )));
            }
            let registration = w_layer_request(
                logical_request,
                entry.index,
                self.name_env_revision,
                self.proposal_revision,
                next_request,
            )?;
            let response = self.exchange(&registration, maximum)?;
            validate_w_layer_replay_response(&registration, entry, &response)?;
            self.w_layer_count += 1;
        }
        if self.w_layer_count < w_sync.target_count() {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "encoding worker did not reach the requested W-layer prefix",
            )));
        }
        Ok(())
    }

    fn record_live_proposal_page(
        &mut self,
        request: &WorkerRequestEnvelope,
        response: &WorkerResponseEnvelope,
    ) -> Result<(), EncodingError> {
        let requested: ProposalPageRequest = serde_json::from_value(request.payload.clone())
            .map_err(|error| {
                EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::ProtocolIncompatibility,
                    format!("decode reference-proposal page request: {error}"),
                ))
            })?;
        let page: ProposalPageResponse =
            serde_json::from_value(response.payload.clone()).map_err(|error| {
                EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::ProtocolIncompatibility,
                    format!("decode reference-proposal page response: {error}"),
                ))
            })?;
        let expected_revision = if page.complete {
            self.proposal_revision.successor().ok_or_else(|| {
                EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::SharedInfrastructure,
                    "proposal revision space exhausted",
                ))
            })?
        } else {
            self.proposal_revision
        };
        let Some(realization) = ProposalRealization::from_wire(
            &requested.realization_id,
            requested.realization_version,
        ) else {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::ProtocolIncompatibility,
                "encoding worker request contains an unknown proposal realization",
            )));
        };
        if self
            .proposal_realization
            .is_some_and(|existing| existing != realization)
            || requested.version != PROPOSAL_PAGE_PROTOCOL_VERSION
            || page.realization_id != requested.realization_id
            || page.realization_version != requested.realization_version
            || page.version != requested.version
            || page.stage != requested.stage
            || requested.cursor != self.proposal_cursor
            || page.cursor != requested.cursor
            || page.next_cursor < page.cursor
            || (!page.complete && page.next_cursor == page.cursor)
            || response.proposal_revision != expected_revision
        {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "encoding worker returned an inconsistent proposal page",
            )));
        }
        self.proposal_revision = response.proposal_revision;
        self.proposal_cursor = if page.complete { 0 } else { page.next_cursor };
        self.proposal_page_count += 1;
        self.proposal_realization = Some(realization);
        Ok(())
    }

    fn record_live_w_layer(
        &mut self,
        request: &WorkerRequestEnvelope,
        response: &WorkerResponseEnvelope,
    ) -> Result<(), EncodingError> {
        let requested: WLayerRequest =
            serde_json::from_value(request.payload.clone()).map_err(|error| {
                EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::ProtocolIncompatibility,
                    format!("decode W-layer request: {error}"),
                ))
            })?;
        let returned: WLayerResponseIndex = serde_json::from_value(response.payload.clone())
            .map_err(|error| {
                EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::MalformedResponse,
                    format!("decode W-layer response index: {error}"),
                ))
            })?;
        if usize::try_from(requested.index).ok() != Some(self.w_layer_count)
            || returned.index != requested.index
        {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "encoding worker returned a noncontiguous W-layer registration",
            )));
        }
        self.w_layer_count += 1;
        Ok(())
    }

    fn kill_owned_tree(&self) {
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        self.process_tree
            .handle
            .signal_all(libc::SIGKILL, &mut Vec::new());
        #[cfg(not(any(target_os = "macos", target_os = "linux")))]
        kill_process_group(self.child.id());
    }

    fn stop(&mut self) -> Result<(), String> {
        if self.stdin.is_none() && self.stdout.is_none() && self.stderr_capture.is_none() {
            return Ok(());
        }
        let mut errors = Vec::new();
        self.kill_owned_tree();
        if let Err(error) = self.child.kill()
            && error.kind() != std::io::ErrorKind::InvalidInput
        {
            errors.push(format!("kill direct Lean encoding worker: {error}"));
        }
        self.stdin.take();
        self.stdout.take();
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        self.process_tree
            .stop_owned_tree(&mut self.child, &mut errors);
        #[cfg(not(any(target_os = "macos", target_os = "linux")))]
        if let Err(error) = self.child.wait() {
            errors.push(format!("reap direct Lean encoding worker: {error}"));
        }
        if let Some(capture) = self.stderr_capture.take()
            && let Err(error) = capture.finish()
        {
            errors.push(error);
        }
        if errors.is_empty() {
            return Ok(());
        }
        let error = errors.join("; ");
        record_cleanup_failure(&self.cleanup_failure, &error);
        Err(error)
    }
}

fn record_cleanup_failure(target: &Mutex<Option<String>>, error: &str) {
    let mut recorded = target
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    match recorded.as_mut() {
        Some(previous) if previous != error => {
            previous.push_str("; ");
            previous.push_str(error);
        }
        Some(_) => {}
        None => *recorded = Some(error.to_string()),
    }
}

fn validate_logical_response_envelope(
    request: &WorkerRequestEnvelope,
    response: &WorkerResponseEnvelope,
) -> Result<(), EncodingError> {
    if response.format_version != WORKER_FORMAT_VERSION
        || response.semantic_version != request.semantic_version
        || response.encoding_version != request.encoding_version
        || response.task_canonical_id != request.task_canonical_id
        || response.task_module != request.task_module
        || response.task_namespace != request.task_namespace
        || response.task_source_sha256 != request.task_source_sha256
        || response.request_id != request.request_id
        || response.context_id != request.context_id
        || response.operation != request.operation
        || response.request_name_env_revision != request.name_env_revision
        || response.name_env_revision != request.name_env_revision
        || response.request_proposal_revision != request.proposal_revision
    {
        return Err(EncodingError::Failure(encoding_failure(
            EncodingFailureClass::SharedInfrastructure,
            "encoding worker returned a response for a different logical request",
        )));
    }
    let proposal_revision_valid = if request.operation == WorkerOperation::RegisterReferenceProposal
    {
        if response.status == WorkerResponseStatus::Ok {
            response.proposal_revision == request.proposal_revision
                || response.proposal_revision
                    == request.proposal_revision.successor().ok_or_else(|| {
                        EncodingError::Failure(encoding_failure(
                            EncodingFailureClass::SharedInfrastructure,
                            "proposal revision space exhausted",
                        ))
                    })?
        } else {
            response.proposal_revision == request.proposal_revision
        }
    } else {
        response.proposal_revision == request.proposal_revision
    };
    if !proposal_revision_valid {
        return Err(EncodingError::Failure(encoding_failure(
            EncodingFailureClass::SharedInfrastructure,
            "encoding worker returned an invalid proposal revision",
        )));
    }
    Ok(())
}

pub(crate) fn validate_fixed_ambient_response_envelope(
    request: &FixedAmbientWorkerRequestEnvelope,
    response: &FixedAmbientWorkerResponseEnvelope,
) -> Result<(), EncodingError> {
    let expected_task = FixedAmbientWorkerTaskIdentity {
        canonical_id: request.task_canonical_id.clone(),
        module: request.task_module.clone(),
        namespace: request.task_namespace.clone(),
        source_sha256: request.task_source_sha256.clone(),
    };
    let expected_revision = if request.operation == FixedAmbientWorkerOperation::ExtendNameEnv
        && response.status == WorkerResponseStatus::Ok
    {
        request.name_env_revision.get().checked_add(1)
    } else {
        Some(request.name_env_revision.get())
    };
    // A frame the worker never bound to a registered task echoes null for
    // both identities. Only an error frame may take that shape; an `ok` frame
    // always names the task it ran under.
    let identities_echoed = match &response.task_identity {
        Some(identity) => {
            *identity == expected_task && response.scope_identity == request.scope_identity
        }
        None => response.status == WorkerResponseStatus::Error && response.scope_identity.is_null(),
    };
    if !identities_echoed
        || response.format_version != FIXED_AMBIENT_WORKER_FORMAT_VERSION
        || response.semantic_version != request.semantic_version
        || response.encoding_version != request.encoding_version
        || response.request_id != request.request_id
        || response.operation != request.operation
        || response.request_name_env_revision != request.name_env_revision
        || expected_revision != Some(response.name_env_revision.get())
        || (response.status == WorkerResponseStatus::Ok && response.error.is_some())
        || (response.status == WorkerResponseStatus::Error && response.error.is_none())
        || (response.status == WorkerResponseStatus::Error && !response.payload.is_null())
    {
        return Err(EncodingError::Failure(encoding_failure(
            EncodingFailureClass::SharedInfrastructure,
            "fixed-ambient worker returned a response for a different logical request",
        )));
    }
    Ok(())
}

fn fixed_ambient_extension_request(
    logical_request: &FixedAmbientWorkerRequestEnvelope,
    delta: &NameEnvDelta,
    next_request: &AtomicU64,
) -> Result<FixedAmbientWorkerRequestEnvelope, EncodingError> {
    let request_id = next_request
        .fetch_update(Ordering::AcqRel, Ordering::Acquire, |current| {
            current.checked_add(1)
        })
        .map_err(|_| {
            EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "fixed-ambient worker request identity space exhausted",
            ))
        })?;
    Ok(FixedAmbientWorkerRequestEnvelope {
        format_version: FIXED_AMBIENT_WORKER_FORMAT_VERSION,
        semantic_version: logical_request.semantic_version,
        encoding_version: logical_request.encoding_version,
        task_canonical_id: logical_request.task_canonical_id.clone(),
        task_module: logical_request.task_module.clone(),
        task_namespace: logical_request.task_namespace.clone(),
        task_source_sha256: logical_request.task_source_sha256.clone(),
        scope_identity: logical_request.scope_identity.clone(),
        request_id,
        name_env_revision: delta.base_revision,
        operation: FixedAmbientWorkerOperation::ExtendNameEnv,
        payload: serde_json::json!({
            "next_revision": delta.revision,
            "relations": delta.relations.iter().map(FixedAmbientNameBinding::from).collect::<Vec<_>>(),
            "constants": delta.constants.iter().map(FixedAmbientNameBinding::from).collect::<Vec<_>>(),
        }),
    })
}

fn validate_fixed_ambient_extension_response(
    request: &FixedAmbientWorkerRequestEnvelope,
    delta: &NameEnvDelta,
    response: &FixedAmbientWorkerResponseEnvelope,
) -> Result<(), EncodingError> {
    validate_fixed_ambient_response_envelope(request, response)?;
    if response.operation != FixedAmbientWorkerOperation::ExtendNameEnv
        || response.status != WorkerResponseStatus::Ok
        || response.request_name_env_revision != delta.base_revision
        || response.name_env_revision != delta.revision
    {
        return Err(EncodingError::Failure(encoding_failure(
            EncodingFailureClass::SharedInfrastructure,
            "fixed-ambient worker returned an invalid NameEnv extension",
        )));
    }
    let echoed: FixedAmbientExtensionEcho = serde_json::from_value(response.payload.clone())
        .map_err(|error| {
            EncodingError::Failure(encoding_failure(
                EncodingFailureClass::ProtocolIncompatibility,
                format!("decode fixed-ambient NameEnv extension: {error}"),
            ))
        })?;
    let expected_relations = delta
        .relations
        .iter()
        .filter(|mapping| mapping.kind == NameMappingKind::Relation)
        .map(FixedAmbientNameBinding::from)
        .collect::<Vec<_>>();
    let expected_constants = delta
        .constants
        .iter()
        .filter(|mapping| mapping.kind == NameMappingKind::Constant)
        .map(FixedAmbientNameBinding::from)
        .collect::<Vec<_>>();
    if echoed.relations != expected_relations || echoed.constants != expected_constants {
        return Err(EncodingError::Failure(encoding_failure(
            EncodingFailureClass::SharedInfrastructure,
            "fixed-ambient worker echoed different NameEnv assignments",
        )));
    }
    Ok(())
}

fn extension_request(
    logical_request: &WorkerRequestEnvelope,
    delta: &NameEnvDelta,
    proposal_revision: ProposalRevision,
    next_request: &AtomicU64,
) -> Result<WorkerRequestEnvelope, EncodingError> {
    let request_id = next_request
        .fetch_update(Ordering::AcqRel, Ordering::Acquire, |current| {
            current.checked_add(1)
        })
        .map_err(|_| {
            EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "encoding-worker request identity space exhausted",
            ))
        })?;
    Ok(WorkerRequestEnvelope {
        format_version: WORKER_FORMAT_VERSION,
        semantic_version: logical_request.semantic_version,
        encoding_version: logical_request.encoding_version,
        task_canonical_id: logical_request.task_canonical_id.clone(),
        task_module: logical_request.task_module.clone(),
        task_namespace: logical_request.task_namespace.clone(),
        task_source_sha256: logical_request.task_source_sha256.clone(),
        request_id,
        context_id: logical_request.context_id.clone(),
        name_env_revision: delta.base_revision,
        proposal_revision,
        operation: WorkerOperation::ExtendNameEnv,
        payload: serde_json::json!({
            "next_revision": delta.revision,
            "relations": delta.relations.iter().map(NameBinding::from).collect::<Vec<_>>(),
            "constants": delta.constants.iter().map(NameBinding::from).collect::<Vec<_>>(),
        }),
    })
}

fn validate_extension_response(
    request: &WorkerRequestEnvelope,
    delta: &NameEnvDelta,
    response: &WorkerResponseEnvelope,
) -> Result<(), EncodingError> {
    if response.format_version != WORKER_FORMAT_VERSION
        || response.semantic_version != request.semantic_version
        || response.encoding_version != request.encoding_version
        || response.task_canonical_id != request.task_canonical_id
        || response.task_module != request.task_module
        || response.task_namespace != request.task_namespace
        || response.task_source_sha256 != request.task_source_sha256
        || response.request_id != request.request_id
        || response.context_id != request.context_id
        || response.operation != WorkerOperation::ExtendNameEnv
        || response.request_name_env_revision != delta.base_revision
        || response.name_env_revision != delta.revision
        || response.request_proposal_revision != request.proposal_revision
        || response.proposal_revision != request.proposal_revision
        || response.status != WorkerResponseStatus::Ok
    {
        return Err(EncodingError::Failure(encoding_failure(
            EncodingFailureClass::SharedInfrastructure,
            "encoding worker returned an invalid NameEnv-extension response",
        )));
    }
    let echoed: ExtensionEcho =
        serde_json::from_value(response.payload.clone()).map_err(|error| {
            EncodingError::Failure(encoding_failure(
                EncodingFailureClass::ProtocolIncompatibility,
                format!("decode NameEnv-extension response: {error}"),
            ))
        })?;
    let expected_relations = delta
        .relations
        .iter()
        .filter(|mapping| mapping.kind == NameMappingKind::Relation)
        .map(NameBinding::from)
        .collect::<Vec<_>>();
    let expected_constants = delta
        .constants
        .iter()
        .filter(|mapping| mapping.kind == NameMappingKind::Constant)
        .map(NameBinding::from)
        .collect::<Vec<_>>();
    if echoed.relations != expected_relations || echoed.constants != expected_constants {
        return Err(EncodingError::Failure(encoding_failure(
            EncodingFailureClass::SharedInfrastructure,
            "encoding worker echoed different NameEnv assignments",
        )));
    }
    Ok(())
}

#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct FixedAmbientExtensionEcho {
    relations: Vec<FixedAmbientNameBinding>,
    constants: Vec<FixedAmbientNameBinding>,
}

#[derive(serde::Deserialize)]
struct ExtensionEcho {
    relations: Vec<NameBinding>,
    constants: Vec<NameBinding>,
}

#[derive(serde::Deserialize)]
struct ProposalPageRequest {
    realization_id: String,
    realization_version: u64,
    version: u64,
    stage: u64,
    cursor: u64,
}

#[derive(serde::Deserialize)]
struct ProposalPageResponse {
    realization_id: String,
    realization_version: u64,
    version: u64,
    stage: u64,
    cursor: u64,
    next_cursor: u64,
    complete: bool,
}

#[derive(serde::Deserialize)]
struct WLayerRequest {
    index: u64,
}

#[derive(serde::Deserialize)]
struct WLayerResponseIndex {
    index: u64,
}

fn w_layer_request(
    logical_request: &WorkerRequestEnvelope,
    index: u64,
    name_env_revision: NameEnvRevision,
    proposal_revision: ProposalRevision,
    next_request: &AtomicU64,
) -> Result<WorkerRequestEnvelope, EncodingError> {
    let request_id = next_request
        .fetch_update(Ordering::AcqRel, Ordering::Acquire, |current| {
            current.checked_add(1)
        })
        .map_err(|_| {
            EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "encoding-worker request identity space exhausted",
            ))
        })?;
    Ok(WorkerRequestEnvelope {
        format_version: WORKER_FORMAT_VERSION,
        semantic_version: logical_request.semantic_version,
        encoding_version: logical_request.encoding_version,
        task_canonical_id: logical_request.task_canonical_id.clone(),
        task_module: logical_request.task_module.clone(),
        task_namespace: logical_request.task_namespace.clone(),
        task_source_sha256: logical_request.task_source_sha256.clone(),
        request_id,
        context_id: logical_request.context_id.clone(),
        name_env_revision,
        proposal_revision,
        operation: WorkerOperation::EnsureWLayer,
        payload: serde_json::json!({ "index": index }),
    })
}

fn validate_w_layer_replay_response(
    request: &WorkerRequestEnvelope,
    entry: &WLayerReplay,
    response: &WorkerResponseEnvelope,
) -> Result<(), EncodingError> {
    validate_logical_response_envelope(request, response)?;
    if response.status != WorkerResponseStatus::Ok
        || canonical_value_sha256(&response.payload) != entry.expected_digest.as_ref()
    {
        return Err(EncodingError::Failure(encoding_failure(
            EncodingFailureClass::SharedInfrastructure,
            "encoding worker returned an invalid W-layer replay response",
        )));
    }
    let returned: WLayerResponseIndex =
        serde_json::from_value(response.payload.clone()).map_err(|error| {
            EncodingError::Failure(encoding_failure(
                EncodingFailureClass::MalformedResponse,
                format!("decode W-layer replay response index: {error}"),
            ))
        })?;
    if returned.index != entry.index {
        return Err(EncodingError::Failure(encoding_failure(
            EncodingFailureClass::SharedInfrastructure,
            "encoding worker replayed a different W-layer index",
        )));
    }
    Ok(())
}

fn proposal_request(
    logical_request: &WorkerRequestEnvelope,
    delta: &ProposalDelta,
    name_env_revision: NameEnvRevision,
    next_request: &AtomicU64,
) -> Result<WorkerRequestEnvelope, EncodingError> {
    let request_id = next_request
        .fetch_update(Ordering::AcqRel, Ordering::Acquire, |current| {
            current.checked_add(1)
        })
        .map_err(|_| {
            EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "encoding-worker request identity space exhausted",
            ))
        })?;
    Ok(WorkerRequestEnvelope {
        format_version: WORKER_FORMAT_VERSION,
        semantic_version: logical_request.semantic_version,
        encoding_version: logical_request.encoding_version,
        task_canonical_id: logical_request.task_canonical_id.clone(),
        task_module: logical_request.task_module.clone(),
        task_namespace: logical_request.task_namespace.clone(),
        task_source_sha256: logical_request.task_source_sha256.clone(),
        request_id,
        context_id: logical_request.context_id.clone(),
        name_env_revision,
        proposal_revision: delta.base_revision,
        operation: WorkerOperation::RegisterReferenceProposal,
        payload: serde_json::json!({
            "realization_id": delta.realization.realization_id(),
            "realization_version": delta.realization.realization_version(),
            "version": PROPOSAL_PAGE_PROTOCOL_VERSION,
            "stage": delta.stage,
            "cursor": delta.cursor,
            "max_response_bytes": delta.max_response_bytes,
        }),
    })
}

fn validate_proposal_response(
    request: &WorkerRequestEnvelope,
    delta: &ProposalDelta,
    response: &WorkerResponseEnvelope,
) -> Result<(), EncodingError> {
    let requested: ProposalPageRequest =
        serde_json::from_value(request.payload.clone()).map_err(|error| {
            EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                format!("decode proposal-replay request: {error}"),
            ))
        })?;
    let returned: ProposalPageResponse =
        serde_json::from_value(response.payload.clone()).map_err(|error| {
            EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                format!("decode proposal-replay response: {error}"),
            ))
        })?;
    if response.format_version != WORKER_FORMAT_VERSION
        || response.semantic_version != request.semantic_version
        || response.encoding_version != request.encoding_version
        || response.task_canonical_id != request.task_canonical_id
        || response.task_module != request.task_module
        || response.task_namespace != request.task_namespace
        || response.task_source_sha256 != request.task_source_sha256
        || response.request_id != request.request_id
        || response.context_id != request.context_id
        || response.operation != WorkerOperation::RegisterReferenceProposal
        || response.request_name_env_revision != request.name_env_revision
        || response.name_env_revision != request.name_env_revision
        || response.request_proposal_revision != delta.base_revision
        || response.proposal_revision != delta.revision
        || response.status != WorkerResponseStatus::Ok
        || requested.realization_id != delta.realization.realization_id()
        || requested.realization_version != delta.realization.realization_version()
        || requested.version != PROPOSAL_PAGE_PROTOCOL_VERSION
        || returned.realization_id != requested.realization_id
        || returned.realization_version != requested.realization_version
        || returned.version != requested.version
        || canonical_value_sha256(&response.payload) != delta.expected_digest.as_ref()
    {
        return Err(EncodingError::Failure(encoding_failure(
            EncodingFailureClass::SharedInfrastructure,
            "encoding worker returned an invalid proposal-replay response",
        )));
    }
    Ok(())
}

impl Drop for WorkerProcess {
    fn drop(&mut self) {
        let _ = self.stop();
    }
}

struct StderrCapture<R = ChildStderr> {
    thread: Option<JoinHandle<StderrCaptureExit<R>>>,
    completed: mpsc::Receiver<()>,
    stop: Arc<AtomicBool>,
}

enum StderrCaptureExit<R> {
    Eof(Vec<u8>),
    Stopped { stderr: R, retained: Vec<u8> },
    Failed(String),
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
impl<R> StderrCapture<R>
where
    R: AsRawFd + Read + Send + 'static,
{
    fn start(stderr: R) -> Result<Self, String> {
        Self::start_with_hook(stderr, |_| {})
    }

    fn start_with_hook<F>(stderr: R, before_completion: F) -> Result<Self, String>
    where
        F: FnOnce(&AtomicBool) + Send + 'static,
    {
        let (completed_sender, completed) = mpsc::sync_channel(1);
        let stop = Arc::new(AtomicBool::new(false));
        let capture_stop = Arc::clone(&stop);
        let thread = thread::Builder::new()
            .name("encoding-worker-stderr-capture".to_string())
            .spawn(move || {
                let result = drain_stderr(stderr, &capture_stop);
                before_completion(&capture_stop);
                let _ = completed_sender.send(());
                result
            })
            .map_err(|error| format!("start Lean encoding-worker stderr capture: {error}"))?;
        Ok(Self {
            thread: Some(thread),
            completed,
            stop,
        })
    }

    fn finish(mut self) -> Result<(), String> {
        self.finish_with_grace(PROCESS_CLEANUP_GRACE)
    }

    fn finish_with_grace(&mut self, grace: Duration) -> Result<(), String> {
        if matches!(
            self.completed.recv_timeout(grace),
            Err(mpsc::RecvTimeoutError::Timeout)
        ) {
            self.stop.store(true, Ordering::Release);
            self.thread
                .as_ref()
                .expect("stderr capture thread remains owned")
                .thread()
                .unpark();
        }
        let result = self
            .thread
            .take()
            .expect("stderr capture thread remains owned")
            .join()
            .map_err(|_| "Lean encoding-worker stderr capture thread panicked".to_string())?;
        match result {
            StderrCaptureExit::Eof(_retained) => Ok(()),
            StderrCaptureExit::Stopped {
                mut stderr,
                retained: _retained,
            } => {
                if stderr_has_no_writers(&mut stderr)? {
                    Ok(())
                } else {
                    Err(
                        "Lean encoding-worker stderr remained open after process-tree cleanup"
                            .to_string(),
                    )
                }
            }
            StderrCaptureExit::Failed(error) => Err(error),
        }
    }
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
impl StderrCapture<ChildStderr> {
    fn start(stderr: ChildStderr) -> Result<Self, String> {
        let (completed_sender, completed) = mpsc::sync_channel(1);
        let stop = Arc::new(AtomicBool::new(false));
        let thread = thread::Builder::new()
            .name("encoding-worker-stderr-capture".to_string())
            .spawn(move || {
                let result = drain_stderr(stderr);
                let _ = completed_sender.send(());
                result
            })
            .map_err(|error| format!("start Lean encoding-worker stderr capture: {error}"))?;
        Ok(Self {
            thread: Some(thread),
            completed,
            stop,
        })
    }

    fn finish(mut self) -> Result<(), String> {
        let _ = self.completed.recv();
        match self
            .thread
            .take()
            .expect("stderr capture thread remains owned")
            .join()
        {
            Ok(StderrCaptureExit::Eof(_retained)) => Ok(()),
            Ok(StderrCaptureExit::Failed(error)) => Err(error),
            Ok(StderrCaptureExit::Stopped { .. }) => {
                Err("Lean encoding-worker stderr capture stopped unexpectedly".to_string())
            }
            Err(_) => Err("Lean encoding-worker stderr capture thread panicked".to_string()),
        }
    }
}

// ------------------------------------------------------------
// Owned Process-Tree Observation
// ------------------------------------------------------------

#[cfg(any(target_os = "macos", target_os = "linux"))]
#[derive(Clone)]
struct ProcessTreeHandle {
    root_pid: u32,
    registry: Arc<Mutex<ProcessRegistry>>,
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
impl ProcessTreeHandle {
    fn signal_all(&self, signal: i32, errors: &mut Vec<String>) {
        let mut registry = self
            .registry
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        registry.refresh();
        let mut descendants = registry.live_matching_descendants();
        descendants.sort_by_key(|process| std::cmp::Reverse(process.depth));
        for descendant in descendants {
            if let Err(error) = signal_identity(&descendant.identity, signal)
                && error.raw_os_error() != Some(libc::ESRCH)
            {
                errors.push(format!(
                    "signal registered Lean encoding-worker descendant: {error}"
                ));
            }
        }
        if let Err(error) = signal_group(self.root_pid, signal)
            && !matches!(error.raw_os_error(), Some(libc::ESRCH) | Some(libc::EPERM))
        {
            errors.push(format!(
                "signal Lean encoding-worker process group: {error}"
            ));
        }
    }

    fn live_descendant_pids(&self) -> Vec<u32> {
        let mut registry = self
            .registry
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        registry.refresh();
        registry
            .owned_live_descendants(self.root_pid)
            .into_iter()
            .map(|process| process.identity.pid)
            .collect()
    }

    fn signal_registered_descendants(&self, signal: i32, errors: &mut Vec<String>) {
        let mut registry = self
            .registry
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        registry.refresh();
        let mut descendants = registry.live_matching_descendants();
        descendants.sort_by_key(|process| std::cmp::Reverse(process.depth));
        for descendant in descendants {
            if let Err(error) = signal_identity(&descendant.identity, signal)
                && error.raw_os_error() != Some(libc::ESRCH)
            {
                errors.push(format!(
                    "signal registered Lean encoding-worker descendant: {error}"
                ));
            }
        }
    }

    fn live_registered_descendant_pids(&self) -> Vec<u32> {
        let mut registry = self
            .registry
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        registry.refresh();
        registry
            .live_matching_descendants()
            .into_iter()
            .map(|process| process.identity.pid)
            .collect()
    }
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
struct ProcessTreeObserver {
    handle: ProcessTreeHandle,
    stop: Arc<AtomicBool>,
    observer: Option<JoinHandle<()>>,
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
impl ProcessTreeObserver {
    fn start(root_pid: u32) -> Result<Self, String> {
        let registry = Arc::new(Mutex::new(ProcessRegistry::new(root_pid)?));
        let handle = ProcessTreeHandle {
            root_pid,
            registry: Arc::clone(&registry),
        };
        let stop = Arc::new(AtomicBool::new(false));
        let observer_stop = Arc::clone(&stop);
        let observer = match thread::Builder::new()
            .name(format!("encoding-worker-{root_pid}-process-tree"))
            .spawn(move || {
                while !observer_stop.load(Ordering::Acquire) {
                    registry
                        .lock()
                        .unwrap_or_else(|poisoned| poisoned.into_inner())
                        .refresh();
                    thread::sleep(PROCESS_POLL_INTERVAL);
                }
            }) {
            Ok(observer) => observer,
            Err(error) => {
                let mut errors = Vec::new();
                handle.signal_all(libc::SIGKILL, &mut errors);
                let detail = format!("start process-tree observer thread: {error}");
                return if errors.is_empty() {
                    Err(detail)
                } else {
                    Err(format!("{detail}; {}", errors.join("; ")))
                };
            }
        };
        Ok(Self {
            handle,
            stop,
            observer: Some(observer),
        })
    }

    fn stop_owned_tree(&mut self, child: &mut Child, errors: &mut Vec<String>) {
        let deadline = Instant::now() + PROCESS_CLEANUP_GRACE;
        let mut survivors = self.handle.live_descendant_pids();
        while !survivors.is_empty() && Instant::now() < deadline {
            self.handle.signal_all(libc::SIGKILL, errors);
            thread::sleep(PROCESS_POLL_INTERVAL);
            survivors = self.handle.live_descendant_pids();
        }
        if !survivors.is_empty() {
            errors.push(format!(
                "owned Lean encoding-worker descendants survived cleanup: {survivors:?}"
            ));
        }

        if let Err(error) = child.wait() {
            errors.push(format!("reap direct Lean encoding worker: {error}"));
        }

        // Once the root is reaped its process-group identifier is no longer
        // anchored. Only identity-recorded descendants are safe to signal.
        // Keep the observer live through this final sweep so a late observed
        // escape cannot outlive successful cleanup.
        let mut registered = self.handle.live_registered_descendant_pids();
        while !registered.is_empty() {
            self.handle
                .signal_registered_descendants(libc::SIGKILL, errors);
            registered = self.handle.live_registered_descendant_pids();
            if registered.is_empty() || Instant::now() >= deadline {
                break;
            }
            thread::sleep(PROCESS_POLL_INTERVAL);
            registered = self.handle.live_registered_descendant_pids();
        }
        if !registered.is_empty() {
            errors.push(format!(
                "registered Lean encoding-worker descendants survived final cleanup: {registered:?}"
            ));
        }
        self.stop.store(true, Ordering::Release);
        if self
            .observer
            .take()
            .expect("process-tree observer remains owned")
            .join()
            .is_err()
        {
            errors.push("Lean encoding-worker process-tree observer panicked".to_string());
        }
    }
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
fn drain_stderr<R>(mut stderr: R, stop: &AtomicBool) -> StderrCaptureExit<R>
where
    R: AsRawFd + Read,
{
    if let Err(error) = set_nonblocking(&stderr) {
        return StderrCaptureExit::Failed(format!(
            "configure Lean encoding-worker stderr capture: {error}"
        ));
    }
    let mut retained = VecDeque::with_capacity(MAX_STDERR_BYTES);
    let mut buffer = [0_u8; 8192];
    loop {
        if stop.load(Ordering::Acquire) {
            return StderrCaptureExit::Stopped {
                stderr,
                retained: retained.into(),
            };
        }
        match stderr.read(&mut buffer) {
            Ok(0) => return StderrCaptureExit::Eof(retained.into()),
            Ok(count) => {
                for byte in &buffer[..count] {
                    if retained.len() == MAX_STDERR_BYTES {
                        retained.pop_front();
                    }
                    retained.push_back(*byte);
                }
            }
            Err(error) if error.kind() == std::io::ErrorKind::Interrupted => {}
            Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                thread::park_timeout(PROCESS_POLL_INTERVAL);
            }
            Err(error) => {
                return StderrCaptureExit::Failed(format!(
                    "read Lean encoding-worker stderr: {error}"
                ));
            }
        }
    }
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
fn set_nonblocking(stderr: &impl AsRawFd) -> std::io::Result<()> {
    let descriptor = stderr.as_raw_fd();
    let flags = unsafe { libc::fcntl(descriptor, libc::F_GETFL) };
    if flags == -1 {
        return Err(std::io::Error::last_os_error());
    }
    if unsafe { libc::fcntl(descriptor, libc::F_SETFL, flags | libc::O_NONBLOCK) } == -1 {
        return Err(std::io::Error::last_os_error());
    }
    Ok(())
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
fn stderr_has_no_writers<R>(stderr: &mut R) -> Result<bool, String>
where
    R: AsRawFd + Read,
{
    let events = stderr_events(stderr)?;
    if events & libc::POLLHUP != 0 {
        return Ok(true);
    }
    if events & libc::POLLIN == 0 {
        return Ok(false);
    }

    // Some kernels report only readable buffered bytes before exposing HUP.
    // Drain exactly this snapshot, never an unbounded live-writer stream.
    let mut available = 0_i32;
    if unsafe { libc::ioctl(stderr.as_raw_fd(), libc::FIONREAD, &mut available) } == -1 {
        return Err(format!(
            "inspect buffered Lean encoding-worker stderr: {}",
            std::io::Error::last_os_error()
        ));
    }
    let mut remaining = usize::try_from(available).map_err(|_| {
        "inspect buffered Lean encoding-worker stderr: negative byte count".to_string()
    })?;
    let mut buffer = [0_u8; 8192];
    while remaining > 0 {
        let maximum = remaining.min(buffer.len());
        match stderr.read(&mut buffer[..maximum]) {
            Ok(0) => return Ok(true),
            Ok(count) => remaining -= count,
            Err(error) if error.kind() == std::io::ErrorKind::Interrupted => {}
            Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => break,
            Err(error) => {
                return Err(format!(
                    "drain buffered Lean encoding-worker stderr: {error}"
                ));
            }
        }
    }
    Ok(stderr_events(stderr)? & libc::POLLHUP != 0)
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
fn stderr_events(stderr: &impl AsRawFd) -> Result<i16, String> {
    let mut descriptor = libc::pollfd {
        fd: stderr.as_raw_fd(),
        events: libc::POLLIN,
        revents: 0,
    };
    loop {
        let result = unsafe { libc::poll(&mut descriptor, 1, 0) };
        if result >= 0 {
            return Ok(if result == 0 { 0 } else { descriptor.revents });
        }
        let error = std::io::Error::last_os_error();
        if error.kind() != std::io::ErrorKind::Interrupted {
            return Err(format!(
                "inspect Lean encoding-worker stderr ownership: {error}"
            ));
        }
    }
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
fn drain_stderr(mut stderr: ChildStderr) -> StderrCaptureExit<ChildStderr> {
    let mut retained = VecDeque::with_capacity(MAX_STDERR_BYTES);
    let mut buffer = [0_u8; 8192];
    loop {
        match stderr.read(&mut buffer) {
            Ok(0) => return StderrCaptureExit::Eof(retained.into()),
            Ok(count) => {
                for byte in &buffer[..count] {
                    if retained.len() == MAX_STDERR_BYTES {
                        retained.pop_front();
                    }
                    retained.push_back(*byte);
                }
            }
            Err(error) if error.kind() == std::io::ErrorKind::Interrupted => {}
            Err(error) => {
                return StderrCaptureExit::Failed(format!(
                    "read Lean encoding-worker stderr: {error}"
                ));
            }
        }
    }
}

#[cfg(unix)]
fn configure_process_group(command: &mut Command) {
    use std::os::unix::process::CommandExt;
    command.process_group(0);
}

#[cfg(not(unix))]
fn configure_process_group(_command: &mut Command) {}

#[cfg(unix)]
fn kill_process_group(pid: u32) {
    if let Ok(pid) = i32::try_from(pid) {
        // The direct child remains owned and unreaped while this signal is
        // sent, so its process-group identifier cannot have been recycled.
        unsafe {
            libc::kill(-pid, libc::SIGKILL);
        }
    }
}

#[cfg(not(unix))]
fn kill_process_group(_pid: u32) {}

#[cfg(test)]
mod tests {
    use super::super::names::{NameMapping, NameMappingKind};
    use super::*;
    use crate::failure::{FailureKind, FailureScope};

    fn fixed_ambient_request() -> FixedAmbientWorkerRequestEnvelope {
        FixedAmbientWorkerRequestEnvelope {
            format_version: FIXED_AMBIENT_WORKER_FORMAT_VERSION,
            semantic_version: 1,
            encoding_version: 1,
            task_canonical_id: "Example0001".to_string(),
            task_module: "Benchmark.Example0001.Input".to_string(),
            task_namespace: "Whiel.Benchmark.Example0001".to_string(),
            task_source_sha256: "a".repeat(64),
            scope_identity: serde_json::json!({"kind":"fixed"}),
            request_id: 4,
            name_env_revision: NameEnvRevision::INITIAL,
            operation: FixedAmbientWorkerOperation::Ping,
            payload: serde_json::json!({}),
        }
    }

    fn fixed_ambient_response(
        request: &FixedAmbientWorkerRequestEnvelope,
    ) -> FixedAmbientWorkerResponseEnvelope {
        FixedAmbientWorkerResponseEnvelope {
            format_version: FIXED_AMBIENT_WORKER_FORMAT_VERSION,
            semantic_version: request.semantic_version,
            encoding_version: request.encoding_version,
            task_identity: Some(FixedAmbientWorkerTaskIdentity {
                canonical_id: request.task_canonical_id.clone(),
                module: request.task_module.clone(),
                namespace: request.task_namespace.clone(),
                source_sha256: request.task_source_sha256.clone(),
            }),
            scope_identity: request.scope_identity.clone(),
            request_id: request.request_id,
            request_name_env_revision: request.name_env_revision,
            name_env_revision: request.name_env_revision,
            operation: request.operation,
            status: WorkerResponseStatus::Ok,
            payload: serde_json::json!({"ready":true}),
            error: None,
        }
    }

    #[test]
    fn fixed_ambient_response_validation_fails_closed() {
        let request = fixed_ambient_request();
        let response = fixed_ambient_response(&request);
        validate_fixed_ambient_response_envelope(&request, &response).unwrap();

        let mut retired = response.clone();
        retired.format_version = WORKER_FORMAT_VERSION;
        assert!(validate_fixed_ambient_response_envelope(&request, &retired).is_err());

        let mut wrong_scope = response.clone();
        wrong_scope.scope_identity = serde_json::json!({"kind":"other"});
        assert!(validate_fixed_ambient_response_envelope(&request, &wrong_scope).is_err());

        let mut wrong_task = response.clone();
        wrong_task
            .task_identity
            .as_mut()
            .expect("the fixture response names its task")
            .source_sha256 = "b".repeat(64);
        assert!(validate_fixed_ambient_response_envelope(&request, &wrong_task).is_err());

        // An unbound error frame echoes null for both identities; the same
        // shape on an `ok` frame, or with a scope still named, fails closed.
        let mut unbound = response.clone();
        unbound.task_identity = None;
        unbound.scope_identity = serde_json::Value::Null;
        assert!(validate_fixed_ambient_response_envelope(&request, &unbound).is_err());
        unbound.status = WorkerResponseStatus::Error;
        unbound.payload = serde_json::Value::Null;
        unbound.error = Some(super::super::protocol::FixedAmbientWorkerResponseError {
            kind: "invalid_envelope".to_string(),
            message: "request canonical ID names no registered task".to_string(),
        });
        validate_fixed_ambient_response_envelope(&request, &unbound).unwrap();
        let mut unbound_with_scope = unbound.clone();
        unbound_with_scope.scope_identity = request.scope_identity.clone();
        assert!(validate_fixed_ambient_response_envelope(&request, &unbound_with_scope).is_err());

        let mut hidden_error = response;
        hidden_error.error = Some(super::super::protocol::FixedAmbientWorkerResponseError {
            kind: "invalid_envelope".to_string(),
            message: "wrong".to_string(),
        });
        assert!(validate_fixed_ambient_response_envelope(&request, &hidden_error).is_err());

        hidden_error.status = WorkerResponseStatus::Error;
        assert!(validate_fixed_ambient_response_envelope(&request, &hidden_error).is_err());
        hidden_error.payload = serde_json::Value::Null;
        validate_fixed_ambient_response_envelope(&request, &hidden_error).unwrap();
    }

    #[test]
    fn fixed_ambient_extension_preserves_complete_binding() {
        let logical = fixed_ambient_request();
        let delta = NameEnvDelta {
            base_revision: NameEnvRevision::INITIAL,
            revision: NameEnvRevision::from_raw(1),
            relations: vec![NameMapping {
                kind: NameMappingKind::Relation,
                key: "y:p::R".to_string(),
                tptp_name: "yp_zR".to_string(),
            }]
            .into(),
            constants: Arc::from([]),
        };
        let request =
            fixed_ambient_extension_request(&logical, &delta, &AtomicU64::new(5)).unwrap();
        assert_eq!(request.scope_identity, logical.scope_identity);
        assert_eq!(
            request.operation,
            FixedAmbientWorkerOperation::ExtendNameEnv
        );
        let mut response = fixed_ambient_response(&request);
        response.name_env_revision = delta.revision;
        response.payload = serde_json::json!({
            "relations": [{"key":"y:p::R","name":"yp_zR"}],
            "constants": []
        });
        validate_fixed_ambient_extension_response(&request, &delta, &response).unwrap();

        response.payload["relations"][0]["key"] = serde_json::json!("o:p::R");
        assert!(validate_fixed_ambient_extension_response(&request, &delta, &response).is_err());
    }

    #[test]
    fn worker_pool_uses_seeded_by_default_and_accepts_reference_fallback() {
        let command = EncodingWorkerCommand::new("worker", ".");
        let defaulted = EncodingWorkerPoolConfig::new(command.clone(), 1).unwrap();
        assert_eq!(
            defaulted.proposal_realization,
            ProposalRealization::SeededV1
        );
        let reference = EncodingWorkerPoolConfig::new(command, 1)
            .unwrap()
            .proposal_realization(ProposalRealization::ReferenceV3);
        assert_eq!(
            reference.proposal_realization,
            ProposalRealization::ReferenceV3
        );
    }

    #[test]
    fn fixed_ambient_command_selects_only_the_worker_mode() {
        let command = FixedAmbientWorkerCommand::new("fixed-worker", "/repo")
            .arguments([OsString::from("prefix")]);
        assert_eq!(command.executable(), std::path::Path::new("fixed-worker"));
        assert_eq!(command.argument_prefix(), &[OsString::from("prefix")]);
        assert_eq!(command.current_directory(), std::path::Path::new("/repo"));
        assert_eq!(
            command.worker_arguments(),
            [OsString::from("prefix"), OsString::from("worker")]
        );
    }

    #[test]
    fn extension_request_replays_one_exact_contiguous_delta() {
        let delta = NameEnvDelta {
            base_revision: NameEnvRevision::INITIAL,
            revision: NameEnvRevision::from_raw(1),
            relations: vec![NameMapping {
                kind: NameMappingKind::Relation,
                key: "rel:R:0".to_string(),
                tptp_name: "r_0zR".to_string(),
            }]
            .into(),
            constants: Arc::from([]),
        };
        let logical = WorkerRequestEnvelope {
            format_version: WORKER_FORMAT_VERSION,
            semantic_version: 2,
            encoding_version: 3,
            task_canonical_id: "Task".to_string(),
            task_module: "Task.Module".to_string(),
            task_namespace: "Task.Namespace".to_string(),
            task_source_sha256: "0".repeat(64),
            request_id: 4,
            context_id: "context".to_string(),
            name_env_revision: delta.revision,
            proposal_revision: ProposalRevision::INITIAL,
            operation: WorkerOperation::PrepareBodies,
            payload: serde_json::Value::Null,
        };
        let next_request = AtomicU64::new(5);
        let request =
            extension_request(&logical, &delta, ProposalRevision::INITIAL, &next_request).unwrap();
        assert_eq!(request.request_id, 5);
        assert_eq!(request.name_env_revision, NameEnvRevision::INITIAL);
        assert_eq!(request.operation, WorkerOperation::ExtendNameEnv);

        let response = WorkerResponseEnvelope {
            format_version: WORKER_FORMAT_VERSION,
            semantic_version: 2,
            encoding_version: 3,
            task_canonical_id: "Task".to_string(),
            task_module: "Task.Module".to_string(),
            task_namespace: "Task.Namespace".to_string(),
            task_source_sha256: "0".repeat(64),
            request_id: 5,
            context_id: "context".to_string(),
            operation: WorkerOperation::ExtendNameEnv,
            request_name_env_revision: NameEnvRevision::INITIAL,
            name_env_revision: NameEnvRevision::from_raw(1),
            request_proposal_revision: ProposalRevision::INITIAL,
            proposal_revision: ProposalRevision::INITIAL,
            status: WorkerResponseStatus::Ok,
            payload: serde_json::json!({
                "relations": [{"key":"rel:R:0", "name":"r_0zR"}],
                "constants": [],
            }),
            error: None,
        };
        validate_extension_response(&request, &delta, &response).unwrap();

        let mut wrong_task = response.clone();
        wrong_task.task_source_sha256 = "1".repeat(64);
        assert!(validate_extension_response(&request, &delta, &wrong_task).is_err());

        let mut wrong_version = response.clone();
        wrong_version.encoding_version += 1;
        assert!(validate_extension_response(&request, &delta, &wrong_version).is_err());

        let mut retired_format = response.clone();
        retired_format.format_version = WORKER_FORMAT_VERSION - 1;
        assert!(validate_extension_response(&request, &delta, &retired_format).is_err());

        let mut wrong_revision = response;
        wrong_revision.name_env_revision = NameEnvRevision::from_raw(2);
        assert!(validate_extension_response(&request, &delta, &wrong_revision).is_err());
    }

    #[test]
    fn proposal_request_replays_one_exact_contiguous_stage() {
        let realization = ProposalRealization::ReferenceV3;
        let expected_payload = serde_json::json!({
            "realization_id": realization.realization_id(),
            "realization_version": realization.realization_version(),
            "version": PROPOSAL_PAGE_PROTOCOL_VERSION,
            "stage": 0,
            "cursor": 0,
            "next_cursor": 2,
            "complete": true,
            "raw_occurrences": 0,
            "canonical_formulas": 0,
            "canonical_duplicates": 0,
            "emitted_formulas": 0,
            "fragment": "[]",
        });
        let delta = ProposalDelta {
            realization,
            base_revision: ProposalRevision::INITIAL,
            revision: ProposalRevision::from_raw(1),
            stage: 0,
            cursor: 0,
            next_cursor: 2,
            max_response_bytes: 4096,
            complete: true,
            fragment: Arc::from("[]"),
            expected_digest: Arc::from(canonical_value_sha256(&expected_payload)),
        };
        let logical = WorkerRequestEnvelope {
            format_version: WORKER_FORMAT_VERSION,
            semantic_version: 2,
            encoding_version: 3,
            task_canonical_id: "Task".to_string(),
            task_module: "Task.Module".to_string(),
            task_namespace: "Task.Namespace".to_string(),
            task_source_sha256: "0".repeat(64),
            request_id: 4,
            context_id: "context".to_string(),
            name_env_revision: NameEnvRevision::INITIAL,
            proposal_revision: delta.revision,
            operation: WorkerOperation::PrepareBodies,
            payload: serde_json::Value::Null,
        };
        let next_request = AtomicU64::new(5);
        let request =
            proposal_request(&logical, &delta, NameEnvRevision::INITIAL, &next_request).unwrap();
        assert_eq!(request.request_id, 5);
        assert_eq!(request.proposal_revision, ProposalRevision::INITIAL);
        assert_eq!(
            request.operation,
            WorkerOperation::RegisterReferenceProposal
        );

        let response = WorkerResponseEnvelope {
            format_version: WORKER_FORMAT_VERSION,
            semantic_version: 2,
            encoding_version: 3,
            task_canonical_id: "Task".to_string(),
            task_module: "Task.Module".to_string(),
            task_namespace: "Task.Namespace".to_string(),
            task_source_sha256: "0".repeat(64),
            request_id: 5,
            context_id: "context".to_string(),
            operation: WorkerOperation::RegisterReferenceProposal,
            request_name_env_revision: NameEnvRevision::INITIAL,
            name_env_revision: NameEnvRevision::INITIAL,
            request_proposal_revision: ProposalRevision::INITIAL,
            proposal_revision: ProposalRevision::from_raw(1),
            status: WorkerResponseStatus::Ok,
            payload: expected_payload,
            error: None,
        };
        validate_proposal_response(&request, &delta, &response).unwrap();

        let mut wrong_payload = response.clone();
        wrong_payload.payload["stage"] = serde_json::json!(1);
        assert!(validate_proposal_response(&request, &delta, &wrong_payload).is_err());

        let mut wrong_realization = response.clone();
        wrong_realization.payload["realization_id"] = serde_json::json!("lean-fast-v1");
        assert!(validate_proposal_response(&request, &delta, &wrong_realization).is_err());

        let mut wrong_revision = response;
        wrong_revision.proposal_revision = ProposalRevision::from_raw(2);
        assert!(validate_proposal_response(&request, &delta, &wrong_revision).is_err());
    }

    #[test]
    fn w_layer_request_and_replay_bind_exact_index_and_payload() {
        let logical = WorkerRequestEnvelope {
            format_version: WORKER_FORMAT_VERSION,
            semantic_version: 2,
            encoding_version: 3,
            task_canonical_id: "Task".to_string(),
            task_module: "Task.Module".to_string(),
            task_namespace: "Task.Namespace".to_string(),
            task_source_sha256: "0".repeat(64),
            request_id: 4,
            context_id: "context".to_string(),
            name_env_revision: NameEnvRevision::from_raw(2),
            proposal_revision: ProposalRevision::from_raw(1),
            operation: WorkerOperation::PrepareBodies,
            payload: serde_json::Value::Null,
        };
        let request = w_layer_request(
            &logical,
            7,
            logical.name_env_revision,
            logical.proposal_revision,
            &AtomicU64::new(5),
        )
        .unwrap();
        assert_eq!(request.operation, WorkerOperation::EnsureWLayer);
        assert_eq!(request.payload, serde_json::json!({ "index": 7 }));

        let payload = serde_json::json!({
            "index": 7,
            "formula": {},
            "maintenance_wp": {},
        });
        let response = WorkerResponseEnvelope {
            format_version: WORKER_FORMAT_VERSION,
            semantic_version: request.semantic_version,
            encoding_version: request.encoding_version,
            task_canonical_id: request.task_canonical_id.clone(),
            task_module: request.task_module.clone(),
            task_namespace: request.task_namespace.clone(),
            task_source_sha256: request.task_source_sha256.clone(),
            request_id: request.request_id,
            context_id: request.context_id.clone(),
            operation: WorkerOperation::EnsureWLayer,
            request_name_env_revision: request.name_env_revision,
            name_env_revision: request.name_env_revision,
            request_proposal_revision: request.proposal_revision,
            proposal_revision: request.proposal_revision,
            status: WorkerResponseStatus::Ok,
            payload: payload.clone(),
            error: None,
        };
        let replay = WLayerReplay {
            index: 7,
            expected_digest: Arc::from(canonical_value_sha256(&payload)),
        };
        validate_w_layer_replay_response(&request, &replay, &response).unwrap();

        let mut altered = response;
        altered.payload["index"] = serde_json::json!(8);
        assert!(validate_w_layer_replay_response(&request, &replay, &altered).is_err());
    }

    #[cfg(unix)]
    #[test]
    fn owned_worker_drop_kills_and_reaps_child() {
        let command = EncodingWorkerCommand::new("/bin/sh", "/")
            .arguments([OsString::from("-c"), OsString::from("sleep 60")]);
        let process = WorkerProcess::spawn(&command, Arc::new(Mutex::new(None))).unwrap();
        let pid = process.pid();
        drop(process);
        let status = unsafe { libc::kill(i32::try_from(pid).unwrap(), 0) };
        assert_eq!(status, -1);
        assert_eq!(
            std::io::Error::last_os_error().raw_os_error(),
            Some(libc::ESRCH)
        );
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn stderr_eof_survives_delayed_capture_completion() {
        use std::os::unix::net::UnixStream;

        let (reader, writer) = UnixStream::pair().unwrap();
        let (drained_sender, drained) = mpsc::sync_channel(1);
        let completion_observed = Arc::new(AtomicBool::new(false));
        let hook_observed = Arc::clone(&completion_observed);
        let mut capture = StderrCapture::start_with_hook(reader, move |stop| {
            drained_sender.send(()).unwrap();
            while !stop.load(Ordering::Acquire) {
                thread::yield_now();
            }
            hook_observed.store(true, Ordering::Release);
        })
        .unwrap();
        drop(writer);
        drained.recv().unwrap();

        capture.finish_with_grace(Duration::ZERO).unwrap();
        assert!(completion_observed.load(Ordering::Acquire));
        assert!(capture.thread.is_none());
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn stderr_writer_past_capture_bound_fails_after_join() {
        use std::os::unix::net::UnixStream;

        let (reader, _writer) = UnixStream::pair().unwrap();
        let mut capture = StderrCapture::start(reader).unwrap();
        let error = capture.finish_with_grace(Duration::ZERO).unwrap_err();

        assert_eq!(
            error,
            "Lean encoding-worker stderr remained open after process-tree cleanup"
        );
        assert!(capture.thread.is_none());
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn stopped_capture_accepts_a_closed_buffered_stderr_pipe() {
        use std::io::Write;
        use std::os::fd::FromRawFd;

        let mut descriptors = [0_i32; 2];
        assert_eq!(unsafe { libc::pipe(descriptors.as_mut_ptr()) }, 0);
        let reader = unsafe { std::fs::File::from_raw_fd(descriptors[0]) };
        let mut writer = unsafe { std::fs::File::from_raw_fd(descriptors[1]) };
        writer.write_all(b"buffered worker diagnostic").unwrap();
        set_nonblocking(&reader).unwrap();
        let (completed_sender, completed) = mpsc::sync_channel(1);
        let stop = Arc::new(AtomicBool::new(false));
        let capture_stop = Arc::clone(&stop);
        let thread = thread::spawn(move || {
            while !capture_stop.load(Ordering::Acquire) {
                thread::yield_now();
            }
            let result = StderrCaptureExit::Stopped {
                stderr: reader,
                retained: Vec::new(),
            };
            completed_sender.send(()).unwrap();
            result
        });
        let mut capture = StderrCapture {
            thread: Some(thread),
            completed,
            stop,
        };
        drop(writer);

        capture.finish_with_grace(Duration::ZERO).unwrap();
        assert!(capture.thread.is_none());
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn stopped_capture_rejects_a_live_buffered_stderr_pipe() {
        use std::io::Write;
        use std::os::fd::FromRawFd;

        let mut descriptors = [0_i32; 2];
        assert_eq!(unsafe { libc::pipe(descriptors.as_mut_ptr()) }, 0);
        let reader = unsafe { std::fs::File::from_raw_fd(descriptors[0]) };
        let mut writer = unsafe { std::fs::File::from_raw_fd(descriptors[1]) };
        writer.write_all(b"buffered worker diagnostic").unwrap();
        set_nonblocking(&reader).unwrap();
        let (completed_sender, completed) = mpsc::sync_channel(1);
        let stop = Arc::new(AtomicBool::new(false));
        let capture_stop = Arc::clone(&stop);
        let thread = thread::spawn(move || {
            while !capture_stop.load(Ordering::Acquire) {
                thread::yield_now();
            }
            let result = StderrCaptureExit::Stopped {
                stderr: reader,
                retained: Vec::new(),
            };
            completed_sender.send(()).unwrap();
            result
        });
        let mut capture = StderrCapture {
            thread: Some(thread),
            completed,
            stop,
        };

        let error = capture.finish_with_grace(Duration::ZERO).unwrap_err();
        assert_eq!(
            error,
            "Lean encoding-worker stderr remained open after process-tree cleanup"
        );
        assert!(capture.thread.is_none());
        drop(writer);
    }

    /// A worker that never answers must not hold its pool slot for the rest of
    /// the run: the exchange fails closed as an infrastructure failure, the
    /// process is killed, and the slot is free for a fresh worker, which
    /// replays the name environment exactly as after any other worker loss.
    #[tokio::test]
    async fn a_silent_fixed_ambient_worker_fails_closed_and_frees_its_slot() {
        // `sh -c 'sleep 600'` reads nothing and writes nothing; the required
        // `worker` argument lands in `$0`.
        let command = FixedAmbientWorkerCommand::new("/bin/sh", "/")
            .arguments([OsString::from("-c"), OsString::from("sleep 600")]);
        let pool = FixedAmbientWorkerPool::new(
            FixedAmbientWorkerPoolConfig::new(command, 1)
                .unwrap()
                .round_trip_timeout(Duration::from_millis(250))
                .unwrap(),
        );
        let request = FixedAmbientWorkerRequestEnvelope {
            format_version: FIXED_AMBIENT_WORKER_FORMAT_VERSION,
            semantic_version: 2,
            encoding_version: 3,
            task_canonical_id: "Task".to_string(),
            task_module: "Task.Module".to_string(),
            task_namespace: "Task.Namespace".to_string(),
            task_source_sha256: "0".repeat(64),
            scope_identity: serde_json::json!({"scope": "fixture"}),
            request_id: 1,
            name_env_revision: NameEnvRevision::INITIAL,
            operation: FixedAmbientWorkerOperation::EvaluateClauses,
            payload: serde_json::Value::Null,
        };
        let sync = NameEnvSync {
            target_revision: NameEnvRevision::INITIAL,
            deltas: Arc::new(Vec::new()),
        };
        let cancellation = CancellationToken::new();
        let started = std::time::Instant::now();
        let result = pool
            .execute(sync, request, Arc::new(AtomicU64::new(2)), &cancellation)
            .await;
        let elapsed = started.elapsed();
        let Err(EncodingError::Failure(report)) = result else {
            panic!("a silent worker must fail closed, not answer or cancel")
        };
        assert_eq!(report.kind(), FailureKind::InfrastructureFailure);
        assert!(
            report
                .detail()
                .is_some_and(|detail| detail.contains("did not answer within")),
            "{report:?}"
        );
        // The allowance, not the worker's own 600 seconds, bounds the wait.
        assert!(elapsed < Duration::from_secs(30), "{elapsed:?}");
        // The slot came back, so the pool is usable rather than wedged.
        assert_eq!(
            pool.available
                .queue
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner())
                .len(),
            1
        );
        assert!(
            pool.slots[0]
                .process
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner())
                .is_none(),
            "the lost worker is replaced, not reused"
        );
        pool.shutdown().await.unwrap();
    }

    /// A timeout replaces its own worker and nobody else's.
    ///
    /// One slot, two concurrent requests: the first times out, the second is
    /// queued behind it. Each request must account for exactly one spawn, and
    /// both must fail closed.
    ///
    /// This pins the invariant rather than the race that motivated holding the
    /// slot lease across the replacement. The race needs the queued request to
    /// take the slot and spawn its worker inside the window between the lease
    /// being released and the cleanup acquiring the slot's process lock, and a
    /// failed exchange already takes and stops its own process, so the cleanup
    /// is usually a no-op and the window is rarely hit. Holding the lease
    /// closes it by construction; this test guards the invariant that closure
    /// preserves.
    #[tokio::test(flavor = "multi_thread", worker_threads = 4)]
    async fn a_timed_out_worker_is_replaced_without_disturbing_the_next_request() {
        let directory = std::env::temp_dir().join(format!(
            "whiel-timeout-replacement-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir_all(&directory).unwrap();
        let spawns = directory.join("spawns.log");
        // Each worker records its own start, then never answers. `$0` takes the
        // required `worker` argument, so the script sees no arguments at all.
        let script = format!("echo started >> {}; sleep 600", spawns.display());
        let command = FixedAmbientWorkerCommand::new("/bin/sh", "/")
            .arguments([OsString::from("-c"), OsString::from(script)]);
        let pool = Arc::new(FixedAmbientWorkerPool::new(
            FixedAmbientWorkerPoolConfig::new(command, 1)
                .unwrap()
                .round_trip_timeout(Duration::from_millis(250))
                .unwrap(),
        ));
        let request = |id: u64| FixedAmbientWorkerRequestEnvelope {
            format_version: FIXED_AMBIENT_WORKER_FORMAT_VERSION,
            semantic_version: 2,
            encoding_version: 3,
            task_canonical_id: "Task".to_string(),
            task_module: "Task.Module".to_string(),
            task_namespace: "Task.Namespace".to_string(),
            task_source_sha256: "0".repeat(64),
            scope_identity: serde_json::json!({"scope": "fixture"}),
            request_id: id,
            name_env_revision: NameEnvRevision::INITIAL,
            operation: FixedAmbientWorkerOperation::EvaluateClauses,
            payload: serde_json::Value::Null,
        };
        let sync = || NameEnvSync {
            target_revision: NameEnvRevision::INITIAL,
            deltas: Arc::new(Vec::new()),
        };
        let cancellation = CancellationToken::new();
        let next = Arc::new(AtomicU64::new(3));
        let first = {
            let pool = Arc::clone(&pool);
            let next = Arc::clone(&next);
            let cancellation = cancellation.clone();
            tokio::spawn(async move { pool.execute(sync(), request(1), next, &cancellation).await })
        };
        let second = {
            let pool = Arc::clone(&pool);
            let next = Arc::clone(&next);
            let cancellation = cancellation.clone();
            tokio::spawn(async move { pool.execute(sync(), request(2), next, &cancellation).await })
        };
        for outcome in [first.await.unwrap(), second.await.unwrap()] {
            let Err(EncodingError::Failure(report)) = outcome else {
                panic!("a silent worker must fail closed")
            };
            assert!(
                report
                    .detail()
                    .is_some_and(|detail| detail.contains("did not answer within")),
                "{report:?}"
            );
        }
        pool.shutdown().await.unwrap();
        let started = std::fs::read_to_string(&spawns).unwrap_or_default();
        assert_eq!(
            started.lines().count(),
            2,
            "one worker spawn per request, not a replacement stopped by the \
             previous request's cleanup: {started:?}"
        );
        let _ = std::fs::remove_dir_all(&directory);
    }

    #[tokio::test]
    async fn pool_shutdown_waits_for_registered_execution_and_never_reopens() {
        let config =
            EncodingWorkerPoolConfig::new(EncodingWorkerCommand::new("/bin/true", "/"), 1).unwrap();
        let pool = Arc::new(EncodingWorkerPool::new(config, "lifecycle-test"));
        let slot = Arc::clone(&pool.slots[0]);
        let execution = pool
            .lifecycle
            .begin(&slot)
            .expect("open pool accepts one execution");
        let shutdown_pool = Arc::clone(&pool);
        let shutdown = tokio::spawn(async move { shutdown_pool.shutdown().await });
        while !pool.shutdown.started.load(Ordering::Acquire) {
            tokio::task::yield_now().await;
        }

        assert!(!shutdown.is_finished());
        assert!(slot.cancel_requested.load(Ordering::Acquire));
        assert!(pool.lifecycle.begin(&slot).is_none());
        assert!(slot.cancel_requested.load(Ordering::Acquire));

        drop(execution);
        shutdown.await.unwrap().unwrap();
    }

    #[tokio::test]
    async fn pool_shutdown_failure_is_sticky_for_concurrent_and_later_callers() {
        let config =
            EncodingWorkerPoolConfig::new(EncodingWorkerCommand::new("/bin/true", "/"), 1).unwrap();
        let pool = EncodingWorkerPool::new(config, "cleanup-test");
        pool.inject_cleanup_failure("fixture cleanup failure");

        let (first, second) = tokio::join!(pool.shutdown(), pool.shutdown());
        let third = pool.shutdown().await;
        let reports = [first, second, third].map(|result| {
            let Err(EncodingError::Failure(report)) = result else {
                panic!("worker cleanup failure must be sticky and typed")
            };
            report
        });
        for report in &reports {
            assert_eq!(report.kind(), FailureKind::InfrastructureFailure);
            assert_eq!(report.scope(), FailureScope::RunGlobal);
            assert!(
                report
                    .detail()
                    .is_some_and(|detail| detail.contains("fixture cleanup failure"))
            );
        }
        assert_eq!(reports[0].detail(), reports[1].detail());
        assert_eq!(reports[1].detail(), reports[2].detail());
    }

    #[tokio::test]
    async fn aborting_first_shutdown_waiter_does_not_cancel_shared_cleanup() {
        let config =
            EncodingWorkerPoolConfig::new(EncodingWorkerCommand::new("/bin/true", "/"), 1).unwrap();
        let pool = Arc::new(EncodingWorkerPool::new(config, "aborted-cleanup-test"));
        pool.inject_cleanup_failure("aborted waiter fixture");
        let first_pool = Arc::clone(&pool);
        let first = tokio::spawn(async move { first_pool.shutdown().await });
        while !pool.shutdown.started.load(Ordering::Acquire) {
            tokio::task::yield_now().await;
        }
        first.abort();
        assert!(first.await.unwrap_err().is_cancelled());

        let result = pool.shutdown().await;
        let Err(EncodingError::Failure(report)) = result else {
            panic!("shared cleanup must outlive its first waiter")
        };
        assert_eq!(report.kind(), FailureKind::InfrastructureFailure);
        assert_eq!(report.scope(), FailureScope::RunGlobal);
        assert!(
            report
                .detail()
                .is_some_and(|detail| detail.contains("aborted waiter fixture"))
        );
    }

    #[test]
    fn run_global_execution_failure_dominates_concurrent_cancellation() {
        let global = arbitrate_cancelled_execution(Err(EncodingError::Failure(encoding_failure(
            EncodingFailureClass::SharedInfrastructure,
            "global execution failure",
        ))));
        let Err(EncodingError::Failure(report)) = global else {
            panic!("run-global execution failure must dominate cancellation")
        };
        assert_eq!(report.scope(), FailureScope::RunGlobal);

        let local = arbitrate_cancelled_execution(Err(EncodingError::Failure(encoding_failure(
            EncodingFailureClass::LocalInfrastructure,
            "lane-local execution failure",
        ))));
        assert!(matches!(local, Err(EncodingError::Cancelled)));
    }
}
