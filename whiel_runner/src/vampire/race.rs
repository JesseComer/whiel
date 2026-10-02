//! Admitted Vampire invocation, paired arbitration, and local deadlines.

use std::fmt;
use std::future::pending;
use std::sync::Arc;
use std::time::Duration;

use serde_json::json;
use tokio::task::JoinError;
use tokio::time::Instant;

use crate::artifact::{ArtifactKind, ArtifactRef, ArtifactStore, AttemptId, ScopeTag};
use crate::failure::{FailureKind, FailureOrigin, FailureReport, FailureScope};
use crate::runtime::{AdmissionError, CancellationToken, SolverAdmission, SolverPermit};

use super::command::{
    FmbOptions, FmbSize, ProofCascPolicy, SolverTimeLimit, VampireProblem, VampireWorkerCommand,
    VampireWorkerMode, VampireWorkerRequest, allocate_attempt,
};
use super::worker::{
    CancelledVampireWorker, VampireCapturePolicy, VampireResult, VampireWorkerOutcome,
    run_single_vampire_worker,
};

// ------------------------------------------------------------
// Admitted Invocation Types
// ------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VampireMode {
    ProofOnly,
    FmbOnly(FmbOptions),
    ProofAndFmb(FmbOptions),
}

impl VampireMode {
    fn preferred_processes(self) -> usize {
        match self {
            Self::ProofOnly | Self::FmbOnly(_) => 1,
            Self::ProofAndFmb(_) => 2,
        }
    }

    fn admitted_processes(self, admission: &SolverAdmission) -> usize {
        self.preferred_processes()
            .min(admission.policy().max_vampire_processes())
    }

    fn telemetry_name(self) -> &'static str {
        match self {
            Self::ProofOnly => "proof",
            Self::FmbOnly(_) => "fmb",
            Self::ProofAndFmb(_) => "proof_and_fmb",
        }
    }
}

/// A first-attempt baseline and the current cumulative search allowance.
///
/// Fresh work uses `finite`, where both limits are equal. Retried work uses
/// `cumulative`, preserving its original baseline while its total grows.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VampireSearchBudget {
    initial_limit: Option<Duration>,
    total_limit: Option<Duration>,
}

impl VampireSearchBudget {
    pub const UNBOUNDED: Self = Self {
        initial_limit: None,
        total_limit: None,
    };

    pub const fn finite(limit: Duration) -> Self {
        Self {
            initial_limit: Some(limit),
            total_limit: Some(limit),
        }
    }

    pub const fn cumulative(initial_limit: Duration, total_limit: Duration) -> Self {
        Self {
            initial_limit: Some(initial_limit),
            total_limit: Some(total_limit),
        }
    }

    pub const fn initial_limit(self) -> Option<Duration> {
        self.initial_limit
    }

    pub const fn total_limit(self) -> Option<Duration> {
        self.total_limit
    }

    fn retry_added(self) -> Duration {
        match (self.initial_limit, self.total_limit) {
            (Some(initial), Some(total)) => total.saturating_sub(initial),
            (None, None) => Duration::ZERO,
            _ => unreachable!("a Vampire search budget has matched finite bounds"),
        }
    }
}

impl From<Option<Duration>> for VampireSearchBudget {
    fn from(limit: Option<Duration>) -> Self {
        limit.map_or(Self::UNBOUNDED, Self::finite)
    }
}

impl From<Duration> for VampireSearchBudget {
    fn from(limit: Duration) -> Self {
        Self::finite(limit)
    }
}

#[derive(Debug)]
pub struct VampireRequest {
    problem: VampireProblem,
    mode: VampireMode,
    command: VampireWorkerCommand,
    attempt_id: AttemptId,
    artifacts: ArtifactStore,
    admission: SolverAdmission,
    search_budget: VampireSearchBudget,
    capture_policy: VampireCapturePolicy,
}

impl VampireRequest {
    #[allow(clippy::too_many_arguments)]
    pub fn new<B>(
        problem: VampireProblem,
        mode: VampireMode,
        command: VampireWorkerCommand,
        artifacts: ArtifactStore,
        admission: SolverAdmission,
        search_budget: B,
    ) -> Result<Self, VampireRequestError>
    where
        B: Into<VampireSearchBudget>,
    {
        let (attempt_id, artifacts) =
            allocate_attempt(artifacts).map_err(VampireRequestError::Artifact)?;
        Self::from_preallocated(
            problem,
            mode,
            command,
            attempt_id,
            artifacts,
            admission,
            search_budget.into(),
        )
    }

    /// Construct one invocation under an already allocated logical attempt.
    ///
    /// The source-linked entailment layer uses this path so proof search,
    /// FMB, empty checking, and every artifact share one attempt identity.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn from_preallocated(
        problem: VampireProblem,
        mode: VampireMode,
        command: VampireWorkerCommand,
        attempt_id: AttemptId,
        artifacts: ArtifactStore,
        admission: SolverAdmission,
        search_budget: VampireSearchBudget,
    ) -> Result<Self, VampireRequestError> {
        let local_limit = search_budget.total_limit();
        if local_limit.is_some_and(|limit| limit.is_zero()) {
            return Err(VampireRequestError::ZeroLocalLimit);
        }
        if search_budget
            .initial_limit()
            .is_some_and(|limit| limit.is_zero())
        {
            return Err(VampireRequestError::ZeroInitialLimit);
        }
        if matches!(
            (search_budget.initial_limit(), local_limit),
            (Some(initial), Some(total)) if initial > total
        ) {
            return Err(VampireRequestError::InitialLimitExceedsTotal {
                initial: search_budget
                    .initial_limit()
                    .expect("the comparison observed an initial limit"),
                total: local_limit.expect("the comparison observed a total limit"),
            });
        }
        if !command.proof_casc_policy().is_disabled()
            && local_limit.is_none()
            && matches!(mode, VampireMode::ProofOnly | VampireMode::ProofAndFmb(_))
        {
            return Err(VampireRequestError::UnboundedProofCasc);
        }
        // Every stage of this request states a limit, and the widest one
        // any of them states is the runner's own backstop, so that is what
        // has to be representable in the solver's units.
        if !command.proof_casc_policy().is_disabled()
            && matches!(mode, VampireMode::ProofOnly | VampireMode::ProofAndFmb(_))
            && local_limit.is_some_and(|limit| {
                SolverTimeLimit::for_local_limit(limit.saturating_add(SOLVER_STOP_GRACE * 2))
                    .is_none()
            })
        {
            return Err(VampireRequestError::UnrepresentableProofCascLimit {
                limit: local_limit.expect("the representability check observed a local limit"),
            });
        }
        let admitted_processes = mode.admitted_processes(&admission);
        if matches!(mode, VampireMode::ProofAndFmb(_))
            && admitted_processes == 1
            && local_limit.is_none()
        {
            return Err(VampireRequestError::UnboundedSerialPair);
        }
        if !admission.can_ever_admit(admitted_processes, local_limit.is_some()) {
            return Err(VampireRequestError::InsufficientCapacity {
                required: admitted_processes,
                available: admission.policy().max_vampire_processes(),
            });
        }
        Ok(Self {
            problem,
            mode,
            command,
            attempt_id,
            artifacts,
            admission,
            search_budget,
            capture_policy: VampireCapturePolicy::default(),
        })
    }

    pub fn with_capture_policy(mut self, capture_policy: VampireCapturePolicy) -> Self {
        self.capture_policy = capture_policy;
        self
    }

    pub fn attempt_id(&self) -> AttemptId {
        self.attempt_id
    }
}

#[derive(Debug)]
pub enum VampireRequestError {
    ZeroLocalLimit,
    ZeroInitialLimit,
    InitialLimitExceedsTotal { initial: Duration, total: Duration },
    UnboundedProofCasc,
    UnboundedSerialPair,
    UnrepresentableProofCascLimit { limit: Duration },
    InsufficientCapacity { required: usize, available: usize },
    Artifact(FailureReport),
}

impl fmt::Display for VampireRequestError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ZeroLocalLimit => formatter.write_str("a local Vampire limit must be positive"),
            Self::ZeroInitialLimit => {
                formatter.write_str("an initial Vampire retry limit must be positive")
            }
            Self::InitialLimitExceedsTotal { initial, total } => write!(
                formatter,
                "initial Vampire retry limit {initial:?} exceeds total local limit {total:?}",
            ),
            Self::UnboundedProofCasc => formatter
                .write_str("a configured proof CASC share requires a finite local Vampire limit"),
            Self::UnboundedSerialPair => formatter
                .write_str("a strict-serial proof/FMB schedule requires finite per-lane budgets"),
            Self::UnrepresentableProofCascLimit { limit } => write!(
                formatter,
                "local Vampire limit {limit:?} exceeds Vampire's safe exact CASC time-limit range",
            ),
            Self::InsufficientCapacity {
                required,
                available,
            } => write!(
                formatter,
                "Vampire mode requires {required} process slots but this admission can expose only {available}"
            ),
            Self::Artifact(report) => write!(
                formatter,
                "allocate Vampire attempt artifact scope: {}",
                report.detail().unwrap_or("artifact backend failure")
            ),
        }
    }
}

impl std::error::Error for VampireRequestError {}

#[derive(Clone, Debug)]
pub struct CancelledVampireInvocation {
    next_fmb_start_size: Option<FmbSize>,
    peer_failure: Option<FailureReport>,
    artifact_references: Vec<ArtifactRef>,
    capture_warnings: Vec<String>,
}

impl CancelledVampireInvocation {
    /// A stop observed at a boundary outside the worker race itself. No
    /// worker was interrupted here, so there is no artifact or warning to
    /// carry and no frontier to resume from.
    pub(crate) fn cooperative_stop() -> Self {
        Self {
            next_fmb_start_size: None,
            peer_failure: None,
            artifact_references: Vec::new(),
            capture_warnings: Vec::new(),
        }
    }

    pub fn next_fmb_start_size(&self) -> Option<FmbSize> {
        self.next_fmb_start_size
    }

    pub fn peer_failure(&self) -> Option<&FailureReport> {
        self.peer_failure.as_ref()
    }

    pub fn artifact_references(&self) -> &[ArtifactRef] {
        &self.artifact_references
    }

    pub fn capture_warnings(&self) -> &[String] {
        &self.capture_warnings
    }
}

#[derive(Clone, Debug)]
pub enum VampireInvocationOutcome {
    Result(VampireResult),
    Cancelled(CancelledVampireInvocation),
    RunFailure(FailureReport),
}

// ------------------------------------------------------------
// Common Vampire Boundary
// ------------------------------------------------------------

pub async fn run_vampire(
    request: VampireRequest,
    overall_cancellation: CancellationToken,
) -> VampireInvocationOutcome {
    let slots = request.mode.admitted_processes(&request.admission);
    let telemetry = request.command.telemetry().clone();
    telemetry.increment("solver.vampire_requests", 1);
    telemetry.increment(
        format!("solver.vampire_requests.{}", request.mode.telemetry_name()),
        1,
    );
    telemetry.increment(
        "solver.vampire_requested_process_slots",
        u64::try_from(slots).unwrap_or(u64::MAX),
    );
    let admission_started = telemetry.start_span();
    let acquisition = request
        .admission
        .acquire_solver(
            slots,
            request.search_budget.total_limit().is_some(),
            &overall_cancellation,
        )
        .await;
    telemetry.finish_span("solver.admission_wait", admission_started);
    let lease = match acquisition {
        Ok(lease) => lease,
        Err(AdmissionError::Cancelled) => return cancelled_invocation(None, None, Vec::new()),
        Err(AdmissionError::Closed(report)) => {
            return VampireInvocationOutcome::RunFailure(report);
        }
        Err(AdmissionError::InsufficientCapacity) => {
            unreachable!("VampireRequest validates immutable admission capacity")
        }
    };
    if overall_cancellation.is_cancelled() {
        drop(lease);
        return cancelled_invocation(None, None, Vec::new());
    }

    // The local allowance begins only after the complete weighted grant.
    // Preserve even durations too large for one Instant addition.
    let deadline = request
        .search_budget
        .total_limit()
        .map(|limit| LocalDeadline::start(runner_backstop(limit, &request)));
    match request.mode {
        VampireMode::ProofOnly => {
            run_proof_single(request, lease, deadline, overall_cancellation).await
        }
        VampireMode::FmbOnly(options) => {
            run_single(
                request,
                VampireWorkerMode::FmbOnly(options),
                lease,
                deadline,
                overall_cancellation,
            )
            .await
        }
        VampireMode::ProofAndFmb(options) => {
            if slots == 1 {
                run_pair_serial(request, options, lease, overall_cancellation).await
            } else {
                run_pair(request, options, lease, deadline, overall_cancellation).await
            }
        }
    }
}

async fn run_proof_single(
    request: VampireRequest,
    lease: SolverPermit,
    deadline: Option<LocalDeadline>,
    overall_cancellation: CancellationToken,
) -> VampireInvocationOutcome {
    let context = InvocationContext::new(&request);
    let lane_cancellation = CancellationToken::new();
    let _cancellation_guard = CancellationGuard::new([lane_cancellation.clone()]);
    let lane_request = ProofLaneRequest::new(&request);
    let mut task = tokio::spawn(run_proof_lane(
        lane_request,
        Arc::new(lease),
        lane_cancellation.clone(),
        deadline,
    ));
    let event = select_single_event(&mut task, &overall_cancellation, deadline).await;
    match event {
        SingleEvent::Worker(joined) => observed_to_invocation(
            observe_join(joined, &VampireWorkerMode::ProofOnly),
            &VampireWorkerMode::ProofOnly,
        ),
        SingleEvent::OverallCancelled => {
            lane_cancellation.cancel();
            let observed = observe_join(task.await, &VampireWorkerMode::ProofOnly);
            interrupted_from_observed(observed)
        }
        SingleEvent::LocalTimeout => {
            lane_cancellation.cancel();
            let observed = observe_join(task.await, &VampireWorkerMode::ProofOnly);
            timeout_from_observed(&context, observed)
        }
    }
}

async fn run_single(
    request: VampireRequest,
    worker_mode: VampireWorkerMode,
    lease: SolverPermit,
    deadline: Option<LocalDeadline>,
    overall_cancellation: CancellationToken,
) -> VampireInvocationOutcome {
    let context = InvocationContext::new(&request);
    let worker_cancellation = CancellationToken::new();
    let _cancellation_guard = CancellationGuard::new([worker_cancellation.clone()]);
    let worker_token = worker_cancellation.clone();
    let worker_request = request.worker_request(worker_mode.clone());
    let capture_policy = request.capture_policy;
    let worker_lease = Arc::new(lease);
    let closure_lease = Arc::clone(&worker_lease);
    let mut task = tokio::task::spawn_blocking(move || {
        let lease = closure_lease;
        let outcome = run_single_vampire_worker(worker_request, worker_token, capture_policy);
        poison_admission_on_run_failure(&outcome, &lease);
        outcome
    });
    // Retain this supervisor clone through final timeout/failure publication.
    // Worker clones still retain capacity if this async supervisor is dropped.

    let event = select_single_event(&mut task, &overall_cancellation, deadline).await;
    match event {
        SingleEvent::Worker(joined) => {
            observed_to_invocation(observe_join(joined, &worker_mode), &worker_mode)
        }
        SingleEvent::OverallCancelled => {
            worker_cancellation.cancel();
            let observed = observe_join(task.await, &worker_mode);
            interrupted_from_observed(observed)
        }
        SingleEvent::LocalTimeout => {
            worker_cancellation.cancel();
            let observed = observe_join(task.await, &worker_mode);
            timeout_from_observed(&context, observed)
        }
    }
}

enum SingleEvent<T> {
    Worker(Result<T, JoinError>),
    OverallCancelled,
    LocalTimeout,
}

async fn select_single_event<T: Send + 'static>(
    task: &mut tokio::task::JoinHandle<T>,
    overall_cancellation: &CancellationToken,
    deadline: Option<LocalDeadline>,
) -> SingleEvent<T> {
    let local_deadline = wait_for_deadline(deadline);
    tokio::pin!(local_deadline);
    tokio::select! {
        biased;
        _ = overall_cancellation.cancelled() => SingleEvent::OverallCancelled,
        result = task => SingleEvent::Worker(result),
        _ = &mut local_deadline => SingleEvent::LocalTimeout,
    }
}

// ------------------------------------------------------------
// Sequential Proof Lane
// ------------------------------------------------------------

#[derive(Clone)]
struct ProofLaneRequest {
    problem: VampireProblem,
    command: VampireWorkerCommand,
    attempt_id: AttemptId,
    artifacts: ArtifactStore,
    capture_policy: VampireCapturePolicy,
    search_budget: VampireSearchBudget,
}

impl ProofLaneRequest {
    fn new(request: &VampireRequest) -> Self {
        Self {
            problem: request.problem.clone(),
            command: request.command.clone(),
            attempt_id: request.attempt_id,
            artifacts: request.artifacts.clone(),
            capture_policy: request.capture_policy,
            search_budget: request.search_budget,
        }
    }

    /// One worker request for a proof-lane stage, under the limit that
    /// stage states to the solver.
    fn worker_request(
        &self,
        mode: VampireWorkerMode,
        stage_limit: Option<SolverTimeLimit>,
    ) -> VampireWorkerRequest {
        VampireWorkerRequest::from_attempt(
            self.problem.clone(),
            mode,
            self.command.clone(),
            self.attempt_id,
            self.artifacts.clone(),
            stage_limit,
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ProofCascTrigger {
    ConfiguredOnly,
    DirectCutoff,
    DirectUnknown,
}

impl ProofCascTrigger {
    fn telemetry_name(self) -> &'static str {
        match self {
            Self::ConfiguredOnly => "configured_only",
            Self::DirectCutoff => "direct_cutoff",
            Self::DirectUnknown => "direct_unknown",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ProofStageStop {
    Finished,
    LaneCancelled,
    PrefixCutoff,
}

struct ProofStageObservation {
    stop: ProofStageStop,
    observed: ObservedWorker,
}

#[allow(clippy::large_enum_variant)]
enum ProofStageEvent {
    Finished(Result<VampireWorkerOutcome, JoinError>),
    LaneCancelled,
    PrefixCutoff,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ProofCascAllocation {
    initial_limit: Duration,
    retry_added: Duration,
    total_limit: Duration,
    direct_limit: Duration,
    casc_limit: Duration,
}

impl ProofCascAllocation {
    fn new(policy: ProofCascPolicy, budget: VampireSearchBudget) -> Self {
        let initial_limit = budget
            .initial_limit()
            .expect("a finite proof search has an initial allowance");
        let total_limit = budget
            .total_limit()
            .expect("a finite proof search has a total allowance");
        let retry_added = budget.retry_added();
        let (direct_limit, casc_limit) = policy.split(total_limit, retry_added);
        Self {
            initial_limit,
            retry_added,
            total_limit,
            direct_limit,
            casc_limit,
        }
    }
}

/// How long the runner waits past a stage's own stated limit before it
/// stops that stage itself.
///
/// Every stage is told the limit it runs under, so the ordinary end of a
/// stage is the solver stopping and reporting — an honest inconclusive
/// result on the retry ladder, with its diagnostics. The runner's deadline
/// is the backstop for a solver that does not stop, and the grace is what
/// keeps the two from racing each other at the same instant. It is fixed
/// and small: it lengthens no search, because no stage is ever told it may
/// use it.
const SOLVER_STOP_GRACE: Duration = Duration::from_secs(2);

/// The runner's own deadline for one launch: the launch's allowance plus
/// one grace for each stage the launch may run in sequence. A proof lane
/// that may escalate runs two, one after the other, so a direct stage that
/// overruns its own limit cannot eat the portfolio's grace.
fn runner_backstop(allowance: Duration, request: &VampireRequest) -> Duration {
    let stages = if request.command.proof_casc_policy().is_disabled()
        || matches!(request.mode, VampireMode::FmbOnly(_))
    {
        1
    } else {
        2
    };
    allowance.saturating_add(SOLVER_STOP_GRACE.saturating_mul(stages))
}

async fn run_proof_lane(
    request: ProofLaneRequest,
    lease: Arc<SolverPermit>,
    lane_cancellation: CancellationToken,
    deadline: Option<LocalDeadline>,
) -> VampireWorkerOutcome {
    let policy = request.command.proof_casc_policy();
    let Some(deadline) = deadline else {
        debug_assert!(policy.is_disabled());
        return observed_to_worker_outcome(
            run_proof_stage(
                &request,
                VampireWorkerMode::ProofOnly,
                None,
                Arc::clone(&lease),
                &lane_cancellation,
                None,
            )
            .await
            .observed,
        );
    };
    let allocation = ProofCascAllocation::new(policy, request.search_budget);
    let direct_limit = allocation.direct_limit;
    let casc_limit = allocation.casc_limit;
    record_casc_allocation(&request.command, &allocation);
    if casc_limit.is_zero() {
        // One stage, and it is told the launch's whole allowance.
        return observed_to_worker_outcome(
            run_proof_stage(
                &request,
                VampireWorkerMode::ProofOnly,
                SolverTimeLimit::for_local_limit(allocation.total_limit),
                Arc::clone(&lease),
                &lane_cancellation,
                None,
            )
            .await
            .observed,
        );
    }

    let mut prior_failure = None;
    let mut prior_references = Vec::new();
    let mut prior_warnings = Vec::new();
    let trigger = if direct_limit.is_zero() {
        ProofCascTrigger::ConfiguredOnly
    } else {
        // The stage states its own prefix to the solver and is expected to
        // stop itself; the runner's cutoff is that prefix plus one fixed
        // grace, so a solver that overruns its own limit is still stopped
        // without eating the portfolio's share.
        let direct_deadline = LocalDeadline {
            started: deadline.started,
            limit: direct_limit.saturating_add(SOLVER_STOP_GRACE),
        };
        let direct = run_proof_stage(
            &request,
            VampireWorkerMode::ProofOnly,
            SolverTimeLimit::for_local_limit(direct_limit),
            Arc::clone(&lease),
            &lane_cancellation,
            Some(direct_deadline),
        )
        .await;
        match (direct.stop, direct.observed) {
            (ProofStageStop::LaneCancelled, observed) => {
                return observed_to_worker_outcome(observed);
            }
            (_, ObservedWorker::Conclusive(result)) => {
                return VampireWorkerOutcome::Result(result);
            }
            (_, ObservedWorker::RunFailure(report)) => {
                return VampireWorkerOutcome::RunFailure(report);
            }
            (_, ObservedWorker::Failure { report, .. }) if eligible_for_casc(&report) => {
                prior_references.extend_from_slice(report.artifact_references());
                let trigger = escalation_trigger(&report);
                prior_failure = Some(report);
                trigger
            }
            (ProofStageStop::PrefixCutoff, ObservedWorker::Cancelled(cancelled)) => {
                prior_references.extend_from_slice(cancelled.artifact_references());
                prior_warnings.extend_from_slice(cancelled.capture_warnings());
                ProofCascTrigger::DirectCutoff
            }
            (_, observed) => return observed_to_worker_outcome(observed),
        }
    };

    // Whether there is any lane time left at all is a runtime question and
    // is read from the clock; what the portfolio is *scheduled against* is
    // not, and comes from the allocation alone.
    if lane_cancellation.is_cancelled() || deadline.remaining().is_zero() {
        if !lane_cancellation.is_cancelled() {
            lane_cancellation.cancelled().await;
        }
        let mut cancelled =
            CancelledVampireWorker::from_prior_capture(prior_references, prior_warnings);
        cancelled.set_prior_failure(prior_failure);
        return VampireWorkerOutcome::Cancelled(cancelled);
    }
    let casc_allowance = allocation.casc_limit;
    record_casc_escalation(
        &request.command,
        trigger,
        &allocation,
        casc_allowance,
        prior_failure.as_ref(),
    );
    let casc_options = SolverTimeLimit::for_local_limit(casc_allowance)
        .expect("a CASC stage limit never exceeds the validated total lane allowance");
    let casc = run_casc_stage(&request, casc_options, lease, &lane_cancellation).await;
    match (prior_failure, casc) {
        (Some(prior), ObservedWorker::Failure { report, frontier }) => {
            let report = sequential_proof_failure(prior, report);
            VampireWorkerOutcome::Result(VampireResult::Failure {
                report: augment_proof_failure(report, &prior_references, &prior_warnings),
                next_fmb_start_size: frontier,
            })
        }
        (None, ObservedWorker::Failure { report, frontier }) => {
            VampireWorkerOutcome::Result(VampireResult::Failure {
                report: augment_proof_failure(report, &prior_references, &prior_warnings),
                next_fmb_start_size: frontier,
            })
        }
        (prior_failure, ObservedWorker::Cancelled(mut cancelled)) => {
            cancelled.extend_prior_capture(&prior_references, &prior_warnings);
            cancelled.set_prior_failure(prior_failure);
            VampireWorkerOutcome::Cancelled(cancelled)
        }
        (_, observed) => observed_to_worker_outcome(observed),
    }
}

async fn run_casc_stage(
    request: &ProofLaneRequest,
    options: SolverTimeLimit,
    lease: Arc<SolverPermit>,
    lane_cancellation: &CancellationToken,
) -> ObservedWorker {
    let mode = VampireWorkerMode::ProofCasc;
    let worker_request = request.worker_request(mode.clone(), Some(options));
    let capture_policy = request.capture_policy;
    // CASC is the terminal proof rung, so its worker observes the lane token
    // directly. If a peer or outer deadline won during the handoff, the
    // worker sees that cancellation before it can launch another process.
    let worker_token = lane_cancellation.clone();
    let task = tokio::task::spawn_blocking(move || {
        let outcome = run_single_vampire_worker(worker_request, worker_token, capture_policy);
        poison_admission_on_run_failure(&outcome, &lease);
        outcome
    });
    observe_join(task.await, &mode)
}

async fn run_proof_stage(
    request: &ProofLaneRequest,
    mode: VampireWorkerMode,
    stage_limit: Option<SolverTimeLimit>,
    lease: Arc<SolverPermit>,
    lane_cancellation: &CancellationToken,
    cutoff: Option<LocalDeadline>,
) -> ProofStageObservation {
    let stage_cancellation = CancellationToken::new();
    let _cancellation_guard = CancellationGuard::new([stage_cancellation.clone()]);
    let worker_request = request.worker_request(mode.clone(), stage_limit);
    let capture_policy = request.capture_policy;
    let stage_token = stage_cancellation.clone();
    let mut task = tokio::task::spawn_blocking(move || {
        let outcome = run_single_vampire_worker(worker_request, stage_token, capture_policy);
        poison_admission_on_run_failure(&outcome, &lease);
        outcome
    });
    let cutoff_wait = wait_for_deadline(cutoff);
    tokio::pin!(cutoff_wait);
    let event = tokio::select! {
        biased;
        _ = lane_cancellation.cancelled() => ProofStageEvent::LaneCancelled,
        _ = &mut cutoff_wait => ProofStageEvent::PrefixCutoff,
        result = &mut task => ProofStageEvent::Finished(result),
    };
    let (stop, observed) = match event {
        ProofStageEvent::Finished(joined) => {
            (ProofStageStop::Finished, observe_join(joined, &mode))
        }
        ProofStageEvent::LaneCancelled => {
            stage_cancellation.cancel();
            (
                ProofStageStop::LaneCancelled,
                observe_join(task.await, &mode),
            )
        }
        ProofStageEvent::PrefixCutoff => {
            stage_cancellation.cancel();
            (
                ProofStageStop::PrefixCutoff,
                observe_join(task.await, &mode),
            )
        }
    };
    ProofStageObservation { stop, observed }
}

/// Whether a direct stage's own report leaves the condition open in a way
/// the portfolio may still close.
///
/// The direct stage gives up (`SolverUnknown`) or runs out of the prefix it
/// was told (`CheckTimeout`); either way it has said nothing about the
/// condition and the portfolio is a different search, so the launch
/// escalates. A malformed output or a process failure does not: those are
/// faults, and running a second stage on top of one would hide it.
/// Why the portfolio is being run, read from what the direct stage itself
/// said rather than from which runner mechanism observed the stop.
///
/// The direct stage is told its prefix and ordinarily stops itself at it,
/// so the runner's cutoff is no longer what distinguishes "ran out of
/// time" from "gave up". The stage's own report is: it stopped at the
/// limit it was given, or it gave up before reaching it. The two are the
/// separate things a reader of these records wants counted — how often the
/// direct strategy was insufficient in time, and how often in power.
fn escalation_trigger(report: &FailureReport) -> ProofCascTrigger {
    match report.kind() {
        FailureKind::CheckTimeout => ProofCascTrigger::DirectCutoff,
        _ => ProofCascTrigger::DirectUnknown,
    }
}

fn eligible_for_casc(report: &FailureReport) -> bool {
    report.origin() == FailureOrigin::VampireProofSearch
        && matches!(
            report.kind(),
            FailureKind::SolverUnknown | FailureKind::CheckTimeout
        )
}

fn observed_to_worker_outcome(observed: ObservedWorker) -> VampireWorkerOutcome {
    match observed {
        ObservedWorker::Conclusive(result) => VampireWorkerOutcome::Result(result),
        ObservedWorker::Failure { report, frontier } => {
            VampireWorkerOutcome::Result(VampireResult::Failure {
                report,
                next_fmb_start_size: frontier,
            })
        }
        ObservedWorker::Cancelled(cancelled) => VampireWorkerOutcome::Cancelled(cancelled),
        ObservedWorker::RunFailure(report) => VampireWorkerOutcome::RunFailure(report),
    }
}

fn sequential_proof_failure(direct: FailureReport, casc: FailureReport) -> FailureReport {
    let mut references = casc.artifact_references().to_vec();
    for reference in direct.artifact_references() {
        if !references.contains(reference) {
            references.push(*reference);
        }
    }
    FailureReport::try_new(
        casc.origin(),
        casc.kind(),
        casc.retryable(),
        casc.scope(),
        Some(format!(
            "direct proof stage: origin={:?} kind={:?} detail={}\nCASC proof stage: origin={:?} kind={:?} detail={}",
            direct.origin(),
            direct.kind(),
            direct.detail().unwrap_or("none"),
            casc.origin(),
            casc.kind(),
            casc.detail().unwrap_or("none"),
        )),
        references,
    )
    .expect("a proof-stage failure remains valid with prior proof context")
}

fn augment_proof_failure(
    report: FailureReport,
    prior_references: &[ArtifactRef],
    prior_warnings: &[String],
) -> FailureReport {
    if prior_references.is_empty() && prior_warnings.is_empty() {
        return report;
    }
    let mut references = report.artifact_references().to_vec();
    for reference in prior_references {
        if !references.contains(reference) {
            references.push(*reference);
        }
    }
    let mut detail = report.detail().unwrap_or("proof search failed").to_string();
    if !prior_warnings.is_empty() {
        detail.push_str("\nprior proof-stage capture warnings:\n");
        detail.push_str(&prior_warnings.join("\n"));
    }
    FailureReport::try_new(
        report.origin(),
        report.kind(),
        report.retryable(),
        report.scope(),
        Some(detail),
        references,
    )
    .expect("adding prior proof-stage context preserves a valid failure classification")
}

fn record_casc_allocation(command: &VampireWorkerCommand, allocation: &ProofCascAllocation) {
    let policy = command.proof_casc_policy();
    command.telemetry().event_with("proof_casc_allocation", || {
        json!({
            "initial_share_millionths": policy.initial_share().millionths(),
            "retry_added_share_millionths": policy.retry_added_share().millionths(),
            "initial_limit_nanoseconds": duration_nanoseconds(allocation.initial_limit),
            "retry_added_nanoseconds": duration_nanoseconds(allocation.retry_added),
            "total_limit_nanoseconds": duration_nanoseconds(allocation.total_limit),
            "nominal_direct_prefix_nanoseconds": duration_nanoseconds(allocation.direct_limit),
            "nominal_casc_tail_nanoseconds": duration_nanoseconds(allocation.casc_limit),
        })
    });
}

fn record_casc_escalation(
    command: &VampireWorkerCommand,
    trigger: ProofCascTrigger,
    allocation: &ProofCascAllocation,
    stage_limit: Duration,
    direct_failure: Option<&FailureReport>,
) {
    let telemetry = command.telemetry();
    let policy = command.proof_casc_policy();
    telemetry.increment("solver.proof_casc_escalations", 1);
    telemetry.increment(
        format!("solver.proof_casc_escalations.{}", trigger.telemetry_name()),
        1,
    );
    telemetry.event_with("proof_casc_escalated", || {
        json!({
            "trigger": trigger.telemetry_name(),
            "initial_share_millionths": policy.initial_share().millionths(),
            "retry_added_share_millionths": policy.retry_added_share().millionths(),
            "initial_limit_nanoseconds": duration_nanoseconds(allocation.initial_limit),
            "retry_added_nanoseconds": duration_nanoseconds(allocation.retry_added),
            "total_limit_nanoseconds": duration_nanoseconds(allocation.total_limit),
            "nominal_direct_prefix_nanoseconds": duration_nanoseconds(allocation.direct_limit),
            "nominal_casc_tail_nanoseconds": duration_nanoseconds(allocation.casc_limit),
            // The limit the portfolio was launched under. It is a function
            // of the allocation only, so two runs of the same campaign
            // record the same number here.
            "stage_limit_nanoseconds": duration_nanoseconds(stage_limit),
            // What the direct stage said before handing over. The winning
            // proof carries no room for it, so this is where the reason
            // the portfolio ran at all survives a portfolio that proves.
            "direct_failure": direct_failure.map(|report| json!({
                "origin": format!("{:?}", report.origin()),
                "kind": format!("{:?}", report.kind()),
            })),
        })
    });
}

fn duration_nanoseconds(duration: Duration) -> u64 {
    duration.as_nanos().min(u128::from(u64::MAX)) as u64
}

// ------------------------------------------------------------
// Paired Proof/FMB Arbitration
// ------------------------------------------------------------

/// Run the same proof ladder and FMB contour as a paired request while using
/// exactly one process slot.  Each lane receives the request's complete
/// finite allowance; only wall-clock scheduling changes.  Both lanes retain
/// the outer request's single attempt identity.
async fn run_pair_serial(
    request: VampireRequest,
    options: FmbOptions,
    lease: SolverPermit,
    overall_cancellation: CancellationToken,
) -> VampireInvocationOutcome {
    let lane_limit = runner_backstop(
        request
            .search_budget
            .total_limit()
            .expect("strict-serial pair construction requires a finite lane allowance"),
        &request,
    );
    let context = InvocationContext::new(&request);
    let lease = Arc::new(lease);
    let proof_cancellation = CancellationToken::new();
    let _proof_guard = CancellationGuard::new([proof_cancellation.clone()]);
    let proof_request = ProofLaneRequest::new(&request);
    let mut proof_task = tokio::spawn(run_proof_lane(
        proof_request,
        Arc::clone(&lease),
        proof_cancellation.clone(),
        Some(LocalDeadline::start(lane_limit)),
    ));
    let proof_event = select_single_event(
        &mut proof_task,
        &overall_cancellation,
        Some(LocalDeadline::start(lane_limit)),
    )
    .await;

    let proof_failure: Option<FailureReport>;
    let mut prior_cancellations = Vec::new();
    match proof_event {
        SingleEvent::Worker(joined) => match observe_join(joined, &VampireWorkerMode::ProofOnly) {
            ObservedWorker::Conclusive(result) => {
                return VampireInvocationOutcome::Result(result);
            }
            ObservedWorker::Failure { report, .. } => proof_failure = Some(report),
            ObservedWorker::Cancelled(cancelled) => {
                proof_failure = cancelled.prior_failure().cloned();
                prior_cancellations.push(cancelled);
            }
            ObservedWorker::RunFailure(report) => {
                return VampireInvocationOutcome::RunFailure(report);
            }
        },
        SingleEvent::OverallCancelled => {
            proof_cancellation.cancel();
            let observed = observe_join(proof_task.await, &VampireWorkerMode::ProofOnly);
            return interrupted_from_serial_observations(observed, None);
        }
        SingleEvent::LocalTimeout => {
            proof_cancellation.cancel();
            match observe_join(proof_task.await, &VampireWorkerMode::ProofOnly) {
                ObservedWorker::Conclusive(result) => {
                    return VampireInvocationOutcome::Result(result);
                }
                ObservedWorker::Failure { report, .. } => proof_failure = Some(report),
                ObservedWorker::Cancelled(cancelled) => {
                    proof_failure = serial_timeout_failure(
                        FailureOrigin::VampireProofSearch,
                        "strict-serial proof lane exhausted its complete allowance",
                        &cancelled,
                    );
                    prior_cancellations.push(cancelled);
                }
                ObservedWorker::RunFailure(report) => {
                    return VampireInvocationOutcome::RunFailure(report);
                }
            }
        }
    }

    if overall_cancellation.is_cancelled() {
        return cancelled_invocation(None, proof_failure, prior_cancellations);
    }

    let fmb_cancellation = CancellationToken::new();
    let _fmb_guard = CancellationGuard::new([fmb_cancellation.clone()]);
    let worker_mode = VampireWorkerMode::FmbOnly(options);
    let worker_request = request.worker_request(worker_mode.clone());
    let capture_policy = request.capture_policy;
    let worker_token = fmb_cancellation.clone();
    let worker_lease = Arc::clone(&lease);
    let mut fmb_task = tokio::task::spawn_blocking(move || {
        let outcome = run_single_vampire_worker(worker_request, worker_token, capture_policy);
        poison_admission_on_run_failure(&outcome, &worker_lease);
        outcome
    });
    let fmb_event = select_single_event(
        &mut fmb_task,
        &overall_cancellation,
        Some(LocalDeadline::start(lane_limit)),
    )
    .await;
    match fmb_event {
        SingleEvent::Worker(joined) => match observe_join(joined, &worker_mode) {
            ObservedWorker::Conclusive(result) => VampireInvocationOutcome::Result(result),
            ObservedWorker::Failure { report, frontier } => {
                VampireInvocationOutcome::Result(VampireResult::Failure {
                    report: combined_failure(proof_failure, Some(report))
                        .expect("a finished FMB failure produces one report"),
                    next_fmb_start_size: frontier,
                })
            }
            ObservedWorker::Cancelled(cancelled) => {
                prior_cancellations.push(cancelled);
                cancelled_invocation(None, proof_failure, prior_cancellations)
            }
            ObservedWorker::RunFailure(report) => VampireInvocationOutcome::RunFailure(report),
        },
        SingleEvent::OverallCancelled => {
            fmb_cancellation.cancel();
            let observed = observe_join(fmb_task.await, &worker_mode);
            interrupted_from_serial_state(proof_failure, prior_cancellations, observed)
        }
        SingleEvent::LocalTimeout => {
            fmb_cancellation.cancel();
            match observe_join(fmb_task.await, &worker_mode) {
                ObservedWorker::Conclusive(result) => VampireInvocationOutcome::Result(result),
                ObservedWorker::RunFailure(report) => VampireInvocationOutcome::RunFailure(report),
                ObservedWorker::Failure { report, frontier } => timeout_result(
                    &context,
                    frontier,
                    combined_failure(proof_failure, Some(report)),
                ),
                ObservedWorker::Cancelled(cancelled) => {
                    let frontier = cancelled.next_fmb_start_size();
                    let fmb_failure = serial_timeout_failure(
                        FailureOrigin::VampireFiniteModelBuilding,
                        "strict-serial FMB lane exhausted its complete allowance",
                        &cancelled,
                    );
                    timeout_result(
                        &context,
                        frontier,
                        combined_failure(proof_failure, fmb_failure),
                    )
                }
            }
        }
    }
}

fn serial_timeout_failure(
    origin: FailureOrigin,
    detail: &str,
    cancelled: &CancelledVampireWorker,
) -> Option<FailureReport> {
    let mut references = cancelled.artifact_references().to_vec();
    let prior = cancelled.prior_failure();
    if let Some(prior) = prior {
        for reference in prior.artifact_references() {
            if !references.contains(reference) {
                references.push(*reference);
            }
        }
    }
    let warnings = cancelled.capture_warnings();
    Some(
        FailureReport::try_new(
            origin,
            FailureKind::SolverUnknown,
            false,
            FailureScope::LaneLocal,
            Some(if warnings.is_empty() {
                detail.to_string()
            } else {
                format!("{detail}; capture warnings: {}", warnings.join("; "))
            }),
            references,
        )
        .expect("a serial lane timeout is a nonlogical solver miss"),
    )
}

fn interrupted_from_serial_observations(
    proof: ObservedWorker,
    fmb: Option<ObservedWorker>,
) -> VampireInvocationOutcome {
    let mut proof_failure = None;
    let mut cancellations = Vec::new();
    match proof {
        ObservedWorker::RunFailure(report) => return VampireInvocationOutcome::RunFailure(report),
        ObservedWorker::Failure { report, .. } => proof_failure = Some(report),
        ObservedWorker::Cancelled(cancelled) => cancellations.push(cancelled),
        ObservedWorker::Conclusive(_) => {}
    }
    match fmb {
        Some(observed) => interrupted_from_serial_state(proof_failure, cancellations, observed),
        None => cancelled_invocation(None, proof_failure, cancellations),
    }
}

fn interrupted_from_serial_state(
    proof_failure: Option<FailureReport>,
    mut cancellations: Vec<CancelledVampireWorker>,
    fmb: ObservedWorker,
) -> VampireInvocationOutcome {
    match fmb {
        ObservedWorker::RunFailure(report) => VampireInvocationOutcome::RunFailure(report),
        ObservedWorker::Failure { report, frontier } => cancelled_invocation(
            frontier,
            combined_failure(proof_failure, Some(report)),
            cancellations,
        ),
        ObservedWorker::Cancelled(cancelled) => {
            let frontier = cancelled.next_fmb_start_size();
            cancellations.push(cancelled);
            cancelled_invocation(frontier, proof_failure, cancellations)
        }
        ObservedWorker::Conclusive(_) => cancelled_invocation(None, proof_failure, cancellations),
    }
}

async fn run_pair(
    request: VampireRequest,
    options: FmbOptions,
    lease: SolverPermit,
    deadline: Option<LocalDeadline>,
    overall_cancellation: CancellationToken,
) -> VampireInvocationOutcome {
    let context = InvocationContext::new(&request);
    let proof_cancellation = CancellationToken::new();
    let fmb_cancellation = CancellationToken::new();
    let _cancellation_guard =
        CancellationGuard::new([proof_cancellation.clone(), fmb_cancellation.clone()]);
    let proof_request = ProofLaneRequest::new(&request);
    let fmb_request = request.worker_request(VampireWorkerMode::FmbOnly(options));
    let capture_policy = request.capture_policy;

    // Each closure owns the shared lease. Capacity therefore survives an
    // interrupted supervisor until both process trees have been discharged.
    let worker_lease = Arc::new(lease);
    let proof_lease = Arc::clone(&worker_lease);
    let proof_token = proof_cancellation.clone();
    let mut proof_task = tokio::spawn(run_proof_lane(
        proof_request,
        proof_lease,
        proof_token,
        deadline,
    ));
    let fmb_lease = Arc::clone(&worker_lease);
    let fmb_token = fmb_cancellation.clone();
    let mut fmb_task = tokio::task::spawn_blocking(move || {
        let lease = fmb_lease;
        let outcome = run_single_vampire_worker(fmb_request, fmb_token, capture_policy);
        poison_admission_on_run_failure(&outcome, &lease);
        outcome
    });
    // Retain this supervisor clone through arbitration and final publication.

    let local_deadline = wait_for_deadline(deadline);
    tokio::pin!(local_deadline);
    let mut proof_done = false;
    let mut fmb_done = false;
    let mut proof_failure = None;
    let mut fmb_failure = None;
    let mut fmb_frontier = None;

    loop {
        let event = tokio::select! {
            biased;
            _ = overall_cancellation.cancelled() => PairEvent::OverallCancelled,
            result = &mut proof_task, if !proof_done => PairEvent::Proof(result),
            result = &mut fmb_task, if !fmb_done => PairEvent::Fmb(result),
            _ = &mut local_deadline => PairEvent::LocalTimeout,
        };
        match event {
            PairEvent::Proof(joined) => {
                proof_done = true;
                match observe_join(joined, &VampireWorkerMode::ProofOnly) {
                    ObservedWorker::Conclusive(result) => {
                        fmb_cancellation.cancel();
                        match await_cleanup(
                            &mut fmb_task,
                            fmb_done,
                            &request.command,
                            WorkerLane::Proof,
                        )
                        .await
                        {
                            CleanupObservation::None | CleanupObservation::RequiredArtifact => {}
                            CleanupObservation::RunFailure(report) => {
                                return VampireInvocationOutcome::RunFailure(report);
                            }
                        }
                        return VampireInvocationOutcome::Result(result);
                    }
                    ObservedWorker::Failure { report, .. } => proof_failure = Some(report),
                    ObservedWorker::RunFailure(report) => {
                        fmb_cancellation.cancel();
                        let _ = await_cleanup(
                            &mut fmb_task,
                            fmb_done,
                            &request.command,
                            WorkerLane::Proof,
                        )
                        .await;
                        return VampireInvocationOutcome::RunFailure(report);
                    }
                    ObservedWorker::Cancelled(cancelled) => {
                        proof_failure = Some(unexpected_cancellation(
                            FailureOrigin::VampireProofSearch,
                            cancelled,
                        ));
                    }
                }
            }
            PairEvent::Fmb(joined) => {
                fmb_done = true;
                match observe_join(joined, &VampireWorkerMode::FmbOnly(options)) {
                    ObservedWorker::Conclusive(result) => {
                        proof_cancellation.cancel();
                        match await_cleanup(
                            &mut proof_task,
                            proof_done,
                            &request.command,
                            WorkerLane::Fmb,
                        )
                        .await
                        {
                            CleanupObservation::None | CleanupObservation::RequiredArtifact => {}
                            CleanupObservation::RunFailure(report) => {
                                return VampireInvocationOutcome::RunFailure(report);
                            }
                        }
                        return VampireInvocationOutcome::Result(result);
                    }
                    ObservedWorker::Failure { report, frontier } => {
                        fmb_frontier = frontier;
                        fmb_failure = Some(report);
                    }
                    ObservedWorker::RunFailure(report) => {
                        proof_cancellation.cancel();
                        let _ = await_cleanup(
                            &mut proof_task,
                            proof_done,
                            &request.command,
                            WorkerLane::Fmb,
                        )
                        .await;
                        return VampireInvocationOutcome::RunFailure(report);
                    }
                    ObservedWorker::Cancelled(cancelled) => {
                        fmb_frontier = cancelled.next_fmb_start_size();
                        fmb_failure = Some(unexpected_cancellation(
                            FailureOrigin::VampireFiniteModelBuilding,
                            cancelled,
                        ));
                    }
                }
            }
            PairEvent::OverallCancelled => {
                proof_cancellation.cancel();
                fmb_cancellation.cancel();
                let mut interrupted = InterruptedState {
                    proof_failure,
                    fmb_failure,
                    fmb_frontier,
                    ..InterruptedState::default()
                };
                if !proof_done {
                    interrupted.observe(
                        WorkerLane::Proof,
                        observe_join(proof_task.await, &VampireWorkerMode::ProofOnly),
                    );
                }
                if !fmb_done {
                    interrupted.observe(
                        WorkerLane::Fmb,
                        observe_join(fmb_task.await, &VampireWorkerMode::FmbOnly(options)),
                    );
                }
                return interrupted.finish_cancelled();
            }
            PairEvent::LocalTimeout => {
                proof_cancellation.cancel();
                fmb_cancellation.cancel();
                let mut interrupted = InterruptedState {
                    proof_failure,
                    fmb_failure,
                    fmb_frontier,
                    ..InterruptedState::default()
                };
                if !proof_done {
                    interrupted.observe(
                        WorkerLane::Proof,
                        observe_join(proof_task.await, &VampireWorkerMode::ProofOnly),
                    );
                }
                if !fmb_done {
                    interrupted.observe(
                        WorkerLane::Fmb,
                        observe_join(fmb_task.await, &VampireWorkerMode::FmbOnly(options)),
                    );
                }
                return interrupted.finish_timeout(&context);
            }
        }

        if proof_done && fmb_done {
            let proof = proof_failure.expect("a nonconclusive proof worker records a failure");
            let fmb = fmb_failure.expect("a nonconclusive FMB worker records a failure");
            return VampireInvocationOutcome::Result(VampireResult::Failure {
                report: combined_failure(Some(proof), Some(fmb))
                    .expect("two completed failures produce one report"),
                next_fmb_start_size: fmb_frontier,
            });
        }
    }
}

enum PairEvent {
    Proof(Result<VampireWorkerOutcome, JoinError>),
    Fmb(Result<VampireWorkerOutcome, JoinError>),
    OverallCancelled,
    LocalTimeout,
}

fn poison_admission_on_run_failure(outcome: &VampireWorkerOutcome, lease: &SolverPermit) {
    if let VampireWorkerOutcome::RunFailure(report) = outcome {
        // Capacity remains quarantined. The report is also the truthful
        // failure returned to every waiter woken by admission closure.
        lease.poison(report.clone());
    }
}

/// Reap the lane that lost the race, and record it if that lane had in
/// fact concluded too.
///
/// The proof lane can only prove and the finite-model lane can only refute,
/// so two conclusive lanes on one query are two opposite verdicts about the
/// same formula — a solver unsoundness, not a tie. The arbitration still
/// takes the lane it observed first, because there is nothing better to do
/// with the pair; what this adds is that the event is counted rather than
/// discarded in silence.
async fn await_cleanup(
    task: &mut tokio::task::JoinHandle<VampireWorkerOutcome>,
    already_done: bool,
    command: &VampireWorkerCommand,
    winner: WorkerLane,
) -> CleanupObservation {
    if already_done {
        return CleanupObservation::None;
    }
    let observed = task.await;
    if let Ok(VampireWorkerOutcome::Result(VampireResult::Proved(_) | VampireResult::Refuted(_))) =
        &observed
    {
        let telemetry = command.telemetry();
        telemetry.increment("solver.lane_disagreements", 1);
        telemetry.event_with("lane_disagreement", || {
            json!({
                "accepted_lane": match winner {
                    WorkerLane::Proof => "proof",
                    WorkerLane::Fmb => "finite_model",
                },
            })
        });
    }
    match observed {
        Ok(VampireWorkerOutcome::RunFailure(report)) => CleanupObservation::RunFailure(report),
        Ok(VampireWorkerOutcome::Result(VampireResult::Failure { report, .. }))
            if is_required_artifact_failure(&report) =>
        {
            CleanupObservation::RequiredArtifact
        }
        _ => CleanupObservation::None,
    }
}

enum CleanupObservation {
    None,
    RequiredArtifact,
    RunFailure(FailureReport),
}

// ------------------------------------------------------------
// Worker Outcome Normalization
// ------------------------------------------------------------

enum ObservedWorker {
    Conclusive(VampireResult),
    Failure {
        report: FailureReport,
        frontier: Option<FmbSize>,
    },
    Cancelled(CancelledVampireWorker),
    RunFailure(FailureReport),
}

fn observe_join(
    joined: Result<VampireWorkerOutcome, JoinError>,
    mode: &VampireWorkerMode,
) -> ObservedWorker {
    let origin = worker_origin(mode);
    match joined {
        Ok(VampireWorkerOutcome::Result(VampireResult::Failure {
            report,
            next_fmb_start_size,
        })) => ObservedWorker::Failure {
            report,
            frontier: next_fmb_start_size,
        },
        Ok(VampireWorkerOutcome::Result(VampireResult::TimedOut { .. })) => {
            ObservedWorker::Failure {
                report: FailureReport::vampire_worker_failure(
                    origin,
                    "a raw Vampire worker returned an orchestration-level timeout",
                    Vec::new(),
                ),
                frontier: None,
            }
        }
        Ok(VampireWorkerOutcome::Result(result)) => ObservedWorker::Conclusive(result),
        Ok(VampireWorkerOutcome::Cancelled(cancelled)) => ObservedWorker::Cancelled(cancelled),
        Ok(VampireWorkerOutcome::RunFailure(report)) => ObservedWorker::RunFailure(report),
        Err(error) => ObservedWorker::Failure {
            report: FailureReport::vampire_worker_failure(
                origin,
                format!("Vampire worker task failed before returning a result: {error}"),
                Vec::new(),
            ),
            frontier: None,
        },
    }
}

fn observed_to_invocation(
    observed: ObservedWorker,
    mode: &VampireWorkerMode,
) -> VampireInvocationOutcome {
    match observed {
        ObservedWorker::Conclusive(result) => VampireInvocationOutcome::Result(result),
        ObservedWorker::Failure { report, frontier } => {
            VampireInvocationOutcome::Result(VampireResult::Failure {
                report,
                next_fmb_start_size: frontier,
            })
        }
        ObservedWorker::Cancelled(cancelled) => {
            let next_fmb_start_size = cancelled.next_fmb_start_size();
            VampireInvocationOutcome::Result(VampireResult::Failure {
                report: unexpected_cancellation(worker_origin(mode), cancelled),
                next_fmb_start_size,
            })
        }
        ObservedWorker::RunFailure(report) => VampireInvocationOutcome::RunFailure(report),
    }
}

fn interrupted_from_observed(observed: ObservedWorker) -> VampireInvocationOutcome {
    match observed {
        ObservedWorker::RunFailure(report) => VampireInvocationOutcome::RunFailure(report),
        ObservedWorker::Cancelled(cancelled) => {
            let prior_failure = cancelled.prior_failure().cloned();
            cancelled_invocation(
                cancelled.next_fmb_start_size(),
                prior_failure,
                vec![cancelled],
            )
        }
        ObservedWorker::Failure { report, frontier } => {
            cancelled_invocation(frontier, Some(report), Vec::new())
        }
        ObservedWorker::Conclusive(_) => cancelled_invocation(None, None, Vec::new()),
    }
}

fn timeout_from_observed(
    context: &InvocationContext,
    observed: ObservedWorker,
) -> VampireInvocationOutcome {
    match observed {
        ObservedWorker::RunFailure(report) => VampireInvocationOutcome::RunFailure(report),
        ObservedWorker::Cancelled(cancelled) => {
            let prior_failure = cancelled.prior_failure().cloned();
            timeout_result(context, cancelled.next_fmb_start_size(), prior_failure)
        }
        ObservedWorker::Failure { frontier, .. } => timeout_result(context, frontier, None),
        ObservedWorker::Conclusive(_) => timeout_result(context, None, None),
    }
}

fn unexpected_cancellation(
    origin: FailureOrigin,
    cancelled: CancelledVampireWorker,
) -> FailureReport {
    FailureReport::vampire_worker_failure(
        origin,
        "Vampire worker cancelled without an authoritative scheduler interruption",
        cancelled.artifact_references().to_vec(),
    )
}

fn worker_origin(mode: &VampireWorkerMode) -> FailureOrigin {
    match mode {
        VampireWorkerMode::ProofOnly | VampireWorkerMode::ProofCasc => {
            FailureOrigin::VampireProofSearch
        }
        VampireWorkerMode::FmbOnly(_) => FailureOrigin::VampireFiniteModelBuilding,
    }
}

// ------------------------------------------------------------
// Timeout And Cancellation Settlement
// ------------------------------------------------------------

#[derive(Default)]
struct InterruptedState {
    proof_failure: Option<FailureReport>,
    fmb_failure: Option<FailureReport>,
    fmb_frontier: Option<FmbSize>,
    cancellations: Vec<CancelledVampireWorker>,
    run_failure: Option<FailureReport>,
}

impl InterruptedState {
    fn observe(&mut self, lane: WorkerLane, observed: ObservedWorker) {
        match observed {
            ObservedWorker::Conclusive(_) => {}
            ObservedWorker::Failure { report, frontier } => match lane {
                WorkerLane::Proof => self.proof_failure = Some(report),
                WorkerLane::Fmb => {
                    self.fmb_failure = Some(report);
                    self.fmb_frontier = frontier;
                }
            },
            ObservedWorker::Cancelled(cancelled) => {
                if lane == WorkerLane::Fmb {
                    self.fmb_frontier = cancelled.next_fmb_start_size();
                } else if self.proof_failure.is_none() {
                    self.proof_failure = cancelled.prior_failure().cloned();
                }
                self.cancellations.push(cancelled);
            }
            ObservedWorker::RunFailure(report) => self.run_failure = Some(report),
        }
    }

    fn finish_cancelled(self) -> VampireInvocationOutcome {
        if let Some(report) = self.run_failure {
            return VampireInvocationOutcome::RunFailure(report);
        }
        cancelled_invocation(
            self.fmb_frontier,
            combined_failure(self.proof_failure, self.fmb_failure),
            self.cancellations,
        )
    }

    fn finish_timeout(self, context: &InvocationContext) -> VampireInvocationOutcome {
        if let Some(report) = self.run_failure {
            return VampireInvocationOutcome::RunFailure(report);
        }
        timeout_result(
            context,
            self.fmb_frontier,
            combined_failure(self.proof_failure, self.fmb_failure),
        )
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum WorkerLane {
    Proof,
    Fmb,
}

fn combined_failure(
    proof: Option<FailureReport>,
    fmb: Option<FailureReport>,
) -> Option<FailureReport> {
    match (proof, fmb) {
        (Some(proof), Some(fmb)) if is_required_artifact_failure(&proof) => {
            Some(required_artifact_with_peer_context(proof, &fmb))
        }
        (Some(proof), Some(fmb)) if is_required_artifact_failure(&fmb) => {
            Some(required_artifact_with_peer_context(fmb, &proof))
        }
        (Some(proof), Some(fmb)) => Some(FailureReport::concurrent_vampire_failures(&proof, &fmb)),
        (Some(report), None) | (None, Some(report)) => Some(report),
        (None, None) => None,
    }
}

fn is_required_artifact_failure(report: &FailureReport) -> bool {
    report.origin() == FailureOrigin::ArtifactSettlement
        && matches!(
            report.kind(),
            FailureKind::PublicationFailure | FailureKind::InfrastructureFailure
        )
}

fn required_artifact_with_peer_context(
    primary: FailureReport,
    peer: &FailureReport,
) -> FailureReport {
    let mut references = primary.artifact_references().to_vec();
    for reference in peer.artifact_references() {
        if !references.contains(reference) {
            references.push(*reference);
        }
    }
    FailureReport::try_new(
        primary.origin(),
        primary.kind(),
        primary.retryable(),
        primary.scope(),
        Some(format!(
            "{}\npeer worker: origin={:?} kind={:?} detail={}",
            primary
                .detail()
                .unwrap_or("required artifact publication failed"),
            peer.origin(),
            peer.kind(),
            peer.detail().unwrap_or("none"),
        )),
        references,
    )
    .expect("preserving a valid required-artifact failure remains valid")
}

fn timeout_result(
    context: &InvocationContext,
    next_fmb_start_size: Option<FmbSize>,
    peer_failure: Option<FailureReport>,
) -> VampireInvocationOutcome {
    let metadata = json!({
        "kind": "vampire_timeout",
        "problem_identity": context.problem_identity.as_ref(),
        "attempt_id": context.attempt_id.get(),
        "proof_casc_profile": super::PROOF_CASC_PROFILE_ID,
        "proof_casc_initial_share_millionths": context.proof_casc_initial_share_millionths,
        "proof_casc_retry_added_share_millionths": context.proof_casc_retry_added_share_millionths,
        "proof_initial_limit_nanoseconds": context.proof_initial_limit_nanoseconds,
        "proof_retry_added_nanoseconds": context.proof_retry_added_nanoseconds,
        "proof_total_limit_nanoseconds": context.proof_total_limit_nanoseconds,
        "nominal_direct_prefix_nanoseconds": context.nominal_direct_prefix_nanoseconds,
        "nominal_casc_tail_nanoseconds": context.nominal_casc_tail_nanoseconds,
        "next_fmb_start_size": next_fmb_start_size.map(FmbSize::get),
        "peer_failure": peer_failure.as_ref().map(|report| json!({
            "origin": format!("{:?}", report.origin()),
            "kind": format!("{:?}", report.kind()),
        })),
    });
    if let Err(report) = context.artifacts.publish(
        ArtifactKind::RuntimeTrace,
        metadata.to_string().into_bytes().into_boxed_slice(),
    ) {
        if report.scope() == FailureScope::RunGlobal {
            context.admission.poison(report.clone());
            return VampireInvocationOutcome::RunFailure(report);
        }
        return VampireInvocationOutcome::Result(VampireResult::Failure {
            report,
            next_fmb_start_size,
        });
    }
    VampireInvocationOutcome::Result(VampireResult::TimedOut {
        next_fmb_start_size,
        peer_failure,
    })
}

fn cancelled_invocation(
    next_fmb_start_size: Option<FmbSize>,
    peer_failure: Option<FailureReport>,
    cancellations: Vec<CancelledVampireWorker>,
) -> VampireInvocationOutcome {
    let mut artifact_references = Vec::new();
    let mut capture_warnings = Vec::new();
    for cancelled in cancellations {
        artifact_references.extend_from_slice(cancelled.artifact_references());
        capture_warnings.extend_from_slice(cancelled.capture_warnings());
    }
    VampireInvocationOutcome::Cancelled(CancelledVampireInvocation {
        next_fmb_start_size,
        peer_failure,
        artifact_references,
        capture_warnings,
    })
}

struct InvocationContext {
    problem_identity: Arc<str>,
    attempt_id: AttemptId,
    artifacts: ArtifactStore,
    admission: SolverAdmission,
    proof_casc_initial_share_millionths: u32,
    proof_casc_retry_added_share_millionths: u32,
    proof_initial_limit_nanoseconds: Option<u64>,
    proof_retry_added_nanoseconds: Option<u64>,
    proof_total_limit_nanoseconds: Option<u64>,
    nominal_direct_prefix_nanoseconds: Option<u64>,
    nominal_casc_tail_nanoseconds: Option<u64>,
}

impl InvocationContext {
    fn new(request: &VampireRequest) -> Self {
        let policy = request.command.proof_casc_policy();
        let allocation = if matches!(
            request.mode,
            VampireMode::ProofOnly | VampireMode::ProofAndFmb(_)
        ) {
            request
                .search_budget
                .total_limit()
                .map(|_| ProofCascAllocation::new(policy, request.search_budget))
        } else {
            None
        };
        Self {
            problem_identity: request.problem.identity_arc(),
            attempt_id: request.attempt_id,
            artifacts: request.artifacts.scoped(ScopeTag::named("timeout")),
            admission: request.admission.clone(),
            proof_casc_initial_share_millionths: policy.initial_share().millionths(),
            proof_casc_retry_added_share_millionths: policy.retry_added_share().millionths(),
            proof_initial_limit_nanoseconds: allocation
                .map(|allocation| duration_nanoseconds(allocation.initial_limit)),
            proof_retry_added_nanoseconds: allocation
                .map(|allocation| duration_nanoseconds(allocation.retry_added)),
            proof_total_limit_nanoseconds: allocation
                .map(|allocation| duration_nanoseconds(allocation.total_limit)),
            nominal_direct_prefix_nanoseconds: allocation
                .map(|allocation| duration_nanoseconds(allocation.direct_limit)),
            nominal_casc_tail_nanoseconds: allocation
                .map(|allocation| duration_nanoseconds(allocation.casc_limit)),
        }
    }
}

impl VampireRequest {
    /// One worker request for the finite-model lane.
    ///
    /// That lane is never split into stages and must stay alive for as
    /// long as the proof lane can still run, so it states the launch's own
    /// outer deadline — the allowance plus the runner's fixed grace per
    /// proof stage — rather than the bare allowance. Stating the bare
    /// allowance would end it just as a direct stage that used its whole
    /// prefix handed over to the portfolio, throwing away a model the
    /// lane might still have found. What ends this lane is the race: the
    /// other lane concluding, or the launch deadline.
    fn worker_request(&self, mode: VampireWorkerMode) -> VampireWorkerRequest {
        VampireWorkerRequest::from_attempt(
            self.problem.clone(),
            mode,
            self.command.clone(),
            self.attempt_id,
            self.artifacts.clone(),
            self.search_budget
                .total_limit()
                .map(|allowance| runner_backstop(allowance, self))
                .and_then(SolverTimeLimit::for_local_limit),
        )
    }
}

#[derive(Clone, Copy)]
struct LocalDeadline {
    started: Instant,
    limit: Duration,
}

impl LocalDeadline {
    fn start(limit: Duration) -> Self {
        Self {
            started: Instant::now(),
            limit,
        }
    }

    fn remaining(self) -> Duration {
        self.limit.saturating_sub(self.started.elapsed())
    }
}

async fn wait_for_deadline(deadline: Option<LocalDeadline>) {
    match deadline {
        Some(deadline) => loop {
            let elapsed = deadline.started.elapsed();
            if elapsed >= deadline.limit {
                return;
            }
            // A one-day chunk is representable on supported runtimes. Re-read
            // elapsed time after each chunk so Duration::MAX is also valid.
            let remaining = deadline.limit - elapsed;
            tokio::time::sleep(remaining.min(Duration::from_secs(86_400))).await;
        },
        None => pending::<()>().await,
    }
}

struct CancellationGuard<const N: usize> {
    tokens: [CancellationToken; N],
}

impl<const N: usize> CancellationGuard<N> {
    fn new(tokens: [CancellationToken; N]) -> Self {
        Self { tokens }
    }
}

impl<const N: usize> Drop for CancellationGuard<N> {
    fn drop(&mut self) {
        for token in &self.tokens {
            token.cancel();
        }
    }
}

// ------------------------------------------------------------
// Tests
// ------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn task_panic_becomes_a_lane_local_worker_failure() {
        let joined = tokio::task::spawn_blocking(|| -> VampireWorkerOutcome {
            panic!("worker panic fixture")
        })
        .await;
        let ObservedWorker::Failure { report, .. } =
            observe_join(joined, &VampireWorkerMode::ProofOnly)
        else {
            panic!("worker panic was not classified as failure")
        };
        assert_eq!(report.origin(), FailureOrigin::VampireProofSearch);
        assert_eq!(report.scope(), FailureScope::LaneLocal);
    }

    /// A direct stage that ran out of the prefix it was given and one that
    /// gave up before reaching it are the two things a reader of these
    /// records wants counted separately — how often the direct strategy
    /// was insufficient in time, and how often in power. The trigger comes
    /// from what the stage itself reported, because the stage now stops
    /// itself and the runner's cutoff no longer distinguishes them.
    #[test]
    fn the_escalation_trigger_follows_what_the_direct_stage_reported() {
        let report = |kind| {
            FailureReport::try_new(
                FailureOrigin::VampireProofSearch,
                kind,
                false,
                FailureScope::LaneLocal,
                None,
                Vec::new(),
            )
            .unwrap()
        };
        let timed_out = report(FailureKind::CheckTimeout);
        let gave_up = report(FailureKind::SolverUnknown);
        assert_eq!(
            escalation_trigger(&timed_out),
            ProofCascTrigger::DirectCutoff
        );
        assert_eq!(
            escalation_trigger(&gave_up),
            ProofCascTrigger::DirectUnknown
        );
        // Both still escalate; a fault does not.
        assert!(eligible_for_casc(&timed_out));
        assert!(eligible_for_casc(&gave_up));
        assert!(!eligible_for_casc(&report(FailureKind::MalformedResult)));
        assert!(!eligible_for_casc(&report(FailureKind::ProcessFailure)));
    }

    #[tokio::test]
    async fn overall_cancellation_wins_when_the_local_deadline_is_also_ready() {
        let cancellation = CancellationToken::new();
        cancellation.cancel();
        let mut task = tokio::spawn(pending::<()>());

        let event = select_single_event(
            &mut task,
            &cancellation,
            Some(LocalDeadline::start(Duration::ZERO)),
        )
        .await;
        assert!(matches!(event, SingleEvent::OverallCancelled));
        task.abort();
        assert!(task.await.unwrap_err().is_cancelled());
    }

    #[test]
    fn required_publication_remains_primary_only_after_both_workers_fail() {
        let publication = FailureReport::artifact(
            FailureKind::PublicationFailure,
            FailureScope::LaneLocal,
            "required proof publication failed",
        );
        let ordinary = FailureReport::vampire_worker_failure(
            FailureOrigin::VampireFiniteModelBuilding,
            "ordinary FMB failure",
            Vec::new(),
        );
        let combined = combined_failure(Some(publication), Some(ordinary))
            .expect("two failures produce one report");
        assert_eq!(combined.origin(), FailureOrigin::ArtifactSettlement);
        assert_eq!(combined.kind(), FailureKind::PublicationFailure);
        assert!(combined.detail().unwrap().contains("peer worker"));
    }
}
