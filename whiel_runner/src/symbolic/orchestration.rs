//! Fixed two-lane Symbolic-Houdini orchestration.
//!
//! This module owns only run construction, lane arbitration, the authoritative
//! overall deadline, and final cleanup.  INV and CEX algorithms remain in
//! their lane modules; solver-process admission remains in `runtime`.

use std::collections::HashSet;
use std::path::PathBuf;
use std::time::Duration;

use tokio::task::{JoinError, JoinHandle};

use crate::artifact::{
    ArtifactRef, ArtifactStore, ArtifactStoreConfig, Retention, new_artifact_store,
};
use crate::encoding::{
    EncodingError, EncodingWorkerPoolConfig, REFERENCE_PROPOSAL_VERSION, SolverEncodingContext,
    new_solver_encoding_context,
};
use crate::failure::{FailureKind, FailureOrigin, FailureReport, FailureScope};
use crate::houdini::{
    CertificationRuntime, CertifiedInvalidity, CertifiedValidity, VerificationParameters,
};
use crate::runtime::{CancellationToken, SolverAdmission, create_symbolic_solver_admissions};
use crate::task::{SynthesisTask, TaskSchemaKind};
use crate::telemetry::{
    ReferenceFeatureSetTelemetry, RunConfigurationTelemetry, TelemetryHandle, TelemetryLevel,
};
use crate::vampire::{
    PROOF_CASC_ALLOCATION_FORMULA, PROOF_CASC_ALLOCATION_ROUNDING, PROOF_CASC_PROFILE_ID,
    PROOF_CASC_SHARE_SCALE, VampireWorkerCommand,
};

use super::{
    CertifiedSynthesisResult, SymbolicCexRuntime, SymbolicCexState, SymbolicHoudiniPolicy,
    SymbolicInvRuntime, SymbolicInvState, SymbolicLaneOutcome, WLimitGrowth, WProofReceiver,
    WProofSender, create_w_proof_channel, new_symbolic_cex_state, new_symbolic_inv_state,
    run_cex_lane, run_inv_lane,
};

// ------------------------------------------------------------
// Entry Configuration And Results
// ------------------------------------------------------------

/// Resolve the shared verification policy for Symbolic-Houdini.
///
/// Symbolic enumeration proposes broad waves, so its INV lane deliberately
/// skips bulk initialization and maintenance checks.  Keeping this rewrite at
/// the entry boundary makes persisted configuration, telemetry, and execution
/// agree on the effective limits.
pub(crate) fn normalize_symbolic_verification(
    verification: VerificationParameters,
) -> VerificationParameters {
    let first_tier = Duration::from_secs(1);
    let verification = verification
        .with_bulk_init_limit(Duration::ZERO)
        .with_bulk_maint_limit(Duration::ZERO);
    if verification.search_limit() <= first_tier {
        return verification;
    }
    verification
        .with_init_first_attempt_limits(vec![first_tier])
        .expect("one positive tier below the search limit is valid")
}

/// Process configuration needed by the synchronous Symbolic-Houdini entry.
///
/// Both lanes receive the same logical configuration.  The entry scopes the
/// certification work and solution directories per lane so concurrent bridge
/// calls cannot contend for one exclusive output lease.
#[derive(Clone, Debug)]
pub struct SymbolicHoudiniRuntime {
    artifact_root: PathBuf,
    encoding_workers: EncodingWorkerPoolConfig,
    vampire: VampireWorkerCommand,
    certification: CertificationRuntime,
    telemetry: TelemetryHandle,
    artifact_allowance_bytes: Option<u64>,
    artifact_file_allowance: Option<u64>,
}

impl SymbolicHoudiniRuntime {
    pub fn new(
        artifact_root: impl Into<PathBuf>,
        encoding_workers: EncodingWorkerPoolConfig,
        vampire: VampireWorkerCommand,
        certification: CertificationRuntime,
    ) -> Self {
        Self {
            artifact_root: artifact_root.into(),
            encoding_workers,
            vampire,
            certification,
            telemetry: TelemetryHandle::disabled(),
            artifact_allowance_bytes: None,
            artifact_file_allowance: None,
        }
    }

    /// Cap the artifact bytes this run may publish.
    ///
    /// The effective ceiling is `min(allowance, free space)` measured at the
    /// artifact root when the run starts, so a generous allowance can never
    /// commit the run to more space than the volume actually has.
    pub fn with_artifact_allowance(mut self, bytes: Option<u64>) -> Self {
        self.artifact_allowance_bytes = bytes;
        self
    }

    /// Cap the number of artifact payload files this run may create.
    ///
    /// Bytes cannot stand in for this: file count is what overwhelms
    /// per-file bookkeeping such as a cloud-sync engine's record queue.
    pub fn with_artifact_file_allowance(mut self, files: Option<u64>) -> Self {
        self.artifact_file_allowance = files;
        self
    }

    /// Attach observational telemetry to both lanes before either starts.
    pub fn with_telemetry(mut self, telemetry: TelemetryHandle) -> Self {
        self.telemetry = telemetry;
        self
    }
}

/// Terminal output of one complete synthesis run.
///
/// Certificate values are the existing wrappers used by the Phase 3
/// certification bridge.  Lane orchestration does not reshape certificates.
#[derive(Clone, Debug)]
pub enum SynthesisResult {
    Valid(CertifiedValidity),
    Invalid(CertifiedInvalidity),
    Failure(FailureReport),
}

impl From<CertifiedSynthesisResult> for SynthesisResult {
    fn from(certified: CertifiedSynthesisResult) -> Self {
        match certified {
            CertifiedSynthesisResult::Valid(certificate) => Self::Valid(certificate),
            CertifiedSynthesisResult::Invalid(certificate) => Self::Invalid(certificate),
        }
    }
}

// ------------------------------------------------------------
// Partitioned Run State
// ------------------------------------------------------------

#[derive(Debug)]
pub struct SymbolicHoudiniState {
    artifacts: ArtifactStore,
    overall_limit: Duration,
    encoding_context: SolverEncodingContext,
    solver_cleanup_authority: SolverAdmission,
    inv: SymbolicInvState,
    cex: SymbolicCexState,
    w_proof_sender: WProofSender,
    w_proof_receiver: WProofReceiver,
}

impl SymbolicHoudiniState {
    pub fn overall_limit(&self) -> Duration {
        self.overall_limit
    }

    pub fn overall_timeout_report(&self) -> FailureReport {
        FailureReport::overall_timeout(self.overall_limit)
    }
}

/// Construct one task-scoped state with shared artifact, encoding, admission,
/// and W-publication authority.
#[allow(clippy::too_many_arguments)]
pub async fn new_symbolic_houdini_state(
    task: &SynthesisTask,
    artifacts: &ArtifactStore,
    overall_limit: Duration,
    verification: VerificationParameters,
    policy: SymbolicHoudiniPolicy,
    log_maintenance_history: bool,
    fail_on_history_log_error: bool,
    encoding_workers: EncodingWorkerPoolConfig,
) -> Result<SymbolicHoudiniState, FailureReport> {
    let verification = normalize_symbolic_verification(verification);
    let fail_on_history_log_error = log_maintenance_history && fail_on_history_log_error;
    let (inv_admission, cex_admission) =
        create_symbolic_solver_admissions(verification.resources()).map_err(|error| {
            run_control_failure(format!("invalid symbolic resource policy: {error}"))
        })?;
    let encoding_context = new_solver_encoding_context(task, artifacts, encoding_workers)?;
    let solver_cleanup_authority = inv_admission.clone();
    let (w_proof_sender, w_proof_receiver) =
        create_w_proof_channel(task.identity(), artifacts.backend_id());

    let inv = match new_symbolic_inv_state(
        task,
        encoding_context.clone(),
        artifacts,
        verification.clone(),
        inv_admission,
        log_maintenance_history,
        fail_on_history_log_error,
    ) {
        Ok(inv) => inv,
        Err(report) => {
            return Err(cleanup_failed_construction(&encoding_context, report).await);
        }
    };
    let cex = match new_symbolic_cex_state(
        task,
        encoding_context.clone(),
        artifacts,
        verification,
        cex_admission,
        policy,
    ) {
        Ok(cex) => cex,
        Err(report) => {
            drop(inv);
            return Err(cleanup_failed_construction(&encoding_context, report).await);
        }
    };

    Ok(SymbolicHoudiniState {
        artifacts: artifacts.clone(),
        overall_limit,
        encoding_context,
        solver_cleanup_authority,
        inv,
        cex,
        w_proof_sender,
        w_proof_receiver,
    })
}

async fn cleanup_failed_construction(
    encoding_context: &SolverEncodingContext,
    original: FailureReport,
) -> FailureReport {
    match encoding_context.shutdown().await {
        Ok(()) => original,
        Err(error) => encoding_cleanup_failure(error),
    }
}

// ------------------------------------------------------------
// Fixed Two-Lane Race
// ------------------------------------------------------------

/// Start INV and CEX before awaiting either, arbitrate under the authoritative
/// overall deadline, then stop all context-owned work before return.
pub async fn race_symbolic_lanes(
    task: &SynthesisTask,
    state: SymbolicHoudiniState,
    inv_runtime: SymbolicInvRuntime,
    cex_runtime: SymbolicCexRuntime,
) -> SynthesisResult {
    // Establish the authoritative deadline before cloning or spawning lane
    // work.  Cleanup may extend beyond this instant, but search may not.
    let deadline = tokio::time::Instant::now() + state.overall_limit;
    let telemetry = state.inv.telemetry_handle();
    let SymbolicHoudiniState {
        artifacts,
        overall_limit,
        encoding_context,
        solver_cleanup_authority,
        inv,
        cex,
        w_proof_sender,
        w_proof_receiver,
    } = state;
    let cancellation = CancellationToken::new();
    let lane_race_span = telemetry.span("symbolic.lane_race");

    let inv_task_source = task.clone();
    let inv_cancellation = cancellation.clone();
    let inv_task = tokio::spawn(async move {
        run_inv_lane(
            &inv_task_source,
            inv,
            w_proof_receiver,
            inv_runtime,
            &inv_cancellation,
        )
        .await
    });

    let cex_task_source = task.clone();
    let cex_cancellation = cancellation.clone();
    let cex_task = tokio::spawn(async move {
        run_cex_lane(
            &cex_task_source,
            cex,
            w_proof_sender,
            &cex_runtime,
            &cex_cancellation,
        )
        .await
    });

    let mut tasks = LaneTasks::new(inv_task, cex_task);
    let selected =
        match arbitrate_lane_tasks_with_deadline(&mut tasks, &cancellation, deadline).await {
            DeadlineArbitration::Completed(result) => result
                .map_terminal(SynthesisResult::from)
                .into_synthesis_result(),
            DeadlineArbitration::TimedOut => {
                SynthesisResult::Failure(FailureReport::overall_timeout(overall_limit))
            }
            DeadlineArbitration::Interrupted(signal) => {
                SynthesisResult::Failure(FailureReport::interrupted(signal))
            }
        };
    drop(lane_race_span);

    // A dropped async solver supervisor can leave its `spawn_blocking`
    // worker cleaning up. The retained admission authority observes the
    // worker-owned lease and joins that cleanup before this async boundary
    // returns or artifacts can settle.
    solver_cleanup_authority.wait_for_solver_idle().await;

    // `SolverEncodingContext` retains every context-owned worker and CPU job.
    // Shutdown is deliberately outside the deadline branch so timeout cannot
    // detach cleanup work.  The root ArtifactStore stays live through it.
    let cleanup_span = telemetry.span("symbolic.encoding_cleanup");
    let cleanup = encoding_context.shutdown().await;
    drop(encoding_context);
    drop(cleanup_span);

    // A lane panic can drop a certification or publication future after its
    // blocking worker starts. The scoped store observes those retained work
    // registrations without acquiring the owner's settlement authority.
    artifacts.wait_for_background_work().await;
    drop(artifacts);
    match cleanup {
        Ok(()) => selected,
        Err(error) => SynthesisResult::Failure(encoding_cleanup_failure(error)),
    }
}

// ------------------------------------------------------------
// Synchronous Entry
// ------------------------------------------------------------

/// Run Symbolic-Houdini from a synchronous caller such as the Phase 4D CLI.
#[allow(clippy::too_many_arguments)]
pub fn symbolic_houdini(
    task: &SynthesisTask,
    overall_limit: Duration,
    verification: VerificationParameters,
    policy: SymbolicHoudiniPolicy,
    log_maintenance_history: bool,
    fail_on_history_log_error: bool,
    runtime: SymbolicHoudiniRuntime,
) -> SynthesisResult {
    if task.schema_kind() != TaskSchemaKind::LegacyProgram {
        return SynthesisResult::Failure(run_control_failure(
            "Symbolic-Houdini accepts only legacy-program tasks",
        ));
    }
    let verification = normalize_symbolic_verification(verification);
    if tokio::runtime::Handle::try_current().is_ok() {
        return SynthesisResult::Failure(run_control_failure(
            "the synchronous Symbolic-Houdini entry cannot run inside an async runtime",
        ));
    }
    let tokio_runtime = match tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
    {
        Ok(runtime) => runtime,
        Err(error) => {
            return SynthesisResult::Failure(run_control_failure(format!(
                "failed to create the Symbolic-Houdini async runtime: {error}"
            )));
        }
    };
    tokio_runtime.block_on(symbolic_houdini_async(
        task,
        overall_limit,
        verification,
        policy,
        log_maintenance_history,
        fail_on_history_log_error,
        runtime,
    ))
}

#[allow(clippy::too_many_arguments)]
/// Return the free bytes on the volume holding `path`, if it can be read.
fn available_bytes(path: &std::path::Path) -> Option<u64> {
    use std::ffi::CString;
    use std::os::unix::ffi::OsStrExt;
    let raw = CString::new(path.as_os_str().as_bytes()).ok()?;
    let mut stat: libc::statvfs = unsafe { std::mem::zeroed() };
    if unsafe { libc::statvfs(raw.as_ptr(), &mut stat) } != 0 {
        return None;
    }
    (stat.f_bavail as u64).checked_mul(stat.f_frsize as u64)
}

/// Clamp a requested allowance to the space the volume actually has.
///
/// Without an allowance the run stays unbounded, preserving historical
/// behavior; with one, the run can never be promised more than free space.
fn effective_artifact_budget(root: &std::path::Path, allowance: Option<u64>) -> Option<u64> {
    let allowance = allowance?;
    Some(match available_bytes(root) {
        Some(free) => allowance.min(free),
        None => allowance,
    })
}

async fn symbolic_houdini_async(
    task: &SynthesisTask,
    overall_limit: Duration,
    verification: VerificationParameters,
    policy: SymbolicHoudiniPolicy,
    log_maintenance_history: bool,
    fail_on_history_log_error: bool,
    runtime: SymbolicHoudiniRuntime,
) -> SynthesisResult {
    let SymbolicHoudiniRuntime {
        artifact_root,
        encoding_workers,
        vampire,
        certification,
        telemetry,
        artifact_allowance_bytes,
        artifact_file_allowance,
    } = runtime;
    let _entry_span = telemetry.span("symbolic.entry");
    let fail_on_history_log_error = log_maintenance_history && fail_on_history_log_error;
    let resources = verification.resources();
    let w_search = policy.w_search();
    let proof_casc_policy = vampire.proof_casc_policy();
    let proposal_realization = encoding_workers.proposal_realization;
    telemetry.record_run_configuration(RunConfigurationTelemetry {
        task_canonical_id: task.identity().canonical_id().to_string(),
        overall_limit_nanoseconds: duration_nanoseconds(overall_limit),
        search_limit_nanoseconds: duration_nanoseconds(verification.search_limit()),
        proof_casc_profile_id: PROOF_CASC_PROFILE_ID.to_string(),
        proof_casc_initial_share_millionths: proof_casc_policy.initial_share().millionths(),
        proof_casc_retry_added_share_millionths: proof_casc_policy.retry_added_share().millionths(),
        proof_casc_share_scale: PROOF_CASC_SHARE_SCALE,
        proof_casc_allocation_formula: PROOF_CASC_ALLOCATION_FORMULA.to_string(),
        proof_casc_allocation_rounding: PROOF_CASC_ALLOCATION_ROUNDING.to_string(),
        maintenance_retry_increment_nanoseconds: verification
            .maintenance_retry_increments()
            .iter()
            .copied()
            .map(duration_nanoseconds)
            .collect(),
        bulk_init_limit_nanoseconds: duration_nanoseconds(verification.bulk_init_limit()),
        bulk_maint_limit_nanoseconds: duration_nanoseconds(verification.bulk_maint_limit()),
        init_first_attempt_limit_nanoseconds: verification
            .init_first_attempt_limits()
            .iter()
            .copied()
            .map(duration_nanoseconds)
            .collect(),
        init_attempt_limit_nanoseconds: verification
            .init_attempt_limits()
            .into_iter()
            .map(duration_nanoseconds)
            .collect(),
        search_term_limit_nanoseconds: duration_nanoseconds(verification.search_term_limit()),
        search_term_retry_increment_nanoseconds: verification
            .search_term_retry_increments()
            .iter()
            .copied()
            .map(duration_nanoseconds)
            .collect(),
        final_certification_limit_nanoseconds: verification
            .final_certification_limit()
            .map(duration_nanoseconds),
        max_vampire_processes: usize_telemetry(resources.max_vampire_processes()),
        cex_reserved_vampire_processes: usize_telemetry(resources.cex_reserved_vampire_processes()),
        max_inv_vampire_processes: usize_telemetry(resources.max_inv_vampire_processes()),
        max_cpu_workers: usize_telemetry(resources.max_cpu_workers()),
        encoding_worker_count: usize_telemetry(encoding_workers.workers),
        admit_higher_w_layers: policy.admit_higher_w_layers(),
        w_fresh_batch_size: usize_telemetry(w_search.fresh_batch_size()),
        w_retry_batch_size: usize_telemetry(w_search.retry_batch_size()),
        w_initial_limit_nanoseconds: duration_nanoseconds(w_search.initial_limit()),
        w_limit_growth: w_limit_growth_name(w_search.limit_growth()),
        log_maintenance_history,
        fail_on_history_log_error,
        proposal_realization_id: proposal_realization.realization_id().to_string(),
        proposal_realization_version: proposal_realization.realization_version(),
        reference_schedule_id: format!(
            "lean-reference-v{REFERENCE_PROPOSAL_VERSION}-all-enabled-diagonal"
        ),
        reference_features: ReferenceFeatureSetTelemetry::all_enabled(),
    });
    let artifact_budget = effective_artifact_budget(&artifact_root, artifact_allowance_bytes);
    let artifact_config = ArtifactStoreConfig::new(artifact_root)
        .maintenance_history(log_maintenance_history, fail_on_history_log_error)
        .payload_budget(artifact_budget)
        .payload_file_budget(artifact_file_allowance)
        .retention(if telemetry.level() == TelemetryLevel::Detailed {
            Retention::All
        } else {
            Retention::CertificateOnly
        });
    let (artifact_owner, artifacts) = match new_artifact_store(task, artifact_config) {
        Ok(backend) => backend,
        Err(report) => return SynthesisResult::Failure(report),
    };
    let state_construction_span = telemetry.span("symbolic.state_construction");
    let state = new_symbolic_houdini_state(
        task,
        &artifacts,
        overall_limit,
        verification,
        policy,
        log_maintenance_history,
        fail_on_history_log_error,
        encoding_workers,
    )
    .await;
    drop(state_construction_span);
    let run = match state {
        Ok(mut state) => {
            state.inv.attach_telemetry(telemetry.clone());
            state.cex.attach_telemetry(telemetry.clone());
            let vampire = vampire.with_telemetry(telemetry.clone());
            let inv_certification = certification.for_symbolic_inv_lane();
            let cex_certification = certification.for_symbolic_cex_lane();
            let inv_runtime = SymbolicInvRuntime::new(vampire.clone(), inv_certification);
            let cex_runtime = SymbolicCexRuntime::new(vampire, cex_certification);
            race_symbolic_lanes(task, state, inv_runtime, cex_runtime).await
        }
        Err(report) => SynthesisResult::Failure(report),
    };

    drop(artifacts);
    let artifact_settlement_span = telemetry.span("symbolic.artifact_settlement");
    let settlement = artifact_owner.settle_retaining(&terminal_artifact_references(&run));
    drop(artifact_settlement_span);
    match settlement {
        Ok(()) => run,
        Err(report) => SynthesisResult::Failure(report),
    }
}

/// The artifact references a terminal result carries into settlement.
///
/// Under certificate-only retention these are the payloads settlement
/// keeps; everything else the run produced is provenance for detailed
/// diagnostics and does not survive a non-detailed run.
fn terminal_artifact_references(result: &SynthesisResult) -> Vec<ArtifactRef> {
    match result {
        SynthesisResult::Valid(valid) => vec![valid.certificate, valid.record],
        SynthesisResult::Invalid(invalid) => {
            vec![invalid.certificate, invalid.witness, invalid.record]
        }
        SynthesisResult::Failure(report) => report.artifact_references().to_vec(),
    }
}

fn duration_nanoseconds(duration: Duration) -> u64 {
    duration.as_nanos().min(u128::from(u64::MAX)) as u64
}

fn usize_telemetry(value: usize) -> u64 {
    u64::try_from(value).unwrap_or(u64::MAX)
}

fn w_limit_growth_name(growth: WLimitGrowth) -> String {
    match growth {
        WLimitGrowth::Linear(increment) => {
            format!("linear:{}ns", duration_nanoseconds(increment))
        }
        WLimitGrowth::Geometric(factor) => format!("geometric:{factor}"),
    }
}

// ------------------------------------------------------------
// Runtime-Native Arbitration Kernel
// ------------------------------------------------------------

#[derive(Clone, Debug)]
enum RankedLaneOutcome<T> {
    Terminal(T),
    Inconclusive(FailureReport),
    RunFatal(FailureReport),
    Cancelled,
}

impl From<SymbolicLaneOutcome> for RankedLaneOutcome<CertifiedSynthesisResult> {
    fn from(outcome: SymbolicLaneOutcome) -> Self {
        match outcome {
            SymbolicLaneOutcome::Terminal(result) => Self::Terminal(result),
            SymbolicLaneOutcome::Inconclusive(report) => Self::Inconclusive(report),
            SymbolicLaneOutcome::RunFatal(report) => Self::RunFatal(report),
            SymbolicLaneOutcome::Cancelled => Self::Cancelled,
        }
    }
}

enum ArbitrationResult<T> {
    Terminal(T),
    Failure(FailureReport),
}

enum DeadlineArbitration<T> {
    Completed(ArbitrationResult<T>),
    TimedOut,
    Interrupted(i32),
}

impl<T> ArbitrationResult<T> {
    fn map_terminal<U>(self, map: impl FnOnce(T) -> U) -> ArbitrationResult<U> {
        match self {
            Self::Terminal(result) => ArbitrationResult::Terminal(map(result)),
            Self::Failure(report) => ArbitrationResult::Failure(report),
        }
    }
}

impl ArbitrationResult<SynthesisResult> {
    fn into_synthesis_result(self) -> SynthesisResult {
        match self {
            Self::Terminal(result) => result,
            Self::Failure(report) => SynthesisResult::Failure(report),
        }
    }
}

struct LaneTasks<T> {
    inv: Option<JoinHandle<T>>,
    cex: Option<JoinHandle<T>>,
}

#[derive(Clone, Copy)]
enum Lane {
    Inv,
    Cex,
}

impl<T: Send + 'static> LaneTasks<T> {
    fn new(inv: JoinHandle<T>, cex: JoinHandle<T>) -> Self {
        Self {
            inv: Some(inv),
            cex: Some(cex),
        }
    }

    fn peer_is_finished(&self, selected: Lane) -> bool {
        match selected {
            Lane::Inv => self.cex.as_ref().is_some_and(JoinHandle::is_finished),
            Lane::Cex => self.inv.as_ref().is_some_and(JoinHandle::is_finished),
        }
    }

    async fn await_first(&mut self) -> (Lane, Result<T, JoinError>) {
        let inv = self.inv.as_mut().expect("INV task remains live");
        let cex = self.cex.as_mut().expect("CEX task remains live");
        tokio::select! {
            biased;
            outcome = inv => {
                self.inv.take();
                (Lane::Inv, outcome)
            }
            outcome = cex => {
                self.cex.take();
                (Lane::Cex, outcome)
            }
        }
    }

    async fn await_peer(&mut self, selected: Lane) -> Result<T, JoinError> {
        match selected {
            Lane::Inv => self.cex.take().expect("CEX peer remains live").await,
            Lane::Cex => self.inv.take().expect("INV peer remains live").await,
        }
    }

    async fn join_cleanup(&mut self) {
        if let Some(inv) = self.inv.take() {
            let _ = inv.await;
        }
        if let Some(cex) = self.cex.take() {
            let _ = cex.await;
        }
    }
}

async fn arbitrate_lane_tasks<T>(
    tasks: &mut LaneTasks<T>,
    cancellation: &CancellationToken,
) -> ArbitrationResult<T::Terminal>
where
    T: LaneOutcomeValue,
{
    let (selected_lane, joined) = tasks.await_first().await;
    let first = normalize_join(selected_lane, joined);
    match first {
        RankedLaneOutcome::Terminal(result) => {
            cancellation.cancel();
            tasks.join_cleanup().await;
            ArbitrationResult::Terminal(result)
        }
        RankedLaneOutcome::RunFatal(report) => {
            if tasks.peer_is_finished(selected_lane) {
                let peer =
                    normalize_join(selected_lane.peer(), tasks.await_peer(selected_lane).await);
                if let RankedLaneOutcome::Terminal(result) = peer {
                    return ArbitrationResult::Terminal(result);
                }
            } else {
                cancellation.cancel();
                tasks.join_cleanup().await;
            }
            ArbitrationResult::Failure(report)
        }
        RankedLaneOutcome::Inconclusive(first_report) => {
            let peer = normalize_join(selected_lane.peer(), tasks.await_peer(selected_lane).await);
            match peer {
                RankedLaneOutcome::Terminal(result) => ArbitrationResult::Terminal(result),
                RankedLaneOutcome::RunFatal(report) => ArbitrationResult::Failure(report),
                RankedLaneOutcome::Inconclusive(second_report) => {
                    ArbitrationResult::Failure(combine_inconclusive(
                        selected_lane,
                        &first_report,
                        selected_lane.peer(),
                        &second_report,
                    ))
                }
                RankedLaneOutcome::Cancelled => ArbitrationResult::Failure(run_control_failure(
                    "symbolic lane stopped without supervisor cancellation",
                )),
            }
        }
        RankedLaneOutcome::Cancelled => {
            cancellation.cancel();
            tasks.join_cleanup().await;
            ArbitrationResult::Failure(run_control_failure(
                "symbolic lane stopped without supervisor cancellation",
            ))
        }
    }
}

/// Apply one authoritative deadline without dropping lane handles.  The
/// completion branch is biased only to make an exactly-ready deadline tie a
/// permitted `Completed` result; cleanup may still extend past the limit.
async fn arbitrate_lane_tasks_with_deadline<T>(
    tasks: &mut LaneTasks<T>,
    cancellation: &CancellationToken,
    deadline: tokio::time::Instant,
) -> DeadlineArbitration<T::Terminal>
where
    T: LaneOutcomeValue,
{
    let deadline = tokio::time::sleep_until(deadline);
    tokio::pin!(deadline);
    tokio::select! {
        biased;
        result = arbitrate_lane_tasks(tasks, cancellation) => {
            DeadlineArbitration::Completed(result)
        }
        _ = &mut deadline => {
            cancellation.cancel();
            tasks.join_cleanup().await;
            DeadlineArbitration::TimedOut
        }
        // An operator interrupt is an externally imposed earlier
        // deadline: cancel, join, and settle through the same path.
        signal = crate::runtime::interrupt::wait() => {
            cancellation.cancel();
            tasks.join_cleanup().await;
            DeadlineArbitration::Interrupted(signal)
        }
    }
}

trait LaneOutcomeValue: Send + 'static {
    type Terminal: Send + 'static;
    fn into_ranked(self) -> RankedLaneOutcome<Self::Terminal>;
}

impl LaneOutcomeValue for SymbolicLaneOutcome {
    type Terminal = CertifiedSynthesisResult;

    fn into_ranked(self) -> RankedLaneOutcome<<SymbolicLaneOutcome as LaneOutcomeValue>::Terminal> {
        self.into()
    }
}

fn normalize_join<T: LaneOutcomeValue>(
    lane: Lane,
    joined: Result<T, JoinError>,
) -> RankedLaneOutcome<T::Terminal> {
    match joined {
        Ok(outcome) => outcome.into_ranked(),
        Err(error) => RankedLaneOutcome::RunFatal(run_control_failure(format!(
            "{} lane task failed before returning an outcome: {error}",
            lane.name()
        ))),
    }
}

impl Lane {
    fn peer(self) -> Self {
        match self {
            Self::Inv => Self::Cex,
            Self::Cex => Self::Inv,
        }
    }

    fn name(self) -> &'static str {
        match self {
            Self::Inv => "INV",
            Self::Cex => "CEX",
        }
    }
}

// ------------------------------------------------------------
// Failure Projection
// ------------------------------------------------------------

fn run_control_failure(detail: impl Into<String>) -> FailureReport {
    FailureReport::try_new(
        FailureOrigin::RunControl,
        FailureKind::InfrastructureFailure,
        false,
        FailureScope::RunGlobal,
        Some(detail.into()),
        Vec::new(),
    )
    .expect("symbolic entry failures use an approved run-control pair")
}

const MAX_SYMBOLIC_LANE_DETAIL_BYTES: usize = 1536;

fn combine_inconclusive(
    first_lane: Lane,
    first: &FailureReport,
    second_lane: Lane,
    second: &FailureReport,
) -> FailureReport {
    let mut artifacts = first.artifact_references().to_vec();
    let mut seen = artifacts.iter().copied().collect::<HashSet<ArtifactRef>>();
    for artifact in second.artifact_references() {
        if seen.insert(*artifact) {
            artifacts.push(*artifact);
        }
    }
    FailureReport::try_new(
        FailureOrigin::SymbolicRace,
        FailureKind::ConcurrentWorkerFailures,
        false,
        FailureScope::LaneLocal,
        Some(format!(
            "INV/CEX inconclusive pair:\n{}\n{}",
            format_lane_failure(first_lane, first),
            format_lane_failure(second_lane, second),
        )),
        artifacts,
    )
    .expect("a symbolic inconclusive pair uses an approved failure pair")
}

fn format_lane_failure(lane: Lane, report: &FailureReport) -> String {
    format!(
        "{} lane: origin={:?} kind={:?} retryable={} scope={:?} detail={}",
        lane.name(),
        report.origin(),
        report.kind(),
        report.retryable(),
        report.scope(),
        bound_text(
            report.detail().unwrap_or("none"),
            MAX_SYMBOLIC_LANE_DETAIL_BYTES,
        ),
    )
}

fn bound_text(text: &str, maximum_bytes: usize) -> String {
    if text.len() <= maximum_bytes {
        return text.to_owned();
    }
    let mut boundary = maximum_bytes;
    while !text.is_char_boundary(boundary) {
        boundary -= 1;
    }
    let mut bounded = text[..boundary].to_owned();
    bounded.push('…');
    bounded
}

fn encoding_cleanup_failure(error: EncodingError) -> FailureReport {
    match error {
        EncodingError::Failure(report) => report,
        EncodingError::Cancelled => {
            run_control_failure("solver encoding-context shutdown was unexpectedly cancelled")
        }
    }
}

// ------------------------------------------------------------
// Focused Arbitration Tests
// ------------------------------------------------------------

#[cfg(test)]
mod tests {
    use std::sync::Arc;
    use std::sync::atomic::{AtomicBool, Ordering};

    use tokio::sync::oneshot;

    use super::*;

    #[test]
    fn symbolic_normalization_keeps_single_tier_at_small_search_limits() {
        let normalized = normalize_symbolic_verification(
            VerificationParameters::new(
                Duration::from_secs(1),
                crate::runtime::RuntimeResourcePolicy::default_symbolic(),
            )
            .unwrap(),
        );
        assert_eq!(
            normalized.init_attempt_limits(),
            vec![Duration::from_secs(1)]
        );
    }

    #[test]
    fn symbolic_verification_normalization_disables_bulk_and_tiers_init() {
        let search_limit = Duration::from_secs(7);
        let raw = VerificationParameters::new(
            search_limit,
            crate::runtime::RuntimeResourcePolicy::default_symbolic(),
        )
        .unwrap()
        .with_bulk_init_limit(Duration::from_secs(2))
        .with_bulk_maint_limit(Duration::from_secs(3));

        let normalized = normalize_symbolic_verification(raw.clone());

        assert_eq!(normalized.search_limit(), raw.search_limit());
        assert_eq!(
            normalized.maintenance_retry_increments(),
            raw.maintenance_retry_increments()
        );
        assert_eq!(normalized.bulk_init_limit(), Duration::ZERO);
        assert_eq!(normalized.bulk_maint_limit(), Duration::ZERO);
        assert_eq!(
            normalized.init_attempt_limits(),
            vec![Duration::from_secs(1), search_limit]
        );
        assert_eq!(normalized.search_term_limit(), raw.search_term_limit());
        assert_eq!(
            normalized.final_certification_limit(),
            raw.final_certification_limit()
        );
        assert_eq!(normalized.resources(), raw.resources());
    }

    #[derive(Debug)]
    enum TestLaneOutcome {
        Terminal(u8),
        Inconclusive(FailureReport),
        RunFatal(FailureReport),
        Cancelled,
    }

    impl LaneOutcomeValue for TestLaneOutcome {
        type Terminal = u8;

        fn into_ranked(self) -> RankedLaneOutcome<<TestLaneOutcome as LaneOutcomeValue>::Terminal> {
            match self {
                Self::Terminal(result) => RankedLaneOutcome::Terminal(result),
                Self::Inconclusive(report) => RankedLaneOutcome::Inconclusive(report),
                Self::RunFatal(report) => RankedLaneOutcome::RunFatal(report),
                Self::Cancelled => RankedLaneOutcome::Cancelled,
            }
        }
    }

    fn lane_local(detail: &str) -> FailureReport {
        lane_local_with_retry(detail, false)
    }

    fn lane_local_with_retry(detail: &str, retryable: bool) -> FailureReport {
        FailureReport::try_new(
            FailureOrigin::EncodingPreparation,
            FailureKind::InfrastructureFailure,
            retryable,
            FailureScope::LaneLocal,
            Some(detail.to_string()),
            Vec::new(),
        )
        .unwrap()
    }

    #[tokio::test]
    async fn simultaneous_terminal_dominates_run_fatal() {
        let inv = tokio::spawn(async { TestLaneOutcome::RunFatal(run_control_failure("fatal")) });
        let cex = tokio::spawn(async { TestLaneOutcome::Terminal(7) });
        while !inv.is_finished() || !cex.is_finished() {
            tokio::task::yield_now().await;
        }
        let cancellation = CancellationToken::new();
        let mut tasks = LaneTasks::new(inv, cex);
        assert!(matches!(
            arbitrate_lane_tasks(&mut tasks, &cancellation).await,
            ArbitrationResult::Terminal(7)
        ));
    }

    #[tokio::test]
    async fn inconclusive_does_not_cancel_a_later_terminal_peer() {
        let (release, wait) = oneshot::channel();
        let inv = tokio::spawn(async { TestLaneOutcome::Inconclusive(lane_local("inv")) });
        let cex = tokio::spawn(async move {
            wait.await.unwrap();
            TestLaneOutcome::Terminal(9)
        });
        let cancellation = CancellationToken::new();
        let observed = cancellation.clone();
        let mut tasks = LaneTasks::new(inv, cex);
        let arbitration = arbitrate_lane_tasks(&mut tasks, &cancellation);
        let release_peer = async move {
            tokio::task::yield_now().await;
            assert!(!observed.is_cancelled());
            release.send(()).unwrap();
        };
        let (result, ()) = tokio::join!(arbitration, release_peer);
        assert!(matches!(result, ArbitrationResult::Terminal(9)));
    }

    #[tokio::test]
    async fn terminal_cancels_and_joins_the_losing_lane() {
        let cancellation = CancellationToken::new();
        let peer_cancellation = cancellation.clone();
        let cleaned = Arc::new(AtomicBool::new(false));
        let peer_cleaned = Arc::clone(&cleaned);
        let inv = tokio::spawn(async { TestLaneOutcome::Terminal(3) });
        let cex = tokio::spawn(async move {
            peer_cancellation.cancelled().await;
            peer_cleaned.store(true, Ordering::Release);
            TestLaneOutcome::Cancelled
        });
        let mut tasks = LaneTasks::new(inv, cex);
        let result = arbitrate_lane_tasks(&mut tasks, &cancellation).await;
        assert!(matches!(result, ArbitrationResult::Terminal(3)));
        assert!(cleaned.load(Ordering::Acquire));
    }

    #[tokio::test]
    async fn lane_panic_is_run_fatal_and_peer_cleanup_is_joined() {
        let cancellation = CancellationToken::new();
        let peer_cancellation = cancellation.clone();
        let cleaned = Arc::new(AtomicBool::new(false));
        let peer_cleaned = Arc::clone(&cleaned);
        let inv = tokio::spawn(async move {
            panic!("lane panic fixture");
            #[allow(unreachable_code)]
            TestLaneOutcome::Terminal(0)
        });
        let cex = tokio::spawn(async move {
            peer_cancellation.cancelled().await;
            peer_cleaned.store(true, Ordering::Release);
            TestLaneOutcome::Cancelled
        });
        let mut tasks = LaneTasks::new(inv, cex);
        let result = arbitrate_lane_tasks(&mut tasks, &cancellation).await;
        let ArbitrationResult::Failure(report) = result else {
            panic!("lane panic must fail the run")
        };
        assert_eq!(report.origin(), FailureOrigin::RunControl);
        assert_eq!(report.kind(), FailureKind::InfrastructureFailure);
        assert_eq!(report.scope(), FailureScope::RunGlobal);
        assert!(cleaned.load(Ordering::Acquire));
    }

    #[tokio::test]
    async fn both_inconclusive_reasons_are_preserved() {
        let inv_detail = format!("INV_REASON:{}", "i".repeat(8_000));
        let cex_detail = format!("CEX_REASON:{}", "c".repeat(8_000));
        let inv = tokio::spawn(async move {
            TestLaneOutcome::Inconclusive(lane_local_with_retry(&inv_detail, true))
        });
        let cex = tokio::spawn(async move {
            TestLaneOutcome::Inconclusive(lane_local_with_retry(&cex_detail, false))
        });
        let cancellation = CancellationToken::new();
        let mut tasks = LaneTasks::new(inv, cex);
        let ArbitrationResult::Failure(report) =
            arbitrate_lane_tasks(&mut tasks, &cancellation).await
        else {
            panic!("two inconclusive lanes must fail without a logical claim")
        };
        let detail = report.detail().unwrap();
        assert!(detail.contains("INV lane:"));
        assert!(detail.contains("CEX lane:"));
        assert!(detail.contains("INV_REASON:"));
        assert!(detail.contains("CEX_REASON:"));
        assert!(detail.contains("retryable=true"));
        assert!(detail.contains("retryable=false"));
    }

    #[tokio::test]
    async fn cancelled_join_is_a_run_fatal_task_failure() {
        let inv = tokio::spawn(async {
            std::future::pending::<()>().await;
            TestLaneOutcome::Terminal(0)
        });
        inv.abort();
        let cancellation = CancellationToken::new();
        let peer_cancellation = cancellation.clone();
        let cex = tokio::spawn(async move {
            peer_cancellation.cancelled().await;
            TestLaneOutcome::Cancelled
        });
        let mut tasks = LaneTasks::new(inv, cex);
        let ArbitrationResult::Failure(report) =
            arbitrate_lane_tasks(&mut tasks, &cancellation).await
        else {
            panic!("a cancelled lane task must fail the run")
        };
        assert_eq!(report.scope(), FailureScope::RunGlobal);
    }

    #[tokio::test]
    async fn ready_terminal_wins_an_exact_deadline_tie() {
        let inv = tokio::spawn(async { TestLaneOutcome::Terminal(11) });
        let cex = tokio::spawn(async { TestLaneOutcome::Inconclusive(lane_local("cex")) });
        while !inv.is_finished() || !cex.is_finished() {
            tokio::task::yield_now().await;
        }
        let cancellation = CancellationToken::new();
        let mut tasks = LaneTasks::new(inv, cex);
        assert!(matches!(
            arbitrate_lane_tasks_with_deadline(
                &mut tasks,
                &cancellation,
                tokio::time::Instant::now(),
            )
            .await,
            DeadlineArbitration::Completed(ArbitrationResult::Terminal(11))
        ));
    }

    #[tokio::test]
    async fn deadline_cancels_and_joins_both_lanes() {
        let cancellation = CancellationToken::new();
        let inv_cancellation = cancellation.clone();
        let cex_cancellation = cancellation.clone();
        let inv_cleaned = Arc::new(AtomicBool::new(false));
        let cex_cleaned = Arc::new(AtomicBool::new(false));
        let inv_flag = Arc::clone(&inv_cleaned);
        let cex_flag = Arc::clone(&cex_cleaned);
        let inv = tokio::spawn(async move {
            inv_cancellation.cancelled().await;
            inv_flag.store(true, Ordering::Release);
            TestLaneOutcome::Cancelled
        });
        let cex = tokio::spawn(async move {
            cex_cancellation.cancelled().await;
            cex_flag.store(true, Ordering::Release);
            TestLaneOutcome::Cancelled
        });
        let mut tasks = LaneTasks::new(inv, cex);
        assert!(matches!(
            arbitrate_lane_tasks_with_deadline(
                &mut tasks,
                &cancellation,
                tokio::time::Instant::now(),
            )
            .await,
            DeadlineArbitration::TimedOut
        ));
        assert!(inv_cleaned.load(Ordering::Acquire));
        assert!(cex_cleaned.load(Ordering::Acquire));
    }
}
