//! Deterministic maintenance execution and state transitions.
//!
//! The sequential runner is intentionally retained as a small semantic
//! oracle. Phase 3D can compare a concurrent track implementation against
//! this code without sharing its orchestration.

use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use serde::Serialize;
use tokio::sync::watch;
use tokio::task::JoinSet;

use crate::artifact::ScopeTag;
use crate::encoding::EncodingError;
use crate::entailment::{
    CancelledEntailmentCheck, EntailmentCheckResult, EntailmentInvocationOutcome,
    assemble_entailment, check_entailment, check_entailment_attempt_detailed,
};
use crate::failure::{FailureKind, FailureOrigin, FailureReport, FailureScope};
use crate::runtime::{AdmissionError, CancellationToken, CpuJobError};
use crate::task::SynthesisTask;
use crate::telemetry::{TelemetryHandle, TelemetryLevel};
use crate::vampire::{FmbOptions, VampireMode, VampireSearchBudget, VampireWorkerCommand};

use super::bulk::{BulkMaintenanceOutcome, bulk_maint_check};
use super::catalog::{
    CandidateSnapshot, ClauseId, ClauseSet, MaintenanceResultClass, MaintenanceResultDisposition,
    MaintenanceResultUpdate, MaintenanceRetryDecision, MaintenanceSnapshotError,
};
use super::initialization::{HoudiniState, LastTermStatus};
use super::maintenance::{CoverageLookup, MaintenancePlan, maintenance_invariant};

// ------------------------------------------------------------
// Block Identity And Semantic Results
// ------------------------------------------------------------

#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct GenerationId(u64);

impl GenerationId {
    pub fn get(self) -> u64 {
        self.0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MaintenanceBlockOutcome {
    Stable,
    Refuted(ClauseId),
    TimedOut(ClauseId),
    RetryExhausted(ClauseId),
    Failed(ClauseId),
}

impl MaintenanceBlockOutcome {
    pub fn target(self) -> Option<ClauseId> {
        match self {
            Self::Stable => None,
            Self::Refuted(target)
            | Self::TimedOut(target)
            | Self::RetryExhausted(target)
            | Self::Failed(target) => Some(target),
        }
    }

    pub fn is_stable(self) -> bool {
        matches!(self, Self::Stable)
    }

    fn history_kind(self) -> &'static str {
        match self {
            Self::Stable => "stable",
            Self::Refuted(_) => "refuted",
            Self::TimedOut(_) => "timed_out",
            Self::RetryExhausted(_) => "retry_exhausted",
            Self::Failed(_) => "failed",
        }
    }
}

/// The immutable semantic result of one fully stopped maintenance block.
#[derive(Clone, Debug)]
pub struct MaintenanceBlockResult {
    catalog_identity: u64,
    plan: Arc<MaintenancePlan>,
    state_revision: Arc<()>,
    generation: GenerationId,
    entry_active: Arc<ClauseSet>,
    candidate: Arc<ClauseSet>,
    known_live: Arc<ClauseSet>,
    outcome: MaintenanceBlockOutcome,
}

impl MaintenanceBlockResult {
    #[allow(clippy::too_many_arguments)]
    fn new(
        catalog_identity: u64,
        plan: Arc<MaintenancePlan>,
        state_revision: Arc<()>,
        generation: GenerationId,
        entry_active: Arc<ClauseSet>,
        candidate: Arc<ClauseSet>,
        known_live: ClauseSet,
        outcome: MaintenanceBlockOutcome,
    ) -> Self {
        Self {
            catalog_identity,
            plan,
            state_revision,
            generation,
            entry_active,
            candidate,
            known_live: Arc::new(known_live),
            outcome,
        }
    }

    pub fn generation(&self) -> GenerationId {
        self.generation
    }

    pub fn entry_active(&self) -> &ClauseSet {
        &self.entry_active
    }

    pub fn candidate(&self) -> &ClauseSet {
        &self.candidate
    }

    pub fn known_live(&self) -> &ClauseSet {
        &self.known_live
    }

    pub fn outcome(&self) -> MaintenanceBlockOutcome {
        self.outcome
    }
}

/// Runtime control around a complete semantic maintenance result.
#[must_use]
#[derive(Clone, Debug)]
pub enum MaintenanceExecutionOutcome<T> {
    Complete(T),
    Cancelled,
    Failed(FailureReport),
}

/// Runtime control around one complete caller-neutral Houdini invocation.
#[must_use]
#[derive(Clone, Debug)]
pub enum HoudiniExecutionOutcome {
    Complete,
    Cancelled,
    Failed(FailureReport),
}

// ------------------------------------------------------------
// Sequential Block Oracle
// ------------------------------------------------------------

/// Run one frozen-Candidate maintenance block in prepared track order.
pub async fn run_maintenance_block_sequential(
    task: &SynthesisTask,
    state: &mut HoudiniState,
    command: VampireWorkerCommand,
    cancellation: &CancellationToken,
) -> MaintenanceExecutionOutcome<MaintenanceBlockResult> {
    run_maintenance_block_sequential_impl(task, state, &command, cancellation).await
}

async fn run_maintenance_block_sequential_impl(
    task: &SynthesisTask,
    state: &mut HoudiniState,
    command: &VampireWorkerCommand,
    cancellation: &CancellationToken,
) -> MaintenanceExecutionOutcome<MaintenanceBlockResult> {
    if let Some(report) = state.maintenance_failure.clone() {
        return MaintenanceExecutionOutcome::Failed(report);
    }
    if cancellation.is_cancelled() {
        return MaintenanceExecutionOutcome::Cancelled;
    }

    let plan = match validate_block_entry(task, state) {
        Ok(plan) => plan,
        Err(report) => return fail_execution(state, report),
    };
    let generation = match state.allocate_generation() {
        Ok(generation) => generation,
        Err(report) => return fail_execution(state, report),
    };

    // Keep the returned entry snapshot independent from mutable state. This
    // lets exclusion update the state Active set without an Arc COW clone.
    let entry_active = Arc::new(state.active.as_ref().clone());
    let candidate = Arc::new(union(state.core.as_ref(), entry_active.as_ref()));
    let candidate_snapshot = match state.candidate_snapshot.as_ref() {
        Some(snapshot) if snapshot.equals_set(candidate.as_ref()) => Arc::clone(snapshot),
        _ => {
            return fail_execution(
                state,
                maintenance_invariant("current Candidate snapshot does not match Core and Active"),
            );
        }
    };
    let guard = match state
        .catalog
        .encoding_context()
        .prepare_loop_guard_body(&state.admission, &state.artifacts, cancellation)
        .await
    {
        Ok(guard) => guard,
        Err(EncodingError::Cancelled) => {
            return MaintenanceExecutionOutcome::Cancelled;
        }
        Err(EncodingError::Failure(report)) => {
            return fail_execution(state, maintenance_context_failure(report));
        }
    };
    let bodies = match state.catalog.snapshot_maintenance_block_bodies(
        candidate.as_ref(),
        entry_active.as_ref(),
        guard,
        cancellation,
    ) {
        Ok(bodies) => bodies,
        Err(MaintenanceSnapshotError::Cancelled) => {
            return MaintenanceExecutionOutcome::Cancelled;
        }
        Err(MaintenanceSnapshotError::Failure(report)) => {
            return fail_execution(state, maintenance_context_failure(report));
        }
    };
    if cancellation.is_cancelled() {
        return MaintenanceExecutionOutcome::Cancelled;
    }

    let mut known_live = ClauseSet::with_capacity(entry_active.len());
    for (track_index, track) in plan.schedule().tracks().iter().enumerate() {
        let track_index = match u64::try_from(track_index) {
            Ok(index) => index,
            Err(_) => {
                return fail_execution(
                    state,
                    maintenance_invariant("maintenance track index exceeds UInt64 range"),
                );
            }
        };
        for target in track.targets().iter().copied() {
            // A plan owns the initial universe. Later blocks traverse only the
            // current Active subset left by completed exclusions.
            if !entry_active.contains(&target) {
                continue;
            }
            if cancellation.is_cancelled() {
                return MaintenanceExecutionOutcome::Cancelled;
            }

            let supported = state.has_present_support(target);
            let shortcut = if supported {
                Some(MaintenanceShortcut::Support)
            } else {
                match state.find_live_cover(&plan, &known_live, target) {
                    Ok(Some(_)) => Some(MaintenanceShortcut::Coverage),
                    Ok(None) => None,
                    Err(report) => return fail_execution(state, report),
                }
            };
            if let Some(shortcut) = shortcut {
                if let Err(report) = state.catalog.close_maintenance_retry(target) {
                    return fail_execution(state, maintenance_context_failure(report));
                }
                known_live.insert(target);
                record_maintenance_shortcut(
                    &state.telemetry,
                    generation,
                    target,
                    shortcut,
                    "before_query",
                );
                continue;
            }

            let permit = match state.catalog.select_maintenance_retry(
                target,
                Arc::clone(&candidate_snapshot),
                state.verification.search_limit(),
                state.verification.maintenance_retry_increments(),
            ) {
                Ok(MaintenanceRetryDecision::Ready(permit)) => permit,
                Ok(MaintenanceRetryDecision::Exhausted) => {
                    return complete_block(
                        state,
                        Arc::clone(&plan),
                        generation,
                        entry_active,
                        candidate,
                        known_live,
                        MaintenanceBlockOutcome::RetryExhausted(target),
                    );
                }
                Err(report) => {
                    return fail_execution(state, maintenance_context_failure(report));
                }
            };

            let Some(goal) = bodies.target(target).cloned() else {
                return fail_execution(
                    state,
                    maintenance_invariant(format!(
                        "maintenance block lacks the WP body for clause {}",
                        target.get()
                    )),
                );
            };
            let artifacts = state
                .artifacts
                .scoped(ScopeTag::Houdini)
                .scoped(ScopeTag::Generation(generation.get()))
                .scoped(ScopeTag::Track(track_index))
                .scoped(ScopeTag::Clause(target.get()))
                .scoped(ScopeTag::verification_stage("maintenance"));
            let entailment = match assemble_entailment(
                state.catalog.encoding_context(),
                &state.admission,
                &artifacts,
                bodies.antecedent_snapshot(),
                vec![goal],
                cancellation,
            )
            .await
            {
                Ok(entailment) => entailment,
                Err(EncodingError::Cancelled) => {
                    return MaintenanceExecutionOutcome::Cancelled;
                }
                Err(EncodingError::Failure(report)) => {
                    if is_fatal_target_failure(&report) {
                        return fail_execution(state, report);
                    }
                    if let Err(report) =
                        apply_late_shortcut(state, &plan, generation, &mut known_live, target)
                    {
                        return fail_execution(state, maintenance_context_failure(report));
                    }
                    if known_live.contains(&target) {
                        continue;
                    }
                    return complete_block(
                        state,
                        Arc::clone(&plan),
                        generation,
                        entry_active,
                        candidate,
                        known_live,
                        MaintenanceBlockOutcome::Failed(target),
                    );
                }
            };

            // Count one requested ProofAndFmb race. This is not a claim that
            // either child process passed admission or reached process spawn.
            state
                .telemetry
                .increment("houdini.maintenance.proof_and_fmb_requests", 1);
            state.telemetry.record_clause_solver_attempt(target.get());
            if state.telemetry.level() == TelemetryLevel::Detailed {
                state.telemetry.event(
                    "maintenance_query_started",
                    serde_json::json!({
                        "generation": generation.get(),
                        "track": track_index,
                        "target": target.get(),
                        "initial_allowance_nanoseconds": permit.initial_allowance().as_nanos().min(u128::from(u64::MAX)) as u64,
                        "allowance_nanoseconds": permit.allowance().as_nanos().min(u128::from(u64::MAX)) as u64,
                        "fmb_start_size": permit.fmb_start_size().get(),
                    }),
                );
            }
            let query_started = state.telemetry.is_enabled().then(Instant::now);
            let outcome = check_entailment(
                &entailment,
                &artifacts,
                VampireSearchBudget::cumulative(permit.initial_allowance(), permit.allowance()),
                VampireMode::ProofAndFmb(FmbOptions {
                    start_size: permit.fmb_start_size(),
                    ..FmbOptions::default()
                }),
                command.clone(),
                state.admission.clone(),
                cancellation.clone(),
            )
            .await;
            let query_duration = query_started.map_or(Duration::ZERO, |started| started.elapsed());
            if state.telemetry.is_enabled() {
                state
                    .telemetry
                    .add_duration("houdini.maintenance.query_inclusive", query_duration);
            }
            // The sequential oracle retains only semantic/retry behavior.
            // The production concurrent path also records hot provenance.
            match outcome {
                EntailmentInvocationOutcome::Result(EntailmentCheckResult::Proved { .. }) => {
                    if let Err(report) = state.catalog.close_maintenance_retry(target) {
                        return fail_execution(state, maintenance_context_failure(report));
                    }
                    known_live.insert(target);
                    record_maintenance_solver_result(
                        &state.telemetry,
                        generation,
                        track_index,
                        target,
                        "proved",
                        MaintenanceResultDisposition::Applied,
                        query_duration,
                    );
                }
                EntailmentInvocationOutcome::Result(EntailmentCheckResult::Refuted(_)) => {
                    if let Err(report) = state.catalog.close_maintenance_retry(target) {
                        return fail_execution(state, maintenance_context_failure(report));
                    }
                    if let Err(report) =
                        apply_late_shortcut(state, &plan, generation, &mut known_live, target)
                    {
                        return fail_execution(state, maintenance_context_failure(report));
                    }
                    if known_live.contains(&target) {
                        record_maintenance_solver_result(
                            &state.telemetry,
                            generation,
                            track_index,
                            target,
                            "refuted",
                            MaintenanceResultDisposition::Conflicting,
                            query_duration,
                        );
                        continue;
                    }
                    record_maintenance_solver_result(
                        &state.telemetry,
                        generation,
                        track_index,
                        target,
                        "refuted",
                        MaintenanceResultDisposition::Applied,
                        query_duration,
                    );
                    return complete_block(
                        state,
                        Arc::clone(&plan),
                        generation,
                        entry_active,
                        candidate,
                        known_live,
                        MaintenanceBlockOutcome::Refuted(target),
                    );
                }
                EntailmentInvocationOutcome::Result(EntailmentCheckResult::TimedOut {
                    next_fmb_start_size,
                    peer_failure,
                }) => {
                    if let Some(report) = peer_failure
                        && is_fatal_target_failure(&report)
                    {
                        record_maintenance_solver_result(
                            &state.telemetry,
                            generation,
                            track_index,
                            target,
                            "failure",
                            MaintenanceResultDisposition::CleanupOnly,
                            query_duration,
                        );
                        return fail_execution(state, maintenance_context_failure(report));
                    }
                    if let Err(report) =
                        apply_late_shortcut(state, &plan, generation, &mut known_live, target)
                    {
                        return fail_execution(state, maintenance_context_failure(report));
                    }
                    if known_live.contains(&target) {
                        record_maintenance_solver_result(
                            &state.telemetry,
                            generation,
                            track_index,
                            target,
                            "timed_out",
                            MaintenanceResultDisposition::Redundant,
                            query_duration,
                        );
                        continue;
                    }
                    if let Err(report) = state
                        .catalog
                        .record_maintenance_timeout(&permit, next_fmb_start_size)
                    {
                        return fail_execution(state, maintenance_context_failure(report));
                    }
                    record_maintenance_solver_result(
                        &state.telemetry,
                        generation,
                        track_index,
                        target,
                        "timed_out",
                        MaintenanceResultDisposition::Applied,
                        query_duration,
                    );
                    return complete_block(
                        state,
                        Arc::clone(&plan),
                        generation,
                        entry_active,
                        candidate,
                        known_live,
                        MaintenanceBlockOutcome::TimedOut(target),
                    );
                }
                EntailmentInvocationOutcome::Result(EntailmentCheckResult::Failure {
                    report,
                    next_fmb_start_size,
                }) => {
                    if is_fatal_target_failure(&report) {
                        record_maintenance_solver_result(
                            &state.telemetry,
                            generation,
                            track_index,
                            target,
                            "failure",
                            MaintenanceResultDisposition::CleanupOnly,
                            query_duration,
                        );
                        return fail_execution(state, report);
                    }
                    if let Err(report) =
                        apply_late_shortcut(state, &plan, generation, &mut known_live, target)
                    {
                        return fail_execution(state, maintenance_context_failure(report));
                    }
                    if known_live.contains(&target) {
                        record_maintenance_solver_result(
                            &state.telemetry,
                            generation,
                            track_index,
                            target,
                            "failure",
                            MaintenanceResultDisposition::Redundant,
                            query_duration,
                        );
                        continue;
                    }
                    if let Err(report) = state
                        .catalog
                        .record_maintenance_frontier(&permit, next_fmb_start_size)
                    {
                        return fail_execution(state, maintenance_context_failure(report));
                    }
                    record_maintenance_solver_result(
                        &state.telemetry,
                        generation,
                        track_index,
                        target,
                        "failure",
                        MaintenanceResultDisposition::Applied,
                        query_duration,
                    );
                    return complete_block(
                        state,
                        Arc::clone(&plan),
                        generation,
                        entry_active,
                        candidate,
                        known_live,
                        MaintenanceBlockOutcome::Failed(target),
                    );
                }
                EntailmentInvocationOutcome::Cancelled(cancelled) => {
                    record_maintenance_solver_result(
                        &state.telemetry,
                        generation,
                        track_index,
                        target,
                        "canceled",
                        MaintenanceResultDisposition::Canceled,
                        query_duration,
                    );
                    if let Some(report) = fatal_cancelled_peer(&cancelled) {
                        return fail_execution(state, report);
                    }
                    return MaintenanceExecutionOutcome::Cancelled;
                }
                EntailmentInvocationOutcome::RunFailure(report) => {
                    record_maintenance_solver_result(
                        &state.telemetry,
                        generation,
                        track_index,
                        target,
                        "failure",
                        MaintenanceResultDisposition::CleanupOnly,
                        query_duration,
                    );
                    return fail_execution(state, report);
                }
            }
        }
    }

    if known_live != *entry_active {
        return fail_execution(
            state,
            maintenance_invariant("maintenance schedule ended before exhausting current Active"),
        );
    }
    complete_block(
        state,
        Arc::clone(&plan),
        generation,
        entry_active,
        candidate,
        known_live,
        MaintenanceBlockOutcome::Stable,
    )
}

/// Restart fresh exact-Candidate blocks after each one-target exclusion.
pub async fn run_maintenance_blocks_sequential(
    task: &SynthesisTask,
    state: &mut HoudiniState,
    command: VampireWorkerCommand,
    cancellation: &CancellationToken,
) -> MaintenanceExecutionOutcome<Option<MaintenanceBlockResult>> {
    while !state.active.is_empty() {
        let result = match run_maintenance_block_sequential_impl(
            task,
            state,
            &command,
            cancellation,
        )
        .await
        {
            MaintenanceExecutionOutcome::Complete(result) => result,
            MaintenanceExecutionOutcome::Cancelled => {
                return MaintenanceExecutionOutcome::Cancelled;
            }
            MaintenanceExecutionOutcome::Failed(report) => {
                return MaintenanceExecutionOutcome::Failed(report);
            }
        };
        if result.outcome.is_stable() {
            return MaintenanceExecutionOutcome::Complete(Some(result));
        }
        if let Err(report) = apply_maintenance_exclusion(state, &result) {
            return MaintenanceExecutionOutcome::Failed(report);
        }
    }
    MaintenanceExecutionOutcome::Complete(None)
}

// ------------------------------------------------------------
// Concurrent Production Executor
// ------------------------------------------------------------

/// One immutable serial work list for a concurrently scheduled track.
#[derive(Debug)]
struct ConcurrentTrackWork {
    index: u64,
    targets: Arc<[ClauseId]>,
}

/// Materialized block inputs prepared outside async orchestration threads.
#[derive(Debug)]
struct ConcurrentBlockSetup {
    entry_active: Arc<ClauseSet>,
    candidate: Arc<ClauseSet>,
    candidate_snapshot: Arc<CandidateSnapshot>,
    bodies: Arc<super::catalog::MaintenanceBlockBodies>,
    supported_targets: Arc<HashSet<ClauseId>>,
    core_covered_targets: Arc<HashSet<ClauseId>>,
    live_slots: Arc<HashMap<ClauseId, usize>>,
    wait_ranks: Arc<HashMap<ClauseId, (usize, usize)>>,
    live_flags: Arc<[AtomicBool]>,
    nonproved_flags: Arc<[AtomicBool]>,
    known_live: ClauseSet,
    tracks: Vec<ConcurrentTrackWork>,
}

/// The one linearization boundary shared by all tracks in a block.
///
/// The mutex protects short set operations and short Catalog commits. Lazy
/// plan-bound coverage scans use an epoch-validated snapshot outside the
/// mutex. No guard is held across an await. In particular, the final shortcut
/// check and a competing exclusion decision share one linearization point.
#[derive(Debug)]
struct MaintenanceBlockArbiter {
    plan: Arc<MaintenancePlan>,
    generation: GenerationId,
    universe: Arc<ClauseSet>,
    supported_targets: Arc<HashSet<ClauseId>>,
    core_covered_targets: Arc<HashSet<ClauseId>>,
    live_slots: Arc<HashMap<ClauseId, usize>>,
    wait_ranks: Arc<HashMap<ClauseId, (usize, usize)>>,
    live_flags: Arc<[AtomicBool]>,
    nonproved_flags: Arc<[AtomicBool]>,
    encoding_context: crate::encoding::SolverEncodingContext,
    admission: crate::runtime::SolverAdmission,
    live_epoch: AtomicU64,
    resolution_version: watch::Sender<u64>,
    cancellation: CancellationToken,
    telemetry: TelemetryHandle,
    inner: Mutex<MaintenanceBlockArbiterState>,
}

#[derive(Debug)]
struct MaintenanceBlockArbiterState {
    known_live: ClauseSet,
    proof_supports: HashMap<ClauseId, ClauseSet>,
    outcome: Option<MaintenanceBlockOutcome>,
    failure: Option<FailureReport>,
    externally_cancelled: bool,
    closed: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TargetResolution {
    Continue,
    Cleanup,
    Stop,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TargetPreparation {
    Query,
    Skip,
    Stop,
}

#[derive(Debug)]
struct ShortcutObservation {
    epoch: u64,
    shortcut: Option<MaintenanceShortcut>,
    unresolved_source: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum MaintenanceShortcut {
    Support,
    Coverage,
}

impl MaintenanceShortcut {
    const fn name(self) -> &'static str {
        match self {
            Self::Support => "support",
            Self::Coverage => "coverage",
        }
    }

    const fn counter_key(self) -> &'static str {
        match self {
            Self::Support => "houdini.maintenance.shortcuts.support",
            Self::Coverage => "houdini.maintenance.shortcuts.coverage",
        }
    }

    const fn disposition_key(self) -> &'static str {
        match self {
            Self::Support => "maintenance_support_shortcut",
            Self::Coverage => "maintenance_coverage_shortcut",
        }
    }
}

fn record_maintenance_shortcut(
    telemetry: &TelemetryHandle,
    generation: GenerationId,
    target: ClauseId,
    shortcut: MaintenanceShortcut,
    boundary: &'static str,
) {
    if !telemetry.is_enabled() {
        return;
    }
    telemetry.increment(shortcut.counter_key(), 1);
    telemetry.record_disposition(shortcut.disposition_key(), 1);
    if telemetry.level() == TelemetryLevel::Detailed {
        telemetry.event(
            "maintenance_shortcut",
            serde_json::json!({
                "generation": generation.get(),
                "target": target.get(),
                "shortcut": shortcut.name(),
                "boundary": boundary,
            }),
        );
    }
}

#[derive(Debug)]
struct MaintenanceBlockArbiterSnapshot {
    known_live: ClauseSet,
    proof_supports: HashMap<ClauseId, ClauseSet>,
    outcome: Option<MaintenanceBlockOutcome>,
    failure: Option<FailureReport>,
    externally_cancelled: bool,
}

impl MaintenanceBlockArbiter {
    #[allow(clippy::too_many_arguments)]
    fn new(
        plan: Arc<MaintenancePlan>,
        generation: GenerationId,
        universe: Arc<ClauseSet>,
        supported_targets: Arc<HashSet<ClauseId>>,
        core_covered_targets: Arc<HashSet<ClauseId>>,
        live_slots: Arc<HashMap<ClauseId, usize>>,
        wait_ranks: Arc<HashMap<ClauseId, (usize, usize)>>,
        live_flags: Arc<[AtomicBool]>,
        nonproved_flags: Arc<[AtomicBool]>,
        encoding_context: crate::encoding::SolverEncodingContext,
        admission: crate::runtime::SolverAdmission,
        known_live: ClauseSet,
        cancellation: CancellationToken,
        telemetry: TelemetryHandle,
    ) -> Self {
        Self {
            plan,
            generation,
            universe,
            supported_targets,
            core_covered_targets,
            live_slots,
            wait_ranks,
            live_flags,
            nonproved_flags,
            encoding_context,
            admission,
            live_epoch: AtomicU64::new(0),
            resolution_version: watch::channel(0).0,
            cancellation,
            telemetry,
            inner: Mutex::new(MaintenanceBlockArbiterState {
                known_live,
                proof_supports: HashMap::new(),
                outcome: None,
                failure: None,
                externally_cancelled: false,
                closed: false,
            }),
        }
    }

    /// Resolve a target from already-visible support or coverage before a
    /// solver launch. The retry close and liveness publication share the
    /// arbiter's linearization point.
    async fn resolve_before_query(
        self: &Arc<Self>,
        catalog: &super::catalog::ClauseCatalog,
        target: ClauseId,
    ) -> Result<TargetPreparation, FailureReport> {
        loop {
            let Some(observation) = self.observe_shortcut(target).await? else {
                return Ok(TargetPreparation::Stop);
            };
            let mut state = self.lock();
            if state.closed {
                return Ok(TargetPreparation::Stop);
            }
            self.validate_target(target)?;
            if self.live_epoch.load(Ordering::Acquire) != observation.epoch {
                continue;
            }
            if let Some(shortcut) = observation.shortcut {
                catalog.close_maintenance_retry(target)?;
                if self.insert_known_live(&mut state, target)? {
                    self.record_shortcut(shortcut, target, "before_query");
                }
                return Ok(TargetPreparation::Skip);
            }
            return Ok(TargetPreparation::Query);
        }
    }

    fn publish_proved(
        &self,
        catalog: &super::catalog::ClauseCatalog,
        target: ClauseId,
        proof_support: Option<ClauseSet>,
    ) -> Result<TargetResolution, FailureReport> {
        let mut state = self.lock();
        if state.closed {
            if state.outcome.is_some() && state.failure.is_none() && !state.externally_cancelled {
                self.validate_target(target)?;
                catalog.close_maintenance_retry(target)?;
                self.insert_known_live(&mut state, target)?;
                if let Some(support) = proof_support {
                    state.proof_supports.insert(target, support);
                }
                return Ok(TargetResolution::Continue);
            }
            return Ok(TargetResolution::Cleanup);
        }
        self.validate_target(target)?;
        catalog.close_maintenance_retry(target)?;
        self.insert_known_live(&mut state, target)?;
        if let Some(support) = proof_support {
            self.telemetry
                .increment("houdini.maintenance.proof_support_recorded", 1);
            state.proof_supports.insert(target, support);
        }
        Ok(TargetResolution::Continue)
    }

    /// Recheck support and coverage at the same boundary which may select the
    /// block's sole nonstable result. A visible cover therefore always wins
    /// over a late Refuted, TimedOut, or Failed result.
    async fn publish_nonproved(
        self: &Arc<Self>,
        catalog: &super::catalog::ClauseCatalog,
        target: ClauseId,
        outcome: MaintenanceBlockOutcome,
        retry_update: RetryUpdate<'_>,
    ) -> Result<TargetResolution, FailureReport> {
        self.mark_nonproved(target)?;
        let mut retry_update = Some(retry_update);
        loop {
            let mut changed = self.resolution_version.subscribe();
            let Some(observation) = self.observe_shortcut(target).await? else {
                return Ok(TargetResolution::Cleanup);
            };
            if observation.shortcut.is_none() && observation.unresolved_source {
                tokio::select! {
                    _ = changed.changed() => continue,
                    _ = self.cancellation.cancelled() => {
                        return Ok(TargetResolution::Cleanup);
                    }
                }
            }
            let mut state = self.lock();
            if self.live_epoch.load(Ordering::Acquire) != observation.epoch {
                continue;
            }
            if state.closed {
                if state.outcome.is_some() && state.failure.is_none() && !state.externally_cancelled
                {
                    self.validate_target(target)?;
                    if let Some(shortcut) = observation.shortcut {
                        catalog.close_maintenance_retry(target)?;
                        if self.insert_known_live(&mut state, target)? {
                            self.record_shortcut(shortcut, target, "late_result");
                        }
                        return Ok(TargetResolution::Continue);
                    }
                    apply_retry_update(
                        catalog,
                        target,
                        retry_update.take().expect("retry update is applied once"),
                    )?;
                }
                return Ok(TargetResolution::Cleanup);
            }
            self.validate_target(target)?;
            if let Some(shortcut) = observation.shortcut {
                catalog.close_maintenance_retry(target)?;
                if self.insert_known_live(&mut state, target)? {
                    self.record_shortcut(shortcut, target, "late_result");
                }
                return Ok(TargetResolution::Continue);
            }

            apply_retry_update(
                catalog,
                target,
                retry_update.take().expect("retry update is applied once"),
            )?;
            state.outcome = Some(outcome);
            state.closed = true;
            drop(state);
            // Selecting the block's result stops its peers as ordinary
            // control flow. The run and its publication targets stay open, so
            // a peer which finishes inside this window is merely canceled.
            self.cancellation.cancel_cooperatively();
            return Ok(TargetResolution::Stop);
        }
    }

    /// Publish that this target completed without proof. Incoming coverage
    /// users may now decide whether another unresolved source can still make
    /// their own nonproof result redundant.
    fn mark_nonproved(&self, target: ClauseId) -> Result<(), FailureReport> {
        self.validate_target(target)?;
        let slot = self.live_slots.get(&target).copied().ok_or_else(|| {
            maintenance_invariant(format!(
                "maintenance target {} lacks a resolution slot",
                target.get()
            ))
        })?;
        self.nonproved_flags[slot].store(true, Ordering::Release);
        self.publish_resolution_change()?;
        Ok(())
    }

    fn publish_resolution_change(&self) -> Result<(), FailureReport> {
        self.resolution_version
            .send_modify(|version| *version = version.wrapping_add(1));
        Ok(())
    }

    /// A run-global report dominates every semantic result observed in the
    /// same joined block. Other fatal failures are retained unless a later
    /// run-global report supplies the stronger scope.
    fn publish_failure(&self, report: FailureReport) {
        let mut state = self.lock();
        retain_dominant_failure(&mut state.failure, report);
        state.closed = true;
        drop(state);
        self.cancellation.cancel();
    }

    /// Cancellation closes only an otherwise-open boundary. A semantic or
    /// fatal result which linearized first remains the block result.
    fn publish_external_cancellation(&self) {
        let mut state = self.lock();
        if !state.closed {
            state.externally_cancelled = true;
            state.closed = true;
        }
        drop(state);
        self.cancellation.cancel();
    }

    fn should_stop(&self) -> bool {
        self.lock().closed
    }

    fn into_snapshot(self) -> MaintenanceBlockArbiterSnapshot {
        let state = self
            .inner
            .into_inner()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        MaintenanceBlockArbiterSnapshot {
            known_live: state.known_live,
            proof_supports: state.proof_supports,
            outcome: state.outcome,
            failure: state.failure,
            externally_cancelled: state.externally_cancelled,
        }
    }

    async fn observe_shortcut(
        self: &Arc<Self>,
        target: ClauseId,
    ) -> Result<Option<ShortcutObservation>, FailureReport> {
        let epoch = {
            let state = self.lock();
            if state.closed {
                return Ok(None);
            }
            self.validate_target(target)?;
            self.live_epoch.load(Ordering::Acquire)
        };
        // Attribute one causal shortcut per skipped query. MaintSupport has
        // the same precedence as the original short-circuiting predicate.
        if self.supported_targets.contains(&target) {
            return Ok(Some(ShortcutObservation {
                epoch,
                shortcut: Some(MaintenanceShortcut::Support),
                unresolved_source: false,
            }));
        }
        if self.core_covered_targets.contains(&target) {
            return Ok(Some(ShortcutObservation {
                epoch,
                shortcut: Some(MaintenanceShortcut::Coverage),
                unresolved_source: false,
            }));
        }
        if self.plan.covered_by(target).is_empty()
            && self.plan.coverage_lookup() == CoverageLookup::IncomingEdges
        {
            return Ok(Some(ShortcutObservation {
                epoch,
                shortcut: None,
                unresolved_source: false,
            }));
        }
        let context = self.encoding_context.clone();
        let admission = self.admission.clone();
        let cancellation = self.cancellation.clone();
        let plan = Arc::clone(&self.plan);
        let live_slots = Arc::clone(&self.live_slots);
        let wait_ranks = Arc::clone(&self.wait_ranks);
        let live_flags = Arc::clone(&self.live_flags);
        let nonproved_flags = Arc::clone(&self.nonproved_flags);
        self.telemetry
            .increment("houdini.maintenance.lazy_coverage_lookup_requests", 1);
        let lookup_started = self.telemetry.is_enabled().then(Instant::now);
        let lookup = context
            .run_cpu_job(&admission, &cancellation, move |job_cancellation| {
                if job_cancellation.is_cancelled() {
                    return Err(CpuJobError::Cancelled);
                }
                let target_rank = wait_ranks.get(&target).copied().ok_or_else(|| {
                    CpuJobError::Failure(maintenance_invariant(format!(
                        "maintenance target {} lacks a wait rank",
                        target.get()
                    )))
                })?;
                let mut unresolved_source = false;
                let literal_cover = plan.find_literal_subset_cover_by(
                    target,
                    |source| {
                        if plan.core().contains(&source) {
                            return true;
                        }
                        let Some(slot) = live_slots.get(&source) else {
                            return false;
                        };
                        if live_flags[*slot].load(Ordering::Acquire) {
                            return true;
                        }
                        if !nonproved_flags[*slot].load(Ordering::Acquire)
                            && wait_ranks
                                .get(&source)
                                .is_some_and(|source_rank| *source_rank < target_rank)
                        {
                            unresolved_source = true;
                        }
                        false
                    },
                    &job_cancellation,
                )?;
                if literal_cover.is_some() {
                    return Ok((true, false));
                }
                for (position, source) in plan.covered_by(target).iter().enumerate() {
                    if position % 256 == 0 && job_cancellation.is_cancelled() {
                        return Err(CpuJobError::Cancelled);
                    }
                    if let Some(slot) = live_slots.get(source) {
                        let source_rank = wait_ranks.get(source).copied().ok_or_else(|| {
                            CpuJobError::Failure(maintenance_invariant(format!(
                                "maintenance source {} lacks a wait rank",
                                source.get()
                            )))
                        })?;
                        if live_flags[*slot].load(Ordering::Acquire) {
                            return Ok((true, false));
                        }
                        // Waiting only toward a strictly smaller immutable
                        // work rank makes the wait relation acyclic, including
                        // when closed coverage SCCs span serial tracks.
                        if !nonproved_flags[*slot].load(Ordering::Acquire)
                            && source_rank < target_rank
                        {
                            unresolved_source = true;
                        }
                    }
                }
                Ok((false, unresolved_source))
            })
            .await;
        let lookup_duration = lookup_started.map_or(Duration::ZERO, |started| started.elapsed());
        if self.telemetry.is_enabled() {
            self.telemetry.add_duration(
                "houdini.maintenance.lazy_coverage_lookup_inclusive",
                lookup_duration,
            );
        }
        let (justified, unresolved_source) = match lookup {
            Ok(observation) => observation,
            Err(CpuJobError::Cancelled)
            | Err(CpuJobError::Admission(AdmissionError::Cancelled)) => return Ok(None),
            Err(error) => {
                return Err(match error {
                    CpuJobError::Failure(report)
                    | CpuJobError::Admission(AdmissionError::Closed(report)) => report,
                    other => maintenance_global_failure(format!(
                        "maintenance coverage lookup worker failed: {other}"
                    )),
                });
            }
        };
        if self.telemetry.level() == TelemetryLevel::Detailed {
            self.telemetry.event(
                "maintenance_lazy_coverage_lookup",
                serde_json::json!({
                    "generation": self.generation.get(),
                    "target": target.get(),
                    "justified": justified,
                    "unresolved_source": unresolved_source,
                    "inclusive_nanoseconds": lookup_duration.as_nanos().min(u128::from(u64::MAX)) as u64,
                }),
            );
        }
        Ok(Some(ShortcutObservation {
            epoch,
            shortcut: justified.then_some(MaintenanceShortcut::Coverage),
            unresolved_source,
        }))
    }

    fn record_shortcut(
        &self,
        shortcut: MaintenanceShortcut,
        target: ClauseId,
        boundary: &'static str,
    ) {
        record_maintenance_shortcut(&self.telemetry, self.generation, target, shortcut, boundary);
    }

    fn insert_known_live(
        &self,
        state: &mut MaintenanceBlockArbiterState,
        target: ClauseId,
    ) -> Result<bool, FailureReport> {
        if state.known_live.insert(target) {
            let Some(slot) = self.live_slots.get(&target).copied() else {
                state.known_live.remove(&target);
                return Err(maintenance_invariant(format!(
                    "maintenance target {} lacks a known-live slot",
                    target.get()
                )));
            };
            let epoch = self.live_epoch.load(Ordering::Acquire);
            let Some(next_epoch) = epoch.checked_add(1) else {
                state.known_live.remove(&target);
                return Err(maintenance_global_failure(
                    "maintenance known-live epoch exhausted",
                ));
            };
            if self.live_flags[slot].swap(true, Ordering::AcqRel) {
                state.known_live.remove(&target);
                return Err(maintenance_invariant(format!(
                    "maintenance target {} was already published in its live slot",
                    target.get()
                )));
            }
            self.live_epoch.store(next_epoch, Ordering::Release);
            self.publish_resolution_change()?;
            return Ok(true);
        }
        Ok(false)
    }

    fn validate_target(&self, target: ClauseId) -> Result<(), FailureReport> {
        if !self.universe.contains(&target) {
            return Err(maintenance_invariant(format!(
                "maintenance track reached clause {} outside its block universe",
                target.get()
            )));
        }
        Ok(())
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, MaintenanceBlockArbiterState> {
        self.inner
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
    }
}

fn retain_dominant_failure(current: &mut Option<FailureReport>, report: FailureReport) {
    let replace = current.as_ref().is_none_or(|selected| {
        selected.scope() != FailureScope::RunGlobal && report.scope() == FailureScope::RunGlobal
    });
    if replace {
        *current = Some(report);
    }
}

enum RetryUpdate<'a> {
    Close,
    Timeout {
        permit: &'a super::catalog::MaintenanceRetryPermit,
        next_fmb_start_size: Option<crate::vampire::FmbSize>,
    },
    Frontier {
        permit: &'a super::catalog::MaintenanceRetryPermit,
        next_fmb_start_size: Option<crate::vampire::FmbSize>,
    },
    None,
}

fn apply_retry_update(
    catalog: &super::catalog::ClauseCatalog,
    target: ClauseId,
    update: RetryUpdate<'_>,
) -> Result<(), FailureReport> {
    match update {
        RetryUpdate::Close => catalog.close_maintenance_retry(target),
        RetryUpdate::Timeout {
            permit,
            next_fmb_start_size,
        } => catalog.record_maintenance_timeout(permit, next_fmb_start_size),
        RetryUpdate::Frontier {
            permit,
            next_fmb_start_size,
        } => catalog.record_maintenance_frontier(permit, next_fmb_start_size),
        RetryUpdate::None => Ok(()),
    }
}

/// Run all nonempty prepared maintenance tracks concurrently for one frozen
/// Candidate. Each task processes its own targets serially.
pub async fn run_maintenance_block(
    task: &SynthesisTask,
    state: &mut HoudiniState,
    command: VampireWorkerCommand,
    cancellation: &CancellationToken,
) -> MaintenanceExecutionOutcome<MaintenanceBlockResult> {
    if let Some(report) = state.maintenance_failure.clone() {
        return MaintenanceExecutionOutcome::Failed(report);
    }
    if cancellation.is_cancelled() {
        return MaintenanceExecutionOutcome::Cancelled;
    }

    let Some(plan) = state.maintenance_plan.as_ref().cloned() else {
        return fail_execution(
            state,
            maintenance_invariant("a maintenance block requires a current maintenance plan"),
        );
    };
    let generation = match state.allocate_generation() {
        Ok(generation) => generation,
        Err(report) => return fail_execution(state, report),
    };
    let setup = match prepare_concurrent_block(task, state, &plan, cancellation).await {
        Ok(setup) => setup,
        Err(ConcurrentPreparationError::Cancelled) => {
            let entry_active = Arc::clone(&state.active);
            let logged =
                append_concurrent_generation_abandoned(state, generation, &plan, entry_active)
                    .await;
            let settled = settle_concurrent_generation_history(state).await;
            if let Err(report) = logged.and(settled) {
                return fail_execution(state, report);
            }
            return MaintenanceExecutionOutcome::Cancelled;
        }
        Err(ConcurrentPreparationError::Failure(report)) => {
            // Preserve the preparation failure as the primary cause even if
            // its optional retirement record cannot be written.
            let _ = append_concurrent_generation_abandoned(
                state,
                generation,
                &plan,
                Arc::clone(&state.active),
            )
            .await;
            let _ = settle_concurrent_generation_history(state).await;
            return fail_execution(state, report);
        }
    };
    if setup.tracks.is_empty() {
        let report =
            maintenance_invariant("nonempty Active produced no nonempty maintenance track");
        let _ = append_concurrent_generation_abandoned(
            state,
            generation,
            &plan,
            Arc::clone(&setup.entry_active),
        )
        .await;
        let _ = settle_concurrent_generation_history(state).await;
        return fail_execution(state, report);
    }
    if let Err(report) =
        append_concurrent_generation_open(state, generation, &plan, Arc::clone(&setup.entry_active))
            .await
    {
        return fail_execution(state, report);
    }
    if cancellation.is_cancelled() {
        let logged = append_concurrent_generation_canceled(
            state,
            generation,
            Arc::clone(&setup.entry_active),
            Arc::new(ClauseSet::new()),
        )
        .await;
        let settled = settle_concurrent_generation_history(state).await;
        if let Err(report) = logged.and(settled) {
            return fail_execution(state, report);
        }
        return MaintenanceExecutionOutcome::Cancelled;
    }

    let block_cancellation = CancellationToken::new();
    let arbiter = Arc::new(MaintenanceBlockArbiter::new(
        Arc::clone(&plan),
        generation,
        Arc::clone(&setup.entry_active),
        Arc::clone(&setup.supported_targets),
        Arc::clone(&setup.core_covered_targets),
        Arc::clone(&setup.live_slots),
        Arc::clone(&setup.wait_ranks),
        Arc::clone(&setup.live_flags),
        Arc::clone(&setup.nonproved_flags),
        state.catalog.encoding_context().clone(),
        state.admission.clone(),
        setup.known_live,
        block_cancellation.clone(),
        state.telemetry.clone(),
    ));
    let mut tracks = JoinSet::new();
    let retry_increments = state.verification.maintenance_retry_increments_arc();
    let command = Arc::new(command);
    for track in &setup.tracks {
        let input = ConcurrentTrackInput {
            catalog: state.catalog.clone(),
            admission: state.admission.clone(),
            artifacts: state.artifacts.clone(),
            candidate_snapshot: Arc::clone(&setup.candidate_snapshot),
            candidate_bodies: setup.bodies.antecedent_snapshot(),
            bodies: Arc::clone(&setup.bodies),
            search_limit: state.verification.search_limit(),
            retry_increments: Arc::clone(&retry_increments),
            command: Arc::clone(&command),
            houdini_run_id: state.houdini_run_id,
            generation,
            track_index: track.index,
            targets: Arc::clone(&track.targets),
            arbiter: Arc::clone(&arbiter),
            cancellation: block_cancellation.clone(),
            telemetry: state.telemetry.clone(),
        };
        tracks.spawn(run_concurrent_track(input));
    }

    let mut caller_cancelled = false;
    while !tracks.is_empty() {
        let joined = if caller_cancelled {
            tracks.join_next().await
        } else {
            tokio::select! {
                biased;
                _ = cancellation.cancelled() => {
                    caller_cancelled = true;
                    arbiter.publish_external_cancellation();
                    continue;
                }
                joined = tracks.join_next() => joined,
            }
        };
        let Some(joined) = joined else {
            break;
        };
        if let Err(error) = joined {
            arbiter.publish_failure(maintenance_global_failure(format!(
                "maintenance track task failed before join: {error}"
            )));
        }
    }

    // No task or solver process survives this point. The block-local Arc is
    // reduced to this owner before its immutable close snapshot is taken.
    let settled = match Arc::try_unwrap(arbiter) {
        Ok(arbiter) => arbiter.into_snapshot(),
        Err(arbiter) => {
            let report = maintenance_global_failure(format!(
                "maintenance block retained {} unexpected arbiter owners after track join",
                Arc::strong_count(&arbiter)
            ));
            let _ = append_concurrent_generation_aborted(state, generation, report.clone()).await;
            let _ = settle_concurrent_generation_history(state).await;
            return fail_execution(state, report);
        }
    };
    if let Some(report) = settled.failure {
        let _ = append_concurrent_generation_aborted(state, generation, report.clone()).await;
        let _ = settle_concurrent_generation_history(state).await;
        return fail_execution(state, report);
    }
    if settled.externally_cancelled {
        let logged = append_concurrent_generation_canceled(
            state,
            generation,
            Arc::clone(&setup.entry_active),
            Arc::new(settled.known_live),
        )
        .await;
        let settled = settle_concurrent_generation_history(state).await;
        if let Err(report) = logged.and(settled) {
            return fail_execution(state, report);
        }
        return MaintenanceExecutionOutcome::Cancelled;
    }
    let outcome = settled.outcome.unwrap_or(MaintenanceBlockOutcome::Stable);
    if outcome.is_stable() && settled.known_live.len() != setup.entry_active.len() {
        let report =
            maintenance_invariant("concurrent tracks stopped before exhausting current Active");
        let _ = append_concurrent_generation_aborted(state, generation, report.clone()).await;
        let _ = settle_concurrent_generation_history(state).await;
        return fail_execution(state, report);
    }

    state.record_proof_supports(settled.proof_supports);
    complete_concurrent_block(
        state,
        ConcurrentBlockClose {
            plan,
            generation,
            entry_active: setup.entry_active,
            candidate: setup.candidate,
            known_live: settled.known_live,
            outcome,
        },
        cancellation,
    )
    .await
}

/// Restart fresh exact-Candidate concurrent blocks after each one-target
/// exclusion. The Phase 3C sequential entry point remains independently
/// available as the differential oracle.
pub async fn run_maintenance_blocks(
    task: &SynthesisTask,
    state: &mut HoudiniState,
    command: VampireWorkerCommand,
    cancellation: &CancellationToken,
) -> MaintenanceExecutionOutcome<Option<MaintenanceBlockResult>> {
    while !state.active.is_empty() {
        let result = match run_maintenance_block(task, state, command.clone(), cancellation).await {
            MaintenanceExecutionOutcome::Complete(result) => result,
            MaintenanceExecutionOutcome::Cancelled => {
                return MaintenanceExecutionOutcome::Cancelled;
            }
            MaintenanceExecutionOutcome::Failed(report) => {
                return MaintenanceExecutionOutcome::Failed(report);
            }
        };
        if result.outcome.is_stable() {
            return MaintenanceExecutionOutcome::Complete(Some(result));
        }
        match apply_maintenance_exclusion_concurrent(state, &result, cancellation).await {
            Ok(()) => {}
            Err(ConcurrentPreparationError::Cancelled) => {
                return MaintenanceExecutionOutcome::Cancelled;
            }
            Err(ConcurrentPreparationError::Failure(report)) => {
                return fail_execution(state, report);
            }
        }
    }
    MaintenanceExecutionOutcome::Complete(None)
}

#[derive(Debug)]
struct ConcurrentTrackInput {
    catalog: super::catalog::ClauseCatalog,
    admission: crate::runtime::SolverAdmission,
    artifacts: crate::ArtifactStore,
    candidate_snapshot: Arc<CandidateSnapshot>,
    candidate_bodies: Arc<[crate::encoding::PreparedBodyRef]>,
    bodies: Arc<super::catalog::MaintenanceBlockBodies>,
    search_limit: std::time::Duration,
    retry_increments: Arc<[std::time::Duration]>,
    command: Arc<VampireWorkerCommand>,
    houdini_run_id: u64,
    generation: GenerationId,
    track_index: u64,
    targets: Arc<[ClauseId]>,
    arbiter: Arc<MaintenanceBlockArbiter>,
    cancellation: CancellationToken,
    telemetry: TelemetryHandle,
}

/// Candidate premises actually used by one Vampire maintenance proof.
///
/// The maintenance query names its antecedents positionally:
/// `axiom_k` is the k-th sorted Candidate clause and the final
/// index is the loop guard. Vampire proofs cite input formulas as
/// `file(SOURCE, NAME)`. The scan is strict: any unparseable
/// `file(` reference, any unknown input name, or a proof citing no
/// inputs at all yields `None`, and the caller records no support.
/// Soundness of the transfer is monotonicity of the step check in
/// the Candidate: if every cited Candidate premise is still
/// present, the old proof still applies. This is untrusted runtime
/// assistance; final certification remains the gate.
fn proof_support_premises(proof_text: &str, candidate: &CandidateSnapshot) -> Option<ClauseSet> {
    let members = candidate.members();
    let mut support = ClauseSet::new();
    let mut cited_any = false;
    for (start, _) in proof_text.match_indices("file(") {
        let rest = &proof_text[start + 5..];
        let close = rest.find(')')?;
        let arguments = &rest[..close];
        let name = arguments.rsplit(',').next()?.trim();
        cited_any = true;
        if let Some(index_text) = name.strip_prefix("axiom_") {
            let index = index_text.parse::<usize>().ok()?;
            match index.cmp(&members.len()) {
                std::cmp::Ordering::Less => {
                    support.insert(members[index]);
                }
                // The final antecedent is the loop guard: present
                // in every step query, so it never constrains
                // transfer.
                std::cmp::Ordering::Equal => {}
                std::cmp::Ordering::Greater => return None,
            }
        } else if name == "support_adom" || name == "goal" || name.starts_with("support_distinct_")
        {
            // Structural axioms present in every query.
        } else {
            return None;
        }
    }
    cited_any.then_some(support)
}

async fn run_concurrent_track(input: ConcurrentTrackInput) {
    for target in input.targets.iter().copied() {
        if input.arbiter.should_stop() || input.cancellation.is_cancelled() {
            return;
        }
        match input
            .arbiter
            .resolve_before_query(&input.catalog, target)
            .await
        {
            Ok(TargetPreparation::Query) => {}
            Ok(TargetPreparation::Skip) => continue,
            Ok(TargetPreparation::Stop) => return,
            Err(report) => {
                input
                    .arbiter
                    .publish_failure(maintenance_context_failure(report));
                return;
            }
        }
        if input.arbiter.should_stop() || input.cancellation.is_cancelled() {
            return;
        }

        let permit = match input.catalog.select_maintenance_retry(
            target,
            Arc::clone(&input.candidate_snapshot),
            input.search_limit,
            &input.retry_increments,
        ) {
            Ok(MaintenanceRetryDecision::Ready(permit)) => permit,
            Ok(MaintenanceRetryDecision::Exhausted) => {
                let disposition = resolve_concurrent_nonproved(
                    &input,
                    target,
                    MaintenanceBlockOutcome::RetryExhausted(target),
                    RetryUpdate::None,
                )
                .await;
                if disposition == MaintenanceResultDisposition::Redundant {
                    continue;
                }
                return;
            }
            Err(report) => {
                input
                    .arbiter
                    .publish_failure(maintenance_context_failure(report));
                return;
            }
        };

        let Some(goal) = input.bodies.target(target).cloned() else {
            input.arbiter.publish_failure(maintenance_invariant(format!(
                "maintenance block lacks the WP body for clause {}",
                target.get()
            )));
            return;
        };
        let artifacts = input
            .artifacts
            .scoped(ScopeTag::Houdini)
            .scoped(ScopeTag::Generation(input.generation.get()))
            .scoped(ScopeTag::Track(input.track_index))
            .scoped(ScopeTag::Clause(target.get()))
            .scoped(ScopeTag::verification_stage("maintenance"));
        let entailment = match assemble_entailment(
            input.catalog.encoding_context(),
            &input.admission,
            &artifacts,
            Arc::clone(&input.candidate_bodies),
            vec![goal],
            &input.cancellation,
        )
        .await
        {
            Ok(entailment) => entailment,
            Err(EncodingError::Cancelled) => return,
            Err(EncodingError::Failure(report)) => {
                if report.scope() == FailureScope::RunGlobal {
                    input.arbiter.publish_failure(report);
                } else {
                    // Assembly may have overlapped a support/coverage
                    // publication or an already-selected block result. Avoid
                    // manufacturing a diagnostic for work which no longer
                    // needs to compete at the close boundary.
                    match input
                        .arbiter
                        .resolve_before_query(&input.catalog, target)
                        .await
                    {
                        Ok(TargetPreparation::Skip) => continue,
                        Ok(TargetPreparation::Stop) => return,
                        Ok(TargetPreparation::Query) => {}
                        Err(shortcut_failure) => {
                            input
                                .arbiter
                                .publish_failure(maintenance_context_failure(shortcut_failure));
                            return;
                        }
                    }
                    let diagnostic = match publish_maintenance_failure_diagnostic(
                        &artifacts,
                        input.generation,
                        input.track_index,
                        target,
                        report,
                    )
                    .await
                    {
                        Ok(reference) => reference,
                        Err(publication) => {
                            input.arbiter.publish_failure(publication);
                            return;
                        }
                    };
                    if let Err(history_error) = append_maintenance_assembly_failure_history(
                        &input, &artifacts, target, diagnostic,
                    )
                    .await
                    {
                        input.arbiter.publish_failure(history_error);
                        return;
                    }
                    let disposition = resolve_concurrent_nonproved(
                        &input,
                        target,
                        MaintenanceBlockOutcome::Failed(target),
                        RetryUpdate::None,
                    )
                    .await;
                    if disposition == MaintenanceResultDisposition::Redundant {
                        continue;
                    }
                }
                return;
            }
        };

        let attempt = match artifacts.begin_entailment_attempt(&entailment) {
            Ok(attempt) => attempt,
            Err(report) => {
                input.arbiter.publish_failure(report);
                return;
            }
        };
        if let Err(report) = append_maintenance_attempt_history(
            &input,
            &artifacts,
            target,
            permit.initial_allowance(),
            permit.allowance(),
            attempt.attempt_id(),
            None,
            None,
            "pending",
        )
        .await
        {
            input.arbiter.publish_failure(report);
            return;
        }
        // Count one requested ProofAndFmb race. Actual child-process launches
        // are observable only at the Vampire process boundary.
        input
            .telemetry
            .increment("houdini.maintenance.proof_and_fmb_requests", 1);
        input.telemetry.record_clause_solver_attempt(target.get());
        if input.telemetry.level() == TelemetryLevel::Detailed {
            input.telemetry.event(
                "maintenance_query_started",
                serde_json::json!({
                    "generation": input.generation.get(),
                    "track": input.track_index,
                    "target": target.get(),
                    "initial_allowance_nanoseconds": permit.initial_allowance().as_nanos().min(u128::from(u64::MAX)) as u64,
                    "allowance_nanoseconds": permit.allowance().as_nanos().min(u128::from(u64::MAX)) as u64,
                    "fmb_start_size": permit.fmb_start_size().get(),
                }),
            );
        }
        let query_started = input.telemetry.is_enabled().then(Instant::now);
        let checked = check_entailment_attempt_detailed(
            &entailment,
            &attempt,
            VampireSearchBudget::cumulative(permit.initial_allowance(), permit.allowance()),
            VampireMode::ProofAndFmb(FmbOptions {
                start_size: permit.fmb_start_size(),
                ..FmbOptions::default()
            }),
            input.command.as_ref().clone(),
            input.admission.clone(),
            input.cancellation.clone(),
        )
        .await;
        let query_duration = query_started.map_or(Duration::ZERO, |started| started.elapsed());
        if input.telemetry.is_enabled() {
            input
                .telemetry
                .add_duration("houdini.maintenance.query_inclusive", query_duration);
        }
        if checked.attempt_id() != Some(attempt.attempt_id()) {
            record_maintenance_solver_result(
                &input.telemetry,
                input.generation,
                input.track_index,
                target,
                "failure",
                MaintenanceResultDisposition::CleanupOnly,
                query_duration,
            );
            input.arbiter.publish_failure(maintenance_invariant(
                "detailed maintenance result changed its preallocated attempt identity",
            ));
            return;
        }
        let terminal_artifact = checked.terminal_artifact();
        if let Some(report) =
            missing_terminal_artifact_failure(terminal_artifact, checked.outcome())
        {
            record_maintenance_solver_result(
                &input.telemetry,
                input.generation,
                input.track_index,
                target,
                maintenance_attempt_outcome(checked.outcome()),
                MaintenanceResultDisposition::CleanupOnly,
                query_duration,
            );
            input.arbiter.publish_failure(report);
            return;
        }
        let hot_result = maintenance_result_class(checked.outcome()).map(|class| {
            (
                class,
                terminal_artifact.expect("a complete maintenance result has durable evidence"),
            )
        });
        let checked = checked.into_outcome();
        let outcome_name = maintenance_attempt_outcome(&checked);
        let outcome_class = Some(outcome_name);
        let disposition;
        match checked {
            EntailmentInvocationOutcome::Result(EntailmentCheckResult::Proved {
                ref proof,
                ..
            }) => {
                let proof_support = artifacts
                    .resolve(proof.output())
                    .ok()
                    .and_then(|resolved| std::fs::read_to_string(resolved.path()).ok())
                    .and_then(|text| proof_support_premises(&text, &input.candidate_snapshot));
                match input
                    .arbiter
                    .publish_proved(&input.catalog, target, proof_support)
                {
                    Ok(TargetResolution::Continue) => {
                        disposition = MaintenanceResultDisposition::Applied
                    }
                    Ok(TargetResolution::Cleanup) | Ok(TargetResolution::Stop) => {
                        disposition = MaintenanceResultDisposition::CleanupOnly
                    }
                    Err(report) => {
                        input
                            .arbiter
                            .publish_failure(maintenance_context_failure(report));
                        disposition = MaintenanceResultDisposition::CleanupOnly;
                    }
                }
            }
            EntailmentInvocationOutcome::Result(EntailmentCheckResult::Refuted(_)) => {
                disposition = resolve_concurrent_nonproved(
                    &input,
                    target,
                    MaintenanceBlockOutcome::Refuted(target),
                    RetryUpdate::Close,
                )
                .await;
            }
            EntailmentInvocationOutcome::Result(EntailmentCheckResult::TimedOut {
                next_fmb_start_size,
                peer_failure,
            }) => {
                if let Some(report) = peer_failure
                    && is_fatal_target_failure(&report)
                {
                    input
                        .arbiter
                        .publish_failure(maintenance_context_failure(report));
                    disposition = MaintenanceResultDisposition::CleanupOnly;
                } else {
                    disposition = resolve_concurrent_nonproved(
                        &input,
                        target,
                        MaintenanceBlockOutcome::TimedOut(target),
                        RetryUpdate::Timeout {
                            permit: &permit,
                            next_fmb_start_size,
                        },
                    )
                    .await;
                }
            }
            EntailmentInvocationOutcome::Result(EntailmentCheckResult::Failure {
                report,
                next_fmb_start_size,
            }) => {
                if is_fatal_target_failure(&report) {
                    input.arbiter.publish_failure(report);
                    disposition = MaintenanceResultDisposition::CleanupOnly;
                } else {
                    disposition = resolve_concurrent_nonproved(
                        &input,
                        target,
                        MaintenanceBlockOutcome::Failed(target),
                        RetryUpdate::Frontier {
                            permit: &permit,
                            next_fmb_start_size,
                        },
                    )
                    .await;
                }
            }
            EntailmentInvocationOutcome::Cancelled(cancelled) => {
                disposition = MaintenanceResultDisposition::Canceled;
                if let Some(report) = fatal_cancelled_peer(&cancelled) {
                    input.arbiter.publish_failure(report);
                }
            }
            EntailmentInvocationOutcome::RunFailure(report) => {
                input.arbiter.publish_failure(report);
                disposition = MaintenanceResultDisposition::CleanupOnly;
            }
        }
        record_maintenance_solver_result(
            &input.telemetry,
            input.generation,
            input.track_index,
            target,
            outcome_name,
            disposition,
            query_duration,
        );
        if let Some((class, evidence)) = hot_result
            && let Err(report) = input.catalog.record_maintenance_result(
                target,
                MaintenanceResultUpdate {
                    candidate: input.candidate_snapshot.as_ref(),
                    run_id: input.houdini_run_id,
                    generation: input.generation.get(),
                    class,
                    disposition,
                    evidence,
                },
            )
        {
            input
                .arbiter
                .publish_failure(maintenance_context_failure(report));
            return;
        }
        if let Err(report) = append_maintenance_attempt_history(
            &input,
            &artifacts,
            target,
            permit.initial_allowance(),
            permit.allowance(),
            attempt.attempt_id(),
            terminal_artifact,
            outcome_class,
            disposition.history_name(),
        )
        .await
        {
            input.arbiter.publish_failure(report);
        }
        if input.arbiter.should_stop() {
            return;
        }
    }
}

/// Reject a complete attempt before any semantic or retry-state commit unless
/// its required terminal summary is durable. Preserve the exact publication
/// failure which explains a missing artifact; use an invariant report only for
/// an impossible nonfailure result without its summary.
fn missing_terminal_artifact_failure(
    terminal_artifact: Option<crate::ArtifactRef>,
    outcome: &EntailmentInvocationOutcome,
) -> Option<FailureReport> {
    if terminal_artifact.is_some() {
        return None;
    }
    Some(match outcome {
        EntailmentInvocationOutcome::RunFailure(report)
        | EntailmentInvocationOutcome::Result(EntailmentCheckResult::Failure { report, .. }) => {
            report.clone()
        }
        _ => maintenance_invariant(
            "complete maintenance attempt lacks its required terminal artifact",
        ),
    })
}

async fn publish_maintenance_failure_diagnostic(
    artifacts: &crate::ArtifactStore,
    generation: GenerationId,
    track_index: u64,
    target: ClauseId,
    report: FailureReport,
) -> Result<crate::ArtifactRef, FailureReport> {
    artifacts
        .publish_required_deferred_async(crate::ArtifactKind::FailureDiagnostic, move || {
            serde_json::to_vec(&serde_json::json!({
                "kind": "maintenance_assembly_failure",
                "generation": generation.get(),
                "track_index": track_index,
                "target": target.get(),
                "origin": format!("{:?}", report.origin()),
                "failure_kind": format!("{:?}", report.kind()),
                "scope": format!("{:?}", report.scope()),
                "detail": report.detail(),
                "references": report.artifact_references().iter().map(|reference| serde_json::json!({
                    "backend": reference.backend_id().to_string(),
                    "local_id": reference.local_id(),
                    "kind": format!("{:?}", reference.kind()),
                })).collect::<Vec<_>>(),
            }))
            .map(Arc::from)
            .map_err(|error| {
                maintenance_global_failure(format!(
                    "serialize maintenance assembly diagnostic: {error}"
                ))
            })
        })
        .await
}

async fn append_maintenance_assembly_failure_history(
    input: &ConcurrentTrackInput,
    artifacts: &crate::ArtifactStore,
    target: ClauseId,
    diagnostic: crate::ArtifactRef,
) -> Result<(), FailureReport> {
    if !input.arbiter.plan.policy().log_maintenance_history() {
        return Ok(());
    }
    let generation = input.generation;
    let track_index = input.track_index;
    artifacts
        .append_maintenance_history_deferred_async(move || {
            Ok((
                serde_json::json!({
                    "event": "maintenance_assembly_failure",
                    "generation": generation.get(),
                    "track_index": track_index,
                    "target": target.get(),
                    "artifact_reference": {
                        "backend": diagnostic.backend_id().to_string(),
                        "local_id": diagnostic.local_id(),
                        "kind": format!("{:?}", diagnostic.kind()),
                    },
                }),
                vec![target.get()],
            ))
        })
        .await
}

async fn resolve_concurrent_nonproved(
    input: &ConcurrentTrackInput,
    target: ClauseId,
    outcome: MaintenanceBlockOutcome,
    retry_update: RetryUpdate<'_>,
) -> MaintenanceResultDisposition {
    match input
        .arbiter
        .publish_nonproved(&input.catalog, target, outcome, retry_update)
        .await
    {
        Ok(TargetResolution::Continue) => {
            if matches!(outcome, MaintenanceBlockOutcome::Refuted(_)) {
                MaintenanceResultDisposition::Conflicting
            } else {
                MaintenanceResultDisposition::Redundant
            }
        }
        Ok(TargetResolution::Cleanup) => MaintenanceResultDisposition::CleanupOnly,
        Ok(TargetResolution::Stop) => MaintenanceResultDisposition::Applied,
        Err(report) => {
            input
                .arbiter
                .publish_failure(maintenance_context_failure(report));
            MaintenanceResultDisposition::CleanupOnly
        }
    }
}

fn maintenance_attempt_outcome(outcome: &EntailmentInvocationOutcome) -> &'static str {
    match outcome {
        EntailmentInvocationOutcome::Result(EntailmentCheckResult::Proved { .. }) => "proved",
        EntailmentInvocationOutcome::Result(EntailmentCheckResult::Refuted(_)) => "refuted",
        EntailmentInvocationOutcome::Result(EntailmentCheckResult::TimedOut { .. }) => "timed_out",
        EntailmentInvocationOutcome::Result(EntailmentCheckResult::Failure { .. })
        | EntailmentInvocationOutcome::RunFailure(_) => "failure",
        EntailmentInvocationOutcome::Cancelled(_) => "canceled",
    }
}

fn record_maintenance_solver_result(
    telemetry: &TelemetryHandle,
    generation: GenerationId,
    track_index: u64,
    target: ClauseId,
    outcome: &'static str,
    disposition: MaintenanceResultDisposition,
    duration: Duration,
) {
    if !telemetry.is_enabled() {
        return;
    }
    let disposition = disposition.history_name();
    telemetry.record_disposition(format!("maintenance_query_{outcome}"), 1);
    telemetry.record_disposition(format!("maintenance_query_{outcome}_{disposition}"), 1);
    telemetry.add_duration(
        format!("disposition.maintenance_query_{outcome}_{disposition}"),
        duration,
    );
    if telemetry.level() == TelemetryLevel::Detailed {
        telemetry.event(
            "maintenance_query_classified",
            serde_json::json!({
                "generation": generation.get(),
                "track": track_index,
                "target": target.get(),
                "outcome": outcome,
                "disposition": disposition,
                "inclusive_nanoseconds": duration.as_nanos().min(u128::from(u64::MAX)) as u64,
            }),
        );
    }
}

fn maintenance_result_class(
    outcome: &EntailmentInvocationOutcome,
) -> Option<MaintenanceResultClass> {
    match outcome {
        EntailmentInvocationOutcome::Result(EntailmentCheckResult::Proved { .. }) => {
            Some(MaintenanceResultClass::Proved)
        }
        EntailmentInvocationOutcome::Result(EntailmentCheckResult::Refuted(_)) => {
            Some(MaintenanceResultClass::Refuted)
        }
        EntailmentInvocationOutcome::Result(EntailmentCheckResult::TimedOut { .. }) => {
            Some(MaintenanceResultClass::TimedOut)
        }
        EntailmentInvocationOutcome::Result(EntailmentCheckResult::Failure { .. }) => {
            Some(MaintenanceResultClass::Failed)
        }
        EntailmentInvocationOutcome::Cancelled(_) | EntailmentInvocationOutcome::RunFailure(_) => {
            None
        }
    }
}

#[allow(clippy::too_many_arguments)]
async fn append_maintenance_attempt_history(
    input: &ConcurrentTrackInput,
    artifacts: &crate::ArtifactStore,
    target: ClauseId,
    initial_allowance: std::time::Duration,
    allowance: std::time::Duration,
    attempt_id: crate::AttemptId,
    terminal_artifact: Option<crate::ArtifactRef>,
    outcome: Option<&'static str>,
    disposition: &'static str,
) -> Result<(), FailureReport> {
    if !input.arbiter.plan.policy().log_maintenance_history() {
        return Ok(());
    }
    let record = MaintenanceAttemptHistoryRecord {
        event: "maintenance_attempt",
        attempt_id: attempt_id.get(),
        generation: input.generation.get(),
        target: target.get(),
        track_index: input.track_index,
        initial_allowance_nanos: initial_allowance.as_nanos(),
        allowance_nanos: allowance.as_nanos(),
        outcome,
        disposition,
        artifact_reference: terminal_artifact.map(MaintenanceAttemptArtifactRecord),
    };
    artifacts
        .append_maintenance_history_deferred_async(move || {
            let record = serde_json::to_value(record).map_err(|error| {
                FailureReport::maintenance_history(
                    FailureScope::LaneLocal,
                    format!("serialize maintenance-attempt history: {error}"),
                )
            })?;
            Ok((record, vec![target.get()]))
        })
        .await
}

#[derive(Serialize)]
struct MaintenanceAttemptHistoryRecord {
    event: &'static str,
    attempt_id: u64,
    generation: u64,
    target: u64,
    track_index: u64,
    initial_allowance_nanos: u128,
    allowance_nanos: u128,
    outcome: Option<&'static str>,
    disposition: &'static str,
    #[serde(skip_serializing_if = "Option::is_none")]
    artifact_reference: Option<MaintenanceAttemptArtifactRecord>,
}

struct MaintenanceAttemptArtifactRecord(crate::ArtifactRef);

impl Serialize for MaintenanceAttemptArtifactRecord {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        use serde::ser::SerializeStruct;
        let mut record = serializer.serialize_struct("ArtifactRef", 3)?;
        record.serialize_field("backend", &self.0.backend_id().to_string())?;
        record.serialize_field("local_id", &self.0.local_id())?;
        record.serialize_field("kind", &format!("{:?}", self.0.kind()))?;
        record.end()
    }
}

#[derive(Debug)]
enum ConcurrentPreparationError {
    Cancelled,
    Failure(FailureReport),
}

impl From<FailureReport> for ConcurrentPreparationError {
    fn from(report: FailureReport) -> Self {
        Self::Failure(report)
    }
}

async fn prepare_concurrent_block(
    task: &SynthesisTask,
    state: &HoudiniState,
    plan: &Arc<MaintenancePlan>,
    cancellation: &CancellationToken,
) -> Result<ConcurrentBlockSetup, ConcurrentPreparationError> {
    let catalog = state.catalog.clone();
    let core = Arc::clone(&state.core);
    let init_candidates = Arc::clone(&state.init_candidates);
    let active = Arc::clone(&state.active);
    let present_support_count = Arc::clone(&state.present_support_count);
    let proof_supports = Arc::clone(&state.proof_support_sets);
    let published_candidate_snapshot = state.candidate_snapshot.as_ref().cloned();
    let plan = Arc::clone(plan);
    let task_identity = task.identity().clone();
    let catalog_identity = catalog.identity();
    let encoding_context_id = Arc::<str>::from(catalog.encoding_context().context_id());
    let proposal_generation = state.proposal_generation;
    let maintenance_policy = state.maintenance_policy.clone();
    let bulk_maint_proved = state.bulk_maint_proved;
    let maintenance_failure = state.maintenance_failure.clone();
    let context = catalog.encoding_context().clone();
    let guard = context
        .prepare_loop_guard_body(&state.admission, &state.artifacts, cancellation)
        .await
        .map_err(|error| match error {
            EncodingError::Cancelled => ConcurrentPreparationError::Cancelled,
            EncodingError::Failure(report) => {
                ConcurrentPreparationError::Failure(maintenance_context_failure(report))
            }
        })?;
    let built = context
        .run_cpu_job(&state.admission, cancellation, move |job_cancellation| {
            if maintenance_failure.is_some()
                || bulk_maint_proved
                || active.is_empty()
                || !plan.matches_runtime_capture(
                    &task_identity,
                    catalog_identity,
                    &encoding_context_id,
                    proposal_generation,
                    &core,
                    &init_candidates,
                    &maintenance_policy,
                )
                || !active.is_subset(plan.initial_active())
                || present_support_count.len() != active.len()
                || active
                    .iter()
                    .any(|target| !present_support_count.contains_key(target))
            {
                return Err(CpuJobError::Failure(maintenance_invariant(
                    "concurrent maintenance-block entry state is stale or incomplete",
                )));
            }
            let entry_active = Arc::new(active.as_ref().clone());
            let candidate = Arc::new(union(core.as_ref(), entry_active.as_ref()));
            let candidate_snapshot = match published_candidate_snapshot {
                Some(snapshot) if snapshot.equals_set(candidate.as_ref()) => snapshot,
                Some(_) => {
                    return Err(CpuJobError::Failure(maintenance_invariant(
                        "current Candidate snapshot does not match Core and Active",
                    )));
                }
                None => CandidateSnapshot::root(Arc::clone(&candidate)),
            };
            let bodies = catalog
                .snapshot_maintenance_block_bodies(
                    candidate.as_ref(),
                    entry_active.as_ref(),
                    guard,
                    &job_cancellation,
                )
                .map_err(|error| match error {
                    MaintenanceSnapshotError::Cancelled => CpuJobError::Cancelled,
                    MaintenanceSnapshotError::Failure(report) => CpuJobError::Failure(report),
                })?;
            let mut supported_targets = HashSet::with_capacity(entry_active.len());
            let mut core_covered_targets = HashSet::with_capacity(entry_active.len());
            let mut live_slots = HashMap::with_capacity(entry_active.len());
            let mut wait_ranks = HashMap::with_capacity(entry_active.len());
            for target in entry_active.iter().copied() {
                let slot = live_slots.len();
                live_slots.insert(target, slot);
                if present_support_count.get(&target).copied().unwrap_or(0) > 0 {
                    supported_targets.insert(target);
                } else if proof_supports.get(&target).is_some_and(|premises| {
                    premises.iter().all(|premise| candidate.contains(premise))
                }) {
                    // A retained Vampire proof cited only premises
                    // still present in this block's Candidate, so
                    // the step check transfers by monotonicity.
                    supported_targets.insert(target);
                }
                if plan
                    .covered_by(target)
                    .iter()
                    .any(|source| core.contains(source))
                {
                    core_covered_targets.insert(target);
                }
            }
            let live_flags = (0..entry_active.len())
                .map(|_| AtomicBool::new(false))
                .collect::<Vec<_>>();
            let nonproved_flags = (0..entry_active.len())
                .map(|_| AtomicBool::new(false))
                .collect::<Vec<_>>();
            let mut tracks = Vec::with_capacity(plan.schedule().tracks().len());
            for (track_position, track) in plan.schedule().tracks().iter().enumerate() {
                if job_cancellation.is_cancelled() {
                    return Err(CpuJobError::Cancelled);
                }
                let targets = track
                    .targets()
                    .iter()
                    .copied()
                    .filter(|target| entry_active.contains(target))
                    .collect::<Vec<_>>();
                if !targets.is_empty() {
                    for (target_position, target) in targets.iter().enumerate() {
                        wait_ranks.insert(*target, (track_position, target_position));
                    }
                    let index = u64::try_from(track_position).map_err(|_| {
                        CpuJobError::Failure(maintenance_invariant(
                            "maintenance track index exceeds UInt64 range",
                        ))
                    })?;
                    tracks.push(ConcurrentTrackWork {
                        index,
                        targets: targets.into(),
                    });
                }
            }
            Ok(ConcurrentBlockSetup {
                entry_active,
                candidate,
                candidate_snapshot,
                bodies: Arc::new(bodies),
                supported_targets: Arc::new(supported_targets),
                core_covered_targets: Arc::new(core_covered_targets),
                live_slots: Arc::new(live_slots),
                wait_ranks: Arc::new(wait_ranks),
                live_flags: live_flags.into(),
                nonproved_flags: nonproved_flags.into(),
                known_live: ClauseSet::with_capacity(active.len()),
                tracks,
            })
        })
        .await;
    map_cpu_job_result(built, "concurrent maintenance-block setup")
}

async fn complete_concurrent_block(
    state: &mut HoudiniState,
    close: ConcurrentBlockClose,
    _cancellation: &CancellationToken,
) -> MaintenanceExecutionOutcome<MaintenanceBlockResult> {
    let result = MaintenanceBlockResult::new(
        state.catalog.identity(),
        close.plan,
        Arc::clone(&state.maintenance_state_revision),
        close.generation,
        close.entry_active,
        close.candidate,
        close.known_live,
        close.outcome,
    );
    if let Err(report) = append_concurrent_generation_history(state, &result, false).await {
        return fail_execution(state, report);
    }
    if state.maintenance_policy.fail_on_history_log_error()
        && let Err(report) = state.artifacts.settle_maintenance_history_async().await
    {
        return fail_execution(state, report);
    }
    MaintenanceExecutionOutcome::Complete(result)
}

async fn append_concurrent_generation_open(
    state: &mut HoudiniState,
    generation: GenerationId,
    plan: &Arc<MaintenancePlan>,
    entry_active: Arc<ClauseSet>,
) -> Result<(), FailureReport> {
    let is_baseline = !state
        .history_baseline_plan
        .as_ref()
        .is_some_and(|baseline| Arc::ptr_eq(baseline, plan));
    let baseline_generation = if is_baseline {
        None
    } else {
        state.history_baseline_generation
    };
    append_concurrent_generation_state(
        state,
        generation,
        is_baseline.then(|| Arc::clone(plan)),
        is_baseline.then_some(entry_active),
        "open",
        None,
        None,
        None,
        baseline_generation,
    )
    .await?;
    if is_baseline {
        state.history_baseline_plan = Some(Arc::clone(plan));
        state.history_baseline_generation = Some(generation.get());
    }
    Ok(())
}

async fn append_concurrent_generation_abandoned(
    state: &HoudiniState,
    generation: GenerationId,
    plan: &Arc<MaintenancePlan>,
    entry_active: Arc<ClauseSet>,
) -> Result<(), FailureReport> {
    append_concurrent_generation_state(
        state,
        generation,
        Some(Arc::clone(plan)),
        Some(entry_active),
        "abandoned",
        None,
        None,
        None,
        None,
    )
    .await
}

async fn append_concurrent_generation_aborted(
    state: &HoudiniState,
    generation: GenerationId,
    report: FailureReport,
) -> Result<(), FailureReport> {
    append_concurrent_generation_state(
        state,
        generation,
        None,
        None,
        "aborted",
        None,
        None,
        Some(report),
        None,
    )
    .await
}

async fn append_concurrent_generation_canceled(
    state: &HoudiniState,
    generation: GenerationId,
    entry_active: Arc<ClauseSet>,
    known_live: Arc<ClauseSet>,
) -> Result<(), FailureReport> {
    if !state.maintenance_policy.log_maintenance_history() {
        return Ok(());
    }
    history_artifacts(state, generation)
        .append_maintenance_history_deferred_async(move || {
            let target_ids = sorted_clause_values(entry_active.as_ref());
            Ok((
                serde_json::json!({
                    "event": "maintenance_generation_canceled",
                    "generation": generation.get(),
                    "known_live": sorted_clause_values(known_live.as_ref()),
                }),
                target_ids,
            ))
        })
        .await
}

#[allow(clippy::too_many_arguments)]
async fn append_concurrent_generation_state(
    state: &HoudiniState,
    generation: GenerationId,
    plan: Option<Arc<MaintenancePlan>>,
    entry_active: Option<Arc<ClauseSet>>,
    generation_state: &'static str,
    known_live: Option<Arc<ClauseSet>>,
    close: Option<(MaintenanceBlockOutcome, bool)>,
    reason: Option<FailureReport>,
    baseline_generation: Option<u64>,
) -> Result<(), FailureReport> {
    if !state.maintenance_policy.log_maintenance_history() {
        return Ok(());
    }
    history_artifacts(state, generation)
        .append_maintenance_history_deferred_async(move || {
            let indexed_clauses = entry_active
                .as_deref()
                .map(sorted_clause_values)
                .unwrap_or_default();
            let initial_core = plan.as_ref().map(|plan| sorted_clause_values(plan.core()));
            let initial_active = entry_active.as_deref().map(sorted_clause_values);
            let candidate = match (plan.as_ref(), entry_active.as_deref()) {
                (Some(plan), Some(entry_active)) => {
                    Some(sorted_clause_values(&union(plan.core(), entry_active)))
                }
                _ => None,
            };
            let (outcome, target, exclusion_applied) = close
                .map(|(outcome, applied)| {
                    (
                        Some(outcome.history_kind()),
                        outcome.target().map(ClauseId::get),
                        Some(applied),
                    )
                })
                .unwrap_or((None, None, None));
            let record = serde_json::to_value(GenerationHistoryRecord {
                event: "maintenance_generation_state",
                generation: generation.get(),
                initial_core,
                initial_active,
                candidate,
                state: generation_state,
                known_live: known_live.as_deref().map(sorted_clause_values),
                outcome,
                target,
                exclusion_applied,
                reason: reason.as_ref().map(FailureHistoryRecord::from),
                baseline_generation,
            })
            .map_err(|error| {
                FailureReport::maintenance_history(
                    FailureScope::LaneLocal,
                    format!("serialize maintenance-generation history: {error}"),
                )
            })?;
            Ok((record, indexed_clauses))
        })
        .await
}

async fn settle_concurrent_generation_history(state: &HoudiniState) -> Result<(), FailureReport> {
    if state.maintenance_policy.fail_on_history_log_error() {
        state.artifacts.settle_maintenance_history_async().await
    } else {
        Ok(())
    }
}

struct ConcurrentBlockClose {
    plan: Arc<MaintenancePlan>,
    generation: GenerationId,
    entry_active: Arc<ClauseSet>,
    candidate: Arc<ClauseSet>,
    known_live: ClauseSet,
    outcome: MaintenanceBlockOutcome,
}

async fn append_concurrent_generation_history(
    state: &mut HoudiniState,
    result: &MaintenanceBlockResult,
    exclusion_applied: bool,
) -> Result<(), FailureReport> {
    append_concurrent_generation_state(
        state,
        result.generation,
        None,
        None,
        "closed",
        (!exclusion_applied).then(|| Arc::clone(&result.known_live)),
        Some((result.outcome, exclusion_applied)),
        None,
        None,
    )
    .await
}

async fn apply_maintenance_exclusion_concurrent(
    state: &mut HoudiniState,
    result: &MaintenanceBlockResult,
    _cancellation: &CancellationToken,
) -> Result<(), ConcurrentPreparationError> {
    let target = result.outcome.target().ok_or_else(|| {
        ConcurrentPreparationError::Failure(maintenance_invariant(
            "a stable block result cannot drive exclusion",
        ))
    })?;
    let plan = state.maintenance_plan.as_ref().ok_or_else(|| {
        ConcurrentPreparationError::Failure(maintenance_invariant(
            "maintenance exclusion requires a current plan",
        ))
    })?;
    if state.maintenance_failure.is_some()
        || result.catalog_identity != state.catalog.identity()
        || !Arc::ptr_eq(&result.plan, plan)
        || !Arc::ptr_eq(&result.state_revision, &state.maintenance_state_revision)
        || !state.active.contains(&target)
        || result.known_live.contains(&target)
    {
        return Err(ConcurrentPreparationError::Failure(maintenance_invariant(
            "maintenance exclusion result does not match current state",
        )));
    }

    // Validate the exact degree-bounded update before publishing any part of
    // it. No allocation or fallible operation occurs after this first pass.
    let next_revision = Arc::new(());
    if !state.present_support_count.contains_key(&target)
        || Arc::get_mut(&mut state.active).is_none()
        || Arc::get_mut(&mut state.present_support_count).is_none()
    {
        return Err(ConcurrentPreparationError::Failure(maintenance_invariant(
            "maintenance exclusion state is not uniquely mutable",
        )));
    }
    for affected in plan.supported_targets_by(target).iter().copied() {
        if affected == target || !state.active.contains(&affected) {
            continue;
        }
        if state
            .present_support_count
            .get(&affected)
            .copied()
            .unwrap_or(0)
            == 0
        {
            return Err(ConcurrentPreparationError::Failure(maintenance_invariant(
                format!(
                    "present-support count for clause {} would underflow",
                    affected.get()
                ),
            )));
        }
    }

    let active = Arc::get_mut(&mut state.active)
        .expect("maintenance exclusion validated unique Active ownership");
    let support_counts = Arc::get_mut(&mut state.present_support_count)
        .expect("maintenance exclusion validated unique support-count ownership");
    let removed = active.remove(&target);
    debug_assert!(removed);
    for affected in plan.supported_targets_by(target).iter().copied() {
        if affected == target || !active.contains(&affected) {
            continue;
        }
        *support_counts
            .get_mut(&affected)
            .expect("the exclusion preflight validated every support count") -= 1;
    }
    support_counts.remove(&target);
    let active_is_empty = active.is_empty();
    state.candidate_snapshot = None;
    if active_is_empty {
        state.maintenance_plan = None;
    }
    state.maintenance_state_revision = next_revision;
    if state.maintenance_policy.log_maintenance_history() {
        append_concurrent_generation_history(state, result, true)
            .await
            .map_err(ConcurrentPreparationError::Failure)?;
        let generation = result.generation;
        history_artifacts(state, generation)
            .append_maintenance_history_deferred_async(move || {
                let record = serde_json::to_value(ExclusionHistoryRecord {
                    event: "maintenance_exclusion_applied",
                    generation: generation.get(),
                    target: target.get(),
                })
                .map_err(|error| {
                    FailureReport::maintenance_history(
                        FailureScope::LaneLocal,
                        format!("serialize maintenance-exclusion history: {error}"),
                    )
                })?;
                Ok((record, vec![target.get()]))
            })
            .await?;
        if state.maintenance_policy.fail_on_history_log_error() {
            state
                .artifacts
                .settle_maintenance_history_async()
                .await
                .map_err(ConcurrentPreparationError::Failure)?;
        }
    }
    Ok(())
}

fn map_cpu_job_result<T>(
    result: Result<T, CpuJobError>,
    context: &str,
) -> Result<T, ConcurrentPreparationError> {
    match result {
        Ok(value) => Ok(value),
        Err(CpuJobError::Cancelled) | Err(CpuJobError::Admission(AdmissionError::Cancelled)) => {
            Err(ConcurrentPreparationError::Cancelled)
        }
        Err(CpuJobError::Admission(AdmissionError::Closed(report)))
        | Err(CpuJobError::Failure(report)) => Err(ConcurrentPreparationError::Failure(report)),
        Err(error) => Err(ConcurrentPreparationError::Failure(
            maintenance_global_failure(format!("{context} failed: {error}")),
        )),
    }
}

// ------------------------------------------------------------
// Atomic Durable State Transitions
// ------------------------------------------------------------

/// Remove the one nonstable target and update support counts atomically.
pub fn apply_maintenance_exclusion(
    state: &mut HoudiniState,
    result: &MaintenanceBlockResult,
) -> Result<(), FailureReport> {
    let transition = match stage_exclusion(state, result) {
        Ok(transition) => transition,
        Err(report) => {
            state.record_execution_failure(report.clone());
            return Err(report);
        }
    };
    if Arc::get_mut(&mut state.active).is_none() {
        let report = maintenance_invariant("mutable Active unexpectedly has another owner");
        state.record_execution_failure(report.clone());
        return Err(report);
    }
    let active =
        Arc::get_mut(&mut state.active).expect("the independently owned Active was just validated");

    match state.candidate_snapshot.as_ref() {
        Some(candidate) if candidate.contains(transition.target) => {}
        _ => {
            let report =
                maintenance_invariant("maintenance exclusion lacks a matching Candidate snapshot");
            state.record_execution_failure(report.clone());
            return Err(report);
        }
    }
    let next_candidate = if active.len() > 1 {
        let mut members = active
            .iter()
            .copied()
            .filter(|clause| *clause != transition.target)
            .chain(state.core.iter().copied())
            .collect::<Vec<_>>();
        members.sort_unstable();
        members.dedup();
        Some(CandidateSnapshot::from_sorted(members))
    } else {
        None
    };

    apply_staged_maintenance_exclusion(state, result, transition, next_candidate, true)
}

fn apply_staged_maintenance_exclusion(
    state: &mut HoudiniState,
    result: &MaintenanceBlockResult,
    transition: ExclusionTransition,
    next_candidate: Option<Arc<CandidateSnapshot>>,
    append_history: bool,
) -> Result<(), FailureReport> {
    if Arc::get_mut(&mut state.active).is_none() {
        let report = maintenance_invariant("mutable Active unexpectedly has another owner");
        state.record_execution_failure(report.clone());
        return Err(report);
    }
    let active =
        Arc::get_mut(&mut state.active).expect("the independently owned Active was just validated");
    match state.candidate_snapshot.as_ref() {
        Some(candidate) if candidate.contains(transition.target) => {}
        _ => {
            let report =
                maintenance_invariant("maintenance exclusion lacks a matching Candidate snapshot");
            state.record_execution_failure(report.clone());
            return Err(report);
        }
    }
    if (active.len() > 1) != next_candidate.is_some() {
        let report = maintenance_invariant(
            "maintenance exclusion received an inconsistent next Candidate snapshot",
        );
        state.record_execution_failure(report.clone());
        return Err(report);
    }

    // All validation and allocation completed before this mutation sequence.
    let removed = active.remove(&transition.target);
    debug_assert!(removed);
    for target in transition.decrements {
        let count = Arc::get_mut(&mut state.present_support_count)
            .expect("stopped maintenance state uniquely owns its support-count table")
            .get_mut(&target)
            .expect("exclusion staging validated every support count");
        *count -= 1;
    }
    Arc::get_mut(&mut state.present_support_count)
        .expect("stopped maintenance state uniquely owns its support-count table")
        .remove(&transition.target);
    let finished_plan = active.is_empty();
    if finished_plan {
        state.present_support_count = Arc::new(std::collections::HashMap::new());
        state.maintenance_plan = None;
        state.candidate_snapshot = None;
    } else {
        state.candidate_snapshot = next_candidate;
    }
    state.maintenance_state_revision = Arc::new(());
    if append_history && let Err(report) = append_exclusion_history(state, result) {
        state.record_execution_failure(report.clone());
        return Err(report);
    }
    Ok(())
}

/// Validate and move one nonempty stable Active set into protected Core.
pub fn expand_core(
    state: &mut HoudiniState,
    stable: &MaintenanceBlockResult,
) -> Result<(), FailureReport> {
    expand_core_impl(state, stable, true)
}

/// Consume a stable result whose concurrent block boundary already settled
/// strict optional history.
fn expand_core_after_history_settlement(
    state: &mut HoudiniState,
    stable: &MaintenanceBlockResult,
) -> Result<(), FailureReport> {
    expand_core_impl(state, stable, false)
}

fn expand_core_impl(
    state: &mut HoudiniState,
    stable: &MaintenanceBlockResult,
    settle_history: bool,
) -> Result<(), FailureReport> {
    if let Some(report) = state.maintenance_failure.clone() {
        return Err(report);
    }
    if !stable.outcome.is_stable()
        || stable.catalog_identity != state.catalog.identity()
        || !Arc::ptr_eq(&stable.state_revision, &state.maintenance_state_revision)
        || !state
            .maintenance_plan
            .as_ref()
            .is_some_and(|plan| Arc::ptr_eq(&stable.plan, plan))
        || stable.entry_active.as_ref() != state.active.as_ref()
        || stable.known_live.as_ref() != state.active.as_ref()
        || !is_exact_union(
            stable.candidate.as_ref(),
            state.core.as_ref(),
            state.active.as_ref(),
        )
    {
        let report = maintenance_invariant(
            "Core expansion requires the current exact stable maintenance result",
        );
        state.record_execution_failure(report.clone());
        return Err(report);
    }
    if settle_history
        && state.maintenance_policy.fail_on_history_log_error()
        && let Err(report) = state.artifacts.settle_maintenance_history()
    {
        state.record_execution_failure(report.clone());
        return Err(report);
    }
    let staged = match stage_core_expansion(state) {
        Ok(staged) => staged,
        Err(report) => {
            state.record_execution_failure(report.clone());
            return Err(report);
        }
    };

    commit_core_expansion(state, staged);
    Ok(())
}

/// Publish one fully staged Core expansion.  Callers own the distinct stable
/// per-clause and exact-bulk capabilities which authorize reaching this point.
fn commit_core_expansion(state: &mut HoudiniState, staged: ClauseSet) {
    // All validation and allocation completed before this coherent publish.
    state.core = Arc::new(staged);
    state.init_candidates = Arc::new(ClauseSet::new());
    state.active = Arc::new(ClauseSet::new());
    state.candidate_snapshot = None;
    state.present_support_count = Arc::new(std::collections::HashMap::new());
    state.maintenance_plan = None;
    state.maintenance_state_revision = Arc::new(());
    state.history_baseline_plan = None;
    state.history_baseline_generation = None;
    state.bulk_init_proved = false;
    state.bulk_maint_proved = false;
    state.bulk_maint_capability = None;
    state.last_term_status = LastTermStatus::Pending;
}

/// Apply the optional-history failure policy at a stopped-work boundary.
pub fn settle_maintenance_history(state: &mut HoudiniState) -> Result<(), FailureReport> {
    if let Some(report) = state.maintenance_failure.clone() {
        return Err(report);
    }
    if !state.maintenance_policy.fail_on_history_log_error() {
        return Ok(());
    }
    if let Err(report) = state.artifacts.settle_maintenance_history() {
        state.record_execution_failure(report.clone());
        return Err(report);
    }
    Ok(())
}

// ------------------------------------------------------------
// Complete Houdini Orchestration
// ------------------------------------------------------------

/// Consume one prepared Active set and atomically expand Core with its
/// maintenance fixed point.
pub async fn houdini(
    task: &SynthesisTask,
    state: &mut HoudiniState,
    command: VampireWorkerCommand,
    cancellation: &CancellationToken,
) -> HoudiniExecutionOutcome {
    if let Some(report) = state.maintenance_failure.clone() {
        return HoudiniExecutionOutcome::Failed(report);
    }
    if cancellation.is_cancelled() {
        return HoudiniExecutionOutcome::Cancelled;
    }
    if state.active.is_empty() {
        return HoudiniExecutionOutcome::Complete;
    }

    state.bulk_maint_proved = false;
    state.bulk_maint_capability = None;
    if !state.verification.bulk_maint_limit().is_zero() {
        match bulk_maint_check(task, state, command.clone(), cancellation).await {
            BulkMaintenanceOutcome::Complete => {}
            BulkMaintenanceOutcome::Cancelled => return HoudiniExecutionOutcome::Cancelled,
            BulkMaintenanceOutcome::Failed(report) => {
                return HoudiniExecutionOutcome::Failed(report);
            }
        }
        if state.bulk_maint_proved {
            return match expand_core_from_bulk(state) {
                Ok(()) => HoudiniExecutionOutcome::Complete,
                Err(report) => HoudiniExecutionOutcome::Failed(report),
            };
        }
    }

    let stable = match run_maintenance_blocks(task, state, command, cancellation).await {
        MaintenanceExecutionOutcome::Complete(stable) => stable,
        MaintenanceExecutionOutcome::Cancelled => return HoudiniExecutionOutcome::Cancelled,
        MaintenanceExecutionOutcome::Failed(report) => {
            return HoudiniExecutionOutcome::Failed(report);
        }
    };
    match stable {
        Some(stable) => match expand_core_after_history_settlement(state, &stable) {
            Ok(()) => HoudiniExecutionOutcome::Complete,
            Err(report) => HoudiniExecutionOutcome::Failed(report),
        },
        None => HoudiniExecutionOutcome::Complete,
    }
}

/// Consume only the private capability minted by an exact successful bulk
/// check.  This path is intentionally separate from `MaintenanceBlockResult`.
fn expand_core_from_bulk(state: &mut HoudiniState) -> Result<(), FailureReport> {
    let valid = state.bulk_maint_proved
        && state
            .bulk_maint_capability
            .as_ref()
            .is_some_and(|capability| {
                capability.catalog_identity == state.catalog.identity()
                    && Arc::ptr_eq(
                        &capability.state_revision,
                        &state.maintenance_state_revision,
                    )
                    && state
                        .maintenance_plan
                        .as_ref()
                        .is_some_and(|plan| Arc::ptr_eq(&capability.plan, plan))
                    && capability.active.as_ref() == state.active.as_ref()
                    && is_exact_union(
                        capability.candidate.as_ref(),
                        state.core.as_ref(),
                        state.active.as_ref(),
                    )
                    && capability.evidence.is_none_or(|evidence| {
                        evidence.backend_id() == state.artifacts.backend_id()
                            && evidence.kind() == crate::ArtifactKind::RuntimeTrace
                            && state.artifacts.resolve(evidence).is_ok()
                    })
            });
    if !valid {
        let report = maintenance_invariant(
            "Core expansion requires the current exact bulk-maintenance capability",
        );
        state.record_execution_failure(report.clone());
        return Err(report);
    }
    let staged = match stage_core_expansion(state) {
        Ok(staged) => staged,
        Err(report) => {
            state.record_execution_failure(report.clone());
            return Err(report);
        }
    };
    commit_core_expansion(state, staged);
    Ok(())
}

// ------------------------------------------------------------
// Sequential Helpers
// ------------------------------------------------------------

struct ExclusionTransition {
    target: ClauseId,
    decrements: Vec<ClauseId>,
}

#[derive(Serialize)]
struct GenerationHistoryRecord {
    event: &'static str,
    generation: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    initial_core: Option<Vec<u64>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    initial_active: Option<Vec<u64>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    candidate: Option<Vec<u64>>,
    state: &'static str,
    #[serde(skip_serializing_if = "Option::is_none")]
    known_live: Option<Vec<u64>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    outcome: Option<&'static str>,
    #[serde(skip_serializing_if = "Option::is_none")]
    target: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    exclusion_applied: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    reason: Option<FailureHistoryRecord>,
    #[serde(skip_serializing_if = "Option::is_none")]
    baseline_generation: Option<u64>,
}

#[derive(Serialize)]
struct FailureHistoryRecord {
    origin: String,
    kind: String,
    retryable: bool,
    scope: String,
    detail: Option<String>,
    artifact_references: Vec<FailureArtifactHistoryRecord>,
}

impl From<&FailureReport> for FailureHistoryRecord {
    fn from(report: &FailureReport) -> Self {
        Self {
            origin: format!("{:?}", report.origin()),
            kind: format!("{:?}", report.kind()),
            retryable: report.retryable(),
            scope: format!("{:?}", report.scope()),
            detail: report.detail().map(str::to_owned),
            artifact_references: report
                .artifact_references()
                .iter()
                .copied()
                .map(FailureArtifactHistoryRecord::from)
                .collect(),
        }
    }
}

#[derive(Serialize)]
struct FailureArtifactHistoryRecord {
    backend: String,
    local_id: u64,
    kind: String,
}

impl From<crate::ArtifactRef> for FailureArtifactHistoryRecord {
    fn from(reference: crate::ArtifactRef) -> Self {
        Self {
            backend: reference.backend_id().to_string(),
            local_id: reference.local_id(),
            kind: format!("{:?}", reference.kind()),
        }
    }
}

#[derive(Serialize)]
struct ExclusionHistoryRecord {
    event: &'static str,
    generation: u64,
    target: u64,
}

fn validate_block_entry(
    task: &SynthesisTask,
    state: &HoudiniState,
) -> Result<Arc<MaintenancePlan>, FailureReport> {
    if state.active.is_empty() {
        return Err(maintenance_invariant(
            "a maintenance block requires nonempty Active",
        ));
    }
    if state.bulk_maint_proved {
        return Err(maintenance_invariant(
            "a per-clause maintenance block cannot follow a proved bulk check",
        ));
    }
    let plan = state.current_maintenance_plan(task)?;
    if state.present_support_count.len() != state.active.len()
        || state
            .active
            .iter()
            .any(|target| !state.present_support_count.contains_key(target))
    {
        return Err(maintenance_invariant(
            "present-support counts do not cover current Active",
        ));
    }
    Ok(plan)
}

fn apply_late_shortcut(
    state: &HoudiniState,
    plan: &MaintenancePlan,
    generation: GenerationId,
    known_live: &mut ClauseSet,
    target: ClauseId,
) -> Result<(), FailureReport> {
    let shortcut = if state.has_present_support(target) {
        Some(MaintenanceShortcut::Support)
    } else if state.find_live_cover(plan, known_live, target)?.is_some() {
        Some(MaintenanceShortcut::Coverage)
    } else {
        None
    };
    if let Some(shortcut) = shortcut {
        state.catalog.close_maintenance_retry(target)?;
        if known_live.insert(target) {
            record_maintenance_shortcut(
                &state.telemetry,
                generation,
                target,
                shortcut,
                "late_result",
            );
        }
    }
    Ok(())
}

fn append_generation_history(
    state: &mut HoudiniState,
    result: &MaintenanceBlockResult,
) -> Result<(), FailureReport> {
    if !state.maintenance_policy.log_maintenance_history() {
        return Ok(());
    }
    let emit_baseline = !state
        .history_baseline_plan
        .as_ref()
        .is_some_and(|plan| Arc::ptr_eq(plan, &result.plan));
    let record = GenerationHistoryRecord {
        event: "maintenance_generation_state",
        generation: result.generation.get(),
        initial_core: emit_baseline.then(|| sorted_clause_values(result.plan.core())),
        initial_active: emit_baseline.then(|| sorted_clause_values(result.plan.initial_active())),
        candidate: emit_baseline.then(|| sorted_clause_values(result.candidate.as_ref())),
        state: "closed",
        known_live: Some(sorted_clause_values(result.known_live.as_ref())),
        outcome: Some(result.outcome.history_kind()),
        target: result.outcome.target().map(ClauseId::get),
        exclusion_applied: Some(false),
        reason: None,
        baseline_generation: None,
    };
    let bytes = serde_json::to_vec(&record).map_err(|error| {
        FailureReport::maintenance_history(
            FailureScope::LaneLocal,
            format!("serialize maintenance-generation history: {error}"),
        )
    })?;
    history_artifacts(state, result.generation).append_maintenance_history(&bytes)?;
    if emit_baseline {
        state.history_baseline_plan = Some(Arc::clone(&result.plan));
    }
    Ok(())
}

fn sorted_clause_values(clauses: &ClauseSet) -> Vec<u64> {
    let mut values = clauses.iter().map(|id| id.get()).collect::<Vec<_>>();
    values.sort_unstable();
    values
}

fn append_exclusion_history(
    state: &HoudiniState,
    result: &MaintenanceBlockResult,
) -> Result<(), FailureReport> {
    if !state.maintenance_policy.log_maintenance_history() {
        return Ok(());
    }
    let target = result
        .outcome
        .target()
        .expect("only nonstable results drive exclusions");
    let bytes = serde_json::to_vec(&ExclusionHistoryRecord {
        event: "maintenance_exclusion_applied",
        generation: result.generation.get(),
        target: target.get(),
    })
    .map_err(|error| {
        FailureReport::maintenance_history(
            FailureScope::LaneLocal,
            format!("serialize maintenance-exclusion history: {error}"),
        )
    })?;
    history_artifacts(state, result.generation).append_maintenance_history(&bytes)
}

fn history_artifacts(state: &HoudiniState, generation: GenerationId) -> crate::ArtifactStore {
    state
        .artifacts
        .scoped(ScopeTag::Houdini)
        .scoped(ScopeTag::named(format!(
            "houdini-run:{}",
            state.houdini_run_id
        )))
        .scoped(ScopeTag::Generation(generation.get()))
}

fn complete_block(
    state: &mut HoudiniState,
    plan: Arc<MaintenancePlan>,
    generation: GenerationId,
    entry_active: Arc<ClauseSet>,
    candidate: Arc<ClauseSet>,
    known_live: ClauseSet,
    outcome: MaintenanceBlockOutcome,
) -> MaintenanceExecutionOutcome<MaintenanceBlockResult> {
    let result = MaintenanceBlockResult::new(
        state.catalog.identity(),
        plan,
        Arc::clone(&state.maintenance_state_revision),
        generation,
        entry_active,
        candidate,
        known_live,
        outcome,
    );
    if let Err(report) = append_generation_history(state, &result) {
        return fail_execution(state, report);
    }
    MaintenanceExecutionOutcome::Complete(result)
}

fn stage_exclusion(
    state: &HoudiniState,
    result: &MaintenanceBlockResult,
) -> Result<ExclusionTransition, FailureReport> {
    let Some(target) = result.outcome.target() else {
        return Err(maintenance_invariant(
            "a stable block result cannot drive exclusion",
        ));
    };
    if state.maintenance_failure.is_some()
        || result.catalog_identity != state.catalog.identity()
        || !Arc::ptr_eq(&result.state_revision, &state.maintenance_state_revision)
        || state.active.as_ref() != result.entry_active.as_ref()
        || !state.active.contains(&target)
        || result.known_live.contains(&target)
        || !is_exact_union(
            result.candidate.as_ref(),
            state.core.as_ref(),
            state.active.as_ref(),
        )
    {
        return Err(maintenance_invariant(
            "maintenance exclusion result does not match current state",
        ));
    }
    let plan = state
        .maintenance_plan
        .as_ref()
        .ok_or_else(|| maintenance_invariant("maintenance exclusion requires a current plan"))?;
    if !Arc::ptr_eq(&result.plan, plan)
        || !state.active.is_subset(plan.initial_active())
        || plan.core() != state.core.as_ref()
    {
        return Err(maintenance_invariant(
            "maintenance exclusion plan does not match current Core and Active",
        ));
    }

    let mut decrements = Vec::new();
    for affected in plan.supported_targets_by(target).iter().copied() {
        if affected != target && state.active.contains(&affected) {
            let Some(count) = state.present_support_count.get(&affected) else {
                return Err(maintenance_invariant(format!(
                    "clause {} lacks a present-support count",
                    affected.get()
                )));
            };
            if *count == 0 {
                return Err(maintenance_invariant(format!(
                    "present-support count for clause {} would underflow",
                    affected.get()
                )));
            }
            decrements.push(affected);
        }
    }
    if !state.present_support_count.contains_key(&target) {
        return Err(maintenance_invariant(format!(
            "excluded clause {} lacks a present-support count",
            target.get()
        )));
    }
    Ok(ExclusionTransition { target, decrements })
}

fn stage_core_expansion(state: &HoudiniState) -> Result<ClauseSet, FailureReport> {
    if state.maintenance_failure.is_some()
        || state.active.is_empty()
        || !state.active.is_disjoint(state.core.as_ref())
    {
        return Err(maintenance_invariant(
            "Core expansion requires nonempty disjoint stable Active",
        ));
    }
    let proved = state
        .catalog
        .select_init_proved(state.active.as_ref())
        .map_err(maintenance_context_failure)?;
    if proved != *state.active {
        let mut offenders = state
            .active
            .difference(&proved)
            .map(|id| id.get())
            .collect::<Vec<_>>();
        offenders.sort_unstable();
        return Err(maintenance_invariant(format!(
            "Core expansion rejected non-InitProved Active clauses {offenders:?}"
        )));
    }
    let mut staged = state.core.as_ref().clone();
    staged.try_reserve(state.active.len()).map_err(|_| {
        FailureReport::try_new(
            FailureOrigin::MaintenanceExecution,
            FailureKind::InfrastructureFailure,
            false,
            FailureScope::LaneLocal,
            Some("could not reserve Core expansion capacity".to_string()),
            Vec::new(),
        )
        .expect("maintenance allocation failure uses a permitted pair")
    })?;
    staged.extend(state.active.iter().copied());
    Ok(staged)
}

fn union(left: &ClauseSet, right: &ClauseSet) -> ClauseSet {
    let mut result = ClauseSet::with_capacity(left.len().saturating_add(right.len()));
    result.extend(left.iter().copied());
    result.extend(right.iter().copied());
    result
}

fn is_exact_union(candidate: &ClauseSet, left: &ClauseSet, right: &ClauseSet) -> bool {
    candidate.len() == left.len().saturating_add(right.len())
        && left.is_subset(candidate)
        && right.is_subset(candidate)
}

fn fail_execution<T>(
    state: &mut HoudiniState,
    report: FailureReport,
) -> MaintenanceExecutionOutcome<T> {
    state.record_execution_failure(report.clone());
    MaintenanceExecutionOutcome::Failed(report)
}

fn maintenance_context_failure(report: FailureReport) -> FailureReport {
    if report.scope() == FailureScope::RunGlobal
        || report.origin() == FailureOrigin::MaintenanceExecution
        || is_required_artifact_failure(&report)
    {
        return report;
    }
    let kind = if report.kind() == FailureKind::StateInvariantViolation {
        FailureKind::StateInvariantViolation
    } else {
        FailureKind::InfrastructureFailure
    };
    FailureReport::try_new(
        FailureOrigin::MaintenanceExecution,
        kind,
        false,
        report.scope(),
        Some(format!(
            "maintenance state boundary: {}",
            report.detail().unwrap_or("unspecified failure")
        )),
        report.artifact_references().to_vec(),
    )
    .expect("maintenance context conversion uses a permitted pair")
}

fn maintenance_global_failure(detail: impl Into<String>) -> FailureReport {
    FailureReport::try_new(
        FailureOrigin::MaintenanceExecution,
        FailureKind::InfrastructureFailure,
        false,
        FailureScope::RunGlobal,
        Some(detail.into()),
        Vec::new(),
    )
    .expect("maintenance global failure uses a permitted classification")
}

fn is_required_artifact_failure(report: &FailureReport) -> bool {
    report.kind() == FailureKind::PublicationFailure
        || report.origin() == FailureOrigin::ArtifactSettlement
}

fn is_fatal_target_failure(report: &FailureReport) -> bool {
    if report.scope() == FailureScope::RunGlobal || is_required_artifact_failure(report) {
        return true;
    }
    !matches!(
        (report.origin(), report.kind()),
        (
            FailureOrigin::EncodingPreparation,
            FailureKind::MalformedResult
                | FailureKind::ProcessFailure
                | FailureKind::InfrastructureFailure
        ) | (
            FailureOrigin::VampireProofSearch | FailureOrigin::VampireFiniteModelBuilding,
            FailureKind::SolverUnknown
                | FailureKind::MalformedResult
                | FailureKind::ProcessFailure
                | FailureKind::InfrastructureFailure
        ) | (
            FailureOrigin::VampireRace,
            FailureKind::ConcurrentWorkerFailures
        ) | (
            FailureOrigin::ModelDecoding,
            FailureKind::UnsupportedCheck
                | FailureKind::CheckTimeout
                | FailureKind::MalformedResult
                | FailureKind::ProcessFailure
                | FailureKind::InfrastructureFailure
        )
    )
}

fn fatal_cancelled_peer(cancelled: &CancelledEntailmentCheck) -> Option<FailureReport> {
    match cancelled {
        CancelledEntailmentCheck::Vampire(cancelled) => cancelled
            .peer_failure()
            .filter(|report| is_fatal_target_failure(report))
            .cloned(),
        CancelledEntailmentCheck::EmptyCheck { .. } => None,
    }
}

impl HoudiniState {
    fn allocate_generation(&mut self) -> Result<GenerationId, FailureReport> {
        allocate_generation(&mut self.next_generation_ordinal)
    }

    fn record_execution_failure(&mut self, report: FailureReport) {
        if self.maintenance_failure.is_none() {
            self.maintenance_failure = Some(report);
        }
    }

    /// Find one coverage witness visible in this block, if one exists.
    fn find_live_cover(
        &self,
        plan: &MaintenancePlan,
        known_live: &ClauseSet,
        target: ClauseId,
    ) -> Result<Option<ClauseId>, FailureReport> {
        let current = self.maintenance_plan.as_ref().ok_or_else(|| {
            maintenance_invariant("live-cover lookup requires a current maintenance plan")
        })?;
        if !std::ptr::eq(current.as_ref(), plan) || !self.active.contains(&target) {
            return Err(maintenance_invariant(
                "live-cover lookup does not match the current block",
            ));
        }

        if let Some(source) = plan.find_literal_subset_cover(known_live, target) {
            return Ok(Some(source));
        }

        // Explicit caller-supplied coverage remains the common fallback.
        Ok(plan
            .covered_by(target)
            .iter()
            .copied()
            .find(|source| plan.core().contains(source) || known_live.contains(source)))
    }
}

fn allocate_generation(next: &mut Option<u64>) -> Result<GenerationId, FailureReport> {
    let ordinal = next.take().ok_or_else(|| {
        maintenance_invariant("maintenance generation identity space is exhausted")
    })?;
    *next = ordinal.checked_add(1);
    Ok(GenerationId(ordinal))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn proof_support_extraction_is_strict_and_positional() {
        let ids = [ClauseId::test(3), ClauseId::test(7), ClauseId::test(9)];
        let candidate = CandidateSnapshot::from_sorted(ids.to_vec());
        let proof = "\
fof(f1, axiom, p, file('/tmp/q.p', axiom_0)).
fof(f2, axiom, g, file('/tmp/q.p', axiom_3)).
fof(f3, axiom, d, file('/tmp/q.p', support_adom)).
fof(f4, axiom, r, file('/tmp/q.p', axiom_2)).
fof(f5, plain, x, inference(resolution, [], [f1, f4])).";
        let support = proof_support_premises(proof, &candidate).unwrap();
        let mut cited = support.iter().copied().collect::<Vec<_>>();
        cited.sort_unstable();
        assert_eq!(cited, vec![ids[0], ids[2]]);

        // An input index beyond the guard position is unknown.
        let beyond = "fof(f1, axiom, p, file('/tmp/q.p', axiom_4)).";
        assert!(proof_support_premises(beyond, &candidate).is_none());

        // Unknown input names disable support recording.
        let unknown = "fof(f1, axiom, p, file('/tmp/q.p', lemma_1)).";
        assert!(proof_support_premises(unknown, &candidate).is_none());

        // A proof citing no inputs records no support.
        assert!(proof_support_premises("fof(f1, plain, x).", &candidate).is_none());

        // Citing only the guard yields an empty (always-intact) set.
        let guard_only = "fof(f1, axiom, g, file('/tmp/q.p', axiom_3)).";
        let empty = proof_support_premises(guard_only, &candidate).unwrap();
        assert!(empty.is_empty());
    }
    use crate::artifact::{ArtifactKind, ArtifactStoreConfig, new_artifact_store};
    use crate::encoding::{
        EncodingWorkerCommand, EncodingWorkerPoolConfig, QfSolverSource, SolverBodySource,
        new_solver_encoding_context,
    };
    use crate::houdini::catalog::{ClauseCatalog, ClauseFormula, InitializationStatus};
    use crate::houdini::maintenance::MaintenancePlan;
    use crate::runtime::{RuntimeResourcePolicy, create_general_solver_admission};
    use crate::task::SynthesisTask;
    use std::fs;
    use std::time::Duration;
    use std::time::{SystemTime, UNIX_EPOCH};

    #[tokio::test]
    async fn resolution_watch_retains_a_publication_before_the_wait_is_polled() {
        let (publisher, _) = watch::channel(0_u64);
        let mut observer = publisher.subscribe();

        publisher.send_modify(|version| *version = version.wrapping_add(1));

        tokio::time::timeout(Duration::from_millis(100), observer.changed())
            .await
            .expect("a pre-poll resolution publication must not be lost")
            .expect("the resolution publisher remains live");
        assert_eq!(*observer.borrow_and_update(), 1);
    }

    #[test]
    fn exact_union_rejects_overlap_and_missing_members() {
        let a = ClauseId::test(0);
        let b = ClauseId::test(1);
        assert!(is_exact_union(
            &ClauseSet::from([a, b]),
            &ClauseSet::from([a]),
            &ClauseSet::from([b]),
        ));
        assert!(!is_exact_union(
            &ClauseSet::from([a]),
            &ClauseSet::from([a]),
            &ClauseSet::from([a]),
        ));
    }

    #[test]
    fn block_outcome_exposes_only_nonstable_targets() {
        let target = ClauseId::test(7);
        assert_eq!(MaintenanceBlockOutcome::Stable.target(), None);
        assert_eq!(
            MaintenanceBlockOutcome::RetryExhausted(target).target(),
            Some(target)
        );
    }

    #[test]
    fn generation_boundary_allocates_max_once_then_stays_exhausted() {
        let mut next = Some(u64::MAX);

        assert_eq!(allocate_generation(&mut next).unwrap().get(), u64::MAX);
        assert!(next.is_none());
        assert!(allocate_generation(&mut next).is_err());
        assert!(allocate_generation(&mut next).is_err());
    }

    #[test]
    fn run_global_failure_replaces_lane_local_failure_and_cannot_be_downgraded() {
        let lane = FailureReport::try_new(
            FailureOrigin::MaintenanceExecution,
            FailureKind::InfrastructureFailure,
            false,
            FailureScope::LaneLocal,
            Some("lane".to_string()),
            Vec::new(),
        )
        .unwrap();
        let global = maintenance_global_failure("global");
        let later_lane = FailureReport::try_new(
            FailureOrigin::MaintenanceExecution,
            FailureKind::InfrastructureFailure,
            false,
            FailureScope::LaneLocal,
            Some("later lane".to_string()),
            Vec::new(),
        )
        .unwrap();
        let mut selected = None;

        retain_dominant_failure(&mut selected, lane);
        assert_eq!(selected.as_ref().unwrap().scope(), FailureScope::LaneLocal);
        retain_dominant_failure(&mut selected, global);
        assert_eq!(selected.as_ref().unwrap().scope(), FailureScope::RunGlobal);
        retain_dominant_failure(&mut selected, later_lane);
        assert_eq!(selected.as_ref().unwrap().scope(), FailureScope::RunGlobal);
        assert_eq!(selected.as_ref().unwrap().detail(), Some("global"));
    }

    #[test]
    fn missing_terminal_artifact_preserves_primary_failure_before_commit() {
        let primary = FailureReport::try_new(
            FailureOrigin::EncodingPreparation,
            FailureKind::PublicationFailure,
            false,
            FailureScope::LaneLocal,
            Some("terminal publication failed".to_string()),
            Vec::new(),
        )
        .unwrap();
        let outcome = EntailmentInvocationOutcome::Result(EntailmentCheckResult::Failure {
            report: primary,
            next_fmb_start_size: None,
        });

        let retained = missing_terminal_artifact_failure(None, &outcome).unwrap();

        assert_eq!(retained.origin(), FailureOrigin::EncodingPreparation);
        assert_eq!(retained.kind(), FailureKind::PublicationFailure);
        assert_eq!(retained.scope(), FailureScope::LaneLocal);
        assert_eq!(retained.detail(), Some("terminal publication failed"));
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[tokio::test]
    async fn core_expansion_resets_nonpending_termination_status() {
        let task = test_task();
        let root = std::env::temp_dir().join(format!(
            "whiel_phase3c_term_reset_{}_{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let (owner, artifacts) =
            new_artifact_store(&task, ArtifactStoreConfig::new(&root)).unwrap();
        let workers = EncodingWorkerPoolConfig::new(
            EncodingWorkerCommand::new("/bin/false", env!("CARGO_MANIFEST_DIR")),
            1,
        )
        .unwrap();
        let context = new_solver_encoding_context(&task, &artifacts, workers).unwrap();
        let resources = RuntimeResourcePolicy::agent_only(2, 2).unwrap();
        let verification = super::super::initialization::VerificationParameters::new(
            Duration::from_secs(1),
            resources,
        )
        .unwrap();
        let catalog = ClauseCatalog::new(&task, context.clone(), &artifacts).unwrap();
        let mut state = HoudiniState::new(
            &task,
            verification,
            create_general_solver_admission(resources).unwrap(),
            catalog,
        )
        .unwrap();
        assert!(matches!(state.last_term_status(), LastTermStatus::Pending));
        let source = SolverBodySource::QuantifierFree(
            QfSolverSource::new(&task, "phase3c.term-reset", [], []).unwrap(),
        );
        let clause = state
            .catalog
            .register_proposed_clause(
                ClauseFormula::from_trusted_lean_source("phase3c.term-reset", source).unwrap(),
            )
            .unwrap();
        let evidence = state
            .catalog
            .artifacts()
            .publish(
                ArtifactKind::InitializationCheck,
                b"phase3c term-reset fixture".as_slice().into(),
            )
            .unwrap();
        state
            .catalog
            .record_initialization(clause, InitializationStatus::InitProved, evidence)
            .unwrap();
        state.init_candidates = Arc::new(ClauseSet::from([clause]));
        state.active = Arc::new(ClauseSet::from([clause]));
        state.candidate_snapshot = Some(CandidateSnapshot::root(Arc::clone(&state.active)));
        Arc::get_mut(&mut state.present_support_count)
            .unwrap()
            .insert(clause, 0);
        let plan = MaintenancePlan::for_core_expansion_test(&task, &state);
        state.maintenance_plan = Some(Arc::clone(&plan));
        state.last_term_status = LastTermStatus::Proved;
        let stable = MaintenanceBlockResult::new(
            state.catalog.identity(),
            plan,
            Arc::clone(&state.maintenance_state_revision),
            GenerationId(0),
            Arc::clone(&state.active),
            Arc::clone(&state.active),
            state.active.as_ref().clone(),
            MaintenanceBlockOutcome::Stable,
        );

        expand_core(&mut state, &stable).unwrap();

        assert_eq!(state.core(), &ClauseSet::from([clause]));
        assert!(matches!(state.last_term_status(), LastTermStatus::Pending));

        context.shutdown().await.unwrap();
        drop(state);
        drop(context);
        drop(artifacts);
        owner.settle().unwrap();
        fs::remove_dir_all(root).unwrap();
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[tokio::test]
    async fn stale_bulk_capability_cannot_expand_core() {
        let task = test_task();
        let root = std::env::temp_dir().join(format!(
            "whiel_phase3e_stale_bulk_{}_{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let (owner, artifacts) =
            new_artifact_store(&task, ArtifactStoreConfig::new(&root)).unwrap();
        let workers = EncodingWorkerPoolConfig::new(
            EncodingWorkerCommand::new("/bin/false", env!("CARGO_MANIFEST_DIR")),
            1,
        )
        .unwrap();
        let context = new_solver_encoding_context(&task, &artifacts, workers).unwrap();
        let resources = RuntimeResourcePolicy::agent_only(2, 2).unwrap();
        let verification = super::super::initialization::VerificationParameters::new(
            Duration::from_secs(1),
            resources,
        )
        .unwrap();
        let catalog = ClauseCatalog::new(&task, context.clone(), &artifacts).unwrap();
        let mut state = HoudiniState::new(
            &task,
            verification,
            create_general_solver_admission(resources).unwrap(),
            catalog,
        )
        .unwrap();
        let source = SolverBodySource::QuantifierFree(
            QfSolverSource::new(&task, "phase3e.stale-bulk", [], []).unwrap(),
        );
        let clause = state
            .catalog
            .register_proposed_clause(
                ClauseFormula::from_trusted_lean_source("phase3e.stale-bulk", source).unwrap(),
            )
            .unwrap();
        let evidence = state
            .catalog
            .artifacts()
            .publish(
                ArtifactKind::InitializationCheck,
                b"phase3e stale bulk fixture".as_slice().into(),
            )
            .unwrap();
        state
            .catalog
            .record_initialization(clause, InitializationStatus::InitProved, evidence)
            .unwrap();
        state.init_candidates = Arc::new(ClauseSet::from([clause]));
        state.active = Arc::new(ClauseSet::from([clause]));
        state.candidate_snapshot = Some(CandidateSnapshot::root(Arc::clone(&state.active)));
        Arc::get_mut(&mut state.present_support_count)
            .unwrap()
            .insert(clause, 1);
        let plan = MaintenancePlan::for_core_expansion_test(&task, &state);
        state.maintenance_plan = Some(Arc::clone(&plan));
        state.bulk_maint_proved = true;
        state.bulk_maint_capability = Some(super::super::bulk::BulkMaintenanceCapability {
            catalog_identity: state.catalog.identity(),
            plan,
            state_revision: Arc::new(()),
            active: Arc::clone(&state.active),
            candidate: Arc::clone(&state.active),
            evidence: None,
        });

        let error = expand_core_from_bulk(&mut state).unwrap_err();

        assert_eq!(error.origin(), FailureOrigin::MaintenanceExecution);
        assert_eq!(error.kind(), FailureKind::StateInvariantViolation);
        assert!(state.core().is_empty());
        assert_eq!(state.active(), &ClauseSet::from([clause]));

        context.shutdown().await.unwrap();
        drop(state);
        drop(context);
        drop(artifacts);
        owner.settle().unwrap();
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn retry_allowance_resets_for_stronger_and_incomparable_candidates() {
        let prior = CandidateSnapshot::root(Arc::new(ClauseSet::from([ClauseId::test(0)])));
        let stronger = CandidateSnapshot::root(Arc::new(ClauseSet::from([
            ClauseId::test(0),
            ClauseId::test(1),
        ])));
        let incomparable = CandidateSnapshot::root(Arc::new(ClauseSet::from([ClauseId::test(2)])));
        let base = Duration::from_secs(5);
        let increments = [base, base];

        assert_eq!(
            super::super::catalog::maintenance_retry_allowance(
                Some(&prior),
                1,
                true,
                base,
                &increments,
                &stronger,
            ),
            Ok(Some(base))
        );
        assert_eq!(
            super::super::catalog::maintenance_retry_allowance(
                Some(&prior),
                1,
                true,
                base,
                &increments,
                &incomparable,
            ),
            Ok(Some(base))
        );
    }

    fn test_task() -> SynthesisTask {
        SynthesisTask::from_json(
            r#"{
              "format_version": 3,
              "semantic_version": 1,
              "encoding_version": 1,
              "identity": {
                "canonical_id": "Phase3CTermReset",
                "module": "Whiel.Tests.Phase3CTermReset",
                "namespace": "Whiel.Tests.Phase3CTermReset",
                "source_sha256": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
              },
              "schema": {"expression":"Whiel.Tests.Phase3CTermReset.programSchema","display":"{}"},
              "original": {
                "pre":{"expression":"Whiel.Tests.Phase3CTermReset.inputPre","display":"true"},
                "command":{"expression":"Whiel.Tests.Phase3CTermReset.inputCmd","display":"SKIP"},
                "post":{"expression":"Whiel.Tests.Phase3CTermReset.inputPost","display":"true"}
              },
              "preprocessed": {
                "pre":{"expression":"Whiel.Tests.Phase3CTermReset.inputPreproc.loopPre","display":"true"},
                "command":{"expression":"Whiel.Tests.Phase3CTermReset.inputPreproc.loopCmd","display":"WHILE true DO SKIP END"},
                "post":{"expression":"Whiel.Tests.Phase3CTermReset.inputPreproc.loopPost","display":"true"}
              },
              "preprocessing_evidence":{"expression":"Whiel.Tests.Phase3CTermReset.inputPreproc"},
              "solver": {
                "schema_relations": [],
                "task_constants": [],
                "preprocessed_pre": {
                  "source_id":"task.preprocessed_pre",
                  "expression":"Whiel.Tests.Phase3CTermReset.inputPreproc.loopPre",
                  "no_bound_expression":"Whiel.Tests.Phase3CTermReset.inputPreproc.loopPre_noBound",
                  "constants":[],
                  "relations":[]
                },
                "preprocessed_post": {
                  "source_id":"task.preprocessed_post",
                  "expression":"Whiel.Tests.Phase3CTermReset.inputPreproc.loopPost",
                  "no_bound_expression":"Whiel.Tests.Phase3CTermReset.inputPreproc.loopPost_noBound",
                  "constants":[],
                  "relations":[]
                },
                "loop_guard": {
                  "source_id":"task.loop_guard",
                  "constants":[],
                  "relations":[]
                },
                "negated_loop_guard": {
                  "source_id":"task.negated_loop_guard",
                  "constants":[],
                  "relations":[]
                }
              }
            }"#,
        )
        .unwrap()
    }
}
