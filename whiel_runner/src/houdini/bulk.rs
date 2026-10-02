//! One exact-Candidate bulk maintenance shortcut.
//!
//! A successful bulk query creates a private capability bound to the current
//! plan and maintenance-state revision.  Core expansion consumes that
//! capability through a separate path; it never fabricates or weakens the
//! per-clause `MaintenanceBlockResult` guard.

use std::sync::Arc;

use serde_json::json;

use crate::artifact::ScopeTag;
use crate::encoding::EncodingError;
use crate::entailment::{
    EntailmentCheckResult, EntailmentInvocationOutcome, assemble_entailment,
    check_entailment_detailed,
};
use crate::failure::{FailureKind, FailureOrigin, FailureReport, FailureScope};
use crate::runtime::{AdmissionError, CancellationToken, CpuJobError};
use crate::task::SynthesisTask;
use crate::vampire::{FmbOptions, VampireMode, VampireWorkerCommand};

use super::catalog::{ClauseId, ClauseSet, MaintenanceSnapshotError};
use super::initialization::HoudiniState;
use super::maintenance::{MaintenancePlan, maintenance_invariant};

#[derive(Clone, Debug)]
pub(super) struct BulkMaintenanceCapability {
    pub(super) catalog_identity: u64,
    pub(super) plan: Arc<MaintenancePlan>,
    pub(super) state_revision: Arc<()>,
    pub(super) active: Arc<ClauseSet>,
    pub(super) candidate: Arc<ClauseSet>,
    pub(super) evidence: Option<crate::ArtifactRef>,
}

/// Runtime control around one optional bulk shortcut.
#[must_use]
#[derive(Clone, Debug)]
pub enum BulkMaintenanceOutcome {
    Complete,
    Cancelled,
    Failed(FailureReport),
}

#[derive(Debug)]
struct BulkSelection {
    plan: Arc<MaintenancePlan>,
    active: Arc<ClauseSet>,
    candidate: Arc<ClauseSet>,
    unsupported: Vec<ClauseId>,
}

#[derive(Debug)]
struct BulkQuerySetup {
    axioms: Arc<[crate::encoding::PreparedBodyRef]>,
    goals: Vec<crate::encoding::PreparedBodyRef>,
}

#[derive(Debug)]
enum BulkPreparationError {
    Cancelled,
    Failure(FailureReport),
}

/// Prove every unsupported Active target under the exact Candidate at once.
pub async fn bulk_maint_check(
    task: &SynthesisTask,
    state: &mut HoudiniState,
    command: VampireWorkerCommand,
    cancellation: &CancellationToken,
) -> BulkMaintenanceOutcome {
    state.bulk_maint_proved = false;
    state.bulk_maint_capability = None;
    if let Some(report) = state.maintenance_failure.clone() {
        return BulkMaintenanceOutcome::Failed(report);
    }
    if cancellation.is_cancelled() {
        return BulkMaintenanceOutcome::Cancelled;
    }
    if state.active.is_empty() || state.verification.bulk_maint_limit().is_zero() {
        return fail_bulk(
            state,
            maintenance_invariant("bulk maintenance requires nonempty Active and a positive limit"),
        );
    }
    let selection = match prepare_bulk_selection(task, state, cancellation).await {
        Ok(selection) => selection,
        Err(BulkPreparationError::Cancelled) => return BulkMaintenanceOutcome::Cancelled,
        Err(BulkPreparationError::Failure(report)) => return fail_bulk(state, report),
    };

    if selection.unsupported.is_empty() {
        if let Err(report) = append_bulk_history(state, "proved_by_support", None) {
            return fail_bulk(state, report);
        }
        if let Err(report) = settle_bulk_history(state).await {
            return fail_bulk(state, report);
        }
        publish_bulk_success(
            state,
            selection.plan,
            selection.active,
            selection.candidate,
            None,
        );
        return BulkMaintenanceOutcome::Complete;
    }

    let guard = match state
        .catalog
        .encoding_context()
        .prepare_loop_guard_body(&state.admission, &state.artifacts, cancellation)
        .await
    {
        Ok(guard) => guard,
        Err(EncodingError::Cancelled) => return BulkMaintenanceOutcome::Cancelled,
        Err(EncodingError::Failure(report)) => return fail_bulk(state, report),
    };
    let query = match prepare_bulk_query(state, &selection, guard, cancellation).await {
        Ok(query) => query,
        Err(BulkPreparationError::Cancelled) => return BulkMaintenanceOutcome::Cancelled,
        Err(BulkPreparationError::Failure(report)) => return fail_bulk(state, report),
    };
    let artifacts = state
        .artifacts
        .scoped(ScopeTag::Houdini)
        .scoped(ScopeTag::named(format!(
            "houdini-run:{}",
            state.houdini_run_id
        )))
        .scoped(ScopeTag::verification_stage("bulk-maintenance"));
    let entailment = match assemble_entailment(
        state.catalog.encoding_context(),
        &state.admission,
        &artifacts,
        query.axioms,
        query.goals,
        cancellation,
    )
    .await
    {
        Ok(entailment) => entailment,
        Err(EncodingError::Cancelled) => return BulkMaintenanceOutcome::Cancelled,
        Err(EncodingError::Failure(report)) => return fail_bulk(state, report),
    };
    let checked = check_entailment_detailed(
        &entailment,
        &artifacts,
        Some(state.verification.bulk_maint_limit()),
        VampireMode::ProofAndFmb(FmbOptions::default()),
        command,
        state.admission.clone(),
        cancellation.clone(),
    )
    .await;
    let evidence = checked.terminal_artifact();
    if evidence.is_none() {
        let report = missing_bulk_evidence(checked.outcome());
        return fail_bulk(state, report);
    }
    let (class, proved) = match checked.outcome() {
        EntailmentInvocationOutcome::Result(EntailmentCheckResult::Proved { .. }) => {
            ("proved", true)
        }
        EntailmentInvocationOutcome::Result(EntailmentCheckResult::Refuted(_)) => {
            ("refuted", false)
        }
        EntailmentInvocationOutcome::Result(EntailmentCheckResult::TimedOut { .. }) => {
            ("timed_out", false)
        }
        EntailmentInvocationOutcome::Result(EntailmentCheckResult::Failure { .. }) => {
            ("failure", false)
        }
        EntailmentInvocationOutcome::Cancelled(_) => return BulkMaintenanceOutcome::Cancelled,
        EntailmentInvocationOutcome::RunFailure(report) => {
            return fail_bulk(state, report.clone());
        }
    };
    if let Err(report) = append_bulk_history(state, class, evidence) {
        return fail_bulk(state, report);
    }
    if let Err(report) = settle_bulk_history(state).await {
        return fail_bulk(state, report);
    }
    if proved {
        publish_bulk_success(
            state,
            selection.plan,
            selection.active,
            selection.candidate,
            evidence,
        );
    }
    BulkMaintenanceOutcome::Complete
}

async fn prepare_bulk_selection(
    task: &SynthesisTask,
    state: &HoudiniState,
    cancellation: &CancellationToken,
) -> Result<BulkSelection, BulkPreparationError> {
    let plan = state.maintenance_plan.as_ref().cloned().ok_or_else(|| {
        BulkPreparationError::Failure(maintenance_invariant(
            "no maintenance plan is currently published",
        ))
    })?;
    let context = state.catalog.encoding_context().clone();
    let task_identity = task.identity().clone();
    let catalog_identity = state.catalog.identity();
    let encoding_context_id = Arc::<str>::from(context.context_id());
    let proposal_generation = state.proposal_generation;
    let core = Arc::clone(&state.core);
    let init_candidates = Arc::clone(&state.init_candidates);
    let active = Arc::clone(&state.active);
    let support_counts = Arc::clone(&state.present_support_count);
    let policy = state.maintenance_policy.clone();
    let candidate_snapshot = state.candidate_snapshot.as_ref().cloned();
    let built = context
        .run_cpu_job(&state.admission, cancellation, move |job_cancellation| {
            if job_cancellation.is_cancelled() {
                return Err(CpuJobError::Cancelled);
            }
            if active.is_empty()
                || !plan.matches_runtime_capture(
                    &task_identity,
                    catalog_identity,
                    &encoding_context_id,
                    proposal_generation,
                    &core,
                    &init_candidates,
                    &policy,
                )
                || !active.is_subset(plan.initial_active())
                || support_counts.len() != active.len()
                || active
                    .iter()
                    .any(|target| !support_counts.contains_key(target))
            {
                return Err(CpuJobError::Failure(maintenance_invariant(
                    "bulk maintenance entry state is stale or incomplete",
                )));
            }
            let exact_active = Arc::new(active.as_ref().clone());
            let candidate = Arc::new(exact_union(core.as_ref(), exact_active.as_ref()));
            match candidate_snapshot {
                Some(snapshot) if snapshot.equals_set(candidate.as_ref()) => {}
                _ => {
                    return Err(CpuJobError::Failure(maintenance_invariant(
                        "bulk maintenance Candidate snapshot does not match Core and Active",
                    )));
                }
            }
            let mut unsupported = Vec::with_capacity(exact_active.len());
            for (position, target) in exact_active.iter().copied().enumerate() {
                if position % 1024 == 0 && job_cancellation.is_cancelled() {
                    return Err(CpuJobError::Cancelled);
                }
                if support_counts.get(&target).copied().unwrap_or(0) == 0 {
                    unsupported.push(target);
                }
            }
            unsupported.sort_unstable();
            Ok(BulkSelection {
                plan,
                active: exact_active,
                candidate,
                unsupported,
            })
        })
        .await;
    map_bulk_cpu_job(built, "bulk maintenance selection")
}

async fn prepare_bulk_query(
    state: &HoudiniState,
    selection: &BulkSelection,
    guard: crate::encoding::PreparedBodyRef,
    cancellation: &CancellationToken,
) -> Result<BulkQuerySetup, BulkPreparationError> {
    let context = state.catalog.encoding_context().clone();
    let catalog = state.catalog.clone();
    let candidate = Arc::clone(&selection.candidate);
    let active = Arc::clone(&selection.active);
    let unsupported = selection.unsupported.clone();
    let built = context
        .run_cpu_job(&state.admission, cancellation, move |job_cancellation| {
            let bodies = catalog
                .snapshot_maintenance_block_bodies(
                    candidate.as_ref(),
                    active.as_ref(),
                    guard,
                    &job_cancellation,
                )
                .map_err(|error| match error {
                    MaintenanceSnapshotError::Cancelled => CpuJobError::Cancelled,
                    MaintenanceSnapshotError::Failure(report) => CpuJobError::Failure(report),
                })?;
            let mut goals = Vec::with_capacity(unsupported.len());
            for (position, target) in unsupported.into_iter().enumerate() {
                if position % 1024 == 0 && job_cancellation.is_cancelled() {
                    return Err(CpuJobError::Cancelled);
                }
                goals.push(bodies.target(target).cloned().ok_or_else(|| {
                    CpuJobError::Failure(maintenance_invariant(format!(
                        "bulk maintenance lacks the WP body for clause {}",
                        target.get()
                    )))
                })?);
            }
            Ok(BulkQuerySetup {
                axioms: bodies.antecedent_snapshot(),
                goals,
            })
        })
        .await;
    map_bulk_cpu_job(built, "bulk maintenance query setup")
}

fn map_bulk_cpu_job<T>(
    result: Result<T, CpuJobError>,
    context: &str,
) -> Result<T, BulkPreparationError> {
    match result {
        Ok(value) => Ok(value),
        Err(CpuJobError::Cancelled) | Err(CpuJobError::Admission(AdmissionError::Cancelled)) => {
            Err(BulkPreparationError::Cancelled)
        }
        Err(CpuJobError::Admission(AdmissionError::Closed(report)))
        | Err(CpuJobError::Failure(report)) => Err(BulkPreparationError::Failure(report)),
        Err(error) => Err(BulkPreparationError::Failure(bulk_global_failure(format!(
            "{context} failed: {error}"
        )))),
    }
}

fn bulk_global_failure(detail: impl Into<String>) -> FailureReport {
    FailureReport::try_new(
        FailureOrigin::MaintenanceExecution,
        FailureKind::InfrastructureFailure,
        false,
        FailureScope::RunGlobal,
        Some(detail.into()),
        Vec::new(),
    )
    .expect("bulk setup uses a permitted failure classification")
}

fn publish_bulk_success(
    state: &mut HoudiniState,
    plan: Arc<MaintenancePlan>,
    active: Arc<ClauseSet>,
    candidate: Arc<ClauseSet>,
    evidence: Option<crate::ArtifactRef>,
) {
    state.bulk_maint_capability = Some(BulkMaintenanceCapability {
        catalog_identity: state.catalog.identity(),
        plan,
        state_revision: Arc::clone(&state.maintenance_state_revision),
        active,
        candidate,
        evidence,
    });
    state.bulk_maint_proved = true;
}

fn append_bulk_history(
    state: &HoudiniState,
    outcome: &'static str,
    evidence: Option<crate::ArtifactRef>,
) -> Result<(), FailureReport> {
    if !state.maintenance_policy.log_maintenance_history() {
        return Ok(());
    }
    state.artifacts.append_maintenance_history_value(
        json!({
            "event": "bulk_maintenance",
            "outcome": outcome,
            "artifact_reference": evidence.map(|reference| json!({
                "backend": reference.backend_id().to_string(),
                "local_id": reference.local_id(),
                "kind": format!("{:?}", reference.kind()),
            })),
        }),
        &[],
    )
}

async fn settle_bulk_history(state: &HoudiniState) -> Result<(), FailureReport> {
    if state.maintenance_policy.fail_on_history_log_error() {
        state.artifacts.settle_maintenance_history_async().await
    } else {
        Ok(())
    }
}

fn missing_bulk_evidence(outcome: &EntailmentInvocationOutcome) -> FailureReport {
    match outcome {
        EntailmentInvocationOutcome::RunFailure(report)
        | EntailmentInvocationOutcome::Result(EntailmentCheckResult::Failure { report, .. }) => {
            report.clone()
        }
        _ => FailureReport::try_new(
            FailureOrigin::MaintenanceExecution,
            FailureKind::PublicationFailure,
            false,
            FailureScope::LaneLocal,
            Some("complete bulk maintenance check lacks durable evidence".to_string()),
            Vec::new(),
        )
        .expect("maintenance publication failures are permitted"),
    }
}

fn fail_bulk(state: &mut HoudiniState, report: FailureReport) -> BulkMaintenanceOutcome {
    if state.maintenance_failure.is_none() {
        state.maintenance_failure = Some(report.clone());
    }
    state.bulk_maint_proved = false;
    state.bulk_maint_capability = None;
    BulkMaintenanceOutcome::Failed(report)
}

fn exact_union(left: &ClauseSet, right: &ClauseSet) -> ClauseSet {
    let mut result = ClauseSet::with_capacity(left.len().saturating_add(right.len()));
    result.extend(left.iter().copied());
    result.extend(right.iter().copied());
    result
}
