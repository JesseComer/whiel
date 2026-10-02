//! Exact-Core termination checking for caller-neutral Houdini state.
//!
//! Termination is checked only after maintenance has stopped.  The query is
//! exactly `(Core and not loopGuard) entails preprocessedPost`; the negated
//! guard and postcondition are Lean-owned sources, while Core formula bodies
//! come from the trusted Catalog registrations.

use std::time::Duration;

use crate::artifact::{ArtifactRef, ScopeTag};
use crate::encoding::{EncodingError, PreparedBodyRef, SolverBodySource};
use crate::entailment::{
    EntailmentCheckResult, EntailmentInvocationOutcome, assemble_entailment,
    check_entailment_detailed,
};
use crate::failure::{FailureKind, FailureOrigin, FailureReport, FailureScope};
use crate::runtime::CancellationToken;
use crate::task::SynthesisTask;
use crate::vampire::{FmbOptions, VampireMode, VampireSearchBudget, VampireWorkerCommand};

use super::catalog::InitializationStatus;
use super::initialization::{HoudiniState, LastTermStatus, SearchFeedback};

// ------------------------------------------------------------
// Invocation Outcome
// ------------------------------------------------------------

/// Runtime control around one complete exact-Core termination check.
#[must_use]
#[derive(Clone, Debug)]
pub enum TerminationInvocationOutcome {
    Complete,
    Cancelled,
    RunFailure(FailureReport),
}

// ------------------------------------------------------------
// Exact-Core Termination Check
// ------------------------------------------------------------

/// Check whether the current protected Core proves the task exit obligation.
pub async fn term_check(
    task: &SynthesisTask,
    state: &mut HoudiniState,
    command: VampireWorkerCommand,
    cancellation: &CancellationToken,
) -> TerminationInvocationOutcome {
    // A settled result belongs to the exact unchanged Core.  Callers may use
    // this idempotent boundary to avoid re-running a failed or proved check.
    if !matches!(state.last_term_status, LastTermStatus::Pending) {
        return TerminationInvocationOutcome::Complete;
    }
    if cancellation.is_cancelled() {
        return TerminationInvocationOutcome::Cancelled;
    }
    if let Err(report) = validate_term_entry(task, state) {
        return finish_failure(state, report);
    }

    let stage = state
        .artifacts
        .scoped(ScopeTag::Houdini)
        .scoped(ScopeTag::verification_stage("termination"));
    let exit_guard = match state
        .catalog
        .encoding_context()
        .prepare_negated_loop_guard_body(&state.admission, &stage, cancellation)
        .await
    {
        Ok(body) => body,
        Err(EncodingError::Cancelled) => return TerminationInvocationOutcome::Cancelled,
        Err(EncodingError::Failure(report)) => {
            return finish_failure(state, map_failure(report, Vec::new()));
        }
    };
    let post = match prepare_postcondition(task, state, &stage, cancellation).await {
        Ok(body) => body,
        Err(EncodingError::Cancelled) => return TerminationInvocationOutcome::Cancelled,
        Err(EncodingError::Failure(report)) => {
            return finish_failure(state, map_failure(report, Vec::new()));
        }
    };
    let mut axioms = match sorted_core_bodies(state) {
        Ok(bodies) => bodies,
        Err(report) => return finish_failure(state, report),
    };
    axioms.push(exit_guard);

    let entailment = match assemble_entailment(
        state.catalog.encoding_context(),
        &state.admission,
        &stage,
        axioms,
        vec![post],
        cancellation,
    )
    .await
    {
        Ok(entailment) => entailment,
        Err(EncodingError::Cancelled) => return TerminationInvocationOutcome::Cancelled,
        Err(EncodingError::Failure(report)) => {
            return finish_failure(state, map_failure(report, Vec::new()));
        }
    };

    let allowances = match termination_allowances(state) {
        Ok(allowances) => allowances,
        Err(report) => return finish_failure(state, report),
    };
    for (attempt_index, allowance) in allowances.iter().copied().enumerate() {
        if cancellation.is_cancelled() {
            return TerminationInvocationOutcome::Cancelled;
        }
        let artifacts = stage.scoped(ScopeTag::named(format!("retry-tier:{attempt_index}")));
        let checked = check_entailment_detailed(
            &entailment,
            &artifacts,
            VampireSearchBudget::cumulative(state.verification.search_term_limit(), allowance),
            VampireMode::ProofAndFmb(FmbOptions::default()),
            command.clone(),
            state.admission.clone(),
            cancellation.clone(),
        )
        .await;
        let attempt_id = checked.attempt_id();
        let terminal_artifact = checked.terminal_artifact();
        match checked.into_outcome() {
            EntailmentInvocationOutcome::Result(EntailmentCheckResult::Proved { .. }) => {
                state.last_term_status = LastTermStatus::Proved;
                return TerminationInvocationOutcome::Complete;
            }
            EntailmentInvocationOutcome::Result(EntailmentCheckResult::Refuted(_)) => {
                let Some(attempt_id) = attempt_id else {
                    return finish_failure(
                        state,
                        termination_failure(
                            FailureKind::InfrastructureFailure,
                            false,
                            FailureScope::RunGlobal,
                            "a refuted termination check lacks an attempt identity",
                            terminal_artifact.into_iter().collect(),
                        ),
                    );
                };
                state.last_term_status = LastTermStatus::Counterexample(SearchFeedback::new(
                    task.identity().clone(),
                    state.artifacts.backend_id(),
                    attempt_id,
                ));
                return TerminationInvocationOutcome::Complete;
            }
            EntailmentInvocationOutcome::Result(EntailmentCheckResult::TimedOut {
                peer_failure,
                ..
            }) => {
                let mut references = terminal_artifact.into_iter().collect::<Vec<_>>();
                if let Some(peer) = peer_failure.as_ref() {
                    append_unique(&mut references, peer.artifact_references());
                }
                let detail = peer_failure.as_ref().map_or_else(
                    || format!("termination query timed out after {allowance:?}"),
                    |peer| {
                        format!(
                            "termination query timed out after {allowance:?}; peer origin={:?} kind={:?} retryable={} detail={}",
                            peer.origin(),
                            peer.kind(),
                            peer.retryable(),
                            peer.detail().unwrap_or("none")
                        )
                    },
                );
                let report = termination_failure(
                    FailureKind::CheckTimeout,
                    true,
                    FailureScope::LaneLocal,
                    detail,
                    references,
                );
                if attempt_index + 1 < allowances.len() {
                    continue;
                }
                return finish_failure(state, report);
            }
            EntailmentInvocationOutcome::Result(EntailmentCheckResult::Failure {
                report, ..
            }) => {
                let mapped = map_failure(report, terminal_artifact.into_iter().collect());
                if is_retryable_termination_failure(&mapped) && attempt_index + 1 < allowances.len()
                {
                    continue;
                }
                return finish_failure(state, mapped);
            }
            EntailmentInvocationOutcome::Cancelled(_) => {
                return TerminationInvocationOutcome::Cancelled;
            }
            EntailmentInvocationOutcome::RunFailure(report) => {
                return finish_failure(
                    state,
                    map_failure(report, terminal_artifact.into_iter().collect()),
                );
            }
        }
    }

    unreachable!("a valid termination policy always schedules its base attempt")
}

// ------------------------------------------------------------
// Trusted Source And State Helpers
// ------------------------------------------------------------

async fn prepare_postcondition(
    task: &SynthesisTask,
    state: &HoudiniState,
    artifacts: &crate::artifact::ArtifactStore,
    cancellation: &CancellationToken,
) -> Result<PreparedBodyRef, EncodingError> {
    let mut bodies = state
        .catalog
        .encoding_context()
        .prepare_solver_bodies(
            &state.admission,
            artifacts,
            vec![SolverBodySource::Assert(
                task.preprocessed_post_solver().clone(),
            )],
            cancellation,
        )
        .await?;
    debug_assert_eq!(bodies.len(), 1);
    Ok(bodies.remove(0))
}

fn sorted_core_bodies(state: &HoudiniState) -> Result<Vec<PreparedBodyRef>, FailureReport> {
    let mut ids = state.core.iter().copied().collect::<Vec<_>>();
    ids.sort_unstable();
    ids.into_iter()
        .map(|id| {
            let record = state.catalog.record(id)?;
            if record.initialization() != InitializationStatus::InitProved {
                return Err(term_state_failure(format!(
                    "Core clause {} is not InitProved",
                    id.get()
                )));
            }
            record.formula_body().cloned().ok_or_else(|| {
                term_state_failure(format!(
                    "Core clause {} lacks its prepared formula body",
                    id.get()
                ))
            })
        })
        .collect()
}

fn validate_term_entry(task: &SynthesisTask, state: &HoudiniState) -> Result<(), FailureReport> {
    if state.catalog.task_identity() != task.identity()
        || state.artifacts.task_identity() != task.identity()
        || state.catalog.artifacts().backend_id() != state.artifacts.backend_id()
        || state.catalog.encoding_context().task_identity() != task.identity()
        || state.admission.policy() != state.verification.resources()
    {
        return Err(termination_failure(
            FailureKind::InfrastructureFailure,
            false,
            FailureScope::RunGlobal,
            "termination task, state, catalog, context, artifacts, and admission differ",
            Vec::new(),
        ));
    }
    if state.maintenance_failure.is_some()
        || !state.active.is_empty()
        || state.maintenance_plan.is_some()
        || state.candidate_snapshot.is_some()
        || !state.present_support_count.is_empty()
    {
        return Err(term_state_failure(
            "termination requires fully stopped maintenance state",
        ));
    }
    Ok(())
}

fn termination_allowances(state: &HoudiniState) -> Result<Vec<Duration>, FailureReport> {
    let mut current = state.verification.search_term_limit();
    let mut allowances = Vec::with_capacity(
        state
            .verification
            .search_term_retry_increments()
            .len()
            .saturating_add(1),
    );
    allowances.push(current);
    for increment in state.verification.search_term_retry_increments() {
        current = current.checked_add(*increment).ok_or_else(|| {
            termination_failure(
                FailureKind::InfrastructureFailure,
                false,
                FailureScope::RunGlobal,
                "cumulative termination retry allowance overflowed Duration",
                Vec::new(),
            )
        })?;
        allowances.push(current);
    }
    Ok(allowances)
}

// ------------------------------------------------------------
// Typed Failure Translation
// ------------------------------------------------------------

fn finish_failure(state: &mut HoudiniState, report: FailureReport) -> TerminationInvocationOutcome {
    let run_global = report.scope() == FailureScope::RunGlobal;
    state.last_term_status = LastTermStatus::Failure(report.clone());
    if run_global {
        TerminationInvocationOutcome::RunFailure(report)
    } else {
        TerminationInvocationOutcome::Complete
    }
}

fn map_failure(report: FailureReport, mut references: Vec<ArtifactRef>) -> FailureReport {
    append_unique(&mut references, report.artifact_references());
    let kind = match report.kind() {
        FailureKind::CheckTimeout => FailureKind::CheckTimeout,
        FailureKind::SolverUnknown => FailureKind::SolverUnknown,
        FailureKind::MalformedResult => FailureKind::MalformedResult,
        FailureKind::ProcessFailure => FailureKind::ProcessFailure,
        FailureKind::ConcurrentWorkerFailures => FailureKind::ConcurrentWorkerFailures,
        _ => FailureKind::InfrastructureFailure,
    };
    let retryable = report.retryable()
        && matches!(
            kind,
            FailureKind::CheckTimeout
                | FailureKind::SolverUnknown
                | FailureKind::InfrastructureFailure
        );
    termination_failure(
        kind,
        retryable,
        report.scope(),
        format!(
            "nested origin={:?} kind={:?} retryable={} scope={:?} detail={}",
            report.origin(),
            report.kind(),
            report.retryable(),
            report.scope(),
            report.detail().unwrap_or("none")
        ),
        references,
    )
}

fn is_retryable_termination_failure(report: &FailureReport) -> bool {
    report.retryable()
        && matches!(
            report.kind(),
            FailureKind::CheckTimeout
                | FailureKind::SolverUnknown
                | FailureKind::InfrastructureFailure
        )
}

fn term_state_failure(detail: impl Into<String>) -> FailureReport {
    termination_failure(
        FailureKind::InfrastructureFailure,
        false,
        FailureScope::RunGlobal,
        detail,
        Vec::new(),
    )
}

fn termination_failure(
    kind: FailureKind,
    retryable: bool,
    scope: FailureScope,
    detail: impl Into<String>,
    references: Vec<ArtifactRef>,
) -> FailureReport {
    FailureReport::try_new(
        FailureOrigin::TerminationCheck,
        kind,
        retryable,
        scope,
        Some(detail.into()),
        references,
    )
    .expect("termination checks use only permitted failure classifications")
}

fn append_unique(target: &mut Vec<ArtifactRef>, sources: &[ArtifactRef]) {
    for source in sources {
        if !target.contains(source) {
            target.push(*source);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::runtime::RuntimeResourcePolicy;

    #[test]
    fn retry_allowances_are_cumulative() {
        let resources = RuntimeResourcePolicy::agent_only(2, 2).unwrap();
        let verification =
            super::super::VerificationParameters::new(Duration::from_secs(3), resources)
                .unwrap()
                .with_search_term_retry_increments(vec![
                    Duration::from_secs(3),
                    Duration::from_secs(3),
                ])
                .unwrap();

        let mut current = verification.search_term_limit();
        let mut allowances = vec![current];
        for increment in verification.search_term_retry_increments() {
            current = current.checked_add(*increment).unwrap();
            allowances.push(current);
        }

        assert_eq!(
            allowances,
            vec![
                Duration::from_secs(3),
                Duration::from_secs(6),
                Duration::from_secs(9)
            ]
        );
    }

    #[test]
    fn failure_translation_preserves_nested_diagnostics() {
        let raw = FailureReport::try_new(
            FailureOrigin::VampireProofSearch,
            FailureKind::SolverUnknown,
            false,
            FailureScope::LaneLocal,
            Some("unknown status".to_string()),
            Vec::new(),
        )
        .unwrap();

        let mapped = map_failure(raw, Vec::new());

        assert_eq!(mapped.origin(), FailureOrigin::TerminationCheck);
        assert_eq!(mapped.kind(), FailureKind::SolverUnknown);
        assert!(!mapped.retryable());
        assert!(
            mapped
                .detail()
                .unwrap()
                .contains("origin=VampireProofSearch")
        );
    }
}
