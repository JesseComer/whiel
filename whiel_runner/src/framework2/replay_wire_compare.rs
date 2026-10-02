//! Strict wire comparison consumes owner-checked bindings; it never establishes
//! identity correspondence from equal-looking wire fields. Rebinding produces
//! typed scalar edits so the caller can preserve original bytes and chunks.

use serde::{Deserialize, Serialize};

use super::replay_identity::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ReplayWireIdentity {
    Run,
    CatalogRecord,
    Partition,
    StateSnapshot,
    CheckRequest,
    LedgerRow,
    EvidenceReceipt,
    RouteDisplay,
    Consultation,
    ValidationManifest,
    DropAuthorization,
    Cursor,
    ArtifactReference,
    PushRequest,
    Response,
}

pub(super) trait ReplayWireBindings {
    fn map_identity(&self, kind: ReplayWireIdentity, old: &str)
    -> Result<String, ReplayDivergence>;
    fn map_attempt(&self, old: PhysicalAttemptId) -> Result<PhysicalAttemptId, ReplayDivergence>;
    /// Rebinding model tool arguments requires a validated-refutation capability,
    /// not merely a known physical proof/progress attempt.
    fn map_refutation_attempt(
        &self,
        old: PhysicalAttemptId,
    ) -> Result<PhysicalAttemptId, ReplayDivergence>;
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "slot", rename_all = "snake_case", deny_unknown_fields)]
pub enum ReplayTimingDifference {
    RemainingSearchBudget {
        path: String,
        old: String,
        live: String,
    },
    LedgerSolver {
        path: String,
        row_ordinal: LedgerRowOrdinal,
        #[serde(deserialize_with = "required_nullable")]
        old: Option<u64>,
        #[serde(deserialize_with = "required_nullable")]
        live: Option<u64>,
    },
    LedgerPreparation {
        path: String,
        row_ordinal: LedgerRowOrdinal,
        #[serde(deserialize_with = "required_nullable")]
        old: Option<u64>,
        #[serde(deserialize_with = "required_nullable")]
        live: Option<u64>,
    },
}

fn required_nullable<'de, D, T>(deserializer: D) -> Result<Option<T>, D::Error>
where
    D: serde::Deserializer<'de>,
    T: Deserialize<'de>,
{
    Option::<T>::deserialize(deserializer)
}

fn divergence(path: &str, reason: &str) -> ReplayDivergence {
    ReplayDivergence {
        path: path.into(),
        reason: reason.into(),
    }
}
fn same<T: PartialEq>(old: &T, live: &T, path: &str) -> Result<(), ReplayDivergence> {
    if old == live {
        Ok(())
    } else {
        Err(divergence(
            path,
            "typed semantic or structural field differs",
        ))
    }
}
fn child(path: &str, field: &str) -> String {
    format!("{path}/{field}")
}
fn indexed(path: &str, ordinal: usize) -> String {
    format!("{path}/{ordinal}")
}

struct Comparator<'a, B: ReplayWireBindings + ?Sized> {
    bindings: &'a B,
    timing: Vec<ReplayTimingDifference>,
}
impl<'a, B: ReplayWireBindings + ?Sized> Comparator<'a, B> {
    fn new(bindings: &'a B) -> Self {
        Self {
            bindings,
            timing: Vec::new(),
        }
    }
    fn identity(
        &self,
        kind: ReplayWireIdentity,
        old: &mut String,
        path: &str,
    ) -> Result<(), ReplayDivergence> {
        *old = self.bindings.map_identity(kind, old).map_err(|mut e| {
            e.path = path.into();
            e
        })?;
        Ok(())
    }
    fn attempt(&self, old: &mut PhysicalAttemptId, path: &str) -> Result<(), ReplayDivergence> {
        *old = self.bindings.map_attempt(*old).map_err(|mut e| {
            e.path = path.into();
            e
        })?;
        Ok(())
    }
    fn clause(&self, old: &mut ClauseV1, path: &str) -> Result<(), ReplayDivergence> {
        self.identity(
            ReplayWireIdentity::CatalogRecord,
            &mut old.record_digest,
            &child(path, "record_digest"),
        )
    }
    fn clause_reference(
        &self,
        old: &mut ClauseReferenceV1,
        path: &str,
    ) -> Result<(), ReplayDivergence> {
        self.identity(
            ReplayWireIdentity::CatalogRecord,
            &mut old.record_digest,
            &child(path, "record_digest"),
        )
    }
    fn drop_reference(&self, old: &mut DropV1, path: &str) -> Result<(), ReplayDivergence> {
        self.clause_reference(&mut old.clause, &child(path, "clause"))?;
        self.identity(
            ReplayWireIdentity::Consultation,
            &mut old.consultation_digest,
            &child(path, "consultation_digest"),
        )?;
        self.identity(
            ReplayWireIdentity::DropAuthorization,
            &mut old.authorization_digest,
            &child(path, "authorization_digest"),
        )
    }
    fn artifact(&self, old: &mut ArtifactV1, path: &str) -> Result<(), ReplayDivergence> {
        self.identity(
            ReplayWireIdentity::ArtifactReference,
            &mut old.stable_id,
            &child(path, "stable_id"),
        )
    }
    fn artifacts(&self, old: &mut [ArtifactV1], path: &str) -> Result<(), ReplayDivergence> {
        for (i, a) in old.iter_mut().enumerate() {
            self.artifact(a, &indexed(path, i))?;
        }
        Ok(())
    }
    fn failure(&self, old: &mut FailureV1, path: &str) -> Result<(), ReplayDivergence> {
        self.artifacts(&mut old.artifacts, &child(path, "artifacts"))
    }
    fn correction(&self, old: &mut CorrectionV1, path: &str) -> Result<(), ReplayDivergence> {
        self.identity(
            ReplayWireIdentity::Consultation,
            &mut old.binding.consultation_digest,
            &child(path, "binding/consultation_digest"),
        )?;
        self.identity(
            ReplayWireIdentity::Response,
            &mut old.binding.rejected_response_digest,
            &child(path, "binding/rejected_response_digest"),
        )
    }
    fn feedback_binding(
        &self,
        old: &mut FeedbackBindingV1,
        path: &str,
    ) -> Result<(), ReplayDivergence> {
        self.identity(
            ReplayWireIdentity::Run,
            &mut old.run_digest,
            &child(path, "run_digest"),
        )?;
        self.identity(
            ReplayWireIdentity::Consultation,
            &mut old.consultation_digest,
            &child(path, "consultation_digest"),
        )?;
        self.identity(
            ReplayWireIdentity::StateSnapshot,
            &mut old.state_snapshot_digest,
            &child(path, "state_snapshot_digest"),
        )?;
        self.identity(
            ReplayWireIdentity::ValidationManifest,
            &mut old.validation_manifest_digest,
            &child(path, "validation_manifest_digest"),
        )
    }
    fn push(&mut self, old: &mut PushV1, live: &PushV1) -> Result<(), ReplayDivergence> {
        let b = &mut old.binding;
        self.identity(
            ReplayWireIdentity::Run,
            &mut b.run_digest,
            "/binding/run_digest",
        )?;
        self.identity(
            ReplayWireIdentity::Consultation,
            &mut b.consultation_digest,
            "/binding/consultation_digest",
        )?;
        self.identity(
            ReplayWireIdentity::StateSnapshot,
            &mut b.state_snapshot_digest,
            "/binding/state_snapshot_digest",
        )?;
        self.identity(
            ReplayWireIdentity::ValidationManifest,
            &mut b.validation_manifest_digest,
            "/binding/validation_manifest_digest",
        )?;
        self.feedback_binding(&mut old.feedback.binding, "/feedback/binding")?;
        let remaining = &mut old.feedback.remaining_search_budget_ns;
        if *remaining != live.feedback.remaining_search_budget_ns {
            self.timing
                .push(ReplayTimingDifference::RemainingSearchBudget {
                    path: "/feedback/remaining_search_budget_ns".into(),
                    old: remaining.clone(),
                    live: live.feedback.remaining_search_budget_ns.clone(),
                });
            remaining.clone_from(&live.feedback.remaining_search_budget_ns);
        }
        for (i, row) in old.feedback.core.iter_mut().enumerate() {
            self.clause(&mut row.clause, &format!("/feedback/core/{i}/clause"))?;
        }
        for (i, row) in old.feedback.last_round.iter_mut().enumerate() {
            self.clause(&mut row.clause, &format!("/feedback/last_round/{i}/clause"))?;
            // Status death reasons contain ledger ordinals, never physical IDs.
        }
        for (i, row) in old.feedback.pending.iter_mut().enumerate() {
            self.clause(&mut row.clause, &format!("/feedback/pending/{i}/clause"))?;
            if let Some(drop) = &mut row.drop_reference {
                self.drop_reference(drop, &format!("/feedback/pending/{i}/drop_reference"))?;
            }
        }
        match &mut old.feedback.latest {
            LatestV1::Initial {} | LatestV1::CounterexampleRejected { .. } => {}
            LatestV1::PostconditionOpen { postcondition_open } => match postcondition_open {
                PostconditionOpenV1::Refuted { attempt } => {
                    if let Some(attempt) = attempt {
                        self.attempt(attempt, "/feedback/latest/postcondition_open/attempt")?;
                    }
                }
                PostconditionOpenV1::Inconclusive { .. } => {}
            },
            LatestV1::Failure { failure } => self.failure(failure, "/feedback/latest/failure")?,
        }
        if let Some(correction) = &mut old.correction {
            self.correction(correction, "/correction")?;
        }
        Ok(())
    }
    fn route(&self, old: &mut RouteV1, path: &str) -> Result<(), ReplayDivergence> {
        match old {
            RouteV1::RuntimeProof {
                receipt_digest,
                artifacts,
                ..
            } => {
                self.identity(
                    ReplayWireIdentity::EvidenceReceipt,
                    receipt_digest,
                    &child(path, "receipt_digest"),
                )?;
                self.artifacts(artifacts, &child(path, "artifacts"))
            }
            RouteV1::ProtectedTheorem { artifact, .. } => {
                self.artifact(artifact, &child(path, "artifact"))
            }
            RouteV1::ValidatedRefutation {
                refutation_digest,
                artifacts,
                ..
            } => {
                self.identity(
                    ReplayWireIdentity::EvidenceReceipt,
                    refutation_digest,
                    &child(path, "refutation_digest"),
                )?;
                self.artifacts(artifacts, &child(path, "artifacts"))
            }
            RouteV1::RetryProgress {
                progress_digest,
                peer_failure,
                artifacts,
                ..
            } => {
                self.identity(
                    ReplayWireIdentity::EvidenceReceipt,
                    progress_digest,
                    &child(path, "progress_digest"),
                )?;
                if let Some(failure) = peer_failure {
                    self.failure(failure, &child(path, "peer_failure"))?;
                }
                // Proof allowances/frontier are exact algorithmic values, not timings.
                self.artifacts(artifacts, &child(path, "artifacts"))
            }
            RouteV1::Suspended {} => Ok(()),
        }
    }
    fn result(&self, old: &mut AttemptResultV1, path: &str) -> Result<(), ReplayDivergence> {
        self.identity(
            ReplayWireIdentity::RouteDisplay,
            &mut old.route_digest,
            &child(path, "route_digest"),
        )?;
        if let Some(route) = &mut old.route {
            self.route(route, &child(path, "route"))?;
        }
        if let Some(attempt) = &mut old.attempt_id {
            self.attempt(attempt, &child(path, "attempt_id"))?;
        }
        Ok(())
    }
    fn previous_row(&self, old: &mut Option<String>, path: &str) -> Result<(), ReplayDivergence> {
        if let Some(digest) = old {
            self.identity(ReplayWireIdentity::LedgerRow, digest, path)?;
        }
        Ok(())
    }
    fn row_timings(
        &mut self,
        ordinal: LedgerRowOrdinal,
        old_solver: &mut Option<u64>,
        live_solver: Option<u64>,
        old_preparation: &mut Option<u64>,
        live_preparation: Option<u64>,
        path: &str,
    ) -> Result<(), ReplayDivergence> {
        same(
            &old_solver.is_some(),
            &live_solver.is_some(),
            &child(path, "solver_time_nanos"),
        )?;
        same(
            &old_preparation.is_some(),
            &live_preparation.is_some(),
            &child(path, "preparation_time_nanos"),
        )?;
        if *old_solver != live_solver {
            self.timing.push(ReplayTimingDifference::LedgerSolver {
                path: child(path, "solver_time_nanos"),
                row_ordinal: ordinal,
                old: *old_solver,
                live: live_solver,
            });
            *old_solver = live_solver;
        }
        if *old_preparation != live_preparation {
            self.timing.push(ReplayTimingDifference::LedgerPreparation {
                path: child(path, "preparation_time_nanos"),
                row_ordinal: ordinal,
                old: *old_preparation,
                live: live_preparation,
            });
            *old_preparation = live_preparation;
        }
        Ok(())
    }
    fn attempt_row(
        &mut self,
        old: &mut AttemptRowV1,
        live: &AttemptRowV1,
        path: &str,
    ) -> Result<(), ReplayDivergence> {
        let AttemptRowV1::Attempt {
            row_ordinal,
            clause,
            request_digest,
            partition_digest,
            result,
            solver_time_nanos,
            preparation_time_nanos,
            previous_row_digest,
            row_digest,
            ..
        } = old;
        let AttemptRowV1::Attempt {
            solver_time_nanos: live_solver,
            preparation_time_nanos: live_preparation,
            ..
        } = live;
        self.clause(clause, &child(path, "clause"))?;
        self.identity(
            ReplayWireIdentity::CheckRequest,
            request_digest,
            &child(path, "request_digest"),
        )?;
        self.identity(
            ReplayWireIdentity::Partition,
            partition_digest,
            &child(path, "partition_digest"),
        )?;
        self.result(result, &child(path, "result"))?;
        self.previous_row(previous_row_digest, &child(path, "previous_row_digest"))?;
        self.identity(
            ReplayWireIdentity::LedgerRow,
            row_digest,
            &child(path, "row_digest"),
        )?;
        self.row_timings(
            *row_ordinal,
            solver_time_nanos,
            *live_solver,
            preparation_time_nanos,
            *live_preparation,
            path,
        )?;
        Ok(())
    }
    fn ledger_row(
        &mut self,
        old: &mut LedgerRowV1,
        live: &LedgerRowV1,
        path: &str,
    ) -> Result<(), ReplayDivergence> {
        match (old, live) {
            (
                LedgerRowV1::Attempt {
                    row_ordinal,
                    clause,
                    request_digest,
                    partition_digest,
                    result,
                    solver_time_nanos,
                    preparation_time_nanos,
                    previous_row_digest,
                    row_digest,
                    ..
                },
                LedgerRowV1::Attempt {
                    solver_time_nanos: live_solver,
                    preparation_time_nanos: live_preparation,
                    ..
                },
            ) => {
                self.clause(clause, &child(path, "clause"))?;
                self.identity(
                    ReplayWireIdentity::CheckRequest,
                    request_digest,
                    &child(path, "request_digest"),
                )?;
                self.identity(
                    ReplayWireIdentity::Partition,
                    partition_digest,
                    &child(path, "partition_digest"),
                )?;
                self.result(result, &child(path, "result"))?;
                self.previous_row(previous_row_digest, &child(path, "previous_row_digest"))?;
                self.identity(
                    ReplayWireIdentity::LedgerRow,
                    row_digest,
                    &child(path, "row_digest"),
                )?;
                self.row_timings(
                    *row_ordinal,
                    solver_time_nanos,
                    *live_solver,
                    preparation_time_nanos,
                    *live_preparation,
                    path,
                )?;
            }
            (
                LedgerRowV1::Invalidation {
                    target,
                    cause,
                    previous_row_digest,
                    row_digest,
                    ..
                },
                LedgerRowV1::Invalidation { .. },
            ) => {
                self.clause(target, &child(path, "target"))?;
                if let Some(cause) = cause {
                    self.clause(cause, &child(path, "cause"))?;
                }
                self.previous_row(previous_row_digest, &child(path, "previous_row_digest"))?;
                self.identity(
                    ReplayWireIdentity::LedgerRow,
                    row_digest,
                    &child(path, "row_digest"),
                )?;
            }
            _ => return Err(divergence(path, "ledger row variant differs")),
        }
        Ok(())
    }
    fn countermodel(&self, old: &mut CountermodelV1, path: &str) -> Result<(), ReplayDivergence> {
        match old {
            CountermodelV1::Clause(ClauseCountermodelV1::Retained(row)) => {
                self.attempt(&mut row.attempt, &child(path, "attempt"))?;
                self.clause(&mut row.clause, &child(path, "clause"))
            }
            CountermodelV1::Clause(ClauseCountermodelV1::Unavailable(row)) => {
                self.attempt(&mut row.attempt, &child(path, "attempt"))?;
                self.clause(&mut row.clause, &child(path, "clause"))
            }
            CountermodelV1::Termination(TerminationCountermodelV1::Retained(row)) => {
                self.attempt(&mut row.attempt, &child(path, "attempt"))
            }
            CountermodelV1::Termination(TerminationCountermodelV1::Unavailable(row)) => {
                self.attempt(&mut row.attempt, &child(path, "attempt"))
            }
        }
    }
    fn tool_response(
        &mut self,
        old: &mut ToolResponseV1,
        live: &ToolResponseV1,
    ) -> Result<(), ReplayDivergence> {
        match (old, live) {
            (ToolResponseV1::Error(_), ToolResponseV1::Error(_)) => {}
            // Opaque skill data is not an identity-bearing engine view. The
            // final same(old, live) compares every content field exactly.
            (ToolResponseV1::ValidateClauses(_), ToolResponseV1::ValidateClauses(_)) => {}
            (ToolResponseV1::Countermodel(old), ToolResponseV1::Countermodel(_)) => {
                self.countermodel(&mut old.result, "/result")?
            }
            (
                ToolResponseV1::StrongestRefutations(old),
                ToolResponseV1::StrongestRefutations(_),
            ) => {
                self.clause(&mut old.result.clause, "/result/clause")?;
                for (i, row) in old.result.refutations.iter_mut().enumerate() {
                    let attempt = match row {
                        RefutationSummaryV1::Retained(row) => &mut row.attempt,
                        RefutationSummaryV1::Unavailable(row) => &mut row.attempt,
                    };
                    self.attempt(attempt, &format!("/result/refutations/{i}/attempt"))?;
                }
            }
            (ToolResponseV1::History(old), ToolResponseV1::History(live)) => {
                self.clause(&mut old.result.clause, "/result/clause")?;
                same(
                    &old.result.attempts.len(),
                    &live.result.attempts.len(),
                    "/result/attempts",
                )?;
                for (i, (old, live)) in old
                    .result
                    .attempts
                    .iter_mut()
                    .zip(&live.result.attempts)
                    .enumerate()
                {
                    self.attempt_row(old, live, &format!("/result/attempts/{i}"))?;
                }
            }
            (ToolResponseV1::Ledger(old), ToolResponseV1::Ledger(live)) => {
                // Actual ledger continuation is an exact decimal row index.
                same(
                    &old.result.items.len(),
                    &live.result.items.len(),
                    "/result/items",
                )?;
                for (i, (old, live)) in old
                    .result
                    .items
                    .iter_mut()
                    .zip(&live.result.items)
                    .enumerate()
                {
                    self.ledger_row(old, live, &format!("/result/items/{i}"))?;
                }
            }
            (ToolResponseV1::EvaluateClauses(old), ToolResponseV1::EvaluateClauses(_)) => {
                for (i, attempt) in old.result.instances.iter_mut().enumerate() {
                    if let EvaluationLabelV1::Retained { attempt, .. } = attempt {
                        self.attempt(attempt, &format!("/result/instances/{i}/attempt"))?;
                    }
                }
                for (i, skipped) in old.result.skipped.iter_mut().enumerate() {
                    self.attempt(
                        &mut skipped.attempt,
                        &format!("/result/skipped/{i}/attempt"),
                    )?;
                }
            }
            _ => return Err(divergence("$", "tool response variant differs")),
        }
        Ok(())
    }
}

pub(super) fn compare_push<B: ReplayWireBindings + ?Sized>(
    old: &[u8],
    live: &[u8],
    bindings: &B,
) -> Result<Vec<ReplayTimingDifference>, ReplayDivergence> {
    let mut old = decode_push(old)?;
    let live = decode_push(live)?;
    let mut comparison = Comparator::new(bindings);
    comparison.push(&mut old, &live)?;
    same(&old, &live, "$")?;
    Ok(comparison.timing)
}
pub(super) fn compare_tool_response<B: ReplayWireBindings + ?Sized>(
    old: &[u8],
    live: &[u8],
    bindings: &B,
) -> Result<Vec<ReplayTimingDifference>, ReplayDivergence> {
    let mut old = decode_tool_response(old)?;
    let live = decode_tool_response(live)?;
    let mut comparison = Comparator::new(bindings);
    comparison.tool_response(&mut old, &live)?;
    same(&old, &live, "$")?;
    Ok(comparison.timing)
}
pub(super) fn compare_route<B: ReplayWireBindings + ?Sized>(
    old: &RouteV1,
    live: &RouteV1,
    bindings: &B,
) -> Result<(), ReplayDivergence> {
    let mut mapped = old.clone();
    Comparator::new(bindings).route(&mut mapped, "/route")?;
    same(&mapped, live, "/route")
}

pub(super) fn compare_correction<B: ReplayWireBindings + ?Sized>(
    old: &[u8],
    live: &[u8],
    bindings: &B,
) -> Result<Vec<ReplayTimingDifference>, ReplayDivergence> {
    let mut old: CorrectionV1 = decode_wire(old)?;
    let live: CorrectionV1 = decode_wire(live)?;
    if old.schema_version != super::agent::AGENT_HOUDINI_PROTOCOL_VERSION
        || live.schema_version != super::agent::AGENT_HOUDINI_PROTOCOL_VERSION
    {
        return Err(divergence(
            "/schema_version",
            "unsupported correction wire version",
        ));
    }
    Comparator::new(bindings).correction(&mut old, "")?;
    same(&old, &live, "$")?;
    Ok(Vec::new())
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum ReplayWireReplacement {
    Identity {
        path: String,
        identity: ReplayWireIdentity,
        old: String,
        live: String,
    },
    PhysicalAttempt {
        path: String,
        old: PhysicalAttemptId,
        live: PhysicalAttemptId,
    },
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReplayWireRebinding {
    /// False means malformed, unsupported, or unknown-schema input. Original
    /// bytes must be returned to the normal validator without any alteration.
    pub parsed: bool,
    pub replacements: Vec<ReplayWireReplacement>,
}
struct Rebinding<'a, B: ReplayWireBindings + ?Sized> {
    bindings: &'a B,
    plan: ReplayWireRebinding,
}
impl<'a, B: ReplayWireBindings + ?Sized> Rebinding<'a, B> {
    fn new(bindings: &'a B) -> Self {
        Self {
            bindings,
            plan: ReplayWireRebinding {
                parsed: true,
                replacements: Vec::new(),
            },
        }
    }
    fn identity(&mut self, kind: ReplayWireIdentity, old: &str, path: &str) {
        // Missing maps represent deliberately wrong/stale echoes, which remain
        // exactly as supplied. The caller cannot create a binding from this plan.
        if let Ok(live) = self.bindings.map_identity(kind, old)
            && live != old
        {
            self.plan
                .replacements
                .push(ReplayWireReplacement::Identity {
                    path: path.into(),
                    identity: kind,
                    old: old.into(),
                    live,
                });
        }
    }
    fn attempt(&mut self, old: PhysicalAttemptId, path: &str) {
        if let Ok(live) = self.bindings.map_refutation_attempt(old)
            && live != old
        {
            self.plan
                .replacements
                .push(ReplayWireReplacement::PhysicalAttempt {
                    path: path.into(),
                    old,
                    live,
                });
        }
    }
    fn clause_reference(&mut self, old: &ClauseReferenceV1, path: &str) {
        self.identity(
            ReplayWireIdentity::CatalogRecord,
            &old.record_digest,
            &child(path, "record_digest"),
        );
    }
    fn clause_argument(&mut self, old: &ClauseArgumentV1, path: &str) {
        self.identity(
            ReplayWireIdentity::CatalogRecord,
            &old.record_digest,
            &child(path, "record_digest"),
        );
    }
    fn response_binding(&mut self, b: &ResponseBindingV1) {
        self.identity(
            ReplayWireIdentity::Run,
            &b.run_digest,
            "/binding/run_digest",
        );
        self.identity(
            ReplayWireIdentity::Consultation,
            &b.consultation_digest,
            "/binding/consultation_digest",
        );
        self.identity(
            ReplayWireIdentity::StateSnapshot,
            &b.state_snapshot_digest,
            "/binding/state_snapshot_digest",
        );
        self.identity(
            ReplayWireIdentity::ValidationManifest,
            &b.validation_manifest_digest,
            "/binding/validation_manifest_digest",
        );
        self.identity(
            ReplayWireIdentity::PushRequest,
            &b.request_digest,
            "/binding/request_digest",
        );
    }
}
fn unparsed() -> ReplayWireRebinding {
    ReplayWireRebinding {
        parsed: false,
        replacements: Vec::new(),
    }
}

/// The plan addresses exact typed scalar paths only. Apply it to the original
/// byte spans; never regenerate the JSON or normalize chunk boundaries. Response
/// capability edits have equal-length 64-hex payloads under checked owner maps.
pub(super) fn rebind_response<B: ReplayWireBindings + ?Sized>(
    bytes: &[u8],
    bindings: &B,
) -> ReplayWireRebinding {
    let Ok(response) = decode_response(bytes) else {
        return unparsed();
    };
    let mut rebind = Rebinding::new(bindings);
    match response {
        ResponseV1::CandidateClauses {
            binding, dropped, ..
        } => {
            rebind.response_binding(&binding);
            for (i, drop) in dropped.iter().enumerate() {
                let p = format!("/dropped/{i}");
                rebind.clause_reference(&drop.clause, &child(&p, "clause"));
                rebind.identity(
                    ReplayWireIdentity::Consultation,
                    &drop.consultation_digest,
                    &child(&p, "consultation_digest"),
                );
                rebind.identity(
                    ReplayWireIdentity::DropAuthorization,
                    &drop.authorization_digest,
                    &child(&p, "authorization_digest"),
                );
            }
        }
        ResponseV1::CandidateCounterexample { binding, .. } => rebind.response_binding(&binding),
    }
    rebind.plan
}
pub(super) fn rebind_tool_arguments<B: ReplayWireBindings + ?Sized>(
    tool: &str,
    bytes: &[u8],
    bindings: &B,
) -> ReplayWireRebinding {
    let Ok(arguments) = decode_tool_arguments(tool, bytes) else {
        return unparsed();
    };
    let mut rebind = Rebinding::new(bindings);
    match arguments {
        ToolArgumentsV1::Countermodel(args) => rebind.attempt(args.attempt, "/attempt"),
        ToolArgumentsV1::StrongestRefutations(args) | ToolArgumentsV1::History(args) => {
            rebind.clause_argument(&args.clause, "/clause")
        }
        ToolArgumentsV1::EvaluateClauses(args) => {
            if let crate::proposer_api::EvaluationSelection::Sources(instances) = args.instances {
                for (i, source) in instances.into_iter().enumerate() {
                    if let crate::proposer_api::EvaluationSource::Retained { attempt } = source {
                        rebind.attempt(
                            PhysicalAttemptId(attempt),
                            &format!("/instances/{i}/attempt"),
                        );
                    }
                }
            }
        }
        ToolArgumentsV1::Ledger(_) | ToolArgumentsV1::ValidateClauses(_) => {}
    }
    rebind.plan
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::{Value, json};
    use std::collections::BTreeMap;

    #[derive(Default)]
    struct Bindings {
        identities: BTreeMap<(ReplayWireIdentity, String), String>,
        attempts: BTreeMap<PhysicalAttemptId, PhysicalAttemptId>,
    }
    impl ReplayWireBindings for Bindings {
        fn map_identity(
            &self,
            kind: ReplayWireIdentity,
            old: &str,
        ) -> Result<String, ReplayDivergence> {
            self.identities
                .get(&(kind, old.to_owned()))
                .cloned()
                .ok_or_else(|| divergence("$", "no checked identity binding"))
        }
        fn map_attempt(
            &self,
            old: PhysicalAttemptId,
        ) -> Result<PhysicalAttemptId, ReplayDivergence> {
            self.attempts
                .get(&old)
                .copied()
                .ok_or_else(|| divergence("$", "no checked attempt binding"))
        }
        fn map_refutation_attempt(
            &self,
            old: PhysicalAttemptId,
        ) -> Result<PhysicalAttemptId, ReplayDivergence> {
            if old.0 == 41 {
                return Err(divergence("$", "known non-refutation attempt"));
            }
            self.map_attempt(old)
        }
    }
    fn cap(side: &str, kind: ReplayWireIdentity) -> String {
        format!("{side}:{kind:?}")
    }
    fn bindings() -> Bindings {
        let kinds = [
            ReplayWireIdentity::Run,
            ReplayWireIdentity::CatalogRecord,
            ReplayWireIdentity::Partition,
            ReplayWireIdentity::StateSnapshot,
            ReplayWireIdentity::CheckRequest,
            ReplayWireIdentity::LedgerRow,
            ReplayWireIdentity::EvidenceReceipt,
            ReplayWireIdentity::RouteDisplay,
            ReplayWireIdentity::Consultation,
            ReplayWireIdentity::ValidationManifest,
            ReplayWireIdentity::DropAuthorization,
            ReplayWireIdentity::ArtifactReference,
            ReplayWireIdentity::PushRequest,
            ReplayWireIdentity::Response,
        ];
        Bindings {
            identities: kinds
                .into_iter()
                .map(|kind| ((kind, cap("old", kind)), cap("live", kind)))
                .collect(),
            attempts: [
                (PhysicalAttemptId(7), PhysicalAttemptId(23)),
                (PhysicalAttemptId(23), PhysicalAttemptId(7)),
            ]
            .into_iter()
            .collect(),
        }
    }
    fn bytes(value: &Value) -> Vec<u8> {
        serde_json::to_vec(value).unwrap()
    }
    fn clause(side: &str) -> Value {
        json!({"clause_id":7,"record_digest":cap(side,ReplayWireIdentity::CatalogRecord),"formula_digest":"exact-formula","canonical_source":"(op_zR = op_zR)","display":null})
    }
    fn clause_reference(side: &str) -> Value {
        json!({"clause_id":7,"record_digest":cap(side,ReplayWireIdentity::CatalogRecord),"formula_digest":"exact-formula"})
    }
    fn drop_reference(side: &str) -> Value {
        json!({"clause":clause_reference(side),"consultation_digest":cap(side,ReplayWireIdentity::Consultation),"authorization_digest":cap(side,ReplayWireIdentity::DropAuthorization)})
    }
    fn artifact(side: &str) -> Value {
        json!({"stable_id":cap(side,ReplayWireIdentity::ArtifactReference),"role":"failure_diagnostic","kind":"failure_diagnostic"})
    }
    fn failure(side: &str) -> Value {
        json!({"origin":"vampire_race","kind":"process_failure","retryable":true,"scope":"lane_local","has_withheld_detail":true,"artifacts":[artifact(side)],"withheld_artifacts":1})
    }
    fn correction(side: &str) -> Value {
        json!({"schema_version":4,"binding":{"consultation_digest":cap(side,ReplayWireIdentity::Consultation),"rejected_response_digest":cap(side,ReplayWireIdentity::Response),"correction_ordinal":1},"diagnostics":[{"code":"invalid_reference","message":"attempt 7 is invalid","item_index":0,"path":"$.clauses[0]"}]})
    }
    fn push(side: &str) -> Value {
        let binding = json!({"task_digest":"task","scope_digest":"scope","run_digest":cap(side,ReplayWireIdentity::Run),"consultation_digest":cap(side,ReplayWireIdentity::Consultation),"state_snapshot_digest":cap(side,ReplayWireIdentity::StateSnapshot),"validation_manifest_digest":cap(side,ReplayWireIdentity::ValidationManifest)});
        let mut outer = binding.clone();
        outer["validation_ordinal"] = json!(2);
        outer["policy_digest"] = json!("policy");
        let triple = json!({"precondition":"pre","command":"command","postcondition":"post"});
        let presentation = json!({"schema_version":16,"task":{"canonical_id":"task","task_digest":"task","semantic_version":1,"encoding_version":1,"schema":"schema","original":triple,"preprocessed":triple},"ambient_schema":{"scope_digest":"scope","relations":[{"key":"R","arity":1}],"prophecy_map":[{"program_relation":"R","prophecy_relation":"thetaR","arity":1}]},"host_limits":[],"resource_limits":{"api_packet_bytes":67108864,"configured":null},"presentation_digest":"standing"});
        json!({"schema_version":4,"operation":"proposer_observation","binding":outer,"feedback":{"schema_version":10,"binding":binding,"iteration":4,"remaining_search_budget_ns":if side=="old"{"900"}else{"700"},"presentation":presentation,"core":[{"clause":clause(side),"source":"submitted","level":0}],"last_round":[{"clause":clause(side),"source":"symbolic","outcome":{"kind":"dead","cause":"refuted","reason":{"kind":"prophecy_free_initialization_refuted","attempt":7}}}],"pending":[{"clause":clause(side),"source":"submitted","minimum_level":0,"current_level":1,"drop_reference":drop_reference(side)}],"latest":{"kind":"failure","failure":failure(side)},"tools":["countermodel","strongest_refutations","history","ledger","validate_clauses","evaluate_clauses"],"state_revision":5},"correction":correction(side)})
    }
    fn model() -> Value {
        json!({"relations":[{"key":"R","rows":[["data:0"],["data:1"]]}]})
    }
    fn physical(side: &str) -> u64 {
        if side == "old" { 7 } else { 23 }
    }
    fn route(side: &str, kind: &str) -> Value {
        match kind {
            "runtime_proof" => {
                json!({"kind":kind,"profile":"direct","receipt_digest":cap(side,ReplayWireIdentity::EvidenceReceipt),"semantic_vc_digest":"vc","artifacts":[artifact(side)]})
            }
            "protected_theorem" => {
                json!({"kind":kind,"target_vc_digest":"vc","theorem_name":"Whiel.protected","artifact":artifact(side)})
            }
            "validated_refutation" => {
                json!({"kind":kind,"refutation_digest":cap(side,ReplayWireIdentity::EvidenceReceipt),"semantic_vc_digest":"vc","artifacts":[artifact(side)]})
            }
            "retry_progress" => {
                json!({"kind":kind,"progress_digest":cap(side,ReplayWireIdentity::EvidenceReceipt),"semantic_vc_digest":"vc","next_fmb_start_size":2,"previous_proof_allowance_ns":"100","current_proof_allowance_ns":"200","peer_failure":failure(side),"artifacts":[artifact(side)]})
            }
            "suspended" => json!({"kind":kind}),
            _ => panic!("unknown test route"),
        }
    }
    fn row(side: &str, kind: &str) -> Value {
        json!({"kind":"attempt","row_ordinal":7,"clause":clause(side),"level":0,"role":"initialization","request_digest":cap(side,ReplayWireIdentity::CheckRequest),"partition_digest":cap(side,ReplayWireIdentity::Partition),"invalidated":false,"result":{"outcome":{"kind":"inconclusive","reason":"peer_failed"},"route_kind":kind,"route_digest":cap(side,ReplayWireIdentity::RouteDisplay),"route":route(side,kind),"route_summarized":false,"attempt_id":physical(side)},"solver_time_nanos":if side=="old"{10}else{20},"preparation_time_nanos":if side=="old"{30}else{40},"previous_row_digest":null,"row_digest":cap(side,ReplayWireIdentity::LedgerRow)})
    }
    fn ledger(side: &str, kind: &str) -> Value {
        json!({"tool":"ledger","state_revision":5,"result":{"metadata":{"total_items":2,"first_index":1,"returned_items":2,"continuation":"1"},"items":[row(side,kind),{"kind":"invalidation","row_ordinal":8,"invalidated_attempt":7,"target":clause(side),"cause":clause(side),"reason":"antecedent_clause_deleted","previous_row_digest":cap(side,ReplayWireIdentity::LedgerRow),"row_digest":cap(side,ReplayWireIdentity::LedgerRow)}]}})
    }
    fn response(side: &str) -> Value {
        json!({"kind":"candidate_clauses","schema_version":4,"binding":{"task_digest":"task","scope_digest":"scope","run_digest":cap(side,ReplayWireIdentity::Run),"consultation_digest":cap(side,ReplayWireIdentity::Consultation),"state_snapshot_digest":cap(side,ReplayWireIdentity::StateSnapshot),"validation_manifest_digest":cap(side,ReplayWireIdentity::ValidationManifest),"request_digest":cap(side,ReplayWireIdentity::PushRequest),"validation_ordinal":2},"clauses":["(not (empty R))"],"dropped":[drop_reference(side)]})
    }
    fn apply_plan_for_test(mut value: Value, plan: &ReplayWireRebinding) -> Value {
        for replacement in &plan.replacements {
            match replacement {
                ReplayWireReplacement::Identity {
                    path, old, live, ..
                } => {
                    assert_eq!(value.pointer(path).unwrap(), old);
                    *value.pointer_mut(path).unwrap() = json!(live);
                }
                ReplayWireReplacement::PhysicalAttempt { path, old, live } => {
                    assert_eq!(*value.pointer(path).unwrap(), json!(old.0));
                    *value.pointer_mut(path).unwrap() = json!(live.0);
                }
            }
        }
        value
    }
    #[test]
    fn push_compares_complete_semantics_and_records_only_remaining_budget() {
        let old = push("old");
        let live = push("live");
        let b = bindings();
        assert_eq!(
            compare_push(&bytes(&old), &bytes(&live), &b).unwrap(),
            vec![ReplayTimingDifference::RemainingSearchBudget {
                path: "/feedback/remaining_search_budget_ns".into(),
                old: "900".into(),
                live: "700".into()
            }]
        );
        for path in [
            "/binding/task_digest",
            "/binding/policy_digest",
            "/feedback/presentation/task/schema",
            "/feedback/presentation/task/original/command",
            "/feedback/presentation/ambient_schema/prophecy_map/0/prophecy_relation",
            "/feedback/core/0/clause/formula_digest",
            "/feedback/latest/failure/has_withheld_detail",
            "/feedback/latest/failure/withheld_artifacts",
            "/feedback/last_round/0/outcome/reason/attempt",
            "/feedback/pending/0/current_level",
            "/correction/diagnostics/0/message",
        ] {
            let mut bad = live.clone();
            let slot = bad.pointer_mut(path).unwrap();
            *slot = match slot {
                Value::Bool(v) => json!(!*v),
                Value::Number(_) => json!(77),
                _ => json!("changed"),
            };
            assert!(
                compare_push(&bytes(&old), &bytes(&bad), &b).is_err(),
                "{path}"
            );
        }
        let mut bad = live.clone();
        bad["feedback"]["presentation"]["task"]["new_semantic_field"] = json!(0);
        assert!(compare_push(&bytes(&old), &bytes(&bad), &b).is_err());
        // Even equal wire digests need an established owner binding.
        assert!(compare_push(&bytes(&old), &bytes(&old), &Bindings::default()).is_err());
    }
    #[test]
    fn all_ledger_routes_preserve_ordinals_allowances_and_nullable_timing_shape() {
        let b = bindings();
        for kind in [
            "runtime_proof",
            "protected_theorem",
            "validated_refutation",
            "retry_progress",
            "suspended",
        ] {
            let old = ledger("old", kind);
            let live = ledger("live", kind);
            let timing = compare_tool_response(&bytes(&old), &bytes(&live), &b).unwrap();
            assert_eq!(timing.len(), 2);
            assert!(matches!(
                &timing[0],
                ReplayTimingDifference::LedgerSolver {
                    row_ordinal: LedgerRowOrdinal(7),
                    old: Some(10),
                    live: Some(20),
                    ..
                }
            ));
            for path in [
                "/result/items/0/row_ordinal",
                "/result/items/1/invalidated_attempt",
                "/result/items/0/result/outcome/reason",
                "/result/metadata/continuation",
            ] {
                let mut bad = live.clone();
                let slot = bad.pointer_mut(path).unwrap();
                *slot = if slot.is_number() {
                    json!(23)
                } else {
                    json!("changed")
                };
                assert!(
                    compare_tool_response(&bytes(&old), &bytes(&bad), &b).is_err(),
                    "{kind} {path}"
                );
            }
            let mut bad = live.clone();
            bad["result"]["items"][0]["solver_time_nanos"] = Value::Null;
            assert!(compare_tool_response(&bytes(&old), &bytes(&bad), &b).is_err());
            if kind == "retry_progress" {
                for name in ["previous_proof_allowance_ns", "current_proof_allowance_ns"] {
                    let mut bad = live.clone();
                    bad["result"]["items"][0]["result"]["route"][name] = json!("300");
                    assert!(compare_tool_response(&bytes(&old), &bytes(&bad), &b).is_err());
                }
            }
            let mut old = old;
            let mut live = live;
            for value in [&mut old, &mut live] {
                value["result"]["items"][0]["result"]["route"] = Value::Null;
                value["result"]["items"][0]["result"]["route_summarized"] = json!(true);
            }
            assert!(compare_tool_response(&bytes(&old), &bytes(&live), &b).is_ok());
        }
    }
    #[test]
    fn tool_models_and_validation_permute_only_physical_attempts() {
        let b = bindings();
        for termination in [false, true] {
            for retained in [false, true] {
                let fixture = |side| {
                    let mut result = json!({"attempt":physical(side),"role":if termination{"termination"}else{"maintenance"}});
                    if !termination {
                        result["clause"] = clause(side);
                        result["level"] = json!(1);
                    }
                    if retained {
                        result["model"] = model();
                    } else {
                        result["found_not_retained"] = json!({"tuple_count":2,"limit":"countermodel_retention_tuples","value":null});
                    }
                    json!({"tool":"countermodel","state_revision":5,"result":result})
                };
                let old = fixture("old");
                let live = fixture("live");
                assert!(compare_tool_response(&bytes(&old), &bytes(&live), &b).is_ok());
                if retained {
                    let mut bad = live;
                    bad["result"]["model"]["relations"][0]["rows"][0][0] = json!("changed");
                    assert!(compare_tool_response(&bytes(&old), &bytes(&bad), &b).is_err());
                }
            }
        }
        let fixture = |side| json!({"tool":"evaluate_clauses","state_revision":5,"result":{"results":[{"source":"source","admitted":true,"holds":[true,false]},{"source":"invalid","admitted":false,"correctable":{"code":"bad","message":"exact 7","item_index":1,"path":null,"offset":0}}],"instances":(if side=="old"{vec![7,23,7]}else{vec![23,7,23]}).into_iter().enumerate().map(|(i,a)|json!({"kind":"retained","source_index":i,"attempt":a})).collect::<Vec<_>>(),"cost":6,"skipped":[{"kind":"retained","source_index":3,"attempt":physical(side),"tuple_count":0,"reason":"carrier_unavailable"}]}});
        let old = fixture("old");
        let live = fixture("live");
        assert!(compare_tool_response(&bytes(&old), &bytes(&live), &b).is_ok());
        for path in [
            "/result/results/0/source",
            "/result/results/1/correctable/message",
            "/result/results/1/correctable/offset",
            "/result/cost",
        ] {
            let mut bad = live.clone();
            let slot = bad.pointer_mut(path).unwrap();
            *slot = if slot.is_number() {
                json!(9)
            } else {
                json!("different")
            };
            assert!(compare_tool_response(&bytes(&old), &bytes(&bad), &b).is_err());
        }
        let mut bad = live;
        bad["result"]["instances"] = json!([23, 23, 7]);
        assert!(compare_tool_response(&bytes(&old), &bytes(&bad), &b).is_err());
    }
    #[test]
    fn history_strongest_and_latest_cover_nullable_and_status_variants() {
        let b = bindings();
        for status in [
            json!({"kind":"committed","level":0}),
            json!({"kind":"pending","level":1}),
            json!({"kind":"dead","cause":"dropped"}),
            json!({"kind":"dead","cause":"refuted","reason":{"kind":"prophecy_free_initialization_refuted","attempt":7}}),
        ] {
            let history = |side| json!({"tool":"history","state_revision":5,"result":{"clause":clause(side),"origin":"submitted","protected":false,"status":status,"minimum_level":0,"current_level":null,"attempts":[row(side,"runtime_proof")]}});
            assert_eq!(
                compare_tool_response(&bytes(&history("old")), &bytes(&history("live")), &b)
                    .unwrap()
                    .len(),
                2
            );
        }
        let summary = |side, retained| {
            let mut value =
                json!({"attempt":physical(side),"level":0,"role":"unknown","premise_count":2});
            if retained {
                value["model"] = model();
            } else {
                value["found_not_retained"] =
                    json!({"tuple_count":0,"limit":"countermodel_retention_tuples","value":null});
            }
            value
        };
        let strongest = |side| json!({"tool":"strongest_refutations","state_revision":5,"result":{"clause":clause(side),"refutations":[summary(side,true),summary(side,false)]}});
        let old = strongest("old");
        let mut live = strongest("live");
        assert!(compare_tool_response(&bytes(&old), &bytes(&live), &b).is_ok());
        live["result"]["refutations"][0]["premise_count"] = json!(3);
        assert!(compare_tool_response(&bytes(&old), &bytes(&live), &b).is_err());
        for kind in 0..5 {
            let latest = |side| match kind {
                0 => json!({"kind":"initial"}),
                1 => {
                    json!({"kind":"postcondition_open","postcondition_open":{"outcome":"refuted","attempt":physical(side)}})
                }
                2 => {
                    json!({"kind":"postcondition_open","postcondition_open":{"outcome":"refuted","attempt":null}})
                }
                3 => {
                    json!({"kind":"postcondition_open","postcondition_open":{"outcome":"inconclusive","reason":"timed_out"}})
                }
                _ => {
                    json!({"kind":"counterexample_rejected","counterexample_rejected":{"code":"exact","reason":"exact 7"}})
                }
            };
            let mut old = push("old");
            let mut live = push("live");
            old["feedback"]["latest"] = latest("old");
            live["feedback"]["latest"] = latest("live");
            assert!(compare_push(&bytes(&old), &bytes(&live), &b).is_ok());
        }
    }
    #[test]
    fn correction_and_errors_keep_diagnostic_text_exact() {
        let b = bindings();
        let old = correction("old");
        let mut live = correction("live");
        assert!(compare_correction(&bytes(&old), &bytes(&live), &b).is_ok());
        live["diagnostics"][0]["message"] = json!("attempt 23 is invalid");
        assert!(compare_correction(&bytes(&old), &bytes(&live), &b).is_err());
        let old = json!({"tool":"unknown-name","state_revision":0,"error":{"code":"unknown_tool","message":"exact name 7"}});
        assert!(compare_tool_response(&bytes(&old), &bytes(&old), &b).is_ok());
        let mut live = old.clone();
        live["error"]["message"] = json!("exact name 23");
        assert!(compare_tool_response(&bytes(&old), &bytes(&live), &b).is_err());
        let future = json!({"tool":"future_tool","state_revision":0,"result":{"id":"new","content":{"anything":true}}});
        assert!(compare_tool_response(&bytes(&future), &bytes(&future), &b).is_err());
    }
    #[test]
    fn local_skills_have_no_semantic_replay_envelope() {
        let b = bindings();
        let old = json!({"tool":"get_skill","state_revision":0,"result":{"id":"fixture","content":"guidance"}});
        assert!(compare_tool_response(&bytes(&old), &bytes(&old), &b).is_err());
    }

    #[test]
    fn rebind_plans_touch_only_typed_known_echoes() {
        let b = bindings();
        let old = response("old");
        let raw = serde_json::to_vec_pretty(&old).unwrap();
        let saved = raw.clone();
        let plan = rebind_response(&raw, &b);
        assert!(plan.parsed);
        assert_eq!(apply_plan_for_test(old.clone(), &plan), response("live"));
        assert_eq!(raw, saved);
        let mut wrong = old;
        wrong["binding"]["run_digest"] = json!("intentionally wrong");
        wrong["clauses"] = json!([cap("old", ReplayWireIdentity::Consultation)]);
        wrong["dropped"][0]["authorization_digest"] = json!("wrong drop");
        let plan = rebind_response(&bytes(&wrong), &b);
        let rebound = apply_plan_for_test(wrong.clone(), &plan);
        assert_eq!(
            rebound["binding"]["run_digest"],
            wrong["binding"]["run_digest"]
        );
        assert_eq!(rebound["clauses"], wrong["clauses"]);
        assert_eq!(
            rebound["dropped"][0]["authorization_digest"],
            wrong["dropped"][0]["authorization_digest"]
        );
        for bytes in [
            b"{ broken".as_slice(),
            b"{\"schema_version\":4}".as_slice(),
            b"{\"kind\":\"unknown\"}".as_slice(),
        ] {
            let plan = rebind_response(bytes, &b);
            assert!(!plan.parsed);
            assert!(plan.replacements.is_empty());
        }
        let mut wrong = response("old");
        wrong["schema_version"] = json!(999);
        assert!(!rebind_response(&bytes(&wrong), &b).parsed);
        let mut wrong = response("old");
        wrong["extra"] = json!(0);
        assert!(!rebind_response(&bytes(&wrong), &b).parsed);
    }
    #[test]
    fn tool_rebinding_preserves_unknown_attempts_null_absent_and_numeric_cursors() {
        let mut b = bindings();
        b.attempts
            .insert(PhysicalAttemptId(41), PhysicalAttemptId(42));
        assert_eq!(
            b.map_attempt(PhysicalAttemptId(41)).unwrap(),
            PhysicalAttemptId(42)
        );
        let proof_argument = json!({"attempt":41});
        let proof_plan = rebind_tool_arguments("countermodel", &bytes(&proof_argument), &b);
        assert!(proof_plan.parsed);
        assert!(proof_plan.replacements.is_empty());
        let old = json!({"clauses":["exact 7"],"instances":([7,999,23,7]).into_iter().map(|a|json!({"kind":"retained","attempt":a})).collect::<Vec<_>>()});
        let plan = rebind_tool_arguments("evaluate_clauses", &bytes(&old), &b);
        assert_eq!(
            apply_plan_for_test(old, &plan),
            json!({"clauses":["exact 7"],"instances":([23,999,7,23]).into_iter().map(|a|json!({"kind":"retained","attempt":a})).collect::<Vec<_>>()})
        );
        for old in [
            json!({"clauses":[],"instances":"all_retained"}),
            json!({"clauses":[],"instances":[]}),
            json!({"clauses":[],"instances":[{"kind":"supplied","instance":{"carrier_keys":["num:7"],"relations":[]}}]}),
        ] {
            let plan = rebind_tool_arguments("evaluate_clauses", &bytes(&old), &b);
            assert!(plan.parsed);
            assert!(plan.replacements.is_empty());
        }
        for old in [
            json!({}),
            json!({"cursor":null}),
            json!({"cursor":"7"}),
            json!({"cursor":"invalid"}),
        ] {
            let plan = rebind_tool_arguments("ledger", &bytes(&old), &b);
            assert!(plan.parsed);
            assert!(plan.replacements.is_empty());
        }
        for (tool, old) in [
            ("countermodel", json!({"attempt":999})),
            ("validate_clauses", json!({"clauses":["old:Run"]})),
        ] {
            let plan = rebind_tool_arguments(tool, &bytes(&old), &b);
            assert!(plan.parsed);
            assert!(plan.replacements.is_empty());
        }
        for old in [
            json!({}),
            json!({"attempt":null}),
            json!({"attempt":"7"}),
            json!({"attempt":7,"extra":0}),
        ] {
            let plan = rebind_tool_arguments("countermodel", &bytes(&old), &b);
            assert!(!plan.parsed);
            assert!(plan.replacements.is_empty());
        }
        assert!(!rebind_tool_arguments("future_tool", b"{}", &b).parsed);
    }
}
