//! Pass 7.5c consultation-session tool surface.
//!
//! The controller exposes a small, per-consultation tool surface to the
//! provider while it produces its response. This module owns the tool
//! identity/policy vocabulary, the wire shape of one tool call's outcome,
//! the controller-side dispatch table, and the six tool bodies themselves:
//! `countermodel` and `strongest_refutations` read the production checker's
//! semantic dictionary; `history` and `ledger` read the ledger/houdini state
//! view through [`super::feedback::PreCertificateAgentHoudiniState`]. The separate
//! validation and evaluation bodies call the engine-owned Lean adapter; Rust
//! never evaluates a formula itself. Public vocabulary and ingress schemas live
//! in `proposer_api`; skills are C-local. Every body
//! observes the countermodel size bound already enforced by the dictionary
//! and never emits proof text or an artifact path.

use std::sync::Arc;

use serde::Deserialize;
use serde_json::{Value, json};

use crate::artifact::AttemptId;
use crate::houdini::ClauseId;
use crate::proposer_api::queries::{ClauseArgs, CountermodelArgs, LedgerArgs, WireClauseIdentity};
use crate::runtime::SolverAdmission;

use super::admission::FrameworkIIAdmissionContext;
use super::agent::AgentSourceCancellation;
use super::evaluation_ops::{
    ClauseEvaluationResult, FrameworkIIEvaluationError, evaluation_instance_from_countermodel,
};
use super::feedback::{
    AgentClauseIdentity, AgentFeedback, AgentFeedbackError, AgentLedgerFeedback,
    PreCertificateAgentHoudiniState, origin_name, record_clause_identity,
};
use super::host_limits::{HOST_LIMIT_CODE, HostLimitRefusal, HostLimitTruncation, HostLimits};
use super::ledger::{FrameworkIICheckOutcome, LevelAttemptRecord, LevelLedgerRow};
use super::production::{
    FrameworkIICountermodelInstance, FrameworkIIQueryChecker, FrameworkIIRetainedCountermodel,
};
use super::solver::FrameworkIISolverContext;
use super::stabilization::{FrameworkIIDeadCause, LeveledHoudiniState};
use super::types::AdmissionDiagnostic;

pub use crate::proposer_api::queries::{
    AgentTool, AgentToolErrorPayload, AgentToolPolicy, AgentToolResponse, AgentToolResponseFuture,
    AgentToolSurface,
};
use crate::proposer_api::{
    EvaluateClausesArgs, EvaluationSelection, EvaluationSource, ValidateClausesArgs,
};

pub(crate) struct AgentToolResources<'a> {
    feedback: Arc<AgentFeedback>,
    houdini: &'a LeveledHoudiniState,
    feedback_state: &'a PreCertificateAgentHoudiniState,
    // Not read directly: `validate_clauses` Lean-admits its draft clauses
    // through `FrameworkIISolverContext::evaluate_clauses`'s own worker
    // round-trip (`evaluation_ops.rs`), not through this admission context.
    // Threaded through and kept here anyway, matching the plan's read-access
    // wiring and this struct's role as the tool surface's one authority
    // bundle, so a later tool needing direct admission never has to add a
    // new parameter to every call site.
    #[allow(dead_code)]
    admission: &'a FrameworkIIAdmissionContext,
    solver: &'a FrameworkIISolverContext,
    solver_admission: &'a SolverAdmission,
    query: Option<&'a dyn FrameworkIIQueryChecker>,
}

impl<'a> AgentToolResources<'a> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new(
        feedback: Arc<AgentFeedback>,
        houdini: &'a LeveledHoudiniState,
        feedback_state: &'a PreCertificateAgentHoudiniState,
        admission: &'a FrameworkIIAdmissionContext,
        solver: &'a FrameworkIISolverContext,
        solver_admission: &'a SolverAdmission,
        query: Option<&'a dyn FrameworkIIQueryChecker>,
    ) -> Self {
        Self {
            feedback,
            houdini,
            feedback_state,
            admission,
            solver,
            solver_admission,
            query,
        }
    }
}

/// The controller's own [`AgentToolSurface`]: checks staleness, tool
/// recognition, and enablement, then dispatches every enabled tool to its
/// real body.
pub(crate) struct AgentToolDispatcher<'a> {
    policy: AgentToolPolicy,
    state_revision: u64,
    cancellation: AgentSourceCancellation,
    resources: AgentToolResources<'a>,
}

impl<'a> AgentToolDispatcher<'a> {
    pub(crate) fn new(
        policy: AgentToolPolicy,
        state_revision: u64,
        cancellation: AgentSourceCancellation,
        resources: AgentToolResources<'a>,
    ) -> Self {
        Self {
            policy,
            state_revision,
            cancellation,
            resources,
        }
    }
}

impl AgentToolSurface for AgentToolDispatcher<'_> {
    fn call<'a>(&'a self, name: &'a str, args: Value) -> AgentToolResponseFuture<'a> {
        Box::pin(async move {
            let tool =
                match authorize_call(&self.policy, self.state_revision, &self.cancellation, name) {
                    Ok(tool) => tool,
                    Err(response) => return response,
                };
            let outcome = match tool {
                AgentTool::Countermodel => tool_countermodel(&self.resources, args),
                AgentTool::StrongestRefutations => {
                    tool_strongest_refutations(&self.resources, args)
                }
                AgentTool::History => tool_history(&self.resources, args),
                AgentTool::Ledger => tool_ledger(&self.resources, args),
                AgentTool::ValidateClauses => {
                    tool_validate_clauses(&self.resources, args, &self.cancellation).await
                }
                AgentTool::EvaluateClauses => {
                    tool_evaluate_clauses(&self.resources, args, &self.cancellation).await
                }
            };
            match outcome {
                Ok(result) => AgentToolResponse::ok(tool.name(), self.state_revision, result),
                Err(error) => AgentToolResponse::err_with_details(
                    tool.name(),
                    self.state_revision,
                    error.code,
                    error.message,
                    error.host_limit,
                ),
            }
        })
    }
}

fn authorize_call(
    policy: &AgentToolPolicy,
    state_revision: u64,
    cancellation: &AgentSourceCancellation,
    name: &str,
) -> Result<AgentTool, AgentToolResponse> {
    if cancellation.is_cancelled() {
        return Err(AgentToolResponse::err(
            name,
            state_revision,
            "stale_surface",
            "This consultation has ended; the tool surface no longer accepts calls.",
        ));
    }
    let Some(tool) = AgentTool::from_name(name) else {
        return Err(AgentToolResponse::err(
            name,
            state_revision,
            "unknown_tool",
            "This tool name is not recognized.",
        ));
    };
    if !policy.is_enabled(tool) {
        return Err(AgentToolResponse::err(
            name,
            state_revision,
            "tool_disabled",
            "This tool is disabled for the current run.",
        ));
    }
    Ok(tool)
}

// ------------------------------------------------------------
// Tool Argument Errors
// ------------------------------------------------------------

/// One tool body's typed failure, before it is stamped with the tool name
/// and state revision by [`AgentToolDispatcher::call`].
#[derive(Debug)]
pub(super) struct ToolError {
    code: &'static str,
    message: String,
    host_limit: Option<Value>,
}

impl ToolError {
    fn new(code: &'static str, message: impl Into<String>) -> Self {
        Self {
            code,
            message: bounded_diagnostic(&message.into()),
            host_limit: None,
        }
    }

    fn with_details(code: &'static str, message: impl Into<String>, host_limit: Value) -> Self {
        Self {
            code,
            message: bounded_diagnostic(&message.into()),
            host_limit: Some(host_limit),
        }
    }
}

/// Decode one tool's strict argument object (`deny_unknown_fields`); any
/// decode failure becomes `invalid_arguments` naming the offending field, as
/// `serde_json`'s own message already does (a missing/unknown/mistyped
/// field name appears in its `Display` text).
fn decode_args<T: for<'de> Deserialize<'de>>(args: Value) -> Result<T, ToolError> {
    serde_json::from_value(args)
        .map_err(|error| ToolError::new("invalid_arguments", error.to_string()))
}

fn ledger_error(error: AgentFeedbackError) -> ToolError {
    match error {
        AgentFeedbackError::StaleCursor => ToolError::new(
            "invalid_arguments",
            "cursor is stale, foreign, or out of range.",
        ),
        other => ToolError::new("tool_failed", other.to_string()),
    }
}

fn evaluation_error(error: FrameworkIIEvaluationError) -> ToolError {
    match error {
        FrameworkIIEvaluationError::Cancelled => ToolError::new(
            "stale_surface",
            "This consultation ended while evaluation was in flight.",
        ),
        FrameworkIIEvaluationError::InvalidInstance(message) => {
            ToolError::new("invalid_instance", bounded_diagnostic(&message))
        }
        FrameworkIIEvaluationError::Failure(_) => ToolError::new("tool_failed", error.to_string()),
    }
}

// ------------------------------------------------------------
// Shared Clause/Attempt Resolution
// ------------------------------------------------------------

fn identity_wire_value(identity: &AgentClauseIdentity) -> Value {
    identity.wire_value()
}

/// Resolve an exact read reference against this consultation's frozen catalog.
/// This does not confer drop authorization or depend on the displayed subset.
///
/// The returned identity is the catalog's own, so every answer carries the
/// admitted clause text even when the caller referenced the clause by its
/// digests alone. A reference that does carry text must carry this record's
/// text: a disagreement names no clause the controller holds.
fn resolve_clause_arg<'f>(
    feedback: &'f AgentFeedback,
    raw: &WireClauseIdentity,
) -> Result<(&'f super::catalog::LeveledClauseRecord, AgentClauseIdentity), ToolError> {
    let reference = AgentClauseIdentity::from_wire_fields(
        ClauseId::from_catalog_ordinal(raw.clause_id),
        raw.record_digest.clone(),
        raw.formula_digest.clone(),
    );
    let unknown = || ToolError::new("unknown_clause", "This clause identity is not recognized.");
    let record = feedback
        .validation_manifest()
        .resolve_read_clause(&reference)
        .ok_or_else(unknown)?;
    let identity = record_clause_identity(record);
    if identity.contradicted_by(raw.canonical_source.as_deref(), raw.display.as_deref()) {
        return Err(unknown());
    }
    Ok((record, identity))
}

/// The ledger row of `clause`'s own refuted check whose Lean-validated
/// refutation is retained under `attempt` (the exact `AttemptId` scalar the
/// dictionary and [`super::feedback::AgentAttemptOutcome::attempt_id`] share
/// — see that field's own doc). `None` when no such row exists, including
/// when `attempt` never refuted anything.
fn refuted_row_for_attempt(
    houdini: &LeveledHoudiniState,
    attempt: u64,
) -> Option<&LevelAttemptRecord> {
    houdini.attempts().rows().iter().find_map(|row| {
        let LevelLedgerRow::Attempt(record) = row else {
            return None;
        };
        let FrameworkIICheckOutcome::Refuted(evidence) = record.outcome() else {
            return None;
        };
        let refutation = evidence.validated_refutation()?;
        (refutation.attempt().get() == attempt).then_some(record.as_ref())
    })
}

fn model_wire_value(instance: &FrameworkIICountermodelInstance) -> Value {
    json!({
        "relations": instance
            .relations()
            .iter()
            .map(|relation| json!({"key": relation.key(), "rows": relation.rows()}))
            .collect::<Vec<_>>(),
    })
}

/// The tool's view of one retained countermodel: the complete instance by
/// default, or — only when the run sets `countermodel_retention_tuples` and
/// the instance exceeded it — the statement that the countermodel exists,
/// with its tuple count and the limit that kept it out
/// (`agent_houdini.tex`, the `countermodel` tool).
fn countermodel_wire_value(
    model: &FrameworkIIRetainedCountermodel,
    host_limits: &HostLimits,
) -> (&'static str, Value) {
    match model {
        FrameworkIIRetainedCountermodel::Retained(instance) => {
            ("model", model_wire_value(instance))
        }
        FrameworkIIRetainedCountermodel::FoundNotRetained { tuple_count } => (
            "found_not_retained",
            json!({
                "tuple_count": tuple_count,
                "limit": "countermodel_retention_tuples",
                "value": host_limits.countermodel_retention_tuples,
            }),
        ),
    }
}

/// The refusal one `evaluate_clauses` call earns under the run's optional
/// `evaluation_cost` host limit, or `None` when the limit is unset or the
/// call is within it. A product that does not fit in a `usize` is an
/// ordinary tool error, never a host limit.
fn evaluation_cost_refusal(
    host_limits: &HostLimits,
    clauses: usize,
    instances: usize,
) -> Result<Option<HostLimitRefusal>, ToolError> {
    let cost = clauses
        .checked_mul(instances)
        .ok_or_else(|| ToolError::new("malformed_args", "clauses * instances overflowed."))?;
    Ok(host_limits.refusal("evaluation_cost", cost as u64))
}

/// The one error a host limit ever produces in the tool surface: the code is
/// always `host_limit`, and the payload names the limit, its value, and what
/// was observed.
fn host_limit_error(refusal: &HostLimitRefusal) -> ToolError {
    ToolError::with_details(HOST_LIMIT_CODE, refusal.message(), refusal.wire_value())
}

fn diagnostic_wire_value(diagnostic: &AdmissionDiagnostic) -> Value {
    json!({
        "code": diagnostic.code(),
        "message": diagnostic.message(),
        "item_index": diagnostic.item_index(),
        "path": diagnostic.path(),
        "offset": diagnostic.offset(),
    })
}

/// Three current partitions; null represents catalog provenance with no current placement.
/// Rolled-back checks remain readable without inventing a fourth partition.
fn clause_status_wire_value(
    houdini: &LeveledHoudiniState,
    clause: ClauseId,
) -> Result<(Value, Option<u64>), ToolError> {
    Ok(
        if let Some(level) = houdini.committed_levels().get(&clause).copied() {
            (
                json!({"kind": "committed", "level": level.get()}),
                Some(level.get()),
            )
        } else if let Some(cause) = houdini.dead_cause(clause) {
            (
                match cause {
                    FrameworkIIDeadCause::Refuted(reason) => json!({
                        "kind": "dead",
                        "cause": "refuted",
                        "reason": reason.identity_fields(),
                    }),
                    FrameworkIIDeadCause::Dropped => json!({"kind": "dead", "cause": "dropped"}),
                },
                None,
            )
        } else if let Some(level) = houdini.pending_levels().get(&clause).copied() {
            (
                json!({"kind": "pending", "level": level.get()}),
                Some(level.get()),
            )
        } else {
            (Value::Null, None)
        },
    )
}

// ------------------------------------------------------------
// Tool Bodies
// ------------------------------------------------------------

fn tool_countermodel(resources: &AgentToolResources<'_>, args: Value) -> Result<Value, ToolError> {
    let parsed: CountermodelArgs = decode_args(args)?;
    // The commonest way to reach this is a ledger row's `row_ordinal` passed
    // where its `result.attempt_id` belongs. Saying only that the attempt has
    // no refutation states something false about a check that was refuted,
    // and points away from the number that would have worked.
    let no_refutation = || {
        ToolError::new(
            "no_refutation",
            format!(
                "No validated refutation is retained under attempt {}. A history or ledger row's \
                 refuting attempt is its `result.attempt_id`, not its `row_ordinal`; the push's \
                 `postcondition_open.attempt` is already that id.",
                parsed.attempt
            ),
        )
    };
    let model = resources
        .query
        .and_then(|query| query.countermodel_of_attempt(AttemptId::from_u64(parsed.attempt)))
        .ok_or_else(no_refutation)?;
    // A countermodel the run's `countermodel_retention_tuples` limit kept
    // out is answered through the same wire builder as a retained one, so
    // the answer always names the limit and its value rather than leaving
    // the proposer to guess why the instance is missing.
    let (key, value) = countermodel_wire_value(model, resources.feedback.host_limits());
    // A refuted attempt is a clause check or the epoch's termination check.
    // The latter appends no clause ledger row, so it answers with the model
    // alone under the `termination` role.
    let Some(row) = refuted_row_for_attempt(resources.houdini, parsed.attempt) else {
        return Ok(json!({
            "attempt": parsed.attempt,
            "role": "termination",
            key: value,
        }));
    };
    let clause_identity = resources
        .feedback
        .validation_manifest()
        .read_clause_identity(row.request().clause())
        .ok_or_else(no_refutation)?;
    Ok(json!({
        "attempt": parsed.attempt,
        "clause": identity_wire_value(&clause_identity),
        "level": row.request().level().get(),
        "role": row.request().role().to_string(),
        key: value,
    }))
}

fn tool_strongest_refutations(
    resources: &AgentToolResources<'_>,
    args: Value,
) -> Result<Value, ToolError> {
    let parsed: ClauseArgs = decode_args(args)?;
    let (_, identity) = resolve_clause_arg(&resources.feedback, &parsed.clause)?;
    let host_limits = resources.feedback.host_limits();
    // The antichain is complete by default. Only a run that sets the
    // optional `strongest_refutations` host limit sees a shorter list, and
    // then the answer says so.
    let refutations = resources
        .query
        .map(|query| query.strongest_refutations(identity.formula_digest(), None))
        .unwrap_or_default();
    let total = refutations.len();
    let shown = host_limits.shown_of("strongest_refutations", total);
    let truncation =
        HostLimitTruncation::of(host_limits, "refutations", "strongest_refutations", total);
    let entries = refutations[..shown]
        .iter()
        .map(|summary| {
            let attempt = summary.validated_refutation().attempt().get();
            let (level, role) = refuted_row_for_attempt(resources.houdini, attempt)
                .map(|row| {
                    (
                        row.request().level().get(),
                        row.request().role().to_string(),
                    )
                })
                .unwrap_or((0, String::from("unknown")));
            let mut entry = json!({
                "attempt": attempt,
                "level": level,
                "role": role,
                "premise_count": summary.tagged_premises().len(),
            });
            let (key, value) = countermodel_wire_value(summary.countermodel(), host_limits);
            entry[key] = value;
            entry
        })
        .collect::<Vec<_>>();
    let mut answer = json!({
        "clause": identity_wire_value(&identity),
        "refutations": entries,
    });
    if let Some(truncation) = truncation {
        answer
            .as_object_mut()
            .expect("a tool answer is an object")
            .insert("truncated".to_string(), truncation.wire_value());
    }
    Ok(answer)
}

fn tool_history(resources: &AgentToolResources<'_>, args: Value) -> Result<Value, ToolError> {
    read_history(
        &resources.feedback,
        resources.houdini,
        resources.feedback_state,
        args,
    )
}

pub(super) fn read_history(
    feedback: &AgentFeedback,
    houdini: &LeveledHoudiniState,
    feedback_state: &PreCertificateAgentHoudiniState,
    args: Value,
) -> Result<Value, ToolError> {
    let parsed: ClauseArgs = decode_args(args)?;
    let (record, identity) = resolve_clause_arg(feedback, &parsed.clause)?;
    let (status, current_level) = clause_status_wire_value(houdini, identity.clause_id())?;
    // Complete: per-clause history is neither paged nor capped (the
    // ledger page size is the `ledger` tool's page, not a bound here).
    let attempts = feedback_state
        .clause_history_tool(houdini, identity.clause_id())
        .map_err(ledger_error)?;
    // Everything the controller's catalog holds about one clause
    // (`houdini.tex`, "Controller state"): its text, carried by the identity;
    // the origin that placed it and whether it is a protected Lean-issued
    // system row; its Lean-assigned minimum level; where it stands now; and
    // every check ever run on it. `protected` is not inferable from `origin`
    // alone, so the answer states it.
    Ok(json!({
        "clause": identity_wire_value(&identity),
        "origin": origin_name(record.origin()),
        "protected": record.is_protected(),
        "status": status,
        "minimum_level": record.minimum_level().get(),
        "current_level": current_level,
        "attempts": attempts.iter().map(AgentLedgerFeedback::wire_value).collect::<Vec<_>>(),
    }))
}

fn tool_ledger(resources: &AgentToolResources<'_>, args: Value) -> Result<Value, ToolError> {
    read_ledger(resources.houdini, resources.feedback_state, args)
}

pub(super) fn read_ledger(
    houdini: &LeveledHoudiniState,
    feedback_state: &PreCertificateAgentHoudiniState,
    args: Value,
) -> Result<Value, ToolError> {
    let parsed: LedgerArgs = decode_args(args)?;
    let end = parsed
        .cursor
        .map(|cursor| {
            cursor.parse::<usize>().map_err(|_| {
                ToolError::new(
                    "invalid_arguments",
                    "cursor must be the decimal row index a previous page's continuation named.",
                )
            })
        })
        .transpose()?;
    let page = feedback_state
        .ledger_tool_page(houdini, end)
        .map_err(ledger_error)?;
    let continuation =
        (page.metadata().first_index() > 0).then(|| page.metadata().first_index().to_string());
    Ok(json!({
        "metadata": {
            "total_items": page.metadata().total_items(),
            "first_index": page.metadata().first_index(),
            "returned_items": page.metadata().returned_items(),
            "continuation": continuation,
        },
        "items": page.items().iter().map(AgentLedgerFeedback::wire_value).collect::<Vec<_>>(),
    }))
}

fn bounded_diagnostic(message: &str) -> String {
    let mut end = message.len().min(4096);
    while !message.is_char_boundary(end) {
        end -= 1;
    }
    message[..end].to_owned()
}

fn clause_results(results: &[ClauseEvaluationResult], include_truth: bool) -> Vec<Value> {
    results
        .iter()
        .map(|result| match result {
            ClauseEvaluationResult::Evaluated { source, holds, .. } => {
                let mut value = json!({"source": source, "admitted": true});
                if include_truth {
                    value["holds"] = json!(holds);
                }
                value
            }
            ClauseEvaluationResult::Correctable { source, diagnostic } => json!({
                "source": source, "admitted": false,
                "correctable": diagnostic_wire_value(diagnostic),
            }),
        })
        .collect()
}

async fn tool_validate_clauses(
    resources: &AgentToolResources<'_>,
    args: Value,
    cancellation: &AgentSourceCancellation,
) -> Result<Value, ToolError> {
    if args
        .as_object()
        .is_some_and(|args| args.contains_key("instances"))
    {
        return Err(ToolError::new(
            "invalid_arguments",
            "validate_clauses accepts clauses only; use evaluate_clauses for instances.",
        ));
    }
    let parsed: ValidateClausesArgs = decode_args(args)?;
    let evaluation = resources
        .solver
        .evaluate_clauses(
            &parsed.clauses,
            &[],
            resources.solver_admission,
            cancellation.token(),
        )
        .await
        .map_err(evaluation_error)?;
    Ok(json!({"results": clause_results(&evaluation.results, false)}))
}

/// Say what `instances` accepts when it did not decode.
///
/// It is an untagged enum, and `serde_json`'s message for one names a Rust
/// type and no accepted shape — a dead end for a caller whose next move is to
/// guess. Every other decode failure already names its own field, so only
/// this one is rewritten.
fn evaluation_argument_error(error: ToolError) -> ToolError {
    if !error.message.contains("EvaluationSelection") {
        return error;
    }
    ToolError::new(
        "invalid_arguments",
        "`instances` is either the string \"all_retained\" or an array whose entries are \
         {\"kind\": \"retained\", \"attempt\": <number>} or {\"kind\": \"supplied\", \
         \"instance\": {\"carrier_keys\": [...], \"relations\": [{\"name\", \"rows\"}]}}. \
         A single selection object is not an array, and neither is a JSON document encoded \
         into a string.",
    )
}

async fn tool_evaluate_clauses(
    resources: &AgentToolResources<'_>,
    args: Value,
    cancellation: &AgentSourceCancellation,
) -> Result<Value, ToolError> {
    use super::evaluation_ops::{EvaluationInstance, EvaluationRelation};
    let parsed: EvaluateClausesArgs = decode_args(args).map_err(evaluation_argument_error)?;
    let requested = match parsed.instances {
        EvaluationSelection::Sources(sources) => sources,
        EvaluationSelection::All(_) => resources
            .query
            .map(|query| {
                query
                    .retained_countermodel_entries()
                    .map(|(attempt, _)| EvaluationSource::Retained { attempt })
                    .collect()
            })
            .unwrap_or_default(),
    };
    let mut instances = Vec::new();
    let mut labels = Vec::new();
    let mut skipped = Vec::new();
    let has_supplied = requested
        .iter()
        .any(|source| matches!(source, EvaluationSource::Supplied { .. }));
    for (source_index, source) in requested.into_iter().enumerate() {
        match source {
            EvaluationSource::Supplied { instance } => {
                instances.push(EvaluationInstance::new(
                    instance.carrier_keys,
                    instance
                        .relations
                        .into_iter()
                        .map(|relation| {
                            EvaluationRelation::new(
                                relation.name,
                                relation.rows.into_iter().map(|row| json!(row)).collect(),
                            )
                        })
                        .collect(),
                ));
                labels.push(json!({"kind": "supplied", "source_index": source_index}));
            }
            EvaluationSource::Retained { attempt } => {
                let model = resources
                    .query
                    .and_then(|query| query.countermodel_of_attempt(AttemptId::from_u64(attempt)))
                    .ok_or_else(|| {
                        ToolError::new(
                            "no_refutation",
                            format!("Attempt {attempt} has no recorded refutation."),
                        )
                    })?;
                match model {
                    FrameworkIIRetainedCountermodel::FoundNotRetained { tuple_count } => {
                        skipped.push(json!({"kind": "retained", "source_index": source_index,
                            "attempt": attempt, "tuple_count": tuple_count, "reason": "not_retained"}));
                    }
                    FrameworkIIRetainedCountermodel::Retained(instance) => {
                        if let Some(instance) = evaluation_instance_from_countermodel(instance) {
                            instances.push(instance);
                            labels.push(json!({"kind": "retained", "source_index": source_index, "attempt": attempt}));
                        } else {
                            skipped.push(json!({"kind": "retained", "source_index": source_index,
                                "attempt": attempt, "tuple_count": instance.tuple_count(), "reason": "carrier_unavailable"}));
                        }
                    }
                }
            }
        }
    }
    if let Some(refusal) = evaluation_cost_refusal(
        resources.feedback.host_limits(),
        parsed.clauses.len(),
        instances.len(),
    )? {
        return Err(host_limit_error(&refusal));
    }
    // Even an empty clause array validates supplied instances through Lean.
    let evaluation = resources
        .solver
        .evaluate_clauses(
            &parsed.clauses,
            &instances,
            resources.solver_admission,
            cancellation.token(),
        )
        .await
        .map_err(|error| match error {
            FrameworkIIEvaluationError::InvalidInstance(_) if !has_supplied => ToolError::new(
                "tool_failed",
                "A retained model failed the Lean instance codec.",
            ),
            other => evaluation_error(other),
        })?;
    Ok(json!({"results": clause_results(&evaluation.results, true),
        "instances": labels, "cost": evaluation.cost, "skipped": skipped}))
}

// Pass 7.5c: `AgentToolDispatcher::call` now dispatches to real tool bodies
// that read a production checker's dictionary, the ledger/houdini state
// view, and a live worker's `evaluate_clauses` operation through
// `AgentToolResources`. None of those authorities has an in-process fake:
// every one of them (`LeveledHoudiniState`, `PreCertificateAgentHoudiniState`,
// `FrameworkIIAdmissionContext`, `FrameworkIISolverContext`,
// `SolverAdmission`) is constructed only via the live fixed-ambient worker
// binding used throughout `tests/framework2_fixed_ambient.rs`, so — unlike
// the pre-2b stub dispatcher this module used to unit-test directly — the
// dispatch-routing checks (`unknown_tool`, `tool_disabled`, `stale_surface`),
// every tool's argument validation and error code, and the six tool bodies'
// live behavior (including serving a refuted termination check's own
// countermodel, and the pending-clause drop) are exercised there instead:
// `live_epoch_refutes_the_termination_check_and_serves_its_countermodel`
// and `live_consultation_tool_surface_rejects_bad_arguments_and_a_disabled_tool`.
// This module tests the state-free canonical gate directly. Proposer-side tool
// presentation and composition are tested by their owning implementations.
#[cfg(test)]
mod tests {
    use super::*;

    fn dispatch_fixture(
        policy: &AgentToolPolicy,
        revision: u64,
        cancellation: &AgentSourceCancellation,
        args: Value,
    ) -> AgentToolResponse {
        match authorize_call(policy, revision, cancellation, "ledger") {
            Err(error) => error,
            Ok(_) => match decode_args::<LedgerArgs>(args) {
                Ok(_) => AgentToolResponse::ok("ledger", revision, json!({"items": []})),
                Err(error) => AgentToolResponse::err("ledger", revision, error.code, error.message),
            },
        }
    }

    /// The shapes `instances` accepts, in place of a Rust type name.
    #[test]
    fn an_undecodable_instance_selection_names_the_forms_it_accepts() {
        for args in [
            json!({"clauses": [], "instances": {"kind": "retained", "attempt": 17}}),
            json!({"clauses": [], "instances": ["all_retained"]}),
            json!({"clauses": [], "instances": "[{\"kind\":\"retained\"}]"}),
        ] {
            let error =
                evaluation_argument_error(decode_args::<EvaluateClausesArgs>(args).unwrap_err());
            assert_eq!(error.code, "invalid_arguments");
            assert!(error.message.contains("all_retained"), "{}", error.message);
            assert!(error.message.contains("carrier_keys"), "{}", error.message);
            assert!(!error.message.contains("EvaluationSelection"));
        }
        // Every other decode failure keeps the message that already names its
        // own field.
        let error = evaluation_argument_error(
            decode_args::<EvaluateClausesArgs>(json!({"instances": "all_retained"})).unwrap_err(),
        );
        assert!(error.message.contains("clauses"), "{}", error.message);
        assert!(!error.message.contains("all_retained"), "{}", error.message);
    }

    #[test]
    fn each_query_rechecks_current_policy_at_the_same_revision() {
        let token = crate::runtime::CancellationToken::new();
        let cancellation = AgentSourceCancellation::new(token);
        let mut policy = AgentToolPolicy::all_enabled();
        let first = dispatch_fixture(&policy, 91, &cancellation, json!({}));
        assert_eq!(
            first,
            AgentToolResponse::ok("ledger", 91, json!({"items": []}))
        );

        policy = AgentToolPolicy::none_enabled();
        let second = dispatch_fixture(&policy, 91, &cancellation, json!({}));
        assert_eq!(second.error_code(), Some("tool_disabled"));
        assert_eq!(second.state_revision(), first.state_revision());
    }

    #[test]
    fn each_query_rechecks_cancellation_before_name_and_policy() {
        let token = crate::runtime::CancellationToken::new();
        let cancellation = AgentSourceCancellation::new(token.clone());
        let policy = AgentToolPolicy::all_enabled();
        let first = dispatch_fixture(&policy, 91, &cancellation, json!({}));
        assert_eq!(first.error_code(), None);
        token.cancel();

        let second = dispatch_fixture(&policy, 91, &cancellation, json!({}));
        assert_eq!(second.error_code(), Some("stale_surface"));
        assert_eq!(second.state_revision(), first.state_revision());
        for name in ["ledger", "unknown"] {
            let refused = authorize_call(&AgentToolPolicy::none_enabled(), 91, &cancellation, name)
                .unwrap_err();
            assert_eq!(refused.error_code(), Some("stale_surface"));
            assert_eq!(refused.state_revision(), 91);
        }
    }

    #[test]
    fn canonical_gate_keeps_unknown_disabled_and_argument_errors_distinct() {
        let token = crate::runtime::CancellationToken::new();
        let cancellation = AgentSourceCancellation::new(token);
        let unknown = authorize_call(
            &AgentToolPolicy::all_enabled(),
            73,
            &cancellation,
            "unknown",
        )
        .unwrap_err();
        assert_eq!(unknown.error_code(), Some("unknown_tool"));
        assert_eq!(unknown.state_revision(), 73);
        let invalid = dispatch_fixture(
            &AgentToolPolicy::all_enabled(),
            73,
            &cancellation,
            json!({"cursor": 7}),
        );
        assert_eq!(invalid.error_code(), Some("invalid_arguments"));
        assert_eq!(invalid.state_revision(), 73);
        let disabled = dispatch_fixture(
            &AgentToolPolicy::none_enabled(),
            73,
            &cancellation,
            json!({"cursor": 7}),
        );
        assert_eq!(disabled.error_code(), Some("tool_disabled"));
        assert_eq!(disabled.state_revision(), 73);
    }

    #[test]
    fn tool_names_round_trip_through_from_name() {
        for tool in AgentTool::ALL {
            assert_eq!(AgentTool::from_name(tool.name()), Some(tool));
        }
        assert_eq!(AgentTool::from_name("bogus"), None);
    }

    #[test]
    fn default_policy_enables_every_tool_in_order() {
        let policy = AgentToolPolicy::default();
        assert_eq!(
            policy.enabled_names(),
            vec![
                "countermodel",
                "strongest_refutations",
                "history",
                "ledger",
                "validate_clauses",
                "evaluate_clauses",
            ]
        );
    }

    /// Pass 7.7b, item 5: a countermodel the run's retention limit kept out
    /// is answered through the same wire builder as a retained one, so the
    /// answer always names the limit and its value instead of leaving the
    /// proposer to guess why the instance is missing.
    #[test]
    fn a_non_retained_countermodel_names_its_limit_and_value() {
        let limits = HostLimits {
            countermodel_retention_tuples: Some(8),
            ..HostLimits::UNBOUNDED
        };
        let model = FrameworkIIRetainedCountermodel::FoundNotRetained { tuple_count: 9 };
        let (key, value) = countermodel_wire_value(&model, &limits);
        assert_eq!(key, "found_not_retained");
        assert_eq!(
            value,
            json!({
                "tuple_count": 9,
                "limit": "countermodel_retention_tuples",
                "value": 8,
            })
        );
    }

    /// Pass 7.7b, items 6 and 10: `validate_clauses` is refused by the
    /// optional `evaluation_cost` limit on the cost the call would actually
    /// run — drafts times models — and never truncated. An unset limit
    /// refuses nothing at any size.
    #[test]
    fn the_evaluation_cost_refusal_measures_the_whole_product() {
        let refusal = |limits: &HostLimits, clauses, instances| match evaluation_cost_refusal(
            limits, clauses, instances,
        ) {
            Ok(refusal) => refusal,
            Err(_) => panic!("a representable product is not a tool error"),
        };
        let unset = HostLimits::UNBOUNDED;
        assert_eq!(
            refusal(&unset, 1_000, 1_000),
            None,
            "an unset limit refuses nothing"
        );

        let limits = HostLimits {
            evaluation_cost: Some(12),
            ..HostLimits::UNBOUNDED
        };
        assert_eq!(refusal(&limits, 3, 4), None);
        assert_eq!(refusal(&limits, 12, 1), None);
        // One model beyond the product is refused, not silently dropped.
        let refused = refusal(&limits, 3, 5).expect("fifteen exceeds a cost limit of twelve");
        assert_eq!(refused.limit(), "evaluation_cost");
        assert_eq!(refused.value(), 12);
        assert_eq!(refused.observed(), 15);
        assert_eq!(host_limit_error(&refused).code, HOST_LIMIT_CODE);

        // A product that does not fit in a usize is an ordinary tool error,
        // never a host limit.
        assert!(evaluation_cost_refusal(&limits, usize::MAX, 2).is_err());
    }
}
