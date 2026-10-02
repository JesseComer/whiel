//! Strict admission for fixed-ambient values.

use std::collections::{BTreeSet, HashSet};
use std::fmt;
use std::sync::Arc;

use serde::Deserialize;
use serde_json::Value;

use crate::encoding::{
    EncodingError, FixedAmbientEncodingContext, FixedAmbientWorkerOperation, canonical_value_sha256,
};
use crate::failure::{FailureKind, FailureOrigin, FailureReport, FailureScope};
use crate::runtime::{CancellationToken, SolverAdmission};
use crate::task::{ConstantKey, RelationKey, SynthesisTask, TaskIdentity, TaskSchemaKind};

use super::components::{
    FrameworkIIClauseComponents, FrameworkIIComponentFormula, FrameworkIIComponentMetadata,
    FrameworkIIComponentRole, FrameworkIITaskComponents,
};
use super::types::{
    AdmissionCorrection, AdmissionDiagnostic, AdmissionOutcome, ExtendedClause,
    FixedAmbientTaskScope, FrameworkIILevel, FrameworkIIProphecyBinding, FrameworkIIRelation,
};

// No clause-batch item cap: `admit_clauses`, `evaluate_clauses` and
// `prepare_clause_pieces` each carry whatever the caller hands them, and
// Lean admits a batch of any size (`FrameworkII.FixedAmbient.admitClauses`).
// A large batch costs more admission work, which the call-local timeout and
// the run deadline answer as resource guards; the run's optional
// `proposal_size` host limit is the only thing that can refuse one, and it
// is unset by default.

const MAX_DIAGNOSTIC_CODE_BYTES: usize = 128;
const MAX_DIAGNOSTIC_MESSAGE_BYTES: usize = 4096;
const FIXED_AMBIENT_SCOPE_KIND: &str = "whiel_framework_ii_fixed_ambient_task";
const FIXED_AMBIENT_SCOPE_VERSION: u64 = 2;
const FIXED_AMBIENT_CLAUSE_KIND: &str = "whiel_fixed_ambient_clause";
const FIXED_AMBIENT_COMPONENT_KIND: &str = "whiel_framework_ii_fixed_ambient_component";
const QF_FORMULA_KIND: &str = "whiel_qf_formula";
const QF_FORMULA_VERSION: u64 = 3;
const FORMULA_SEMANTIC_THEOREM: &str = "Whiel.QFAssertExpr.toRelCalcSentence_correct";

/// Explicit bootstrap selected by the fixed-ambient registry.
#[derive(Clone, Debug)]
pub struct FixedAmbientTaskBootstrap {
    task: SynthesisTask,
    scope: FixedAmbientTaskScope,
}

impl FixedAmbientTaskBootstrap {
    /// Decode the exact result of the worker's `manifest` command.
    pub fn from_json(value: Value) -> Result<Self, FrameworkIIAdmissionError> {
        let wire: WireDescriptor = decode_payload(value, "fixed-ambient bootstrap")?;
        decode_descriptor(wire)
    }

    pub fn task(&self) -> &SynthesisTask {
        &self.task
    }

    pub fn scope(&self) -> &FixedAmbientTaskScope {
        &self.scope
    }
}

/// Task-scoped admission over the independent V5 worker protocol.
#[derive(Clone)]
pub struct FrameworkIIAdmissionContext {
    encoding: FixedAmbientEncodingContext,
    scope: FixedAmbientTaskScope,
}

impl FrameworkIIAdmissionContext {
    pub fn scope(&self) -> &FixedAmbientTaskScope {
        &self.scope
    }

    pub(super) fn encoding(&self) -> &FixedAmbientEncodingContext {
        &self.encoding
    }

    /// Atomically admit one submitted clause batch through Lean.
    ///
    /// `clause_text_bytes` is the run's optional host limit on one clause's
    /// text, or `None` when the run sets none — the default, under which
    /// Lean's parser applies no bound of its own. The caller has already
    /// refused an oversized clause under this limit with a `host_limit`
    /// correction; sending it here is what keeps the two sides from
    /// disagreeing about the bound in force, and Lean treats reaching it as
    /// an infrastructure fault rather than a defect of the clause.
    pub async fn admit_clauses(
        &self,
        clauses: &[String],
        clause_text_bytes: Option<u64>,
        admission: &SolverAdmission,
        cancellation: &CancellationToken,
    ) -> Result<AdmissionOutcome<Arc<[ExtendedClause]>>, FrameworkIIAdmissionError> {
        let response = self
            .encoding
            .execute(
                admission,
                cancellation,
                FixedAmbientWorkerOperation::AdmitClauses,
                serde_json::json!({
                    "clauses": clauses,
                    "clause_text_bytes": clause_text_bytes,
                }),
            )
            .await
            .map_err(FrameworkIIAdmissionError::from)?;
        let outcome = decode_clause_response(response.payload, &self.scope, clauses.len())?;
        if let AdmissionOutcome::Accepted(clauses) = &outcome {
            self.encoding.extend_name_env(
                std::iter::empty(),
                clauses.iter().flat_map(|clause| {
                    clause
                        .components()
                        .components()
                        .iter()
                        .flat_map(|component| component.formula().constant_keys().iter().cloned())
                }),
            )?;
        }
        Ok(outcome)
    }
}

impl fmt::Debug for FrameworkIIAdmissionContext {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("FrameworkIIAdmissionContext")
            .field("scope", &self.scope)
            .finish_non_exhaustive()
    }
}

/// Bind a bootstrapped scope to a live worker and recheck its descriptor.
pub async fn build_framework_ii_admission(
    encoding: &FixedAmbientEncodingContext,
    bootstrap: &FixedAmbientTaskBootstrap,
    admission: &SolverAdmission,
    cancellation: &CancellationToken,
) -> Result<FrameworkIIAdmissionContext, FrameworkIIAdmissionError> {
    if encoding.task_identity() != bootstrap.task().identity()
        || encoding.scope_identity() != bootstrap.scope().identity()
    {
        return Err(response_validation_failure(
            "fixed-ambient encoding context disagrees with its bootstrap",
        ));
    }
    let response = encoding
        .execute(
            admission,
            cancellation,
            FixedAmbientWorkerOperation::Describe,
            serde_json::json!({}),
        )
        .await
        .map_err(FrameworkIIAdmissionError::from)?;
    let live: WireDescriptor = decode_payload(response.payload, "fixed-ambient descriptor")?;
    let live = decode_descriptor(live)?;
    if live.task().identity() != bootstrap.task().identity() || live.scope() != bootstrap.scope() {
        return Err(response_validation_failure(
            "live fixed-ambient descriptor differs from bootstrap",
        ));
    }
    Ok(FrameworkIIAdmissionContext {
        encoding: encoding.clone(),
        scope: live.scope,
    })
}

#[derive(Clone, Debug)]
pub enum FrameworkIIAdmissionError {
    Cancelled,
    Failure(FailureReport),
}

impl FrameworkIIAdmissionError {
    pub fn failure(&self) -> Option<&FailureReport> {
        match self {
            Self::Cancelled => None,
            Self::Failure(report) => Some(report),
        }
    }
}

impl From<EncodingError> for FrameworkIIAdmissionError {
    fn from(error: EncodingError) -> Self {
        match error {
            EncodingError::Cancelled => Self::Cancelled,
            EncodingError::Failure(report) => Self::Failure(report),
        }
    }
}

impl fmt::Display for FrameworkIIAdmissionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Cancelled => formatter.write_str("fixed-ambient admission was cancelled"),
            Self::Failure(report) => write!(
                formatter,
                "fixed-ambient admission failed: origin={:?} kind={:?} detail={}",
                report.origin(),
                report.kind(),
                report.detail().unwrap_or("none"),
            ),
        }
    }
}

impl std::error::Error for FrameworkIIAdmissionError {}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WireDescriptor {
    task_identity: WireTaskIdentity,
    manifest: Value,
    scope_identity: Value,
    relation_table: Vec<WireRelation>,
    prophecy_bindings: Vec<WireProphecyBinding>,
    task_components: Vec<WireComponentMetadata>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WireTaskIdentity {
    canonical_id: String,
    module: String,
    namespace: String,
    source_sha256: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WireRelation {
    key: String,
    display: String,
    arity: u64,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WireProphecyBinding {
    program_key: String,
    prophecy_key: String,
    arity: u64,
}

#[derive(Deserialize)]
#[serde(tag = "outcome", rename_all = "snake_case", deny_unknown_fields)]
enum WireClauseOutcome {
    Accepted { clauses: Vec<WireClauseResult> },
    Correctable { diagnostic: WireAdmissionDiagnostic },
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct WireClauseResult {
    pub(super) clause: WireExtendedClause,
    pub(super) components: Vec<WireComponentMetadata>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct WireExtendedClause {
    identity: Value,
    order_key: String,
    source: String,
    display: String,
    relation_keys: Vec<String>,
    mentions_prophecy: bool,
    minimum_level: u64,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct WireComponentMetadata {
    component_identity: Value,
    component_digest: String,
    formula: WireComponentFormula,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WireComponentFormula {
    source_id: String,
    formula_identity: Value,
    canonical_source: String,
    display: String,
    relation_keys: Vec<String>,
    constant_keys: Vec<String>,
    semantic_theorem: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WireAdmissionDiagnostic {
    code: String,
    message: String,
    #[serde(default)]
    item_index: Option<u64>,
    #[serde(default)]
    offset: Option<u64>,
}

fn decode_descriptor(
    wire: WireDescriptor,
) -> Result<FixedAmbientTaskBootstrap, FrameworkIIAdmissionError> {
    let manifest = serde_json::to_string(&wire.manifest).map_err(|error| {
        response_validation_failure(format!("serialize fixed-ambient task manifest: {error}",))
    })?;
    let task = SynthesisTask::from_fixed_ambient_json(&manifest).map_err(|error| {
        response_validation_failure(format!("decode fixed-ambient task manifest: {error}",))
    })?;
    if task.schema_kind() != TaskSchemaKind::FixedAmbient
        || !wire_task_matches(&wire.task_identity, task.identity())
    {
        return Err(response_validation_failure(
            "fixed-ambient descriptor task identity is inconsistent",
        ));
    }
    validate_scope_identity(&wire.scope_identity, task.identity())?;
    let relations = decode_relations(wire.relation_table, &task)?;
    let bindings = decode_prophecy_bindings(wire.prophecy_bindings, &relations)?;
    let components = decode_component_bundle(
        wire.task_components,
        &wire.scope_identity,
        &relations,
        None,
        true,
    )?;
    let scope = FixedAmbientTaskScope::admitted(
        task.identity().clone(),
        wire.scope_identity,
        relations,
        bindings,
        FrameworkIITaskComponents::new(components),
    );
    Ok(FixedAmbientTaskBootstrap { task, scope })
}

fn decode_relations(
    rows: Vec<WireRelation>,
    task: &SynthesisTask,
) -> Result<Vec<FrameworkIIRelation>, FrameworkIIAdmissionError> {
    let expected = task
        .solver_relations()
        .iter()
        .map(|row| (row.key().as_str(), row.arity()))
        .collect::<Vec<_>>();
    let received = rows
        .iter()
        .map(|row| (row.key.as_str(), row.arity))
        .collect::<Vec<_>>();
    if received != expected || rows.iter().any(|row| row.display.is_empty()) {
        return Err(response_validation_failure(
            "fixed-ambient relation table differs from the manifest",
        ));
    }
    rows.into_iter()
        .map(|row| {
            Ok(FrameworkIIRelation::new(
                RelationKey::from_lean_scope(row.key).map_err(|error| {
                    response_validation_failure(format!(
                        "invalid opaque ambient relation key: {error}",
                    ))
                })?,
                row.arity,
            ))
        })
        .collect()
}

fn decode_prophecy_bindings(
    rows: Vec<WireProphecyBinding>,
    relations: &[FrameworkIIRelation],
) -> Result<Vec<FrameworkIIProphecyBinding>, FrameworkIIAdmissionError> {
    let relation_arities = relations
        .iter()
        .map(|relation| (relation.key(), relation.arity()))
        .collect::<std::collections::HashMap<_, _>>();
    let mut programs = HashSet::new();
    let mut prophecies = HashSet::new();
    let mut bindings = Vec::with_capacity(rows.len());
    for row in rows {
        let program = RelationKey::from_lean_scope(row.program_key).map_err(|error| {
            response_validation_failure(format!("invalid opaque program-binding key: {error}",))
        })?;
        let prophecy = RelationKey::from_lean_scope(row.prophecy_key).map_err(|error| {
            response_validation_failure(format!("invalid opaque prophecy-binding key: {error}",))
        })?;
        if program == prophecy
            || relation_arities.get(&program) != Some(&row.arity)
            || relation_arities.get(&prophecy) != Some(&row.arity)
            || !programs.insert(program.clone())
            || !prophecies.insert(prophecy.clone())
        {
            return Err(response_validation_failure(
                "fixed-ambient binding is duplicate or arity-inconsistent",
            ));
        }
        bindings.push(FrameworkIIProphecyBinding::new(
            program, prophecy, row.arity,
        ));
    }
    Ok(bindings)
}

fn decode_clause_response(
    payload: Value,
    scope: &FixedAmbientTaskScope,
    submitted_count: usize,
) -> Result<AdmissionOutcome<Arc<[ExtendedClause]>>, FrameworkIIAdmissionError> {
    let wire: WireClauseOutcome = decode_payload(payload, "clause admission")?;
    match wire {
        WireClauseOutcome::Correctable { diagnostic } => Ok(AdmissionOutcome::Correctable(
            AdmissionCorrection::new(vec![validate_diagnostic(diagnostic, submitted_count)?]),
        )),
        WireClauseOutcome::Accepted { clauses } => {
            if clauses.len() > submitted_count {
                return Err(response_validation_failure(
                    "clause admission returned more rows than submitted",
                ));
            }
            let mut identities = HashSet::new();
            let mut decoded = Vec::with_capacity(clauses.len());
            for row in clauses {
                let identity_key = canonical_json(&row.clause.identity)?;
                if !identities.insert(identity_key) {
                    return Err(response_validation_failure(
                        "clause admission repeated a complete identity",
                    ));
                }
                decoded.push(decode_clause(row, scope)?);
            }
            Ok(AdmissionOutcome::Accepted(decoded.into()))
        }
    }
}

pub(super) fn decode_clause(
    row: WireClauseResult,
    scope: &FixedAmbientTaskScope,
) -> Result<ExtendedClause, FrameworkIIAdmissionError> {
    validate_tagged_identity(
        &row.clause.identity,
        FIXED_AMBIENT_CLAUSE_KIND,
        1,
        "fixed-ambient clause",
    )?;
    if row.clause.order_key != canonical_json(&row.clause.identity)?
        || row.clause.source.is_empty()
        || row.clause.display.is_empty()
    {
        return Err(response_validation_failure(
            "fixed-ambient clause has noncanonical or empty source metadata",
        ));
    }
    let relation_keys = validate_relation_keys(
        row.clause.relation_keys,
        scope.relations(),
        "fixed-ambient clause",
    )?;
    let components = decode_component_bundle(
        row.components,
        scope.identity(),
        scope.relations(),
        Some(&row.clause.identity),
        false,
    )?;
    let clause_component = components
        .iter()
        .find(|component| component.role() == FrameworkIIComponentRole::Clause)
        .expect("the exact clause role set was validated");
    if clause_component.formula().canonical_source() != row.clause.source
        || clause_component.formula().relation_keys() != relation_keys.as_slice()
        || clause_component.formula().identity().get("formula")
            != row.clause.identity.get("formula")
    {
        return Err(response_validation_failure(
            "fixed-ambient clause differs from its Lean component authority",
        ));
    }
    Ok(ExtendedClause::admitted(
        scope.clone(),
        row.clause.identity,
        row.clause.order_key,
        row.clause.source,
        row.clause.display,
        relation_keys
            .iter()
            .map(|key| key.as_str().to_owned())
            .collect(),
        FrameworkIILevel::admitted(row.clause.minimum_level),
        row.clause.mentions_prophecy,
        FrameworkIIClauseComponents::new(components),
    ))
}

fn decode_component_bundle(
    rows: Vec<WireComponentMetadata>,
    scope_identity: &Value,
    relations: &[FrameworkIIRelation],
    base_clause_identity: Option<&Value>,
    task_bundle: bool,
) -> Result<Vec<FrameworkIIComponentMetadata>, FrameworkIIAdmissionError> {
    let expected = if task_bundle {
        vec![
            FrameworkIIComponentRole::Precondition,
            FrameworkIIComponentRole::Guard,
            FrameworkIIComponentRole::NegatedThetaGuard,
            FrameworkIIComponentRole::NegatedGuard,
            FrameworkIIComponentRole::Postcondition,
        ]
    } else {
        vec![
            FrameworkIIComponentRole::Clause,
            FrameworkIIComponentRole::ThetaClause,
            FrameworkIIComponentRole::MaintenanceWp,
            FrameworkIIComponentRole::CollapsedClause,
        ]
    };
    if rows.len() != expected.len() {
        return Err(response_validation_failure(
            "fixed-ambient component bundle has the wrong cardinality",
        ));
    }
    let mut components = Vec::with_capacity(rows.len());
    for (wire, expected_role) in rows.into_iter().zip(expected) {
        components.push(decode_component(
            wire,
            expected_role,
            scope_identity,
            relations,
            base_clause_identity,
        )?);
    }
    Ok(components)
}

fn decode_component(
    wire: WireComponentMetadata,
    role: FrameworkIIComponentRole,
    scope_identity: &Value,
    relations: &[FrameworkIIRelation],
    base_clause_identity: Option<&Value>,
) -> Result<FrameworkIIComponentMetadata, FrameworkIIAdmissionError> {
    validate_tagged_identity(
        &wire.component_identity,
        FIXED_AMBIENT_COMPONENT_KIND,
        1,
        "fixed-ambient component",
    )?;
    if canonical_value_sha256(&wire.component_identity) != wire.component_digest {
        return Err(response_validation_failure(
            "fixed-ambient component digest disagrees with its identity",
        ));
    }
    let fields = wire.component_identity.as_object().ok_or_else(|| {
        response_validation_failure("fixed-ambient component identity is not an object")
    })?;
    let expected_fields = if base_clause_identity.is_some() {
        [
            "base_clause_identity",
            "kind",
            "result_formula_identity",
            "role",
            "scope_identity",
            "source_id",
            "version",
        ]
        .as_slice()
    } else {
        [
            "kind",
            "result_formula_identity",
            "role",
            "scope_identity",
            "source_id",
            "version",
        ]
        .as_slice()
    };
    require_exact_fields(fields, expected_fields, "component identity")?;
    if fields.get("scope_identity") != Some(scope_identity)
        || fields.get("role").and_then(Value::as_str) != Some(role.as_str())
        || fields.get("base_clause_identity") != base_clause_identity
        || fields.get("result_formula_identity") != Some(&wire.formula.formula_identity)
        || fields.get("source_id").and_then(Value::as_str) != Some(wire.formula.source_id.as_str())
        || role.is_task() != base_clause_identity.is_none()
    {
        return Err(response_validation_failure(
            "fixed-ambient component identity bindings disagree",
        ));
    }
    validate_tagged_identity(
        &wire.formula.formula_identity,
        QF_FORMULA_KIND,
        QF_FORMULA_VERSION,
        "fixed-ambient QF formula",
    )?;
    if wire.formula.source_id.is_empty()
        || wire.formula.canonical_source.is_empty()
        || wire.formula.display.is_empty()
        || wire.formula.semantic_theorem != FORMULA_SEMANTIC_THEOREM
    {
        return Err(response_validation_failure(
            "fixed-ambient component formula metadata is invalid",
        ));
    }
    let relation_keys = validate_relation_keys(
        wire.formula.relation_keys,
        relations,
        "fixed-ambient component",
    )?;
    let mut seen_constants = HashSet::new();
    let constant_keys = wire
        .formula
        .constant_keys
        .into_iter()
        .map(|key| {
            let key = ConstantKey::from_canonical(key).map_err(|error| {
                response_validation_failure(format!(
                    "invalid fixed-ambient component constant: {error}",
                ))
            })?;
            if !seen_constants.insert(key.clone()) {
                return Err(response_validation_failure(
                    "fixed-ambient component repeats a constant key",
                ));
            }
            Ok(key)
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(FrameworkIIComponentMetadata::new(
        role,
        wire.component_identity,
        wire.component_digest,
        FrameworkIIComponentFormula::new(
            wire.formula.source_id,
            wire.formula.formula_identity,
            wire.formula.canonical_source,
            wire.formula.display,
            relation_keys,
            constant_keys,
            wire.formula.semantic_theorem,
        ),
    ))
}

fn validate_relation_keys(
    raw: Vec<String>,
    relations: &[FrameworkIIRelation],
    label: &str,
) -> Result<Vec<RelationKey>, FrameworkIIAdmissionError> {
    let known = relations
        .iter()
        .map(|relation| relation.key())
        .collect::<HashSet<_>>();
    let mut seen = HashSet::new();
    raw.into_iter()
        .map(|key| {
            let key = RelationKey::from_lean_scope(key).map_err(|error| {
                response_validation_failure(format!(
                    "{label} has an invalid opaque relation key: {error}",
                ))
            })?;
            if !known.contains(&key) || !seen.insert(key.clone()) {
                return Err(response_validation_failure(format!(
                    "{label} has an unknown or duplicate relation key",
                )));
            }
            Ok(key)
        })
        .collect()
}

fn validate_scope_identity(
    identity: &Value,
    task: &TaskIdentity,
) -> Result<(), FrameworkIIAdmissionError> {
    validate_tagged_identity(
        identity,
        FIXED_AMBIENT_SCOPE_KIND,
        FIXED_AMBIENT_SCOPE_VERSION,
        "fixed-ambient task scope",
    )?;
    let fields = identity
        .as_object()
        .expect("tag validation requires an object");
    require_exact_fields(
        fields,
        &[
            "ambient_scope",
            "encoding_version",
            "kind",
            "semantic_version",
            "task_canonical_id",
            "task_module",
            "task_namespace",
            "task_source_sha256",
            "version",
        ],
        "fixed-ambient task scope",
    )?;
    if fields.get("semantic_version").and_then(Value::as_u64) != Some(task.semantic_version())
        || fields.get("encoding_version").and_then(Value::as_u64) != Some(task.encoding_version())
        || fields.get("task_canonical_id").and_then(Value::as_str) != Some(task.canonical_id())
        || fields.get("task_module").and_then(Value::as_str) != Some(task.module())
        || fields.get("task_namespace").and_then(Value::as_str) != Some(task.namespace())
        || fields.get("task_source_sha256").and_then(Value::as_str)
            != Some(task.source_digest().as_str())
        || !matches!(fields.get("ambient_scope"), Some(Value::Array(_)))
    {
        return Err(response_validation_failure(
            "fixed-ambient task scope does not bind its exact task",
        ));
    }
    Ok(())
}

fn validate_tagged_identity(
    identity: &Value,
    kind: &str,
    version: u64,
    label: &str,
) -> Result<(), FrameworkIIAdmissionError> {
    let fields = identity
        .as_object()
        .ok_or_else(|| response_validation_failure(format!("{label} identity is not an object")))?;
    if fields.get("kind").and_then(Value::as_str) != Some(kind)
        || fields.get("version").and_then(Value::as_u64) != Some(version)
    {
        return Err(response_validation_failure(format!(
            "{label} has a retired or unsupported identity tag",
        )));
    }
    Ok(())
}

fn validate_diagnostic(
    wire: WireAdmissionDiagnostic,
    item_count: usize,
) -> Result<AdmissionDiagnostic, FrameworkIIAdmissionError> {
    if wire.code.is_empty()
        || wire.code.len() > MAX_DIAGNOSTIC_CODE_BYTES
        || !wire
            .code
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'-'))
        || wire.message.is_empty()
        || wire.message.len() > MAX_DIAGNOSTIC_MESSAGE_BYTES
    {
        return Err(response_validation_failure(
            "fixed-ambient admission diagnostic is invalid",
        ));
    }
    let item_index = wire
        .item_index
        .map(usize::try_from)
        .transpose()
        .map_err(|_| {
            response_validation_failure("fixed-ambient diagnostic item index overflows usize")
        })?;
    if item_index.is_some_and(|index| index >= item_count) {
        return Err(response_validation_failure(
            "fixed-ambient diagnostic item index is outside the batch",
        ));
    }
    let offset = wire.offset.map(usize::try_from).transpose().map_err(|_| {
        response_validation_failure("fixed-ambient diagnostic offset overflows usize")
    })?;
    Ok(AdmissionDiagnostic::new(
        wire.code,
        wire.message,
        item_index,
        None,
        offset,
    ))
}

fn wire_task_matches(wire: &WireTaskIdentity, task: &TaskIdentity) -> bool {
    wire.canonical_id == task.canonical_id()
        && wire.module == task.module()
        && wire.namespace == task.namespace()
        && wire.source_sha256 == task.source_digest().as_str()
}

fn require_exact_fields(
    fields: &serde_json::Map<String, Value>,
    expected: &[&str],
    label: &str,
) -> Result<(), FrameworkIIAdmissionError> {
    let actual = fields.keys().map(String::as_str).collect::<BTreeSet<_>>();
    let expected = expected.iter().copied().collect::<BTreeSet<_>>();
    if actual != expected {
        return Err(response_validation_failure(format!(
            "{label} fields differ from the V5 contract",
        )));
    }
    Ok(())
}

fn canonical_json(value: &Value) -> Result<String, FrameworkIIAdmissionError> {
    serde_json::to_string(value).map_err(|error| {
        response_validation_failure(format!(
            "serialize fixed-ambient structural identity: {error}",
        ))
    })
}

fn decode_payload<T: for<'de> Deserialize<'de>>(
    payload: Value,
    label: &str,
) -> Result<T, FrameworkIIAdmissionError> {
    serde_json::from_value(payload)
        .map_err(|error| response_validation_failure(format!("decode {label}: {error}")))
}

fn response_validation_failure(detail: impl Into<String>) -> FrameworkIIAdmissionError {
    FrameworkIIAdmissionError::Failure(
        FailureReport::try_new(
            FailureOrigin::ResponseValidation,
            FailureKind::ValidationInfrastructureFailure,
            false,
            FailureScope::RunGlobal,
            Some(detail.into()),
            Vec::new(),
        )
        .expect("fixed-ambient response validation uses an approved failure pair"),
    )
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    /// The batch cap is gone on both sides, and this is the guard against
    /// either side quietly growing one back: Lean's `admitClauses` must
    /// define no item bound, and Rust must mirror none.
    #[test]
    fn neither_side_defines_a_clause_batch_item_cap() {
        let admission = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("whiel_runner lives below the repository root")
            .join("Whiel/Synthesis/FrameworkII/FixedAmbient/Admission.lean");
        let source = std::fs::read_to_string(&admission)
            .unwrap_or_else(|error| panic!("read {}: {error}", admission.display()));
        assert!(
            !source.contains("maxClauseBatchItems"),
            "{} must define no clause-batch item cap",
            admission.display()
        );
        let this_file = include_str!("admission.rs");
        assert!(
            !this_file.contains(concat!("MAX_CLAUSE", "_BATCH_ITEMS")),
            "the Rust mirror of the clause-batch cap must stay removed"
        );
    }
}
