//! Lean-owned direct clause evaluation over supplied finite instances.
//!
//! `evaluate_clauses` is a thin typed wrapper over the `evaluate_clauses`
//! fixed-ambient worker operation
//! (`Whiel/Synthesis/Runtime/FixedAmbientWorker.lean`). It admits and
//! evaluates each clause source independently of any admitted Core, over
//! whatever finite instances the caller supplies. Rust never constructs or
//! interprets clause admission or truth-value semantics; it only builds
//! the request payload and structurally validates the JSON Lean returns.
//!
//! There are no cost caps on either side (Pass 7.7b). Neither Lean nor Rust
//! bounds the draft count, the model count, or their product here. A run
//! that wants a ceiling sets the optional `evaluation_cost` host limit,
//! which refuses an oversized `evaluate_clauses` call in the tool layer
//! before it reaches this wrapper; with no such limit, the run deadline is
//! what bounds the work.

use std::collections::BTreeSet;
use std::fmt;

use serde::Deserialize;
use serde_json::{Value, json};

use crate::encoding::{EncodingError, FixedAmbientEvaluationError, canonical_value_sha256};
use crate::failure::{FailureKind, FailureReport, FailureScope};
use crate::runtime::{CancellationToken, SolverAdmission};

use super::production::FrameworkIICountermodelInstance;
use super::solver::FrameworkIISolverContext;
use super::types::AdmissionDiagnostic;

// ------------------------------------------------------------
// Evaluation Instances
// ------------------------------------------------------------

/// One relation table of a finite instance submitted for evaluation: its
/// ambient relation name and its concrete tuple rows (each row a JSON
/// array of Lean `SolverKey` value-key strings).
#[derive(Clone, Debug, PartialEq)]
pub struct EvaluationRelation {
    name: String,
    rows: Vec<Value>,
}

impl EvaluationRelation {
    pub fn new(name: impl Into<String>, rows: Vec<Value>) -> Self {
        Self {
            name: name.into(),
            rows,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn rows(&self) -> &[Value] {
        &self.rows
    }

    fn to_payload(&self) -> Value {
        json!({"name": self.name, "rows": self.rows})
    }
}

/// One finite instance submitted to `evaluate_clauses`: an explicit
/// carrier and one relation table per ambient relation it names — exactly
/// the shape `FrameworkII.Refutation.decodeInstance` accepts (`carrier_keys`
/// nonempty; `relations` each `{name, rows}`), the same decoder ordinary
/// refutation validation uses.
#[derive(Clone, Debug, PartialEq)]
pub struct EvaluationInstance {
    carrier_keys: Vec<String>,
    relations: Vec<EvaluationRelation>,
}

impl EvaluationInstance {
    pub fn new(carrier_keys: Vec<String>, relations: Vec<EvaluationRelation>) -> Self {
        Self {
            carrier_keys,
            relations,
        }
    }

    pub fn carrier_keys(&self) -> &[String] {
        &self.carrier_keys
    }

    pub fn relations(&self) -> &[EvaluationRelation] {
        &self.relations
    }

    fn to_payload(&self) -> Value {
        json!({
            "carrier_keys": self.carrier_keys,
            "relations": self
                .relations
                .iter()
                .map(EvaluationRelation::to_payload)
                .collect::<Vec<_>>(),
        })
    }
}

/// Build one [`EvaluationInstance`] from a retained countermodel
/// ([`FrameworkIICountermodelInstance`], owned by `production.rs`), using
/// only its public accessors. The carrier is derived as the sorted,
/// deduplicated set of value keys actually referenced by the countermodel's
/// relation rows — the same values Lean's own carrier-membership check
/// (`decodeCarrier`/`validateRelationCells`) would already require to be
/// present. Returns `None` when no such key exists (every relation is
/// empty), since Lean's decoder requires a nonempty carrier and a retained
/// countermodel does not otherwise expose one.
pub fn evaluation_instance_from_countermodel(
    instance: &FrameworkIICountermodelInstance,
) -> Option<EvaluationInstance> {
    let mut carrier = BTreeSet::new();
    for relation in instance.relations() {
        for row in relation.rows() {
            if let Some(cells) = row.as_array() {
                for cell in cells {
                    if let Some(key) = cell.as_str() {
                        carrier.insert(key.to_string());
                    }
                }
            }
        }
    }
    if carrier.is_empty() {
        return None;
    }
    let relations = instance
        .relations()
        .iter()
        .map(|relation| {
            EvaluationRelation::new(relation.key().to_string(), relation.rows().to_vec())
        })
        .collect();
    Some(EvaluationInstance::new(
        carrier.into_iter().collect(),
        relations,
    ))
}

// ------------------------------------------------------------
// Evaluation Results
// ------------------------------------------------------------

/// One clause's outcome from `evaluate_clauses`.
#[derive(Clone, Debug, PartialEq)]
pub enum ClauseEvaluationResult {
    /// The clause was admitted; `holds[i]` is its truth value on the `i`th
    /// submitted instance.
    Evaluated {
        identity_sha256: String,
        source: String,
        holds: Vec<bool>,
    },
    /// The clause source was not admissible over the ambient schema.
    Correctable {
        source: String,
        diagnostic: AdmissionDiagnostic,
    },
}

/// Complete in-memory result of one `evaluate_clauses` request.
#[derive(Clone, Debug, PartialEq)]
pub struct ClauseEvaluation {
    pub results: Vec<ClauseEvaluationResult>,
    pub instances: usize,
    pub cost: usize,
}

// ------------------------------------------------------------
// Strict Worker Response
// ------------------------------------------------------------

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WireClauseEvaluation {
    results: Vec<Value>,
    instances: u64,
    cost: u64,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WireEvaluationDiagnostic {
    code: String,
    message: String,
    #[serde(default)]
    item_index: Option<u64>,
    #[serde(default)]
    offset: Option<u64>,
}

fn decode_evaluation_diagnostic(
    value: Value,
) -> Result<AdmissionDiagnostic, FrameworkIIEvaluationError> {
    let wire: WireEvaluationDiagnostic = decode_payload(value, "evaluate_clauses diagnostic")?;
    if wire.code.is_empty() || wire.message.is_empty() {
        return Err(validation_failure(
            "evaluate_clauses correctable diagnostic is invalid",
        ));
    }
    let item_index = wire
        .item_index
        .map(usize::try_from)
        .transpose()
        .map_err(|_| {
            validation_failure("evaluate_clauses diagnostic item index overflows usize")
        })?;
    let offset =
        wire.offset.map(usize::try_from).transpose().map_err(|_| {
            validation_failure("evaluate_clauses diagnostic offset overflows usize")
        })?;
    Ok(AdmissionDiagnostic::new(
        wire.code,
        wire.message,
        item_index,
        None,
        offset,
    ))
}

fn decode_clause_evaluation_result(
    value: Value,
    instance_count: usize,
) -> Result<ClauseEvaluationResult, FrameworkIIEvaluationError> {
    let object = value
        .as_object()
        .ok_or_else(|| validation_failure("evaluate_clauses result entry is not an object"))?;
    let keys: BTreeSet<&str> = object.keys().map(String::as_str).collect();
    if keys == BTreeSet::from(["clause", "source", "holds"]) {
        let clause = object["clause"].clone();
        let source = object["source"]
            .as_str()
            .ok_or_else(|| {
                validation_failure("evaluate_clauses evaluated result source is not a string")
            })?
            .to_string();
        if clause.get("source").and_then(Value::as_str) != Some(source.as_str()) {
            return Err(validation_failure(
                "evaluate_clauses evaluated result clause disagrees with its own source",
            ));
        }
        let holds: Vec<bool> =
            serde_json::from_value(object["holds"].clone()).map_err(|error| {
                validation_failure(format!("decode evaluate_clauses holds: {error}"))
            })?;
        if holds.len() != instance_count {
            return Err(validation_failure(
                "evaluate_clauses evaluated result holds length disagrees with the instance count",
            ));
        }
        let identity_sha256 = canonical_value_sha256(&clause);
        Ok(ClauseEvaluationResult::Evaluated {
            identity_sha256,
            source,
            holds,
        })
    } else if keys == BTreeSet::from(["source", "correctable"]) {
        let source = object["source"]
            .as_str()
            .ok_or_else(|| {
                validation_failure("evaluate_clauses correctable result source is not a string")
            })?
            .to_string();
        let diagnostic = decode_evaluation_diagnostic(object["correctable"].clone())?;
        Ok(ClauseEvaluationResult::Correctable { source, diagnostic })
    } else {
        Err(validation_failure(
            "evaluate_clauses result entry has unsupported fields",
        ))
    }
}

fn decode_clause_evaluation(
    payload: Value,
    clause_count: usize,
    instance_count: usize,
) -> Result<ClauseEvaluation, FrameworkIIEvaluationError> {
    let wire: WireClauseEvaluation = decode_payload(payload, "evaluate_clauses response")?;
    if wire.instances as usize != instance_count {
        return Err(validation_failure(
            "evaluate_clauses response echoed a different instance count",
        ));
    }
    let expected_cost = clause_count
        .checked_mul(instance_count)
        .ok_or_else(|| validation_failure("evaluate_clauses cost overflows usize"))?;
    if wire.cost as usize != expected_cost {
        return Err(validation_failure(
            "evaluate_clauses response echoed a different cost",
        ));
    }
    if wire.results.len() != clause_count {
        return Err(validation_failure(
            "evaluate_clauses response does not carry one result per submitted clause",
        ));
    }
    let results = wire
        .results
        .into_iter()
        .map(|entry| decode_clause_evaluation_result(entry, instance_count))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(ClauseEvaluation {
        results,
        instances: instance_count,
        cost: expected_cost,
    })
}

/// The exact cost of one `evaluate_clauses` request,
/// `clause_count * instance_count`.
///
/// There is no built-in bound on either factor or on the product: an
/// optional host `evaluation_cost` limit, refused in the tool layer as
/// `host_limit`, is the only limit, and it is unset by default. The cost is
/// still computed because the worker echoes it back and the response is
/// checked against it.
pub fn evaluation_cost(
    clause_count: usize,
    instance_count: usize,
) -> Result<usize, FrameworkIIEvaluationError> {
    clause_count
        .checked_mul(instance_count)
        .ok_or_else(|| validation_failure("evaluate_clauses cost overflows usize"))
}

// ------------------------------------------------------------
// Worker Operation
// ------------------------------------------------------------

impl FrameworkIISolverContext {
    /// Evaluate a batch of clause sources against a batch of finite
    /// instances, independent of any admitted Core: Lean admits each
    /// clause source over the ambient schema and reports its truth value
    /// on every instance, or a per-clause correctable diagnostic when a
    /// source is not admissible. `results.len() == clauses.len()` and,
    /// for every [`ClauseEvaluationResult::Evaluated`],
    /// `holds.len() == instances.len()`.
    ///
    /// Cost is `clauses.len() * instances.len()`. Neither the clause count,
    /// the instance count, nor the product is bounded here: the run's
    /// optional `evaluation_cost` host limit is applied in the tool layer
    /// and is unset by default.
    pub async fn evaluate_clauses(
        &self,
        clauses: &[String],
        instances: &[EvaluationInstance],
        admission: &SolverAdmission,
        cancellation: &CancellationToken,
    ) -> Result<ClauseEvaluation, FrameworkIIEvaluationError> {
        evaluation_cost(clauses.len(), instances.len())?;
        let payload = json!({
            "clauses": clauses,
            "instances": instances
                .iter()
                .map(EvaluationInstance::to_payload)
                .collect::<Vec<_>>(),
        });
        let response = self
            .encoding()
            .execute_evaluation(admission, cancellation, payload)
            .await
            .map_err(FrameworkIIEvaluationError::from)?;
        decode_clause_evaluation(response.payload, clauses.len(), instances.len())
    }
}

// ------------------------------------------------------------
// Errors
// ------------------------------------------------------------

fn decode_payload<T: for<'de> Deserialize<'de>>(
    value: Value,
    label: &str,
) -> Result<T, FrameworkIIEvaluationError> {
    serde_json::from_value(value)
        .map_err(|error| validation_failure(format!("decode {label}: {error}")))
}

fn validation_failure(detail: impl Into<String>) -> FrameworkIIEvaluationError {
    FrameworkIIEvaluationError::Failure(FailureReport::encoding_preparation(
        FailureKind::MalformedResult,
        FailureScope::RunGlobal,
        detail,
    ))
}

#[derive(Clone, Debug)]
pub enum FrameworkIIEvaluationError {
    Cancelled,
    /// Lean rejected the supplied instance structure; no semantic claim was checked.
    InvalidInstance(String),
    Failure(FailureReport),
}

impl FrameworkIIEvaluationError {
    pub fn failure(&self) -> Option<&FailureReport> {
        match self {
            Self::Cancelled | Self::InvalidInstance(_) => None,
            Self::Failure(report) => Some(report),
        }
    }
}

impl From<EncodingError> for FrameworkIIEvaluationError {
    fn from(error: EncodingError) -> Self {
        match error {
            EncodingError::Cancelled => Self::Cancelled,
            EncodingError::Failure(report) => Self::Failure(report),
        }
    }
}

impl From<FixedAmbientEvaluationError> for FrameworkIIEvaluationError {
    fn from(error: FixedAmbientEvaluationError) -> Self {
        match error {
            FixedAmbientEvaluationError::InvalidInstance(message) => Self::InvalidInstance(message),
            FixedAmbientEvaluationError::Encoding(error) => error.into(),
        }
    }
}

impl fmt::Display for FrameworkIIEvaluationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Cancelled => formatter.write_str("fixed-ambient clause evaluation was cancelled"),
            Self::InvalidInstance(message) => {
                write!(formatter, "Invalid evaluation instance: {message}")
            }
            Self::Failure(report) => write!(
                formatter,
                "fixed-ambient clause evaluation failed: origin={:?} kind={:?} detail={}",
                report.origin(),
                report.kind(),
                report.detail().unwrap_or("none")
            ),
        }
    }
}

impl std::error::Error for FrameworkIIEvaluationError {}

// ------------------------------------------------------------
// Tests
// ------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn instance_admission_is_a_structured_input_error_without_failure_report() {
        let error = FrameworkIIEvaluationError::from(FixedAmbientEvaluationError::InvalidInstance(
            "missing relation o:p::R".into(),
        ));
        assert!(matches!(
            &error,
            FrameworkIIEvaluationError::InvalidInstance(message)
                if message == "missing relation o:p::R"
        ));
        assert!(error.failure().is_none());
        assert_eq!(
            error.to_string(),
            "Invalid evaluation instance: missing relation o:p::R"
        );
    }

    #[test]
    fn evaluation_encoding_conversion_preserves_cancellation_and_failure() {
        let cancelled = FrameworkIIEvaluationError::from(FixedAmbientEvaluationError::Encoding(
            EncodingError::Cancelled,
        ));
        assert!(matches!(cancelled, FrameworkIIEvaluationError::Cancelled));
        assert!(cancelled.failure().is_none());

        let report = FailureReport::encoding_preparation(
            FailureKind::InfrastructureFailure,
            FailureScope::RunGlobal,
            "instance_admission: diagnostic text is not an error classification",
        );
        let error = FrameworkIIEvaluationError::from(FixedAmbientEvaluationError::Encoding(
            EncodingError::Failure(report.clone()),
        ));
        let retained = error
            .failure()
            .expect("infrastructure report remains available");
        assert_eq!(retained.origin(), report.origin());
        assert_eq!(retained.kind(), report.kind());
        assert_eq!(retained.scope(), report.scope());
        assert_eq!(retained.detail(), report.detail());
    }

    fn sample_instance() -> EvaluationInstance {
        EvaluationInstance::new(
            vec!["num:1".to_string()],
            vec![EvaluationRelation::new(
                "o:p::E",
                vec![json!(["num:1", "num:1"])],
            )],
        )
    }

    fn sample_evaluated_entry() -> Value {
        json!({
            "clause": {
                "identity": {"kind": "whiel_fixed_ambient_clause", "version": 1},
                "order_key": "order",
                "source": "(op_zT = \u{2205}[2])",
                "display": "display",
                "relation_keys": ["o:p::T"],
                "mentions_prophecy": false,
                "minimum_level": 0,
            },
            "source": "(op_zT = \u{2205}[2])",
            "holds": [true, false],
        })
    }

    #[test]
    fn evaluation_instance_payload_carries_carrier_keys_and_named_relations() {
        let payload = sample_instance().to_payload();
        assert_eq!(payload["carrier_keys"], json!(["num:1"]));
        assert_eq!(
            payload["relations"],
            json!([{"name": "o:p::E", "rows": [["num:1", "num:1"]]}])
        );
    }

    // `evaluation_instance_from_countermodel` takes a
    // `FrameworkIICountermodelInstance` (`production.rs`), which exposes no
    // public constructor of its own (only `production.rs`'s private
    // `build_retained_countermodel`, reached through a live refutation);
    // its live behavior is exercised indirectly whenever a caller derives
    // an [`EvaluationInstance`] from a real retained countermodel, and its
    // pure logic — sorted, deduplicated carrier keys plus a `{name, rows}`
    // relation per table — mirrors `evaluation_instance_payload_carries_*`
    // above, which covers the identical payload shape built by hand.

    #[test]
    fn decodes_an_evaluated_result() {
        let decoded = decode_clause_evaluation_result(sample_evaluated_entry(), 2).unwrap();
        match decoded {
            ClauseEvaluationResult::Evaluated { source, holds, .. } => {
                assert_eq!(source, "(op_zT = \u{2205}[2])");
                assert_eq!(holds, vec![true, false]);
            }
            other => panic!("expected Evaluated, got {other:?}"),
        }
    }

    #[test]
    fn decodes_a_correctable_result() {
        let entry = json!({
            "source": "not a clause",
            "correctable": {"code": "clause_syntax_error", "message": "bad", "offset": 3},
        });
        let decoded = decode_clause_evaluation_result(entry, 1).unwrap();
        match decoded {
            ClauseEvaluationResult::Correctable { source, diagnostic } => {
                assert_eq!(source, "not a clause");
                assert_eq!(diagnostic.code(), "clause_syntax_error");
                assert_eq!(diagnostic.offset(), Some(3));
            }
            other => panic!("expected Correctable, got {other:?}"),
        }
    }

    #[test]
    fn rejects_a_mismatched_holds_length() {
        let entry = sample_evaluated_entry();
        assert!(decode_clause_evaluation_result(entry, 3).is_err());
    }

    #[test]
    fn rejects_an_unknown_field_in_a_result_entry() {
        let mut entry = sample_evaluated_entry();
        entry["unexpected"] = json!(true);
        assert!(decode_clause_evaluation_result(entry, 2).is_err());
    }

    #[test]
    fn rejects_a_result_entry_whose_clause_disagrees_with_its_own_source() {
        let mut entry = sample_evaluated_entry();
        entry["clause"]["source"] = json!("different");
        assert!(decode_clause_evaluation_result(entry, 2).is_err());
    }

    #[test]
    fn decodes_a_well_formed_response() {
        let payload = json!({
            "results": [sample_evaluated_entry()],
            "instances": 2,
            "cost": 2,
        });
        let decoded = decode_clause_evaluation(payload, 1, 2).unwrap();
        assert_eq!(decoded.results.len(), 1);
        assert_eq!(decoded.instances, 2);
        assert_eq!(decoded.cost, 2);
    }

    #[test]
    fn rejects_a_response_with_the_wrong_result_count() {
        let payload = json!({
            "results": [sample_evaluated_entry(), sample_evaluated_entry()],
            "instances": 2,
            "cost": 2,
        });
        assert!(decode_clause_evaluation(payload, 1, 2).is_err());
    }

    #[test]
    fn rejects_a_response_with_an_unknown_field() {
        let payload = json!({
            "results": [sample_evaluated_entry()],
            "instances": 2,
            "cost": 2,
            "unexpected": true,
        });
        assert!(decode_clause_evaluation(payload, 1, 2).is_err());
    }

    #[test]
    fn reports_the_exact_cost_of_a_batch() {
        assert_eq!(evaluation_cost(2, 2).unwrap(), 4);
    }

    /// No clause count, instance count, or product is refused here. The old
    /// 128/64/4096 caps are gone; only the run's optional `evaluation_cost`
    /// host limit can refuse a call, and it is unset by default.
    #[test]
    fn no_clause_or_instance_count_is_refused_by_the_cost_computation() {
        assert_eq!(evaluation_cost(4_096, 1).unwrap(), 4_096);
        assert_eq!(evaluation_cost(1, 4_096).unwrap(), 4_096);
        assert_eq!(evaluation_cost(65, 64).unwrap(), 4_160);
        assert_eq!(evaluation_cost(10_000, 10_000).unwrap(), 100_000_000);
    }

    /// The one arithmetic guard that stays: a product that does not fit in
    /// a `usize` is an infrastructure failure, not a host limit.
    #[test]
    fn an_overflowing_cost_is_a_failure() {
        assert!(evaluation_cost(usize::MAX, 2).is_err());
    }
}
