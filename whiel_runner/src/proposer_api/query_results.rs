//! Closed query reply DTOs shared by clients and transcript conformance checks.

use super::observation::*;
use serde::{Deserialize, Serialize};
use serde_json::Value;

fn decimal_nanos<'de, D: serde::Deserializer<'de>>(deserializer: D) -> Result<String, D::Error> {
    let value = String::deserialize(deserializer)?;
    match value.parse::<u128>() {
        Ok(nanos) if nanos.to_string() == value => Ok(value),
        _ => Err(serde::de::Error::custom(
            "nanoseconds must be a canonical unsigned decimal string",
        )),
    }
}

fn nullable<'de, D, T>(deserializer: D) -> Result<Option<T>, D::Error>
where
    D: serde::Deserializer<'de>,
    T: Deserialize<'de>,
{
    Option::<T>::deserialize(deserializer)
}
fn present<'de, D, T>(deserializer: D) -> Result<Option<T>, D::Error>
where
    D: serde::Deserializer<'de>,
    T: Deserialize<'de>,
{
    T::deserialize(deserializer).map(Some)
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CountermodelArgumentsV1 {
    pub attempt: PhysicalAttemptId,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ClauseArgumentsV1 {
    pub clause: ClauseArgumentV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LedgerArgumentsV1 {
    #[serde(default, skip_serializing_if = "PresenceV1::is_absent")]
    pub cursor: PresenceV1<String>,
}

pub use crate::proposer_api::{
    EvaluateClausesArgs as EvaluateArgumentsV1, ValidateClausesArgs as ValidateArgumentsV1,
};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ToolErrorV1 {
    pub code: String,
    pub message: String,
    #[serde(
        default,
        deserialize_with = "present",
        skip_serializing_if = "Option::is_none"
    )]
    pub host_limit: Option<RefusalV1>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ErrorEnvelopeV1 {
    pub tool: String,
    pub state_revision: u64,
    pub error: ToolErrorV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SuccessEnvelopeV1<T> {
    pub tool: ToolV1,
    pub state_revision: u64,
    pub result: T,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ModelV1 {
    pub relations: Vec<ModelRelationV1>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ModelRelationV1 {
    pub key: String,
    pub rows: Vec<Vec<String>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CountermodelRetentionLimitV1 {
    CountermodelRetentionTuples,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NotRetainedV1 {
    pub tuple_count: u64,
    pub limit: CountermodelRetentionLimitV1,
    #[serde(deserialize_with = "nullable")]
    pub value: Option<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ClauseCountermodelV1Retained {
    pub attempt: PhysicalAttemptId,
    pub clause: ClauseV1,
    pub level: u64,
    pub role: RoleV1,
    pub model: ModelV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ClauseCountermodelV1Unavailable {
    pub attempt: PhysicalAttemptId,
    pub clause: ClauseV1,
    pub level: u64,
    pub role: RoleV1,
    pub found_not_retained: NotRetainedV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum ClauseCountermodelV1 {
    Retained(ClauseCountermodelV1Retained),
    Unavailable(ClauseCountermodelV1Unavailable),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TerminationCountermodelV1Retained {
    pub attempt: PhysicalAttemptId,
    pub role: TerminationRoleV1,
    pub model: ModelV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TerminationCountermodelV1Unavailable {
    pub attempt: PhysicalAttemptId,
    pub role: TerminationRoleV1,
    pub found_not_retained: NotRetainedV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum TerminationCountermodelV1 {
    Retained(TerminationCountermodelV1Retained),
    Unavailable(TerminationCountermodelV1Unavailable),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RefutationSummaryV1Retained {
    pub attempt: PhysicalAttemptId,
    pub level: u64,
    pub role: SummaryRoleV1,
    pub premise_count: u64,
    pub model: ModelV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RefutationSummaryV1Unavailable {
    pub attempt: PhysicalAttemptId,
    pub level: u64,
    pub role: SummaryRoleV1,
    pub premise_count: u64,
    pub found_not_retained: NotRetainedV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum RefutationSummaryV1 {
    Retained(RefutationSummaryV1Retained),
    Unavailable(RefutationSummaryV1Unavailable),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TerminationRoleV1 {
    Termination,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SummaryRoleV1 {
    Initialization,
    Maintenance,
    Unknown,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum CountermodelV1 {
    Clause(ClauseCountermodelV1),
    Termination(TerminationCountermodelV1),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct StrongestRefutationsV1 {
    pub clause: ClauseV1,
    pub refutations: Vec<RefutationSummaryV1>,
    #[serde(
        default,
        deserialize_with = "present",
        skip_serializing_if = "Option::is_none"
    )]
    pub truncated: Option<TruncationV1>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", deny_unknown_fields, rename_all = "snake_case")]
pub enum OutcomeV1 {
    Proved {},
    Refuted {},
    Inconclusive { reason: InconclusiveReasonV1 },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", deny_unknown_fields, rename_all = "snake_case")]
pub enum RouteV1 {
    RuntimeProof {
        profile: ProfileV1,
        receipt_digest: String,
        semantic_vc_digest: String,
        artifacts: Vec<ArtifactV1>,
    },
    ProtectedTheorem {
        target_vc_digest: String,
        theorem_name: String,
        artifact: ArtifactV1,
    },
    ValidatedRefutation {
        refutation_digest: String,
        semantic_vc_digest: String,
        artifacts: Vec<ArtifactV1>,
    },
    RetryProgress {
        progress_digest: String,
        semantic_vc_digest: String,
        #[serde(deserialize_with = "nullable")]
        next_fmb_start_size: Option<u64>,
        #[serde(deserialize_with = "decimal_nanos")]
        previous_proof_allowance_ns: String,
        #[serde(deserialize_with = "decimal_nanos")]
        current_proof_allowance_ns: String,
        #[serde(deserialize_with = "nullable")]
        peer_failure: Option<FailureV1>,
        artifacts: Vec<ArtifactV1>,
    },
    Suspended {},
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RouteKindV1 {
    RuntimeProof,
    ProtectedTheorem,
    ValidatedRefutation,
    RetryProgress,
    Suspended,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AttemptResultV1 {
    pub outcome: OutcomeV1,
    pub route_kind: RouteKindV1,
    pub route_digest: String,
    #[serde(deserialize_with = "nullable")]
    pub route: Option<RouteV1>,
    pub route_summarized: bool,
    #[serde(deserialize_with = "nullable")]
    pub attempt_id: Option<PhysicalAttemptId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", deny_unknown_fields, rename_all = "snake_case")]
pub enum LedgerRowV1 {
    Attempt {
        row_ordinal: LedgerRowOrdinal,
        clause: ClauseV1,
        level: u64,
        role: RoleV1,
        request_digest: String,
        partition_digest: String,
        invalidated: bool,
        result: Box<AttemptResultV1>,
        #[serde(deserialize_with = "nullable")]
        solver_time_nanos: Option<u64>,
        #[serde(deserialize_with = "nullable")]
        preparation_time_nanos: Option<u64>,
        #[serde(deserialize_with = "nullable")]
        previous_row_digest: Option<String>,
        row_digest: String,
    },
    Invalidation {
        row_ordinal: LedgerRowOrdinal,
        invalidated_attempt: LedgerRowOrdinal,
        target: ClauseV1,
        #[serde(deserialize_with = "nullable")]
        cause: Option<ClauseV1>,
        reason: InvalidationReasonV1,
        #[serde(deserialize_with = "nullable")]
        previous_row_digest: Option<String>,
        row_digest: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", deny_unknown_fields, rename_all = "snake_case")]
pub enum AttemptRowV1 {
    Attempt {
        row_ordinal: LedgerRowOrdinal,
        clause: ClauseV1,
        level: u64,
        role: RoleV1,
        request_digest: String,
        partition_digest: String,
        invalidated: bool,
        result: Box<AttemptResultV1>,
        #[serde(deserialize_with = "nullable")]
        solver_time_nanos: Option<u64>,
        #[serde(deserialize_with = "nullable")]
        preparation_time_nanos: Option<u64>,
        #[serde(deserialize_with = "nullable")]
        previous_row_digest: Option<String>,
        row_digest: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HistoryV1 {
    pub clause: ClauseV1,
    /// The audited origin that placed the clause, and whether it is a
    /// protected Lean-issued system row Houdini may never drop.
    pub origin: OriginV1,
    pub protected: bool,
    #[serde(deserialize_with = "nullable")]
    pub status: Option<StatusV1>,
    pub minimum_level: u64,
    #[serde(deserialize_with = "nullable")]
    pub current_level: Option<u64>,
    pub attempts: Vec<AttemptRowV1>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PageV1 {
    pub total_items: u64,
    pub first_index: u64,
    pub returned_items: u64,
    #[serde(deserialize_with = "nullable")]
    pub continuation: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LedgerV1 {
    pub metadata: PageV1,
    pub items: Vec<LedgerRowV1>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AdmissionDiagnosticV1 {
    pub code: String,
    pub message: String,
    #[serde(deserialize_with = "nullable")]
    pub item_index: Option<u64>,
    #[serde(deserialize_with = "nullable")]
    pub path: Option<String>,
    #[serde(deserialize_with = "nullable")]
    pub offset: Option<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EvaluatedV1 {
    pub source: String,
    #[serde(deserialize_with = "admitted_true")]
    pub admitted: bool,
    pub holds: Vec<bool>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CorrectableV1 {
    pub source: String,
    #[serde(deserialize_with = "admitted_false")]
    pub admitted: bool,
    pub correctable: AdmissionDiagnosticV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum EvaluationV1 {
    Evaluated(EvaluatedV1),
    Correctable(CorrectableV1),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum EvaluationLabelV1 {
    Retained {
        attempt: PhysicalAttemptId,
        source_index: u64,
    },
    Supplied {
        source_index: u64,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RetainedKindV1 {
    Retained,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SkipReasonV1 {
    NotRetained,
    CarrierUnavailable,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SkippedV1 {
    pub kind: RetainedKindV1,
    pub source_index: u64,
    pub attempt: PhysicalAttemptId,
    pub tuple_count: u64,
    pub reason: SkipReasonV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ValidatedV1 {
    pub source: String,
    #[serde(deserialize_with = "admitted_true")]
    pub admitted: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum ValidationV1 {
    Validated(ValidatedV1),
    Correctable(CorrectableV1),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ValidateResultV1 {
    pub results: Vec<ValidationV1>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EvaluateResultV1 {
    pub results: Vec<EvaluationV1>,
    pub instances: Vec<EvaluationLabelV1>,
    pub cost: u64,
    pub skipped: Vec<SkippedV1>,
}

fn admitted_true<'de, D: serde::Deserializer<'de>>(deserializer: D) -> Result<bool, D::Error> {
    if bool::deserialize(deserializer)? {
        Ok(true)
    } else {
        Err(serde::de::Error::custom(
            "an evaluated clause must have admitted=true",
        ))
    }
}

fn admitted_false<'de, D: serde::Deserializer<'de>>(deserializer: D) -> Result<bool, D::Error> {
    if bool::deserialize(deserializer)? {
        Err(serde::de::Error::custom(
            "a correctable clause must have admitted=false",
        ))
    } else {
        Ok(false)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(untagged)]
pub enum ToolResponseV1 {
    Error(ErrorEnvelopeV1),
    Countermodel(SuccessEnvelopeV1<CountermodelV1>),
    StrongestRefutations(SuccessEnvelopeV1<StrongestRefutationsV1>),
    History(SuccessEnvelopeV1<HistoryV1>),
    Ledger(SuccessEnvelopeV1<LedgerV1>),
    ValidateClauses(SuccessEnvelopeV1<ValidateResultV1>),
    EvaluateClauses(SuccessEnvelopeV1<EvaluateResultV1>),
}

impl<'de> Deserialize<'de> for ToolResponseV1 {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let value = Value::deserialize(deserializer)?;
        tool_response_from_value(value).map_err(serde::de::Error::custom)
    }
}

fn tool_response_from_value(value: Value) -> Result<ToolResponseV1, String> {
    fn decode<T: serde::de::DeserializeOwned>(value: Value) -> Result<T, String> {
        serde_json::from_value(value).map_err(|error| error.to_string())
    }
    // Even unknown tool names have legitimate errors. The strict envelope
    // rejects extra fields (including result alongside error).
    if value.get("error").is_some() {
        return decode(value).map(ToolResponseV1::Error);
    }
    match value.get("tool").and_then(Value::as_str) {
        Some("countermodel") => decode(value).map(ToolResponseV1::Countermodel),
        Some("strongest_refutations") => decode(value).map(ToolResponseV1::StrongestRefutations),
        Some("history") => decode(value).map(ToolResponseV1::History),
        Some("ledger") => decode(value).map(ToolResponseV1::Ledger),
        Some("validate_clauses") => decode(value).map(ToolResponseV1::ValidateClauses),
        Some("evaluate_clauses") => decode(value).map(ToolResponseV1::EvaluateClauses),
        _ => Err("unknown successful tool response".into()),
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(untagged)]
pub enum ToolArgumentsV1 {
    Countermodel(CountermodelArgumentsV1),
    StrongestRefutations(ClauseArgumentsV1),
    History(ClauseArgumentsV1),
    Ledger(LedgerArgumentsV1),
    ValidateClauses(ValidateArgumentsV1),
    EvaluateClauses(EvaluateArgumentsV1),
}
