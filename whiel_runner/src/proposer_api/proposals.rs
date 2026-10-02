//! Strict proposal wire shapes. Deserialization grants no admission authority.

use super::observation::{DropV1, ResponseBindingV1};
use serde::{Deserialize, Serialize};
use serde_json::Value;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProgramInstanceV1 {
    pub relations: Vec<ProgramRelationV1>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProgramRelationV1 {
    pub name: String,
    pub rows: Vec<Vec<String>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", deny_unknown_fields, rename_all = "snake_case")]
pub enum ResponseV1 {
    CandidateClauses {
        schema_version: u64,
        binding: ResponseBindingV1,
        clauses: Vec<String>,
        dropped: Vec<DropV1>,
    },
    CandidateCounterexample {
        schema_version: u64,
        binding: ResponseBindingV1,
        input: ProgramInstanceV1,
    },
}
// Raw ingress keeps counterexample input opaque until Lean admission.
#[derive(Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub(crate) enum RawAgentHoudiniResponse {
    CandidateClauses {
        schema_version: u64,
        binding: RawResponseBinding,
        clauses: Vec<String>,
        dropped: Vec<RawDropReference>,
    },
    CandidateCounterexample {
        schema_version: u64,
        binding: RawResponseBinding,
        input: Value,
    },
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct RawResponseBinding {
    pub(crate) task_digest: String,
    pub(crate) scope_digest: String,
    pub(crate) run_digest: String,
    pub(crate) consultation_digest: String,
    pub(crate) state_snapshot_digest: String,
    pub(crate) validation_manifest_digest: String,
    pub(crate) request_digest: String,
    pub(crate) validation_ordinal: usize,
}

/// A clause named in a submission. Same rule as the read surface's
/// [`crate::proposer_api::queries::WireClauseIdentity`]: the digests name the
/// clause, the admitted text may be echoed back exactly as the push carried
/// it, and text that disagrees with the named record is refused.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct RawClauseIdentity {
    pub(crate) clause_id: u64,
    pub(crate) record_digest: String,
    pub(crate) formula_digest: String,
    #[serde(default)]
    pub(crate) canonical_source: Option<String>,
    #[serde(default)]
    pub(crate) display: Option<String>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct RawDropReference {
    pub(crate) clause: RawClauseIdentity,
    pub(crate) consultation_digest: String,
    pub(crate) authorization_digest: String,
}
