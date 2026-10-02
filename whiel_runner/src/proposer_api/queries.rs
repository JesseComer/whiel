//! Public query vocabulary and data shapes; no state or worker handles.

use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::future::Future;
use std::pin::Pin;

// ------------------------------------------------------------
// Tool Identity And Policy
// ------------------------------------------------------------

/// Every tool the controller can expose to a provider during one
/// consultation. Submission is never a tool: it is the provider's response,
/// not a call against this surface.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AgentTool {
    Countermodel,
    StrongestRefutations,
    History,
    Ledger,
    ValidateClauses,
    EvaluateClauses,
}

impl AgentTool {
    /// Every tool, in the exact order their wire names are documented.
    pub const ALL: [AgentTool; 6] = [
        AgentTool::Countermodel,
        AgentTool::StrongestRefutations,
        AgentTool::History,
        AgentTool::Ledger,
        AgentTool::ValidateClauses,
        AgentTool::EvaluateClauses,
    ];

    /// The exact wire name shown in a push's `tools` list and expected as
    /// the tool surface's `name` argument.
    pub fn name(self) -> &'static str {
        match self {
            AgentTool::Countermodel => "countermodel",
            AgentTool::StrongestRefutations => "strongest_refutations",
            AgentTool::History => "history",
            AgentTool::Ledger => "ledger",
            AgentTool::ValidateClauses => "validate_clauses",
            AgentTool::EvaluateClauses => "evaluate_clauses",
        }
    }

    /// Resolve an exact wire name to its tool, or `None` for anything else
    /// (including a name that is not currently enabled: enablement is a
    /// separate, policy-level check).
    pub fn from_name(name: &str) -> Option<Self> {
        AgentTool::ALL.into_iter().find(|tool| tool.name() == name)
    }
}

/// The typed host option selecting which tools this run's provider may call.
///
/// Bound once per run and drift-checked between the persistent
/// `LeveledHoudiniState`
/// and the runtime authorities that must agree with it. Submission is never
/// part of this set; it is always available and is not a tool.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgentToolPolicy {
    enabled: std::collections::BTreeSet<AgentTool>,
}

impl Default for AgentToolPolicy {
    /// Every tool enabled, the default for AgentHoudini runs.
    fn default() -> Self {
        Self {
            enabled: AgentTool::ALL.into_iter().collect(),
        }
    }
}

impl AgentToolPolicy {
    pub fn new(enabled: impl IntoIterator<Item = AgentTool>) -> Self {
        Self {
            enabled: enabled.into_iter().collect(),
        }
    }

    /// Every tool enabled (equivalent to [`Default::default`], spelled out
    /// for callers that want to name the choice explicitly).
    pub fn all_enabled() -> Self {
        Self::default()
    }

    /// No tool enabled.
    pub fn none_enabled() -> Self {
        Self {
            enabled: std::collections::BTreeSet::new(),
        }
    }

    pub fn is_enabled(&self, tool: AgentTool) -> bool {
        self.enabled.contains(&tool)
    }

    pub fn enabled(&self) -> &std::collections::BTreeSet<AgentTool> {
        &self.enabled
    }

    /// The enabled set's exact wire names, in [`AgentTool::ALL`] order —
    /// exactly what a push's `tools` list carries.
    pub fn enabled_names(&self) -> Vec<&'static str> {
        AgentTool::ALL
            .into_iter()
            .filter(|tool| self.is_enabled(*tool))
            .map(AgentTool::name)
            .collect()
    }
}

// ------------------------------------------------------------
// Tool Call Outcome
// ------------------------------------------------------------

/// One tool call's typed error.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AgentToolErrorPayload {
    pub code: String,
    pub message: String,
    /// Present exactly on a `host_limit` error: `{limit, value, observed}`,
    /// naming which of the run's optional limits refused the call. Absent on
    /// every error that reports a real defect of the call.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub host_limit: Option<Value>,
}

/// The result of one [`AgentToolSurface::call`], always stamped with the
/// exact state revision of the push this call answers (Pass 7.5c): the
/// `LeveledHoudiniState::proposal_revision` in force
/// when the answering push was built. A live tool body may report a result
/// computed from state that has since moved on only by naming that revision
/// here; it never silently reports against a newer one.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum AgentToolResponse {
    Ok {
        tool: String,
        state_revision: u64,
        result: Value,
    },
    Err {
        tool: String,
        state_revision: u64,
        error: AgentToolErrorPayload,
    },
}

impl AgentToolResponse {
    pub fn ok(tool: &str, state_revision: u64, result: Value) -> Self {
        Self::Ok {
            tool: tool.to_owned(),
            state_revision,
            result,
        }
    }

    pub fn err(tool: &str, state_revision: u64, code: &str, message: impl Into<String>) -> Self {
        Self::err_with_details(tool, state_revision, code, message, None)
    }

    /// One tool error carrying a structured payload beside its code, used
    /// for the `host_limit` refusal's `{limit, value, observed}`.
    pub fn err_with_details(
        tool: &str,
        state_revision: u64,
        code: &str,
        message: impl Into<String>,
        host_limit: Option<Value>,
    ) -> Self {
        Self::Err {
            tool: tool.to_owned(),
            state_revision,
            error: AgentToolErrorPayload {
                code: code.to_owned(),
                message: message.into(),
                host_limit,
            },
        }
    }

    pub fn tool(&self) -> &str {
        match self {
            Self::Ok { tool, .. } | Self::Err { tool, .. } => tool,
        }
    }

    pub fn state_revision(&self) -> u64 {
        match self {
            Self::Ok { state_revision, .. } | Self::Err { state_revision, .. } => *state_revision,
        }
    }

    pub fn error_code(&self) -> Option<&str> {
        match self {
            Self::Ok { .. } => None,
            Self::Err { error, .. } => Some(error.code.as_str()),
        }
    }
}

// ------------------------------------------------------------
// Provider-Facing Tool Surface
// ------------------------------------------------------------

pub type AgentToolResponseFuture<'a> = Pin<Box<dyn Future<Output = AgentToolResponse> + Send + 'a>>;

/// The bounded tool surface served to one provider for the lifetime of one
/// consultation. Constructing and polling `call` must be infallible and
/// nonpanicking; every outcome, including an unrecognized name, a disabled
/// tool, or a call arriving after the consultation ended, is reported as an
/// [`AgentToolResponse::Err`] rather than by aborting the consultation.
pub trait AgentToolSurface: Sync {
    fn call<'a>(&'a self, name: &'a str, args: Value) -> AgentToolResponseFuture<'a>;
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ValidateClausesArgs {
    pub clauses: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EvaluationRelation {
    pub name: String,
    pub rows: Vec<Vec<String>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EvaluationInstance {
    pub carrier_keys: Vec<String>,
    pub relations: Vec<EvaluationRelation>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum EvaluationSource {
    Retained { attempt: u64 },
    Supplied { instance: EvaluationInstance },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RetainedSelection {
    AllRetained,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum EvaluationSelection {
    Sources(Vec<EvaluationSource>),
    All(RetainedSelection),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EvaluateClausesArgs {
    pub clauses: Vec<String>,
    pub instances: EvaluationSelection,
}

// Raw ingress DTOs retain existing nullable/default and scalar decoding rules.
/// Exact clause-reference shape accepted by the scoped read dispatcher.
///
/// The three digest fields name the clause. The admitted text the API shows
/// beside them may be echoed back unchanged — a reference copied whole out of
/// the push is always accepted — but asserts nothing the digests do not
/// already fix, and an omitted or null text field is not a reference to a
/// different clause. Text that disagrees with the named record is refused.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct WireClauseIdentity {
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
pub(crate) struct CountermodelArgs {
    pub(crate) attempt: u64,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct ClauseArgs {
    pub(crate) clause: WireClauseIdentity,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct LedgerArgs {
    #[serde(default)]
    pub(crate) cursor: Option<String>,
}
