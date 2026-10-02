//! Scoped proposer capabilities. No mutable engine state or admission constructors.
mod negotiation;
pub mod observation;
pub mod proposals;
pub mod queries;
pub mod query_results;
pub mod wire;
pub use queries::{
    AgentTool, AgentToolErrorPayload, AgentToolPolicy, AgentToolResponse, AgentToolResponseFuture,
    AgentToolSurface, EvaluateClausesArgs, EvaluationInstance, EvaluationRelation,
    EvaluationSelection, EvaluationSource, ValidateClausesArgs,
};
pub(crate) mod version;
pub use crate::framework2::proposer_contract::{
    AgentProvider, AgentPush, AgentResponseLimitExceeded, AgentResponseWriter,
    AgentSourceCancellation, AgentSourceCleanupFuture, AgentSourceFuture, AgentSourceOutcome,
    ProposerTerminalFailure,
};
pub use AgentProvider as Proposer;
pub use AgentPush as ProposerPush;
pub use AgentToolSurface as ProposerQueries;
pub use negotiation::{ApiCapabilities, ApiNegotiationError, NegotiatedApi};
pub use observation::{ClauseV1 as ClauseRef, PushV1 as ObservationSnapshot};
pub use version::API_VERSION;
pub use wire::{ProposerCleanupError, ProposerCleanupFuture};
