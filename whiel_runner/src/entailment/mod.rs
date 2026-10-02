//! Immutable source-linked entailment assembly.

pub(crate) mod assembly;
mod check;
mod model;
mod resolution;

pub use assembly::{Entailment, PremiseRole, assemble_entailment};
pub use check::{
    CancelledEntailmentCheck, DecodedModelCache, EmptyCheckEvidence, EntailmentAttemptScope,
    EntailmentCheckReport, EntailmentCheckResult, EntailmentCounterexample,
    EntailmentInvocationOutcome, check_entailment, check_entailment_attempt_detailed,
    check_entailment_detailed,
};
pub(crate) use check::{
    SpecializedEntailmentCheckReport, SpecializedEntailmentTerminal,
    check_entailment_attempt_detailed_with_resolver, publish_specialized_entailment_terminal,
};
pub(crate) use model::{DecodedFiniteModel, decode_vampire_model_for_relations};
pub use model::{
    DecodedInstance, DecodedRelation, EmptyInstanceError, InstanceValue, ModelDecodeError,
    decode_vampire_model,
};
pub use resolution::resolve_entailment_counterexample;

pub(crate) use check::{
    ReplayProofStrategy, ReplaySpecializedTerminalDetail, ReplaySpecializedTerminalOwner,
    ReplaySpecializedTerminalProjection,
};
