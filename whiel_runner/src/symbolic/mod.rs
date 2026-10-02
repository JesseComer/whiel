//! Symbolic invariant-lane state and orchestration.
//!
//! Phase 4A owns the typed reference-proposal boundary and INV orchestration.
//! Phase 4B owns exact W construction and refutation resolution. Phase 4C owns
//! fair CEX scheduling. Phase 4D owns the fixed lane race and entry wrapper.

mod cex;
mod inv;
mod orchestration;
mod w_channel;

pub use cex::{
    CertifiedSynthesisResult, CheckedWInitialization, CounterexampleResolutionOutcome,
    SymbolicCexRuntime, SymbolicCexState, SymbolicHoudiniPolicy, WAttemptRecord,
    WInitializationInvocationOutcome, WLimitGrowth, WRefutationResolutionOutcome, WSearchAttempt,
    WSearchResult, WSearchSchedule, check_w_initialization, ensure_w_layer_bundle,
    new_symbolic_cex_state, publish_available_w_proofs, resolve_w_refutation, run_cex_lane,
    search_w_counterexamples, select_next_w_attempt,
};

pub use inv::{
    SymbolicEpochOutcome, SymbolicInvRuntime, SymbolicInvState, SymbolicLaneOutcome,
    SymbolicProposalProgress, apply_w_zero_term_shortcut, drain_proved_w_batch,
    new_symbolic_inv_state, prepare_ordinary_candidates, propose_symbolic_clauses, run_inv_lane,
    run_symbolic_inv_epoch,
};
pub(crate) use orchestration::normalize_symbolic_verification;
pub use orchestration::{
    SymbolicHoudiniRuntime, SymbolicHoudiniState, SynthesisResult, new_symbolic_houdini_state,
    race_symbolic_lanes, symbolic_houdini,
};
pub use w_channel::{
    AdmittedWEntry, ProvedWBatch, ProvedWEntry, WAdmissionIndex, WProofReceiver, WProofSender,
    WPublicationOutcome, create_w_proof_channel,
};
