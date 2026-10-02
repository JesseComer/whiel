//! Caller-neutral Vampire process and invocation boundaries.
//!
//! Phase 2A owns proof-only and finite-model-only workers. Phase 2B owns
//! paired arbitration, admission, and local-deadline interpretation.

// ------------------------------------------------------------
// Internal Modules
// ------------------------------------------------------------

mod command;
pub(crate) mod process;
mod protocol;
mod race;
mod worker;

pub(crate) use command::{
    PROOF_CASC_ALLOCATION_FORMULA, PROOF_CASC_ALLOCATION_ROUNDING, PROOF_CASC_AVATAR,
    PROOF_CASC_CORES, PROOF_CASC_PROFILE_ID, PROOF_CASC_RANDOM_SEED,
    PROOF_CASC_RANDOMIZE_WORKER_SEEDS, PROOF_CASC_SCHEDULE, PROOF_CASC_SHARE_SCALE,
    PROOF_CASC_SHUFFLE_SCHEDULE_REPEATS,
};

// ------------------------------------------------------------
// Public Vampire API
// ------------------------------------------------------------

pub use command::{
    FmbContourStrategy, FmbOptions, FmbSize, ProofCascPolicy, ProofCascPolicyError, ProofCascShare,
    ProofCascShareError, SolverTimeLimit, VAMPIRE_MEMORY_LIMIT_MB, VAMPIRE_PLANNED_FOOTPRINT_MB,
    VampireCommandError, VampireInvocationProfile, VampireProblem, VampireWorkerCommand,
    VampireWorkerMode, VampireWorkerRequest,
};
pub use race::{
    CancelledVampireInvocation, VampireInvocationOutcome, VampireMode, VampireRequest,
    VampireRequestError, VampireSearchBudget, run_vampire,
};
pub use worker::{
    CancelledVampireWorker, VampireCapturePolicy, VampireModel, VampireProof, VampireProofStrategy,
    VampireResult, VampireWorkerOutcome, run_single_vampire_worker,
};
