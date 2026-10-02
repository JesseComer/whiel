//! Persistent Lean-backed preparation of reusable solver bodies.
//!
//! This module is additive.  It shares task identities, resource admission,
//! and artifact-backend identity with the synthesis runtime, but does not
//! replace any legacy manifest or query-scoped Lean interface.

mod cache;
mod context;
mod names;
mod proposal;
mod protocol;
mod solver_name;
mod worker;

pub(crate) use context::{
    CatalogFormulaBindingError, FixedAmbientEvaluationError, FixedAmbientPreparedBodyData,
    FixedAmbientPreparedSupportData, NativeEmptyCheck, NativeEmptyOutcome,
};
pub use context::{
    EncodingError, FixedAmbientEncodingContext, PreparedBodyRef, PreparedWLayerBundle,
    QfSolverSource, ReferenceProposalBatch, ReferenceProposalSource, SolverBodySource,
    SolverEncodingContext, SupportBlockRef, new_fixed_ambient_encoding_context,
    new_solver_encoding_context,
};
pub use names::{NameEnvRevision, NameMapping, NameMappingKind, TaskNameEnv};
pub use proposal::{
    PROPOSAL_PAGE_PROTOCOL_VERSION, ProposalRealization, ProposalRevision,
    REFERENCE_PROPOSAL_VERSION,
};
pub(crate) use proposal::{bytes_sha256, canonical_value_sha256};
pub use protocol::{
    FIXED_AMBIENT_WORKER_FORMAT_VERSION, FixedAmbientWorkerBinding, FixedAmbientWorkerOperation,
    FixedAmbientWorkerRequestEnvelope, FixedAmbientWorkerResponseEnvelope,
    FixedAmbientWorkerResponseError, FixedAmbientWorkerTaskIdentity, MAX_ENCODING_FRAME_BYTES,
    WORKER_FORMAT_VERSION, WorkerOperation, WorkerRequestEnvelope, WorkerResponseEnvelope,
    WorkerResponseError, WorkerResponseStatus,
};
pub use solver_name::SolverNameError;
pub use worker::{
    EncodingWorkerCommand, EncodingWorkerPoolConfig, FIXED_AMBIENT_ROUND_TRIP_TIMEOUT,
    FixedAmbientWorkerCommand, FixedAmbientWorkerPoolConfig, LEAN_WORKER_THREADS,
};

pub(crate) use context::ReplayFixedAmbientAllocation;
