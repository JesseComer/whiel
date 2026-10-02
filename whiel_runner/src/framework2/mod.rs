//! Lean-owned fixed-ambient values and classification-free Rust control state.

mod acceptance;
mod admission;
mod agent;
#[cfg(test)]
pub(crate) use agent::{fixture_push_for_negotiated_api, fixture_push_for_tools};
mod aggregate;
mod bootstrap;
mod catalog;
mod certificate;
mod certificate_ops;
mod certificate_profiles;
mod components;
mod counterexample;
mod evaluation_ops;
mod feedback;
mod freeze;
mod host_limits;
mod leancheck;
mod ledger;
mod model;
mod pieces;
mod premise;
mod production;
mod proof_transform;
mod proposal;
mod publication;
pub mod replay_audit;
mod replay_correspondence;
pub mod replay_identity;
mod replay_production_compare;
mod replay_wire_compare;
pub mod resource_limits;
mod search;
mod snapshot;
mod solver;
mod stabilization;
pub(crate) mod strict_json;
// Physically versioned with the API while retaining private engine assembly.
#[path = "../proposer_api/adapters/dispatch.rs"]
mod tools;
mod transcript;
mod types;

pub(crate) const FRAMEWORK_II_RUNTIME_CACHE_IDENTITY_VERSION: u64 = 9;

pub use admission::{
    FixedAmbientTaskBootstrap, FrameworkIIAdmissionContext, FrameworkIIAdmissionError,
    build_framework_ii_admission,
};
// API declarations stay in the versioned source directory; nesting preserves
// compiler-enforced B-only assembly and response accounting fields.
#[path = "../proposer_api/provider.rs"]
pub(crate) mod proposer_contract;
pub use acceptance::{
    ACCEPTED_RECORD_KIND, ACCEPTED_RECORD_NAME, ACCEPTED_RECORD_VERSION, AcceptanceEnvelope,
    AcceptanceRecordError, AcceptanceRecordRequest, AcceptedVerdict, WrittenAcceptance,
    read_acceptance_envelope, record_acceptance, release_without_certifying,
    task_identity_from_worker_manifest, task_identity_record,
};
pub use agent::{
    Agent, AgentConsultationBinding, AgentConsultationCancelled, AgentConsultationLimits,
    AgentConsultationPolicy, AgentConsultationPolicyError, AgentCorrectionDiagnostic,
    AgentCounterexampleProposal, AgentHoudiniAttempt, AgentHoudiniCorrection, AgentHoudiniResponse,
    AgentProvider, AgentPush, AgentRequestAttemptOutcome, AgentResponseLimitExceeded,
    AgentResponseValidation, AgentResponseValidator, AgentResponseWriter, AgentSourceCancellation,
    AgentSourceCleanupFuture, AgentSourceFuture, AgentSourceOutcome, HoudiniProposal,
};
pub use aggregate::{
    AggregateCertificationError, CertifyFrozenCoreRequest, CheckedAggregateCandidate,
    DEFAULT_CERTIFICATION_CONCURRENCY, certify_frozen_core,
};
pub use bootstrap::{
    BoundFixedAmbientFrameworkII, FrameworkIIBindError, bind_fixed_ambient_framework_ii,
};
pub use catalog::{
    ExtendedClauseOrigin, FrameworkIIStateError, LeveledClauseCatalog, LeveledClauseRecord,
    RegisteredLeveledClauses,
};
pub use certificate::{CORE_RECORD_NAME, CORE_ROWS_KIND, CORE_ROWS_VERSION, core_record_text};
pub use certificate::{
    CertificateBuildError, CertificateBuildReceipt, CertificateBuildRequest, CertificateJobReceipt,
    CertificateRevalidation, CertificateRevalidationRequest, InvalidCertificateBuildRequest,
    build_certificate, build_invalid_certificate, revalidate_certificate_tree,
};
#[cfg(feature = "test-hooks")]
pub use certificate::{CertificateBuildHook, CertificateBuildHooks, CertificateModuleHook};
pub use certificate_ops::{
    CertificateArtifact, CertificateBundle, CertificateBundleShape, CertificateJob,
    FrameworkIICertificateError, PackagedProof,
};
pub use certificate_profiles::SearchProfileProvenance;
pub use components::{
    FrameworkIIClauseComponents, FrameworkIIComponentFormula, FrameworkIIComponentMetadata,
    FrameworkIIComponentRole, FrameworkIITaskComponents,
};
pub use counterexample::{
    COUNTEREXAMPLE_TIMEOUT_CODE, CounterexampleProvenance, CounterexampleRejection,
    CounterexampleValidation, FrameworkIICounterexampleError, FrozenCounterexampleRecord,
    LEAN_COUNTEREXAMPLE_REJECTION_CODES, ValidatedCounterexample,
};
pub use evaluation_ops::{
    ClauseEvaluation, ClauseEvaluationResult, EvaluationInstance, EvaluationRelation,
    FrameworkIIEvaluationError, evaluation_cost, evaluation_instance_from_countermodel,
};
pub use feedback::{
    AgentArtifactReference, AgentArtifactRole, AgentAttemptOutcome, AgentAttemptOutcomeKind,
    AgentClauseDropReference, AgentClauseFeedback, AgentClauseIdentity, AgentClausePage,
    AgentClauseStatus, AgentCurrentRoot, AgentEvidenceRoute, AgentFailureFeedback, AgentFeedback,
    AgentFeedbackCursor, AgentFeedbackError, AgentFeedbackLimits, AgentFeedbackPageCategory,
    AgentFeedbackPolicy, AgentFeedbackPresentation, AgentFeedbackSummary, AgentLatestFeedback,
    AgentLedgerFeedback, AgentLedgerPage, AgentPageMetadata, AgentPostconditionOpenFeedback,
    AgentProphecyBinding, AgentSearchFeedback, AgentTaskPresentation, AgentTaskTriple,
    PreCertificateAgentHoudiniState,
};
pub use freeze::{
    CoreFreezeError, FROZEN_CORE_KIND, FROZEN_CORE_VERSION, FrameworkIITerminationProof,
    FrozenCoreRow, FrozenLeveledCore,
};
pub use host_limits::{
    HOST_LIMIT_CODE, HOST_LIMIT_NAMES, HostLimitName, HostLimitRefusal, HostLimitTruncation,
    HostLimits,
};
pub use leancheck::{
    LeancheckError, LeancheckOutput, LeancheckProfile, LeancheckRun, PinnedKernelLratCadical,
    PinnedLeancheckVampire,
};
pub use ledger::{
    FrameworkIICheckEvidence, FrameworkIICheckOutcome, FrameworkIICheckRequest,
    FrameworkIICheckRole, FrameworkIIDeadReason, FrameworkIIInconclusiveReason,
    FrameworkIIInvalidationReason, LevelAttemptLedger, LevelAttemptRecord, LevelInvalidationRecord,
    LevelLedgerRow,
};
pub use model::{
    FrameworkIIFiniteInterpretation, FrameworkIIRelationTable, decode_framework_ii_vampire_model,
};
pub use pieces::FrameworkIIPieceCacheStats;
pub use production::{
    CascPortfolioPolicy, FrameworkIICertificationProfiles, FrameworkIICountermodelInstance,
    FrameworkIICountermodelRelation, FrameworkIIEmptyCheckEvidence, FrameworkIIEntailmentProgress,
    FrameworkIIPreCheckOutcome, FrameworkIIProductionCheckConfig, FrameworkIIProductionChecker,
    FrameworkIIRefutationSummary, FrameworkIIRetainedCountermodel, FrameworkIIRetryPolicy,
    FrameworkIISemanticReuseKind, FrameworkIITerminationRequest, LeancheckCertificationProfile,
    PreparedFrameworkIIEntailment, ProofSearchProfile, ProtectedPreconditionRule,
    ProtectedTheoremSelectionReceipt, RuntimeProofReceipt, SemanticReuseEvidence,
    SolverInvocationIdentity, ValidatedFiniteRefutation,
};
pub use proof_transform::canonical::{
    CERTIFICATE_RESOURCE_POLICY, VOLATILE_LINE_PREFIXES, normalize_telescope_order,
};
pub use proof_transform::lrat::{
    AvatarKind, CADICAL_ENVIRONMENT_CONTRACT, CadicalLratSolver, FROM_LRAT_IMPORT, KernelSatError,
    KernelSatOutcome, KernelSatProblem, KernelSatTransform, LratSolver, RecordedLratSolver,
    ValidatedKernelSat, plan_avatar_kernel_sat, qualify_lrat_collisions, render_kernel_sat_probe,
    render_lrat_helper, transform_avatar_kernel_sat, validate_lrat,
};
pub use proof_transform::{
    CLAUSE_PROJECTION_IMPORT, KernelSatContext, ProofCandidate, ProofTransformError,
    ProofTransformId, ProofTransformOutcome, ProofTransformRecord, TRANSFORM_ORDER,
    TransformedProof, apply_proof_transforms, mark_rolled_back,
};
pub use proposal::{
    FrameworkIIEpochOutcome, FrameworkIIEpochResult, FrameworkIIProposalContext,
    FrameworkIIProposalDrop, FrameworkIIProposalEpoch, run_framework_ii_proposal_epoch,
};
pub(crate) use publication::publish_invalid_in_phase;
pub use publication::{
    COUNTEREXAMPLE_RECORD_FILE, COUNTEREXAMPLE_RECORD_KIND, COUNTEREXAMPLE_RECORD_VERSION,
    CounterexampleFuelPolicy, DurableCounterexampleError, DurableCounterexampleRecord,
    PublicationError, PublishInvalidRequest, PublishValidRequest, PublishedInvalid, PublishedValid,
    RUN_CONFIGURATION_KIND, RUN_CONFIGURATION_VERSION, RunConfiguration, RunConfigurationError,
    SettledSearchOutcome, SettlementError, SettlementPolicy, SettlementResources,
    VALID_EVIDENCE_DIRECTORY, publish_invalid, publish_valid, settle_search_outcome,
};
pub use search::{
    ATTEMPT_HISTORY_KIND, ATTEMPT_HISTORY_SCOPE, ATTEMPT_HISTORY_VERSION,
    AttemptHistoryPublication, DEFAULT_COUNTEREXAMPLE_VALIDATION_LIMIT,
    PreCertificateAgentHoudiniHandoff, PreCertificateAgentHoudiniInspection,
    PreCertificateAgentHoudiniLimits, PreCertificateAgentHoudiniOutcome,
    PreCertificateAgentHoudiniRuntime, PreCertificateAgentHoudiniRuntimeInspection,
    PreCertificateAgentHoudiniSearch, RecordedWitnessValidation, validate_recorded_witness,
};
pub use snapshot::{LeveledCandidateSnapshot, LeveledCoreHandle};
pub use solver::{
    FrameworkIIPreconditionBasis, FrameworkIIPreconditionRoute, FrameworkIISolverContext,
    FrameworkIISolverError,
};
pub use stabilization::{
    CurrentFrameworkIIRoot, FrameworkIICheckExecution, FrameworkIIChecker, FrameworkIIDeadCause,
    FrameworkIIPreconditionInstallationOutcome, FrameworkIIRootCoverage, FrameworkIISweepDispatch,
    LeveledHoudiniState, LeveledStabilizationOutcome, SyncFrameworkIIChecker,
    install_framework_ii_precondition_clauses, stabilize_leveled_houdini,
    stabilize_leveled_houdini_with_system_clauses,
};
pub use tools::{
    AgentTool, AgentToolErrorPayload, AgentToolPolicy, AgentToolResponse, AgentToolResponseFuture,
    AgentToolSurface,
};
pub use types::{
    AdmissionCorrection, AdmissionDiagnostic, AdmissionOutcome, ExtendedClause,
    FixedAmbientTaskScope, FrameworkIILevel, FrameworkIIProphecyBinding, FrameworkIIRelation,
};

#[cfg(test)]
mod tests;

#[cfg(test)]
mod proposal_tests;

#[cfg(test)]
mod feedback_tests;

#[cfg(test)]
mod search_tests;

pub use transcript::{
    CONSULTATION_RECORD_SCOPE, DEFAULT_TRANSCRIPT_READ_BYTES, RecordedTranscript,
    RecordingProvider, Redaction, ReplayIneligibility, ResponseChunkAccounting, TRANSCRIPT_VERSION,
    TranscriptCoordinates, TranscriptError, TranscriptEvent, TranscriptHeader, TranscriptLifecycle,
    TranscriptOutcome, TranscriptPins, TranscriptProviderOutcome, TranscriptRecorder,
    TranscriptStream, TranscriptToolchainPins, VerifiedTranscript,
};

// Shared closed owner DTOs used by the existing entailment terminal owner.
pub(crate) use production::{
    ReplayArtifactIdentity, ReplayFailureKind, ReplayFailureOrigin, ReplayFailureScope,
    ReplayPrivateFailure, ReplaySha256,
};

pub use replay_correspondence::{
    ReplayCaptureError, ReplayCorrespondenceV1, ReplayFinalStateOwner, ReplayFinalStateProjection,
    ReplayPushProjection, ReplayResponseChunk,
};

pub use replay_wire_compare::{
    ReplayTimingDifference, ReplayWireIdentity, ReplayWireRebinding, ReplayWireReplacement,
};
