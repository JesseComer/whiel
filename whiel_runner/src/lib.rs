//! Shared runtime foundations for Whiel synthesis.
//!
//! This crate is additive. It does not depend on the legacy Python
//! synthesis package or the legacy `vampire_runner` executable.

pub mod artifact;
pub mod campaign;
pub mod campaign_cli;
pub mod certificate_cli;
pub mod certification;
pub mod cli;
pub mod encoding;
pub mod entailment;
pub mod failure;
pub mod framework2;
pub mod framing;
pub mod houdini;
pub mod proposer_api;
pub mod proposer_host;
pub mod reporting;
pub mod runtime;
pub mod symbolic;
pub mod task;
pub mod telemetry;
pub mod vampire;

pub use artifact::{
    ArtifactBackendOwner, ArtifactKind, ArtifactRef, ArtifactStore, ArtifactStoreConfig, AttemptId,
    BackendId, HistoryMode, RUN_CONFIGURATION_FILE, ResolvedArtifact, Retention,
    RunConfigurationBinding, ScopeTag, new_artifact_store, read_run_configuration,
};
pub use certification::{
    CertificationBridgeCommand, CertificationBridgeError, CertificationDiagnosticRef,
    CertificationFailure, CertificationOperation, CertificationOutcome, CertificationRejection,
    CertifiedBundle, CertifiedClassification, InvalidityCertificationLimits,
    ValidityCertificationLimits, WitnessArtifactRef,
};
pub use entailment::{
    CancelledEntailmentCheck, DecodedInstance, DecodedRelation, EmptyCheckEvidence,
    EmptyInstanceError, Entailment, EntailmentAttemptScope, EntailmentCheckReport,
    EntailmentCheckResult, EntailmentCounterexample, EntailmentInvocationOutcome, InstanceValue,
    ModelDecodeError, PremiseRole, assemble_entailment, check_entailment,
    check_entailment_detailed, decode_vampire_model, resolve_entailment_counterexample,
};
pub use failure::{FailureKind, FailureOrigin, FailureReport, FailureScope};
pub use framework2::{
    AdmissionCorrection, AdmissionDiagnostic, AdmissionOutcome, Agent, AgentConsultationBinding,
    AgentConsultationCancelled, AgentConsultationLimits, AgentConsultationPolicy,
    AgentConsultationPolicyError, AgentCorrectionDiagnostic, AgentCounterexampleProposal,
    AgentHoudiniAttempt, AgentHoudiniCorrection, AgentHoudiniResponse, AgentProvider, AgentPush,
    AgentRequestAttemptOutcome, AgentResponseLimitExceeded, AgentResponseValidation,
    AgentResponseValidator, AgentResponseWriter, AgentSourceCancellation, AgentSourceCleanupFuture,
    AgentSourceFuture, AgentSourceOutcome, AgentTool, AgentToolErrorPayload, AgentToolPolicy,
    AgentToolResponse, AgentToolResponseFuture, AgentToolSurface, BoundFixedAmbientFrameworkII,
    COUNTEREXAMPLE_TIMEOUT_CODE, CascPortfolioPolicy, CounterexampleRejection,
    CounterexampleValidation, CurrentFrameworkIIRoot, DEFAULT_COUNTEREXAMPLE_VALIDATION_LIMIT,
    ExtendedClause, ExtendedClauseOrigin, FixedAmbientTaskBootstrap, FixedAmbientTaskScope,
    FrameworkIIAdmissionContext, FrameworkIIAdmissionError, FrameworkIIBindError,
    FrameworkIICertificationProfiles, FrameworkIICheckEvidence, FrameworkIICheckExecution,
    FrameworkIICheckOutcome, FrameworkIICheckRequest, FrameworkIICheckRole, FrameworkIIChecker,
    FrameworkIIClauseComponents, FrameworkIIComponentFormula, FrameworkIIComponentMetadata,
    FrameworkIIComponentRole, FrameworkIICounterexampleError, FrameworkIIDeadCause,
    FrameworkIIDeadReason, FrameworkIIEmptyCheckEvidence, FrameworkIIEntailmentProgress,
    FrameworkIIEpochOutcome, FrameworkIIEpochResult, FrameworkIIFiniteInterpretation,
    FrameworkIIInconclusiveReason, FrameworkIIInvalidationReason, FrameworkIILevel,
    FrameworkIIPieceCacheStats, FrameworkIIPreCheckOutcome, FrameworkIIPreconditionBasis,
    FrameworkIIPreconditionInstallationOutcome, FrameworkIIPreconditionRoute,
    FrameworkIIProductionCheckConfig, FrameworkIIProductionChecker, FrameworkIIProphecyBinding,
    FrameworkIIProposalContext, FrameworkIIProposalDrop, FrameworkIIProposalEpoch,
    FrameworkIIRelation, FrameworkIIRelationTable, FrameworkIIRetryPolicy, FrameworkIIRootCoverage,
    FrameworkIISolverContext, FrameworkIISolverError, FrameworkIIStateError,
    FrameworkIISweepDispatch, FrameworkIITaskComponents, FrameworkIITerminationRequest,
    FrozenCounterexampleRecord, HOST_LIMIT_CODE, HOST_LIMIT_NAMES, HostLimitName, HostLimitRefusal,
    HostLimitTruncation, HostLimits, HoudiniProposal, InvalidCertificateBuildRequest,
    LEAN_COUNTEREXAMPLE_REJECTION_CODES, LeancheckCertificationProfile, LevelAttemptLedger,
    LevelAttemptRecord, LevelInvalidationRecord, LevelLedgerRow, LeveledCandidateSnapshot,
    LeveledClauseCatalog, LeveledClauseRecord, LeveledCoreHandle, LeveledHoudiniState,
    LeveledStabilizationOutcome, PreCertificateAgentHoudiniHandoff,
    PreCertificateAgentHoudiniInspection, PreCertificateAgentHoudiniLimits,
    PreCertificateAgentHoudiniOutcome, PreCertificateAgentHoudiniRuntime,
    PreCertificateAgentHoudiniRuntimeInspection, PreCertificateAgentHoudiniSearch,
    PreparedFrameworkIIEntailment, ProofSearchProfile, ProtectedPreconditionRule,
    ProtectedTheoremSelectionReceipt, RegisteredLeveledClauses, RuntimeProofReceipt,
    SolverInvocationIdentity, SyncFrameworkIIChecker, ValidatedCounterexample,
    ValidatedFiniteRefutation, bind_fixed_ambient_framework_ii, build_framework_ii_admission,
    build_invalid_certificate, decode_framework_ii_vampire_model,
    install_framework_ii_precondition_clauses, run_framework_ii_proposal_epoch,
    stabilize_leveled_houdini, stabilize_leveled_houdini_with_system_clauses,
};
pub use framework2::{
    COUNTEREXAMPLE_RECORD_FILE, COUNTEREXAMPLE_RECORD_KIND, COUNTEREXAMPLE_RECORD_VERSION,
    CertificateRevalidation, CertificateRevalidationRequest, CounterexampleFuelPolicy,
    CounterexampleProvenance, DurableCounterexampleError, DurableCounterexampleRecord,
    PublicationError, PublishInvalidRequest, PublishValidRequest, PublishedInvalid, PublishedValid,
    RUN_CONFIGURATION_KIND, RUN_CONFIGURATION_VERSION, RecordedWitnessValidation, RunConfiguration,
    RunConfigurationError, SettledSearchOutcome, SettlementError, SettlementPolicy,
    SettlementResources, publish_invalid, publish_valid, revalidate_certificate_tree,
    settle_search_outcome, validate_recorded_witness,
};
pub use houdini::{
    BulkMaintenanceOutcome, CertificationInstance, CertificationInstanceError,
    CertificationRuntime, CertifiedInvalidity, CertifiedValidity, ClauseCatalog, ClauseFormula,
    ClauseId, ClauseRecordSnapshot, ClauseSet, CoverageClosureMetrics, CoverageLookup,
    CoverageMode, GenerationId, HoudiniExecutionOutcome, HoudiniState, InitCoverage,
    InitializationInvocationOutcome, InitializationStatus, InvalidityCertificationOutcome,
    LastTermStatus, LatestMaintenanceResult, MaintCoverage, MaintSupport, MaintenanceBlockOutcome,
    MaintenanceBlockResult, MaintenanceExecutionOutcome, MaintenancePlan, MaintenancePolicy,
    MaintenancePreparationOutcome, MaintenanceResultClass, MaintenanceResultDisposition,
    MaintenanceSchedule, MaintenanceTrack, MaintenanceTrackHint, MaintenanceTrackKind,
    RegisteredClauses, SearchFeedback, TerminationInvocationOutcome, TrackLayout,
    ValidityCertificationOutcome, VerificationParameters, apply_maintenance_exclusion,
    bulk_maint_check, certify_invalid, certify_valid, check_initialization, close_init_coverage,
    close_maint_coverage, expand_core, houdini, prepare_maintenance, project_closed_maint_coverage,
    register_clauses, run_maintenance_block, run_maintenance_block_sequential,
    run_maintenance_blocks, run_maintenance_blocks_sequential, settle_maintenance_history,
    term_check,
};
pub use runtime::{
    AdmissionError, CancellationToken, ChildPanic, CpuWorkerPermit, ResourcePolicyError,
    RuntimeResourcePolicy, SolverAdmission, SolverAdmissionClass, TimedChildOutcome, TimedChildRun,
    create_general_solver_admission, create_symbolic_solver_admissions, run_timed_child,
};
pub use symbolic::{
    AdmittedWEntry, CertifiedSynthesisResult, CheckedWInitialization,
    CounterexampleResolutionOutcome, ProvedWBatch, ProvedWEntry, SymbolicCexRuntime,
    SymbolicCexState, SymbolicEpochOutcome, SymbolicHoudiniPolicy, SymbolicHoudiniRuntime,
    SymbolicHoudiniState, SymbolicInvRuntime, SymbolicInvState, SymbolicLaneOutcome,
    SymbolicProposalProgress, SynthesisResult, WAdmissionIndex, WAttemptRecord,
    WInitializationInvocationOutcome, WLimitGrowth, WProofReceiver, WProofSender,
    WPublicationOutcome, WRefutationResolutionOutcome, WSearchAttempt, WSearchResult,
    WSearchSchedule, apply_w_zero_term_shortcut, check_w_initialization, create_w_proof_channel,
    drain_proved_w_batch, ensure_w_layer_bundle, new_symbolic_cex_state,
    new_symbolic_houdini_state, new_symbolic_inv_state, prepare_ordinary_candidates,
    propose_symbolic_clauses, publish_available_w_proofs, race_symbolic_lanes,
    resolve_w_refutation, run_cex_lane, run_inv_lane, run_symbolic_inv_epoch,
    search_w_counterexamples, select_next_w_attempt, symbolic_houdini,
};
pub use task::{
    AgentTaskView, AssertExprRef, ConstantKey, NoBoundEvidenceRef, PreprocessingEvidenceRef,
    RelationKey, SchemaRef, SchemaRelationRef, SolverAssertSourceRef, SolverQfSourceRef,
    SourceDigest, SynthesisTask, TaskIdentity, TaskLoadError, WhielCommandRef,
};
pub use telemetry::{
    DEFAULT_EVENT_QUEUE_CAPACITY, DerivedTelemetry, FormulaBirthTelemetry, FormulaShape,
    MemoryTelemetry, ParameterDimensionYieldTelemetry, ReferenceParametersTelemetry,
    ShapeYieldTelemetry, StageYieldTelemetry, TELEMETRY_SCHEMA_VERSION, TelemetryConfig,
    TelemetryHandle, TelemetryLevel, TelemetryReport, TelemetrySession, TelemetrySnapshot,
    TelemetrySpan, WaveTelemetry, reference_formula_shape,
};
pub use vampire::{
    CancelledVampireInvocation, CancelledVampireWorker, FmbContourStrategy, FmbOptions, FmbSize,
    ProofCascPolicy, ProofCascPolicyError, ProofCascShare, ProofCascShareError, SolverTimeLimit,
    VampireCapturePolicy, VampireCommandError, VampireInvocationOutcome, VampireInvocationProfile,
    VampireMode, VampireModel, VampireProblem, VampireProof, VampireProofStrategy, VampireRequest,
    VampireRequestError, VampireResult, VampireSearchBudget, VampireWorkerCommand,
    VampireWorkerMode, VampireWorkerOutcome, VampireWorkerRequest, run_single_vampire_worker,
    run_vampire,
};
