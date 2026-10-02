//! Caller-neutral Houdini state, registration, and checking phases.
//!
//! This module owns clause identity and verification classifications.  It
//! deliberately does not inspect the syntax or provenance of a clause.

mod bulk;
mod catalog;
mod certification;
mod execution;
mod initialization;
mod maintenance;
mod termination;

pub use bulk::{BulkMaintenanceOutcome, bulk_maint_check};
pub use catalog::{
    ClauseCatalog, ClauseFormula, ClauseId, ClauseRecordSnapshot, ClauseSet, InitCoverage,
    InitializationStatus, LatestMaintenanceResult, MaintenanceResultClass,
    MaintenanceResultDisposition, RegisteredClauses, close_init_coverage, register_clauses,
};
pub use certification::{
    CertificationInstance, CertificationInstanceError, CertificationRuntime, CertifiedInvalidity,
    CertifiedValidity, InvalidityCertificationOutcome, ValidityCertificationOutcome,
    certify_invalid, certify_valid,
};
pub use execution::{
    GenerationId, HoudiniExecutionOutcome, MaintenanceBlockOutcome, MaintenanceBlockResult,
    MaintenanceExecutionOutcome, apply_maintenance_exclusion, expand_core, houdini,
    run_maintenance_block, run_maintenance_block_sequential, run_maintenance_blocks,
    run_maintenance_blocks_sequential, settle_maintenance_history,
};
pub use initialization::{
    HoudiniState, InitializationInvocationOutcome, LastTermStatus, SearchFeedback,
    VerificationParameters, check_initialization,
};
pub use maintenance::{
    CoverageClosureMetrics, CoverageLookup, CoverageMode, MaintCoverage, MaintSupport,
    MaintenancePlan, MaintenancePolicy, MaintenancePreparationOutcome, MaintenanceSchedule,
    MaintenanceTrack, MaintenanceTrackHint, MaintenanceTrackKind, TrackLayout,
    close_maint_coverage, prepare_maintenance, project_closed_maint_coverage,
};
pub use termination::{TerminationInvocationOutcome, term_check};
