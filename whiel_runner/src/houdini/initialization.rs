//! Persistent initialization checking before Houdini maintenance.

use std::collections::{BTreeSet, HashMap, VecDeque};
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

use serde_json::{Value, json};

use crate::artifact::{
    ArtifactKind, ArtifactRef, ArtifactStore, AttemptId, BackendId, HistoryMode, ScopeTag,
};
use crate::encoding::{EncodingError, SolverBodySource};
use crate::entailment::{
    EntailmentCheckResult, EntailmentCounterexample, EntailmentInvocationOutcome,
    assemble_entailment, check_entailment,
};
use crate::failure::{FailureKind, FailureReport, FailureScope};
use crate::runtime::{CancellationToken, RuntimeResourcePolicy, SolverAdmission};
use crate::task::{SynthesisTask, TaskIdentity};
use crate::telemetry::{TelemetryHandle, TelemetryLevel};
use crate::vampire::{FmbOptions, VampireMode, VampireSearchBudget, VampireWorkerCommand};

use super::bulk::BulkMaintenanceCapability;
use super::catalog::{
    CandidateSnapshot, ClauseCatalog, ClauseFormula, ClauseId, ClauseSet, InitCoverage,
    InitializationStatus, RegisteredClauses, RegistrationTiming, close_init_coverage,
    initialization_failure, register_clauses_with_timing,
};
use super::maintenance::{
    MaintCoverage, MaintSupport, MaintenancePlan, MaintenancePolicy, MaintenanceTrackHint,
};

static NEXT_HOUDINI_RUN_ID: AtomicU64 = AtomicU64::new(0);

// ------------------------------------------------------------
// Resolved Verification Policy
// ------------------------------------------------------------

/// Shared resolved limits used by initialization and later verification.
#[derive(Clone, Debug)]
pub struct VerificationParameters {
    search_limit: Duration,
    maintenance_retry_increments: Arc<[Duration]>,
    bulk_init_limit: Duration,
    bulk_maint_limit: Duration,
    init_first_attempt_limits: Vec<Duration>,
    search_term_limit: Duration,
    search_term_retry_increments: Vec<Duration>,
    final_certification_limit: Option<Duration>,
    resources: RuntimeResourcePolicy,
}

impl VerificationParameters {
    /// Construct the approved defaults from one positive search limit.
    pub fn new(
        search_limit: Duration,
        resources: RuntimeResourcePolicy,
    ) -> Result<Self, &'static str> {
        if search_limit.is_zero() {
            return Err("search_limit must be positive");
        }
        Ok(Self {
            search_limit,
            maintenance_retry_increments: Arc::from([search_limit, search_limit]),
            bulk_init_limit: search_limit,
            bulk_maint_limit: search_limit,
            init_first_attempt_limits: Vec::new(),
            search_term_limit: search_limit,
            search_term_retry_increments: Vec::new(),
            final_certification_limit: None,
            resources,
        })
    }

    pub fn with_init_first_attempt_limits(
        mut self,
        limits: Vec<Duration>,
    ) -> Result<Self, &'static str> {
        if limits.iter().any(Duration::is_zero) {
            return Err("init first-attempt limits must be positive");
        }
        if limits.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err("init first-attempt limits must be strictly increasing");
        }
        self.init_first_attempt_limits = limits;
        Ok(self)
    }

    pub fn with_bulk_init_limit(mut self, limit: Duration) -> Self {
        self.bulk_init_limit = limit;
        self
    }

    pub fn with_bulk_maint_limit(mut self, limit: Duration) -> Self {
        self.bulk_maint_limit = limit;
        self
    }

    pub fn with_maintenance_retry_increments(
        mut self,
        increments: Vec<Duration>,
    ) -> Result<Self, &'static str> {
        if increments.iter().any(Duration::is_zero) {
            return Err("maintenance retry increments must be positive");
        }
        self.maintenance_retry_increments = increments.into();
        Ok(self)
    }

    pub fn with_search_term_limit(mut self, limit: Duration) -> Result<Self, &'static str> {
        if limit.is_zero() {
            return Err("search term limit must be positive");
        }
        self.search_term_limit = limit;
        Ok(self)
    }

    pub fn with_search_term_retry_increments(
        mut self,
        increments: Vec<Duration>,
    ) -> Result<Self, &'static str> {
        if increments.iter().any(Duration::is_zero) {
            return Err("search term retry increments must be positive");
        }
        self.search_term_retry_increments = increments;
        Ok(self)
    }

    pub fn with_final_certification_limit(
        mut self,
        limit: Option<Duration>,
    ) -> Result<Self, &'static str> {
        if limit.is_some_and(|limit| limit.is_zero()) {
            return Err("final certification limit must be positive when present");
        }
        self.final_certification_limit = limit;
        Ok(self)
    }

    pub fn search_limit(&self) -> Duration {
        self.search_limit
    }

    pub fn maintenance_retry_increments(&self) -> &[Duration] {
        &self.maintenance_retry_increments
    }

    pub(super) fn maintenance_retry_increments_arc(&self) -> Arc<[Duration]> {
        Arc::clone(&self.maintenance_retry_increments)
    }

    pub fn bulk_init_limit(&self) -> Duration {
        self.bulk_init_limit
    }

    pub fn init_first_attempt_limits(&self) -> &[Duration] {
        &self.init_first_attempt_limits
    }

    /// The per-clause initialization ladder: short first tiers
    /// strictly below the search limit, then the full limit. A
    /// clause timing out below the final tier is deferred to the
    /// next tier instead of being classified.
    pub fn init_attempt_limits(&self) -> Vec<Duration> {
        self.init_first_attempt_limits
            .iter()
            .copied()
            .filter(|limit| *limit < self.search_limit)
            .chain(std::iter::once(self.search_limit))
            .collect()
    }

    pub fn bulk_maint_limit(&self) -> Duration {
        self.bulk_maint_limit
    }

    pub fn search_term_limit(&self) -> Duration {
        self.search_term_limit
    }

    pub fn search_term_retry_increments(&self) -> &[Duration] {
        &self.search_term_retry_increments
    }

    pub fn final_certification_limit(&self) -> Option<Duration> {
        self.final_certification_limit
    }

    pub fn resources(&self) -> RuntimeResourcePolicy {
        self.resources
    }
}

// ------------------------------------------------------------
// Initialization Projection Of Houdini State
// ------------------------------------------------------------

/// Minimal provenance retained for nonterminal logical search feedback.
///
/// The payload remains opaque until the search frontends define their exact
/// sanitized feedback views. These two fields prevent a future payload from
/// losing its exact task and attempt binding in the meantime.
#[derive(Clone, Debug)]
pub struct SearchFeedback {
    task_identity: TaskIdentity,
    backend_id: BackendId,
    attempt_id: AttemptId,
    artifact_references: Vec<ArtifactRef>,
}

impl SearchFeedback {
    pub(super) fn new(
        task_identity: TaskIdentity,
        backend_id: BackendId,
        attempt_id: AttemptId,
    ) -> Self {
        Self {
            task_identity,
            backend_id,
            attempt_id,
            artifact_references: Vec::new(),
        }
    }

    pub(super) fn with_artifact_references(mut self, references: Vec<ArtifactRef>) -> Self {
        self.artifact_references = references;
        self
    }

    pub fn task_identity(&self) -> &TaskIdentity {
        &self.task_identity
    }

    pub fn backend_id(&self) -> BackendId {
        self.backend_id
    }

    pub fn attempt_id(&self) -> AttemptId {
        self.attempt_id
    }

    /// Required records which preserve the exact source of this feedback.
    pub fn artifact_references(&self) -> &[ArtifactRef] {
        &self.artifact_references
    }
}

/// Termination knowledge for the exact current Core.
#[derive(Clone, Debug)]
pub enum LastTermStatus {
    Pending,
    Proved,
    Counterexample(SearchFeedback),
    Failure(FailureReport),
}

/// Durable caller-neutral state needed through the initialization phase.
/// Later phases extend this private representation with maintenance state.
#[derive(Debug)]
pub struct HoudiniState {
    pub(super) verification: VerificationParameters,
    pub(super) admission: SolverAdmission,
    pub(super) catalog: ClauseCatalog,
    pub(super) core: Arc<ClauseSet>,
    pub(super) init_candidates: Arc<ClauseSet>,
    pub(super) active: Arc<ClauseSet>,
    pub(super) candidate_snapshot: Option<Arc<CandidateSnapshot>>,
    pub(super) bulk_init_proved: bool,
    pub(super) bulk_maint_proved: bool,
    pub(super) bulk_maint_capability: Option<BulkMaintenanceCapability>,
    pub(super) last_term_status: LastTermStatus,
    pub(super) init_coverage: InitCoverage,
    pub(super) maint_support: MaintSupport,
    pub(super) maint_coverage: MaintCoverage,
    pub(super) maintenance_policy: MaintenancePolicy,
    pub(super) track_hints: Arc<HashMap<ClauseId, MaintenanceTrackHint>>,
    pub(super) maintenance_plan: Option<Arc<MaintenancePlan>>,
    pub(super) present_support_count: Arc<HashMap<ClauseId, usize>>,
    /// Candidate premises cited by each clause's latest Vampire
    /// maintenance proof. A step check is skipped while every
    /// cited premise remains in the Candidate (monotone transfer);
    /// staleness is detected by the subset check at use, so no
    /// invalidation bookkeeping is needed. Untrusted runtime
    /// assistance: final certification revalidates the core.
    pub(super) proof_support_sets: Arc<HashMap<ClauseId, ClauseSet>>,
    /// Private capability for the exact published Active/count/plan state.
    /// Block results retain this identity for constant-time stale-result
    /// rejection; every coherent maintenance-state mutation replaces it.
    pub(super) maintenance_state_revision: Arc<()>,
    pub(super) proposal_generation: u64,
    pub(super) next_generation_ordinal: Option<u64>,
    pub(super) houdini_run_id: u64,
    pub(super) history_baseline_plan: Option<Arc<MaintenancePlan>>,
    pub(super) history_baseline_generation: Option<u64>,
    pub(super) maintenance_failure: Option<FailureReport>,
    pub(super) artifacts: ArtifactStore,
    pub(super) telemetry: TelemetryHandle,
}

impl HoudiniState {
    pub fn new(
        task: &SynthesisTask,
        verification: VerificationParameters,
        admission: SolverAdmission,
        catalog: ClauseCatalog,
    ) -> Result<Self, FailureReport> {
        if catalog.task_identity() != task.identity()
            || admission.policy() != verification.resources()
        {
            return Err(initialization_failure(
                FailureKind::InfrastructureFailure,
                "Houdini task, catalog, verification, and admission identities differ",
                Vec::new(),
            ));
        }
        let artifacts = catalog.artifacts().clone();
        let init_coverage = InitCoverage::new(&catalog);
        let maint_support = MaintSupport::new(&catalog, ClauseSet::new())?;
        let maint_coverage = MaintCoverage::new(&catalog, ClauseSet::new())?;
        let history = artifacts.diagnostics().history_mode;
        let maintenance_policy = MaintenancePolicy::single_track().with_history(
            history != HistoryMode::Disabled,
            history == HistoryMode::Strict,
        );
        let houdini_run_id = NEXT_HOUDINI_RUN_ID
            .fetch_update(Ordering::AcqRel, Ordering::Acquire, |current| {
                current.checked_add(1)
            })
            .map_err(|_| {
                initialization_failure(
                    FailureKind::InfrastructureFailure,
                    "Houdini run identity space is exhausted",
                    Vec::new(),
                )
            })?;
        Ok(Self {
            verification,
            admission,
            catalog,
            core: Arc::new(ClauseSet::new()),
            init_candidates: Arc::new(ClauseSet::new()),
            active: Arc::new(ClauseSet::new()),
            candidate_snapshot: None,
            bulk_init_proved: false,
            bulk_maint_proved: false,
            bulk_maint_capability: None,
            last_term_status: LastTermStatus::Pending,
            init_coverage,
            maint_support,
            maint_coverage,
            maintenance_policy,
            track_hints: Arc::new(HashMap::new()),
            maintenance_plan: None,
            present_support_count: Arc::new(std::collections::HashMap::new()),
            proof_support_sets: Arc::new(std::collections::HashMap::new()),
            maintenance_state_revision: Arc::new(()),
            proposal_generation: 0,
            next_generation_ordinal: Some(0),
            houdini_run_id,
            history_baseline_plan: None,
            history_baseline_generation: None,
            maintenance_failure: None,
            artifacts,
            telemetry: TelemetryHandle::disabled(),
        })
    }

    /// Attach one observational telemetry sink.
    ///
    /// Telemetry is disabled by default and never contributes to Houdini's
    /// semantic state or result.
    pub fn attach_telemetry(&mut self, telemetry: TelemetryHandle) {
        self.telemetry = telemetry;
    }

    pub fn verification(&self) -> &VerificationParameters {
        &self.verification
    }

    pub fn admission(&self) -> &SolverAdmission {
        &self.admission
    }

    pub fn catalog(&self) -> &ClauseCatalog {
        &self.catalog
    }

    pub fn core(&self) -> &ClauseSet {
        self.core.as_ref()
    }

    pub fn init_candidates(&self) -> &ClauseSet {
        self.init_candidates.as_ref()
    }

    pub fn active(&self) -> &ClauseSet {
        self.active.as_ref()
    }

    pub fn bulk_init_proved(&self) -> bool {
        self.bulk_init_proved
    }

    pub fn bulk_maint_proved(&self) -> bool {
        self.bulk_maint_proved
    }

    pub fn last_term_status(&self) -> &LastTermStatus {
        &self.last_term_status
    }

    pub fn init_coverage(&self) -> &InitCoverage {
        &self.init_coverage
    }

    pub fn insert_init_coverage(
        &mut self,
        source: ClauseId,
        target: ClauseId,
    ) -> Result<bool, FailureReport> {
        self.require_unprepared_relations("InitCoverage")?;
        self.init_coverage.insert(&self.catalog, source, target)
    }

    pub fn close_init_coverage(&mut self) -> Result<(), FailureReport> {
        self.require_unprepared_relations("InitCoverage")?;
        close_init_coverage(&mut self.init_coverage);
        Ok(())
    }

    pub fn init_coverage_is_closed(&self) -> bool {
        self.init_coverage.is_transitively_closed()
    }

    pub fn maint_support(&self) -> &MaintSupport {
        &self.maint_support
    }

    pub fn maint_coverage(&self) -> &MaintCoverage {
        &self.maint_coverage
    }

    pub fn maintenance_policy(&self) -> &MaintenancePolicy {
        &self.maintenance_policy
    }

    pub fn maintenance_plan(&self) -> Option<&Arc<MaintenancePlan>> {
        self.maintenance_plan.as_ref()
    }

    pub fn present_support_count(&self, target: ClauseId) -> Option<usize> {
        self.present_support_count.get(&target).copied()
    }

    /// Absorb proof-cited premise sets settled by one maintenance
    /// block. Later entries for a clause replace earlier ones.
    pub(super) fn record_proof_supports(&mut self, settled: HashMap<ClauseId, ClauseSet>) {
        if settled.is_empty() {
            return;
        }
        Arc::make_mut(&mut self.proof_support_sets).extend(settled);
    }

    pub fn has_present_support(&self, target: ClauseId) -> bool {
        self.present_support_count(target)
            .is_some_and(|count| count > 0)
    }

    pub fn proposal_generation(&self) -> u64 {
        self.proposal_generation
    }

    pub fn set_maintenance_policy(
        &mut self,
        policy: MaintenancePolicy,
    ) -> Result<(), FailureReport> {
        if !self.active.is_empty() || self.maintenance_plan.is_some() {
            return Err(super::maintenance::maintenance_invariant(
                "maintenance policy cannot change during a prepared run",
            ));
        }
        let history = self.artifacts.diagnostics().history_mode;
        let history_matches_backend = policy.log_maintenance_history()
            == (history != HistoryMode::Disabled)
            && policy.fail_on_history_log_error() == (history == HistoryMode::Strict);
        if !history_matches_backend {
            return Err(super::maintenance::maintenance_invariant(
                "maintenance policy history flags must match the ArtifactStore history mode",
            ));
        }
        self.maintenance_policy = policy;
        Ok(())
    }

    /// Select a frontend-specific schedule while retaining backend-owned
    /// history semantics. History flags are never a synthesis policy choice.
    pub fn set_maintenance_schedule_policy(
        &mut self,
        coverage_mode: super::maintenance::CoverageMode,
        track_layout: super::maintenance::TrackLayout,
        coverage_lookup: super::maintenance::CoverageLookup,
    ) -> Result<(), FailureReport> {
        let history = self.artifacts.diagnostics().history_mode;
        // One paired query per track: with the W track set aside,
        // the ordinary tracks fill the remaining INV process pairs.
        let ordinary_tracks = (self.verification.resources().max_inv_vampire_processes() / 2)
            .saturating_sub(1)
            .max(1);
        let policy = MaintenancePolicy::new(coverage_mode, track_layout, coverage_lookup)
            .with_ordinary_track_count(ordinary_tracks)
            .map_err(|detail| {
                initialization_failure(
                    FailureKind::StateInvariantViolation,
                    format!("maintenance schedule policy rejected: {detail}"),
                    Vec::new(),
                )
            })?
            .with_history(
                history != HistoryMode::Disabled,
                history == HistoryMode::Strict,
            );
        self.set_maintenance_policy(policy)
    }

    pub fn set_track_hint(
        &mut self,
        clause: ClauseId,
        hint: MaintenanceTrackHint,
    ) -> Result<(), FailureReport> {
        if !self.active.is_empty() || self.maintenance_plan.is_some() {
            return Err(super::maintenance::maintenance_invariant(
                "track hints cannot change during a prepared run",
            ));
        }
        self.catalog.record(clause)?;
        Arc::make_mut(&mut self.track_hints).insert(clause, hint);
        Ok(())
    }

    pub fn insert_maint_support(
        &mut self,
        source: ClauseId,
        target: ClauseId,
    ) -> Result<bool, FailureReport> {
        self.require_unprepared_relations("MaintSupport")?;
        self.maint_support.insert(&self.catalog, source, target)
    }

    pub fn has_maint_support(&self, source: ClauseId, target: ClauseId) -> bool {
        self.maint_support.contains(source, target)
    }

    pub fn insert_maint_coverage(
        &mut self,
        source: ClauseId,
        target: ClauseId,
    ) -> Result<bool, FailureReport> {
        self.require_unprepared_relations("MaintCoverage")?;
        self.maint_coverage.insert(&self.catalog, source, target)
    }

    fn require_unprepared_relations(&self, relation: &str) -> Result<(), FailureReport> {
        if !self.active.is_empty() || self.maintenance_plan.is_some() {
            return Err(super::maintenance::maintenance_invariant(format!(
                "{relation} cannot change during a prepared run"
            )));
        }
        Ok(())
    }

    pub fn maintenance_failure(&self) -> Option<&FailureReport> {
        self.maintenance_failure.as_ref()
    }

    pub fn artifacts(&self) -> &ArtifactStore {
        &self.artifacts
    }

    /// Retain an exact subset of the current initialization candidates.
    ///
    /// This caller-neutral boundary lets a proposal frontend remove durable
    /// source-specific exclusions before initialization without teaching
    /// generic Houdini where its clauses came from.
    pub fn retain_init_candidates(&mut self, retained: ClauseSet) -> Result<(), FailureReport> {
        if !self.active.is_empty() || self.maintenance_plan.is_some() {
            return Err(initialization_failure(
                FailureKind::StateInvariantViolation,
                "initialization candidates cannot change during maintenance",
                Vec::new(),
            ));
        }
        if !retained.is_subset(self.init_candidates.as_ref()) {
            return Err(initialization_failure(
                FailureKind::StateInvariantViolation,
                "retained initialization candidates are not a subset of the current set",
                Vec::new(),
            ));
        }
        for id in &retained {
            self.catalog.record(*id)?;
            if self.core.contains(id) {
                return Err(initialization_failure(
                    FailureKind::StateInvariantViolation,
                    "a retained initialization candidate is already in Core",
                    Vec::new(),
                ));
            }
        }
        self.init_candidates = Arc::new(retained);
        self.bulk_init_proved = false;
        self.bulk_maint_proved = false;
        self.bulk_maint_capability = None;
        Ok(())
    }

    /// Restore already initialized, non-Core clauses before maintenance.
    ///
    /// The operation performs no solver query. It is used by frontends whose
    /// durable clauses are admitted independently from the current proposal.
    pub fn restore_initialized_candidates(
        &mut self,
        restored: &ClauseSet,
    ) -> Result<(), FailureReport> {
        if !self.active.is_empty() || self.maintenance_plan.is_some() {
            return Err(initialization_failure(
                FailureKind::StateInvariantViolation,
                "initialized candidates cannot be restored during maintenance",
                Vec::new(),
            ));
        }
        let mut next = self.init_candidates.as_ref().clone();
        for id in restored {
            if self.core.contains(id) {
                continue;
            }
            let record = self.catalog.record(*id)?;
            if record.initialization() != InitializationStatus::InitProved
                || record.formula_body().is_none()
            {
                return Err(initialization_failure(
                    FailureKind::StateInvariantViolation,
                    format!(
                        "restored clause {} is not a prepared InitProved clause",
                        id.get()
                    ),
                    record.initialization_evidence().into_iter().collect(),
                ));
            }
            next.insert(*id);
        }
        self.init_candidates = Arc::new(next);
        self.bulk_init_proved = false;
        self.bulk_maint_proved = false;
        self.bulk_maint_capability = None;
        Ok(())
    }

    /// Mark Term proved from one frontend-justified exact Core member.
    ///
    /// Generic Houdini validates only stopped-state membership and durable
    /// initialization. The frontend owns the theorem which makes that member
    /// sufficient. Final certification independently checks the exact Core.
    pub fn apply_exact_term_shortcut(
        &mut self,
        sufficient_clause: ClauseId,
    ) -> Result<bool, FailureReport> {
        if !matches!(self.last_term_status, LastTermStatus::Pending) {
            return Ok(false);
        }
        if !self.active.is_empty() || self.maintenance_plan.is_some() {
            return Err(initialization_failure(
                FailureKind::StateInvariantViolation,
                "a termination shortcut requires stopped maintenance",
                Vec::new(),
            ));
        }
        if !self.core.contains(&sufficient_clause) {
            return Ok(false);
        }
        let record = self.catalog.record(sufficient_clause)?;
        if record.initialization() != InitializationStatus::InitProved {
            return Err(initialization_failure(
                FailureKind::StateInvariantViolation,
                "a termination shortcut requires an initialized Core member",
                record.initialization_evidence().into_iter().collect(),
            ));
        }
        self.last_term_status = LastTermStatus::Proved;
        Ok(true)
    }

    /// Reopen termination only when newly supplied frontend evidence makes an
    /// exact shortcut applicable to the unchanged Core.
    ///
    /// This does not discard a proved result. It only supersedes an earlier
    /// counterexample or failed solver attempt with a stronger, frontend-owned
    /// theorem path which final certification will independently check.
    pub(crate) fn reopen_term_for_exact_shortcut(
        &mut self,
        sufficient_clause: ClauseId,
    ) -> Result<bool, FailureReport> {
        if !self.active.is_empty() || self.maintenance_plan.is_some() {
            return Err(initialization_failure(
                FailureKind::StateInvariantViolation,
                "reopening an exact termination shortcut requires stopped maintenance",
                Vec::new(),
            ));
        }
        if !self.core.contains(&sufficient_clause)
            || matches!(
                self.last_term_status,
                LastTermStatus::Pending | LastTermStatus::Proved
            )
        {
            return Ok(false);
        }
        let record = self.catalog.record(sufficient_clause)?;
        if record.initialization() != InitializationStatus::InitProved {
            return Err(initialization_failure(
                FailureKind::StateInvariantViolation,
                "reopening an exact termination shortcut requires an initialized Core member",
                record.initialization_evidence().into_iter().collect(),
            ));
        }
        self.last_term_status = LastTermStatus::Pending;
        Ok(true)
    }

    /// Retain the first frontend failure in the same stopped-state field used
    /// by generic initialization and maintenance.
    pub(crate) fn record_frontend_failure(&mut self, report: FailureReport) {
        self.telemetry
            .record_error(format!("houdini frontend failure: {report:?}"));
        self.clear_maintenance_publication();
        if self.maintenance_failure.is_none() {
            self.maintenance_failure = Some(report);
        }
    }

    /// Record drops, register one proposal, and publish only complete bodies
    /// as the next initialization candidates.
    pub async fn prepare_init_candidates(
        &mut self,
        proposed: impl IntoIterator<Item = ClauseFormula>,
        dropped: &ClauseSet,
        cancellation: &CancellationToken,
    ) -> InitializationInvocationOutcome {
        self.prepare_init_candidates_with_timing(proposed, dropped, cancellation)
            .await
            .0
    }

    pub(crate) async fn prepare_init_candidates_with_timing(
        &mut self,
        proposed: impl IntoIterator<Item = ClauseFormula>,
        dropped: &ClauseSet,
        cancellation: &CancellationToken,
    ) -> (InitializationInvocationOutcome, RegistrationTiming) {
        self.clear_maintenance_publication();
        self.proposal_generation = match self.proposal_generation.checked_add(1) {
            Some(generation) => generation,
            None => {
                return (
                    self.finish_fatal(initialization_failure(
                        FailureKind::StateInvariantViolation,
                        "proposal generation space is exhausted",
                        Vec::new(),
                    )),
                    RegistrationTiming::default(),
                );
            }
        };
        if !dropped.is_disjoint(self.core.as_ref()) {
            return (
                self.finish_fatal(initialization_failure(
                    FailureKind::StateInvariantViolation,
                    "a Core clause cannot be recorded as an explicit proposal drop",
                    Vec::new(),
                )),
                RegistrationTiming::default(),
            );
        }
        if let Err(report) =
            self.catalog
                .record_clause_drops(dropped, &ClauseSet::new(), self.proposal_generation)
        {
            return (self.finish_fatal(report), RegistrationTiming::default());
        }
        let (registered, timing) =
            register_clauses_with_timing(&self.catalog, &self.admission, proposed, cancellation)
                .await;
        let outcome = match registered {
            RegisteredClauses::Complete(clauses) => {
                // A response that both drops and proposes the same historical
                // clause keeps the explicit drop. Only a later proposal can
                // opt that clause back into an epoch.
                let explicitly_proposed =
                    clauses.difference(dropped).copied().collect::<ClauseSet>();
                if let Err(report) = self.catalog.record_clause_drops(
                    &ClauseSet::new(),
                    &explicitly_proposed,
                    self.proposal_generation,
                ) {
                    return (self.finish_fatal(report), timing);
                }
                self.init_candidates = Arc::new(
                    clauses
                        .iter()
                        .filter(|id| !dropped.contains(id) && !self.core.contains(id))
                        .copied()
                        .collect::<ClauseSet>(),
                );
                InitializationInvocationOutcome::Complete
            }
            RegisteredClauses::Failure { report, .. } => self.finish_fatal(report),
            RegisteredClauses::Cancelled { .. } => InitializationInvocationOutcome::Cancelled,
        };
        (outcome, timing)
    }

    fn clear_maintenance_publication(&mut self) {
        self.active = Arc::new(ClauseSet::new());
        self.candidate_snapshot = None;
        self.present_support_count = Arc::new(HashMap::new());
        self.maintenance_plan = None;
        self.maintenance_state_revision = Arc::new(());
        self.history_baseline_plan = None;
        self.history_baseline_generation = None;
        self.bulk_init_proved = false;
        self.bulk_maint_proved = false;
        self.bulk_maint_capability = None;
    }

    fn finish_fatal(&mut self, report: FailureReport) -> InitializationInvocationOutcome {
        self.init_candidates = Arc::new(ClauseSet::new());
        self.active = Arc::new(ClauseSet::new());
        self.candidate_snapshot = None;
        self.present_support_count = Arc::new(HashMap::new());
        self.maintenance_plan = None;
        self.maintenance_state_revision = Arc::new(());
        self.history_baseline_plan = None;
        self.history_baseline_generation = None;
        self.bulk_init_proved = false;
        self.bulk_maint_proved = false;
        self.bulk_maint_capability = None;
        let run_global = report.scope() == FailureScope::RunGlobal;
        self.maintenance_failure = Some(report.clone());
        if run_global {
            InitializationInvocationOutcome::RunFailure(report)
        } else {
            InitializationInvocationOutcome::Complete
        }
    }
}

/// Runtime control remains outside logical initialization classifications.
#[derive(Clone, Debug)]
pub enum InitializationInvocationOutcome {
    Complete,
    Cancelled,
    RunFailure(FailureReport),
}

// ------------------------------------------------------------
// Initialization Orchestration
// ------------------------------------------------------------

/// Classify every current initialization candidate without publishing Active.
pub async fn check_initialization(
    task: &SynthesisTask,
    state: &mut HoudiniState,
    command: VampireWorkerCommand,
    cancellation: &CancellationToken,
) -> InitializationInvocationOutcome {
    if state.maintenance_failure.is_some() || state.init_candidates.is_empty() {
        return InitializationInvocationOutcome::Complete;
    }
    if let Err(report) = validate_state(task, state) {
        return state.finish_fatal(report);
    }
    if cancellation.is_cancelled() {
        return InitializationInvocationOutcome::Cancelled;
    }

    state.bulk_init_proved = false;
    let work = match state
        .catalog
        .select_initialization_work(&state.init_candidates)
    {
        Ok(work) => work,
        Err(report) => return state.finish_fatal(report),
    };
    if work.is_empty() {
        return InitializationInvocationOutcome::Complete;
    }

    if !state.verification.bulk_init_limit.is_zero() {
        let outcome = bulk_init_check(task, state, &work, command.clone(), cancellation).await;
        if !matches!(outcome, InitializationInvocationOutcome::Complete)
            || state.maintenance_failure.is_some()
            || state.bulk_init_proved
        {
            return outcome;
        }
    }
    per_clause_init_check(task, state, command, cancellation).await
}

async fn bulk_init_check(
    task: &SynthesisTask,
    state: &mut HoudiniState,
    targets: &ClauseSet,
    command: VampireWorkerCommand,
    cancellation: &CancellationToken,
) -> InitializationInvocationOutcome {
    let unresolved = match apply_init_coverage(state, targets) {
        Ok(unresolved) => unresolved,
        Err(report) => return state.finish_fatal(report),
    };
    if unresolved.is_empty() {
        state.bulk_init_proved = true;
        return InitializationInvocationOutcome::Complete;
    }

    let artifacts = initialization_artifacts(state).scoped(ScopeTag::named("bulk"));
    let precondition = match prepare_precondition(task, state, &artifacts, cancellation).await {
        Ok(body) => body,
        Err(EncodingError::Cancelled) => return InitializationInvocationOutcome::Cancelled,
        Err(EncodingError::Failure(report)) => return state.finish_fatal(report),
    };
    let goals = match sorted_formula_bodies(&state.catalog, &unresolved) {
        Ok(goals) => goals,
        Err(report) => return state.finish_fatal(report),
    };
    let entailment = match assemble_entailment(
        state.catalog.encoding_context(),
        &state.admission,
        &artifacts,
        vec![precondition],
        goals,
        cancellation,
    )
    .await
    {
        Ok(entailment) => entailment,
        Err(EncodingError::Cancelled) => return InitializationInvocationOutcome::Cancelled,
        Err(EncodingError::Failure(report)) => return state.finish_fatal(report),
    };

    state
        .telemetry
        .increment("houdini.initialization.proof_and_fmb_requests", 1);
    let query_started = state.telemetry.is_enabled().then(Instant::now);
    let outcome = check_entailment(
        &entailment,
        &artifacts,
        Some(state.verification.bulk_init_limit),
        VampireMode::ProofAndFmb(FmbOptions::default()),
        command,
        state.admission.clone(),
        cancellation.clone(),
    )
    .await;
    record_initialization_query(
        &state.telemetry,
        "bulk",
        initialization_outcome_name(&outcome),
        &sorted_ids(&unresolved),
        query_started.map_or(Duration::ZERO, |started| started.elapsed()),
    );
    match outcome {
        EntailmentInvocationOutcome::Result(EntailmentCheckResult::Proved {
            proof,
            empty_evidence,
        }) => {
            let references = vec![
                entailment.query_artifact(),
                proof.output(),
                empty_evidence.artifact(),
            ];
            let evidence = match publish_initialization_evidence(
                &artifacts,
                "bulk",
                sorted_ids(&unresolved),
                "proved",
                &references,
                Value::Null,
            ) {
                Ok(evidence) => evidence,
                Err(report) => return state.finish_fatal(report),
            };
            for id in sorted_ids(&unresolved) {
                if let Err(report) = state.catalog.record_initialization(
                    id,
                    InitializationStatus::InitProved,
                    evidence,
                ) {
                    return state.finish_fatal(report);
                }
            }
            state
                .telemetry
                .record_initialized_clauses(unresolved.iter().map(|id| id.get()));
            state.bulk_init_proved = true;
            InitializationInvocationOutcome::Complete
        }
        EntailmentInvocationOutcome::Result(result) => {
            let (outcome, references, detail) = nonproof_evidence(&entailment, &result);
            if let Err(report) = publish_initialization_evidence(
                &artifacts,
                "bulk",
                sorted_ids(&unresolved),
                outcome,
                &references,
                detail,
            ) {
                return state.finish_fatal(report);
            }
            state.bulk_init_proved = false;
            InitializationInvocationOutcome::Complete
        }
        EntailmentInvocationOutcome::Cancelled(_) => InitializationInvocationOutcome::Cancelled,
        EntailmentInvocationOutcome::RunFailure(report) => state.finish_fatal(report),
    }
}

async fn per_clause_init_check(
    task: &SynthesisTask,
    state: &mut HoudiniState,
    command: VampireWorkerCommand,
    cancellation: &CancellationToken,
) -> InitializationInvocationOutcome {
    state.bulk_init_proved = false;
    let unresolved = match state
        .catalog
        .select_initialization_work(&state.init_candidates)
    {
        Ok(work) => match apply_init_coverage(state, &work) {
            Ok(work) => work.into_iter().collect::<BTreeSet<_>>(),
            Err(report) => return state.finish_fatal(report),
        },
        Err(report) => return state.finish_fatal(report),
    };
    if unresolved.is_empty() {
        return InitializationInvocationOutcome::Complete;
    }

    let stage = initialization_artifacts(state);
    let precondition = match prepare_precondition(task, state, &stage, cancellation).await {
        Ok(body) => body,
        Err(EncodingError::Cancelled) => return InitializationInvocationOutcome::Cancelled,
        Err(EncodingError::Failure(report)) => return state.finish_fatal(report),
    };
    let mut unresolved = unresolved;
    let attempt_limits = state.verification.init_attempt_limits();
    let initial_attempt_limit = *attempt_limits
        .first()
        .expect("the effective initialization ladder is nonempty");
    let window = (state.admission.policy().max_inv_vampire_processes() / 2).max(1);
    for (tier, attempt_limit) in attempt_limits.iter().enumerate() {
        let is_final_tier = tier + 1 == attempt_limits.len();
        let mut deferred = BTreeSet::new();
        // Concurrent paired queries with strictly serialized result
        // application in launch order: catalog evolution is a
        // deterministic function of the per-query outcomes. Tasks
        // observe only the block token; caller cancellation reaches
        // them through it, and every exit path joins all tasks so no
        // solver process survives this loop.
        let block_cancellation = CancellationToken::new();
        let mut in_flight: VecDeque<(ClauseId, tokio::task::JoinHandle<InitQueryOutput>)> =
            VecDeque::new();
        loop {
            while in_flight.len() < window {
                let Some(id) = unresolved.pop_first() else {
                    break;
                };
                let current = match state.catalog.record(id) {
                    Ok(record) => record,
                    Err(report) => {
                        block_cancellation.cancel();
                        drain_init_queries(in_flight).await;
                        return state.finish_fatal(report);
                    }
                };
                if !matches!(
                    current.initialization(),
                    InitializationStatus::Unclassified | InitializationStatus::InitInconclusive
                ) {
                    continue;
                }
                let Some(goal) = current.formula_body().cloned() else {
                    block_cancellation.cancel();
                    drain_init_queries(in_flight).await;
                    return state.finish_fatal(initialization_failure(
                        FailureKind::StateInvariantViolation,
                        format!("clause {} lacks its prepared formula body", id.get()),
                        Vec::new(),
                    ));
                };
                state
                    .telemetry
                    .increment("houdini.initialization.proof_and_fmb_requests", 1);
                state.telemetry.record_clause_solver_attempt(id.get());
                let artifacts = stage.scoped(ScopeTag::Clause(id.get()));
                let context = state.catalog.encoding_context().clone();
                let admission = state.admission.clone();
                let precondition = precondition.clone();
                let command = command.clone();
                let task_cancellation = block_cancellation.clone();
                let attempt_limit = *attempt_limit;
                let handle = tokio::spawn(async move {
                    let started = Instant::now();
                    let entailment = match assemble_entailment(
                        &context,
                        &admission,
                        &artifacts,
                        vec![precondition],
                        vec![goal],
                        &task_cancellation,
                    )
                    .await
                    {
                        Ok(entailment) => entailment,
                        Err(EncodingError::Cancelled) => {
                            return InitQueryOutput {
                                elapsed: started.elapsed(),
                                phase: InitQueryPhase::AssembleCancelled,
                            };
                        }
                        Err(EncodingError::Failure(report)) => {
                            return InitQueryOutput {
                                elapsed: started.elapsed(),
                                phase: InitQueryPhase::AssembleFailed(report),
                            };
                        }
                    };
                    let outcome = check_entailment(
                        &entailment,
                        &artifacts,
                        VampireSearchBudget::cumulative(initial_attempt_limit, attempt_limit),
                        VampireMode::ProofAndFmb(FmbOptions::default()),
                        command,
                        admission,
                        task_cancellation,
                    )
                    .await;
                    InitQueryOutput {
                        elapsed: started.elapsed(),
                        phase: InitQueryPhase::Checked {
                            entailment: Box::new(entailment),
                            outcome,
                        },
                    }
                });
                in_flight.push_back((id, handle));
            }
            let Some((id, handle)) = in_flight.pop_front() else {
                break;
            };
            let mut handle = handle;
            let joined = tokio::select! {
                biased;
                _ = cancellation.cancelled() => {
                    block_cancellation.cancel();
                    in_flight.push_front((id, handle));
                    drain_init_queries(in_flight).await;
                    return InitializationInvocationOutcome::Cancelled;
                }
                joined = &mut handle => joined,
            };
            let output = match joined {
                Ok(output) => output,
                Err(error) => {
                    block_cancellation.cancel();
                    drain_init_queries(in_flight).await;
                    return state.finish_fatal(initialization_failure(
                        FailureKind::StateInvariantViolation,
                        format!(
                            "initialization query task for clause {} failed: {error}",
                            id.get()
                        ),
                        Vec::new(),
                    ));
                }
            };
            let (entailment, outcome) = match output.phase {
                InitQueryPhase::AssembleCancelled => {
                    block_cancellation.cancel();
                    drain_init_queries(in_flight).await;
                    return InitializationInvocationOutcome::Cancelled;
                }
                InitQueryPhase::AssembleFailed(report) => {
                    block_cancellation.cancel();
                    drain_init_queries(in_flight).await;
                    return state.finish_fatal(report);
                }
                InitQueryPhase::Checked {
                    entailment,
                    outcome,
                } => (entailment, outcome),
            };
            let current = match state.catalog.record(id) {
                Ok(record) => record,
                Err(report) => {
                    block_cancellation.cancel();
                    drain_init_queries(in_flight).await;
                    return state.finish_fatal(report);
                }
            };
            let covered_in_flight = !matches!(
                current.initialization(),
                InitializationStatus::Unclassified | InitializationStatus::InitInconclusive
            );
            let defer = !covered_in_flight
                && !is_final_tier
                && matches!(
                    outcome,
                    EntailmentInvocationOutcome::Result(EntailmentCheckResult::TimedOut { .. })
                );
            record_initialization_query(
                &state.telemetry,
                "clause",
                if defer {
                    "deferred"
                } else {
                    initialization_outcome_name(&outcome)
                },
                std::slice::from_ref(&id),
                output.elapsed,
            );
            if covered_in_flight {
                state
                    .telemetry
                    .increment("houdini.initialization.covered_in_flight", 1);
                continue;
            }
            if defer {
                state
                    .telemetry
                    .increment("houdini.initialization.first_tier_deferrals", 1);
                deferred.insert(id);
                continue;
            }
            let result = match outcome {
                EntailmentInvocationOutcome::Result(result) => result,
                EntailmentInvocationOutcome::Cancelled(_) => {
                    block_cancellation.cancel();
                    drain_init_queries(in_flight).await;
                    return InitializationInvocationOutcome::Cancelled;
                }
                EntailmentInvocationOutcome::RunFailure(report) => {
                    block_cancellation.cancel();
                    drain_init_queries(in_flight).await;
                    return state.finish_fatal(report);
                }
            };
            let (status, outcome_name, references, detail) = classification(&entailment, &result);
            let artifacts = stage.scoped(ScopeTag::Clause(id.get()));
            let evidence = match publish_initialization_evidence(
                &artifacts,
                "clause",
                vec![id],
                outcome_name,
                &references,
                detail,
            ) {
                Ok(evidence) => evidence,
                Err(report) => {
                    block_cancellation.cancel();
                    drain_init_queries(in_flight).await;
                    return state.finish_fatal(report);
                }
            };
            if let Err(report) = state.catalog.record_initialization(id, status, evidence) {
                block_cancellation.cancel();
                drain_init_queries(in_flight).await;
                return state.finish_fatal(report);
            }
            if status == InitializationStatus::InitProved {
                state.telemetry.record_initialized_clauses([id.get()]);
            }
            if status == InitializationStatus::InitProved
                && (!unresolved.is_empty() || !deferred.is_empty())
            {
                let remaining = unresolved
                    .iter()
                    .chain(deferred.iter())
                    .copied()
                    .collect::<ClauseSet>();
                let still_unresolved = match apply_init_coverage_from_source(state, id, &remaining)
                {
                    Ok(work) => work,
                    Err(report) => {
                        block_cancellation.cancel();
                        drain_init_queries(in_flight).await;
                        return state.finish_fatal(report);
                    }
                };
                unresolved = still_unresolved
                    .into_iter()
                    .filter(|clause| !deferred.contains(clause))
                    .collect();
            }
        }
        unresolved = deferred;
        if unresolved.is_empty() {
            break;
        }
    }
    InitializationInvocationOutcome::Complete
}

/// One concurrently executed per-clause initialization query.
struct InitQueryOutput {
    elapsed: Duration,
    phase: InitQueryPhase,
}

#[allow(clippy::large_enum_variant)]
enum InitQueryPhase {
    Checked {
        entailment: Box<crate::entailment::Entailment>,
        outcome: EntailmentInvocationOutcome,
    },
    AssembleCancelled,
    AssembleFailed(FailureReport),
}

/// Join every in-flight query without applying its result. The
/// block cancellation token is already cancelled, so the underlying
/// solver runs terminate through their normal cancellation path.
async fn drain_init_queries(
    mut in_flight: VecDeque<(ClauseId, tokio::task::JoinHandle<InitQueryOutput>)>,
) {
    while let Some((_, handle)) = in_flight.pop_front() {
        let _ = handle.await;
    }
}

// ------------------------------------------------------------
// Coverage And Evidence Publication
// ------------------------------------------------------------

fn apply_init_coverage(
    state: &mut HoudiniState,
    targets: &ClauseSet,
) -> Result<ClauseSet, FailureReport> {
    let pairs = state
        .init_coverage
        .covering_proved_pairs(&state.catalog, targets)?;
    record_init_coverage(state, targets, pairs)
}

fn apply_init_coverage_from_source(
    state: &mut HoudiniState,
    source: ClauseId,
    targets: &ClauseSet,
) -> Result<ClauseSet, FailureReport> {
    let pairs = state
        .init_coverage
        .covering_pairs_from_source(&state.catalog, source, targets)?;
    record_init_coverage(state, targets, pairs)
}

fn record_init_coverage(
    state: &mut HoudiniState,
    targets: &ClauseSet,
    pairs: Vec<(ClauseId, ClauseId)>,
) -> Result<ClauseSet, FailureReport> {
    if pairs.is_empty() {
        return Ok(targets.clone());
    }
    let mut references = Vec::new();
    for (_, source) in &pairs {
        let source_record = state.catalog.record(*source)?;
        let source_evidence = source_record.initialization_evidence().ok_or_else(|| {
            initialization_failure(
                FailureKind::StateInvariantViolation,
                format!("InitProved source {} lacks durable evidence", source.get()),
                Vec::new(),
            )
        })?;
        references.push(source_evidence);
    }
    references.sort_unstable_by_key(|reference| reference.local_id());
    references.dedup();
    let covered = pairs
        .iter()
        .map(|(target, _)| *target)
        .collect::<ClauseSet>();
    let evidence = publish_initialization_evidence(
        &initialization_artifacts(state).scoped(ScopeTag::named("coverage")),
        "coverage",
        sorted_ids(&covered),
        "proved",
        &references,
        json!({
            "transfers": pairs
                .iter()
                .map(|(target, source)| json!({
                    "target_clause_id": target.get(),
                    "source_clause_id": source.get(),
                }))
                .collect::<Vec<_>>(),
        }),
    )?;
    for (target, _) in pairs {
        state
            .catalog
            .record_initialization(target, InitializationStatus::InitProved, evidence)?;
    }
    state
        .telemetry
        .record_initialized_clauses(covered.iter().map(|id| id.get()));
    let covered_count = u64::try_from(covered.len()).unwrap_or(u64::MAX);
    state
        .telemetry
        .increment("houdini.initialization.coverage_shortcuts", covered_count);
    state
        .telemetry
        .record_disposition("initialization_coverage_shortcut", covered_count);
    if state.telemetry.level() == TelemetryLevel::Detailed {
        state.telemetry.event(
            "initialization_coverage_shortcut",
            json!({
                "covered_targets": sorted_ids(&covered).into_iter().map(ClauseId::get).collect::<Vec<_>>(),
                "covered_target_count": covered_count,
            }),
        );
    }
    Ok(targets.difference(&covered).copied().collect())
}

fn publish_initialization_evidence(
    artifacts: &ArtifactStore,
    check: &str,
    clause_ids: Vec<ClauseId>,
    outcome: &str,
    references: &[ArtifactRef],
    detail: Value,
) -> Result<ArtifactRef, FailureReport> {
    let payload = json!({
        "kind": "initialization_check",
        "check": check,
        "clauses": clause_ids.into_iter().map(ClauseId::get).collect::<Vec<_>>(),
        "outcome": outcome,
        "references": references.iter().map(artifact_json).collect::<Vec<_>>(),
        "detail": detail,
    });
    artifacts
        .publish(
            ArtifactKind::InitializationCheck,
            payload.to_string().into_bytes().into_boxed_slice(),
        )
        .map_err(initialization_publication_failure)
}

fn classification(
    entailment: &crate::entailment::Entailment,
    result: &EntailmentCheckResult,
) -> (InitializationStatus, &'static str, Vec<ArtifactRef>, Value) {
    match result {
        EntailmentCheckResult::Proved {
            proof,
            empty_evidence,
        } => (
            InitializationStatus::InitProved,
            "proved",
            vec![
                entailment.query_artifact(),
                proof.output(),
                empty_evidence.artifact(),
            ],
            Value::Null,
        ),
        EntailmentCheckResult::Refuted(counterexample) => (
            InitializationStatus::InitRefuted,
            "refuted",
            counterexample_references(entailment, counterexample),
            Value::Null,
        ),
        EntailmentCheckResult::TimedOut {
            next_fmb_start_size,
            peer_failure,
        } => (
            InitializationStatus::InitInconclusive,
            "timed_out",
            check_references(entailment, peer_failure.as_ref()),
            json!({
                "next_fmb_start_size": next_fmb_start_size.map(|size| size.get()),
            }),
        ),
        EntailmentCheckResult::Failure {
            report,
            next_fmb_start_size,
        } => (
            InitializationStatus::InitInconclusive,
            "failure",
            check_references(entailment, Some(report)),
            json!({
                "origin": format!("{:?}", report.origin()),
                "failure_kind": format!("{:?}", report.kind()),
                "detail": report.detail(),
                "next_fmb_start_size": next_fmb_start_size.map(|size| size.get()),
            }),
        ),
    }
}

fn initialization_outcome_name(outcome: &EntailmentInvocationOutcome) -> &'static str {
    match outcome {
        EntailmentInvocationOutcome::Result(EntailmentCheckResult::Proved { .. }) => "proved",
        EntailmentInvocationOutcome::Result(EntailmentCheckResult::Refuted(_)) => "refuted",
        EntailmentInvocationOutcome::Result(EntailmentCheckResult::TimedOut { .. }) => "timed_out",
        EntailmentInvocationOutcome::Result(EntailmentCheckResult::Failure { .. })
        | EntailmentInvocationOutcome::RunFailure(_) => "failure",
        EntailmentInvocationOutcome::Cancelled(_) => "canceled",
    }
}

fn record_initialization_query(
    telemetry: &TelemetryHandle,
    check: &'static str,
    outcome: &'static str,
    targets: &[ClauseId],
    duration: Duration,
) {
    if !telemetry.is_enabled() {
        return;
    }
    telemetry.add_duration("houdini.initialization.query_inclusive", duration);
    telemetry.add_duration(
        format!("disposition.initialization_query_{outcome}"),
        duration,
    );
    telemetry.record_disposition(format!("initialization_query_{outcome}"), 1);
    telemetry.record_disposition(format!("initialization_{check}_query_{outcome}"), 1);
    let target_count = u64::try_from(targets.len()).unwrap_or(u64::MAX);
    let target_disposition = match (check, outcome) {
        ("bulk", "proved") | ("clause", "proved") => Some("initialization_proof"),
        ("clause", "refuted") => Some("initialization_refutation"),
        ("clause", "timed_out") => Some("initialization_timeout"),
        ("clause", "failure") => Some("initialization_failure"),
        _ => None,
    };
    if let Some(disposition) = target_disposition {
        telemetry.record_disposition(disposition, target_count);
        for target in targets {
            telemetry.event_with("initialization_target_classified", || {
                json!({
                    "target": target.get(),
                    "check": check,
                    "outcome": outcome,
                    "disposition": disposition,
                })
            });
        }
    }
    if telemetry.level() == TelemetryLevel::Detailed {
        telemetry.event(
            "initialization_query_classified",
            json!({
                "check": check,
                "outcome": outcome,
                "target_count": target_count,
                "inclusive_nanoseconds": duration.as_nanos().min(u128::from(u64::MAX)) as u64,
            }),
        );
    }
}

fn nonproof_evidence(
    entailment: &crate::entailment::Entailment,
    result: &EntailmentCheckResult,
) -> (&'static str, Vec<ArtifactRef>, Value) {
    let (_, outcome, references, detail) = classification(entailment, result);
    (outcome, references, detail)
}

fn counterexample_references(
    entailment: &crate::entailment::Entailment,
    counterexample: &EntailmentCounterexample,
) -> Vec<ArtifactRef> {
    let mut references = vec![entailment.query_artifact()];
    if let Some(model) = counterexample.model() {
        references.push(model.output());
    }
    if let Some(evidence) = counterexample.empty_evidence() {
        references.push(evidence);
    }
    references
}

fn check_references(
    entailment: &crate::entailment::Entailment,
    failure: Option<&FailureReport>,
) -> Vec<ArtifactRef> {
    let mut references = vec![entailment.query_artifact()];
    if let Some(failure) = failure {
        references.extend_from_slice(failure.artifact_references());
    }
    references.sort_unstable_by_key(|reference| reference.local_id());
    references.dedup();
    references
}

fn artifact_json(reference: &ArtifactRef) -> Value {
    json!({
        "backend": reference.backend_id().to_string(),
        "local_id": reference.local_id(),
        "kind": format!("{:?}", reference.kind()),
    })
}

fn initialization_publication_failure(report: FailureReport) -> FailureReport {
    let kind = if report.kind() == FailureKind::PublicationFailure {
        FailureKind::PublicationFailure
    } else {
        FailureKind::InfrastructureFailure
    };
    FailureReport::try_new(
        crate::failure::FailureOrigin::InitializationExecution,
        kind,
        false,
        report.scope(),
        Some(format!(
            "publish initialization evidence: {}",
            report.detail().unwrap_or("artifact backend failure")
        )),
        report.artifact_references().to_vec(),
    )
    .expect("initialization publication maps to a permitted failure")
}

// ------------------------------------------------------------
// Exact Source Assembly
// ------------------------------------------------------------

async fn prepare_precondition(
    task: &SynthesisTask,
    state: &HoudiniState,
    artifacts: &ArtifactStore,
    cancellation: &CancellationToken,
) -> Result<crate::encoding::PreparedBodyRef, EncodingError> {
    let mut bodies = state
        .catalog
        .encoding_context()
        .prepare_solver_bodies(
            &state.admission,
            artifacts,
            vec![SolverBodySource::Assert(
                task.preprocessed_pre_solver().clone(),
            )],
            cancellation,
        )
        .await?;
    debug_assert_eq!(bodies.len(), 1);
    Ok(bodies.remove(0))
}

fn sorted_formula_bodies(
    catalog: &ClauseCatalog,
    ids: &ClauseSet,
) -> Result<Vec<crate::encoding::PreparedBodyRef>, FailureReport> {
    sorted_ids(ids)
        .into_iter()
        .map(|id| {
            catalog.record(id)?.formula_body().cloned().ok_or_else(|| {
                initialization_failure(
                    FailureKind::StateInvariantViolation,
                    format!("clause {} lacks its prepared formula body", id.get()),
                    Vec::new(),
                )
            })
        })
        .collect()
}

fn sorted_ids(ids: &ClauseSet) -> Vec<ClauseId> {
    let mut ids = ids.iter().copied().collect::<Vec<_>>();
    ids.sort_unstable();
    ids
}

fn initialization_artifacts(state: &HoudiniState) -> ArtifactStore {
    state
        .artifacts
        .scoped(ScopeTag::verification_stage("initialization"))
}

fn validate_state(task: &SynthesisTask, state: &HoudiniState) -> Result<(), FailureReport> {
    if state.catalog.task_identity() != task.identity()
        || state.artifacts.task_identity() != task.identity()
        || state.catalog.artifacts().backend_id() != state.artifacts.backend_id()
        || state.catalog.encoding_context().task_identity() != task.identity()
        || state.admission.policy() != state.verification.resources()
    {
        return Err(initialization_failure(
            FailureKind::InfrastructureFailure,
            "initialization task, state, catalog, context, artifacts, and admission differ",
            Vec::new(),
        ));
    }
    if !state.active.is_empty() {
        return Err(initialization_failure(
            FailureKind::StateInvariantViolation,
            "initialization requires an empty Active set",
            Vec::new(),
        ));
    }
    for id in state.init_candidates.iter() {
        state.catalog.record(*id)?;
        if state.core.contains(id) {
            return Err(initialization_failure(
                FailureKind::StateInvariantViolation,
                format!("initialization candidate {} is already in Core", id.get()),
                Vec::new(),
            ));
        }
    }
    Ok(())
}

// ------------------------------------------------------------
// Tests
// ------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn parameters(search_limit: Duration) -> VerificationParameters {
        VerificationParameters::new(
            search_limit,
            crate::runtime::RuntimeResourcePolicy::default_symbolic(),
        )
        .unwrap()
    }

    #[test]
    fn default_init_ladder_is_the_single_full_limit() {
        let verification = parameters(Duration::from_secs(5));
        assert_eq!(
            verification.init_attempt_limits(),
            vec![Duration::from_secs(5)]
        );
    }

    #[test]
    fn init_ladder_appends_the_full_limit_after_first_tiers() {
        let verification = parameters(Duration::from_secs(5))
            .with_init_first_attempt_limits(vec![
                Duration::from_millis(500),
                Duration::from_secs(2),
            ])
            .unwrap();
        assert_eq!(
            verification.init_attempt_limits(),
            vec![
                Duration::from_millis(500),
                Duration::from_secs(2),
                Duration::from_secs(5),
            ]
        );
    }

    #[test]
    fn init_ladder_drops_tiers_at_or_above_the_search_limit() {
        let verification = parameters(Duration::from_secs(1))
            .with_init_first_attempt_limits(vec![Duration::from_secs(1)])
            .unwrap();
        assert_eq!(
            verification.init_attempt_limits(),
            vec![Duration::from_secs(1)]
        );
    }

    #[test]
    fn init_first_tier_validation_rejects_bad_ladders() {
        assert!(
            parameters(Duration::from_secs(5))
                .with_init_first_attempt_limits(vec![Duration::ZERO])
                .is_err()
        );
        assert!(
            parameters(Duration::from_secs(5))
                .with_init_first_attempt_limits(vec![
                    Duration::from_secs(2),
                    Duration::from_secs(2),
                ])
                .is_err()
        );
    }
}
