//! Auditable bottom-up control for fixed-ambient Houdini stabilization.
//!
//! This module owns no logical formula construction.  It operates on opaque
//! admission and snapshot handles and accepts conclusive authority only from
//! a crate-owned checked adapter implementing [`FrameworkIIChecker`].
//!
//! The controller keeps the contract's three partitions — *committed* (the
//! Core, at a fixed level), *dead* (with a reason: refuted, never revived, or
//! dropped by the proposer, revived only by an exact resubmission), and
//! *pending* (everything else, each at a current level) — and runs one
//! bottom-up scan per epoch.

use std::collections::{BTreeMap, BTreeSet};
use std::future::{Future, ready};
use std::pin::Pin;
use std::sync::Arc;
use std::time::Duration;

use crate::failure::FailureReport;
use crate::houdini::ClauseId;
use crate::runtime::CancellationToken;

use super::catalog::{FrameworkIIStateError, LeveledClauseCatalog, RegisteredLeveledClauses};
use super::certificate_profiles::SearchProfileProvenance;
use super::ledger::{
    FrameworkIICheckEvidence, FrameworkIICheckOutcome, FrameworkIICheckRequest,
    FrameworkIICheckRole, FrameworkIIDeadReason, FrameworkIIInvalidationReason, LevelAttemptLedger,
    LevelLedgerRow,
};
use super::snapshot::{LeveledCandidateSnapshot, LeveledCoreHandle};
use super::tools::AgentToolPolicy;
use super::types::FrameworkIILevel;

// ------------------------------------------------------------
// Checked Adapter Boundary
// ------------------------------------------------------------

/// One typed result from the checked production boundary.
///
/// Only `Applied` carries ledger authority. A nonlogical failure stops before
/// any level-attempt row is appended.
#[derive(Clone, Debug)]
pub enum FrameworkIICheckExecution {
    Applied(FrameworkIICheckOutcome),
    Failure(FailureReport),
}

// Replay observations retain actual completion evidence without participating
// in scheduling, placement, proof roots, or the controller ledger.
#[derive(Clone)]
pub(super) struct ReplayTerminationObservation {
    pub ordinal: u64,
    pub core: Arc<LeveledCandidateSnapshot>,
    pub result: Result<FrameworkIICheckExecution, FrameworkIIStateError>,
}

impl std::fmt::Debug for ReplayTerminationObservation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ReplayTerminationObservation")
            .field("ordinal", &self.ordinal)
            .finish_non_exhaustive()
    }
}

/// Crate-owned authority boundary for one exact fixed-ambient obligation.
///
/// A production implementation must call the approved Lean/solver/model
/// validation path.  The pure controller intentionally does not implement
/// `CheckFrameworkIIEntailment`; tests inject a deterministic script here.
pub trait FrameworkIIChecker: sealed::Sealed + Send {
    fn check<'a>(
        &'a mut self,
        request: FrameworkIICheckRequest,
    ) -> Pin<
        Box<
            dyn Future<Output = Result<FrameworkIICheckExecution, FrameworkIIStateError>>
                + Send
                + 'a,
        >,
    >;

    /// Check one whole sweep of a level as a single batch.
    ///
    /// `requests` holds every request of one Phase-1 initialization sweep,
    /// or of one step fixed-point sweep, of a single level, already in
    /// check order; the returned executions are in that same order and of
    /// the same length. `houdini.tex` Section 4.4: "Every Phase-1
    /// initialization sweep and every step sweep of a level is dispatched
    /// as one batch to the worker and solver pools; the single-failure drop
    /// applies to the first failure in check order, and the remaining
    /// outcomes of the batch enter the dictionary."
    ///
    /// The default body runs [`Self::check`] once per request, in order, so
    /// an adapter that cannot dispatch concurrently keeps exactly the
    /// behaviour it had before batching existed. A first error aborts the
    /// batch, as a first error aborted the sequential sweep.
    fn check_batch<'a>(
        &'a mut self,
        requests: Vec<FrameworkIICheckRequest>,
    ) -> Pin<
        Box<
            dyn Future<Output = Result<Vec<FrameworkIICheckExecution>, FrameworkIIStateError>>
                + Send
                + 'a,
        >,
    > {
        Box::pin(async move {
            let mut executions = Vec::with_capacity(requests.len());
            for request in requests {
                executions.push(self.check(request).await?);
            }
            Ok(executions)
        })
    }

    /// Check the termination condition on the epoch's committed clauses.
    ///
    /// `core` is a snapshot containing exactly the committed clauses at their
    /// fixed levels. The controller runs this after every epoch's scan and
    /// returns its outcome as the epoch's outcome; an epoch that did not
    /// change the Core's clause set is expected to be served from the
    /// checker's semantic dictionary without a launch.
    ///
    /// The default body fails closed: a checker that does not build the
    /// termination request cannot silently report a proof.
    fn check_termination<'a>(
        &'a mut self,
        core: Arc<LeveledCandidateSnapshot>,
    ) -> Pin<
        Box<
            dyn Future<Output = Result<FrameworkIICheckExecution, FrameworkIIStateError>>
                + Send
                + 'a,
        >,
    > {
        let _ = core;
        Box::pin(ready(Err(FrameworkIIStateError::InvalidEvidence(
            "termination check not provided by this checker",
        ))))
    }

    /// Open a new epoch.
    ///
    /// The contract grants each semantic key at most one launch per epoch,
    /// so the epoch entry point calls this exactly once at the start of
    /// every epoch, before its first check. Compression's re-stabilization
    /// deliberately does not call it: it belongs to the epoch that
    /// triggered it.
    ///
    /// The default is a no-op: a checker without a per-epoch dictionary
    /// state has nothing to reset.
    fn begin_epoch(&mut self) {}

    /// The run's host limits as this checker was configured with them, or
    /// `None` from a checker that carries no host-limit configuration.
    ///
    /// The run's single source of host limits is its feedback policy
    /// (Pass 7.7b). A checker that keeps its own copy — the production
    /// checker does, for countermodel retention — reports it here so
    /// [`super::search::PreCertificateAgentHoudiniSearch::new`] can reject a
    /// run whose checker and policy disagree, rather than letting the
    /// presentation state one limit while the dictionary applies another.
    /// Test adapters that carry none return the `None` default and are not
    /// checked.
    fn host_limits(&self) -> Option<&super::host_limits::HostLimits> {
        None
    }

    /// The run's solver retry policy (Pass 7.5g).
    ///
    /// Part of the run configuration bound to the artifact store's run
    /// identity, so a resume under a different ladder of solver allowances
    /// fails closed instead of continuing. Test adapters that hold no
    /// dictionary and launch nothing return the `None` default and
    /// contribute an empty policy to the record.
    fn retry_policy(&self) -> Option<&super::production::FrameworkIIRetryPolicy> {
        None
    }

    /// The TPTP role a *retry* launch of this run writes its premises
    /// under.
    ///
    /// Bound to the run identity beside the retry policy, and for the same
    /// reason: it decides which conditions a retry reaches, so a resume
    /// under the other role is a different search and fails closed. Test
    /// adapters that launch nothing return the `None` default, which the
    /// record states as the role every first launch uses.
    fn retry_premise_role(&self) -> Option<crate::entailment::PremiseRole> {
        None
    }

    /// The run's per-condition profile provenance for the conditions of
    /// `core` (Pass 7.5f).
    ///
    /// Pass 7.5f's freeze labels every frozen job with one closed leancheck
    /// profile, read from provenance and never from root tracking: the
    /// winning schedule of the launch the semantic dictionary's proof
    /// entries record as having closed that condition against `core`
    /// itself, or the run's configured search profile for a condition the
    /// search closed without such a launch. `core` is the final Core, and
    /// it is what decides which of several recorded launches labels a
    /// condition.
    ///
    /// The default reports the configured-only provenance of a
    /// deterministic adapter, which holds no dictionary and therefore
    /// records no winner at all.
    fn search_profile_provenance(
        &self,
        _core: &LeveledCandidateSnapshot,
    ) -> SearchProfileProvenance {
        SearchProfileProvenance::configured_only(super::production::ProofSearchProfile::Direct)
    }

    /// Confirm that this checker owns the exact live authorities of a search.
    ///
    /// Deterministic unit-test adapters deliberately retain the fail-closed
    /// default. The production checker overrides this with identity checks for
    /// its Lean context, artifact backend, solver controller, and cancellation
    /// token.
    fn matches_search_runtime(
        &self,
        _solver: &super::solver::FrameworkIISolverContext,
        _artifacts: &crate::artifact::ArtifactStore,
        _admission: &crate::runtime::SolverAdmission,
        _cancellation: &crate::runtime::CancellationToken,
    ) -> bool {
        false
    }
}

/// Adapt a synchronous checked boundary without duplicating controller logic.
pub struct SyncFrameworkIIChecker<F> {
    checker: F,
}

impl<F> SyncFrameworkIIChecker<F> {
    #[cfg(test)]
    pub(crate) fn new(checker: F) -> Self {
        Self { checker }
    }
}

pub(crate) mod sealed {
    pub trait Sealed {}
}

impl<F> sealed::Sealed for SyncFrameworkIIChecker<F> {}

impl<F> FrameworkIIChecker for SyncFrameworkIIChecker<F>
where
    F: FnMut(FrameworkIICheckRequest) -> Result<FrameworkIICheckOutcome, FrameworkIIStateError>
        + Send,
{
    fn check<'a>(
        &'a mut self,
        request: FrameworkIICheckRequest,
    ) -> Pin<
        Box<
            dyn Future<Output = Result<FrameworkIICheckExecution, FrameworkIIStateError>>
                + Send
                + 'a,
        >,
    > {
        Box::pin(ready(
            (self.checker)(request).map(FrameworkIICheckExecution::Applied),
        ))
    }
}

// ------------------------------------------------------------
// The Dead Partition
// ------------------------------------------------------------

/// Why a catalog clause sits in the terminal `dead` partition.
///
/// A dead clause is never checked. `Refuted` is final for the run; `Dropped`
/// is a proposer veto that only an exact resubmission lifts, which returns
/// the clause to pending at its Lean-owned minimum level.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FrameworkIIDeadCause {
    /// A never-committed prophecy-free clause received a Lean-validated
    /// finite refutation of its initialization at some level. The same
    /// countermodel refutes the level-zero initialization (Lean:
    /// `LeveledFamily.initVC_zero_countermodel_of_countermodel`, and
    /// semantically `not_initObligation_zero_of_countermodel`, in
    /// `Whiel/Synthesis/FrameworkII/FixedAmbient/DictionarySoundness.lean`);
    /// for a prophecy-free clause that initialization decides the clause on
    /// every halting input (`Whiel/Hoare/ProphecyFreeInitialization.lean`,
    /// `prophecyFree_holds_on_halting_of_initValid`), which is why the
    /// contract makes the verdict final for the run and never revives the
    /// clause.
    Refuted(FrameworkIIDeadReason),
    /// The proposer dropped the clause. Revived only by an exact
    /// resubmission, at its minimum level.
    Dropped,
}

impl FrameworkIIDeadCause {
    /// The refutation reason, when this clause died by refutation.
    pub fn refutation(self) -> Option<FrameworkIIDeadReason> {
        match self {
            Self::Refuted(reason) => Some(reason),
            Self::Dropped => None,
        }
    }

    /// Whether an exact resubmission may revive this clause.
    pub fn is_revivable(self) -> bool {
        matches!(self, Self::Dropped)
    }
}

// ------------------------------------------------------------
// Mutable Control State
// ------------------------------------------------------------

/// One exact currently usable proof root in the append-only attempt ledger.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CurrentFrameworkIIRoot {
    attempt_row: u64,
    request_digest: Arc<str>,
    partition_digest: Arc<str>,
    proof_evidence: FrameworkIICheckEvidence,
}

impl CurrentFrameworkIIRoot {
    pub fn attempt_row(&self) -> u64 {
        self.attempt_row
    }

    pub fn request_digest(&self) -> &str {
        &self.request_digest
    }

    pub fn partition_digest(&self) -> &str {
        &self.partition_digest
    }

    /// Complete typed evidence that closes this runtime controller check.
    pub fn proof_evidence(&self) -> &FrameworkIICheckEvidence {
        &self.proof_evidence
    }
}

/// Exact current-root coverage for the published Core.
///
/// This is provenance, never an input to a decision: committed clauses are
/// not re-checked during search, so a scan that commits at several levels
/// ordinarily ends with partial coverage. Certification re-proves every
/// condition of the frozen final Core regardless.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FrameworkIIRootCoverage {
    Complete,
    Incomplete {
        missing: Arc<[(ClauseId, FrameworkIICheckRole)]>,
    },
}

impl FrameworkIIRootCoverage {
    pub fn is_complete(&self) -> bool {
        matches!(self, Self::Complete)
    }

    pub fn missing(&self) -> &[(ClauseId, FrameworkIICheckRole)] {
        match self {
            Self::Complete => &[],
            Self::Incomplete { missing } => missing,
        }
    }
}

/// Caller-neutral mutable fixed-ambient placement state.
///
/// This is deliberately separate from flat [`crate::houdini::HoudiniState`]
/// and contains no task-wide F1 initialization or maintenance classification.
#[derive(Debug)]
pub struct LeveledHoudiniState {
    catalog: LeveledClauseCatalog,
    /// The optional level bound. Absent by default; when a host sets one it
    /// is at least 1, a clause whose minimum level exceeds it is rejected at
    /// admission, and no clause is promoted above it.
    max_level: Option<FrameworkIILevel>,
    control_revision: u64,
    committed: BTreeMap<ClauseId, FrameworkIILevel>,
    pending: BTreeMap<ClauseId, FrameworkIILevel>,
    dead: BTreeMap<ClauseId, FrameworkIIDeadCause>,
    /// Every clause the run has ever committed. A formerly committed clause
    /// is never killed by the initialization death rule; it is promoted
    /// instead (this only arises under `compress_core`).
    ever_committed: BTreeSet<ClauseId>,
    /// This epoch's fresh clauses: neither committed nor pending when the
    /// epoch began (a new identity, or a revived dropped clause). Checked
    /// first within every level.
    fresh: BTreeSet<ClauseId>,
    /// This epoch's `Susp` set: clauses whose inconclusive *launch* suspends
    /// their remaining checks for the rest of the epoch. Cleared every epoch.
    suspended: BTreeSet<ClauseId>,
    attempts: LevelAttemptLedger,
    current_roots: BTreeMap<(ClauseId, FrameworkIICheckRole), CurrentFrameworkIIRoot>,
    core: LeveledCoreHandle,
    system_clauses_installed: bool,
    system_clauses: BTreeSet<ClauseId>,
    /// Count of promotions declined because the clause already sat at the
    /// run's level bound, so it stayed pending there.
    max_level_stops_total: u64,
    /// Host option: after an epoch that changed the Core, return every Core
    /// clause except the protected rows to pending at its minimum level and
    /// re-stabilize the Core alone with the dictionary in force. Bound once
    /// at construction, never mutated; the agent path never enables it.
    compress_core: bool,
    /// Host option: the tool set the provider may call during a
    /// consultation. Bound once at construction, never mutated.
    tool_policy: AgentToolPolicy,
    /// Set whenever `committed` changes; cleared once compression has run
    /// against that change.
    compress_core_dirty: bool,
    /// Count of Core clauses that re-converged strictly lower than before.
    compress_core_moves_total: u64,
    /// Count of compression re-stabilizations attempted (moved or not).
    compress_core_attempts_total: u64,
    /// Count of termination checks this run has run.
    ///
    /// This is a run counter only. A refuted termination check is addressed
    /// by the checker's own attempt identifier — the one its retained
    /// countermodel is keyed under and the `countermodel` tool serves — so
    /// the controller keeps no second identifier space and no second copy
    /// of the evidence.
    termination_attempts_total: u64,
    replay_termination_observations: Vec<ReplayTerminationObservation>,
    /// Sum of [`FrameworkIICheckEvidence::preparation_time`] over every check
    /// outcome recorded into `attempts` so far this run. Zero contribution
    /// from a dictionary-reuse or protected-theorem row, both of which
    /// report `None`.
    preparation_time_total: Duration,
    /// Sum of [`FrameworkIICheckEvidence::solver_time`] over every check
    /// outcome recorded into `attempts` so far this run.
    solver_time_total: Duration,
    /// Count of check outcomes recorded into `attempts` so far this run
    /// whose evidence carries a `preparation_time` — one fresh obligation
    /// preparation per count. A preparation is not a worker round trip:
    /// since Pass 7.5d it is spliced from the run's opaque-piece cache and
    /// contacts the worker only on a cache miss. The real round-trip counts
    /// are `FrameworkIISolverContext::piece_cache_stats()`.
    preparations_total: u64,
    /// How a sweep of a level reaches the checked adapter. The contract's
    /// dispatch is one batch per sweep; `Sequential` exists only so a test
    /// can hold everything else fixed. Bound once, never mutated by a scan.
    sweep_dispatch: FrameworkIISweepDispatch,
    /// Count of sweeps dispatched to the checked adapter this run — one per
    /// Phase-1 level and one per step fixed-point sweep under `Batched`, one
    /// per check under `Sequential`.
    dispatched_sweeps_total: u64,
    /// Count of requests carried by those dispatches.
    dispatched_batch_checks_total: u64,
}

/// Fully checked state-side half of one proposal installation. The catalog
/// batch is published only after this private checkpoint exists.
pub(super) struct PreparedFrameworkIIProposalCheckpoint {
    base_control_revision: u64,
    staged: LeveledHoudiniState,
}

impl LeveledHoudiniState {
    /// Construct one empty control state with no level bound.
    pub fn new(catalog: LeveledClauseCatalog) -> Result<Self, FrameworkIIStateError> {
        Self::new_with_max_level(catalog, None)
    }

    /// Construct one empty control state under an optional level bound.
    ///
    /// The bound is a host knob for the symbolic method, never a termination
    /// guard: the scan's halting rule ends a scan on its own. When set it
    /// must be at least 1, since levels 0 and 1 always run.
    pub fn new_with_max_level(
        catalog: LeveledClauseCatalog,
        max_level: Option<FrameworkIILevel>,
    ) -> Result<Self, FrameworkIIStateError> {
        Self::new_with_options(
            catalog,
            max_level,
            false,
            BTreeSet::new(),
            BTreeSet::new(),
            AgentToolPolicy::default(),
        )
    }

    /// Construct one empty control state under every typed host option.
    ///
    /// Every option is bound once here and never mutated. `compress_core` is
    /// not Lean semantics, not provider framing, and not an Agent-controlled
    /// field; the agent path never enables it (enforced at
    /// [`super::search::PreCertificateAgentHoudiniSearch::new`], which fails
    /// closed on a `true` value). `tool_policy` is drift-checked the same
    /// way.
    ///
    /// `maintenance_support_edges`/`maintenance_coverage_edges` are the
    /// shared core's interface-level placeholder for the legacy
    /// SymbolicHoudini's clause-identity relations: this pass accepts only
    /// the empty relation for each and rejects a nonempty one with
    /// [`FrameworkIIStateError::EdgeInputRequiresSymbolicMigration`], naming
    /// the rejected field.
    pub fn new_with_options(
        catalog: LeveledClauseCatalog,
        max_level: Option<FrameworkIILevel>,
        compress_core: bool,
        maintenance_support_edges: BTreeSet<(ClauseId, ClauseId)>,
        maintenance_coverage_edges: BTreeSet<(ClauseId, ClauseId)>,
        tool_policy: AgentToolPolicy,
    ) -> Result<Self, FrameworkIIStateError> {
        if !maintenance_support_edges.is_empty() {
            return Err(FrameworkIIStateError::EdgeInputRequiresSymbolicMigration(
                "maintenance_support_edges",
            ));
        }
        if !maintenance_coverage_edges.is_empty() {
            return Err(FrameworkIIStateError::EdgeInputRequiresSymbolicMigration(
                "maintenance_coverage_edges",
            ));
        }
        if max_level.is_some_and(|bound| bound < FrameworkIILevel::ONE) {
            return Err(FrameworkIIStateError::InvalidPlacement(
                "a fixed-ambient level bound must be at least one",
            ));
        }
        let empty = Arc::new(LeveledCandidateSnapshot::build(
            &catalog,
            max_level,
            BTreeMap::new(),
        )?);
        Ok(Self {
            catalog,
            max_level,
            control_revision: 0,
            committed: BTreeMap::new(),
            pending: BTreeMap::new(),
            dead: BTreeMap::new(),
            ever_committed: BTreeSet::new(),
            fresh: BTreeSet::new(),
            suspended: BTreeSet::new(),
            attempts: LevelAttemptLedger::default(),
            current_roots: BTreeMap::new(),
            core: LeveledCoreHandle::build(empty)?,
            system_clauses_installed: false,
            system_clauses: BTreeSet::new(),
            max_level_stops_total: 0,
            compress_core,
            tool_policy,
            compress_core_dirty: false,
            compress_core_moves_total: 0,
            compress_core_attempts_total: 0,
            termination_attempts_total: 0,
            replay_termination_observations: Vec::new(),
            preparation_time_total: Duration::ZERO,
            solver_time_total: Duration::ZERO,
            preparations_total: 0,
            sweep_dispatch: FrameworkIISweepDispatch::default(),
            dispatched_sweeps_total: 0,
            dispatched_batch_checks_total: 0,
        })
    }

    pub fn catalog(&self) -> &LeveledClauseCatalog {
        &self.catalog
    }

    /// The typed host option bound at construction. Never Agent-controlled.
    pub fn tool_policy(&self) -> &AgentToolPolicy {
        &self.tool_policy
    }

    /// Whether the reserved Lean system rows have entered the Core.
    pub fn system_clauses_installed(&self) -> bool {
        self.system_clauses_installed
    }

    /// The installed protected system rows.
    pub fn system_clauses(&self) -> &BTreeSet<ClauseId> {
        &self.system_clauses
    }

    /// Whether reserved system rows still await installation.
    pub fn system_installation_pending(&self) -> Result<bool, FrameworkIIStateError> {
        Ok(!self.system_clauses_installed
            && self.catalog.system_origins_reserved()?
            && !self.catalog.reserved_system_clauses()?.ids().is_empty())
    }

    /// The run's optional level bound, absent unless a host set one.
    pub fn max_level(&self) -> Option<FrameworkIILevel> {
        self.max_level
    }

    /// Whether this clause's Lean-owned minimum level exceeds the run's
    /// level bound, which is a rejection at admission rather than a
    /// placement.
    pub fn exceeds_level_bound(&self, minimum_level: FrameworkIILevel) -> bool {
        self.max_level.is_some_and(|bound| minimum_level > bound)
    }

    /// Monotone exact-state revision bound into each proposal context.
    ///
    /// This is an authorization revision, not a count of consultations: any
    /// published placement transition advances it and stales an older context.
    pub fn proposal_revision(&self) -> u64 {
        self.control_revision
    }

    pub fn core(&self) -> &LeveledCoreHandle {
        &self.core
    }

    pub fn committed_levels(&self) -> &BTreeMap<ClauseId, FrameworkIILevel> {
        &self.committed
    }

    pub fn pending_levels(&self) -> &BTreeMap<ClauseId, FrameworkIILevel> {
        &self.pending
    }

    /// The terminal `dead` partition with each clause's cause.
    pub fn dead(&self) -> &BTreeMap<ClauseId, FrameworkIIDeadCause> {
        &self.dead
    }

    pub fn is_dead(&self, clause: ClauseId) -> bool {
        self.dead.contains_key(&clause)
    }

    pub fn dead_cause(&self, clause: ClauseId) -> Option<FrameworkIIDeadCause> {
        self.dead.get(&clause).copied()
    }

    /// The refutation reason for a clause dead by refutation, which no
    /// resubmission revives.
    pub fn dead_reason(&self, clause: ClauseId) -> Option<FrameworkIIDeadReason> {
        self.dead_cause(clause)
            .and_then(FrameworkIIDeadCause::refutation)
    }

    /// Whether an earlier proposer drop still suppresses this clause. An
    /// exact resubmission revives it at its minimum level.
    pub fn is_dropped(&self, clause: ClauseId) -> bool {
        self.dead_cause(clause) == Some(FrameworkIIDeadCause::Dropped)
    }

    /// Exact dropped identities, in stable ClauseId order.
    pub fn dropped_clauses(&self) -> impl Iterator<Item = ClauseId> + '_ {
        self.dead
            .iter()
            .filter(|(_, cause)| **cause == FrameworkIIDeadCause::Dropped)
            .map(|(clause, _)| *clause)
    }

    /// This epoch's fresh clauses, checked before every other clause of a
    /// level.
    pub fn fresh_clauses(&self) -> &BTreeSet<ClauseId> {
        &self.fresh
    }

    /// This epoch's suspended clauses: an inconclusive launch stops their
    /// further launches for the rest of the epoch.
    pub fn suspended_clauses(&self) -> &BTreeSet<ClauseId> {
        &self.suspended
    }

    /// Cumulative count of promotions declined at the run's level bound.
    pub fn max_level_stops_total(&self) -> u64 {
        self.max_level_stops_total
    }

    /// Whether the `compress_core` host option is enabled. The agent path
    /// never enables it.
    pub fn compress_core(&self) -> bool {
        self.compress_core
    }

    /// Count of Core clauses that re-converged strictly lower than before.
    pub fn compress_core_moves_total(&self) -> u64 {
        self.compress_core_moves_total
    }

    /// Count of compression re-stabilizations attempted, moved or not.
    pub fn compress_core_attempts_total(&self) -> u64 {
        self.compress_core_attempts_total
    }

    /// Count of termination checks this run has run.
    pub fn termination_attempts_total(&self) -> u64 {
        self.termination_attempts_total
    }

    pub(super) fn replay_termination_observations(&self) -> &[ReplayTerminationObservation] {
        &self.replay_termination_observations
    }

    pub(super) fn record_replay_termination(
        &mut self,
        core: Arc<LeveledCandidateSnapshot>,
        result: &Result<FrameworkIICheckExecution, FrameworkIIStateError>,
    ) {
        self.replay_termination_observations
            .push(ReplayTerminationObservation {
                ordinal: self.termination_attempts_total,
                core,
                result: result.clone(),
            });
    }

    /// Count one termination check this run ran.
    pub(super) fn count_termination_attempt(&mut self) {
        self.termination_attempts_total = self.termination_attempts_total.saturating_add(1);
    }

    /// Cumulative wall time of every obligation preparation recorded into
    /// `attempts` so far this run: piece-cache splicing plus whatever
    /// worker round trips the cache missed on.
    pub fn preparation_time_total(&self) -> Duration {
        self.preparation_time_total
    }

    /// Cumulative wall time of every solver launch recorded into `attempts`
    /// so far this run.
    pub fn solver_time_total(&self) -> Duration {
        self.solver_time_total
    }

    /// Count of check outcomes recorded into `attempts` so far this run
    /// whose evidence carries a `preparation_time`: one fresh obligation
    /// preparation each, which is not the same thing as one worker round
    /// trip (see the field doc).
    pub fn preparations_total(&self) -> u64 {
        self.preparations_total
    }

    /// How this controller dispatches one sweep of a level.
    pub fn sweep_dispatch(&self) -> FrameworkIISweepDispatch {
        self.sweep_dispatch
    }

    /// Dispatch one request at a time instead of one sweep at a time.
    ///
    /// Test-only. The contract's dispatch is batched (`houdini.tex`
    /// Section 4.4) and is this controller's default; nothing on the
    /// production path changes it. It exists so a test can compare the two
    /// dispatches with everything else held fixed (Section 4.4's abort
    /// criterion: batching must not change which clause the single-failure
    /// drop removes).
    #[doc(hidden)]
    pub fn set_sweep_dispatch(&mut self, dispatch: FrameworkIISweepDispatch) {
        self.sweep_dispatch = dispatch;
    }

    /// Count of sweeps this run dispatched to the checked adapter.
    pub fn dispatched_sweeps_total(&self) -> u64 {
        self.dispatched_sweeps_total
    }

    /// Count of requests carried by those dispatches. Equals the number of
    /// checks issued, whichever dispatch is in force.
    pub fn dispatched_batch_checks_total(&self) -> u64 {
        self.dispatched_batch_checks_total
    }

    /// Whether any of `clauses` names an identity this catalog already
    /// interned and this run has classified dead by refutation. Used at the
    /// proposal boundary to reject a resubmission with its exact reason.
    /// A clause dead by drop is not a conflict: its exact resubmission
    /// revives it.
    /// The first clause of `clauses` that is already permanently dead, as its
    /// position in the slice, its catalog identity and the reason it died.
    /// The position lets a caller name the offending formula, which is the
    /// one thing a refusal of this kind has to say.
    pub fn dead_conflict(
        &self,
        clauses: &[super::types::ExtendedClause],
    ) -> Result<Option<(usize, ClauseId, FrameworkIIDeadReason)>, FrameworkIIStateError> {
        for (index, clause) in clauses.iter().enumerate() {
            if let Some(id) = self.catalog.find(clause)?
                && let Some(reason) = self.dead_reason(id)
            {
                return Ok(Some((index, id, reason)));
            }
        }
        Ok(None)
    }

    pub fn attempts(&self) -> &LevelAttemptLedger {
        &self.attempts
    }

    pub fn current_root(
        &self,
        clause: ClauseId,
        role: FrameworkIICheckRole,
    ) -> Option<&CurrentFrameworkIIRoot> {
        self.current_roots.get(&(clause, role))
    }

    /// Compute exact root coverage without treating a digest as authority.
    pub fn root_coverage(&self) -> Result<FrameworkIIRootCoverage, FrameworkIIStateError> {
        if self.committed.len() != self.core.snapshot().records().len()
            || self
                .committed
                .iter()
                .any(|(clause, level)| self.core.snapshot().level_of(*clause) != Some(*level))
        {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "the published Core and committed placement disagree",
            ));
        }
        for (clause, role) in self.current_roots.keys() {
            let Some(level) = self.committed.get(clause).copied() else {
                return Err(FrameworkIIStateError::InvalidEvidence(
                    "a current root names a clause outside the published Core",
                ));
            };
            if !self.root_matches(*clause, *role, level, self.core.snapshot()) {
                return Err(FrameworkIIStateError::InvalidEvidence(
                    "a current root does not match the exact Core",
                ));
            }
        }

        let mut missing = Vec::new();
        for clause in self.core.snapshot().canonical_order() {
            let level = self.committed.get(clause).copied().ok_or(
                FrameworkIIStateError::InvalidEvidence(
                    "the published Core and committed placement disagree",
                ),
            )?;
            for role in [
                FrameworkIICheckRole::Initialization,
                FrameworkIICheckRole::Maintenance,
            ] {
                if !self.root_matches(*clause, role, level, self.core.snapshot()) {
                    missing.push((*clause, role));
                }
            }
        }
        Ok(if missing.is_empty() {
            FrameworkIIRootCoverage::Complete
        } else {
            FrameworkIIRootCoverage::Incomplete {
                missing: missing.into(),
            }
        })
    }

    /// Enqueue exact catalog records at their Lean-owned minimum levels.
    ///
    /// A clause whose minimum level exceeds the run's level bound is rejected
    /// here rather than placed.
    pub fn enqueue_registered(
        &mut self,
        registered: &RegisteredLeveledClauses,
    ) -> Result<(), FrameworkIIStateError> {
        let next_revision = self.next_control_revision()?;
        self.enqueue_registered_inner(registered)?;
        self.control_revision = next_revision;
        Ok(())
    }

    fn enqueue_registered_inner(
        &mut self,
        registered: &RegisteredLeveledClauses,
    ) -> Result<(), FrameworkIIStateError> {
        if !registered.belongs_to(&self.catalog) {
            return Err(FrameworkIIStateError::WrongCatalog);
        }
        if registered.ids().len() != registered.records().len()
            || registered
                .ids()
                .iter()
                .zip(registered.records())
                .any(|(clause, record)| *clause != record.id())
        {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "a registered batch is detached from its exact catalog records",
            ));
        }
        for record in registered.records() {
            if self.exceeds_level_bound(record.minimum_level()) {
                return Err(FrameworkIIStateError::LevelBoundExceeded {
                    clause: Some(record.id()),
                    minimum_level: record.minimum_level().get(),
                    max_level: self
                        .max_level
                        .map(FrameworkIILevel::get)
                        .unwrap_or_default(),
                });
            }
        }
        self.enqueue_registered_records(registered)
    }

    /// Intern one already validated batch: a never-seen identity and a
    /// revived dropped clause alike enter pending at the clause's minimum
    /// level and count as fresh for this epoch.
    fn enqueue_registered_records(
        &mut self,
        registered: &RegisteredLeveledClauses,
    ) -> Result<(), FrameworkIIStateError> {
        for (clause, record) in registered.ids().iter().zip(registered.records()) {
            if self.committed.contains_key(clause) || self.pending.contains_key(clause) {
                continue;
            }
            match self.dead.get(clause) {
                // Dead by refutation is never revived; the proposal boundary
                // rejects the resubmission before this point, and this guard
                // keeps that true at the state level.
                Some(FrameworkIIDeadCause::Refuted(_)) => continue,
                Some(FrameworkIIDeadCause::Dropped) => {
                    self.dead.remove(clause);
                }
                None => {}
            }
            // Admission rejects a clause whose minimum level is above the
            // run's bound, so reaching one here means the catalog and this
            // owner disagree about the bound. Fail closed rather than
            // silently dropping the clause from the batch it was
            // registered in.
            if self.exceeds_level_bound(record.minimum_level()) {
                return Err(FrameworkIIStateError::InvalidPlacement(
                    "a registered clause's minimum level exceeds the run's level bound",
                ));
            }
            self.pending.insert(*clause, record.minimum_level());
            self.fresh.insert(*clause);
        }
        Ok(())
    }

    /// Every clause eligible for a proposal drop: any pending clause. A
    /// committed or already dead clause is never drop-eligible.
    pub(super) fn drop_eligible_records(
        &self,
    ) -> Result<Vec<super::catalog::LeveledClauseRecord>, FrameworkIIStateError> {
        let mut records = Vec::new();
        for clause in self.pending.keys() {
            if self.committed.contains_key(clause) || self.dead.contains_key(clause) {
                continue;
            }
            records.push(self.catalog.record(*clause)?);
        }
        Ok(records)
    }

    /// Open one epoch: apply its drops and clear the per-epoch fresh and
    /// suspension sets, on a private staged owner.
    pub(super) fn prepare_proposal_checkpoint(
        &self,
        dropped: &BTreeSet<ClauseId>,
    ) -> Result<PreparedFrameworkIIProposalCheckpoint, FrameworkIIStateError> {
        // Validate every present root and the exact Core/placement relation
        // before staging any invalidation rows.
        let _ = self.root_coverage()?;
        let next_revision = self.next_control_revision()?;
        let mut staged = self.stage_transition();
        staged.fresh.clear();
        staged.suspended.clear();

        // Drops are validated against the immutable proposal context before
        // registration. Recheck their mutable predicates on the staged owner
        // so this publication remains fail closed even if a caller violates
        // the coordinator's serialized-use contract.
        for clause in dropped {
            let record = staged.catalog.record(*clause)?;
            if staged.committed.contains_key(clause) || record.is_protected() {
                return Err(FrameworkIIStateError::InvalidPlacement(
                    "Core and protected clauses cannot be dropped",
                ));
            }
            if staged.dead.contains_key(clause) {
                return Err(FrameworkIIStateError::InvalidPlacement(
                    "a dead clause cannot be dropped",
                ));
            }
            if !staged.pending.contains_key(clause) {
                return Err(FrameworkIIStateError::InvalidPlacement(
                    "a proposal drop is not eligible for suppression",
                ));
            }
            staged.pending.remove(clause);
            staged.dead.insert(*clause, FrameworkIIDeadCause::Dropped);
        }

        staged.control_revision = next_revision;
        Ok(PreparedFrameworkIIProposalCheckpoint {
            base_control_revision: self.control_revision,
            staged,
        })
    }

    /// Enqueue a batch just atomically returned by this checkpoint's exact
    /// catalog and synchronously publish the already validated state half.
    pub(super) fn publish_proposal_checkpoint(
        &mut self,
        mut checkpoint: PreparedFrameworkIIProposalCheckpoint,
        registered: &RegisteredLeveledClauses,
    ) {
        assert_eq!(
            checkpoint.base_control_revision, self.control_revision,
            "a prepared proposal checkpoint must publish on its exact base revision"
        );
        assert!(
            checkpoint.staged.catalog == self.catalog,
            "a prepared proposal checkpoint must retain its exact catalog owner"
        );
        assert!(
            registered.belongs_to(&self.catalog),
            "a proposal registration must retain its exact catalog owner"
        );
        assert_eq!(
            registered.ids().len(),
            registered.records().len(),
            "a proposal registration must retain one exact record per ID"
        );
        assert!(
            registered
                .ids()
                .iter()
                .zip(registered.records())
                .all(|(clause, record)| *clause == record.id()),
            "a proposal registration must retain matching ID-record pairs"
        );
        // The catalog transaction supplies already materialized exact records,
        // so this owner-side finalize performs no lock acquisition while the
        // catalog publication lock remains held. Its one fallible condition —
        // a record above the run's level bound — is rejected at admission
        // long before registration, so like the invariants asserted above it
        // is a hard contract violation rather than a recoverable outcome.
        checkpoint
            .staged
            .enqueue_registered_records(registered)
            .expect("a proposal registration must respect the run's level bound");
        *self = checkpoint.staged;
    }

    /// Open this epoch's private work state: every pending clause returns to
    /// its Lean-owned minimum level, whatever its history.
    ///
    /// A fresh clause may commit at any level, and once committed it is a new
    /// premise there and, through its prophecy image, at every level above;
    /// so the level a pending clause reached last epoch says nothing about
    /// the lowest level at which it can commit now. Levels whose premises are
    /// unchanged are served by the semantic dictionary, so restarting low
    /// costs only lookups.
    pub(super) fn activate_proposal_work(&self) -> Result<Self, FrameworkIIStateError> {
        let mut work = self.stage_transition();
        let pending = work.pending.keys().copied().collect::<Vec<_>>();
        for clause in pending {
            let minimum_level = work.catalog.record(clause)?.minimum_level();
            let current_level = work.pending.insert(clause, minimum_level);
            if current_level != Some(minimum_level) {
                work.invalidate_roots_depending_on(
                    clause,
                    FrameworkIIInvalidationReason::SnapshotChanged,
                )?;
            }
        }
        Ok(work)
    }

    /// Publish the completed work state after stabilization. A typed stop
    /// publishes only earlier transitions that already advanced beyond the
    /// durable proposal checkpoint; its failing transition remains rolled
    /// back.
    pub(super) fn publish_advanced_proposal_work(
        &mut self,
        work: Self,
    ) -> Result<bool, FrameworkIIStateError> {
        if work.catalog != self.catalog || work.control_revision < self.control_revision {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "proposal work is detached from its durable checkpoint",
            ));
        }
        if work.control_revision == self.control_revision {
            return Ok(false);
        }
        *self = work;
        Ok(true)
    }

    /// The partition an epoch is about to change, retained so that an
    /// aborted epoch can be rolled back onto it.
    ///
    /// Taken before [`Self::prepare_proposal_checkpoint`], so it is the
    /// state as of the epoch's start in the contract's own sense: before the
    /// drops, before the batch is interned, and with the previous epoch's
    /// `Fresh` and `Susp` sets still standing.
    pub(super) fn epoch_rollback_point(&self) -> Self {
        self.stage_transition()
    }

    /// Roll one aborted epoch back onto the partition it began with, keeping
    /// the append-only ledger history the checks it really ran produced.
    ///
    /// `houdini.tex` Algorithm 1 (`Epoch`): an epoch is atomic against
    /// infrastructure faults, and one that returns `Failure` leaves "the
    /// partition as it was when the epoch began". That covers the whole
    /// epoch, not only its stabilization: the drops it applied, the fresh
    /// clauses it admitted to `Pend`, the pending levels it reset to their
    /// minimums, the clauses it committed, the roots it installed, and its
    /// `Fresh` and `Susp` sets all go back to what they were.
    ///
    /// What does *not* go back is the catalog and the ledger. A clause
    /// identity is a content digest, so the catalog records the epoch
    /// interned are inert for a partition that does not name them and an
    /// exact resubmission re-admits the same clause identically — and it is
    /// fresh again, because the rolled-back partition holds it in neither
    /// `Core` nor `Pend`. The ledger is provenance: its rows name checks
    /// that really ran, so they survive with the measured cost of the checks
    /// that produced them, and roots the epoch invalidated stay invalidated.
    ///
    /// The control revision advances rather than returning to the epoch's,
    /// because a rollback is itself a published transition: a proposal
    /// context taken before the epoch must not become current again.
    pub(super) fn rollback_epoch(
        &mut self,
        epoch_start: Self,
        work: Self,
    ) -> Result<(), FrameworkIIStateError> {
        if work.catalog != self.catalog || epoch_start.catalog != self.catalog {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "abandoned proposal work is detached from its durable checkpoint",
            ));
        }
        let next_revision = self.next_control_revision()?;
        let mut restored = epoch_start;
        restored.merge_staged_history(&work)?;
        restored.control_revision = next_revision;
        restored.preparation_time_total = work.preparation_time_total;
        restored.solver_time_total = work.solver_time_total;
        restored.preparations_total = work.preparations_total;
        restored.dispatched_sweeps_total = work.dispatched_sweeps_total;
        restored.dispatched_batch_checks_total = work.dispatched_batch_checks_total;
        restored.max_level_stops_total = work.max_level_stops_total;
        restored.compress_core_attempts_total = work.compress_core_attempts_total;
        restored.compress_core_moves_total = work.compress_core_moves_total;
        restored.termination_attempts_total = self.termination_attempts_total;
        restored.replay_termination_observations = self.replay_termination_observations.clone();
        *self = restored;
        Ok(())
    }

    fn next_control_revision(&self) -> Result<u64, FrameworkIIStateError> {
        self.control_revision
            .checked_add(1)
            .ok_or(FrameworkIIStateError::InvalidPlacement(
                "the proposal revision space is exhausted",
            ))
    }

    #[cfg(test)]
    pub(super) fn set_proposal_revision_for_test(&mut self, revision: u64) {
        self.control_revision = revision;
    }

    /// Copy the complete control state for one fail-closed transition.
    ///
    /// This is deliberately not `Clone`: callers cannot fork mutable
    /// placement authority.
    fn stage_transition(&self) -> Self {
        Self {
            catalog: self.catalog.clone(),
            max_level: self.max_level,
            control_revision: self.control_revision,
            committed: self.committed.clone(),
            pending: self.pending.clone(),
            dead: self.dead.clone(),
            ever_committed: self.ever_committed.clone(),
            fresh: self.fresh.clone(),
            suspended: self.suspended.clone(),
            attempts: self.attempts.clone(),
            current_roots: self.current_roots.clone(),
            core: self.core.clone(),
            system_clauses_installed: self.system_clauses_installed,
            system_clauses: self.system_clauses.clone(),
            max_level_stops_total: self.max_level_stops_total,
            compress_core: self.compress_core,
            tool_policy: self.tool_policy.clone(),
            compress_core_dirty: self.compress_core_dirty,
            compress_core_moves_total: self.compress_core_moves_total,
            compress_core_attempts_total: self.compress_core_attempts_total,
            termination_attempts_total: self.termination_attempts_total,
            replay_termination_observations: self.replay_termination_observations.clone(),
            preparation_time_total: self.preparation_time_total,
            solver_time_total: self.solver_time_total,
            preparations_total: self.preparations_total,
            sweep_dispatch: self.sweep_dispatch,
            dispatched_sweeps_total: self.dispatched_sweeps_total,
            dispatched_batch_checks_total: self.dispatched_batch_checks_total,
        }
    }

    /// Place the reserved protected rows as level-zero pending work.
    ///
    /// The production adapter later closes both verification conditions of
    /// every row through its reviewed Lean theorem route; this pure method
    /// performs only atomic control publication.
    fn install_reserved_system_clauses(
        &mut self,
    ) -> Result<RegisteredLeveledClauses, FrameworkIIStateError> {
        if self.system_clauses_installed {
            return Err(FrameworkIIStateError::InvalidPlacement(
                "fixed-ambient system clauses are already installed",
            ));
        }
        let registered = self.catalog.reserved_system_clauses()?;
        let mut installed = BTreeSet::new();
        for clause in registered.ids() {
            let record = self.catalog.record(*clause)?;
            if !record.is_protected() || record.minimum_level() != FrameworkIILevel::ZERO {
                return Err(FrameworkIIStateError::InvalidPlacement(
                    "the reserved system batch contains a non-system record",
                ));
            }
            installed.insert(*clause);
        }
        self.system_clauses_installed = true;
        self.system_clauses = installed.clone();
        for clause in installed {
            if !self.committed.contains_key(&clause) {
                self.pending.insert(clause, FrameworkIILevel::ZERO);
            }
        }
        if !self.system_clauses.is_empty() {
            self.invalidate_all_roots(FrameworkIIInvalidationReason::SystemClausesInstalled)?;
        }
        Ok(registered)
    }

    /// Retain only append-only audit history completed before a later typed
    /// stop. Tentative placement, Core, pending state, and new roots remain on
    /// the private staged owner and are rolled back.
    fn merge_staged_history(&mut self, staged: &Self) -> Result<bool, FrameworkIIStateError> {
        let advanced = self.attempts.merge_exact_extension(&staged.attempts)?;
        if advanced {
            let invalidated = &self.attempts;
            self.current_roots
                .retain(|_, root| !invalidated.is_invalidated(root.attempt_row));
        }
        Ok(advanced)
    }

    fn refresh_core(&mut self) -> Result<(), FrameworkIIStateError> {
        let snapshot = Arc::new(LeveledCandidateSnapshot::build(
            &self.catalog,
            self.max_level,
            self.committed.clone(),
        )?);
        let core = LeveledCoreHandle::build(Arc::clone(&snapshot))?;
        let stale_roots = self
            .current_roots
            .keys()
            .copied()
            .filter(|(clause, role)| {
                self.committed
                    .get(clause)
                    .is_none_or(|level| !self.root_matches(*clause, *role, *level, &snapshot))
            })
            .collect::<Vec<_>>();
        for key in stale_roots {
            self.invalidate_root(key, None, FrameworkIIInvalidationReason::SnapshotChanged)?;
        }

        // Successful tentative attempts are ledger evidence, never public
        // roots.  Once their exact partition becomes the published Core,
        // promote the latest still-valid row without repeating proof search.
        let mut promoted = Vec::new();
        for (clause, level) in &self.committed {
            for role in [
                FrameworkIICheckRole::Initialization,
                FrameworkIICheckRole::Maintenance,
            ] {
                if self.current_roots.contains_key(&(*clause, role)) {
                    continue;
                }
                let root = self.attempts.rows().iter().rev().find_map(|row| {
                    let LevelLedgerRow::Attempt(attempt) = row else {
                        return None;
                    };
                    let FrameworkIICheckOutcome::Proved(proof_evidence) = attempt.outcome() else {
                        return None;
                    };
                    (attempt.request().clause() == *clause
                        && attempt.request().role() == role
                        && attempt.request().level() == *level
                        && attempt.request().snapshot().same_partition(&snapshot)
                        && !self.attempts.is_invalidated(attempt.row_ordinal()))
                    .then(|| {
                        (
                            (*clause, role),
                            CurrentFrameworkIIRoot {
                                attempt_row: attempt.row_ordinal(),
                                request_digest: Arc::from(attempt.request().request_digest()),
                                partition_digest: Arc::from(
                                    attempt.request().snapshot().partition_digest(),
                                ),
                                proof_evidence: proof_evidence.clone(),
                            },
                        )
                    })
                });
                if let Some(root) = root {
                    promoted.push(root);
                }
            }
        }
        self.current_roots.extend(promoted);
        self.core = core;
        Ok(())
    }

    /// The exact snapshot one level's checks range over: the Core plus the
    /// named cohort placed at `level`.
    fn tentative_snapshot(
        &self,
        cohort: &BTreeSet<ClauseId>,
        level: FrameworkIILevel,
    ) -> Result<Arc<LeveledCandidateSnapshot>, FrameworkIIStateError> {
        let mut placement = self.committed.clone();
        for clause in cohort {
            placement.insert(*clause, level);
        }
        Ok(Arc::new(LeveledCandidateSnapshot::build(
            &self.catalog,
            self.max_level,
            placement,
        )?))
    }

    /// The contract's check order over one cohort: this epoch's fresh clauses
    /// first, then every other clause, each group in the snapshot's canonical
    /// order (level, registration order, identifier).
    fn check_order(
        &self,
        snapshot: &LeveledCandidateSnapshot,
        cohort: &BTreeSet<ClauseId>,
    ) -> Vec<ClauseId> {
        let canonical = snapshot
            .canonical_order()
            .iter()
            .copied()
            .filter(|clause| cohort.contains(clause))
            .collect::<Vec<_>>();
        let mut order = canonical
            .iter()
            .copied()
            .filter(|clause| self.fresh.contains(clause))
            .collect::<Vec<_>>();
        order.extend(
            canonical
                .iter()
                .copied()
                .filter(|clause| !self.fresh.contains(clause)),
        );
        order
    }

    fn pending_at(&self, level: FrameworkIILevel) -> BTreeSet<ClauseId> {
        self.pending
            .iter()
            .filter_map(|(clause, current)| (*current == level).then_some(*clause))
            .collect()
    }

    fn least_pending_level_from(&self, from: FrameworkIILevel) -> Option<FrameworkIILevel> {
        self.pending
            .values()
            .copied()
            .filter(|level| *level >= from)
            .min()
    }

    fn core_holds(&self, level: FrameworkIILevel) -> bool {
        self.committed.values().any(|current| *current == level)
    }

    fn core_holds_above(&self, level: FrameworkIILevel) -> bool {
        self.committed.values().any(|current| *current > level)
    }

    fn root_matches(
        &self,
        clause: ClauseId,
        role: FrameworkIICheckRole,
        level: FrameworkIILevel,
        snapshot: &LeveledCandidateSnapshot,
    ) -> bool {
        let Some(root) = self.current_roots.get(&(clause, role)) else {
            return false;
        };
        if self.attempts.is_invalidated(root.attempt_row) {
            return false;
        }
        let Some(attempt) = self.attempts.attempt(root.attempt_row) else {
            return false;
        };
        attempt.request().clause() == clause
            && attempt.request().role() == role
            && attempt.request().level() == level
            && attempt.request().has_current_identity()
            && attempt.request().snapshot().same_partition(snapshot)
            && root.request_digest.as_ref() == attempt.request().request_digest()
            && root.partition_digest.as_ref() == attempt.request().snapshot().partition_digest()
            && matches!(
                attempt.outcome(),
                FrameworkIICheckOutcome::Proved(evidence) if evidence == &root.proof_evidence
            )
    }

    fn invalidate_root(
        &mut self,
        key: (ClauseId, FrameworkIICheckRole),
        cause: Option<ClauseId>,
        reason: FrameworkIIInvalidationReason,
    ) -> Result<(), FrameworkIIStateError> {
        if let Some(root) = self.current_roots.remove(&key) {
            self.attempts
                .append_invalidation(root.attempt_row, key.0, cause, reason)?;
        }
        Ok(())
    }

    fn invalidate_all_roots(
        &mut self,
        reason: FrameworkIIInvalidationReason,
    ) -> Result<(), FrameworkIIStateError> {
        let keys = self.current_roots.keys().copied().collect::<Vec<_>>();
        for key in keys {
            self.invalidate_root(key, None, reason)?;
        }
        Ok(())
    }

    fn invalidate_roots_depending_on(
        &mut self,
        cause: ClauseId,
        reason: FrameworkIIInvalidationReason,
    ) -> Result<(), FrameworkIIStateError> {
        let keys = self
            .current_roots
            .iter()
            .filter_map(|(key, root)| {
                self.attempts
                    .attempt(root.attempt_row)
                    .filter(|attempt| attempt.request().snapshot().contains(cause))
                    .map(|_| *key)
            })
            .collect::<Vec<_>>();
        for key in keys {
            self.invalidate_root(key, Some(cause), reason)?;
        }
        Ok(())
    }

    /// Issue and record one check on its own, outside any sweep.
    ///
    /// The protected-row installation path uses this: it is not one of the
    /// contract's two sweeps, and its checks are a fixed handful.
    ///
    /// A clause this epoch already suspended is still checked, and still
    /// gets its ledger row; the request only carries the instruction that
    /// no solver may be launched for it. The checker answers such a request
    /// from its semantic dictionary exactly as it answers any other — a
    /// proof hit commits, a refutation hit kills or excludes — and returns
    /// [`FrameworkIIInconclusiveReason::Suspended`] only when the
    /// dictionary has nothing, without a launch, without consuming a retry
    /// allowance and without recording a dictionary entry. The pruning
    /// algorithms treat that inconclusive answer as any other failure at
    /// the level.
    async fn check_one<C: FrameworkIIChecker + ?Sized>(
        &mut self,
        checker: &mut C,
        clause: ClauseId,
        role: FrameworkIICheckRole,
        level: FrameworkIILevel,
        snapshot: Arc<LeveledCandidateSnapshot>,
        control: Option<&CancellationToken>,
    ) -> Result<FrameworkIICheckStep, FrameworkIIStateError> {
        let request = self.build_request(clause, role, level, snapshot, 0)?;
        let mut executions = match checker.check_batch(vec![request.clone()]).await {
            Ok(executions) => executions,
            Err(FrameworkIIStateError::Cancelled) => return Ok(FrameworkIICheckStep::Cancelled),
            Err(error) => return Err(error),
        };
        if executions.len() != 1 {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "a checked adapter returned another number of batch executions",
            ));
        }
        self.record_execution(request, executions.remove(0), control)
    }

    /// Build one check request at the ledger ordinal it will occupy.
    ///
    /// `reserved` is the number of requests of the same sweep already built
    /// but not yet appended: a batch reserves consecutive ledger ordinals in
    /// check order, and [`LevelAttemptLedger::append_attempt`] requires each
    /// request's ordinal to be exactly its own row's.
    fn build_request(
        &self,
        clause: ClauseId,
        role: FrameworkIICheckRole,
        level: FrameworkIILevel,
        snapshot: Arc<LeveledCandidateSnapshot>,
        reserved: u64,
    ) -> Result<FrameworkIICheckRequest, FrameworkIIStateError> {
        let ordinal = self.attempts.next_ordinal()?.checked_add(reserved).ok_or(
            FrameworkIIStateError::InvalidEvidence("the attempt ledger exhausted its row space"),
        )?;
        FrameworkIICheckRequest::new(
            ordinal,
            clause,
            level,
            role,
            snapshot,
            self.suspended.contains(&clause),
        )
    }

    /// Record one already-obtained execution: the epoch's `Susp` set, the
    /// run's preparation/solver accounting, the append-only ledger row, and
    /// the current-root table. Never issues a check.
    ///
    /// Recording is single-writer and always happens in check order, so a
    /// batch's rows are appended exactly as the sequential sweep appended
    /// them one at a time.
    fn record_execution(
        &mut self,
        request: FrameworkIICheckRequest,
        execution: FrameworkIICheckExecution,
        control: Option<&CancellationToken>,
    ) -> Result<FrameworkIICheckStep, FrameworkIIStateError> {
        let clause = request.clause();
        let role = request.role();
        let launch_suppressed = request.launch_suppressed();
        let outcome = match execution {
            FrameworkIICheckExecution::Applied(outcome) => outcome,
            FrameworkIICheckExecution::Failure(report) => {
                return Ok(FrameworkIICheckStep::Failure(report));
            }
        };
        if control.is_some_and(CancellationToken::should_stop) {
            return Ok(FrameworkIICheckStep::Cancelled);
        }
        if !outcome.is_bound_to(request.request_digest()) {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "a checked outcome is bound to another request",
            ));
        }
        let partition_digest: Arc<str> = Arc::from(request.snapshot().partition_digest());
        let request_digest: Arc<str> = Arc::from(request.request_digest());
        let matches_published_core = request.snapshot().same_partition(self.core.snapshot());
        let evidence = outcome.evidence();
        if let Some(preparation_time) = evidence.preparation_time() {
            self.preparation_time_total += preparation_time;
            self.preparations_total = self.preparations_total.saturating_add(1);
        }
        if let Some(solver_time) = evidence.solver_time() {
            self.solver_time_total += solver_time;
        }
        // An inconclusive launch — as opposed to an inconclusive answer the
        // checker served from its semantic dictionary, or one it declined
        // to launch because this clause is already suspended — suspends
        // this clause's further launches for the rest of the epoch, so one
        // stuck clause costs one launch per epoch rather than one per
        // level.
        if !launch_suppressed
            && matches!(outcome, FrameworkIICheckOutcome::Inconclusive { .. })
            && evidence.semantic_reuse().is_none()
        {
            self.suspended.insert(clause);
        }
        let attempt_row = self.attempts.append_attempt(request, outcome.clone())?;
        if let FrameworkIICheckOutcome::Proved(proof_evidence) = &outcome
            && matches_published_core
        {
            self.current_roots.insert(
                (clause, role),
                CurrentFrameworkIIRoot {
                    attempt_row,
                    request_digest,
                    partition_digest,
                    proof_evidence: proof_evidence.clone(),
                },
            );
        }
        Ok(FrameworkIICheckStep::Outcome {
            attempt_row,
            outcome,
        })
    }
}

enum FrameworkIICheckStep {
    Outcome {
        attempt_row: u64,
        outcome: FrameworkIICheckOutcome,
    },
    Failure(FailureReport),
    Cancelled,
}

/// How one sweep of a level reaches the checked adapter.
///
/// `Batched` is the contract's dispatch (`houdini.tex` Section 4.4): the
/// whole sweep goes to the worker and solver pools at once. `Sequential`
/// keeps the pre-batch dispatch — one request at a time, with each
/// outcome's consequences applied before the next request is built — and
/// exists so a test can hold everything else fixed and check that batching
/// does not change which clause the single-failure drop removes.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum FrameworkIISweepDispatch {
    #[default]
    Batched,
    /// Test-only: the pre-batch dispatch, reachable only through
    /// [`LeveledHoudiniState::set_sweep_dispatch`]. The contract's dispatch
    /// is [`Self::Batched`].
    #[doc(hidden)]
    Sequential,
}

/// One sweep in progress: the requests of one level and one phase, in check
/// order, and — under [`FrameworkIISweepDispatch::Batched`] — the executions
/// the checker already returned for all of them.
struct SweepCursor {
    role: FrameworkIICheckRole,
    level: FrameworkIILevel,
    snapshot: Arc<LeveledCandidateSnapshot>,
    order: Vec<ClauseId>,
    position: usize,
    prefetched:
        Option<std::collections::VecDeque<(FrameworkIICheckRequest, FrameworkIICheckExecution)>>,
}

/// One recorded sweep step: the clause, its ledger row, and its outcome.
struct SweepStep {
    clause: ClauseId,
    attempt_row: u64,
    outcome: FrameworkIICheckOutcome,
}

/// What the cursor yielded for one clause of a sweep.
enum SweepItem {
    Recorded(SweepStep),
    Failure(FailureReport),
    Cancelled,
}

impl SweepCursor {
    /// Open a sweep, dispatching the whole of it under `Batched`.
    ///
    /// Every request of a batch is built before any of them is issued, so
    /// the batch reserves consecutive ledger ordinals in check order; the
    /// controller then records the outcomes into those exact rows.
    async fn open<C: FrameworkIIChecker + ?Sized>(
        state: &mut LeveledHoudiniState,
        checker: &mut C,
        role: FrameworkIICheckRole,
        level: FrameworkIILevel,
        snapshot: Arc<LeveledCandidateSnapshot>,
        order: Vec<ClauseId>,
        control: Option<&CancellationToken>,
    ) -> Result<Self, FrameworkIIStateError> {
        let mut cursor = Self {
            role,
            level,
            snapshot,
            order,
            position: 0,
            prefetched: None,
        };
        if state.sweep_dispatch == FrameworkIISweepDispatch::Sequential || cursor.order.is_empty() {
            return Ok(cursor);
        }
        let mut requests = Vec::with_capacity(cursor.order.len());
        for (reserved, clause) in cursor.order.iter().enumerate() {
            requests.push(state.build_request(
                *clause,
                role,
                level,
                Arc::clone(&cursor.snapshot),
                reserved as u64,
            )?);
        }
        require_control_open(control)?;
        state.dispatched_sweeps_total = state.dispatched_sweeps_total.saturating_add(1);
        state.dispatched_batch_checks_total = state
            .dispatched_batch_checks_total
            .saturating_add(requests.len() as u64);
        let executions = checker.check_batch(requests.clone()).await?;
        if executions.len() != requests.len() {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "a checked adapter returned another number of batch executions",
            ));
        }
        cursor.prefetched = Some(requests.into_iter().zip(executions).collect());
        Ok(cursor)
    }

    /// The next clause of the sweep, recorded into the ledger.
    ///
    /// Under `Sequential` the request is built and issued here, so every
    /// consequence the caller drew from the previous clause is already in
    /// the state this request is built against.
    async fn next<C: FrameworkIIChecker + ?Sized>(
        &mut self,
        state: &mut LeveledHoudiniState,
        checker: &mut C,
        control: Option<&CancellationToken>,
    ) -> Result<Option<SweepItem>, FrameworkIIStateError> {
        if self.position >= self.order.len() {
            return Ok(None);
        }
        let index = self.position;
        self.position += 1;
        let (request, execution) = match &mut self.prefetched {
            Some(prefetched) => {
                prefetched
                    .pop_front()
                    .ok_or(FrameworkIIStateError::InvalidEvidence(
                        "a dispatched batch ran out of executions",
                    ))?
            }
            None => {
                let request = state.build_request(
                    self.order[index],
                    self.role,
                    self.level,
                    Arc::clone(&self.snapshot),
                    0,
                )?;
                state.dispatched_sweeps_total = state.dispatched_sweeps_total.saturating_add(1);
                state.dispatched_batch_checks_total =
                    state.dispatched_batch_checks_total.saturating_add(1);
                let mut executions = match checker.check_batch(vec![request.clone()]).await {
                    Ok(executions) => executions,
                    Err(FrameworkIIStateError::Cancelled) => {
                        return Ok(Some(SweepItem::Cancelled));
                    }
                    Err(error) => return Err(error),
                };
                if executions.len() != 1 {
                    return Err(FrameworkIIStateError::InvalidEvidence(
                        "a checked adapter returned another number of batch executions",
                    ));
                }
                (request, executions.remove(0))
            }
        };
        let clause = request.clause();
        Ok(Some(
            match state.record_execution(request, execution, control)? {
                FrameworkIICheckStep::Outcome {
                    attempt_row,
                    outcome,
                } => SweepItem::Recorded(SweepStep {
                    clause,
                    attempt_row,
                    outcome,
                }),
                FrameworkIICheckStep::Failure(report) => SweepItem::Failure(report),
                FrameworkIICheckStep::Cancelled => SweepItem::Cancelled,
            },
        ))
    }
}

fn require_control_open(control: Option<&CancellationToken>) -> Result<(), FrameworkIIStateError> {
    if control.is_some_and(CancellationToken::should_stop) {
        Err(FrameworkIIStateError::Cancelled)
    } else {
        Ok(())
    }
}

// ------------------------------------------------------------
// Bottom-Up Stabilization
// ------------------------------------------------------------

/// The result of one scan.
///
/// A scan that ran to its halting rule is `Stabilized`; clauses may remain
/// pending at the level the scan ended on, and the next epoch retries them
/// from their minimum levels.
#[derive(Clone, Debug)]
pub enum LeveledStabilizationOutcome {
    Stabilized(LeveledCoreHandle),
    Failure(FailureReport),
}

/// Run one bottom-up scan over the pending partition.
///
/// The scan visits each least level holding pending clauses once: one
/// initialization query per pending clause, then the step greatest fixed
/// point among the survivors, then the commit, the halting test, and the
/// promotion. Committed clauses are never checked.
pub async fn stabilize_leveled_houdini<C: FrameworkIIChecker + ?Sized>(
    state: &mut LeveledHoudiniState,
    checker: &mut C,
) -> Result<LeveledStabilizationOutcome, FrameworkIIStateError> {
    stabilize_leveled_houdini_with_system_clauses_inner(state, checker, None).await
}

pub(super) async fn stabilize_leveled_houdini_under_control<C: FrameworkIIChecker + ?Sized>(
    state: &mut LeveledHoudiniState,
    checker: &mut C,
    control: &CancellationToken,
) -> Result<LeveledStabilizationOutcome, FrameworkIIStateError> {
    stabilize_leveled_houdini_with_system_clauses_inner(state, checker, Some(control)).await
}

/// Atomic result of installing and closing the protected precondition rows.
#[derive(Clone, Debug)]
pub enum FrameworkIIPreconditionInstallationOutcome {
    Installed(RegisteredLeveledClauses),
    /// A cancellation interrupted the staged installation before any row was
    /// published; the named rows remain reserved and uninstalled.
    Interrupted(Arc<[ClauseId]>),
    Failure(FailureReport),
}

/// Atomically install and close every reserved protected EDB-precondition row.
///
/// The catalog interned these records during reservation, so the transition
/// allocates no identity. All placement, invalidation, ledger, and current-root
/// mutations happen on a private staged state; anything other than a proved
/// outcome through the reviewed theorem route drops that staged state.
pub async fn install_framework_ii_precondition_clauses<C: FrameworkIIChecker + ?Sized>(
    state: &mut LeveledHoudiniState,
    checker: &mut C,
) -> Result<FrameworkIIPreconditionInstallationOutcome, FrameworkIIStateError> {
    install_framework_ii_precondition_clauses_inner(state, checker, None).await
}

async fn install_framework_ii_precondition_clauses_inner<C: FrameworkIIChecker + ?Sized>(
    state: &mut LeveledHoudiniState,
    checker: &mut C,
    control: Option<&CancellationToken>,
) -> Result<FrameworkIIPreconditionInstallationOutcome, FrameworkIIStateError> {
    require_control_open(control)?;
    let next_revision = state.next_control_revision()?;
    let mut staged = state.stage_transition();
    require_control_open(control)?;
    let registered = staged.install_reserved_system_clauses()?;

    let mut placement = staged.committed.clone();
    for clause in &staged.system_clauses {
        placement.insert(*clause, FrameworkIILevel::ZERO);
    }
    let snapshot = Arc::new(LeveledCandidateSnapshot::build(
        &staged.catalog,
        staged.max_level,
        placement,
    )?);

    let protected = snapshot
        .canonical_order()
        .iter()
        .copied()
        .filter(|clause| staged.system_clauses.contains(clause))
        .collect::<Vec<_>>();
    for clause in &protected {
        for role in [
            FrameworkIICheckRole::Initialization,
            FrameworkIICheckRole::Maintenance,
        ] {
            match staged
                .check_one(
                    checker,
                    *clause,
                    role,
                    FrameworkIILevel::ZERO,
                    Arc::clone(&snapshot),
                    control,
                )
                .await?
            {
                FrameworkIICheckStep::Outcome {
                    outcome: FrameworkIICheckOutcome::Proved(_),
                    ..
                } => {}
                FrameworkIICheckStep::Failure(report) => {
                    return Ok(FrameworkIIPreconditionInstallationOutcome::Failure(report));
                }
                FrameworkIICheckStep::Cancelled => {
                    return Ok(FrameworkIIPreconditionInstallationOutcome::Interrupted(
                        protected.clone().into(),
                    ));
                }
                FrameworkIICheckStep::Outcome {
                    outcome:
                        FrameworkIICheckOutcome::Refuted(_)
                        | FrameworkIICheckOutcome::Inconclusive { .. },
                    ..
                } => {
                    return Err(FrameworkIIStateError::InvalidEvidence(
                        "a protected system clause did not close through its reviewed theorem selection",
                    ));
                }
            }
        }
    }

    for clause in &protected {
        staged.pending.remove(clause);
        staged.fresh.remove(clause);
        staged.committed.insert(*clause, FrameworkIILevel::ZERO);
        staged.ever_committed.insert(*clause);
    }
    staged.refresh_core()?;
    for clause in &protected {
        for role in [
            FrameworkIICheckRole::Initialization,
            FrameworkIICheckRole::Maintenance,
        ] {
            if staged.current_root(*clause, role).is_none() {
                return Err(FrameworkIIStateError::InvalidEvidence(
                    "a protected fixed-ambient system root was not published atomically",
                ));
            }
        }
    }

    staged.control_revision = next_revision;
    require_control_open(control)?;
    *state = staged;
    Ok(FrameworkIIPreconditionInstallationOutcome::Installed(
        registered,
    ))
}

/// Run live stabilization, installing the reserved protected system rows
/// first whenever the catalog reserved any and they are not yet in the Core.
pub async fn stabilize_leveled_houdini_with_system_clauses<C: FrameworkIIChecker + ?Sized>(
    state: &mut LeveledHoudiniState,
    checker: &mut C,
) -> Result<LeveledStabilizationOutcome, FrameworkIIStateError> {
    stabilize_leveled_houdini_with_system_clauses_inner(state, checker, None).await
}

async fn stabilize_leveled_houdini_with_system_clauses_inner<C: FrameworkIIChecker + ?Sized>(
    state: &mut LeveledHoudiniState,
    checker: &mut C,
    control: Option<&CancellationToken>,
) -> Result<LeveledStabilizationOutcome, FrameworkIIStateError> {
    if state.system_installation_pending()? {
        match install_framework_ii_precondition_clauses_inner(state, checker, control).await? {
            FrameworkIIPreconditionInstallationOutcome::Installed(_) => {}
            FrameworkIIPreconditionInstallationOutcome::Interrupted(_) => {
                return Err(FrameworkIIStateError::Cancelled);
            }
            FrameworkIIPreconditionInstallationOutcome::Failure(report) => {
                return Ok(LeveledStabilizationOutcome::Failure(report));
            }
        }
    }
    stabilize_leveled_houdini_inner_publication(state, checker, control).await
}

async fn stabilize_leveled_houdini_inner_publication<C: FrameworkIIChecker + ?Sized>(
    state: &mut LeveledHoudiniState,
    checker: &mut C,
    control: Option<&CancellationToken>,
) -> Result<LeveledStabilizationOutcome, FrameworkIIStateError> {
    require_control_open(control)?;
    let next_revision = state.next_control_revision()?;
    let mut staged = state.stage_transition();
    let result = stabilize_leveled_houdini_inner(&mut staged, checker, control).await;
    require_control_open(control)?;
    if result.is_err() || matches!(&result, Ok(LeveledStabilizationOutcome::Failure(_))) {
        // A typed stop or checker error retains completed append-only history
        // and its invalidations, but publishes no tentative placement, Core,
        // or replacement root: the partition is left as it was when the scan
        // began.
        let history_advanced = state.merge_staged_history(&staged)?;
        if history_advanced {
            state.control_revision = next_revision;
        }
    } else {
        staged.control_revision = next_revision;
        *state = staged;
    }
    result
}

/// One bottom-up scan (\textsc{Stabilize}).
async fn stabilize_leveled_houdini_inner<C: FrameworkIIChecker + ?Sized>(
    state: &mut LeveledHoudiniState,
    checker: &mut C,
    control: Option<&CancellationToken>,
) -> Result<LeveledStabilizationOutcome, FrameworkIIStateError> {
    if let ScanOutcome::Failure(report) = run_scan(state, checker, control).await? {
        return Ok(LeveledStabilizationOutcome::Failure(report));
    }
    state.refresh_core()?;
    if state.system_installation_pending()? {
        return Err(FrameworkIIStateError::InvalidPlacement(
            "a Core cannot stabilize while reserved system rows await installation",
        ));
    }
    if state.compress_core && state.compress_core_dirty {
        if let CompressCoreOutcome::Failure(report) =
            compress_core_pass(state, checker, control).await?
        {
            return Ok(LeveledStabilizationOutcome::Failure(report));
        }
        state.compress_core_dirty = false;
    }
    Ok(LeveledStabilizationOutcome::Stabilized(state.core.clone()))
}

enum ScanOutcome {
    Completed,
    Failure(FailureReport),
}

/// The scan proper: one pass over the levels that hold pending clauses.
///
/// The halting test is exact. For `j >= 1`, if the Core has no clause at
/// level `j` (from this or any earlier epoch) and nothing sits above `j`,
/// then the level-`j+1` cohort, premises, and hypothesis set would be those
/// of level `j`, so every check there would be the check at `j` verbatim.
/// The test is not applied at level 0, so levels 0 and 1 always run.
async fn run_scan<C: FrameworkIIChecker + ?Sized>(
    state: &mut LeveledHoudiniState,
    checker: &mut C,
    control: Option<&CancellationToken>,
) -> Result<ScanOutcome, FrameworkIIStateError> {
    let mut from = FrameworkIILevel::ZERO;
    while let Some(level) = state.least_pending_level_from(from) {
        require_control_open(control)?;
        let mut failed = match init_pruning(state, checker, level, control).await? {
            PhaseOutcome::Completed(failed) => failed,
            PhaseOutcome::Failure(report) => return Ok(ScanOutcome::Failure(report)),
        };
        match step_pruning(state, checker, level, &failed, control).await? {
            PhaseOutcome::Completed(excluded) => failed.extend(excluded),
            PhaseOutcome::Failure(report) => return Ok(ScanOutcome::Failure(report)),
        }

        // Commit Pending[j] \ Q: every survivor proved both its conditions
        // against the exact cohort that commits with it.
        for clause in state.pending_at(level) {
            if failed.contains(&clause) {
                continue;
            }
            state.pending.remove(&clause);
            state.committed.insert(clause, level);
            state.ever_committed.insert(clause);
            state.compress_core_dirty = true;
        }

        if level > FrameworkIILevel::ZERO
            && !state.core_holds(level)
            && !state.core_holds_above(level)
        {
            // Level j+1 would replay level j verbatim; the failures stay
            // pending at j and the next epoch retries them from their
            // minimum levels.
            break;
        }

        if state.max_level == Some(level) {
            state.max_level_stops_total = state
                .max_level_stops_total
                .saturating_add(failed.len() as u64);
        } else {
            let successor =
                level
                    .checked_successor()
                    .ok_or(FrameworkIIStateError::InvalidPlacement(
                        "a fixed-ambient promotion overflowed its level",
                    ))?;
            for clause in &failed {
                state.pending.insert(*clause, successor);
            }
        }
        from = match level.checked_successor() {
            Some(successor) => successor,
            None => break,
        };
    }
    Ok(ScanOutcome::Completed)
}

#[derive(Debug)]
pub(super) enum PhaseOutcome {
    Completed(BTreeSet<ClauseId>),
    Failure(FailureReport),
}

/// Phase 1: one initialization query per pending clause of the level.
///
/// Within an epoch the levels below `level` are final once it starts, so the
/// initialization premises are fixed for the whole level: one frozen snapshot
/// serves every query here, and a single clause's outcome never restarts the
/// pass, because the initialization condition depends only on the strictly
/// lower levels, never on a same-level peer.
///
/// An outcome other than Proved is a failure at this level — refuted,
/// inconclusive, or suspended alike — and the clause joins `Q`. A
/// never-committed prophecy-free clause whose initialization is refuted at
/// any level is dead: the countermodel also refutes the level-zero
/// initialization (Lean: `LeveledFamily.initVC_zero_countermodel_of_countermodel`
/// and `not_initObligation_zero_of_countermodel` in
/// `DictionarySoundness.lean`), and a prophecy-free clause is decided by
/// its initialization on every halting input
/// (`prophecyFree_holds_on_halting_of_initValid`), so the contract makes
/// the verdict final.
///
/// The whole level is one batch (`houdini.tex` Section 4.4). Every outcome
/// is recorded into the ledger in check order first, and only then are its
/// consequences — the death rule, `Q`, and root invalidation — drawn, in
/// check order.
pub(super) async fn init_pruning<C: FrameworkIIChecker + ?Sized>(
    state: &mut LeveledHoudiniState,
    checker: &mut C,
    level: FrameworkIILevel,
    control: Option<&CancellationToken>,
) -> Result<PhaseOutcome, FrameworkIIStateError> {
    let cohort = state.pending_at(level);
    let snapshot = state.tentative_snapshot(&cohort, level)?;
    let order = state.check_order(&snapshot, &cohort);
    require_control_open(control)?;
    let mut cursor = SweepCursor::open(
        state,
        checker,
        FrameworkIICheckRole::Initialization,
        level,
        snapshot,
        order,
        control,
    )
    .await?;
    let mut steps = Vec::new();
    let mut halt = None;
    while let Some(item) = cursor.next(state, checker, control).await? {
        match item {
            SweepItem::Recorded(step) => steps.push(step),
            SweepItem::Failure(report) => {
                halt = Some(PhaseOutcome::Failure(report));
                break;
            }
            SweepItem::Cancelled => return Err(FrameworkIIStateError::Cancelled),
        }
    }
    let mut failed = BTreeSet::new();
    for step in steps {
        let SweepStep {
            clause,
            attempt_row,
            outcome,
        } = step;
        require_control_open(control)?;
        match outcome {
            FrameworkIICheckOutcome::Proved(_) => {}
            FrameworkIICheckOutcome::Refuted(_) => {
                let record = state.catalog.record(clause)?;
                if record.is_protected() || state.committed.contains_key(&clause) {
                    return Err(FrameworkIIStateError::InvalidEvidence(
                        "a checked adapter refuted a protected or committed clause",
                    ));
                }
                if !record.mentions_prophecy_relation() && !state.ever_committed.contains(&clause) {
                    state.pending.remove(&clause);
                    state.dead.insert(
                        clause,
                        FrameworkIIDeadCause::Refuted(
                            FrameworkIIDeadReason::ProphecyFreeInitializationRefuted {
                                attempt: attempt_row,
                            },
                        ),
                    );
                    state.invalidate_roots_depending_on(
                        clause,
                        FrameworkIIInvalidationReason::AntecedentClauseDeleted,
                    )?;
                } else {
                    // The clause survives its refutation and is promoted
                    // past this level; nothing was deleted.
                    failed.insert(clause);
                    state.invalidate_roots_depending_on(
                        clause,
                        FrameworkIIInvalidationReason::AntecedentClausePromoted,
                    )?;
                }
            }
            FrameworkIICheckOutcome::Inconclusive { .. } => {
                failed.insert(clause);
                state.invalidate_roots_depending_on(
                    clause,
                    FrameworkIIInvalidationReason::SnapshotChanged,
                )?;
            }
        }
    }
    if let Some(outcome) = halt {
        return Ok(outcome);
    }
    Ok(PhaseOutcome::Completed(failed))
}

/// Phase 2: the step greatest fixed point over the initialization survivors.
///
/// The hypothesis cohort is `Pending[j] \ (Q u Q')`, and the request's
/// snapshot contains exactly `Core u H`. A single failure drops its clause
/// from the cohort and restarts the sweep; a full sweep without a failure is
/// the fixed point.
pub(super) async fn step_pruning<C: FrameworkIIChecker + ?Sized>(
    state: &mut LeveledHoudiniState,
    checker: &mut C,
    level: FrameworkIILevel,
    initialization_failures: &BTreeSet<ClauseId>,
    control: Option<&CancellationToken>,
) -> Result<PhaseOutcome, FrameworkIIStateError> {
    let mut excluded = BTreeSet::new();
    loop {
        require_control_open(control)?;
        let cohort = state
            .pending_at(level)
            .into_iter()
            .filter(|clause| {
                !initialization_failures.contains(clause) && !excluded.contains(clause)
            })
            .collect::<BTreeSet<_>>();
        let snapshot = state.tentative_snapshot(&cohort, level)?;
        let order = state.check_order(&snapshot, &cohort);
        let mut cursor = SweepCursor::open(
            state,
            checker,
            FrameworkIICheckRole::Maintenance,
            level,
            snapshot,
            order,
            control,
        )
        .await?;
        // The whole sweep is one batch, so every outcome is recorded —
        // including the ones after the first failure, whose dictionary
        // entries answer the restarted sweep without a second launch. Only
        // the *first* failure in check order acts (`houdini.tex` Section
        // 4.4: "the single-failure drop applies to the first failure in
        // check order, and the remaining outcomes of the batch enter the
        // dictionary"); under `Sequential` dispatch the cursor never
        // reaches the later clauses at all, and the drop is the same one.
        let mut first_failure = None;
        let mut failure_report = None;
        while let Some(item) = cursor.next(state, checker, control).await? {
            match item {
                SweepItem::Recorded(step) => {
                    if !matches!(step.outcome, FrameworkIICheckOutcome::Proved(_))
                        && first_failure.is_none()
                    {
                        first_failure = Some(step);
                        if state.sweep_dispatch == FrameworkIISweepDispatch::Sequential {
                            break;
                        }
                    }
                }
                SweepItem::Failure(report) => {
                    failure_report = Some(report);
                    break;
                }
                SweepItem::Cancelled => return Err(FrameworkIIStateError::Cancelled),
            }
        }
        if let Some(report) = failure_report {
            return Ok(PhaseOutcome::Failure(report));
        }
        let Some(step) = first_failure else {
            return Ok(PhaseOutcome::Completed(excluded));
        };
        let clause = step.clause;
        require_control_open(control)?;
        match step.outcome {
            FrameworkIICheckOutcome::Refuted(_) => {
                let record = state.catalog.record(clause)?;
                if record.is_protected() || state.committed.contains_key(&clause) {
                    return Err(FrameworkIIStateError::InvalidEvidence(
                        "a checked adapter refuted a protected or committed clause",
                    ));
                }
                // The clause leaves this level's step cohort; it is
                // neither deleted nor promoted out of the run.
                excluded.insert(clause);
                state.invalidate_roots_depending_on(
                    clause,
                    FrameworkIIInvalidationReason::AntecedentClauseExcluded,
                )?;
            }
            _ => {
                // Inconclusive, suspended: a failure at this level like
                // any other, and the cohort it was checked against is
                // about to shrink.
                excluded.insert(clause);
                state.invalidate_roots_depending_on(
                    clause,
                    FrameworkIIInvalidationReason::SnapshotChanged,
                )?;
            }
        }
    }
}

/// Typed result of one [`compress_core_pass`] call.
enum CompressCoreOutcome {
    Completed,
    Failure(FailureReport),
}

/// Host option: after an epoch that changed the Core, return every Core
/// clause except the protected rows to pending at its minimum level and run
/// one scan on the Core alone, with the semantic dictionary in force.
///
/// No clause dies under compression: the death rule applies only to clauses
/// that were never committed, and a failure at a level below a clause's old
/// one promotes it. Lowering any clause only enlarges every other clause's
/// premise sets, so each clause's checks at its old level are served by proof
/// subsumption if it did not commit earlier, and the Core re-converges with
/// every clause at a level no higher than before. Should a run of the scan
/// nevertheless fail to re-converge — an inconclusive check can make a level
/// order-dependent — the whole compression is rolled back, so compression can
/// never remove a clause from the Core.
async fn compress_core_pass<C: FrameworkIIChecker + ?Sized>(
    state: &mut LeveledHoudiniState,
    checker: &mut C,
    control: Option<&CancellationToken>,
) -> Result<CompressCoreOutcome, FrameworkIIStateError> {
    require_control_open(control)?;
    let previous_committed = state.committed.clone();
    let previous_pending = state.pending.clone();
    state.compress_core_attempts_total = state.compress_core_attempts_total.saturating_add(1);

    // Stabilize the Core alone: the clauses the ordinary scan left pending
    // are set aside and restored afterwards at the levels they reached.
    state.pending.clear();
    for (clause, _) in previous_committed.iter() {
        if state.catalog.record(*clause)?.is_protected() {
            continue;
        }
        let minimum_level = state.catalog.record(*clause)?.minimum_level();
        state.committed.remove(clause);
        state.pending.insert(*clause, minimum_level);
    }
    // `Susp` is per epoch, not per scan: a clause whose launch already came
    // back inconclusive this epoch is not launched again here either.
    let scan = run_scan(state, checker, control).await;
    let reconverged = match &scan {
        Ok(ScanOutcome::Completed) => previous_committed.iter().all(|(clause, previous_level)| {
            state
                .committed
                .get(clause)
                .is_some_and(|level| level <= previous_level)
        }),
        _ => false,
    };
    if !reconverged {
        state.committed = previous_committed;
        state.pending = previous_pending;
        state.refresh_core()?;
        return match scan? {
            ScanOutcome::Failure(report) => Ok(CompressCoreOutcome::Failure(report)),
            ScanOutcome::Completed => Ok(CompressCoreOutcome::Completed),
        };
    }

    let moved = previous_committed
        .iter()
        .filter(|(clause, previous_level)| {
            state
                .committed
                .get(clause)
                .is_some_and(|level| level < *previous_level)
        })
        .count();
    state.compress_core_moves_total = state.compress_core_moves_total.saturating_add(moved as u64);
    for (clause, level) in previous_pending {
        state.pending.entry(clause).or_insert(level);
    }
    state.refresh_core()?;
    Ok(CompressCoreOutcome::Completed)
}
