//! Stable clause identities and persistent initialization classifications.

use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, MutexGuard};
use std::time::{Duration, Instant};

use serde_json::Value;
use tokio::task::JoinSet;

use crate::artifact::{ArtifactRef, ArtifactStore, ScopeTag};
use crate::encoding::{
    CatalogFormulaBindingError, EncodingError, PreparedBodyRef, PreparedWLayerBundle,
    ReferenceProposalSource, SolverBodySource, SolverEncodingContext,
};
use crate::failure::{FailureKind, FailureReport, FailureScope};
use crate::runtime::{CancellationToken, SolverAdmission};
use crate::task::{SynthesisTask, TaskIdentity};

static NEXT_CATALOG_ID: AtomicU64 = AtomicU64::new(0);

// ------------------------------------------------------------
// Formula And Clause Identity
// ------------------------------------------------------------

/// One well-formed QF formula with exact Lean-owned canonical identity.
///
/// Equality is exact task identity plus canonical serialization, never the
/// registry source ID or a digest. Phase 4A will construct these values at the
/// dynamic Lean registration boundary; the current constructor also supports
/// fixed theorem-backed sources used by the incremental implementation.
#[derive(Clone, Debug)]
pub struct ClauseFormula {
    identity: Arc<str>,
    display: Arc<str>,
    source: SolverBodySource,
    literal_set: Option<CanonicalLiteralSet>,
}

/// Canonical set of structural literals retained from one reference clause.
///
/// The Lean reference enumerator emits normalized disjunctive clauses. Rust
/// extracts this optimization key from the already validated structural
/// identity. Fixed, W-layer, and agent formulas deliberately have no key.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) struct CanonicalLiteralSet(Arc<[Arc<str>]>);

impl CanonicalLiteralSet {
    pub(super) fn from_reference_identity(identity: &str) -> Option<Self> {
        let guard: Value = serde_json::from_str(identity).ok()?;
        let mut literals = Vec::new();
        if !collect_disjunctive_literals(&guard, &mut literals) {
            return None;
        }
        literals.sort_unstable();
        if literals.windows(2).any(|pair| pair[0] == pair[1]) {
            return None;
        }
        Some(Self(literals.into()))
    }

    pub(super) fn literals(&self) -> &[Arc<str>] {
        &self.0
    }
}

fn collect_disjunctive_literals(guard: &Value, literals: &mut Vec<Arc<str>>) -> bool {
    let Some(parts) = guard.as_array() else {
        return false;
    };
    let Some(tag) = parts.first().and_then(Value::as_str) else {
        return false;
    };
    match (tag, parts.as_slice()) {
        ("false", [_]) => true,
        ("or", [_, left, right]) => {
            collect_disjunctive_literals(left, literals)
                && collect_disjunctive_literals(right, literals)
        }
        ("eq" | "subset", [_, _, _])
        | (
            "eq_empty_right" | "eq_empty_left" | "subset_empty_right" | "subset_empty_left",
            [_, _],
        ) => push_structural_literal(guard, literals),
        ("not", [_, atom]) if is_structural_atom(atom) => push_structural_literal(guard, literals),
        _ => false,
    }
}

fn is_structural_atom(value: &Value) -> bool {
    let Some(parts) = value.as_array() else {
        return false;
    };
    match parts.as_slice() {
        [tag, _, _] => tag
            .as_str()
            .is_some_and(|tag| matches!(tag, "eq" | "subset")),
        [tag, _] => tag.as_str().is_some_and(|tag| {
            matches!(
                tag,
                "eq_empty_right" | "eq_empty_left" | "subset_empty_right" | "subset_empty_left"
            )
        }),
        _ => false,
    }
}

fn push_structural_literal(value: &Value, literals: &mut Vec<Arc<str>>) -> bool {
    match serde_json::to_string(value) {
        Ok(serialized) => {
            literals.push(Arc::from(serialized));
            true
        }
        Err(_) => false,
    }
}

impl ClauseFormula {
    /// Consume one source already validated by SolverEncodingContext.
    ///
    /// This step performs no parsing or fallible reconstruction after the
    /// append-only proposal revision has committed.
    pub(crate) fn from_validated_reference_source(entry: ReferenceProposalSource) -> Self {
        let (identity, display, source) = entry.into_parts();
        let literal_set = CanonicalLiteralSet::from_reference_identity(&identity);
        Self {
            identity,
            display,
            source: SolverBodySource::QuantifierFree(source),
            literal_set,
        }
    }

    /// Borrow one complete W bundle already validated by the shared encoding
    /// context. The structural identity is the same Lean serialization used
    /// by reference proposals, so Catalog deduplication remains exact.
    #[allow(dead_code)] // Phase 4C connects the production CEX-to-INV publisher.
    pub(crate) fn from_validated_w_bundle(bundle: &PreparedWLayerBundle) -> Self {
        Self {
            identity: bundle.identity_arc(),
            display: bundle.display_arc(),
            source: SolverBodySource::QuantifierFree(bundle.formula_source().clone()),
            literal_set: None,
        }
    }

    /// Construct a fixed trusted source whose exact identity is also its
    /// certificate-facing Whiel syntax.
    ///
    /// Dynamic reference-enumerator sources enter only through the
    /// crate-private validated proposal boundary because their structural
    /// identity is deliberately distinct from human-readable syntax.
    pub fn from_trusted_lean_source(
        canonical: impl Into<Arc<str>>,
        source: SolverBodySource,
    ) -> Result<Self, &'static str> {
        let canonical = canonical.into();
        if canonical.is_empty() {
            return Err("a clause requires a nonempty canonical Lean serialization");
        }
        if !matches!(source, SolverBodySource::QuantifierFree(_)) {
            return Err("a catalog clause source must be quantifier-free");
        }
        Ok(Self {
            identity: Arc::clone(&canonical),
            display: canonical,
            source,
            literal_set: None,
        })
    }

    /// Return certificate-facing Whiel syntax for compatibility with fixed
    /// sources. Catalog identity code must use [`Self::identity`].
    pub fn canonical(&self) -> &str {
        &self.display
    }

    pub fn identity(&self) -> &str {
        &self.identity
    }

    pub(crate) fn identity_arc(&self) -> Arc<str> {
        Arc::clone(&self.identity)
    }

    pub fn certificate_formula(&self) -> &str {
        &self.display
    }

    pub fn source(&self) -> &SolverBodySource {
        &self.source
    }

    pub fn task_identity(&self) -> &TaskIdentity {
        self.source.task_identity()
    }

    pub(super) fn literal_set(&self) -> Option<&CanonicalLiteralSet> {
        self.literal_set.as_ref()
    }
}

impl PartialEq for ClauseFormula {
    fn eq(&self, other: &Self) -> bool {
        self.task_identity() == other.task_identity() && self.identity == other.identity
    }
}

impl Eq for ClauseFormula {}

impl Hash for ClauseFormula {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.task_identity().hash(state);
        self.identity.hash(state);
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ClauseId(u64);

impl ClauseId {
    pub fn get(self) -> u64 {
        self.0
    }

    /// Construct the shared scalar from one catalog-owned dense ordinal.
    /// Catalog semantics remain in the owning F1 or fixed-ambient registry.
    pub(crate) const fn from_catalog_ordinal(value: u64) -> Self {
        Self(value)
    }

    #[cfg(test)]
    pub(crate) const fn test(value: u64) -> Self {
        Self(value)
    }

    fn checked_index(self) -> Result<usize, FailureReport> {
        usize::try_from(self.0).map_err(|_| {
            initialization_failure(
                FailureKind::StateInvariantViolation,
                "ClauseId does not fit the catalog record index",
                Vec::new(),
            )
        })
    }
}

pub type ClauseSet = HashSet<ClauseId>;

/// Flat exact Candidate snapshot used only by timeout retry chains.
///
/// Phase 3C used a persistent removal lineage. That representation made a
/// membership test proportional to pruning depth and retained obsolete roots
/// through per-clause retry records. The production representation stores one
/// sorted immutable set. Equality and subset checks are bounded linear merges.
#[derive(Debug)]
pub(super) struct CandidateSnapshot {
    members: Arc<[ClauseId]>,
}

impl CandidateSnapshot {
    pub(super) fn root(candidate: Arc<ClauseSet>) -> Arc<Self> {
        let mut members = candidate.iter().copied().collect::<Vec<_>>();
        members.sort_unstable();
        Arc::new(Self {
            members: members.into(),
        })
    }

    pub(super) fn from_sorted(members: Vec<ClauseId>) -> Arc<Self> {
        debug_assert!(members.windows(2).all(|pair| pair[0] < pair[1]));
        Arc::new(Self {
            members: members.into(),
        })
    }

    pub(super) fn contains(&self, clause: ClauseId) -> bool {
        self.members.binary_search(&clause).is_ok()
    }

    pub(super) fn members(&self) -> &[ClauseId] {
        &self.members
    }

    fn is_subset_of(&self, other: &Self) -> bool {
        if self.members.len() > other.members.len() {
            return false;
        }
        let mut other_index = 0;
        for member in self.members.iter().copied() {
            while other_index < other.members.len() && other.members[other_index] < member {
                other_index += 1;
            }
            if other.members.get(other_index).copied() != Some(member) {
                return false;
            }
            other_index += 1;
        }
        true
    }

    fn same_members(&self, other: &Self) -> bool {
        self.members == other.members
    }

    pub(super) fn equals_set(&self, candidate: &ClauseSet) -> bool {
        self.members.len() == candidate.len()
            && candidate.iter().all(|clause| self.contains(*clause))
    }

    fn len(&self) -> usize {
        self.members.len()
    }
}

// ------------------------------------------------------------
// Compact Clause Records
// ------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InitializationStatus {
    Unclassified,
    InitProved,
    InitRefuted,
    InitInconclusive,
}

/// Compact classification of the latest completed per-target maintenance
/// query. Exact bulk checks retain one bulk-level capability and artifact;
/// they do not fabricate a result for each clause.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MaintenanceResultClass {
    Proved,
    Refuted,
    TimedOut,
    Failed,
}

/// The semantic use made of a completed maintenance query after the final
/// support/coverage recheck at the concurrent block boundary.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MaintenanceResultDisposition {
    Applied,
    Redundant,
    Conflicting,
    CleanupOnly,
    Canceled,
}

impl MaintenanceResultDisposition {
    pub(super) const fn history_name(self) -> &'static str {
        match self {
            Self::Applied => "applied",
            Self::Redundant => "redundant",
            Self::Conflicting => "conflicting",
            Self::CleanupOnly => "cleanup_only",
            Self::Canceled => "canceled",
        }
    }
}

/// Fixed-size identity of the exact Candidate used by one completed query.
///
/// `run_id` is globally fresh and `generation` is never reused within that
/// run. Together they identify the full Candidate without retaining it in
/// every ClauseRecord. Exact sets remain only in open retry chains and cold
/// artifacts/history.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct MaintenanceCandidateIdentity {
    run_id: u64,
    generation: u64,
    member_count: usize,
}

/// Bounded hot feedback for the latest completed per-target query.
///
/// This is hot run state, not optional audit history. Large solver output and
/// exact historical Candidate membership remain in ArtifactStore. The record
/// has constant size, so one slot per ClauseRecord keeps resident storage
/// linear in the number of registered clauses.
#[derive(Clone, Copy, Debug)]
pub struct LatestMaintenanceResult {
    candidate: MaintenanceCandidateIdentity,
    class: MaintenanceResultClass,
    disposition: MaintenanceResultDisposition,
    evidence: ArtifactRef,
}

impl LatestMaintenanceResult {
    pub fn candidate_len(&self) -> usize {
        self.candidate.member_count
    }

    pub fn candidate_run_id(&self) -> u64 {
        self.candidate.run_id
    }

    pub fn candidate_generation(&self) -> u64 {
        self.candidate.generation
    }

    pub fn class(&self) -> MaintenanceResultClass {
        self.class
    }

    pub fn disposition(&self) -> MaintenanceResultDisposition {
        self.disposition
    }

    pub fn evidence(&self) -> ArtifactRef {
        self.evidence
    }
}

impl InitializationStatus {
    fn is_conclusive(self) -> bool {
        matches!(self, Self::InitProved | Self::InitRefuted)
    }
}

#[derive(Clone, Debug)]
struct ClauseRecord {
    formula: ClauseFormula,
    formula_body: Option<PreparedBodyRef>,
    maintenance: Option<PreparedMaintenance>,
    initialization: InitializationStatus,
    initialization_evidence: Option<ArtifactRef>,
    latest_maintenance: Option<LatestMaintenanceResult>,
    explicitly_dropped: bool,
    explicitly_proposed_generation: Option<u64>,
    retry_candidate: Option<Arc<CandidateSnapshot>>,
    retry_initial_allowance: Option<Duration>,
    fmb_frontier_candidate: Option<Arc<CandidateSnapshot>>,
    next_retry_tier: usize,
    retry_exhausted: bool,
    next_fmb_start_size: Option<crate::vampire::FmbSize>,
}

#[derive(Clone, Debug)]
struct PreparedMaintenance {
    base: SolverBodySource,
    wp: SolverBodySource,
    body: PreparedBodyRef,
}

impl ClauseRecord {
    fn new(formula: ClauseFormula) -> Self {
        Self {
            formula,
            formula_body: None,
            maintenance: None,
            initialization: InitializationStatus::Unclassified,
            initialization_evidence: None,
            latest_maintenance: None,
            explicitly_dropped: false,
            explicitly_proposed_generation: None,
            retry_candidate: None,
            retry_initial_allowance: None,
            fmb_frontier_candidate: None,
            next_retry_tier: 0,
            retry_exhausted: false,
            next_fmb_start_size: None,
        }
    }

    fn snapshot(&self) -> ClauseRecordSnapshot {
        ClauseRecordSnapshot {
            formula: self.formula.clone(),
            formula_body: self.formula_body.clone(),
            maintenance: self.maintenance.clone(),
            initialization: self.initialization,
            initialization_evidence: self.initialization_evidence,
            latest_maintenance: self.latest_maintenance,
            explicitly_dropped: self.explicitly_dropped,
            retry_candidate: self.retry_candidate.clone(),
            retry_initial_allowance: self.retry_initial_allowance,
            next_retry_tier: self.next_retry_tier,
            retry_exhausted: self.retry_exhausted,
            next_fmb_start_size: self.next_fmb_start_size,
        }
    }
}

/// Read-only compact record view. Large evidence remains in ArtifactStore.
#[derive(Clone, Debug)]
pub struct ClauseRecordSnapshot {
    formula: ClauseFormula,
    formula_body: Option<PreparedBodyRef>,
    maintenance: Option<PreparedMaintenance>,
    initialization: InitializationStatus,
    initialization_evidence: Option<ArtifactRef>,
    latest_maintenance: Option<LatestMaintenanceResult>,
    explicitly_dropped: bool,
    retry_candidate: Option<Arc<CandidateSnapshot>>,
    retry_initial_allowance: Option<Duration>,
    next_retry_tier: usize,
    retry_exhausted: bool,
    next_fmb_start_size: Option<crate::vampire::FmbSize>,
}

impl ClauseRecordSnapshot {
    pub fn formula(&self) -> &ClauseFormula {
        &self.formula
    }

    pub fn formula_body(&self) -> Option<&PreparedBodyRef> {
        self.formula_body.as_ref()
    }

    pub fn maintenance_wp(&self) -> Option<&SolverBodySource> {
        self.maintenance.as_ref().map(|prepared| &prepared.wp)
    }

    pub fn maintenance_wp_body(&self) -> Option<&PreparedBodyRef> {
        self.maintenance.as_ref().map(|prepared| &prepared.body)
    }

    pub fn initialization(&self) -> InitializationStatus {
        self.initialization
    }

    pub fn initialization_evidence(&self) -> Option<ArtifactRef> {
        self.initialization_evidence
    }

    pub fn latest_maintenance(&self) -> Option<&LatestMaintenanceResult> {
        self.latest_maintenance.as_ref()
    }

    pub fn explicitly_dropped(&self) -> bool {
        self.explicitly_dropped
    }

    pub fn has_retry_candidate(&self) -> bool {
        self.retry_candidate.is_some()
    }

    pub fn retry_candidate_len(&self) -> Option<usize> {
        self.retry_candidate
            .as_ref()
            .map(|candidate| candidate.len())
    }

    pub fn retry_candidate_contains(&self, clause: ClauseId) -> Option<bool> {
        self.retry_candidate
            .as_ref()
            .map(|candidate| candidate.contains(clause))
    }

    pub fn retry_initial_allowance(&self) -> Option<Duration> {
        self.retry_initial_allowance
    }

    pub fn next_retry_tier(&self) -> usize {
        self.next_retry_tier
    }

    pub fn retry_exhausted(&self) -> bool {
        self.retry_exhausted
    }

    pub fn next_fmb_start_size(&self) -> Option<crate::vampire::FmbSize> {
        self.next_fmb_start_size
    }

    pub fn next_maintenance_allowance(
        &self,
        search_limit: Duration,
        increments: &[Duration],
        current_candidate: &ClauseSet,
    ) -> Result<Option<Duration>, &'static str> {
        let current_candidate = CandidateSnapshot::root(Arc::new(current_candidate.clone()));
        maintenance_retry_allowance(
            self.retry_candidate.as_deref(),
            self.next_retry_tier,
            self.retry_exhausted,
            search_limit,
            increments,
            &current_candidate,
        )
        .map_err(|_| "maintenance retry allowance exceeds Duration range")
    }
}

// ------------------------------------------------------------
// Shared Catalog
// ------------------------------------------------------------

#[derive(Clone)]
pub struct ClauseCatalog {
    inner: Arc<CatalogInner>,
}

struct CatalogInner {
    identity: u64,
    task: TaskIdentity,
    context: SolverEncodingContext,
    artifacts: ArtifactStore,
    record_count: AtomicU64,
    data: Mutex<CatalogData>,
}

struct CatalogData {
    /// Monotone version for every record change that can affect maintenance
    /// admission or publication. A readiness snapshot is valid exactly while
    /// this value is unchanged.
    maintenance_generation: u64,
    by_formula: HashMap<Arc<str>, ClauseId>,
    canonical_by_source: HashMap<Arc<str>, Arc<str>>,
    records: Vec<ClauseRecord>,
}

/// Exact authoritative input to one maintenance-plan build.
///
/// The Active set is complete for the supplied initialization-candidate
/// universe at `generation`; it is not a hint or a relation-derived result.
#[derive(Clone, Debug)]
pub(super) struct MaintenanceReadinessSnapshot {
    generation: u64,
    core: Arc<ClauseSet>,
    init_candidates: Arc<ClauseSet>,
    active: Arc<ClauseSet>,
    missing_wps: Arc<[(ClauseId, SolverBodySource)]>,
}

#[derive(Debug)]
pub(super) enum MaintenanceSnapshotError {
    Cancelled,
    Failure(FailureReport),
}

/// A pure retry-policy decision bound to one exact Catalog snapshot.
///
/// Selecting a permit never mutates durable retry state. Only a completed
/// timeout may commit the transition encoded by this value.
#[derive(Clone, Debug)]
pub(super) struct MaintenanceRetryPermit {
    clause: ClauseId,
    initial_allowance: Duration,
    allowance: Duration,
    current_candidate: Arc<CandidateSnapshot>,
    expected_candidate: Option<Arc<CandidateSnapshot>>,
    expected_initial_allowance: Option<Duration>,
    expected_frontier_candidate: Option<Arc<CandidateSnapshot>>,
    expected_next_tier: usize,
    expected_exhausted: bool,
    expected_fmb_start_size: Option<crate::vampire::FmbSize>,
    timeout_next_tier: usize,
    timeout_exhausted: bool,
    fmb_start_size: crate::vampire::FmbSize,
    retained_fmb_start_size: Option<crate::vampire::FmbSize>,
}

impl MaintenanceRetryPermit {
    pub(super) fn initial_allowance(&self) -> Duration {
        self.initial_allowance
    }

    pub(super) fn allowance(&self) -> Duration {
        self.allowance
    }

    pub(super) fn fmb_start_size(&self) -> crate::vampire::FmbSize {
        self.fmb_start_size
    }
}

#[derive(Clone, Debug)]
pub(super) enum MaintenanceRetryDecision {
    Ready(MaintenanceRetryPermit),
    Exhausted,
}

/// One lock-bounded snapshot of every prepared body needed by a block.
#[derive(Clone, Debug)]
pub(super) struct MaintenanceBlockBodies {
    antecedent: Arc<[PreparedBodyRef]>,
    targets: HashMap<ClauseId, PreparedBodyRef>,
}

pub(super) struct MaintenanceResultUpdate<'a> {
    pub(super) candidate: &'a CandidateSnapshot,
    pub(super) run_id: u64,
    pub(super) generation: u64,
    pub(super) class: MaintenanceResultClass,
    pub(super) disposition: MaintenanceResultDisposition,
    pub(super) evidence: ArtifactRef,
}

impl MaintenanceBlockBodies {
    pub(super) fn antecedent_snapshot(&self) -> Arc<[PreparedBodyRef]> {
        Arc::clone(&self.antecedent)
    }

    pub(super) fn target(&self, id: ClauseId) -> Option<&PreparedBodyRef> {
        self.targets.get(&id)
    }
}

impl From<FailureReport> for MaintenanceSnapshotError {
    fn from(report: FailureReport) -> Self {
        Self::Failure(report)
    }
}

impl MaintenanceReadinessSnapshot {
    pub(super) fn generation(&self) -> u64 {
        self.generation
    }

    pub(super) fn core_snapshot(&self) -> Arc<ClauseSet> {
        Arc::clone(&self.core)
    }

    pub(super) fn init_candidates_snapshot(&self) -> Arc<ClauseSet> {
        Arc::clone(&self.init_candidates)
    }

    pub(super) fn active_snapshot(&self) -> Arc<ClauseSet> {
        Arc::clone(&self.active)
    }

    pub(super) fn missing_wps_snapshot(&self) -> Arc<[(ClauseId, SolverBodySource)]> {
        Arc::clone(&self.missing_wps)
    }
}

/// Short-lived exclusive proof that one readiness snapshot is still current.
/// Dropping the guard releases Catalog mutation.
pub(super) struct MaintenancePublicationGuard<'a> {
    _data: MutexGuard<'a, CatalogData>,
}

#[derive(Clone, Debug)]
pub(super) enum MaintenancePublicationError {
    Stale,
    Failure(FailureReport),
}

impl fmt::Debug for ClauseCatalog {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ClauseCatalog")
            .field("identity", &self.inner.identity)
            .field("task", &self.inner.task.canonical_id())
            .field("record_count", &self.len())
            .finish_non_exhaustive()
    }
}

impl ClauseCatalog {
    pub fn new(
        task: &SynthesisTask,
        context: SolverEncodingContext,
        artifacts: &ArtifactStore,
    ) -> Result<Self, FailureReport> {
        if context.task_identity() != task.identity()
            || artifacts.task_identity() != task.identity()
            || context.artifact_store().backend_id() != artifacts.backend_id()
        {
            return Err(initialization_failure(
                FailureKind::InfrastructureFailure,
                "catalog task, encoding context, and artifact backend identities differ",
                Vec::new(),
            ));
        }
        let identity = NEXT_CATALOG_ID
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |value| {
                value.checked_add(1)
            })
            .map_err(|_| {
                initialization_failure(
                    FailureKind::StateInvariantViolation,
                    "catalog identity space is exhausted",
                    Vec::new(),
                )
            })?;
        Ok(Self {
            inner: Arc::new(CatalogInner {
                identity,
                task: task.identity().clone(),
                context,
                artifacts: artifacts.scoped(ScopeTag::Catalog(identity)),
                record_count: AtomicU64::new(0),
                data: Mutex::new(CatalogData {
                    maintenance_generation: 0,
                    by_formula: HashMap::new(),
                    canonical_by_source: HashMap::new(),
                    records: Vec::new(),
                }),
            }),
        })
    }

    pub fn identity(&self) -> u64 {
        self.inner.identity
    }

    pub fn task_identity(&self) -> &TaskIdentity {
        &self.inner.task
    }

    pub fn encoding_context(&self) -> &SolverEncodingContext {
        &self.inner.context
    }

    pub fn artifacts(&self) -> &ArtifactStore {
        &self.inner.artifacts
    }

    pub fn len(&self) -> usize {
        usize::try_from(self.inner.record_count.load(Ordering::Acquire))
            .expect("a committed Catalog record count fits the platform index")
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Return the dense ID represented by the current record count.
    /// Registration allocates and appends while holding the same writer lock;
    /// callers must not treat this read-only preview as a reservation.
    pub fn next_clause_id(&self) -> Result<ClauseId, FailureReport> {
        let count = self.lock_data()?.records.len();
        u64::try_from(count).map(ClauseId).map_err(|_| {
            initialization_failure(
                FailureKind::StateInvariantViolation,
                "catalog record count exceeds ClauseId range",
                Vec::new(),
            )
        })
    }

    /// Return an existing exact ID or append one dense fresh record.
    pub fn register_proposed_clause(
        &self,
        formula: ClauseFormula,
    ) -> Result<ClauseId, FailureReport> {
        if formula.task_identity() != &self.inner.task {
            return Err(initialization_failure(
                FailureKind::InfrastructureFailure,
                "proposed clause belongs to another synthesis task",
                Vec::new(),
            ));
        }
        let mut data = self.lock_data()?;
        if let Some(known_identity) = data.canonical_by_source.get(formula.source().source_id())
            && known_identity.as_ref() != formula.identity()
        {
            return Err(initialization_failure(
                FailureKind::StateInvariantViolation,
                format!(
                    "trusted source {:?} was presented for two distinct canonical formulas",
                    formula.source().source_id()
                ),
                Vec::new(),
            ));
        }
        if let Some(id) = data.by_formula.get(formula.identity()).copied() {
            let needs_source_alias = !data
                .canonical_by_source
                .contains_key(formula.source().source_id());
            if needs_source_alias {
                data.canonical_by_source.try_reserve(1).map_err(|_| {
                    initialization_failure(
                        FailureKind::InfrastructureFailure,
                        "could not reserve source-alias capacity",
                        Vec::new(),
                    )
                })?;
            }
            self.bind_context_formula(&formula)?;
            if needs_source_alias {
                data.canonical_by_source.insert(
                    Arc::from(formula.source().source_id()),
                    Arc::clone(&formula.identity),
                );
            }
            return Ok(id);
        }

        let ordinal = u64::try_from(data.records.len()).map_err(|_| {
            initialization_failure(
                FailureKind::StateInvariantViolation,
                "catalog record count exceeds ClauseId range",
                Vec::new(),
            )
        })?;
        data.by_formula.try_reserve(1).map_err(|_| {
            initialization_failure(
                FailureKind::InfrastructureFailure,
                "could not reserve formula-index capacity",
                Vec::new(),
            )
        })?;
        data.canonical_by_source.try_reserve(1).map_err(|_| {
            initialization_failure(
                FailureKind::InfrastructureFailure,
                "could not reserve source-identity capacity",
                Vec::new(),
            )
        })?;
        data.records.try_reserve(1).map_err(|_| {
            initialization_failure(
                FailureKind::InfrastructureFailure,
                "could not reserve clause-record capacity",
                Vec::new(),
            )
        })?;

        // Every fallible Catalog allocation is complete before this shared
        // binding is published. Once it succeeds, all remaining local
        // mutations are infallible while this Catalog writer is held.
        self.bind_context_formula(&formula)?;

        bump_maintenance_generation(&mut data)?;

        let id = ClauseId(ordinal);
        let identity = Arc::clone(&formula.identity);
        let source_id: Arc<str> = Arc::from(formula.source().source_id());
        data.records.push(ClauseRecord::new(formula));
        let previous = data.by_formula.insert(Arc::clone(&identity), id);
        debug_assert!(previous.is_none());
        let previous = data.canonical_by_source.insert(source_id, identity);
        debug_assert!(previous.is_none());
        self.inner
            .record_count
            .store(ordinal + 1, Ordering::Release);
        Ok(id)
    }

    pub fn find(&self, formula: &ClauseFormula) -> Result<Option<ClauseId>, FailureReport> {
        if formula.task_identity() != &self.inner.task {
            return Ok(None);
        }
        Ok(self
            .lock_data()?
            .by_formula
            .get(formula.identity())
            .copied())
    }

    pub fn record(&self, id: ClauseId) -> Result<ClauseRecordSnapshot, FailureReport> {
        let index = id.checked_index()?;
        self.lock_data()?
            .records
            .get(index)
            .map(ClauseRecord::snapshot)
            .ok_or_else(|| unknown_clause(id))
    }

    /// Replace one clause's compact latest-result slot.
    ///
    /// This deliberately does not advance `maintenance_generation`: the slot
    /// is observational feedback and required-evidence provenance, not an
    /// input to maintenance admission or plan construction.
    pub(super) fn record_maintenance_result(
        &self,
        id: ClauseId,
        update: MaintenanceResultUpdate<'_>,
    ) -> Result<(), FailureReport> {
        if !update.candidate.contains(id) {
            return Err(initialization_failure(
                FailureKind::StateInvariantViolation,
                format!(
                    "maintenance result for clause {} omits that clause from its Candidate",
                    id.get()
                ),
                vec![update.evidence],
            ));
        }
        if update.evidence.backend_id() != self.inner.artifacts.backend_id()
            || update.evidence.kind() != crate::artifact::ArtifactKind::RuntimeTrace
        {
            return Err(initialization_failure(
                FailureKind::InfrastructureFailure,
                "maintenance result evidence has the wrong backend or artifact kind",
                vec![update.evidence],
            ));
        }
        self.inner.artifacts.resolve(update.evidence)?;
        let index = id.checked_index()?;
        let mut data = self.lock_data()?;
        let record = data
            .records
            .get_mut(index)
            .ok_or_else(|| unknown_clause(id))?;
        record.latest_maintenance = Some(LatestMaintenanceResult {
            candidate: MaintenanceCandidateIdentity {
                run_id: update.run_id,
                generation: update.generation,
                member_count: update.candidate.len(),
            },
            class: update.class,
            disposition: update.disposition,
            evidence: update.evidence,
        });
        Ok(())
    }

    pub fn select_initialization_work(
        &self,
        candidates: &ClauseSet,
    ) -> Result<ClauseSet, FailureReport> {
        let data = self.lock_data()?;
        candidates
            .iter()
            .copied()
            .filter_map(|id| {
                let index = match id.checked_index() {
                    Ok(index) => index,
                    Err(error) => return Some(Err(error)),
                };
                match data.records.get(index) {
                    Some(record)
                        if matches!(
                            record.initialization,
                            InitializationStatus::Unclassified
                                | InitializationStatus::InitInconclusive
                        ) =>
                    {
                        Some(Ok(id))
                    }
                    Some(_) => None,
                    None => Some(Err(unknown_clause(id))),
                }
            })
            .collect()
    }

    pub fn select_init_proved(&self, candidates: &ClauseSet) -> Result<ClauseSet, FailureReport> {
        let data = self.lock_data()?;
        candidates
            .iter()
            .copied()
            .filter_map(|id| {
                let index = match id.checked_index() {
                    Ok(index) => index,
                    Err(error) => return Some(Err(error)),
                };
                match data.records.get(index) {
                    Some(record) if record.initialization == InitializationStatus::InitProved => {
                        Some(Ok(id))
                    }
                    Some(_) => None,
                    None => Some(Err(unknown_clause(id))),
                }
            })
            .collect()
    }

    /// Snapshot exact block bodies under one short Catalog read.
    ///
    /// Candidate bodies are sorted by ClauseId. The exact task guard follows
    /// them once, so logically identical blocks obtain identical entailment
    /// identities and proof-cache keys.
    pub(super) fn snapshot_maintenance_block_bodies(
        &self,
        candidate: &ClauseSet,
        active: &ClauseSet,
        guard: PreparedBodyRef,
        cancellation: &CancellationToken,
    ) -> Result<MaintenanceBlockBodies, MaintenanceSnapshotError> {
        let mut candidate_ids = candidate.iter().copied().collect::<Vec<_>>();
        candidate_ids.sort_unstable();
        let mut active_ids = active.iter().copied().collect::<Vec<_>>();
        active_ids.sort_unstable();

        let data = self.lock_data()?;
        let mut candidate_bodies = Vec::with_capacity(candidate_ids.len());
        for (position, id) in candidate_ids.into_iter().enumerate() {
            check_catalog_cancellation(cancellation, position)?;
            let record = catalog_record(&data, id)?;
            let body = record.formula_body.clone().ok_or_else(|| {
                initialization_failure(
                    FailureKind::StateInvariantViolation,
                    format!(
                        "Candidate clause {} lacks its prepared formula body",
                        id.get()
                    ),
                    Vec::new(),
                )
            })?;
            candidate_bodies.push(body);
        }
        candidate_bodies.push(guard);

        let mut targets = HashMap::with_capacity(active_ids.len());
        for (position, id) in active_ids.into_iter().enumerate() {
            check_catalog_cancellation(cancellation, position)?;
            let record = catalog_record(&data, id)?;
            if record.initialization != InitializationStatus::InitProved {
                return Err(initialization_failure(
                    FailureKind::StateInvariantViolation,
                    format!("Active clause {} is not InitProved", id.get()),
                    record.initialization_evidence.into_iter().collect(),
                )
                .into());
            }
            let body = record
                .maintenance
                .as_ref()
                .map(|prepared| prepared.body.clone())
                .ok_or_else(|| {
                    initialization_failure(
                        FailureKind::StateInvariantViolation,
                        format!(
                            "Active clause {} lacks its prepared maintenance WP",
                            id.get()
                        ),
                        Vec::new(),
                    )
                })?;
            targets.insert(id, body);
        }
        Ok(MaintenanceBlockBodies {
            antecedent: candidate_bodies.into(),
            targets,
        })
    }

    /// Select the next maintenance allowance without changing retry state.
    pub(super) fn select_maintenance_retry(
        &self,
        clause: ClauseId,
        candidate: Arc<CandidateSnapshot>,
        search_limit: Duration,
        increments: &[Duration],
    ) -> Result<MaintenanceRetryDecision, FailureReport> {
        let index = clause.checked_index()?;
        let (
            expected_candidate,
            expected_initial_allowance,
            expected_frontier_candidate,
            expected_next_tier,
            expected_exhausted,
            expected_fmb_start_size,
        ) = {
            let data = self.lock_data()?;
            let record = data
                .records
                .get(index)
                .ok_or_else(|| unknown_clause(clause))?;
            (
                record.retry_candidate.clone(),
                record.retry_initial_allowance,
                record.fmb_frontier_candidate.clone(),
                record.next_retry_tier,
                record.retry_exhausted,
                record.next_fmb_start_size,
            )
        };

        let Some(allowance) = maintenance_retry_allowance(
            expected_candidate.as_deref(),
            expected_next_tier,
            expected_exhausted,
            search_limit,
            increments,
            &candidate,
        )
        .map_err(|_| {
            initialization_failure(
                FailureKind::StateInvariantViolation,
                "maintenance retry allowance exceeds Duration range",
                Vec::new(),
            )
        })?
        else {
            return Ok(MaintenanceRetryDecision::Exhausted);
        };
        let advancing = expected_candidate
            .as_deref()
            .is_some_and(|previous| candidate.is_subset_of(previous));
        let same_query = expected_candidate
            .as_deref()
            .is_some_and(|previous| candidate.same_members(previous));
        let initial_allowance = if same_query {
            expected_initial_allowance.ok_or_else(|| {
                initialization_failure(
                    FailureKind::StateInvariantViolation,
                    "maintenance retry candidate lacks its initial allowance",
                    Vec::new(),
                )
            })?
        } else {
            allowance
        };
        let fmb_start_size = expected_frontier_candidate
            .as_deref()
            .filter(|previous| candidate.same_members(previous))
            .and(expected_fmb_start_size)
            .unwrap_or(crate::vampire::FmbSize::ONE);
        let retained_fmb_start_size = expected_frontier_candidate
            .as_deref()
            .filter(|previous| candidate.same_members(previous))
            .and(expected_fmb_start_size);
        let timeout_next_tier = if advancing { expected_next_tier + 1 } else { 0 };
        let timeout_exhausted = timeout_next_tier >= increments.len();
        Ok(MaintenanceRetryDecision::Ready(MaintenanceRetryPermit {
            clause,
            initial_allowance,
            allowance,
            current_candidate: candidate,
            expected_candidate,
            expected_initial_allowance,
            expected_frontier_candidate,
            expected_next_tier,
            expected_exhausted,
            expected_fmb_start_size,
            timeout_next_tier,
            timeout_exhausted,
            fmb_start_size,
            retained_fmb_start_size,
        }))
    }

    /// Commit one full timeout if the selected retry snapshot is still exact.
    pub(super) fn record_maintenance_timeout(
        &self,
        permit: &MaintenanceRetryPermit,
        next_fmb_start_size: Option<crate::vampire::FmbSize>,
    ) -> Result<(), FailureReport> {
        let index = permit.clause.checked_index()?;
        let mut data = self.lock_data()?;
        let record = data
            .records
            .get_mut(index)
            .ok_or_else(|| unknown_clause(permit.clause))?;
        let retry_snapshot_matches = match (
            record.retry_candidate.as_ref(),
            permit.expected_candidate.as_ref(),
        ) {
            (Some(current), Some(expected)) => Arc::ptr_eq(current, expected),
            (None, None) => true,
            _ => false,
        };
        if !retry_snapshot_matches
            || record.retry_initial_allowance != permit.expected_initial_allowance
            || record.fmb_frontier_candidate.as_ref().map(Arc::as_ptr)
                != permit.expected_frontier_candidate.as_ref().map(Arc::as_ptr)
            || record.next_retry_tier != permit.expected_next_tier
            || record.retry_exhausted != permit.expected_exhausted
            || record.next_fmb_start_size != permit.expected_fmb_start_size
        {
            return Err(initialization_failure(
                FailureKind::StateInvariantViolation,
                format!(
                    "maintenance retry state for clause {} changed after allowance selection",
                    permit.clause.get()
                ),
                Vec::new(),
            ));
        }
        record.retry_candidate = Some(Arc::clone(&permit.current_candidate));
        record.retry_initial_allowance = Some(permit.initial_allowance);
        record.fmb_frontier_candidate = next_fmb_start_size
            .or(permit.retained_fmb_start_size)
            .map(|_| Arc::clone(&permit.current_candidate));
        record.next_retry_tier = permit.timeout_next_tier;
        record.retry_exhausted = permit.timeout_exhausted;
        record.next_fmb_start_size = next_fmb_start_size.or(permit.retained_fmb_start_size);
        Ok(())
    }

    /// Retain safe FMB progress after a nonlogical failure without advancing
    /// the timeout allowance chain.
    pub(super) fn record_maintenance_frontier(
        &self,
        permit: &MaintenanceRetryPermit,
        next_fmb_start_size: Option<crate::vampire::FmbSize>,
    ) -> Result<(), FailureReport> {
        let Some(next_fmb_start_size) = next_fmb_start_size else {
            return Ok(());
        };
        let index = permit.clause.checked_index()?;
        let mut data = self.lock_data()?;
        let record = data
            .records
            .get_mut(index)
            .ok_or_else(|| unknown_clause(permit.clause))?;
        if record.retry_candidate.as_ref().map(Arc::as_ptr)
            != permit.expected_candidate.as_ref().map(Arc::as_ptr)
            || record.retry_initial_allowance != permit.expected_initial_allowance
            || record.fmb_frontier_candidate.as_ref().map(Arc::as_ptr)
                != permit.expected_frontier_candidate.as_ref().map(Arc::as_ptr)
            || record.next_retry_tier != permit.expected_next_tier
            || record.retry_exhausted != permit.expected_exhausted
            || record.next_fmb_start_size != permit.expected_fmb_start_size
        {
            return Err(initialization_failure(
                FailureKind::StateInvariantViolation,
                format!(
                    "maintenance retry state for clause {} changed before FMB frontier retention",
                    permit.clause.get()
                ),
                Vec::new(),
            ));
        }
        record.fmb_frontier_candidate = Some(Arc::clone(&permit.current_candidate));
        record.next_fmb_start_size = Some(next_fmb_start_size);
        Ok(())
    }

    /// Close any timeout chain after a conclusive or shortcut result.
    pub(super) fn close_maintenance_retry(&self, clause: ClauseId) -> Result<(), FailureReport> {
        let index = clause.checked_index()?;
        let mut data = self.lock_data()?;
        let record = data
            .records
            .get_mut(index)
            .ok_or_else(|| unknown_clause(clause))?;
        record.retry_candidate = None;
        record.retry_initial_allowance = None;
        record.fmb_frontier_candidate = None;
        record.next_retry_tier = 0;
        record.retry_exhausted = false;
        record.next_fmb_start_size = None;
        Ok(())
    }

    /// Take one exact maintenance-admission snapshot under one Catalog read.
    ///
    /// This scan is intentionally synchronous. Callers with large universes
    /// run it inside an admitted blocking job. The returned generation lets a
    /// later publication acquire an O(1) guard instead of repeating this
    /// unbounded scan on an async executor thread.
    pub(super) fn snapshot_maintenance_readiness(
        &self,
        init_candidates: Arc<ClauseSet>,
        core: Arc<ClauseSet>,
        proposal_generation: u64,
        cancellation: &CancellationToken,
    ) -> Result<MaintenanceReadinessSnapshot, MaintenanceSnapshotError> {
        self.snapshot_maintenance_readiness_impl(
            init_candidates,
            core,
            proposal_generation,
            true,
            cancellation,
        )
    }

    /// Select the exact initialized proposal before WP preparation.
    ///
    /// The caller runs this scan as retained CPU work. Unlike the final
    /// readiness snapshot, it does not require target WPs to exist yet.
    pub(super) fn snapshot_maintenance_selection(
        &self,
        init_candidates: Arc<ClauseSet>,
        core: Arc<ClauseSet>,
        proposal_generation: u64,
        cancellation: &CancellationToken,
    ) -> Result<MaintenanceReadinessSnapshot, MaintenanceSnapshotError> {
        self.snapshot_maintenance_readiness_impl(
            init_candidates,
            core,
            proposal_generation,
            false,
            cancellation,
        )
    }

    fn snapshot_maintenance_readiness_impl(
        &self,
        init_candidates: Arc<ClauseSet>,
        core: Arc<ClauseSet>,
        proposal_generation: u64,
        require_maintenance_wp: bool,
        cancellation: &CancellationToken,
    ) -> Result<MaintenanceReadinessSnapshot, MaintenanceSnapshotError> {
        for (position, id) in init_candidates.iter().enumerate() {
            check_catalog_cancellation(cancellation, position)?;
            if core.contains(id) {
                return Err(initialization_failure(
                    FailureKind::StateInvariantViolation,
                    "maintenance readiness requires disjoint Core and initialization candidates",
                    Vec::new(),
                )
                .into());
            }
        }

        let data = self.lock_data()?;
        validate_core_readiness(&data, &core, cancellation)?;
        let active = self.select_candidate_readiness(
            &data,
            &init_candidates,
            proposal_generation,
            require_maintenance_wp,
            cancellation,
        )?;
        let missing_wps = if require_maintenance_wp {
            Vec::new()
        } else {
            let mut missing = Vec::new();
            for (position, id) in active.iter().enumerate() {
                check_catalog_cancellation(cancellation, position)?;
                let record = catalog_record(&data, *id).expect("Active was just validated");
                if record.maintenance.is_none() {
                    missing.push((*id, record.formula.source().clone()));
                }
            }
            missing
        };
        Ok(MaintenanceReadinessSnapshot {
            generation: data.maintenance_generation,
            core,
            init_candidates,
            active: Arc::new(active),
            missing_wps: missing_wps.into(),
        })
    }

    /// Lock publication to the exact authoritative state observed by
    /// `snapshot_maintenance_readiness`.
    ///
    /// Every readiness-affecting Catalog mutation takes this same mutex and
    /// increments the generation. Therefore equality is a complete O(1)
    /// revalidation. The caller may publish its matching state tuple while
    /// this short-lived guard exists; no Catalog mutation can interleave.
    pub(super) fn lock_maintenance_publication<'a>(
        &'a self,
        snapshot: &MaintenanceReadinessSnapshot,
    ) -> Result<MaintenancePublicationGuard<'a>, MaintenancePublicationError> {
        let data = self
            .lock_data()
            .map_err(MaintenancePublicationError::Failure)?;
        if data.maintenance_generation != snapshot.generation {
            return Err(MaintenancePublicationError::Stale);
        }
        Ok(MaintenancePublicationGuard { _data: data })
    }

    fn select_candidate_readiness(
        &self,
        data: &CatalogData,
        init_candidates: &ClauseSet,
        proposal_generation: u64,
        require_maintenance_wp: bool,
        cancellation: &CancellationToken,
    ) -> Result<ClauseSet, MaintenanceSnapshotError> {
        let mut active = ClauseSet::with_capacity(init_candidates.len());
        for (position, id) in init_candidates.iter().enumerate() {
            check_catalog_cancellation(cancellation, position)?;
            let record = catalog_record(data, *id)?;
            if record.explicitly_dropped
                && record.explicitly_proposed_generation != Some(proposal_generation)
            {
                return Err(initialization_failure(
                    FailureKind::StateInvariantViolation,
                    format!(
                        "explicitly dropped clause {} remains in initialization candidates",
                        id.get()
                    ),
                    Vec::new(),
                )
                .into());
            }
            if record.formula_body.is_none() {
                return Err(initialization_failure(
                    FailureKind::StateInvariantViolation,
                    format!("clause {} lacks its prepared formula body", id.get()),
                    Vec::new(),
                )
                .into());
            }
            match record.initialization {
                InitializationStatus::Unclassified => {
                    return Err(initialization_failure(
                        FailureKind::StateInvariantViolation,
                        format!(
                            "initialization candidate {} is still Unclassified",
                            id.get()
                        ),
                        Vec::new(),
                    )
                    .into());
                }
                InitializationStatus::InitProved => {
                    if !require_maintenance_wp {
                        active.insert(*id);
                        continue;
                    }
                    let Some(prepared) = &record.maintenance else {
                        return Err(initialization_failure(
                            FailureKind::StateInvariantViolation,
                            format!(
                                "InitProved clause {} lacks its complete maintenance WP",
                                id.get()
                            ),
                            Vec::new(),
                        )
                        .into());
                    };
                    if !prepared.base.same_identity(record.formula.source())
                        || !self
                            .inner
                            .context
                            .prepared_body_matches(&prepared.wp, &prepared.body)
                    {
                        return Err(initialization_global_failure(
                            FailureKind::StateInvariantViolation,
                            format!("InitProved clause {} has a stale maintenance WP", id.get()),
                            Vec::new(),
                        )
                        .into());
                    }
                    active.insert(*id);
                }
                InitializationStatus::InitRefuted | InitializationStatus::InitInconclusive => {}
            }
        }
        Ok(active)
    }

    /// Record explicit operational drops without changing verification state.
    /// InitProved remains eligible because maintenance may still be unresolved;
    /// the state-level caller rejects Core members.
    pub(super) fn record_clause_drops(
        &self,
        dropped: &ClauseSet,
        explicitly_proposed: &ClauseSet,
        proposal_generation: u64,
    ) -> Result<(), FailureReport> {
        let mut data = self.lock_data()?;
        let mut indices = Vec::with_capacity(dropped.len());
        for id in dropped {
            let index = id.checked_index()?;
            let record = data.records.get(index).ok_or_else(|| unknown_clause(*id))?;
            if record.initialization == InitializationStatus::InitRefuted {
                return Err(initialization_failure(
                    FailureKind::StateInvariantViolation,
                    format!(
                        "permanently initialization-refuted clause {} is not drop-eligible",
                        id.get()
                    ),
                    record.initialization_evidence.into_iter().collect(),
                ));
            }
            indices.push(index);
        }
        for id in explicitly_proposed {
            let index = id.checked_index()?;
            catalog_record(&data, *id)?;
            if !dropped.contains(id) {
                indices.push(index);
            }
        }
        let changed = indices.iter().any(|index| {
            let id = ClauseId(
                u64::try_from(*index)
                    .expect("an existing Catalog index fits its original ClauseId"),
            );
            data.records[*index].explicitly_dropped != dropped.contains(&id)
                || (explicitly_proposed.contains(&id)
                    && data.records[*index].explicitly_proposed_generation
                        != Some(proposal_generation))
        });
        if changed {
            bump_maintenance_generation(&mut data)?;
        }
        for index in indices {
            let id = ClauseId(
                u64::try_from(index).expect("an existing Catalog index fits its original ClauseId"),
            );
            let record = &mut data.records[index];
            record.explicitly_dropped = record.explicitly_dropped || dropped.contains(&id);
            if explicitly_proposed.contains(&id) && !dropped.contains(&id) {
                record.explicitly_proposed_generation = Some(proposal_generation);
            }
        }
        Ok(())
    }

    /// Prepare missing bodies without retaining the serialized writer across
    /// Lean work. Every completed body is attached even when a sibling fails.
    pub async fn prepare_formula_bodies(
        &self,
        admission: &SolverAdmission,
        ids: &ClauseSet,
        cancellation: &CancellationToken,
    ) -> Result<(), EncodingError> {
        if cancellation.is_cancelled() {
            return Err(EncodingError::Cancelled);
        }
        let missing = {
            let data = self.lock_data().map_err(EncodingError::Failure)?;
            let mut missing = Vec::new();
            for id in ids {
                let index = id.checked_index().map_err(EncodingError::Failure)?;
                let record = data
                    .records
                    .get(index)
                    .ok_or_else(|| EncodingError::Failure(unknown_clause(*id)))?;
                if record.formula_body.is_none() {
                    missing.push((*id, record.formula.source().clone()));
                }
            }
            missing
        };
        if missing.is_empty() {
            return Ok(());
        }

        let mut tasks = JoinSet::new();
        let mut pending = missing.into_iter();
        let task_limit = self.inner.context.body_preparation_capacity().max(1);
        for (id, source) in pending.by_ref().take(task_limit) {
            let context = self.inner.context.clone();
            let admission = admission.clone();
            let artifacts = self.inner.artifacts.clone();
            let cancellation = cancellation.clone();
            tasks.spawn(async move {
                let result = context
                    .prepare_solver_bodies(&admission, &artifacts, vec![source], &cancellation)
                    .await
                    .map(|mut bodies| {
                        debug_assert_eq!(bodies.len(), 1);
                        bodies.remove(0)
                    });
                (id, result)
            });
        }

        let mut selected_error = None;
        while let Some(joined) = tasks.join_next().await {
            let (id, result) = match joined {
                Ok(result) => result,
                Err(error) => {
                    retain_preparation_error(
                        &mut selected_error,
                        EncodingError::Failure(initialization_failure(
                            FailureKind::InfrastructureFailure,
                            format!("formula-body preparation task failed: {error}"),
                            Vec::new(),
                        )),
                    );
                    continue;
                }
            };
            match result {
                Ok(body) => {
                    if let Err(error) = self.attach_formula_body(id, body) {
                        retain_preparation_error(
                            &mut selected_error,
                            EncodingError::Failure(error),
                        );
                    }
                }
                Err(error) => retain_preparation_error(&mut selected_error, error),
            }
            if selected_error.is_none()
                && let Some((id, source)) = pending.next()
            {
                let context = self.inner.context.clone();
                let admission = admission.clone();
                let artifacts = self.inner.artifacts.clone();
                let cancellation = cancellation.clone();
                tasks.spawn(async move {
                    let result = context
                        .prepare_solver_bodies(&admission, &artifacts, vec![source], &cancellation)
                        .await
                        .map(|mut bodies| {
                            debug_assert_eq!(bodies.len(), 1);
                            bodies.remove(0)
                        });
                    (id, result)
                });
            }
        }
        match selected_error {
            Some(error) => Err(error),
            None => Ok(()),
        }
    }

    /// Compute missing exact target WPs through Lean and publish each WP/body
    /// pair atomically. No Catalog lock is retained across worker execution.
    pub(super) async fn prepare_maintenance_wps(
        &self,
        admission: &SolverAdmission,
        selection: &MaintenanceReadinessSnapshot,
        cancellation: &CancellationToken,
    ) -> Result<(), EncodingError> {
        if cancellation.is_cancelled() {
            return Err(EncodingError::Cancelled);
        }
        let missing = selection.missing_wps_snapshot();
        if missing.is_empty() {
            return Ok(());
        }

        let mut tasks = JoinSet::new();
        let mut next_missing = 0;
        let task_limit = self.inner.context.body_preparation_capacity().max(1);
        while next_missing < missing.len() && tasks.len() < task_limit {
            let (id, source) = missing[next_missing].clone();
            next_missing += 1;
            let context = self.inner.context.clone();
            let admission = admission.clone();
            let artifacts = self.inner.artifacts.clone();
            let cancellation = cancellation.clone();
            tasks.spawn(async move {
                let result = context
                    .prepare_maintenance_wp(&admission, &artifacts, source.clone(), &cancellation)
                    .await;
                (id, source, result)
            });
        }

        let mut selected_error = None;
        while let Some(joined) = tasks.join_next().await {
            let (id, source, result) = match joined {
                Ok(result) => result,
                Err(error) => {
                    retain_preparation_error(
                        &mut selected_error,
                        EncodingError::Failure(initialization_failure(
                            FailureKind::InfrastructureFailure,
                            format!("maintenance-WP preparation task failed: {error}"),
                            Vec::new(),
                        )),
                    );
                    continue;
                }
            };
            match result {
                Ok(body) => {
                    if let Err(error) = self.attach_maintenance_wp(id, &source, body) {
                        retain_preparation_error(
                            &mut selected_error,
                            EncodingError::Failure(error),
                        );
                    }
                }
                Err(error) => retain_preparation_error(&mut selected_error, error),
            }
            if selected_error.is_none() && next_missing < missing.len() {
                let (id, source) = missing[next_missing].clone();
                next_missing += 1;
                let context = self.inner.context.clone();
                let admission = admission.clone();
                let artifacts = self.inner.artifacts.clone();
                let cancellation = cancellation.clone();
                tasks.spawn(async move {
                    let result = context
                        .prepare_maintenance_wp(
                            &admission,
                            &artifacts,
                            source.clone(),
                            &cancellation,
                        )
                        .await;
                    (id, source, result)
                });
            }
        }
        match selected_error {
            Some(error) => Err(error),
            None => Ok(()),
        }
    }

    /// Accept one caller-asserted exact maintenance WP and prepare its body
    /// through the same Lean-owned translation boundary. The semantic claim
    /// that `wp` is exact belongs to the trusted clause producer.
    pub async fn prepare_supplied_maintenance_wp(
        &self,
        admission: &SolverAdmission,
        id: ClauseId,
        wp: ClauseFormula,
        cancellation: &CancellationToken,
    ) -> Result<(), EncodingError> {
        if wp.task_identity() != &self.inner.task {
            return Err(EncodingError::Failure(initialization_failure(
                FailureKind::InfrastructureFailure,
                "supplied maintenance WP belongs to another task",
                Vec::new(),
            )));
        }
        let base = self
            .record(id)
            .map_err(EncodingError::Failure)?
            .formula()
            .source()
            .clone();
        let mut bodies = self
            .inner
            .context
            .prepare_solver_bodies(
                admission,
                &self.inner.artifacts,
                vec![wp.source().clone()],
                cancellation,
            )
            .await?;
        debug_assert_eq!(bodies.len(), 1);
        let body = bodies.remove(0);
        self.attach_prepared_maintenance(id, &base, wp.source(), body)
            .map_err(EncodingError::Failure)
    }

    /// Attach the exact maintenance WP already prepared by a trusted producer.
    ///
    /// Dynamic W construction uses this path so admission into INV reuses the
    /// CEX-owned WP body instead of asking Lean to compute the same WP again.
    pub(crate) fn accept_prepared_maintenance_wp(
        &self,
        id: ClauseId,
        expected_formula_identity: &str,
        body: PreparedBodyRef,
    ) -> Result<(), FailureReport> {
        let record = self.record(id)?;
        if record.formula().identity() != expected_formula_identity {
            return Err(initialization_global_failure(
                FailureKind::StateInvariantViolation,
                "prepared W maintenance WP differs from the interned formula identity",
                Vec::new(),
            ));
        }
        // Catalog interning is structural, not source-based. An ordinary
        // proposal or an earlier W index can therefore have prepared the same
        // formula through another exact source identity. Keep that complete
        // package: weakest precondition is extensional in the formula, and
        // replacing it merely because W used a different source alias would
        // make admission order-dependent.
        if record.maintenance_wp_body().is_some() {
            return Ok(());
        }
        let target = record.formula().source().clone();
        let wp = body.source().clone();
        self.attach_prepared_maintenance(id, &target, &wp, body)
    }

    /// Atomically commit one durable initialization classification.
    ///
    /// Callers establish the logical basis for the status. The Catalog only
    /// enforces evidence/backend coupling and rejects contradictory durable
    /// conclusions.
    pub fn record_initialization(
        &self,
        id: ClauseId,
        status: InitializationStatus,
        evidence: ArtifactRef,
    ) -> Result<(), FailureReport> {
        if status == InitializationStatus::Unclassified {
            return Err(initialization_failure(
                FailureKind::StateInvariantViolation,
                "an initialization update cannot write Unclassified with evidence",
                vec![evidence],
            ));
        }
        if evidence.backend_id() != self.inner.artifacts.backend_id()
            || evidence.kind() != crate::artifact::ArtifactKind::InitializationCheck
        {
            return Err(initialization_failure(
                FailureKind::InfrastructureFailure,
                "initialization evidence has the wrong backend or artifact kind",
                vec![evidence],
            ));
        }
        let resolved = self.inner.artifacts.resolve(evidence)?;
        let expected_scope = format!("catalog:{}", self.inner.identity);
        if !resolved
            .scope()
            .iter()
            .any(|scope| scope == &expected_scope)
        {
            return Err(initialization_failure(
                FailureKind::InfrastructureFailure,
                "initialization evidence belongs to another Catalog scope",
                vec![evidence],
            ));
        }
        let index = id.checked_index()?;
        let mut data = self.lock_data()?;
        let record = data.records.get(index).ok_or_else(|| unknown_clause(id))?;
        let old = record.initialization;
        if old.is_conclusive() && status.is_conclusive() && old != status {
            return Err(initialization_failure(
                FailureKind::StateInvariantViolation,
                format!(
                    "conflicting conclusive initialization classifications for clause {}: {old:?} then {status:?}",
                    id.get()
                ),
                vec![
                    record
                        .initialization_evidence
                        .expect("a classified record always has evidence"),
                    evidence,
                ],
            ));
        }
        if old.is_conclusive() {
            return Ok(());
        }
        bump_maintenance_generation(&mut data)?;
        let record = &mut data.records[index];
        record.initialization = status;
        record.initialization_evidence = Some(evidence);
        Ok(())
    }

    /// Accept one same-run initialization proof from another lane.
    ///
    /// The original artifact remains in its producer scope. This Catalog
    /// publishes a small acceptance record which refers to that artifact, so
    /// the existing conflict-aware initialization path retains one local
    /// evidence reference without copying the proof payload.
    pub fn accept_external_initialization_proof(
        &self,
        id: ClauseId,
        evidence: ArtifactRef,
    ) -> Result<ArtifactRef, FailureReport> {
        if evidence.backend_id() != self.inner.artifacts.backend_id()
            || evidence.kind() != crate::artifact::ArtifactKind::InitializationCheck
        {
            return Err(initialization_global_failure(
                FailureKind::InfrastructureFailure,
                "external initialization evidence has the wrong backend or artifact kind",
                vec![evidence],
            ));
        }
        self.inner.artifacts.resolve(evidence)?;
        let acceptance = serde_json::json!({
            "kind": "external_initialization_acceptance",
            "clause_id": id.get(),
            "source": {
                "backend_id": evidence.backend_id().to_string(),
                "artifact_id": evidence.local_id(),
                "artifact_kind": "initialization_check",
            },
        });
        let accepted = self
            .inner
            .artifacts
            .publish(
                crate::artifact::ArtifactKind::InitializationCheck,
                acceptance.to_string().into_bytes().into_boxed_slice(),
            )
            .map_err(|report| {
                initialization_global_failure(
                    if report.kind() == FailureKind::PublicationFailure {
                        FailureKind::PublicationFailure
                    } else {
                        FailureKind::InfrastructureFailure
                    },
                    format!(
                        "publish external initialization acceptance: {}",
                        report.detail().unwrap_or("artifact backend failure")
                    ),
                    vec![evidence],
                )
            })?;
        self.record_initialization(id, InitializationStatus::InitProved, accepted)?;
        Ok(accepted)
    }

    fn attach_formula_body(
        &self,
        id: ClauseId,
        body: PreparedBodyRef,
    ) -> Result<(), FailureReport> {
        if body.context_id() != self.inner.context.context_id()
            || body.source().task_identity() != &self.inner.task
        {
            return Err(initialization_failure(
                FailureKind::InfrastructureFailure,
                "prepared clause body belongs to another task or encoding context",
                Vec::new(),
            ));
        }
        let index = id.checked_index()?;
        let mut data = self.lock_data()?;
        let record = data.records.get(index).ok_or_else(|| unknown_clause(id))?;
        if body.source().source_id() != record.formula.source().source_id() {
            return Err(initialization_failure(
                FailureKind::StateInvariantViolation,
                "prepared clause body does not match the registered source",
                Vec::new(),
            ));
        }
        match &record.formula_body {
            Some(existing) if existing.body_id() != body.body_id() => Err(initialization_failure(
                FailureKind::StateInvariantViolation,
                "one clause acquired conflicting prepared formula bodies",
                Vec::new(),
            )),
            Some(_) => Ok(()),
            None => {
                bump_maintenance_generation(&mut data)?;
                data.records[index].formula_body = Some(body);
                Ok(())
            }
        }
    }

    fn attach_maintenance_wp(
        &self,
        id: ClauseId,
        target: &SolverBodySource,
        body: PreparedBodyRef,
    ) -> Result<(), FailureReport> {
        if !self.inner.context.maintenance_wp_matches(target, &body) {
            return Err(initialization_global_failure(
                FailureKind::StateInvariantViolation,
                "prepared maintenance WP does not match its target source",
                Vec::new(),
            ));
        }
        let wp = body.source().clone();
        self.attach_prepared_maintenance(id, target, &wp, body)
    }

    fn attach_prepared_maintenance(
        &self,
        id: ClauseId,
        target: &SolverBodySource,
        wp: &SolverBodySource,
        body: PreparedBodyRef,
    ) -> Result<(), FailureReport> {
        if !self.inner.context.prepared_body_matches(wp, &body) {
            return Err(initialization_global_failure(
                FailureKind::StateInvariantViolation,
                "prepared maintenance body does not match its exact WP source",
                Vec::new(),
            ));
        }
        let index = id.checked_index()?;
        let mut data = self.lock_data()?;
        let record = data.records.get(index).ok_or_else(|| unknown_clause(id))?;
        if record.formula.source().source_id() != target.source_id() {
            return Err(initialization_global_failure(
                FailureKind::StateInvariantViolation,
                "maintenance WP target differs from the registered clause source",
                Vec::new(),
            ));
        }
        match &record.maintenance {
            Some(existing)
                if !existing.base.same_identity(target)
                    || !existing.wp.same_identity(wp)
                    || existing.body.body_id() != body.body_id() =>
            {
                Err(initialization_global_failure(
                    FailureKind::StateInvariantViolation,
                    "one clause acquired conflicting prepared maintenance WPs",
                    Vec::new(),
                ))
            }
            Some(_) => Ok(()),
            None => {
                bump_maintenance_generation(&mut data)?;
                data.records[index].maintenance = Some(PreparedMaintenance {
                    base: target.clone(),
                    wp: wp.clone(),
                    body,
                });
                Ok(())
            }
        }
    }

    fn bind_context_formula(&self, formula: &ClauseFormula) -> Result<(), FailureReport> {
        self.inner
            .context
            .bind_catalog_formula(formula.source().source_id(), formula.identity())
            .map_err(|error| match error {
                CatalogFormulaBindingError::ConflictingCanonicalIdentity => {
                    initialization_global_failure(
                        FailureKind::StateInvariantViolation,
                        format!(
                            "trusted source {:?} was presented for two distinct canonical formulas in one encoding context",
                            formula.source().source_id()
                        ),
                        Vec::new(),
                    )
                }
                CatalogFormulaBindingError::Capacity => initialization_failure(
                    FailureKind::InfrastructureFailure,
                    "could not reserve encoding-context source-binding capacity",
                    Vec::new(),
                ),
                CatalogFormulaBindingError::Poisoned => initialization_global_failure(
                    FailureKind::InfrastructureFailure,
                    "encoding-context source-binding lock was poisoned",
                    Vec::new(),
                ),
            })
    }

    fn lock_data(&self) -> Result<MutexGuard<'_, CatalogData>, FailureReport> {
        self.inner.data.lock().map_err(|_| {
            initialization_global_failure(
                FailureKind::InfrastructureFailure,
                "Catalog writer lock was poisoned",
                Vec::new(),
            )
        })
    }
}

// ------------------------------------------------------------
// Registration
// ------------------------------------------------------------

#[derive(Clone, Debug)]
pub enum RegisteredClauses {
    Complete(ClauseSet),
    Failure {
        retained_registrations: ClauseSet,
        report: FailureReport,
    },
    Cancelled {
        retained_registrations: ClauseSet,
    },
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct RegistrationTiming {
    pub catalog_registration: Duration,
    pub formula_body_preparation: Duration,
}

impl RegisteredClauses {
    /// Return usable clause IDs only after every required body is complete.
    pub fn complete_clauses(&self) -> Option<&ClauseSet> {
        match self {
            Self::Complete(clauses) => Some(clauses),
            Self::Failure { .. } | Self::Cancelled { .. } => None,
        }
    }

    pub fn failure(&self) -> Option<&FailureReport> {
        match self {
            Self::Failure { report, .. } => Some(report),
            Self::Complete(_) | Self::Cancelled { .. } => None,
        }
    }

    pub fn was_cancelled(&self) -> bool {
        matches!(self, Self::Cancelled { .. })
    }

    /// Registrations survive an incomplete preparation for a later retry,
    /// but are not safe initialization work in this outcome.
    pub fn retained_registrations(&self) -> &ClauseSet {
        match self {
            Self::Complete(clauses) => clauses,
            Self::Failure {
                retained_registrations,
                ..
            }
            | Self::Cancelled {
                retained_registrations,
            } => retained_registrations,
        }
    }
}

pub async fn register_clauses(
    catalog: &ClauseCatalog,
    admission: &SolverAdmission,
    proposed: impl IntoIterator<Item = ClauseFormula>,
    cancellation: &CancellationToken,
) -> RegisteredClauses {
    register_clauses_with_timing(catalog, admission, proposed, cancellation)
        .await
        .0
}

pub(crate) async fn register_clauses_with_timing(
    catalog: &ClauseCatalog,
    admission: &SolverAdmission,
    proposed: impl IntoIterator<Item = ClauseFormula>,
    cancellation: &CancellationToken,
) -> (RegisteredClauses, RegistrationTiming) {
    let mut clauses = ClauseSet::new();
    let registration_started = Instant::now();
    for formula in proposed {
        match catalog.register_proposed_clause(formula) {
            Ok(id) => {
                clauses.insert(id);
            }
            Err(failure) => {
                return (
                    RegisteredClauses::Failure {
                        retained_registrations: clauses,
                        report: failure,
                    },
                    RegistrationTiming {
                        catalog_registration: registration_started.elapsed(),
                        formula_body_preparation: Duration::ZERO,
                    },
                );
            }
        }
    }
    let catalog_registration = registration_started.elapsed();
    let preparation_started = Instant::now();
    let outcome = match catalog
        .prepare_formula_bodies(admission, &clauses, cancellation)
        .await
    {
        Ok(()) => RegisteredClauses::Complete(clauses),
        Err(EncodingError::Failure(report)) => RegisteredClauses::Failure {
            retained_registrations: clauses,
            report,
        },
        Err(EncodingError::Cancelled) => RegisteredClauses::Cancelled {
            retained_registrations: clauses,
        },
    };
    (
        outcome,
        RegistrationTiming {
            catalog_registration,
            formula_body_preparation: preparation_started.elapsed(),
        },
    )
}

// ------------------------------------------------------------
// Initialization Coverage
// ------------------------------------------------------------

#[derive(Clone, Debug)]
pub struct InitCoverage {
    catalog_identity: u64,
    outgoing: Arc<HashMap<ClauseId, HashSet<ClauseId>>>,
    incoming: Arc<HashMap<ClauseId, HashSet<ClauseId>>>,
    transitively_closed: bool,
}

impl InitCoverage {
    pub fn new(catalog: &ClauseCatalog) -> Self {
        Self {
            catalog_identity: catalog.identity(),
            outgoing: Arc::new(HashMap::new()),
            incoming: Arc::new(HashMap::new()),
            transitively_closed: true,
        }
    }

    pub fn insert(
        &mut self,
        catalog: &ClauseCatalog,
        source: ClauseId,
        target: ClauseId,
    ) -> Result<bool, FailureReport> {
        self.validate_catalog(catalog)?;
        catalog.record(source)?;
        catalog.record(target)?;
        let inserted = Arc::make_mut(&mut self.outgoing)
            .entry(source)
            .or_default()
            .insert(target);
        if inserted {
            Arc::make_mut(&mut self.incoming)
                .entry(target)
                .or_default()
                .insert(source);
            self.transitively_closed = false;
        }
        Ok(inserted)
    }

    pub fn contains(&self, source: ClauseId, target: ClauseId) -> bool {
        self.outgoing
            .get(&source)
            .is_some_and(|targets| targets.contains(&target))
    }

    pub fn is_transitively_closed(&self) -> bool {
        self.transitively_closed
    }

    pub fn edge_count(&self) -> usize {
        self.outgoing.values().map(HashSet::len).sum()
    }

    pub(super) fn edges(&self) -> impl Iterator<Item = (ClauseId, ClauseId)> + '_ {
        self.outgoing
            .iter()
            .flat_map(|(source, targets)| targets.iter().map(move |target| (*source, *target)))
    }

    pub(crate) fn covering_proved_pairs(
        &self,
        catalog: &ClauseCatalog,
        targets: &ClauseSet,
    ) -> Result<Vec<(ClauseId, ClauseId)>, FailureReport> {
        self.validate_closed(catalog)?;
        let sources = self.outgoing.keys().copied().collect::<ClauseSet>();
        let proved = catalog.select_init_proved(&sources)?;
        self.covering_pairs_from_sources(catalog, &proved, targets)
    }

    pub(crate) fn covering_pairs_from_source(
        &self,
        catalog: &ClauseCatalog,
        source: ClauseId,
        targets: &ClauseSet,
    ) -> Result<Vec<(ClauseId, ClauseId)>, FailureReport> {
        self.validate_closed(catalog)?;
        let sources = ClauseSet::from([source]);
        let proved = catalog.select_init_proved(&sources)?;
        if proved != sources {
            return Err(initialization_failure(
                FailureKind::StateInvariantViolation,
                format!(
                    "initialization coverage source {} is not durably InitProved",
                    source.get()
                ),
                Vec::new(),
            ));
        }
        self.covering_pairs_from_sources(catalog, &sources, targets)
    }

    fn covering_pairs_from_sources(
        &self,
        catalog: &ClauseCatalog,
        sources: &ClauseSet,
        targets: &ClauseSet,
    ) -> Result<Vec<(ClauseId, ClauseId)>, FailureReport> {
        self.validate_closed(catalog)?;
        let mut covered = BTreeMap::<ClauseId, ClauseId>::new();
        let mut ordered_sources = sources.iter().copied().collect::<Vec<_>>();
        ordered_sources.sort_unstable();
        for source in ordered_sources {
            let Some(outgoing) = self.outgoing.get(&source) else {
                continue;
            };
            for target in outgoing {
                if targets.contains(target) {
                    covered.entry(*target).or_insert(source);
                }
            }
        }
        Ok(covered.into_iter().collect())
    }

    fn validate_catalog(&self, catalog: &ClauseCatalog) -> Result<(), FailureReport> {
        if self.catalog_identity != catalog.identity() {
            return Err(initialization_failure(
                FailureKind::InfrastructureFailure,
                "InitCoverage belongs to another ClauseCatalog",
                Vec::new(),
            ));
        }
        Ok(())
    }

    pub(super) fn validate_closed(&self, catalog: &ClauseCatalog) -> Result<(), FailureReport> {
        self.validate_catalog(catalog)?;
        if !self.transitively_closed {
            return Err(initialization_failure(
                FailureKind::StateInvariantViolation,
                "initialization checking requires transitively closed InitCoverage",
                Vec::new(),
            ));
        }
        Ok(())
    }
}

/// Compute exact positive-path transitive closure. Self edges arise only from
/// explicit self edges or cycles; closure is not reflexive by default.
pub fn close_init_coverage(coverage: &mut InitCoverage) {
    if coverage.transitively_closed {
        return;
    }
    let sources = coverage
        .outgoing
        .keys()
        .chain(coverage.outgoing.values().flatten())
        .copied()
        .collect::<HashSet<_>>();
    let direct = Arc::clone(&coverage.outgoing);
    let mut closed = HashMap::new();
    for source in sources {
        let mut reached = HashSet::new();
        let mut queue = direct
            .get(&source)
            .into_iter()
            .flatten()
            .copied()
            .collect::<VecDeque<_>>();
        while let Some(target) = queue.pop_front() {
            if !reached.insert(target) {
                continue;
            }
            if let Some(next) = direct.get(&target) {
                queue.extend(next.iter().copied());
            }
        }
        if !reached.is_empty() {
            closed.insert(source, reached);
        }
    }
    coverage.outgoing = Arc::new(closed);
    let mut incoming = HashMap::<ClauseId, HashSet<ClauseId>>::new();
    for (source, targets) in coverage.outgoing.iter() {
        for target in targets {
            incoming.entry(*target).or_default().insert(*source);
        }
    }
    coverage.incoming = Arc::new(incoming);
    coverage.transitively_closed = true;
}

// ------------------------------------------------------------
// Internal Failure Selection
// ------------------------------------------------------------

fn bump_maintenance_generation(data: &mut CatalogData) -> Result<(), FailureReport> {
    data.maintenance_generation = data.maintenance_generation.checked_add(1).ok_or_else(|| {
        initialization_global_failure(
            FailureKind::StateInvariantViolation,
            "Catalog maintenance-generation space is exhausted",
            Vec::new(),
        )
    })?;
    Ok(())
}

fn catalog_record(data: &CatalogData, id: ClauseId) -> Result<&ClauseRecord, FailureReport> {
    let index = id.checked_index()?;
    data.records.get(index).ok_or_else(|| unknown_clause(id))
}

fn validate_core_readiness(
    data: &CatalogData,
    core: &ClauseSet,
    cancellation: &CancellationToken,
) -> Result<(), MaintenanceSnapshotError> {
    for (position, id) in core.iter().enumerate() {
        check_catalog_cancellation(cancellation, position)?;
        let record = catalog_record(data, *id)?;
        if record.initialization != InitializationStatus::InitProved {
            return Err(initialization_failure(
                FailureKind::StateInvariantViolation,
                format!("Core clause {} is not authoritatively InitProved", id.get()),
                record.initialization_evidence.into_iter().collect(),
            )
            .into());
        }
        if record.formula_body.is_none() {
            return Err(initialization_failure(
                FailureKind::StateInvariantViolation,
                format!("Core clause {} lacks its prepared formula body", id.get()),
                Vec::new(),
            )
            .into());
        }
    }
    Ok(())
}

fn check_catalog_cancellation(
    cancellation: &CancellationToken,
    position: usize,
) -> Result<(), MaintenanceSnapshotError> {
    if position % 1024 == 0 && cancellation.is_cancelled() {
        Err(MaintenanceSnapshotError::Cancelled)
    } else {
        Ok(())
    }
}

pub(super) fn maintenance_retry_allowance(
    previous: Option<&CandidateSnapshot>,
    next_tier: usize,
    exhausted: bool,
    search_limit: Duration,
    increments: &[Duration],
    current: &CandidateSnapshot,
) -> Result<Option<Duration>, ()> {
    let Some(previous) = previous else {
        return Ok(Some(search_limit));
    };
    if !current.is_subset_of(previous) {
        return Ok(Some(search_limit));
    }
    if exhausted || next_tier >= increments.len() {
        return Ok(None);
    }
    increments[..=next_tier]
        .iter()
        .try_fold(search_limit, |allowance, increment| {
            allowance.checked_add(*increment).ok_or(())
        })
        .map(Some)
}

pub(crate) fn initialization_failure(
    kind: FailureKind,
    detail: impl Into<String>,
    artifacts: Vec<ArtifactRef>,
) -> FailureReport {
    FailureReport::try_new(
        crate::failure::FailureOrigin::InitializationExecution,
        kind,
        false,
        FailureScope::LaneLocal,
        Some(detail.into()),
        artifacts,
    )
    .expect("initialization helper uses a permitted failure kind")
}

fn initialization_global_failure(
    kind: FailureKind,
    detail: impl Into<String>,
    artifacts: Vec<ArtifactRef>,
) -> FailureReport {
    FailureReport::try_new(
        crate::failure::FailureOrigin::InitializationExecution,
        kind,
        false,
        FailureScope::RunGlobal,
        Some(detail.into()),
        artifacts,
    )
    .expect("global initialization helper uses a permitted failure kind")
}

fn unknown_clause(id: ClauseId) -> FailureReport {
    initialization_failure(
        FailureKind::StateInvariantViolation,
        format!("unknown ClauseId {}", id.get()),
        Vec::new(),
    )
}

fn retain_preparation_error(selected: &mut Option<EncodingError>, candidate: EncodingError) {
    let candidate_rank = match &candidate {
        EncodingError::Failure(report) if report.scope() == FailureScope::RunGlobal => 2,
        EncodingError::Failure(_) => 1,
        EncodingError::Cancelled => 0,
    };
    let selected_rank = match selected {
        Some(EncodingError::Failure(report)) if report.scope() == FailureScope::RunGlobal => 2,
        Some(EncodingError::Failure(_)) => 1,
        Some(EncodingError::Cancelled) => 0,
        None => return *selected = Some(candidate),
    };
    if candidate_rank > selected_rank {
        *selected = Some(candidate);
    }
}

#[cfg(test)]
mod retry_tests {
    use super::*;

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[tokio::test]
    async fn maintenance_retry_baseline_resets_only_when_the_exact_query_changes() {
        use std::fs;
        use std::time::{SystemTime, UNIX_EPOCH};

        use crate::artifact::{ArtifactStoreConfig, new_artifact_store};
        use crate::encoding::{
            EncodingWorkerCommand, EncodingWorkerPoolConfig, QfSolverSource, SolverBodySource,
            new_solver_encoding_context,
        };
        use crate::task::SynthesisTask;

        let task = SynthesisTask::from_json(
            r#"{
              "format_version":3,"semantic_version":1,"encoding_version":1,
              "identity":{"canonical_id":"CatalogRetryBaseline","module":"Whiel.Test.CatalogRetryBaseline","namespace":"Whiel.Test.CatalogRetryBaseline","source_sha256":"0000000000000000000000000000000000000000000000000000000000000000"},
              "schema":{"expression":"Whiel.Test.CatalogRetryBaseline.programSchema","display":"schema"},
              "original":{"pre":{"expression":"Whiel.Test.CatalogRetryBaseline.inputPre","display":"true"},"command":{"expression":"Whiel.Test.CatalogRetryBaseline.inputCmd","display":"SKIP"},"post":{"expression":"Whiel.Test.CatalogRetryBaseline.inputPost","display":"true"}},
              "preprocessed":{"pre":{"expression":"Whiel.Test.CatalogRetryBaseline.inputPreproc.loopPre","display":"true"},"command":{"expression":"Whiel.Test.CatalogRetryBaseline.inputPreproc.loopCmd","display":"SKIP"},"post":{"expression":"Whiel.Test.CatalogRetryBaseline.inputPreproc.loopPost","display":"true"}},
              "preprocessing_evidence":{"expression":"Whiel.Test.CatalogRetryBaseline.inputPreproc"},
              "solver":{"schema_relations":[],"task_constants":[],
                "preprocessed_pre":{"source_id":"task.preprocessed_pre","expression":"Whiel.Test.CatalogRetryBaseline.inputPreproc.loopPre","no_bound_expression":"Whiel.Test.CatalogRetryBaseline.inputPreproc.loopPre_noBound","constants":[],"relations":[]},
                "preprocessed_post":{"source_id":"task.preprocessed_post","expression":"Whiel.Test.CatalogRetryBaseline.inputPreproc.loopPost","no_bound_expression":"Whiel.Test.CatalogRetryBaseline.inputPreproc.loopPost_noBound","constants":[],"relations":[]},
                "loop_guard":{"source_id":"task.loop_guard","constants":[],"relations":[]},
                "negated_loop_guard":{"source_id":"task.negated_loop_guard","constants":[],"relations":[]}}
            }"#,
        )
        .unwrap();
        let root = std::env::temp_dir().join(format!(
            "whiel_catalog_retry_baseline_{}_{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos(),
        ));
        let (owner, artifacts) =
            new_artifact_store(&task, ArtifactStoreConfig::new(&root)).unwrap();
        let workers = EncodingWorkerPoolConfig::new(
            EncodingWorkerCommand::new("/bin/false", env!("CARGO_MANIFEST_DIR")),
            1,
        )
        .unwrap();
        let context = new_solver_encoding_context(&task, &artifacts, workers).unwrap();
        let catalog = ClauseCatalog::new(&task, context.clone(), &artifacts).unwrap();
        let register = |identity: &str, source_id: &str| {
            let source = SolverBodySource::QuantifierFree(
                QfSolverSource::new(&task, source_id, [], []).unwrap(),
            );
            catalog
                .register_proposed_clause(
                    ClauseFormula::from_trusted_lean_source(identity, source).unwrap(),
                )
                .unwrap()
        };
        let target = register("retry-baseline.target", "retry-baseline.target");
        let support = register("retry-baseline.support", "retry-baseline.support");
        let full = CandidateSnapshot::root(Arc::new(ClauseSet::from([target, support])));
        let reduced = CandidateSnapshot::root(Arc::new(ClauseSet::from([target])));
        let base = Duration::from_secs(3);
        let increments = [
            Duration::from_secs(2),
            Duration::from_secs(4),
            Duration::from_secs(8),
        ];

        let MaintenanceRetryDecision::Ready(first) = catalog
            .select_maintenance_retry(target, Arc::clone(&full), base, &increments)
            .unwrap()
        else {
            panic!("the first maintenance attempt must be ready")
        };
        assert_eq!(first.initial_allowance(), Duration::from_secs(3));
        assert_eq!(first.allowance(), Duration::from_secs(3));
        catalog.record_maintenance_timeout(&first, None).unwrap();
        assert_eq!(
            catalog.record(target).unwrap().retry_initial_allowance(),
            Some(Duration::from_secs(3)),
        );

        let MaintenanceRetryDecision::Ready(same_full) = catalog
            .select_maintenance_retry(target, Arc::clone(&full), base, &increments)
            .unwrap()
        else {
            panic!("the exact-query retry must be ready")
        };
        assert_eq!(same_full.initial_allowance(), Duration::from_secs(3));
        assert_eq!(same_full.allowance(), Duration::from_secs(5));
        catalog
            .record_maintenance_timeout(&same_full, None)
            .unwrap();

        let MaintenanceRetryDecision::Ready(first_reduced) = catalog
            .select_maintenance_retry(target, Arc::clone(&reduced), base, &increments)
            .unwrap()
        else {
            panic!("the subset-query attempt must be ready")
        };
        assert_eq!(first_reduced.initial_allowance(), Duration::from_secs(9));
        assert_eq!(first_reduced.allowance(), Duration::from_secs(9));
        catalog
            .record_maintenance_timeout(&first_reduced, None)
            .unwrap();
        let reduced_record = catalog.record(target).unwrap();
        assert_eq!(
            reduced_record.retry_initial_allowance(),
            Some(Duration::from_secs(9)),
        );
        assert_eq!(reduced_record.retry_candidate_len(), Some(1));

        let MaintenanceRetryDecision::Ready(same_reduced) = catalog
            .select_maintenance_retry(target, reduced, base, &increments)
            .unwrap()
        else {
            panic!("the reduced exact-query retry must be ready")
        };
        assert_eq!(same_reduced.initial_allowance(), Duration::from_secs(9));
        assert_eq!(same_reduced.allowance(), Duration::from_secs(17));

        context.shutdown().await.unwrap();
        drop(catalog);
        drop(context);
        drop(artifacts);
        owner.settle().unwrap();
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn literal_subset_key_uses_stronger_source_to_weaker_target_orientation() {
        let literal_a = serde_json::json!(["eq", ["rel", "r"], ["rel", "s"]]);
        let literal_b = serde_json::json!(["not", ["subset", ["rel", "r"], ["rel", "s"]]]);
        let source_identity = serde_json::to_string(&literal_a).unwrap();
        let target_identity =
            serde_json::to_string(&serde_json::json!(["or", literal_a, literal_b])).unwrap();
        let source = CanonicalLiteralSet::from_reference_identity(&source_identity)
            .expect("one structural literal");
        let target = CanonicalLiteralSet::from_reference_identity(&target_identity)
            .expect("two structural literals");
        assert_eq!(source.literals().len(), 1);
        assert_eq!(target.literals().len(), 2);

        let source_is_subset = source
            .literals()
            .iter()
            .all(|literal| target.literals().binary_search(literal).is_ok());
        let target_is_subset = target
            .literals()
            .iter()
            .all(|literal| source.literals().binary_search(literal).is_ok());
        assert!(
            source_is_subset,
            "the stronger one-literal clause must cover its two-literal extension",
        );
        assert!(
            !target_is_subset,
            "the weaker extension must not cover its stronger source",
        );
    }

    #[test]
    fn latest_maintenance_result_is_fixed_size_hot_state() {
        assert!(
            !std::mem::needs_drop::<LatestMaintenanceResult>(),
            "the hot latest-result slot must not own a Candidate or other heap allocation"
        );
        assert!(
            std::mem::size_of::<LatestMaintenanceResult>() <= 64,
            "the hot latest-result slot must remain a compact identity and evidence record"
        );
    }

    #[test]
    fn same_or_weaker_support_advances_cumulatively_then_exhausts() {
        let a = ClauseId::test(0);
        let b = ClauseId::test(1);
        let prior = CandidateSnapshot::root(Arc::new(ClauseSet::from([a, b])));
        let same = Arc::clone(&prior);
        let weaker = CandidateSnapshot::from_sorted(vec![a]);
        let n = Duration::from_secs(7);
        let increments = [n, n];

        assert_eq!(
            maintenance_retry_allowance(Some(&prior), 0, false, n, &increments, &same),
            Ok(Some(Duration::from_secs(14)))
        );
        assert_eq!(
            maintenance_retry_allowance(Some(&prior), 1, false, n, &increments, &weaker),
            Ok(Some(Duration::from_secs(21)))
        );
        assert_eq!(
            maintenance_retry_allowance(Some(&prior), 2, true, n, &increments, &weaker),
            Ok(None)
        );
    }

    #[test]
    fn exact_candidate_reuses_fmb_frontier_but_shrinking_candidate_resets_it() {
        let a = ClauseId::test(0);
        let b = ClauseId::test(1);
        let prior = CandidateSnapshot::root(Arc::new(ClauseSet::from([a, b])));
        let frontier = crate::vampire::FmbSize::new(9).unwrap();

        let same = prior.clone();
        assert!(same.same_members(&prior));
        assert_eq!(
            Some(frontier).filter(|_| same.same_members(&prior)),
            Some(frontier)
        );

        let weaker = CandidateSnapshot::from_sorted(vec![a]);
        assert!(!weaker.same_members(&prior));
        assert_eq!(Some(frontier).filter(|_| weaker.same_members(&prior)), None);
    }

    #[test]
    fn no_previous_timeout_uses_initial_allowance_even_without_retries() {
        assert_eq!(
            maintenance_retry_allowance(
                None,
                0,
                false,
                Duration::from_secs(3),
                &[],
                &CandidateSnapshot::root(Arc::new(ClauseSet::new())),
            ),
            Ok(Some(Duration::from_secs(3)))
        );
    }

    #[test]
    fn candidate_snapshots_are_flat_sorted_and_bounded() {
        let width = 256_u64;
        let root = CandidateSnapshot::root(Arc::new(
            (0..width).map(ClauseId::test).collect::<ClauseSet>(),
        ));
        let current = CandidateSnapshot::from_sorted(vec![ClauseId::test(width - 1)]);
        assert!(current.is_subset_of(&root));
        assert_eq!(current.len(), 1);
        assert!(current.contains(ClauseId::test(width - 1)));
        assert!(!current.contains(ClauseId::test(0)));
    }
}
