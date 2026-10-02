//! Immutable maintenance preparation for caller-neutral Houdini.

use std::cmp::Reverse;
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::mem;
use std::sync::Arc;
use std::time::{Duration, Instant};

use crate::failure::{FailureKind, FailureOrigin, FailureReport, FailureScope};
use crate::runtime::{AdmissionError, CancellationToken, CpuJobError};
use crate::task::{SynthesisTask, TaskIdentity};

use super::catalog::{
    CandidateSnapshot, CanonicalLiteralSet, ClauseCatalog, ClauseId, ClauseSet, InitCoverage,
    MaintenancePublicationError, MaintenanceReadinessSnapshot, MaintenanceSnapshotError,
};
use super::initialization::HoudiniState;

// ------------------------------------------------------------
// Caller-Supplied Semantic Relations
// ------------------------------------------------------------

/// Caller-asserted facts `Step(base_core ∪ {source}, target)`.
///
/// The runtime validates scope and membership. It deliberately does not ask a
/// solver to establish the caller-owned semantic assertion.
#[derive(Clone, Debug)]
pub struct MaintSupport {
    catalog_identity: u64,
    base_core: Arc<ClauseSet>,
    edges: Arc<HashSet<(ClauseId, ClauseId)>>,
}

impl MaintSupport {
    pub fn new(catalog: &ClauseCatalog, base_core: ClauseSet) -> Result<Self, FailureReport> {
        validate_registered_set(catalog, &base_core)?;
        Ok(Self {
            catalog_identity: catalog.identity(),
            base_core: Arc::new(base_core),
            edges: Arc::new(HashSet::new()),
        })
    }

    pub fn base_core(&self) -> &ClauseSet {
        &self.base_core
    }

    pub fn edge_count(&self) -> usize {
        self.edges.len()
    }

    pub fn contains(&self, source: ClauseId, target: ClauseId) -> bool {
        self.edges.contains(&(source, target))
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
        Ok(Arc::make_mut(&mut self.edges).insert((source, target)))
    }

    pub fn rebase(
        &mut self,
        catalog: &ClauseCatalog,
        stronger_core: ClauseSet,
    ) -> Result<(), FailureReport> {
        self.validate_catalog(catalog)?;
        validate_registered_set(catalog, &stronger_core)?;
        if !self.base_core.is_subset(&stronger_core) {
            return Err(maintenance_invariant(
                "MaintSupport can only be rebased to a stronger Core",
            ));
        }
        self.base_core = Arc::new(stronger_core);
        Ok(())
    }

    fn validate_catalog(&self, catalog: &ClauseCatalog) -> Result<(), FailureReport> {
        if self.catalog_identity != catalog.identity() {
            return Err(maintenance_scope_failure(
                "MaintSupport belongs to another ClauseCatalog",
            ));
        }
        Ok(())
    }
}

/// Caller-asserted maintenance-result transfer facts.
///
/// An edge `(a, b)` means that for every `K` containing `base_core`,
/// `Step(K, a)` implies `Step(K, b)`.
#[derive(Clone, Debug)]
pub struct MaintCoverage {
    catalog_identity: u64,
    base_core: Arc<ClauseSet>,
    edges: Arc<HashSet<(ClauseId, ClauseId)>>,
}

impl MaintCoverage {
    pub fn new(catalog: &ClauseCatalog, base_core: ClauseSet) -> Result<Self, FailureReport> {
        validate_registered_set(catalog, &base_core)?;
        Ok(Self {
            catalog_identity: catalog.identity(),
            base_core: Arc::new(base_core),
            edges: Arc::new(HashSet::new()),
        })
    }

    pub fn base_core(&self) -> &ClauseSet {
        &self.base_core
    }

    pub fn edge_count(&self) -> usize {
        self.edges.len()
    }

    pub fn contains(&self, source: ClauseId, target: ClauseId) -> bool {
        self.edges.contains(&(source, target))
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
        Ok(Arc::make_mut(&mut self.edges).insert((source, target)))
    }

    pub fn rebase(
        &mut self,
        catalog: &ClauseCatalog,
        stronger_core: ClauseSet,
    ) -> Result<(), FailureReport> {
        self.validate_catalog(catalog)?;
        validate_registered_set(catalog, &stronger_core)?;
        if !self.base_core.is_subset(&stronger_core) {
            return Err(maintenance_invariant(
                "MaintCoverage can only be rebased to a stronger Core",
            ));
        }
        self.base_core = Arc::new(stronger_core);
        Ok(())
    }

    fn from_edges(
        catalog_identity: u64,
        base_core: Arc<ClauseSet>,
        edges: HashSet<(ClauseId, ClauseId)>,
    ) -> Self {
        Self {
            catalog_identity,
            base_core,
            edges: Arc::new(edges),
        }
    }

    fn validate_catalog(&self, catalog: &ClauseCatalog) -> Result<(), FailureReport> {
        if self.catalog_identity != catalog.identity() {
            return Err(maintenance_scope_failure(
                "MaintCoverage belongs to another ClauseCatalog",
            ));
        }
        Ok(())
    }
}

// ------------------------------------------------------------
// Preparation Policy And Track Hints
// ------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CoverageMode {
    /// The caller guarantees that the rebased/lifted union is already closed.
    UseProducerClosed,
    /// Compute exact positive-path closure as the correctness fallback.
    ComputeClosure,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CoverageLookup {
    IncomingEdges,
    LiteralSubsetThenIncoming,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TrackLayout {
    SingleTrack,
    OrdinaryAndWTracks,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum MaintenanceTrackKind {
    Default,
    Ordinary,
    WLayer,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MaintenanceTrackHint {
    kind: MaintenanceTrackKind,
    descending_order_key: Option<i64>,
}

impl MaintenanceTrackHint {
    pub fn new(kind: MaintenanceTrackKind, descending_order_key: Option<i64>) -> Self {
        Self {
            kind,
            descending_order_key,
        }
    }

    pub fn kind(self) -> MaintenanceTrackKind {
        self.kind
    }

    pub fn descending_order_key(self) -> Option<i64> {
        self.descending_order_key
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MaintenancePolicy {
    coverage_mode: CoverageMode,
    track_layout: TrackLayout,
    coverage_lookup: CoverageLookup,
    ordinary_track_count: usize,
    log_maintenance_history: bool,
    fail_on_history_log_error: bool,
}

impl MaintenancePolicy {
    pub fn new(
        coverage_mode: CoverageMode,
        track_layout: TrackLayout,
        coverage_lookup: CoverageLookup,
    ) -> Self {
        Self {
            coverage_mode,
            track_layout,
            coverage_lookup,
            ordinary_track_count: 1,
            log_maintenance_history: false,
            fail_on_history_log_error: false,
        }
    }

    /// Split the ordinary maintenance targets round-robin across
    /// this many concurrent tracks. The W track stays separate.
    pub fn with_ordinary_track_count(mut self, count: usize) -> Result<Self, &'static str> {
        if count == 0 {
            return Err("ordinary track count must be positive");
        }
        self.ordinary_track_count = count;
        Ok(self)
    }

    pub fn single_track() -> Self {
        Self::new(
            CoverageMode::UseProducerClosed,
            TrackLayout::SingleTrack,
            CoverageLookup::IncomingEdges,
        )
    }

    pub fn with_history(mut self, enabled: bool, strict: bool) -> Self {
        self.log_maintenance_history = enabled;
        self.fail_on_history_log_error = enabled && strict;
        self
    }

    pub fn coverage_mode(&self) -> CoverageMode {
        self.coverage_mode
    }

    pub fn track_layout(&self) -> TrackLayout {
        self.track_layout
    }

    pub fn coverage_lookup(&self) -> CoverageLookup {
        self.coverage_lookup
    }

    pub fn ordinary_track_count(&self) -> usize {
        self.ordinary_track_count
    }

    pub fn log_maintenance_history(&self) -> bool {
        self.log_maintenance_history
    }

    pub fn fail_on_history_log_error(&self) -> bool {
        self.fail_on_history_log_error
    }
}

impl Default for MaintenancePolicy {
    fn default() -> Self {
        Self::single_track()
    }
}

// ------------------------------------------------------------
// Immutable Maintenance Plan
// ------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MaintenanceTrack {
    kind: MaintenanceTrackKind,
    targets: Arc<[ClauseId]>,
}

impl MaintenanceTrack {
    pub fn kind(&self) -> MaintenanceTrackKind {
        self.kind
    }

    pub fn targets(&self) -> &[ClauseId] {
        &self.targets
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MaintenanceSchedule {
    tracks: Arc<[MaintenanceTrack]>,
}

impl MaintenanceSchedule {
    pub fn tracks(&self) -> &[MaintenanceTrack] {
        &self.tracks
    }
}

/// Measurements retained only when the exact closure fallback is selected.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoverageClosureMetrics {
    represented_vertices: usize,
    input_edge_count: usize,
    retained_edge_count: usize,
    estimated_retained_bytes: usize,
    elapsed: Duration,
}

impl CoverageClosureMetrics {
    pub fn represented_vertices(&self) -> usize {
        self.represented_vertices
    }

    pub fn input_edge_count(&self) -> usize {
        self.input_edge_count
    }

    pub fn retained_edge_count(&self) -> usize {
        self.retained_edge_count
    }

    pub fn estimated_retained_bytes(&self) -> usize {
        self.estimated_retained_bytes
    }

    pub fn elapsed(&self) -> Duration {
        self.elapsed
    }
}

type RelationIndex = HashMap<ClauseId, Arc<[ClauseId]>>;

/// Exact index of canonical reference-clause literal sets.
///
/// Trie paths are sorted literal sets. A path ending above the target path is
/// exactly a subset witness; no semantic query or approximate hash test is
/// involved.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct LiteralSubsetIndex {
    keys: HashMap<ClauseId, CanonicalLiteralSet>,
    root: LiteralSubsetTrieNode,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct LiteralSubsetTrieNode {
    clauses: Vec<ClauseId>,
    children: BTreeMap<Arc<str>, LiteralSubsetTrieNode>,
}

impl LiteralSubsetIndex {
    fn build(
        catalog: &ClauseCatalog,
        candidate: &ClauseSet,
        cancellation: Option<&CancellationToken>,
    ) -> Result<Self, PlanBuildError> {
        let mut index = Self::default();
        let mut clauses = candidate.iter().copied().collect::<Vec<_>>();
        clauses.sort_unstable();
        for (position, clause) in clauses.into_iter().enumerate() {
            check_cancelled_periodically(cancellation, position)?;
            let record = catalog.record(clause)?;
            let Some(key) = record.formula().literal_set().cloned() else {
                continue;
            };
            index.root.insert(key.literals(), clause);
            index.keys.insert(clause, key);
        }
        Ok(index)
    }

    fn find_live_subset(
        &self,
        target: ClauseId,
        core: &ClauseSet,
        known_live: &ClauseSet,
    ) -> Option<ClauseId> {
        self.find_subset_by(
            target,
            |source| core.contains(&source) || known_live.contains(&source),
            None,
        )
        .expect("a literal-subset lookup without cancellation cannot fail")
    }

    fn find_subset_by(
        &self,
        target: ClauseId,
        mut predicate: impl FnMut(ClauseId) -> bool,
        cancellation: Option<&CancellationToken>,
    ) -> Result<Option<ClauseId>, CpuJobError> {
        let Some(target_literals) = self.keys.get(&target).map(CanonicalLiteralSet::literals)
        else {
            return Ok(None);
        };
        let mut visited = 0_usize;
        self.root.find_subset_by(
            target_literals,
            0,
            &mut predicate,
            cancellation,
            &mut visited,
        )
    }
}

impl LiteralSubsetTrieNode {
    fn insert(&mut self, literals: &[Arc<str>], clause: ClauseId) {
        let mut node = self;
        for literal in literals {
            node = node.children.entry(Arc::clone(literal)).or_default();
        }
        node.clauses.push(clause);
    }

    fn find_subset_by(
        &self,
        target_literals: &[Arc<str>],
        first_target_position: usize,
        predicate: &mut impl FnMut(ClauseId) -> bool,
        cancellation: Option<&CancellationToken>,
        visited: &mut usize,
    ) -> Result<Option<ClauseId>, CpuJobError> {
        *visited = visited.saturating_add(1);
        if *visited % 256 == 0 && cancellation.is_some_and(CancellationToken::is_cancelled) {
            return Err(CpuJobError::Cancelled);
        }
        if let Some(source) = self
            .clauses
            .iter()
            .copied()
            .find(|source| predicate(*source))
        {
            return Ok(Some(source));
        }
        for position in first_target_position..target_literals.len() {
            let Some(child) = self.children.get(&target_literals[position]) else {
                continue;
            };
            if let Some(source) = child.find_subset_by(
                target_literals,
                position + 1,
                predicate,
                cancellation,
                visited,
            )? {
                return Ok(Some(source));
            }
        }
        Ok(None)
    }
}

/// Immutable dispatch object selected before a maintenance plan is published.
/// Phase 3C supplies the block-local `knownLive` view used by each lookup.
#[derive(Clone, Debug, PartialEq, Eq)]
enum LiveCoverLookup {
    IncomingEdges,
    LiteralSubsetThenIncoming(LiteralSubsetIndex),
}

impl LiveCoverLookup {
    fn bind(
        policy: &MaintenancePolicy,
        catalog: &ClauseCatalog,
        candidate: &ClauseSet,
        cancellation: Option<&CancellationToken>,
    ) -> Result<Self, PlanBuildError> {
        match policy.coverage_lookup {
            CoverageLookup::IncomingEdges => Ok(Self::IncomingEdges),
            CoverageLookup::LiteralSubsetThenIncoming => Ok(Self::LiteralSubsetThenIncoming(
                LiteralSubsetIndex::build(catalog, candidate, cancellation)?,
            )),
        }
    }

    fn find_literal_subset(
        &self,
        target: ClauseId,
        core: &ClauseSet,
        known_live: &ClauseSet,
    ) -> Option<ClauseId> {
        match self {
            Self::IncomingEdges => None,
            Self::LiteralSubsetThenIncoming(index) => {
                index.find_live_subset(target, core, known_live)
            }
        }
    }

    fn find_literal_subset_by(
        &self,
        target: ClauseId,
        predicate: impl FnMut(ClauseId) -> bool,
        cancellation: &CancellationToken,
    ) -> Result<Option<ClauseId>, CpuJobError> {
        match self {
            Self::IncomingEdges => Ok(None),
            Self::LiteralSubsetThenIncoming(index) => {
                index.find_subset_by(target, predicate, Some(cancellation))
            }
        }
    }

    fn kind(&self) -> CoverageLookup {
        match self {
            Self::IncomingEdges => CoverageLookup::IncomingEdges,
            Self::LiteralSubsetThenIncoming(_) => CoverageLookup::LiteralSubsetThenIncoming,
        }
    }
}

/// One lock-free snapshot for a Core and an initial Active universe.
#[derive(Clone, Debug)]
pub struct MaintenancePlan {
    task: TaskIdentity,
    catalog_identity: u64,
    encoding_context_id: Arc<str>,
    proposal_generation: u64,
    catalog_generation: u64,
    core: Arc<ClauseSet>,
    init_candidates: Arc<ClauseSet>,
    initial_active: Arc<ClauseSet>,
    policy: MaintenancePolicy,
    supported_by: RelationIndex,
    supported_targets_by: RelationIndex,
    covered_by: RelationIndex,
    live_cover_lookup: LiveCoverLookup,
    covered_count: HashMap<ClauseId, usize>,
    schedule: MaintenanceSchedule,
    closure_metrics: Option<CoverageClosureMetrics>,
}

impl MaintenancePlan {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn matches_runtime_capture(
        &self,
        task: &TaskIdentity,
        catalog_identity: u64,
        encoding_context_id: &str,
        proposal_generation: u64,
        core: &Arc<ClauseSet>,
        init_candidates: &Arc<ClauseSet>,
        policy: &MaintenancePolicy,
    ) -> bool {
        &self.task == task
            && self.catalog_identity == catalog_identity
            && self.encoding_context_id.as_ref() == encoding_context_id
            && self.proposal_generation == proposal_generation
            && Arc::ptr_eq(&self.core, core)
            && Arc::ptr_eq(&self.init_candidates, init_candidates)
            && &self.policy == policy
    }

    #[cfg(test)]
    pub(super) fn for_core_expansion_test(task: &SynthesisTask, state: &HoudiniState) -> Arc<Self> {
        let mut targets = state.active.iter().copied().collect::<Vec<_>>();
        targets.sort_unstable();
        Arc::new(Self {
            task: task.identity().clone(),
            catalog_identity: state.catalog.identity(),
            encoding_context_id: Arc::from(state.catalog.encoding_context().context_id()),
            proposal_generation: state.proposal_generation,
            catalog_generation: 0,
            core: Arc::clone(&state.core),
            init_candidates: Arc::clone(&state.init_candidates),
            initial_active: Arc::clone(&state.active),
            policy: state.maintenance_policy.clone(),
            supported_by: HashMap::new(),
            supported_targets_by: HashMap::new(),
            covered_by: HashMap::new(),
            live_cover_lookup: LiveCoverLookup::IncomingEdges,
            covered_count: HashMap::new(),
            schedule: MaintenanceSchedule {
                tracks: vec![MaintenanceTrack {
                    kind: MaintenanceTrackKind::Default,
                    targets: targets.into(),
                }]
                .into(),
            },
            closure_metrics: None,
        })
    }

    pub fn core(&self) -> &ClauseSet {
        &self.core
    }

    pub fn init_candidates(&self) -> &ClauseSet {
        &self.init_candidates
    }

    pub fn initial_active(&self) -> &ClauseSet {
        &self.initial_active
    }

    pub fn policy(&self) -> &MaintenancePolicy {
        &self.policy
    }

    pub fn supported_by(&self, target: ClauseId) -> &[ClauseId] {
        self.supported_by
            .get(&target)
            .map(AsRef::as_ref)
            .unwrap_or(&[])
    }

    pub fn supported_targets_by(&self, source: ClauseId) -> &[ClauseId] {
        self.supported_targets_by
            .get(&source)
            .map(AsRef::as_ref)
            .unwrap_or(&[])
    }

    pub fn covered_by(&self, target: ClauseId) -> &[ClauseId] {
        self.covered_by
            .get(&target)
            .map(AsRef::as_ref)
            .unwrap_or(&[])
    }

    pub fn coverage_lookup(&self) -> CoverageLookup {
        self.live_cover_lookup.kind()
    }

    pub(super) fn find_literal_subset_cover(
        &self,
        known_live: &ClauseSet,
        target: ClauseId,
    ) -> Option<ClauseId> {
        self.live_cover_lookup
            .find_literal_subset(target, &self.core, known_live)
    }

    pub(super) fn find_literal_subset_cover_by(
        &self,
        target: ClauseId,
        predicate: impl FnMut(ClauseId) -> bool,
        cancellation: &CancellationToken,
    ) -> Result<Option<ClauseId>, CpuJobError> {
        self.live_cover_lookup
            .find_literal_subset_by(target, predicate, cancellation)
    }

    pub fn covered_count(&self, source: ClauseId) -> usize {
        self.covered_count.get(&source).copied().unwrap_or(0)
    }

    pub fn schedule(&self) -> &MaintenanceSchedule {
        &self.schedule
    }

    pub fn closure_metrics(&self) -> Option<&CoverageClosureMetrics> {
        self.closure_metrics.as_ref()
    }

    /// Active may shrink within this immutable universe. All other bound
    /// identities must remain exact.
    pub fn is_current_for(&self, task: &SynthesisTask, state: &HoudiniState) -> bool {
        state.maintenance_failure.is_none()
            && state
                .maintenance_plan
                .as_ref()
                .is_some_and(|current| std::ptr::eq(current.as_ref(), self))
            && self.matches_state_inputs(task, state)
            && state.active.is_subset(&self.initial_active)
    }

    fn matches_state_inputs(&self, task: &SynthesisTask, state: &HoudiniState) -> bool {
        &self.task == task.identity()
            && self.catalog_identity == state.catalog.identity()
            && self.encoding_context_id.as_ref() == state.catalog.encoding_context().context_id()
            && self.proposal_generation == state.proposal_generation
            && Arc::ptr_eq(&self.core, &state.core)
            && Arc::ptr_eq(&self.init_candidates, &state.init_candidates)
            && self.policy == state.maintenance_policy
    }

    fn matches_publication_inputs(
        &self,
        task: &SynthesisTask,
        state: &HoudiniState,
        readiness: &MaintenanceReadinessSnapshot,
    ) -> bool {
        &self.task == task.identity()
            && self.catalog_identity == state.catalog.identity()
            && self.encoding_context_id.as_ref() == state.catalog.encoding_context().context_id()
            && self.proposal_generation == state.proposal_generation
            && self.catalog_generation == readiness.generation()
            && Arc::ptr_eq(&self.core, &state.core)
            && Arc::ptr_eq(&self.init_candidates, &state.init_candidates)
            && Arc::ptr_eq(&self.initial_active, &readiness.active_snapshot())
            && self.policy == state.maintenance_policy
    }
}

// ------------------------------------------------------------
// Coverage Closure And Projection
// ------------------------------------------------------------

/// Rebase, lift, close, and only then project to eligible endpoints.
pub fn close_maint_coverage(
    catalog: &ClauseCatalog,
    core: &ClauseSet,
    eligible: &ClauseSet,
    init_coverage: &InitCoverage,
    coverage: &MaintCoverage,
) -> Result<(MaintCoverage, CoverageClosureMetrics), FailureReport> {
    close_maint_coverage_with_cancellation(catalog, core, eligible, init_coverage, coverage, None)
        .map_err(|error| match error {
            PlanBuildError::Failure(report) => report,
            PlanBuildError::Cancelled => {
                maintenance_invariant("closure was cancelled without a cancellation token")
            }
        })
}

fn close_maint_coverage_with_cancellation(
    catalog: &ClauseCatalog,
    core: &ClauseSet,
    eligible: &ClauseSet,
    init_coverage: &InitCoverage,
    coverage: &MaintCoverage,
    cancellation: Option<&CancellationToken>,
) -> Result<(MaintCoverage, CoverageClosureMetrics), PlanBuildError> {
    close_maint_coverage_with_base(
        catalog,
        Arc::new(core.clone()),
        eligible,
        init_coverage,
        coverage,
        cancellation,
    )
}

fn close_maint_coverage_with_base(
    catalog: &ClauseCatalog,
    core: Arc<ClauseSet>,
    eligible: &ClauseSet,
    init_coverage: &InitCoverage,
    coverage: &MaintCoverage,
    cancellation: Option<&CancellationToken>,
) -> Result<(MaintCoverage, CoverageClosureMetrics), PlanBuildError> {
    validate_coverage_inputs(
        catalog,
        &core,
        eligible,
        init_coverage,
        coverage,
        cancellation,
    )?;
    let started = Instant::now();
    let mut direct = HashSet::with_capacity(
        coverage
            .edges
            .len()
            .saturating_add(init_coverage.edge_count()),
    );
    for (position, edge) in coverage.edges.iter().copied().enumerate() {
        check_cancelled_periodically(cancellation, position)?;
        direct.insert(edge);
    }
    let offset = coverage.edges.len();
    for (position, edge) in init_coverage.edges().enumerate() {
        check_cancelled_periodically(cancellation, offset.saturating_add(position))?;
        direct.insert(edge);
    }
    let input_edge_count = direct.len();
    let mut adjacency = HashMap::<ClauseId, Vec<ClauseId>>::new();
    let mut vertices = ClauseSet::new();
    for (position, (source, target)) in direct.iter().enumerate() {
        check_cancelled_periodically(cancellation, position)?;
        vertices.insert(*source);
        vertices.insert(*target);
        adjacency.entry(*source).or_default().push(*target);
    }
    for (position, targets) in adjacency.values_mut().enumerate() {
        check_cancelled_periodically(cancellation, position)?;
        targets.sort_unstable();
        if cancellation.is_some_and(CancellationToken::is_cancelled) {
            return Err(PlanBuildError::Cancelled);
        }
        targets.dedup();
    }

    let mut sources = Vec::with_capacity(eligible.len());
    for (position, source) in eligible.iter().copied().enumerate() {
        check_cancelled_periodically(cancellation, position)?;
        sources.push(source);
    }
    sources.sort_unstable();
    if cancellation.is_some_and(CancellationToken::is_cancelled) {
        return Err(PlanBuildError::Cancelled);
    }
    let mut closed_edges = HashSet::new();
    for source in sources {
        if cancellation.is_some_and(CancellationToken::is_cancelled) {
            return Err(PlanBuildError::Cancelled);
        }
        let mut reached = ClauseSet::new();
        let mut queue = VecDeque::new();
        if let Some(initial) = adjacency.get(&source) {
            for (position, target) in initial.iter().copied().enumerate() {
                check_cancelled_periodically(cancellation, position)?;
                queue.push_back(target);
            }
        }
        while let Some(target) = queue.pop_front() {
            if cancellation.is_some_and(CancellationToken::is_cancelled) {
                return Err(PlanBuildError::Cancelled);
            }
            if !reached.insert(target) {
                continue;
            }
            if let Some(next) = adjacency.get(&target) {
                for (position, next_target) in next.iter().copied().enumerate() {
                    check_cancelled_periodically(cancellation, position)?;
                    queue.push_back(next_target);
                }
            }
        }
        for (position, target) in reached.into_iter().enumerate() {
            check_cancelled_periodically(cancellation, position)?;
            if eligible.contains(&target) {
                closed_edges.insert((source, target));
            }
        }
    }
    let estimated_retained_bytes = vertices
        .len()
        .saturating_mul(mem::size_of::<ClauseId>())
        .saturating_add(
            closed_edges
                .len()
                .saturating_mul(mem::size_of::<(ClauseId, ClauseId)>()),
        );
    let metrics = CoverageClosureMetrics {
        represented_vertices: vertices.len(),
        input_edge_count,
        retained_edge_count: closed_edges.len(),
        estimated_retained_bytes,
        elapsed: started.elapsed(),
    };
    Ok((
        MaintCoverage::from_edges(catalog.identity(), core, closed_edges),
        metrics,
    ))
}

/// Project a caller-guaranteed closed union without another closure traversal.
pub fn project_closed_maint_coverage(
    catalog: &ClauseCatalog,
    core: &ClauseSet,
    eligible: &ClauseSet,
    init_coverage: &InitCoverage,
    coverage: &MaintCoverage,
) -> Result<MaintCoverage, FailureReport> {
    project_closed_maint_coverage_with_cancellation(
        catalog,
        core,
        eligible,
        init_coverage,
        coverage,
        None,
    )
    .map_err(PlanBuildError::into_failure)
}

fn project_closed_maint_coverage_with_cancellation(
    catalog: &ClauseCatalog,
    core: &ClauseSet,
    eligible: &ClauseSet,
    init_coverage: &InitCoverage,
    coverage: &MaintCoverage,
    cancellation: Option<&CancellationToken>,
) -> Result<MaintCoverage, PlanBuildError> {
    project_closed_maint_coverage_with_base(
        catalog,
        Arc::new(core.clone()),
        eligible,
        init_coverage,
        coverage,
        cancellation,
    )
}

fn project_closed_maint_coverage_with_base(
    catalog: &ClauseCatalog,
    core: Arc<ClauseSet>,
    eligible: &ClauseSet,
    init_coverage: &InitCoverage,
    coverage: &MaintCoverage,
    cancellation: Option<&CancellationToken>,
) -> Result<MaintCoverage, PlanBuildError> {
    validate_coverage_inputs(
        catalog,
        &core,
        eligible,
        init_coverage,
        coverage,
        cancellation,
    )?;
    let mut edges = HashSet::new();
    for (index, edge) in coverage
        .edges
        .iter()
        .copied()
        .chain(init_coverage.edges())
        .enumerate()
    {
        check_cancelled_periodically(cancellation, index)?;
        if eligible.contains(&edge.0) && eligible.contains(&edge.1) {
            edges.insert(edge);
        }
    }
    Ok(MaintCoverage::from_edges(catalog.identity(), core, edges))
}

fn validate_coverage_inputs(
    catalog: &ClauseCatalog,
    core: &ClauseSet,
    eligible: &ClauseSet,
    init_coverage: &InitCoverage,
    coverage: &MaintCoverage,
    cancellation: Option<&CancellationToken>,
) -> Result<(), PlanBuildError> {
    coverage.validate_catalog(catalog)?;
    init_coverage.validate_closed(catalog)?;
    validate_registered_set_with_cancellation(catalog, core, cancellation)?;
    validate_registered_set_with_cancellation(catalog, eligible, cancellation)?;
    if !is_subset_with_cancellation(core, eligible, cancellation)?
        || !is_subset_with_cancellation(&coverage.base_core, core, cancellation)?
    {
        return Err(maintenance_invariant(
            "maintenance coverage Core/eligible snapshots are inconsistent",
        )
        .into());
    }
    Ok(())
}

// ------------------------------------------------------------
// Relation Indexes And Deterministic Tracks
// ------------------------------------------------------------

fn index_maint_support(
    catalog: &ClauseCatalog,
    core: &ClauseSet,
    candidate: &ClauseSet,
    active: &ClauseSet,
    support: &MaintSupport,
    cancellation: Option<&CancellationToken>,
) -> Result<(RelationIndex, RelationIndex, HashMap<ClauseId, usize>), PlanBuildError> {
    support.validate_catalog(catalog)?;
    if !is_subset_with_cancellation(&support.base_core, core, cancellation)?
        || !is_exact_union_with_cancellation(candidate, core, active, cancellation)?
    {
        return Err(maintenance_invariant(
            "MaintSupport projection received inconsistent Core/Candidate/Active",
        )
        .into());
    }
    let mut incoming = HashMap::with_capacity(active.len());
    let mut outgoing = HashMap::with_capacity(active.len());
    for (position, id) in active.iter().copied().enumerate() {
        check_cancelled_periodically(cancellation, position)?;
        incoming.insert(id, Vec::new());
        outgoing.insert(id, Vec::new());
    }
    for (index, (source, target)) in support.edges.iter().enumerate() {
        check_cancelled_periodically(cancellation, index)?;
        if candidate.contains(source) && active.contains(target) {
            incoming
                .get_mut(target)
                .expect("every Active target has an incoming bucket")
                .push(*source);
            if active.contains(source) {
                outgoing
                    .get_mut(source)
                    .expect("every Active source has an outgoing bucket")
                    .push(*target);
            }
        }
    }
    let incoming = freeze_index(incoming, cancellation)?;
    let outgoing = freeze_index(outgoing, cancellation)?;
    let mut counts = HashMap::with_capacity(active.len());
    for (position, target) in active.iter().copied().enumerate() {
        check_cancelled_periodically(cancellation, position)?;
        counts.insert(target, incoming[&target].len());
    }
    Ok((incoming, outgoing, counts))
}

fn index_maint_coverage(
    active: &ClauseSet,
    coverage: &MaintCoverage,
    cancellation: Option<&CancellationToken>,
) -> Result<(RelationIndex, HashMap<ClauseId, usize>), PlanBuildError> {
    let mut incoming = HashMap::with_capacity(active.len());
    let mut outdegree = HashMap::with_capacity(active.len());
    for (position, id) in active.iter().copied().enumerate() {
        check_cancelled_periodically(cancellation, position)?;
        incoming.insert(id, Vec::new());
        outdegree.insert(id, 0);
    }
    for (index, (source, target)) in coverage.edges.iter().enumerate() {
        check_cancelled_periodically(cancellation, index)?;
        if source == target || !active.contains(target) {
            continue;
        }
        incoming
            .get_mut(target)
            .expect("every Active target has an incoming bucket")
            .push(*source);
        if let Some(count) = outdegree.get_mut(source) {
            *count += 1;
        }
    }
    Ok((freeze_index(incoming, cancellation)?, outdegree))
}

fn build_maintenance_schedule(
    hints: &HashMap<ClauseId, MaintenanceTrackHint>,
    active: &ClauseSet,
    covered_count: &HashMap<ClauseId, usize>,
    policy: &MaintenancePolicy,
    cancellation: Option<&CancellationToken>,
) -> Result<MaintenanceSchedule, PlanBuildError> {
    if cancellation.is_some_and(CancellationToken::is_cancelled) {
        return Err(PlanBuildError::Cancelled);
    }
    let source_first = |left: &ClauseId, right: &ClauseId| {
        (
            Reverse(covered_count.get(left).copied().unwrap_or(0)),
            *left,
        )
            .cmp(&(
                Reverse(covered_count.get(right).copied().unwrap_or(0)),
                *right,
            ))
    };
    match policy.track_layout {
        TrackLayout::SingleTrack => {
            let mut targets = Vec::with_capacity(active.len());
            for (position, target) in active.iter().copied().enumerate() {
                check_cancelled_periodically(cancellation, position)?;
                targets.push(target);
            }
            targets.sort_by(source_first);
            if cancellation.is_some_and(CancellationToken::is_cancelled) {
                return Err(PlanBuildError::Cancelled);
            }
            Ok(MaintenanceSchedule {
                tracks: vec![MaintenanceTrack {
                    kind: MaintenanceTrackKind::Default,
                    targets: targets.into(),
                }]
                .into(),
            })
        }
        TrackLayout::OrdinaryAndWTracks => {
            let mut w_layers = Vec::with_capacity(active.len());
            let mut ordinary = Vec::with_capacity(active.len());
            for (position, target) in active.iter().copied().enumerate() {
                check_cancelled_periodically(cancellation, position)?;
                if hints
                    .get(&target)
                    .is_some_and(|hint| hint.kind == MaintenanceTrackKind::WLayer)
                {
                    w_layers.push(target);
                } else {
                    ordinary.push(target);
                }
            }
            ordinary.sort_by(source_first);
            if cancellation.is_some_and(CancellationToken::is_cancelled) {
                return Err(PlanBuildError::Cancelled);
            }
            w_layers.sort_by(|left, right| {
                match (
                    hints.get(left).and_then(|hint| hint.descending_order_key),
                    hints.get(right).and_then(|hint| hint.descending_order_key),
                ) {
                    (Some(left_key), Some(right_key)) => {
                        (Reverse(left_key), *left).cmp(&(Reverse(right_key), *right))
                    }
                    (Some(_), None) => std::cmp::Ordering::Less,
                    (None, Some(_)) => std::cmp::Ordering::Greater,
                    (None, None) => source_first(left, right),
                }
            });
            if cancellation.is_some_and(CancellationToken::is_cancelled) {
                return Err(PlanBuildError::Cancelled);
            }
            // Round-robin over the sorted order, so every ordinary
            // track processes its targets in global priority order.
            let track_count = policy.ordinary_track_count.max(1);
            let mut ordinary_targets: Vec<Vec<ClauseId>> = vec![Vec::new(); track_count];
            for (position, target) in ordinary.into_iter().enumerate() {
                ordinary_targets[position % track_count].push(target);
            }
            let mut tracks = Vec::with_capacity(track_count + 1);
            for targets in ordinary_targets {
                tracks.push(MaintenanceTrack {
                    kind: MaintenanceTrackKind::Ordinary,
                    targets: targets.into(),
                });
            }
            tracks.push(MaintenanceTrack {
                kind: MaintenanceTrackKind::WLayer,
                targets: w_layers.into(),
            });
            Ok(MaintenanceSchedule {
                tracks: tracks.into(),
            })
        }
    }
}

// ------------------------------------------------------------
// End-To-End Maintenance Preparation
// ------------------------------------------------------------

#[derive(Clone, Debug)]
struct PlanBuildInput {
    task: SynthesisTask,
    catalog: ClauseCatalog,
    readiness: MaintenanceReadinessSnapshot,
    init_coverage: InitCoverage,
    maint_support: MaintSupport,
    maint_coverage: MaintCoverage,
    policy: MaintenancePolicy,
    track_hints: Arc<HashMap<ClauseId, MaintenanceTrackHint>>,
    proposal_generation: u64,
}

#[derive(Debug)]
enum PlanBuildError {
    Cancelled,
    Failure(FailureReport),
}

struct PlanBuildOutput {
    readiness: MaintenanceReadinessSnapshot,
    plan: MaintenancePlan,
    present_support_count: HashMap<ClauseId, usize>,
    candidate_snapshot: Arc<CandidateSnapshot>,
}

impl PlanBuildError {
    fn into_failure(self) -> FailureReport {
        match self {
            Self::Failure(report) => report,
            Self::Cancelled => {
                maintenance_invariant("a cancelled plan build was used as a logical failure")
            }
        }
    }
}

impl From<FailureReport> for PlanBuildError {
    fn from(value: FailureReport) -> Self {
        Self::Failure(value)
    }
}

impl From<MaintenanceSnapshotError> for PlanBuildError {
    fn from(value: MaintenanceSnapshotError) -> Self {
        match value {
            MaintenanceSnapshotError::Cancelled => Self::Cancelled,
            MaintenanceSnapshotError::Failure(report) => Self::Failure(report),
        }
    }
}

fn build_maintenance_plan(
    input: PlanBuildInput,
    cancellation: &CancellationToken,
) -> Result<PlanBuildOutput, PlanBuildError> {
    check_cancelled(cancellation)?;
    let core = input.readiness.core_snapshot();
    let init_candidates = input.readiness.init_candidates_snapshot();
    let active = input.readiness.active_snapshot();
    input.init_coverage.validate_closed(&input.catalog)?;
    if !is_subset_with_cancellation(&input.maint_support.base_core, &core, Some(cancellation))?
        || !is_subset_with_cancellation(&input.maint_coverage.base_core, &core, Some(cancellation))?
    {
        return Err(maintenance_invariant(
            "maintenance relation base Core is not a subset of current Core",
        )
        .into());
    }
    let candidate = union_with_cancellation(&core, &active, Some(cancellation))?;
    check_cancelled(cancellation)?;
    let (coverage, closure_metrics) = match input.policy.coverage_mode {
        CoverageMode::UseProducerClosed => (
            project_closed_maint_coverage_with_base(
                &input.catalog,
                Arc::clone(&core),
                &candidate,
                &input.init_coverage,
                &input.maint_coverage,
                Some(cancellation),
            )?,
            None,
        ),
        CoverageMode::ComputeClosure => {
            let (coverage, metrics) = close_maint_coverage_with_base(
                &input.catalog,
                Arc::clone(&core),
                &candidate,
                &input.init_coverage,
                &input.maint_coverage,
                Some(cancellation),
            )?;
            (coverage, Some(metrics))
        }
    };
    check_cancelled(cancellation)?;
    let (supported_by, supported_targets_by, present_support_count) = index_maint_support(
        &input.catalog,
        &core,
        &candidate,
        &active,
        &input.maint_support,
        Some(cancellation),
    )?;
    check_cancelled(cancellation)?;
    let (covered_by, covered_count) = index_maint_coverage(&active, &coverage, Some(cancellation))?;
    let live_cover_lookup = LiveCoverLookup::bind(
        &input.policy,
        &input.catalog,
        &candidate,
        Some(cancellation),
    )?;
    check_cancelled(cancellation)?;
    let schedule = build_maintenance_schedule(
        &input.track_hints,
        &active,
        &covered_count,
        &input.policy,
        Some(cancellation),
    )?;
    check_cancelled(cancellation)?;
    let candidate_snapshot = CandidateSnapshot::root(Arc::new(candidate));
    let plan = MaintenancePlan {
        task: input.task.identity().clone(),
        catalog_identity: input.catalog.identity(),
        encoding_context_id: Arc::from(input.catalog.encoding_context().context_id()),
        proposal_generation: input.proposal_generation,
        catalog_generation: input.readiness.generation(),
        core,
        init_candidates,
        initial_active: active,
        policy: input.policy,
        supported_by,
        supported_targets_by,
        covered_by,
        live_cover_lookup,
        covered_count,
        schedule,
        closure_metrics,
    };
    validate_built_plan(&plan, &present_support_count, cancellation)?;
    Ok(PlanBuildOutput {
        readiness: input.readiness,
        plan,
        present_support_count,
        candidate_snapshot,
    })
}

fn validate_built_plan(
    plan: &MaintenancePlan,
    present_support_count: &HashMap<ClauseId, usize>,
    cancellation: &CancellationToken,
) -> Result<(), PlanBuildError> {
    if plan.initial_active.is_empty() || present_support_count.len() != plan.initial_active.len() {
        return Err(
            maintenance_invariant("maintenance plan has the wrong Active/count universe").into(),
        );
    }
    for (position, id) in plan.initial_active.iter().enumerate() {
        check_cancelled_periodically(Some(cancellation), position)?;
        if present_support_count.get(id).copied() != Some(plan.supported_by(*id).len()) {
            return Err(
                maintenance_invariant("present-support counts do not match the plan").into(),
            );
        }
    }
    validate_schedule_with_cancellation(&plan.schedule, &plan.initial_active, cancellation)?;
    if (plan.policy.coverage_mode == CoverageMode::ComputeClosure) != plan.closure_metrics.is_some()
    {
        return Err(
            maintenance_invariant("fallback-closure metrics do not match coverage policy").into(),
        );
    }
    Ok(())
}

fn check_cancelled(cancellation: &CancellationToken) -> Result<(), PlanBuildError> {
    if cancellation.is_cancelled() {
        Err(PlanBuildError::Cancelled)
    } else {
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub enum MaintenancePreparationOutcome {
    Complete,
    Cancelled,
    RunFailure(FailureReport),
}

/// Prepare exact WPs, immutable indexes, and one checked Active publication.
pub async fn prepare_maintenance(
    task: &SynthesisTask,
    state: &mut HoudiniState,
    cancellation: &CancellationToken,
) -> MaintenancePreparationOutcome {
    if state.maintenance_failure.is_some() {
        return MaintenancePreparationOutcome::Complete;
    }
    if let Err(report) = state.validate_maintenance_entry(task) {
        return state.finish_maintenance_failure(report);
    }
    let selection_catalog = state.catalog.clone();
    let selection_core = Arc::clone(&state.core);
    let selection_candidates = Arc::clone(&state.init_candidates);
    let selection_proposal_generation = state.proposal_generation;
    let selection = match state
        .catalog
        .encoding_context()
        .run_cpu_job(&state.admission, cancellation, move |job_cancellation| {
            selection_catalog
                .snapshot_maintenance_selection(
                    selection_candidates,
                    selection_core,
                    selection_proposal_generation,
                    &job_cancellation,
                )
                .map_err(|error| match error {
                    MaintenanceSnapshotError::Cancelled => CpuJobError::Cancelled,
                    MaintenanceSnapshotError::Failure(report) => CpuJobError::Failure(report),
                })
        })
        .await
    {
        Ok(snapshot) => snapshot,
        Err(CpuJobError::Failure(report)) => {
            return state.finish_maintenance_failure(report);
        }
        Err(CpuJobError::Cancelled) | Err(CpuJobError::Admission(AdmissionError::Cancelled)) => {
            return MaintenancePreparationOutcome::Cancelled;
        }
        Err(CpuJobError::Admission(AdmissionError::Closed(report))) => {
            return state.finish_maintenance_failure(report);
        }
        Err(error) => {
            return state.finish_maintenance_failure(maintenance_global_failure(format!(
                "maintenance-selection CPU task failed: {error}"
            )));
        }
    };
    let wp_targets = selection.active_snapshot();
    if wp_targets.is_empty() {
        let catalog = state.catalog.clone();
        let _guard = match catalog.lock_maintenance_publication(&selection) {
            Ok(guard) => guard,
            Err(MaintenancePublicationError::Stale) => {
                return state.finish_maintenance_failure(maintenance_invariant(
                    "Catalog maintenance readiness changed before empty publication",
                ));
            }
            Err(MaintenancePublicationError::Failure(report)) => {
                return state.finish_maintenance_failure(report);
            }
        };
        state.bulk_init_proved = false;
        state.bulk_maint_proved = false;
        state.bulk_maint_capability = None;
        return MaintenancePreparationOutcome::Complete;
    }

    match state
        .catalog
        .prepare_maintenance_wps(&state.admission, &selection, cancellation)
        .await
    {
        Ok(()) => {}
        Err(crate::encoding::EncodingError::Cancelled) => {
            return MaintenancePreparationOutcome::Cancelled;
        }
        Err(crate::encoding::EncodingError::Failure(report)) => {
            return state.finish_maintenance_failure(report);
        }
    }
    if cancellation.is_cancelled() {
        return MaintenancePreparationOutcome::Cancelled;
    }

    let task_snapshot = task.clone();
    let catalog = state.catalog.clone();
    let core = state.core.clone();
    let init_candidates = state.init_candidates.clone();
    let init_coverage = state.init_coverage.clone();
    let maint_support = state.maint_support.clone();
    let maint_coverage = state.maint_coverage.clone();
    let policy = state.maintenance_policy.clone();
    let track_hints = state.track_hints.clone();
    let proposal_generation = state.proposal_generation;
    let context = state.catalog.encoding_context().clone();
    let built = context
        .run_cpu_job(&state.admission, cancellation, move |build_cancellation| {
            let readiness = catalog
                .snapshot_maintenance_readiness(
                    init_candidates,
                    core,
                    proposal_generation,
                    &build_cancellation,
                )
                .map_err(|error| match error {
                    MaintenanceSnapshotError::Cancelled => CpuJobError::Cancelled,
                    MaintenanceSnapshotError::Failure(report) => CpuJobError::Failure(report),
                })?;
            let input = PlanBuildInput {
                task: task_snapshot,
                catalog,
                readiness,
                init_coverage,
                maint_support,
                maint_coverage,
                policy,
                track_hints,
                proposal_generation,
            };
            build_maintenance_plan(input, &build_cancellation).map_err(|error| match error {
                PlanBuildError::Cancelled => CpuJobError::Cancelled,
                PlanBuildError::Failure(report) => CpuJobError::Failure(report),
            })
        })
        .await;
    let PlanBuildOutput {
        readiness,
        plan,
        present_support_count,
        candidate_snapshot,
    } = match built {
        Ok(built) => built,
        Err(CpuJobError::Cancelled) => {
            return MaintenancePreparationOutcome::Cancelled;
        }
        Err(CpuJobError::Admission(AdmissionError::Cancelled)) => {
            return MaintenancePreparationOutcome::Cancelled;
        }
        Err(CpuJobError::Admission(AdmissionError::Closed(report)))
        | Err(CpuJobError::Failure(report)) => {
            return state.finish_maintenance_failure(report);
        }
        Err(error) => {
            return state.finish_maintenance_failure(maintenance_global_failure(format!(
                "maintenance-plan CPU task failed: {error}"
            )));
        }
    };
    if cancellation.is_cancelled() {
        return MaintenancePreparationOutcome::Cancelled;
    }
    state.publish_maintenance_preparation(
        task,
        readiness,
        plan,
        present_support_count,
        candidate_snapshot,
    )
}

impl HoudiniState {
    fn validate_maintenance_entry(&self, task: &SynthesisTask) -> Result<(), FailureReport> {
        if self.catalog.task_identity() != task.identity()
            || self.artifacts.task_identity() != task.identity()
            || self.catalog.artifacts().backend_id() != self.artifacts.backend_id()
            || self.catalog.encoding_context().task_identity() != task.identity()
            || self.admission.policy() != self.verification.resources()
        {
            return Err(maintenance_global_failure(
                "maintenance task, state, Catalog, context, artifacts, and admission differ",
            ));
        }
        if !self.active.is_empty()
            || !self.present_support_count.is_empty()
            || self.maintenance_plan.is_some()
        {
            return Err(maintenance_invariant(
                "maintenance preparation requires no published Active/count/plan triple",
            ));
        }
        self.maint_support.validate_catalog(&self.catalog)?;
        self.maint_coverage.validate_catalog(&self.catalog)?;
        Ok(())
    }

    fn publish_maintenance_preparation(
        &mut self,
        task: &SynthesisTask,
        readiness: MaintenanceReadinessSnapshot,
        plan: MaintenancePlan,
        present_support_count: HashMap<ClauseId, usize>,
        candidate_snapshot: Arc<CandidateSnapshot>,
    ) -> MaintenancePreparationOutcome {
        // Keep mutable runtime Active independently owned. The immutable plan
        // retains its initial universe, but later exclusions must not trigger
        // an O(n) Arc copy-on-write clone merely because the plan exists.
        let active = Arc::new(plan.initial_active.as_ref().clone());
        if !self.active.is_empty()
            || !self.present_support_count.is_empty()
            || self.maintenance_plan.is_some()
            || self.maintenance_failure.is_some()
            || !plan.matches_publication_inputs(task, self, &readiness)
        {
            return self.finish_maintenance_failure(maintenance_invariant(
                "maintenance publication entry state became stale",
            ));
        }

        let plan = Arc::new(plan);
        let catalog = self.catalog.clone();
        let guard = match catalog.lock_maintenance_publication(&readiness) {
            Ok(guard) => guard,
            Err(MaintenancePublicationError::Stale) => {
                return self.finish_maintenance_failure(maintenance_invariant(
                    "Catalog maintenance readiness changed before publication",
                ));
            }
            Err(MaintenancePublicationError::Failure(report)) => {
                return self.finish_maintenance_failure(report);
            }
        };
        // All fallible work is complete. Publish the matching triple without
        // awaiting or allocating between its component assignments.
        self.active = active;
        self.candidate_snapshot = Some(candidate_snapshot);
        self.present_support_count = Arc::new(present_support_count);
        self.maintenance_plan = Some(plan);
        self.maintenance_state_revision = Arc::new(());
        self.history_baseline_plan = None;
        self.history_baseline_generation = None;
        self.bulk_init_proved = false;
        self.bulk_maint_proved = false;
        self.bulk_maint_capability = None;
        drop(guard);
        MaintenancePreparationOutcome::Complete
    }

    pub fn current_maintenance_plan(
        &self,
        task: &SynthesisTask,
    ) -> Result<Arc<MaintenancePlan>, FailureReport> {
        let plan = self
            .maintenance_plan
            .as_ref()
            .ok_or_else(|| maintenance_invariant("no maintenance plan is currently published"))?;
        if self.maintenance_failure.is_some()
            || !std::ptr::eq(
                self.maintenance_plan
                    .as_ref()
                    .expect("the plan was obtained from this slot")
                    .as_ref(),
                plan.as_ref(),
            )
            || !plan.matches_state_inputs(task, self)
            || !self.active.is_subset(&plan.initial_active)
        {
            return Err(maintenance_invariant(
                "the published maintenance plan is stale",
            ));
        }
        Ok(Arc::clone(plan))
    }

    fn finish_maintenance_failure(
        &mut self,
        report: FailureReport,
    ) -> MaintenancePreparationOutcome {
        self.telemetry
            .record_error(format!("maintenance preparation failure: {report:?}"));
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
        self.maintenance_failure = Some(report.clone());
        if report.scope() == FailureScope::RunGlobal {
            MaintenancePreparationOutcome::RunFailure(report)
        } else {
            MaintenancePreparationOutcome::Complete
        }
    }
}

// ------------------------------------------------------------
// Shared Validation And Failure Helpers
// ------------------------------------------------------------

fn validate_registered_set(catalog: &ClauseCatalog, ids: &ClauseSet) -> Result<(), FailureReport> {
    for id in ids {
        catalog.record(*id)?;
    }
    Ok(())
}

fn validate_registered_set_with_cancellation(
    catalog: &ClauseCatalog,
    ids: &ClauseSet,
    cancellation: Option<&CancellationToken>,
) -> Result<(), PlanBuildError> {
    for (position, id) in ids.iter().enumerate() {
        check_cancelled_periodically(cancellation, position)?;
        catalog.record(*id)?;
    }
    Ok(())
}

fn is_subset_with_cancellation(
    left: &ClauseSet,
    right: &ClauseSet,
    cancellation: Option<&CancellationToken>,
) -> Result<bool, PlanBuildError> {
    for (position, id) in left.iter().enumerate() {
        check_cancelled_periodically(cancellation, position)?;
        if !right.contains(id) {
            return Ok(false);
        }
    }
    Ok(true)
}

fn union_with_cancellation(
    left: &ClauseSet,
    right: &ClauseSet,
    cancellation: Option<&CancellationToken>,
) -> Result<ClauseSet, PlanBuildError> {
    let mut result = ClauseSet::with_capacity(left.len().saturating_add(right.len()));
    for (position, id) in left.iter().chain(right.iter()).enumerate() {
        check_cancelled_periodically(cancellation, position)?;
        result.insert(*id);
    }
    Ok(result)
}

fn is_exact_union_with_cancellation(
    candidate: &ClauseSet,
    core: &ClauseSet,
    active: &ClauseSet,
    cancellation: Option<&CancellationToken>,
) -> Result<bool, PlanBuildError> {
    if candidate.len() != core.len().saturating_add(active.len()) {
        return Ok(false);
    }
    Ok(is_subset_with_cancellation(core, candidate, cancellation)?
        && is_subset_with_cancellation(active, candidate, cancellation)?)
}

fn freeze_index(
    index: HashMap<ClauseId, Vec<ClauseId>>,
    cancellation: Option<&CancellationToken>,
) -> Result<RelationIndex, PlanBuildError> {
    let mut frozen = HashMap::with_capacity(index.len());
    for (position, (id, mut entries)) in index.into_iter().enumerate() {
        check_cancelled_periodically(cancellation, position)?;
        entries.sort_unstable();
        if cancellation.is_some_and(CancellationToken::is_cancelled) {
            return Err(PlanBuildError::Cancelled);
        }
        entries.dedup();
        frozen.insert(id, Arc::from(entries));
    }
    Ok(frozen)
}

fn check_cancelled_periodically(
    cancellation: Option<&CancellationToken>,
    position: usize,
) -> Result<(), PlanBuildError> {
    if position % 1024 == 0 && cancellation.is_some_and(CancellationToken::is_cancelled) {
        Err(PlanBuildError::Cancelled)
    } else {
        Ok(())
    }
}

fn validate_schedule_with_cancellation(
    schedule: &MaintenanceSchedule,
    active: &ClauseSet,
    cancellation: &CancellationToken,
) -> Result<(), PlanBuildError> {
    let mut seen = ClauseSet::new();
    let mut kinds = HashSet::new();
    for (track_position, track) in schedule.tracks().iter().enumerate() {
        check_cancelled_periodically(Some(cancellation), track_position)?;
        // Ordinary tracks may repeat: the ordinary worklist splits
        // round-robin across concurrent tracks. The Default and
        // WLayer kinds remain unique per schedule.
        if !kinds.insert(track.kind()) && track.kind() != MaintenanceTrackKind::Ordinary {
            return Err(
                maintenance_invariant("a maintenance schedule repeats a track kind").into(),
            );
        }
        for (position, id) in track.targets().iter().enumerate() {
            check_cancelled_periodically(Some(cancellation), position)?;
            if !active.contains(id) || !seen.insert(*id) {
                return Err(maintenance_invariant(
                    "a maintenance schedule has an unknown or duplicate target",
                )
                .into());
            }
        }
    }
    if seen.len() != active.len()
        || !is_subset_with_cancellation(&seen, active, Some(cancellation))?
    {
        return Err(maintenance_invariant("a maintenance schedule does not exhaust Active").into());
    }
    Ok(())
}

pub(super) fn maintenance_invariant(detail: impl Into<String>) -> FailureReport {
    FailureReport::try_new(
        FailureOrigin::MaintenanceExecution,
        FailureKind::StateInvariantViolation,
        false,
        FailureScope::LaneLocal,
        Some(detail.into()),
        Vec::new(),
    )
    .expect("maintenance invariant failures use a permitted pair")
}

fn maintenance_scope_failure(detail: impl Into<String>) -> FailureReport {
    FailureReport::try_new(
        FailureOrigin::MaintenanceExecution,
        FailureKind::InfrastructureFailure,
        false,
        FailureScope::LaneLocal,
        Some(detail.into()),
        Vec::new(),
    )
    .expect("maintenance infrastructure failures use a permitted pair")
}

fn maintenance_global_failure(detail: impl Into<String>) -> FailureReport {
    FailureReport::try_new(
        FailureOrigin::MaintenanceExecution,
        FailureKind::InfrastructureFailure,
        false,
        FailureScope::RunGlobal,
        Some(detail.into()),
        Vec::new(),
    )
    .expect("maintenance shared-infrastructure failures use a permitted pair")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn source_first_order_uses_coverage_then_id() {
        let ids = [ClauseId::test(0), ClauseId::test(1), ClauseId::test(2)];
        let active = ClauseSet::from(ids);
        let counts = HashMap::from([(ids[0], 1), (ids[1], 2), (ids[2], 2)]);
        let hints = HashMap::from([
            (
                ids[1],
                MaintenanceTrackHint::new(MaintenanceTrackKind::Ordinary, Some(1)),
            ),
            (
                ids[2],
                MaintenanceTrackHint::new(MaintenanceTrackKind::Ordinary, Some(4)),
            ),
        ]);
        let schedule = build_maintenance_schedule(
            &hints,
            &active,
            &counts,
            &MaintenancePolicy::single_track(),
            None,
        )
        .unwrap();
        assert_eq!(schedule.tracks[0].targets(), &[ids[1], ids[2], ids[0]]);
    }

    #[test]
    fn closed_coverage_index_preserves_incoming_and_outdegree_views() {
        let catalog_identity = 7;
        let ids = [ClauseId::test(0), ClauseId::test(1), ClauseId::test(2)];
        let core = ClauseSet::new();
        let closed_edges = HashSet::from([(ids[0], ids[1]), (ids[1], ids[2]), (ids[0], ids[2])]);
        let projected = MaintCoverage::from_edges(
            catalog_identity,
            Arc::new(core.clone()),
            closed_edges.clone(),
        );
        assert_eq!(projected.edges.as_ref(), &closed_edges);

        let active = ClauseSet::from(ids);
        let (incoming, outdegree) = index_maint_coverage(&active, &projected, None).unwrap();
        assert_eq!(incoming[&ids[1]].as_ref(), &[ids[0]]);
        assert_eq!(incoming[&ids[2]].as_ref(), &[ids[0], ids[1]]);
        assert_eq!(outdegree[&ids[0]], 2);
        assert_eq!(outdegree[&ids[1]], 1);
    }

    #[test]
    fn sparse_w_targets_are_descending_without_bridging_gaps() {
        let ids = [ClauseId::test(0), ClauseId::test(1), ClauseId::test(2)];
        let active = ClauseSet::from(ids);
        let counts = HashMap::from_iter(ids.into_iter().map(|id| (id, 0)));
        let hints = HashMap::from([
            (
                ids[0],
                MaintenanceTrackHint::new(MaintenanceTrackKind::WLayer, Some(2)),
            ),
            (
                ids[1],
                MaintenanceTrackHint::new(MaintenanceTrackKind::WLayer, Some(9)),
            ),
            (
                ids[2],
                MaintenanceTrackHint::new(MaintenanceTrackKind::WLayer, Some(4)),
            ),
        ]);
        let policy = MaintenancePolicy::new(
            CoverageMode::UseProducerClosed,
            TrackLayout::OrdinaryAndWTracks,
            CoverageLookup::IncomingEdges,
        );
        let schedule = build_maintenance_schedule(&hints, &active, &counts, &policy, None).unwrap();
        assert!(schedule.tracks[0].targets().is_empty());
        assert_eq!(schedule.tracks[1].targets(), &[ids[1], ids[2], ids[0]]);
    }

    #[test]
    fn ordinary_targets_split_round_robin_across_requested_tracks() {
        let ids = [
            ClauseId::test(0),
            ClauseId::test(1),
            ClauseId::test(2),
            ClauseId::test(3),
            ClauseId::test(4),
        ];
        let active = ClauseSet::from(ids);
        // Distinct covered counts fix the sorted order: 4, 3, 2, 1, 0.
        let counts = HashMap::from_iter(
            ids.into_iter()
                .enumerate()
                .map(|(position, id)| (id, position)),
        );
        let hints = HashMap::new();
        let policy = MaintenancePolicy::new(
            CoverageMode::UseProducerClosed,
            TrackLayout::OrdinaryAndWTracks,
            CoverageLookup::IncomingEdges,
        )
        .with_ordinary_track_count(2)
        .unwrap();

        let schedule = build_maintenance_schedule(&hints, &active, &counts, &policy, None).unwrap();

        assert_eq!(schedule.tracks.len(), 3);
        assert_eq!(schedule.tracks[0].kind(), MaintenanceTrackKind::Ordinary);
        assert_eq!(schedule.tracks[1].kind(), MaintenanceTrackKind::Ordinary);
        assert_eq!(schedule.tracks[2].kind(), MaintenanceTrackKind::WLayer);
        assert_eq!(schedule.tracks[0].targets(), &[ids[4], ids[2], ids[0]]);
        assert_eq!(schedule.tracks[1].targets(), &[ids[3], ids[1]]);
        assert!(schedule.tracks[2].targets().is_empty());
        assert!(
            MaintenancePolicy::new(
                CoverageMode::UseProducerClosed,
                TrackLayout::OrdinaryAndWTracks,
                CoverageLookup::IncomingEdges,
            )
            .with_ordinary_track_count(0)
            .is_err()
        );
    }

    #[test]
    fn w_targets_without_order_keys_use_ordinary_coverage_order() {
        let ids = [ClauseId::test(0), ClauseId::test(1), ClauseId::test(2)];
        let active = ClauseSet::from(ids);
        let counts = HashMap::from([(ids[0], 1), (ids[1], 3), (ids[2], 3)]);
        let hints = HashMap::from_iter(ids.into_iter().map(|id| {
            (
                id,
                MaintenanceTrackHint::new(MaintenanceTrackKind::WLayer, None),
            )
        }));
        let policy = MaintenancePolicy::new(
            CoverageMode::UseProducerClosed,
            TrackLayout::OrdinaryAndWTracks,
            CoverageLookup::IncomingEdges,
        );

        let schedule = build_maintenance_schedule(&hints, &active, &counts, &policy, None).unwrap();

        assert_eq!(schedule.tracks[1].targets(), &[ids[1], ids[2], ids[0]]);
    }

    #[test]
    fn literal_subset_trie_covers_only_from_stronger_to_weaker_clause() {
        let literal_a = serde_json::json!(["eq", ["rel", "r"], ["rel", "s"]]);
        let literal_b = serde_json::json!(["not", ["subset", ["rel", "r"], ["rel", "s"]]]);
        let source = CanonicalLiteralSet::from_reference_identity(
            &serde_json::to_string(&literal_a).unwrap(),
        )
        .expect("one structural literal");
        let target = CanonicalLiteralSet::from_reference_identity(
            &serde_json::to_string(&serde_json::json!(["or", literal_a, literal_b])).unwrap(),
        )
        .expect("two structural literals");
        let source_clause = ClauseId::test(0);
        let target_clause = ClauseId::test(1);

        let mut forward = LiteralSubsetTrieNode::default();
        forward.insert(source.literals(), source_clause);
        assert_eq!(
            forward
                .find_subset_by(target.literals(), 0, &mut |_| true, None, &mut 0)
                .unwrap(),
            Some(source_clause),
        );

        let mut reverse = LiteralSubsetTrieNode::default();
        reverse.insert(target.literals(), target_clause);
        assert_eq!(
            reverse
                .find_subset_by(source.literals(), 0, &mut |_| true, None, &mut 0)
                .unwrap(),
            None,
        );
    }

    #[test]
    fn literal_subset_traversal_cooperatively_observes_cancellation() {
        let literals = (0..300)
            .map(|index| Arc::<str>::from(format!("literal-{index:03}")))
            .collect::<Vec<_>>();
        let mut root = LiteralSubsetTrieNode::default();
        for (index, literal) in literals.iter().enumerate() {
            root.insert(std::slice::from_ref(literal), ClauseId::test(index as u64));
        }
        let cancellation = CancellationToken::new();
        cancellation.cancel();
        let mut visited = 0;

        let result = root.find_subset_by(
            &literals,
            0,
            &mut |_| false,
            Some(&cancellation),
            &mut visited,
        );

        assert!(matches!(result, Err(CpuJobError::Cancelled)));
        assert_eq!(visited, 256);
    }
}
