//! Shared encoding context, exact sources, and memoized preparation API.

use std::collections::hash_map::DefaultHasher;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use serde::{Deserialize, Serialize};
use serde_json::json;
use tokio::sync::{Mutex as AsyncMutex, Notify};
use tokio::task::{JoinError, JoinSet};

use crate::artifact::{
    ArtifactKind, ArtifactRef, ArtifactStore, AttemptId, OwnedWorkRegistration, ScopeTag,
};
use crate::failure::{FailureKind, FailureReport, FailureScope};
use crate::runtime::{CancellationToken, CpuJobError, RetainedCpuJobs, SolverAdmission};
use crate::task::{
    ConstantKey, RelationKey, SolverAssertSourceRef, SolverQfSourceRef, SynthesisTask, TaskIdentity,
};
use crate::vampire::{VampireModel, VampireProof};

use super::cache::AsyncMemo;
use super::names::{NameEnvRevision, NameEnvSync, NameMapping, NameMappingKind, TaskNameEnv};
use super::proposal::{
    PROPOSAL_PAGE_PROTOCOL_VERSION, ProposalRealization, ProposalRevision, ProposalSync,
    ReferenceProposalAuthority, bytes_sha256, canonical_value_sha256,
};
use super::protocol::{
    FIXED_AMBIENT_WORKER_FORMAT_VERSION, FixedAmbientNameBinding, FixedAmbientWorkerBinding,
    FixedAmbientWorkerOperation, FixedAmbientWorkerRequestEnvelope,
    FixedAmbientWorkerResponseError, NameBinding, WORKER_FORMAT_VERSION, WorkerOperation,
    WorkerRequestEnvelope, WorkerResponseEnvelope, WorkerResponseStatus,
};
use super::solver_name::SolverNameError;
use super::worker::{
    EncodingWorkerPool, EncodingWorkerPoolConfig, FixedAmbientWorkerPool,
    FixedAmbientWorkerPoolConfig, RetainedWorkerResponse, RetainedWorkerSession, WLayerReplay,
    WLayerSync, WorkerAffinity,
};

static NEXT_CONTEXT: AtomicU64 = AtomicU64::new(0);
static NEXT_FIXED_AMBIENT_CONTEXT: AtomicU64 = AtomicU64::new(0);
pub(crate) const MAINTENANCE_WP_SOURCE_PREFIX: &str = "__whiel_maintenance_wp__:";
pub(crate) const W_LAYER_SOURCE_PREFIX: &str = "__whiel_w_layer__:";
pub(crate) const W_LAYER_WP_SOURCE_PREFIX: &str = "__whiel_w_layer_wp__:";

// ------------------------------------------------------------
// Public Source And Result Types
// ------------------------------------------------------------

#[derive(Clone, Debug)]
pub enum SolverBodySource {
    Assert(SolverAssertSourceRef),
    QuantifierFree(QfSolverSource),
}

#[derive(Clone, Debug)]
pub struct QfSolverSource {
    task: TaskIdentity,
    source_id: Arc<str>,
    constants: Arc<[ConstantKey]>,
    relations: Arc<[RelationKey]>,
}

/// One Lean-owned formula admitted from the reference enumerator.
#[derive(Clone, Debug)]
pub struct ReferenceProposalSource {
    identity: Arc<str>,
    display: Arc<str>,
    source: QfSolverSource,
}

impl ReferenceProposalSource {
    pub fn identity(&self) -> &str {
        &self.identity
    }

    pub fn display(&self) -> &str {
        &self.display
    }

    pub fn source(&self) -> &QfSolverSource {
        &self.source
    }

    pub fn into_parts(self) -> (Arc<str>, Arc<str>, QfSolverSource) {
        (self.identity, self.display, self.source)
    }
}

/// One exact incremental wave returned by the Lean reference enumerator.
#[derive(Clone, Debug)]
pub struct ReferenceProposalBatch {
    stage: u64,
    revision: ProposalRevision,
    entries: Arc<[ReferenceProposalSource]>,
    page_count: u64,
    // These counts describe the cumulative Lean slice at `stage`. Callers
    // that report a stage delta must subtract the preceding stage's counts.
    // Equality deduplication is the one measured duplicate boundary.
    cumulative_decoded_formula_occurrences: u64,
    cumulative_equality_distinct_formulas: u64,
    cumulative_equality_deduplicated_occurrences: u64,
    /// Stage-local stable work units reported by the selected Lean realization.
    generator_work_units: u64,
    /// Stage-local nodes visited by the lower-width fresh-member traversal.
    fresh_traversal_nodes: u64,
    fresh_no_fresh_prunes: u64,
    fresh_too_short_prunes: u64,
}

/// One complete Lean-owned exact W formula and maintenance WP bundle.
#[derive(Clone, Debug)]
pub struct PreparedWLayerBundle {
    index: u64,
    identity: Arc<str>,
    display: Arc<str>,
    formula_source: QfSolverSource,
    formula_body: PreparedBodyRef,
    maintenance_wp_source: QfSolverSource,
    maintenance_wp_body: PreparedBodyRef,
}

impl PreparedWLayerBundle {
    pub fn index(&self) -> u64 {
        self.index
    }

    pub fn identity(&self) -> &str {
        &self.identity
    }

    pub(crate) fn identity_arc(&self) -> Arc<str> {
        Arc::clone(&self.identity)
    }

    pub fn display(&self) -> &str {
        &self.display
    }

    pub(crate) fn display_arc(&self) -> Arc<str> {
        Arc::clone(&self.display)
    }

    pub fn formula_source(&self) -> &QfSolverSource {
        &self.formula_source
    }

    pub fn formula_body(&self) -> &PreparedBodyRef {
        &self.formula_body
    }

    pub fn maintenance_wp_source(&self) -> &QfSolverSource {
        &self.maintenance_wp_source
    }

    pub fn maintenance_wp_body(&self) -> &PreparedBodyRef {
        &self.maintenance_wp_body
    }
}

impl ReferenceProposalBatch {
    pub fn stage(&self) -> u64 {
        self.stage
    }

    pub fn revision(&self) -> ProposalRevision {
        self.revision
    }

    pub fn entries(&self) -> &[ReferenceProposalSource] {
        &self.entries
    }

    pub fn page_count(&self) -> u64 {
        self.page_count
    }

    pub fn cumulative_decoded_formula_occurrences(&self) -> u64 {
        self.cumulative_decoded_formula_occurrences
    }

    pub fn cumulative_equality_distinct_formulas(&self) -> u64 {
        self.cumulative_equality_distinct_formulas
    }

    pub fn cumulative_equality_deduplicated_occurrences(&self) -> u64 {
        self.cumulative_equality_deduplicated_occurrences
    }

    pub fn generator_work_units(&self) -> u64 {
        self.generator_work_units
    }

    pub fn fresh_traversal_nodes(&self) -> u64 {
        self.fresh_traversal_nodes
    }

    pub fn fresh_no_fresh_prunes(&self) -> u64 {
        self.fresh_no_fresh_prunes
    }

    pub fn fresh_too_short_prunes(&self) -> u64 {
        self.fresh_too_short_prunes
    }

    pub fn into_entries(self) -> Arc<[ReferenceProposalSource]> {
        self.entries
    }
}

impl QfSolverSource {
    pub fn new(
        task: &SynthesisTask,
        source_id: impl Into<Arc<str>>,
        constants: impl IntoIterator<Item = ConstantKey>,
        relations: impl IntoIterator<Item = RelationKey>,
    ) -> Result<Self, &'static str> {
        let source_id = source_id.into();
        if source_id.is_empty() {
            return Err("a QF solver source requires a nonempty trusted registry identity");
        }
        if source_id.starts_with(MAINTENANCE_WP_SOURCE_PREFIX)
            || source_id.starts_with(W_LAYER_SOURCE_PREFIX)
            || source_id.starts_with(W_LAYER_WP_SOURCE_PREFIX)
        {
            return Err("a raw QF source cannot use a reserved derived-source namespace");
        }
        let constants: BTreeSet<_> = constants.into_iter().collect();
        let relations: BTreeSet<_> = relations.into_iter().collect();
        Ok(Self {
            task: task.identity().clone(),
            source_id,
            constants: constants.into_iter().collect::<Vec<_>>().into(),
            relations: relations.into_iter().collect::<Vec<_>>().into(),
        })
    }

    pub fn source_id(&self) -> &str {
        &self.source_id
    }

    fn new_maintenance_wp(
        task: &SynthesisTask,
        source_id: impl Into<Arc<str>>,
        constants: impl IntoIterator<Item = ConstantKey>,
        relations: impl IntoIterator<Item = RelationKey>,
    ) -> Result<Self, &'static str> {
        let source_id = source_id.into();
        if !source_id.starts_with(MAINTENANCE_WP_SOURCE_PREFIX)
            || source_id.len() == MAINTENANCE_WP_SOURCE_PREFIX.len()
        {
            return Err("a derived maintenance WP requires its reserved source identity");
        }
        let constants: BTreeSet<_> = constants.into_iter().collect();
        let relations: BTreeSet<_> = relations.into_iter().collect();
        Ok(Self {
            task: task.identity().clone(),
            source_id,
            constants: constants.into_iter().collect::<Vec<_>>().into(),
            relations: relations.into_iter().collect::<Vec<_>>().into(),
        })
    }

    fn new_w_layer_source(
        task: &SynthesisTask,
        source_id: impl Into<Arc<str>>,
        expected_prefix: &str,
        constants: impl IntoIterator<Item = ConstantKey>,
        relations: impl IntoIterator<Item = RelationKey>,
    ) -> Result<Self, &'static str> {
        let source_id = source_id.into();
        if !source_id.starts_with(expected_prefix) || source_id.len() == expected_prefix.len() {
            return Err("a W-layer source requires its reserved source identity");
        }
        let constants: BTreeSet<_> = constants.into_iter().collect();
        let relations: BTreeSet<_> = relations.into_iter().collect();
        Ok(Self {
            task: task.identity().clone(),
            source_id,
            constants: constants.into_iter().collect::<Vec<_>>().into(),
            relations: relations.into_iter().collect::<Vec<_>>().into(),
        })
    }
}

impl SolverBodySource {
    pub fn task_identity(&self) -> &TaskIdentity {
        match self {
            Self::Assert(source) => source.task_identity(),
            Self::QuantifierFree(source) => &source.task,
        }
    }

    pub fn source_id(&self) -> &str {
        match self {
            Self::Assert(source) => source.source_id(),
            Self::QuantifierFree(source) => source.source_id(),
        }
    }

    fn constants(&self) -> &[ConstantKey] {
        match self {
            Self::Assert(source) => source.constants(),
            Self::QuantifierFree(source) => &source.constants,
        }
    }

    fn relations(&self) -> &[RelationKey] {
        match self {
            Self::Assert(source) => source.relations(),
            Self::QuantifierFree(source) => &source.relations,
        }
    }

    fn key(&self) -> BodyCacheKey {
        BodyCacheKey {
            kind: match self {
                Self::Assert(_) => SourceKind::Assert,
                Self::QuantifierFree(_) => SourceKind::QuantifierFree,
            },
            source_id: Arc::from(self.source_id()),
            constants: self.constants().to_vec().into(),
            relations: self.relations().to_vec().into(),
        }
    }

    pub(crate) fn same_identity(&self, other: &Self) -> bool {
        self.task_identity() == other.task_identity()
            && match (self, other) {
                (Self::Assert(left), Self::Assert(right)) => {
                    left.source_id() == right.source_id()
                        && left.constants() == right.constants()
                        && left.relations() == right.relations()
                }
                (Self::QuantifierFree(left), Self::QuantifierFree(right)) => {
                    left.source_id == right.source_id
                        && left.constants == right.constants
                        && left.relations == right.relations
                }
                _ => false,
            }
    }
}

impl From<SolverQfSourceRef> for SolverBodySource {
    fn from(source: SolverQfSourceRef) -> Self {
        Self::QuantifierFree(QfSolverSource {
            task: source.task_identity().clone(),
            source_id: Arc::from(source.source_id()),
            constants: Arc::from(source.constants()),
            relations: Arc::from(source.relations()),
        })
    }
}

#[derive(Clone, Debug)]
pub struct PreparedBodyRef(Arc<PreparedBody>);

#[derive(Debug)]
struct PreparedBody {
    context_id: Arc<str>,
    semantic_version: u64,
    encoding_version: u64,
    source: SolverBodySource,
    body_id: Arc<str>,
    fol_identity: Arc<str>,
    tptp_body: Arc<str>,
    constants: Arc<[ConstantKey]>,
    preparation_revision: NameEnvRevision,
    theorem_id: Arc<str>,
}

impl PreparedBodyRef {
    pub fn context_id(&self) -> &str {
        &self.0.context_id
    }

    pub fn source(&self) -> &SolverBodySource {
        &self.0.source
    }

    pub fn body_id(&self) -> &str {
        &self.0.body_id
    }

    pub fn fol_identity(&self) -> &str {
        &self.0.fol_identity
    }

    pub fn tptp_body(&self) -> &str {
        &self.0.tptp_body
    }

    pub fn constants(&self) -> &[ConstantKey] {
        &self.0.constants
    }

    pub fn preparation_revision(&self) -> NameEnvRevision {
        self.0.preparation_revision
    }

    pub fn theorem_id(&self) -> &str {
        &self.0.theorem_id
    }

    pub fn semantic_version(&self) -> u64 {
        self.0.semantic_version
    }

    pub fn encoding_version(&self) -> u64 {
        self.0.encoding_version
    }
}

#[derive(Clone, Debug)]
pub struct SupportBlockRef(Arc<SupportBlock>);

#[derive(Debug)]
struct SupportBlock {
    context_id: Arc<str>,
    constant_keys: Arc<[ConstantKey]>,
    block_id: Arc<str>,
    role_neutral_bodies: Arc<[Arc<str>]>,
    preparation_revision: NameEnvRevision,
}

impl SupportBlockRef {
    pub fn context_id(&self) -> &str {
        &self.0.context_id
    }

    pub fn constant_keys(&self) -> &[ConstantKey] {
        &self.0.constant_keys
    }

    pub fn block_id(&self) -> &str {
        &self.0.block_id
    }

    /// Return the adom body followed by every distinctness body.
    ///
    /// Query assembly assigns TPTP names and axiom roles; these cached bodies
    /// intentionally contain neither.
    pub fn role_neutral_bodies(&self) -> &[Arc<str>] {
        &self.0.role_neutral_bodies
    }

    pub fn preparation_revision(&self) -> NameEnvRevision {
        self.0.preparation_revision
    }
}

#[derive(Clone, Debug)]
pub enum EncodingError {
    Cancelled,
    Failure(FailureReport),
}

/// Only draft evaluation treats instance admission as caller input failure.
/// Other fixed-ambient operations retain the ordinary encoding error contract.
#[derive(Clone, Debug)]
pub(crate) enum FixedAmbientEvaluationError {
    InvalidInstance(String),
    Encoding(EncodingError),
}

impl From<EncodingError> for FixedAmbientEvaluationError {
    fn from(error: EncodingError) -> Self {
        Self::Encoding(error)
    }
}

impl FixedAmbientEvaluationError {
    fn into_encoding(self) -> EncodingError {
        match self {
            Self::InvalidInstance(message) => EncodingError::Failure(encoding_failure(
                EncodingFailureClass::MalformedResponse,
                format!("instance_admission: {message}"),
            )),
            Self::Encoding(error) => error,
        }
    }
}

fn fixed_ambient_worker_error(
    operation: FixedAmbientWorkerOperation,
    error: Option<&FixedAmbientWorkerResponseError>,
) -> FixedAmbientEvaluationError {
    if operation == FixedAmbientWorkerOperation::EvaluateClauses
        && let Some(error) = error
        && error.kind == "instance_admission"
    {
        return FixedAmbientEvaluationError::InvalidInstance(error.message.clone());
    }
    let class = match error.map(|error| error.kind.as_str()) {
        Some("invalid_envelope" | "name_environment") => EncodingFailureClass::SharedInfrastructure,
        Some("malformed_payload" | "unknown_operation") => {
            EncodingFailureClass::ProtocolIncompatibility
        }
        _ => EncodingFailureClass::MalformedResponse,
    };
    let detail = error.map_or_else(
        || "fixed-ambient worker rejected the request".to_string(),
        |error| format!("{}: {}", error.kind, error.message),
    );
    EncodingError::Failure(encoding_failure(class, detail)).into()
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CatalogFormulaBindingError {
    ConflictingCanonicalIdentity,
    Capacity,
    Poisoned,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct NullaryAssignmentValue {
    pub(crate) relation_key: RelationKey,
    pub(crate) value: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum NativeEmptyOutcome {
    NoCounterexample,
    Counterexample(Arc<[NullaryAssignmentValue]>),
}

#[derive(Clone, Debug)]
pub(crate) struct NativeEmptyCheck {
    pub(crate) outcome: NativeEmptyOutcome,
    pub(crate) evidence: ArtifactRef,
    pub(crate) evidence_digest: Arc<str>,
    pub(crate) elapsed: Duration,
}

#[derive(Clone, Debug)]
pub(crate) struct FixedAmbientWorkerResult {
    pub(crate) payload: serde_json::Value,
    pub(crate) name_env_revision: NameEnvRevision,
}

/// Proof-erased body returned by the fixed-ambient Lean worker.
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct FixedAmbientPreparedBodyData {
    pub(crate) source_id: String,
    pub(crate) source_kind: String,
    pub(crate) exact_constant_keys: BTreeSet<String>,
    pub(crate) body: String,
    pub(crate) referenced_relations: Vec<FixedAmbientNameBinding>,
    pub(crate) referenced_constants: Vec<FixedAmbientNameBinding>,
}

/// Proof-erased support block returned by the fixed-ambient Lean worker.
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct FixedAmbientPreparedSupportData {
    pub(crate) constant_keys: BTreeSet<String>,
    pub(crate) adom_body: String,
    pub(crate) distinct_bodies: Vec<String>,
    pub(crate) referenced_relations: Vec<FixedAmbientNameBinding>,
    pub(crate) referenced_constants: Vec<FixedAmbientNameBinding>,
}

impl fmt::Display for EncodingError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Cancelled => formatter.write_str("encoding preparation was cancelled"),
            Self::Failure(report) => write!(
                formatter,
                "encoding failure: origin={:?} kind={:?} detail={}",
                report.origin(),
                report.kind(),
                report.detail().unwrap_or("none")
            ),
        }
    }
}

impl std::error::Error for EncodingError {}

// ------------------------------------------------------------
// Shared Context
// ------------------------------------------------------------

#[derive(Clone)]
pub struct SolverEncodingContext {
    inner: Arc<ContextInner>,
}

struct ContextInner {
    context_id: Arc<str>,
    task: TaskIdentity,
    source_task: SynthesisTask,
    schema_relations: Arc<[RelationKey]>,
    schema_arities: Arc<HashMap<RelationKey, u64>>,
    artifacts: ArtifactStore,
    owned_work: OwnedWorkRegistration,
    admission_authority: Mutex<Option<SolverAdmission>>,
    names: Mutex<TaskNameEnv>,
    proposals: Mutex<ReferenceProposalAuthority>,
    proposal_worker_affinity: Mutex<Option<WorkerAffinity>>,
    proposal_registration: AsyncMutex<()>,
    proposal_source_ids: Mutex<HashSet<Arc<str>>>,
    proposal_identities: Mutex<HashSet<Arc<str>>>,
    w_layers: Mutex<WLayerAuthority>,
    w_layer_registration: AsyncMutex<()>,
    workers: EncodingWorkerPool,
    cpu_jobs: RetainedCpuJobs,
    next_request: Arc<AtomicU64>,
    body_cache: AsyncMemo<BodyCacheKey, PreparedBody, EncodingError>,
    maintenance_wp_cache: AsyncMemo<BodyCacheKey, PreparedBody, EncodingError>,
    support_cache: AsyncMemo<SupportKey, SupportBlock, EncodingError>,
    empty_cache: AsyncMemo<Arc<str>, NativeEmptyCheck, EncodingError>,
    proof_cache: Mutex<HashMap<(Arc<str>, AttemptId), VampireProof>>,
    model_cache: Mutex<HashMap<(Arc<str>, AttemptId), VampireModel>>,
    catalog_formula_bindings: Mutex<HashMap<Arc<str>, Arc<str>>>,
    shutdown: Arc<ContextShutdown>,
}

#[derive(Default)]
struct WLayerAuthority {
    bundles: Vec<Arc<PreparedWLayerBundle>>,
    replay: Arc<Vec<WLayerReplay>>,
}

impl WLayerAuthority {
    fn sync(&self) -> WLayerSync {
        WLayerSync {
            entries: Arc::clone(&self.replay),
        }
    }
}

struct ContextShutdown {
    started: AtomicBool,
    result: Mutex<Option<Result<(), EncodingError>>>,
    settled: Notify,
}

impl fmt::Debug for SolverEncodingContext {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SolverEncodingContext")
            .field("context_id", &self.inner.context_id)
            .field("task", &self.inner.task.canonical_id())
            .finish_non_exhaustive()
    }
}

pub fn new_solver_encoding_context(
    task: &SynthesisTask,
    artifacts: &ArtifactStore,
    workers: EncodingWorkerPoolConfig,
) -> Result<SolverEncodingContext, FailureReport> {
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    return Err(encoding_failure(
        EncodingFailureClass::SharedInfrastructure,
        "owned Lean encoding-worker process-tree supervision is unavailable on this platform",
    ));

    if artifacts.task_identity() != task.identity() {
        return Err(encoding_failure(
            EncodingFailureClass::SharedInfrastructure,
            "artifact backend and solver-encoding task identities differ",
        ));
    }
    let proposal_realization = workers.proposal_realization;
    let sequence = NEXT_CONTEXT.fetch_add(1, Ordering::Relaxed);
    let context_id: Arc<str> = Arc::from(format!("{}-{sequence}", artifacts.backend_id()));
    let worker_pool = EncodingWorkerPool::new(workers, &context_id);
    let names = TaskNameEnv::from_task(task).map_err(unnameable_symbol)?;
    let owned_work = artifacts.register_lifetime_owned_work()?;
    Ok(SolverEncodingContext {
        inner: Arc::new(ContextInner {
            context_id,
            task: task.identity().clone(),
            source_task: task.clone(),
            schema_relations: task
                .solver_relations()
                .iter()
                .map(|relation| relation.key().clone())
                .collect::<Vec<_>>()
                .into(),
            schema_arities: Arc::new(
                task.solver_relations()
                    .iter()
                    .map(|relation| (relation.key().clone(), relation.arity()))
                    .collect(),
            ),
            artifacts: artifacts.scoped(ScopeTag::solver("encoding")),
            owned_work,
            admission_authority: Mutex::new(None),
            names: Mutex::new(names),
            proposals: Mutex::new(ReferenceProposalAuthority::new(proposal_realization)),
            proposal_worker_affinity: Mutex::new(None),
            proposal_registration: AsyncMutex::new(()),
            proposal_source_ids: Mutex::new(HashSet::new()),
            proposal_identities: Mutex::new(HashSet::new()),
            w_layers: Mutex::new(WLayerAuthority::default()),
            w_layer_registration: AsyncMutex::new(()),
            workers: worker_pool,
            cpu_jobs: RetainedCpuJobs::new(),
            next_request: Arc::new(AtomicU64::new(0)),
            body_cache: AsyncMemo::new(),
            maintenance_wp_cache: AsyncMemo::new(),
            support_cache: AsyncMemo::new(),
            empty_cache: AsyncMemo::new(),
            proof_cache: Mutex::new(HashMap::new()),
            model_cache: Mutex::new(HashMap::new()),
            catalog_formula_bindings: Mutex::new(HashMap::new()),
            shutdown: Arc::new(ContextShutdown {
                started: AtomicBool::new(false),
                result: Mutex::new(None),
                settled: Notify::new(),
            }),
        }),
    })
}

// ------------------------------------------------------------
// Fixed-Ambient Context
// ------------------------------------------------------------

/// Retained solver outputs keyed by entailment identity, attempt scope, and attempt.
type RetainedSolverOutput<T> = Mutex<HashMap<(Arc<str>, Arc<str>, AttemptId), T>>;

#[derive(Clone)]
pub struct FixedAmbientEncodingContext {
    inner: Arc<FixedAmbientContextInner>,
}

struct FixedAmbientContextInner {
    context_id: Arc<str>,
    replay_allocation_sequence: u64,
    binding: FixedAmbientWorkerBinding,
    schema_relations: Arc<HashSet<RelationKey>>,
    admission_authority: Mutex<Option<SolverAdmission>>,
    names: Mutex<TaskNameEnv>,
    workers: FixedAmbientWorkerPool,
    cpu_jobs: RetainedCpuJobs,
    next_request: Arc<AtomicU64>,
    proof_cache: RetainedSolverOutput<VampireProof>,
    model_cache: RetainedSolverOutput<VampireModel>,
    shutdown: Arc<ContextShutdown>,
}

fn complete_value_key(value: &serde_json::Value) -> Arc<str> {
    Arc::from(
        serde_json::to_string(value)
            .expect("an in-memory fixed-ambient identity always serializes"),
    )
}

impl fmt::Debug for FixedAmbientEncodingContext {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("FixedAmbientEncodingContext")
            .field("context_id", &self.inner.context_id)
            .field("task", &self.inner.binding.task_identity().canonical_id())
            .finish_non_exhaustive()
    }
}

pub fn new_fixed_ambient_encoding_context(
    binding: FixedAmbientWorkerBinding,
    relations: impl IntoIterator<Item = RelationKey>,
    constants: impl IntoIterator<Item = ConstantKey>,
    workers: FixedAmbientWorkerPoolConfig,
) -> Result<FixedAmbientEncodingContext, FailureReport> {
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    return Err(encoding_failure(
        EncodingFailureClass::SharedInfrastructure,
        "owned fixed-ambient worker supervision is unavailable on this platform",
    ));

    let relations = relations.into_iter().collect::<BTreeSet<_>>();
    let constants = constants.into_iter().collect::<BTreeSet<_>>();
    let scope_bytes = serde_json::to_vec(binding.scope_identity()).map_err(|error| {
        encoding_failure(
            EncodingFailureClass::ProtocolIncompatibility,
            format!("serialize fixed-ambient scope identity: {error}"),
        )
    })?;
    if scope_bytes.is_empty() || scope_bytes.len() > workers.frame_limit() {
        return Err(encoding_failure(
            EncodingFailureClass::ProtocolIncompatibility,
            "fixed-ambient scope identity is outside the worker frame bound",
        ));
    }
    let sequence = NEXT_FIXED_AMBIENT_CONTEXT.fetch_add(1, Ordering::Relaxed);
    let context_id = Arc::from(replay_fixed_ambient_context_id(
        binding.task_identity().canonical_id(),
        sequence,
    ));
    let names = TaskNameEnv::from_keys(relations.iter().cloned(), constants.iter().cloned())
        .map_err(unnameable_symbol)?;
    Ok(FixedAmbientEncodingContext {
        inner: Arc::new(FixedAmbientContextInner {
            context_id,
            replay_allocation_sequence: sequence,
            schema_relations: Arc::new(relations.iter().cloned().collect()),
            admission_authority: Mutex::new(None),
            names: Mutex::new(names),
            workers: FixedAmbientWorkerPool::new(workers),
            cpu_jobs: RetainedCpuJobs::new(),
            binding,
            next_request: Arc::new(AtomicU64::new(0)),
            proof_cache: Mutex::new(HashMap::new()),
            model_cache: Mutex::new(HashMap::new()),
            shutdown: Arc::new(ContextShutdown {
                started: AtomicBool::new(false),
                result: Mutex::new(None),
                settled: Notify::new(),
            }),
        }),
    })
}

impl FixedAmbientEncodingContext {
    pub fn context_id(&self) -> &str {
        &self.inner.context_id
    }

    pub fn task_identity(&self) -> &TaskIdentity {
        self.inner.binding.task_identity()
    }

    pub fn scope_identity(&self) -> &serde_json::Value {
        self.inner.binding.scope_identity()
    }

    pub fn worker_capacity(&self) -> usize {
        self.inner.workers.capacity()
    }

    pub fn worker_frame_limit(&self) -> usize {
        self.inner.workers.max_frame_bytes()
    }

    pub(crate) fn extend_name_env(
        &self,
        relations: impl IntoIterator<Item = RelationKey>,
        constants: impl IntoIterator<Item = ConstantKey>,
    ) -> Result<NameEnvRevision, EncodingError> {
        let relations = relations.into_iter().collect::<BTreeSet<_>>();
        if relations
            .iter()
            .any(|relation| !self.inner.schema_relations.contains(relation))
        {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "fixed-ambient NameEnv extension names a relation outside the scope",
            )));
        }
        self.inner
            .names
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .extend(relations, constants)
            .map_err(|error| EncodingError::Failure(unnameable_symbol(error)))
    }

    #[cfg(test)]
    pub(crate) fn name_snapshot(
        &self,
        relations: impl IntoIterator<Item = RelationKey>,
        constants: impl IntoIterator<Item = ConstantKey>,
    ) -> Result<(NameEnvRevision, Vec<NameMapping>), EncodingError> {
        let relations = relations.into_iter().collect::<BTreeSet<_>>();
        let constants = constants.into_iter().collect::<BTreeSet<_>>();
        let names = self
            .inner
            .names
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let mappings = names.mappings_for(relations.iter().cloned(), constants.iter().cloned());
        if mappings.len() != relations.len() + constants.len() {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "fixed-ambient NameEnv snapshot requested an unadmitted key",
            )));
        }
        Ok((names.revision(), mappings))
    }

    /// Copy the current append-only fixed-ambient name environment.
    pub(crate) fn task_name_env(&self) -> TaskNameEnv {
        self.inner
            .names
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .clone()
    }

    #[cfg(test)]
    pub(crate) fn name_env(&self) -> TaskNameEnv {
        self.task_name_env()
    }

    pub(crate) async fn run_cpu_job<T, F>(
        &self,
        admission: &SolverAdmission,
        cancellation: &CancellationToken,
        work: F,
    ) -> Result<T, CpuJobError>
    where
        T: Send + 'static,
        F: FnOnce(CancellationToken) -> Result<T, CpuJobError> + Send + 'static,
    {
        self.bind_admission_authority(admission)
            .map_err(|error| match error {
                EncodingError::Cancelled => CpuJobError::Cancelled,
                EncodingError::Failure(report) => CpuJobError::Failure(report),
            })?;
        self.inner.cpu_jobs.run(admission, cancellation, work).await
    }

    pub(crate) async fn execute(
        &self,
        admission: &SolverAdmission,
        cancellation: &CancellationToken,
        operation: FixedAmbientWorkerOperation,
        payload: serde_json::Value,
    ) -> Result<FixedAmbientWorkerResult, EncodingError> {
        self.execute_with_evaluation_diagnostics(admission, cancellation, operation, payload)
            .await
            .map_err(FixedAmbientEvaluationError::into_encoding)
    }

    /// Evaluate caller-supplied instances without treating malformed instance
    /// data as a worker defect. The operation is fixed here, not caller-selected.
    pub(crate) async fn execute_evaluation(
        &self,
        admission: &SolverAdmission,
        cancellation: &CancellationToken,
        payload: serde_json::Value,
    ) -> Result<FixedAmbientWorkerResult, FixedAmbientEvaluationError> {
        self.execute_with_evaluation_diagnostics(
            admission,
            cancellation,
            FixedAmbientWorkerOperation::EvaluateClauses,
            payload,
        )
        .await
    }

    async fn execute_with_evaluation_diagnostics(
        &self,
        admission: &SolverAdmission,
        cancellation: &CancellationToken,
        operation: FixedAmbientWorkerOperation,
        payload: serde_json::Value,
    ) -> Result<FixedAmbientWorkerResult, FixedAmbientEvaluationError> {
        if matches!(
            operation,
            FixedAmbientWorkerOperation::ExtendNameEnv | FixedAmbientWorkerOperation::Shutdown
        ) {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "stateful fixed-ambient operations are context-owned",
            ))
            .into());
        }
        self.bind_admission_authority(admission)?;
        if cancellation.is_cancelled() {
            return Err(EncodingError::Cancelled.into());
        }
        let (revision, sync) = {
            let names = self
                .inner
                .names
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner());
            let revision = names.revision();
            let sync = names.sync_through(revision).ok_or_else(|| {
                EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::SharedInfrastructure,
                    "failed to snapshot the fixed-ambient NameEnv revision",
                ))
            })?;
            (revision, sync)
        };
        let request = self.request(revision, operation, payload)?;
        let response = self
            .inner
            .workers
            .execute(
                sync,
                request,
                Arc::clone(&self.inner.next_request),
                cancellation,
            )
            .await?;
        if cancellation.is_cancelled() {
            return Err(EncodingError::Cancelled.into());
        }
        if response.status == WorkerResponseStatus::Error {
            return Err(fixed_ambient_worker_error(
                operation,
                response.error.as_ref(),
            ));
        }
        Ok(FixedAmbientWorkerResult {
            payload: response.payload,
            name_env_revision: response.name_env_revision,
        })
    }

    pub(crate) fn adopt_body(
        &self,
        data: FixedAmbientPreparedBodyData,
        preparation_revision: NameEnvRevision,
    ) -> Result<PreparedBodyRef, EncodingError> {
        if data.source_id.is_empty()
            || data.source_kind != "quantifier_free"
            || data.body.is_empty()
        {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::MalformedResponse,
                "invalid fixed-ambient prepared body",
            )));
        }
        self.validate_preparation_revision(preparation_revision)?;
        let (relations, constants) = self
            .validate_prepared_mappings(&data.referenced_relations, &data.referenced_constants)?;
        let exact_constants = data
            .exact_constant_keys
            .into_iter()
            .map(ConstantKey::from_canonical)
            .collect::<Result<BTreeSet<_>, _>>()
            .map_err(|error| {
                EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::MalformedResponse,
                    format!("fixed-ambient body returned an invalid constant key: {error}"),
                ))
            })?;
        if exact_constants != constants {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::MalformedResponse,
                "fixed-ambient body constant identities disagree",
            )));
        }
        let source_id: Arc<str> = Arc::from(data.source_id);
        let source = SolverBodySource::QuantifierFree(QfSolverSource {
            task: self.task_identity().clone(),
            source_id: Arc::clone(&source_id),
            constants: constants.into_iter().collect::<Vec<_>>().into(),
            relations: relations.into_iter().collect::<Vec<_>>().into(),
        });
        Ok(PreparedBodyRef(Arc::new(PreparedBody {
            context_id: Arc::clone(&self.inner.context_id),
            semantic_version: self.task_identity().semantic_version(),
            encoding_version: self.task_identity().encoding_version(),
            constants: source.constants().to_vec().into(),
            body_id: Arc::from(replay_fixed_ambient_body_id(
                &self.inner.context_id,
                &source_id,
            )),
            fol_identity: Arc::clone(&source_id),
            source,
            tptp_body: Arc::from(data.body),
            preparation_revision,
            theorem_id: Arc::from("Whiel.Vampire.TPTP.roleNeutralBody_stable"),
        })))
    }

    pub(crate) fn adopt_support(
        &self,
        data: FixedAmbientPreparedSupportData,
        preparation_revision: NameEnvRevision,
    ) -> Result<SupportBlockRef, EncodingError> {
        if data.adom_body.is_empty() || data.distinct_bodies.iter().any(String::is_empty) {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::MalformedResponse,
                "invalid fixed-ambient support block",
            )));
        }
        self.validate_preparation_revision(preparation_revision)?;
        let (relations, constants) = self
            .validate_prepared_mappings(&data.referenced_relations, &data.referenced_constants)?;
        if relations.len() != self.inner.schema_relations.len()
            || relations
                .iter()
                .any(|relation| !self.inner.schema_relations.contains(relation))
        {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::MalformedResponse,
                "fixed-ambient support does not cover the exact ambient schema",
            )));
        }
        let exact_constants = data
            .constant_keys
            .into_iter()
            .map(ConstantKey::from_canonical)
            .collect::<Result<BTreeSet<_>, _>>()
            .map_err(|error| {
                EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::MalformedResponse,
                    format!("fixed-ambient support returned an invalid constant key: {error}"),
                ))
            })?;
        if exact_constants != constants {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::MalformedResponse,
                "fixed-ambient support constant identities disagree",
            )));
        }
        let constants = constants.into_iter().collect::<Vec<_>>();
        let block_id: Arc<str> = Arc::from(replay_fixed_ambient_support_id(
            &self.inner.context_id,
            constants.iter().map(ConstantKey::as_str),
        ));
        let role_neutral_bodies = std::iter::once(data.adom_body)
            .chain(data.distinct_bodies)
            .map(Arc::from)
            .collect::<Vec<_>>();
        Ok(SupportBlockRef(Arc::new(SupportBlock {
            context_id: Arc::clone(&self.inner.context_id),
            constant_keys: constants.into(),
            block_id,
            role_neutral_bodies: role_neutral_bodies.into(),
            preparation_revision,
        })))
    }

    pub(crate) fn retained_proof(
        &self,
        worker_identity: &serde_json::Value,
        logical_identity: &str,
        attempt: AttemptId,
    ) -> Option<VampireProof> {
        let worker_identity = complete_value_key(worker_identity);
        self.inner
            .proof_cache
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .get(&(worker_identity, Arc::from(logical_identity), attempt))
            .cloned()
    }

    pub(crate) fn retain_proof(
        &self,
        worker_identity: &serde_json::Value,
        logical_identity: Arc<str>,
        attempt: AttemptId,
        proof: VampireProof,
    ) -> Result<VampireProof, EncodingError> {
        if proof.problem_identity() != logical_identity.as_ref() || proof.attempt_id() != attempt {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "Vampire proof identity differs from its fixed-ambient cache key",
            )));
        }
        let mut cache = self
            .inner
            .proof_cache
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let retained = cache
            .entry((
                complete_value_key(worker_identity),
                logical_identity,
                attempt,
            ))
            .or_insert_with(|| proof.clone());
        if retained.output() != proof.output()
            || retained.query_artifact() != proof.query_artifact()
            || retained.szs_status() != proof.szs_status()
            || retained.strategy() != proof.strategy()
            || retained.invocation() != proof.invocation()
        {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "fixed-ambient proof cache observed conflicting results for one attempt",
            )));
        }
        Ok(retained.clone())
    }

    pub(crate) fn retained_model(
        &self,
        worker_identity: &serde_json::Value,
        logical_identity: &str,
        attempt: AttemptId,
    ) -> Option<VampireModel> {
        let worker_identity = complete_value_key(worker_identity);
        self.inner
            .model_cache
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .get(&(worker_identity, Arc::from(logical_identity), attempt))
            .cloned()
    }

    pub(crate) fn retain_model(
        &self,
        worker_identity: &serde_json::Value,
        logical_identity: Arc<str>,
        attempt: AttemptId,
        model: VampireModel,
    ) -> Result<VampireModel, EncodingError> {
        if model.problem_identity() != logical_identity.as_ref() || model.attempt_id() != attempt {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "Vampire model identity differs from its fixed-ambient cache key",
            )));
        }
        let mut cache = self
            .inner
            .model_cache
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let retained = cache
            .entry((
                complete_value_key(worker_identity),
                logical_identity,
                attempt,
            ))
            .or_insert_with(|| model.clone());
        if retained.output() != model.output()
            || retained.query_artifact() != model.query_artifact()
            || retained.szs_status() != model.szs_status()
        {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "fixed-ambient model cache observed conflicting results for one attempt",
            )));
        }
        Ok(retained.clone())
    }

    pub(crate) async fn shutdown(&self) -> Result<(), EncodingError> {
        if self
            .inner
            .shutdown
            .started
            .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
            .is_ok()
        {
            let context = self.clone();
            let shutdown = Arc::clone(&self.inner.shutdown);
            tokio::spawn(async move {
                let cleanup = tokio::spawn(async move { context.perform_shutdown().await }).await;
                let result = match cleanup {
                    Ok(result) => result,
                    Err(error) => Err(EncodingError::Failure(encoding_failure(
                        EncodingFailureClass::SharedInfrastructure,
                        format!("fixed-ambient context shutdown task failed: {error}"),
                    ))),
                };
                *shutdown
                    .result
                    .lock()
                    .unwrap_or_else(|poisoned| poisoned.into_inner()) = Some(result);
                shutdown.settled.notify_waiters();
            });
        }
        self.inner.shutdown.wait().await
    }

    async fn perform_shutdown(&self) -> Result<(), EncodingError> {
        let cpu_jobs = self.inner.cpu_jobs.shutdown().await;
        let workers = self.inner.workers.shutdown().await;
        cpu_jobs.map_err(|error| match error {
            CpuJobError::Failure(report) if report.scope() == FailureScope::RunGlobal => {
                EncodingError::Failure(report)
            }
            CpuJobError::Admission(crate::runtime::AdmissionError::Closed(report)) => {
                EncodingError::Failure(report)
            }
            error => EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                format!("fixed-ambient retained CPU-job shutdown failed: {error}"),
            )),
        })?;
        workers
    }

    fn request(
        &self,
        revision: NameEnvRevision,
        operation: FixedAmbientWorkerOperation,
        payload: serde_json::Value,
    ) -> Result<FixedAmbientWorkerRequestEnvelope, EncodingError> {
        let request_id = self
            .inner
            .next_request
            .fetch_update(Ordering::AcqRel, Ordering::Acquire, |current| {
                current.checked_add(1)
            })
            .map_err(|_| {
                EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::SharedInfrastructure,
                    "fixed-ambient worker request identity space exhausted",
                ))
            })?;
        let task = self.task_identity();
        Ok(FixedAmbientWorkerRequestEnvelope {
            format_version: FIXED_AMBIENT_WORKER_FORMAT_VERSION,
            semantic_version: task.semantic_version(),
            encoding_version: task.encoding_version(),
            task_canonical_id: task.canonical_id().to_string(),
            task_module: task.module().to_string(),
            task_namespace: task.namespace().to_string(),
            task_source_sha256: task.source_digest().as_str().to_string(),
            scope_identity: self.scope_identity().clone(),
            request_id,
            name_env_revision: revision,
            operation,
            payload,
        })
    }

    fn validate_preparation_revision(
        &self,
        preparation_revision: NameEnvRevision,
    ) -> Result<(), EncodingError> {
        let current = self
            .inner
            .names
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .revision();
        if preparation_revision > current {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::MalformedResponse,
                "fixed-ambient preparation names a future NameEnv revision",
            )));
        }
        Ok(())
    }

    fn validate_prepared_mappings(
        &self,
        relation_bindings: &[FixedAmbientNameBinding],
        constant_bindings: &[FixedAmbientNameBinding],
    ) -> Result<(BTreeSet<RelationKey>, BTreeSet<ConstantKey>), EncodingError> {
        let relations = relation_bindings
            .iter()
            .map(|binding| RelationKey::from_lean_scope(binding.key.clone()))
            .collect::<Result<BTreeSet<_>, _>>()
            .map_err(|error| {
                EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::MalformedResponse,
                    format!("fixed-ambient body returned an invalid relation key: {error}"),
                ))
            })?;
        if relations.len() != relation_bindings.len()
            || relations
                .iter()
                .any(|relation| !self.inner.schema_relations.contains(relation))
        {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::MalformedResponse,
                "fixed-ambient body repeats or escapes the ambient relation scope",
            )));
        }
        let constants = constant_bindings
            .iter()
            .map(|binding| ConstantKey::from_canonical(binding.key.clone()))
            .collect::<Result<BTreeSet<_>, _>>()
            .map_err(|error| {
                EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::MalformedResponse,
                    format!("fixed-ambient body returned an invalid constant key: {error}"),
                ))
            })?;
        if constants.len() != constant_bindings.len() {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::MalformedResponse,
                "fixed-ambient body repeats a constant key",
            )));
        }
        let mappings = relation_bindings
            .iter()
            .map(|binding| NameMapping {
                kind: NameMappingKind::Relation,
                key: binding.key.clone(),
                tptp_name: binding.name.clone(),
            })
            .chain(constant_bindings.iter().map(|binding| NameMapping {
                kind: NameMappingKind::Constant,
                key: binding.key.clone(),
                tptp_name: binding.name.clone(),
            }))
            .collect::<Vec<_>>();
        let names = self
            .inner
            .names
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        if !names.agrees_with(&mappings) {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "fixed-ambient prepared data conflicts with the NameEnv authority",
            )));
        }
        Ok((relations, constants))
    }

    fn bind_admission_authority(&self, admission: &SolverAdmission) -> Result<(), EncodingError> {
        let mut authority = self
            .inner
            .admission_authority
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        match authority.as_ref() {
            None => {
                *authority = Some(admission.clone());
                Ok(())
            }
            Some(bound) if bound.shares_controller_with(admission) => Ok(()),
            Some(_) => Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "fixed-ambient context received an unrelated admission authority",
            ))),
        }
    }

    /// Return whether an admission authority is bound and shares its controller.
    pub(crate) fn matches_admission_authority(&self, admission: &SolverAdmission) -> bool {
        self.inner
            .admission_authority
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .as_ref()
            .is_some_and(|bound| bound.shares_controller_with(admission))
    }
}

impl SolverEncodingContext {
    pub fn context_id(&self) -> &str {
        &self.inner.context_id
    }

    pub fn task_identity(&self) -> &TaskIdentity {
        &self.inner.task
    }

    /// Return the immutable source task owned by this context.
    pub fn task(&self) -> &SynthesisTask {
        &self.inner.source_task
    }

    pub fn artifact_store(&self) -> &ArtifactStore {
        &self.inner.artifacts
    }

    pub(crate) fn body_preparation_capacity(&self) -> usize {
        self.inner.workers.capacity()
    }

    /// Run one context-owned CPU job under the context's exact admission
    /// authority. The retained supervisor remains joinable through context
    /// shutdown even if the calling future is dropped.
    pub(crate) async fn run_cpu_job<T, F>(
        &self,
        admission: &SolverAdmission,
        cancellation: &CancellationToken,
        work: F,
    ) -> Result<T, CpuJobError>
    where
        T: Send + 'static,
        F: FnOnce(CancellationToken) -> Result<T, CpuJobError> + Send + 'static,
    {
        self.bind_admission_authority(admission)
            .map_err(|error| match error {
                EncodingError::Cancelled => CpuJobError::Cancelled,
                EncodingError::Failure(report) => CpuJobError::Failure(report),
            })?;
        self.inner.cpu_jobs.run(admission, cancellation, work).await
    }

    pub(crate) fn maintenance_wp_matches(
        &self,
        target: &SolverBodySource,
        body: &PreparedBodyRef,
    ) -> bool {
        self.prepared_body_matches(body.source(), body)
            && body.source().source_id()
                == format!("{MAINTENANCE_WP_SOURCE_PREFIX}{}", target.source_id())
    }

    pub(crate) fn prepared_body_matches(
        &self,
        source: &SolverBodySource,
        body: &PreparedBodyRef,
    ) -> bool {
        body.context_id() == self.context_id()
            && body.source().task_identity() == self.task_identity()
            && body.source().same_identity(source)
    }

    /// Bind each theorem-backed source to one exact canonical formula across
    /// all Catalogs that share this encoding context.
    pub(crate) fn bind_catalog_formula(
        &self,
        source_id: &str,
        canonical: &str,
    ) -> Result<(), CatalogFormulaBindingError> {
        let mut bindings = self
            .inner
            .catalog_formula_bindings
            .lock()
            .map_err(|_| CatalogFormulaBindingError::Poisoned)?;
        if let Some(existing) = bindings.get(source_id) {
            return if existing.as_ref() == canonical {
                Ok(())
            } else {
                Err(CatalogFormulaBindingError::ConflictingCanonicalIdentity)
            };
        }
        bindings
            .try_reserve(1)
            .map_err(|_| CatalogFormulaBindingError::Capacity)?;
        bindings.insert(Arc::from(source_id), Arc::from(canonical));
        Ok(())
    }

    pub fn name_env(&self) -> TaskNameEnv {
        self.inner
            .names
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .clone()
    }

    pub fn proposal_revision(&self) -> ProposalRevision {
        self.inner
            .proposals
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .revision()
    }

    pub fn proposal_realization(&self) -> ProposalRealization {
        self.inner
            .proposals
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .realization()
    }

    /// Ask Lean to enumerate and register the next reference-proposal stage.
    ///
    /// Rust validates only the typed wire metadata. It never parses or
    /// elaborates the returned formula text. The append-only revision commits
    /// only after the complete response passes validation.
    pub async fn advance_reference_proposal(
        &self,
        admission: &SolverAdmission,
        cancellation: &CancellationToken,
    ) -> Result<ReferenceProposalBatch, EncodingError> {
        self.bind_admission_authority(admission)?;
        let _registration = tokio::select! {
            biased;
            _ = cancellation.cancelled() => return Err(EncodingError::Cancelled),
            guard = self.inner.proposal_registration.lock() => guard,
        };
        let (name_revision, name_sync) = {
            let names = self
                .inner
                .names
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner());
            let revision = names.revision();
            let sync = names
                .sync_through(revision)
                .expect("the current NameEnv revision has a replay plan");
            (revision, sync)
        };
        let max_response_bytes =
            u64::try_from(self.inner.workers.max_frame_bytes()).map_err(|_| {
                EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::SharedInfrastructure,
                    "encoding-worker frame limit does not fit the proposal protocol",
                ))
            })?;
        let mut page_counts = None;
        let mut page_count = 0_u64;
        let mut retained_session: Option<RetainedWorkerSession> = None;
        loop {
            if cancellation.is_cancelled() {
                if let Some(session) = retained_session.take() {
                    return Err(session.reject(EncodingError::Cancelled).await);
                }
                return Err(EncodingError::Cancelled);
            }
            let (base_revision, cursor, proposal_sync, realization) = {
                let proposals = self
                    .inner
                    .proposals
                    .lock()
                    .unwrap_or_else(|poisoned| poisoned.into_inner());
                (
                    proposals.revision(),
                    proposals.next_cursor(),
                    proposals.sync(),
                    proposals.realization(),
                )
            };
            let stage = base_revision.get();
            let request = match self.request(
                name_revision,
                WorkerOperation::RegisterReferenceProposal,
                json!({
                    "realization_id": realization.realization_id(),
                    "realization_version": realization.realization_version(),
                    "version": PROPOSAL_PAGE_PROTOCOL_VERSION,
                    "stage": stage,
                    "cursor": cursor,
                    "max_response_bytes": max_response_bytes,
                }),
            ) {
                Ok(request) => request,
                Err(error) => {
                    if let Some(session) = retained_session.take() {
                        return Err(session.reject(error).await);
                    }
                    return Err(error);
                }
            };
            if request.proposal_revision != base_revision {
                let error = EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::SharedInfrastructure,
                    "proposal authority changed while constructing a registration request",
                ));
                if let Some(session) = retained_session.take() {
                    return Err(session.reject(error).await);
                }
                return Err(error);
            }
            let retained_response = match retained_session.take() {
                Some(session) => {
                    self.inner
                        .workers
                        .execute_retained_in(
                            session,
                            admission,
                            name_sync.clone(),
                            proposal_sync,
                            WLayerSync::empty(),
                            request.clone(),
                            Arc::clone(&self.inner.next_request),
                            cancellation,
                        )
                        .await?
                }
                None => {
                    let affinity = *self
                        .inner
                        .proposal_worker_affinity
                        .lock()
                        .unwrap_or_else(|poisoned| poisoned.into_inner());
                    self.inner
                        .workers
                        .execute_retained_with_affinity(
                            affinity,
                            admission,
                            name_sync.clone(),
                            proposal_sync,
                            WLayerSync::empty(),
                            request.clone(),
                            Arc::clone(&self.inner.next_request),
                            cancellation,
                        )
                        .await?
                }
            };
            let response = retained_response.response();
            if cancellation.is_cancelled() {
                return self
                    .reject_proposal_response(retained_response, EncodingError::Cancelled)
                    .await;
            }
            if let Err(error) = self.validate_response(&request, response) {
                return self
                    .reject_proposal_response(retained_response, error)
                    .await;
            }
            let replay_payload = response.payload.clone();
            let payload: ReferenceProposalPageResponse =
                match serde_json::from_value(response.payload.clone()) {
                    Ok(payload) => payload,
                    Err(error) => {
                        return self
                            .reject_proposal_response(
                                retained_response,
                                EncodingError::Failure(encoding_failure(
                                    EncodingFailureClass::MalformedResponse,
                                    format!("decode reference-proposal page response: {error}"),
                                )),
                            )
                            .await;
                    }
                };
            if let Err(error) = validate_reference_proposal_page(
                realization,
                stage,
                cursor,
                base_revision,
                response.proposal_revision,
                &payload,
            ) {
                return self
                    .reject_proposal_response(retained_response, error)
                    .await;
            }
            let [
                generator_work_units,
                fresh_traversal_nodes,
                fresh_no_fresh_prunes,
                fresh_too_short_prunes,
            ] = payload
                .work_metrics(realization)
                .expect("validated proposal work metadata");
            page_count = match page_count.checked_add(1) {
                Some(page_count) => page_count,
                None => {
                    let error = EncodingError::Failure(encoding_failure(
                        EncodingFailureClass::SharedInfrastructure,
                        "reference-proposal page count exhausted",
                    ));
                    return self
                        .reject_proposal_response(retained_response, error)
                        .await;
                }
            };
            let observed_counts = (
                payload.decoded_formula_occurrences,
                payload.equality_distinct_formulas,
                payload.equality_deduplicated_occurrences,
                payload.emitted_formulas,
                generator_work_units,
                fresh_traversal_nodes,
                fresh_no_fresh_prunes,
                fresh_too_short_prunes,
            );
            if page_counts.is_some_and(|expected| expected != observed_counts) {
                self.discard_partial_reference_proposal();
                return self
                    .reject_proposal_response(
                        retained_response,
                        EncodingError::Failure(encoding_failure(
                            EncodingFailureClass::MalformedResponse,
                            "reference-proposal counts changed between pages",
                        )),
                    )
                    .await;
            }
            page_counts.get_or_insert(observed_counts);
            let terminal_entries = if payload.complete {
                let mut assembled = self
                    .inner
                    .proposals
                    .lock()
                    .unwrap_or_else(|poisoned| poisoned.into_inner())
                    .partial_fragment_text();
                assembled.push_str(&payload.fragment);
                let wire_entries: Vec<WireReferenceProposalSource> =
                    match serde_json::from_str(&assembled) {
                        Ok(entries) => entries,
                        Err(error) => {
                            self.discard_partial_reference_proposal();
                            return self
                                .reject_proposal_response(
                                    retained_response,
                                    EncodingError::Failure(encoding_failure(
                                        EncodingFailureClass::MalformedResponse,
                                        format!(
                                            "decode assembled reference-proposal wave: {error}"
                                        ),
                                    )),
                                )
                                .await;
                        }
                    };
                let entries = match self.validate_reference_proposal(wire_entries) {
                    Ok(entries) => entries,
                    Err(error) => {
                        self.discard_partial_reference_proposal();
                        return self
                            .reject_proposal_response(retained_response, error)
                            .await;
                    }
                };
                if let Err(error) = self.validate_reference_proposal_freshness(&entries) {
                    self.discard_partial_reference_proposal();
                    return self
                        .reject_proposal_response(retained_response, error)
                        .await;
                }
                if u64::try_from(entries.len()).ok() != Some(payload.emitted_formulas) {
                    self.discard_partial_reference_proposal();
                    return self
                        .reject_proposal_response(
                            retained_response,
                            EncodingError::Failure(encoding_failure(
                                EncodingFailureClass::MalformedResponse,
                                "reference-proposal emitted count differs from its decoded wave",
                            )),
                        )
                        .await;
                }
                Some(entries)
            } else {
                None
            };
            if cancellation.is_cancelled() {
                return self
                    .reject_proposal_response(retained_response, EncodingError::Cancelled)
                    .await;
            }
            let fragment: Arc<str> = Arc::from(payload.fragment);
            let committed_revision = self
                .inner
                .proposals
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner())
                .commit_page(
                    base_revision,
                    stage,
                    cursor,
                    payload.next_cursor,
                    max_response_bytes,
                    payload.complete,
                    fragment,
                    replay_payload,
                );
            let revision = match committed_revision {
                Some(revision) => revision,
                None => {
                    return self
                        .reject_proposal_response(
                            retained_response,
                            EncodingError::Failure(encoding_failure(
                                EncodingFailureClass::SharedInfrastructure,
                                "proposal authority changed before page commit",
                            )),
                        )
                        .await;
                }
            };
            if let Some(entries) = terminal_entries {
                self.record_reference_proposal_identities(&entries);
                let (_, affinity) = retained_response.accept_with_affinity();
                *self
                    .inner
                    .proposal_worker_affinity
                    .lock()
                    .unwrap_or_else(|poisoned| poisoned.into_inner()) = Some(affinity);
                return Ok(ReferenceProposalBatch {
                    stage,
                    revision,
                    entries: entries.into(),
                    page_count,
                    cumulative_decoded_formula_occurrences: payload.decoded_formula_occurrences,
                    cumulative_equality_distinct_formulas: payload.equality_distinct_formulas,
                    cumulative_equality_deduplicated_occurrences: payload
                        .equality_deduplicated_occurrences,
                    generator_work_units,
                    fresh_traversal_nodes,
                    fresh_no_fresh_prunes,
                    fresh_too_short_prunes,
                });
            }
            retained_session = Some(retained_response.accept_and_retain_slot());
        }
    }

    /// Construct and retain one exact contiguous W-layer bundle in Lean.
    ///
    /// The worker creates both `W(index)` and its loop-body WP once. Rust
    /// validates the complete response before extending the append-only
    /// authority. A rejected response retires the speculative worker child.
    pub async fn ensure_w_layer_bundle(
        &self,
        admission: &SolverAdmission,
        index: u64,
        cancellation: &CancellationToken,
    ) -> Result<Arc<PreparedWLayerBundle>, EncodingError> {
        self.bind_admission_authority(admission)?;
        let _registration = tokio::select! {
            biased;
            _ = cancellation.cancelled() => return Err(EncodingError::Cancelled),
            guard = self.inner.w_layer_registration.lock() => guard,
        };
        let index_usize = usize::try_from(index).map_err(|_| {
            EncodingError::Failure(encoding_failure(
                EncodingFailureClass::LocalInfrastructure,
                "W-layer index does not fit this runtime",
            ))
        })?;
        let base_sync = {
            let authority = self
                .inner
                .w_layers
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner());
            if let Some(bundle) = authority.bundles.get(index_usize) {
                return Ok(Arc::clone(bundle));
            }
            if index_usize != authority.bundles.len() {
                return Err(EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::LocalInfrastructure,
                    "fresh W-layer construction must be contiguous",
                )));
            }
            authority.sync()
        };
        let (name_revision, name_sync) = {
            let names = self
                .inner
                .names
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner());
            let revision = names.revision();
            let sync = names.sync_through(revision).ok_or_else(|| {
                EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::SharedInfrastructure,
                    "failed to snapshot the W-layer NameEnv revision",
                ))
            })?;
            (revision, sync)
        };
        let request = self.request(
            name_revision,
            WorkerOperation::EnsureWLayer,
            json!({ "index": index }),
        )?;
        let retained_response = self
            .inner
            .workers
            .execute_retained(
                admission,
                name_sync,
                self.proposal_sync_through(request.proposal_revision)?,
                base_sync,
                request.clone(),
                Arc::clone(&self.inner.next_request),
                cancellation,
            )
            .await?;
        let response = retained_response.response();
        if cancellation.is_cancelled() {
            return Err(retained_response.reject(EncodingError::Cancelled).await);
        }
        if let Err(error) = self.validate_response(&request, response) {
            return Err(retained_response.reject(error).await);
        }
        let payload: WireWLayerResponse = match serde_json::from_value(response.payload.clone()) {
            Ok(payload) => payload,
            Err(error) => {
                let error = EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::MalformedResponse,
                    format!("decode ensure_w_layer response: {error}"),
                ));
                return Err(retained_response.reject(error).await);
            }
        };
        let bundle =
            match self.validate_w_layer_response(index, response.name_env_revision, payload) {
                Ok(bundle) => Arc::new(bundle),
                Err(error) => return Err(retained_response.reject(error).await),
            };
        if cancellation.is_cancelled() {
            return Err(retained_response.reject(EncodingError::Cancelled).await);
        }
        let replay = WLayerReplay {
            index,
            expected_digest: Arc::from(canonical_value_sha256(&response.payload)),
        };
        let authority_error = {
            let mut authority = self
                .inner
                .w_layers
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner());
            if authority.bundles.len() != index_usize {
                Some(EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::SharedInfrastructure,
                    "W-layer authority changed before bundle publication",
                )))
            } else {
                authority.bundles.push(Arc::clone(&bundle));
                Arc::make_mut(&mut authority.replay).push(replay);
                None
            }
        };
        if let Some(error) = authority_error {
            return Err(retained_response.reject(error).await);
        }
        self.inner.body_cache.insert_ready_if_vacant(
            bundle.formula_body.source().key(),
            Arc::clone(&bundle.formula_body.0),
        );
        self.inner.body_cache.insert_ready_if_vacant(
            bundle.maintenance_wp_body.source().key(),
            Arc::clone(&bundle.maintenance_wp_body.0),
        );
        let _ = retained_response.accept();
        Ok(bundle)
    }

    async fn reject_proposal_response<T>(
        &self,
        response: RetainedWorkerResponse,
        error: EncodingError,
    ) -> Result<T, EncodingError> {
        // Retire only this exact child. Keep its slot unavailable until the
        // process tree and capture threads have stopped, then return the
        // original error unless cleanup itself failed.
        Err(response.reject(error).await)
    }

    fn discard_partial_reference_proposal(&self) {
        self.inner
            .proposals
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .discard_partial();
    }

    #[cfg(test)]
    pub(crate) fn inject_worker_cleanup_failure(&self, detail: &str) {
        self.inner.workers.inject_cleanup_failure(detail);
    }

    pub async fn prepare_solver_bodies(
        &self,
        admission: &SolverAdmission,
        artifacts: &ArtifactStore,
        sources: Vec<SolverBodySource>,
        cancellation: &CancellationToken,
    ) -> Result<Vec<PreparedBodyRef>, EncodingError> {
        self.validate_call_scope(artifacts)?;
        for source in &sources {
            self.validate_source(source)?;
        }
        self.bind_admission_authority(admission)?;
        if cancellation.is_cancelled() {
            return Err(EncodingError::Cancelled);
        }
        let mut tasks = JoinSet::new();
        let mut pending = sources.into_iter().enumerate();
        for (index, source) in pending.by_ref().take(self.inner.workers.capacity()) {
            let context = self.clone();
            let admission = admission.clone();
            let cancellation = cancellation.clone();
            tasks.spawn(async move {
                let body = context
                    .prepare_one_body(admission, source, &cancellation)
                    .await?;
                Ok::<_, EncodingError>((index, body))
            });
        }
        let mut bodies = Vec::new();
        let mut selected_error = None;
        while let Some(result) = tasks.join_next().await {
            match result {
                Ok(Ok(body)) => bodies.push(body),
                Ok(Err(error)) => {
                    retain_higher_precedence_error(&mut selected_error, error);
                }
                Err(error) => {
                    retain_higher_precedence_error(
                        &mut selected_error,
                        EncodingError::Failure(encoding_failure(
                            EncodingFailureClass::LocalInfrastructure,
                            format!("body preparation task failed: {error}"),
                        )),
                    );
                }
            }
            if selected_error.is_none()
                && let Some((index, source)) = pending.next()
            {
                let context = self.clone();
                let admission = admission.clone();
                let cancellation = cancellation.clone();
                tasks.spawn(async move {
                    let body = context
                        .prepare_one_body(admission, source, &cancellation)
                        .await?;
                    Ok::<_, EncodingError>((index, body))
                });
            }
        }
        if let Some(error) = selected_error {
            return Err(error);
        }
        bodies.sort_by_key(|(index, _)| *index);
        Ok(bodies.into_iter().map(|(_, body)| body).collect())
    }

    /// Prepare and cache the exact loop-guard body owned by this task.
    pub async fn prepare_loop_guard_body(
        &self,
        admission: &SolverAdmission,
        artifacts: &ArtifactStore,
        cancellation: &CancellationToken,
    ) -> Result<PreparedBodyRef, EncodingError> {
        self.prepare_fixed_task_body(
            admission,
            artifacts,
            self.task().loop_guard_solver().clone().into(),
            cancellation,
        )
        .await
    }

    /// Prepare and cache the exact negated-loop-guard body owned by this task.
    pub async fn prepare_negated_loop_guard_body(
        &self,
        admission: &SolverAdmission,
        artifacts: &ArtifactStore,
        cancellation: &CancellationToken,
    ) -> Result<PreparedBodyRef, EncodingError> {
        self.prepare_fixed_task_body(
            admission,
            artifacts,
            self.task().negated_loop_guard_solver().clone().into(),
            cancellation,
        )
        .await
    }

    async fn prepare_fixed_task_body(
        &self,
        admission: &SolverAdmission,
        artifacts: &ArtifactStore,
        source: SolverBodySource,
        cancellation: &CancellationToken,
    ) -> Result<PreparedBodyRef, EncodingError> {
        let mut bodies = self
            .prepare_solver_bodies(admission, artifacts, vec![source], cancellation)
            .await?;
        debug_assert_eq!(bodies.len(), 1);
        Ok(bodies.remove(0))
    }

    /// Compute and memoize the exact loop-body WP of one trusted QF source.
    ///
    /// Lean owns both WP construction and role-neutral rendering. Rust binds
    /// the response to the exact source, task, context, and NameEnv revision.
    pub(crate) async fn prepare_maintenance_wp(
        &self,
        admission: &SolverAdmission,
        artifacts: &ArtifactStore,
        source: SolverBodySource,
        cancellation: &CancellationToken,
    ) -> Result<PreparedBodyRef, EncodingError> {
        self.validate_call_scope(artifacts)?;
        self.validate_source(&source)?;
        if !matches!(source, SolverBodySource::QuantifierFree(_)) {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "maintenance WP preparation requires a quantifier-free source",
            )));
        }
        self.bind_admission_authority(admission)?;
        if cancellation.is_cancelled() {
            return Err(EncodingError::Cancelled);
        }
        let key = source.key();
        if let Some(value) = self.inner.maintenance_wp_cache.ready(&key) {
            return Ok(PreparedBodyRef(value));
        }
        let context = self.clone();
        let admission = admission.clone();
        let prepared = self
            .inner
            .maintenance_wp_cache
            .get_or_fill(
                key,
                cancellation,
                EncodingError::Cancelled,
                cache_producer_failure,
                cache_producer_error_is_sticky,
                move |fill_cancellation| async move {
                    context
                        .request_maintenance_wp(&admission, source, &fill_cancellation)
                        .await
                },
            )
            .await?;
        self.inner
            .body_cache
            .insert_ready_if_vacant(prepared.source.key(), Arc::clone(&prepared));
        Ok(PreparedBodyRef(prepared))
    }

    pub async fn prepare_support_block(
        &self,
        admission: &SolverAdmission,
        artifacts: &ArtifactStore,
        constants: impl IntoIterator<Item = ConstantKey>,
        cancellation: &CancellationToken,
    ) -> Result<SupportBlockRef, EncodingError> {
        self.validate_call_scope(artifacts)?;
        self.bind_admission_authority(admission)?;
        if cancellation.is_cancelled() {
            return Err(EncodingError::Cancelled);
        }
        let constants: BTreeSet<_> = constants.into_iter().collect();
        let key = SupportKey::new(constants.into_iter().collect::<Vec<_>>().into());
        if let Some(value) = self.inner.support_cache.ready(&key) {
            return Ok(SupportBlockRef(value));
        }
        let context = self.clone();
        let admission = admission.clone();
        let key_for_fill = key.clone();
        self.inner
            .support_cache
            .get_or_fill(
                key,
                cancellation,
                EncodingError::Cancelled,
                cache_producer_failure,
                cache_producer_error_is_sticky,
                move |fill_cancellation| async move {
                    context
                        .request_support(&admission, &key_for_fill.constants, &fill_cancellation)
                        .await
                },
            )
            .await
            .map(SupportBlockRef)
    }

    pub(crate) async fn check_empty_counterexample(
        &self,
        admission: &SolverAdmission,
        artifacts: &ArtifactStore,
        logical_identity: Arc<str>,
        axiom_bodies: &[PreparedBodyRef],
        goal_bodies: &[PreparedBodyRef],
        cancellation: &CancellationToken,
    ) -> Result<NativeEmptyCheck, EncodingError> {
        self.validate_call_scope(artifacts)?;
        self.validate_entailment_bodies(axiom_bodies, goal_bodies)?;
        self.bind_admission_authority(admission)?;
        if cancellation.is_cancelled() {
            return Err(EncodingError::Cancelled);
        }
        if let Some(value) = self.inner.empty_cache.ready(&logical_identity) {
            return Ok((*value).clone());
        }
        let context = self.clone();
        let admission = admission.clone();
        let artifacts = artifacts.clone();
        let key_for_fill = Arc::clone(&logical_identity);
        let axiom_source_ids: Arc<[Arc<str>]> = axiom_bodies
            .iter()
            .map(|body| Arc::from(body.source().source_id()))
            .collect::<Vec<_>>()
            .into();
        let goal_source_ids: Arc<[Arc<str>]> = goal_bodies
            .iter()
            .map(|body| Arc::from(body.source().source_id()))
            .collect::<Vec<_>>()
            .into();
        self.inner
            .empty_cache
            .get_or_fill(
                logical_identity,
                cancellation,
                EncodingError::Cancelled,
                cache_producer_failure,
                cache_producer_error_is_sticky,
                move |fill_cancellation| async move {
                    context
                        .request_empty_check(
                            &admission,
                            &artifacts,
                            key_for_fill,
                            axiom_source_ids,
                            goal_source_ids,
                            &fill_cancellation,
                        )
                        .await
                },
            )
            .await
            .map(|value| (*value).clone())
    }

    pub(crate) fn retained_proof(
        &self,
        logical_identity: &str,
        attempt: AttemptId,
    ) -> Option<VampireProof> {
        self.inner
            .proof_cache
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .get(&(Arc::from(logical_identity), attempt))
            .cloned()
    }

    pub(crate) fn retain_proof(
        &self,
        logical_identity: Arc<str>,
        attempt: AttemptId,
        proof: VampireProof,
    ) -> Result<VampireProof, EncodingError> {
        if proof.problem_identity() != logical_identity.as_ref() || proof.attempt_id() != attempt {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "Vampire proof identity or attempt differs from its encoding-context cache key",
            )));
        }
        let mut cache = self
            .inner
            .proof_cache
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let retained = cache
            .entry((logical_identity, attempt))
            .or_insert_with(|| proof.clone());
        if retained.output() != proof.output()
            || retained.query_artifact() != proof.query_artifact()
            || retained.szs_status() != proof.szs_status()
            || retained.strategy() != proof.strategy()
            || retained.invocation() != proof.invocation()
        {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "Vampire proof cache observed conflicting complete proofs for one attempt",
            )));
        }
        Ok(retained.clone())
    }

    pub(crate) fn retained_model(
        &self,
        logical_identity: &str,
        attempt: AttemptId,
    ) -> Option<VampireModel> {
        self.inner
            .model_cache
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .get(&(Arc::from(logical_identity), attempt))
            .cloned()
    }

    pub(crate) fn retain_model(
        &self,
        logical_identity: Arc<str>,
        attempt: AttemptId,
        model: VampireModel,
    ) -> Result<VampireModel, EncodingError> {
        if model.problem_identity() != logical_identity.as_ref() || model.attempt_id() != attempt {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "Vampire model identity differs from its encoding-context cache key",
            )));
        }
        let mut cache = self
            .inner
            .model_cache
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let retained = cache
            .entry((logical_identity, attempt))
            .or_insert_with(|| model.clone());
        if retained.output() != model.output()
            || retained.query_artifact() != model.query_artifact()
            || retained.szs_status() != model.szs_status()
        {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "Vampire model cache observed conflicting complete models for one attempt",
            )));
        }
        Ok(retained.clone())
    }

    pub async fn shutdown(&self) -> Result<(), EncodingError> {
        if self
            .inner
            .shutdown
            .started
            .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
            .is_ok()
        {
            let context = self.clone();
            let shutdown = Arc::clone(&self.inner.shutdown);
            tokio::spawn(async move {
                let cleanup = tokio::spawn(async move { context.perform_shutdown().await }).await;
                let result = match cleanup {
                    Ok(result) => result,
                    Err(error) => Err(EncodingError::Failure(encoding_failure(
                        EncodingFailureClass::SharedInfrastructure,
                        format!("solver encoding-context shutdown task failed: {error}"),
                    ))),
                };
                *shutdown
                    .result
                    .lock()
                    .unwrap_or_else(|poisoned| poisoned.into_inner()) = Some(result);
                shutdown.settled.notify_waiters();
            });
        }
        self.inner.shutdown.wait().await
    }

    async fn perform_shutdown(&self) -> Result<(), EncodingError> {
        let cpu_jobs = self.inner.cpu_jobs.shutdown().await;
        let (body_cache, maintenance_wp_cache, support_cache, empty_cache) = tokio::join!(
            self.inner.body_cache.shutdown(),
            self.inner.maintenance_wp_cache.shutdown(),
            self.inner.support_cache.shutdown(),
            self.inner.empty_cache.shutdown(),
        );
        // Keep the backend-owned work registration live after any worker-tree
        // cleanup failure. Artifact settlement then fails closed with a typed
        // run-global infrastructure report instead of publishing a run whose
        // subprocess ownership could not be verified.
        let workers = self.inner.workers.shutdown().await;
        cpu_jobs.map_err(|error| match error {
            CpuJobError::Failure(report) if report.scope() == FailureScope::RunGlobal => {
                EncodingError::Failure(report)
            }
            CpuJobError::Admission(crate::runtime::AdmissionError::Closed(report)) => {
                EncodingError::Failure(report)
            }
            error => EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                format!("retained CPU-job shutdown failed: {error}"),
            )),
        })?;
        body_cache?;
        maintenance_wp_cache?;
        support_cache?;
        empty_cache?;
        workers?;
        self.inner.owned_work.discharge();
        Ok(())
    }

    async fn prepare_one_body(
        &self,
        admission: SolverAdmission,
        source: SolverBodySource,
        cancellation: &CancellationToken,
    ) -> Result<PreparedBodyRef, EncodingError> {
        if cancellation.is_cancelled() {
            return Err(EncodingError::Cancelled);
        }
        self.validate_source(&source)?;
        let key = source.key();
        if let Some(value) = self.inner.body_cache.ready(&key) {
            return Ok(PreparedBodyRef(value));
        }
        let context = self.clone();
        self.inner
            .body_cache
            .get_or_fill(
                key,
                cancellation,
                EncodingError::Cancelled,
                cache_producer_failure,
                cache_producer_error_is_sticky,
                move |fill_cancellation| async move {
                    context
                        .request_body(&admission, source, &fill_cancellation)
                        .await
                },
            )
            .await
            .map(PreparedBodyRef)
    }

    async fn request_empty_check(
        &self,
        admission: &SolverAdmission,
        artifacts: &ArtifactStore,
        logical_identity: Arc<str>,
        axiom_source_ids: Arc<[Arc<str>]>,
        goal_source_ids: Arc<[Arc<str>]>,
        cancellation: &CancellationToken,
    ) -> Result<NativeEmptyCheck, EncodingError> {
        let (revision, sync) = {
            let names = self
                .inner
                .names
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner());
            let revision = names.revision();
            let sync = names.sync_through(revision).ok_or_else(|| {
                EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::SharedInfrastructure,
                    "failed to snapshot the empty-check NameEnv revision",
                ))
            })?;
            (revision, sync)
        };
        let request = self.request(
            revision,
            WorkerOperation::CheckEmptyCounterexample,
            json!({
                "axiom_source_ids": axiom_source_ids
                    .iter()
                    .map(AsRef::<str>::as_ref)
                    .collect::<Vec<_>>(),
                "goal_source_ids": goal_source_ids
                    .iter()
                    .map(AsRef::<str>::as_ref)
                    .collect::<Vec<_>>(),
            }),
        )?;
        let started = Instant::now();
        let response = self
            .inner
            .workers
            .execute(
                admission,
                sync,
                self.proposal_sync_through(request.proposal_revision)?,
                self.w_layer_sync_for_sources(&axiom_source_ids, &goal_source_ids),
                request.clone(),
                Arc::clone(&self.inner.next_request),
                cancellation,
            )
            .await?;
        let elapsed = started.elapsed();
        self.validate_response(&request, &response)?;
        if cancellation.is_cancelled() {
            return Err(EncodingError::Cancelled);
        }
        let payload: EmptyCheckResponse =
            serde_json::from_value(response.payload).map_err(|error| {
                EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::MalformedResponse,
                    format!("decode empty-counterexample response: {error}"),
                ))
            })?;
        let outcome =
            self.validate_empty_check_response(payload, &axiom_source_ids, &goal_source_ids)?;
        let evidence_payload = json!({
            "kind": "empty_instance_check",
            "entailment_identity": logical_identity.as_ref(),
            "axiom_source_ids": axiom_source_ids
                .iter()
                .map(AsRef::<str>::as_ref)
                .collect::<Vec<_>>(),
            "goal_source_ids": goal_source_ids
                .iter()
                .map(AsRef::<str>::as_ref)
                .collect::<Vec<_>>(),
            "elapsed_nanoseconds": elapsed.as_nanos().to_string(),
            "outcome": match &outcome {
                NativeEmptyOutcome::NoCounterexample => json!({
                    "status": "no_counterexample",
                }),
                NativeEmptyOutcome::Counterexample(assignment) => json!({
                    "status": "counterexample",
                    "nullary_assignment": assignment.iter().map(|entry| json!({
                        "relation_key": entry.relation_key.as_str(),
                        "value": entry.value,
                    })).collect::<Vec<_>>(),
                }),
            },
        });
        let evidence_bytes = evidence_payload.to_string().into_bytes();
        let evidence_digest = Arc::<str>::from(bytes_sha256(&evidence_bytes));
        let evidence = artifacts
            .scoped(ScopeTag::named("empty-instance-check"))
            .publish(
                ArtifactKind::EmptyInstanceCheck,
                evidence_bytes.into_boxed_slice(),
            )
            .map_err(|report| {
                EncodingError::Failure(FailureReport::encoding_preparation(
                    FailureKind::PublicationFailure,
                    report.scope(),
                    format!(
                        "publish empty-instance evidence: {}",
                        report.detail().unwrap_or("artifact backend failure")
                    ),
                ))
            })?;
        Ok(NativeEmptyCheck {
            outcome,
            evidence,
            evidence_digest,
            elapsed,
        })
    }

    async fn request_body(
        &self,
        admission: &SolverAdmission,
        source: SolverBodySource,
        cancellation: &CancellationToken,
    ) -> Result<PreparedBody, EncodingError> {
        let (revision, sync) = self.admit_source_names(&source)?;
        let exact_constant_keys = source
            .constants()
            .iter()
            .map(|key| key.as_str().to_string())
            .collect::<Vec<_>>();
        let request = self.request(
            revision,
            WorkerOperation::PrepareBodies,
            json!({
                "sources": [{
                    "source_id": source.source_id(),
                    "exact_constant_keys": exact_constant_keys,
                }],
            }),
        )?;
        let response = self
            .inner
            .workers
            .execute(
                admission,
                sync,
                self.proposal_sync_through(request.proposal_revision)?,
                self.w_layer_sync_for_source(&source),
                request.clone(),
                Arc::clone(&self.inner.next_request),
                cancellation,
            )
            .await?;
        self.validate_response(&request, &response)?;
        let payload: PrepareBodiesResponse =
            serde_json::from_value(response.payload).map_err(|error| {
                EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::MalformedResponse,
                    format!("decode prepare_bodies response: {error}"),
                ))
            })?;
        let [body]: [WirePreparedBody; 1] =
            payload.bodies.try_into().map_err(|bodies: Vec<_>| {
                EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::MalformedResponse,
                    format!(
                        "prepare_bodies returned {} bodies; expected one",
                        bodies.len()
                    ),
                ))
            })?;
        if body.source_id != source.source_id()
            || body.source_kind
                != match source {
                    SolverBodySource::Assert(_) => SourceKind::Assert,
                    SolverBodySource::QuantifierFree(_) => SourceKind::QuantifierFree,
                }
            || body.exact_constant_keys
                != exact_constant_keys.iter().cloned().collect::<BTreeSet<_>>()
        {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::MalformedResponse,
                "prepare_bodies returned a mismatched source or exact constant set",
            )));
        }
        self.validate_body_mappings(&source, &body)?;
        if body.body.is_empty() {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::MalformedResponse,
                "prepare_bodies returned an empty required field",
            )));
        }
        let body_id: Arc<str> = Arc::from(format!(
            "{}:{}:{}",
            self.inner.context_id,
            match &source {
                SolverBodySource::Assert(_) => "assert",
                SolverBodySource::QuantifierFree(_) => "qf",
            },
            source.source_id()
        ));
        let fol_identity: Arc<str> = Arc::from(source.source_id());
        Ok(PreparedBody {
            context_id: Arc::clone(&self.inner.context_id),
            semantic_version: self.inner.task.semantic_version(),
            encoding_version: self.inner.task.encoding_version(),
            constants: source.constants().to_vec().into(),
            source,
            body_id,
            fol_identity,
            tptp_body: Arc::from(body.body),
            preparation_revision: response.name_env_revision,
            theorem_id: Arc::from("Whiel.Vampire.TPTP.roleNeutralBody_stable"),
        })
    }

    async fn request_maintenance_wp(
        &self,
        admission: &SolverAdmission,
        source: SolverBodySource,
        cancellation: &CancellationToken,
    ) -> Result<PreparedBody, EncodingError> {
        let (revision, sync) = self.admit_source_names(&source)?;
        let derived_source_id = format!("{MAINTENANCE_WP_SOURCE_PREFIX}{}", source.source_id());
        let request = self.request(
            revision,
            WorkerOperation::PrepareMaintenanceWps,
            json!({ "source_ids": [source.source_id()] }),
        )?;
        let response = self
            .inner
            .workers
            .execute(
                admission,
                sync,
                self.proposal_sync_through(request.proposal_revision)?,
                self.w_layer_sync_for_source(&source),
                request.clone(),
                Arc::clone(&self.inner.next_request),
                cancellation,
            )
            .await?;
        self.validate_response(&request, &response)?;
        let payload: PrepareBodiesResponse =
            serde_json::from_value(response.payload).map_err(|error| {
                EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::MalformedResponse,
                    format!("decode prepare_maintenance_wps response: {error}"),
                ))
            })?;
        let [body]: [WirePreparedBody; 1] =
            payload.bodies.try_into().map_err(|bodies: Vec<_>| {
                EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::MalformedResponse,
                    format!(
                        "prepare_maintenance_wps returned {} bodies; expected one",
                        bodies.len()
                    ),
                ))
            })?;
        if body.source_id != derived_source_id
            || body.source_kind != SourceKind::QuantifierFree
            || body.body.is_empty()
        {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::MalformedResponse,
                "prepare_maintenance_wps returned a mismatched or empty body",
            )));
        }

        let constants = body
            .exact_constant_keys
            .iter()
            .map(|key| ConstantKey::from_canonical(key.clone()))
            .collect::<Result<Vec<_>, _>>()
            .map_err(|error| {
                EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::MalformedResponse,
                    format!("maintenance WP returned an invalid constant key: {error}"),
                ))
            })?;
        let mut relations = Vec::with_capacity(body.referenced_relations.len());
        for binding in &body.referenced_relations {
            let relation = self
                .inner
                .schema_relations
                .iter()
                .find(|relation| relation.as_str() == binding.key)
                .ok_or_else(|| {
                    EncodingError::Failure(encoding_failure(
                        EncodingFailureClass::MalformedResponse,
                        format!(
                            "maintenance WP returned unknown relation key {:?}",
                            binding.key
                        ),
                    ))
                })?;
            relations.push(relation.clone());
        }
        let derived_source = SolverBodySource::QuantifierFree(
            QfSolverSource::new_maintenance_wp(
                self.task(),
                Arc::<str>::from(derived_source_id.clone()),
                constants,
                relations,
            )
            .map_err(|detail| {
                EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::MalformedResponse,
                    format!("invalid maintenance-WP source: {detail}"),
                ))
            })?,
        );
        if body.exact_constant_keys
            != derived_source
                .constants()
                .iter()
                .map(|key| key.as_str().to_string())
                .collect::<BTreeSet<_>>()
        {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::MalformedResponse,
                "maintenance WP returned inconsistent exact constants",
            )));
        }
        self.validate_body_mappings(&derived_source, &body)?;

        Ok(PreparedBody {
            context_id: Arc::clone(&self.inner.context_id),
            semantic_version: self.inner.task.semantic_version(),
            encoding_version: self.inner.task.encoding_version(),
            constants: derived_source.constants().to_vec().into(),
            body_id: Arc::from(format!("{}:qf:{derived_source_id}", self.inner.context_id)),
            fol_identity: Arc::from(derived_source_id),
            source: derived_source,
            tptp_body: Arc::from(body.body),
            preparation_revision: response.name_env_revision,
            theorem_id: Arc::from(
                "Whiel.QFAssertExpr.wpLoopFree_eval_iff+Whiel.Vampire.TPTP.roleNeutralBody_stable",
            ),
        })
    }

    async fn request_support(
        &self,
        admission: &SolverAdmission,
        constants: &[ConstantKey],
        cancellation: &CancellationToken,
    ) -> Result<SupportBlock, EncodingError> {
        let (revision, sync) = {
            let mut names = self
                .inner
                .names
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner());
            let revision = names
                .extend([], constants.iter().cloned())
                .map_err(|error| EncodingError::Failure(unnameable_symbol(error)))?;
            let sync = names
                .sync_through(revision)
                .expect("current revision has a replay plan");
            (revision, sync)
        };
        let constant_keys: Vec<_> = constants
            .iter()
            .map(|key| key.as_str().to_string())
            .collect();
        let request = self.request(
            revision,
            WorkerOperation::PrepareSupport,
            json!({
                "constant_keys": constant_keys,
            }),
        )?;
        let response = self
            .inner
            .workers
            .execute(
                admission,
                sync,
                self.proposal_sync_through(request.proposal_revision)?,
                WLayerSync::empty(),
                request.clone(),
                Arc::clone(&self.inner.next_request),
                cancellation,
            )
            .await?;
        self.validate_response(&request, &response)?;
        let payload: PrepareSupportResponse =
            serde_json::from_value(response.payload).map_err(|error| {
                EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::MalformedResponse,
                    format!("decode prepare_support response: {error}"),
                ))
            })?;
        if payload.constant_keys
            != constants
                .iter()
                .map(|key| key.as_str().to_string())
                .collect::<BTreeSet<_>>()
        {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::MalformedResponse,
                "prepare_support returned a mismatched exact constant set",
            )));
        }
        self.validate_support_mappings(constants, &payload)?;
        if payload.adom_body.is_empty() || payload.distinct_bodies.iter().any(String::is_empty) {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::MalformedResponse,
                "prepare_support returned an empty required field",
            )));
        }
        let role_neutral_bodies: Arc<[Arc<str>]> = std::iter::once(payload.adom_body)
            .chain(payload.distinct_bodies)
            .map(Arc::from)
            .collect::<Vec<_>>()
            .into();
        let block_id: Arc<str> = Arc::from(format!(
            "{}:support:{}",
            self.inner.context_id,
            constants
                .iter()
                .map(|key| format!("{}:{}", key.as_str().len(), key.as_str()))
                .collect::<Vec<_>>()
                .concat()
        ));
        Ok(SupportBlock {
            context_id: Arc::clone(&self.inner.context_id),
            constant_keys: constants.to_vec().into(),
            block_id,
            role_neutral_bodies,
            preparation_revision: response.name_env_revision,
        })
    }

    fn admit_source_names(
        &self,
        source: &SolverBodySource,
    ) -> Result<(NameEnvRevision, NameEnvSync), EncodingError> {
        let mut names = self
            .inner
            .names
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let revision = names
            .extend(
                source.relations().iter().cloned(),
                source.constants().iter().cloned(),
            )
            .map_err(|error| EncodingError::Failure(unnameable_symbol(error)))?;
        let sync = names.sync_through(revision).ok_or_else(|| {
            EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "failed to snapshot the authoritative NameEnv revision",
            ))
        })?;
        Ok((revision, sync))
    }

    fn proposal_sync_through(
        &self,
        revision: ProposalRevision,
    ) -> Result<ProposalSync, EncodingError> {
        self.inner
            .proposals
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .sync_through(revision)
            .ok_or_else(|| {
                EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::SharedInfrastructure,
                    "failed to snapshot the requested proposal revision",
                ))
            })
    }

    fn w_layer_sync(&self) -> WLayerSync {
        self.inner
            .w_layers
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .sync()
    }

    fn w_layer_sync_for_source(&self, source: &SolverBodySource) -> WLayerSync {
        if source.source_id().starts_with(W_LAYER_SOURCE_PREFIX)
            || source.source_id().starts_with(W_LAYER_WP_SOURCE_PREFIX)
        {
            self.w_layer_sync()
        } else {
            WLayerSync::empty()
        }
    }

    fn w_layer_sync_for_sources(&self, axioms: &[Arc<str>], goals: &[Arc<str>]) -> WLayerSync {
        if axioms.iter().chain(goals).any(|source_id| {
            source_id.starts_with(W_LAYER_SOURCE_PREFIX)
                || source_id.starts_with(W_LAYER_WP_SOURCE_PREFIX)
        }) {
            self.w_layer_sync()
        } else {
            WLayerSync::empty()
        }
    }

    fn request(
        &self,
        revision: NameEnvRevision,
        operation: WorkerOperation,
        payload: serde_json::Value,
    ) -> Result<WorkerRequestEnvelope, EncodingError> {
        let request_id = self
            .inner
            .next_request
            .fetch_update(Ordering::AcqRel, Ordering::Acquire, |current| {
                current.checked_add(1)
            })
            .map_err(|_| {
                EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::SharedInfrastructure,
                    "encoding-worker request identity space exhausted",
                ))
            })?;
        Ok(WorkerRequestEnvelope {
            format_version: WORKER_FORMAT_VERSION,
            semantic_version: self.inner.task.semantic_version(),
            encoding_version: self.inner.task.encoding_version(),
            task_canonical_id: self.inner.task.canonical_id().to_string(),
            task_module: self.inner.task.module().to_string(),
            task_namespace: self.inner.task.namespace().to_string(),
            task_source_sha256: self.inner.task.source_digest().as_str().to_string(),
            request_id,
            context_id: self.inner.context_id.to_string(),
            name_env_revision: revision,
            proposal_revision: self
                .inner
                .proposals
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner())
                .revision(),
            operation,
            payload,
        })
    }

    fn validate_response(
        &self,
        request: &WorkerRequestEnvelope,
        response: &WorkerResponseEnvelope,
    ) -> Result<(), EncodingError> {
        if response.format_version != WORKER_FORMAT_VERSION
            || response.semantic_version != request.semantic_version
            || response.encoding_version != request.encoding_version
            || response.task_canonical_id != request.task_canonical_id
            || response.task_module != request.task_module
            || response.task_namespace != request.task_namespace
            || response.task_source_sha256 != request.task_source_sha256
            || response.request_id != request.request_id
            || response.context_id != request.context_id
            || response.operation != request.operation
        {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "encoding-worker response identity does not match its request",
            )));
        }
        let current_revision = self
            .inner
            .names
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .revision();
        if response.request_name_env_revision < request.name_env_revision
            || response.request_name_env_revision != response.name_env_revision
            || response.name_env_revision > current_revision
        {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "encoding-worker response conflicts with the task NameEnv authority",
            )));
        }
        let current_proposal_revision = self
            .inner
            .proposals
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .revision();
        validate_proposal_response_revisions(
            request.operation,
            response.status,
            request.proposal_revision,
            current_proposal_revision,
            response.request_proposal_revision,
            response.proposal_revision,
        )?;
        if response.status == WorkerResponseStatus::Error {
            let class = match response.error.as_ref().map(|error| error.kind.as_str()) {
                Some("invalid_envelope" | "name_env_extension") => {
                    EncodingFailureClass::SharedInfrastructure
                }
                Some("malformed_payload" | "unknown_operation") => {
                    EncodingFailureClass::ProtocolIncompatibility
                }
                Some("reference_proposal_response_budget") => {
                    EncodingFailureClass::LocalInfrastructure
                }
                _ => EncodingFailureClass::MalformedResponse,
            };
            let detail = response.error.as_ref().map_or_else(
                || "Lean encoding worker rejected the request".to_string(),
                |error| format!("{}: {}", error.kind, error.message),
            );
            return Err(EncodingError::Failure(encoding_failure(class, detail)));
        }
        if response.error.is_some() {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::MalformedResponse,
                "successful encoding-worker response contains an error object",
            )));
        }
        Ok(())
    }

    fn validate_source(&self, source: &SolverBodySource) -> Result<(), EncodingError> {
        if source.task_identity() != &self.inner.task {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "solver body source and encoding context task identities differ",
            )));
        }
        if matches!(source, SolverBodySource::Assert(_))
            && (source.source_id().starts_with(MAINTENANCE_WP_SOURCE_PREFIX)
                || source.source_id().starts_with(W_LAYER_SOURCE_PREFIX)
                || source.source_id().starts_with(W_LAYER_WP_SOURCE_PREFIX))
        {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "an Assert source cannot use a reserved derived-source namespace",
            )));
        }
        let schema: HashSet<_> = self.inner.schema_relations.iter().collect();
        if source
            .relations()
            .iter()
            .any(|relation| !schema.contains(relation))
        {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::MalformedResponse,
                "solver body source names a relation outside the task schema",
            )));
        }
        Ok(())
    }

    fn validate_reference_proposal(
        &self,
        wire_entries: Vec<WireReferenceProposalSource>,
    ) -> Result<Vec<ReferenceProposalSource>, EncodingError> {
        let mut source_ids = HashSet::with_capacity(wire_entries.len());
        let mut identities = HashSet::with_capacity(wire_entries.len());
        let mut entries = Vec::with_capacity(wire_entries.len());
        for entry in wire_entries {
            let identity = match &entry.identity {
                serde_json::Value::Array(parts) if !parts.is_empty() => {
                    serde_json::to_string(&entry.identity).map_err(|error| {
                        EncodingError::Failure(encoding_failure(
                            EncodingFailureClass::MalformedResponse,
                            format!("serialize reference-proposal identity: {error}"),
                        ))
                    })?
                }
                _ => {
                    return Err(EncodingError::Failure(encoding_failure(
                        EncodingFailureClass::MalformedResponse,
                        "reference proposal contains a non-structural identity",
                    )));
                }
            };
            if entry.source_id.is_empty()
                || entry.display.is_empty()
                || entry.source_id.starts_with(MAINTENANCE_WP_SOURCE_PREFIX)
                || entry.source_id.starts_with(W_LAYER_SOURCE_PREFIX)
                || entry.source_id.starts_with(W_LAYER_WP_SOURCE_PREFIX)
                || !source_ids.insert(entry.source_id.clone())
                || !identities.insert(identity.clone())
            {
                return Err(EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::MalformedResponse,
                    "reference proposal contains an empty, reserved, or duplicate identity",
                )));
            }
            let mut constants = Vec::with_capacity(entry.constants.len());
            for key in entry.constants {
                let key = ConstantKey::from_canonical(key).map_err(|error| {
                    EncodingError::Failure(encoding_failure(
                        EncodingFailureClass::MalformedResponse,
                        format!("reference proposal returned an invalid constant key: {error}"),
                    ))
                })?;
                if !self.inner.source_task.solver_constants().contains(&key) {
                    return Err(EncodingError::Failure(encoding_failure(
                        EncodingFailureClass::MalformedResponse,
                        "reference proposal returned a constant outside the task alphabet",
                    )));
                }
                constants.push(key);
            }
            let mut relations = Vec::with_capacity(entry.relations.len());
            for key in entry.relations {
                let relation = self
                    .inner
                    .schema_relations
                    .iter()
                    .find(|relation| relation.as_str() == key)
                    .cloned()
                    .ok_or_else(|| {
                        EncodingError::Failure(encoding_failure(
                            EncodingFailureClass::MalformedResponse,
                            format!("reference proposal returned unknown relation key {key:?}"),
                        ))
                    })?;
                relations.push(relation);
            }
            let source = QfSolverSource::new(
                self.task(),
                Arc::<str>::from(entry.source_id),
                constants,
                relations,
            )
            .map_err(|detail| {
                EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::MalformedResponse,
                    format!("reference proposal returned an invalid source: {detail}"),
                ))
            })?;
            entries.push(ReferenceProposalSource {
                identity: Arc::from(identity),
                display: Arc::from(entry.display),
                source,
            });
        }
        Ok(entries)
    }

    fn validate_w_layer_response(
        &self,
        expected_index: u64,
        revision: NameEnvRevision,
        response: WireWLayerResponse,
    ) -> Result<PreparedWLayerBundle, EncodingError> {
        if response.index != expected_index {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::MalformedResponse,
                "ensure_w_layer returned a different W index",
            )));
        }
        let formula_id = format!("{W_LAYER_SOURCE_PREFIX}{expected_index}");
        let wp_id = format!("{W_LAYER_WP_SOURCE_PREFIX}{expected_index}");
        let (identity, display, formula_source, formula_body) = self.validate_dynamic_w_source(
            &formula_id,
            W_LAYER_SOURCE_PREFIX,
            revision,
            response.formula,
            "Whiel.Vampire.TPTP.roleNeutralBody_stable",
        )?;
        let (_, _, maintenance_wp_source, maintenance_wp_body) = self.validate_dynamic_w_source(
            &wp_id,
            W_LAYER_WP_SOURCE_PREFIX,
            revision,
            response.maintenance_wp,
            "Whiel.QFAssertExpr.wpLoopFree_eval_iff+Whiel.Vampire.TPTP.roleNeutralBody_stable",
        )?;
        Ok(PreparedWLayerBundle {
            index: expected_index,
            identity,
            display,
            formula_source,
            formula_body,
            maintenance_wp_source,
            maintenance_wp_body,
        })
    }

    fn validate_dynamic_w_source(
        &self,
        expected_source_id: &str,
        expected_prefix: &str,
        revision: NameEnvRevision,
        wire: WireDynamicQfSource,
        theorem_id: &'static str,
    ) -> Result<(Arc<str>, Arc<str>, QfSolverSource, PreparedBodyRef), EncodingError> {
        let identity = match &wire.identity {
            serde_json::Value::Array(parts) if !parts.is_empty() => {
                serde_json::to_string(&wire.identity).map_err(|error| {
                    EncodingError::Failure(encoding_failure(
                        EncodingFailureClass::MalformedResponse,
                        format!("serialize W-layer structural identity: {error}"),
                    ))
                })?
            }
            _ => {
                return Err(EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::MalformedResponse,
                    "W-layer source contains a non-structural identity",
                )));
            }
        };
        if wire.source_id != expected_source_id || wire.display.is_empty() {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::MalformedResponse,
                "W-layer source contains an invalid identity or display",
            )));
        }
        let mut constants = Vec::with_capacity(wire.constants.len());
        let mut constant_set = HashSet::with_capacity(wire.constants.len());
        for raw in wire.constants {
            if !constant_set.insert(raw.clone()) {
                return Err(EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::MalformedResponse,
                    "W-layer source repeats an exact constant key",
                )));
            }
            let key = ConstantKey::from_canonical(raw).map_err(|error| {
                EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::MalformedResponse,
                    format!("W-layer source returned an invalid constant key: {error}"),
                ))
            })?;
            if !self.inner.source_task.solver_constants().contains(&key) {
                return Err(EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::MalformedResponse,
                    "W-layer source returned a constant outside the task alphabet",
                )));
            }
            constants.push(key);
        }
        let mut relations = Vec::with_capacity(wire.relations.len());
        let mut relation_set = HashSet::with_capacity(wire.relations.len());
        for raw in wire.relations {
            if !relation_set.insert(raw.clone()) {
                return Err(EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::MalformedResponse,
                    "W-layer source repeats a relation key",
                )));
            }
            let relation = self
                .inner
                .schema_relations
                .iter()
                .find(|relation| relation.as_str() == raw)
                .cloned()
                .ok_or_else(|| {
                    EncodingError::Failure(encoding_failure(
                        EncodingFailureClass::MalformedResponse,
                        format!("W-layer source returned unknown relation key {raw:?}"),
                    ))
                })?;
            relations.push(relation);
        }
        let source = QfSolverSource::new_w_layer_source(
            self.task(),
            Arc::<str>::from(wire.source_id),
            expected_prefix,
            constants,
            relations,
        )
        .map_err(|detail| {
            EncodingError::Failure(encoding_failure(
                EncodingFailureClass::MalformedResponse,
                format!("invalid W-layer source: {detail}"),
            ))
        })?;
        let source_wrapper = SolverBodySource::QuantifierFree(source.clone());
        let body = wire.prepared_body;
        if body.source_id != source.source_id()
            || body.source_kind != SourceKind::QuantifierFree
            || body.exact_constant_keys
                != source
                    .constants
                    .iter()
                    .map(|key| key.as_str().to_string())
                    .collect::<BTreeSet<_>>()
            || body.body.is_empty()
        {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::MalformedResponse,
                "W-layer prepared body conflicts with its exact source",
            )));
        }
        self.validate_body_mappings(&source_wrapper, &body)?;
        let prepared = PreparedBodyRef(Arc::new(PreparedBody {
            context_id: Arc::clone(&self.inner.context_id),
            semantic_version: self.inner.task.semantic_version(),
            encoding_version: self.inner.task.encoding_version(),
            constants: source.constants.to_vec().into(),
            body_id: Arc::from(format!(
                "{}:qf:{}",
                self.inner.context_id,
                source.source_id()
            )),
            fol_identity: Arc::from(source.source_id()),
            source: source_wrapper,
            tptp_body: Arc::from(body.body),
            preparation_revision: revision,
            theorem_id: Arc::from(theorem_id),
        }));
        Ok((
            Arc::from(identity),
            Arc::from(wire.display),
            source,
            prepared,
        ))
    }

    fn validate_reference_proposal_freshness(
        &self,
        entries: &[ReferenceProposalSource],
    ) -> Result<(), EncodingError> {
        let source_ids = self
            .inner
            .proposal_source_ids
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let identities = self
            .inner
            .proposal_identities
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        if entries.iter().any(|entry| {
            source_ids.contains(entry.source.source_id.as_ref())
                || identities.contains(entry.identity.as_ref())
        }) {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::MalformedResponse,
                "reference proposal repeats a source or formula from an earlier wave",
            )));
        }
        Ok(())
    }

    fn record_reference_proposal_identities(&self, entries: &[ReferenceProposalSource]) {
        let mut source_ids = self
            .inner
            .proposal_source_ids
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let mut identities = self
            .inner
            .proposal_identities
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        for entry in entries {
            let inserted_source = source_ids.insert(Arc::clone(&entry.source.source_id));
            let inserted_identity = identities.insert(Arc::clone(&entry.identity));
            debug_assert!(inserted_source && inserted_identity);
        }
    }

    fn validate_entailment_bodies(
        &self,
        axiom_bodies: &[PreparedBodyRef],
        goal_bodies: &[PreparedBodyRef],
    ) -> Result<(), EncodingError> {
        if goal_bodies.is_empty() {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::MalformedResponse,
                "an entailment requires at least one goal body",
            )));
        }
        for body in axiom_bodies.iter().chain(goal_bodies) {
            if body.context_id() != self.context_id()
                || body.semantic_version() != self.inner.task.semantic_version()
                || body.encoding_version() != self.inner.task.encoding_version()
                || body.source().task_identity() != &self.inner.task
            {
                return Err(EncodingError::Failure(encoding_failure(
                    EncodingFailureClass::SharedInfrastructure,
                    "prepared entailment body belongs to another task or encoding context",
                )));
            }
        }
        Ok(())
    }

    fn validate_empty_check_response(
        &self,
        response: EmptyCheckResponse,
        axiom_source_ids: &[Arc<str>],
        goal_source_ids: &[Arc<str>],
    ) -> Result<NativeEmptyOutcome, EncodingError> {
        if response.axiom_source_ids
            != axiom_source_ids
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
            || response.goal_source_ids
                != goal_source_ids
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
        {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::MalformedResponse,
                "empty-check response changed its ordered source identity",
            )));
        }
        match response.outcome.as_str() {
            "no_counterexample" => {
                if !response.nullary_assignment.is_empty() {
                    return Err(EncodingError::Failure(encoding_failure(
                        EncodingFailureClass::MalformedResponse,
                        "no-counterexample response contains a nullary assignment",
                    )));
                }
                Ok(NativeEmptyOutcome::NoCounterexample)
            }
            "counterexample" => {
                let expected: BTreeSet<_> = self
                    .inner
                    .schema_arities
                    .iter()
                    .filter_map(|(key, arity)| (*arity == 0).then_some(key.as_str()))
                    .collect();
                let received: BTreeSet<_> = response
                    .nullary_assignment
                    .iter()
                    .map(|entry| entry.relation_key.as_str())
                    .collect();
                if received.len() != response.nullary_assignment.len() || received != expected {
                    return Err(EncodingError::Failure(encoding_failure(
                        EncodingFailureClass::MalformedResponse,
                        "empty-counterexample response has an incomplete or duplicate nullary assignment",
                    )));
                }
                let assignment = response
                    .nullary_assignment
                    .into_iter()
                    .map(|entry| {
                        let key = self
                            .inner
                            .schema_arities
                            .keys()
                            .find(|key| key.as_str() == entry.relation_key)
                            .expect("the exact received key set was validated")
                            .clone();
                        NullaryAssignmentValue {
                            relation_key: key,
                            value: entry.value,
                        }
                    })
                    .collect::<Vec<_>>();
                Ok(NativeEmptyOutcome::Counterexample(assignment.into()))
            }
            _ => Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::MalformedResponse,
                "empty-counterexample response has an unknown outcome",
            ))),
        }
    }

    fn validate_body_mappings(
        &self,
        source: &SolverBodySource,
        body: &WirePreparedBody,
    ) -> Result<(), EncodingError> {
        self.validate_mapping_echoes(
            source.relations().iter().map(RelationKey::as_str),
            source.constants().iter().map(ConstantKey::as_str),
            &body.referenced_relations,
            &body.referenced_constants,
        )
    }

    fn validate_support_mappings(
        &self,
        constants: &[ConstantKey],
        support: &PrepareSupportResponse,
    ) -> Result<(), EncodingError> {
        self.validate_mapping_echoes(
            self.inner.schema_relations.iter().map(RelationKey::as_str),
            constants.iter().map(ConstantKey::as_str),
            &support.referenced_relations,
            &support.referenced_constants,
        )
    }

    fn validate_mapping_echoes<'a>(
        &self,
        relation_keys: impl IntoIterator<Item = &'a str>,
        constant_keys: impl IntoIterator<Item = &'a str>,
        relation_echoes: &[NameBinding],
        constant_echoes: &[NameBinding],
    ) -> Result<(), EncodingError> {
        let relation_keys = relation_keys.into_iter().collect::<BTreeSet<_>>();
        let constant_keys = constant_keys.into_iter().collect::<BTreeSet<_>>();
        let echoed_relation_keys = relation_echoes
            .iter()
            .map(|binding| binding.key.as_str())
            .collect::<BTreeSet<_>>();
        let echoed_constant_keys = constant_echoes
            .iter()
            .map(|binding| binding.key.as_str())
            .collect::<BTreeSet<_>>();
        if relation_echoes.len() != echoed_relation_keys.len()
            || constant_echoes.len() != echoed_constant_keys.len()
            || relation_keys != echoed_relation_keys
            || constant_keys != echoed_constant_keys
        {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::MalformedResponse,
                format!(
                    "encoding-worker symbol mappings differ: expected relations={relation_keys:?} constants={constant_keys:?}; received relations={echoed_relation_keys:?} constants={echoed_constant_keys:?}"
                ),
            )));
        }
        let echoed = relation_echoes
            .iter()
            .map(|binding| NameMapping {
                kind: NameMappingKind::Relation,
                key: binding.key.clone(),
                tptp_name: binding.name.clone(),
            })
            .chain(constant_echoes.iter().map(|binding| NameMapping {
                kind: NameMappingKind::Constant,
                key: binding.key.clone(),
                tptp_name: binding.name.clone(),
            }))
            .collect::<Vec<_>>();
        let names = self
            .inner
            .names
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        if !names.agrees_with(&echoed) {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "encoding-worker response conflicts with the task NameEnv authority",
            )));
        }
        Ok(())
    }

    fn validate_call_scope(&self, artifacts: &ArtifactStore) -> Result<(), EncodingError> {
        if artifacts.task_identity() != &self.inner.task
            || artifacts.backend_id() != self.inner.artifacts.backend_id()
        {
            return Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "encoding context and caller artifact scope differ",
            )));
        }
        Ok(())
    }

    fn bind_admission_authority(&self, admission: &SolverAdmission) -> Result<(), EncodingError> {
        let mut authority = self
            .inner
            .admission_authority
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        match authority.as_ref() {
            None => {
                *authority = Some(admission.clone());
                Ok(())
            }
            Some(bound) if bound.shares_controller_with(admission) => Ok(()),
            Some(_) => Err(EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "solver encoding context received an unrelated admission authority",
            ))),
        }
    }
}

fn encoding_error_precedence(error: &EncodingError) -> u8 {
    match error {
        EncodingError::Cancelled => 0,
        EncodingError::Failure(report) if report.scope() == FailureScope::LaneLocal => 1,
        EncodingError::Failure(_) => 2,
    }
}

fn retain_higher_precedence_error(selected: &mut Option<EncodingError>, candidate: EncodingError) {
    let replace = selected.as_ref().is_none_or(|current| {
        encoding_error_precedence(&candidate) > encoding_error_precedence(current)
    });
    if replace {
        *selected = Some(candidate);
    }
}

impl ContextShutdown {
    async fn wait(&self) -> Result<(), EncodingError> {
        loop {
            let notified = self.settled.notified();
            tokio::pin!(notified);
            notified.as_mut().enable();
            if let Some(result) = self
                .result
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner())
                .clone()
            {
                return result;
            }
            notified.await;
        }
    }
}

fn validate_proposal_response_revisions(
    operation: WorkerOperation,
    status: WorkerResponseStatus,
    request_revision: ProposalRevision,
    authority_revision: ProposalRevision,
    response_request_revision: ProposalRevision,
    response_revision: ProposalRevision,
) -> Result<(), EncodingError> {
    let valid = if operation == WorkerOperation::RegisterReferenceProposal {
        authority_revision == request_revision
            && if status == WorkerResponseStatus::Ok {
                let successor = request_revision.successor().ok_or_else(|| {
                    EncodingError::Failure(encoding_failure(
                        EncodingFailureClass::SharedInfrastructure,
                        "proposal revision space exhausted",
                    ))
                })?;
                response_request_revision == request_revision
                    && (response_revision == request_revision || response_revision == successor)
            } else {
                response_request_revision == request_revision
                    && response_revision == request_revision
            }
    } else {
        request_revision <= response_request_revision
            && response_request_revision == response_revision
            && response_revision <= authority_revision
    };
    if valid {
        Ok(())
    } else {
        Err(EncodingError::Failure(encoding_failure(
            EncodingFailureClass::SharedInfrastructure,
            "encoding-worker response conflicts with the proposal authority",
        )))
    }
}

fn validate_reference_proposal_page(
    expected_realization: ProposalRealization,
    expected_stage: u64,
    expected_cursor: u64,
    base_revision: ProposalRevision,
    response_revision: ProposalRevision,
    response: &ReferenceProposalPageResponse,
) -> Result<(), EncodingError> {
    let Some(
        [
            generator_work_units,
            fresh_traversal_nodes,
            fresh_no_fresh_prunes,
            fresh_too_short_prunes,
        ],
    ) = response.work_metrics(expected_realization)
    else {
        return Err(EncodingError::Failure(encoding_failure(
            EncodingFailureClass::MalformedResponse,
            "reference-proposal work metadata does not match its realization",
        )));
    };
    let fragment_length = u64::try_from(response.fragment.chars().count()).map_err(|_| {
        EncodingError::Failure(encoding_failure(
            EncodingFailureClass::MalformedResponse,
            "reference-proposal fragment length does not fit its cursor",
        ))
    })?;
    let expected_next_cursor = expected_cursor
        .checked_add(fragment_length)
        .ok_or_else(|| {
            EncodingError::Failure(encoding_failure(
                EncodingFailureClass::MalformedResponse,
                "reference-proposal cursor space exhausted",
            ))
        })?;
    let expected_revision = if response.complete {
        base_revision.successor().ok_or_else(|| {
            EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "proposal revision space exhausted",
            ))
        })?
    } else {
        base_revision
    };
    if response.realization_id != expected_realization.realization_id()
        || response.realization_version != expected_realization.realization_version()
        || response.version != PROPOSAL_PAGE_PROTOCOL_VERSION
        || response.stage != expected_stage
        || response.cursor != expected_cursor
        || response.next_cursor != expected_next_cursor
        || response_revision != expected_revision
        || response.equality_distinct_formulas > response.decoded_formula_occurrences
        || response.equality_deduplicated_occurrences
            != response.decoded_formula_occurrences - response.equality_distinct_formulas
        || response.emitted_formulas > response.equality_distinct_formulas
        || fresh_no_fresh_prunes > fresh_traversal_nodes
        || fresh_too_short_prunes > fresh_traversal_nodes
        || fresh_no_fresh_prunes.saturating_add(fresh_too_short_prunes) > fresh_traversal_nodes
        || generator_work_units < fresh_traversal_nodes
        || (!response.complete && response.fragment.is_empty())
    {
        return Err(EncodingError::Failure(encoding_failure(
            EncodingFailureClass::MalformedResponse,
            "reference-proposal page metadata is inconsistent",
        )));
    }
    Ok(())
}

// ------------------------------------------------------------
// Cache And Wire Records
// ------------------------------------------------------------

#[derive(Deserialize)]
struct ReferenceProposalPageResponse {
    realization_id: String,
    realization_version: u64,
    version: u64,
    stage: u64,
    cursor: u64,
    next_cursor: u64,
    complete: bool,
    #[serde(rename = "raw_occurrences")]
    decoded_formula_occurrences: u64,
    #[serde(rename = "canonical_formulas")]
    equality_distinct_formulas: u64,
    #[serde(rename = "canonical_duplicates")]
    equality_deduplicated_occurrences: u64,
    emitted_formulas: u64,
    #[serde(default)]
    fast_work: Option<[u64; 4]>,
    fragment: String,
}

impl ReferenceProposalPageResponse {
    fn work_metrics(&self, realization: ProposalRealization) -> Option<[u64; 4]> {
        match (realization, self.fast_work) {
            (ProposalRealization::ReferenceV3, None) => Some([0; 4]),
            (ProposalRealization::FastV1, Some(metrics)) => Some(metrics),
            (ProposalRealization::SeededV1, Some(metrics)) => Some(metrics),
            (ProposalRealization::CappedV1, Some(metrics)) => Some(metrics),
            _ => None,
        }
    }
}

#[derive(Deserialize)]
struct WireReferenceProposalSource {
    source_id: String,
    identity: serde_json::Value,
    display: String,
    constants: Vec<String>,
    relations: Vec<String>,
}

#[derive(Deserialize)]
struct WireWLayerResponse {
    index: u64,
    formula: WireDynamicQfSource,
    maintenance_wp: WireDynamicQfSource,
}

#[derive(Deserialize)]
struct WireDynamicQfSource {
    source_id: String,
    identity: serde_json::Value,
    display: String,
    constants: Vec<String>,
    relations: Vec<String>,
    prepared_body: WirePreparedBody,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
enum SourceKind {
    Assert,
    QuantifierFree,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct BodyCacheKey {
    kind: SourceKind,
    source_id: Arc<str>,
    constants: Arc<[ConstantKey]>,
    relations: Arc<[RelationKey]>,
}

#[derive(Clone, Debug, Eq)]
struct SupportKey {
    constants: Arc<[ConstantKey]>,
    digest: u64,
}

impl SupportKey {
    fn new(constants: Arc<[ConstantKey]>) -> Self {
        let mut hasher = DefaultHasher::new();
        constants.hash(&mut hasher);
        Self {
            constants,
            digest: hasher.finish(),
        }
    }
}

impl PartialEq for SupportKey {
    fn eq(&self, other: &Self) -> bool {
        self.constants == other.constants
    }
}

impl Hash for SupportKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.digest.hash(state);
    }
}

#[derive(Deserialize)]
struct PrepareBodiesResponse {
    bodies: Vec<WirePreparedBody>,
}

#[derive(Deserialize)]
struct WirePreparedBody {
    source_id: String,
    source_kind: SourceKind,
    exact_constant_keys: BTreeSet<String>,
    body: String,
    referenced_relations: Vec<NameBinding>,
    referenced_constants: Vec<NameBinding>,
}

#[derive(Deserialize)]
struct PrepareSupportResponse {
    constant_keys: BTreeSet<String>,
    adom_body: String,
    distinct_bodies: Vec<String>,
    referenced_relations: Vec<NameBinding>,
    referenced_constants: Vec<NameBinding>,
}

#[derive(Deserialize)]
struct EmptyCheckResponse {
    outcome: String,
    axiom_source_ids: Vec<String>,
    goal_source_ids: Vec<String>,
    #[serde(default)]
    nullary_assignment: Vec<WireNullaryAssignment>,
}

#[derive(Deserialize)]
struct WireNullaryAssignment {
    relation_key: String,
    value: bool,
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum EncodingFailureClass {
    MalformedResponse,
    ProtocolIncompatibility,
    Process,
    // Current in-memory cache publication is infallible. Keep the approved
    // classification explicit for a future fallible publication backend.
    #[allow(dead_code)]
    LocalPublication,
    #[allow(dead_code)]
    SharedPublication,
    LocalInfrastructure,
    SharedInfrastructure,
}

/// Report one wire key the shared naming function cannot name.
///
/// Naming is a total function of the key, so this is a defect of the key
/// itself rather than of any solver run: the environment is left untouched
/// and no symbol is renamed around the failure.
pub(crate) fn unnameable_symbol(error: SolverNameError) -> FailureReport {
    encoding_failure(
        EncodingFailureClass::SharedInfrastructure,
        error.to_string(),
    )
}

pub(crate) fn encoding_failure(
    class: EncodingFailureClass,
    detail: impl Into<String>,
) -> FailureReport {
    let (kind, scope) = match class {
        EncodingFailureClass::MalformedResponse => {
            (FailureKind::MalformedResult, FailureScope::LaneLocal)
        }
        EncodingFailureClass::ProtocolIncompatibility => {
            (FailureKind::MalformedResult, FailureScope::RunGlobal)
        }
        EncodingFailureClass::Process => (FailureKind::ProcessFailure, FailureScope::LaneLocal),
        EncodingFailureClass::LocalPublication => {
            (FailureKind::PublicationFailure, FailureScope::LaneLocal)
        }
        EncodingFailureClass::SharedPublication => {
            (FailureKind::PublicationFailure, FailureScope::RunGlobal)
        }
        EncodingFailureClass::LocalInfrastructure => {
            (FailureKind::InfrastructureFailure, FailureScope::LaneLocal)
        }
        EncodingFailureClass::SharedInfrastructure => {
            (FailureKind::InfrastructureFailure, FailureScope::RunGlobal)
        }
    };
    FailureReport::encoding_preparation(kind, scope, detail)
}

fn cache_producer_failure(error: JoinError) -> EncodingError {
    EncodingError::Failure(encoding_failure(
        EncodingFailureClass::SharedInfrastructure,
        format!("solver encoding cache producer task failed: {error}"),
    ))
}

fn cache_producer_error_is_sticky(error: &EncodingError) -> bool {
    matches!(
        error,
        EncodingError::Failure(report) if report.scope() == FailureScope::RunGlobal
    )
}

#[cfg(test)]
mod failure_tests {
    use super::*;
    use crate::failure::FailureOrigin;

    #[test]
    fn only_evaluation_instance_admission_is_a_caller_input_error() {
        let error = FixedAmbientWorkerResponseError {
            kind: "instance_admission".into(),
            message: "missing relation o:p::R".into(),
        };
        let classified =
            fixed_ambient_worker_error(FixedAmbientWorkerOperation::EvaluateClauses, Some(&error));
        assert!(matches!(
            &classified,
            FixedAmbientEvaluationError::InvalidInstance(message)
                if message == "missing relation o:p::R"
        ));

        // The ordinary execute entry point retains its former classification,
        // even if an internal caller selects EvaluateClauses there.
        let EncodingError::Failure(report) = classified.into_encoding() else {
            panic!("ordinary execution must preserve the worker failure");
        };
        assert_eq!(report.kind(), FailureKind::MalformedResult);
        assert_eq!(report.scope(), FailureScope::LaneLocal);
        assert_eq!(
            report.detail(),
            Some("instance_admission: missing relation o:p::R")
        );

        for operation in [
            FixedAmbientWorkerOperation::AdmitClauses,
            FixedAmbientWorkerOperation::ValidateRefutation,
            FixedAmbientWorkerOperation::ValidateCounterexample,
            FixedAmbientWorkerOperation::Describe,
        ] {
            let FixedAmbientEvaluationError::Encoding(EncodingError::Failure(report)) =
                fixed_ambient_worker_error(operation, Some(&error))
            else {
                panic!("only EvaluateClauses may produce InvalidInstance");
            };
            assert_eq!(report.kind(), FailureKind::MalformedResult);
            assert_eq!(report.scope(), FailureScope::LaneLocal);
            assert_eq!(
                report.detail(),
                Some("instance_admission: missing relation o:p::R")
            );
        }
    }

    #[test]
    fn evaluation_preserves_other_worker_failure_classifications() {
        for (kind, expected_kind, expected_scope) in [
            (
                "invalid_envelope",
                FailureKind::InfrastructureFailure,
                FailureScope::RunGlobal,
            ),
            (
                "name_environment",
                FailureKind::InfrastructureFailure,
                FailureScope::RunGlobal,
            ),
            (
                "malformed_payload",
                FailureKind::MalformedResult,
                FailureScope::RunGlobal,
            ),
            (
                "unknown_operation",
                FailureKind::MalformedResult,
                FailureScope::RunGlobal,
            ),
            (
                "clause_admission",
                FailureKind::MalformedResult,
                FailureScope::LaneLocal,
            ),
            (
                "instance_admission_extra",
                FailureKind::MalformedResult,
                FailureScope::LaneLocal,
            ),
        ] {
            // This text must never turn an infrastructure failure into bad input.
            let error = FixedAmbientWorkerResponseError {
                kind: kind.into(),
                message: "instance_admission: misleading diagnostic text".into(),
            };
            let FixedAmbientEvaluationError::Encoding(EncodingError::Failure(report)) =
                fixed_ambient_worker_error(
                    FixedAmbientWorkerOperation::EvaluateClauses,
                    Some(&error),
                )
            else {
                panic!("unexpected caller input classification for {kind}");
            };
            assert_eq!(report.kind(), expected_kind);
            assert_eq!(report.scope(), expected_scope);
            assert_eq!(
                report.detail(),
                Some(format!("{kind}: {}", error.message).as_str())
            );
        }
        let FixedAmbientEvaluationError::Encoding(EncodingError::Failure(report)) =
            fixed_ambient_worker_error(FixedAmbientWorkerOperation::EvaluateClauses, None)
        else {
            panic!("missing error envelope remains a worker failure");
        };
        assert_eq!(report.kind(), FailureKind::MalformedResult);
        assert_eq!(report.scope(), FailureScope::LaneLocal);
        assert_eq!(
            report.detail(),
            Some("fixed-ambient worker rejected the request")
        );
    }

    fn fixed_ambient_context() -> (FixedAmbientEncodingContext, RelationKey) {
        let task = super::super::names::sample_task_for_encoding_tests();
        let relation = RelationKey::from_lean_scope("y:p::R").unwrap();
        let binding = FixedAmbientWorkerBinding::for_test(
            task.identity().clone(),
            serde_json::json!({
                "kind":"whiel_framework_ii_fixed_ambient_task",
                "version":2,
                "ambient_scope":["complete"]
            }),
        );
        let config = FixedAmbientWorkerPoolConfig::new(
            super::super::worker::FixedAmbientWorkerCommand::new("/bin/true", "/"),
            1,
        )
        .unwrap();
        let context =
            new_fixed_ambient_encoding_context(binding, [relation.clone()], [], config).unwrap();
        (context, relation)
    }

    #[test]
    fn fixed_ambient_context_retains_opaque_relation_identity() {
        let (context, relation) = fixed_ambient_context();
        assert_eq!(context.task_identity().canonical_id(), "EncodingNames");
        assert_eq!(
            context.scope_identity()["kind"],
            serde_json::json!("whiel_framework_ii_fixed_ambient_task")
        );
        let (revision, mappings) = context.name_snapshot([relation], []).unwrap();
        assert_eq!(revision, NameEnvRevision::from_raw(1));
        assert_eq!(mappings[0].key, "y:p::R");
        assert_eq!(mappings[0].tptp_name, "yp_zR");

        let escaped = RelationKey::from_lean_scope("o:p::R").unwrap();
        assert!(context.extend_name_env([escaped], []).is_err());
    }

    #[test]
    fn fixed_ambient_adoption_checks_exact_name_echoes() {
        let (context, relation) = fixed_ambient_context();
        let revision = context.name_env().revision();
        let body = context
            .adopt_body(
                FixedAmbientPreparedBodyData {
                    source_id: "fixed.body".to_string(),
                    source_kind: "quantifier_free".to_string(),
                    exact_constant_keys: BTreeSet::new(),
                    body: "![X] : p(X)".to_string(),
                    referenced_relations: vec![FixedAmbientNameBinding {
                        key: relation.as_str().to_string(),
                        name: "yp_zR".to_string(),
                    }],
                    referenced_constants: Vec::new(),
                },
                revision,
            )
            .unwrap();
        assert_eq!(body.source().relations(), std::slice::from_ref(&relation));
        assert_eq!(body.tptp_body(), "![X] : p(X)");

        let wrong = FixedAmbientPreparedBodyData {
            source_id: "fixed.body.2".to_string(),
            source_kind: "quantifier_free".to_string(),
            exact_constant_keys: BTreeSet::new(),
            body: "![X] : p(X)".to_string(),
            referenced_relations: vec![FixedAmbientNameBinding {
                key: relation.as_str().to_string(),
                name: "wrong".to_string(),
            }],
            referenced_constants: Vec::new(),
        };
        assert!(context.adopt_body(wrong, revision).is_err());
    }

    #[test]
    fn proposal_response_revisions_accept_an_authoritative_append_only_extension() {
        let request = ProposalRevision::from_raw(1);
        let current = ProposalRevision::from_raw(3);
        assert!(
            validate_proposal_response_revisions(
                WorkerOperation::PrepareBodies,
                WorkerResponseStatus::Ok,
                request,
                current,
                current,
                current,
            )
            .is_ok()
        );

        for (response_request, response) in [
            (ProposalRevision::INITIAL, ProposalRevision::INITIAL),
            (ProposalRevision::from_raw(2), ProposalRevision::from_raw(3)),
            (ProposalRevision::from_raw(4), ProposalRevision::from_raw(4)),
        ] {
            assert!(
                validate_proposal_response_revisions(
                    WorkerOperation::PrepareBodies,
                    WorkerResponseStatus::Ok,
                    request,
                    current,
                    response_request,
                    response,
                )
                .is_err()
            );
        }
    }

    #[test]
    fn proposal_registration_keeps_exact_base_and_page_completion_rules() {
        let base = ProposalRevision::from_raw(2);
        let successor = ProposalRevision::from_raw(3);
        assert!(
            validate_proposal_response_revisions(
                WorkerOperation::RegisterReferenceProposal,
                WorkerResponseStatus::Ok,
                base,
                base,
                base,
                successor,
            )
            .is_ok()
        );
        assert!(
            validate_proposal_response_revisions(
                WorkerOperation::RegisterReferenceProposal,
                WorkerResponseStatus::Ok,
                base,
                base,
                base,
                base,
            )
            .is_ok()
        );
        assert!(
            validate_proposal_response_revisions(
                WorkerOperation::RegisterReferenceProposal,
                WorkerResponseStatus::Error,
                base,
                base,
                base,
                base,
            )
            .is_ok()
        );
        assert!(
            validate_proposal_response_revisions(
                WorkerOperation::RegisterReferenceProposal,
                WorkerResponseStatus::Ok,
                base,
                successor,
                successor,
                successor,
            )
            .is_err()
        );
        assert!(
            validate_proposal_response_revisions(
                WorkerOperation::RegisterReferenceProposal,
                WorkerResponseStatus::Ok,
                base,
                successor,
                base,
                base,
            )
            .is_err()
        );
        assert!(
            validate_proposal_response_revisions(
                WorkerOperation::RegisterReferenceProposal,
                WorkerResponseStatus::Ok,
                base,
                successor,
                successor,
                successor,
            )
            .is_err()
        );
    }

    #[test]
    fn publication_classification_distinguishes_local_and_shared_cache_safety() {
        let local = encoding_failure(
            EncodingFailureClass::LocalPublication,
            "one cache value was not published",
        );
        assert_eq!(local.kind(), FailureKind::PublicationFailure);
        assert_eq!(local.scope(), FailureScope::LaneLocal);

        let shared = encoding_failure(
            EncodingFailureClass::SharedPublication,
            "the shared cache cannot publish future values safely",
        );
        assert_eq!(shared.kind(), FailureKind::PublicationFailure);
        assert_eq!(shared.scope(), FailureScope::RunGlobal);
    }

    #[test]
    fn only_run_global_producer_errors_are_sticky() {
        let local = EncodingError::Failure(encoding_failure(
            EncodingFailureClass::LocalInfrastructure,
            "lane-local producer error",
        ));
        let global = EncodingError::Failure(encoding_failure(
            EncodingFailureClass::SharedInfrastructure,
            "run-global producer error",
        ));

        assert!(!cache_producer_error_is_sticky(&EncodingError::Cancelled));
        assert!(!cache_producer_error_is_sticky(&local));
        assert!(cache_producer_error_is_sticky(&global));
    }

    #[test]
    fn body_batch_error_precedence_is_independent_of_completion_order() {
        let errors = [
            EncodingError::Cancelled,
            EncodingError::Failure(encoding_failure(
                EncodingFailureClass::LocalInfrastructure,
                "lane-local failure",
            )),
            EncodingError::Failure(encoding_failure(
                EncodingFailureClass::SharedInfrastructure,
                "run-global failure",
            )),
        ];
        for order in [
            [0, 1, 2],
            [0, 2, 1],
            [1, 0, 2],
            [1, 2, 0],
            [2, 0, 1],
            [2, 1, 0],
        ] {
            let mut selected = None;
            for index in order {
                retain_higher_precedence_error(&mut selected, errors[index].clone());
            }
            let Some(EncodingError::Failure(report)) = selected else {
                panic!("run-global failure must dominate every completion order")
            };
            assert_eq!(report.scope(), FailureScope::RunGlobal);
        }

        let mut without_global = None;
        retain_higher_precedence_error(&mut without_global, errors[1].clone());
        retain_higher_precedence_error(&mut without_global, errors[0].clone());
        let Some(EncodingError::Failure(report)) = without_global else {
            panic!("lane-local failure must dominate cancellation")
        };
        assert_eq!(report.scope(), FailureScope::LaneLocal);
    }

    #[tokio::test]
    async fn cache_producer_panic_is_a_run_global_infrastructure_failure() {
        let memo = AsyncMemo::<u64, u64, EncodingError>::new();
        let result = memo
            .get_or_fill(
                1,
                &CancellationToken::new(),
                EncodingError::Cancelled,
                cache_producer_failure,
                cache_producer_error_is_sticky,
                |_| async { panic!("cache producer panic") },
            )
            .await;
        let Err(EncodingError::Failure(report)) = result else {
            panic!("a producer panic must not be reported as caller cancellation")
        };
        assert_eq!(report.origin(), FailureOrigin::EncodingPreparation);
        assert_eq!(report.kind(), FailureKind::InfrastructureFailure);
        assert_eq!(report.scope(), FailureScope::RunGlobal);
        assert!(
            report
                .detail()
                .is_some_and(|detail| detail.contains("cache producer task failed"))
        );
        let shutdown = memo.shutdown().await;
        assert!(matches!(shutdown, Err(EncodingError::Failure(_))));
    }

    #[tokio::test]
    async fn context_shutdown_failure_is_sticky_and_never_discharges_owned_work() {
        use std::path::PathBuf;

        use crate::artifact::{ArtifactStoreConfig, new_artifact_store};

        let task = super::super::names::sample_task_for_encoding_tests();
        let root = std::env::temp_dir().join(format!(
            "whiel_context_shutdown_failure_{}",
            std::process::id()
        ));
        let (owner, artifacts) =
            new_artifact_store(&task, ArtifactStoreConfig::new(&root)).unwrap();
        let config = EncodingWorkerPoolConfig::new(
            super::super::worker::EncodingWorkerCommand::new("/bin/true", PathBuf::from("/")),
            1,
        )
        .unwrap();
        let context = new_solver_encoding_context(&task, &artifacts, config).unwrap();
        context.inject_worker_cleanup_failure("sticky context fixture");

        let (first, second) = tokio::join!(context.shutdown(), context.shutdown());
        let third = context.shutdown().await;
        let reports = [first, second, third].map(|result| {
            let Err(EncodingError::Failure(report)) = result else {
                panic!("context cleanup failure must remain sticky")
            };
            report
        });
        for report in &reports {
            assert_eq!(report.kind(), FailureKind::InfrastructureFailure);
            assert_eq!(report.scope(), FailureScope::RunGlobal);
        }
        assert_eq!(reports[0].detail(), reports[1].detail());
        assert_eq!(reports[1].detail(), reports[2].detail());
        drop(context);
        drop(artifacts);
        let failure = owner.settle().unwrap_err();
        assert_eq!(failure.kind(), FailureKind::InfrastructureFailure);
        assert_eq!(failure.scope(), FailureScope::RunGlobal);
        let _ = std::fs::remove_dir_all(root);
    }

    #[tokio::test]
    async fn abandoned_run_global_cache_error_fails_context_shutdown_and_settlement() {
        use std::path::PathBuf;

        use crate::artifact::{ArtifactStoreConfig, new_artifact_store};

        let task = super::super::names::sample_task_for_encoding_tests();
        let root = std::env::temp_dir().join(format!(
            "whiel_context_cache_producer_failure_{}",
            std::process::id()
        ));
        let (owner, artifacts) =
            new_artifact_store(&task, ArtifactStoreConfig::new(&root)).unwrap();
        let config = EncodingWorkerPoolConfig::new(
            super::super::worker::EncodingWorkerCommand::new("/bin/true", PathBuf::from("/")),
            1,
        )
        .unwrap();
        let context = new_solver_encoding_context(&task, &artifacts, config).unwrap();
        let key = BodyCacheKey {
            kind: SourceKind::QuantifierFree,
            source_id: Arc::from("run-global-error-fixture"),
            constants: Arc::from([]),
            relations: Arc::from([]),
        };
        let started = Arc::new(Notify::new());
        let waiter = {
            let context = context.clone();
            let started = Arc::clone(&started);
            tokio::spawn(async move {
                context
                    .inner
                    .body_cache
                    .get_or_fill(
                        key,
                        &CancellationToken::new(),
                        EncodingError::Cancelled,
                        cache_producer_failure,
                        cache_producer_error_is_sticky,
                        move |fill_cancel| async move {
                            started.notify_one();
                            fill_cancel.cancelled().await;
                            Err(EncodingError::Failure(encoding_failure(
                                EncodingFailureClass::SharedInfrastructure,
                                "abandoned context cache producer failed",
                            )))
                        },
                    )
                    .await
            })
        };
        started.notified().await;
        waiter.abort();
        assert!(waiter.await.unwrap_err().is_cancelled());

        let Err(EncodingError::Failure(report)) = context.shutdown().await else {
            panic!("an abandoned run-global producer error must fail context shutdown")
        };
        assert_eq!(report.kind(), FailureKind::InfrastructureFailure);
        assert_eq!(report.scope(), FailureScope::RunGlobal);
        drop(context);
        drop(artifacts);
        let failure = owner.settle().unwrap_err();
        assert_eq!(failure.kind(), FailureKind::InfrastructureFailure);
        assert_eq!(failure.scope(), FailureScope::RunGlobal);
        let _ = std::fs::remove_dir_all(root);
    }

    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn abandoned_run_global_cpu_job_error_fails_context_shutdown_and_settlement() {
        use std::path::PathBuf;

        use tokio::sync::oneshot;

        use crate::artifact::{ArtifactStoreConfig, new_artifact_store};
        use crate::runtime::{RuntimeResourcePolicy, create_general_solver_admission};

        let task = super::super::names::sample_task_for_encoding_tests();
        let root = std::env::temp_dir().join(format!(
            "whiel_context_cpu_job_failure_{}",
            std::process::id()
        ));
        let (owner, artifacts) =
            new_artifact_store(&task, ArtifactStoreConfig::new(&root)).unwrap();
        let config = EncodingWorkerPoolConfig::new(
            super::super::worker::EncodingWorkerCommand::new("/bin/true", PathBuf::from("/")),
            1,
        )
        .unwrap();
        let context = new_solver_encoding_context(&task, &artifacts, config).unwrap();
        let policy = RuntimeResourcePolicy::agent_only(1, 1).unwrap();
        let admission = create_general_solver_admission(policy).unwrap();
        let (started_sender, started_receiver) = oneshot::channel();
        let (failed_sender, failed_receiver) = oneshot::channel();

        let waiter_context = context.clone();
        let waiter_admission = admission.clone();
        let waiter = tokio::spawn(async move {
            waiter_context
                .run_cpu_job(
                    &waiter_admission,
                    &CancellationToken::new(),
                    move |child_cancellation| {
                        let _ = started_sender.send(());
                        child_cancellation.wait_cancelled();
                        let report = encoding_failure(
                            EncodingFailureClass::SharedInfrastructure,
                            "abandoned context CPU job failed",
                        );
                        let _ = failed_sender.send(());
                        Err::<(), _>(CpuJobError::Failure(report))
                    },
                )
                .await
        });
        started_receiver.await.unwrap();
        waiter.abort();
        assert!(waiter.await.unwrap_err().is_cancelled());
        tokio::time::timeout(Duration::from_secs(1), failed_receiver)
            .await
            .expect("the cancelled CPU child must publish its run-global failure")
            .unwrap();

        let Err(EncodingError::Failure(report)) = context.shutdown().await else {
            panic!("an abandoned run-global CPU-job error must fail context shutdown")
        };
        assert_eq!(report.kind(), FailureKind::InfrastructureFailure);
        assert_eq!(report.scope(), FailureScope::RunGlobal);
        assert_eq!(report.detail(), Some("abandoned context CPU job failed"));
        drop(context);
        drop(artifacts);
        let failure = owner.settle().unwrap_err();
        assert_eq!(failure.kind(), FailureKind::InfrastructureFailure);
        assert_eq!(failure.scope(), FailureScope::RunGlobal);
        let _ = std::fs::remove_dir_all(root);
    }

    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn context_shutdown_cancels_and_joins_retained_cpu_jobs_before_discharge() {
        use std::path::PathBuf;
        use std::sync::{Condvar, Mutex};

        use tokio::sync::oneshot;

        use crate::artifact::{ArtifactStoreConfig, new_artifact_store};
        use crate::runtime::{RuntimeResourcePolicy, create_general_solver_admission};

        let task = super::super::names::sample_task_for_encoding_tests();
        let root = std::env::temp_dir().join(format!(
            "whiel_context_retained_cpu_job_{}",
            std::process::id()
        ));
        let (owner, artifacts) =
            new_artifact_store(&task, ArtifactStoreConfig::new(&root)).unwrap();
        let config = EncodingWorkerPoolConfig::new(
            super::super::worker::EncodingWorkerCommand::new("/bin/true", PathBuf::from("/")),
            1,
        )
        .unwrap();
        let context = new_solver_encoding_context(&task, &artifacts, config).unwrap();
        let policy = RuntimeResourcePolicy::agent_only(1, 1).unwrap();
        let admission = create_general_solver_admission(policy).unwrap();
        let release = Arc::new((Mutex::new(false), Condvar::new()));
        let (started_sender, started_receiver) = oneshot::channel();
        let (cancelled_sender, cancelled_receiver) = oneshot::channel();

        let waiter_context = context.clone();
        let waiter_admission = admission.clone();
        let worker_release = Arc::clone(&release);
        let waiter = tokio::spawn(async move {
            waiter_context
                .run_cpu_job(
                    &waiter_admission,
                    &CancellationToken::new(),
                    move |child_cancellation| {
                        let _ = started_sender.send(());
                        child_cancellation.wait_cancelled();
                        let _ = cancelled_sender.send(());
                        let (lock, condition) = &*worker_release;
                        let mut released =
                            lock.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
                        while !*released {
                            released = condition
                                .wait(released)
                                .unwrap_or_else(|poisoned| poisoned.into_inner());
                        }
                        Ok(())
                    },
                )
                .await
        });
        started_receiver.await.unwrap();
        waiter.abort();
        assert!(waiter.await.unwrap_err().is_cancelled());
        tokio::time::timeout(Duration::from_secs(1), cancelled_receiver)
            .await
            .expect("aborting the context CPU-job waiter must cancel its child")
            .unwrap();

        let shutdown_context = context.clone();
        let mut shutdown = tokio::spawn(async move { shutdown_context.shutdown().await });
        tokio::time::sleep(Duration::from_millis(30)).await;
        assert!(
            !shutdown.is_finished(),
            "context shutdown must await retained CPU-job cleanup"
        );
        {
            let (lock, condition) = &*release;
            *lock.lock().unwrap_or_else(|poisoned| poisoned.into_inner()) = true;
            condition.notify_all();
        }
        tokio::time::timeout(Duration::from_secs(1), &mut shutdown)
            .await
            .expect("context shutdown must finish after CPU-job cleanup")
            .expect("context shutdown supervisor must not fail")
            .expect("context shutdown must succeed");

        drop(context);
        drop(artifacts);
        owner.settle().unwrap();
        let _ = std::fs::remove_dir_all(root);
    }
}

// The allocated sequence is diagnostic owner evidence, not an execution token.
// These exact constructor helpers are shared with replay verification.
fn replay_fixed_ambient_context_id(canonical_id: &str, sequence: u64) -> String {
    format!("fixed-ambient-{canonical_id}-{sequence}")
}
fn replay_fixed_ambient_body_id(context: &str, source_id: &str) -> String {
    format!("{context}:fixed-ambient:qf:{source_id}")
}
fn replay_fixed_ambient_support_id<'a>(
    context: &str,
    constants: impl Iterator<Item = &'a str>,
) -> String {
    format!(
        "{context}:fixed-ambient-support:{}",
        constants
            .map(|key| format!("{}:{key}", key.len()))
            .collect::<Vec<_>>()
            .concat()
    )
}
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct ReplayFixedAmbientAllocation {
    pub(crate) canonical_id: String,
    pub(crate) allocation_sequence: u64,
    pub(crate) context_id: String,
}
impl ReplayFixedAmbientAllocation {
    pub(crate) fn verify(&self) -> bool {
        self.context_id
            == replay_fixed_ambient_context_id(&self.canonical_id, self.allocation_sequence)
    }
    pub(crate) fn body_id(&self, source_id: &str) -> String {
        replay_fixed_ambient_body_id(&self.context_id, source_id)
    }
    pub(crate) fn support_id<'a>(&self, constants: impl Iterator<Item = &'a str>) -> String {
        replay_fixed_ambient_support_id(&self.context_id, constants)
    }
}
impl FixedAmbientEncodingContext {
    pub(crate) fn replay_allocation(&self) -> ReplayFixedAmbientAllocation {
        ReplayFixedAmbientAllocation {
            canonical_id: self.task_identity().canonical_id().to_owned(),
            allocation_sequence: self.inner.replay_allocation_sequence,
            context_id: self.context_id().to_owned(),
        }
    }
}
