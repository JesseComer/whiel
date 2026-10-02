//! Opaque Rust orchestration for exact fixed-ambient jobs.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::sync::atomic::{AtomicBool, Ordering as AtomicOrdering};
use std::sync::{Arc, Mutex};

use serde::Deserialize;
use serde_json::{Value, json};

use crate::artifact::{ArtifactKind, ArtifactRef, ArtifactStore};
use crate::encoding::{
    EncodingError, FixedAmbientEncodingContext, FixedAmbientPreparedBodyData,
    FixedAmbientPreparedSupportData, FixedAmbientWorkerOperation, PreparedBodyRef, SupportBlockRef,
    canonical_value_sha256,
};
use crate::entailment::EntailmentAttemptScope;
use crate::entailment::assembly::{
    Entailment, assemble_fixed_ambient_entailment_with_support, render_fixed_ambient_query,
};
use crate::failure::{FailureKind, FailureReport, FailureScope};
use crate::houdini::ClauseId;
use crate::runtime::{CancellationToken, CpuJobError, SolverAdmission};

use crate::vampire::VampireModel;

use super::admission::{FrameworkIIAdmissionContext, WireClauseResult, decode_clause};
use super::catalog::{ExtendedClauseOrigin, FrameworkIIStateError, LeveledClauseCatalog};
use super::ledger::{FrameworkIICheckRequest, FrameworkIICheckRole};
use super::model::decode_framework_ii_vampire_model;
use super::pieces::{
    FrameworkIIPieceCache, FrameworkIIPieceCacheStats, PieceError, constant_union, splice_recipe,
};
use super::premise::{
    FrameworkIIAxiomTagTable, FrameworkIIPremiseTag, fixed_ambient_tptp_name_for_wire_axiom_tag,
};
use super::production::{
    FrameworkIICheckSubject, FrameworkIIEmptyCheckEvidence, FrameworkIIEmptyCheckOutcome,
    FrameworkIIModelValidationOutcome, FrameworkIIPreCheckOutcome,
    FrameworkIIProductionCheckConfig, FrameworkIIProductionChecker,
    FrameworkIIProtectedTheoremCandidate, FrameworkIISemanticAdapter,
    FrameworkIISemanticCheckError, FrameworkIIValidatedRefutationEvidence,
    PreparedFrameworkIIEntailment,
};
use super::snapshot::LeveledCandidateSnapshot;
use super::types::{ExtendedClause, FixedAmbientTaskScope};

const FIXED_AMBIENT_OBLIGATION_VERSION: u64 = 1;
const FIXED_AMBIENT_EMPTY_CHECK_VERSION: u64 = 2;
const FIXED_AMBIENT_PRECONDITION_ROUTE_VERSION: u64 = 1;
const FIXED_AMBIENT_REFUTATION_VALIDATION_VERSION: u64 = 1;
const EDB_PRECONDITION_INIT_THEOREM: &str =
    "Whiel.Synthesis.FrameworkII.FixedAmbient.EdbPrecondition.initVC_valid";
const EDB_PRECONDITION_MAINT_THEOREM: &str =
    "Whiel.Synthesis.FrameworkII.FixedAmbient.EdbPrecondition.maintenanceVC_valid";
/// Lean theorems closing a confirmed bound row's two jobs.
const CONFIRMATION_INIT_THEOREM: &str =
    "Whiel.Synthesis.FrameworkII.FixedAmbient.PreconditionRowConfirmation.initVC_valid";
const CONFIRMATION_MAINT_THEOREM: &str =
    "Whiel.Synthesis.FrameworkII.FixedAmbient.PreconditionRowConfirmation.maintenanceVC_valid";
const EDB_PRECONDITION_EXTRACTION_THEOREM: &str =
    "Whiel.Synthesis.FrameworkII.FixedAmbient.EdbPrecondition.eval_iff_all_topConjuncts";

// ------------------------------------------------------------
// Exact Job Identity
// ------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FrameworkIISelector {
    Initialization(ClauseId),
    Maintenance(ClauseId),
    Termination,
}

impl FrameworkIISelector {
    pub(crate) fn from_check_request(request: &FrameworkIICheckRequest) -> Self {
        match request.role() {
            FrameworkIICheckRole::Initialization => Self::Initialization(request.clause()),
            FrameworkIICheckRole::Maintenance => Self::Maintenance(request.clause()),
        }
    }

    pub(crate) fn identity(self) -> Value {
        match self {
            Self::Initialization(clause) => json!({
                "kind": "initialization",
                "clause_id": clause.get(),
            }),
            Self::Maintenance(clause) => json!({
                "kind": "maintenance",
                "clause_id": clause.get(),
            }),
            Self::Termination => json!({"kind": "termination"}),
        }
    }
}

/// Complete Lean-issued identity for one selected fixed-ambient obligation.
///
/// Test-only since Pass 7.5d: the ordinary check path assembles its
/// obligation from cached opaque pieces and never asks the worker to build
/// one, so nothing outside this crate's own tests constructs this value.
#[cfg(test)]
#[derive(Clone, Debug)]
pub struct FrameworkIIObligation {
    snapshot: Arc<LeveledCandidateSnapshot>,
    selector: FrameworkIISelector,
    obligation_identity: Arc<Value>,
    entailment_identity: Arc<Value>,
}

#[cfg(test)]
impl FrameworkIIObligation {
    pub fn snapshot(&self) -> &Arc<LeveledCandidateSnapshot> {
        &self.snapshot
    }

    pub fn obligation_identity(&self) -> &Value {
        &self.obligation_identity
    }

    pub fn entailment_identity(&self) -> &Value {
        &self.entailment_identity
    }

    pub fn selector_identity(&self) -> Value {
        self.selector.identity()
    }
}

// ------------------------------------------------------------
// Persistent Solver Context
// ------------------------------------------------------------

#[derive(Clone)]
pub struct FrameworkIISolverContext {
    state_owner: Arc<()>,
    encoding: FixedAmbientEncodingContext,
    scope: FixedAmbientTaskScope,
    prepared: Arc<Mutex<BTreeMap<Arc<str>, CachedPreparedEntailment>>>,
    empty_checks: Arc<Mutex<BTreeMap<Arc<str>, CachedEmptyCheck>>>,
    system_routes: Arc<Mutex<BTreeMap<Arc<str>, FrameworkIIPreconditionRoute>>>,
    /// Run-scoped cache of Lean-rendered opaque pieces and support blocks.
    pieces: FrameworkIIPieceCache,
    /// Pass 7.5d's differential safety net (off by default; every live
    /// suite turns it on). When set, every preparation also runs the
    /// worker's own `prepare_exact_obligation` and requires byte-identical
    /// problem text, an identical `axiom_tags` table, and an identical
    /// entailment identity.
    assembly_differential: Arc<AtomicBool>,
    /// Whether a batch may resolve its launches concurrently (Pass 7.5d).
    /// On by default; a test turns it off to run the very same fixture
    /// through the trait's sequential `check_batch` instead.
    concurrent_dispatch: Arc<AtomicBool>,
}

/// One obligation spliced out of cached pieces by the controller.
struct AssembledObligation {
    entailment_identity: Value,
    entailment: Entailment,
    axiom_tags: FrameworkIIAxiomTagTable,
    axiom_bodies: Vec<PreparedBodyRef>,
    conjecture_body: PreparedBodyRef,
    support: SupportBlockRef,
}

/// One Lean-extracted protected EDB-precondition row and its closed routes.
#[derive(Clone, Debug)]
pub struct FrameworkIIPreconditionRoute {
    source_ordinal: u64,
    clause: ExtendedClause,
    route_identity: Arc<Value>,
    route_digest: Arc<str>,
    initialization_theorem: Arc<str>,
    maintenance_theorem: Arc<str>,
}

impl FrameworkIIPreconditionRoute {
    pub fn source_ordinal(&self) -> u64 {
        self.source_ordinal
    }

    pub fn clause(&self) -> &ExtendedClause {
        &self.clause
    }

    pub fn route_identity(&self) -> &Value {
        &self.route_identity
    }

    pub fn route_digest(&self) -> &str {
        &self.route_digest
    }

    pub fn initialization_theorem(&self) -> &str {
        &self.initialization_theorem
    }

    pub fn maintenance_theorem(&self) -> &str {
        &self.maintenance_theorem
    }
}

/// The complete Lean-issued protected precondition basis of one task.
#[derive(Clone, Debug)]
pub struct FrameworkIIPreconditionBasis {
    basis_identity: Arc<Value>,
    basis_digest: Arc<str>,
    routes: Arc<[FrameworkIIPreconditionRoute]>,
}

impl FrameworkIIPreconditionBasis {
    pub fn basis_identity(&self) -> &Value {
        &self.basis_identity
    }

    pub fn basis_digest(&self) -> &str {
        &self.basis_digest
    }

    pub fn routes(&self) -> &[FrameworkIIPreconditionRoute] {
        &self.routes
    }
}

#[derive(Clone)]
struct CachedPreparedEntailment {
    obligation_identity: Arc<Value>,
    prepared: PreparedFrameworkIIEntailment,
}

#[derive(Clone)]
struct CachedEmptyCheck {
    request_identity: Arc<Value>,
    obligation_identity: Arc<Value>,
    /// The entailment identity the cached check was taken over — the same
    /// Rust-computed value
    /// [`PreparedFrameworkIIEntailment::entailment_identity`] carries, which
    /// the worker confirmed verbatim when it answered this very check.
    /// A cache hit is refused unless a later preparation reproduces it
    /// exactly.
    entailment_identity: Arc<Value>,
    outcome: FrameworkIIEmptyCheckOutcome,
}

impl FrameworkIISolverContext {
    pub fn from_admission(admission: &FrameworkIIAdmissionContext) -> Self {
        Self {
            state_owner: Arc::new(()),
            encoding: admission.encoding().clone(),
            scope: admission.scope().clone(),
            prepared: Arc::new(Mutex::new(BTreeMap::new())),
            empty_checks: Arc::new(Mutex::new(BTreeMap::new())),
            system_routes: Arc::new(Mutex::new(BTreeMap::new())),
            pieces: FrameworkIIPieceCache::default(),
            assembly_differential: Arc::new(AtomicBool::new(false)),
            concurrent_dispatch: Arc::new(AtomicBool::new(true)),
        }
    }

    pub fn scope(&self) -> &FixedAmbientTaskScope {
        &self.scope
    }

    /// Turn Pass 7.5d's differential safety net on or off for this run.
    ///
    /// Every live suite enables it: a mismatch between the controller's
    /// assembled problem and the worker's own is a hard failure, never a
    /// warning.
    pub fn set_assembly_differential(&self, enabled: bool) {
        self.assembly_differential
            .store(enabled, AtomicOrdering::Relaxed);
    }

    pub fn assembly_differential(&self) -> bool {
        self.assembly_differential.load(AtomicOrdering::Relaxed)
    }

    /// Allow or forbid concurrent resolution of a batch's launches.
    ///
    /// Test-only. The contract's dispatch is batched and concurrent, and
    /// that is this context's default; nothing on the production path
    /// forbids the concurrency. Forbidding it leaves the batched *dispatch*
    /// in place and only removes the overlap, so a test can run one fixture
    /// both ways and require the same Core, the same drops and the same
    /// dictionary.
    #[doc(hidden)]
    pub fn set_concurrent_dispatch(&self, enabled: bool) {
        self.concurrent_dispatch
            .store(enabled, AtomicOrdering::Relaxed);
    }

    pub fn concurrent_dispatch(&self) -> bool {
        self.concurrent_dispatch.load(AtomicOrdering::Relaxed)
    }

    /// Cache-miss counters for the run's opaque-piece cache.
    pub fn piece_cache_stats(&self) -> FrameworkIIPieceCacheStats {
        self.pieces.stats()
    }

    /// `(distinct clause pieces, distinct task pieces, distinct constant
    /// sets)` currently held. Nothing is evicted, so each equals the number
    /// of misses that populated it.
    pub fn piece_cache_sizes(&self) -> (usize, usize, usize) {
        self.pieces.sizes()
    }

    pub fn encoding(&self) -> &FixedAmbientEncodingContext {
        &self.encoding
    }

    pub(crate) fn shares_state_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.state_owner, &other.state_owner)
            && self.encoding.context_id() == other.encoding.context_id()
            && self.scope == other.scope
    }

    pub fn production_checker(
        self,
        config: FrameworkIIProductionCheckConfig,
    ) -> FrameworkIIProductionChecker<Self> {
        FrameworkIIProductionChecker::new(self, config)
    }

    pub async fn shutdown(&self) -> Result<(), FrameworkIISolverError> {
        self.encoding.shutdown().await.map_err(Into::into)
    }

    /// Ask the worker to build one exact obligation identity.
    ///
    /// Test-only since Pass 7.5d (see [`FrameworkIIObligation`]): the
    /// production path never issues `build_exact_obligation`.
    #[cfg(test)]
    pub async fn build_obligation(
        &self,
        request: &FrameworkIICheckRequest,
        admission: &SolverAdmission,
        cancellation: &CancellationToken,
    ) -> Result<FrameworkIIObligation, FrameworkIISolverError> {
        self.require_check_request(request)?;
        self.build_selected_obligation(
            request.snapshot(),
            FrameworkIISelector::from_check_request(request),
            admission,
            cancellation,
        )
        .await
    }

    /// Test-only companion of [`Self::build_obligation`] for the epoch's
    /// termination obligation.
    #[cfg(test)]
    pub async fn build_termination_obligation(
        &self,
        snapshot: &Arc<LeveledCandidateSnapshot>,
        admission: &SolverAdmission,
        cancellation: &CancellationToken,
    ) -> Result<FrameworkIIObligation, FrameworkIISolverError> {
        self.require_snapshot_scope(snapshot)?;
        self.build_selected_obligation(
            snapshot,
            FrameworkIISelector::Termination,
            admission,
            cancellation,
        )
        .await
    }

    #[cfg(test)]
    async fn build_selected_obligation(
        &self,
        snapshot: &Arc<LeveledCandidateSnapshot>,
        selector: FrameworkIISelector,
        admission: &SolverAdmission,
        cancellation: &CancellationToken,
    ) -> Result<FrameworkIIObligation, FrameworkIISolverError> {
        self.require_snapshot_scope(snapshot)?;
        let selector_identity = selector.identity();
        let response = self
            .encoding
            .execute(
                admission,
                cancellation,
                FixedAmbientWorkerOperation::BuildExactObligation,
                json!({
                    "snapshot": snapshot.worker_payload(),
                    "selector": &selector_identity,
                }),
            )
            .await?;
        let response: WireBuiltObligation =
            decode_payload(response.payload, "fixed-ambient exact-obligation response")?;
        let expected_obligation = obligation_identity(&self.scope, snapshot, &selector_identity);
        if response.obligation_identity != expected_obligation
            || response.selector != selector_identity
        {
            return Err(validation_failure(
                "fixed-ambient worker returned another obligation or selector",
            ));
        }
        validate_entailment_identity(&response.entailment_identity)?;
        Ok(FrameworkIIObligation {
            snapshot: Arc::clone(snapshot),
            selector,
            obligation_identity: Arc::new(response.obligation_identity),
            entailment_identity: Arc::new(response.entailment_identity),
        })
    }

    async fn prepare_entailment(
        &self,
        subject: &FrameworkIICheckSubject,
        admission: &SolverAdmission,
        artifacts: &ArtifactStore,
        cancellation: &CancellationToken,
    ) -> Result<PreparedFrameworkIIEntailment, FrameworkIISolverError> {
        let request = subject;
        self.require_check_subject(subject)?;
        if artifacts.task_identity() != self.scope.task_identity() {
            return Err(validation_failure(
                "fixed-ambient solver received another task's artifact backend",
            ));
        }
        let selector = subject.selector();
        let selector_identity = selector.identity();
        let expected_obligation =
            obligation_identity(&self.scope, request.snapshot(), &selector_identity);
        // The preparation cache is a per-context memo of a preparation bound
        // to one exact run snapshot, and `binds_subject` fails closed on a
        // rebinding across runs. The obligation identity alone is the
        // Lean-facing *semantic* identity — two runs over the same task can
        // denote the same obligation, and an empty Core snapshot does so for
        // the termination request in every run — so the key adds the
        // run-scoped fields the rebinding check compares.
        let cache_key: Arc<str> = Arc::from(canonical_value_sha256(&json!({
            "obligation": expected_obligation,
            "catalog_instance_digest": request.snapshot().catalog_instance_digest(),
            "partition_digest": request.snapshot().partition_digest(),
        })));
        if let Some(cached) = self
            .prepared
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .get(cache_key.as_ref())
            .cloned()
        {
            if cached.obligation_identity.as_ref() != &expected_obligation {
                return Err(validation_failure(
                    "fixed-ambient preparation cache digest collided",
                ));
            }
            return cached
                .prepared
                .rebind_control_request(subject)
                .map_err(state_failure);
        }

        // Pass 7.5d: the ordinary path never asks the worker to assemble a
        // request from a partition snapshot. Rust splices the cached opaque
        // pieces itself, in the order `Obligations.lean` emits them, and
        // computes the obligation and entailment identities from the
        // Lean-issued component identities it already holds.
        let assembled = self
            .assemble_from_pieces(
                request.snapshot(),
                selector,
                admission,
                artifacts,
                cancellation,
            )
            .await?;
        if self.assembly_differential.load(AtomicOrdering::Relaxed) {
            self.check_assembly_differential(
                request.snapshot(),
                &selector_identity,
                &expected_obligation,
                &assembled,
                admission,
                cancellation,
            )
            .await?;
        }
        let prepared = PreparedFrameworkIIEntailment::from_fixed_ambient_job(
            subject,
            expected_obligation.clone(),
            assembled.entailment_identity.clone(),
            assembled.entailment.clone(),
            assembled.axiom_tags.clone(),
        )
        .map_err(state_failure)?;

        let candidate = CachedPreparedEntailment {
            obligation_identity: Arc::new(expected_obligation),
            prepared: prepared.clone(),
        };
        let mut cache = self
            .prepared
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        if let Some(existing) = cache.get(cache_key.as_ref()) {
            if existing.obligation_identity != candidate.obligation_identity
                || existing.prepared.entailment_identity()
                    != candidate.prepared.entailment_identity()
                || !existing
                    .prepared
                    .entailment()
                    .same_exact_fixed_ambient_package(candidate.prepared.entailment())
            {
                return Err(validation_failure(
                    "concurrent fixed-ambient preparations disagreed",
                ));
            }
            return existing
                .prepared
                .rebind_control_request(request)
                .map_err(state_failure);
        }
        if cancellation.should_stop() {
            return Err(FrameworkIISolverError::Cancelled);
        }
        cache.insert(cache_key, candidate);
        Ok(prepared)
    }

    /// Render and cache every clause piece of `clauses` this run does not
    /// already hold.
    ///
    /// Test-only. The ordinary path reaches the same cache through
    /// [`Self::assemble_from_pieces`]; this exists so a live test can hand
    /// the cache a large set and observe that one `prepare_clause_pieces`
    /// request carries all of it, without first committing that many
    /// clauses to a Core.
    #[doc(hidden)]
    pub async fn prefetch_clause_pieces(
        &self,
        clauses: &[ExtendedClause],
        admission: &SolverAdmission,
        cancellation: &CancellationToken,
    ) -> Result<(), FrameworkIISolverError> {
        self.pieces
            .ensure_clause_pieces(&self.encoding, clauses, admission, cancellation)
            .await
            .map_err(piece_failure)
    }

    /// Splice one obligation out of cached opaque pieces.
    ///
    /// Every formula string here came from Lean and is copied verbatim;
    /// every identity is the Lean-issued component identity admitted with
    /// the clause or the task. Rust chooses only the order, and the order
    /// is `Obligations.lean`'s (see [`splice_recipe`]).
    async fn assemble_from_pieces(
        &self,
        snapshot: &Arc<LeveledCandidateSnapshot>,
        selector: FrameworkIISelector,
        admission: &SolverAdmission,
        artifacts: &ArtifactStore,
        cancellation: &CancellationToken,
    ) -> Result<AssembledObligation, FrameworkIISolverError> {
        let recipe = splice_recipe(snapshot, selector).map_err(piece_failure)?;
        self.pieces
            .ensure_task_pieces(&self.encoding, &self.scope, admission, cancellation)
            .await
            .map_err(piece_failure)?;
        self.pieces
            .ensure_clause_pieces(&self.encoding, &recipe.clauses, admission, cancellation)
            .await
            .map_err(piece_failure)?;

        let mut axiom_bodies = Vec::with_capacity(recipe.axioms.len());
        let mut axiom_identities = Vec::with_capacity(recipe.axioms.len());
        let mut tag_entries = Vec::with_capacity(recipe.axioms.len() + 1);
        for (index, (slot, tag)) in recipe.axioms.iter().enumerate() {
            let piece = self.pieces.piece_for(slot).map_err(piece_failure)?;
            axiom_identities.push(piece.formula_identity().clone());
            axiom_bodies.push(piece.body().clone());
            // `render_query` names the axiom at position `index`
            // `axiom_{index}`; the tag table is keyed by that short name,
            // exactly as `decode_axiom_tag_table` keys Lean's own table.
            tag_entries.push((Arc::from(format!("axiom_{index}")) as Arc<str>, tag.clone()));
        }
        let conjecture = self
            .pieces
            .piece_for(&recipe.conjecture)
            .map_err(piece_failure)?;
        let entailment_identity = json!({
            "axioms": axiom_identities,
            "conjecture": conjecture.formula_identity(),
        });
        validate_entailment_identity(&entailment_identity)?;

        let constants = constant_union(
            axiom_bodies
                .iter()
                .chain(std::iter::once(conjecture.body()))
                .map(PreparedBodyRef::constants),
        );
        let support = self
            .pieces
            .support_block(&self.encoding, &constants, admission, cancellation)
            .await
            .map_err(piece_failure)?;
        tag_entries.push((Arc::from("support_adom"), FrameworkIIPremiseTag::Support));
        for index in 0..support.role_neutral_bodies().len().saturating_sub(1) {
            tag_entries.push((
                Arc::from(format!("support_distinct_{index}")) as Arc<str>,
                FrameworkIIPremiseTag::Support,
            ));
        }
        let axiom_tags =
            FrameworkIIAxiomTagTable::from_entries(tag_entries).map_err(|message| {
                validation_failure(format!("fixed-ambient assembled axiom tags: {message}"))
            })?;
        let conjecture_body = conjecture.body().clone();
        let entailment = assemble_fixed_ambient_entailment_with_support(
            &self.encoding,
            admission,
            artifacts,
            entailment_identity.clone(),
            axiom_bodies.clone(),
            vec![conjecture_body.clone()],
            support.clone(),
            cancellation,
        )
        .await?;
        Ok(AssembledObligation {
            entailment_identity,
            entailment,
            axiom_tags,
            axiom_bodies,
            conjecture_body,
            support,
        })
    }

    /// The permanent differential safety net: assemble the same request
    /// through the worker's own `prepare_exact_obligation` and require the
    /// rendered problem bytes, the `axiom_tags` table, and the entailment
    /// identity to agree exactly.
    async fn check_assembly_differential(
        &self,
        snapshot: &Arc<LeveledCandidateSnapshot>,
        selector_identity: &Value,
        obligation_identity: &Value,
        assembled: &AssembledObligation,
        admission: &SolverAdmission,
        cancellation: &CancellationToken,
    ) -> Result<(), FrameworkIISolverError> {
        let response = self
            .encoding
            .execute(
                admission,
                cancellation,
                FixedAmbientWorkerOperation::PrepareExactObligation,
                json!({
                    "obligation_identity": obligation_identity,
                    "selector": selector_identity,
                    "snapshot": snapshot.worker_payload(),
                }),
            )
            .await?;
        let revision = response.name_env_revision;
        let response: WirePreparedObligation = decode_payload(
            response.payload,
            "fixed-ambient prepared-obligation response",
        )?;
        if response.obligation_identity != *obligation_identity {
            return Err(validation_failure(
                "fixed-ambient preparation changed its exact obligation",
            ));
        }
        if response.entailment_identity != assembled.entailment_identity {
            return Err(validation_failure(
                "the assembled fixed-ambient entailment identity differs from Lean's",
            ));
        }
        validate_prepared_sources(
            obligation_identity,
            &response.entailment_identity,
            &response.axiom_bodies,
            &response.conjecture_body,
        )?;
        let worker_tags = decode_axiom_tag_table(response.axiom_tags, obligation_identity)?;
        if worker_tags.as_ref() != Some(&assembled.axiom_tags) {
            return Err(validation_failure(
                "the assembled fixed-ambient axiom_tags table differs from Lean's",
            ));
        }
        let mut worker_axioms = Vec::with_capacity(response.axiom_bodies.len());
        for body in response.axiom_bodies {
            worker_axioms.push(self.encoding.adopt_body(body, revision)?);
        }
        let worker_conjecture = self
            .encoding
            .adopt_body(response.conjecture_body, revision)?;
        let worker_support = self.encoding.adopt_support(response.support, revision)?;
        let assembled_query = render_problem(
            assembled.support.role_neutral_bodies(),
            &assembled.axiom_bodies,
            std::slice::from_ref(&assembled.conjecture_body),
        )?;
        let worker_query = render_problem(
            worker_support.role_neutral_bodies(),
            &worker_axioms,
            std::slice::from_ref(&worker_conjecture),
        )?;
        if assembled_query != worker_query {
            return Err(validation_failure(
                "the assembled fixed-ambient problem bytes differ from Lean's",
            ));
        }
        Ok(())
    }

    async fn check_prepared_empty(
        &self,
        prepared: &PreparedFrameworkIIEntailment,
        attempt: &EntailmentAttemptScope,
        admission: &SolverAdmission,
        cancellation: &CancellationToken,
    ) -> Result<FrameworkIIEmptyCheckOutcome, FrameworkIISemanticCheckError> {
        validate_attempt_binding(prepared, attempt).map_err(semantic_error)?;
        let request_identity = prepared.empty_request_identity();
        let cache_key = prepared.empty_request_digest();
        if let Some(cached) = self
            .empty_checks
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .get(cache_key)
            .cloned()
        {
            if cached.request_identity.as_ref() != request_identity
                || cached.obligation_identity.as_ref() != prepared.base_obligation_identity()
                || cached.entailment_identity.as_ref() != prepared.entailment_identity()
            {
                return Err(semantic_error(validation_failure(
                    "fixed-ambient empty-check cache digest collided",
                )));
            }
            return Ok(cached.outcome);
        }

        let response = self
            .encoding
            .execute(
                admission,
                cancellation,
                FixedAmbientWorkerOperation::CheckEmptyCounterexample,
                prepared.bound_worker_obligation_payload(),
            )
            .await
            .map_err(semantic_encoding_error)?;
        let raw_payload = response.payload;
        let evidence_bytes = serde_json::to_vec(&raw_payload).map_err(|error| {
            semantic_error(validation_failure(format!(
                "serialize fixed-ambient empty-check response: {error}"
            )))
        })?;
        let response: WireEmptyResponse = decode_payload(
            raw_payload.clone(),
            "fixed-ambient empty-counterexample response",
        )
        .map_err(semantic_error)?;
        if response.obligation_identity != *prepared.base_obligation_identity()
            || response.entailment_identity != *prepared.entailment_identity()
            || response.decision_definition != "QFEntailment.adomEmptyCounterexample?"
        {
            return Err(semantic_error(validation_failure(
                "fixed-ambient empty checker changed its exact obligation",
            )));
        }
        let result_identity = response.result.clone();
        let result: WireEmptyResult =
            decode_payload(response.result, "fixed-ambient empty-counterexample result")
                .map_err(semantic_error)?;
        let check_identity = json!({
            "kind": "whiel_fixed_ambient_empty_counterexample_check",
            "version": FIXED_AMBIENT_EMPTY_CHECK_VERSION,
            "empty_request_identity": request_identity,
            "obligation_identity": prepared.base_obligation_identity(),
            "worker_entailment_identity": prepared.entailment_identity(),
            "result": &result_identity,
            "decision_definition": "QFEntailment.adomEmptyCounterexample?",
        });
        let check_digest: Arc<str> = Arc::from(canonical_value_sha256(&check_identity));
        if cancellation.should_stop() {
            return Err(FrameworkIISemanticCheckError::Cancelled);
        }
        let empty_artifact = attempt
            .artifacts()
            .publish(
                ArtifactKind::EmptyInstanceCheck,
                evidence_bytes.clone().into_boxed_slice(),
            )
            .map_err(FrameworkIISemanticCheckError::Failure)?;
        let outcome = match result {
            WireEmptyResult::NoCounterexample => FrameworkIIEmptyCheckOutcome::NoCounterexample(
                FrameworkIIEmptyCheckEvidence::new_no_counterexample(
                    prepared.empty_request_digest(),
                    prepared.base_obligation_digest(),
                    check_identity,
                    Arc::clone(&check_digest),
                    empty_artifact,
                )
                .map_err(|error| semantic_error(state_failure(error)))?,
            ),
            WireEmptyResult::Counterexample { nullary_assignment } => {
                validate_nullary_assignment(&self.scope, &nullary_assignment)
                    .map_err(semantic_error)?;
                if cancellation.should_stop() {
                    return Err(FrameworkIISemanticCheckError::Cancelled);
                }
                let validation_artifact = attempt
                    .artifacts()
                    .publish(ArtifactKind::Witness, evidence_bytes.into_boxed_slice())
                    .map_err(FrameworkIISemanticCheckError::Failure)?;
                FrameworkIIEmptyCheckOutcome::ValidatedRefutation(
                    FrameworkIIValidatedRefutationEvidence::new(
                        empty_artifact,
                        check_identity,
                        Arc::clone(&check_digest),
                        validation_artifact,
                    )
                    .map_err(|error| semantic_error(state_failure(error)))?,
                )
            }
        };
        let candidate = CachedEmptyCheck {
            request_identity: Arc::new(request_identity.clone()),
            obligation_identity: Arc::new(prepared.base_obligation_identity().clone()),
            entailment_identity: Arc::new(prepared.entailment_identity().clone()),
            outcome: outcome.clone(),
        };
        let mut cache = self
            .empty_checks
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        if let Some(existing) = cache.get(cache_key) {
            if existing.request_identity != candidate.request_identity
                || existing.obligation_identity != candidate.obligation_identity
                || existing.entailment_identity != candidate.entailment_identity
                || existing.outcome.check_identity() != candidate.outcome.check_identity()
                || existing.outcome.check_digest() != candidate.outcome.check_digest()
            {
                return Err(semantic_error(validation_failure(
                    "concurrent fixed-ambient empty checks disagreed on identity or result",
                )));
            }
            return Ok(existing.outcome.clone());
        }
        cache.insert(Arc::from(cache_key), candidate);
        Ok(outcome)
    }

    /// Extract the Lean-issued protected EDB-precondition basis.
    pub async fn extract_precondition_basis(
        &self,
        admission: &SolverAdmission,
        cancellation: &CancellationToken,
    ) -> Result<FrameworkIIPreconditionBasis, FrameworkIISolverError> {
        let response = self
            .encoding
            .execute(
                admission,
                cancellation,
                FixedAmbientWorkerOperation::ExtractPreconditionClauses,
                json!({}),
            )
            .await?;
        decode_precondition_response(response.payload, &self.scope)
    }

    /// Close the protected-system reservation before any external clause
    /// registration. Every reserved origin is linked to the complete
    /// Lean-produced route that later authorizes its two closed derivations.
    pub async fn reserve_precondition_system_clauses(
        &self,
        catalog: &LeveledClauseCatalog,
        admission: &SolverAdmission,
        cancellation: &CancellationToken,
    ) -> Result<FrameworkIIPreconditionBasis, FrameworkIISolverError> {
        if catalog.scope() != &self.scope {
            return Err(validation_failure(
                "fixed-ambient precondition reservation received another catalog scope",
            ));
        }
        let basis = self
            .extract_precondition_basis(admission, cancellation)
            .await?;
        let mut routes = BTreeMap::<Arc<str>, FrameworkIIPreconditionRoute>::new();
        for route in basis.routes() {
            let key: Arc<str> = Arc::from(route.clause().identity_intern_key());
            if let Some(existing) = routes.get(&key) {
                if !existing.clause().semantic_metadata_matches(route.clause()) {
                    return Err(validation_failure(
                        "duplicate fixed-ambient precondition routes disagree semantically",
                    ));
                }
                // Routes arrive in strict source order; the earliest conjunct
                // owns a repeated formula, matching catalog reservation.
                continue;
            }
            routes.insert(key, route.clone());
        }
        let reservations = basis
            .routes()
            .iter()
            .map(|route| {
                Ok((
                    route.clause().clone(),
                    ExtendedClauseOrigin::edb_precondition_system(
                        route.source_ordinal(),
                        route.route_digest(),
                    )
                    .map_err(state_failure)?,
                ))
            })
            .collect::<Result<Vec<_>, FrameworkIISolverError>>()?;
        catalog
            .reserve_system_clauses(reservations)
            .map_err(state_failure)?;
        *self
            .system_routes
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner()) = routes;
        Ok(basis)
    }

    pub(crate) fn protected_route_for(
        &self,
        subject: &FrameworkIICheckSubject,
        prepared: &PreparedFrameworkIIEntailment,
    ) -> Result<Option<FrameworkIIPreconditionRoute>, FrameworkIIStateError> {
        prepared.rebind_control_request(subject)?;
        let Some(request) = subject.as_clause() else {
            return Ok(None);
        };
        let record = request.snapshot().records().get(&request.clause()).ok_or(
            FrameworkIIStateError::InvalidEvidence(
                "fixed-ambient protected-route lookup lost its target record",
            ),
        )?;
        if !record.is_protected() {
            return Ok(None);
        }
        let ExtendedClauseOrigin::EdbPreconditionSystem {
            conjunct_ordinal,
            route_digest,
        } = record.origin()
        else {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "a protected fixed-ambient record lacks a system origin",
            ));
        };
        let route = self
            .system_routes
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .get(record.identity_intern_key())
            .cloned()
            .ok_or(FrameworkIIStateError::InvalidEvidence(
                "a protected fixed-ambient record has no extracted Lean route",
            ))?;
        if route.source_ordinal() != *conjunct_ordinal
            || route.route_digest() != route_digest.as_ref()
            || !route.clause().semantic_metadata_matches(record.formula())
            || request.level() != super::types::FrameworkIILevel::ZERO
        {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "a protected fixed-ambient route disagrees with its exact catalog record",
            ));
        }
        Ok(Some(route))
    }

    /// Ask Lean to confirm that the bound job's row is one of its extracted
    /// protected precondition rows at the reserved source ordinal. Rust
    /// bookkeeping alone never authorizes a protected derivation.
    async fn confirm_protected_row(
        &self,
        request: &FrameworkIICheckRequest,
        prepared: &PreparedFrameworkIIEntailment,
        route: &FrameworkIIPreconditionRoute,
        admission: &SolverAdmission,
        cancellation: &CancellationToken,
    ) -> Result<(), FrameworkIIStateError> {
        let invalid = |detail: &'static str| FrameworkIIStateError::InvalidEvidence(detail);
        let mut payload = prepared.bound_worker_obligation_payload();
        let Value::Object(fields) = &mut payload else {
            return Err(invalid(
                "a bound fixed-ambient obligation payload is not an object",
            ));
        };
        fields.insert(
            "source_ordinal".to_string(),
            Value::from(route.source_ordinal()),
        );
        let response = self
            .encoding
            .execute(
                admission,
                cancellation,
                FixedAmbientWorkerOperation::ConfirmPreconditionRow,
                payload,
            )
            .await
            .map_err(FrameworkIISolverError::from)
            .map_err(|error| match error {
                FrameworkIISolverError::Cancelled => FrameworkIIStateError::Cancelled,
                FrameworkIISolverError::Failure(_) => {
                    invalid("the Lean worker did not confirm the protected row of a bound job")
                }
            })?;
        let response: WireConfirmationResponse = decode_payload(
            response.payload,
            "fixed-ambient precondition-row confirmation",
        )
        .map_err(|_| invalid("a protected-row confirmation has an invalid shape"))?;
        let expected_theorem = match request.role() {
            FrameworkIICheckRole::Initialization => CONFIRMATION_INIT_THEOREM,
            FrameworkIICheckRole::Maintenance => CONFIRMATION_MAINT_THEOREM,
        };
        if response.obligation_identity != *prepared.base_obligation_identity()
            || response.entailment_identity != *prepared.entailment_identity()
            || response.source_ordinal != route.source_ordinal()
            || response.level != 0
            || response.clause_id != request.clause().get()
            || response.route_digest != route.route_digest()
            || &response.route_identity != route.route_identity()
            || &response.clause_identity != route.clause().identity()
            || response.confirmation_theorem != expected_theorem
        {
            return Err(invalid(
                "Lean's protected-row confirmation disagrees with the reserved route",
            ));
        }
        Ok(())
    }

    async fn validate_prepared_model(
        &self,
        prepared: &PreparedFrameworkIIEntailment,
        attempt: &EntailmentAttemptScope,
        model: VampireModel,
        admission: &SolverAdmission,
        cancellation: &CancellationToken,
    ) -> Result<FrameworkIIModelValidationOutcome, FrameworkIISemanticCheckError> {
        validate_attempt_binding(prepared, attempt).map_err(semantic_error)?;
        if model.problem_identity() != prepared.entailment().identity()
            || model.attempt_id() != attempt.attempt_id()
            || model.query_artifact() != Some(prepared.entailment().query_artifact())
            || model.output().backend_id() != attempt.artifacts().backend_id()
            || model.output().kind() != ArtifactKind::Model
        {
            return Err(semantic_error(validation_failure(
                "fixed-ambient model changed its entailment, query, attempt, or artifact backend",
            )));
        }
        if cancellation.should_stop() {
            return Err(FrameworkIISemanticCheckError::Cancelled);
        }
        let resolved = attempt
            .artifacts()
            .resolve(model.output())
            .map_err(FrameworkIISemanticCheckError::Failure)?;
        let model_path = resolved.path().to_path_buf();
        // The exact problem the solver was handed. It decides whether a
        // relation the model omits was unconstrained by the problem.
        let query_path = attempt
            .artifacts()
            .resolve(prepared.entailment().query_artifact())
            .ok()
            .map(|resolved| resolved.path().to_path_buf());
        let scope = self.scope.clone();
        let names = self.encoding.task_name_env();
        let required_constants = prepared.required_constants().to_vec();
        let interpretation = self
            .encoding
            .run_cpu_job(admission, cancellation, move |job_cancellation| {
                if job_cancellation.is_cancelled() {
                    return Err(CpuJobError::Cancelled);
                }
                let stdout = std::fs::read_to_string(&model_path).map_err(|error| {
                    CpuJobError::Failure(model_decode_report(format!(
                        "read fixed-ambient Vampire model {}: {error}",
                        model_path.display()
                    )))
                })?;
                if job_cancellation.is_cancelled() {
                    return Err(CpuJobError::Cancelled);
                }
                let query = query_path.and_then(|path| std::fs::read_to_string(path).ok());
                let interpretation = decode_framework_ii_vampire_model(
                    &scope,
                    &names,
                    &required_constants,
                    &stdout,
                    query.as_deref(),
                )
                .map_err(|error| {
                    CpuJobError::Failure(model_decode_report(format!(
                        "decode complete fixed-ambient model: {error}"
                    )))
                })?;
                if job_cancellation.is_cancelled() {
                    return Err(CpuJobError::Cancelled);
                }
                Ok(interpretation)
            })
            .await
            .map_err(cpu_semantic_error)?;
        if cancellation.should_stop() {
            return Err(FrameworkIISemanticCheckError::Cancelled);
        }
        let mut payload = prepared.bound_worker_obligation_payload();
        let Some(fields) = payload.as_object_mut() else {
            return Err(semantic_error(validation_failure(
                "fixed-ambient obligation payload is not an object",
            )));
        };
        fields.insert(
            "interpretation".to_owned(),
            interpretation.as_json().clone(),
        );
        let response = self
            .encoding
            .execute(
                admission,
                cancellation,
                FixedAmbientWorkerOperation::ValidateRefutation,
                payload,
            )
            .await
            .map_err(semantic_encoding_error)?;
        decode_refutation_response(
            response.payload,
            prepared,
            attempt,
            model.output(),
            interpretation.as_json(),
            &self.scope,
            cancellation,
        )
        .map_err(semantic_error)
    }

    fn require_check_request(
        &self,
        request: &FrameworkIICheckRequest,
    ) -> Result<(), FrameworkIISolverError> {
        self.require_snapshot_scope(request.snapshot())?;
        if !request.has_current_identity()
            || request.worker_selector()
                != FrameworkIISelector::from_check_request(request).identity()
        {
            return Err(validation_failure(
                "the check request lost its complete fixed-ambient identity",
            ));
        }
        Ok(())
    }

    /// The subject-level form: a clause request keeps its full worker
    /// selector check; the termination request has no clause and is checked
    /// for scope and structural identity alone.
    fn require_check_subject(
        &self,
        subject: &FrameworkIICheckSubject,
    ) -> Result<(), FrameworkIISolverError> {
        match subject {
            FrameworkIICheckSubject::Clause(request) => self.require_check_request(request),
            FrameworkIICheckSubject::Termination(request) => {
                self.require_snapshot_scope(request.core())?;
                if !subject.has_current_identity() {
                    return Err(validation_failure(
                        "the fixed-ambient termination request lost its structural identity",
                    ));
                }
                Ok(())
            }
        }
    }

    fn require_snapshot_scope(
        &self,
        snapshot: &LeveledCandidateSnapshot,
    ) -> Result<(), FrameworkIISolverError> {
        if snapshot.scope() != &self.scope {
            return Err(validation_failure(
                "fixed-ambient solver received another task scope",
            ));
        }
        Ok(())
    }
}

// ------------------------------------------------------------
// Production Adapter
// ------------------------------------------------------------

impl FrameworkIISemanticAdapter for FrameworkIISolverContext {
    /// Every piece of this context's mutable state — the preparation cache,
    /// the empty-check cache, the extracted routes, the opaque-piece cache,
    /// the worker pool behind the encoding context — already sits behind a
    /// shared handle, so a clone is another handle onto the same state, not
    /// a fork of it. A batch hands one to each concurrent launch.
    fn concurrent_handle(&self) -> Option<Self> {
        self.concurrent_dispatch
            .load(AtomicOrdering::Relaxed)
            .then(|| self.clone())
    }

    fn encoding_context_id(&self) -> Option<&str> {
        Some(self.encoding.context_id())
    }

    fn matches_solver_context(&self, solver: &FrameworkIISolverContext) -> bool {
        self.shares_state_with(solver)
    }

    fn prepare<'a>(
        &'a mut self,
        subject: &'a FrameworkIICheckSubject,
        admission: &'a SolverAdmission,
        artifacts: &'a ArtifactStore,
        cancellation: &'a CancellationToken,
    ) -> std::pin::Pin<
        Box<
            dyn std::future::Future<
                    Output = Result<FrameworkIIPreCheckOutcome, FrameworkIIStateError>,
                > + Send
                + 'a,
        >,
    > {
        Box::pin(async move {
            match self
                .prepare_entailment(subject, admission, artifacts, cancellation)
                .await
            {
                Ok(prepared) => Ok(FrameworkIIPreCheckOutcome::Applied(prepared)),
                Err(FrameworkIISolverError::Cancelled) => Err(FrameworkIIStateError::Cancelled),
                Err(FrameworkIISolverError::Failure(report)) => {
                    Ok(FrameworkIIPreCheckOutcome::Failure(report))
                }
            }
        })
    }

    fn check_empty<'a>(
        &'a mut self,
        prepared: &'a PreparedFrameworkIIEntailment,
        attempt: &'a EntailmentAttemptScope,
        admission: &'a SolverAdmission,
        cancellation: &'a CancellationToken,
    ) -> std::pin::Pin<
        Box<
            dyn std::future::Future<
                    Output = Result<FrameworkIIEmptyCheckOutcome, FrameworkIISemanticCheckError>,
                > + Send
                + 'a,
        >,
    > {
        Box::pin(async move {
            self.check_prepared_empty(prepared, attempt, admission, cancellation)
                .await
        })
    }

    fn validate_model<'a>(
        &'a mut self,
        prepared: &'a PreparedFrameworkIIEntailment,
        attempt: &'a EntailmentAttemptScope,
        model: VampireModel,
        admission: &'a SolverAdmission,
        cancellation: &'a CancellationToken,
    ) -> std::pin::Pin<
        Box<
            dyn std::future::Future<
                    Output = Result<
                        FrameworkIIModelValidationOutcome,
                        FrameworkIISemanticCheckError,
                    >,
                > + Send
                + 'a,
        >,
    > {
        Box::pin(async move {
            self.validate_prepared_model(prepared, attempt, model, admission, cancellation)
                .await
        })
    }

    fn protected_theorem_candidate<'a>(
        &'a mut self,
        subject: &'a FrameworkIICheckSubject,
        prepared: &'a PreparedFrameworkIIEntailment,
        admission: &'a SolverAdmission,
        cancellation: &'a CancellationToken,
    ) -> std::pin::Pin<
        Box<
            dyn std::future::Future<
                    Output = Result<
                        Option<FrameworkIIProtectedTheoremCandidate>,
                        FrameworkIIStateError,
                    >,
                > + Send
                + 'a,
        >,
    > {
        Box::pin(async move {
            // The termination request names no clause and is never a
            // protected precondition row.
            let Some(request) = subject.as_clause() else {
                return Ok(None);
            };
            let Some(route) = self.protected_route_for(subject, prepared)? else {
                return Ok(None);
            };
            self.confirm_protected_row(request, prepared, &route, admission, cancellation)
                .await?;
            let theorem = match request.role() {
                FrameworkIICheckRole::Initialization => route.initialization_theorem(),
                FrameworkIICheckRole::Maintenance => route.maintenance_theorem(),
            };
            FrameworkIIProtectedTheoremCandidate::new(
                request.role(),
                route.route_digest(),
                route.clause().identity(),
                route.clause().relation_keys(),
                theorem,
            )
            .map(Some)
        })
    }
}

// ------------------------------------------------------------
// Strict Worker Responses
// ------------------------------------------------------------

#[cfg(test)]
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WireBuiltObligation {
    obligation_identity: Value,
    entailment_identity: Value,
    selector: Value,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WirePreparedObligation {
    obligation_identity: Value,
    entailment_identity: Value,
    axiom_bodies: Vec<FixedAmbientPreparedBodyData>,
    conjecture_body: FixedAmbientPreparedBodyData,
    support: FixedAmbientPreparedSupportData,
    /// Pass 7.5b: Lean's positional axiom-name-to-tag table for this exact
    /// preparation. `#[serde(default)]` so a worker binary that does not
    /// yet emit this field still decodes — `prepare_entailment` then simply
    /// carries `None`, and proof-search caching degrades to recording no
    /// proof-subsumption entry rather than failing the preparation.
    #[serde(default)]
    axiom_tags: Option<Vec<WireAxiomTag>>,
}

/// One entry of Lean's `axiom_tags` preparation-response table: a
/// positional axiom name, its tag, and — for `plain`/`theta`/`collapsed` —
/// the clause identity the tag carries.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WireAxiomTag {
    name: String,
    tag: String,
    /// Lean's raw structural clause-identity token (the same shape
    /// `ExtendedClause::identity`/`FrameworkIIComponentFormula::identity`
    /// carry), or `null` for a tag that names no clause. Always present as
    /// a key (Lean emits `Lean.Json.null` rather than omitting it), never a
    /// pre-hashed digest string — [`decode_axiom_tag_table`] hashes it the
    /// same way every other clause identity in this crate is hashed.
    identity: Value,
}

/// Decode Lean's `axiom_tags` wire table into a lookup table, failing closed
/// on an unsupported tag shape, an unrecognized wire name, or a repeated
/// axiom name. `None` in, `None` out: a worker binary that omits the table
/// entirely is tolerated here, not treated as a decode failure.
///
/// Lean's wire name for each entry is its long qualified source id (e.g.
/// `framework_ii.fixed_ambient.obligation.<hash>.axiom.3`), but the TPTP
/// problem text the solver actually sees — and that a proof's `file(...)`
/// annotations actually cite — names the same axiom with the short,
/// obligation-independent identifier `entailment::assembly::render_query`
/// assigns it (`axiom_3`, `support_adom`, `support_distinct_1`, ...). The
/// table must be keyed by that short name, the only thing
/// [`cited_tagged_premises_from_proof`] ever looks up, so every entry's wire
/// name is translated through [`fixed_ambient_tptp_name_for_wire_axiom_tag`]
/// first. This is a deterministic decode of Lean's own name structure — the
/// same `sourcePrefix` `validate_prepared_sources` already recomputes and
/// checks against every prepared body's `source_id` — never an inference
/// from an entry's position in the wire array.
fn decode_axiom_tag_table(
    entries: Option<Vec<WireAxiomTag>>,
    obligation_identity: &Value,
) -> Result<Option<FrameworkIIAxiomTagTable>, FrameworkIISolverError> {
    let Some(entries) = entries else {
        return Ok(None);
    };
    let prefix = fixed_ambient_obligation_source_prefix(obligation_identity);
    let mut pairs = Vec::with_capacity(entries.len());
    for entry in entries {
        // Hash the raw identity token exactly the way every other clause
        // identity in this crate is hashed (`ExtendedClause`/
        // `FrameworkIIComponentFormula` both compute
        // `canonical_value_sha256(&identity)`), so a `plain`/`theta`
        // premise's digest here matches the digest `tagged_premise_set`
        // computes from the same clause elsewhere.
        let identity_digest: Option<Arc<str>> = match &entry.identity {
            Value::Null => None,
            identity => Some(Arc::from(canonical_value_sha256(identity))),
        };
        let tag = FrameworkIIPremiseTag::from_wire(&entry.tag, identity_digest.as_deref())
            .map_err(|message| {
                validation_failure(format!("fixed-ambient axiom_tags table: {message}"))
            })?;
        let tptp_name = fixed_ambient_tptp_name_for_wire_axiom_tag(&prefix, &entry.name)
            .ok_or_else(|| {
                validation_failure(format!(
                    "fixed-ambient axiom_tags table: unrecognized wire name {:?}",
                    entry.name
                ))
            })?;
        pairs.push((tptp_name, tag));
    }
    let table = FrameworkIIAxiomTagTable::from_entries(pairs).map_err(|message| {
        validation_failure(format!("fixed-ambient axiom_tags table: {message}"))
    })?;
    Ok(Some(table))
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WireEmptyResponse {
    obligation_identity: Value,
    entailment_identity: Value,
    result: Value,
    decision_definition: String,
}

#[derive(Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
enum WireEmptyResult {
    NoCounterexample,
    Counterexample {
        nullary_assignment: Vec<WireNullaryAssignment>,
    },
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WireNullaryAssignment {
    relation_key: String,
    value: bool,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WireConfirmationResponse {
    obligation_identity: Value,
    entailment_identity: Value,
    #[allow(dead_code)]
    selector: Value,
    source_ordinal: u64,
    clause_id: u64,
    level: u64,
    clause_identity: Value,
    route_identity: Value,
    route_digest: String,
    confirmation_theorem: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WirePreconditionResponse {
    basis_identity: Value,
    basis_digest: String,
    rows: Vec<WirePreconditionRow>,
    extraction_theorem: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WirePreconditionRow {
    source_ordinal: u64,
    clause: super::admission::WireExtendedClause,
    components: Vec<super::admission::WireComponentMetadata>,
    route_identity: Value,
    route_digest: String,
    initialization_theorem: String,
    maintenance_theorem: String,
}

fn decode_precondition_response(
    payload: Value,
    scope: &FixedAmbientTaskScope,
) -> Result<FrameworkIIPreconditionBasis, FrameworkIISolverError> {
    let response: WirePreconditionResponse =
        decode_payload(payload, "fixed-ambient precondition basis")?;
    if response.extraction_theorem != EDB_PRECONDITION_EXTRACTION_THEOREM {
        return Err(validation_failure(
            "fixed-ambient precondition response changed its extraction theorem",
        ));
    }
    let mut routes = Vec::with_capacity(response.rows.len());
    let mut route_identities = Vec::with_capacity(response.rows.len());
    let mut prior_ordinal = None;
    for wire in response.rows {
        if prior_ordinal.is_some_and(|prior| wire.source_ordinal <= prior) {
            return Err(validation_failure(
                "fixed-ambient precondition routes are not in strict source order",
            ));
        }
        prior_ordinal = Some(wire.source_ordinal);
        if wire.initialization_theorem != EDB_PRECONDITION_INIT_THEOREM
            || wire.maintenance_theorem != EDB_PRECONDITION_MAINT_THEOREM
        {
            return Err(validation_failure(
                "fixed-ambient precondition route changed a closed derivation theorem",
            ));
        }
        let clause = decode_clause(
            WireClauseResult {
                clause: wire.clause,
                components: wire.components,
            },
            scope,
        )
        .map_err(|error| match error {
            super::admission::FrameworkIIAdmissionError::Cancelled => {
                FrameworkIISolverError::Cancelled
            }
            super::admission::FrameworkIIAdmissionError::Failure(report) => {
                FrameworkIISolverError::Failure(report)
            }
        })?;
        let expected_route = json!({
            "kind": "whiel_fixed_ambient_edb_precondition_route",
            "version": FIXED_AMBIENT_PRECONDITION_ROUTE_VERSION,
            "scope_identity": scope.identity(),
            "source_ordinal": wire.source_ordinal,
            "level": 0,
            "clause_identity": clause.identity(),
            "initialization_theorem": wire.initialization_theorem,
            "maintenance_theorem": wire.maintenance_theorem,
        });
        if wire.route_identity != expected_route {
            return Err(validation_failure(
                "fixed-ambient precondition route identity disagrees with its clause",
            ));
        }
        validate_identity_digest("route_digest", &wire.route_identity, &wire.route_digest)?;
        route_identities.push(wire.route_identity.clone());
        routes.push(FrameworkIIPreconditionRoute {
            source_ordinal: wire.source_ordinal,
            clause,
            route_identity: Arc::new(wire.route_identity),
            route_digest: Arc::from(wire.route_digest),
            initialization_theorem: Arc::from(wire.initialization_theorem),
            maintenance_theorem: Arc::from(wire.maintenance_theorem),
        });
    }
    let Some(basis) = response.basis_identity.as_object() else {
        return Err(validation_failure(
            "fixed-ambient precondition basis identity is not an object",
        ));
    };
    let precondition = scope
        .components()
        .get(super::components::FrameworkIIComponentRole::Precondition)
        .ok_or_else(|| {
            validation_failure("fixed-ambient scope lacks its precondition component")
        })?;
    if basis.len() != 5
        || basis.get("kind").and_then(Value::as_str)
            != Some("whiel_fixed_ambient_edb_precondition_basis")
        || basis.get("version").and_then(Value::as_u64)
            != Some(FIXED_AMBIENT_PRECONDITION_ROUTE_VERSION)
        || basis.get("scope_identity") != Some(scope.identity())
        || basis.get("precondition_identity") != Some(precondition.formula().identity())
        || basis.get("routes") != Some(&Value::Array(route_identities))
    {
        return Err(validation_failure(
            "fixed-ambient precondition basis identity disagrees with its exact routes",
        ));
    }
    validate_identity_digest(
        "basis_digest",
        &response.basis_identity,
        &response.basis_digest,
    )?;
    Ok(FrameworkIIPreconditionBasis {
        basis_identity: Arc::new(response.basis_identity),
        basis_digest: Arc::from(response.basis_digest),
        routes: routes.into(),
    })
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WireRefutationResponse {
    obligation_identity: Value,
    obligation_digest: String,
    carrier_identity: Value,
    carrier_digest: String,
    interpretation_identity: Value,
    interpretation_digest: String,
    validation_identity: Value,
    validation_digest: String,
    axioms_hold: bool,
    conjecture_holds: bool,
    validated_refutation: bool,
    validation_definition: String,
    entailment_identity: Value,
    selector: Value,
}

fn decode_refutation_response(
    payload: Value,
    prepared: &PreparedFrameworkIIEntailment,
    attempt: &EntailmentAttemptScope,
    source_artifact: ArtifactRef,
    interpretation_input: &Value,
    scope: &FixedAmbientTaskScope,
    cancellation: &CancellationToken,
) -> Result<FrameworkIIModelValidationOutcome, FrameworkIISolverError> {
    let artifact_payload = serde_json::to_vec(&payload).map_err(|error| {
        validation_failure(format!(
            "serialize fixed-ambient refutation validation: {error}"
        ))
    })?;
    let response: WireRefutationResponse =
        decode_payload(payload, "fixed-ambient refutation validation")?;
    if response.obligation_identity != *prepared.base_obligation_identity()
        || response.obligation_digest != prepared.base_obligation_digest()
        || response.entailment_identity != *prepared.entailment_identity()
        || response.validation_definition != "QFEntailment.Valid"
        || Some(&response.selector) != prepared.bound_worker_obligation_payload().get("selector")
    {
        return Err(validation_failure(
            "fixed-ambient refutation validator changed its exact obligation or definition",
        ));
    }
    let carrier_keys = interpretation_input
        .get("carrier_keys")
        .and_then(Value::as_array)
        .ok_or_else(|| {
            validation_failure("canonical fixed-ambient interpretation omitted its carrier")
        })?;
    let expected_carrier = json!({
        "kind": "whiel_framework_ii_finite_carrier",
        "version": FIXED_AMBIENT_REFUTATION_VALIDATION_VERSION,
        "carrier_keys": carrier_keys,
    });
    if response.carrier_identity != expected_carrier {
        return Err(validation_failure(
            "fixed-ambient refutation validator changed its exact finite carrier",
        ));
    }
    validate_identity_digest(
        "carrier_digest",
        &response.carrier_identity,
        &response.carrier_digest,
    )?;
    let input_relations = interpretation_input
        .get("relations")
        .and_then(Value::as_array)
        .ok_or_else(|| {
            validation_failure("canonical fixed-ambient interpretation omitted its relations")
        })?;
    let mut input_rows = BTreeMap::new();
    for relation in input_relations {
        let object = relation.as_object().ok_or_else(|| {
            validation_failure("canonical fixed-ambient relation is not an object")
        })?;
        if object.len() != 2 || !object.contains_key("name") || !object.contains_key("rows") {
            return Err(validation_failure(
                "canonical fixed-ambient relation has unsupported fields",
            ));
        }
        let name = object.get("name").and_then(Value::as_str).ok_or_else(|| {
            validation_failure("canonical fixed-ambient relation omitted its key")
        })?;
        let rows = object
            .get("rows")
            .and_then(Value::as_array)
            .ok_or_else(|| {
                validation_failure("canonical fixed-ambient relation omitted its tuple rows")
            })?;
        if input_rows.insert(name.to_string(), rows.clone()).is_some() {
            return Err(validation_failure(
                "canonical fixed-ambient interpretation repeats a relation",
            ));
        }
    }
    let schema_relations = scope
        .relations()
        .iter()
        .map(|relation| {
            json!({
                "key": relation.key().as_str(),
                "arity": relation.arity(),
            })
        })
        .collect::<Vec<_>>();
    let mut instance_relations = scope
        .relations()
        .iter()
        .map(|relation| {
            let rows = input_rows.get(relation.key().as_str()).ok_or_else(|| {
                validation_failure(
                    "canonical fixed-ambient interpretation is incomplete over the ambient schema",
                )
            })?;
            Ok(json!({
                "key": relation.key().as_str(),
                "arity": relation.arity(),
                "rows": rows,
            }))
        })
        .collect::<Result<Vec<_>, FrameworkIISolverError>>()?;
    instance_relations.sort_by(|left, right| {
        left.get("key")
            .and_then(Value::as_str)
            .cmp(&right.get("key").and_then(Value::as_str))
    });
    if input_rows.len() != instance_relations.len() {
        return Err(validation_failure(
            "canonical fixed-ambient interpretation contains an out-of-scope relation",
        ));
    }
    let instance_identity = json!({
        "kind": "whiel_source_instance",
        "version": 1,
        "relations": instance_relations,
    });
    let expected_interpretation = json!({
        "kind": "whiel_framework_ii_finite_interpretation",
        "version": FIXED_AMBIENT_REFUTATION_VALIDATION_VERSION,
        "schema_relations": schema_relations,
        "carrier_identity": response.carrier_identity,
        "instance_identity": &instance_identity,
    });
    if response.interpretation_identity != expected_interpretation {
        return Err(validation_failure(
            "fixed-ambient refutation validator changed its complete interpretation identity",
        ));
    }
    validate_identity_digest(
        "interpretation_digest",
        &response.interpretation_identity,
        &response.interpretation_digest,
    )?;
    let expected_validation = json!({
        "kind": "whiel_framework_ii_base_refutation_validation",
        "version": FIXED_AMBIENT_REFUTATION_VALIDATION_VERSION,
        "obligation_identity": response.obligation_identity,
        "interpretation_identity": response.interpretation_identity,
        "axioms_hold": response.axioms_hold,
        "conjecture_holds": response.conjecture_holds,
        "validated_refutation": response.validated_refutation,
    });
    if response.validation_identity != expected_validation {
        return Err(validation_failure(
            "fixed-ambient refutation-validation identity does not bind its exact Lean decisions",
        ));
    }
    validate_identity_digest(
        "validation_digest",
        &response.validation_identity,
        &response.validation_digest,
    )?;
    if !(response.axioms_hold && !response.conjecture_holds && response.validated_refutation) {
        return Ok(FrameworkIIModelValidationOutcome::NotRefutation);
    }
    if source_artifact.kind() != ArtifactKind::Model
        || source_artifact.backend_id() != attempt.artifacts().backend_id()
    {
        return Err(validation_failure(
            "fixed-ambient validated refutation lost its exact Vampire model artifact",
        ));
    }
    if cancellation.should_stop() {
        return Err(FrameworkIISolverError::Cancelled);
    }
    let validation_artifact = attempt
        .artifacts()
        .publish(ArtifactKind::Witness, artifact_payload.into_boxed_slice())
        .map_err(FrameworkIISolverError::Failure)?;
    let evidence = FrameworkIIValidatedRefutationEvidence::new(
        source_artifact,
        response.validation_identity,
        response.validation_digest,
        validation_artifact,
    )
    .map_err(state_failure)?;
    Ok(FrameworkIIModelValidationOutcome::Validated(evidence))
}

fn piece_failure(error: PieceError) -> FrameworkIISolverError {
    match error {
        PieceError::Encoding(error) => error.into(),
        PieceError::Decode(detail) => validation_failure(detail),
        PieceError::Invalid(detail) => validation_failure(detail),
    }
}

/// Render one fixed-ambient problem's literal bytes from prepared bodies.
fn render_problem(
    support: &[Arc<str>],
    axioms: &[PreparedBodyRef],
    goals: &[PreparedBodyRef],
) -> Result<String, FrameworkIISolverError> {
    let support = support.iter().map(AsRef::as_ref).collect::<Vec<&str>>();
    let axioms = axioms
        .iter()
        .map(PreparedBodyRef::tptp_body)
        .collect::<Vec<_>>();
    let goals = goals
        .iter()
        .map(PreparedBodyRef::tptp_body)
        .collect::<Vec<_>>();
    render_fixed_ambient_query(&support, &axioms, &goals).map_err(|error| match error {
        CpuJobError::Cancelled => FrameworkIISolverError::Cancelled,
        other => validation_failure(format!("render a fixed-ambient problem: {other}")),
    })
}

fn validate_identity_digest(
    name: &str,
    identity: &Value,
    digest: &str,
) -> Result<(), FrameworkIISolverError> {
    if canonical_value_sha256(identity) != digest {
        return Err(validation_failure(format!(
            "fixed-ambient {name} does not bind its complete identity"
        )));
    }
    Ok(())
}

/// A model this run could not decode is a fact about one lane's answer,
/// not about the run: the check is inconclusive and the search goes on.
/// Keeping the report lane-local is also what keeps it out of the CPU
/// pool's sticky failure, which would otherwise fail every later job of
/// the run and the pool's own shutdown.
fn model_decode_report(detail: String) -> FailureReport {
    FailureReport::encoding_preparation(
        FailureKind::InfrastructureFailure,
        FailureScope::LaneLocal,
        detail,
    )
}

fn validation_report(detail: String) -> FailureReport {
    FailureReport::encoding_preparation(
        FailureKind::InfrastructureFailure,
        FailureScope::RunGlobal,
        detail,
    )
}

fn cpu_semantic_error(error: CpuJobError) -> FrameworkIISemanticCheckError {
    match error {
        CpuJobError::Cancelled => FrameworkIISemanticCheckError::Cancelled,
        CpuJobError::Failure(report) => FrameworkIISemanticCheckError::Failure(report),
        CpuJobError::Admission(crate::runtime::AdmissionError::Closed(report)) => {
            FrameworkIISemanticCheckError::Failure(report)
        }
        other => FrameworkIISemanticCheckError::Failure(validation_report(format!(
            "fixed-ambient model decoding could not run: {other}"
        ))),
    }
}

fn obligation_identity(
    scope: &FixedAmbientTaskScope,
    snapshot: &LeveledCandidateSnapshot,
    selector: &Value,
) -> Value {
    json!({
        "kind": "whiel_fixed_ambient_obligation",
        "version": FIXED_AMBIENT_OBLIGATION_VERSION,
        "scope_identity": scope.identity(),
        "snapshot": snapshot.worker_identity(),
        "selector": selector,
    })
}

fn validate_entailment_identity(identity: &Value) -> Result<(), FrameworkIISolverError> {
    let Some(object) = identity.as_object() else {
        return Err(validation_failure(
            "fixed-ambient entailment identity is not an object",
        ));
    };
    if object.len() != 2
        || !object.contains_key("axioms")
        || !object.contains_key("conjecture")
        || !object["axioms"].is_array()
        || object["conjecture"].is_null()
    {
        return Err(validation_failure(
            "fixed-ambient entailment identity has unsupported fields",
        ));
    }
    Ok(())
}

/// The exact `sourcePrefix` Lean's fixed-ambient worker computes for one
/// obligation (`FixedAmbientWorker.lean`'s `prepareEntailmentJson`): every
/// prepared body's `source_id` and every `axiom_tags` wire name for this
/// obligation starts with this prefix followed by `.axiom.<index>`,
/// `.conjecture`, `.support.adom`, or `.support.distinct.<index>`.
fn fixed_ambient_obligation_source_prefix(obligation_identity: &Value) -> String {
    format!(
        "framework_ii.fixed_ambient.obligation.{}",
        canonical_value_sha256(obligation_identity)
    )
}

fn validate_prepared_sources(
    obligation_identity: &Value,
    entailment_identity: &Value,
    axioms: &[FixedAmbientPreparedBodyData],
    conjecture: &FixedAmbientPreparedBodyData,
) -> Result<(), FrameworkIISolverError> {
    let expected_axioms = entailment_identity["axioms"]
        .as_array()
        .ok_or_else(|| validation_failure("fixed-ambient entailment omits its axiom list"))?
        .len();
    if axioms.len() != expected_axioms {
        return Err(validation_failure(
            "fixed-ambient worker returned the wrong number of axiom bodies",
        ));
    }
    let prefix = fixed_ambient_obligation_source_prefix(obligation_identity);
    let expected_ids = (0..axioms.len())
        .map(|index| format!("{prefix}.axiom.{index}"))
        .collect::<Vec<_>>();
    if axioms
        .iter()
        .zip(&expected_ids)
        .any(|(body, expected)| body.source_id != *expected)
        || conjecture.source_id != format!("{prefix}.conjecture")
    {
        return Err(validation_failure(
            "fixed-ambient prepared bodies changed their deterministic source identities",
        ));
    }
    Ok(())
}

fn validate_nullary_assignment(
    scope: &FixedAmbientTaskScope,
    assignment: &[WireNullaryAssignment],
) -> Result<(), FrameworkIISolverError> {
    let expected = scope
        .relations()
        .iter()
        .filter(|relation| relation.arity() == 0)
        .map(|relation| relation.key().as_str().to_string())
        .collect::<BTreeSet<_>>();
    let returned = assignment
        .iter()
        .map(|entry| (entry.relation_key.clone(), entry.value))
        .collect::<BTreeMap<_, _>>();
    if returned.len() != assignment.len()
        || returned.keys().cloned().collect::<BTreeSet<_>>() != expected
    {
        return Err(validation_failure(
            "fixed-ambient empty counterexample is not a complete nullary assignment",
        ));
    }
    Ok(())
}

fn validate_attempt_binding(
    prepared: &PreparedFrameworkIIEntailment,
    attempt: &EntailmentAttemptScope,
) -> Result<(), FrameworkIISolverError> {
    if attempt.entailment_identity() != prepared.entailment().identity()
        || attempt.query_artifact() != prepared.entailment().query_artifact()
        || attempt.artifacts().task_identity() != prepared.entailment().task_identity()
        || attempt.artifacts().backend_id() != prepared.entailment().query_artifact().backend_id()
    {
        return Err(validation_failure(
            "fixed-ambient check attempt differs from its prepared entailment",
        ));
    }
    Ok(())
}

fn decode_payload<T: for<'de> Deserialize<'de>>(
    value: Value,
    label: &str,
) -> Result<T, FrameworkIISolverError> {
    serde_json::from_value(value)
        .map_err(|error| validation_failure(format!("decode {label}: {error}")))
}

fn validation_failure(detail: impl Into<String>) -> FrameworkIISolverError {
    FrameworkIISolverError::Failure(FailureReport::encoding_preparation(
        FailureKind::MalformedResult,
        FailureScope::RunGlobal,
        detail,
    ))
}

fn state_failure(error: FrameworkIIStateError) -> FrameworkIISolverError {
    match error {
        FrameworkIIStateError::Cancelled => FrameworkIISolverError::Cancelled,
        other => validation_failure(other.to_string()),
    }
}

fn semantic_error(error: FrameworkIISolverError) -> FrameworkIISemanticCheckError {
    match error {
        FrameworkIISolverError::Cancelled => FrameworkIISemanticCheckError::Cancelled,
        FrameworkIISolverError::Failure(report) => FrameworkIISemanticCheckError::Failure(report),
    }
}

fn semantic_encoding_error(error: EncodingError) -> FrameworkIISemanticCheckError {
    match error {
        EncodingError::Cancelled => FrameworkIISemanticCheckError::Cancelled,
        EncodingError::Failure(report) => FrameworkIISemanticCheckError::Failure(report),
    }
}

#[derive(Clone, Debug)]
pub enum FrameworkIISolverError {
    Cancelled,
    Failure(FailureReport),
}

impl FrameworkIISolverError {
    pub fn failure(&self) -> Option<&FailureReport> {
        match self {
            Self::Cancelled => None,
            Self::Failure(report) => Some(report),
        }
    }
}

impl From<EncodingError> for FrameworkIISolverError {
    fn from(error: EncodingError) -> Self {
        match error {
            EncodingError::Cancelled => Self::Cancelled,
            EncodingError::Failure(report) => Self::Failure(report),
        }
    }
}

impl fmt::Display for FrameworkIISolverError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Cancelled => formatter.write_str("fixed-ambient solver operation was cancelled"),
            Self::Failure(report) => write!(
                formatter,
                "fixed-ambient solver operation failed: origin={:?} kind={:?} detail={}",
                report.origin(),
                report.kind(),
                report.detail().unwrap_or("none")
            ),
        }
    }
}

impl std::error::Error for FrameworkIISolverError {}
