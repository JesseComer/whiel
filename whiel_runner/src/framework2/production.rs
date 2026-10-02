//! Production evidence for checked fixed-ambient solver attempts.
//!
//! These values retain the exact semantic, process, and artifact bindings
//! needed by the leveled controller.  Construction stays crate-private: a
//! solver result is not proof or promotion authority until every binding has
//! been checked and the compact witness has been published.

use std::collections::{BTreeMap, BTreeSet};
use std::fs::File;
use std::future::Future;
use std::io::Read;
use std::path::Path;
use std::pin::Pin;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering as AtomicOrdering};
use std::time::Duration;

use serde_json::{Value, json};

use crate::artifact::{ArtifactKind, ArtifactRef, ArtifactStore, AttemptId};
use crate::encoding::{EncodingError, canonical_value_sha256};
use crate::entailment::assembly::{PremiseRole, Sha256};
use crate::entailment::{Entailment, EntailmentAttemptScope, SpecializedEntailmentCheckReport};
use crate::entailment::{
    SpecializedEntailmentTerminal, check_entailment_attempt_detailed_with_resolver,
    publish_specialized_entailment_terminal,
};
use crate::failure::{FailureKind, FailureReport, FailureScope};
use crate::runtime::{CancellationToken, SolverAdmission};
use crate::task::TaskIdentity;
use crate::vampire::{
    FmbOptions, FmbSize, VampireInvocationOutcome, VampireInvocationProfile, VampireMode,
    VampireModel, VampireProof, VampireProofStrategy, VampireResult, VampireSearchBudget,
    VampireWorkerCommand,
};

use super::FRAMEWORK_II_RUNTIME_CACHE_IDENTITY_VERSION;
use super::catalog::FrameworkIIStateError;
use super::certificate_profiles::{
    SearchProfileProvenance, tagged_conjecture_key, termination_conjecture_key,
};
use super::host_limits::HostLimits;
use super::ledger::{FrameworkIICheckEvidence, FrameworkIICheckOutcome};
use super::ledger::{FrameworkIICheckRequest, FrameworkIICheckRole, FrameworkIIInconclusiveReason};
use super::premise::FrameworkIIPremiseTag;
use super::premise::{
    CitedTaggedPremiseSource, FrameworkIIAxiomTagTable, TaggedPremiseSet,
    cited_tagged_premises_from_proof, core_identity_list, tagged_premise_set,
    tagged_premise_set_at, tagged_premise_set_to_json, termination_tagged_premise_set,
};
use super::snapshot::LeveledCandidateSnapshot;
use super::solver::{FrameworkIISelector, FrameworkIISolverContext};
use super::stabilization::{FrameworkIICheckExecution, FrameworkIIChecker, sealed};

macro_rules! replay_runtime_proof_fields {
    (task_digest: $task_digest:expr, catalog_digest: $catalog_digest:expr, artifact_backend_digest: $artifact_backend_digest:expr, semantic_version: $semantic_version:expr, encoding_version: $encoding_version:expr, framework_ii_context_digest: $framework_ii_context_digest:expr, request_digest: $request_digest:expr, job_id: $job_id:expr, semantic_vc_digest: $semantic_vc_digest:expr, query_digest: $query_digest:expr, query_bytes: $query_bytes:expr, attempt: $attempt:expr, terminal_result_digest: $terminal_result_digest:expr, empty_check_digest: $empty_check_digest:expr, winner: $winner:expr, runtime_invocation: $runtime_invocation:expr, certification_profile: $certification_profile:expr, fixed_ambient_job: $fixed_ambient_job:expr, query_artifact: $query_artifact:expr, proof_artifact: $proof_artifact:expr, terminal_artifact: $terminal_artifact:expr, empty_check_artifact: $empty_check_artifact:expr $(,)?) => {
        json!({
            "domain": "whiel-framework-ii-runtime-proof-receipt-v3",
            "task_digest": $task_digest,
            "catalog_digest": $catalog_digest,
            "artifact_backend_digest": $artifact_backend_digest,
            "semantic_version": $semantic_version,
            "encoding_version": $encoding_version,
            "framework_ii_context_digest": $framework_ii_context_digest,
            "request_digest": $request_digest,
            "job_id": $job_id,
            "semantic_vc_digest": $semantic_vc_digest,
            "query_digest": $query_digest,
            "query_bytes": $query_bytes,
            "attempt": $attempt,
            "terminal_result_digest": $terminal_result_digest,
            "empty_check_digest": $empty_check_digest,
            "winner": $winner,
            "runtime_invocation": $runtime_invocation,
            "certification_profile": $certification_profile,
            "fixed_ambient_job": $fixed_ambient_job,
            "query_artifact": $query_artifact,
            "proof_artifact": $proof_artifact,
            "terminal_artifact": $terminal_artifact,
            "empty_check_artifact": $empty_check_artifact
        })
    };
}
macro_rules! replay_protected_fields {
    (request_digest: $request_digest:expr, selector_registry_digest: $selector_registry_digest:expr, rule: $rule:expr, source_route_digest: $source_route_digest:expr, source_formula_digest: $source_formula_digest:expr, target_vc_digest: $target_vc_digest:expr, fixed_ambient_job: $fixed_ambient_job:expr, theorem_name: $theorem_name:expr, registry_entry_digest: $registry_entry_digest:expr $(,)?) => {
        json!({
            "domain": "whiel-framework-ii-protected-theorem-selection-v3",
            "request_digest": $request_digest,
            "selector_registry_digest": $selector_registry_digest,
            "rule": $rule,
            "source_route_digest": $source_route_digest,
            "source_formula_digest": $source_formula_digest,
            "target_vc_digest": $target_vc_digest,
            "fixed_ambient_job": $fixed_ambient_job,
            "theorem_name": $theorem_name,
            "registry_entry_digest": $registry_entry_digest
        })
    };
}
macro_rules! replay_progress_fields {
    (request_digest: $request_digest:expr, job_id: $job_id:expr, semantic_vc_digest: $semantic_vc_digest:expr, fixed_ambient_job: $fixed_ambient_job:expr, reason: $reason:expr, attempt: $attempt:expr, next_fmb_start_size: $next_fmb_start_size:expr, previous_proof_allowance_ns: $previous_proof_allowance_ns:expr, current_proof_allowance_ns: $current_proof_allowance_ns:expr, peer_failure: $peer_failure:expr, terminal_artifact: $terminal_artifact:expr, terminal_result_digest: $terminal_result_digest:expr $(,)?) => {
        json!({
            "domain": "whiel-framework-ii-entailment-progress-v3",
            "request_digest": $request_digest,
            "job_id": $job_id,
            "semantic_vc_digest": $semantic_vc_digest,
            "fixed_ambient_job": $fixed_ambient_job,
            "reason": $reason,
            "attempt": $attempt,
            "next_fmb_start_size": $next_fmb_start_size,
            "previous_proof_allowance_ns": $previous_proof_allowance_ns,
            "current_proof_allowance_ns": $current_proof_allowance_ns,
            "peer_failure": $peer_failure,
            "terminal_artifact": $terminal_artifact,
            "terminal_result_digest": $terminal_result_digest
        })
    };
}
macro_rules! replay_refutation_fields {
    (request_digest: $request_digest:expr, job_id: $job_id:expr, semantic_vc_digest: $semantic_vc_digest:expr, fixed_ambient_job: $fixed_ambient_job:expr, attempt: $attempt:expr, terminal_artifact: $terminal_artifact:expr, terminal_result_digest: $terminal_result_digest:expr, source_artifact: $source_artifact:expr, validation_identity: $validation_identity:expr, validation_digest: $validation_digest:expr, validation_artifact: $validation_artifact:expr $(,)?) => {
        json!({
            "domain": "whiel-framework-ii-validated-finite-refutation-v4",
            "request_digest": $request_digest,
            "job_id": $job_id,
            "semantic_vc_digest": $semantic_vc_digest,
            "fixed_ambient_job": $fixed_ambient_job,
            "attempt": $attempt,
            "terminal_artifact": $terminal_artifact,
            "terminal_result_digest": $terminal_result_digest,
            "source_artifact": $source_artifact,
            "validation_identity": $validation_identity,
            "validation_digest": $validation_digest,
            "validation_artifact": $validation_artifact
        })
    };
}
macro_rules! replay_reuse_fields {
    (reuse_kind: $reuse_kind:expr, semantic_vc_key: $semantic_vc_key:expr, matched_tagged_premises: $matched_tagged_premises:expr, original_request_digest: $original_request_digest:expr, original_evidence_identity: $original_evidence_identity:expr $(,)?) => {
        json!({
            "kind": "whiel_framework_ii_semantic_reuse",
            "version": FRAMEWORK_II_RUNTIME_CACHE_IDENTITY_VERSION,
            "reuse_kind": $reuse_kind,
            "semantic_vc_key": $semantic_vc_key,
            "matched_tagged_premises": $matched_tagged_premises,
            "original_request_digest": $original_request_digest,
            "original_evidence_identity": $original_evidence_identity
        })
    };
}
macro_rules! replay_obligation_fields {
    (scope_identity: $scope_identity:expr, snapshot: $snapshot:expr, selector: $selector:expr $(,)?) => {
        json!({
            "kind": "whiel_fixed_ambient_obligation",
            "version": FIXED_AMBIENT_OBLIGATION_IDENTITY_VERSION,
            "scope_identity": $scope_identity,
            "snapshot": $snapshot,
            "selector": $selector
        })
    };
}
macro_rules! replay_job_fields {
    (obligation_identity: $obligation_identity:expr, worker_entailment_identity: $worker_entailment_identity:expr $(,)?) => {
        json!({
            "kind": "whiel_fixed_ambient_validity_job",
            "version": FIXED_AMBIENT_VALIDITY_JOB_IDENTITY_VERSION,
            "obligation_identity": $obligation_identity,
            "worker_entailment_identity": $worker_entailment_identity
        })
    };
}
macro_rules! replay_empty_request_fields {
    (scope_identity: $scope_identity:expr, obligation_identity: $obligation_identity:expr, worker_entailment_identity: $worker_entailment_identity:expr $(,)?) => {
        json!({
            "kind": "whiel_fixed_ambient_empty_counterexample_request",
            "version": FIXED_AMBIENT_EMPTY_REQUEST_IDENTITY_VERSION,
            "scope_identity": $scope_identity,
            "obligation_identity": $obligation_identity,
            "worker_entailment_identity": $worker_entailment_identity
        })
    };
}
macro_rules! replay_preparation_fields {
    (scope_identity: $scope_identity:expr, obligation_identity: $obligation_identity:expr, worker_entailment_identity: $worker_entailment_identity:expr, job_id: $job_id:expr, empty_request_identity: $empty_request_identity:expr, empty_request_digest: $empty_request_digest:expr, entailment_identity: $entailment_identity:expr $(,)?) => {
        json!({
            "kind": "whiel_fixed_ambient_obligation_preparation",
            "version": FIXED_AMBIENT_PREPARATION_IDENTITY_VERSION,
            "scope_identity": $scope_identity,
            "obligation_identity": $obligation_identity,
            "worker_entailment_identity": $worker_entailment_identity,
            "job_id": $job_id,
            "empty_request_identity": $empty_request_identity,
            "empty_request_digest": $empty_request_digest,
            "entailment_identity": $entailment_identity
        })
    };
}

const FIXED_AMBIENT_OBLIGATION_IDENTITY_VERSION: u64 = 1;
const FIXED_AMBIENT_PREPARATION_IDENTITY_VERSION: u64 = 1;
const FIXED_AMBIENT_VALIDITY_JOB_IDENTITY_VERSION: u64 = 1;
const FIXED_AMBIENT_EMPTY_REQUEST_IDENTITY_VERSION: u64 = 1;
const FIXED_AMBIENT_EMPTY_CHECK_IDENTITY_VERSION: u64 = 2;
const EDB_PRECONDITION_INIT_THEOREM: &str =
    "Whiel.Synthesis.FrameworkII.FixedAmbient.EdbPrecondition.initVC_valid";
const EDB_PRECONDITION_MAINT_THEOREM: &str =
    "Whiel.Synthesis.FrameworkII.FixedAmbient.EdbPrecondition.maintenanceVC_valid";
const PROTECTED_THEOREM_SELECTOR_REGISTRY_VERSION: u64 = 2;

#[derive(Debug)]
enum FrameworkIIReceiptError {
    State(FrameworkIIStateError),
    Failure(FailureReport),
}

impl From<FrameworkIIStateError> for FrameworkIIReceiptError {
    fn from(error: FrameworkIIStateError) -> Self {
        Self::State(error)
    }
}

// ------------------------------------------------------------
// Check Subjects: Clause Requests And The Termination Request
// ------------------------------------------------------------

const FRAMEWORK_II_TERMINATION_REQUEST_IDENTITY_VERSION: u64 = 1;

/// The epoch's termination request over one Core (`houdini.tex` Section 4.3
/// and Section 4.4, Table 1, row `Term(F)`).
///
/// Unlike a clause request this names no clause and no level: its tagged
/// conjecture is the fixed `(Term, post')` and its tagged premise set is
/// `{not_guard} ∪ {collapsed(d) : d ∈ Core}`, whose key representation is
/// the Core's sorted Lean-issued identity list without levels. Two epochs
/// whose Core clause set did not change therefore produce the identical
/// key and the second is answered from the dictionary without a launch.
#[derive(Clone, Debug)]
pub struct FrameworkIITerminationRequest {
    core: Arc<LeveledCandidateSnapshot>,
    core_identities: Arc<[Arc<str>]>,
    identity: Arc<Value>,
    request_digest: Arc<str>,
}

impl FrameworkIITerminationRequest {
    pub(crate) fn new(core: Arc<LeveledCandidateSnapshot>) -> Self {
        let core_identities: Arc<[Arc<str>]> = Arc::from(core_identity_list(&core));
        let identity = Arc::new(termination_request_identity(&core));
        let request_digest = Arc::from(canonical_value_sha256(identity.as_ref()));
        Self {
            core,
            core_identities,
            identity,
            request_digest,
        }
    }

    /// The Core this termination request ranges over.
    pub fn core(&self) -> &Arc<LeveledCandidateSnapshot> {
        &self.core
    }

    /// The Core's sorted Lean-issued clause identities, without levels —
    /// the premise representation of this request's semantic key.
    pub fn core_identities(&self) -> &[Arc<str>] {
        &self.core_identities
    }

    pub fn identity(&self) -> &Value {
        &self.identity
    }

    pub fn request_digest(&self) -> &str {
        &self.request_digest
    }

    fn has_current_identity(&self) -> bool {
        let identity = termination_request_identity(&self.core);
        identity == *self.identity
            && canonical_value_sha256(&identity) == self.request_digest.as_ref()
    }
}

fn termination_request_identity(core: &LeveledCandidateSnapshot) -> Value {
    json!({
        "kind": "whiel_framework_ii_termination_request",
        "version": FRAMEWORK_II_TERMINATION_REQUEST_IDENTITY_VERSION,
        "scope_identity": core.scope().identity(),
        "snapshot": core.worker_identity(),
    })
}

/// Which obligation a prepared entailment is bound to, independent of the
/// controller request that asked for it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FrameworkIISubjectTarget {
    Clause {
        clause: crate::houdini::ClauseId,
        level: super::types::FrameworkIILevel,
        role: FrameworkIICheckRole,
    },
    Termination,
}

/// One request the production checker can serve: an ordinary clause check
/// issued by the controller's ledger, or the epoch's termination check over
/// the current Core. Both are requests of `houdini.tex` Table 1 and both go
/// through `Check(q)` — the dictionary first, then the worker and solver.
#[derive(Clone, Debug)]
pub(crate) enum FrameworkIICheckSubject {
    Clause(FrameworkIICheckRequest),
    Termination(FrameworkIITerminationRequest),
}

impl FrameworkIICheckSubject {
    pub(crate) fn snapshot(&self) -> &Arc<LeveledCandidateSnapshot> {
        match self {
            Self::Clause(request) => request.snapshot(),
            Self::Termination(request) => request.core(),
        }
    }

    pub(crate) fn request_digest(&self) -> &str {
        match self {
            Self::Clause(request) => request.request_digest(),
            Self::Termination(request) => request.request_digest(),
        }
    }

    pub(crate) fn target(&self) -> FrameworkIISubjectTarget {
        match self {
            Self::Clause(request) => FrameworkIISubjectTarget::Clause {
                clause: request.clause(),
                level: request.level(),
                role: request.role(),
            },
            Self::Termination(_) => FrameworkIISubjectTarget::Termination,
        }
    }

    pub(crate) fn selector(&self) -> FrameworkIISelector {
        match self {
            Self::Clause(request) => FrameworkIISelector::from_check_request(request),
            Self::Termination(_) => FrameworkIISelector::Termination,
        }
    }

    pub(crate) fn has_current_identity(&self) -> bool {
        match self {
            Self::Clause(request) => request.has_current_identity(),
            Self::Termination(request) => request.has_current_identity(),
        }
    }

    /// Whether the controller already suspended this request's clause for
    /// the epoch, so the dictionary may answer it but no solver may be
    /// launched for it. Never set for the termination request, which names
    /// no clause and is never suspended.
    pub(crate) fn launch_suppressed(&self) -> bool {
        match self {
            Self::Clause(request) => request.launch_suppressed(),
            Self::Termination(_) => false,
        }
    }

    pub(crate) fn as_clause(&self) -> Option<&FrameworkIICheckRequest> {
        match self {
            Self::Clause(request) => Some(request),
            Self::Termination(_) => None,
        }
    }
}

impl From<FrameworkIICheckRequest> for FrameworkIICheckSubject {
    fn from(request: FrameworkIICheckRequest) -> Self {
        Self::Clause(request)
    }
}

impl From<FrameworkIITerminationRequest> for FrameworkIICheckSubject {
    fn from(request: FrameworkIITerminationRequest) -> Self {
        Self::Termination(request)
    }
}

// ------------------------------------------------------------
// Prepared Semantic Entailment
// ------------------------------------------------------------

/// One Lean-prepared fixed-ambient obligation and its exact solver package.
#[derive(Clone, Debug)]
pub struct PreparedFrameworkIIEntailment {
    replay_control_subject: Result<ReplayControlSubject, ReplayProductionError>,
    control_request_digest: Arc<str>,
    control_target: FrameworkIISubjectTarget,
    control_snapshot: Arc<LeveledCandidateSnapshot>,
    prepare_request_identity: Arc<Value>,
    prepare_request_digest: Arc<str>,
    scope_digest: Arc<str>,
    catalog_digest: Arc<str>,
    partition_digest: Arc<str>,
    framework_context_digest: Arc<str>,
    job_id: Arc<str>,
    base_obligation_identity: Arc<Value>,
    base_obligation_digest: Arc<str>,
    /// The structural identity of the entailment this preparation denotes:
    /// the ordered Lean-issued formula identities of its axioms together
    /// with its conjecture's.
    ///
    /// Rust computes it (Pass 7.5d assembles the problem from cached opaque
    /// pieces, so no worker call produces it), but it is never taken on
    /// trust: every field of it is a Lean-issued component identity
    /// admitted with the clause or the task, and the worker confirms the
    /// assembled value verbatim twice on the production path — at the
    /// empty-instance check (`check_empty_counterexample`) and at
    /// refutation validation, both of which fail closed when the identity
    /// they are handed differs from the one they compute for the problem
    /// they were given. That double confirmation is the production path's
    /// soundness argument for a locally assembled obligation; the assembly
    /// differential (`set_assembly_differential`) is a development-time
    /// safety net on top of it, not what makes it sound.
    ///
    /// It stays under the wire name `worker_entailment_identity` in every
    /// identity payload and every Lean-facing request: those names are on
    /// digested, pinned schemas.
    entailment_identity: Arc<Value>,
    empty_request_digest: Arc<str>,
    empty_request_identity: Arc<Value>,
    entailment: Entailment,
    /// The `axiom_tags` table of this exact preparation: the tag Lean
    /// assigns each axiom of the assembled problem, keyed by the short
    /// TPTP name `render_query` gives it. Rust builds this table itself
    /// from the splice recipe (Pass 7.5d) and the differential compares it
    /// against the worker's own, so every preparation carries one and
    /// proof-subsumption caching never has to guess a tag.
    axiom_tags: FrameworkIIAxiomTagTable,
}

impl PreparedFrameworkIIEntailment {
    /// Construct the production handle from one exact fixed-ambient worker job.
    pub(crate) fn from_fixed_ambient_job(
        subject: &FrameworkIICheckSubject,
        obligation_identity: Value,
        entailment_identity: Value,
        entailment: Entailment,
        axiom_tags: FrameworkIIAxiomTagTable,
    ) -> Result<Self, FrameworkIIStateError> {
        let request = subject;
        if !request.has_current_identity() {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "a fixed-ambient request lost its full structural identity",
            ));
        }
        if request.snapshot().scope().task_identity() != entailment.task_identity() {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "a fixed-ambient entailment belongs to another task",
            ));
        }
        let selector = request.selector().identity();
        let expected_obligation_identity = replay_obligation_fields! {
            scope_identity: request.snapshot().scope().identity(),
            snapshot: request.snapshot().worker_identity(),
            selector: &selector
        };
        if obligation_identity != expected_obligation_identity {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "the fixed-ambient worker prepared another exact obligation",
            ));
        }
        let Some(worker_entailment_fields) = entailment_identity.as_object() else {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "the fixed-ambient worker entailment identity is not structural",
            ));
        };
        if worker_entailment_fields.len() != 2
            || !worker_entailment_fields.contains_key("axioms")
            || !worker_entailment_fields.contains_key("conjecture")
            || !worker_entailment_fields["axioms"].is_array()
            || worker_entailment_fields["conjecture"].is_null()
        {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "the fixed-ambient worker entailment identity has unsupported fields",
            ));
        }
        if entailment.fixed_ambient_identity() != Some(&entailment_identity) {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "the fixed-ambient query package retained another Lean entailment identity",
            ));
        }
        let base_obligation_digest: Arc<str> =
            Arc::from(canonical_value_sha256(&obligation_identity));
        let framework_context_digest = Arc::clone(&base_obligation_digest);
        let job_identity = replay_job_fields! {
            obligation_identity: &obligation_identity,
            worker_entailment_identity: &entailment_identity
        };
        let job_id: Arc<str> = Arc::from(canonical_value_sha256(&job_identity));
        let empty_request_identity = replay_empty_request_fields! {
            scope_identity: request.snapshot().scope().identity(),
            obligation_identity: &obligation_identity,
            worker_entailment_identity: &entailment_identity
        };
        let empty_request_digest: Arc<str> =
            Arc::from(canonical_value_sha256(&empty_request_identity));
        let preparation_identity = replay_preparation_fields! {
            scope_identity: request.snapshot().scope().identity(),
            obligation_identity: &obligation_identity,
            worker_entailment_identity: &entailment_identity,
            job_id: job_id.as_ref(),
            empty_request_identity: &empty_request_identity,
            empty_request_digest: empty_request_digest.as_ref(),
            entailment_identity: entailment.identity()
        };
        let preparation_digest: Arc<str> = Arc::from(canonical_value_sha256(&preparation_identity));
        Ok(Self {
            replay_control_subject: replay_subject_projection(subject),
            control_request_digest: Arc::from(request.request_digest()),
            control_target: request.target(),
            control_snapshot: Arc::clone(request.snapshot()),
            prepare_request_identity: Arc::new(preparation_identity),
            prepare_request_digest: preparation_digest,
            scope_digest: Arc::from(request.snapshot().scope().identity_sha256()),
            catalog_digest: Arc::from(request.snapshot().catalog_instance_digest()),
            partition_digest: Arc::from(request.snapshot().partition_digest()),
            framework_context_digest,
            job_id,
            base_obligation_identity: Arc::new(obligation_identity),
            base_obligation_digest,
            entailment_identity: Arc::new(entailment_identity),
            empty_request_digest,
            empty_request_identity: Arc::new(empty_request_identity),
            entailment,
            axiom_tags,
        })
    }

    pub(crate) fn axiom_tags(&self) -> &FrameworkIIAxiomTagTable {
        &self.axiom_tags
    }

    pub fn control_request_digest(&self) -> &str {
        &self.control_request_digest
    }

    pub fn prepare_request_digest(&self) -> &str {
        &self.prepare_request_digest
    }

    pub(crate) fn prepare_request_identity(&self) -> &Value {
        &self.prepare_request_identity
    }

    pub fn scope_digest(&self) -> &str {
        &self.scope_digest
    }

    pub fn catalog_digest(&self) -> &str {
        &self.catalog_digest
    }

    pub fn partition_digest(&self) -> &str {
        &self.partition_digest
    }

    pub fn framework_context_digest(&self) -> &str {
        &self.framework_context_digest
    }

    pub fn job_id(&self) -> &str {
        &self.job_id
    }

    pub fn semantic_vc_digest(&self) -> &str {
        &self.base_obligation_digest
    }

    pub fn base_obligation_digest(&self) -> &str {
        &self.base_obligation_digest
    }

    pub(crate) fn base_obligation_identity(&self) -> &Value {
        &self.base_obligation_identity
    }

    /// See the field of the same name: Rust-computed, confirmed verbatim by
    /// the worker at the empty-instance check and at refutation validation.
    pub(crate) fn entailment_identity(&self) -> &Value {
        &self.entailment_identity
    }

    pub fn empty_request_digest(&self) -> &str {
        &self.empty_request_digest
    }

    pub(crate) fn empty_request_identity(&self) -> &Value {
        &self.empty_request_identity
    }

    pub(crate) fn bound_worker_obligation_payload(&self) -> Value {
        let selector = match self.control_target {
            FrameworkIISubjectTarget::Clause { clause, role, .. } => {
                let kind = match role {
                    FrameworkIICheckRole::Initialization => "initialization",
                    FrameworkIICheckRole::Maintenance => "maintenance",
                };
                json!({"clause_id": clause.get(), "kind": kind})
            }
            FrameworkIISubjectTarget::Termination => json!({"kind": "termination"}),
        };
        json!({
            "obligation_identity": self.base_obligation_identity(),
            "selector": selector,
            "snapshot": self.control_snapshot.worker_payload(),
        })
    }

    pub(crate) fn entailment(&self) -> &Entailment {
        &self.entailment
    }

    /// The same preparation over a re-tagged rendering of its own query.
    ///
    /// `with_premise_role` changes nothing but the role word each premise
    /// carries, so the structural identity, the Lean-issued entailment
    /// identity and the `axiom_tags` table are the same values; only the
    /// published query artifact differs. Everything else this preparation
    /// denotes is carried over untouched.
    fn with_entailment(&self, entailment: Entailment) -> Result<Self, FrameworkIIStateError> {
        if entailment.identity() != self.entailment.identity()
            || entailment.task_identity() != self.entailment.task_identity()
        {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "a re-tagged entailment denotes another exact obligation",
            ));
        }
        Ok(Self {
            entailment,
            ..self.clone()
        })
    }

    pub fn required_constants(&self) -> &[crate::task::ConstantKey] {
        self.entailment.constants()
    }

    /// Rebind an identical semantic request to a later ledger ordinal.
    ///
    /// The control request digest includes the attempt ordinal, while Lean's
    /// preparation request does not.  Rebinding therefore changes only that
    /// control link after checking the complete selector and immutable scope.
    pub(crate) fn rebind_control_request(
        &self,
        subject: &FrameworkIICheckSubject,
    ) -> Result<Self, FrameworkIIStateError> {
        if !self.binds_subject(subject) {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "a cached fixed-ambient preparation cannot be rebound to another semantic request",
            ));
        }
        let mut rebound = self.clone();
        rebound.control_request_digest = Arc::from(subject.request_digest());
        rebound.replay_control_subject = replay_subject_projection(subject);
        Ok(rebound)
    }

    /// Everything but the control request digest: the exact obligation this
    /// preparation denotes.
    fn binds_subject(&self, subject: &FrameworkIICheckSubject) -> bool {
        subject.has_current_identity()
            && self.control_target == subject.target()
            && self.control_snapshot.same_partition(subject.snapshot())
            && self.scope_digest() == subject.snapshot().scope().identity_sha256()
            && self.catalog_digest() == subject.snapshot().catalog_instance_digest()
            && self.partition_digest() == subject.snapshot().partition_digest()
            && self.entailment.task_identity() == subject.snapshot().scope().task_identity()
    }

    fn matches_subject(&self, subject: &FrameworkIICheckSubject) -> bool {
        self.control_request_digest() == subject.request_digest() && self.binds_subject(subject)
    }
}

/// Snapshot-bound successful empty-domain result from the fixed-ambient worker.
#[derive(Clone, Debug)]
pub struct FrameworkIIEmptyCheckEvidence {
    request_digest: Arc<str>,
    obligation_digest: Arc<str>,
    check_identity: Arc<Value>,
    check_digest: Arc<str>,
    artifact: ArtifactRef,
}

impl FrameworkIIEmptyCheckEvidence {
    pub(crate) fn new_no_counterexample(
        request_digest: impl Into<Arc<str>>,
        obligation_digest: impl Into<Arc<str>>,
        check_identity: Value,
        check_digest: impl Into<Arc<str>>,
        artifact: ArtifactRef,
    ) -> Result<Self, FrameworkIIStateError> {
        let request_digest = request_digest.into();
        let obligation_digest = obligation_digest.into();
        let check_digest = check_digest.into();
        for (name, digest) in [
            ("empty-check request", request_digest.as_ref()),
            ("fixed-ambient obligation", obligation_digest.as_ref()),
            ("empty-instance check", check_digest.as_ref()),
        ] {
            require_sha256(name, digest)?;
        }
        if canonical_value_sha256(&check_identity) != check_digest.as_ref() {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "the fixed-ambient empty-check digest does not bind its full identity",
            ));
        }
        let Some(fields) = check_identity.as_object() else {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "the fixed-ambient empty-check identity is not structural",
            ));
        };
        if fields.len() != 7
            || fields.get("kind").and_then(Value::as_str)
                != Some("whiel_fixed_ambient_empty_counterexample_check")
            || fields.get("version").and_then(Value::as_u64)
                != Some(FIXED_AMBIENT_EMPTY_CHECK_IDENTITY_VERSION)
            || fields.get("decision_definition").and_then(Value::as_str)
                != Some("QFEntailment.adomEmptyCounterexample?")
            || fields.get("result") != Some(&json!({"kind": "no_counterexample"}))
            || fields
                .get("empty_request_identity")
                .is_none_or(|identity| canonical_value_sha256(identity) != request_digest.as_ref())
            || fields.get("obligation_identity").is_none_or(|identity| {
                canonical_value_sha256(identity) != obligation_digest.as_ref()
            })
            || !fields.contains_key("worker_entailment_identity")
        {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "the fixed-ambient no-counterexample identity changed its exact request or result",
            ));
        }
        Ok(Self {
            request_digest,
            obligation_digest,
            check_identity: Arc::new(check_identity),
            check_digest,
            artifact,
        })
    }

    pub fn request_digest(&self) -> &str {
        &self.request_digest
    }

    pub fn obligation_digest(&self) -> &str {
        &self.obligation_digest
    }

    pub fn check_digest(&self) -> &str {
        &self.check_digest
    }

    pub fn check_identity(&self) -> &Value {
        &self.check_identity
    }

    pub fn artifact(&self) -> ArtifactRef {
        self.artifact
    }
}

/// Accepted Lean validation response before the terminal refutation receipt.
#[derive(Clone, Debug)]
pub(crate) struct FrameworkIIValidatedRefutationEvidence {
    source_artifact: ArtifactRef,
    validation_identity: Value,
    validation_digest: Arc<str>,
    validation_artifact: ArtifactRef,
}

impl FrameworkIIValidatedRefutationEvidence {
    pub(crate) fn new(
        source_artifact: ArtifactRef,
        validation_identity: Value,
        validation_digest: impl Into<Arc<str>>,
        validation_artifact: ArtifactRef,
    ) -> Result<Self, FrameworkIIStateError> {
        let validation_digest = validation_digest.into();
        require_sha256("finite-refutation validation", &validation_digest)?;
        if canonical_value_sha256(&validation_identity) != validation_digest.as_ref() {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "the finite-refutation validation digest does not bind its full identity",
            ));
        }
        if !matches!(
            source_artifact.kind(),
            ArtifactKind::EmptyInstanceCheck | ArtifactKind::Model
        ) || validation_artifact.kind() != ArtifactKind::Witness
            || source_artifact.backend_id() != validation_artifact.backend_id()
        {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "only a same-backend Lean-validated empty check or finite model can become refutation evidence",
            ));
        }
        Ok(Self {
            source_artifact,
            validation_identity,
            validation_digest,
            validation_artifact,
        })
    }
}

/// Fully resolved specialized attempt before its durable authority is built.
#[derive(Clone, Debug)]
#[allow(clippy::large_enum_variant)]
pub(crate) enum FrameworkIIResolvedAttempt {
    Proved {
        proof: VampireProof,
        empty_check: FrameworkIIEmptyCheckEvidence,
    },
    Refuted(FrameworkIIValidatedRefutationEvidence),
    Inconclusive {
        reason: FrameworkIIInconclusiveReason,
        next_fmb_start_size: Option<FmbSize>,
        peer_failure: Option<FailureReport>,
        reuse_attempt: bool,
    },
}

#[derive(Clone, Debug)]
pub(crate) enum FrameworkIIEmptyCheckOutcome {
    NoCounterexample(FrameworkIIEmptyCheckEvidence),
    ValidatedRefutation(FrameworkIIValidatedRefutationEvidence),
}

impl FrameworkIIEmptyCheckOutcome {
    pub(crate) fn check_identity(&self) -> &Value {
        match self {
            Self::NoCounterexample(evidence) => evidence.check_identity(),
            Self::ValidatedRefutation(evidence) => &evidence.validation_identity,
        }
    }

    pub(crate) fn check_digest(&self) -> &str {
        match self {
            Self::NoCounterexample(evidence) => evidence.check_digest(),
            Self::ValidatedRefutation(evidence) => &evidence.validation_digest,
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) enum FrameworkIIModelValidationOutcome {
    Validated(FrameworkIIValidatedRefutationEvidence),
    NotRefutation,
}

#[derive(Clone, Debug)]
pub(crate) enum FrameworkIISemanticCheckError {
    Cancelled,
    Failure(FailureReport),
}

/// Semantic preparation before any solver-side effect.
#[derive(Clone, Debug)]
#[allow(clippy::large_enum_variant)]
pub enum FrameworkIIPreCheckOutcome {
    Applied(PreparedFrameworkIIEntailment),
    Failure(FailureReport),
}

/// Exact semantic callbacks supplied by the persistent fixed-ambient worker.
pub(crate) trait FrameworkIISemanticAdapter: Send + Sized + 'static {
    /// A handle onto the same underlying semantic state, usable from a
    /// concurrent task.
    ///
    /// `None` — the default — means this adapter's state cannot be shared,
    /// and a batch resolves its launches one at a time on the adapter it
    /// already holds. The production adapter's caches all sit behind shared
    /// handles, so it returns a clone.
    fn concurrent_handle(&self) -> Option<Self> {
        None
    }

    /// Identify the persistent Lean context when this is the production
    /// fixed-ambient semantic adapter.
    fn encoding_context_id(&self) -> Option<&str> {
        None
    }

    /// Confirm that this adapter retains the exact persistent solver state.
    fn matches_solver_context(&self, _solver: &FrameworkIISolverContext) -> bool {
        false
    }

    fn prepare<'a>(
        &'a mut self,
        subject: &'a FrameworkIICheckSubject,
        admission: &'a SolverAdmission,
        artifacts: &'a ArtifactStore,
        cancellation: &'a CancellationToken,
    ) -> Pin<
        Box<
            dyn Future<Output = Result<FrameworkIIPreCheckOutcome, FrameworkIIStateError>>
                + Send
                + 'a,
        >,
    >;

    fn check_empty<'a>(
        &'a mut self,
        prepared: &'a PreparedFrameworkIIEntailment,
        attempt: &'a EntailmentAttemptScope,
        admission: &'a SolverAdmission,
        cancellation: &'a CancellationToken,
    ) -> Pin<
        Box<
            dyn Future<Output = Result<FrameworkIIEmptyCheckOutcome, FrameworkIISemanticCheckError>>
                + Send
                + 'a,
        >,
    >;

    /// Validate one nonempty solver finite model through Lean against the
    /// exact prepared obligation.
    fn validate_model<'a>(
        &'a mut self,
        prepared: &'a PreparedFrameworkIIEntailment,
        attempt: &'a EntailmentAttemptScope,
        model: VampireModel,
        admission: &'a SolverAdmission,
        cancellation: &'a CancellationToken,
    ) -> Pin<
        Box<
            dyn Future<
                    Output = Result<
                        FrameworkIIModelValidationOutcome,
                        FrameworkIISemanticCheckError,
                    >,
                > + Send
                + 'a,
        >,
    >;

    /// Resolve the one reviewed theorem-route selector for a protected row.
    ///
    /// The production adapter asks Lean to confirm that the bound job's row
    /// is one of its extracted precondition rows before any candidate exists.
    /// The default is deliberately fail-closed: a semantic adapter may omit
    /// this callback only when the requested row is not protected.
    fn protected_theorem_candidate<'a>(
        &'a mut self,
        subject: &'a FrameworkIICheckSubject,
        _prepared: &'a PreparedFrameworkIIEntailment,
        _admission: &'a SolverAdmission,
        _cancellation: &'a CancellationToken,
    ) -> Pin<
        Box<
            dyn Future<
                    Output = Result<
                        Option<FrameworkIIProtectedTheoremCandidate>,
                        FrameworkIIStateError,
                    >,
                > + Send
                + 'a,
        >,
    > {
        Box::pin(async move {
            // The termination request names no clause, so it is never a
            // protected row.
            let protected = subject.as_clause().is_some_and(|request| {
                request
                    .snapshot()
                    .records()
                    .get(&request.clause())
                    .is_some_and(|record| record.is_protected())
            });
            if protected {
                Err(FrameworkIIStateError::InvalidEvidence(
                    "a protected fixed-ambient row has no reviewed theorem selection",
                ))
            } else {
                Ok(None)
            }
        })
    }
}

/// Worker-checked input to the reviewed EDB-precondition derivation registry.
#[derive(Clone, Debug)]
pub(crate) struct FrameworkIIProtectedTheoremCandidate {
    source_route_digest: Arc<str>,
    source_formula_digest: Arc<str>,
    unchanged_relations_digest: Arc<str>,
    theorem_name: Arc<str>,
}

impl FrameworkIIProtectedTheoremCandidate {
    pub(crate) fn new(
        role: FrameworkIICheckRole,
        source_route_digest: impl Into<Arc<str>>,
        source_formula_identity: &Value,
        referenced_relations: &[String],
        theorem_name: impl Into<Arc<str>>,
    ) -> Result<Self, FrameworkIIStateError> {
        let source_route_digest = source_route_digest.into();
        require_sha256("protected precondition route", &source_route_digest)?;
        let structural_identity = match source_formula_identity {
            Value::Object(values) => !values.is_empty(),
            Value::Array(values) => !values.is_empty(),
            _ => false,
        };
        let relation_keys = referenced_relations
            .iter()
            .map(String::as_str)
            .collect::<std::collections::BTreeSet<_>>();
        if !structural_identity || relation_keys.len() != referenced_relations.len() {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "a protected route lacks canonical Lean source-formula metadata",
            ));
        }
        let theorem_name = theorem_name.into();
        let expected_theorem = match role {
            FrameworkIICheckRole::Initialization => EDB_PRECONDITION_INIT_THEOREM,
            FrameworkIICheckRole::Maintenance => EDB_PRECONDITION_MAINT_THEOREM,
        };
        if theorem_name.as_ref() != expected_theorem {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "a protected route changed its allowlisted Lean theorem",
            ));
        }
        let source_formula_digest: Arc<str> =
            Arc::from(canonical_value_sha256(source_formula_identity));
        let unchanged_relations_digest = Arc::from(canonical_value_sha256(&json!({
            "domain": "whiel-framework-ii-edb-relation-keys-v2",
            "source_route_digest": source_route_digest.as_ref(),
            "source_formula_digest": source_formula_digest.as_ref(),
            "relation_keys": relation_keys.into_iter().collect::<Vec<_>>(),
        })));
        Ok(Self {
            source_route_digest,
            source_formula_digest,
            unchanged_relations_digest,
            theorem_name,
        })
    }
}

/// The run's **retry policy** (`houdini.tex` Section 4.7, host options): a
/// finite, strictly increasing list of solver allowances for relaunching
/// one inconclusive dictionary key on later epochs.
///
/// The first launch of any key runs under `a_1`, the `k`-th under `a_k`,
/// and each launch runs under the lesser of its allowance and the run
/// deadline (the run deadline is the search's own `CancellationToken`,
/// which stops any launch that outlives it). After the list is exhausted
/// the key is a permanent dictionary hit for the run. Within one epoch a
/// key is launched at most once — see
/// [`FrameworkIIProductionChecker::begin_epoch`].
///
/// Whether the escalation a retried launch buys is spent on the direct
/// strategy or split with the CASC portfolio is the run's
/// [`CascPortfolioPolicy`], carried here and recorded in the run
/// configuration. `Enabled`, the launch runs under
/// `VampireSearchBudget::cumulative(baseline, a_k)`, so the run's
/// [`crate::vampire::ProofCascPolicy`] applies its initial share to
/// `baseline` and its retry-added share to `a_k - baseline`. `Disabled` —
/// the default — the launch runs under `VampireSearchBudget::finite(a_k)`
/// with the CASC policy off entirely, so the whole allowance, escalation
/// included, is direct.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FrameworkIIRetryPolicy {
    /// The direct-search portion every launch of this policy runs under.
    /// Kept separately from `a_1`: a `cumulative` run budget adds a CASC
    /// share on top of its baseline, and that whole total is what the
    /// first launch has always been given.
    baseline: Duration,
    allowances: Arc<[Duration]>,
    casc_portfolio: CascPortfolioPolicy,
}

/// Whether this run may run and certify the `casc_2025` portfolio at all.
///
/// `Enabled`, a proof-lane launch spends the run's
/// [`crate::vampire::ProofCascPolicy`] share of its allowance on the
/// portfolio once the direct strategy has exhausted its own prefix or
/// returned unknown, a condition the portfolio proves is labelled
/// `casc_2025`, and certification runs that condition's job under the
/// pinned `casc_2025` leancheck vector. `Disabled`:
///
/// - the retry escalation's profile split is direct-only, so a launch's
///   whole allowance — baseline and escalation alike — runs the direct
///   strategy and no launch can produce a `casc_2025` winner; and
/// - [`super::freeze::FrozenLeveledCore::freeze`] refuses a Core that
///   carries a `casc_2025` label anyway, so a record that contradicts its
///   own run fails at the freeze rather than at certification.
///
/// The two are different searches, not a fast and a slow route to the same
/// one: a condition is reached under one and not the other, so which was
/// used belongs in the run configuration that decides comparability.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CascPortfolioPolicy {
    #[default]
    Disabled,
    Enabled,
}

impl CascPortfolioPolicy {
    pub fn is_enabled(self) -> bool {
        matches!(self, Self::Enabled)
    }

    /// The stable wire name the run configuration records.
    pub fn name(self) -> &'static str {
        match self {
            Self::Disabled => "disabled",
            Self::Enabled => "enabled",
        }
    }

    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "disabled" => Some(Self::Disabled),
            "enabled" => Some(Self::Enabled),
            _ => None,
        }
    }
}

impl FrameworkIIRetryPolicy {
    /// A finite, strictly increasing, nonempty list of allowances. The
    /// direct-search baseline is `a_1`, so every launch splits at the first
    /// allowance.
    pub fn new(
        allowances: impl IntoIterator<Item = Duration>,
    ) -> Result<Self, FrameworkIIStateError> {
        let allowances: Vec<Duration> = allowances.into_iter().collect();
        let Some(first) = allowances.first().copied() else {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "a fixed-ambient retry policy needs at least one solver allowance",
            ));
        };
        Self::with_baseline(first, allowances)
    }

    fn with_baseline(
        baseline: Duration,
        allowances: Vec<Duration>,
    ) -> Result<Self, FrameworkIIStateError> {
        let Some(first) = allowances.first().copied() else {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "a fixed-ambient retry policy needs at least one solver allowance",
            ));
        };
        if first.is_zero() || baseline.is_zero() {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "fixed-ambient retry allowances must all be positive",
            ));
        }
        if baseline > first {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "a fixed-ambient retry policy's direct-search baseline exceeds its first allowance",
            ));
        }
        if allowances.windows(2).any(|pair| pair[1] <= pair[0]) {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "a fixed-ambient retry policy must be strictly increasing",
            ));
        }
        Ok(Self {
            baseline,
            allowances: allowances.into(),
            casc_portfolio: CascPortfolioPolicy::default(),
        })
    }

    /// This policy under an explicit [`CascPortfolioPolicy`].
    pub fn with_casc_portfolio(mut self, casc_portfolio: CascPortfolioPolicy) -> Self {
        self.casc_portfolio = casc_portfolio;
        self
    }

    /// Whether this run may run and certify the `casc_2025` portfolio.
    pub fn casc_portfolio(&self) -> CascPortfolioPolicy {
        self.casc_portfolio
    }

    /// The mapping from the legacy adaptive-retry configuration onto the
    /// contract's allowance list.
    ///
    /// The budget's **total** is `a_1`: a `cumulative(initial, total)` run
    /// budget has always given its first launch the whole total, including
    /// the CASC-added share, and the retry contract must not shorten it.
    /// Each configured increment adds one further allowance,
    /// `a_k = a_{k-1} + increment_k`. The budget's `initial` is retained
    /// separately as the direct-search baseline, so launch `k` runs under
    /// `cumulative(initial, a_k)` and the `ProofCascPolicy` split is
    /// unchanged. For a `finite` budget total equals initial and the ladder
    /// is the familiar `[t, 2t, 3t]`.
    pub fn from_budget_and_increments(
        budget: VampireSearchBudget,
        increments: impl IntoIterator<Item = Duration>,
    ) -> Result<Self, FrameworkIIStateError> {
        let (Some(initial), Some(total)) = (budget.initial_limit(), budget.total_limit()) else {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "a fixed-ambient retry policy requires a finite proof-search baseline",
            ));
        };
        let mut allowances = vec![total];
        for increment in increments {
            if increment.is_zero() {
                return Err(FrameworkIIStateError::InvalidEvidence(
                    "fixed-ambient retry increments must all be positive",
                ));
            }
            let last = *allowances
                .last()
                .expect("the allowance list starts with the run budget's total");
            allowances.push(last.checked_add(increment).ok_or(
                FrameworkIIStateError::InvalidEvidence(
                    "fixed-ambient cumulative retry allowances overflow Duration",
                ),
            )?);
        }
        Self::with_baseline(initial, allowances)
    }

    /// The direct-search portion every launch of this policy runs under.
    pub fn baseline(&self) -> Duration {
        self.baseline
    }

    /// The complete allowance list, `a_1` first.
    pub fn allowances(&self) -> &[Duration] {
        &self.allowances
    }

    /// How many launches the policy grants one key over the whole run.
    pub fn granted_launches(&self) -> usize {
        self.allowances.len()
    }

    /// The allowance of the launch that follows `launches_so_far` earlier
    /// launches of the same key, or `None` when the policy grants no
    /// further launch and the key is a permanent dictionary hit.
    pub fn allowance_after(&self, launches_so_far: usize) -> Option<Duration> {
        self.allowances.get(launches_so_far).copied()
    }

    /// The budget one launch runs under.
    ///
    /// With the CASC portfolio enabled: the policy's direct-search baseline
    /// as the initial portion and the granted allowance as the total, so the
    /// `ProofCascPolicy` split sees exactly the part beyond the baseline.
    /// Disabled — this type's own default, though not what `campaign run`
    /// selects — the launch is a plain `finite(a_k)` with no
    /// retry-added portion for the split to reach, and the launch's command
    /// has its CASC policy cleared besides
    /// ([`FrameworkIIProductionCheckConfig::launch_command`]), so a
    /// direct-only run is direct-only whatever the host's own
    /// `ProofCascPolicy` says.
    fn budget_after(&self, launches_so_far: usize) -> Option<VampireSearchBudget> {
        self.allowance_after(launches_so_far).map(|allowance| {
            if self.casc_portfolio.is_enabled() {
                VampireSearchBudget::cumulative(self.baseline, allowance)
            } else {
                VampireSearchBudget::finite(allowance)
            }
        })
    }
}

/// How one launch's own lane report classifies that launch.
///
/// A lane that stopped itself at the limit it was given reports
/// [`FailureKind::CheckTimeout`], and that is this launch's timeout: the
/// same outcome the runner's own backstop kill produces, recorded as such
/// and charged to the retry ladder, so the key climbs to its next rung. A
/// lane that gave up on the obligation says so. Anything else is a fault in
/// one lane, and the launch is inconclusive because its peer failed.
fn lane_failure_reason(kind: FailureKind) -> FrameworkIIInconclusiveReason {
    match kind {
        FailureKind::SolverUnknown => FrameworkIIInconclusiveReason::SolverUnknown,
        FailureKind::CheckTimeout => FrameworkIIInconclusiveReason::TimedOut,
        _ => FrameworkIIInconclusiveReason::PeerFailed,
    }
}

#[derive(Clone)]
pub struct FrameworkIIProductionCheckConfig {
    artifacts: ArtifactStore,
    admission: SolverAdmission,
    budget: VampireSearchBudget,
    fmb: Option<FmbOptions>,
    command: VampireWorkerCommand,
    cancellation: CancellationToken,
    runtime_vampire_version: Arc<str>,
    certification_profiles: FrameworkIICertificationProfiles,
    retry_policy: FrameworkIIRetryPolicy,
    retry_premise_role: PremiseRole,
    host_limits: HostLimits,
    search_profile: ProofSearchProfile,
}

impl FrameworkIIProductionCheckConfig {
    /// A production check configuration. Every check it configures races the
    /// proof lane against the finite-model lane, so a condition that is not
    /// inductive comes back refuted with a Lean-validated countermodel rather
    /// than merely unproved within the budget.
    ///
    /// The finite-model lane is not an option here on purpose: a proof-only
    /// run is a different search, and no command, default or omitted argument
    /// may reach one by accident. The only way to build a proof-only
    /// configuration is to name
    /// [`Self::new_proof_only_not_a_campaign_configuration`].
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        artifacts: ArtifactStore,
        admission: SolverAdmission,
        budget: VampireSearchBudget,
        fmb: FmbOptions,
        command: VampireWorkerCommand,
        cancellation: CancellationToken,
        runtime_vampire_version: impl Into<Arc<str>>,
        certification_profiles: FrameworkIICertificationProfiles,
    ) -> Result<Self, FrameworkIIStateError> {
        Self::build(
            artifacts,
            admission,
            budget,
            Some(fmb),
            command,
            cancellation,
            runtime_vampire_version,
            certification_profiles,
        )
    }

    /// A proof-only check configuration. **Not a campaign configuration.**
    ///
    /// It exists for tests whose subject is the proof lane by itself, and for
    /// fake-Vampire fixtures written around a single lane, where a racing
    /// finite-model launch would answer a call the fixture has no reply for.
    /// A check configured this way reports a condition it cannot prove as
    /// inconclusive, never as refuted, so it must not stand in for a
    /// production search. The name is deliberately hard to reach for.
    #[allow(clippy::too_many_arguments)]
    pub fn new_proof_only_not_a_campaign_configuration(
        artifacts: ArtifactStore,
        admission: SolverAdmission,
        budget: VampireSearchBudget,
        command: VampireWorkerCommand,
        cancellation: CancellationToken,
        runtime_vampire_version: impl Into<Arc<str>>,
        certification_profiles: FrameworkIICertificationProfiles,
    ) -> Result<Self, FrameworkIIStateError> {
        Self::build(
            artifacts,
            admission,
            budget,
            None,
            command,
            cancellation,
            runtime_vampire_version,
            certification_profiles,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn build(
        artifacts: ArtifactStore,
        admission: SolverAdmission,
        budget: VampireSearchBudget,
        fmb: Option<FmbOptions>,
        command: VampireWorkerCommand,
        cancellation: CancellationToken,
        runtime_vampire_version: impl Into<Arc<str>>,
        certification_profiles: FrameworkIICertificationProfiles,
    ) -> Result<Self, FrameworkIIStateError> {
        let runtime_vampire_version = runtime_vampire_version.into();
        let Some(initial_limit) = budget.initial_limit() else {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "fixed-ambient production checks require a finite proof-search baseline",
            ));
        };
        let Some(total_limit) = budget.total_limit() else {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "fixed-ambient production checks require a finite proof-search allowance",
            ));
        };
        if initial_limit.is_zero()
            || total_limit < initial_limit
            || runtime_vampire_version.is_empty()
            || runtime_vampire_version.len() > 4096
        {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "fixed-ambient production checks require finite positive budgets and a bounded Vampire version",
            ));
        }
        Ok(Self {
            artifacts,
            admission,
            budget,
            fmb,
            command,
            cancellation,
            runtime_vampire_version,
            certification_profiles,
            // A key may be launched at most three times per run, under the
            // run budget's total, `total + 2 * initial` and
            // `total + 7 * initial` — `initial`, `3 * initial` and
            // `8 * initial` for a `finite` budget, whose total is its
            // initial, so the familiar 30-second baseline gives 30, 90 and
            // 240 seconds.
            //
            // The rungs grow faster than the baseline because the portfolio
            // stage only gets the share of a launch beyond that baseline: a
            // ladder in equal steps spends most of its added time on the
            // direct prefix, and the third launch's portfolio share never
            // reaches the range where the hard checks of this benchmark are
            // proved.
            retry_policy: FrameworkIIRetryPolicy::from_budget_and_increments(
                budget,
                [initial_limit * 2, initial_limit * 5],
            )?,
            // Every retry launch re-tags its premises by default
            // ([`PremiseRole`]); the first launch of a check never does.
            retry_premise_role: PremiseRole::NegatedConjecture,
            host_limits: HostLimits::UNBOUNDED,
            // The run's configured search profile (Pass 7.5f): the closed
            // label a frozen job takes when the search closed its condition
            // without a launch of its own — from the semantic dictionary,
            // or by reviewed Lean theorem selection on a protected row. It
            // never affects search-time dispatch, which races the schedules
            // the budget's CASC share allots.
            //
            // It stays `Direct` whatever the run's `CascPortfolioPolicy`,
            // and the policy is the wrong thing to read here. This label is
            // a claim about one condition: that no launch of this run
            // proved it with the portfolio. A run that merely *permits* the
            // portfolio is no evidence that this condition needed it, and
            // labelling it `casc_2025` would send certification to a
            // schedule nothing chose for it. A condition a launch did close
            // never reaches this value — `SearchProfileProvenance` gives it
            // the winner the dictionary recorded, portfolio included.
            search_profile: ProofSearchProfile::Direct,
        })
    }

    /// Set the run's configured search profile (Pass 7.5f). The default is
    /// [`ProofSearchProfile::Direct`].
    pub fn with_search_profile(mut self, search_profile: ProofSearchProfile) -> Self {
        self.search_profile = search_profile;
        self
    }

    /// The run's configured search profile.
    pub fn search_profile(&self) -> ProofSearchProfile {
        self.search_profile
    }

    /// Give this run its optional host limits. The default is
    /// [`HostLimits::UNBOUNDED`]: every validated countermodel is retained
    /// in full, however large, because the `countermodel` tool and clause
    /// evaluation read its tables (`houdini.tex` Section 4.4). A run that
    /// sets `countermodel_retention_tuples` records a larger countermodel as
    /// [`FrameworkIIRetainedCountermodel::FoundNotRetained`] with its tuple
    /// count instead.
    pub fn with_host_limits(mut self, host_limits: HostLimits) -> Self {
        self.host_limits = host_limits;
        self
    }

    /// Set the run's retry policy (`houdini.tex` Section 4.7).
    pub fn with_retry_policy(mut self, policy: FrameworkIIRetryPolicy) -> Self {
        self.retry_policy = policy;
        self
    }

    /// Set the TPTP role a *retry* launch writes its premises under. The
    /// first launch of a check always writes them as axioms.
    pub fn with_retry_premise_role(mut self, premise_role: PremiseRole) -> Self {
        self.retry_premise_role = premise_role;
        self
    }

    /// The role a retry launch writes its premises under.
    pub fn retry_premise_role(&self) -> PremiseRole {
        self.retry_premise_role
    }

    /// Legacy adaptive-retry configuration, kept as a thin shim over
    /// [`Self::with_retry_policy`]: the increments are mapped onto the
    /// contract's allowance list by
    /// [`FrameworkIIRetryPolicy::from_budget_and_increments`].
    #[deprecated(
        note = "Pass 7.5c-2 replaced the adaptive retry ladder with the run's retry policy; \
                use `with_retry_policy` (see `FrameworkIIRetryPolicy::from_budget_and_increments` \
                for the mapping)"
    )]
    pub fn with_retry_increments(
        self,
        increments: impl IntoIterator<Item = Duration>,
    ) -> Result<Self, FrameworkIIStateError> {
        let policy = FrameworkIIRetryPolicy::from_budget_and_increments(self.budget, increments)?;
        Ok(self.with_retry_policy(policy))
    }

    pub fn artifacts(&self) -> &ArtifactStore {
        &self.artifacts
    }

    pub fn admission(&self) -> &SolverAdmission {
        &self.admission
    }

    pub fn budget(&self) -> VampireSearchBudget {
        self.budget
    }

    /// The finite-model lane this configuration races, `None` only for a
    /// configuration built by
    /// [`Self::new_proof_only_not_a_campaign_configuration`].
    pub fn fmb(&self) -> Option<FmbOptions> {
        self.fmb
    }

    pub fn command(&self) -> &VampireWorkerCommand {
        &self.command
    }

    pub fn cancellation(&self) -> &CancellationToken {
        &self.cancellation
    }

    pub fn runtime_vampire_version(&self) -> &str {
        &self.runtime_vampire_version
    }

    pub fn certification_profiles(&self) -> &FrameworkIICertificationProfiles {
        &self.certification_profiles
    }

    /// The run's retry policy.
    pub fn retry_policy(&self) -> &FrameworkIIRetryPolicy {
        &self.retry_policy
    }

    /// The retry policy's allowance list. Named for the legacy accessor it
    /// replaces; the values are *allowances*, not increments.
    #[deprecated(note = "Pass 7.5c-2: use `retry_policy().allowances()`")]
    pub fn retry_increments(&self) -> &[Duration] {
        self.retry_policy.allowances()
    }

    /// The run's optional host limits (absent by default).
    pub fn host_limits(&self) -> &HostLimits {
        &self.host_limits
    }

    /// The optional tuple-count bound on validated-countermodel retention.
    /// `None` — the default — retains every countermodel in full.
    pub fn countermodel_tuple_bound(&self) -> Option<usize> {
        self.host_limits.get_usize("countermodel_retention_tuples")
    }

    /// The Vampire command one search launch runs under.
    ///
    /// With the run's [`CascPortfolioPolicy`] disabled — the default — the
    /// host's own [`crate::vampire::ProofCascPolicy`] is cleared, so no
    /// launch of this run can produce a `casc_2025` winner whatever the host
    /// configured. This is the enforcing half of "runs direct only": the
    /// budget alone would still hand the portfolio the policy's *initial*
    /// share of every allowance.
    fn launch_command(&self) -> VampireWorkerCommand {
        if self.retry_policy.casc_portfolio().is_enabled() {
            return self.command.clone();
        }
        self.command.clone().without_proof_casc()
    }
}

#[derive(Clone)]
struct PendingFrameworkIIAttempt {
    obligation_identity: Arc<Value>,
    entailment_identity: Arc<str>,
    query_artifact: ArtifactRef,
    attempt: EntailmentAttemptScope,
}

#[derive(Clone, Copy, Debug)]
struct FrameworkIIAdaptiveAttempt {
    budget: VampireSearchBudget,
    previous_proof_allowance: Duration,
    fmb: Option<FmbOptions>,
    retained_fmb_start_size: Option<FmbSize>,
}

/// Per-key solver state that survives an inconclusive attempt but is not
/// part of the retry policy: the finite-model-builder frontier the next
/// launch of the same key should resume from.
///
/// The launch *allowance* no longer lives here — it is the run's
/// [`FrameworkIIRetryPolicy`] indexed by the launch count the semantic
/// dictionary's inconclusive entry records (`houdini.tex` Section 4.4,
/// Definition "Subsumption").
#[derive(Clone, Debug)]
struct FrameworkIIRetryFrontier {
    semantic_key_identity: Arc<Value>,
    next_fmb_start_size: Option<FmbSize>,
}

impl FrameworkIIRetryFrontier {
    fn new(config: &FrameworkIIProductionCheckConfig, semantic_key_identity: &Value) -> Self {
        Self {
            semantic_key_identity: Arc::new(semantic_key_identity.clone()),
            next_fmb_start_size: config.fmb.map(|options| options.start_size),
        }
    }

    fn attempt(
        &self,
        config: &FrameworkIIProductionCheckConfig,
        budget: VampireSearchBudget,
        previous_proof_allowance: Duration,
    ) -> FrameworkIIAdaptiveAttempt {
        let fmb = config.fmb.map(|mut options| {
            if let Some(frontier) = self.next_fmb_start_size {
                options.start_size = options.start_size.max(frontier);
            }
            options
        });
        FrameworkIIAdaptiveAttempt {
            budget,
            previous_proof_allowance,
            fmb,
            retained_fmb_start_size: self.next_fmb_start_size,
        }
    }

    fn record_inconclusive(&mut self, next_fmb_start_size: Option<FmbSize>) {
        if let Some(frontier) = next_fmb_start_size {
            self.next_fmb_start_size = Some(
                self.next_fmb_start_size
                    .map_or(frontier, |retained| retained.max(frontier)),
            );
        }
    }
}

/// Production checker retaining exact complete receipts and resumable attempts.
pub struct FrameworkIIProductionChecker<S> {
    semantic: S,
    config: FrameworkIIProductionCheckConfig,
    pending: BTreeMap<Arc<str>, PendingFrameworkIIAttempt>,
    retries: BTreeMap<Arc<str>, FrameworkIIRetryFrontier>,
    complete: BTreeMap<Arc<str>, CompletedFrameworkIICheck>,
    /// The semantic dictionary (Pass 7.5b): every search-phase proof and
    /// Lean-validated refutation resolved so far in this run, keyed by
    /// conjecture identity and looked up by tagged-premise-set inclusion —
    /// independent of the exact tentative snapshot or `ClauseId` that first
    /// resolved it. Consulted before any worker preparation.
    semantic_dictionary: FrameworkIISemanticDictionary,
    /// Every validated countermodel retained so far in this run, keyed by
    /// the numeric id of the attempt that produced it (`AttemptId` has no
    /// `Ord`; see [`Self::countermodel_of_attempt`]).
    countermodels: BTreeMap<u64, Arc<FrameworkIIRetainedCountermodel>>,
    /// Count of checks closed by semantic-dictionary reuse instead of a
    /// fresh worker preparation and solver launch (the sum of
    /// [`Self::proof_subsumption_hits_total`] and
    /// [`Self::refutation_subsumption_hits_total`]).
    semantic_reuses_total: u64,
    /// Count of checks closed by a proof-subsumption dictionary hit.
    proof_subsumption_hits_total: u64,
    /// Count of checks closed by a refutation-subsumption dictionary hit.
    refutation_subsumption_hits_total: u64,
    /// Count of checks answered Inconclusive from an exact-key inconclusive
    /// dictionary entry, without a launch.
    inconclusive_dictionary_hits_total: u64,
    /// Count of proof entries whose cited set is the request's own full
    /// tagged premise set because the proof's citations failed closed.
    full_tagged_set_fallbacks_total: u64,
    /// Every semantic key launched during the current epoch. The retry
    /// policy grants a key at most one launch per epoch, so a key in this
    /// set is answered from its inconclusive entry until the controller
    /// opens the next epoch through [`FrameworkIIProductionChecker::begin_epoch`].
    launched_this_epoch: std::collections::BTreeSet<Arc<str>>,
    /// Count of batches this checker served (Pass 7.5d). One per Phase-1
    /// sweep and one per step sweep under the contract's dispatch; a lone
    /// check — the termination request, a protected-row installation — is a
    /// batch of one.
    batches_total: u64,
    /// Count of requests carried by those batches.
    batched_checks_total: u64,
    /// Count of batches whose launches actually ran concurrently: at least
    /// two launches, a shareable semantic adapter, and a live executor.
    concurrent_batches_total: u64,
    /// High-water mark of launches in flight at one instant across every
    /// concurrent batch of this run. `1` means dispatch never overlapped.
    max_in_flight_launches: usize,
}

#[derive(Clone)]
struct CompletedFrameworkIICheck {
    subject: FrameworkIICheckSubject,
    semantic_key_identity: Arc<Value>,
    outcome: FrameworkIICheckOutcome,
}

impl CompletedFrameworkIICheck {
    fn matches_subject(
        &self,
        subject: &FrameworkIICheckSubject,
        semantic_key_identity: &Value,
    ) -> bool {
        exact_check_subject_matches(&self.subject, subject)
            && self.semantic_key_identity.as_ref() == semantic_key_identity
    }
}

fn runtime_semantic_check_key_identity(prepared: &PreparedFrameworkIIEntailment) -> Value {
    json!({
        "kind": "whiel_framework_ii_runtime_semantic_check_key",
        "version": FRAMEWORK_II_RUNTIME_CACHE_IDENTITY_VERSION,
        "preparation_identity": prepared.prepare_request_identity(),
        "preparation_digest": prepared.prepare_request_digest(),
        "obligation_identity": prepared.base_obligation_identity(),
        "obligation_digest": prepared.base_obligation_digest(),
        "worker_entailment_identity": prepared.entailment_identity(),
        "empty_request_identity": prepared.empty_request_identity(),
        "empty_request_digest": prepared.empty_request_digest(),
        "entailment_identity": prepared.entailment().identity(),
        "query_artifact": artifact_fields(prepared.entailment().query_artifact()),
    })
}

fn runtime_complete_check_key(
    subject: &FrameworkIICheckSubject,
    semantic_key_identity: &Value,
) -> Arc<str> {
    Arc::from(canonical_value_sha256(&json!({
        "kind": "whiel_framework_ii_runtime_complete_check_key",
        "version": FRAMEWORK_II_RUNTIME_CACHE_IDENTITY_VERSION,
        "request_digest": subject.request_digest(),
        "semantic_key_identity": semantic_key_identity,
    })))
}

pub(super) fn exact_check_request_matches(
    left: &FrameworkIICheckRequest,
    right: &FrameworkIICheckRequest,
) -> bool {
    left.has_current_identity()
        && right.has_current_identity()
        && left.identity() == right.identity()
        && left.request_digest() == right.request_digest()
        && left.attempt_ordinal() == right.attempt_ordinal()
        && left.clause() == right.clause()
        && left.level() == right.level()
        && left.role() == right.role()
        && left.snapshot().same_partition(right.snapshot())
}

fn exact_check_subject_matches(
    left: &FrameworkIICheckSubject,
    right: &FrameworkIICheckSubject,
) -> bool {
    match (left, right) {
        (FrameworkIICheckSubject::Clause(left), FrameworkIICheckSubject::Clause(right)) => {
            exact_check_request_matches(left, right)
        }
        (
            FrameworkIICheckSubject::Termination(left),
            FrameworkIICheckSubject::Termination(right),
        ) => {
            left.has_current_identity()
                && right.has_current_identity()
                && left.identity() == right.identity()
                && left.request_digest() == right.request_digest()
                && left.core().same_partition(right.core())
        }
        _ => false,
    }
}

impl<S> FrameworkIIProductionChecker<S> {
    pub(crate) fn new(semantic: S, config: FrameworkIIProductionCheckConfig) -> Self {
        Self {
            semantic,
            config,
            pending: BTreeMap::new(),
            retries: BTreeMap::new(),
            complete: BTreeMap::new(),
            semantic_dictionary: FrameworkIISemanticDictionary::default(),
            countermodels: BTreeMap::new(),
            semantic_reuses_total: 0,
            proof_subsumption_hits_total: 0,
            refutation_subsumption_hits_total: 0,
            inconclusive_dictionary_hits_total: 0,
            full_tagged_set_fallbacks_total: 0,
            launched_this_epoch: std::collections::BTreeSet::new(),
            batches_total: 0,
            batched_checks_total: 0,
            concurrent_batches_total: 0,
            max_in_flight_launches: 0,
        }
    }

    /// Count of checks in this run closed by semantic-dictionary reuse
    /// (proof or refutation subsumption) instead of a fresh worker
    /// preparation and solver launch. Measures the saving from every epoch
    /// returning its pending clauses to their minimum levels: every level
    /// whose premises did not change is served level for level from the
    /// dictionary.
    pub fn semantic_reuses_total(&self) -> u64 {
        self.semantic_reuses_total
    }

    /// Count of checks in this run closed by a proof-subsumption dictionary
    /// hit: the request's own tagged premise set contained an earlier
    /// proof's cited tagged set for the same conjecture.
    pub fn proof_subsumption_hits_total(&self) -> u64 {
        self.proof_subsumption_hits_total
    }

    /// Count of checks in this run closed by a refutation-subsumption
    /// dictionary hit: the request's own tagged premise set was contained
    /// in an earlier validated refutation's full tagged set for the same
    /// conjecture.
    pub fn refutation_subsumption_hits_total(&self) -> u64 {
        self.refutation_subsumption_hits_total
    }

    /// Count of checks in this run answered Inconclusive from an exact-key
    /// inconclusive dictionary entry without a launch — either because the
    /// retry policy grants the key no further launch, or because the key
    /// was already launched in the current epoch.
    pub fn inconclusive_dictionary_hits_total(&self) -> u64 {
        self.inconclusive_dictionary_hits_total
    }

    /// Count of proof entries recorded in this run whose cited tagged set
    /// is the request's own *full* tagged premise set because the winning
    /// proof's citations failed closed — it named no axiom at all, or named
    /// one absent from Lean's `axiom_tags` table.
    pub fn full_tagged_set_fallbacks_total(&self) -> u64 {
        self.full_tagged_set_fallbacks_total
    }

    /// Open a new epoch: clear the set of semantic keys already launched.
    ///
    /// The contract grants each inconclusive key at most one launch per
    /// epoch (`houdini.tex` Section 4.4, Definition "Subsumption": "Within
    /// one epoch a key is launched at most once"), so the controller must
    /// call this exactly once at the start of every epoch, before its first
    /// check. `Epoch` (wave 1A's `stabilization.rs`) is the caller;
    /// `compress_core`'s re-stabilization deliberately does *not* call it,
    /// since it belongs to the epoch that triggered it.
    ///
    /// Nothing else is reset: the dictionary, its inconclusive launch
    /// counts, retained countermodels, and the run's completed checks all
    /// persist across epochs for the life of the run.
    pub fn begin_epoch(&mut self) {
        self.launched_this_epoch.clear();
    }

    /// The retained countermodel for a completed attempt, when that attempt
    /// closed as a Lean-validated refutation. `None` for an attempt that
    /// never produced a refutation (including every proved or inconclusive
    /// attempt) — never a stand-in for "not yet checked".
    pub fn countermodel_of_attempt(
        &self,
        attempt: AttemptId,
    ) -> Option<&FrameworkIIRetainedCountermodel> {
        self.countermodels.get(&attempt.get()).map(Arc::as_ref)
    }

    /// The antichain of a clause's strongest recorded refutations: the
    /// refutation-dictionary entries for `clause_identity` whose tagged
    /// premise sets are maximal under inclusion (no retained entry's set is
    /// a strict subset of another's), ordered by set size descending.
    ///
    /// `cap` is the run's optional `strongest_refutations` host limit;
    /// `None` — the default — returns the complete antichain, and the tool
    /// layer says so when a limit truncates it.
    pub fn strongest_refutations(
        &self,
        clause_identity: &str,
        cap: Option<usize>,
    ) -> Vec<FrameworkIIRefutationSummary> {
        self.semantic_dictionary
            .strongest_refutations(clause_identity, cap)
    }

    /// Every keyed entry of the semantic dictionary, as
    /// `(kind, key, count)`: `("proof", tagged conjecture, entries)`,
    /// `("refutation", tagged conjecture, entries)`, and
    /// `("inconclusive", semantic key, launches)`. Sorted, so two runs of
    /// one fixture are directly comparable.
    ///
    /// Test-only. It exposes what the dictionary *holds*, which the hit
    /// counters do not: two runs can agree on every count while having
    /// recorded entries under different keys.
    #[doc(hidden)]
    pub fn dictionary_entry_summary(&self) -> Vec<(&'static str, String, usize)> {
        self.semantic_dictionary.entry_summary()
    }

    /// The run's per-condition profile provenance for the conditions of
    /// `core` (Pass 7.5f): the run's configured search profile together
    /// with the winning schedule of every condition of that Core this run's
    /// search proved by a launch of its own, as the semantic dictionary's
    /// proof entries recorded it. Read once by the freeze, against the
    /// final Core; never consulted on a decision path.
    ///
    /// `core` is what decides *which* launch labels a condition when the
    /// dictionary holds several — see
    /// [`FrameworkIISemanticDictionary::launched_proof_winners`].
    pub fn search_profile_provenance(
        &self,
        core: &LeveledCandidateSnapshot,
    ) -> SearchProfileProvenance {
        SearchProfileProvenance::from_dictionary_winners(
            self.config.search_profile,
            self.semantic_dictionary.launched_proof_winners(core),
        )
    }

    /// Count of batches this checker served (Pass 7.5d): one per Phase-1
    /// initialization sweep and one per step fixed-point sweep under the
    /// contract's dispatch, plus one per lone check.
    pub fn batches_total(&self) -> u64 {
        self.batches_total
    }

    /// Count of requests those batches carried. Equals the number of checks
    /// this checker served.
    pub fn batched_checks_total(&self) -> u64 {
        self.batched_checks_total
    }

    /// Count of batches whose launches ran concurrently rather than one at
    /// a time.
    pub fn concurrent_batches_total(&self) -> u64 {
        self.concurrent_batches_total
    }

    /// The largest number of launches this run ever had in flight at once.
    /// `1` (or `0`, for a run that never launched) means dispatch never
    /// overlapped, whatever the pool sizes allow.
    pub fn max_in_flight_launches(&self) -> usize {
        self.max_in_flight_launches
    }

    /// Every fully retained (not [`FrameworkIIRetainedCountermodel::FoundNotRetained`])
    /// countermodel instance from this run's dictionary, keyed by the exact
    /// `AttemptId` scalar it is retained under, most-recent-attempt first
    /// (the `evaluate_clauses` query's explicit `all_retained` selection).
    /// Callers cap further themselves; this yields every retained instance
    /// with no built-in limit.
    pub fn retained_countermodel_entries(
        &self,
    ) -> impl Iterator<Item = (u64, &FrameworkIICountermodelInstance)> {
        self.countermodels
            .iter()
            .rev()
            .filter_map(|(&attempt, model)| match model.as_ref() {
                FrameworkIIRetainedCountermodel::Retained(instance) => Some((attempt, instance)),
                FrameworkIIRetainedCountermodel::FoundNotRetained { .. } => None,
            })
    }
}

/// Pass 7.5c: the semantic-dictionary queries the AgentHoudini session/tool
/// layer serves (`countermodel`, `strongest_refutations`, and
/// `evaluate_clauses`), lifted to a trait so `agent.rs`'s response validator
/// and `search.rs`'s consultation driver can reach them generically over the
/// search's checker type parameter without depending on the concrete
/// [`FrameworkIIProductionChecker`]. Defined here, alongside the inherent
/// methods it forwards to, rather than on [`FrameworkIIChecker`] in
/// `stabilization.rs`, so `stabilization.rs` never needs to depend on this
/// module's types. `Send + Sync`: [`super::agent::AgentResponseValidator`]
/// and [`super::tools::AgentToolResources`] hold a `&dyn FrameworkIIQueryChecker`
/// across the `evaluate_clauses` tool body's own `.await`, so the trait
/// object itself must satisfy the bound the tool surface's future needs.
pub trait FrameworkIIQueryChecker: Send + Sync {
    fn countermodel_of_attempt(
        &self,
        attempt: AttemptId,
    ) -> Option<&FrameworkIIRetainedCountermodel>;

    fn strongest_refutations(
        &self,
        clause_identity: &str,
        cap: Option<usize>,
    ) -> Vec<FrameworkIIRefutationSummary>;

    fn retained_countermodel_entries(
        &self,
    ) -> Box<dyn Iterator<Item = (u64, &FrameworkIICountermodelInstance)> + '_>;
}

impl<S> FrameworkIIQueryChecker for FrameworkIIProductionChecker<S>
where
    S: Send + Sync,
{
    fn countermodel_of_attempt(
        &self,
        attempt: AttemptId,
    ) -> Option<&FrameworkIIRetainedCountermodel> {
        Self::countermodel_of_attempt(self, attempt)
    }

    fn strongest_refutations(
        &self,
        clause_identity: &str,
        cap: Option<usize>,
    ) -> Vec<FrameworkIIRefutationSummary> {
        Self::strongest_refutations(self, clause_identity, cap)
    }

    fn retained_countermodel_entries(
        &self,
    ) -> Box<dyn Iterator<Item = (u64, &FrameworkIICountermodelInstance)> + '_> {
        Box::new(Self::retained_countermodel_entries(self))
    }
}

async fn reach_production_publication_boundary(
    cancellation: CancellationToken,
) -> Result<(), FrameworkIIStateError> {
    tokio::task::yield_now().await;
    if cancellation.should_stop() {
        Err(FrameworkIIStateError::Cancelled)
    } else {
        Ok(())
    }
}

#[allow(private_bounds)]
impl<S> FrameworkIIProductionChecker<S>
where
    S: FrameworkIISemanticAdapter,
{
    async fn check_request(
        &mut self,
        subject: FrameworkIICheckSubject,
    ) -> Result<FrameworkIICheckExecution, FrameworkIIStateError> {
        let mut executions = self.check_subject_batch(vec![subject]).await?;
        if executions.len() != 1 {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "a fixed-ambient batch of one returned another number of executions",
            ));
        }
        Ok(executions.remove(0))
    }

    /// One batch through `Check(q)`: the sequential dictionary pass, the
    /// concurrent launches, then the sequential recording pass.
    ///
    /// `houdini.tex` Section 4.4 dispatches a whole sweep of a level at
    /// once. Only the middle phase is concurrent; the dictionary decides in
    /// check order before it, and every state change lands in check order
    /// after it, so the dictionary and the keyed caches keep exactly one
    /// writer.
    async fn check_subject_batch(
        &mut self,
        subjects: Vec<FrameworkIICheckSubject>,
    ) -> Result<Vec<FrameworkIICheckExecution>, FrameworkIIStateError> {
        // A cached check can otherwise complete inside one parent poll.
        // Yield on both sides of the batch so the search deadline owner can
        // cancel before work starts or before a result is published into
        // the controller ledger.
        reach_production_publication_boundary(self.config.cancellation.clone()).await?;
        self.batches_total = self.batches_total.saturating_add(1);
        self.batched_checks_total = self
            .batched_checks_total
            .saturating_add(subjects.len() as u64);

        let mut slots = Vec::with_capacity(subjects.len());
        let mut claimed: BTreeSet<Arc<str>> = BTreeSet::new();
        for subject in subjects {
            match self.plan_subject(subject)? {
                FrameworkIICheckPlan::Resolved { execution, writes } => {
                    slots.push(FrameworkIIBatchSlot::Resolved { execution, writes });
                }
                FrameworkIICheckPlan::Launch(plan) => {
                    // "Within one epoch a key is launched at most once"
                    // holds inside a batch too: only the first request of a
                    // key is dispatched, and the rest are answered from
                    // what it recorded.
                    if claimed.insert(Arc::clone(&plan.semantic_vc_key)) {
                        slots.push(FrameworkIIBatchSlot::Launch(plan));
                    } else {
                        let plan = *plan;
                        slots.push(FrameworkIIBatchSlot::Deferred {
                            semantic_vc_key: plan.semantic_vc_key,
                            subject: plan.subject,
                        });
                    }
                }
            }
        }

        let mut base = self.snapshot_base();
        self.dispatch_batch_launches(&mut slots, &base).await?;

        // A leader that came back a nonlogical `Failure` recorded no
        // dictionary entry and did not mark its key launched, so a deferred
        // duplicate of that key would re-plan into a second launch of the
        // same key in the same epoch. The contract grants one; the
        // duplicate is answered with the leader's own failure instead.
        let mut leader_failures: BTreeMap<Arc<str>, FailureReport> = BTreeMap::new();
        let mut executions = Vec::with_capacity(slots.len());
        for slot in slots {
            match slot {
                FrameworkIIBatchSlot::Resolved { execution, writes } => {
                    self.commit_writes(writes, &mut base);
                    executions.push(execution);
                }
                FrameworkIIBatchSlot::Product(product) => {
                    let FrameworkIILaunchProduct {
                        semantic_vc_key,
                        result,
                        writes,
                    } = *product;
                    self.commit_writes(writes, &mut base);
                    let execution = result?;
                    record_leader_failure(&mut leader_failures, semantic_vc_key, &execution);
                    executions.push(execution);
                }
                FrameworkIIBatchSlot::Launch(plan) => {
                    let semantic_vc_key = Arc::clone(&plan.semantic_vc_key);
                    let execution = self.resolve_plan(*plan, &mut base).await?;
                    record_leader_failure(&mut leader_failures, semantic_vc_key, &execution);
                    executions.push(execution);
                }
                FrameworkIIBatchSlot::Deferred {
                    subject,
                    semantic_vc_key,
                } => match leader_failures.get(semantic_vc_key.as_ref()) {
                    Some(report) => {
                        executions.push(FrameworkIICheckExecution::Failure(report.clone()));
                    }
                    None => {
                        executions.push(self.resolve_subject(subject, &mut base).await?);
                    }
                },
                FrameworkIIBatchSlot::Taken => {
                    return Err(FrameworkIIStateError::InvalidEvidence(
                        "a fixed-ambient batch slot lost its check",
                    ));
                }
            }
        }
        reach_production_publication_boundary(self.config.cancellation.clone()).await?;
        Ok(executions)
    }

    /// Run the batch's launches at once, one cloned semantic handle each,
    /// and park every finished product back in its own slot.
    ///
    /// The worker pool and the Vampire process pool are the bounds: every
    /// launch acquires its own permits through the run's `SolverAdmission`
    /// exactly as a lone check does, so a batch never exceeds the pool
    /// sizes the host configured. Concurrency needs a semantic adapter
    /// whose state is shareable and a running executor; without either the
    /// slots stay `Launch` and the recording pass resolves them one at a
    /// time on this checker's own adapter — the dispatch the controller had
    /// before batching.
    async fn dispatch_batch_launches(
        &mut self,
        slots: &mut [FrameworkIIBatchSlot],
        base: &FrameworkIICheckerBase,
    ) -> Result<(), FrameworkIIStateError> {
        let launches = slots
            .iter()
            .filter(|slot| matches!(slot, FrameworkIIBatchSlot::Launch(_)))
            .count();
        if launches < 2 || tokio::runtime::Handle::try_current().is_err() {
            return Ok(());
        }
        let mut handles = Vec::with_capacity(launches);
        for _ in 0..launches {
            let Some(handle) = self.semantic.concurrent_handle() else {
                return Ok(());
            };
            handles.push(handle);
        }
        self.concurrent_batches_total = self.concurrent_batches_total.saturating_add(1);
        let frozen = Arc::new(base.clone());
        let gauge = Arc::new(FrameworkIIInFlightGauge::default());
        let mut tasks = tokio::task::JoinSet::new();
        for (index, slot) in slots.iter_mut().enumerate() {
            if !matches!(slot, FrameworkIIBatchSlot::Launch(_)) {
                continue;
            }
            let FrameworkIIBatchSlot::Launch(plan) =
                std::mem::replace(slot, FrameworkIIBatchSlot::Taken)
            else {
                unreachable!("the slot was just matched as a launch")
            };
            let mut semantic = handles.pop().expect("one handle per launch");
            let config = self.config.clone();
            let frozen = Arc::clone(&frozen);
            let gauge = Arc::clone(&gauge);
            let semantic_vc_key = Arc::clone(&plan.semantic_vc_key);
            tasks.spawn(async move {
                let _in_flight = gauge.enter();
                let mut writes = Vec::new();
                let result = match reach_production_publication_boundary(
                    config.cancellation.clone(),
                )
                .await
                {
                    Ok(()) => {
                        resolve_framework_ii_launch(
                            *plan,
                            &mut semantic,
                            &config,
                            &frozen,
                            &mut writes,
                        )
                        .await
                    }
                    Err(error) => Err(error),
                };
                (
                    index,
                    FrameworkIILaunchProduct {
                        semantic_vc_key,
                        result,
                        writes,
                    },
                )
            });
        }
        // A hard `Err` — cancellation, or a fail-closed evidence defect —
        // ends the whole batch: the recording pass would return it at this
        // slot and discard everything after it anyway, and nothing later in
        // the batch may publish once the run is stopping. `Ok(Failure)` is
        // not such an error: a nonlogical failure is an ordinary batch
        // outcome, recorded in check order like any other. Aborting drains
        // the remaining tasks so no launch outlives this call.
        let mut aborted: Option<FrameworkIIStateError> = None;
        while let Some(joined) = tasks.join_next().await {
            match joined {
                Ok((index, product)) => {
                    if aborted.is_some() {
                        continue;
                    }
                    if let Err(error) = &product.result {
                        aborted = Some(error.clone());
                        tasks.abort_all();
                        continue;
                    }
                    slots[index] = FrameworkIIBatchSlot::Product(Box::new(product));
                }
                Err(joined) if joined.is_panic() => {
                    std::panic::resume_unwind(joined.into_panic());
                }
                Err(joined) if joined.is_cancelled() && aborted.is_some() => {}
                Err(_) => {
                    tasks.abort_all();
                    aborted.get_or_insert(FrameworkIIStateError::InvalidEvidence(
                        "a batched fixed-ambient check did not complete",
                    ));
                }
            }
        }
        self.max_in_flight_launches = self
            .max_in_flight_launches
            .max(gauge.max.load(AtomicOrdering::Acquire));
        match aborted {
            Some(error) => Err(error),
            None => Ok(()),
        }
    }

    /// Plan and resolve one request on this checker's own adapter, against
    /// the keyed state as the recording pass has left it.
    async fn resolve_subject(
        &mut self,
        subject: FrameworkIICheckSubject,
        base: &mut FrameworkIICheckerBase,
    ) -> Result<FrameworkIICheckExecution, FrameworkIIStateError> {
        match self.plan_subject(subject)? {
            FrameworkIICheckPlan::Resolved { execution, writes } => {
                self.commit_writes(writes, base);
                Ok(execution)
            }
            FrameworkIICheckPlan::Launch(plan) => self.resolve_plan(*plan, base).await,
        }
    }

    /// Resolve one already-planned launch on this checker's own adapter and
    /// commit its journalled writes, whether it succeeded or failed.
    ///
    /// The recording pass and [`Self::resolve_subject`] share this: a
    /// launch the batch could not dispatch concurrently and a launch a
    /// deferred slot re-planned are resolved by exactly the same code.
    async fn resolve_plan(
        &mut self,
        plan: FrameworkIICheckLaunchPlan,
        base: &mut FrameworkIICheckerBase,
    ) -> Result<FrameworkIICheckExecution, FrameworkIIStateError> {
        let mut writes = Vec::new();
        let result =
            resolve_framework_ii_launch(plan, &mut self.semantic, &self.config, base, &mut writes)
                .await;
        self.commit_writes(writes, base);
        result
    }

    fn snapshot_base(&self) -> FrameworkIICheckerBase {
        FrameworkIICheckerBase {
            complete: self.complete.clone(),
            retries: self.retries.clone(),
            pending: self.pending.clone(),
        }
    }

    /// Apply one check's journalled state changes, and carry them into the
    /// batch's own view so a launch the recording pass performs itself
    /// reads the keyed state as it now is.
    fn commit_writes(
        &mut self,
        writes: Vec<FrameworkIICheckerWrite>,
        base: &mut FrameworkIICheckerBase,
    ) {
        for write in writes {
            base.absorb(&write);
            self.apply_write(write);
        }
    }

    fn apply_write(&mut self, write: FrameworkIICheckerWrite) {
        match write {
            FrameworkIICheckerWrite::CountProofSubsumption => {
                self.proof_subsumption_hits_total =
                    self.proof_subsumption_hits_total.saturating_add(1);
                self.semantic_reuses_total = self.semantic_reuses_total.saturating_add(1);
            }
            FrameworkIICheckerWrite::CountRefutationSubsumption => {
                self.refutation_subsumption_hits_total =
                    self.refutation_subsumption_hits_total.saturating_add(1);
                self.semantic_reuses_total = self.semantic_reuses_total.saturating_add(1);
            }
            FrameworkIICheckerWrite::CountInconclusiveDictionary => {
                self.inconclusive_dictionary_hits_total =
                    self.inconclusive_dictionary_hits_total.saturating_add(1);
                self.semantic_reuses_total = self.semantic_reuses_total.saturating_add(1);
            }
            FrameworkIICheckerWrite::CountFullTaggedSetFallback => {
                self.full_tagged_set_fallbacks_total =
                    self.full_tagged_set_fallbacks_total.saturating_add(1);
            }
            FrameworkIICheckerWrite::LaunchedThisEpoch(key) => {
                self.launched_this_epoch.insert(key);
            }
            FrameworkIICheckerWrite::CompleteSet(key, value) => {
                self.complete.insert(key, value);
            }
            FrameworkIICheckerWrite::PendingSet(key, value) => {
                self.pending.insert(key, value);
            }
            FrameworkIICheckerWrite::PendingRemove(key) => {
                self.pending.remove(&key);
            }
            FrameworkIICheckerWrite::RetriesSet(key, value) => {
                self.retries.insert(key, value);
            }
            FrameworkIICheckerWrite::RetriesRemove(key) => {
                self.retries.remove(&key);
            }
            FrameworkIICheckerWrite::RecordProof(conjecture, entry) => {
                self.semantic_dictionary.record_proof(conjecture, entry);
            }
            FrameworkIICheckerWrite::RecordRefutation(conjecture, entry) => {
                self.semantic_dictionary
                    .record_refutation(conjecture, entry);
            }
            FrameworkIICheckerWrite::RecordInconclusive {
                key,
                reason,
                tagged,
                progress,
            } => {
                self.semantic_dictionary
                    .record_inconclusive(key, reason, tagged, progress);
            }
            FrameworkIICheckerWrite::ClearInconclusive(key) => {
                self.semantic_dictionary.clear_inconclusive(&key);
            }
            FrameworkIICheckerWrite::Countermodel(attempt, countermodel) => {
                self.countermodels.insert(attempt, countermodel);
            }
        }
    }

    /// The dictionary half of `Check(q)` (`houdini.tex` Algorithm 3): every
    /// answer reachable without a worker or a solver.
    ///
    /// Runs once per request, sequentially and in check order. A refutation-
    /// subsumption hit and an inconclusive entry the retry policy (or this
    /// epoch's one launch) already closed return here; a proof hit does
    /// not, because `houdini.tex` Section 4.4 requires Lean's empty-instance
    /// check on the *new* obligation before the reuse counts as Proved, and
    /// that check needs the prepared obligation.
    ///
    /// The refutation lookup runs **first and unconditionally**, and a
    /// refutation hit answers `Refuted` by reuse whatever proof entries the
    /// dictionary also holds for the conjecture. A proof entry `(g, C)` and a
    /// refutation entry `(g, T)` with `C ⊆ T` are not contradictory: the
    /// proof is evidence over *nonempty* active domains only, while the
    /// refutation is an adom-empty countermodel — recorded, in the very case
    /// that produced it, by the proof hit's own empty-instance check further
    /// down this file. Reading the two as contradictory and aborting the run
    /// would fail closed on the checker's own sound behaviour, so the two
    /// coexist and the refutation, which is a validated countermodel of this
    /// conjecture, wins.
    ///
    /// Every plan of one batch is made *before* any of that batch's
    /// launches run, so all of them see the same pre-batch dictionary: a
    /// sweep's requests are never answered from each other's results, and
    /// the plan a request gets does not depend on where in the sweep it
    /// sits. The recording pass then commits each check's writes in check
    /// order, and only a `Deferred` slot — a second request for a key an
    /// earlier slot of the same batch already claimed — is re-planned after
    /// those commits, so that it can be answered from what its leader
    /// recorded rather than launching the key a second time.
    fn plan_subject(
        &self,
        subject: FrameworkIICheckSubject,
    ) -> Result<FrameworkIICheckPlan, FrameworkIIStateError> {
        // Computed purely from Lean-issued clause-identity digests already
        // held by the request's own snapshot: the tagged conjecture and the
        // exact tagged premise multiset Lean is known to build for this
        // request (see `tagged_premise_set` and
        // `termination_tagged_premise_set`). No worker call has happened
        // yet. The key is level-free: `g` and `T` determine the problem, so
        // the same problem recurs at `j` and `j+1` across a level the Core
        // leaves empty; the level is recorded on the ledger row only.
        let semantic_vc_key_identity = Arc::new(semantic_vc_key_identity(&subject));
        let semantic_vc_key: Arc<str> =
            Arc::from(canonical_value_sha256(semantic_vc_key_identity.as_ref()));
        let conjecture_identity = conjecture_identity_of(&subject);
        let request_tags = subject_tagged_premise_set(&subject);
        // Every request is served through the dictionary, including one
        // whose clause the controller has already suspended: suspension
        // suppresses the *launch*, never the lookup. Core compression is a
        // re-stabilization with the dictionary in force too, so no path
        // bypasses it.
        let launch_suppressed = subject.launch_suppressed();
        // Refutations are consulted first, and a hit answers on its own. A
        // refutation entry is a *validated* countermodel of this conjecture
        // under a premise set this request's own tags contain, so it decides
        // the request whether or not a proof entry also matches: the two
        // speak about different domains (see this function's doc comment),
        // and the proof entry's only remaining effect would be the
        // empty-instance recheck the refutation already answers.
        let refutation_hit = self
            .semantic_dictionary
            .find_refutation_hit(&conjecture_identity, &request_tags)
            .cloned();
        if let Some(entry) = refutation_hit {
            let matched = Value::Array(tagged_premise_set_to_json(&entry.tagged));
            let reuse = SemanticReuseEvidence::new(
                &subject,
                FrameworkIISemanticReuseKind::RefutationSubsumption,
                Arc::clone(&semantic_vc_key),
                Arc::clone(&semantic_vc_key_identity),
                matched,
                &entry.evidence,
            );
            let evidence = FrameworkIICheckEvidence::from_semantic_reuse(&entry.evidence, reuse);
            return Ok(FrameworkIICheckPlan::Resolved {
                execution: FrameworkIICheckExecution::Applied(FrameworkIICheckOutcome::Refuted(
                    evidence,
                )),
                writes: vec![FrameworkIICheckerWrite::CountRefutationSubsumption],
            });
        }
        // Same-conjecture proof subsumption only. Reuse never crosses the
        // two roles (`houdini.tex` Section 4.4): an initialization entry
        // never answers a step request, since a proof of `c` over nonempty
        // domains says nothing about `c` at the emptied state the body may
        // produce, and a step entry never answers an initialization request,
        // since `C |= wp(body, c)` does not imply `C |= c`. The result
        // carries which rule matched.
        let proof_hit = self
            .semantic_dictionary
            .find_proof_hit(&conjecture_identity, &request_tags)
            .cloned()
            .map(|entry| (entry, FrameworkIISemanticReuseKind::ProofSubsumption));
        let inconclusive_entry = self
            .semantic_dictionary
            .find_inconclusive(&semantic_vc_key)
            .cloned();
        // The launch this request would perform is the `(launches_so_far +
        // 1)`-st of this key under the run's retry policy.
        let launches_so_far = inconclusive_entry
            .as_ref()
            .map_or(0, |entry| entry.launches);

        if proof_hit.is_none()
            && let Some(entry) = &inconclusive_entry
        {
            let policy_grants_launch = self
                .config
                .retry_policy
                .allowance_after(launches_so_far)
                .is_some();
            let launched_this_epoch = self.launched_this_epoch.contains(&semantic_vc_key);
            if !policy_grants_launch || launched_this_epoch {
                let matched = Value::Array(tagged_premise_set_to_json(&entry.tagged));
                let reuse = SemanticReuseEvidence::new(
                    &subject,
                    FrameworkIISemanticReuseKind::InconclusiveEntry,
                    Arc::clone(&semantic_vc_key),
                    Arc::clone(&semantic_vc_key_identity),
                    matched,
                    &entry.evidence,
                );
                let evidence =
                    FrameworkIICheckEvidence::from_semantic_reuse(&entry.evidence, reuse);
                return Ok(FrameworkIICheckPlan::Resolved {
                    execution: FrameworkIICheckExecution::Applied(
                        FrameworkIICheckOutcome::Inconclusive {
                            reason: entry.reason,
                            progress: evidence,
                        },
                    ),
                    writes: vec![FrameworkIICheckerWrite::CountInconclusiveDictionary],
                });
            }
        }
        Ok(FrameworkIICheckPlan::Launch(Box::new(
            FrameworkIICheckLaunchPlan {
                subject,
                semantic_vc_key,
                semantic_vc_key_identity,
                conjecture_identity,
                request_tags,
                launch_suppressed,
                proof_hit,
                launches_so_far,
            },
        )))
    }
    /// The epoch's termination check (`houdini.tex` Section 4.3): the
    /// request `Term(F)` of Table 1 over the epoch's Core, served through
    /// the same `Check(q)` as any clause request.
    ///
    /// Its tagged premise set is `{not_guard} ∪ {collapsed(d) : d ∈ Core}`,
    /// its tagged conjecture the fixed `(Term, post')`, and its key ranges
    /// over the Core's sorted identity list without levels — so an epoch
    /// that did not change the Core's clause set is answered from the
    /// dictionary without a launch. A refutation retains its validated
    /// countermodel under the launching attempt's id, addressable by the
    /// `countermodel` tool like any other.
    pub(crate) async fn check_termination_request(
        &mut self,
        core: Arc<LeveledCandidateSnapshot>,
    ) -> Result<FrameworkIICheckExecution, FrameworkIIStateError> {
        self.check_request(FrameworkIICheckSubject::Termination(
            FrameworkIITerminationRequest::new(core),
        ))
        .await
    }
}

// ------------------------------------------------------------
// Batched Dispatch (Pass 7.5d)
// ------------------------------------------------------------

/// A read-only view of the checker's keyed state, taken once per batch.
///
/// Every concurrent launch of a batch reads the maps as the batch found
/// them; nothing writes here. The checker's own copies are updated only by
/// the sequential recording pass, in check order, so the dictionary and the
/// keyed caches stay single-writer.
#[derive(Clone, Default)]
struct FrameworkIICheckerBase {
    complete: BTreeMap<Arc<str>, CompletedFrameworkIICheck>,
    retries: BTreeMap<Arc<str>, FrameworkIIRetryFrontier>,
    pending: BTreeMap<Arc<str>, PendingFrameworkIIAttempt>,
}

impl FrameworkIICheckerBase {
    /// Carry one already-applied write into this view, so a launch the
    /// recording pass performs itself sees the keyed state as it now is.
    fn absorb(&mut self, write: &FrameworkIICheckerWrite) {
        match write {
            FrameworkIICheckerWrite::CompleteSet(key, value) => {
                self.complete.insert(Arc::clone(key), value.clone());
            }
            FrameworkIICheckerWrite::PendingSet(key, value) => {
                self.pending.insert(Arc::clone(key), value.clone());
            }
            FrameworkIICheckerWrite::PendingRemove(key) => {
                self.pending.remove(key);
            }
            FrameworkIICheckerWrite::RetriesSet(key, value) => {
                self.retries.insert(Arc::clone(key), value.clone());
            }
            FrameworkIICheckerWrite::RetriesRemove(key) => {
                self.retries.remove(key);
            }
            _ => {}
        }
    }
}

/// One state change a check produced, replayed into the checker in check
/// order after the batch's outcomes are in.
enum FrameworkIICheckerWrite {
    CountProofSubsumption,
    CountRefutationSubsumption,
    CountInconclusiveDictionary,
    CountFullTaggedSetFallback,
    LaunchedThisEpoch(Arc<str>),
    CompleteSet(Arc<str>, CompletedFrameworkIICheck),
    PendingSet(Arc<str>, PendingFrameworkIIAttempt),
    PendingRemove(Arc<str>),
    RetriesSet(Arc<str>, FrameworkIIRetryFrontier),
    RetriesRemove(Arc<str>),
    RecordProof(Arc<str>, FrameworkIIDictionaryProofEntry),
    RecordRefutation(Arc<str>, FrameworkIIDictionaryRefutationEntry),
    RecordInconclusive {
        key: Arc<str>,
        reason: FrameworkIIInconclusiveReason,
        tagged: Arc<TaggedPremiseSet>,
        progress: FrameworkIICheckEvidence,
    },
    ClearInconclusive(Arc<str>),
    Countermodel(u64, Arc<FrameworkIIRetainedCountermodel>),
}

/// Everything the sequential dictionary pass decided about one request that
/// the dictionary could not close on its own.
struct FrameworkIICheckLaunchPlan {
    subject: FrameworkIICheckSubject,
    semantic_vc_key: Arc<str>,
    semantic_vc_key_identity: Arc<Value>,
    conjecture_identity: Arc<str>,
    request_tags: TaggedPremiseSet,
    launch_suppressed: bool,
    proof_hit: Option<(
        FrameworkIIDictionaryProofEntry,
        FrameworkIISemanticReuseKind,
    )>,
    launches_so_far: usize,
}

/// The outcome of the sequential dictionary pass for one request.
enum FrameworkIICheckPlan {
    /// Closed from the dictionary alone: no worker, no solver.
    Resolved {
        execution: FrameworkIICheckExecution,
        writes: Vec<FrameworkIICheckerWrite>,
    },
    /// Needs the worker, and possibly the solver.
    Launch(Box<FrameworkIICheckLaunchPlan>),
}

/// One resolved launch: its execution (or the error it raised) together
/// with every state change it made, still unapplied, and the key it was
/// dispatched for.
struct FrameworkIILaunchProduct {
    semantic_vc_key: Arc<str>,
    result: Result<FrameworkIICheckExecution, FrameworkIIStateError>,
    writes: Vec<FrameworkIICheckerWrite>,
}

/// Remember a leader's nonlogical failure so a deferred duplicate of the
/// same key is answered with it instead of launching the key again.
fn record_leader_failure(
    failures: &mut BTreeMap<Arc<str>, FailureReport>,
    semantic_vc_key: Arc<str>,
    execution: &FrameworkIICheckExecution,
) {
    if let FrameworkIICheckExecution::Failure(report) = execution {
        failures.insert(semantic_vc_key, report.clone());
    }
}

/// One slot of a batch, in check order.
enum FrameworkIIBatchSlot {
    Resolved {
        execution: FrameworkIICheckExecution,
        writes: Vec<FrameworkIICheckerWrite>,
    },
    Launch(Box<FrameworkIICheckLaunchPlan>),
    Product(Box<FrameworkIILaunchProduct>),
    /// A second request for a key an earlier slot of this batch already
    /// claimed. The contract grants a key one launch per epoch, so this one
    /// waits for the sequential recording pass, where the leader's own
    /// dictionary entry answers it — or, when the leader came back a
    /// nonlogical failure and so recorded nothing, the leader's failure
    /// itself does, which is why the key is carried alongside the subject.
    Deferred {
        subject: FrameworkIICheckSubject,
        semantic_vc_key: Arc<str>,
    },
    Taken,
}

/// Live count of batched launches, and the high-water mark of this run.
#[derive(Default)]
struct FrameworkIIInFlightGauge {
    current: AtomicUsize,
    max: AtomicUsize,
}

impl FrameworkIIInFlightGauge {
    fn enter(self: &Arc<Self>) -> FrameworkIIInFlightGuard {
        let now = self.current.fetch_add(1, AtomicOrdering::AcqRel) + 1;
        self.max.fetch_max(now, AtomicOrdering::AcqRel);
        FrameworkIIInFlightGuard {
            gauge: Arc::clone(self),
        }
    }
}

struct FrameworkIIInFlightGuard {
    gauge: Arc<FrameworkIIInFlightGauge>,
}

impl Drop for FrameworkIIInFlightGuard {
    fn drop(&mut self) {
        self.gauge.current.fetch_sub(1, AtomicOrdering::AcqRel);
    }
}

fn require_config_publication_open(
    config: &FrameworkIIProductionCheckConfig,
) -> Result<(), FrameworkIIStateError> {
    if config.cancellation.should_stop() {
        Err(FrameworkIIStateError::Cancelled)
    } else {
        Ok(())
    }
}

/// The launching half of `Check(q)` (`houdini.tex` Algorithm 3): worker
/// preparation, the protected-theorem route, Lean's empty-instance recheck
/// of a proof-dictionary hit, and the solver.
///
/// Holds no reference to the checker: it reads the keyed caches through
/// `base` and journals every state change into `writes`, so a batch can run
/// many of these at once against cloned semantic handles and still record
/// their effects one at a time, in check order. `writes` is returned to the
/// caller whether this call succeeds or fails, exactly as the sequential
/// checker's own state kept every change it made before an error.
async fn resolve_framework_ii_launch<S>(
    plan: FrameworkIICheckLaunchPlan,
    semantic: &mut S,
    config: &FrameworkIIProductionCheckConfig,
    base: &FrameworkIICheckerBase,
    writes: &mut Vec<FrameworkIICheckerWrite>,
) -> Result<FrameworkIICheckExecution, FrameworkIIStateError>
where
    S: FrameworkIISemanticAdapter,
{
    macro_rules! w {
        ($($variant:tt)*) => {
            writes.push(FrameworkIICheckerWrite::$($variant)*)
        };
    }
    let FrameworkIICheckLaunchPlan {
        subject,
        semantic_vc_key,
        semantic_vc_key_identity,
        conjecture_identity,
        request_tags,
        launch_suppressed,
        proof_hit,
        launches_so_far,
    } = plan;
    // Measured around the call rather than read from the prepared
    // entailment: this spans the whole preparation of this check —
    // splicing the obligation out of the run's opaque-piece cache, plus
    // whatever worker round trips that cache missed on
    // (`prepare_task_pieces`, `prepare_clause_pieces`,
    // `prepare_support_block`), plus the assembly differential's own
    // `prepare_exact_obligation` when it is enabled. A preparation whose
    // pieces are all cached makes no worker round trip at all, so this is
    // preparation time, not worker time; `piece_cache_stats()` counts the
    // round trips. It is measured regardless of whether the check goes on
    // to launch a solver, close by protected-theorem selection, or replay
    // an earlier completed outcome from this same run.
    let preparation_started_at = std::time::Instant::now();
    let pre_check = semantic
        .prepare(
            &subject,
            &config.admission,
            &config.artifacts,
            &config.cancellation,
        )
        .await?;
    let preparation_time = Some(preparation_started_at.elapsed());
    require_config_publication_open(config)?;
    let prepared = match pre_check {
        FrameworkIIPreCheckOutcome::Applied(prepared) => prepared,
        FrameworkIIPreCheckOutcome::Failure(report) => {
            return Ok(FrameworkIICheckExecution::Failure(report));
        }
    };
    if !prepared.matches_subject(&subject) {
        return Err(FrameworkIIStateError::InvalidEvidence(
            "the semantic adapter prepared another fixed-ambient request",
        ));
    }
    let semantic_key_identity = runtime_semantic_check_key_identity(&prepared);
    let semantic_key: Arc<str> = Arc::from(canonical_value_sha256(&semantic_key_identity));
    let complete_key = runtime_complete_check_key(&subject, &semantic_key_identity);
    if let Some(completed) = base.complete.get(&complete_key) {
        if !completed.matches_subject(&subject, &semantic_key_identity) {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "a completed-check digest matched another structural request or semantic check",
            ));
        }
        return Ok(FrameworkIICheckExecution::Applied(
            completed.outcome.clone(),
        ));
    }
    let protected_candidate = semantic
        .protected_theorem_candidate(&subject, &prepared, &config.admission, &config.cancellation)
        .await?;
    require_config_publication_open(config)?;
    if let Some(candidate) = protected_candidate {
        let selection = match ProtectedTheoremSelectionReceipt::commit(
            &subject,
            &prepared,
            candidate,
            &config.artifacts,
            &config.cancellation,
        ) {
            Ok(selection) => selection,
            Err(FrameworkIIReceiptError::State(error)) => return Err(error),
            Err(FrameworkIIReceiptError::Failure(report)) => {
                return Ok(FrameworkIICheckExecution::Failure(report));
            }
        };
        let evidence = FrameworkIICheckEvidence::from_protected_theorem_selection(selection);
        let outcome = FrameworkIICheckOutcome::Proved(evidence.clone());
        require_config_publication_open(config)?;
        w!(CompleteSet(
            Arc::clone(&complete_key),
            CompletedFrameworkIICheck {
                subject: subject.clone(),
                semantic_key_identity: Arc::new(semantic_key_identity.clone()),
                outcome: outcome.clone(),
            },
        ));
        // Soundness of the `{Pre}` cited set: a protected precondition
        // row's initialization is closed by Lean's conjunct-elimination
        // theorem (`houdini.tex` Section 4.6, "Protected precondition
        // rows"), which eliminates the row's conjunct from `pre'` and so
        // consults exactly one premise — the precondition — and no Core
        // clause at all. `{Pre}` is therefore exact, not an
        // approximation: it subsumes every later *initialization*
        // request for the same conjecture at any level, whose tagged set
        // always contains `pre`, and it deliberately does not subsume a
        // step request, whose tagged set carries `guard` and the Core's
        // `plain` premises but never `pre`. An empty cited set would
        // wrongly claim the latter too. Step (maintenance) protected
        // rows are not recorded here: the plan scopes this proof entry
        // to initialization only.
        if subject.as_clause().is_some_and(|request| {
            request.role() == FrameworkIICheckRole::Initialization && request.level().get() == 0
        }) {
            let mut cited = TaggedPremiseSet::new();
            cited.insert(FrameworkIIPremiseTag::Pre);
            w!(RecordProof(
                Arc::clone(&conjecture_identity),
                FrameworkIIDictionaryProofEntry {
                    cited: Arc::new(cited),
                    evidence,
                },
            ));
        }
        return Ok(FrameworkIICheckExecution::Applied(outcome));
    }
    // `houdini.tex` Section 4.4, "Susp": the remaining checks of a
    // clause suspended this epoch are answered from the dictionary, and
    // failing that are inconclusive without a launch — no retry
    // allowance is consumed, no inconclusive entry is recorded, and the
    // key stays unlaunched for this epoch. A proof entry still needs
    // its empty-instance recheck below, which needs a begun attempt, so
    // only a request with no proof hit stops here; the proof-hit branch
    // never reaches the launch.
    if launch_suppressed && proof_hit.is_none() {
        return Ok(FrameworkIICheckExecution::Applied(
            FrameworkIICheckOutcome::Inconclusive {
                reason: FrameworkIIInconclusiveReason::Suspended,
                progress: FrameworkIICheckEvidence::launch_suppressed(subject.request_digest())?
                    .with_preparation_time(preparation_time),
            },
        ));
    }
    // The premise role of the launch this request is about to make
    // (`PremiseRole`). The first launch of a key renders its premises as
    // axioms; every retry of it renders the same premises, with the same
    // names, bodies and order, under the run's configured retry role.
    //
    // It is applied here, after the keys are taken and before the attempt
    // is begun, for three reasons. The semantic check key, the completed
    // check key and the semantic VC key are all computed above from the
    // untagged preparation, so the two renderings of one check stay the
    // same check to every cache and to the dictionary. The attempt scope
    // is begun below on whatever entailment is launched, so both lanes of
    // this launch read the one re-rendered file. And a request answered by
    // a proof entry runs no solver at all, so it is left exactly as it was.
    //
    // A retained pending attempt is only ever resumed after a cancelled
    // launch, which consumes no allowance, so a resumed attempt comes back
    // to the same rung and re-renders the same bytes.
    let prepared = if proof_hit.is_none() && launches_so_far > 0 {
        match prepared
            .entailment()
            .with_premise_role(
                config.retry_premise_role,
                &config.admission,
                &config.artifacts,
                &config.cancellation,
            )
            .await
        {
            Ok(retagged) => prepared.with_entailment(retagged)?,
            Err(EncodingError::Cancelled) => return Err(FrameworkIIStateError::Cancelled),
            Err(EncodingError::Failure(report)) => {
                return Ok(FrameworkIICheckExecution::Failure(report));
            }
        }
    } else {
        prepared
    };
    require_config_publication_open(config)?;
    let mut retry = base
        .retries
        .get(&semantic_key)
        .cloned()
        .unwrap_or_else(|| FrameworkIIRetryFrontier::new(config, &semantic_key_identity));
    w!(RetriesSet(Arc::clone(&semantic_key), retry.clone()));
    if retry.semantic_key_identity.as_ref() != &semantic_key_identity {
        return Err(FrameworkIIStateError::InvalidEvidence(
            "an adaptive-retry digest matched another semantic check",
        ));
    }
    // Resuming a retained attempt requires the launch to be on the exact
    // entailment the attempt was begun for, the published query artifact
    // included. Two invariants keep the premise role from ever moving
    // underneath a resumed attempt, and a change to either must be made
    // together with a change here:
    //
    // - an attempt is retained only across a launch that consumed no
    //   allowance, so a resume returns to the same rung and re-renders the
    //   same bytes; and
    // - the re-tag above is skipped exactly when a proof entry answers the
    //   request, and that branch always returns without reaching a launch,
    //   so it can never resume an attempt a retry began.
    //
    // If a retained attempt could ever outlive its rung, or a proof-entry
    // request could reach this point holding a retry's attempt, the role
    // would have to be carried in `PendingFrameworkIIAttempt` and compared
    // here instead of the artifact it produced.
    debug_assert!(
        !base.pending.contains_key(&semantic_key)
            || prepared.entailment().premise_role()
                == if proof_hit.is_none() && launches_so_far > 0 {
                    config.retry_premise_role
                } else {
                    PremiseRole::Axiom
                },
        "a resumed attempt is launched under the premise role of its own rung"
    );
    let attempt = if let Some(pending) = base.pending.get(&semantic_key) {
        if pending.obligation_identity.as_ref() != prepared.base_obligation_identity()
            || pending.entailment_identity.as_ref() != prepared.entailment().identity()
            || pending.query_artifact != prepared.entailment().query_artifact()
        {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "a resumable fixed-ambient attempt changed its exact entailment",
            ));
        }
        pending.attempt.clone()
    } else {
        require_config_publication_open(config)?;
        let attempt = match config
            .artifacts
            .begin_entailment_attempt(prepared.entailment())
        {
            Ok(attempt) => attempt,
            Err(report) => {
                w!(RetriesRemove(Arc::clone(&semantic_key)));
                return Ok(FrameworkIICheckExecution::Failure(report));
            }
        };
        require_config_publication_open(config)?;
        w!(PendingSet(
            Arc::clone(&semantic_key),
            PendingFrameworkIIAttempt {
                obligation_identity: Arc::new(prepared.base_obligation_identity().clone()),
                entailment_identity: prepared.entailment().identity_arc(),
                query_artifact: prepared.entailment().query_artifact(),
                attempt: attempt.clone(),
            },
        ));
        attempt
    };
    // A proof entry hit: repeat Lean's empty-instance check on this
    // request's own obligation before the reuse counts as Proved. A
    // solver proof covers nonempty domains only, and the entry does not
    // record which uncited premise of the original request may have
    // excluded the empty instance. A counterexample there is a
    // validated refutation of *this* request (`houdini.tex` Section
    // 4.4: "Lean finds a counterexample at the empty instance: o ←
    // Refuted, validated; record it; return o"), committed here on the
    // attempt already begun above, with the same terminal row the
    // launch path's resolver publishes for its own empty-instance
    // counterexample. No solver runs either way, so this branch always
    // returns.
    //
    // Lean: `QFEntailment.valid_of_proofHit` (`DictionarySoundness.lean`)
    // is this rule — the cited set's validity over nonempty active domains
    // plus a fresh verdict over the adom-empty instances of the new
    // obligation. The worker's check is constant-blind
    // (`QFEntailment.adomEmptyCounterexample?`, decided exactly by
    // `adomEmptyCounterexample?_eq_false_iff`), because the entry's proof
    // was found in the *original* request's constant signature and covers
    // nothing at an empty adom that only the new request's constants would
    // make a nonempty FOL domain. The witness
    // `empty_verdict_does_not_transfer` in
    // `Whiel/Synthesis/Tests/FrameworkIIDictionarySoundness.lean` shows the
    // entry's own empty-instance verdict must not be inherited.
    if let Some((entry, reuse_kind)) = proof_hit {
        match semantic
            .check_empty(&prepared, &attempt, &config.admission, &config.cancellation)
            .await
        {
            Ok(FrameworkIIEmptyCheckOutcome::NoCounterexample(_)) => {
                let matched = Value::Array(tagged_premise_set_to_json(&entry.cited));
                let reuse = SemanticReuseEvidence::new(
                    &subject,
                    reuse_kind,
                    Arc::clone(&semantic_vc_key),
                    Arc::clone(&semantic_vc_key_identity),
                    matched,
                    &entry.evidence,
                );
                let evidence =
                    FrameworkIICheckEvidence::from_semantic_reuse(&entry.evidence, reuse);
                w!(CountProofSubsumption);
                // No solver ran, so nothing is in flight for this key
                // and no launch state needs to survive.
                w!(PendingRemove(Arc::clone(&semantic_key)));
                w!(RetriesRemove(Arc::clone(&semantic_key)));
                return Ok(FrameworkIICheckExecution::Applied(
                    FrameworkIICheckOutcome::Proved(evidence),
                ));
            }
            Ok(FrameworkIIEmptyCheckOutcome::ValidatedRefutation(evidence)) => {
                if let Err(error) = validate_refutation_evidence(
                    &prepared,
                    &attempt,
                    &evidence,
                    evidence.source_artifact,
                    ArtifactKind::EmptyInstanceCheck,
                ) {
                    w!(PendingRemove(Arc::clone(&semantic_key)));
                    w!(RetriesRemove(Arc::clone(&semantic_key)));
                    return Err(error);
                }
                let terminal = match SpecializedEntailmentTerminal::new(
                    "refuted",
                    vec![evidence.source_artifact, evidence.validation_artifact],
                    json!({
                        "validation_digest": evidence.validation_digest.as_ref(),
                        "refutation_source": "empty_counterexample",
                    }),
                    FrameworkIIResolvedAttempt::Refuted(evidence),
                ) {
                    Ok(terminal) => terminal,
                    Err(report) => {
                        w!(PendingRemove(Arc::clone(&semantic_key)));
                        w!(RetriesRemove(Arc::clone(&semantic_key)));
                        return Ok(FrameworkIICheckExecution::Failure(report));
                    }
                };
                let report = match publish_specialized_entailment_terminal(
                    prepared.entailment(),
                    &attempt,
                    &config.cancellation,
                    terminal,
                )
                .await
                {
                    Ok(report) => report,
                    Err(report) => {
                        w!(PendingRemove(Arc::clone(&semantic_key)));
                        w!(RetriesRemove(Arc::clone(&semantic_key)));
                        return Ok(FrameworkIICheckExecution::Failure(report));
                    }
                };
                let refutation = match ValidatedFiniteRefutation::commit(
                    &subject,
                    &prepared,
                    &attempt,
                    &report,
                    &config.cancellation,
                ) {
                    Ok(refutation) => refutation,
                    Err(FrameworkIIReceiptError::State(error)) => {
                        w!(PendingRemove(Arc::clone(&semantic_key)));
                        w!(RetriesRemove(Arc::clone(&semantic_key)));
                        return Err(error);
                    }
                    Err(FrameworkIIReceiptError::Failure(report)) => {
                        w!(PendingRemove(Arc::clone(&semantic_key)));
                        w!(RetriesRemove(Arc::clone(&semantic_key)));
                        return Ok(FrameworkIICheckExecution::Failure(report));
                    }
                };
                // No solver ran, so no solver time is attributable and
                // nothing stays in flight for this key.
                let evidence =
                    FrameworkIICheckEvidence::from_validated_refutation(refutation, None)
                        .with_preparation_time(preparation_time);
                let outcome = FrameworkIICheckOutcome::Refuted(evidence.clone());
                w!(PendingRemove(Arc::clone(&semantic_key)));
                w!(RetriesRemove(Arc::clone(&semantic_key)));
                require_config_publication_open(config)?;
                w!(ClearInconclusive(Arc::clone(&semantic_vc_key)));
                w!(CompleteSet(
                    Arc::clone(&complete_key),
                    CompletedFrameworkIICheck {
                        subject: subject.clone(),
                        semantic_key_identity: Arc::new(semantic_key_identity.clone()),
                        outcome: outcome.clone(),
                    },
                ));
                if let Some(refutation) = evidence.validated_refutation() {
                    let countermodel = Arc::new(build_retained_countermodel(
                        refutation.validation_identity(),
                        config.countermodel_tuple_bound(),
                    ));
                    w!(Countermodel(
                        attempt.attempt_id().get(),
                        Arc::clone(&countermodel)
                    ));
                    w!(RecordRefutation(
                        Arc::clone(&conjecture_identity),
                        FrameworkIIDictionaryRefutationEntry {
                            tagged: Arc::new(request_tags.clone()),
                            evidence: evidence.clone(),
                            countermodel,
                        },
                    ));
                }
                return Ok(FrameworkIICheckExecution::Applied(outcome));
            }
            Err(FrameworkIISemanticCheckError::Cancelled) => {
                return Err(FrameworkIIStateError::Cancelled);
            }
            Err(FrameworkIISemanticCheckError::Failure(report)) => {
                return Ok(FrameworkIICheckExecution::Failure(report));
            }
        }
    }
    // Only a request that really launches needs an allowance. The lookup
    // sits *below* the proof-hit branch on purpose: a key whose retry
    // policy is exhausted is still answerable by a proof entry through the
    // empty-instance check above, which runs no solver and consumes no
    // allowance, and reading the policy before that branch turned such a
    // request into a fail-closed abort. The allowance itself is indexed by
    // the launch count the dictionary's inconclusive entry records; the
    // policy's direct-search baseline stays the initial portion so
    // `ProofCascPolicy` keeps splitting only the part beyond it.
    let Some(policy_budget) = config.retry_policy.budget_after(launches_so_far) else {
        return Err(FrameworkIIStateError::InvalidEvidence(
            "the retry policy granted a launch it has no allowance for",
        ));
    };
    // The allowance the previous launch of this key ran under; the
    // direct-search baseline for the first launch, which had none.
    let previous_proof_allowance = launches_so_far
        .checked_sub(1)
        .and_then(|previous| config.retry_policy.allowance_after(previous))
        .unwrap_or_else(|| config.retry_policy.baseline());
    let adaptive_attempt = retry.attempt(config, policy_budget, previous_proof_allowance);
    // Racing both lanes is what a production configuration does; there is no
    // proof-only default to fall through to. The proof-only arm is reachable
    // only from a configuration that named
    // `FrameworkIIProductionCheckConfig::new_proof_only_not_a_campaign_configuration`.
    let mode = match adaptive_attempt.fmb {
        Some(options) => VampireMode::ProofAndFmb(options),
        None => VampireMode::ProofOnly,
    };
    require_config_publication_open(config)?;
    // One launch per key per epoch (`houdini.tex` Section 4.4).
    w!(LaunchedThisEpoch(Arc::clone(&semantic_vc_key)));
    let semantic = &mut *semantic;
    let resolver_prepared = prepared.clone();
    let resolver_attempt = attempt.clone();
    let resolver_admission = config.admission.clone();
    let resolver_cancellation = config.cancellation.clone();
    // Measured around the launch rather than read from the invocation
    // receipt: neither `VampireInvocationOutcome` nor the resolved report
    // carries its own wall-clock duration today. This spans the exact
    // Vampire invocation this check attempt performs, including its
    // resolver callback.
    let solver_launched_at = std::time::Instant::now();
    let report = match check_entailment_attempt_detailed_with_resolver(
        prepared.entailment(),
        &attempt,
        adaptive_attempt.budget,
        mode,
        config.launch_command(),
        config.admission.clone(),
        config.cancellation.clone(),
        move |vampire| async move {
            resolve_framework_ii_vampire(
                semantic,
                &resolver_prepared,
                &resolver_attempt,
                &resolver_admission,
                &resolver_cancellation,
                vampire,
            )
            .await
        },
    )
    .await
    {
        Ok(report) => report,
        Err(report) => {
            w!(PendingRemove(Arc::clone(&semantic_key)));
            w!(RetriesRemove(Arc::clone(&semantic_key)));
            return Ok(FrameworkIICheckExecution::Failure(report));
        }
    };
    if let Err(error) = require_config_publication_open(config) {
        w!(PendingRemove(Arc::clone(&semantic_key)));
        w!(RetriesRemove(Arc::clone(&semantic_key)));
        return Err(error);
    }
    let solver_time = Some(solver_launched_at.elapsed());

    let reuse_attempt = matches!(
        report.outcome(),
        FrameworkIIResolvedAttempt::Inconclusive {
            reuse_attempt: true,
            ..
        }
    );
    let outcome = match report.outcome() {
        FrameworkIIResolvedAttempt::Proved { .. } => {
            let receipt = match RuntimeProofReceipt::commit(
                &subject,
                &prepared,
                &attempt,
                &report,
                Arc::clone(&config.runtime_vampire_version),
                &config.certification_profiles,
                &config.artifacts,
                &config.cancellation,
            ) {
                Ok(receipt) => receipt,
                Err(FrameworkIIReceiptError::State(error)) => {
                    w!(PendingRemove(Arc::clone(&semantic_key)));
                    w!(RetriesRemove(Arc::clone(&semantic_key)));
                    return Err(error);
                }
                Err(FrameworkIIReceiptError::Failure(report)) => {
                    w!(PendingRemove(Arc::clone(&semantic_key)));
                    w!(RetriesRemove(Arc::clone(&semantic_key)));
                    return Ok(FrameworkIICheckExecution::Failure(report));
                }
            };
            FrameworkIICheckOutcome::Proved(
                FrameworkIICheckEvidence::from_runtime_proof(receipt, solver_time)
                    .with_preparation_time(preparation_time),
            )
        }
        FrameworkIIResolvedAttempt::Refuted(_) => {
            let refutation = match ValidatedFiniteRefutation::commit(
                &subject,
                &prepared,
                &attempt,
                &report,
                &config.cancellation,
            ) {
                Ok(refutation) => refutation,
                Err(FrameworkIIReceiptError::State(error)) => {
                    w!(PendingRemove(Arc::clone(&semantic_key)));
                    w!(RetriesRemove(Arc::clone(&semantic_key)));
                    return Err(error);
                }
                Err(FrameworkIIReceiptError::Failure(report)) => {
                    w!(PendingRemove(Arc::clone(&semantic_key)));
                    w!(RetriesRemove(Arc::clone(&semantic_key)));
                    return Ok(FrameworkIICheckExecution::Failure(report));
                }
            };
            FrameworkIICheckOutcome::Refuted(
                FrameworkIICheckEvidence::from_validated_refutation(refutation, solver_time)
                    .with_preparation_time(preparation_time),
            )
        }
        FrameworkIIResolvedAttempt::Inconclusive {
            reason,
            next_fmb_start_size,
            ..
        } => {
            let effective_fmb_start_size =
                next_fmb_start_size.or(adaptive_attempt.retained_fmb_start_size);
            let progress = match FrameworkIIEntailmentProgress::commit(
                &subject,
                &prepared,
                &attempt,
                &report,
                adaptive_attempt.previous_proof_allowance,
                adaptive_attempt.budget,
                effective_fmb_start_size,
                &config.cancellation,
            ) {
                Ok(progress) => progress,
                Err(FrameworkIIReceiptError::State(error)) => {
                    w!(PendingRemove(Arc::clone(&semantic_key)));
                    w!(RetriesRemove(Arc::clone(&semantic_key)));
                    return Err(error);
                }
                Err(FrameworkIIReceiptError::Failure(report)) => {
                    w!(PendingRemove(Arc::clone(&semantic_key)));
                    w!(RetriesRemove(Arc::clone(&semantic_key)));
                    return Ok(FrameworkIICheckExecution::Failure(report));
                }
            };
            FrameworkIICheckOutcome::Inconclusive {
                reason: *reason,
                progress: FrameworkIICheckEvidence::from_progress(progress, solver_time)
                    .with_preparation_time(preparation_time),
            }
        }
    };
    if let Err(error) = require_config_publication_open(config) {
        w!(PendingRemove(Arc::clone(&semantic_key)));
        w!(RetriesRemove(Arc::clone(&semantic_key)));
        return Err(error);
    }
    if !reuse_attempt {
        w!(PendingRemove(Arc::clone(&semantic_key)));
    }
    match &outcome {
        FrameworkIICheckOutcome::Proved(evidence) => {
            w!(RetriesRemove(Arc::clone(&semantic_key)));
            w!(ClearInconclusive(Arc::clone(&semantic_vc_key)));
            w!(CompleteSet(
                Arc::clone(&complete_key),
                CompletedFrameworkIICheck {
                    subject: subject.clone(),
                    semantic_key_identity: Arc::new(semantic_key_identity.clone()),
                    outcome: outcome.clone(),
                },
            ));
            // Proof-subsumption caching (Pass 7.5b, revised by Pass
            // 7.5c-2): the cited set is read from the winning proof's
            // own text through Lean's `axiom_tags` table, and falls
            // back to this request's *full* tagged premise set whenever
            // the citations fail closed (no citation at all, or a name
            // absent from the table). The fallback is always a sound
            // cited set — the proof used some subset of this request's
            // premises — and merely subsumes fewer later requests
            // (Lean: `QFEntailment.fullTaggedSet_hit_sound`,
            // `DictionarySoundness.lean`).
            // Every preparation carries an `axiom_tags` table (Rust builds
            // it), so nothing is recorded only when the proof text is
            // unreadable: Rust never guesses a tag.
            if let FrameworkIIResolvedAttempt::Proved { proof, .. } = report.outcome()
                && let Ok(resolved) = config.artifacts.resolve(proof.output())
                && let Ok(proof_text) = std::fs::read_to_string(resolved.path())
            {
                let (cited, source) = cited_tagged_premises_from_proof(
                    &proof_text,
                    prepared.axiom_tags(),
                    &request_tags,
                );
                if source == CitedTaggedPremiseSource::FullTaggedSetFallback {
                    w!(CountFullTaggedSetFallback);
                }
                w!(RecordProof(
                    Arc::clone(&conjecture_identity),
                    FrameworkIIDictionaryProofEntry {
                        cited: Arc::new(cited),
                        evidence: evidence.clone(),
                    },
                ));
            }
        }
        FrameworkIICheckOutcome::Refuted(evidence) => {
            w!(RetriesRemove(Arc::clone(&semantic_key)));
            w!(ClearInconclusive(Arc::clone(&semantic_vc_key)));
            w!(CompleteSet(
                Arc::clone(&complete_key),
                CompletedFrameworkIICheck {
                    subject: subject.clone(),
                    semantic_key_identity: Arc::new(semantic_key_identity.clone()),
                    outcome: outcome.clone(),
                },
            ));
            // Refutation entries never need extraction: the full
            // request tagged set is already exact premise-set
            // authority for the countermodel Lean just validated.
            if let Some(refutation) = evidence.validated_refutation() {
                let countermodel = Arc::new(build_retained_countermodel(
                    refutation.validation_identity(),
                    config.countermodel_tuple_bound(),
                ));
                w!(Countermodel(
                    attempt.attempt_id().get(),
                    Arc::clone(&countermodel)
                ));
                w!(RecordRefutation(
                    Arc::clone(&conjecture_identity),
                    FrameworkIIDictionaryRefutationEntry {
                        tagged: Arc::new(request_tags.clone()),
                        evidence: evidence.clone(),
                        countermodel,
                    },
                ));
            }
        }
        FrameworkIICheckOutcome::Inconclusive { reason, progress } => {
            retry.record_inconclusive(
                progress
                    .progress()
                    .expect("inconclusive evidence carries typed progress")
                    .next_fmb_start_size(),
            );
            w!(RetriesSet(Arc::clone(&semantic_key), retry.clone()));
            // Add, or advance the launch count of, this exact key's
            // inconclusive entry. A later request with the same key is
            // answered from it without a launch until the retry policy
            // grants the next allowance, and at most once per epoch.
            //
            // A cancellation, and a launch stopped because a peer
            // failed, say nothing about the obligation: the solver
            // never reported on it. Such a launch leaves the key
            // exactly as it found it — no entry, no advanced launch
            // count, so the next epoch relaunches it under the same
            // allowance. Only a timeout, an unknown result and a model
            // the validator could not accept are evidence that this key
            // is hard. The FMB frontier recorded above is retained
            // either way: it is measured progress, not a verdict.
            if reason.consumes_retry_allowance() {
                w!(RecordInconclusive {
                    key: Arc::clone(&semantic_vc_key),
                    reason: *reason,
                    tagged: Arc::new(request_tags.clone()),
                    progress: progress.clone(),
                });
            }
        }
    }
    Ok(FrameworkIICheckExecution::Applied(outcome))
}

impl<S> sealed::Sealed for FrameworkIIProductionChecker<S> where S: Send {}

impl<S> FrameworkIIChecker for FrameworkIIProductionChecker<S>
where
    S: FrameworkIISemanticAdapter,
{
    fn host_limits(&self) -> Option<&HostLimits> {
        Some(self.config.host_limits())
    }

    fn retry_policy(&self) -> Option<&FrameworkIIRetryPolicy> {
        Some(self.config.retry_policy())
    }

    fn retry_premise_role(&self) -> Option<PremiseRole> {
        Some(self.config.retry_premise_role())
    }

    fn search_profile_provenance(
        &self,
        core: &LeveledCandidateSnapshot,
    ) -> SearchProfileProvenance {
        Self::search_profile_provenance(self, core)
    }

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
        Box::pin(self.check_request(FrameworkIICheckSubject::Clause(request)))
    }

    /// One whole sweep, dispatched at once (`houdini.tex` Section 4.4).
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
        Box::pin(
            self.check_subject_batch(
                requests
                    .into_iter()
                    .map(FrameworkIICheckSubject::Clause)
                    .collect(),
            ),
        )
    }

    /// The epoch's termination check, forwarded to this checker's inherent
    /// `check_termination_request`.
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
        Box::pin(self.check_termination_request(core))
    }

    /// Open a new epoch, forwarded to this checker's inherent
    /// [`FrameworkIIProductionChecker::begin_epoch`]: the per-epoch
    /// launched-key set is cleared so each semantic key is launched at most
    /// once per epoch.
    fn begin_epoch(&mut self) {
        FrameworkIIProductionChecker::begin_epoch(self);
    }

    fn matches_search_runtime(
        &self,
        solver: &FrameworkIISolverContext,
        artifacts: &ArtifactStore,
        admission: &SolverAdmission,
        cancellation: &CancellationToken,
    ) -> bool {
        self.semantic.encoding_context_id() == Some(solver.encoding().context_id())
            && self.semantic.matches_solver_context(solver)
            && self.config.artifacts.backend_id() == artifacts.backend_id()
            && self.config.artifacts.task_identity() == artifacts.task_identity()
            && self.config.admission.shares_controller_with(admission)
            && self.config.cancellation.shares_state_with(cancellation)
    }
}

async fn resolve_framework_ii_vampire<S>(
    semantic: &mut S,
    prepared: &PreparedFrameworkIIEntailment,
    attempt: &EntailmentAttemptScope,
    admission: &SolverAdmission,
    cancellation: &CancellationToken,
    vampire: VampireInvocationOutcome,
) -> Result<SpecializedEntailmentTerminal<FrameworkIIResolvedAttempt>, FailureReport>
where
    S: FrameworkIISemanticAdapter,
{
    match vampire {
        VampireInvocationOutcome::RunFailure(report) => Err(report),
        VampireInvocationOutcome::Cancelled(cancelled) => {
            let mut references = cancelled.artifact_references().to_vec();
            if let Some(report) = cancelled.peer_failure() {
                references.extend_from_slice(report.artifact_references());
            }
            SpecializedEntailmentTerminal::new(
                "canceled",
                references,
                json!({
                    "next_fmb_start_size": cancelled.next_fmb_start_size().map(FmbSize::get),
                    "peer_failure": cancelled.peer_failure().map(failure_fields),
                    "capture_warnings": cancelled.capture_warnings(),
                }),
                FrameworkIIResolvedAttempt::Inconclusive {
                    reason: FrameworkIIInconclusiveReason::Cancelled,
                    next_fmb_start_size: cancelled.next_fmb_start_size(),
                    peer_failure: cancelled.peer_failure().cloned(),
                    reuse_attempt: false,
                },
            )
        }
        VampireInvocationOutcome::Result(VampireResult::TimedOut {
            next_fmb_start_size,
            peer_failure,
        }) => {
            let references = peer_failure
                .as_ref()
                .map_or_else(Vec::new, |report| report.artifact_references().to_vec());
            SpecializedEntailmentTerminal::new(
                "timed_out",
                references,
                json!({
                    "next_fmb_start_size": next_fmb_start_size.map(FmbSize::get),
                    "peer_failure": peer_failure.as_ref().map(failure_fields),
                }),
                FrameworkIIResolvedAttempt::Inconclusive {
                    reason: FrameworkIIInconclusiveReason::TimedOut,
                    next_fmb_start_size,
                    peer_failure,
                    reuse_attempt: false,
                },
            )
        }
        VampireInvocationOutcome::Result(VampireResult::Failure {
            report,
            next_fmb_start_size,
        }) => {
            if report.scope() == FailureScope::RunGlobal {
                return Err(report);
            }
            let reason = lane_failure_reason(report.kind());
            let references = report.artifact_references().to_vec();
            let detail = json!({
                "next_fmb_start_size": next_fmb_start_size.map(FmbSize::get),
                "failure": failure_fields(&report),
            });
            SpecializedEntailmentTerminal::new(
                "failure",
                references,
                detail,
                FrameworkIIResolvedAttempt::Inconclusive {
                    reason,
                    next_fmb_start_size,
                    peer_failure: Some(report),
                    reuse_attempt: false,
                },
            )
        }
        VampireInvocationOutcome::Result(VampireResult::Refuted(model)) => {
            validate_model_bindings(prepared, attempt, &model).map_err(state_as_failure)?;
            let source = model.output();
            match semantic
                .validate_model(prepared, attempt, model, admission, cancellation)
                .await
            {
                Ok(FrameworkIIModelValidationOutcome::Validated(evidence)) => {
                    validate_refutation_evidence(
                        prepared,
                        attempt,
                        &evidence,
                        source,
                        ArtifactKind::Model,
                    )
                    .map_err(state_as_failure)?;
                    SpecializedEntailmentTerminal::new(
                        "refuted",
                        vec![evidence.source_artifact, evidence.validation_artifact],
                        json!({
                            "validation_digest": evidence.validation_digest.as_ref(),
                        }),
                        FrameworkIIResolvedAttempt::Refuted(evidence),
                    )
                }
                Ok(FrameworkIIModelValidationOutcome::NotRefutation) => {
                    SpecializedEntailmentTerminal::new(
                        "inconclusive",
                        vec![source],
                        json!({
                            "reason": "unvalidated_refutation",
                            "source": artifact_fields(source),
                        }),
                        FrameworkIIResolvedAttempt::Inconclusive {
                            reason: FrameworkIIInconclusiveReason::UnvalidatedRefutation,
                            next_fmb_start_size: None,
                            peer_failure: None,
                            reuse_attempt: false,
                        },
                    )
                }
                Err(FrameworkIISemanticCheckError::Cancelled) => {
                    SpecializedEntailmentTerminal::new(
                        "canceled",
                        vec![source],
                        json!({
                            "phase": "finite_refutation_validation",
                            "source": artifact_fields(source),
                        }),
                        FrameworkIIResolvedAttempt::Inconclusive {
                            reason: FrameworkIIInconclusiveReason::Cancelled,
                            next_fmb_start_size: None,
                            peer_failure: None,
                            reuse_attempt: true,
                        },
                    )
                }
                // A lane-local failure of the model's validation — a model
                // this host could not decode, most of all — says only that
                // this refutation was not established. The check is
                // inconclusive, exactly as an unvalidated refutation is,
                // and the search goes on; only a run-global failure ends
                // the run.
                Err(FrameworkIISemanticCheckError::Failure(report))
                    if report.scope() != FailureScope::RunGlobal =>
                {
                    let mut references = vec![source];
                    references.extend_from_slice(report.artifact_references());
                    SpecializedEntailmentTerminal::new(
                        "inconclusive",
                        references,
                        json!({
                            "reason": "unvalidated_refutation",
                            "source": artifact_fields(source),
                            "failure": failure_fields(&report),
                        }),
                        FrameworkIIResolvedAttempt::Inconclusive {
                            reason: FrameworkIIInconclusiveReason::UnvalidatedRefutation,
                            next_fmb_start_size: None,
                            peer_failure: Some(report),
                            reuse_attempt: false,
                        },
                    )
                }
                Err(FrameworkIISemanticCheckError::Failure(report)) => Err(report),
            }
        }
        VampireInvocationOutcome::Result(VampireResult::Proved(proof)) => {
            validate_proof_source(prepared, attempt, &proof).map_err(state_as_failure)?;
            let source = proof.output();
            match semantic
                .check_empty(prepared, attempt, admission, cancellation)
                .await
            {
                Ok(FrameworkIIEmptyCheckOutcome::NoCounterexample(empty_check)) => {
                    validate_proof_bindings(
                        prepared,
                        attempt,
                        &proof,
                        &empty_check,
                        attempt.artifacts(),
                    )
                    .map_err(state_as_failure)?;
                    SpecializedEntailmentTerminal::new(
                        "proved",
                        vec![source, empty_check.artifact()],
                        json!({
                            "proof_strategy": proof.strategy().as_str(),
                            "empty_check_digest": empty_check.check_digest(),
                        }),
                        FrameworkIIResolvedAttempt::Proved { proof, empty_check },
                    )
                }
                Ok(FrameworkIIEmptyCheckOutcome::ValidatedRefutation(evidence)) => {
                    validate_refutation_evidence(
                        prepared,
                        attempt,
                        &evidence,
                        evidence.source_artifact,
                        ArtifactKind::EmptyInstanceCheck,
                    )
                    .map_err(state_as_failure)?;
                    SpecializedEntailmentTerminal::new(
                        "refuted",
                        vec![
                            source,
                            evidence.source_artifact,
                            evidence.validation_artifact,
                        ],
                        json!({
                            "proof_strategy": proof.strategy().as_str(),
                            "validation_digest": evidence.validation_digest.as_ref(),
                            "refutation_source": "empty_counterexample",
                        }),
                        FrameworkIIResolvedAttempt::Refuted(evidence),
                    )
                }
                Err(FrameworkIISemanticCheckError::Cancelled) => {
                    SpecializedEntailmentTerminal::new(
                        "canceled",
                        vec![source],
                        json!({
                            "phase": "empty_counterexample_check",
                            "retained_proof": artifact_fields(source),
                        }),
                        FrameworkIIResolvedAttempt::Inconclusive {
                            reason: FrameworkIIInconclusiveReason::Cancelled,
                            next_fmb_start_size: None,
                            peer_failure: None,
                            reuse_attempt: true,
                        },
                    )
                }
                Err(FrameworkIISemanticCheckError::Failure(report)) => Err(report),
            }
        }
    }
}

// ------------------------------------------------------------
// Runtime Solver And Provisional Certification Profiles
// ------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ProofSearchProfile {
    Direct,
    Casc2025,
}

impl ProofSearchProfile {
    fn identity_name(self) -> &'static str {
        match self {
            Self::Direct => "direct",
            Self::Casc2025 => "casc_2025",
        }
    }
}

impl From<VampireProofStrategy> for ProofSearchProfile {
    fn from(strategy: VampireProofStrategy) -> Self {
        match strategy {
            VampireProofStrategy::Direct => Self::Direct,
            VampireProofStrategy::Casc2025 => Self::Casc2025,
        }
    }
}

/// Exact executable bytes and expanded ordered arguments for one invocation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SolverInvocationIdentity {
    tool: Arc<str>,
    version: Arc<str>,
    resolved_path: Arc<str>,
    binary_digest: Arc<str>,
    platform: Arc<str>,
    architecture: Arc<str>,
    arguments: Arc<[Arc<str>]>,
    identity_digest: Arc<str>,
}

impl SolverInvocationIdentity {
    pub(crate) fn from_runtime_vampire(
        version: impl Into<Arc<str>>,
        profile: &VampireInvocationProfile,
    ) -> Result<Self, FrameworkIIStateError> {
        let version = version.into();
        if version.is_empty() || version.len() > 4096 {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "the runtime Vampire version is empty or unbounded",
            ));
        }
        require_sha256("runtime Vampire executable", profile.executable_sha256())?;
        let canonical = std::fs::canonicalize(profile.executable()).map_err(|error| {
            checker_failure(format!(
                "resolve runtime Vampire executable {} for receipt: {error}",
                profile.executable().display()
            ))
        })?;
        if canonical != profile.executable() {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "the launched Vampire profile does not retain its canonical executable path",
            ));
        }
        let resolved_path = path_text(&canonical, "runtime Vampire executable")?;
        let arguments = profile
            .arguments()
            .iter()
            .map(|argument| {
                argument.to_str().map(Arc::<str>::from).ok_or(
                    FrameworkIIStateError::InvalidEvidence(
                        "a runtime Vampire argument is not valid UTF-8",
                    ),
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        Self::from_parts(
            Arc::from("vampire"),
            version,
            resolved_path,
            Arc::from(profile.executable_sha256()),
            Arc::from(std::env::consts::OS),
            Arc::from(std::env::consts::ARCH),
            arguments,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub fn from_parts(
        tool: Arc<str>,
        version: Arc<str>,
        resolved_path: Arc<str>,
        binary_digest: Arc<str>,
        platform: Arc<str>,
        architecture: Arc<str>,
        arguments: Vec<Arc<str>>,
    ) -> Result<Self, FrameworkIIStateError> {
        if [
            tool.as_ref(),
            version.as_ref(),
            resolved_path.as_ref(),
            platform.as_ref(),
            architecture.as_ref(),
        ]
        .iter()
        .any(|value| value.is_empty() || value.len() > 4096)
        {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "a solver-invocation identity has an empty or unbounded field",
            ));
        }
        require_sha256("solver executable", &binary_digest)?;
        if arguments.iter().any(|argument| argument.len() > 64 * 1024) {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "a solver argument exceeds the receipt bound",
            ));
        }
        let payload = json!({
            "domain": "whiel-solver-invocation-v1",
            "tool": tool.as_ref(),
            "version": version.as_ref(),
            "resolved_path": resolved_path.as_ref(),
            "binary_digest": binary_digest.as_ref(),
            "platform": platform.as_ref(),
            "architecture": architecture.as_ref(),
            "arguments": arguments.iter().map(AsRef::<str>::as_ref).collect::<Vec<_>>(),
        });
        let identity_digest = Arc::from(canonical_value_sha256(&payload));
        Ok(Self {
            tool,
            version,
            resolved_path,
            binary_digest,
            platform,
            architecture,
            arguments: arguments.into(),
            identity_digest,
        })
    }

    pub fn identity_digest(&self) -> &str {
        &self.identity_digest
    }

    pub fn tool(&self) -> &str {
        &self.tool
    }

    pub fn version(&self) -> &str {
        &self.version
    }

    pub fn resolved_path(&self) -> &str {
        &self.resolved_path
    }

    pub fn binary_digest(&self) -> &str {
        &self.binary_digest
    }

    pub fn arguments(&self) -> &[Arc<str>] {
        &self.arguments
    }

    pub fn platform(&self) -> &str {
        &self.platform
    }

    pub fn architecture(&self) -> &str {
        &self.architecture
    }

    fn identity_fields(&self) -> Value {
        json!({
            "tool": self.tool.as_ref(),
            "version": self.version.as_ref(),
            "resolved_path": self.resolved_path.as_ref(),
            "binary_digest": self.binary_digest.as_ref(),
            "platform": self.platform.as_ref(),
            "architecture": self.architecture.as_ref(),
            "arguments": self.arguments.iter().map(AsRef::<str>::as_ref).collect::<Vec<_>>(),
            "identity_digest": self.identity_digest.as_ref(),
        })
    }
}

/// Caller-supplied certification selector paired with one runtime winner.
///
/// Roadmap step 7 must resolve this value through the pinned production
/// registry before it becomes certificate authority.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeancheckCertificationProfile {
    profile: ProofSearchProfile,
    profile_version: Arc<str>,
    leancheck_invocation: SolverInvocationIdentity,
    permitted_cadical: Option<SolverInvocationIdentity>,
    vamplean_digest: Arc<str>,
    generator_digest: Arc<str>,
    output_contract_digest: Arc<str>,
    transformer_digest: Arc<str>,
    lean_bridge_digest: Arc<str>,
    profile_digest: Arc<str>,
}

impl LeancheckCertificationProfile {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        profile: ProofSearchProfile,
        profile_version: impl Into<Arc<str>>,
        leancheck_invocation: SolverInvocationIdentity,
        permitted_cadical: Option<SolverInvocationIdentity>,
        vamplean_digest: impl Into<Arc<str>>,
        generator_digest: impl Into<Arc<str>>,
        output_contract_digest: impl Into<Arc<str>>,
        transformer_digest: impl Into<Arc<str>>,
        lean_bridge_digest: impl Into<Arc<str>>,
    ) -> Result<Self, FrameworkIIStateError> {
        let profile_version = profile_version.into();
        if profile_version.is_empty() || profile_version.len() > 4096 {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "the leancheck certification profile version is empty or unbounded",
            ));
        }
        let vamplean_digest = vamplean_digest.into();
        let generator_digest = generator_digest.into();
        let output_contract_digest = output_contract_digest.into();
        let transformer_digest = transformer_digest.into();
        let lean_bridge_digest = lean_bridge_digest.into();
        for (name, digest) in [
            ("VampLean", vamplean_digest.as_ref()),
            ("certificate generator", generator_digest.as_ref()),
            ("output contract", output_contract_digest.as_ref()),
            ("proof transformer", transformer_digest.as_ref()),
            ("Lean bridge", lean_bridge_digest.as_ref()),
        ] {
            require_sha256(name, digest)?;
        }
        let payload = json!({
            "domain": "whiel-leancheck-certification-profile-v1",
            "profile": profile.identity_name(),
            "profile_version": profile_version.as_ref(),
            "leancheck_invocation": leancheck_invocation.identity_fields(),
            "permitted_cadical": permitted_cadical.as_ref().map(SolverInvocationIdentity::identity_fields),
            "vamplean_digest": vamplean_digest.as_ref(),
            "generator_digest": generator_digest.as_ref(),
            "output_contract_digest": output_contract_digest.as_ref(),
            "transformer_digest": transformer_digest.as_ref(),
            "lean_bridge_digest": lean_bridge_digest.as_ref(),
        });
        let profile_digest = Arc::from(canonical_value_sha256(&payload));
        Ok(Self {
            profile,
            profile_version,
            leancheck_invocation,
            permitted_cadical,
            vamplean_digest,
            generator_digest,
            output_contract_digest,
            transformer_digest,
            lean_bridge_digest,
            profile_digest,
        })
    }

    pub fn profile(&self) -> ProofSearchProfile {
        self.profile
    }

    pub fn profile_digest(&self) -> &str {
        &self.profile_digest
    }

    pub fn profile_version(&self) -> &str {
        &self.profile_version
    }

    pub fn leancheck_invocation(&self) -> &SolverInvocationIdentity {
        &self.leancheck_invocation
    }

    pub fn permitted_cadical(&self) -> Option<&SolverInvocationIdentity> {
        self.permitted_cadical.as_ref()
    }

    pub fn vamplean_digest(&self) -> &str {
        &self.vamplean_digest
    }

    pub fn generator_digest(&self) -> &str {
        &self.generator_digest
    }

    pub fn output_contract_digest(&self) -> &str {
        &self.output_contract_digest
    }

    pub fn transformer_digest(&self) -> &str {
        &self.transformer_digest
    }

    pub fn lean_bridge_digest(&self) -> &str {
        &self.lean_bridge_digest
    }

    fn identity_fields(&self) -> Value {
        json!({
            "profile": self.profile.identity_name(),
            "profile_version": self.profile_version.as_ref(),
            "leancheck_invocation": self.leancheck_invocation.identity_fields(),
            "permitted_cadical": self.permitted_cadical.as_ref().map(SolverInvocationIdentity::identity_fields),
            "vamplean_digest": self.vamplean_digest.as_ref(),
            "generator_digest": self.generator_digest.as_ref(),
            "output_contract_digest": self.output_contract_digest.as_ref(),
            "transformer_digest": self.transformer_digest.as_ref(),
            "lean_bridge_digest": self.lean_bridge_digest.as_ref(),
            "profile_digest": self.profile_digest.as_ref(),
        })
    }
}

/// Runtime pairing of direct and CASC proof winners with provisional replay
/// selectors. The final certificate boundary revalidates the pinned registry.
#[derive(Clone, Debug)]
pub struct FrameworkIICertificationProfiles {
    direct: LeancheckCertificationProfile,
    casc_2025: LeancheckCertificationProfile,
}

impl FrameworkIICertificationProfiles {
    pub fn new(
        direct: LeancheckCertificationProfile,
        casc_2025: LeancheckCertificationProfile,
    ) -> Result<Self, FrameworkIIStateError> {
        if direct.profile() != ProofSearchProfile::Direct
            || casc_2025.profile() != ProofSearchProfile::Casc2025
        {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "leancheck profiles are not bound to direct and casc_2025 respectively",
            ));
        }
        Ok(Self { direct, casc_2025 })
    }

    pub fn direct(&self) -> &LeancheckCertificationProfile {
        &self.direct
    }

    pub fn casc_2025(&self) -> &LeancheckCertificationProfile {
        &self.casc_2025
    }

    fn select(&self, winner: ProofSearchProfile) -> &LeancheckCertificationProfile {
        match winner {
            ProofSearchProfile::Direct => &self.direct,
            ProofSearchProfile::Casc2025 => &self.casc_2025,
        }
    }
}

// ------------------------------------------------------------
// Reviewed Protected-Precondition Theorem Selectors
// ------------------------------------------------------------

/// Reviewed theorem shapes that may bypass runtime proof search.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProtectedPreconditionRule {
    EdbPreconditionInitialization {
        source_conjunct: Arc<str>,
        target_clause: crate::houdini::ClauseId,
        target_context: Arc<str>,
    },
    EdbPreconditionMaintenance {
        source_conjunct: Arc<str>,
        unchanged_relations: Arc<str>,
        target_clause: crate::houdini::ClauseId,
        target_context: Arc<str>,
    },
}

impl ProtectedPreconditionRule {
    pub fn source_conjunct(&self) -> &str {
        match self {
            Self::EdbPreconditionInitialization {
                source_conjunct, ..
            }
            | Self::EdbPreconditionMaintenance {
                source_conjunct, ..
            } => source_conjunct,
        }
    }

    pub fn target_clause(&self) -> crate::houdini::ClauseId {
        match self {
            Self::EdbPreconditionInitialization { target_clause, .. }
            | Self::EdbPreconditionMaintenance { target_clause, .. } => *target_clause,
        }
    }

    pub fn target_context(&self) -> &str {
        match self {
            Self::EdbPreconditionInitialization { target_context, .. }
            | Self::EdbPreconditionMaintenance { target_context, .. } => target_context,
        }
    }

    pub fn unchanged_relations(&self) -> Option<&str> {
        match self {
            Self::EdbPreconditionInitialization { .. } => None,
            Self::EdbPreconditionMaintenance {
                unchanged_relations,
                ..
            } => Some(unchanged_relations),
        }
    }

    fn identity_fields(&self) -> Value {
        match self {
            Self::EdbPreconditionInitialization {
                source_conjunct,
                target_clause,
                target_context,
            } => json!({
                "kind": "edb_precondition_initialization",
                "source_conjunct": source_conjunct.as_ref(),
                "target_clause": target_clause.get(),
                "target_context": target_context.as_ref(),
            }),
            Self::EdbPreconditionMaintenance {
                source_conjunct,
                unchanged_relations,
                target_clause,
                target_context,
            } => json!({
                "kind": "edb_precondition_maintenance",
                "source_conjunct": source_conjunct.as_ref(),
                "unchanged_relations": unchanged_relations.as_ref(),
                "target_clause": target_clause.get(),
                "target_context": target_context.as_ref(),
            }),
        }
    }
}

/// Durable runtime selector for one allowlisted protected-precondition theorem.
///
/// The final certificate pass must reconstruct this route in Lean and bind
/// the compiled theorem/dependency closure before it becomes kernel authority.
#[derive(Clone, Debug)]
pub struct ProtectedTheoremSelectionReceipt {
    replay_capture: ReplayProductionCapture,
    replay_prepared: Result<ReplayPreparedProjection, ReplayProductionError>,
    request_digest: Arc<str>,
    selector_registry_digest: Arc<str>,
    rule: ProtectedPreconditionRule,
    source_route_digest: Arc<str>,
    source_formula_digest: Arc<str>,
    target_vc_digest: Arc<str>,
    preparation_digest: Arc<str>,
    theorem_name: Arc<str>,
    registry_entry_digest: Arc<str>,
    receipt_artifact: ArtifactRef,
    selection_digest: Arc<str>,
}

impl ProtectedTheoremSelectionReceipt {
    pub(super) fn replay_projection(&self) -> &ReplayProductionCapture {
        &self.replay_capture
    }
    pub(super) fn replay_preparation(
        &self,
    ) -> Result<&ReplayPreparedProjection, &ReplayProductionError> {
        self.replay_prepared.as_ref()
    }
    fn commit(
        subject: &FrameworkIICheckSubject,
        prepared: &PreparedFrameworkIIEntailment,
        candidate: FrameworkIIProtectedTheoremCandidate,
        artifacts: &ArtifactStore,
        cancellation: &CancellationToken,
    ) -> Result<Self, FrameworkIIReceiptError> {
        // Protected precondition rows are clause rows; the termination
        // request names no clause and never closes by theorem route.
        let Some(request) = subject.as_clause() else {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "the termination request has no protected precondition route",
            )
            .into());
        };
        if !prepared.matches_subject(subject)
            || prepared.entailment().task_identity() != request.snapshot().scope().task_identity()
            || artifacts.task_identity() != prepared.entailment().task_identity()
        {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "a protected-theorem selection is bound to another task or request",
            )
            .into());
        }
        for (name, digest) in [
            (
                "protected precondition route",
                candidate.source_route_digest.as_ref(),
            ),
            ("source formula", candidate.source_formula_digest.as_ref()),
            ("target VC", prepared.semantic_vc_digest()),
            ("target obligation", prepared.framework_context_digest()),
        ] {
            require_sha256(name, digest)?;
        }
        // The route is only valid for a protected level-zero record; do not
        // trust the semantic adapter's judgement about that.
        let record = request.snapshot().records().get(&request.clause()).ok_or(
            FrameworkIIStateError::InvalidEvidence(
                "a protected-theorem selection targets a clause outside its snapshot",
            ),
        )?;
        if !record.is_protected() || request.level() != super::types::FrameworkIILevel::ZERO {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "only a protected level-zero row may close through the theorem route",
            )
            .into());
        }
        if !matches!(
            record.origin(),
            super::catalog::ExtendedClauseOrigin::EdbPreconditionSystem { route_digest, .. }
                if route_digest.as_ref() == candidate.source_route_digest.as_ref()
        ) {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "a protected-theorem selection cites another route than its record",
            )
            .into());
        }
        let rule = match request.role() {
            FrameworkIICheckRole::Initialization => {
                if candidate.theorem_name.as_ref() != EDB_PRECONDITION_INIT_THEOREM {
                    return Err(FrameworkIIStateError::InvalidEvidence(
                        "an initialization route changed its allowlisted theorem",
                    )
                    .into());
                }
                ProtectedPreconditionRule::EdbPreconditionInitialization {
                    source_conjunct: Arc::clone(&candidate.source_formula_digest),
                    target_clause: request.clause(),
                    target_context: Arc::from(prepared.framework_context_digest()),
                }
            }
            FrameworkIICheckRole::Maintenance => {
                if candidate.theorem_name.as_ref() != EDB_PRECONDITION_MAINT_THEOREM {
                    return Err(FrameworkIIStateError::InvalidEvidence(
                        "a maintenance route changed its allowlisted theorem",
                    )
                    .into());
                }
                ProtectedPreconditionRule::EdbPreconditionMaintenance {
                    source_conjunct: Arc::clone(&candidate.source_formula_digest),
                    unchanged_relations: Arc::clone(&candidate.unchanged_relations_digest),
                    target_clause: request.clause(),
                    target_context: Arc::from(prepared.framework_context_digest()),
                }
            }
        };
        let registry_fields = protected_theorem_selector_registry_fields();
        let selector_registry_digest = Arc::<str>::from(canonical_value_sha256(&registry_fields));
        let registry_entry_fields = replay_registry_entry_fields(
            &selector_registry_digest,
            match request.role() {
                FrameworkIICheckRole::Initialization => "edb_precondition_initialization",
                FrameworkIICheckRole::Maintenance => "edb_precondition_maintenance",
            },
            &candidate.theorem_name,
        );
        let registry_entry_digest =
            Arc::<str>::from(canonical_value_sha256(&registry_entry_fields));
        let selection_fields = replay_protected_fields! {
            request_digest: request.request_digest(),
            selector_registry_digest: selector_registry_digest.as_ref(),
            rule: rule.identity_fields(),
            source_route_digest: candidate.source_route_digest.as_ref(),
            source_formula_digest: candidate.source_formula_digest.as_ref(),
            target_vc_digest: prepared.semantic_vc_digest(),
            fixed_ambient_job: fixed_ambient_job_fields(prepared),
            theorem_name: candidate.theorem_name.as_ref(),
            registry_entry_digest: registry_entry_digest.as_ref()
        };
        let selection_digest = Arc::<str>::from(canonical_value_sha256(&selection_fields));
        let replay_prepared = prepared.replay_projection();
        let replay_capture = match &replay_prepared {
            Ok(_) => replay_capture_production(
                "protected",
                &selection_fields,
                &selection_digest,
                None,
                None,
            ),
            Err(reason) => ReplayProductionCapture::NonReplayable(reason.clone()),
        };
        let payload = json!({
            "kind": "framework_ii_protected_theorem_selection",
            "fields": selection_fields,
            "selection_digest": selection_digest.as_ref(),
        })
        .to_string()
        .into_bytes()
        .into_boxed_slice();
        if cancellation.should_stop() {
            return Err(FrameworkIIStateError::Cancelled.into());
        }
        let receipt_artifact = artifacts
            .publish(ArtifactKind::Witness, payload)
            .map_err(FrameworkIIReceiptError::Failure)?;
        Ok(Self {
            replay_capture,
            replay_prepared,
            request_digest: Arc::from(request.request_digest()),
            selector_registry_digest,
            rule,
            source_route_digest: candidate.source_route_digest,
            source_formula_digest: candidate.source_formula_digest,
            target_vc_digest: Arc::from(prepared.semantic_vc_digest()),
            preparation_digest: Arc::from(prepared.prepare_request_digest()),
            theorem_name: candidate.theorem_name,
            registry_entry_digest,
            receipt_artifact,
            selection_digest,
        })
    }

    pub fn request_digest(&self) -> &str {
        &self.request_digest
    }

    pub fn selector_registry_digest(&self) -> &str {
        &self.selector_registry_digest
    }

    pub fn rule(&self) -> &ProtectedPreconditionRule {
        &self.rule
    }

    pub fn source_route_digest(&self) -> &str {
        &self.source_route_digest
    }

    pub fn source_formula_digest(&self) -> &str {
        &self.source_formula_digest
    }

    pub fn target_vc_digest(&self) -> &str {
        &self.target_vc_digest
    }

    pub fn preparation_digest(&self) -> &str {
        &self.preparation_digest
    }

    pub fn theorem_name(&self) -> &str {
        &self.theorem_name
    }

    /// Versioned registry-entry digest used by the runtime selector.
    ///
    /// This deliberately does not claim to hash the compiled theorem closure;
    /// the certificate replay owns that later trust boundary.
    pub fn registry_entry_digest(&self) -> &str {
        &self.registry_entry_digest
    }

    pub fn receipt_artifact(&self) -> ArtifactRef {
        self.receipt_artifact
    }

    pub fn selection_digest(&self) -> &str {
        &self.selection_digest
    }
}

fn protected_theorem_selector_registry_fields() -> Value {
    json!({
        "domain": "whiel-framework-ii-protected-theorem-selector-registry-v2",
        "version": PROTECTED_THEOREM_SELECTOR_REGISTRY_VERSION,
        "entries": [
            {
                "rule": "edb_precondition_initialization",
                "theorem": EDB_PRECONDITION_INIT_THEOREM,
            },
            {
                "rule": "edb_precondition_maintenance",
                "theorem": EDB_PRECONDITION_MAINT_THEOREM,
            },
        ],
    })
}

// ------------------------------------------------------------
// Durable Proved Receipt
// ------------------------------------------------------------

/// Compact strategy-bearing authority for one proved fixed-ambient VC.
#[derive(Clone, Debug)]
pub struct RuntimeProofReceipt {
    replay_capture: ReplayProductionCapture,
    replay_prepared: Result<ReplayPreparedProjection, ReplayProductionError>,
    replay_terminal: Option<Arc<crate::entailment::ReplaySpecializedTerminalOwner>>,
    task_digest: Arc<str>,
    catalog_digest: Arc<str>,
    artifact_backend_digest: Arc<str>,
    semantic_version: u64,
    encoding_version: u64,
    framework_ii_context_digest: Arc<str>,
    request_digest: Arc<str>,
    job_id: Arc<str>,
    semantic_vc_digest: Arc<str>,
    query_digest: Arc<str>,
    query_bytes: u64,
    attempt: AttemptId,
    terminal_result_digest: Arc<str>,
    empty_check_digest: Arc<str>,
    winner: ProofSearchProfile,
    runtime_invocation: SolverInvocationIdentity,
    certification_profile: LeancheckCertificationProfile,
    preparation_digest: Arc<str>,
    query_artifact: ArtifactRef,
    proof_artifact: ArtifactRef,
    terminal_artifact: ArtifactRef,
    empty_check_artifact: ArtifactRef,
    receipt_artifact: ArtifactRef,
    receipt_digest: Arc<str>,
}

impl RuntimeProofReceipt {
    pub(super) fn replay_projection(&self) -> &ReplayProductionCapture {
        &self.replay_capture
    }
    pub(super) fn replay_preparation(
        &self,
    ) -> Result<&ReplayPreparedProjection, &ReplayProductionError> {
        self.replay_prepared.as_ref()
    }
    /// Validate and atomically publish the compact witness for a proved row.
    #[allow(clippy::too_many_arguments)]
    fn commit(
        subject: &FrameworkIICheckSubject,
        prepared: &PreparedFrameworkIIEntailment,
        attempt: &EntailmentAttemptScope,
        report: &SpecializedEntailmentCheckReport<FrameworkIIResolvedAttempt>,
        runtime_vampire_version: impl Into<Arc<str>>,
        certification_profiles: &FrameworkIICertificationProfiles,
        artifacts: &ArtifactStore,
        cancellation: &CancellationToken,
    ) -> Result<Self, FrameworkIIReceiptError> {
        let request = subject;
        if !prepared.matches_subject(subject) {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "the proved entailment is bound to another fixed-ambient request",
            )
            .into());
        }
        if artifacts.backend_id() != attempt.artifacts().backend_id()
            || artifacts.task_identity() != prepared.entailment().task_identity()
            || attempt.entailment_identity() != prepared.entailment().identity()
            || attempt.query_artifact() != prepared.entailment().query_artifact()
        {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "the proof attempt, entailment, and artifact backend do not match",
            )
            .into());
        }
        if report.attempt_id() != attempt.attempt_id() {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "the proof terminal row belongs to another attempt",
            )
            .into());
        }
        let terminal_artifact = report.terminal_artifact();
        let terminal_result_digest = report.terminal_result_digest();
        require_sha256("terminal result", terminal_result_digest)?;
        let FrameworkIIResolvedAttempt::Proved { proof, empty_check } = report.outcome() else {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "a runtime proof receipt was requested for a non-proof outcome",
            )
            .into());
        };
        validate_proof_bindings(prepared, attempt, proof, empty_check, artifacts)?;
        let query_artifact = prepared.entailment().query_artifact();
        let query = artifacts
            .resolve(query_artifact)
            .map_err(FrameworkIIReceiptError::Failure)?;
        let (query_digest, query_bytes) = digest_file(query.path())?;
        if query_bytes != query.byte_len() {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "the resolved query length differs from its artifact record",
            )
            .into());
        }
        let query_path = std::fs::canonicalize(query.path()).map_err(|error| {
            checker_failure(format!(
                "resolve runtime query {} for receipt: {error}",
                query.path().display()
            ))
        })?;
        if proof.invocation().arguments().last().map(Path::new) != Some(query_path.as_path()) {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "the proof invocation is not bound to the exact assembled query path",
            )
            .into());
        }
        let winner = ProofSearchProfile::from(proof.strategy());
        let proof_artifact = proof.output();
        let expected_mode = match winner {
            ProofSearchProfile::Direct => "proof_normal",
            ProofSearchProfile::Casc2025 => "proof_casc",
        };
        if proof.invocation().mode() != expected_mode {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "the proof winner disagrees with its exact Vampire invocation",
            )
            .into());
        }
        let runtime_invocation = SolverInvocationIdentity::from_runtime_vampire(
            runtime_vampire_version,
            proof.invocation(),
        )?;
        let certification_profile = certification_profiles.select(winner).clone();
        let task = prepared.entailment().task_identity();
        let task_digest = task_digest(task);
        let artifact_backend_digest: Arc<str> = Arc::from(canonical_value_sha256(&json!({
            "domain": "whiel-artifact-backend-v1",
            "task_digest": task_digest.as_ref(),
            "backend": artifacts.backend_id().to_string(),
        })));
        let receipt_fields = replay_runtime_proof_fields! {
            task_digest: task_digest.as_ref(),
            catalog_digest: prepared.catalog_digest(),
            artifact_backend_digest: artifact_backend_digest.as_ref(),
            semantic_version: task.semantic_version(),
            encoding_version: task.encoding_version(),
            framework_ii_context_digest: prepared.framework_context_digest(),
            request_digest: request.request_digest(),
            job_id: prepared.job_id(),
            semantic_vc_digest: prepared.semantic_vc_digest(),
            query_digest: query_digest.as_ref(),
            query_bytes: query_bytes,
            attempt: attempt.attempt_id().get(),
            terminal_result_digest: terminal_result_digest,
            empty_check_digest: empty_check.check_digest(),
            winner: winner.identity_name(),
            runtime_invocation: runtime_invocation.identity_fields(),
            certification_profile: certification_profile.identity_fields(),
            fixed_ambient_job: fixed_ambient_job_fields(prepared),
            query_artifact: artifact_fields(query_artifact),
            proof_artifact: artifact_fields(proof_artifact),
            terminal_artifact: artifact_fields(terminal_artifact),
            empty_check_artifact: artifact_fields(empty_check.artifact())
        };
        let receipt_digest = Arc::<str>::from(canonical_value_sha256(&receipt_fields));
        let replay_terminal = report.replay_terminal();
        let replay_prepared = prepared.replay_projection();
        let replay_capture = match &replay_prepared {
            Ok(_) => replay_capture_production(
                "runtime_proof",
                &receipt_fields,
                &receipt_digest,
                None,
                replay_terminal.as_deref(),
            ),
            Err(reason) => ReplayProductionCapture::NonReplayable(reason.clone()),
        };
        let payload = json!({
            "kind": "framework_ii_runtime_proof_receipt",
            "fields": receipt_fields,
            "receipt_digest": receipt_digest.as_ref(),
        })
        .to_string()
        .into_bytes()
        .into_boxed_slice();
        if cancellation.should_stop() {
            return Err(FrameworkIIStateError::Cancelled.into());
        }
        let receipt_artifact = attempt
            .artifacts()
            .publish(ArtifactKind::Witness, payload)
            .map_err(FrameworkIIReceiptError::Failure)?;
        Ok(Self {
            replay_capture,
            replay_prepared,
            replay_terminal,
            task_digest,
            catalog_digest: Arc::from(prepared.catalog_digest()),
            artifact_backend_digest,
            semantic_version: task.semantic_version(),
            encoding_version: task.encoding_version(),
            framework_ii_context_digest: Arc::from(prepared.framework_context_digest()),
            request_digest: Arc::from(request.request_digest()),
            job_id: Arc::from(prepared.job_id()),
            semantic_vc_digest: Arc::from(prepared.semantic_vc_digest()),
            query_digest,
            query_bytes,
            attempt: attempt.attempt_id(),
            terminal_result_digest: Arc::from(terminal_result_digest),
            empty_check_digest: Arc::from(empty_check.check_digest()),
            winner,
            runtime_invocation,
            certification_profile,
            preparation_digest: Arc::from(prepared.prepare_request_digest()),
            query_artifact,
            proof_artifact,
            terminal_artifact,
            empty_check_artifact: empty_check.artifact(),
            receipt_artifact,
            receipt_digest,
        })
    }

    pub fn request_digest(&self) -> &str {
        &self.request_digest
    }

    pub fn receipt_digest(&self) -> &str {
        &self.receipt_digest
    }

    pub fn job_id(&self) -> &str {
        &self.job_id
    }

    pub fn semantic_vc_digest(&self) -> &str {
        &self.semantic_vc_digest
    }

    pub fn winner(&self) -> ProofSearchProfile {
        self.winner
    }

    pub fn attempt(&self) -> AttemptId {
        self.attempt
    }

    pub fn receipt_artifact(&self) -> ArtifactRef {
        self.receipt_artifact
    }

    pub fn retained_artifacts(&self) -> [ArtifactRef; 5] {
        [
            self.query_artifact,
            self.proof_artifact,
            self.terminal_artifact,
            self.empty_check_artifact,
            self.receipt_artifact,
        ]
    }

    pub fn query_artifact(&self) -> ArtifactRef {
        self.query_artifact
    }

    pub fn proof_artifact(&self) -> ArtifactRef {
        self.proof_artifact
    }

    pub fn terminal_artifact(&self) -> ArtifactRef {
        self.terminal_artifact
    }

    pub fn empty_check_artifact(&self) -> ArtifactRef {
        self.empty_check_artifact
    }

    pub fn runtime_invocation(&self) -> &SolverInvocationIdentity {
        &self.runtime_invocation
    }

    pub fn certification_profile(&self) -> &LeancheckCertificationProfile {
        &self.certification_profile
    }

    pub fn query_digest(&self) -> &str {
        &self.query_digest
    }

    pub fn query_bytes(&self) -> u64 {
        self.query_bytes
    }

    pub fn empty_check_digest(&self) -> &str {
        &self.empty_check_digest
    }

    pub fn terminal_result_digest(&self) -> &str {
        &self.terminal_result_digest
    }

    pub fn task_digest(&self) -> &str {
        &self.task_digest
    }

    pub fn catalog_digest(&self) -> &str {
        &self.catalog_digest
    }

    pub fn artifact_backend_digest(&self) -> &str {
        &self.artifact_backend_digest
    }

    pub fn framework_ii_context_digest(&self) -> &str {
        &self.framework_ii_context_digest
    }

    pub fn semantic_version(&self) -> u64 {
        self.semantic_version
    }

    pub fn encoding_version(&self) -> u64 {
        self.encoding_version
    }

    pub fn preparation_digest(&self) -> &str {
        &self.preparation_digest
    }
}

// ------------------------------------------------------------
// Inconclusive And Refutation Evidence
// ------------------------------------------------------------

/// Complete safe retry frontier for one inconclusive checked attempt.
#[derive(Clone, Debug)]
pub struct FrameworkIIEntailmentProgress {
    replay_capture: ReplayProductionCapture,
    replay_prepared: Result<ReplayPreparedProjection, ReplayProductionError>,
    replay_terminal: Option<Arc<crate::entailment::ReplaySpecializedTerminalOwner>>,
    request_digest: Arc<str>,
    job_id: Arc<str>,
    semantic_vc_digest: Arc<str>,
    preparation_digest: Arc<str>,
    reason: FrameworkIIInconclusiveReason,
    attempt: AttemptId,
    next_fmb_start_size: Option<FmbSize>,
    previous_proof_allowance: Duration,
    current_proof_allowance: Duration,
    peer_failure: Option<FailureReport>,
    terminal_artifact: ArtifactRef,
    terminal_result_digest: Arc<str>,
    progress_artifact: ArtifactRef,
    progress_digest: Arc<str>,
}

impl FrameworkIIEntailmentProgress {
    pub(super) fn replay_projection(&self) -> &ReplayProductionCapture {
        &self.replay_capture
    }
    pub(super) fn replay_preparation(
        &self,
    ) -> Result<&ReplayPreparedProjection, &ReplayProductionError> {
        self.replay_prepared.as_ref()
    }
    #[allow(clippy::too_many_arguments)]
    fn commit(
        subject: &FrameworkIICheckSubject,
        prepared: &PreparedFrameworkIIEntailment,
        attempt: &EntailmentAttemptScope,
        report: &SpecializedEntailmentCheckReport<FrameworkIIResolvedAttempt>,
        previous_proof_allowance: Duration,
        budget: VampireSearchBudget,
        retained_fmb_start_size: Option<FmbSize>,
        cancellation: &CancellationToken,
    ) -> Result<Self, FrameworkIIReceiptError> {
        let request = subject;
        if !prepared.matches_subject(subject) || report.attempt_id() != attempt.attempt_id() {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "inconclusive progress is bound to another request or attempt",
            )
            .into());
        }
        let FrameworkIIResolvedAttempt::Inconclusive {
            reason,
            next_fmb_start_size: _,
            peer_failure,
            reuse_attempt: _,
        } = report.outcome()
        else {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "retry progress was requested for a conclusive fixed-ambient result",
            )
            .into());
        };
        let current_proof_allowance =
            budget
                .total_limit()
                .ok_or(FrameworkIIStateError::InvalidEvidence(
                    "fixed-ambient retry progress requires a finite current allowance",
                ))?;
        if previous_proof_allowance.is_zero() || previous_proof_allowance > current_proof_allowance
        {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "fixed-ambient retry progress has a nonmonotone proof allowance",
            )
            .into());
        }
        let terminal_artifact = report.terminal_artifact();
        let terminal_result_digest = report.terminal_result_digest();
        let peer_failure_fields = peer_failure.as_ref().map(failure_fields);
        let fields = replay_progress_fields! {
            request_digest: request.request_digest(),
            job_id: prepared.job_id(),
            semantic_vc_digest: prepared.semantic_vc_digest(),
            fixed_ambient_job: fixed_ambient_job_fields(prepared),
            reason: inconclusive_name(*reason),
            attempt: attempt.attempt_id().get(),
            next_fmb_start_size: retained_fmb_start_size.map(FmbSize::get),
            previous_proof_allowance_ns: previous_proof_allowance.as_nanos().to_string(),
            current_proof_allowance_ns: current_proof_allowance.as_nanos().to_string(),
            peer_failure: peer_failure_fields,
            terminal_artifact: artifact_fields(terminal_artifact),
            terminal_result_digest: terminal_result_digest
        };
        let progress_digest = Arc::<str>::from(canonical_value_sha256(&fields));
        let replay_terminal = report.replay_terminal();
        let replay_prepared = prepared.replay_projection();
        let replay_capture = match &replay_prepared {
            Ok(_) => replay_capture_production(
                "progress",
                &fields,
                &progress_digest,
                peer_failure.as_ref(),
                replay_terminal.as_deref(),
            ),
            Err(reason) => ReplayProductionCapture::NonReplayable(reason.clone()),
        };
        let payload = json!({
            "kind": "framework_ii_entailment_progress",
            "fields": fields,
            "progress_digest": progress_digest.as_ref(),
        })
        .to_string()
        .into_bytes()
        .into_boxed_slice();
        if cancellation.should_stop() {
            return Err(FrameworkIIStateError::Cancelled.into());
        }
        let progress_artifact = attempt
            .artifacts()
            .publish(ArtifactKind::Witness, payload)
            .map_err(FrameworkIIReceiptError::Failure)?;
        Ok(Self {
            replay_capture,
            replay_prepared,
            replay_terminal,
            request_digest: Arc::from(request.request_digest()),
            job_id: Arc::from(prepared.job_id()),
            semantic_vc_digest: Arc::from(prepared.semantic_vc_digest()),
            preparation_digest: Arc::from(prepared.prepare_request_digest()),
            reason: *reason,
            attempt: attempt.attempt_id(),
            next_fmb_start_size: retained_fmb_start_size,
            previous_proof_allowance,
            current_proof_allowance,
            peer_failure: peer_failure.clone(),
            terminal_artifact,
            terminal_result_digest: Arc::from(terminal_result_digest),
            progress_artifact,
            progress_digest,
        })
    }

    pub fn request_digest(&self) -> &str {
        &self.request_digest
    }

    pub fn progress_digest(&self) -> &str {
        &self.progress_digest
    }

    pub fn job_id(&self) -> &str {
        &self.job_id
    }

    pub fn semantic_vc_digest(&self) -> &str {
        &self.semantic_vc_digest
    }

    pub fn preparation_digest(&self) -> &str {
        &self.preparation_digest
    }

    pub fn reason(&self) -> FrameworkIIInconclusiveReason {
        self.reason
    }

    pub fn attempt(&self) -> AttemptId {
        self.attempt
    }

    pub fn next_fmb_start_size(&self) -> Option<FmbSize> {
        self.next_fmb_start_size
    }

    pub fn progress_artifact(&self) -> ArtifactRef {
        self.progress_artifact
    }

    pub fn previous_proof_allowance(&self) -> Duration {
        self.previous_proof_allowance
    }

    pub fn current_proof_allowance(&self) -> Duration {
        self.current_proof_allowance
    }

    pub fn peer_failure(&self) -> Option<&FailureReport> {
        self.peer_failure.as_ref()
    }

    pub fn terminal_artifact(&self) -> ArtifactRef {
        self.terminal_artifact
    }

    pub fn terminal_result_digest(&self) -> &str {
        &self.terminal_result_digest
    }
}

/// Legacy-named search-control authority for a Lean-checked empty assignment.
#[derive(Clone, Debug)]
pub struct ValidatedFiniteRefutation {
    replay_capture: ReplayProductionCapture,
    replay_prepared: Result<ReplayPreparedProjection, ReplayProductionError>,
    replay_terminal: Option<Arc<crate::entailment::ReplaySpecializedTerminalOwner>>,
    request_digest: Arc<str>,
    job_id: Arc<str>,
    semantic_vc_digest: Arc<str>,
    preparation_digest: Arc<str>,
    attempt: AttemptId,
    terminal_artifact: ArtifactRef,
    terminal_result_digest: Arc<str>,
    source_artifact: ArtifactRef,
    validation_identity: Arc<Value>,
    validation_digest: Arc<str>,
    validation_artifact: ArtifactRef,
    receipt_artifact: ArtifactRef,
    refutation_digest: Arc<str>,
}

impl ValidatedFiniteRefutation {
    pub(super) fn replay_projection(&self) -> &ReplayProductionCapture {
        &self.replay_capture
    }
    pub(super) fn replay_preparation(
        &self,
    ) -> Result<&ReplayPreparedProjection, &ReplayProductionError> {
        self.replay_prepared.as_ref()
    }
    /// Promote only an exact worker-validated empty assignment to authority.
    #[allow(clippy::too_many_arguments)]
    fn commit(
        subject: &FrameworkIICheckSubject,
        prepared: &PreparedFrameworkIIEntailment,
        attempt: &EntailmentAttemptScope,
        report: &SpecializedEntailmentCheckReport<FrameworkIIResolvedAttempt>,
        cancellation: &CancellationToken,
    ) -> Result<Self, FrameworkIIReceiptError> {
        let request = subject;
        if !prepared.matches_subject(subject) || report.attempt_id() != attempt.attempt_id() {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "a validated refutation is bound to another request or attempt",
            )
            .into());
        }
        let FrameworkIIResolvedAttempt::Refuted(evidence) = report.outcome() else {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "a refutation receipt was requested for a non-refutation outcome",
            )
            .into());
        };
        let source_artifact = evidence.source_artifact;
        let validation_identity = evidence.validation_identity.clone();
        let validation_digest = Arc::clone(&evidence.validation_digest);
        let validation_artifact = evidence.validation_artifact;
        require_sha256("finite-refutation validation", &validation_digest)?;
        if canonical_value_sha256(&validation_identity) != validation_digest.as_ref() {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "the finite-refutation validation digest does not bind its full identity",
            )
            .into());
        }
        validate_fixed_ambient_refutation_identity(
            prepared,
            &validation_identity,
            source_artifact.kind(),
        )?;
        let terminal_artifact = report.terminal_artifact();
        let terminal_result_digest = report.terminal_result_digest();
        for reference in [terminal_artifact, source_artifact, validation_artifact] {
            if reference.backend_id() != attempt.artifacts().backend_id() {
                return Err(FrameworkIIStateError::InvalidEvidence(
                    "a finite-refutation artifact belongs to another backend",
                )
                .into());
            }
        }
        let fields = replay_refutation_fields! {
            request_digest: request.request_digest(),
            job_id: prepared.job_id(),
            semantic_vc_digest: prepared.semantic_vc_digest(),
            fixed_ambient_job: fixed_ambient_job_fields(prepared),
            attempt: attempt.attempt_id().get(),
            terminal_artifact: artifact_fields(terminal_artifact),
            terminal_result_digest: terminal_result_digest,
            source_artifact: artifact_fields(source_artifact),
            validation_identity: validation_identity.clone(),
            validation_digest: validation_digest.as_ref(),
            validation_artifact: artifact_fields(validation_artifact)
        };
        let refutation_digest = Arc::<str>::from(canonical_value_sha256(&fields));
        let replay_terminal = report.replay_terminal();
        let replay_prepared = prepared.replay_projection();
        let replay_capture = match &replay_prepared {
            Ok(_) => replay_capture_production(
                "validated_refutation",
                &fields,
                &refutation_digest,
                None,
                replay_terminal.as_deref(),
            ),
            Err(reason) => ReplayProductionCapture::NonReplayable(reason.clone()),
        };
        let payload = json!({
            "kind": "framework_ii_validated_finite_refutation",
            "fields": fields,
            "refutation_digest": refutation_digest.as_ref(),
        })
        .to_string()
        .into_bytes()
        .into_boxed_slice();
        if cancellation.should_stop() {
            return Err(FrameworkIIStateError::Cancelled.into());
        }
        let receipt_artifact = attempt
            .artifacts()
            .publish(ArtifactKind::Witness, payload)
            .map_err(FrameworkIIReceiptError::Failure)?;
        Ok(Self {
            replay_capture,
            replay_prepared,
            replay_terminal,
            request_digest: Arc::from(request.request_digest()),
            job_id: Arc::from(prepared.job_id()),
            semantic_vc_digest: Arc::from(prepared.semantic_vc_digest()),
            preparation_digest: Arc::from(prepared.prepare_request_digest()),
            attempt: attempt.attempt_id(),
            terminal_artifact,
            terminal_result_digest: Arc::from(terminal_result_digest),
            source_artifact,
            validation_identity: Arc::new(validation_identity),
            validation_digest,
            validation_artifact,
            receipt_artifact,
            refutation_digest,
        })
    }

    pub fn request_digest(&self) -> &str {
        &self.request_digest
    }

    pub fn refutation_digest(&self) -> &str {
        &self.refutation_digest
    }

    pub fn job_id(&self) -> &str {
        &self.job_id
    }

    pub fn semantic_vc_digest(&self) -> &str {
        &self.semantic_vc_digest
    }

    pub fn preparation_digest(&self) -> &str {
        &self.preparation_digest
    }

    pub fn attempt(&self) -> AttemptId {
        self.attempt
    }

    pub fn terminal_artifact(&self) -> ArtifactRef {
        self.terminal_artifact
    }

    pub fn terminal_result_digest(&self) -> &str {
        &self.terminal_result_digest
    }

    pub fn source_artifact(&self) -> ArtifactRef {
        self.source_artifact
    }

    pub fn validation_identity(&self) -> &Value {
        &self.validation_identity
    }

    pub fn validation_digest(&self) -> &str {
        &self.validation_digest
    }

    pub fn validation_artifact(&self) -> ArtifactRef {
        self.validation_artifact
    }

    pub fn receipt_artifact(&self) -> ArtifactRef {
        self.receipt_artifact
    }
}

// ------------------------------------------------------------
// Semantic Dictionary: Tagged-Premise Subsumption (Pass 7.5b)
// ------------------------------------------------------------

/// Which subsumption rule closed a reused check.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FrameworkIISemanticReuseKind {
    /// The request's own tagged premise set contained an earlier proof's
    /// cited tagged set for the same conjecture (monotonicity of
    /// entailment: weakening an already-closed entailment's hypotheses
    /// cannot break it).
    ProofSubsumption,
    /// The request's own tagged premise set was contained in an earlier
    /// validated refutation's full tagged set for the same conjecture (the
    /// countermodel already falsifies every one of the larger set's
    /// premises, and the smaller request's premises are all among them).
    RefutationSubsumption,
    /// The request's *exact* semantic key already carries an inconclusive
    /// entry and the retry policy grants no further launch for it — either
    /// its allowance list is exhausted, or the key was already launched in
    /// this epoch. Inconclusiveness subsumes in neither direction, so this
    /// is the one reuse kind that matches only on the exact key.
    ///
    /// The distinction matters to the controller: it suspends a clause for
    /// the rest of the epoch only after an inconclusive *launch*, never
    /// after an inconclusive reuse (`houdini.tex` Section 4.3,
    /// "Inconclusive as failure"), so every inconclusive outcome carries
    /// this provenance or none.
    InconclusiveEntry,
}

/// A resolved runtime check outcome reused for another request whose tagged
/// premise set stands in the required subsumption relation to an
/// already-resolved attempt from earlier in this run, without repeating
/// worker preparation or a solver launch.
///
/// This never fabricates new proof or refutation authority: it is a
/// Rust-owned pointer from the reusing request back to the exact evidence
/// the original attempt already published (a runtime proof receipt, a
/// protected-theorem selection, or a validated finite refutation). The
/// referenced original is never itself a reuse — reuse always resolves to
/// the first attempt that closed this semantic verification condition.
#[derive(Clone, Debug)]
pub struct SemanticReuseEvidence {
    replay_capture: ReplayProductionCapture,
    request_digest: Arc<str>,
    kind: FrameworkIISemanticReuseKind,
    semantic_vc_key: Arc<str>,
    semantic_vc_key_identity: Arc<Value>,
    matched_tagged_premises: Arc<Value>,
    original_request_digest: Arc<str>,
    original_evidence_identity: Arc<str>,
    identity: Arc<str>,
}

impl SemanticReuseEvidence {
    pub(super) fn replay_projection(&self) -> &ReplayProductionCapture {
        &self.replay_capture
    }
    fn new(
        request: &FrameworkIICheckSubject,
        kind: FrameworkIISemanticReuseKind,
        semantic_vc_key: Arc<str>,
        semantic_vc_key_identity: Arc<Value>,
        matched_tagged_premises: Value,
        original: &FrameworkIICheckEvidence,
    ) -> Self {
        let kind_name = match kind {
            FrameworkIISemanticReuseKind::ProofSubsumption => "proof_subsumption",
            FrameworkIISemanticReuseKind::RefutationSubsumption => "refutation_subsumption",
            FrameworkIISemanticReuseKind::InconclusiveEntry => "inconclusive_entry",
        };
        let identity_fields = replay_reuse_fields! {
            reuse_kind: kind_name,
            semantic_vc_key: semantic_vc_key.as_ref(),
            matched_tagged_premises: &matched_tagged_premises,
            original_request_digest: original.request_digest(),
            original_evidence_identity: original.identity()
        };
        let identity: Arc<str> = Arc::from(canonical_value_sha256(&identity_fields));
        let replay_capture = replay_capture_reuse(
            &identity_fields,
            &identity,
            request.request_digest(),
            &semantic_vc_key_identity,
        );
        Self {
            replay_capture,
            request_digest: Arc::from(request.request_digest()),
            kind,
            semantic_vc_key,
            semantic_vc_key_identity,
            matched_tagged_premises: Arc::new(matched_tagged_premises),
            original_request_digest: Arc::from(original.request_digest()),
            original_evidence_identity: Arc::from(original.identity()),
            identity,
        }
    }

    pub(crate) fn request_digest_arc(&self) -> Arc<str> {
        Arc::clone(&self.request_digest)
    }

    pub(crate) fn identity_arc(&self) -> Arc<str> {
        Arc::clone(&self.identity)
    }

    /// The digest of the reusing request bound to this evidence.
    pub fn request_digest(&self) -> &str {
        &self.request_digest
    }

    /// The digest identifying this reuse (a function of the semantic key and
    /// the original evidence's own identity).
    pub fn identity(&self) -> &str {
        &self.identity
    }

    /// Which subsumption rule closed this reuse.
    pub fn kind(&self) -> FrameworkIISemanticReuseKind {
        self.kind
    }

    /// SHA-256 digest of the reusing request's own semantic verification-
    /// condition key.
    pub fn semantic_vc_key(&self) -> &str {
        &self.semantic_vc_key
    }

    /// The reusing request's own complete semantic verification-condition
    /// key identity.
    pub fn semantic_vc_key_identity(&self) -> &Value {
        &self.semantic_vc_key_identity
    }

    /// The tagged premise set that actually matched: the original proof's
    /// cited set for a [`FrameworkIISemanticReuseKind::ProofSubsumption`],
    /// or the original refutation's full tagged set for a
    /// [`FrameworkIISemanticReuseKind::RefutationSubsumption`].
    pub fn matched_tagged_premises(&self) -> &Value {
        &self.matched_tagged_premises
    }

    /// The `request_digest` of the original attempt that first resolved this
    /// semantic verification condition.
    pub fn original_request_digest(&self) -> &str {
        &self.original_request_digest
    }

    /// The `identity` of the original attempt's own evidence (its runtime
    /// proof receipt digest, protected-theorem selection digest, or
    /// validated-refutation digest) — the audit trail back to the row that
    /// actually closed this verification condition.
    pub fn original_evidence_identity(&self) -> &str {
        &self.original_evidence_identity
    }
}

/// Compute the Rust-owned semantic verification-condition key for a check
/// request, entirely from Lean-issued clause-identity digests already held
/// by the snapshot — before any worker call.
///
/// The key's `tagged_premises` field is the exact tagged multiset Lean
/// builds for `(clause, level, role)` (see [`tagged_premise_set`] and
/// `houdini.tex` Section 4.3): for `Initialization`, `pre` plus (above level
/// 0) `not_theta_guard` and a `theta` tag for every clause strictly below
/// the checked level; for `Maintenance`, a `plain` tag for every clause at
/// or below the checked level (including the conjecture itself) plus
/// `guard` plus (above level 0) `not_theta_guard` and `theta` below. Two
/// same-level maintenance checks of the same clause with different
/// same-level candidate sets are genuinely different verification
/// conditions — a proof under a larger inductive hypothesis set does not
/// transfer to a smaller one, and a refutation does not transfer to a
/// larger one — so they must key differently.
///
/// Two requests sharing this key denote the exact same verification
/// condition regardless of which `ClauseId` values or tentative snapshot
/// digests happen to carry it. Clause content is identified by its
/// Lean-issued `identity_sha256`, never by `ClauseId`, so an identical
/// clause re-interned in another run — or restored to the same level by
/// reconsideration — keys identically. This key remains an *exact*
/// identity for the request; the semantic dictionary's proof/refutation
/// subsumption lookups use [`tagged_premise_set`] and conjecture identity
/// directly rather than this composite digest, but every field kept here
/// (task/scope identity, role, checked level, conjecture identity) still
/// documents and pins the exact condition a request denotes.
fn semantic_vc_key_identity(subject: &FrameworkIICheckSubject) -> Value {
    let snapshot = subject.snapshot();
    match subject {
        FrameworkIICheckSubject::Clause(request) => {
            let conjecture_record = snapshot
                .records()
                .get(&request.clause())
                .expect("a check request's clause is placed in its own snapshot");
            json!({
                "kind": "whiel_framework_ii_semantic_vc_key",
                "version": FRAMEWORK_II_RUNTIME_CACHE_IDENTITY_VERSION,
                "task_identity": super::catalog::task_identity_fields(snapshot.scope()),
                "scope_identity": snapshot.scope().identity(),
                "role": match request.role() {
                    FrameworkIICheckRole::Initialization => "initialization",
                    FrameworkIICheckRole::Maintenance => "maintenance",
                },
                "conjecture": {
                    "identity_sha256": conjecture_record.formula().identity_sha256(),
                },
                "tagged_premises": tagged_premise_set_to_json(&tagged_premise_set(request)),
            })
        }
        FrameworkIICheckSubject::Termination(request) => json!({
            "kind": "whiel_framework_ii_semantic_vc_key",
            "version": FRAMEWORK_II_RUNTIME_CACHE_IDENTITY_VERSION,
            "task_identity": super::catalog::task_identity_fields(snapshot.scope()),
            "scope_identity": snapshot.scope().identity(),
            "role": "termination",
            "conjecture": {
                "identity_sha256": FRAMEWORK_II_TERMINATION_CONJECTURE_NAME,
            },
            // `houdini.tex` Section 4.4: "for Term, T is represented by the
            // sorted identity list of F" — the Core's clause identities
            // without levels, so an epoch that did not change the Core's
            // clause set produces the identical key.
            "tagged_premises": request
                .core_identities()
                .iter()
                .map(|identity| Value::from(identity.as_ref()))
                .collect::<Vec<_>>(),
        }),
    }
}

/// The fixed conjecture of the termination request, `(Term, post')`. It
/// names no clause, so the dictionary indexes every termination entry under
/// this one tagged conjecture and separates them by their tagged premise
/// sets alone.
pub(crate) const FRAMEWORK_II_TERMINATION_CONJECTURE_NAME: &str = "post_prime";

/// The tagged premise set of any request the production checker serves.
fn subject_tagged_premise_set(subject: &FrameworkIICheckSubject) -> TaggedPremiseSet {
    match subject {
        FrameworkIICheckSubject::Clause(request) => tagged_premise_set(request),
        FrameworkIICheckSubject::Termination(request) => {
            termination_tagged_premise_set(request.core())
        }
    }
}

/// The tagged conjecture a request's dictionary entries are indexed
/// under: the check role together with the Lean-issued content digest of
/// the checked clause's own formula, independent of level. The role is
/// part of the index because the two roles prove different conjectures
/// (`Initialization` proves `c`, `Maintenance` proves `wp(body, c)`), and
/// monotonicity of entailment only licenses reuse of a proof for the same
/// conjecture: a maintenance proof of `wp(body, c)` that cites only
/// body-invariant premises says nothing about `c` itself, so it must never
/// answer an initialization request.
fn conjecture_identity_of(subject: &FrameworkIICheckSubject) -> Arc<str> {
    match subject {
        FrameworkIICheckSubject::Clause(request) => {
            let digest = request
                .snapshot()
                .records()
                .get(&request.clause())
                .expect("a check request's clause is placed in its own snapshot")
                .formula()
                .identity_sha256();
            tagged_conjecture_key(request.role(), digest)
        }
        FrameworkIICheckSubject::Termination(_) => termination_conjecture_key(),
    }
}

/// Both tagged conjectures of one clause, for lookups that span roles.
const FRAMEWORK_II_CHECK_ROLES: [FrameworkIICheckRole; 2] = [
    FrameworkIICheckRole::Initialization,
    FrameworkIICheckRole::Maintenance,
];

/// One search-phase proof recorded for later proof-subsumption lookup: the
/// tagged premises the winning proof's own text actually cited (mapped
/// through Lean's `axiom_tags` table and stripped of `support` tags), and a
/// pointer back to the evidence that closed the original check.
#[derive(Clone)]
struct FrameworkIIDictionaryProofEntry {
    cited: Arc<TaggedPremiseSet>,
    evidence: FrameworkIICheckEvidence,
}

/// One Lean-validated finite refutation recorded for later
/// refutation-subsumption lookup: the complete tagged premise set of the
/// refuted request, a pointer back to the evidence that closed the original
/// check, and the retained countermodel.
#[derive(Clone)]
struct FrameworkIIDictionaryRefutationEntry {
    tagged: Arc<TaggedPremiseSet>,
    evidence: FrameworkIICheckEvidence,
    countermodel: Arc<FrameworkIIRetainedCountermodel>,
}

/// One inconclusive check recorded under the *exact* semantic key of the
/// request that produced it (`houdini.tex` Section 4.4, Definition
/// "Subsumption"): the reason, the number of launches made so far under the
/// retry policy, and a pointer back to the progress evidence of the last of
/// them.
///
/// Only a request with the same exact key consults it — inconclusiveness
/// subsumes in neither direction — and such a request is a hit, answered
/// Inconclusive without a launch, unless the retry policy grants a further
/// launch and the key was not already launched in this epoch.
#[derive(Clone)]
struct FrameworkIIDictionaryInconclusiveEntry {
    reason: FrameworkIIInconclusiveReason,
    launches: usize,
    tagged: Arc<TaggedPremiseSet>,
    evidence: FrameworkIICheckEvidence,
}

/// The semantic dictionary: every search-phase proof and Lean-validated
/// refutation resolved so far in this run, indexed by tagged conjecture
/// (role plus clause identity) and looked up by tagged-premise-set inclusion (see `houdini.tex`
/// Section 4.4, Definition "Subsumption"). Rust never interprets formula
/// text and never infers a premise from an axiom's position — every tagged
/// set here is either computed structurally by [`tagged_premise_set`] or
/// read verbatim from Lean's `axiom_tags` table.
#[derive(Default)]
struct FrameworkIISemanticDictionary {
    proof_entries: BTreeMap<Arc<str>, Vec<FrameworkIIDictionaryProofEntry>>,
    refutation_entries: BTreeMap<Arc<str>, Vec<FrameworkIIDictionaryRefutationEntry>>,
    /// Keyed by the exact level-free semantic key digest, never by tagged
    /// conjecture: an inconclusive entry matches only itself.
    inconclusive_entries: BTreeMap<Arc<str>, FrameworkIIDictionaryInconclusiveEntry>,
}

impl FrameworkIISemanticDictionary {
    /// A proof entry is a hit when its cited set is contained in `tags`
    /// (monotonicity of entailment: a proof from a subset of `tags` is also
    /// a proof from `tags`).
    ///
    /// Lean: `QFEntailment.valid_of_axioms_subset`
    /// (`Whiel/Synthesis/FrameworkII/FixedAmbient/DictionarySoundness.lean`).
    fn find_proof_hit(
        &self,
        conjecture: &str,
        tags: &TaggedPremiseSet,
    ) -> Option<&FrameworkIIDictionaryProofEntry> {
        self.proof_entries
            .get(conjecture)?
            .iter()
            .find(|entry| entry.cited.is_subset(tags))
    }

    /// A refutation entry is a hit when `tags` is contained in its full
    /// tagged set (the countermodel already falsifies every premise of the
    /// larger set, and `tags`'s premises are all among them).
    ///
    /// Lean: `QFEntailment.countermodel_of_axioms_subset`
    /// (`DictionarySoundness.lean`).
    fn find_refutation_hit(
        &self,
        conjecture: &str,
        tags: &TaggedPremiseSet,
    ) -> Option<&FrameworkIIDictionaryRefutationEntry> {
        self.refutation_entries
            .get(conjecture)?
            .iter()
            .find(|entry| tags.is_subset(&entry.tagged))
    }

    /// The inconclusive entry recorded under this exact semantic key, if
    /// any. Deliberately not a subsumption lookup.
    fn find_inconclusive(
        &self,
        semantic_vc_key: &str,
    ) -> Option<&FrameworkIIDictionaryInconclusiveEntry> {
        self.inconclusive_entries.get(semantic_vc_key)
    }

    /// Add, or advance the launch count of, the inconclusive entry under
    /// this exact semantic key.
    fn record_inconclusive(
        &mut self,
        semantic_vc_key: Arc<str>,
        reason: FrameworkIIInconclusiveReason,
        tagged: Arc<TaggedPremiseSet>,
        evidence: FrameworkIICheckEvidence,
    ) {
        let launches = self
            .inconclusive_entries
            .get(semantic_vc_key.as_ref())
            .map_or(0, |entry| entry.launches)
            .saturating_add(1);
        self.inconclusive_entries.insert(
            semantic_vc_key,
            FrameworkIIDictionaryInconclusiveEntry {
                reason,
                launches,
                tagged,
                evidence,
            },
        );
    }

    /// Drop an exhausted key's inconclusive entry once the same key resolves
    /// as a proof or a refutation: a decided key is never answered
    /// Inconclusive again.
    fn clear_inconclusive(&mut self, semantic_vc_key: &str) {
        self.inconclusive_entries.remove(semantic_vc_key);
    }

    fn record_proof(&mut self, conjecture: Arc<str>, entry: FrameworkIIDictionaryProofEntry) {
        self.proof_entries
            .entry(conjecture)
            .or_default()
            .push(entry);
    }

    /// The winning [`ProofSearchProfile`] of every condition of `core` that
    /// this run's search proved by a launch of its own, keyed by tagged
    /// conjecture.
    ///
    /// One conjecture can hold several proof entries: the same condition is
    /// re-posed as the Core grows and as its clause promotes, and each
    /// launch appends its own entry in check order. Which entry labels the
    /// frozen job is chosen deliberately, by the same subsumption rule the
    /// dictionary answers with: the **last** launched entry whose cited
    /// premises are contained in the tagged premise set of the condition as
    /// `core` — the final Core — poses it. That is the launch that closed
    /// this condition against *this* Core, rather than against a smaller
    /// earlier one, and taking the last of them prefers the most recent
    /// launch when several qualify.
    ///
    /// Two kinds of condition contribute nothing here and take the run's
    /// configured search profile at the freeze instead: one whose only
    /// proof entries carry theorem-selection authority (a protected
    /// precondition row — no solver ran, so no schedule won), and one whose
    /// every launched entry cites a premise this Core's request does not
    /// carry (a clause the compression pass moved down, say). There is no
    /// fallback *between* profiles either way.
    fn launched_proof_winners(
        &self,
        core: &LeveledCandidateSnapshot,
    ) -> Vec<(Arc<str>, ProofSearchProfile)> {
        let mut winners = Vec::new();
        for clause in core.canonical_order() {
            let Some(record) = core.records().get(clause) else {
                continue;
            };
            let Some(level) = core.level_of(*clause) else {
                continue;
            };
            for role in [
                FrameworkIICheckRole::Initialization,
                FrameworkIICheckRole::Maintenance,
            ] {
                let key = tagged_conjecture_key(role, record.formula().identity_sha256());
                let tags = tagged_premise_set_at(core, level, role);
                if let Some(profile) = self.last_launched_winner(&key, &tags) {
                    winners.push((key, profile));
                }
            }
        }
        let key = termination_conjecture_key();
        let tags = termination_tagged_premise_set(core);
        if let Some(profile) = self.last_launched_winner(&key, &tags) {
            winners.push((key, profile));
        }
        winners
    }

    /// The winning schedule of the last launched proof entry of
    /// `conjecture` whose cited premises are contained in `tags`.
    ///
    /// A theorem-closed entry is not a launched one and is skipped, not
    /// stopped at: the search may have closed a condition by theorem after
    /// having launched it earlier.
    fn last_launched_winner(
        &self,
        conjecture: &str,
        tags: &TaggedPremiseSet,
    ) -> Option<ProofSearchProfile> {
        self.proof_entries
            .get(conjecture)?
            .iter()
            .rev()
            .filter(|entry| entry.cited.is_subset(tags))
            .find_map(|entry| entry.evidence.runtime_proof())
            .map(|receipt| receipt.winner())
    }

    fn record_refutation(
        &mut self,
        conjecture: Arc<str>,
        entry: FrameworkIIDictionaryRefutationEntry,
    ) {
        self.refutation_entries
            .entry(conjecture)
            .or_default()
            .push(entry);
    }

    /// Every keyed entry, as `(kind, key, count)`, in a stable order.
    ///
    /// Test-only inspection: the counts a checker publishes say how often
    /// the dictionary answered, never what it holds.
    fn entry_summary(&self) -> Vec<(&'static str, String, usize)> {
        let proofs = self
            .proof_entries
            .iter()
            .map(|(key, entries)| ("proof", key.to_string(), entries.len()));
        let refutations = self
            .refutation_entries
            .iter()
            .map(|(key, entries)| ("refutation", key.to_string(), entries.len()));
        let inconclusive = self
            .inconclusive_entries
            .iter()
            .map(|(key, entry)| ("inconclusive", key.to_string(), entry.launches));
        let mut summary = proofs
            .chain(refutations)
            .chain(inconclusive)
            .collect::<Vec<_>>();
        summary.sort();
        summary
    }

    /// The strongest refutations recorded for `clause_identity` under
    /// either role. An initialization set always carries `pre` and never
    /// `guard`, a maintenance set the reverse, so no set of one role is
    /// contained in a set of the other and the antichain is taken over the
    /// union without cross-role interference.
    fn strongest_refutations(
        &self,
        clause_identity: &str,
        cap: Option<usize>,
    ) -> Vec<FrameworkIIRefutationSummary> {
        let entries: Vec<FrameworkIIDictionaryRefutationEntry> = FRAMEWORK_II_CHECK_ROLES
            .iter()
            .filter_map(|role| {
                self.refutation_entries
                    .get(&tagged_conjecture_key(*role, clause_identity))
            })
            .flat_map(|entries| entries.iter().cloned())
            .collect();
        if entries.is_empty() {
            return Vec::new();
        }
        let mut maximal = maximal_refutations(&entries);
        maximal.sort_by(|left, right| right.tagged.len().cmp(&left.tagged.len()));
        if let Some(cap) = cap {
            maximal.truncate(cap);
        }
        maximal
            .into_iter()
            .map(|entry| FrameworkIIRefutationSummary {
                tagged_premises: tagged_premise_set_to_json(&entry.tagged),
                validated_refutation: entry.evidence.validated_refutation().cloned().expect(
                    "a refutation-dictionary entry always carries validated refutation authority",
                ),
                countermodel: Arc::clone(&entry.countermodel),
            })
            .collect()
    }
}

/// The antichain of `entries` maximal under tagged-set inclusion: no
/// retained entry's tagged set is a strict subset of another retained
/// entry's. Equal sets are deduplicated (the earlier one is kept).
fn maximal_refutations(
    entries: &[FrameworkIIDictionaryRefutationEntry],
) -> Vec<&FrameworkIIDictionaryRefutationEntry> {
    let mut maximal: Vec<&FrameworkIIDictionaryRefutationEntry> = Vec::new();
    for candidate in entries {
        if maximal
            .iter()
            .any(|kept| candidate.tagged.is_subset(&kept.tagged))
        {
            continue;
        }
        maximal.retain(|kept| !kept.tagged.is_subset(&candidate.tagged));
        maximal.push(candidate);
    }
    maximal
}

/// One entry of [`FrameworkIIProductionChecker::strongest_refutations`]'s
/// result: a clause's refutation-dictionary entry whose tagged premise set
/// is maximal under inclusion among that clause's recorded refutations.
#[derive(Clone)]
pub struct FrameworkIIRefutationSummary {
    tagged_premises: Vec<Value>,
    validated_refutation: Arc<ValidatedFiniteRefutation>,
    countermodel: Arc<FrameworkIIRetainedCountermodel>,
}

impl FrameworkIIRefutationSummary {
    pub fn tagged_premises(&self) -> &[Value] {
        &self.tagged_premises
    }

    pub fn validated_refutation(&self) -> &Arc<ValidatedFiniteRefutation> {
        &self.validated_refutation
    }

    pub fn countermodel(&self) -> &FrameworkIIRetainedCountermodel {
        &self.countermodel
    }
}

// ------------------------------------------------------------
// Countermodel Retention (Pass 7.5b)
// ------------------------------------------------------------

/// One validated countermodel, retained up to a configurable tuple bound
/// (see [`FrameworkIIProductionCheckConfig::with_host_limits`]).
#[derive(Clone, Debug)]
pub enum FrameworkIIRetainedCountermodel {
    /// The decoded finite instance in full.
    Retained(FrameworkIICountermodelInstance),
    /// Beyond the tuple bound: a refutation exists, but only its tuple
    /// count is retained.
    FoundNotRetained { tuple_count: usize },
}

/// A validated countermodel's decoded finite instance: one relation table
/// per ambient relation, each with its concrete tuple rows.
#[derive(Clone, Debug)]
pub struct FrameworkIICountermodelInstance {
    relations: Arc<[FrameworkIICountermodelRelation]>,
    tuple_count: usize,
}

impl FrameworkIICountermodelInstance {
    pub fn relations(&self) -> &[FrameworkIICountermodelRelation] {
        &self.relations
    }

    /// Total tuple rows across every relation.
    pub fn tuple_count(&self) -> usize {
        self.tuple_count
    }
}

/// One relation table of a retained countermodel.
#[derive(Clone, Debug)]
pub struct FrameworkIICountermodelRelation {
    key: Arc<str>,
    arity: u32,
    rows: Arc<[Value]>,
}

impl FrameworkIICountermodelRelation {
    pub fn key(&self) -> &str {
        &self.key
    }

    pub fn arity(&self) -> u32 {
        self.arity
    }

    pub fn rows(&self) -> &[Value] {
        &self.rows
    }
}

/// Decode the relation tables Lean already checked into the validated
/// refutation's `validation_identity` (`interpretation_identity.
/// instance_identity.relations`, each `{key, arity, rows}` — see
/// `decode_refutation_response` in `solver.rs`, which requires this exact
/// shape before a refutation is ever accepted). Returns `None` only if that
/// invariant is somehow violated; callers treat a `None` as "not
/// retained" rather than panicking, since this is a caching heuristic, not
/// certificate authority.
/// One decoded countermodel relation before retention-bound truncation:
/// its key, arity, and tuple rows.
type DecodedCountermodelRelation = (Arc<str>, u32, Vec<Value>);

fn countermodel_relations_from_validation(
    validation_identity: &Value,
) -> Option<Vec<DecodedCountermodelRelation>> {
    let relations = validation_identity
        .get("interpretation_identity")?
        .get("instance_identity")?
        .get("relations")?
        .as_array()?;
    let mut decoded = Vec::with_capacity(relations.len());
    for relation in relations {
        let key = relation.get("key")?.as_str()?;
        let arity = relation.get("arity")?.as_u64()?;
        let rows = relation.get("rows")?.as_array()?.clone();
        decoded.push((Arc::<str>::from(key), arity as u32, rows));
    }
    Some(decoded)
}

/// Build the retained countermodel for a validated refutation.
///
/// `tuple_bound` is the run's optional `countermodel_retention_tuples` host
/// limit. `None` — the default — retains the countermodel in full at any
/// size; a run that sets the limit records a larger one as
/// [`FrameworkIIRetainedCountermodel::FoundNotRetained`] with its tuple
/// count, which is what the `countermodel` tool then reports.
fn build_retained_countermodel(
    validation_identity: &Value,
    tuple_bound: Option<usize>,
) -> FrameworkIIRetainedCountermodel {
    let Some(relations) = countermodel_relations_from_validation(validation_identity) else {
        return FrameworkIIRetainedCountermodel::FoundNotRetained { tuple_count: 0 };
    };
    let tuple_count: usize = relations.iter().map(|(_, _, rows)| rows.len()).sum();
    if tuple_bound.is_some_and(|bound| tuple_count > bound) {
        return FrameworkIIRetainedCountermodel::FoundNotRetained { tuple_count };
    }
    let relations: Arc<[FrameworkIICountermodelRelation]> = relations
        .into_iter()
        .map(|(key, arity, rows)| FrameworkIICountermodelRelation {
            key,
            arity,
            rows: rows.into(),
        })
        .collect::<Vec<_>>()
        .into();
    FrameworkIIRetainedCountermodel::Retained(FrameworkIICountermodelInstance {
        relations,
        tuple_count,
    })
}

#[cfg(test)]
fn feedback_test_digest(label: &str, request_digest: &str) -> Arc<str> {
    Arc::from(canonical_value_sha256(&json!({
        "kind": label,
        "request_digest": request_digest,
    })))
}

#[cfg(test)]
fn feedback_test_artifact(
    artifacts: &ArtifactStore,
    kind: ArtifactKind,
    label: &str,
) -> ArtifactRef {
    artifacts
        .publish(kind, label.as_bytes().to_vec().into_boxed_slice())
        .expect("feedback route fixtures publish into an open artifact store")
}

#[cfg(test)]
fn feedback_test_invocation() -> SolverInvocationIdentity {
    SolverInvocationIdentity::from_parts(
        Arc::from("feedback-test-tool"),
        Arc::from("test-version"),
        Arc::from("/withheld/feedback-test-tool"),
        Arc::from("a".repeat(64)),
        Arc::from("test-platform"),
        Arc::from("test-architecture"),
        vec![Arc::from("SECRET_TEST_INVOCATION_ARGUMENT")],
    )
    .expect("the fixed feedback invocation identity is valid")
}

#[cfg(test)]
fn feedback_test_certification_profile(
    winner: ProofSearchProfile,
) -> LeancheckCertificationProfile {
    LeancheckCertificationProfile::new(
        winner,
        "feedback-test-profile",
        feedback_test_invocation(),
        None,
        "b".repeat(64),
        "c".repeat(64),
        "d".repeat(64),
        "e".repeat(64),
        "f".repeat(64),
    )
    .expect("the fixed feedback certification profile is valid")
}

#[cfg(test)]
impl RuntimeProofReceipt {
    pub(crate) fn feedback_test_fixture(
        request: &FrameworkIICheckRequest,
        artifacts: &ArtifactStore,
        winner: ProofSearchProfile,
    ) -> Self {
        let request_digest = request.request_digest();
        let query_artifact =
            feedback_test_artifact(artifacts, ArtifactKind::Query, "feedback query");
        let proof_artifact =
            feedback_test_artifact(artifacts, ArtifactKind::Proof, "feedback proof");
        let terminal_artifact = feedback_test_artifact(
            artifacts,
            ArtifactKind::RuntimeTrace,
            "hidden feedback terminal",
        );
        let empty_check_artifact = feedback_test_artifact(
            artifacts,
            ArtifactKind::EmptyInstanceCheck,
            "feedback empty check",
        );
        let receipt_artifact =
            feedback_test_artifact(artifacts, ArtifactKind::Witness, "feedback proof receipt");
        let task = request.snapshot().scope().task_identity();
        let task_digest = task_digest(task);
        Self {
            replay_capture: ReplayProductionCapture::NonReplayable(
                ReplayProductionError::UnsupportedSchema,
            ),
            replay_prepared: Err(ReplayProductionError::UnsupportedSchema),
            replay_terminal: None,
            task_digest,
            catalog_digest: Arc::from(request.snapshot().catalog_instance_digest()),
            artifact_backend_digest: Arc::from(canonical_value_sha256(&json!({
                "backend": artifacts.backend_id().to_string(),
            }))),
            semantic_version: task.semantic_version(),
            encoding_version: task.encoding_version(),
            framework_ii_context_digest: feedback_test_digest("context", request_digest),
            request_digest: Arc::from(request_digest),
            job_id: feedback_test_digest("job", request_digest),
            semantic_vc_digest: feedback_test_digest("semantic-vc", request_digest),
            query_digest: feedback_test_digest("query", request_digest),
            query_bytes: 14,
            attempt: artifacts
                .next_attempt_id()
                .expect("the feedback artifact store allocates an attempt"),
            terminal_result_digest: feedback_test_digest("terminal", request_digest),
            empty_check_digest: feedback_test_digest("empty", request_digest),
            winner,
            runtime_invocation: feedback_test_invocation(),
            certification_profile: feedback_test_certification_profile(winner),
            preparation_digest: feedback_test_digest("preparation", request_digest),
            query_artifact,
            proof_artifact,
            terminal_artifact,
            empty_check_artifact,
            receipt_artifact,
            receipt_digest: feedback_test_digest("proof-receipt", request_digest),
        }
    }
}

#[cfg(test)]
impl FrameworkIIEntailmentProgress {
    pub(crate) fn feedback_test_fixture(
        request: &FrameworkIICheckRequest,
        artifacts: &ArtifactStore,
        reason: FrameworkIIInconclusiveReason,
        peer_failure: Option<FailureReport>,
    ) -> Self {
        let request_digest = request.request_digest();
        Self {
            replay_capture: ReplayProductionCapture::NonReplayable(
                ReplayProductionError::UnsupportedSchema,
            ),
            replay_prepared: Err(ReplayProductionError::UnsupportedSchema),
            replay_terminal: None,
            request_digest: Arc::from(request_digest),
            job_id: feedback_test_digest("job", request_digest),
            semantic_vc_digest: feedback_test_digest("semantic-vc", request_digest),
            preparation_digest: feedback_test_digest("preparation", request_digest),
            reason,
            attempt: artifacts
                .next_attempt_id()
                .expect("the feedback artifact store allocates an attempt"),
            next_fmb_start_size: None,
            previous_proof_allowance: Duration::from_millis(10),
            current_proof_allowance: Duration::from_millis(20),
            peer_failure,
            terminal_artifact: feedback_test_artifact(
                artifacts,
                ArtifactKind::RuntimeTrace,
                "hidden feedback progress terminal",
            ),
            terminal_result_digest: feedback_test_digest("progress-terminal", request_digest),
            progress_artifact: feedback_test_artifact(
                artifacts,
                ArtifactKind::Witness,
                "feedback progress receipt",
            ),
            progress_digest: feedback_test_digest("progress", request_digest),
        }
    }
}

#[cfg(test)]
impl ValidatedFiniteRefutation {
    pub(crate) fn feedback_test_fixture(
        request: &FrameworkIICheckRequest,
        artifacts: &ArtifactStore,
    ) -> Self {
        let request_digest = request.request_digest();
        let validation_identity = json!({
            "kind": "feedback_test_empty_refutation_validation",
            "request_digest": request_digest,
        });
        Self {
            replay_capture: ReplayProductionCapture::NonReplayable(
                ReplayProductionError::UnsupportedSchema,
            ),
            replay_prepared: Err(ReplayProductionError::UnsupportedSchema),
            replay_terminal: None,
            request_digest: Arc::from(request_digest),
            job_id: feedback_test_digest("job", request_digest),
            semantic_vc_digest: feedback_test_digest("semantic-vc", request_digest),
            preparation_digest: feedback_test_digest("preparation", request_digest),
            attempt: artifacts
                .next_attempt_id()
                .expect("the feedback artifact store allocates an attempt"),
            terminal_artifact: feedback_test_artifact(
                artifacts,
                ArtifactKind::RuntimeTrace,
                "hidden feedback refutation terminal",
            ),
            terminal_result_digest: feedback_test_digest("refutation-terminal", request_digest),
            source_artifact: feedback_test_artifact(
                artifacts,
                ArtifactKind::EmptyInstanceCheck,
                "feedback refutation source",
            ),
            validation_digest: Arc::from(canonical_value_sha256(&validation_identity)),
            validation_identity: Arc::new(validation_identity),
            validation_artifact: feedback_test_artifact(
                artifacts,
                ArtifactKind::Witness,
                "feedback validation receipt",
            ),
            receipt_artifact: feedback_test_artifact(
                artifacts,
                ArtifactKind::Witness,
                "feedback refutation receipt",
            ),
            refutation_digest: feedback_test_digest("refutation", request_digest),
        }
    }
}

// ------------------------------------------------------------
// Validation Helpers
// ------------------------------------------------------------

fn fixed_ambient_job_fields(prepared: &PreparedFrameworkIIEntailment) -> Value {
    json!({
        "preparation_identity": prepared.prepare_request_identity(),
        "preparation_digest": prepared.prepare_request_digest(),
        "obligation_identity": prepared.base_obligation_identity(),
        "obligation_digest": prepared.base_obligation_digest(),
        "worker_entailment_identity": prepared.entailment_identity(),
        "job_id": prepared.job_id(),
        "empty_request_identity": prepared.empty_request_identity(),
        "empty_request_digest": prepared.empty_request_digest(),
        "entailment_identity": prepared.entailment().identity(),
        "query_artifact": artifact_fields(prepared.entailment().query_artifact()),
    })
}

/// Bind one Lean refutation identity to the exact prepared obligation by its
/// source: the empty-domain check or a validated nonempty finite model.
fn validate_fixed_ambient_refutation_identity(
    prepared: &PreparedFrameworkIIEntailment,
    validation_identity: &Value,
    source_kind: ArtifactKind,
) -> Result<(), FrameworkIIStateError> {
    match source_kind {
        ArtifactKind::EmptyInstanceCheck => validate_fixed_ambient_empty_check_identity(
            prepared,
            validation_identity,
            "counterexample",
        ),
        ArtifactKind::Model => {
            validate_fixed_ambient_model_validation_identity(prepared, validation_identity)
        }
        _ => Err(FrameworkIIStateError::InvalidEvidence(
            "a fixed-ambient refutation source is neither an empty check nor a finite model",
        )),
    }
}

/// The Lean finite-model validation identity must bind the exact obligation
/// and record a genuine refutation decision.
fn validate_fixed_ambient_model_validation_identity(
    prepared: &PreparedFrameworkIIEntailment,
    validation_identity: &Value,
) -> Result<(), FrameworkIIStateError> {
    let Some(fields) = validation_identity.as_object() else {
        return Err(FrameworkIIStateError::InvalidEvidence(
            "the fixed-ambient finite-model validation identity is not structural",
        ));
    };
    if fields.len() != 7
        || fields.get("kind").and_then(Value::as_str)
            != Some("whiel_framework_ii_base_refutation_validation")
        || fields.get("version").and_then(Value::as_u64) != Some(1)
        || fields.get("obligation_identity") != Some(prepared.base_obligation_identity())
        || fields.get("axioms_hold") != Some(&Value::Bool(true))
        || fields.get("conjecture_holds") != Some(&Value::Bool(false))
        || fields.get("validated_refutation") != Some(&Value::Bool(true))
        || !fields
            .get("interpretation_identity")
            .is_some_and(Value::is_object)
    {
        return Err(FrameworkIIStateError::InvalidEvidence(
            "the fixed-ambient finite-model validation lost its exact obligation binding",
        ));
    }
    Ok(())
}

fn validate_fixed_ambient_empty_check_identity(
    prepared: &PreparedFrameworkIIEntailment,
    check_identity: &Value,
    expected_result_kind: &str,
) -> Result<(), FrameworkIIStateError> {
    let Some(fields) = check_identity.as_object() else {
        return Err(FrameworkIIStateError::InvalidEvidence(
            "the fixed-ambient empty-check identity is not structural",
        ));
    };
    let result_kind = fields
        .get("result")
        .and_then(Value::as_object)
        .and_then(|result| result.get("kind"))
        .and_then(Value::as_str);
    if fields.len() != 7
        || fields.get("kind").and_then(Value::as_str)
            != Some("whiel_fixed_ambient_empty_counterexample_check")
        || fields.get("version").and_then(Value::as_u64)
            != Some(FIXED_AMBIENT_EMPTY_CHECK_IDENTITY_VERSION)
        || fields.get("decision_definition").and_then(Value::as_str)
            != Some("QFEntailment.adomEmptyCounterexample?")
        || fields.get("empty_request_identity") != Some(prepared.empty_request_identity())
        || fields.get("obligation_identity") != Some(prepared.base_obligation_identity())
        || fields.get("worker_entailment_identity") != Some(prepared.entailment_identity())
        || result_kind != Some(expected_result_kind)
    {
        return Err(FrameworkIIStateError::InvalidEvidence(
            "the fixed-ambient empty-check result lost its full prepared-obligation binding",
        ));
    }
    Ok(())
}

fn validate_proof_bindings(
    prepared: &PreparedFrameworkIIEntailment,
    attempt: &EntailmentAttemptScope,
    proof: &VampireProof,
    empty: &FrameworkIIEmptyCheckEvidence,
    artifacts: &ArtifactStore,
) -> Result<(), FrameworkIIStateError> {
    validate_fixed_ambient_empty_check_identity(
        prepared,
        empty.check_identity(),
        "no_counterexample",
    )?;
    if proof.problem_identity() != prepared.entailment().identity()
        || proof.attempt_id() != attempt.attempt_id()
        || proof.query_artifact() != Some(prepared.entailment().query_artifact())
        || empty.request_digest() != prepared.empty_request_digest()
        || empty.obligation_digest() != prepared.base_obligation_digest()
        || proof.output().backend_id() != artifacts.backend_id()
        || empty.artifact().backend_id() != artifacts.backend_id()
        || proof.output().kind() != ArtifactKind::Proof
        || empty.artifact().kind() != ArtifactKind::EmptyInstanceCheck
    {
        return Err(FrameworkIIStateError::InvalidEvidence(
            "the proof, empty check, query, attempt, and backend bindings disagree",
        ));
    }
    require_sha256("empty-instance check", empty.check_digest())
}

fn validate_proof_source(
    prepared: &PreparedFrameworkIIEntailment,
    attempt: &EntailmentAttemptScope,
    proof: &VampireProof,
) -> Result<(), FrameworkIIStateError> {
    if proof.problem_identity() != prepared.entailment().identity()
        || proof.attempt_id() != attempt.attempt_id()
        || proof.query_artifact() != Some(prepared.entailment().query_artifact())
        || proof.output().backend_id() != attempt.artifacts().backend_id()
        || proof.output().kind() != ArtifactKind::Proof
    {
        return Err(FrameworkIIStateError::InvalidEvidence(
            "the Vampire proof changed its entailment, query, attempt, backend, or artifact kind",
        ));
    }
    Ok(())
}

fn validate_model_bindings(
    prepared: &PreparedFrameworkIIEntailment,
    attempt: &EntailmentAttemptScope,
    model: &VampireModel,
) -> Result<(), FrameworkIIStateError> {
    if model.problem_identity() != prepared.entailment().identity()
        || model.attempt_id() != attempt.attempt_id()
        || model.query_artifact() != Some(prepared.entailment().query_artifact())
        || model.output().backend_id() != attempt.artifacts().backend_id()
        || model.output().kind() != ArtifactKind::Model
    {
        return Err(FrameworkIIStateError::InvalidEvidence(
            "the Vampire model changed its entailment, query, attempt, backend, or artifact kind",
        ));
    }
    Ok(())
}

fn validate_refutation_evidence(
    prepared: &PreparedFrameworkIIEntailment,
    attempt: &EntailmentAttemptScope,
    evidence: &FrameworkIIValidatedRefutationEvidence,
    expected_source: ArtifactRef,
    expected_source_kind: ArtifactKind,
) -> Result<(), FrameworkIIStateError> {
    validate_fixed_ambient_refutation_identity(
        prepared,
        &evidence.validation_identity,
        expected_source_kind,
    )?;
    if evidence.source_artifact != expected_source
        || evidence.source_artifact.kind() != expected_source_kind
        || evidence.source_artifact.backend_id() != attempt.artifacts().backend_id()
        || evidence.validation_artifact.kind() != ArtifactKind::Witness
        || evidence.validation_artifact.backend_id() != attempt.artifacts().backend_id()
    {
        return Err(FrameworkIIStateError::InvalidEvidence(
            "the finite-refutation source or Lean validation artifact changed its exact binding",
        ));
    }
    require_sha256("finite-refutation validation", &evidence.validation_digest)?;
    if canonical_value_sha256(&evidence.validation_identity) != evidence.validation_digest.as_ref()
    {
        return Err(FrameworkIIStateError::InvalidEvidence(
            "the finite-refutation validation digest does not bind its full identity",
        ));
    }
    Ok(())
}

fn task_digest(task: &TaskIdentity) -> Arc<str> {
    Arc::from(replay_task_digest(&task_identity_fields_from_task(task)))
}

fn task_identity_fields_from_task(task: &TaskIdentity) -> Value {
    // One renderer, shared with the fixed-ambient snapshot identity and the
    // acceptance envelope, so the three cannot drift apart.
    super::catalog::task_identity_fields_of(task)
}

fn digest_file(path: &Path) -> Result<(Arc<str>, u64), FrameworkIIStateError> {
    let mut file = File::open(path).map_err(|error| {
        checker_failure(format!("open receipt input {}: {error}", path.display()))
    })?;
    let mut digest = Sha256::new();
    let mut buffer = [0_u8; 64 * 1024];
    let mut length = 0_u64;
    loop {
        let read = file.read(&mut buffer).map_err(|error| {
            checker_failure(format!("read receipt input {}: {error}", path.display()))
        })?;
        if read == 0 {
            break;
        }
        length = length
            .checked_add(read as u64)
            .ok_or_else(|| checker_failure("receipt input length overflowed u64".to_string()))?;
        digest.update(&buffer[..read]);
    }
    Ok((Arc::from(digest.finalize_hex()), length))
}

fn artifact_fields(reference: ArtifactRef) -> Value {
    json!({
        "backend": reference.backend_id().to_string(),
        "local_id": reference.local_id(),
        "kind": format!("{:?}", reference.kind()),
    })
}

fn replay_failure_fields(
    origin: &impl serde::Serialize,
    kind: &impl serde::Serialize,
    retryable: bool,
    scope: &impl serde::Serialize,
    detail: Option<&str>,
    artifacts: &impl serde::Serialize,
) -> Value {
    json!({"origin":origin,"kind":kind,"retryable":retryable,"scope":scope,"detail":detail,"artifacts":artifacts})
}

fn failure_fields(report: &FailureReport) -> Value {
    replay_failure_fields(
        &format!("{:?}", report.origin()),
        &format!("{:?}", report.kind()),
        report.retryable(),
        &format!("{:?}", report.scope()),
        report.detail(),
        &report
            .artifact_references()
            .iter()
            .map(|reference| artifact_fields(*reference))
            .collect::<Vec<_>>(),
    )
}

fn inconclusive_name(reason: FrameworkIIInconclusiveReason) -> &'static str {
    match reason {
        FrameworkIIInconclusiveReason::TimedOut => "timed_out",
        FrameworkIIInconclusiveReason::SolverUnknown => "solver_unknown",
        FrameworkIIInconclusiveReason::PeerFailed => "peer_failed",
        FrameworkIIInconclusiveReason::UnvalidatedRefutation => "unvalidated_refutation",
        FrameworkIIInconclusiveReason::Cancelled => "cancelled",
        FrameworkIIInconclusiveReason::Suspended => "suspended",
    }
}

fn path_text(path: &Path, name: &'static str) -> Result<Arc<str>, FrameworkIIStateError> {
    path.to_str()
        .map(Arc::from)
        .ok_or(FrameworkIIStateError::InvalidEvidence(match name {
            "runtime Vampire executable" => "the resolved runtime Vampire path is not valid UTF-8",
            _ => "a receipt path is not valid UTF-8",
        }))
}

fn require_sha256(name: &'static str, value: &str) -> Result<(), FrameworkIIStateError> {
    if is_sha256(value) {
        Ok(())
    } else {
        Err(FrameworkIIStateError::InvalidEvidence(match name {
            "fixed-ambient obligation" => {
                "the fixed-ambient obligation digest is not lowercase SHA-256"
            }
            "empty-check request" => "the empty-check request digest is not lowercase SHA-256",
            "terminal result" => "the terminal-result digest is not lowercase SHA-256",
            "empty-instance check" => "the empty-check digest is not lowercase SHA-256",
            "finite-refutation validation" => {
                "the refutation-validation digest is not lowercase SHA-256"
            }
            _ => "a required receipt digest is not lowercase SHA-256",
        }))
    }
}

fn is_sha256(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn state_as_failure(error: FrameworkIIStateError) -> FailureReport {
    FailureReport::encoding_preparation(
        FailureKind::InfrastructureFailure,
        FailureScope::RunGlobal,
        error.to_string(),
    )
}

fn checker_failure(detail: String) -> FrameworkIIStateError {
    FrameworkIIStateError::CheckerFailure(Arc::from(detail))
}

// ------------------------------------------------------------
// Owner-Only Replay Identity Projections
// ------------------------------------------------------------
// Strict owner projections retain constructor inputs without granting replay authority.

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum ReplayProductionError {
    UnsupportedSchema,
    PrivateDetailRedacted,
    PrivateDetailMismatch,
    ConstructorDigestMismatch,
    NestedBindingMismatch,
}

fn replay_nullable<'de, D, T>(deserializer: D) -> Result<Option<T>, D::Error>
where
    D: serde::Deserializer<'de>,
    T: serde::Deserialize<'de>,
{
    <Option<T> as serde::Deserialize>::deserialize(deserializer)
}

macro_rules! replay_literal {
    ($name:ident, $literal:literal) => {
        #[derive(Clone, Debug, PartialEq, Eq)]
        pub(super) struct $name;
        impl serde::Serialize for $name {
            fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
                s.serialize_str($literal)
            }
        }
        impl<'de> serde::Deserialize<'de> for $name {
            fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
                let value = <String as serde::Deserialize>::deserialize(d)?;
                if value == $literal {
                    Ok(Self)
                } else {
                    Err(serde::de::Error::custom("unsupported identity literal"))
                }
            }
        }
    };
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct ReplayVersion<const VERSION: u64>;
impl<const V: u64> serde::Serialize for ReplayVersion<V> {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.serialize_u64(V)
    }
}
impl<'de, const V: u64> serde::Deserialize<'de> for ReplayVersion<V> {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        if <u64 as serde::Deserialize>::deserialize(d)? == V {
            Ok(Self)
        } else {
            Err(serde::de::Error::custom("unsupported identity version"))
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
#[serde(transparent)]
pub(crate) struct ReplaySha256(pub(crate) String);
impl<'de> serde::Deserialize<'de> for ReplaySha256 {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let value = <String as serde::Deserialize>::deserialize(d)?;
        if value.len() == 64
            && value
                .bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
        {
            Ok(Self(value))
        } else {
            Err(serde::de::Error::custom("invalid lowercase SHA-256"))
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
#[serde(transparent)]
pub(super) struct ReplayNatText(pub(super) String);
impl<'de> serde::Deserialize<'de> for ReplayNatText {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let v = <String as serde::Deserialize>::deserialize(d)?;
        if v == "0"
            || (!v.starts_with('0') && !v.is_empty() && v.bytes().all(|b| b.is_ascii_digit()))
        {
            Ok(Self(v))
        } else {
            Err(serde::de::Error::custom("noncanonical natural text"))
        }
    }
}

replay_literal!(ReplayScopeTag, "whiel-framework-ii-fixed-ambient-scope-v1");

replay_literal!(ReplayClauseTag, "whiel_fixed_ambient_clause");

replay_literal!(ReplayQfTag, "whiel_qf_formula");

replay_literal!(ReplaySnapshotTag, "whiel_fixed_ambient_snapshot");

replay_literal!(ReplayObligationTag, "whiel_fixed_ambient_obligation");

replay_literal!(ReplayJobTag, "whiel_fixed_ambient_validity_job");

replay_literal!(
    ReplayEmptyRequestTag,
    "whiel_fixed_ambient_empty_counterexample_request"
);

replay_literal!(
    ReplayPreparationTag,
    "whiel_fixed_ambient_obligation_preparation"
);

replay_literal!(
    ReplayEmptyCheckTag,
    "whiel_fixed_ambient_empty_counterexample_check"
);

replay_literal!(
    ReplayEmptyDefinition,
    "QFEntailment.adomEmptyCounterexample?"
);

replay_literal!(
    ReplayValidationTag,
    "whiel_framework_ii_base_refutation_validation"
);

replay_literal!(
    ReplayInterpretationTag,
    "whiel_framework_ii_finite_interpretation"
);

replay_literal!(ReplayCarrierTag, "whiel_framework_ii_finite_carrier");

replay_literal!(ReplayInstanceTag, "whiel_source_instance");

replay_literal!(
    ReplayRuntimeProofDomain,
    "whiel-framework-ii-runtime-proof-receipt-v3"
);

replay_literal!(
    ReplayProtectedDomain,
    "whiel-framework-ii-protected-theorem-selection-v3"
);

replay_literal!(
    ReplayProgressDomain,
    "whiel-framework-ii-entailment-progress-v3"
);

replay_literal!(
    ReplayRefutationDomain,
    "whiel-framework-ii-validated-finite-refutation-v4"
);

replay_literal!(ReplayReuseTag, "whiel_framework_ii_semantic_reuse");

replay_literal!(ReplaySemanticKeyTag, "whiel_framework_ii_semantic_vc_key");

replay_literal!(ReplayTerminationConjecture, "post_prime");

fn replay_array(value: Value, tag: &str, length: usize) -> Result<Vec<Value>, String> {
    let Value::Array(mut items) = value else {
        return Err("identity must be an array".into());
    };
    if items.len() != length || items.first().and_then(Value::as_str) != Some(tag) {
        return Err("unsupported structural tag or arity".into());
    }
    items.remove(0);
    Ok(items)
}
fn replay_element<T: serde::de::DeserializeOwned>(value: Value) -> Result<T, String> {
    serde_json::from_value(value).map_err(|_| "invalid typed structural operand".into())
}
macro_rules! replay_array_serde {
    ($name:ident) => {
        impl serde::Serialize for $name {
            fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
                serde::Serialize::serialize(&self.identity_fields(), s)
            }
        }
        impl<'de> serde::Deserialize<'de> for $name {
            fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
                let value = <Value as serde::Deserialize>::deserialize(d)?;
                Self::decode_identity(value).map_err(serde::de::Error::custom)
            }
        }
    };
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum ReplayNatList {
    Nil,
    Cons(ReplayNatText, Box<ReplayNatList>),
}

impl ReplayNatList {
    fn identity_fields(&self) -> Value {
        match self {
            Self::Nil => json!(["nil"]),
            Self::Cons(v0, v1) => json!(["cons", v0, v1]),
        }
    }
    fn decode_identity(value: Value) -> Result<Self, String> {
        let tag = value
            .as_array()
            .and_then(|v| v.first())
            .and_then(Value::as_str)
            .ok_or("missing structural tag")?
            .to_owned();
        match tag.as_str() {
            "nil" => {
                let mut fields = replay_array(value, "nil", 1)?.into_iter();
                let _ = &mut fields;
                Ok(Self::Nil)
            }
            "cons" => {
                let mut fields = replay_array(value, "cons", 3)?.into_iter();
                Ok(Self::Cons(
                    replay_element(fields.next().ok_or("missing operand")?)?,
                    replay_element(fields.next().ok_or("missing operand")?)?,
                ))
            }
            _ => Err("unknown structural variant".into()),
        }
    }
}
replay_array_serde!(ReplayNatList);

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum ReplaySelection {
    EqIndex(ReplayNatText, ReplayNatText),
    EqConstant(ReplayNatText, String),
    And(Box<ReplaySelection>, Box<ReplaySelection>),
    Or(Box<ReplaySelection>, Box<ReplaySelection>),
    Not(Box<ReplaySelection>),
}

impl ReplaySelection {
    fn identity_fields(&self) -> Value {
        match self {
            Self::EqIndex(v0, v1) => json!(["eq_idx", v0, v1]),
            Self::EqConstant(v0, v1) => json!(["eq_const", v0, v1]),
            Self::And(v0, v1) => json!(["and", v0, v1]),
            Self::Or(v0, v1) => json!(["or", v0, v1]),
            Self::Not(v0) => json!(["not", v0]),
        }
    }
    fn decode_identity(value: Value) -> Result<Self, String> {
        let tag = value
            .as_array()
            .and_then(|v| v.first())
            .and_then(Value::as_str)
            .ok_or("missing structural tag")?
            .to_owned();
        match tag.as_str() {
            "eq_idx" => {
                let mut fields = replay_array(value, "eq_idx", 3)?.into_iter();
                Ok(Self::EqIndex(
                    replay_element(fields.next().ok_or("missing operand")?)?,
                    replay_element(fields.next().ok_or("missing operand")?)?,
                ))
            }
            "eq_const" => {
                let mut fields = replay_array(value, "eq_const", 3)?.into_iter();
                Ok(Self::EqConstant(
                    replay_element(fields.next().ok_or("missing operand")?)?,
                    replay_element(fields.next().ok_or("missing operand")?)?,
                ))
            }
            "and" => {
                let mut fields = replay_array(value, "and", 3)?.into_iter();
                Ok(Self::And(
                    replay_element(fields.next().ok_or("missing operand")?)?,
                    replay_element(fields.next().ok_or("missing operand")?)?,
                ))
            }
            "or" => {
                let mut fields = replay_array(value, "or", 3)?.into_iter();
                Ok(Self::Or(
                    replay_element(fields.next().ok_or("missing operand")?)?,
                    replay_element(fields.next().ok_or("missing operand")?)?,
                ))
            }
            "not" => {
                let mut fields = replay_array(value, "not", 2)?.into_iter();
                Ok(Self::Not(replay_element(
                    fields.next().ok_or("missing operand")?,
                )?))
            }
            _ => Err("unknown structural variant".into()),
        }
    }
}
replay_array_serde!(ReplaySelection);

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum ReplayExpression {
    Top,
    Empty(ReplayNatText),
    Relation(String),
    Single(String),
    Select(ReplaySelection, Box<ReplayExpression>),
    Project(ReplayNatList, Box<ReplayExpression>),
    Product(Box<ReplayExpression>, Box<ReplayExpression>),
    Union(Box<ReplayExpression>, Box<ReplayExpression>),
    Difference(Box<ReplayExpression>, Box<ReplayExpression>),
}

impl ReplayExpression {
    fn identity_fields(&self) -> Value {
        match self {
            Self::Top => json!(["top"]),
            Self::Empty(v0) => json!(["empty", v0]),
            Self::Relation(v0) => json!(["rel", v0]),
            Self::Single(v0) => json!(["single", v0]),
            Self::Select(v0, v1) => json!(["select", v0, v1]),
            Self::Project(v0, v1) => json!(["proj", v0, v1]),
            Self::Product(v0, v1) => json!(["prod", v0, v1]),
            Self::Union(v0, v1) => json!(["union", v0, v1]),
            Self::Difference(v0, v1) => json!(["diff", v0, v1]),
        }
    }
    fn decode_identity(value: Value) -> Result<Self, String> {
        let tag = value
            .as_array()
            .and_then(|v| v.first())
            .and_then(Value::as_str)
            .ok_or("missing structural tag")?
            .to_owned();
        match tag.as_str() {
            "top" => {
                let mut fields = replay_array(value, "top", 1)?.into_iter();
                let _ = &mut fields;
                Ok(Self::Top)
            }
            "empty" => {
                let mut fields = replay_array(value, "empty", 2)?.into_iter();
                Ok(Self::Empty(replay_element(
                    fields.next().ok_or("missing operand")?,
                )?))
            }
            "rel" => {
                let mut fields = replay_array(value, "rel", 2)?.into_iter();
                Ok(Self::Relation(replay_element(
                    fields.next().ok_or("missing operand")?,
                )?))
            }
            "single" => {
                let mut fields = replay_array(value, "single", 2)?.into_iter();
                Ok(Self::Single(replay_element(
                    fields.next().ok_or("missing operand")?,
                )?))
            }
            "select" => {
                let mut fields = replay_array(value, "select", 3)?.into_iter();
                Ok(Self::Select(
                    replay_element(fields.next().ok_or("missing operand")?)?,
                    replay_element(fields.next().ok_or("missing operand")?)?,
                ))
            }
            "proj" => {
                let mut fields = replay_array(value, "proj", 3)?.into_iter();
                Ok(Self::Project(
                    replay_element(fields.next().ok_or("missing operand")?)?,
                    replay_element(fields.next().ok_or("missing operand")?)?,
                ))
            }
            "prod" => {
                let mut fields = replay_array(value, "prod", 3)?.into_iter();
                Ok(Self::Product(
                    replay_element(fields.next().ok_or("missing operand")?)?,
                    replay_element(fields.next().ok_or("missing operand")?)?,
                ))
            }
            "union" => {
                let mut fields = replay_array(value, "union", 3)?.into_iter();
                Ok(Self::Union(
                    replay_element(fields.next().ok_or("missing operand")?)?,
                    replay_element(fields.next().ok_or("missing operand")?)?,
                ))
            }
            "diff" => {
                let mut fields = replay_array(value, "diff", 3)?.into_iter();
                Ok(Self::Difference(
                    replay_element(fields.next().ok_or("missing operand")?)?,
                    replay_element(fields.next().ok_or("missing operand")?)?,
                ))
            }
            _ => Err("unknown structural variant".into()),
        }
    }
}
replay_array_serde!(ReplayExpression);

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum ReplayGuard {
    True,
    False,
    Equal(ReplayExpression, ReplayExpression),
    Subset(ReplayExpression, ReplayExpression),
    EqualEmptyRight(ReplayExpression),
    EqualEmptyLeft(ReplayExpression),
    SubsetEmptyRight(ReplayExpression),
    SubsetEmptyLeft(ReplayExpression),
    And(Box<ReplayGuard>, Box<ReplayGuard>),
    Or(Box<ReplayGuard>, Box<ReplayGuard>),
    Not(Box<ReplayGuard>),
}

impl ReplayGuard {
    fn identity_fields(&self) -> Value {
        match self {
            Self::True => json!(["true"]),
            Self::False => json!(["false"]),
            Self::Equal(v0, v1) => json!(["eq", v0, v1]),
            Self::Subset(v0, v1) => json!(["subset", v0, v1]),
            Self::EqualEmptyRight(v0) => json!(["eq_empty_right", v0]),
            Self::EqualEmptyLeft(v0) => json!(["eq_empty_left", v0]),
            Self::SubsetEmptyRight(v0) => json!(["subset_empty_right", v0]),
            Self::SubsetEmptyLeft(v0) => json!(["subset_empty_left", v0]),
            Self::And(v0, v1) => json!(["and", v0, v1]),
            Self::Or(v0, v1) => json!(["or", v0, v1]),
            Self::Not(v0) => json!(["not", v0]),
        }
    }
    fn decode_identity(value: Value) -> Result<Self, String> {
        let tag = value
            .as_array()
            .and_then(|v| v.first())
            .and_then(Value::as_str)
            .ok_or("missing structural tag")?
            .to_owned();
        match tag.as_str() {
            "true" => {
                let mut fields = replay_array(value, "true", 1)?.into_iter();
                let _ = &mut fields;
                Ok(Self::True)
            }
            "false" => {
                let mut fields = replay_array(value, "false", 1)?.into_iter();
                let _ = &mut fields;
                Ok(Self::False)
            }
            "eq" => {
                let mut fields = replay_array(value, "eq", 3)?.into_iter();
                Ok(Self::Equal(
                    replay_element(fields.next().ok_or("missing operand")?)?,
                    replay_element(fields.next().ok_or("missing operand")?)?,
                ))
            }
            "subset" => {
                let mut fields = replay_array(value, "subset", 3)?.into_iter();
                Ok(Self::Subset(
                    replay_element(fields.next().ok_or("missing operand")?)?,
                    replay_element(fields.next().ok_or("missing operand")?)?,
                ))
            }
            "eq_empty_right" => {
                let mut fields = replay_array(value, "eq_empty_right", 2)?.into_iter();
                Ok(Self::EqualEmptyRight(replay_element(
                    fields.next().ok_or("missing operand")?,
                )?))
            }
            "eq_empty_left" => {
                let mut fields = replay_array(value, "eq_empty_left", 2)?.into_iter();
                Ok(Self::EqualEmptyLeft(replay_element(
                    fields.next().ok_or("missing operand")?,
                )?))
            }
            "subset_empty_right" => {
                let mut fields = replay_array(value, "subset_empty_right", 2)?.into_iter();
                Ok(Self::SubsetEmptyRight(replay_element(
                    fields.next().ok_or("missing operand")?,
                )?))
            }
            "subset_empty_left" => {
                let mut fields = replay_array(value, "subset_empty_left", 2)?.into_iter();
                Ok(Self::SubsetEmptyLeft(replay_element(
                    fields.next().ok_or("missing operand")?,
                )?))
            }
            "and" => {
                let mut fields = replay_array(value, "and", 3)?.into_iter();
                Ok(Self::And(
                    replay_element(fields.next().ok_or("missing operand")?)?,
                    replay_element(fields.next().ok_or("missing operand")?)?,
                ))
            }
            "or" => {
                let mut fields = replay_array(value, "or", 3)?.into_iter();
                Ok(Self::Or(
                    replay_element(fields.next().ok_or("missing operand")?)?,
                    replay_element(fields.next().ok_or("missing operand")?)?,
                ))
            }
            "not" => {
                let mut fields = replay_array(value, "not", 2)?.into_iter();
                Ok(Self::Not(replay_element(
                    fields.next().ok_or("missing operand")?,
                )?))
            }
            _ => Err("unknown structural variant".into()),
        }
    }
}
replay_array_serde!(ReplayGuard);

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(super) struct ReplayAmbientScopeIdentity(
    pub(super) ReplayScopeTag,
    pub(super) Vec<(String, u64)>,
    pub(super) Vec<(String, String, u64)>,
);
replay_literal!(ReplayTaskScopeTag, "whiel_framework_ii_fixed_ambient_task");
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayScopeIdentity {
    pub(super) kind: ReplayTaskScopeTag,
    pub(super) version: ReplayVersion<2>,
    pub(super) semantic_version: u64,
    pub(super) encoding_version: u64,
    pub(super) task_canonical_id: String,
    pub(super) task_module: String,
    pub(super) task_namespace: String,
    pub(super) task_source_sha256: ReplaySha256,
    pub(super) ambient_scope: ReplayAmbientScopeIdentity,
}
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub(super) enum ReplaySelector {
    Initialization { clause_id: u64 },
    Maintenance { clause_id: u64 },
    Termination {},
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayClauseIdentity {
    pub(super) kind: ReplayClauseTag,
    pub(super) version: ReplayVersion<1>,
    pub(super) formula: ReplayGuard,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayQfIdentity {
    pub(super) kind: ReplayQfTag,
    pub(super) version: ReplayVersion<3>,
    pub(super) formula: ReplayGuard,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplaySnapshotRow {
    pub(super) clause_id: u64,
    pub(super) level: u64,
    pub(super) identity: ReplayClauseIdentity,
    pub(super) canonical_source: String,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplaySnapshotIdentity {
    pub(super) kind: ReplaySnapshotTag,
    pub(super) version: ReplayVersion<1>,
    pub(super) rows: Vec<ReplaySnapshotRow>,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayWorkerEntailmentIdentity {
    pub(super) axioms: Vec<ReplayQfIdentity>,
    pub(super) conjecture: ReplayQfIdentity,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayObligationIdentity {
    pub(super) kind: ReplayObligationTag,
    pub(super) version: ReplayVersion<1>,
    pub(super) scope_identity: ReplayScopeIdentity,
    pub(super) snapshot: ReplaySnapshotIdentity,
    pub(super) selector: ReplaySelector,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayJobIdentity {
    pub(super) kind: ReplayJobTag,
    pub(super) version: ReplayVersion<1>,
    pub(super) obligation_identity: ReplayObligationIdentity,
    pub(super) worker_entailment_identity: ReplayWorkerEntailmentIdentity,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayEmptyRequestIdentity {
    pub(super) kind: ReplayEmptyRequestTag,
    pub(super) version: ReplayVersion<1>,
    pub(super) scope_identity: ReplayScopeIdentity,
    pub(super) obligation_identity: ReplayObligationIdentity,
    pub(super) worker_entailment_identity: ReplayWorkerEntailmentIdentity,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
#[serde(transparent)]
pub(super) struct ReplayEntailmentIdentity(pub(super) String);
impl<'de> serde::Deserialize<'de> for ReplayEntailmentIdentity {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let value = <String as serde::Deserialize>::deserialize(d)?;
        let Some(hash) = value.strip_prefix("whiel-fixed-ambient-entailment-v1:sha256:") else {
            return Err(serde::de::Error::custom("unsupported entailment identity"));
        };
        if hash.len() != 64
            || !hash
                .bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
        {
            return Err(serde::de::Error::custom("invalid entailment digest"));
        }
        Ok(Self(value))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayPreparationIdentity {
    pub(super) kind: ReplayPreparationTag,
    pub(super) version: ReplayVersion<1>,
    pub(super) scope_identity: ReplayScopeIdentity,
    pub(super) obligation_identity: ReplayObligationIdentity,
    pub(super) worker_entailment_identity: ReplayWorkerEntailmentIdentity,
    pub(super) job_id: ReplaySha256,
    pub(super) empty_request_identity: ReplayEmptyRequestIdentity,
    pub(super) empty_request_digest: ReplaySha256,
    pub(super) entailment_identity: ReplayEntailmentIdentity,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) enum ReplayArtifactKind {
    Query,
    Proof,
    Model,
    EmptyInstanceCheck,
    InitializationCheck,
    Certificate,
    AcceptanceRecord,
    Witness,
    FailureDiagnostic,
    RuntimeTrace,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) enum ReplayFailureScope {
    LaneLocal,
    RunGlobal,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) enum ReplayFailureOrigin {
    RunControl,
    ArtifactSettlement,
    AgentConsultation,
    ResponseValidation,
    EncodingPreparation,
    InitializationExecution,
    VampireProofSearch,
    VampireFiniteModelBuilding,
    VampireRace,
    SymbolicRace,
    ModelDecoding,
    TerminationCheck,
    MaintenanceExecution,
    MaintenanceHistory,
    ValidityCertification,
    InvalidityCertification,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) enum ReplayFailureKind {
    OverallTimeout,
    Interrupted,
    ConsultationTimeout,
    IterationLimitExhausted,
    SourceExhausted,
    CorrectionExhausted,
    NoResponse,
    TransportFailure,
    ValidationInfrastructureFailure,
    UnsupportedCheck,
    FuelExhausted,
    CheckTimeout,
    SolverUnknown,
    MalformedResult,
    ProcessFailure,
    InfrastructureFailure,
    ConcurrentWorkerFailures,
    CertificateConstructionFailure,
    CertificateRejected,
    CertificateTypecheckFailure,
    ManifestFailure,
    PublicationFailure,
    HistoryLogFailure,
    StateInvariantViolation,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct ReplayArtifactIdentity {
    pub(crate) backend: ReplayBackendIdentity,
    pub(crate) local_id: u64,
    pub(crate) kind: ReplayArtifactKind,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayFixedAmbientJobFields {
    pub(super) preparation_identity: ReplayPreparationIdentity,
    pub(super) preparation_digest: ReplaySha256,
    pub(super) obligation_identity: ReplayObligationIdentity,
    pub(super) obligation_digest: ReplaySha256,
    pub(super) worker_entailment_identity: ReplayWorkerEntailmentIdentity,
    pub(super) job_id: ReplaySha256,
    pub(super) empty_request_identity: ReplayEmptyRequestIdentity,
    pub(super) empty_request_digest: ReplaySha256,
    pub(super) entailment_identity: ReplayEntailmentIdentity,
    pub(super) query_artifact: ReplayArtifactIdentity,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct ReplayPrivateFailure {
    pub(crate) origin: ReplayFailureOrigin,
    pub(crate) kind: ReplayFailureKind,
    pub(crate) retryable: bool,
    pub(crate) scope: ReplayFailureScope,
    #[serde(deserialize_with = "replay_nullable")]
    pub(crate) detail_digest: Option<ReplaySha256>,
    pub(crate) artifacts: Vec<ReplayArtifactIdentity>,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplaySolverInvocation {
    pub(super) tool: String,
    pub(super) version: String,
    pub(super) resolved_path: String,
    pub(super) binary_digest: ReplaySha256,
    pub(super) platform: String,
    pub(super) architecture: String,
    pub(super) arguments: Vec<String>,
    pub(super) identity_digest: ReplaySha256,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(super) enum ReplayProofProfile {
    #[serde(rename = "direct")]
    Direct,
    #[serde(rename = "casc_2025")]
    Casc2025,
}
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "snake_case")]
pub(super) enum ReplayInconclusiveReason {
    TimedOut,
    SolverUnknown,
    PeerFailed,
    UnvalidatedRefutation,
    Cancelled,
    Suspended,
}
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(tag = "kind", deny_unknown_fields)]
pub(super) enum ReplayProtectedRule {
    #[serde(rename = "edb_precondition_initialization")]
    Initialization {
        source_conjunct: ReplaySha256,
        target_clause: u64,
        target_context: ReplaySha256,
    },
    #[serde(rename = "edb_precondition_maintenance")]
    Maintenance {
        source_conjunct: ReplaySha256,
        unchanged_relations: ReplaySha256,
        target_clause: u64,
        target_context: ReplaySha256,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayCertificationProfile {
    pub(super) profile: ReplayProofProfile,
    pub(super) profile_version: String,
    pub(super) leancheck_invocation: ReplaySolverInvocation,
    #[serde(deserialize_with = "replay_nullable")]
    pub(super) permitted_cadical: Option<ReplaySolverInvocation>,
    pub(super) vamplean_digest: ReplaySha256,
    pub(super) generator_digest: ReplaySha256,
    pub(super) output_contract_digest: ReplaySha256,
    pub(super) transformer_digest: ReplaySha256,
    pub(super) lean_bridge_digest: ReplaySha256,
    pub(super) profile_digest: ReplaySha256,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayCarrierIdentity {
    pub(super) kind: ReplayCarrierTag,
    pub(super) version: ReplayVersion<1>,
    pub(super) carrier_keys: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayRelationSchema {
    pub(super) key: String,
    pub(super) arity: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayInstanceRelation {
    pub(super) key: String,
    pub(super) arity: u64,
    pub(super) rows: Vec<Vec<String>>,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayInstanceIdentity {
    pub(super) kind: ReplayInstanceTag,
    pub(super) version: ReplayVersion<1>,
    pub(super) relations: Vec<ReplayInstanceRelation>,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayInterpretationIdentity {
    pub(super) kind: ReplayInterpretationTag,
    pub(super) version: ReplayVersion<1>,
    pub(super) schema_relations: Vec<ReplayRelationSchema>,
    pub(super) carrier_identity: ReplayCarrierIdentity,
    pub(super) instance_identity: ReplayInstanceIdentity,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayModelValidationIdentity {
    pub(super) kind: ReplayValidationTag,
    pub(super) version: ReplayVersion<1>,
    pub(super) obligation_identity: ReplayObligationIdentity,
    pub(super) interpretation_identity: ReplayInterpretationIdentity,
    pub(super) axioms_hold: ReplayAdmittedBool<true>,
    pub(super) conjecture_holds: ReplayAdmittedBool<false>,
    pub(super) validated_refutation: ReplayAdmittedBool<true>,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayNullaryAssignment {
    pub(super) relation_key: String,
    pub(super) value: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub(super) enum ReplayEmptyResult {
    NoCounterexample {},
    Counterexample {
        nullary_assignment: Vec<ReplayNullaryAssignment>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayEmptyCheckIdentity {
    pub(super) kind: ReplayEmptyCheckTag,
    pub(super) version: ReplayVersion<2>,
    pub(super) empty_request_identity: ReplayEmptyRequestIdentity,
    pub(super) obligation_identity: ReplayObligationIdentity,
    pub(super) worker_entailment_identity: ReplayWorkerEntailmentIdentity,
    pub(super) decision_definition: ReplayEmptyDefinition,
    pub(super) result: ReplayEmptyResult,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(untagged)]
pub(super) enum ReplayValidationIdentity {
    Model(Box<ReplayModelValidationIdentity>),
    Empty(Box<ReplayEmptyCheckIdentity>),
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayRuntimeProofFields {
    pub(super) domain: ReplayRuntimeProofDomain,
    pub(super) task_digest: ReplaySha256,
    pub(super) catalog_digest: ReplaySha256,
    pub(super) artifact_backend_digest: ReplaySha256,
    pub(super) semantic_version: u64,
    pub(super) encoding_version: u64,
    pub(super) framework_ii_context_digest: ReplaySha256,
    pub(super) request_digest: ReplaySha256,
    pub(super) job_id: ReplaySha256,
    pub(super) semantic_vc_digest: ReplaySha256,
    pub(super) query_digest: ReplaySha256,
    pub(super) query_bytes: u64,
    pub(super) attempt: super::replay_identity::PhysicalAttemptId,
    pub(super) terminal_result_digest: ReplaySha256,
    pub(super) empty_check_digest: ReplaySha256,
    pub(super) winner: ReplayProofProfile,
    pub(super) runtime_invocation: ReplaySolverInvocation,
    pub(super) certification_profile: ReplayCertificationProfile,
    pub(super) fixed_ambient_job: ReplayFixedAmbientJobFields,
    pub(super) query_artifact: ReplayArtifactIdentity,
    pub(super) proof_artifact: ReplayArtifactIdentity,
    pub(super) terminal_artifact: ReplayArtifactIdentity,
    pub(super) empty_check_artifact: ReplayArtifactIdentity,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayProtectedFields {
    pub(super) domain: ReplayProtectedDomain,
    pub(super) request_digest: ReplaySha256,
    pub(super) selector_registry_digest: ReplaySha256,
    pub(super) rule: ReplayProtectedRule,
    pub(super) source_route_digest: ReplaySha256,
    pub(super) source_formula_digest: ReplaySha256,
    pub(super) target_vc_digest: ReplaySha256,
    pub(super) fixed_ambient_job: ReplayFixedAmbientJobFields,
    pub(super) theorem_name: String,
    pub(super) registry_entry_digest: ReplaySha256,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayProgressFields {
    pub(super) domain: ReplayProgressDomain,
    pub(super) request_digest: ReplaySha256,
    pub(super) job_id: ReplaySha256,
    pub(super) semantic_vc_digest: ReplaySha256,
    pub(super) fixed_ambient_job: ReplayFixedAmbientJobFields,
    pub(super) reason: ReplayInconclusiveReason,
    pub(super) attempt: super::replay_identity::PhysicalAttemptId,
    #[serde(deserialize_with = "replay_nullable")]
    pub(super) next_fmb_start_size: Option<u64>,
    pub(super) previous_proof_allowance_ns: ReplayNatText,
    pub(super) current_proof_allowance_ns: ReplayNatText,
    #[serde(deserialize_with = "replay_nullable")]
    pub(super) peer_failure: Option<ReplayPrivateFailure>,
    pub(super) terminal_artifact: ReplayArtifactIdentity,
    pub(super) terminal_result_digest: ReplaySha256,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayRefutationFields {
    pub(super) domain: ReplayRefutationDomain,
    pub(super) request_digest: ReplaySha256,
    pub(super) job_id: ReplaySha256,
    pub(super) semantic_vc_digest: ReplaySha256,
    pub(super) fixed_ambient_job: ReplayFixedAmbientJobFields,
    pub(super) attempt: super::replay_identity::PhysicalAttemptId,
    pub(super) terminal_artifact: ReplayArtifactIdentity,
    pub(super) terminal_result_digest: ReplaySha256,
    pub(super) source_artifact: ReplayArtifactIdentity,
    pub(super) validation_identity: ReplayValidationIdentity,
    pub(super) validation_digest: ReplaySha256,
    pub(super) validation_artifact: ReplayArtifactIdentity,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "snake_case")]
pub(super) enum ReplayReuseKind {
    ProofSubsumption,
    RefutationSubsumption,
    InconclusiveEntry,
}
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(tag = "tag", rename_all = "snake_case", deny_unknown_fields)]
pub(super) enum ReplayTaggedPremise {
    Pre { identity: ReplayNull },
    Guard { identity: ReplayNull },
    NotThetaGuard { identity: ReplayNull },
    NotGuard { identity: ReplayNull },
    Support { identity: ReplayNull },
    Plain { identity: ReplaySha256 },
    Theta { identity: ReplaySha256 },
    Collapsed { identity: ReplaySha256 },
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayTaskIdentity {
    pub(super) canonical_id: String,
    pub(super) module: String,
    pub(super) namespace: String,
    pub(super) source_sha256: ReplaySha256,
    pub(super) semantic_version: u64,
    pub(super) encoding_version: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayConjecture {
    pub(super) identity_sha256: ReplaySha256,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayTerminationConjectureIdentity {
    pub(super) identity_sha256: ReplayTerminationConjecture,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(tag = "role", rename_all = "snake_case", deny_unknown_fields)]
pub(super) enum ReplaySemanticKey {
    Initialization {
        kind: ReplaySemanticKeyTag,
        version: ReplayVersion<9>,
        task_identity: ReplayTaskIdentity,
        scope_identity: ReplayScopeIdentity,
        conjecture: ReplayConjecture,
        tagged_premises: Vec<ReplayTaggedPremise>,
    },
    Maintenance {
        kind: ReplaySemanticKeyTag,
        version: ReplayVersion<9>,
        task_identity: ReplayTaskIdentity,
        scope_identity: ReplayScopeIdentity,
        conjecture: ReplayConjecture,
        tagged_premises: Vec<ReplayTaggedPremise>,
    },
    Termination {
        kind: ReplaySemanticKeyTag,
        version: ReplayVersion<9>,
        task_identity: ReplayTaskIdentity,
        scope_identity: ReplayScopeIdentity,
        conjecture: ReplayTerminationConjectureIdentity,
        tagged_premises: Vec<ReplaySha256>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayReuseFields {
    pub(super) kind: ReplayReuseTag,
    pub(super) version: ReplayVersion<9>,
    pub(super) reuse_kind: ReplayReuseKind,
    pub(super) semantic_vc_key: ReplaySha256,
    pub(super) matched_tagged_premises: Vec<ReplayTaggedPremise>,
    pub(super) original_request_digest: ReplaySha256,
    pub(super) original_evidence_identity: ReplaySha256,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(tag = "route", rename_all = "snake_case", deny_unknown_fields)]
pub(super) enum ReplayProductionProjection {
    RuntimeProof {
        fields: Box<ReplayRuntimeProofFields>,
        original_digest: ReplaySha256,
        terminal: crate::entailment::ReplaySpecializedTerminalProjection,
    },
    Protected {
        fields: Box<ReplayProtectedFields>,
        original_digest: ReplaySha256,
    },
    Progress {
        fields: Box<ReplayProgressFields>,
        original_digest: ReplaySha256,
        terminal: crate::entailment::ReplaySpecializedTerminalProjection,
    },
    ValidatedRefutation {
        fields: Box<ReplayRefutationFields>,
        original_digest: ReplaySha256,
        terminal: crate::entailment::ReplaySpecializedTerminalProjection,
    },
    SemanticReuse {
        fields: Box<ReplayReuseFields>,
        original_digest: ReplaySha256,
        current_request_digest: ReplaySha256,
        semantic_key_identity: ReplaySemanticKey,
    },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum ReplayProductionCapture {
    Replayable(Box<ReplayProductionProjection>),
    NonReplayable(ReplayProductionError),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct ReplayNull;
impl serde::Serialize for ReplayNull {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.serialize_none()
    }
}
impl<'de> serde::Deserialize<'de> for ReplayNull {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let value = <Value as serde::Deserialize>::deserialize(d)?;
        if value.is_null() {
            Ok(Self)
        } else {
            Err(serde::de::Error::custom("required null"))
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct ReplayAdmittedBool<const B: bool>;
impl<const B: bool> serde::Serialize for ReplayAdmittedBool<B> {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.serialize_bool(B)
    }
}
impl<'de, const B: bool> serde::Deserialize<'de> for ReplayAdmittedBool<B> {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        if <bool as serde::Deserialize>::deserialize(d)? == B {
            Ok(Self)
        } else {
            Err(serde::de::Error::custom("invalid admitted boolean"))
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
#[serde(transparent)]
pub(crate) struct ReplayBackendIdentity(pub(crate) String);
impl<'de> serde::Deserialize<'de> for ReplayBackendIdentity {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let v = <String as serde::Deserialize>::deserialize(d)?;
        if v.len() == 32
            && v.bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
        {
            Ok(Self(v))
        } else {
            Err(serde::de::Error::custom("invalid backend identity"))
        }
    }
}

replay_literal!(
    ReplayClauseRequestTag,
    "whiel_framework_ii_fixed_ambient_check_request"
);
replay_literal!(
    ReplayTerminationRequestTag,
    "whiel_framework_ii_termination_request"
);
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub(super) enum ReplayClauseSelector {
    Initialization { clause_id: u64 },
    Maintenance { clause_id: u64 },
}
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayClauseRequestIdentity {
    pub(super) kind: ReplayClauseRequestTag,
    pub(super) version: ReplayVersion<1>,
    pub(super) attempt_ordinal: super::replay_identity::LedgerRowOrdinal,
    pub(super) scope_identity: ReplayScopeIdentity,
    pub(super) snapshot_identity: ReplaySnapshotIdentity,
    pub(super) selector: ReplayClauseSelector,
}
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayTerminationRequestIdentity {
    pub(super) kind: ReplayTerminationRequestTag,
    pub(super) version: ReplayVersion<1>,
    pub(super) scope_identity: ReplayScopeIdentity,
    pub(super) snapshot: ReplaySnapshotIdentity,
}
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(tag = "subject", rename_all = "snake_case", deny_unknown_fields)]
pub(super) enum ReplayControlSubject {
    Clause {
        identity: ReplayClauseRequestIdentity,
        request_digest: ReplaySha256,
        level: u64,
        launch_suppressed: bool,
    },
    Termination {
        identity: ReplayTerminationRequestIdentity,
        request_digest: ReplaySha256,
    },
}

fn replay_decode<T: serde::de::DeserializeOwned>(
    value: &Value,
) -> Result<T, ReplayProductionError> {
    serde_json::from_value(value.clone()).map_err(|_| ReplayProductionError::UnsupportedSchema)
}

fn replay_scan(value: &impl serde::Serialize) -> Result<(), ReplayProductionError> {
    let encoded =
        serde_json::to_vec(value).map_err(|_| ReplayProductionError::UnsupportedSchema)?;
    if super::Redaction::changes(&encoded) {
        return Err(ReplayProductionError::PrivateDetailRedacted);
    }
    Ok(())
}

fn replay_sha<T: serde::Serialize>(value: &T) -> Result<String, ReplayProductionError> {
    let value =
        serde_json::to_value(value).map_err(|_| ReplayProductionError::UnsupportedSchema)?;
    Ok(canonical_value_sha256(&value))
}

impl ReplayFixedAmbientJobFields {
    pub(super) fn verify_bindings(&self) -> Result<(), ReplayProductionError> {
        let preparation = &self.preparation_identity;
        let empty = &self.empty_request_identity;
        let job = ReplayJobIdentity {
            kind: ReplayJobTag,
            version: ReplayVersion,
            obligation_identity: self.obligation_identity.clone(),
            worker_entailment_identity: self.worker_entailment_identity.clone(),
        };
        if preparation.obligation_identity != self.obligation_identity
            || preparation.worker_entailment_identity != self.worker_entailment_identity
            || preparation.empty_request_identity != *empty
            || preparation.empty_request_digest != self.empty_request_digest
            || preparation.entailment_identity != self.entailment_identity
            || preparation.job_id != self.job_id
            || preparation.scope_identity != self.obligation_identity.scope_identity
            || empty.scope_identity != preparation.scope_identity
            || empty.obligation_identity != self.obligation_identity
            || empty.worker_entailment_identity != self.worker_entailment_identity
            || canonical_value_sha256(&preparation.owner_identity_fields())
                != self.preparation_digest.0
            || canonical_value_sha256(&self.obligation_identity.owner_identity_fields())
                != self.obligation_digest.0
            || canonical_value_sha256(&empty.owner_identity_fields()) != self.empty_request_digest.0
            || canonical_value_sha256(&job.owner_identity_fields()) != self.job_id.0
            || self.query_artifact.kind != ReplayArtifactKind::Query
        {
            return Err(ReplayProductionError::NestedBindingMismatch);
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayPreparedProjection {
    pub(super) fixed_ambient_job: ReplayFixedAmbientJobFields,
    pub(super) entailment_structure: crate::entailment::assembly::ReplayEntailmentStructure,
    pub(super) control_request_digest: ReplaySha256,
    pub(super) control_subject: ReplayControlSubject,
    pub(super) control_target: ReplaySelector,
    pub(super) control_snapshot: ReplaySnapshotIdentity,
    pub(super) scope_digest: ReplaySha256,
    pub(super) catalog_digest: ReplaySha256,
    pub(super) partition_digest: ReplaySha256,
    pub(super) framework_context_digest: ReplaySha256,
}

impl PreparedFrameworkIIEntailment {
    pub(super) fn replay_projection(
        &self,
    ) -> Result<ReplayPreparedProjection, ReplayProductionError> {
        let fixed_ambient_job: ReplayFixedAmbientJobFields =
            replay_decode(&fixed_ambient_job_fields(self))?;
        fixed_ambient_job.verify_bindings()?;
        let entailment_structure = self
            .entailment
            .replay_structure()
            .map_err(|_| ReplayProductionError::UnsupportedSchema)?;
        if entailment_structure.derive_identity() != self.entailment.identity()
            || entailment_structure.worker_entailment_digest
                != replay_sha(&fixed_ambient_job.worker_entailment_identity)?
        {
            return Err(ReplayProductionError::NestedBindingMismatch);
        }
        let projection = ReplayPreparedProjection {
            entailment_structure,
            control_subject: self.replay_control_subject.clone()?,
            control_request_digest: replay_decode(&json!(self.control_request_digest()))?,
            control_target: fixed_ambient_job.obligation_identity.selector.clone(),
            control_snapshot: replay_decode(&self.control_snapshot.worker_identity())?,
            scope_digest: replay_decode(&json!(self.scope_digest()))?,
            catalog_digest: replay_decode(&json!(self.catalog_digest()))?,
            partition_digest: replay_decode(&json!(self.partition_digest()))?,
            framework_context_digest: replay_decode(&json!(self.framework_context_digest()))?,
            fixed_ambient_job,
        };
        if projection.control_snapshot != projection.fixed_ambient_job.obligation_identity.snapshot
            || projection.framework_context_digest != projection.fixed_ambient_job.obligation_digest
            || replay_sha(
                &projection
                    .fixed_ambient_job
                    .obligation_identity
                    .scope_identity,
            )? != projection.scope_digest.0
        {
            return Err(ReplayProductionError::NestedBindingMismatch);
        }
        projection.verify()?;
        let bytes = serde_json::to_vec(&projection)
            .map_err(|_| ReplayProductionError::UnsupportedSchema)?;
        if super::Redaction::changes(&bytes) {
            return Err(ReplayProductionError::PrivateDetailRedacted);
        }
        Ok(projection)
    }
}

// This helper receives only live owner-held detail, never a recorded raw string.
// Redaction is checked before deriving any durable detail or containing digest.
fn replay_private_failure(
    report: &FailureReport,
) -> Result<ReplayPrivateFailure, ReplayProductionError> {
    if report
        .detail()
        .is_some_and(|detail| super::Redaction::changes(detail.as_bytes()))
    {
        return Err(ReplayProductionError::PrivateDetailRedacted);
    }
    let mut fields = failure_fields(report);
    let object = fields
        .as_object_mut()
        .ok_or(ReplayProductionError::UnsupportedSchema)?;
    object.remove("detail");
    object.insert(
        "detail_digest".into(),
        json!(
            report
                .detail()
                .map(|detail| canonical_value_sha256(&json!(detail)))
        ),
    );
    replay_decode(&fields)
}

// No callback receives private text. A matching digest permits this owner to
// re-use the identical live detail to verify the old constructor's exact hash.
fn replay_progress_constructor_fields(
    fields: &ReplayProgressFields,
    live_failure: Option<&FailureReport>,
) -> Result<Value, ReplayProductionError> {
    let live = live_failure.map(replay_private_failure).transpose()?;
    if fields
        .peer_failure
        .as_ref()
        .map(|failure| &failure.detail_digest)
        != live.as_ref().map(|failure| &failure.detail_digest)
    {
        return Err(ReplayProductionError::PrivateDetailMismatch);
    }
    let peer_failure = if let Some(failure) = fields.peer_failure.as_ref() {
        let report = live_failure.ok_or(ReplayProductionError::PrivateDetailMismatch)?;
        Some(replay_failure_fields(
            &failure.origin,
            &failure.kind,
            failure.retryable,
            &failure.scope,
            report.detail(),
            &failure.artifacts,
        ))
    } else {
        None
    };
    let value = replay_progress_fields! {
        request_digest: &fields.request_digest,
        job_id: &fields.job_id,
        semantic_vc_digest: &fields.semantic_vc_digest,
        fixed_ambient_job: &fields.fixed_ambient_job,
        reason: &fields.reason,
        attempt: &fields.attempt,
        next_fmb_start_size: &fields.next_fmb_start_size,
        previous_proof_allowance_ns: &fields.previous_proof_allowance_ns,
        current_proof_allowance_ns: &fields.current_proof_allowance_ns,
        peer_failure: peer_failure,
        terminal_artifact: &fields.terminal_artifact,
        terminal_result_digest: &fields.terminal_result_digest
    };
    Ok(value)
}

fn replay_capture_production(
    route: &str,
    fields: &Value,
    digest: &str,
    live_failure: Option<&FailureReport>,
    terminal: Option<&crate::entailment::ReplaySpecializedTerminalOwner>,
) -> ReplayProductionCapture {
    let capture = || -> Result<ReplayProductionProjection, ReplayProductionError> {
        // This scan sees private constructor fields only inside their owner.
        if let Some(report) = live_failure {
            replay_private_failure(report)?;
        }
        let encoded =
            serde_json::to_vec(fields).map_err(|_| ReplayProductionError::UnsupportedSchema)?;
        if super::Redaction::changes(&encoded) {
            return Err(ReplayProductionError::PrivateDetailRedacted);
        }
        if canonical_value_sha256(fields) != digest {
            return Err(ReplayProductionError::ConstructorDigestMismatch);
        }
        let mut typed_fields = fields.clone();
        if route == "progress" {
            typed_fields["peer_failure"] =
                serde_json::to_value(live_failure.map(replay_private_failure).transpose()?)
                    .map_err(|_| ReplayProductionError::UnsupportedSchema)?;
        }
        let mut envelope = json!({"route":route,"fields":typed_fields,"original_digest":digest});
        if route != "protected" {
            let owner = terminal.ok_or(ReplayProductionError::UnsupportedSchema)?;
            let projection = owner.projection();
            if fields.get("terminal_result_digest").and_then(Value::as_str)
                != Some(projection.digest())
            {
                return Err(ReplayProductionError::NestedBindingMismatch);
            }
            envelope["terminal"] = serde_json::to_value(projection)
                .map_err(|_| ReplayProductionError::UnsupportedSchema)?;
        }
        let projection: ReplayProductionProjection = replay_decode(&envelope)?;
        projection.verify_constructor(live_failure)?;
        Ok(projection)
    };
    match capture() {
        Ok(value) => ReplayProductionCapture::Replayable(Box::new(value)),
        Err(reason) => ReplayProductionCapture::NonReplayable(reason),
    }
}

impl ReplayProductionProjection {
    // This verifies each retained constructor hash, not correspondence authority.
    // R's graph supplies checked request/artifact/attempt and upstream leaf links.
    fn constructor_fields(
        &self,
        live_failure: Option<&FailureReport>,
    ) -> Result<Value, ReplayProductionError> {
        let value: Result<Value, serde_json::Error> = match self {
            Self::RuntimeProof { fields, .. } => {
                fields.fixed_ambient_job.verify_bindings()?;
                fields.verify_bindings()?;
                Ok(fields.owner_identity_fields())
            }
            Self::Protected { fields, .. } => {
                fields.fixed_ambient_job.verify_bindings()?;
                fields.verify_bindings()?;
                Ok(fields.owner_identity_fields())
            }
            Self::Progress { fields, .. } => {
                fields.fixed_ambient_job.verify_bindings()?;
                fields.verify_bindings()?;
                return replay_progress_constructor_fields(fields, live_failure);
            }
            Self::ValidatedRefutation { fields, .. } => {
                fields.fixed_ambient_job.verify_bindings()?;
                fields.verify_bindings()?;
                if replay_sha(&fields.validation_identity)? != fields.validation_digest.0 {
                    return Err(ReplayProductionError::NestedBindingMismatch);
                }
                match &fields.validation_identity {
                    ReplayValidationIdentity::Model(model) => {
                        if model.obligation_identity != fields.fixed_ambient_job.obligation_identity
                            || fields.source_artifact.kind != ReplayArtifactKind::Model
                        {
                            return Err(ReplayProductionError::NestedBindingMismatch);
                        }
                    }
                    ReplayValidationIdentity::Empty(empty) => {
                        if !matches!(empty.result, ReplayEmptyResult::Counterexample { .. })
                            || empty.obligation_identity
                                != fields.fixed_ambient_job.obligation_identity
                            || empty.empty_request_identity
                                != fields.fixed_ambient_job.empty_request_identity
                            || empty.worker_entailment_identity
                                != fields.fixed_ambient_job.worker_entailment_identity
                            || fields.source_artifact.kind != ReplayArtifactKind::EmptyInstanceCheck
                        {
                            return Err(ReplayProductionError::NestedBindingMismatch);
                        }
                    }
                }
                Ok(fields.owner_identity_fields())
            }
            Self::SemanticReuse {
                fields,
                semantic_key_identity,
                ..
            } => {
                if replay_sha(semantic_key_identity)? != fields.semantic_vc_key.0 {
                    return Err(ReplayProductionError::NestedBindingMismatch);
                }
                Ok(fields.owner_identity_fields())
            }
        };
        value.map_err(|_| ReplayProductionError::UnsupportedSchema)
    }

    fn original_digest(&self) -> &ReplaySha256 {
        match self {
            Self::RuntimeProof {
                original_digest, ..
            }
            | Self::Protected {
                original_digest, ..
            }
            | Self::Progress {
                original_digest, ..
            }
            | Self::ValidatedRefutation {
                original_digest, ..
            }
            | Self::SemanticReuse {
                original_digest, ..
            } => original_digest,
        }
    }

    fn verify_constructor(
        &self,
        live_failure: Option<&FailureReport>,
    ) -> Result<(), ReplayProductionError> {
        replay_scan(self)?;
        self.verify_terminal_bindings()?;
        let fields = self.constructor_fields(live_failure)?;
        if canonical_value_sha256(&fields) != self.original_digest().0 {
            return Err(ReplayProductionError::ConstructorDigestMismatch);
        }
        Ok(())
    }
}

impl FrameworkIIEntailmentProgress {
    pub(super) fn verify_replay_projection(
        &self,
        recorded: &ReplayProductionProjection,
    ) -> Result<(), ReplayProductionError> {
        let ReplayProductionCapture::Replayable(live) = &self.replay_capture else {
            return Err(ReplayProductionError::UnsupportedSchema);
        };
        if !matches!(recorded, ReplayProductionProjection::Progress { .. }) {
            return Err(ReplayProductionError::UnsupportedSchema);
        }
        let owner = self
            .replay_terminal
            .as_ref()
            .ok_or(ReplayProductionError::UnsupportedSchema)?;
        if let ReplayProductionProjection::Progress {
            fields, terminal, ..
        } = recorded
        {
            if fields.terminal_result_digest.0 != terminal.digest() {
                return Err(ReplayProductionError::NestedBindingMismatch);
            }
            owner
                .verify_replay_projection(terminal)
                .map_err(|_| ReplayProductionError::ConstructorDigestMismatch)?;
        }
        live.verify_constructor(self.peer_failure.as_ref())?;
        recorded.verify_constructor(self.peer_failure.as_ref())
    }
}

fn replay_capture_reuse(
    fields: &Value,
    digest: &str,
    current_request: &str,
    semantic_key: &Value,
) -> ReplayProductionCapture {
    let capture = || -> Result<ReplayProductionProjection, ReplayProductionError> {
        let value = json!({"route":"semantic_reuse","fields":fields,"original_digest":digest,
            "current_request_digest":current_request,"semantic_key_identity":semantic_key});
        let bytes =
            serde_json::to_vec(&value).map_err(|_| ReplayProductionError::UnsupportedSchema)?;
        if super::Redaction::changes(&bytes) {
            return Err(ReplayProductionError::PrivateDetailRedacted);
        }
        let projection: ReplayProductionProjection = replay_decode(&value)?;
        projection.verify_constructor(None)?;
        Ok(projection)
    };
    match capture() {
        Ok(value) => ReplayProductionCapture::Replayable(Box::new(value)),
        Err(reason) => ReplayProductionCapture::NonReplayable(reason),
    }
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(tag = "role", rename_all = "snake_case", deny_unknown_fields)]
pub(super) enum ReplayArtifactRole {
    Query {},
    Proof {},
    TerminalTrace {},
    EmptyCheck {},
    SourceModel {},
    ValidationReceipt {},
    RouteReceipt {},
    ProgressReceipt {},
    PeerFailure { ordinal: u64 },
}
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayArtifactAssociation {
    pub(super) role: ReplayArtifactRole,
    pub(super) artifact: ReplayArtifactIdentity,
}
fn replay_artifact_association(
    role: ReplayArtifactRole,
    artifact: ArtifactRef,
) -> Result<ReplayArtifactAssociation, ReplayProductionError> {
    Ok(ReplayArtifactAssociation {
        role,
        artifact: replay_decode(&artifact_fields(artifact))?,
    })
}
impl RuntimeProofReceipt {
    pub(super) fn replay_artifact_associations(
        &self,
    ) -> Result<Vec<ReplayArtifactAssociation>, ReplayProductionError> {
        [
            (ReplayArtifactRole::Query {}, self.query_artifact),
            (ReplayArtifactRole::Proof {}, self.proof_artifact),
            (ReplayArtifactRole::TerminalTrace {}, self.terminal_artifact),
            (ReplayArtifactRole::EmptyCheck {}, self.empty_check_artifact),
            (ReplayArtifactRole::RouteReceipt {}, self.receipt_artifact),
        ]
        .into_iter()
        .map(|(role, artifact)| replay_artifact_association(role, artifact))
        .collect()
    }
}
impl ProtectedTheoremSelectionReceipt {
    pub(super) fn replay_artifact_associations(
        &self,
    ) -> Result<Vec<ReplayArtifactAssociation>, ReplayProductionError> {
        Ok(vec![replay_artifact_association(
            ReplayArtifactRole::RouteReceipt {},
            self.receipt_artifact,
        )?])
    }
}
impl ValidatedFiniteRefutation {
    pub(super) fn replay_artifact_associations(
        &self,
    ) -> Result<Vec<ReplayArtifactAssociation>, ReplayProductionError> {
        let source_role = match self.source_artifact.kind() {
            ArtifactKind::Model => ReplayArtifactRole::SourceModel {},
            ArtifactKind::EmptyInstanceCheck => ReplayArtifactRole::EmptyCheck {},
            _ => return Err(ReplayProductionError::UnsupportedSchema),
        };
        [
            (ReplayArtifactRole::TerminalTrace {}, self.terminal_artifact),
            (source_role, self.source_artifact),
            (
                ReplayArtifactRole::ValidationReceipt {},
                self.validation_artifact,
            ),
            (ReplayArtifactRole::RouteReceipt {}, self.receipt_artifact),
        ]
        .into_iter()
        .map(|(role, artifact)| replay_artifact_association(role, artifact))
        .collect()
    }
}
impl FrameworkIIEntailmentProgress {
    pub(super) fn replay_artifact_associations(
        &self,
    ) -> Result<Vec<ReplayArtifactAssociation>, ReplayProductionError> {
        let mut result = vec![
            replay_artifact_association(
                ReplayArtifactRole::TerminalTrace {},
                self.terminal_artifact,
            )?,
            replay_artifact_association(
                ReplayArtifactRole::ProgressReceipt {},
                self.progress_artifact,
            )?,
        ];
        if let Some(report) = self.peer_failure.as_ref() {
            replay_private_failure(report)?;
            for (ordinal, artifact) in report.artifact_references().iter().enumerate() {
                result.push(replay_artifact_association(
                    ReplayArtifactRole::PeerFailure {
                        ordinal: ordinal as u64,
                    },
                    *artifact,
                )?);
            }
        }
        Ok(result)
    }
}

fn replay_subject_projection(
    subject: &FrameworkIICheckSubject,
) -> Result<ReplayControlSubject, ReplayProductionError> {
    if !subject.has_current_identity() {
        return Err(ReplayProductionError::NestedBindingMismatch);
    }
    let digest: ReplaySha256 = replay_decode(&json!(subject.request_digest()))?;
    let projection = match subject {
        FrameworkIICheckSubject::Clause(request) => ReplayControlSubject::Clause {
            identity: replay_decode(request.identity())?,
            request_digest: digest,
            level: request.level().get(),
            launch_suppressed: request.launch_suppressed(),
        },
        FrameworkIICheckSubject::Termination(request) => ReplayControlSubject::Termination {
            identity: replay_decode(request.identity())?,
            request_digest: digest,
        },
    };
    let bytes =
        serde_json::to_vec(&projection).map_err(|_| ReplayProductionError::UnsupportedSchema)?;
    if super::Redaction::changes(&bytes) {
        return Err(ReplayProductionError::PrivateDetailRedacted);
    }
    Ok(projection)
}

macro_rules! replay_physical_receipt_verifier {
    ($owner:ty,$variant:ident) => {
        impl $owner {
            pub(super) fn verify_replay_projection(
                &self,
                recorded: &ReplayProductionProjection,
            ) -> Result<(), ReplayProductionError> {
                let ReplayProductionCapture::Replayable(live) = &self.replay_capture else {
                    return Err(ReplayProductionError::UnsupportedSchema);
                };
                let ReplayProductionProjection::$variant {
                    fields, terminal, ..
                } = recorded
                else {
                    return Err(ReplayProductionError::UnsupportedSchema);
                };
                if fields.terminal_result_digest.0 != terminal.digest() {
                    return Err(ReplayProductionError::NestedBindingMismatch);
                }
                let owner = self
                    .replay_terminal
                    .as_ref()
                    .ok_or(ReplayProductionError::UnsupportedSchema)?;
                owner
                    .verify_replay_projection(terminal)
                    .map_err(|_| ReplayProductionError::ConstructorDigestMismatch)?;
                live.verify_constructor(None)?;
                recorded.verify_constructor(None)
            }
        }
    };
}
replay_physical_receipt_verifier!(RuntimeProofReceipt, RuntimeProof);
replay_physical_receipt_verifier!(ValidatedFiniteRefutation, ValidatedRefutation);
macro_rules! replay_nonphysical_receipt_verifier {
    ($owner:ty,$variant:ident) => {
        impl $owner {
            pub(super) fn verify_replay_projection(
                &self,
                recorded: &ReplayProductionProjection,
            ) -> Result<(), ReplayProductionError> {
                let ReplayProductionCapture::Replayable(live) = &self.replay_capture else {
                    return Err(ReplayProductionError::UnsupportedSchema);
                };
                if !matches!(recorded, ReplayProductionProjection::$variant { .. }) {
                    return Err(ReplayProductionError::UnsupportedSchema);
                }
                live.verify_constructor(None)?;
                recorded.verify_constructor(None)
            }
        }
    };
}
replay_nonphysical_receipt_verifier!(ProtectedTheoremSelectionReceipt, Protected);
replay_nonphysical_receipt_verifier!(SemanticReuseEvidence, SemanticReuse);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ReplayPrivateFailureError {
    Redacted,
    Unsupported,
}
impl ReplaySha256 {
    pub(crate) fn parse(value: &str) -> Result<Self, &'static str> {
        replay_decode(&json!(value)).map_err(|_| "invalid lowercase SHA-256")
    }
    pub(crate) fn as_str(&self) -> &str {
        &self.0
    }
}
impl ReplayBackendIdentity {
    pub(crate) fn parse(value: &str) -> Result<Self, &'static str> {
        replay_decode(&json!(value)).map_err(|_| "invalid backend identity")
    }
    pub(crate) fn as_str(&self) -> &str {
        &self.0
    }
}
impl ReplayArtifactIdentity {
    pub(crate) fn capture(reference: ArtifactRef) -> Result<Self, &'static str> {
        replay_decode(&artifact_fields(reference)).map_err(|_| "invalid artifact identity")
    }
}
impl ReplayPrivateFailure {
    pub(crate) fn capture(report: &FailureReport) -> Result<Self, ReplayPrivateFailureError> {
        replay_private_failure(report).map_err(|error| match error {
            ReplayProductionError::PrivateDetailRedacted => ReplayPrivateFailureError::Redacted,
            _ => ReplayPrivateFailureError::Unsupported,
        })
    }
}

impl ReplayRuntimeProofFields {
    fn owner_identity_fields(&self) -> Value {
        replay_runtime_proof_fields! {
            task_digest: &self.task_digest,
            catalog_digest: &self.catalog_digest,
            artifact_backend_digest: &self.artifact_backend_digest,
            semantic_version: &self.semantic_version,
            encoding_version: &self.encoding_version,
            framework_ii_context_digest: &self.framework_ii_context_digest,
            request_digest: &self.request_digest,
            job_id: &self.job_id,
            semantic_vc_digest: &self.semantic_vc_digest,
            query_digest: &self.query_digest,
            query_bytes: &self.query_bytes,
            attempt: &self.attempt,
            terminal_result_digest: &self.terminal_result_digest,
            empty_check_digest: &self.empty_check_digest,
            winner: &self.winner,
            runtime_invocation: &self.runtime_invocation,
            certification_profile: &self.certification_profile,
            fixed_ambient_job: &self.fixed_ambient_job,
            query_artifact: &self.query_artifact,
            proof_artifact: &self.proof_artifact,
            terminal_artifact: &self.terminal_artifact,
            empty_check_artifact: &self.empty_check_artifact
        }
    }
}
impl ReplayProtectedFields {
    fn owner_identity_fields(&self) -> Value {
        replay_protected_fields! {
            request_digest: &self.request_digest,
            selector_registry_digest: &self.selector_registry_digest,
            rule: &self.rule,
            source_route_digest: &self.source_route_digest,
            source_formula_digest: &self.source_formula_digest,
            target_vc_digest: &self.target_vc_digest,
            fixed_ambient_job: &self.fixed_ambient_job,
            theorem_name: &self.theorem_name,
            registry_entry_digest: &self.registry_entry_digest
        }
    }
}
impl ReplayRefutationFields {
    fn owner_identity_fields(&self) -> Value {
        replay_refutation_fields! {
            request_digest: &self.request_digest,
            job_id: &self.job_id,
            semantic_vc_digest: &self.semantic_vc_digest,
            fixed_ambient_job: &self.fixed_ambient_job,
            attempt: &self.attempt,
            terminal_artifact: &self.terminal_artifact,
            terminal_result_digest: &self.terminal_result_digest,
            source_artifact: &self.source_artifact,
            validation_identity: &self.validation_identity,
            validation_digest: &self.validation_digest,
            validation_artifact: &self.validation_artifact
        }
    }
}
impl ReplayReuseFields {
    fn owner_identity_fields(&self) -> Value {
        replay_reuse_fields! {
            reuse_kind: &self.reuse_kind,
            semantic_vc_key: &self.semantic_vc_key,
            matched_tagged_premises: &self.matched_tagged_premises,
            original_request_digest: &self.original_request_digest,
            original_evidence_identity: &self.original_evidence_identity
        }
    }
}
impl ReplayObligationIdentity {
    fn owner_identity_fields(&self) -> Value {
        replay_obligation_fields! {
            scope_identity: &self.scope_identity,
            snapshot: &self.snapshot,
            selector: &self.selector
        }
    }
}
impl ReplayJobIdentity {
    fn owner_identity_fields(&self) -> Value {
        replay_job_fields! {
            obligation_identity: &self.obligation_identity,
            worker_entailment_identity: &self.worker_entailment_identity
        }
    }
}
impl ReplayEmptyRequestIdentity {
    fn owner_identity_fields(&self) -> Value {
        replay_empty_request_fields! {
            scope_identity: &self.scope_identity,
            obligation_identity: &self.obligation_identity,
            worker_entailment_identity: &self.worker_entailment_identity
        }
    }
}
impl ReplayPreparationIdentity {
    fn owner_identity_fields(&self) -> Value {
        replay_preparation_fields! {
            scope_identity: &self.scope_identity,
            obligation_identity: &self.obligation_identity,
            worker_entailment_identity: &self.worker_entailment_identity,
            job_id: &self.job_id,
            empty_request_identity: &self.empty_request_identity,
            empty_request_digest: &self.empty_request_digest,
            entailment_identity: &self.entailment_identity
        }
    }
}

impl ReplaySolverInvocation {
    fn verified_owner(&self) -> Result<SolverInvocationIdentity, ReplayProductionError> {
        let owner = SolverInvocationIdentity::from_parts(
            Arc::from(self.tool.as_str()),
            Arc::from(self.version.as_str()),
            Arc::from(self.resolved_path.as_str()),
            Arc::from(self.binary_digest.as_str()),
            Arc::from(self.platform.as_str()),
            Arc::from(self.architecture.as_str()),
            self.arguments
                .iter()
                .map(|v| Arc::from(v.as_str()))
                .collect(),
        )
        .map_err(|_| ReplayProductionError::NestedBindingMismatch)?;
        if owner.identity_digest() != self.identity_digest.as_str() {
            return Err(ReplayProductionError::NestedBindingMismatch);
        }
        Ok(owner)
    }
}
impl ReplayProofProfile {
    fn owner(&self) -> ProofSearchProfile {
        match self {
            Self::Direct => ProofSearchProfile::Direct,
            Self::Casc2025 => ProofSearchProfile::Casc2025,
        }
    }
}
impl ReplayCertificationProfile {
    fn verify(&self) -> Result<(), ReplayProductionError> {
        let owner = LeancheckCertificationProfile::new(
            self.profile.owner(),
            self.profile_version.as_str(),
            self.leancheck_invocation.verified_owner()?,
            self.permitted_cadical
                .as_ref()
                .map(ReplaySolverInvocation::verified_owner)
                .transpose()?,
            self.vamplean_digest.as_str(),
            self.generator_digest.as_str(),
            self.output_contract_digest.as_str(),
            self.transformer_digest.as_str(),
            self.lean_bridge_digest.as_str(),
        )
        .map_err(|_| ReplayProductionError::NestedBindingMismatch)?;
        if owner.profile_digest() != self.profile_digest.as_str() {
            return Err(ReplayProductionError::NestedBindingMismatch);
        }
        Ok(())
    }
}
impl ReplayArtifactIdentity {
    fn verify_role(
        &self,
        backend: &ReplayBackendIdentity,
        kind: ReplayArtifactKind,
    ) -> Result<(), ReplayProductionError> {
        if &self.backend != backend || self.kind != kind {
            return Err(ReplayProductionError::NestedBindingMismatch);
        }
        Ok(())
    }
}
impl ReplayRuntimeProofFields {
    fn verify_bindings(&self) -> Result<(), ReplayProductionError> {
        let fixed = &self.fixed_ambient_job;
        self.runtime_invocation.verified_owner()?;
        self.certification_profile.verify()?;
        let empty = ReplayEmptyCheckIdentity {
            kind: ReplayEmptyCheckTag,
            version: ReplayVersion,
            empty_request_identity: fixed.empty_request_identity.clone(),
            obligation_identity: fixed.obligation_identity.clone(),
            worker_entailment_identity: fixed.worker_entailment_identity.clone(),
            decision_definition: ReplayEmptyDefinition,
            result: ReplayEmptyResult::NoCounterexample {},
        };
        if self.job_id != fixed.job_id
            || self.semantic_vc_digest != fixed.obligation_digest
            || self.framework_ii_context_digest != fixed.obligation_digest
            || self.query_artifact != fixed.query_artifact
            || self.winner != self.certification_profile.profile
            || replay_sha(&empty)? != self.empty_check_digest.0
        {
            return Err(ReplayProductionError::NestedBindingMismatch);
        }
        let backend = &fixed.query_artifact.backend;
        let backend_digest = canonical_value_sha256(
            &json!({"domain":"whiel-artifact-backend-v1","task_digest":self.task_digest,"backend":backend}),
        );
        if backend_digest != self.artifact_backend_digest.0 {
            return Err(ReplayProductionError::NestedBindingMismatch);
        }
        self.proof_artifact
            .verify_role(backend, ReplayArtifactKind::Proof)?;
        self.terminal_artifact
            .verify_role(backend, ReplayArtifactKind::RuntimeTrace)?;
        self.empty_check_artifact
            .verify_role(backend, ReplayArtifactKind::EmptyInstanceCheck)
    }
}
impl ReplayProtectedFields {
    fn verify_bindings(&self) -> Result<(), ReplayProductionError> {
        let registry = canonical_value_sha256(&protected_theorem_selector_registry_fields());
        let (rule, source, target, context, theorem) = match &self.rule {
            ReplayProtectedRule::Initialization {
                source_conjunct,
                target_clause,
                target_context,
            } => (
                "edb_precondition_initialization",
                source_conjunct,
                *target_clause,
                target_context,
                EDB_PRECONDITION_INIT_THEOREM,
            ),
            ReplayProtectedRule::Maintenance {
                source_conjunct,
                target_clause,
                target_context,
                ..
            } => (
                "edb_precondition_maintenance",
                source_conjunct,
                *target_clause,
                target_context,
                EDB_PRECONDITION_MAINT_THEOREM,
            ),
        };
        let selector_matches = matches!((&self.rule,&self.fixed_ambient_job.obligation_identity.selector),
            (ReplayProtectedRule::Initialization{..},ReplaySelector::Initialization{clause_id})
            | (ReplayProtectedRule::Maintenance{..},ReplaySelector::Maintenance{clause_id}) if *clause_id==target);
        let entry = canonical_value_sha256(&replay_registry_entry_fields(&registry, rule, theorem));
        if registry != self.selector_registry_digest.0
            || entry != self.registry_entry_digest.0
            || theorem != self.theorem_name
            || source != &self.source_formula_digest
            || context != &self.fixed_ambient_job.obligation_digest
            || self.target_vc_digest != self.fixed_ambient_job.obligation_digest
            || !selector_matches
        {
            return Err(ReplayProductionError::NestedBindingMismatch);
        }
        Ok(())
    }
}
fn replay_nat_cmp(left: &ReplayNatText, right: &ReplayNatText) -> std::cmp::Ordering {
    left.0
        .len()
        .cmp(&right.0.len())
        .then_with(|| left.0.cmp(&right.0))
}
impl ReplayProgressFields {
    fn verify_bindings(&self) -> Result<(), ReplayProductionError> {
        let fixed = &self.fixed_ambient_job;
        if self.job_id != fixed.job_id
            || self.semantic_vc_digest != fixed.obligation_digest
            || self.previous_proof_allowance_ns.0 == "0"
            || replay_nat_cmp(
                &self.previous_proof_allowance_ns,
                &self.current_proof_allowance_ns,
            )
            .is_gt()
            || self.next_fmb_start_size == Some(0)
        {
            return Err(ReplayProductionError::NestedBindingMismatch);
        }
        self.terminal_artifact.verify_role(
            &fixed.query_artifact.backend,
            ReplayArtifactKind::RuntimeTrace,
        )?;
        if let Some(failure) = &self.peer_failure {
            for artifact in &failure.artifacts {
                if artifact.backend != fixed.query_artifact.backend {
                    return Err(ReplayProductionError::NestedBindingMismatch);
                }
            }
        }
        Ok(())
    }
}
impl ReplayInterpretationIdentity {
    fn verify_scope(&self, scope: &ReplayScopeIdentity) -> Result<(), ReplayProductionError> {
        let schema = self
            .schema_relations
            .iter()
            .map(|r| (r.key.clone(), r.arity))
            .collect::<Vec<_>>();
        if schema != scope.ambient_scope.1 || self.instance_identity.relations.len() != schema.len()
        {
            return Err(ReplayProductionError::NestedBindingMismatch);
        }
        let carrier = self
            .carrier_identity
            .carrier_keys
            .iter()
            .collect::<std::collections::BTreeSet<_>>();
        if carrier.len() != self.carrier_identity.carrier_keys.len() {
            return Err(ReplayProductionError::NestedBindingMismatch);
        }
        for ((key, arity), relation) in schema.iter().zip(&self.instance_identity.relations) {
            if key != &relation.key || *arity != relation.arity {
                return Err(ReplayProductionError::NestedBindingMismatch);
            }
            let unique = relation
                .rows
                .iter()
                .collect::<std::collections::BTreeSet<_>>();
            if unique.len() != relation.rows.len()
                || relation.rows.iter().any(|row| {
                    row.len() as u64 != *arity || row.iter().any(|value| !carrier.contains(value))
                })
            {
                return Err(ReplayProductionError::NestedBindingMismatch);
            }
        }
        Ok(())
    }
}
impl ReplayEmptyCheckIdentity {
    fn verify_assignment(&self) -> Result<(), ReplayProductionError> {
        if let ReplayEmptyResult::Counterexample { nullary_assignment } = &self.result {
            let expected = self
                .obligation_identity
                .scope_identity
                .ambient_scope
                .1
                .iter()
                .filter(|(_, arity)| *arity == 0)
                .map(|(key, _)| key)
                .collect::<Vec<_>>();
            let actual = nullary_assignment
                .iter()
                .map(|item| &item.relation_key)
                .collect::<Vec<_>>();
            if expected != actual {
                return Err(ReplayProductionError::NestedBindingMismatch);
            }
        }
        Ok(())
    }
}
impl ReplayRefutationFields {
    fn verify_bindings(&self) -> Result<(), ReplayProductionError> {
        let fixed = &self.fixed_ambient_job;
        if self.job_id != fixed.job_id || self.semantic_vc_digest != fixed.obligation_digest {
            return Err(ReplayProductionError::NestedBindingMismatch);
        }
        let backend = &fixed.query_artifact.backend;
        if &self.source_artifact.backend != backend {
            return Err(ReplayProductionError::NestedBindingMismatch);
        }
        self.terminal_artifact
            .verify_role(backend, ReplayArtifactKind::RuntimeTrace)?;
        self.validation_artifact
            .verify_role(backend, ReplayArtifactKind::Witness)?;
        match &self.validation_identity {
            ReplayValidationIdentity::Model(model) => model
                .interpretation_identity
                .verify_scope(&fixed.obligation_identity.scope_identity),
            ReplayValidationIdentity::Empty(empty) => empty.verify_assignment(),
        }
    }
}
impl ReplayPreparedProjection {
    pub(super) fn verify(&self) -> Result<(), ReplayProductionError> {
        replay_scan(self)?;
        let fixed = &self.fixed_ambient_job;
        fixed.verify_bindings()?;
        let scope = &fixed.obligation_identity.scope_identity;
        let task = &self.entailment_structure;
        if scope.task_canonical_id != task.canonical_id
            || scope.task_module != task.module
            || scope.task_namespace != task.namespace
            || scope.task_source_sha256.0 != task.source_digest
            || scope.semantic_version != task.semantic_version
            || scope.encoding_version != task.encoding_version
        {
            return Err(ReplayProductionError::NestedBindingMismatch);
        }
        if !self.entailment_structure.verify_allocation()
            || self.entailment_structure.derive_identity() != fixed.entailment_identity.0
            || self.entailment_structure.worker_entailment_digest
                != replay_sha(&fixed.worker_entailment_identity)?
            || self.control_snapshot != fixed.obligation_identity.snapshot
            || self.control_target != fixed.obligation_identity.selector
            || self.framework_context_digest != fixed.obligation_digest
            || replay_sha(&fixed.obligation_identity.scope_identity)? != self.scope_digest.0
        {
            return Err(ReplayProductionError::NestedBindingMismatch);
        }
        match &self.control_subject {
            ReplayControlSubject::Clause {
                identity,
                request_digest,
                level,
                ..
            } => {
                let selector = match identity.selector {
                    ReplayClauseSelector::Initialization { clause_id } => {
                        ReplaySelector::Initialization { clause_id }
                    }
                    ReplayClauseSelector::Maintenance { clause_id } => {
                        ReplaySelector::Maintenance { clause_id }
                    }
                };
                let clause = match selector {
                    ReplaySelector::Initialization { clause_id }
                    | ReplaySelector::Maintenance { clause_id } => clause_id,
                    _ => return Err(ReplayProductionError::NestedBindingMismatch),
                };
                if replay_sha(identity)? != request_digest.0
                    || request_digest != &self.control_request_digest
                    || selector != self.control_target
                    || identity.snapshot_identity != self.control_snapshot
                    || identity.scope_identity != fixed.obligation_identity.scope_identity
                    || !self
                        .control_snapshot
                        .rows
                        .iter()
                        .any(|row| row.clause_id == clause && row.level == *level)
                {
                    return Err(ReplayProductionError::NestedBindingMismatch);
                }
            }
            ReplayControlSubject::Termination {
                identity,
                request_digest,
            } => {
                if replay_sha(identity)? != request_digest.0
                    || request_digest != &self.control_request_digest
                    || !matches!(self.control_target, ReplaySelector::Termination {})
                    || identity.snapshot != self.control_snapshot
                    || identity.scope_identity != fixed.obligation_identity.scope_identity
                {
                    return Err(ReplayProductionError::NestedBindingMismatch);
                }
            }
        }
        Ok(())
    }
}

impl ReplayProductionProjection {
    pub(super) fn verify_preparation(
        &self,
        prepared: &ReplayPreparedProjection,
    ) -> Result<(), ReplayProductionError> {
        prepared.verify()?;
        let (fixed, request) = match self {
            Self::RuntimeProof { fields, .. } => {
                let structure = &prepared.entailment_structure;
                let task = ReplayTaskIdentity {
                    canonical_id: structure.canonical_id.clone(),
                    module: structure.module.clone(),
                    namespace: structure.namespace.clone(),
                    source_sha256: ReplaySha256::parse(&structure.source_digest)
                        .map_err(|_| ReplayProductionError::NestedBindingMismatch)?,
                    semantic_version: structure.semantic_version,
                    encoding_version: structure.encoding_version,
                };
                if fields.task_digest.0 != replay_task_digest(&task)
                    || fields.catalog_digest != prepared.catalog_digest
                    || fields.semantic_version != structure.semantic_version
                    || fields.encoding_version != structure.encoding_version
                {
                    return Err(ReplayProductionError::NestedBindingMismatch);
                }
                (&fields.fixed_ambient_job, &fields.request_digest)
            }
            Self::Protected { fields, .. } => (&fields.fixed_ambient_job, &fields.request_digest),
            Self::Progress { fields, .. } => (&fields.fixed_ambient_job, &fields.request_digest),
            Self::ValidatedRefutation { fields, .. } => {
                (&fields.fixed_ambient_job, &fields.request_digest)
            }
            Self::SemanticReuse { .. } => return Err(ReplayProductionError::UnsupportedSchema),
        };
        if fixed != &prepared.fixed_ambient_job || request != &prepared.control_request_digest {
            return Err(ReplayProductionError::NestedBindingMismatch);
        }
        self.verify_terminal_bindings()
    }

    fn verify_terminal_bindings(&self) -> Result<(), ReplayProductionError> {
        use crate::entailment::{ReplayProofStrategy as S, ReplaySpecializedTerminalDetail as D};
        let fail = || ReplayProductionError::NestedBindingMismatch;
        let (fixed, attempt, digest, terminal) = match self {
            Self::RuntimeProof {
                fields, terminal, ..
            } => (
                &fields.fixed_ambient_job,
                &fields.attempt,
                &fields.terminal_result_digest,
                terminal,
            ),
            Self::Progress {
                fields, terminal, ..
            } => (
                &fields.fixed_ambient_job,
                &fields.attempt,
                &fields.terminal_result_digest,
                terminal,
            ),
            Self::ValidatedRefutation {
                fields, terminal, ..
            } => (
                &fields.fixed_ambient_job,
                &fields.attempt,
                &fields.terminal_result_digest,
                terminal,
            ),
            Self::Protected { .. } | Self::SemanticReuse { .. } => return Ok(()),
        };
        if terminal.entailment_identity != fixed.entailment_identity.0
            || terminal.query_artifact != fixed.query_artifact
            || &terminal.attempt_id != attempt
            || terminal.digest() != digest.0
            || terminal
                .references
                .iter()
                .any(|a| a.backend != fixed.query_artifact.backend)
            || terminal
                .references
                .windows(2)
                .any(|w| w[0].local_id >= w[1].local_id)
            || !terminal.references.contains(&fixed.query_artifact)
        {
            return Err(fail());
        }
        let mut expected = vec![fixed.query_artifact.clone()];
        let exact_references = match self {
            Self::RuntimeProof { fields, .. } => {
                let D::Proved {
                    proof_strategy,
                    empty_check_digest,
                } = &terminal.detail
                else {
                    return Err(fail());
                };
                let winner_matches = matches!(
                    (&fields.winner, proof_strategy),
                    (ReplayProofProfile::Direct, S::Direct)
                        | (ReplayProofProfile::Casc2025, S::Casc2025)
                );
                if !winner_matches || empty_check_digest != &fields.empty_check_digest {
                    return Err(fail());
                }
                expected.extend([
                    fields.proof_artifact.clone(),
                    fields.empty_check_artifact.clone(),
                ]);
                true
            }
            Self::ValidatedRefutation { fields, .. } => {
                let validation = match (&fields.validation_identity, &terminal.detail) {
                    (ReplayValidationIdentity::Model(_), D::RefutedModel { validation_digest })
                    | (ReplayValidationIdentity::Empty(_), D::RefutedEmpty { validation_digest }) => {
                        validation_digest
                    }
                    (
                        ReplayValidationIdentity::Empty(_),
                        D::RefutedEmptyAfterProof {
                            validation_digest, ..
                        },
                    ) => {
                        let proofs = terminal
                            .references
                            .iter()
                            .filter(|a| a.kind == ReplayArtifactKind::Proof)
                            .cloned()
                            .collect::<Vec<_>>();
                        if proofs.len() != 1 {
                            return Err(fail());
                        }
                        expected.extend(proofs);
                        validation_digest
                    }
                    _ => return Err(fail()),
                };
                if validation != &fields.validation_digest {
                    return Err(fail());
                }
                expected.extend([
                    fields.source_artifact.clone(),
                    fields.validation_artifact.clone(),
                ]);
                true
            }
            Self::Progress { fields, .. } => {
                let (reason, frontier, peer, exact) = match &terminal.detail {
                    D::TimedOut {
                        next_fmb_start_size,
                        peer_failure,
                    } => (
                        ReplayInconclusiveReason::TimedOut,
                        *next_fmb_start_size,
                        peer_failure.as_ref(),
                        true,
                    ),
                    D::Failure {
                        next_fmb_start_size,
                        failure,
                    } => {
                        if failure.scope != ReplayFailureScope::LaneLocal {
                            return Err(fail());
                        }
                        let reason = if failure.kind == ReplayFailureKind::SolverUnknown {
                            ReplayInconclusiveReason::SolverUnknown
                        } else {
                            ReplayInconclusiveReason::PeerFailed
                        };
                        (reason, *next_fmb_start_size, Some(failure), true)
                    }
                    // Cancellation captures may include solver diagnostics beyond the peer failure.
                    // The complete typed terminal references remain required graph inputs.
                    D::CancelledSolver {
                        next_fmb_start_size,
                        peer_failure,
                        ..
                    } => (
                        ReplayInconclusiveReason::Cancelled,
                        *next_fmb_start_size,
                        peer_failure.as_ref(),
                        false,
                    ),
                    D::CancelledRefutation { source } => {
                        source.verify_role(
                            &fixed.query_artifact.backend,
                            ReplayArtifactKind::Model,
                        )?;
                        expected.push(source.clone());
                        (ReplayInconclusiveReason::Cancelled, None, None, true)
                    }
                    D::CancelledEmpty { retained_proof } => {
                        retained_proof.verify_role(
                            &fixed.query_artifact.backend,
                            ReplayArtifactKind::Proof,
                        )?;
                        expected.push(retained_proof.clone());
                        (ReplayInconclusiveReason::Cancelled, None, None, true)
                    }
                    D::UnvalidatedRefutation { source } => {
                        source.verify_role(
                            &fixed.query_artifact.backend,
                            ReplayArtifactKind::Model,
                        )?;
                        expected.push(source.clone());
                        (
                            ReplayInconclusiveReason::UnvalidatedRefutation,
                            None,
                            None,
                            true,
                        )
                    }
                    _ => return Err(fail()),
                };
                // Production uses next.or(retained). A missing terminal frontier must be
                // derived from the preceding adaptive attempt by the correspondence graph.
                if reason != fields.reason
                    || peer != fields.peer_failure.as_ref()
                    || frontier.is_some_and(|v| fields.next_fmb_start_size != Some(v))
                {
                    return Err(fail());
                }
                if let Some(peer) = peer {
                    expected.extend(peer.artifacts.clone());
                }
                exact
            }
            _ => unreachable!(),
        };
        expected.sort_unstable_by_key(|a| a.local_id);
        expected.dedup();
        if (exact_references && expected != terminal.references)
            || expected.iter().any(|a| !terminal.references.contains(a))
        {
            return Err(fail());
        }
        Ok(())
    }
}

fn replay_registry_entry_fields(registry: &str, rule: &str, theorem: &str) -> Value {
    json!({"domain":"whiel-framework-ii-protected-theorem-registry-entry-v2","selector_registry_digest":registry,"rule_kind":rule,"theorem_name":theorem})
}

fn replay_task_digest(task: &impl serde::Serialize) -> String {
    canonical_value_sha256(&json!({"domain":"whiel-task-identity-v1","task":task}))
}

#[cfg(test)]
mod replay_projection_tests {
    use super::*;
    use crate::failure::FailureOrigin;

    fn h() -> String {
        "4".repeat(64)
    }
    fn fixed() -> ReplayFixedAmbientJobFields {
        let scope = json!({"kind":"whiel_framework_ii_fixed_ambient_task","version":2,"semantic_version":1,"encoding_version":1,"task_canonical_id":"Example0001","task_module":"Task","task_namespace":"Task","task_source_sha256":h(),"ambient_scope":["whiel-framework-ii-fixed-ambient-scope-v1",[["rel:R:0",1]],[]]});
        let formula = json!({"kind":"whiel_fixed_ambient_clause","version":1,"formula":["true"]});
        let snapshot = json!({"kind":"whiel_fixed_ambient_snapshot","version":1,"rows":[{"clause_id":0,"level":0,"identity":formula,"canonical_source":"true"}]});
        let selector = json!({"kind":"initialization","clause_id":0});
        let obligation =
            replay_obligation_fields! {scope_identity:&scope,snapshot:&snapshot,selector:&selector};
        let worker = json!({"axioms":[{"kind":"whiel_qf_formula","version":3,"formula":["true"]}],"conjecture":{"kind":"whiel_qf_formula","version":3,"formula":["false"]}});
        let job = canonical_value_sha256(
            &replay_job_fields! {obligation_identity:&obligation,worker_entailment_identity:&worker},
        );
        let empty = replay_empty_request_fields! {scope_identity:&scope,obligation_identity:&obligation,worker_entailment_identity:&worker};
        let empty_digest = canonical_value_sha256(&empty);
        let entailment = format!("whiel-fixed-ambient-entailment-v1:sha256:{}", h());
        let preparation = replay_preparation_fields! {scope_identity:&scope,obligation_identity:&obligation,worker_entailment_identity:&worker,job_id:&job,empty_request_identity:&empty,empty_request_digest:&empty_digest,entailment_identity:&entailment};
        replay_decode(&json!({"preparation_identity":preparation,"preparation_digest":canonical_value_sha256(&preparation),"obligation_identity":obligation,"obligation_digest":canonical_value_sha256(&obligation),"worker_entailment_identity":worker,"job_id":job,"empty_request_identity":empty,"empty_request_digest":empty_digest,"entailment_identity":entailment,"query_artifact":{"backend":"0".repeat(32),"local_id":1,"kind":"Query"}})).unwrap()
    }
    fn report(detail: Option<&str>) -> FailureReport {
        FailureReport::try_new(
            FailureOrigin::EncodingPreparation,
            FailureKind::InfrastructureFailure,
            false,
            FailureScope::LaneLocal,
            detail.map(str::to_owned),
            Vec::new(),
        )
        .unwrap()
    }
    fn progress(report: Option<&FailureReport>) -> (ReplayProgressFields, Value) {
        let fixed = fixed();
        let raw = replay_progress_fields! {request_digest:h(),job_id:&fixed.job_id,semantic_vc_digest:&fixed.obligation_digest,fixed_ambient_job:&fixed,reason:"peer_failed",attempt:7u64,next_fmb_start_size:Some(2u64),previous_proof_allowance_ns:"100",current_proof_allowance_ns:"200",peer_failure:report.map(failure_fields),terminal_artifact:json!({"backend":"0".repeat(32),"local_id":2,"kind":"RuntimeTrace"}),terminal_result_digest:h()};
        let mut typed = raw.clone();
        typed["peer_failure"] =
            serde_json::to_value(report.map(replay_private_failure).transpose().unwrap()).unwrap();
        (replay_decode(&typed).unwrap(), raw)
    }
    fn object_paths(value: &Value, path: &str, result: &mut Vec<String>) {
        match value {
            Value::Object(map) => {
                result.push(path.to_owned());
                for (k, v) in map {
                    object_paths(v, &format!("{path}/{k}"), result);
                }
            }
            Value::Array(items) => {
                for (i, v) in items.iter().enumerate() {
                    object_paths(v, &format!("{path}/{i}"), result);
                }
            }
            _ => {}
        }
    }
    #[test]
    fn structural_variants_roundtrip_and_reject_wrong_arity() {
        let selections = vec![
            json!(["eq_idx", "0", "1"]),
            json!(["eq_const", "0", "data:0"]),
            json!(["and", ["eq_idx", "0", "1"], ["eq_idx", "1", "2"]]),
            json!(["or", ["eq_idx", "0", "1"], ["eq_idx", "1", "2"]]),
            json!(["not", ["eq_idx", "0", "1"]]),
        ];
        for value in &selections {
            let typed: ReplaySelection = replay_decode(value).unwrap();
            assert_eq!(serde_json::to_value(typed).unwrap(), *value);
        }
        let mut expressions = vec![
            json!(["top"]),
            json!(["empty", "0"]),
            json!(["rel", "rel:R:0"]),
            json!(["single", "data:0"]),
            json!(["proj", ["cons", "1", ["nil"]], ["top"]]),
        ];
        for tag in ["prod", "union", "diff"] {
            expressions.push(json!([tag, ["top"], ["empty", "0"]]));
        }
        for selection in selections {
            expressions.push(json!(["select", selection, ["top"]]));
        }
        for value in &expressions {
            let typed: ReplayExpression = replay_decode(value).unwrap();
            assert_eq!(serde_json::to_value(typed).unwrap(), *value);
        }
        let mut guards = vec![
            json!(["true"]),
            json!(["false"]),
            json!(["and", ["true"], ["false"]]),
            json!(["or", ["true"], ["false"]]),
            json!(["not", ["true"]]),
        ];
        for expression in expressions {
            for tag in ["eq", "subset"] {
                guards.push(json!([tag, expression, ["top"]]));
            }
            for tag in [
                "eq_empty_right",
                "eq_empty_left",
                "subset_empty_right",
                "subset_empty_left",
            ] {
                guards.push(json!([tag, expression]));
            }
        }
        for value in guards {
            let typed: ReplayGuard = replay_decode(&value).unwrap();
            assert_eq!(serde_json::to_value(typed).unwrap(), value);
            let mut bad = value.clone();
            bad.as_array_mut().unwrap().push(Value::Null);
            assert!(replay_decode::<ReplayGuard>(&bad).is_err());
        }
        assert!(replay_decode::<ReplayGuard>(&json!(["future_guard"])).is_err());
        assert!(replay_decode::<ReplayNatList>(&json!([0, 1])).is_err());
        for bad in ["", "00", "01", "-1", " 1", "1.0"] {
            assert!(replay_decode::<ReplayNatText>(&json!(bad)).is_err());
        }
    }
    #[test]
    fn every_nested_prepared_object_denies_unknown_fields() {
        let fields = fixed();
        fields.verify_bindings().unwrap();
        let value = serde_json::to_value(&fields).unwrap();
        let mut paths = Vec::new();
        object_paths(&value, "", &mut paths);
        assert!(paths.len() > 15);
        for path in paths {
            let mut bad = value.clone();
            bad.pointer_mut(&path)
                .unwrap()
                .as_object_mut()
                .unwrap()
                .insert("unexpected".into(), Value::Null);
            assert!(
                replay_decode::<ReplayFixedAmbientJobFields>(&bad).is_err(),
                "{path}"
            );
        }
        let mut bad = fields.clone();
        bad.preparation_identity.job_id = ReplaySha256("5".repeat(64));
        assert!(bad.verify_bindings().is_err());
        let mut bad = fields.clone();
        bad.obligation_identity.snapshot.rows[0].level = 1;
        assert!(bad.verify_bindings().is_err());
    }
    #[test]
    fn tags_and_admitted_booleans_are_strict() {
        for tag in ["pre", "guard", "not_theta_guard", "not_guard", "support"] {
            assert!(
                replay_decode::<ReplayTaggedPremise>(&json!({"tag":tag,"identity":null})).is_ok()
            );
            for bad in [
                json!({"tag":tag}),
                json!({"tag":tag,"identity":h()}),
                json!({"tag":tag,"identity":null,"extra":0}),
            ] {
                assert!(replay_decode::<ReplayTaggedPremise>(&bad).is_err());
            }
        }
        for tag in ["plain", "theta", "collapsed"] {
            assert!(
                replay_decode::<ReplayTaggedPremise>(&json!({"tag":tag,"identity":h()})).is_ok()
            );
            assert!(
                replay_decode::<ReplayTaggedPremise>(&json!({"tag":tag,"identity":null})).is_err()
            );
        }
        assert!(replay_decode::<ReplayAdmittedBool<true>>(&json!(false)).is_err());
        assert!(replay_decode::<ReplayAdmittedBool<false>>(&json!(true)).is_err());
        assert!(
            replay_decode::<ReplayEmptyResult>(&json!({"kind":"no_counterexample","extra":null}))
                .is_err()
        );
    }
    #[test]
    fn private_detail_rederives_old_and_live_exact_constructor_fields() {
        let owner = report(Some("worker stopped safely"));
        let (live, raw) = progress(Some(&owner));
        assert_eq!(
            replay_progress_constructor_fields(&live, Some(&owner)).unwrap(),
            raw
        );
        let mut old = live.clone();
        old.attempt = super::super::replay_identity::PhysicalAttemptId(23);
        old.terminal_artifact.local_id = 91;
        let old_raw = replay_progress_constructor_fields(&old, Some(&owner)).unwrap();
        assert_ne!(
            canonical_value_sha256(&old_raw),
            canonical_value_sha256(&raw)
        );
        assert_eq!(old_raw["peer_failure"], raw["peer_failure"]);
        assert!(
            !serde_json::to_string(&old)
                .unwrap()
                .contains("worker stopped safely")
        );
        let mut wrong = old.clone();
        wrong.peer_failure.as_mut().unwrap().detail_digest = Some(ReplaySha256("5".repeat(64)));
        assert_eq!(
            replay_progress_constructor_fields(&wrong, Some(&owner)),
            Err(ReplayProductionError::PrivateDetailMismatch)
        );
        assert!(replay_progress_constructor_fields(&old, Some(&report(Some("changed")))).is_err());
        assert!(replay_progress_constructor_fields(&old, None).is_err());
    }
    #[test]
    fn withheld_artifacts_change_outer_hash_and_private_null_is_not_empty() {
        let owner = report(Some("safe"));
        let (fields, raw) = progress(Some(&owner));
        let expected = canonical_value_sha256(&raw);
        let mut changed = fields.clone();
        changed
            .peer_failure
            .as_mut()
            .unwrap()
            .artifacts
            .push(ReplayArtifactIdentity {
                backend: ReplayBackendIdentity("0".repeat(32)),
                local_id: 77,
                kind: ReplayArtifactKind::RuntimeTrace,
            });
        assert_ne!(
            canonical_value_sha256(
                &replay_progress_constructor_fields(&changed, Some(&owner)).unwrap()
            ),
            expected
        );
        let absent = report(None);
        let empty = report(Some(""));
        let (fields, _) = progress(Some(&absent));
        assert!(replay_progress_constructor_fields(&fields, Some(&empty)).is_err());
        let mut value = serde_json::to_value(fields).unwrap();
        value["peer_failure"]
            .as_object_mut()
            .unwrap()
            .remove("detail_digest");
        assert!(replay_decode::<ReplayProgressFields>(&value).is_err());
        let (none, _) = progress(None);
        let mut value = serde_json::to_value(none).unwrap();
        value.as_object_mut().unwrap().remove("peer_failure");
        assert!(replay_decode::<ReplayProgressFields>(&value).is_err());
    }
    #[test]
    fn redacted_private_input_never_produces_commitment() {
        let secret = "sk-proj-abcdefghijklmnopqrstuvwxyz1234567890";
        let owner = report(Some(secret));
        assert_eq!(
            replay_private_failure(&owner),
            Err(ReplayProductionError::PrivateDetailRedacted)
        );
        let (fields, _) = progress(Some(&report(Some("safe"))));
        assert_eq!(
            replay_progress_constructor_fields(&fields, Some(&owner)),
            Err(ReplayProductionError::PrivateDetailRedacted)
        );
    }
    #[test]
    fn profile_and_registry_mutations_fail_owner_recomputation() {
        let profile = feedback_test_certification_profile(ProofSearchProfile::Direct);
        let mut typed: ReplayCertificationProfile =
            replay_decode(&profile.identity_fields()).unwrap();
        typed.verify().unwrap();
        typed.leancheck_invocation.arguments.push("changed".into());
        assert!(typed.verify().is_err());
        let fixed = fixed();
        let registry = canonical_value_sha256(&protected_theorem_selector_registry_fields());
        let entry = canonical_value_sha256(&replay_registry_entry_fields(
            &registry,
            "edb_precondition_initialization",
            EDB_PRECONDITION_INIT_THEOREM,
        ));
        let value = replay_protected_fields! {request_digest:h(),selector_registry_digest:&registry,rule:json!({"kind":"edb_precondition_initialization","source_conjunct":h(),"target_clause":0,"target_context":fixed.obligation_digest}),source_route_digest:h(),source_formula_digest:h(),target_vc_digest:&fixed.obligation_digest,fixed_ambient_job:&fixed,theorem_name:EDB_PRECONDITION_INIT_THEOREM,registry_entry_digest:entry};
        let mut typed: ReplayProtectedFields = replay_decode(&value).unwrap();
        typed.verify_bindings().unwrap();
        typed.theorem_name.push_str("Changed");
        assert!(typed.verify_bindings().is_err());
    }
    fn progress_projection(owner: &FailureReport) -> ReplayProductionProjection {
        // This fixture exercises the receipt constructor and cross-links. Terminal
        // private hash verification has its own owner tests in entailment/check.rs.
        let (fields, raw) = progress(Some(owner));
        let terminal = replay_decode(&json!({
            "entailment_identity":fields.fixed_ambient_job.entailment_identity,
            "attempt_id":fields.attempt,
            "query_artifact":fields.fixed_ambient_job.query_artifact,
            "constructor_references":[],
            "references":[fields.fixed_ambient_job.query_artifact],
            "detail":{"kind":"failure","next_fmb_start_size":fields.next_fmb_start_size,"failure":fields.peer_failure},
            "terminal_result_digest":fields.terminal_result_digest,
        })).unwrap();
        ReplayProductionProjection::Progress {
            fields: Box::new(fields),
            original_digest: ReplaySha256(canonical_value_sha256(&raw)),
            terminal,
        }
    }
    #[test]
    fn terminal_route_links_and_outer_hash_reject_independent_mutations() {
        let owner = report(Some("safe"));
        let projection = progress_projection(&owner);
        projection.verify_constructor(Some(&owner)).unwrap();
        let mut bad = projection.clone();
        if let ReplayProductionProjection::Progress {
            original_digest, ..
        } = &mut bad
        {
            original_digest.0 = "6".repeat(64);
        }
        assert_eq!(
            bad.verify_constructor(Some(&owner)),
            Err(ReplayProductionError::ConstructorDigestMismatch)
        );
        let mut bad = projection.clone();
        if let ReplayProductionProjection::Progress { terminal, .. } = &mut bad {
            terminal.attempt_id.0 += 1;
        }
        assert_eq!(
            bad.verify_constructor(Some(&owner)),
            Err(ReplayProductionError::NestedBindingMismatch)
        );
        let mut bad = projection.clone();
        if let ReplayProductionProjection::Progress { terminal, .. } = &mut bad {
            terminal.references.clear();
        }
        assert_eq!(
            bad.verify_constructor(Some(&owner)),
            Err(ReplayProductionError::NestedBindingMismatch)
        );
        let mut bad = projection.clone();
        if let ReplayProductionProjection::Progress { fields, .. } = &mut bad {
            fields.reason = ReplayInconclusiveReason::TimedOut;
        }
        assert!(bad.verify_constructor(Some(&owner)).is_err());
        let mut bad = projection.clone();
        if let ReplayProductionProjection::Progress { fields, .. } = &mut bad {
            fields.next_fmb_start_size = Some(3);
        }
        assert!(bad.verify_constructor(Some(&owner)).is_err());
        let value = serde_json::to_value(projection).unwrap();
        let mut paths = Vec::new();
        object_paths(&value, "", &mut paths);
        for path in paths {
            let mut bad = value.clone();
            bad.pointer_mut(&path)
                .unwrap()
                .as_object_mut()
                .unwrap()
                .insert("extra".into(), Value::Null);
            assert!(
                replay_decode::<ReplayProductionProjection>(&bad).is_err(),
                "{path}"
            );
        }
    }
    fn artifact(local_id: u64, kind: &str) -> Value {
        json!({"backend":"0".repeat(32),"local_id":local_id,"kind":kind})
    }
    fn terminal_for(fields: &Value, detail: Value, references: Value) -> Value {
        let constructor_references = references
            .as_array()
            .unwrap()
            .iter()
            .filter(|a| **a != fields["fixed_ambient_job"]["query_artifact"])
            .cloned()
            .collect::<Vec<_>>();
        json!({"entailment_identity":fields["fixed_ambient_job"]["entailment_identity"],"attempt_id":fields["attempt"],"query_artifact":fields["fixed_ambient_job"]["query_artifact"],"constructor_references":constructor_references,"references":references,"detail":detail,"terminal_result_digest":fields["terminal_result_digest"]})
    }
    fn assert_route_schema(value: Value) {
        let projection: ReplayProductionProjection = replay_decode(&value).unwrap();
        projection.verify_constructor(None).unwrap();
        assert_eq!(serde_json::to_value(projection).unwrap(), value);
        let mut paths = Vec::new();
        object_paths(&value, "", &mut paths);
        for path in paths {
            let mut bad = value.clone();
            bad.pointer_mut(&path)
                .unwrap()
                .as_object_mut()
                .unwrap()
                .insert("unexpected".into(), Value::Null);
            assert!(
                replay_decode::<ReplayProductionProjection>(&bad).is_err(),
                "{} {path}",
                value["route"]
            );
        }
    }
    #[test]
    fn proof_protected_refutation_and_reuse_routes_are_strict_and_rederive() {
        let fixed = fixed();
        let mut empty = ReplayEmptyCheckIdentity {
            kind: ReplayEmptyCheckTag,
            version: ReplayVersion,
            empty_request_identity: fixed.empty_request_identity.clone(),
            obligation_identity: fixed.obligation_identity.clone(),
            worker_entailment_identity: fixed.worker_entailment_identity.clone(),
            decision_definition: ReplayEmptyDefinition,
            result: ReplayEmptyResult::NoCounterexample {},
        };
        for (profile, strategy) in [
            (ProofSearchProfile::Direct, "direct"),
            (ProofSearchProfile::Casc2025, "casc_2025"),
        ] {
            let fields = replay_runtime_proof_fields! {task_digest:h(),catalog_digest:h(),artifact_backend_digest:canonical_value_sha256(&json!({"domain":"whiel-artifact-backend-v1","task_digest":h(),"backend":"0".repeat(32)})),semantic_version:1,encoding_version:1,framework_ii_context_digest:&fixed.obligation_digest,request_digest:h(),job_id:&fixed.job_id,semantic_vc_digest:&fixed.obligation_digest,query_digest:h(),query_bytes:42,attempt:7,terminal_result_digest:h(),empty_check_digest:replay_sha(&empty).unwrap(),winner:strategy,runtime_invocation:feedback_test_invocation().identity_fields(),certification_profile:feedback_test_certification_profile(profile).identity_fields(),fixed_ambient_job:&fixed,query_artifact:&fixed.query_artifact,proof_artifact:artifact(2,"Proof"),terminal_artifact:artifact(4,"RuntimeTrace"),empty_check_artifact:artifact(3,"EmptyInstanceCheck")};
            let terminal = terminal_for(
                &fields,
                json!({"kind":"proved","proof_strategy":strategy,"empty_check_digest":fields["empty_check_digest"]}),
                json!([
                    fixed.query_artifact,
                    artifact(2, "Proof"),
                    artifact(3, "EmptyInstanceCheck")
                ]),
            );
            assert_route_schema(
                json!({"route":"runtime_proof","original_digest":canonical_value_sha256(&fields),"fields":fields,"terminal":terminal}),
            );
        }
        empty.result = ReplayEmptyResult::Counterexample {
            nullary_assignment: Vec::new(),
        };
        let fields = replay_refutation_fields! {request_digest:h(),job_id:&fixed.job_id,semantic_vc_digest:&fixed.obligation_digest,fixed_ambient_job:&fixed,attempt:7,terminal_artifact:artifact(4,"RuntimeTrace"),terminal_result_digest:h(),source_artifact:artifact(2,"EmptyInstanceCheck"),validation_identity:&empty,validation_digest:replay_sha(&empty).unwrap(),validation_artifact:artifact(3,"Witness")};
        let terminal = terminal_for(
            &fields,
            json!({"kind":"refuted_empty","validation_digest":fields["validation_digest"]}),
            json!([
                fixed.query_artifact,
                artifact(2, "EmptyInstanceCheck"),
                artifact(3, "Witness")
            ]),
        );
        assert_route_schema(
            json!({"route":"validated_refutation","original_digest":canonical_value_sha256(&fields),"fields":fields,"terminal":terminal}),
        );
        let registry = canonical_value_sha256(&protected_theorem_selector_registry_fields());
        let entry = canonical_value_sha256(&replay_registry_entry_fields(
            &registry,
            "edb_precondition_initialization",
            EDB_PRECONDITION_INIT_THEOREM,
        ));
        let fields = replay_protected_fields! {request_digest:h(),selector_registry_digest:registry,rule:json!({"kind":"edb_precondition_initialization","source_conjunct":h(),"target_clause":0,"target_context":fixed.obligation_digest}),source_route_digest:h(),source_formula_digest:h(),target_vc_digest:&fixed.obligation_digest,fixed_ambient_job:&fixed,theorem_name:EDB_PRECONDITION_INIT_THEOREM,registry_entry_digest:entry};
        assert_route_schema(
            json!({"route":"protected","original_digest":canonical_value_sha256(&fields),"fields":fields}),
        );
        for role in ["initialization", "maintenance", "termination"] {
            let semantic = json!({"kind":"whiel_framework_ii_semantic_vc_key","version":9,"role":role,"task_identity":{"canonical_id":"task","module":"Task","namespace":"Task","source_sha256":h(),"semantic_version":1,"encoding_version":1},"scope_identity":fixed.obligation_identity.scope_identity,"conjecture":{"identity_sha256":if role=="termination"{"post_prime".to_owned()}else{h()}},"tagged_premises":[]});
            for kind in [
                "proof_subsumption",
                "refutation_subsumption",
                "inconclusive_entry",
            ] {
                let fields = replay_reuse_fields! {reuse_kind:kind,semantic_vc_key:canonical_value_sha256(&semantic),matched_tagged_premises:Vec::<ReplayTaggedPremise>::new(),original_request_digest:h(),original_evidence_identity:h()};
                assert_route_schema(
                    json!({"route":"semantic_reuse","original_digest":canonical_value_sha256(&fields),"fields":fields,"current_request_digest":h(),"semantic_key_identity":semantic}),
                );
            }
        }
    }
    #[test]
    fn hidden_carrier_schema_and_tuple_semantics_are_checked() {
        let scope = fixed().obligation_identity.scope_identity;
        let value = json!({"kind":"whiel_framework_ii_finite_interpretation","version":1,"schema_relations":[{"key":"rel:R:0","arity":1}],"carrier_identity":{"kind":"whiel_framework_ii_finite_carrier","version":1,"carrier_keys":["data:0"]},"instance_identity":{"kind":"whiel_source_instance","version":1,"relations":[{"key":"rel:R:0","arity":1,"rows":[["data:0"]]}]}});
        let typed: ReplayInterpretationIdentity = replay_decode(&value).unwrap();
        typed.verify_scope(&scope).unwrap();
        let mut bad = typed.clone();
        bad.carrier_identity.carrier_keys.clear();
        assert!(bad.verify_scope(&scope).is_err());
        let mut bad = typed.clone();
        bad.instance_identity.relations[0].rows[0].push("data:0".into());
        assert!(bad.verify_scope(&scope).is_err());
        let mut bad = typed;
        bad.schema_relations[0].arity = 2;
        assert!(bad.verify_scope(&scope).is_err());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Wrap a clause request as the subject the production pipeline now
    /// takes.
    fn clause_subject(request: &FrameworkIICheckRequest) -> FrameworkIICheckSubject {
        FrameworkIICheckSubject::Clause(request.clone())
    }

    fn semantic_key_of(request: &FrameworkIICheckRequest) -> Value {
        semantic_vc_key_identity(&clause_subject(request))
    }

    fn conjecture_of(request: &FrameworkIICheckRequest) -> Arc<str> {
        conjecture_identity_of(&clause_subject(request))
    }

    /// A Lean-style `axiom_tags` table that issues exactly the tags Rust
    /// computes for `request`, under the short TPTP names the fixture
    /// proofs cite. Building fixtures this way is what makes the live
    /// path's tagged-set equality `debug_assert!` meaningful in the suites:
    /// a fixture whose table disagreed with `tagged_premise_set` would trip
    /// it (Pass 7.5c-2 verification bullet).
    fn axiom_tag_table_for(request: &FrameworkIICheckRequest) -> FrameworkIIAxiomTagTable {
        let entries = tagged_premise_set(request)
            .into_iter()
            .map(|tag| (Arc::from(axiom_tag_fixture_name(&tag).as_str()), tag))
            .collect();
        FrameworkIIAxiomTagTable::from_entries(entries)
            .expect("fixture axiom names are unique per tag")
    }

    fn axiom_tag_fixture_name(tag: &FrameworkIIPremiseTag) -> String {
        match tag {
            FrameworkIIPremiseTag::Pre => "ax_pre".to_owned(),
            FrameworkIIPremiseTag::Guard => "ax_guard".to_owned(),
            FrameworkIIPremiseTag::NotThetaGuard => "ax_not_theta_guard".to_owned(),
            FrameworkIIPremiseTag::NotGuard => "ax_not_guard".to_owned(),
            FrameworkIIPremiseTag::Support => "support_adom".to_owned(),
            FrameworkIIPremiseTag::Plain(identity) => format!("ax_plain_{identity}"),
            FrameworkIIPremiseTag::Theta(identity) => format!("ax_theta_{identity}"),
            FrameworkIIPremiseTag::Collapsed(identity) => format!("ax_collapsed_{identity}"),
        }
    }

    /// The fixture table for the termination request over `core`.
    fn termination_axiom_tag_table(core: &LeveledCandidateSnapshot) -> FrameworkIIAxiomTagTable {
        let entries = termination_tagged_premise_set(core)
            .into_iter()
            .map(|tag| (Arc::from(axiom_tag_fixture_name(&tag).as_str()), tag))
            .collect();
        FrameworkIIAxiomTagTable::from_entries(entries)
            .expect("fixture axiom names are unique per tag")
    }
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};

    use crate::artifact::{ArtifactBackendOwner, ArtifactStoreConfig, new_artifact_store};
    use crate::encoding::{
        FixedAmbientEncodingContext, FixedAmbientPreparedBodyData, FixedAmbientPreparedSupportData,
        FixedAmbientWorkerBinding, FixedAmbientWorkerCommand, FixedAmbientWorkerPoolConfig,
        PreparedBodyRef, new_fixed_ambient_encoding_context,
    };
    use crate::entailment::assembly::assemble_fixed_ambient_entailment_with_support;
    use crate::failure::FailureOrigin;
    use crate::framework2::catalog::{ExtendedClauseOrigin, LeveledClauseCatalog};
    use crate::framework2::ledger::LevelAttemptLedger;
    use crate::framework2::search::{OverallOperation, await_overall_operation};
    use crate::framework2::snapshot::LeveledCandidateSnapshot;
    use crate::framework2::types::{
        ExtendedClause, FixedAmbientTaskScope, FrameworkIILevel, FrameworkIIRelation,
    };
    use crate::runtime::{RuntimeResourcePolicy, create_general_solver_admission};
    use crate::task::SynthesisTask;

    static NEXT_TEST_DIRECTORY: AtomicU64 = AtomicU64::new(0);

    struct TestDirectory(PathBuf);

    impl TestDirectory {
        fn new(label: &str) -> Self {
            let ordinal = NEXT_TEST_DIRECTORY.fetch_add(1, Ordering::Relaxed);
            let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("target/framework2-production-unit-tests")
                .join(format!("{label}_{}_{}", std::process::id(), ordinal));
            fs::create_dir_all(&path).expect("create fixed-ambient production test directory");
            Self(path)
        }

        fn path(&self) -> &Path {
            &self.0
        }
    }

    impl Drop for TestDirectory {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    struct InjectedPreCheckSemantic {
        outcome: FrameworkIIPreCheckOutcome,
        prepare_calls: usize,
        prepare_delay: Duration,
        prepare_completed: Option<Arc<AtomicBool>>,
        downstream_called: Arc<AtomicBool>,
    }

    impl InjectedPreCheckSemantic {
        fn new(outcome: FrameworkIIPreCheckOutcome, downstream_called: Arc<AtomicBool>) -> Self {
            Self {
                outcome,
                prepare_calls: 0,
                prepare_delay: Duration::ZERO,
                prepare_completed: None,
                downstream_called,
            }
        }

        fn with_blocking_prepare(mut self, delay: Duration, completed: Arc<AtomicBool>) -> Self {
            self.prepare_delay = delay;
            self.prepare_completed = Some(completed);
            self
        }
    }

    impl FrameworkIISemanticAdapter for InjectedPreCheckSemantic {
        fn prepare<'a>(
            &'a mut self,
            _subject: &'a FrameworkIICheckSubject,
            _admission: &'a SolverAdmission,
            _artifacts: &'a ArtifactStore,
            _cancellation: &'a CancellationToken,
        ) -> Pin<
            Box<
                dyn Future<Output = Result<FrameworkIIPreCheckOutcome, FrameworkIIStateError>>
                    + Send
                    + 'a,
            >,
        > {
            self.prepare_calls += 1;
            let outcome = self.outcome.clone();
            let delay = self.prepare_delay;
            let completed = self.prepare_completed.clone();
            Box::pin(async move {
                if !delay.is_zero() {
                    std::thread::sleep(delay);
                }
                if let Some(completed) = completed {
                    completed.store(true, Ordering::SeqCst);
                }
                Ok(outcome)
            })
        }

        fn check_empty<'a>(
            &'a mut self,
            _prepared: &'a PreparedFrameworkIIEntailment,
            _attempt: &'a EntailmentAttemptScope,
            _admission: &'a SolverAdmission,
            _cancellation: &'a CancellationToken,
        ) -> Pin<
            Box<
                dyn Future<
                        Output = Result<
                            FrameworkIIEmptyCheckOutcome,
                            FrameworkIISemanticCheckError,
                        >,
                    > + Send
                    + 'a,
            >,
        > {
            self.downstream_called.store(true, Ordering::Relaxed);
            Box::pin(async { panic!("pre-check result reached empty-instance checking") })
        }

        fn validate_model<'a>(
            &'a mut self,
            _prepared: &'a PreparedFrameworkIIEntailment,
            _attempt: &'a EntailmentAttemptScope,
            _model: VampireModel,
            _admission: &'a SolverAdmission,
            _cancellation: &'a CancellationToken,
        ) -> Pin<
            Box<
                dyn Future<
                        Output = Result<
                            FrameworkIIModelValidationOutcome,
                            FrameworkIISemanticCheckError,
                        >,
                    > + Send
                    + 'a,
            >,
        > {
            // A scripted adapter never validates: every nonempty model stays
            // fail-closed inconclusive.
            self.downstream_called.store(true, Ordering::Relaxed);
            Box::pin(async { Ok(FrameworkIIModelValidationOutcome::NotRefutation) })
        }
    }

    fn production_test_task() -> SynthesisTask {
        SynthesisTask::from_json(
            r#"{
              "format_version":3,
              "semantic_version":1,
              "encoding_version":1,
              "identity":{
                "canonical_id":"FrameworkIIProductionPreCheckTest",
                "module":"Whiel.Test.FrameworkIIProductionPreCheckTest",
                "namespace":"Whiel.Test.FrameworkIIProductionPreCheckTest",
                "source_sha256":"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
              },
              "schema":{
                "expression":"Whiel.Test.FrameworkIIProductionPreCheckTest.programSchema",
                "display":"{R}"
              },
              "original":{
                "pre":{"expression":"Whiel.Test.FrameworkIIProductionPreCheckTest.inputPre","display":"true"},
                "command":{"expression":"Whiel.Test.FrameworkIIProductionPreCheckTest.inputCmd","display":"SKIP"},
                "post":{"expression":"Whiel.Test.FrameworkIIProductionPreCheckTest.inputPost","display":"true"}
              },
              "preprocessed":{
                "pre":{"expression":"Whiel.Test.FrameworkIIProductionPreCheckTest.inputPreproc.loopPre","display":"true"},
                "command":{"expression":"Whiel.Test.FrameworkIIProductionPreCheckTest.inputPreproc.loopCmd","display":"SKIP"},
                "post":{"expression":"Whiel.Test.FrameworkIIProductionPreCheckTest.inputPreproc.loopPost","display":"true"}
              },
              "preprocessing_evidence":{
                "expression":"Whiel.Test.FrameworkIIProductionPreCheckTest.inputPreproc"
              },
              "solver":{
                "schema_relations":[{"key":"rel:R:0","arity":1}],
                "task_constants":[],
                "preprocessed_pre":{
                  "source_id":"task.preprocessed_pre",
                  "expression":"Whiel.Test.FrameworkIIProductionPreCheckTest.inputPreproc.loopPre",
                  "no_bound_expression":"Whiel.Test.FrameworkIIProductionPreCheckTest.inputPreproc.loopPre_noBound",
                  "constants":[],
                  "relations":[]
                },
                "preprocessed_post":{
                  "source_id":"task.preprocessed_post",
                  "expression":"Whiel.Test.FrameworkIIProductionPreCheckTest.inputPreproc.loopPost",
                  "no_bound_expression":"Whiel.Test.FrameworkIIProductionPreCheckTest.inputPreproc.loopPost_noBound",
                  "constants":[],
                  "relations":[]
                },
                "loop_guard":{"source_id":"task.loop_guard","constants":[],"relations":[]},
                "negated_loop_guard":{"source_id":"task.negated_loop_guard","constants":[],"relations":[]}
              }
            }"#,
        )
        .unwrap()
    }

    fn production_test_request() -> (SynthesisTask, FrameworkIICheckRequest) {
        let task = production_test_task();
        let source = FrameworkIIRelation::new(
            task.solver_relations()[0].key().clone(),
            task.solver_relations()[0].arity(),
        );
        let scope = FixedAmbientTaskScope::new(
            task.identity().clone(),
            json!(["framework-ii-production-pre-check", ["rel:R:0", 1]]),
            json!([]),
            vec![source.clone()],
            vec![source],
            Vec::new(),
        );
        let formula_identity = json!(["production-pre-check-clause", "rel:R:0"]);
        let clause = ExtendedClause::new(
            scope.clone(),
            formula_identity.clone(),
            "production-pre-check-clause".to_string(),
            serde_json::to_string(&formula_identity).unwrap(),
            vec!["rel:R:0".to_string()],
            false,
            FrameworkIILevel::ZERO,
        );
        let catalog = LeveledClauseCatalog::new(scope.clone(), "1".repeat(64)).unwrap();
        let registered = catalog
            .register_batch(0, [(clause, ExtendedClauseOrigin::Submitted)])
            .unwrap();
        let clause_id = registered.ids()[0];
        let snapshot = Arc::new(
            LeveledCandidateSnapshot::build(
                &catalog,
                None,
                BTreeMap::from([(clause_id, FrameworkIILevel::ZERO)]),
            )
            .unwrap(),
        );
        let request = FrameworkIICheckRequest::new(
            0,
            clause_id,
            FrameworkIILevel::ZERO,
            FrameworkIICheckRole::Initialization,
            snapshot,
            false,
        )
        .unwrap();
        (task, request)
    }

    async fn applied_pre_check_fixture(
        task: &SynthesisTask,
        request: &FrameworkIICheckRequest,
        artifacts: &ArtifactStore,
        admission: &SolverAdmission,
    ) -> (FixedAmbientEncodingContext, PreparedFrameworkIIEntailment) {
        applied_pre_check_fixture_with_axiom_tags(
            task,
            request,
            artifacts,
            admission,
            FrameworkIIAxiomTagTable::from_entries(Vec::new()).unwrap(),
        )
        .await
    }

    /// As [`applied_pre_check_fixture`], but with a caller-chosen synthetic
    /// `axiom_tags` table — this fixture builds
    /// `PreparedFrameworkIIEntailment` directly rather than assembling one,
    /// so the table is whatever this call passes.
    async fn applied_pre_check_fixture_with_axiom_tags(
        task: &SynthesisTask,
        request: &FrameworkIICheckRequest,
        artifacts: &ArtifactStore,
        admission: &SolverAdmission,
        axiom_tags: FrameworkIIAxiomTagTable,
    ) -> (FixedAmbientEncodingContext, PreparedFrameworkIIEntailment) {
        applied_pre_check_fixture_for_subject(
            task,
            &clause_subject(request),
            artifacts,
            admission,
            axiom_tags,
        )
        .await
    }

    /// The subject-level fixture: serves the termination request as well as
    /// an ordinary clause request.
    async fn applied_pre_check_fixture_for_subject(
        task: &SynthesisTask,
        request: &FrameworkIICheckSubject,
        artifacts: &ArtifactStore,
        admission: &SolverAdmission,
        axiom_tags: FrameworkIIAxiomTagTable,
    ) -> (FixedAmbientEncodingContext, PreparedFrameworkIIEntailment) {
        let relation = task.solver_relations()[0].key().clone();
        let binding = FixedAmbientWorkerBinding::for_test(
            task.identity().clone(),
            request.snapshot().scope().identity().clone(),
        );
        let workers = FixedAmbientWorkerPoolConfig::new(
            FixedAmbientWorkerCommand::new("/bin/true", PathBuf::from("/")),
            1,
        )
        .unwrap();
        let encoding = new_fixed_ambient_encoding_context(
            binding,
            [relation.clone()],
            Vec::<crate::task::ConstantKey>::new(),
            workers,
        )
        .unwrap();
        let (revision, mappings) = encoding
            .name_snapshot([relation], Vec::<crate::task::ConstantKey>::new())
            .unwrap();
        let relation_bindings = mappings
            .into_iter()
            .map(|mapping| json!({"key": mapping.key, "name": mapping.tptp_name}))
            .collect::<Vec<_>>();
        let goal_data: FixedAmbientPreparedBodyData = serde_json::from_value(json!({
            "source_id": "framework-ii-production-test-goal",
            "source_kind": "quantifier_free",
            "exact_constant_keys": [],
            "body": "$true",
            "referenced_relations": [],
            "referenced_constants": [],
        }))
        .unwrap();
        let goal = encoding.adopt_body(goal_data, revision).unwrap();
        let support_data: FixedAmbientPreparedSupportData = serde_json::from_value(json!({
            "constant_keys": [],
            "adom_body": "$true",
            "distinct_bodies": [],
            "referenced_relations": relation_bindings,
            "referenced_constants": [],
        }))
        .unwrap();
        let support = encoding.adopt_support(support_data, revision).unwrap();
        let entailment_identity = json!({
            "axioms": [],
            "conjecture": {"kind": "production_test_goal"},
        });
        let entailment = assemble_fixed_ambient_entailment_with_support(
            &encoding,
            admission,
            artifacts,
            entailment_identity.clone(),
            Vec::<PreparedBodyRef>::new(),
            vec![goal],
            support,
            &CancellationToken::new(),
        )
        .await
        .unwrap();

        let obligation_identity = json!({
            "kind": "whiel_fixed_ambient_obligation",
            "version": FIXED_AMBIENT_OBLIGATION_IDENTITY_VERSION,
            "scope_identity": request.snapshot().scope().identity(),
            "snapshot": request.snapshot().worker_identity(),
            "selector": request.selector().identity(),
        });
        let prepared = PreparedFrameworkIIEntailment::from_fixed_ambient_job(
            request,
            obligation_identity,
            entailment_identity,
            entailment,
            axiom_tags,
        )
        .unwrap();
        (encoding, prepared)
    }

    #[tokio::test(flavor = "current_thread")]
    async fn fixed_ambient_preparation_rejects_legacy_and_tampered_worker_identity() {
        let directory = TestDirectory::new("fixed-ambient-preparation-strictness");
        let (task, request) = production_test_request();
        let (owner, artifacts) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(directory.path().join("artifacts")),
        )
        .unwrap();
        let admission =
            create_general_solver_admission(RuntimeResourcePolicy::agent_only(1, 1).unwrap())
                .unwrap();
        let (encoding, prepared) =
            applied_pre_check_fixture(&task, &request, &artifacts, &admission).await;

        let rebuild = |obligation_identity: Value, entailment_identity: Value| {
            PreparedFrameworkIIEntailment::from_fixed_ambient_job(
                &clause_subject(&request),
                obligation_identity,
                entailment_identity,
                prepared.entailment().clone(),
                prepared.axiom_tags().clone(),
            )
        };

        let mut legacy = prepared.base_obligation_identity().clone();
        legacy["kind"] = json!("whiel_framework_ii_semantic_job");
        legacy["schema_kind"] = json!("extended");
        assert!(rebuild(legacy, prepared.entailment_identity().clone(),).is_err());

        let mut wrong_snapshot = prepared.base_obligation_identity().clone();
        wrong_snapshot["snapshot"] = json!({"kind": "stale_snapshot"});
        assert!(rebuild(wrong_snapshot, prepared.entailment_identity().clone(),).is_err());

        let mut extra_entailment = prepared.entailment_identity().clone();
        extra_entailment["schema_kind"] = json!("extended");
        assert!(
            rebuild(
                prepared.base_obligation_identity().clone(),
                extra_entailment
            )
            .is_err()
        );

        let wrong_entailment_shape = json!({
            "axioms": {},
            "conjecture": {"kind": "production_test_goal"},
        });
        assert!(
            rebuild(
                prepared.base_obligation_identity().clone(),
                wrong_entailment_shape,
            )
            .is_err()
        );

        let mut stale_request = request.clone();
        stale_request.replace_request_digest_for_legacy_test("f".repeat(64));
        assert!(
            PreparedFrameworkIIEntailment::from_fixed_ambient_job(
                &clause_subject(&stale_request),
                prepared.base_obligation_identity().clone(),
                prepared.entailment_identity().clone(),
                prepared.entailment().clone(),
                prepared.axiom_tags().clone(),
            )
            .is_err()
        );

        assert_eq!(
            prepared.prepare_request_identity()["obligation_identity"],
            *prepared.base_obligation_identity()
        );
        assert_eq!(
            prepared.prepare_request_identity()["worker_entailment_identity"],
            *prepared.entailment_identity()
        );

        drop(prepared);
        encoding.shutdown().await.unwrap();
        drop(encoding);
        drop(artifacts);
        owner.settle().unwrap();
    }

    fn test_certification_profiles() -> FrameworkIICertificationProfiles {
        let invocation = |profile: &str| {
            SolverInvocationIdentity::from_parts(
                Arc::from("vampire"),
                Arc::from("fixture-leancheck"),
                Arc::from("/fixture/pinned-vampire"),
                Arc::from("a".repeat(64)),
                Arc::from(std::env::consts::OS),
                Arc::from(std::env::consts::ARCH),
                vec![Arc::from(profile)],
            )
            .unwrap()
        };
        let profile = |kind, name: &str| {
            LeancheckCertificationProfile::new(
                kind,
                format!("fixture-{name}-v1"),
                invocation(name),
                None,
                "b".repeat(64),
                "c".repeat(64),
                "d".repeat(64),
                "e".repeat(64),
                "f".repeat(64),
            )
            .unwrap()
        };
        FrameworkIICertificationProfiles::new(
            profile(ProofSearchProfile::Direct, "direct"),
            profile(ProofSearchProfile::Casc2025, "casc-2025"),
        )
        .unwrap()
    }

    fn sentinel_vampire(directory: &Path) -> (VampireWorkerCommand, PathBuf) {
        let executable = directory.join("vampire-must-not-launch.sh");
        let launch_marker = directory.join("vampire-launched");
        fs::write(
            &executable,
            format!(
                "#!/bin/sh\nprintf launched > {}\nexit 1\n",
                launch_marker.display()
            ),
        )
        .expect("write sentinel Vampire executable");
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(&executable, fs::Permissions::from_mode(0o700))
                .expect("make sentinel Vampire executable");
        }
        (VampireWorkerCommand::new(executable), launch_marker)
    }

    fn model_vampire(directory: &Path) -> VampireWorkerCommand {
        let executable = directory.join("vampire-model.sh");
        fs::write(
            &executable,
            "#!/bin/sh\nprintf '%s\\n' '% SZS status CounterSatisfiable for problem'\nprintf '%s\\n' '% SZS output start FiniteModel for problem'\nprintf '%s\\n' 'fof(fixture_model, fi_domain, ! [X] : X = d0).'\nprintf '%s\\n' '% SZS output end FiniteModel for problem'\n",
        )
        .expect("write model Vampire executable");
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(&executable, fs::Permissions::from_mode(0o700))
                .expect("make model Vampire executable");
        }
        VampireWorkerCommand::new(executable)
    }

    fn production_test_config(
        artifacts: ArtifactStore,
        command: VampireWorkerCommand,
    ) -> FrameworkIIProductionCheckConfig {
        production_test_config_with_cancellation(artifacts, command, CancellationToken::new())
    }

    /// The same configuration bound to an admission authority the caller
    /// already holds. A test whose key is launched more than once needs
    /// this: a retry re-renders its own query through the preparation's
    /// encoding context, which admits only its own authority.
    fn production_test_config_with_admission(
        artifacts: ArtifactStore,
        command: VampireWorkerCommand,
        admission: SolverAdmission,
    ) -> FrameworkIIProductionCheckConfig {
        FrameworkIIProductionCheckConfig::new_proof_only_not_a_campaign_configuration(
            artifacts,
            admission,
            VampireSearchBudget::finite(Duration::from_secs(1)),
            command,
            CancellationToken::new(),
            "fixture-vampire",
            test_certification_profiles(),
        )
        .unwrap()
    }

    fn production_test_config_with_cancellation(
        artifacts: ArtifactStore,
        command: VampireWorkerCommand,
        cancellation: CancellationToken,
    ) -> FrameworkIIProductionCheckConfig {
        // Proof lane only: these tests drive the retry ladder, the semantic
        // dictionary and the receipt machinery against a stand-in that answers
        // one proof call, and a racing finite-model launch would ask it a
        // question it has no reply for.
        FrameworkIIProductionCheckConfig::new_proof_only_not_a_campaign_configuration(
            artifacts,
            create_general_solver_admission(RuntimeResourcePolicy::agent_only(1, 1).unwrap())
                .unwrap(),
            VampireSearchBudget::finite(Duration::from_secs(1)),
            command,
            cancellation,
            "fixture-vampire",
            test_certification_profiles(),
        )
        .unwrap()
    }

    fn assert_no_solver_side_effects(
        checker: &FrameworkIIProductionChecker<InjectedPreCheckSemantic>,
        artifacts: &ArtifactStore,
        launch_marker: &Path,
    ) {
        assert_eq!(checker.semantic.prepare_calls, 1);
        assert!(!checker.semantic.downstream_called.load(Ordering::Relaxed));
        assert!(checker.pending.is_empty());
        assert!(checker.retries.is_empty());
        assert!(checker.complete.is_empty());
        assert!(!launch_marker.exists());
        assert_eq!(
            artifacts.next_attempt_id().unwrap().get(),
            0,
            "a pre-check-only result allocated a solver attempt"
        );
    }

    fn settle_test_artifacts<S>(
        checker: FrameworkIIProductionChecker<S>,
        owner: ArtifactBackendOwner,
    ) {
        drop(checker);
        owner.settle().unwrap();
    }

    fn assert_exact_failure_report(actual: &FailureReport, expected: &FailureReport) {
        assert_eq!(actual.origin(), expected.origin());
        assert_eq!(actual.kind(), expected.kind());
        assert_eq!(actual.retryable(), expected.retryable());
        assert_eq!(actual.scope(), expected.scope());
        assert_eq!(actual.detail(), expected.detail());
        assert_eq!(actual.artifact_references(), expected.artifact_references());
    }

    fn semantic_key_with_changed_entailment(
        identity: &Value,
        alternate_query: ArtifactRef,
    ) -> Value {
        let mut changed = identity.clone();
        let fields = changed
            .as_object_mut()
            .expect("the semantic-check key is an object");
        fields.insert(
            "entailment_identity".to_string(),
            Value::String("digest-collision-entailment".to_string()),
        );
        fields.insert(
            "query_artifact".to_string(),
            artifact_fields(alternate_query),
        );
        changed
    }

    #[test]
    fn the_retry_frontier_retains_the_highest_fmb_start_size() {
        let config_budget = VampireSearchBudget::finite(Duration::from_secs(10));
        assert_eq!(config_budget.initial_limit(), Some(Duration::from_secs(10)));
        let mut frontier = FrameworkIIRetryFrontier {
            semantic_key_identity: Arc::new(json!({"semantic_check": "test"})),
            next_fmb_start_size: Some(FmbSize::ONE),
        };
        frontier.record_inconclusive(FmbSize::new(4));
        assert_eq!(frontier.next_fmb_start_size.unwrap().get(), 4);
        frontier.record_inconclusive(FmbSize::new(6));
        assert_eq!(frontier.next_fmb_start_size.unwrap().get(), 6);
        // A lower reported frontier never lowers the retained one, and an
        // absent one never clears it.
        frontier.record_inconclusive(FmbSize::new(5));
        assert_eq!(frontier.next_fmb_start_size.unwrap().get(), 6);
        frontier.record_inconclusive(None);
        assert_eq!(frontier.next_fmb_start_size.unwrap().get(), 6);
    }

    #[test]
    fn the_retry_policy_is_a_strictly_increasing_allowance_list() {
        assert!(FrameworkIIRetryPolicy::new([]).is_err());
        assert!(FrameworkIIRetryPolicy::new([Duration::ZERO]).is_err());
        assert!(
            FrameworkIIRetryPolicy::new([Duration::from_secs(10), Duration::from_secs(10)])
                .is_err(),
            "equal neighbours are not strictly increasing"
        );
        assert!(
            FrameworkIIRetryPolicy::new([Duration::from_secs(10), Duration::from_secs(5)]).is_err()
        );
        let policy =
            FrameworkIIRetryPolicy::new([Duration::from_secs(10), Duration::from_secs(30)])
                .unwrap();
        assert_eq!(policy.granted_launches(), 2);
        assert_eq!(policy.allowance_after(0), Some(Duration::from_secs(10)));
        assert_eq!(policy.allowance_after(1), Some(Duration::from_secs(30)));
        assert_eq!(policy.allowance_after(2), None);
        // Milestone 7.5 review, finding 5: the CASC portfolio is a run
        // option and it is disabled by default, so a retried launch's whole
        // allowance is direct and there is no retry-added portion for
        // `ProofCascPolicy` to split.
        assert_eq!(policy.casc_portfolio(), CascPortfolioPolicy::Disabled);
        let direct_only = policy.budget_after(1).unwrap();
        assert_eq!(direct_only.initial_limit(), Some(Duration::from_secs(30)));
        assert_eq!(direct_only.total_limit(), Some(Duration::from_secs(30)));
        // Enabled, the baseline stays the direct-search portion so
        // `ProofCascPolicy` splits exactly the retry-added part beyond `a_1`.
        let escalating = policy
            .clone()
            .with_casc_portfolio(CascPortfolioPolicy::Enabled);
        let budget = escalating.budget_after(1).unwrap();
        assert_eq!(budget.initial_limit(), Some(Duration::from_secs(10)));
        assert_eq!(budget.total_limit(), Some(Duration::from_secs(30)));
    }

    /// `houdini.tex` Section 4.7: only a launch that actually reported on
    /// the obligation consumes one of the key's allowances. A cancellation
    /// and a peer's failure stop the launch before the solver says anything
    /// about it, so they record no inconclusive dictionary entry and leave
    /// the key's launch count where they found it — the next epoch
    /// relaunches under the same allowance. `Suspended` never launched at
    /// all.
    /// Milestone 7.5 review, finding 5. "Runs direct only" is enforced, not
    /// merely intended: with the run's CASC portfolio disabled — the default
    /// — a launch's whole allowance is direct *and* the command the launch
    /// runs under has the host's own `ProofCascPolicy` cleared, so no launch
    /// of the run can produce a `casc_2025` winner however the host
    /// configured the solver. Enabled, both halves come back.
    #[test]
    fn a_direct_only_run_clears_the_casc_portfolio_from_its_launch_command() {
        let directory = TestDirectory::new("direct-only-launch-command");
        let (task, _request) = production_test_request();
        let (owner, artifacts) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(directory.path().join("artifacts")),
        )
        .unwrap();
        // A host that asked for the CASC portfolio explicitly.
        let command = VampireWorkerCommand::new(directory.path().join("vampire"))
            .with_proof_casc_policy(crate::vampire::ProofCascPolicy::CLI_DEFAULT)
            .unwrap();
        assert!(!command.proof_casc_policy().is_disabled());
        let config = production_test_config(artifacts.clone(), command);

        // The default run: direct only, both halves.
        assert_eq!(
            config.retry_policy().casc_portfolio(),
            CascPortfolioPolicy::Disabled
        );
        assert!(
            config.launch_command().proof_casc_policy().is_disabled(),
            "a direct-only run never launches the portfolio"
        );
        let budget = config.retry_policy().budget_after(1).unwrap();
        assert_eq!(
            budget.initial_limit(),
            budget.total_limit(),
            "a direct-only launch has no retry-added portion for the CASC split to reach"
        );

        // The same config with the portfolio enabled.
        let mut enabled = config.clone();
        enabled.retry_policy = enabled
            .retry_policy
            .clone()
            .with_casc_portfolio(CascPortfolioPolicy::Enabled);
        assert!(!enabled.launch_command().proof_casc_policy().is_disabled());
        let budget = enabled.retry_policy().budget_after(1).unwrap();
        assert!(budget.initial_limit() < budget.total_limit());

        owner.settle().unwrap();
    }

    /// A launch whose solver stopped itself at the limit it was given is
    /// this launch's timeout, and a timeout climbs the ladder: the next
    /// epoch relaunches the same key under the next rung. A lane fault is
    /// still a peer failure, which does not.
    #[test]
    fn a_self_limited_launch_is_a_timeout_and_climbs_the_retry_ladder() {
        assert_eq!(
            lane_failure_reason(FailureKind::CheckTimeout),
            FrameworkIIInconclusiveReason::TimedOut
        );
        assert_eq!(
            lane_failure_reason(FailureKind::SolverUnknown),
            FrameworkIIInconclusiveReason::SolverUnknown
        );
        for kind in [
            FailureKind::ProcessFailure,
            FailureKind::MalformedResult,
            FailureKind::ConcurrentWorkerFailures,
        ] {
            assert_eq!(
                lane_failure_reason(kind),
                FrameworkIIInconclusiveReason::PeerFailed,
                "{kind:?}"
            );
        }
        assert!(FrameworkIIInconclusiveReason::TimedOut.consumes_retry_allowance());
        let baseline = Duration::from_secs(30);
        let policy = FrameworkIIRetryPolicy::from_budget_and_increments(
            VampireSearchBudget::finite(baseline),
            [baseline, baseline],
        )
        .unwrap();
        assert_eq!(policy.allowance_after(0), Some(baseline));
        assert_eq!(policy.allowance_after(1), Some(2 * baseline));
        assert_eq!(policy.allowance_after(2), Some(3 * baseline));
    }

    #[test]
    fn only_a_reporting_launch_consumes_a_retry_allowance() {
        for reason in [
            FrameworkIIInconclusiveReason::TimedOut,
            FrameworkIIInconclusiveReason::SolverUnknown,
            FrameworkIIInconclusiveReason::UnvalidatedRefutation,
        ] {
            assert!(reason.consumes_retry_allowance(), "{reason:?}");
        }
        for reason in [
            FrameworkIIInconclusiveReason::Cancelled,
            FrameworkIIInconclusiveReason::PeerFailed,
            FrameworkIIInconclusiveReason::Suspended,
        ] {
            assert!(!reason.consumes_retry_allowance(), "{reason:?}");
        }
    }

    #[test]
    fn the_default_retry_policy_maps_the_legacy_increment_ladder() {
        let baseline = Duration::from_secs(7);
        let policy = FrameworkIIRetryPolicy::from_budget_and_increments(
            VampireSearchBudget::finite(baseline),
            [baseline, baseline],
        )
        .unwrap();
        assert_eq!(
            policy.allowances(),
            [baseline, 2 * baseline, 3 * baseline],
            "a_1 = the budget's total (= initial for a finite budget) and \
             a_k = a_(k-1) + increment_k"
        );
        assert_eq!(policy.baseline(), baseline);
        // A cumulative budget's first launch keeps the whole total,
        // CASC-added share included, exactly as it did before the retry
        // contract existed; `initial` stays the direct-search baseline the
        // `ProofCascPolicy` splits at.
        let cumulative = FrameworkIIRetryPolicy::from_budget_and_increments(
            VampireSearchBudget::cumulative(baseline, 4 * baseline),
            [baseline],
        )
        .unwrap();
        assert_eq!(cumulative.allowances(), [4 * baseline, 5 * baseline]);
        assert_eq!(cumulative.baseline(), baseline);
        let cumulative = cumulative.with_casc_portfolio(CascPortfolioPolicy::Enabled);
        let first = cumulative.budget_after(0).unwrap();
        assert_eq!(first.initial_limit(), Some(baseline));
        assert_eq!(
            first.total_limit(),
            Some(4 * baseline),
            "the first launch runs under the run budget it was configured with"
        );
        assert!(
            FrameworkIIRetryPolicy::from_budget_and_increments(
                VampireSearchBudget::finite(baseline),
                [Duration::ZERO]
            )
            .is_err()
        );
        assert!(
            FrameworkIIRetryPolicy::from_budget_and_increments(
                VampireSearchBudget::UNBOUNDED,
                [baseline]
            )
            .is_err()
        );
    }

    /// The production ladder a campaign runs under, stated end to end: a
    /// 30 s baseline with two 30 s increments, the portfolio enabled, and
    /// the shares the command line defaults to. The direct limit is a
    /// prefix cutoff and the CASC figure is the nominal tail the split
    /// reserves for the portfolio.
    #[test]
    fn the_campaign_ladder_splits_each_launch_between_direct_and_the_portfolio() {
        let baseline = Duration::from_secs(30);
        let policy = FrameworkIIRetryPolicy::from_budget_and_increments(
            VampireSearchBudget::finite(baseline),
            [baseline, baseline],
        )
        .unwrap()
        .with_casc_portfolio(CascPortfolioPolicy::Enabled);
        let shares = crate::vampire::ProofCascPolicy::CLI_DEFAULT;
        let millis = |amount| Duration::from_millis(amount);
        for (launch, allowance, direct, casc) in [
            (0, 30_000, 22_500, 7_500),
            (1, 60_000, 30_000, 30_000),
            (2, 90_000, 37_500, 52_500),
        ] {
            let budget = policy.budget_after(launch).unwrap();
            assert_eq!(budget.initial_limit(), Some(baseline));
            assert_eq!(budget.total_limit(), Some(millis(allowance)));
            assert_eq!(
                shares.split(
                    budget.total_limit().unwrap(),
                    budget.total_limit().unwrap() - budget.initial_limit().unwrap(),
                ),
                (millis(direct), millis(casc)),
                "launch {launch}"
            );
        }
        assert_eq!(policy.allowance_after(3), None);

        // Disabled, every launch is a plain finite allowance with no
        // retry-added portion for the split to reach.
        let direct_only = policy.with_casc_portfolio(CascPortfolioPolicy::Disabled);
        for launch in 0..3 {
            let budget = direct_only.budget_after(launch).unwrap();
            assert_eq!(budget.initial_limit(), budget.total_limit());
        }
    }

    #[tokio::test(flavor = "current_thread")]
    async fn fixed_ambient_unvalidated_model_stays_inconclusive() {
        let directory = TestDirectory::new("fixed-ambient-model-fails-closed");
        let (task, request) = production_test_request();
        let (owner, artifacts) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(directory.path().join("artifacts")),
        )
        .unwrap();
        let admission =
            create_general_solver_admission(RuntimeResourcePolicy::agent_only(1, 1).unwrap())
                .unwrap();
        let config = FrameworkIIProductionCheckConfig::new(
            artifacts.clone(),
            admission,
            VampireSearchBudget::finite(Duration::from_secs(1)),
            FmbOptions::default(),
            model_vampire(directory.path()),
            CancellationToken::new(),
            "fixture-vampire",
            test_certification_profiles(),
        )
        .unwrap();
        let (encoding, prepared) =
            applied_pre_check_fixture(&task, &request, &artifacts, config.admission()).await;
        let downstream_called = Arc::new(AtomicBool::new(false));
        let semantic = InjectedPreCheckSemantic::new(
            FrameworkIIPreCheckOutcome::Applied(prepared),
            Arc::clone(&downstream_called),
        );
        let mut checker = FrameworkIIProductionChecker::new(semantic, config);

        let execution = checker.check(request).await.unwrap();

        let FrameworkIICheckExecution::Applied(FrameworkIICheckOutcome::Inconclusive {
            reason,
            progress,
        }) = execution
        else {
            panic!("a fixed-ambient nonempty model must be inconclusive")
        };
        assert_eq!(reason, FrameworkIIInconclusiveReason::UnvalidatedRefutation);
        assert!(progress.progress().is_some());
        assert!(
            progress.preparation_time().is_some(),
            "a launched check that reached worker preparation must carry a measured preparation time"
        );
        assert!(
            downstream_called.load(Ordering::Relaxed),
            "a nonempty model must be handed to Lean validation"
        );
        assert!(checker.pending.is_empty());
        assert!(checker.complete.is_empty());

        encoding.shutdown().await.unwrap();
        settle_test_artifacts(checker, owner);
    }

    #[tokio::test(flavor = "current_thread")]
    async fn overall_deadline_stops_after_blocked_first_check_before_followup_or_publication() {
        let directory = TestDirectory::new("blocked-applied-check-overall-deadline");
        let (task, request) = production_test_request();
        let (owner, artifacts) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(directory.path().join("artifacts")),
        )
        .unwrap();
        let (command, launch_marker) = sentinel_vampire(directory.path());
        let cancellation = CancellationToken::new();
        let config = production_test_config_with_cancellation(
            artifacts.clone(),
            command,
            cancellation.clone(),
        );
        let (encoding, prepared) =
            applied_pre_check_fixture(&task, &request, &artifacts, config.admission()).await;
        artifacts.wait_for_background_work().await;
        let artifacts_before = artifacts.diagnostics();
        assert!(artifacts_before.required_payloads_published > 0);

        let prepare_completed = Arc::new(AtomicBool::new(false));
        let downstream_called = Arc::new(AtomicBool::new(false));
        let semantic = InjectedPreCheckSemantic::new(
            FrameworkIIPreCheckOutcome::Applied(prepared),
            downstream_called,
        )
        .with_blocking_prepare(Duration::from_millis(250), Arc::clone(&prepare_completed));
        let mut checker = FrameworkIIProductionChecker::new(semantic, config);
        let followup_started = Arc::new(AtomicBool::new(false));
        let first_cancelled = Arc::new(AtomicBool::new(false));
        let unexpected_first_result = Arc::new(AtomicBool::new(false));
        let operation_joined = Arc::new(AtomicBool::new(false));
        let followup_started_in_operation = Arc::clone(&followup_started);
        let first_cancelled_in_operation = Arc::clone(&first_cancelled);
        let unexpected_first_result_in_operation = Arc::clone(&unexpected_first_result);
        let operation_joined_in_operation = Arc::clone(&operation_joined);
        let first_request = request.clone();
        let absolute_deadline = tokio::time::Instant::now() + Duration::from_millis(100);
        assert!(cancellation.bind_absolute_deadline(absolute_deadline));
        let operation = async {
            match checker.check(first_request).await {
                Err(FrameworkIIStateError::Cancelled) => {
                    first_cancelled_in_operation.store(true, Ordering::SeqCst);
                }
                Ok(_) => {
                    unexpected_first_result_in_operation.store(true, Ordering::SeqCst);
                    followup_started_in_operation.store(true, Ordering::SeqCst);
                    let _ = checker.check(request).await;
                }
                Err(_) => {
                    unexpected_first_result_in_operation.store(true, Ordering::SeqCst);
                }
            }
            operation_joined_in_operation.store(true, Ordering::SeqCst);
        };

        let outcome = await_overall_operation(operation, &cancellation, absolute_deadline).await;

        assert!(matches!(outcome, OverallOperation::TimedOut));
        assert!(cancellation.is_cancelled());
        assert!(cancellation.deadline_elapsed());
        assert!(prepare_completed.load(Ordering::SeqCst));
        assert!(first_cancelled.load(Ordering::SeqCst));
        assert!(!unexpected_first_result.load(Ordering::SeqCst));
        assert!(!followup_started.load(Ordering::SeqCst));
        assert!(operation_joined.load(Ordering::SeqCst));
        assert_eq!(checker.semantic.prepare_calls, 1);
        assert!(!checker.semantic.downstream_called.load(Ordering::SeqCst));
        assert!(checker.pending.is_empty());
        assert!(checker.retries.is_empty());
        assert!(checker.complete.is_empty());
        assert!(!launch_marker.exists());
        assert_eq!(artifacts.next_attempt_id().unwrap().get(), 0);
        artifacts.wait_for_background_work().await;
        let artifacts_after = artifacts.diagnostics();
        assert_eq!(
            artifacts_after.required_payloads_published,
            artifacts_before.required_payloads_published,
        );
        assert_eq!(
            artifacts_after.required_payload_files_created,
            artifacts_before.required_payload_files_created,
        );
        assert_eq!(
            artifacts_after.ready_query_artifacts,
            artifacts_before.ready_query_artifacts,
        );

        encoding.shutdown().await.unwrap();
        settle_test_artifacts(checker, owner);
    }

    #[tokio::test(flavor = "current_thread")]
    async fn failed_pre_check_preserves_every_failure_report_field() {
        let directory = TestDirectory::new("failed-pre-check");
        let (task, request) = production_test_request();
        let (owner, artifacts) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(directory.path().join("artifacts")),
        )
        .unwrap();
        let first_reference = artifacts
            .publish(
                ArtifactKind::FailureDiagnostic,
                b"first typed failure artifact".to_vec().into_boxed_slice(),
            )
            .unwrap();
        let second_reference = artifacts
            .publish(
                ArtifactKind::Witness,
                b"second typed failure artifact".to_vec().into_boxed_slice(),
            )
            .unwrap();
        let expected = FailureReport::try_new(
            FailureOrigin::EncodingPreparation,
            FailureKind::InfrastructureFailure,
            true,
            FailureScope::RunGlobal,
            Some("injected typed pre-check failure".to_string()),
            vec![first_reference, second_reference],
        )
        .unwrap();
        let (command, launch_marker) = sentinel_vampire(directory.path());
        let downstream_called = Arc::new(AtomicBool::new(false));
        let semantic = InjectedPreCheckSemantic::new(
            FrameworkIIPreCheckOutcome::Failure(expected.clone()),
            downstream_called,
        );
        let mut checker = FrameworkIIProductionChecker::new(
            semantic,
            production_test_config(artifacts.clone(), command),
        );

        let execution = checker.check(request).await.unwrap();

        let actual = match execution {
            FrameworkIICheckExecution::Failure(actual) => actual,
            other => panic!("expected the exact typed failure, got {other:?}"),
        };
        assert_exact_failure_report(&actual, &expected);
        assert_no_solver_side_effects(&checker, &artifacts, &launch_marker);
        settle_test_artifacts(checker, owner);
    }

    /// Pass 7.5d, one launch per key per epoch: a batch whose leader for a
    /// key came back a nonlogical `Failure` recorded no dictionary entry
    /// and did not mark the key launched, so the deferred duplicate must be
    /// answered with the leader's own failure rather than re-planned into a
    /// second launch of the same key in the same epoch.
    #[tokio::test(flavor = "current_thread")]
    async fn a_deferred_duplicate_of_a_failed_leader_is_not_launched_again() {
        let directory = TestDirectory::new("deferred-duplicate-after-leader-failure");
        let (task, request) = production_test_request();
        let (owner, artifacts) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(directory.path().join("artifacts")),
        )
        .unwrap();
        // The same clause, role, level and snapshot at a later ledger
        // ordinal: a distinct request that denotes the identical semantic
        // verification condition, which is exactly what the batch defers.
        let duplicate = FrameworkIICheckRequest::new(
            request.attempt_ordinal() + 1,
            request.clause(),
            request.level(),
            request.role(),
            Arc::clone(request.snapshot()),
            false,
        )
        .unwrap();
        assert_ne!(request.request_digest(), duplicate.request_digest());
        assert_eq!(
            semantic_vc_key_identity(&clause_subject(&request)),
            semantic_vc_key_identity(&clause_subject(&duplicate)),
        );

        let expected = FailureReport::try_new(
            FailureOrigin::EncodingPreparation,
            FailureKind::InfrastructureFailure,
            true,
            FailureScope::RunGlobal,
            Some("injected leader preparation failure".to_string()),
            Vec::new(),
        )
        .unwrap();
        let (command, launch_marker) = sentinel_vampire(directory.path());
        let downstream_called = Arc::new(AtomicBool::new(false));
        let semantic = InjectedPreCheckSemantic::new(
            FrameworkIIPreCheckOutcome::Failure(expected.clone()),
            downstream_called,
        );
        let mut checker = FrameworkIIProductionChecker::new(
            semantic,
            production_test_config(artifacts.clone(), command),
        );

        let executions = checker.check_batch(vec![request, duplicate]).await.unwrap();

        assert_eq!(executions.len(), 2);
        for execution in &executions {
            let FrameworkIICheckExecution::Failure(actual) = execution else {
                panic!("both slots must carry the leader's failure, got {execution:?}")
            };
            assert_exact_failure_report(actual, &expected);
        }
        assert_eq!(
            checker.semantic.prepare_calls, 1,
            "the deferred duplicate must not launch the key a second time"
        );
        assert_eq!(checker.batches_total(), 1);
        assert_eq!(checker.batched_checks_total(), 2);
        assert!(checker.launched_this_epoch.is_empty());
        assert!(checker.dictionary_entry_summary().is_empty());
        assert_no_solver_side_effects(&checker, &artifacts, &launch_marker);
        settle_test_artifacts(checker, owner);
    }

    #[tokio::test(flavor = "current_thread")]
    async fn solver_pipeline_failure_preserves_every_field_and_reference() {
        let directory = TestDirectory::new("solver-pipeline-failure");
        let (task, request) = production_test_request();
        let (owner, artifacts) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(directory.path().join("artifacts")),
        )
        .unwrap();
        let (command, launch_marker) = sentinel_vampire(directory.path());
        let config = production_test_config(artifacts.clone(), command);
        let (encoding, prepared) =
            applied_pre_check_fixture(&task, &request, &artifacts, config.admission()).await;
        let first_reference = artifacts
            .publish(
                ArtifactKind::FailureDiagnostic,
                b"first solver-pipeline failure artifact"
                    .to_vec()
                    .into_boxed_slice(),
            )
            .unwrap();
        let second_reference = artifacts
            .publish(
                ArtifactKind::Witness,
                b"second solver-pipeline failure artifact"
                    .to_vec()
                    .into_boxed_slice(),
            )
            .unwrap();
        let expected = FailureReport::try_new(
            FailureOrigin::VampireProofSearch,
            FailureKind::InfrastructureFailure,
            false,
            FailureScope::RunGlobal,
            Some("injected run-global solver-pipeline failure".to_string()),
            vec![first_reference, second_reference],
        )
        .unwrap();
        config.admission().poison(expected.clone());
        let payloads_before = artifacts.diagnostics().required_payloads_published;
        let downstream_called = Arc::new(AtomicBool::new(false));
        let semantic = InjectedPreCheckSemantic::new(
            FrameworkIIPreCheckOutcome::Applied(prepared),
            downstream_called,
        );
        let mut checker = FrameworkIIProductionChecker::new(semantic, config);

        let execution = checker.check(request).await.unwrap();

        let actual = match execution {
            FrameworkIICheckExecution::Failure(actual) => actual,
            other => panic!("expected the exact solver-pipeline failure, got {other:?}"),
        };
        assert_exact_failure_report(&actual, &expected);
        assert_eq!(checker.semantic.prepare_calls, 1);
        assert!(!checker.semantic.downstream_called.load(Ordering::Relaxed));
        assert!(checker.pending.is_empty());
        assert!(checker.retries.is_empty());
        assert!(checker.complete.is_empty());
        assert!(!launch_marker.exists());
        assert_eq!(
            artifacts.diagnostics().required_payloads_published,
            payloads_before,
            "a solver-pipeline failure published false terminal authority"
        );

        encoding.shutdown().await.unwrap();
        settle_test_artifacts(checker, owner);
    }

    #[tokio::test(flavor = "current_thread")]
    async fn settled_artifact_publication_failure_preserves_the_exact_report() {
        let directory = TestDirectory::new("settled-artifact-publication-failure");
        let (task, request) = production_test_request();
        let (owner, artifacts) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(directory.path().join("artifacts")),
        )
        .unwrap();
        let (command, launch_marker) = sentinel_vampire(directory.path());
        let config = production_test_config(artifacts.clone(), command);
        let (encoding, prepared) =
            applied_pre_check_fixture(&task, &request, &artifacts, config.admission()).await;
        let downstream_called = Arc::new(AtomicBool::new(false));
        let semantic = InjectedPreCheckSemantic::new(
            FrameworkIIPreCheckOutcome::Applied(prepared),
            downstream_called,
        );
        let payloads_before = artifacts.diagnostics().required_payloads_published;
        encoding.shutdown().await.unwrap();
        owner.settle().unwrap();
        assert!(artifacts.diagnostics().settled);
        // The exact fixed-ambient query artifact is already published while
        // the backend is open, so the first settled-store touch is attempt
        // allocation. That store report must reach the caller unchanged.
        let expected = FailureReport::artifact(
            FailureKind::InfrastructureFailure,
            FailureScope::RunGlobal,
            "cannot allocate an attempt after artifact settlement begins",
        );
        let mut checker = FrameworkIIProductionChecker::new(semantic, config);

        let execution = checker.check(request).await.unwrap();

        let actual = match execution {
            FrameworkIICheckExecution::Failure(actual) => actual,
            other => panic!("expected the exact artifact settlement failure, got {other:?}"),
        };
        assert_exact_failure_report(&actual, &expected);
        assert_eq!(checker.semantic.prepare_calls, 1);
        assert!(!checker.semantic.downstream_called.load(Ordering::Relaxed));
        assert!(checker.pending.is_empty());
        assert!(checker.retries.is_empty());
        assert!(checker.complete.is_empty());
        assert!(!launch_marker.exists());
        assert_eq!(
            artifacts.diagnostics().required_payloads_published,
            payloads_before,
            "failed receipt publication created false theorem authority"
        );
    }

    #[tokio::test(flavor = "current_thread")]
    async fn retry_key_digest_collision_with_changed_entailment_fails_closed() {
        let directory = TestDirectory::new("retry-key-digest-collision");
        let (task, request) = production_test_request();
        let (owner, artifacts) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(directory.path().join("artifacts")),
        )
        .unwrap();
        let (command, launch_marker) = sentinel_vampire(directory.path());
        let config = production_test_config(artifacts.clone(), command);
        let (encoding, prepared) =
            applied_pre_check_fixture(&task, &request, &artifacts, config.admission()).await;
        let semantic_key_identity = runtime_semantic_check_key_identity(&prepared);
        let semantic_key: Arc<str> = Arc::from(canonical_value_sha256(&semantic_key_identity));
        let alternate_query = artifacts
            .publish(
                ArtifactKind::Query,
                b"changed query for a simulated digest collision"
                    .to_vec()
                    .into_boxed_slice(),
            )
            .unwrap();
        let colliding_identity =
            semantic_key_with_changed_entailment(&semantic_key_identity, alternate_query);
        assert_ne!(
            canonical_value_sha256(&colliding_identity),
            semantic_key.as_ref(),
            "the test must explicitly force the wrong identity into the digest bucket"
        );
        let retry = FrameworkIIRetryFrontier::new(&config, &colliding_identity);
        let downstream_called = Arc::new(AtomicBool::new(false));
        let semantic = InjectedPreCheckSemantic::new(
            FrameworkIIPreCheckOutcome::Applied(prepared),
            downstream_called,
        );
        let mut checker = FrameworkIIProductionChecker::new(semantic, config);
        checker.retries.insert(semantic_key, retry);

        let error = checker.check(request).await.unwrap_err();

        assert_eq!(
            error,
            FrameworkIIStateError::InvalidEvidence(
                "an adaptive-retry digest matched another semantic check"
            )
        );
        assert_eq!(checker.semantic.prepare_calls, 1);
        assert!(!checker.semantic.downstream_called.load(Ordering::Relaxed));
        assert!(checker.pending.is_empty());
        assert!(checker.complete.is_empty());
        assert_eq!(checker.retries.len(), 1);
        assert!(!launch_marker.exists());
        assert_eq!(artifacts.next_attempt_id().unwrap().get(), 0);

        encoding.shutdown().await.unwrap();
        settle_test_artifacts(checker, owner);
    }

    #[tokio::test(flavor = "current_thread")]
    async fn completed_key_digest_collision_with_changed_entailment_fails_closed() {
        let directory = TestDirectory::new("completed-key-digest-collision");
        let (task, request) = production_test_request();
        let (owner, artifacts) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(directory.path().join("artifacts")),
        )
        .unwrap();
        let (command, launch_marker) = sentinel_vampire(directory.path());
        let config = production_test_config(artifacts.clone(), command);
        let (encoding, prepared) =
            applied_pre_check_fixture(&task, &request, &artifacts, config.admission()).await;
        let semantic_key_identity = runtime_semantic_check_key_identity(&prepared);
        let complete_key =
            runtime_complete_check_key(&clause_subject(&request), &semantic_key_identity);
        let alternate_query = artifacts
            .publish(
                ArtifactKind::Query,
                b"changed completed query for a simulated digest collision"
                    .to_vec()
                    .into_boxed_slice(),
            )
            .unwrap();
        let colliding_identity =
            semantic_key_with_changed_entailment(&semantic_key_identity, alternate_query);
        assert_ne!(
            canonical_value_sha256(&colliding_identity),
            canonical_value_sha256(&semantic_key_identity),
            "the test must explicitly force the wrong identity into the digest bucket"
        );
        let colliding_outcome = FrameworkIICheckOutcome::Proved(
            FrameworkIICheckEvidence::new(
                request.request_digest(),
                "completed-result-from-another-entailment",
            )
            .unwrap(),
        );
        let downstream_called = Arc::new(AtomicBool::new(false));
        let semantic = InjectedPreCheckSemantic::new(
            FrameworkIIPreCheckOutcome::Applied(prepared),
            downstream_called,
        );
        let mut checker = FrameworkIIProductionChecker::new(semantic, config);
        checker.complete.insert(
            complete_key,
            CompletedFrameworkIICheck {
                subject: clause_subject(&request),
                semantic_key_identity: Arc::new(colliding_identity),
                outcome: colliding_outcome,
            },
        );

        let error = checker.check(request).await.unwrap_err();

        assert_eq!(
            error,
            FrameworkIIStateError::InvalidEvidence(
                "a completed-check digest matched another structural request or semantic check"
            )
        );
        assert_eq!(checker.semantic.prepare_calls, 1);
        assert!(!checker.semantic.downstream_called.load(Ordering::Relaxed));
        assert!(checker.pending.is_empty());
        assert!(checker.retries.is_empty());
        assert_eq!(checker.complete.len(), 1);
        assert!(!launch_marker.exists());
        assert_eq!(artifacts.next_attempt_id().unwrap().get(), 0);

        encoding.shutdown().await.unwrap();
        settle_test_artifacts(checker, owner);
    }

    // ------------------------------------------------------------
    // Semantic Verification-Condition Reuse
    // ------------------------------------------------------------

    /// Build an independent scope, catalog, and multi-clause snapshot for
    /// semantic-key tests. Each `(label, minimum_level)` in `clauses` is
    /// registered as its own distinct Lean-issued clause identity; `placement`
    /// selects which labels are placed, and at which level, in the returned
    /// snapshot.
    fn multi_clause_snapshot(
        task: &SynthesisTask,
        clauses: &[(&str, u64)],
        placement: &[(&str, u64)],
        max_level: u64,
    ) -> (
        BTreeMap<String, crate::houdini::ClauseId>,
        Arc<LeveledCandidateSnapshot>,
    ) {
        let source = FrameworkIIRelation::new(
            task.solver_relations()[0].key().clone(),
            task.solver_relations()[0].arity(),
        );
        let scope = FixedAmbientTaskScope::new(
            task.identity().clone(),
            json!(["framework-ii-semantic-reuse-multi-clause", ["rel:R:0", 1]]),
            json!([]),
            vec![source.clone()],
            vec![source],
            Vec::new(),
        );
        let catalog = LeveledClauseCatalog::new(scope.clone(), "1".repeat(64)).unwrap();
        let mut ids = BTreeMap::new();
        for (ordinal, (label, minimum_level)) in clauses.iter().enumerate() {
            let formula_identity = json!(["semantic-reuse-multi-clause-test", label]);
            let clause = ExtendedClause::new(
                scope.clone(),
                formula_identity,
                (*label).to_string(),
                (*label).to_string(),
                vec!["rel:R:0".to_string()],
                false,
                FrameworkIILevel::new(*minimum_level),
            );
            let registered = catalog
                .register_batch(ordinal as u64, [(clause, ExtendedClauseOrigin::Submitted)])
                .unwrap();
            ids.insert((*label).to_string(), registered.ids()[0]);
        }
        let level_of = placement
            .iter()
            .map(|(label, level)| (ids[*label], FrameworkIILevel::new(*level)))
            .collect::<BTreeMap<_, _>>();
        let snapshot = Arc::new(
            LeveledCandidateSnapshot::build(
                &catalog,
                Some(FrameworkIILevel::new(max_level)),
                level_of,
            )
            .unwrap(),
        );
        (ids, snapshot)
    }

    #[test]
    fn semantic_vc_key_ignores_unrelated_placement_and_tracks_every_vc_defining_field() {
        let task = production_test_task();

        // An unrelated clause `H`, placed at or above the checked level, must
        // not affect the key: it never appears in Lean's `LeveledFamily.below`
        // premises for `C` at level 1.
        let (ids_absent, snapshot_absent) = multi_clause_snapshot(
            &task,
            &[("C", 1), ("P", 0), ("H", 1)],
            &[("C", 1), ("P", 0)],
            2,
        );
        let (ids_present, snapshot_present) = multi_clause_snapshot(
            &task,
            &[("C", 1), ("P", 0), ("H", 1)],
            &[("C", 1), ("P", 0), ("H", 1)],
            2,
        );
        let request_absent = FrameworkIICheckRequest::new(
            0,
            ids_absent["C"],
            FrameworkIILevel::new(1),
            FrameworkIICheckRole::Initialization,
            snapshot_absent,
            false,
        )
        .unwrap();
        let request_present = FrameworkIICheckRequest::new(
            0,
            ids_present["C"],
            FrameworkIILevel::new(1),
            FrameworkIICheckRole::Initialization,
            snapshot_present,
            false,
        )
        .unwrap();
        let key_absent = semantic_key_of(&request_absent);
        let key_present = semantic_key_of(&request_present);
        assert_eq!(
            key_absent, key_present,
            "a clause at or above the checked level must never affect the semantic VC key"
        );
        assert_eq!(
            key_absent["version"],
            json!(FRAMEWORK_II_RUNTIME_CACHE_IDENTITY_VERSION)
        );

        // The exact same same-level clause `H`, however, DOES change the key
        // for a maintenance check: Lean's `maintenanceVC` axioms come from
        // `family.upTo clause.level` (`LeveledFamily.upTo`), which includes
        // every clause at the checked level — not just those strictly below
        // it — so a same-level candidate that an initialization key must
        // ignore is exactly what a maintenance key must track.
        let (ids_maint_absent, snapshot_maint_absent) = multi_clause_snapshot(
            &task,
            &[("C", 1), ("P", 0), ("H", 1)],
            &[("C", 1), ("P", 0)],
            2,
        );
        let (ids_maint_present, snapshot_maint_present) = multi_clause_snapshot(
            &task,
            &[("C", 1), ("P", 0), ("H", 1)],
            &[("C", 1), ("P", 0), ("H", 1)],
            2,
        );
        let request_maint_absent = FrameworkIICheckRequest::new(
            0,
            ids_maint_absent["C"],
            FrameworkIILevel::new(1),
            FrameworkIICheckRole::Maintenance,
            snapshot_maint_absent,
            false,
        )
        .unwrap();
        let request_maint_present = FrameworkIICheckRequest::new(
            0,
            ids_maint_present["C"],
            FrameworkIILevel::new(1),
            FrameworkIICheckRole::Maintenance,
            snapshot_maint_present,
            false,
        )
        .unwrap();
        assert_ne!(
            semantic_key_of(&request_maint_absent),
            semantic_key_of(&request_maint_present),
            "a different clause placed at the checked level must change a maintenance key, \
             even though the same placement never changes an initialization key"
        );

        // A clause strictly ABOVE the checked level must still never affect
        // either role's key.
        let (ids_maint_above_absent, snapshot_maint_above_absent) = multi_clause_snapshot(
            &task,
            &[("C", 1), ("P", 0), ("G", 2)],
            &[("C", 1), ("P", 0)],
            3,
        );
        let (ids_maint_above_present, snapshot_maint_above_present) = multi_clause_snapshot(
            &task,
            &[("C", 1), ("P", 0), ("G", 2)],
            &[("C", 1), ("P", 0), ("G", 2)],
            3,
        );
        let request_maint_above_absent = FrameworkIICheckRequest::new(
            0,
            ids_maint_above_absent["C"],
            FrameworkIILevel::new(1),
            FrameworkIICheckRole::Maintenance,
            snapshot_maint_above_absent,
            false,
        )
        .unwrap();
        let request_maint_above_present = FrameworkIICheckRequest::new(
            0,
            ids_maint_above_present["C"],
            FrameworkIILevel::new(1),
            FrameworkIICheckRole::Maintenance,
            snapshot_maint_above_present,
            false,
        )
        .unwrap();
        assert_eq!(
            semantic_key_of(&request_maint_above_absent),
            semantic_key_of(&request_maint_above_present),
            "a clause strictly above the checked level must never affect a maintenance key either"
        );

        // A different premise clause identity changes the key.
        let (ids_other_premise, snapshot_other_premise) =
            multi_clause_snapshot(&task, &[("C", 1), ("Q", 0)], &[("C", 1), ("Q", 0)], 2);
        let request_other_premise = FrameworkIICheckRequest::new(
            0,
            ids_other_premise["C"],
            FrameworkIILevel::new(1),
            FrameworkIICheckRole::Initialization,
            snapshot_other_premise,
            false,
        )
        .unwrap();
        assert_ne!(
            key_absent,
            semantic_key_of(&request_other_premise),
            "a changed premise identity must change the key"
        );

        // The same premise clause identity placed at a different
        // strictly-below level does NOT change the key (Pass 7.5b): the
        // tagged premise set records `theta(identity)` for every clause
        // strictly below the checked level, with no per-clause sub-level
        // component — exactly mirroring Lean's `ProphecyContext.build`,
        // which folds every strictly-below clause into one theta list
        // without further stratifying by exact sub-level.
        let (ids_premise_low, snapshot_premise_low) =
            multi_clause_snapshot(&task, &[("C", 2), ("P", 0)], &[("C", 2), ("P", 0)], 2);
        let (ids_premise_high, snapshot_premise_high) =
            multi_clause_snapshot(&task, &[("C", 2), ("P", 0)], &[("C", 2), ("P", 1)], 2);
        let request_premise_low = FrameworkIICheckRequest::new(
            0,
            ids_premise_low["C"],
            FrameworkIILevel::new(2),
            FrameworkIICheckRole::Initialization,
            snapshot_premise_low,
            false,
        )
        .unwrap();
        let request_premise_high = FrameworkIICheckRequest::new(
            0,
            ids_premise_high["C"],
            FrameworkIILevel::new(2),
            FrameworkIICheckRole::Initialization,
            snapshot_premise_high,
            false,
        )
        .unwrap();
        assert_eq!(
            semantic_key_of(&request_premise_low),
            semantic_key_of(&request_premise_high),
            "a strictly-below premise's own sub-level is not part of the tagged key, only its identity"
        );

        // A different conjecture clause (checking `D` instead of `C` in the
        // same cohort) changes the key.
        let (ids_two_conjectures, snapshot_two_conjectures) = multi_clause_snapshot(
            &task,
            &[("C", 1), ("P", 0), ("D", 1)],
            &[("C", 1), ("P", 0), ("D", 1)],
            2,
        );
        let request_conjecture_c = FrameworkIICheckRequest::new(
            0,
            ids_two_conjectures["C"],
            FrameworkIILevel::new(1),
            FrameworkIICheckRole::Initialization,
            Arc::clone(&snapshot_two_conjectures),
            false,
        )
        .unwrap();
        let request_conjecture_d = FrameworkIICheckRequest::new(
            0,
            ids_two_conjectures["D"],
            FrameworkIILevel::new(1),
            FrameworkIICheckRole::Initialization,
            Arc::clone(&snapshot_two_conjectures),
            false,
        )
        .unwrap();
        assert_ne!(
            semantic_key_of(&request_conjecture_c),
            semantic_key_of(&request_conjecture_d),
            "a changed conjecture clause must change the key"
        );

        // A changed role changes the key.
        let request_maintenance = FrameworkIICheckRequest::new(
            0,
            ids_two_conjectures["C"],
            FrameworkIILevel::new(1),
            FrameworkIICheckRole::Maintenance,
            snapshot_two_conjectures,
            false,
        )
        .unwrap();
        assert_ne!(
            semantic_key_of(&request_conjecture_c),
            semantic_key_of(&request_maintenance),
            "a changed role must change the key"
        );

        // A changed checked level changes the key.
        let (ids_level_low, snapshot_level_low) =
            multi_clause_snapshot(&task, &[("C", 0)], &[("C", 0)], 1);
        let (ids_level_high, snapshot_level_high) =
            multi_clause_snapshot(&task, &[("C", 0)], &[("C", 1)], 1);
        let request_level_low = FrameworkIICheckRequest::new(
            0,
            ids_level_low["C"],
            FrameworkIILevel::new(0),
            FrameworkIICheckRole::Initialization,
            snapshot_level_low,
            false,
        )
        .unwrap();
        let request_level_high = FrameworkIICheckRequest::new(
            0,
            ids_level_high["C"],
            FrameworkIILevel::new(1),
            FrameworkIICheckRole::Initialization,
            snapshot_level_high,
            false,
        )
        .unwrap();
        assert_ne!(
            semantic_key_of(&request_level_low),
            semantic_key_of(&request_level_high),
            "a changed checked level must change the key"
        );
    }

    /// A proof-entry hit no longer returns Proved straight from the
    /// dictionary: `houdini.tex` Section 4.4 requires Lean's empty-instance
    /// check on the *new* obligation first, so the reuse prepares the
    /// obligation but never launches a solver.
    #[tokio::test(flavor = "current_thread")]
    async fn semantic_reuse_rechecks_the_empty_instance_and_references_the_original_proof() {
        let directory = TestDirectory::new("semantic-reuse-references-original");
        let (task, request) = production_test_request();
        let (owner, artifacts) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(directory.path().join("artifacts")),
        )
        .unwrap();
        let admission =
            create_general_solver_admission(RuntimeResourcePolicy::agent_only(1, 1).unwrap())
                .unwrap();
        let (encoding, prepared) = applied_pre_check_fixture_with_axiom_tags(
            &task,
            &request,
            &artifacts,
            &admission,
            axiom_tag_table_for(&request),
        )
        .await;
        let (command, launch_marker) = sentinel_vampire(directory.path());
        let config = production_test_config(artifacts.clone(), command);
        let mut semantic = MultiRequestPreCheckSemantic::new();
        semantic.register(&request, prepared);
        let mut checker = FrameworkIIProductionChecker::new(semantic, config);

        let conjecture_identity = conjecture_of(&request);
        let original_request_digest = "1".repeat(64);
        let original_evidence = FrameworkIICheckEvidence::new(
            original_request_digest.clone(),
            "original-runtime-proof-receipt-digest",
        )
        .unwrap();
        checker.semantic_dictionary.record_proof(
            Arc::clone(&conjecture_identity),
            FrameworkIIDictionaryProofEntry {
                cited: Arc::new(TaggedPremiseSet::new()),
                evidence: original_evidence,
            },
        );

        let execution = checker.check(request.clone()).await.unwrap();
        let FrameworkIICheckExecution::Applied(FrameworkIICheckOutcome::Proved(evidence)) =
            execution
        else {
            panic!("a matching semantic key must reuse a Proved outcome")
        };
        let reuse = evidence
            .semantic_reuse()
            .expect("a reused outcome carries a semantic-reuse reference");
        assert_eq!(reuse.kind(), FrameworkIISemanticReuseKind::ProofSubsumption);
        assert_eq!(reuse.original_request_digest(), original_request_digest);
        assert_eq!(
            reuse.original_evidence_identity(),
            "original-runtime-proof-receipt-digest"
        );
        assert_eq!(evidence.request_digest(), request.request_digest());
        assert!(
            FrameworkIICheckOutcome::Proved(evidence.clone()).is_bound_to(request.request_digest()),
            "a reused outcome still binds to the reusing request's own digest"
        );
        assert!(
            evidence.preparation_time().is_none(),
            "a semantic-key reuse row must never carry a fabricated preparation time"
        );

        assert_eq!(
            checker.semantic.prepare_calls, 1,
            "a proof reuse still prepares the new obligation for the empty-instance check"
        );
        assert!(checker.pending.is_empty());
        assert!(checker.retries.is_empty());
        assert!(
            checker.complete.is_empty(),
            "semantic reuse sits in front of the exact snapshot cache and does not populate it"
        );
        assert_eq!(checker.semantic_reuses_total(), 1);
        assert_eq!(checker.proof_subsumption_hits_total(), 1);
        assert!(
            !launch_marker.exists(),
            "semantic reuse must never launch a solver process"
        );

        // The reused evidence still satisfies ordinary ledger admission.
        let mut ledger = LevelAttemptLedger::default();
        ledger
            .append_attempt(request, FrameworkIICheckOutcome::Proved(evidence))
            .expect("a reused Proved outcome is valid ledger authority");

        encoding.shutdown().await.unwrap();
        settle_test_artifacts(checker, owner);
    }

    /// Pass 7.5f: a frozen job's profile label
    /// (`certificate_profiles.rs`) is the winner recorded in the semantic
    /// dictionary's proof entry for that condition, read purely through
    /// `FrameworkIICheckEvidence::runtime_proof()`. `from_semantic_reuse`
    /// keeps the exact original authority `Arc` unchanged regardless of
    /// which subsumption rule produced the reuse, so a check served from
    /// the dictionary still exposes the original launch's own `winner()`.
    /// This pins that guarantee directly at the evidence layer rather than
    /// depending on a live prover's proof text happening to reuse a
    /// specific clause end-to-end during a real stabilization run.
    #[tokio::test(flavor = "current_thread")]
    async fn proof_subsumption_reuse_still_exposes_the_original_runtime_proof_receipt() {
        let directory = TestDirectory::new("proof-subsumption-root-profile");
        let (task, request) = production_test_request();
        let (owner, artifacts) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(directory.path().join("artifacts")),
        )
        .unwrap();
        let original_receipt = RuntimeProofReceipt::feedback_test_fixture(
            &request,
            &artifacts,
            ProofSearchProfile::Casc2025,
        );
        let original_evidence =
            FrameworkIICheckEvidence::from_runtime_proof(original_receipt, None);
        let reuse = SemanticReuseEvidence::new(
            &clause_subject(&request),
            FrameworkIISemanticReuseKind::ProofSubsumption,
            Arc::from("reuse-key-digest"),
            Arc::new(json!({"kind": "test-key"})),
            Value::Array(Vec::new()),
            &original_evidence,
        );
        let reused_evidence =
            FrameworkIICheckEvidence::from_semantic_reuse(&original_evidence, reuse);

        let original = original_evidence
            .runtime_proof()
            .expect("the original evidence carries a runtime proof receipt");
        let reused = reused_evidence
            .runtime_proof()
            .expect("a proof-subsumption reuse still exposes the original runtime proof receipt");
        assert_eq!(reused.receipt_digest(), original.receipt_digest());
        assert_eq!(reused.winner(), ProofSearchProfile::Casc2025);
        assert!(
            Arc::ptr_eq(original, reused),
            "profile provenance must read the identical Arc, never a fabricated copy"
        );

        owner.settle().unwrap();
    }

    #[tokio::test(flavor = "current_thread")]
    async fn semantic_reuse_of_a_refuted_outcome_references_the_original_validated_refutation() {
        let directory = TestDirectory::new("semantic-reuse-refuted-reference");
        let (task, request) = production_test_request();
        let (owner, artifacts) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(directory.path().join("artifacts")),
        )
        .unwrap();
        let (command, launch_marker) = sentinel_vampire(directory.path());
        let config = production_test_config(artifacts.clone(), command);
        let downstream_called = Arc::new(AtomicBool::new(false));
        let semantic = InjectedPreCheckSemantic::new(
            FrameworkIIPreCheckOutcome::Failure(FailureReport::artifact(
                FailureKind::InfrastructureFailure,
                FailureScope::RunGlobal,
                "a matching semantic key must never reach worker preparation",
            )),
            downstream_called,
        );
        let mut checker = FrameworkIIProductionChecker::new(semantic, config);

        let conjecture_identity = conjecture_of(&request);
        let original_request_digest = "3".repeat(64);
        let original_evidence = FrameworkIICheckEvidence::new(
            original_request_digest.clone(),
            "original-validated-refutation-digest",
        )
        .unwrap();
        checker.semantic_dictionary.record_refutation(
            Arc::clone(&conjecture_identity),
            FrameworkIIDictionaryRefutationEntry {
                tagged: Arc::new(tagged_premise_set(&request)),
                evidence: original_evidence,
                countermodel: Arc::new(FrameworkIIRetainedCountermodel::FoundNotRetained {
                    tuple_count: 0,
                }),
            },
        );

        let execution = checker.check(request.clone()).await.unwrap();
        let FrameworkIICheckExecution::Applied(FrameworkIICheckOutcome::Refuted(evidence)) =
            execution
        else {
            panic!("a matching semantic key must reuse a Refuted outcome")
        };
        let reuse = evidence
            .semantic_reuse()
            .expect("a reused outcome carries a semantic-reuse reference");
        assert_eq!(
            reuse.kind(),
            FrameworkIISemanticReuseKind::RefutationSubsumption
        );
        assert_eq!(reuse.original_request_digest(), original_request_digest);
        assert_eq!(
            reuse.original_evidence_identity(),
            "original-validated-refutation-digest"
        );
        assert!(
            FrameworkIICheckOutcome::Refuted(evidence.clone())
                .is_bound_to(request.request_digest()),
            "a reused refutation still binds to the reusing request's own digest"
        );
        assert_eq!(checker.semantic.prepare_calls, 0);
        assert_eq!(checker.semantic_reuses_total(), 1);
        assert_eq!(checker.refutation_subsumption_hits_total(), 1);
        assert!(!launch_marker.exists());

        let mut ledger = LevelAttemptLedger::default();
        ledger
            .append_attempt(request, FrameworkIICheckOutcome::Refuted(evidence))
            .expect("a reused Refuted outcome is valid ledger authority");

        settle_test_artifacts(checker, owner);
    }

    /// Milestone 7.5 review, finding 1. A proof entry and a refutation
    /// entry for the same conjecture are *not* contradictory evidence: the
    /// proof holds over nonempty active domains, the refutation is an
    /// adom-empty countermodel, and the checker itself records exactly that
    /// pair whenever a proof hit's empty-instance check finds one. The
    /// refutation lookup therefore runs first and answers `Refuted` by
    /// reuse, with no worker preparation, no launch, and no abort.
    #[tokio::test(flavor = "current_thread")]
    async fn a_refutation_entry_answers_even_when_a_proof_entry_also_matches() {
        let directory = TestDirectory::new("semantic-dictionary-both-hit");
        let (task, request) = production_test_request();
        let (owner, artifacts) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(directory.path().join("artifacts")),
        )
        .unwrap();
        let (command, launch_marker) = sentinel_vampire(directory.path());
        let config = production_test_config(artifacts.clone(), command);
        let downstream_called = Arc::new(AtomicBool::new(false));
        let semantic = InjectedPreCheckSemantic::new(
            FrameworkIIPreCheckOutcome::Failure(FailureReport::artifact(
                FailureKind::InfrastructureFailure,
                FailureScope::RunGlobal,
                "a refutation dictionary hit must never reach worker preparation",
            )),
            downstream_called,
        );
        let mut checker = FrameworkIIProductionChecker::new(semantic, config);

        let conjecture_identity = conjecture_of(&request);
        // The cited set is empty, so it is a subset of this request's tags
        // and the proof entry matches too.
        checker.semantic_dictionary.record_proof(
            Arc::clone(&conjecture_identity),
            FrameworkIIDictionaryProofEntry {
                cited: Arc::new(TaggedPremiseSet::new()),
                evidence: FrameworkIICheckEvidence::new("4".repeat(64), "nonempty-domain-proof")
                    .unwrap(),
            },
        );
        checker.semantic_dictionary.record_refutation(
            Arc::clone(&conjecture_identity),
            FrameworkIIDictionaryRefutationEntry {
                tagged: Arc::new(tagged_premise_set(&request)),
                evidence: FrameworkIICheckEvidence::new(
                    "5".repeat(64),
                    "empty-instance-refutation",
                )
                .unwrap(),
                countermodel: Arc::new(FrameworkIIRetainedCountermodel::FoundNotRetained {
                    tuple_count: 0,
                }),
            },
        );

        let execution = checker.check(request.clone()).await.unwrap();
        let FrameworkIICheckExecution::Applied(FrameworkIICheckOutcome::Refuted(evidence)) =
            execution
        else {
            panic!("a matching refutation entry answers Refuted by reuse")
        };
        let reuse = evidence
            .semantic_reuse()
            .expect("a reused outcome carries a semantic-reuse reference");
        assert_eq!(
            reuse.kind(),
            FrameworkIISemanticReuseKind::RefutationSubsumption
        );
        assert_eq!(
            reuse.original_evidence_identity(),
            "empty-instance-refutation"
        );
        assert_eq!(checker.semantic.prepare_calls, 0);
        assert_eq!(checker.semantic_reuses_total(), 1);
        assert_eq!(checker.refutation_subsumption_hits_total(), 1);
        assert_eq!(checker.proof_subsumption_hits_total(), 0);
        assert!(!launch_marker.exists());

        settle_test_artifacts(checker, owner);
    }

    /// Milestone 7.5 review, finding 1, the epoch after. The pair the
    /// previous test plants is exactly what a proof hit whose
    /// empty-instance check refuted the new obligation leaves behind, so
    /// the *next* epoch's request for the same key must be answered
    /// `Refuted` by reuse rather than aborting on a both-hit. `begin_epoch`
    /// is what separates the two epochs.
    #[tokio::test(flavor = "current_thread")]
    async fn the_epoch_after_a_proof_hit_empty_refutation_reuses_that_refutation() {
        let directory = TestDirectory::new("proof-hit-empty-refutation-next-epoch");
        let (task, request) = production_test_request();
        let (owner, artifacts) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(directory.path().join("artifacts")),
        )
        .unwrap();
        let (command, launch_marker) = sentinel_vampire(directory.path());
        let config = production_test_config(artifacts.clone(), command);
        let downstream_called = Arc::new(AtomicBool::new(false));
        let semantic = InjectedPreCheckSemantic::new(
            FrameworkIIPreCheckOutcome::Failure(FailureReport::artifact(
                FailureKind::InfrastructureFailure,
                FailureScope::RunGlobal,
                "the second epoch's request must never reach worker preparation",
            )),
            downstream_called,
        );
        let mut checker = FrameworkIIProductionChecker::new(semantic, config);

        // Epoch 1's residue: the proof entry that was hit, plus the
        // refutation the hit's own empty-instance check recorded under the
        // request's exact tags.
        let conjecture_identity = conjecture_of(&request);
        checker.semantic_dictionary.record_proof(
            Arc::clone(&conjecture_identity),
            FrameworkIIDictionaryProofEntry {
                cited: Arc::new(TaggedPremiseSet::new()),
                evidence: FrameworkIICheckEvidence::new("6".repeat(64), "nonempty-domain-proof")
                    .unwrap(),
            },
        );
        checker.semantic_dictionary.record_refutation(
            Arc::clone(&conjecture_identity),
            FrameworkIIDictionaryRefutationEntry {
                tagged: Arc::new(tagged_premise_set(&request)),
                evidence: FrameworkIICheckEvidence::new(
                    "7".repeat(64),
                    "empty-instance-refutation",
                )
                .unwrap(),
                countermodel: Arc::new(FrameworkIIRetainedCountermodel::FoundNotRetained {
                    tuple_count: 0,
                }),
            },
        );

        // Epoch 2.
        checker.begin_epoch();
        let execution = checker.check(request.clone()).await.unwrap();
        let FrameworkIICheckExecution::Applied(FrameworkIICheckOutcome::Refuted(evidence)) =
            execution
        else {
            panic!("the epoch after a proof-hit empty refutation reuses that refutation")
        };
        assert_eq!(
            evidence
                .semantic_reuse()
                .expect("a reused outcome carries a semantic-reuse reference")
                .original_evidence_identity(),
            "empty-instance-refutation"
        );
        assert_eq!(checker.semantic.prepare_calls, 0);
        assert!(!launch_marker.exists());

        settle_test_artifacts(checker, owner);
    }

    /// Milestone 7.5 review, finding 3. A key whose retry policy is
    /// exhausted and whose later-recorded proof entry matches is resolved by
    /// reuse: the proof hit repeats Lean's empty-instance check on this
    /// request's own obligation, runs no solver, and consumes no allowance,
    /// so the retry policy's exhaustion is irrelevant to it. Before the fix
    /// the budget lookup sat above the proof-hit branch and turned this
    /// exact request into `InvalidEvidence("the retry policy granted a
    /// launch it has no allowance for")`.
    #[tokio::test(flavor = "current_thread")]
    async fn an_exhausted_key_with_a_matching_proof_entry_is_resolved_by_reuse() {
        let directory = TestDirectory::new("exhausted-key-proof-hit");
        let (task, request) = production_test_request();
        let (owner, artifacts) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(directory.path().join("artifacts")),
        )
        .unwrap();
        let admission =
            create_general_solver_admission(RuntimeResourcePolicy::agent_only(1, 1).unwrap())
                .unwrap();
        let (encoding, prepared) = applied_pre_check_fixture_with_axiom_tags(
            &task,
            &request,
            &artifacts,
            &admission,
            axiom_tag_table_for(&request),
        )
        .await;
        let mut semantic = MultiRequestPreCheckSemantic::new();
        semantic.register(&request, prepared);
        let (command, launch_marker) = sentinel_vampire(directory.path());
        let config = production_test_config(artifacts.clone(), command);
        let granted_launches = config.retry_policy.granted_launches();
        let mut checker = FrameworkIIProductionChecker::new(semantic, config);

        // Exhaust the key: `record_inconclusive` advances the launch count
        // by one per call, so `granted_launches` calls leave the policy with
        // no further allowance for it.
        let semantic_vc_key: Arc<str> =
            Arc::from(canonical_value_sha256(&semantic_key_of(&request)));
        for _ in 0..granted_launches {
            checker.semantic_dictionary.record_inconclusive(
                Arc::clone(&semantic_vc_key),
                FrameworkIIInconclusiveReason::TimedOut,
                Arc::new(tagged_premise_set(&request)),
                FrameworkIICheckEvidence::new("8".repeat(64), "exhausted-progress").unwrap(),
            );
        }
        assert!(
            checker
                .config
                .retry_policy
                .allowance_after(granted_launches)
                .is_none(),
            "the key must have no allowance left for this test to mean anything"
        );

        // The proof entry arrives afterwards, from another request for the
        // same conjecture.
        checker.semantic_dictionary.record_proof(
            conjecture_of(&request),
            FrameworkIIDictionaryProofEntry {
                cited: Arc::new(TaggedPremiseSet::new()),
                evidence: FrameworkIICheckEvidence::new("9".repeat(64), "later-proof-entry")
                    .unwrap(),
            },
        );

        let execution = checker.check(request.clone()).await.unwrap();
        let FrameworkIICheckExecution::Applied(FrameworkIICheckOutcome::Proved(evidence)) =
            execution
        else {
            panic!("an exhausted key with a matching proof entry is proved by reuse: {execution:?}")
        };
        let reuse = evidence
            .semantic_reuse()
            .expect("a reused outcome carries a semantic-reuse reference");
        assert_eq!(reuse.kind(), FrameworkIISemanticReuseKind::ProofSubsumption);
        assert_eq!(reuse.original_evidence_identity(), "later-proof-entry");
        assert_eq!(
            checker.semantic.prepare_calls, 1,
            "the proof hit prepares its own obligation for the empty-instance recheck"
        );
        assert_eq!(checker.proof_subsumption_hits_total(), 1);
        assert!(
            !launch_marker.exists(),
            "no solver runs on the proof-hit path"
        );

        encoding.shutdown().await.unwrap();
        settle_test_artifacts(checker, owner);
    }

    #[test]
    fn countermodel_retention_honors_the_tuple_bound() {
        let validation_identity = json!({
            "interpretation_identity": {
                "instance_identity": {
                    "relations": [
                        {"key": "R", "arity": 1, "rows": [[1], [2], [3]]},
                    ]
                }
            }
        });
        // The default: no retention limit, so the countermodel is retained
        // in full whatever its size.
        let retained = build_retained_countermodel(&validation_identity, None);
        let FrameworkIIRetainedCountermodel::Retained(instance) = retained else {
            panic!("with no retention limit a countermodel is always retained in full")
        };
        assert_eq!(instance.tuple_count(), 3);
        assert_eq!(instance.relations().len(), 1);
        assert_eq!(instance.relations()[0].key(), "R");
        assert_eq!(instance.relations()[0].arity(), 1);
        assert_eq!(instance.relations()[0].rows().len(), 3);

        let not_retained = build_retained_countermodel(&validation_identity, Some(2));
        assert!(
            matches!(
                not_retained,
                FrameworkIIRetainedCountermodel::FoundNotRetained { tuple_count: 3 }
            ),
            "beyond the tuple bound only the tuple count is retained"
        );
    }

    #[test]
    fn countermodel_relations_malformed_shape_is_not_retained_rather_than_panicking() {
        let malformed = json!({"nothing": "here"});
        let result = build_retained_countermodel(&malformed, None);
        assert!(matches!(
            result,
            FrameworkIIRetainedCountermodel::FoundNotRetained { tuple_count: 0 }
        ));
    }

    #[test]
    fn proof_dictionary_hits_a_superset_request_and_misses_a_subset() {
        let mut dictionary = FrameworkIISemanticDictionary::default();
        let conjecture: Arc<str> = Arc::from("conjecture-x");
        let mut cited = TaggedPremiseSet::new();
        cited.insert(FrameworkIIPremiseTag::Pre);
        cited.insert(FrameworkIIPremiseTag::Guard);
        let evidence = FrameworkIICheckEvidence::new("6".repeat(64), "proof-x").unwrap();
        dictionary.record_proof(
            Arc::clone(&conjecture),
            FrameworkIIDictionaryProofEntry {
                cited: Arc::new(cited.clone()),
                evidence,
            },
        );

        let mut superset = cited.clone();
        superset.insert(FrameworkIIPremiseTag::NotThetaGuard);
        assert!(
            dictionary.find_proof_hit(&conjecture, &superset).is_some(),
            "a request whose tagged set contains the cited set must hit"
        );

        let mut subset = TaggedPremiseSet::new();
        subset.insert(FrameworkIIPremiseTag::Pre);
        assert!(
            dictionary.find_proof_hit(&conjecture, &subset).is_none(),
            "a request whose tagged set does not contain the cited set must miss"
        );
    }

    /// Two launched proof entries for one conjecture, and the final Core
    /// picks between them: the label is the last entry whose cited premises
    /// the Core's own request for that condition carries.
    ///
    /// The clause here was launched twice — once at level zero, citing
    /// `{pre}`, won by the direct schedule, and once at level one, citing
    /// `{pre, not_theta_guard}`, won by CASC. A Core that places it at
    /// level zero poses `{pre}`, which does not carry `not_theta_guard`, so
    /// the level-one entry is not a candidate at all and the label is
    /// `direct`. A Core that places it at level one poses both premises,
    /// both entries qualify, and the later one wins.
    #[test]
    fn the_final_core_picks_which_of_two_launched_entries_labels_a_condition() {
        let directory = TestDirectory::new("launched-proof-winner-choice");
        let (task, request) = production_test_request();
        let (owner, artifacts) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(directory.path().join("artifacts")),
        )
        .unwrap();
        let launched = |winner| {
            FrameworkIICheckEvidence::from_runtime_proof(
                RuntimeProofReceipt::feedback_test_fixture(&request, &artifacts, winner),
                None,
            )
        };

        let (ids, at_level_zero) = multi_clause_snapshot(&task, &[("A", 0)], &[("A", 0)], 3);
        let (_, at_level_one) = multi_clause_snapshot(&task, &[("A", 0)], &[("A", 1)], 3);
        let identity = at_level_zero.records()[&ids["A"]]
            .formula()
            .identity_sha256()
            .to_string();
        let key = tagged_conjecture_key(FrameworkIICheckRole::Initialization, &identity);

        let mut dictionary = FrameworkIISemanticDictionary::default();
        let level_zero_cited = TaggedPremiseSet::from([FrameworkIIPremiseTag::Pre]);
        let level_one_cited = TaggedPremiseSet::from([
            FrameworkIIPremiseTag::Pre,
            FrameworkIIPremiseTag::NotThetaGuard,
        ]);
        dictionary.record_proof(
            Arc::clone(&key),
            FrameworkIIDictionaryProofEntry {
                cited: Arc::new(level_zero_cited),
                evidence: launched(ProofSearchProfile::Direct),
            },
        );
        dictionary.record_proof(
            Arc::clone(&key),
            FrameworkIIDictionaryProofEntry {
                cited: Arc::new(level_one_cited),
                evidence: launched(ProofSearchProfile::Casc2025),
            },
        );

        fn winners_at(
            dictionary: &FrameworkIISemanticDictionary,
            core: &LeveledCandidateSnapshot,
        ) -> BTreeMap<Arc<str>, ProofSearchProfile> {
            dictionary
                .launched_proof_winners(core)
                .into_iter()
                .collect()
        }
        assert_eq!(
            winners_at(&dictionary, &at_level_zero).get(&key).copied(),
            Some(ProofSearchProfile::Direct),
            "a level-zero Core carries no not_theta_guard, so only the level-zero launch qualifies"
        );
        assert_eq!(
            winners_at(&dictionary, &at_level_one).get(&key).copied(),
            Some(ProofSearchProfile::Casc2025),
            "a level-one Core carries both cited sets, and the later launch wins"
        );

        // A conjecture whose only entry is theorem-closed is not launched,
        // so it carries no winner and the freeze falls back to the run's
        // configured profile.
        let step_key = tagged_conjecture_key(FrameworkIICheckRole::Maintenance, &identity);
        dictionary.record_proof(
            Arc::clone(&step_key),
            FrameworkIIDictionaryProofEntry {
                cited: Arc::new(TaggedPremiseSet::new()),
                evidence: FrameworkIICheckEvidence::new("9".repeat(64), "theorem-selection")
                    .unwrap(),
            },
        );
        assert!(!winners_at(&dictionary, &at_level_zero).contains_key(&step_key));

        drop(dictionary);
        drop(artifacts);
        owner.settle().unwrap();
    }

    /// Pass 7.7b, item 13: a protected precondition row's level-zero
    /// initialization proof entry cites `{Pre}`, because Lean's
    /// conjunct-elimination theorem consults `pre'`. That entry subsumes
    /// every later initialization request and no step request at all — an
    /// empty cited set would have answered a step request the theorem
    /// never justified.
    #[test]
    fn a_protected_row_init_entry_cites_pre_and_never_answers_a_step_request() {
        let mut dictionary = FrameworkIISemanticDictionary::default();
        let conjecture: Arc<str> = Arc::from("protected-row-conjecture");
        let mut cited = TaggedPremiseSet::new();
        cited.insert(FrameworkIIPremiseTag::Pre);
        dictionary.record_proof(
            Arc::clone(&conjecture),
            FrameworkIIDictionaryProofEntry {
                cited: Arc::new(cited),
                evidence: FrameworkIICheckEvidence::new("8".repeat(64), "conjunct-elimination")
                    .unwrap(),
            },
        );

        // An initialization request at level zero: `{pre}`.
        let mut init_zero = TaggedPremiseSet::new();
        init_zero.insert(FrameworkIIPremiseTag::Pre);
        assert!(
            dictionary.find_proof_hit(&conjecture, &init_zero).is_some(),
            "the entry must still subsume the initialization it came from"
        );

        // An initialization request at a higher level adds theta premises
        // and still contains `pre`.
        let mut init_higher = init_zero.clone();
        init_higher.insert(FrameworkIIPremiseTag::NotThetaGuard);
        init_higher.insert(FrameworkIIPremiseTag::Theta(Arc::from("d".repeat(64))));
        assert!(
            dictionary
                .find_proof_hit(&conjecture, &init_higher)
                .is_some(),
            "an initialization request at any level must still hit"
        );

        // A step (maintenance) request carries `guard` and the Core's
        // `plain` premises, and never `pre`.
        let mut step = TaggedPremiseSet::new();
        step.insert(FrameworkIIPremiseTag::Guard);
        step.insert(FrameworkIIPremiseTag::Plain(Arc::from("e".repeat(64))));
        assert!(
            dictionary.find_proof_hit(&conjecture, &step).is_none(),
            "a step request must not be answered by the initialization entry"
        );
        let mut step_higher = step.clone();
        step_higher.insert(FrameworkIIPremiseTag::NotThetaGuard);
        step_higher.insert(FrameworkIIPremiseTag::Theta(Arc::from("f".repeat(64))));
        assert!(
            dictionary
                .find_proof_hit(&conjecture, &step_higher)
                .is_none(),
            "a step request at a higher level must not be answered either"
        );
    }

    #[test]
    fn refutation_dictionary_hits_a_subset_request_and_misses_a_superset() {
        let mut dictionary = FrameworkIISemanticDictionary::default();
        let conjecture: Arc<str> = Arc::from("conjecture-y");
        let mut tagged = TaggedPremiseSet::new();
        tagged.insert(FrameworkIIPremiseTag::Pre);
        tagged.insert(FrameworkIIPremiseTag::Guard);
        let evidence = FrameworkIICheckEvidence::new("7".repeat(64), "refutation-y").unwrap();
        dictionary.record_refutation(
            Arc::clone(&conjecture),
            FrameworkIIDictionaryRefutationEntry {
                tagged: Arc::new(tagged.clone()),
                evidence,
                countermodel: Arc::new(FrameworkIIRetainedCountermodel::FoundNotRetained {
                    tuple_count: 0,
                }),
            },
        );

        let mut subset = TaggedPremiseSet::new();
        subset.insert(FrameworkIIPremiseTag::Pre);
        assert!(
            dictionary
                .find_refutation_hit(&conjecture, &subset)
                .is_some(),
            "a request whose tagged set is contained in the entry's set must hit"
        );

        let mut superset = tagged.clone();
        superset.insert(FrameworkIIPremiseTag::NotThetaGuard);
        assert!(
            dictionary
                .find_refutation_hit(&conjecture, &superset)
                .is_none(),
            "a request whose tagged set is not contained in the entry's set must miss"
        );
    }

    #[test]
    fn semantic_dictionary_never_reuses_a_proof_across_roles() {
        // Initialization proves `c`; Maintenance proves `wp(body, c)`.
        // Monotonicity of entailment only licenses proof reuse for the same
        // conjecture, so a maintenance proof entry — even one whose cited
        // tags happen to be a subset of an initialization request's tagged
        // set — must never answer that initialization request. The
        // dictionary enforces this by indexing on the tagged conjecture
        // (role plus clause identity), not clause identity alone.
        let task = production_test_task();
        let (ids, snapshot) =
            multi_clause_snapshot(&task, &[("C", 1), ("P", 0)], &[("C", 1), ("P", 0)], 2);

        let init_request = FrameworkIICheckRequest::new(
            0,
            ids["C"],
            FrameworkIILevel::new(1),
            FrameworkIICheckRole::Initialization,
            Arc::clone(&snapshot),
            false,
        )
        .unwrap();
        let maint_request = FrameworkIICheckRequest::new(
            0,
            ids["C"],
            FrameworkIILevel::new(1),
            FrameworkIICheckRole::Maintenance,
            snapshot,
            false,
        )
        .unwrap();

        let init_conjecture = conjecture_of(&init_request);
        let maint_conjecture = conjecture_of(&maint_request);
        assert_ne!(
            init_conjecture, maint_conjecture,
            "the same clause's Initialization and Maintenance requests must key under \
             different tagged conjectures"
        );

        let init_tags = tagged_premise_set(&init_request);
        let maint_tags = tagged_premise_set(&maint_request);

        // The proof entry's cited set: everything init_tags carries besides
        // `pre`, i.e. `{not_theta_guard, theta(P)}`. It is a genuine subset
        // of the initialization request's own tagged set, so tag-inclusion
        // alone would wrongly let it subsume that request; only the
        // per-role conjecture key stops it.
        let cited: TaggedPremiseSet = init_tags
            .iter()
            .filter(|tag| **tag != FrameworkIIPremiseTag::Pre)
            .cloned()
            .collect();
        assert!(
            !cited.is_empty(),
            "level 1 must carry not_theta_guard/theta tags to make this scenario meaningful"
        );
        assert!(
            cited.is_subset(&init_tags),
            "sanity: the citation is drawn from init_tags itself"
        );
        assert!(
            cited.is_subset(&maint_tags),
            "sanity: the same citation is also a subset of the maintenance tagged set"
        );

        let mut dictionary = FrameworkIISemanticDictionary::default();
        dictionary.record_proof(
            Arc::clone(&maint_conjecture),
            FrameworkIIDictionaryProofEntry {
                cited: Arc::new(cited),
                evidence: FrameworkIICheckEvidence::new("8".repeat(64), "maintenance-only-proof")
                    .unwrap(),
            },
        );

        assert!(
            dictionary
                .find_proof_hit(&maint_conjecture, &maint_tags)
                .is_some(),
            "the recorded entry still resolves a maintenance lookup for the same clause"
        );
        assert!(
            dictionary
                .find_proof_hit(&init_conjecture, &init_tags)
                .is_none(),
            "a maintenance-only proof entry must never answer an initialization request for \
             the same clause, even though its cited tags are a subset of the initialization \
             request's tagged set"
        );
    }

    /// Pass 7.5b, deliverable 4: `strongest_refutations` returns the
    /// antichain of a clause's refutation-dictionary entries maximal under
    /// tagged-set inclusion — here three entries where the smallest
    /// (`{pre}`) is dominated by a second (`{pre, guard}`) and dropped,
    /// while the third (`{not_theta_guard}`) is incomparable to both and
    /// survives, sorted by set size descending.
    #[tokio::test(flavor = "current_thread")]
    async fn strongest_refutations_returns_the_maximal_antichain_capped_and_sorted() {
        let directory = TestDirectory::new("strongest-refutations-antichain");
        let (task, request) = production_test_request();
        let (owner, artifacts) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(directory.path().join("artifacts")),
        )
        .unwrap();
        let clause_identity = "conjecture-under-test";
        let conjecture = tagged_conjecture_key(FrameworkIICheckRole::Maintenance, clause_identity);

        let mut dictionary = FrameworkIISemanticDictionary::default();
        let mut small = TaggedPremiseSet::new();
        small.insert(FrameworkIIPremiseTag::Pre);
        let mut medium = small.clone();
        medium.insert(FrameworkIIPremiseTag::Guard);
        let mut incomparable = TaggedPremiseSet::new();
        incomparable.insert(FrameworkIIPremiseTag::NotThetaGuard);

        let refutation = ValidatedFiniteRefutation::feedback_test_fixture(&request, &artifacts);
        let evidence = FrameworkIICheckEvidence::from_validated_refutation(refutation, None);

        for tagged in [small, medium, incomparable] {
            dictionary.record_refutation(
                Arc::clone(&conjecture),
                FrameworkIIDictionaryRefutationEntry {
                    tagged: Arc::new(tagged),
                    evidence: evidence.clone(),
                    countermodel: Arc::new(FrameworkIIRetainedCountermodel::FoundNotRetained {
                        tuple_count: 0,
                    }),
                },
            );
        }

        let strongest = dictionary.strongest_refutations(clause_identity, None);
        assert_eq!(
            strongest.len(),
            2,
            "the smallest entry is dominated by the medium entry and dropped"
        );
        assert_eq!(
            strongest[0].tagged_premises().len(),
            2,
            "sorted by tagged-set size descending"
        );
        assert_eq!(strongest[1].tagged_premises().len(), 1);

        let capped = dictionary.strongest_refutations(clause_identity, Some(1));
        assert_eq!(capped.len(), 1, "the cap truncates the sorted antichain");
        assert_eq!(capped[0].tagged_premises().len(), 2);

        owner.settle().unwrap();
    }

    /// A scripted Vampire proof fixture whose emitted proof cites `names`
    /// via `file('problem.p', <name>)` annotations (Vampire's
    /// `--output_axiom_names on` shape), so a paired
    /// [`FrameworkIIAxiomTagTable`] mapping those names lets Pass 7.5b's
    /// proof-subsumption caching record a real cited tagged set instead of
    /// recording nothing.
    /// A Vampire stub that proves its first invocation, citing `names`, and
    /// times out on every later one while recording that a launch happened.
    ///
    /// Returns the marker path a second launch would create, so a test can
    /// assert that no solver ran at all.
    fn proof_then_timeout_vampire(
        directory: &Path,
        label: &str,
        names: &[&str],
    ) -> (VampireWorkerCommand, PathBuf) {
        let executable = directory.join(format!("vampire-proof-then-timeout-{label}.sh"));
        let first_marker = directory.join(format!("vampire-first-{label}"));
        let relaunch_marker = directory.join(format!("vampire-relaunched-{label}"));
        let mut script = format!(
            "#!/bin/sh\nif [ -f {first} ]; then\n  printf relaunched > {relaunch}\n  printf '%s\\n' '% SZS status Timeout for problem'\n  printf '%s\\n' '% Termination reason: Time limit'\n  exit 0\nfi\nprintf first > {first}\n",
            first = first_marker.display(),
            relaunch = relaunch_marker.display(),
        );
        script.push_str(
            "printf '%s\\n' '% SZS status Theorem for problem'\nprintf '%s\\n' '% SZS output start Proof for problem'\n",
        );
        for (ordinal, name) in names.iter().enumerate() {
            script.push_str(&format!(
                "printf '%s\\n' \"fof(f{ordinal}, axiom, ($true), file('problem.p', {name})).\"\n"
            ));
        }
        script.push_str(
            "printf '%s\\n' '1. $false [fixture]'\nprintf '%s\\n' '% SZS output end Proof for problem'\n",
        );
        fs::write(&executable, script).expect("write proof-then-timeout Vampire executable");
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(&executable, fs::Permissions::from_mode(0o700))
                .expect("make proof-then-timeout Vampire executable");
        }
        (VampireWorkerCommand::new(executable), relaunch_marker)
    }

    fn proof_vampire_citing(directory: &Path, label: &str, names: &[&str]) -> VampireWorkerCommand {
        let executable = directory.join(format!("vampire-proof-{label}.sh"));
        let mut script = String::from(
            "#!/bin/sh\nprintf '%s\\n' '% SZS status Theorem for problem'\nprintf '%s\\n' '% SZS output start Proof for problem'\n",
        );
        for (ordinal, name) in names.iter().enumerate() {
            script.push_str(&format!(
                "printf '%s\\n' \"fof(f{ordinal}, axiom, ($true), file('problem.p', {name})).\"\n"
            ));
        }
        script.push_str(
            "printf '%s\\n' '1. $false [fixture]'\nprintf '%s\\n' '% SZS output end Proof for problem'\n",
        );
        fs::write(&executable, script).expect("write citing proof Vampire executable");
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(&executable, fs::Permissions::from_mode(0o700))
                .expect("make citing proof Vampire executable");
        }
        VampireWorkerCommand::new(executable)
    }

    /// A test-only semantic adapter that resolves multiple distinct requests
    /// (keyed by their own `request_digest`) against pre-fabricated prepared
    /// entailments, standing in for the real worker/Lean round trip. Every
    /// genuine proof closes as `NoCounterexample` (an ordinary `Proved`);
    /// `validate_model` is never expected to run in these fixtures.
    struct MultiRequestPreCheckSemantic {
        prepared_by_request: BTreeMap<Arc<str>, PreparedFrameworkIIEntailment>,
        prepare_calls: usize,
        /// Empty-check request digests whose obligation has a
        /// Lean-validated counterexample at the empty instance.
        empty_counterexamples: std::collections::BTreeSet<Arc<str>>,
    }

    impl MultiRequestPreCheckSemantic {
        fn new() -> Self {
            Self {
                prepared_by_request: BTreeMap::new(),
                prepare_calls: 0,
                empty_counterexamples: std::collections::BTreeSet::new(),
            }
        }

        /// Make this obligation's empty-instance check report a validated
        /// counterexample instead of "no counterexample".
        fn with_empty_counterexample(&mut self, prepared: &PreparedFrameworkIIEntailment) {
            self.empty_counterexamples
                .insert(Arc::from(prepared.empty_request_digest()));
        }

        fn register(
            &mut self,
            request: &FrameworkIICheckRequest,
            prepared: PreparedFrameworkIIEntailment,
        ) {
            self.prepared_by_request
                .insert(Arc::from(request.request_digest()), prepared);
        }

        fn register_subject(
            &mut self,
            subject: &FrameworkIICheckSubject,
            prepared: PreparedFrameworkIIEntailment,
        ) {
            self.prepared_by_request
                .insert(Arc::from(subject.request_digest()), prepared);
        }
    }

    impl FrameworkIISemanticAdapter for MultiRequestPreCheckSemantic {
        fn prepare<'a>(
            &'a mut self,
            subject: &'a FrameworkIICheckSubject,
            _admission: &'a SolverAdmission,
            _artifacts: &'a ArtifactStore,
            _cancellation: &'a CancellationToken,
        ) -> Pin<
            Box<
                dyn Future<Output = Result<FrameworkIIPreCheckOutcome, FrameworkIIStateError>>
                    + Send
                    + 'a,
            >,
        > {
            self.prepare_calls += 1;
            let prepared = self
                .prepared_by_request
                .get(subject.request_digest())
                .cloned();
            Box::pin(async move {
                Ok(match prepared {
                    Some(prepared) => FrameworkIIPreCheckOutcome::Applied(prepared),
                    None => FrameworkIIPreCheckOutcome::Failure(FailureReport::artifact(
                        FailureKind::InfrastructureFailure,
                        FailureScope::RunGlobal,
                        "no fixture prepared for this request",
                    )),
                })
            })
        }

        fn check_empty<'a>(
            &'a mut self,
            prepared: &'a PreparedFrameworkIIEntailment,
            attempt: &'a EntailmentAttemptScope,
            _admission: &'a SolverAdmission,
            _cancellation: &'a CancellationToken,
        ) -> Pin<
            Box<
                dyn Future<
                        Output = Result<
                            FrameworkIIEmptyCheckOutcome,
                            FrameworkIISemanticCheckError,
                        >,
                    > + Send
                    + 'a,
            >,
        > {
            let counterexample = self
                .empty_counterexamples
                .contains(prepared.empty_request_digest());
            Box::pin(async move {
                let result_kind = if counterexample {
                    "counterexample"
                } else {
                    "no_counterexample"
                };
                let check_identity = json!({
                    "kind": "whiel_fixed_ambient_empty_counterexample_check",
                    "version": FIXED_AMBIENT_EMPTY_CHECK_IDENTITY_VERSION,
                    "empty_request_identity": prepared.empty_request_identity(),
                    "obligation_identity": prepared.base_obligation_identity(),
                    "worker_entailment_identity": prepared.entailment_identity(),
                    "result": {"kind": result_kind},
                    "decision_definition": "QFEntailment.adomEmptyCounterexample?",
                });
                let check_digest = canonical_value_sha256(&check_identity);
                let artifact = attempt
                    .artifacts()
                    .publish(
                        ArtifactKind::EmptyInstanceCheck,
                        format!("fixture: {result_kind}")
                            .into_bytes()
                            .into_boxed_slice(),
                    )
                    .map_err(FrameworkIISemanticCheckError::Failure)?;
                if counterexample {
                    let validation_artifact = attempt
                        .artifacts()
                        .publish(
                            ArtifactKind::Witness,
                            b"fixture: validated empty counterexample"
                                .to_vec()
                                .into_boxed_slice(),
                        )
                        .map_err(FrameworkIISemanticCheckError::Failure)?;
                    let evidence = FrameworkIIValidatedRefutationEvidence::new(
                        artifact,
                        check_identity,
                        check_digest,
                        validation_artifact,
                    )
                    .map_err(|error| {
                        FrameworkIISemanticCheckError::Failure(state_as_failure(error))
                    })?;
                    return Ok(FrameworkIIEmptyCheckOutcome::ValidatedRefutation(evidence));
                }
                let evidence = FrameworkIIEmptyCheckEvidence::new_no_counterexample(
                    prepared.empty_request_digest(),
                    prepared.base_obligation_digest(),
                    check_identity,
                    check_digest,
                    artifact,
                )
                .map_err(|error| FrameworkIISemanticCheckError::Failure(state_as_failure(error)))?;
                Ok(FrameworkIIEmptyCheckOutcome::NoCounterexample(evidence))
            })
        }

        fn validate_model<'a>(
            &'a mut self,
            _prepared: &'a PreparedFrameworkIIEntailment,
            _attempt: &'a EntailmentAttemptScope,
            _model: VampireModel,
            _admission: &'a SolverAdmission,
            _cancellation: &'a CancellationToken,
        ) -> Pin<
            Box<
                dyn Future<
                        Output = Result<
                            FrameworkIIModelValidationOutcome,
                            FrameworkIISemanticCheckError,
                        >,
                    > + Send
                    + 'a,
            >,
        > {
            Box::pin(async { Ok(FrameworkIIModelValidationOutcome::NotRefutation) })
        }
    }

    /// Models exactly the story that motivates proof subsumption: clause
    /// `C` is rechecked at the same level twice, once per epoch. The second
    /// check either adds a genuinely new premise below `C` (from a freshly
    /// registered clause `N`) — a strict tagged-set superset of
    /// the first check's, so the first proof's cited set (everything this
    /// fixture's proof cites, since `N` did not even exist when it ran)
    /// still subsumes it, with zero further preparation — or only an
    /// unrelated clause at or above `C`'s own level, which leaves the
    /// tagged set unchanged and reuses identically.
    #[tokio::test(flavor = "current_thread")]
    async fn reconsideration_style_premise_change_forces_a_fresh_check_while_unchanged_premises_reuse()
     {
        let directory = TestDirectory::new("semantic-reuse-reconsideration-style");
        let task = production_test_task();
        let (owner, artifacts) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(directory.path().join("artifacts")),
        )
        .unwrap();
        let admission =
            create_general_solver_admission(RuntimeResourcePolicy::agent_only(1, 1).unwrap())
                .unwrap();

        let (ids_before, snapshot_before) =
            multi_clause_snapshot(&task, &[("C", 1)], &[("C", 1)], 2);
        let (ids_after, snapshot_after) =
            multi_clause_snapshot(&task, &[("C", 1), ("N", 0)], &[("C", 1), ("N", 0)], 2);
        let (ids_unrelated_after, snapshot_unrelated_after) =
            multi_clause_snapshot(&task, &[("C", 1), ("H", 1)], &[("C", 1), ("H", 1)], 2);

        let request_before = FrameworkIICheckRequest::new(
            0,
            ids_before["C"],
            FrameworkIILevel::new(1),
            FrameworkIICheckRole::Initialization,
            snapshot_before,
            false,
        )
        .unwrap();
        let request_after = FrameworkIICheckRequest::new(
            0,
            ids_after["C"],
            FrameworkIILevel::new(1),
            FrameworkIICheckRole::Initialization,
            snapshot_after,
            false,
        )
        .unwrap();
        let request_unrelated_after = FrameworkIICheckRequest::new(
            0,
            ids_unrelated_after["C"],
            FrameworkIILevel::new(1),
            FrameworkIICheckRole::Initialization,
            snapshot_unrelated_after,
            false,
        )
        .unwrap();

        assert_ne!(
            semantic_key_of(&request_before),
            semantic_key_of(&request_after),
            "a newly placed premise below the checked level must change the key"
        );
        assert_eq!(
            semantic_key_of(&request_before),
            semantic_key_of(&request_unrelated_after),
            "an unrelated clause at or above the checked level must not change the key"
        );

        let axiom_tags = FrameworkIIAxiomTagTable::for_test(vec![
            ("ax_pre", FrameworkIIPremiseTag::Pre),
            ("ax_not_theta_guard", FrameworkIIPremiseTag::NotThetaGuard),
        ]);
        let (encoding, prepared_before) = applied_pre_check_fixture_with_axiom_tags(
            &task,
            &request_before,
            &artifacts,
            &admission,
            axiom_tags,
        )
        .await;
        // Every reusing request is prepared too: a proof-entry hit repeats
        // Lean's empty-instance check on its own obligation before it counts
        // as Proved, so it needs the prepared obligation even though it
        // never launches a solver.
        let (encoding_after, prepared_after) = applied_pre_check_fixture_with_axiom_tags(
            &task,
            &request_after,
            &artifacts,
            &admission,
            axiom_tag_table_for(&request_after),
        )
        .await;
        let (encoding_unrelated, prepared_unrelated) = applied_pre_check_fixture_with_axiom_tags(
            &task,
            &request_unrelated_after,
            &artifacts,
            &admission,
            axiom_tag_table_for(&request_unrelated_after),
        )
        .await;
        let mut semantic = MultiRequestPreCheckSemantic::new();
        semantic.register(&request_before, prepared_before);
        semantic.register(&request_after, prepared_after);
        semantic.register(&request_unrelated_after, prepared_unrelated);
        let config = production_test_config(
            artifacts.clone(),
            proof_vampire_citing(directory.path(), "init", &["ax_pre", "ax_not_theta_guard"]),
        );
        let mut checker = FrameworkIIProductionChecker::new(semantic, config);

        // First check: a real worker preparation and a real solver launch
        // prove C at level 1 with no premises below it. The fixture proof
        // cites both premises it actually had (`pre`, `not_theta_guard`),
        // so the recorded cited set equals this request's own full tagged
        // set exactly.
        let execution_before = checker.check(request_before.clone()).await.unwrap();
        assert!(
            matches!(
                execution_before,
                FrameworkIICheckExecution::Applied(FrameworkIICheckOutcome::Proved(_))
            ),
            "{execution_before:?}"
        );
        assert_eq!(checker.semantic.prepare_calls, 1);
        assert_eq!(checker.semantic_reuses_total(), 0);

        // Second check: same clause and level, but N is now a level-0
        // premise, adding a `theta(N)` tag the first proof never cited (N
        // did not exist when it ran). The first proof's cited set — exactly
        // `{pre, not_theta_guard}` — is therefore still contained in this
        // request's own (strictly larger) tagged set: a proof-subsumption
        // hit, with zero further worker preparation.
        let execution_after = checker.check(request_after.clone()).await.unwrap();
        let FrameworkIICheckExecution::Applied(FrameworkIICheckOutcome::Proved(evidence_after)) =
            execution_after
        else {
            panic!("a superset request must be served by proof subsumption: {execution_after:?}")
        };
        let reuse_after = evidence_after
            .semantic_reuse()
            .expect("a superset request must reuse the smaller premise set's proof");
        assert_eq!(
            reuse_after.kind(),
            FrameworkIISemanticReuseKind::ProofSubsumption
        );
        assert_eq!(
            reuse_after.original_request_digest(),
            request_before.request_digest()
        );
        assert_eq!(
            checker.semantic.prepare_calls, 2,
            "a superset request prepares its own obligation for the empty-instance re-check, \
             but launches no solver"
        );
        assert_eq!(checker.semantic_reuses_total(), 1);
        assert_eq!(checker.proof_subsumption_hits_total(), 1);

        // Third check: same clause and level, only an unrelated clause H at
        // or above C's level differs from the first snapshot. The tagged
        // set is unchanged, so this reuses the first proof identically.
        let execution_unrelated_after = checker
            .check(request_unrelated_after.clone())
            .await
            .unwrap();
        let FrameworkIICheckExecution::Applied(FrameworkIICheckOutcome::Proved(evidence)) =
            execution_unrelated_after
        else {
            panic!("an unrelated higher-level clause must not block proof subsumption")
        };
        let reuse = evidence
            .semantic_reuse()
            .expect("this outcome must be a proof-subsumption reuse");
        assert_eq!(
            reuse.original_request_digest(),
            request_before.request_digest()
        );
        assert_eq!(
            checker.semantic.prepare_calls, 3,
            "proof subsumption prepares but never launches"
        );
        assert_eq!(checker.semantic_reuses_total(), 2);
        assert_eq!(checker.proof_subsumption_hits_total(), 2);

        encoding.shutdown().await.unwrap();
        encoding_after.shutdown().await.unwrap();
        encoding_unrelated.shutdown().await.unwrap();
        drop(checker);
        owner.settle().unwrap();
    }

    /// The maintenance-role counterpart to
    /// `reconsideration_style_premise_change_forces_a_fresh_check_while_unchanged_premises_reuse`:
    /// clause `C`'s maintenance verification condition at level 1 depends on
    /// EVERY same-level candidate (Lean's `family.upTo clause.level`), not
    /// just the strictly-below premises an initialization check depends on.
    /// A newly placed same-level sibling `S` adds a `plain(S)` tag — again a
    /// strict tagged-set superset of the first check's, so it is served by
    /// proof subsumption exactly as the initialization counterpart's new
    /// below-level clause is; a clause strictly above the checked level
    /// leaves the tagged set unchanged and reuses identically.
    #[tokio::test(flavor = "current_thread")]
    async fn maintenance_same_level_candidate_change_forces_a_fresh_check_while_above_level_clause_reuses()
     {
        let directory = TestDirectory::new("semantic-reuse-maintenance-same-level");
        let task = production_test_task();
        let (owner, artifacts) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(directory.path().join("artifacts")),
        )
        .unwrap();
        let admission =
            create_general_solver_admission(RuntimeResourcePolicy::agent_only(1, 1).unwrap())
                .unwrap();

        let (ids_before, snapshot_before) =
            multi_clause_snapshot(&task, &[("C", 1)], &[("C", 1)], 2);
        let (ids_same_level_added, snapshot_same_level_added) =
            multi_clause_snapshot(&task, &[("C", 1), ("S", 1)], &[("C", 1), ("S", 1)], 2);
        let (ids_above_after, snapshot_above_after) =
            multi_clause_snapshot(&task, &[("C", 1), ("G", 2)], &[("C", 1), ("G", 2)], 2);

        let clause_c_identity: Arc<str> = Arc::from(
            snapshot_before
                .records()
                .get(&ids_before["C"])
                .unwrap()
                .formula()
                .identity_sha256(),
        );

        let request_before = FrameworkIICheckRequest::new(
            0,
            ids_before["C"],
            FrameworkIILevel::new(1),
            FrameworkIICheckRole::Maintenance,
            snapshot_before,
            false,
        )
        .unwrap();
        let request_same_level_added = FrameworkIICheckRequest::new(
            0,
            ids_same_level_added["C"],
            FrameworkIILevel::new(1),
            FrameworkIICheckRole::Maintenance,
            snapshot_same_level_added,
            false,
        )
        .unwrap();
        let request_above_after = FrameworkIICheckRequest::new(
            0,
            ids_above_after["C"],
            FrameworkIILevel::new(1),
            FrameworkIICheckRole::Maintenance,
            snapshot_above_after,
            false,
        )
        .unwrap();

        assert_ne!(
            semantic_key_of(&request_before),
            semantic_key_of(&request_same_level_added),
            "a newly placed same-level maintenance candidate must change the key"
        );
        assert_eq!(
            semantic_key_of(&request_before),
            semantic_key_of(&request_above_after),
            "a clause strictly above the checked level must not change a maintenance key"
        );

        let axiom_tags = FrameworkIIAxiomTagTable::for_test(vec![
            ("ax_guard", FrameworkIIPremiseTag::Guard),
            ("ax_not_theta_guard", FrameworkIIPremiseTag::NotThetaGuard),
            (
                "ax_plain_c",
                FrameworkIIPremiseTag::Plain(Arc::clone(&clause_c_identity)),
            ),
        ]);
        let (encoding, prepared_before) = applied_pre_check_fixture_with_axiom_tags(
            &task,
            &request_before,
            &artifacts,
            &admission,
            axiom_tags,
        )
        .await;
        let (encoding_same_level, prepared_same_level) = applied_pre_check_fixture_with_axiom_tags(
            &task,
            &request_same_level_added,
            &artifacts,
            &admission,
            axiom_tag_table_for(&request_same_level_added),
        )
        .await;
        let (encoding_above, prepared_above) = applied_pre_check_fixture_with_axiom_tags(
            &task,
            &request_above_after,
            &artifacts,
            &admission,
            axiom_tag_table_for(&request_above_after),
        )
        .await;
        let mut semantic = MultiRequestPreCheckSemantic::new();
        semantic.register(&request_before, prepared_before);
        semantic.register(&request_same_level_added, prepared_same_level);
        semantic.register(&request_above_after, prepared_above);
        let config = production_test_config(
            artifacts.clone(),
            proof_vampire_citing(
                directory.path(),
                "maint",
                &["ax_guard", "ax_not_theta_guard", "ax_plain_c"],
            ),
        );
        let mut checker = FrameworkIIProductionChecker::new(semantic, config);

        // First check: a real worker preparation and a real solver launch
        // proves C's maintenance VC at level 1 with no same-level siblings.
        // The fixture proof cites every premise it actually had, so the
        // recorded cited set equals this request's own full tagged set
        // exactly.
        let execution_before = checker.check(request_before.clone()).await.unwrap();
        assert!(
            matches!(
                execution_before,
                FrameworkIICheckExecution::Applied(FrameworkIICheckOutcome::Proved(_))
            ),
            "{execution_before:?}"
        );
        assert_eq!(checker.semantic.prepare_calls, 1);
        assert_eq!(checker.semantic_reuses_total(), 0);

        // Second check: same clause and level, but S is now a same-level
        // maintenance candidate, adding a `plain(S)` tag the first proof
        // never cited (S did not exist when it ran). The first proof's
        // cited set is therefore still contained in this request's own
        // (strictly larger) tagged set: a proof-subsumption hit, with zero
        // further worker preparation — sound because weakening an
        // already-closed entailment's hypotheses cannot break it.
        let execution_same_level_added = checker
            .check(request_same_level_added.clone())
            .await
            .unwrap();
        let FrameworkIICheckExecution::Applied(FrameworkIICheckOutcome::Proved(
            evidence_same_level_added,
        )) = execution_same_level_added
        else {
            panic!(
                "a same-level superset request must be served by proof subsumption: \
                 {execution_same_level_added:?}"
            )
        };
        let reuse_same_level_added = evidence_same_level_added
            .semantic_reuse()
            .expect("a same-level superset request must reuse the smaller premise set's proof");
        assert_eq!(
            reuse_same_level_added.kind(),
            FrameworkIISemanticReuseKind::ProofSubsumption
        );
        assert_eq!(
            reuse_same_level_added.original_request_digest(),
            request_before.request_digest()
        );
        assert_eq!(
            checker.semantic.prepare_calls, 2,
            "a same-level superset request prepares its own obligation for the \
             empty-instance re-check, but launches no solver"
        );
        assert_eq!(checker.semantic_reuses_total(), 1);
        assert_eq!(checker.proof_subsumption_hits_total(), 1);

        // Third check: same clause and level, only a clause strictly above
        // C's level differs from the first snapshot. The tagged set is
        // unchanged, so this reuses the first proof identically.
        let execution_above_after = checker.check(request_above_after.clone()).await.unwrap();
        let FrameworkIICheckExecution::Applied(FrameworkIICheckOutcome::Proved(evidence)) =
            execution_above_after
        else {
            panic!("a strictly-above-level clause must not block proof subsumption")
        };
        let reuse = evidence
            .semantic_reuse()
            .expect("this outcome must be a proof-subsumption reuse");
        assert_eq!(
            reuse.original_request_digest(),
            request_before.request_digest()
        );
        assert_eq!(
            checker.semantic.prepare_calls, 3,
            "proof subsumption prepares but never launches"
        );
        assert_eq!(checker.semantic_reuses_total(), 2);
        assert_eq!(checker.proof_subsumption_hits_total(), 2);

        encoding.shutdown().await.unwrap();
        encoding_same_level.shutdown().await.unwrap();
        encoding_above.shutdown().await.unwrap();
        drop(checker);
        owner.settle().unwrap();
    }

    // --------------------------------------------------------
    // Pass 7.5c-2: the level-free key, the retry policy, and the
    // termination request
    // --------------------------------------------------------

    /// `houdini.tex` Section 4.4: "The level `j` is not part of the key,
    /// since `g` and `T` determine the problem (the same problem recurs at
    /// `j` and `j+1` across a level the Core leaves empty, which Core
    /// compression can create)".
    #[test]
    fn the_level_free_key_serves_the_same_problem_at_j_and_j_plus_one() {
        let task = production_test_task();
        // `P` sits at level 0 and `C` at level 1; nothing occupies level 1
        // in the second placement, where `C` sits at level 2 instead. An
        // initialization request reads only the strictly-lower clauses, so
        // both requests denote the identical verification condition.
        let (ids_j, snapshot_j) =
            multi_clause_snapshot(&task, &[("C", 0), ("P", 0)], &[("C", 1), ("P", 0)], 3);
        let (ids_j1, snapshot_j1) =
            multi_clause_snapshot(&task, &[("C", 0), ("P", 0)], &[("C", 2), ("P", 0)], 3);
        let request_j = FrameworkIICheckRequest::new(
            0,
            ids_j["C"],
            FrameworkIILevel::new(1),
            FrameworkIICheckRole::Initialization,
            snapshot_j,
            false,
        )
        .unwrap();
        let request_j1 = FrameworkIICheckRequest::new(
            0,
            ids_j1["C"],
            FrameworkIILevel::new(2),
            FrameworkIICheckRole::Initialization,
            snapshot_j1,
            false,
        )
        .unwrap();
        assert_eq!(
            tagged_premise_set(&request_j),
            tagged_premise_set(&request_j1),
            "an empty Core level adds no premise"
        );
        assert_eq!(
            semantic_key_of(&request_j),
            semantic_key_of(&request_j1),
            "the semantic key is level-free: the same problem at j and j+1 keys identically"
        );
        assert_eq!(
            semantic_key_of(&request_j)["conjecture"],
            json!({"identity_sha256": snapshot_of(&request_j1)}),
            "the tagged conjecture is the role plus the clause identity, without a level"
        );
        assert!(
            semantic_key_of(&request_j).get("checked_level").is_none(),
            "the checked level is recorded on the ledger row only"
        );

        // Control: a clause that actually occupies the intervening level
        // adds a theta tag and therefore a different key.
        let (ids_occupied, snapshot_occupied) = multi_clause_snapshot(
            &task,
            &[("C", 0), ("P", 0), ("M", 0)],
            &[("C", 2), ("P", 0), ("M", 1)],
            3,
        );
        let request_occupied = FrameworkIICheckRequest::new(
            0,
            ids_occupied["C"],
            FrameworkIILevel::new(2),
            FrameworkIICheckRole::Initialization,
            snapshot_occupied,
            false,
        )
        .unwrap();
        assert_ne!(
            semantic_key_of(&request_j),
            semantic_key_of(&request_occupied),
            "a clause that really occupies the level changes the premise set"
        );
    }

    fn snapshot_of(request: &FrameworkIICheckRequest) -> String {
        request
            .snapshot()
            .records()
            .get(&request.clause())
            .unwrap()
            .formula()
            .identity_sha256()
            .to_owned()
    }

    /// The retry policy, the per-epoch launch bound, and the inconclusive
    /// dictionary entry, end to end (`houdini.tex` Section 4.4, Definition
    /// "Subsumption"; `TODO.md` Pass 7.5c-2, "Dictionary").
    #[tokio::test(flavor = "current_thread")]
    async fn inconclusive_entries_relaunch_once_per_epoch_until_the_policy_is_exhausted() {
        let directory = TestDirectory::new("inconclusive-entry-retry-policy");
        let task = production_test_task();
        let (owner, artifacts) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(directory.path().join("artifacts")),
        )
        .unwrap();
        let admission =
            create_general_solver_admission(RuntimeResourcePolicy::agent_only(1, 1).unwrap())
                .unwrap();

        // `C` at level 1 with nothing below it, and the same clause with a
        // fresh level-0 premise `N` — a genuinely different tagged set, so
        // a different key that starts again at the first allowance.
        let (ids_before, snapshot_before) =
            multi_clause_snapshot(&task, &[("C", 1)], &[("C", 1)], 2);
        let (ids_after, snapshot_after) =
            multi_clause_snapshot(&task, &[("C", 1), ("N", 0)], &[("C", 1), ("N", 0)], 2);
        let request = FrameworkIICheckRequest::new(
            0,
            ids_before["C"],
            FrameworkIILevel::new(1),
            FrameworkIICheckRole::Initialization,
            snapshot_before,
            false,
        )
        .unwrap();
        let request_core_changed = FrameworkIICheckRequest::new(
            0,
            ids_after["C"],
            FrameworkIILevel::new(1),
            FrameworkIICheckRole::Initialization,
            snapshot_after,
            false,
        )
        .unwrap();
        let (encoding, prepared) = applied_pre_check_fixture_with_axiom_tags(
            &task,
            &request,
            &artifacts,
            &admission,
            axiom_tag_table_for(&request),
        )
        .await;
        let (encoding_changed, prepared_changed) = applied_pre_check_fixture_with_axiom_tags(
            &task,
            &request_core_changed,
            &artifacts,
            &admission,
            axiom_tag_table_for(&request_core_changed),
        )
        .await;
        let mut semantic = MultiRequestPreCheckSemantic::new();
        semantic.register(&request, prepared);
        semantic.register(&request_core_changed, prepared_changed);

        // Every launch returns a model Lean refuses to validate: an
        // inconclusive outcome, deterministically.
        let first = Duration::from_secs(1);
        let second = Duration::from_secs(4);
        let config = production_test_config_with_admission(
            artifacts.clone(),
            model_vampire(directory.path()),
            admission.clone(),
        )
        .with_retry_policy(FrameworkIIRetryPolicy::new([first, second]).unwrap());
        let mut checker = FrameworkIIProductionChecker::new(semantic, config);
        let key: Arc<str> = Arc::from(canonical_value_sha256(&semantic_key_of(&request)));

        // Launch 1, under a_1.
        let launched = inconclusive_outcome(checker.check(request.clone()).await.unwrap());
        assert!(
            launched.semantic_reuse().is_none(),
            "an inconclusive launch carries no reuse provenance"
        );
        assert_eq!(
            launched
                .progress()
                .expect("a launch carries typed progress")
                .current_proof_allowance(),
            first
        );
        assert_eq!(checker.semantic.prepare_calls, 1);
        assert_eq!(
            checker
                .semantic_dictionary
                .find_inconclusive(&key)
                .unwrap()
                .launches,
            1
        );

        // A second check of the same key in the same epoch is a hit,
        // answered Inconclusive without a launch — and it says so.
        let reused = inconclusive_outcome(checker.check(request.clone()).await.unwrap());
        let reuse = reused
            .semantic_reuse()
            .expect("an inconclusive dictionary hit carries reuse provenance");
        assert_eq!(
            reuse.kind(),
            FrameworkIISemanticReuseKind::InconclusiveEntry
        );
        assert_eq!(reuse.semantic_vc_key(), key.as_ref());
        assert_eq!(
            checker.semantic.prepare_calls, 1,
            "an inconclusive hit never reaches worker preparation"
        );
        assert_eq!(checker.inconclusive_dictionary_hits_total(), 1);
        assert_eq!(
            checker
                .semantic_dictionary
                .find_inconclusive(&key)
                .unwrap()
                .launches,
            1,
            "a hit does not advance the launch count"
        );

        // The next epoch grants the second allowance, exactly once.
        checker.begin_epoch();
        let relaunched = inconclusive_outcome(checker.check(request.clone()).await.unwrap());
        assert!(relaunched.semantic_reuse().is_none());
        assert_eq!(
            relaunched
                .progress()
                .expect("a launch carries typed progress")
                .current_proof_allowance(),
            second,
            "the second launch of a key runs under a_2"
        );
        assert_eq!(checker.semantic.prepare_calls, 2);
        assert_eq!(
            checker
                .semantic_dictionary
                .find_inconclusive(&key)
                .unwrap()
                .launches,
            2
        );
        let same_epoch_again = inconclusive_outcome(checker.check(request.clone()).await.unwrap());
        assert!(
            same_epoch_again.semantic_reuse().is_some(),
            "a key is launched at most once per epoch"
        );
        assert_eq!(checker.semantic.prepare_calls, 2);

        // The list is exhausted: the key is now a permanent hit for the run.
        checker.begin_epoch();
        let permanent = inconclusive_outcome(checker.check(request.clone()).await.unwrap());
        assert!(
            permanent.semantic_reuse().is_some(),
            "after the allowance list is exhausted the key is a permanent hit"
        );
        assert_eq!(checker.semantic.prepare_calls, 2);
        assert_eq!(checker.inconclusive_dictionary_hits_total(), 3);

        // A Core change yields a new key, which starts again at a_1 in the
        // very same epoch.
        let fresh_key = inconclusive_outcome(checker.check(request_core_changed).await.unwrap());
        assert!(
            fresh_key.semantic_reuse().is_none(),
            "a changed Core is a different key and launches afresh"
        );
        assert_eq!(
            fresh_key
                .progress()
                .expect("a launch carries typed progress")
                .current_proof_allowance(),
            first,
            "a new key starts at the first allowance"
        );
        assert_eq!(checker.semantic.prepare_calls, 3);

        encoding.shutdown().await.unwrap();
        encoding_changed.shutdown().await.unwrap();
        settle_test_artifacts(checker, owner);
    }

    /// A retry launch's re-tagged rendering: the same problem, with the
    /// premises under the retry role and everything else untouched,
    /// published as its own artifact. The first launch's file is left
    /// exactly as it was written, and a second retry of the same rung
    /// resolves to the same re-tagged artifact rather than a new one.
    #[tokio::test(flavor = "current_thread")]
    async fn a_retry_role_republishes_the_problem_without_touching_the_first() {
        let directory = TestDirectory::new("retry-premise-role");
        let task = production_test_task();
        let (owner, artifacts) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(directory.path().join("artifacts")),
        )
        .unwrap();
        let admission =
            create_general_solver_admission(RuntimeResourcePolicy::agent_only(1, 1).unwrap())
                .unwrap();
        let (_ids, snapshot) = multi_clause_snapshot(&task, &[("C", 1)], &[("C", 1)], 2);
        let relation = task.solver_relations()[0].key().clone();
        let binding = FixedAmbientWorkerBinding::for_test(
            task.identity().clone(),
            snapshot.scope().identity().clone(),
        );
        let encoding = new_fixed_ambient_encoding_context(
            binding,
            [relation.clone()],
            Vec::<crate::task::ConstantKey>::new(),
            FixedAmbientWorkerPoolConfig::new(
                FixedAmbientWorkerCommand::new("/bin/true", PathBuf::from("/")),
                1,
            )
            .unwrap(),
        )
        .unwrap();
        let (revision, mappings) = encoding
            .name_snapshot([relation], Vec::<crate::task::ConstantKey>::new())
            .unwrap();
        let relation_bindings = mappings
            .into_iter()
            .map(|mapping| json!({"key": mapping.key, "name": mapping.tptp_name}))
            .collect::<Vec<_>>();
        let adopt = |source_id: &str, body: &str| {
            let data: FixedAmbientPreparedBodyData = serde_json::from_value(json!({
                "source_id": source_id,
                "source_kind": "quantifier_free",
                "exact_constant_keys": [],
                "body": body,
                "referenced_relations": [],
                "referenced_constants": [],
            }))
            .unwrap();
            encoding.adopt_body(data, revision).unwrap()
        };
        let premises = vec![
            adopt("framework-ii-retry-role-premise-0", "$true"),
            adopt("framework-ii-retry-role-premise-1", "$false"),
        ];
        let goal = adopt("framework-ii-retry-role-goal", "$true");
        let support_data: FixedAmbientPreparedSupportData = serde_json::from_value(json!({
            "constant_keys": [],
            "adom_body": "$true",
            "distinct_bodies": [],
            "referenced_relations": relation_bindings,
            "referenced_constants": [],
        }))
        .unwrap();
        let support = encoding.adopt_support(support_data, revision).unwrap();
        let first = assemble_fixed_ambient_entailment_with_support(
            &encoding,
            &admission,
            &artifacts,
            json!({
                "axioms": [{"kind": "retry_role_premise_0"}, {"kind": "retry_role_premise_1"}],
                "conjecture": {"kind": "retry_role_goal"},
            }),
            premises,
            vec![goal],
            support,
            &CancellationToken::new(),
        )
        .await
        .unwrap();
        let read_query = |entailment: &Entailment| {
            let resolved = artifacts.resolve(entailment.query_artifact()).unwrap();
            std::fs::read_to_string(resolved.path()).unwrap()
        };
        let first_text = read_query(&first);
        assert_eq!(first.premise_role(), PremiseRole::Axiom);

        let retag = async |role| {
            first
                .with_premise_role(role, &admission, &artifacts, &CancellationToken::new())
                .await
                .unwrap()
        };
        let retagged = retag(PremiseRole::NegatedConjecture).await;
        assert_eq!(
            retagged.identity(),
            first.identity(),
            "a role word is not part of the logical identity"
        );
        assert_ne!(
            retagged.query_artifact(),
            first.query_artifact(),
            "the two renderings are distinct immutable artifacts"
        );
        let retagged_text = read_query(&retagged);
        let mut premise_lines = 0;
        for (before, after) in first_text.lines().zip(retagged_text.lines()) {
            if before.starts_with("fof(axiom_") {
                premise_lines += 1;
                assert_eq!(
                    after,
                    before.replacen(", axiom, ", ", negated_conjecture, ", 1),
                    "a premise keeps its name, body and position"
                );
            } else {
                assert_eq!(after, before, "only the premises change role");
            }
        }
        assert_eq!(premise_lines, 2);
        assert_eq!(first_text.lines().count(), retagged_text.lines().count());
        assert!(retagged_text.contains("fof(support_adom, axiom, "));
        assert!(retagged_text.contains("fof(goal, conjecture, "));
        assert_eq!(
            read_query(&first),
            first_text,
            "the first launch's artifact is not rewritten"
        );
        assert_eq!(
            retag(PremiseRole::NegatedConjecture).await.query_artifact(),
            retagged.query_artifact(),
            "the same rendering resolves to the same content-addressed artifact"
        );
        assert_eq!(
            retag(PremiseRole::Axiom).await.query_artifact(),
            first.query_artifact(),
            "the flag's ablation value leaves a retry on today's bytes"
        );

        encoding.shutdown().await.unwrap();
        drop(first);
        drop(retagged);
        drop(artifacts);
        owner.settle().unwrap();
    }

    fn inconclusive_outcome(execution: FrameworkIICheckExecution) -> FrameworkIICheckEvidence {
        match execution {
            FrameworkIICheckExecution::Applied(FrameworkIICheckOutcome::Inconclusive {
                progress,
                ..
            }) => progress,
            other => panic!("expected an inconclusive outcome, got {other:?}"),
        }
    }

    /// `houdini.tex` Section 4.4: "on an unknown name or an empty citation
    /// it records the request's full tagged set instead, which is always a
    /// sound cited set".
    #[tokio::test(flavor = "current_thread")]
    async fn a_proof_with_an_unknown_axiom_name_records_the_full_tagged_set() {
        let directory = TestDirectory::new("full-tagged-set-fallback");
        let task = production_test_task();
        let (owner, artifacts) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(directory.path().join("artifacts")),
        )
        .unwrap();
        let admission =
            create_general_solver_admission(RuntimeResourcePolicy::agent_only(1, 1).unwrap())
                .unwrap();
        let (ids, snapshot) = multi_clause_snapshot(&task, &[("C", 1)], &[("C", 1)], 2);
        let request = FrameworkIICheckRequest::new(
            0,
            ids["C"],
            FrameworkIILevel::new(1),
            FrameworkIICheckRole::Initialization,
            snapshot,
            false,
        )
        .unwrap();
        let (encoding, prepared) = applied_pre_check_fixture_with_axiom_tags(
            &task,
            &request,
            &artifacts,
            &admission,
            axiom_tag_table_for(&request),
        )
        .await;
        let mut semantic = MultiRequestPreCheckSemantic::new();
        semantic.register(&request, prepared);
        let config = production_test_config(
            artifacts.clone(),
            // The proof cites a name Lean's table never issued.
            proof_vampire_citing(directory.path(), "unknown", &["ax_from_another_problem"]),
        );
        let mut checker = FrameworkIIProductionChecker::new(semantic, config);

        let execution = checker.check(request.clone()).await.unwrap();
        assert!(
            matches!(
                execution,
                FrameworkIICheckExecution::Applied(FrameworkIICheckOutcome::Proved(_))
            ),
            "{execution:?}"
        );
        assert_eq!(checker.full_tagged_set_fallbacks_total(), 1);

        let full = tagged_premise_set(&request);
        let conjecture = conjecture_of(&request);
        let entry = checker
            .semantic_dictionary
            .find_proof_hit(&conjecture, &full)
            .expect("the fallback entry is recorded and hits its own request");
        assert_eq!(
            entry.cited.as_ref(),
            &full,
            "a fail-closed citation records the request's own full tagged set"
        );

        // Soundness under subsumption: a strictly smaller premise set does
        // not hit; only a superset does.
        let mut smaller = full.clone();
        smaller.remove(&FrameworkIIPremiseTag::NotThetaGuard);
        assert!(
            checker
                .semantic_dictionary
                .find_proof_hit(&conjecture, &smaller)
                .is_none(),
            "the full-tagged-set fallback never subsumes a weaker request"
        );
        let mut larger = full;
        larger.insert(FrameworkIIPremiseTag::Theta(Arc::from("a".repeat(64))));
        assert!(
            checker
                .semantic_dictionary
                .find_proof_hit(&conjecture, &larger)
                .is_some()
        );

        encoding.shutdown().await.unwrap();
        settle_test_artifacts(checker, owner);
    }

    /// `houdini.tex` Section 4.4: "Every proof hit therefore repeats Lean's
    /// empty-instance check on the new obligation before it counts as
    /// Proved ... Lean finds a counterexample at the empty instance: o <-
    /// Refuted, validated; record it; return o."
    ///
    /// The refutation is committed on the already-begun attempt, with no
    /// solver launch of its own: the stub proves once and then times out,
    /// so a fall-through to the launch path would answer Inconclusive and
    /// leave its relaunch marker behind.
    #[tokio::test(flavor = "current_thread")]
    async fn a_proof_reuse_with_an_empty_counterexample_is_a_validated_refutation() {
        let directory = TestDirectory::new("proof-reuse-empty-counterexample");
        let task = production_test_task();
        let (owner, artifacts) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(directory.path().join("artifacts")),
        )
        .unwrap();
        let admission =
            create_general_solver_admission(RuntimeResourcePolicy::agent_only(1, 1).unwrap())
                .unwrap();
        let (ids_before, snapshot_before) =
            multi_clause_snapshot(&task, &[("C", 1)], &[("C", 1)], 2);
        let (ids_after, snapshot_after) =
            multi_clause_snapshot(&task, &[("C", 1), ("N", 0)], &[("C", 1), ("N", 0)], 2);
        let request_before = FrameworkIICheckRequest::new(
            0,
            ids_before["C"],
            FrameworkIILevel::new(1),
            FrameworkIICheckRole::Initialization,
            snapshot_before,
            false,
        )
        .unwrap();
        let request_after = FrameworkIICheckRequest::new(
            0,
            ids_after["C"],
            FrameworkIILevel::new(1),
            FrameworkIICheckRole::Initialization,
            snapshot_after,
            false,
        )
        .unwrap();
        let (encoding, prepared_before) = applied_pre_check_fixture_with_axiom_tags(
            &task,
            &request_before,
            &artifacts,
            &admission,
            axiom_tag_table_for(&request_before),
        )
        .await;
        let (encoding_after, prepared_after) = applied_pre_check_fixture_with_axiom_tags(
            &task,
            &request_after,
            &artifacts,
            &admission,
            axiom_tag_table_for(&request_after),
        )
        .await;
        let mut semantic = MultiRequestPreCheckSemantic::new();
        semantic.register(&request_before, prepared_before);
        semantic.register(&request_after, prepared_after.clone());
        // The reusing request's own obligation is falsified at the empty
        // instance — the premise that excluded it is one the original proof
        // never cited.
        semantic.with_empty_counterexample(&prepared_after);
        let (command, relaunch_marker) =
            proof_then_timeout_vampire(directory.path(), "init-reuse", &["ax_pre"]);
        let config = production_test_config(artifacts.clone(), command);
        let mut checker = FrameworkIIProductionChecker::new(semantic, config);

        let proved = checker.check(request_before.clone()).await.unwrap();
        assert!(
            matches!(
                proved,
                FrameworkIICheckExecution::Applied(FrameworkIICheckOutcome::Proved(_))
            ),
            "{proved:?}"
        );

        let execution = checker.check(request_after.clone()).await.unwrap();
        let FrameworkIICheckExecution::Applied(FrameworkIICheckOutcome::Refuted(evidence)) =
            execution
        else {
            panic!("an empty-instance counterexample must refute, never reuse: {execution:?}")
        };
        assert!(
            evidence.semantic_reuse().is_none(),
            "the refutation is this request's own validated authority, not a reuse"
        );
        let refutation = evidence
            .validated_refutation()
            .expect("a refuted outcome carries validated-refutation authority");
        assert_eq!(refutation.request_digest(), request_after.request_digest());
        assert_eq!(
            checker.proof_subsumption_hits_total(),
            0,
            "the proof entry never closed this request"
        );
        assert!(
            checker
                .countermodel_of_attempt(refutation.attempt())
                .is_some(),
            "the countermodel is retained under the refuting attempt's id"
        );
        assert!(
            !relaunch_marker.exists(),
            "the empty-instance counterexample commits without a second launch"
        );

        encoding.shutdown().await.unwrap();
        encoding_after.shutdown().await.unwrap();
        settle_test_artifacts(checker, owner);
    }

    /// The termination request of `houdini.tex` Table 1: tagged premises
    /// `{not_guard} ∪ {collapsed(d) : d ∈ Core}`, the fixed tagged
    /// conjecture `(Term, post')`, and a key over the Core's sorted
    /// identity list without levels.
    #[test]
    fn the_termination_request_tags_the_core_and_keys_without_levels() {
        let task = production_test_task();
        let (_, core) =
            multi_clause_snapshot(&task, &[("C", 0), ("D", 0)], &[("C", 0), ("D", 1)], 2);
        let (_, relevelled) =
            multi_clause_snapshot(&task, &[("C", 0), ("D", 0)], &[("C", 1), ("D", 0)], 2);
        let (_, smaller) = multi_clause_snapshot(&task, &[("C", 0)], &[("C", 0)], 2);

        let tags = termination_tagged_premise_set(&core);
        assert!(tags.contains(&FrameworkIIPremiseTag::NotGuard));
        assert_eq!(
            tags.len(),
            3,
            "one not_guard tag plus one collapsed tag per Core clause"
        );
        assert!(
            tags.iter()
                .filter(|tag| matches!(tag, FrameworkIIPremiseTag::Collapsed(_)))
                .count()
                == 2
        );

        let request = FrameworkIITerminationRequest::new(Arc::clone(&core));
        let relevelled_request = FrameworkIITerminationRequest::new(Arc::clone(&relevelled));
        let smaller_request = FrameworkIITerminationRequest::new(Arc::clone(&smaller));
        assert_eq!(
            request.core_identities().len(),
            2,
            "the key's premise representation is the sorted Core identity list"
        );
        assert!(request.core_identities().windows(2).all(|w| w[0] < w[1]));

        let subject = FrameworkIICheckSubject::Termination(request);
        let relevelled_subject = FrameworkIICheckSubject::Termination(relevelled_request);
        let smaller_subject = FrameworkIICheckSubject::Termination(smaller_request);
        assert_eq!(
            semantic_vc_key_identity(&subject),
            semantic_vc_key_identity(&relevelled_subject),
            "the termination key ranges over the Core's clause set, never its levels"
        );
        assert_ne!(
            semantic_vc_key_identity(&subject),
            semantic_vc_key_identity(&smaller_subject),
            "a changed Core clause set is a different termination key"
        );
        assert_eq!(
            conjecture_identity_of(&subject),
            conjecture_identity_of(&smaller_subject),
            "every termination request shares the one tagged conjecture (Term, post')"
        );
        assert_ne!(
            conjecture_identity_of(&subject),
            Arc::<str>::from("initialization:x"),
        );
    }

    /// The termination check runs through `Check(q)` like any other
    /// request: launched once, then served from the dictionary while the
    /// Core's clause set is unchanged.
    #[tokio::test(flavor = "current_thread")]
    async fn the_termination_check_is_a_dictionary_hit_while_the_core_is_unchanged() {
        let directory = TestDirectory::new("termination-check-dictionary");
        let task = production_test_task();
        let (owner, artifacts) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(directory.path().join("artifacts")),
        )
        .unwrap();
        let admission =
            create_general_solver_admission(RuntimeResourcePolicy::agent_only(1, 1).unwrap())
                .unwrap();
        let (_, core) = multi_clause_snapshot(&task, &[("C", 0)], &[("C", 0)], 2);
        // The same clause set at another level: a different snapshot, the
        // same termination key.
        let (_, relevelled) = multi_clause_snapshot(&task, &[("C", 0)], &[("C", 1)], 2);

        let subject = FrameworkIICheckSubject::Termination(FrameworkIITerminationRequest::new(
            Arc::clone(&core),
        ));
        let relevelled_subject = FrameworkIICheckSubject::Termination(
            FrameworkIITerminationRequest::new(Arc::clone(&relevelled)),
        );
        let (encoding, prepared) = applied_pre_check_fixture_for_subject(
            &task,
            &subject,
            &artifacts,
            &admission,
            termination_axiom_tag_table(&core),
        )
        .await;
        let (encoding_relevelled, prepared_relevelled) = applied_pre_check_fixture_for_subject(
            &task,
            &relevelled_subject,
            &artifacts,
            &admission,
            termination_axiom_tag_table(&relevelled),
        )
        .await;
        let mut semantic = MultiRequestPreCheckSemantic::new();
        semantic.register_subject(&subject, prepared);
        semantic.register_subject(&relevelled_subject, prepared_relevelled);
        let config = production_test_config(
            artifacts.clone(),
            proof_vampire_citing(directory.path(), "term", &["ax_not_guard"]),
        );
        let mut checker = FrameworkIIProductionChecker::new(semantic, config);

        let first = checker.check_termination(Arc::clone(&core)).await.unwrap();
        let FrameworkIICheckExecution::Applied(FrameworkIICheckOutcome::Proved(evidence)) = first
        else {
            panic!("the fixture proof closes the termination request: {first:?}")
        };
        assert!(
            evidence.semantic_reuse().is_none(),
            "the first check launches"
        );
        assert_eq!(checker.semantic.prepare_calls, 1);

        // An epoch that did not change the Core's clause set is answered
        // from the dictionary without a launch, even though every clause
        // moved a level.
        let second = checker
            .check_termination(Arc::clone(&relevelled))
            .await
            .unwrap();
        let FrameworkIICheckExecution::Applied(FrameworkIICheckOutcome::Proved(evidence)) = second
        else {
            panic!("an unchanged Core is served from the dictionary: {second:?}")
        };
        assert_eq!(
            evidence
                .semantic_reuse()
                .expect("an unchanged Core reuses the earlier termination proof")
                .kind(),
            FrameworkIISemanticReuseKind::ProofSubsumption
        );
        assert_eq!(checker.proof_subsumption_hits_total(), 1);

        encoding.shutdown().await.unwrap();
        encoding_relevelled.shutdown().await.unwrap();
        settle_test_artifacts(checker, owner);
    }

    /// A refuted termination check retains its countermodel under the
    /// launching attempt's id, exactly like a refuted clause check, so the
    /// `countermodel` tool can address it.
    #[tokio::test(flavor = "current_thread")]
    async fn a_refuted_termination_check_retains_its_countermodel_by_attempt() {
        let directory = TestDirectory::new("termination-check-refuted");
        let task = production_test_task();
        let (owner, artifacts) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(directory.path().join("artifacts")),
        )
        .unwrap();
        let admission =
            create_general_solver_admission(RuntimeResourcePolicy::agent_only(1, 1).unwrap())
                .unwrap();
        let (_, core) = multi_clause_snapshot(&task, &[("C", 0)], &[("C", 0)], 2);
        let subject = FrameworkIICheckSubject::Termination(FrameworkIITerminationRequest::new(
            Arc::clone(&core),
        ));
        let (encoding, prepared) = applied_pre_check_fixture_for_subject(
            &task,
            &subject,
            &artifacts,
            &admission,
            termination_axiom_tag_table(&core),
        )
        .await;
        let mut semantic = MultiRequestPreCheckSemantic::new();
        semantic.register_subject(&subject, prepared.clone());
        semantic.with_empty_counterexample(&prepared);
        let config = production_test_config(
            artifacts.clone(),
            proof_vampire_citing(directory.path(), "term-refuted", &["ax_not_guard"]),
        );
        let mut checker = FrameworkIIProductionChecker::new(semantic, config);

        let execution = checker.check_termination(Arc::clone(&core)).await.unwrap();
        let FrameworkIICheckExecution::Applied(FrameworkIICheckOutcome::Refuted(evidence)) =
            execution
        else {
            panic!("the empty-instance counterexample refutes termination: {execution:?}")
        };
        let refutation = evidence
            .validated_refutation()
            .expect("a refuted termination check carries validated-refutation authority");
        assert!(
            checker
                .countermodel_of_attempt(refutation.attempt())
                .is_some(),
            "a refuted termination check's countermodel is addressable by attempt id"
        );

        // And the refutation enters the dictionary under the termination
        // conjecture, so an unchanged Core is answered without a launch.
        let again = checker.check_termination(Arc::clone(&core)).await.unwrap();
        let FrameworkIICheckExecution::Applied(FrameworkIICheckOutcome::Refuted(reused)) = again
        else {
            panic!("an unchanged Core reuses the refutation: {again:?}")
        };
        assert_eq!(
            reused
                .semantic_reuse()
                .expect("the second check is a reuse")
                .kind(),
            FrameworkIISemanticReuseKind::RefutationSubsumption
        );

        encoding.shutdown().await.unwrap();
        settle_test_artifacts(checker, owner);
    }

    /// Pass 7.5c-2 verification bullet: "for every prepared request, the
    /// tagged set Rust computes equals the tag multiset of the issued
    /// `axiom_tags` table". This pins it directly over every request kind
    /// the fixtures build, with `support` excluded on both sides. On the
    /// live path the same agreement is checked end to end and byte for
    /// byte by the assembly differential, which compares Rust's whole
    /// assembled table against the worker's own.
    #[test]
    fn the_computed_tagged_set_equals_the_issued_axiom_tag_table() {
        let task = production_test_task();
        let (ids, snapshot) = multi_clause_snapshot(
            &task,
            &[("A", 0), ("B", 0), ("C", 0)],
            &[("A", 0), ("B", 1), ("C", 2)],
            3,
        );
        for (clause, level) in [("A", 0u64), ("B", 1), ("C", 2)] {
            for role in FRAMEWORK_II_CHECK_ROLES {
                let request = FrameworkIICheckRequest::new(
                    0,
                    ids[clause],
                    FrameworkIILevel::new(level),
                    role,
                    Arc::clone(&snapshot),
                    false,
                )
                .unwrap();
                let mut issued = axiom_tag_table_for(&request).issued_tagged_premise_set();
                // Lean also issues the support block; it is excluded on
                // both sides, so adding one here must not change the
                // comparison.
                issued.remove(&FrameworkIIPremiseTag::Support);
                assert_eq!(
                    issued,
                    tagged_premise_set(&request),
                    "{role:?} at level {level} for clause {clause}"
                );
            }
        }
        let termination = termination_axiom_tag_table(&snapshot).issued_tagged_premise_set();
        assert_eq!(termination, termination_tagged_premise_set(&snapshot));
    }
}
