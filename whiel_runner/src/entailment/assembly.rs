//! Exact assembly of prepared solver bodies into one Vampire query.

use std::collections::BTreeSet;
use std::fmt::{self, Write as _};
use std::io::Read;
use std::path::Path;
use std::sync::Arc;

use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::artifact::{ArtifactRef, ArtifactStore};
use crate::encoding::{
    EncodingError, FixedAmbientEncodingContext, PreparedBodyRef, SolverBodySource,
    SolverEncodingContext, SupportBlockRef, canonical_value_sha256,
};
use crate::failure::{FailureKind, FailureReport, FailureScope};
use crate::runtime::{AdmissionError, CancellationToken, CpuJobError, SolverAdmission};
use crate::task::{ConstantKey, TaskIdentity};
use crate::vampire::{VampireModel, VampireProblem, VampireProof};

// ------------------------------------------------------------
// Premise Role
// ------------------------------------------------------------

/// The TPTP role the premises of an assembled query are written under.
///
/// Both values assert exactly the same formulas: a `negated_conjecture`
/// formula is asserted as written, not negated, so the two renderings are
/// the same logical problem and differ only in the word. The role is a
/// search hint. Vampire classifies `axiom` formulas as background theory
/// and deprioritises them, which is wrong for a loop-invariant check whose
/// premises are the hypotheses of the very implication being proved;
/// writing them as goal-derived lets the proof search treat them as such.
///
/// Rust forms no connective here. It copies each Lean-emitted body verbatim
/// and chooses one of these two role words.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PremiseRole {
    /// The role every first launch uses.
    #[default]
    Axiom,
    NegatedConjecture,
}

impl PremiseRole {
    /// The stable TPTP role word, which is also the name the run
    /// configuration records and the CLI accepts.
    pub fn name(self) -> &'static str {
        match self {
            Self::Axiom => "axiom",
            Self::NegatedConjecture => "negated_conjecture",
        }
    }

    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "axiom" => Some(Self::Axiom),
            "negated_conjecture" => Some(Self::NegatedConjecture),
            _ => None,
        }
    }
}

// ------------------------------------------------------------
// Immutable Entailment Package
// ------------------------------------------------------------

/*
  One package retains exact source-linked bodies and one immutable
  query artifact. Its logical identity excludes execution attempts.
*/

#[derive(Clone)]
pub struct Entailment {
    inner: Arc<EntailmentData>,
}

struct EntailmentData {
    identity: Arc<str>,
    context: EntailmentContext,
    fixed_ambient_identity: Option<Arc<Value>>,
    constants: Arc<[ConstantKey]>,
    support: SupportBlockRef,
    axiom_bodies: Arc<[PreparedBodyRef]>,
    goal_bodies: Arc<[PreparedBodyRef]>,
    query_artifact: ArtifactRef,
    premise_role: PremiseRole,
}

#[derive(Clone)]
enum EntailmentContext {
    Legacy(SolverEncodingContext),
    FixedAmbient(FixedAmbientEncodingContext),
}

impl EntailmentContext {
    fn context_id(&self) -> &str {
        match self {
            Self::Legacy(context) => context.context_id(),
            Self::FixedAmbient(context) => context.context_id(),
        }
    }

    fn task_identity(&self) -> &TaskIdentity {
        match self {
            Self::Legacy(context) => context.task_identity(),
            Self::FixedAmbient(context) => context.task_identity(),
        }
    }
}

impl fmt::Debug for Entailment {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("Entailment")
            .field("identity", &self.inner.identity)
            .field("context_id", &self.inner.context.context_id())
            .field("constant_count", &self.inner.constants.len())
            .field("axiom_count", &self.inner.axiom_bodies.len())
            .field("goal_count", &self.inner.goal_bodies.len())
            .field("query_artifact", &self.inner.query_artifact)
            .finish()
    }
}

impl Entailment {
    /// Return the exact logical identity used across solver attempts.
    pub fn identity(&self) -> &str {
        &self.inner.identity
    }

    /// Clone the small shared identity handle for runtime caches.
    pub fn identity_arc(&self) -> Arc<str> {
        Arc::clone(&self.inner.identity)
    }

    /// Return the context which owns every prepared component.
    pub fn context(&self) -> &SolverEncodingContext {
        match &self.inner.context {
            EntailmentContext::Legacy(context) => context,
            EntailmentContext::FixedAmbient(_) => {
                panic!("fixed-ambient entailments require their typed closer")
            }
        }
    }

    pub fn context_id(&self) -> &str {
        self.inner.context.context_id()
    }

    pub fn task_identity(&self) -> &TaskIdentity {
        self.inner.context.task_identity()
    }

    /// Return the complete Lean-emitted identity for a fixed-ambient package.
    pub(crate) fn fixed_ambient_identity(&self) -> Option<&Value> {
        self.inner.fixed_ambient_identity.as_deref()
    }

    /// Compare every retained field which can affect a fixed-ambient query.
    ///
    /// Cache maps may use compact digests for lookup, but a digest is never
    /// sufficient to establish equality at an authority boundary.
    pub(crate) fn same_exact_fixed_ambient_package(&self, other: &Self) -> bool {
        self.fixed_ambient_identity().is_some()
            && self.fixed_ambient_identity() == other.fixed_ambient_identity()
            && self.context_id() == other.context_id()
            && self.task_identity() == other.task_identity()
            && self.constants() == other.constants()
            && same_support_block(self.support_block(), other.support_block())
            && same_prepared_bodies(self.axiom_bodies(), other.axiom_bodies())
            && same_prepared_bodies(self.goal_bodies(), other.goal_bodies())
            && self.query_artifact() == other.query_artifact()
    }

    pub(crate) fn retained_proof(
        &self,
        attempt: crate::artifact::AttemptId,
    ) -> Option<VampireProof> {
        match &self.inner.context {
            EntailmentContext::Legacy(context) => context.retained_proof(self.identity(), attempt),
            EntailmentContext::FixedAmbient(context) => context.retained_proof(
                self.fixed_ambient_identity()
                    .expect("every fixed-ambient entailment retains its Lean identity"),
                self.identity(),
                attempt,
            ),
        }
    }

    pub(crate) fn retain_proof(
        &self,
        attempt: crate::artifact::AttemptId,
        proof: VampireProof,
    ) -> Result<VampireProof, EncodingError> {
        match &self.inner.context {
            EntailmentContext::Legacy(context) => {
                context.retain_proof(self.identity_arc(), attempt, proof)
            }
            EntailmentContext::FixedAmbient(context) => context.retain_proof(
                self.fixed_ambient_identity()
                    .expect("every fixed-ambient entailment retains its Lean identity"),
                self.identity_arc(),
                attempt,
                proof,
            ),
        }
    }

    pub(crate) fn retained_model(
        &self,
        attempt: crate::artifact::AttemptId,
    ) -> Option<VampireModel> {
        match &self.inner.context {
            EntailmentContext::Legacy(context) => context.retained_model(self.identity(), attempt),
            EntailmentContext::FixedAmbient(context) => context.retained_model(
                self.fixed_ambient_identity()
                    .expect("every fixed-ambient entailment retains its Lean identity"),
                self.identity(),
                attempt,
            ),
        }
    }

    pub(crate) fn retain_model(
        &self,
        attempt: crate::artifact::AttemptId,
        model: VampireModel,
    ) -> Result<VampireModel, EncodingError> {
        match &self.inner.context {
            EntailmentContext::Legacy(context) => {
                context.retain_model(self.identity_arc(), attempt, model)
            }
            EntailmentContext::FixedAmbient(context) => context.retain_model(
                self.fixed_ambient_identity()
                    .expect("every fixed-ambient entailment retains its Lean identity"),
                self.identity_arc(),
                attempt,
                model,
            ),
        }
    }

    /// Return the exact sorted union used to select the support block.
    pub fn constants(&self) -> &[ConstantKey] {
        &self.inner.constants
    }

    pub fn support_block(&self) -> &SupportBlockRef {
        &self.inner.support
    }

    pub fn axiom_bodies(&self) -> &[PreparedBodyRef] {
        &self.inner.axiom_bodies
    }

    pub fn goal_bodies(&self) -> &[PreparedBodyRef] {
        &self.inner.goal_bodies
    }

    /// Return the sole immutable artifact containing the assembled query.
    pub fn query_artifact(&self) -> ArtifactRef {
        self.inner.query_artifact
    }

    /// The TPTP role this package's premises are written under.
    pub fn premise_role(&self) -> PremiseRole {
        self.inner.premise_role
    }

    /// The same package with its premises written under `premise_role`.
    ///
    /// The formulas, their names and their order are untouched, so the
    /// structural identity is unchanged and this is the same logical
    /// entailment: only the role word each premise carries differs. The
    /// re-rendered bytes are published as their own content-addressed
    /// artifact, so a launch that re-tags neither overwrites nor reuses the
    /// artifact of a launch that did not.
    pub(crate) async fn with_premise_role(
        &self,
        premise_role: PremiseRole,
        admission: &SolverAdmission,
        artifacts: &ArtifactStore,
        cancellation: &CancellationToken,
    ) -> Result<Self, EncodingError> {
        if premise_role == self.inner.premise_role {
            return Ok(self.clone());
        }
        if artifacts.task_identity() != self.task_identity()
            || artifacts.backend_id() != self.inner.query_artifact.backend_id()
        {
            return Err(shared_failure(
                "entailment re-tagging was asked for another run backend",
            ));
        }
        let domain = match &self.inner.context {
            EntailmentContext::Legacy(_) => "whiel-query-v1",
            EntailmentContext::FixedAmbient(_) => "whiel-fixed-ambient-query-v1",
        };
        let support = self.inner.support.clone();
        let axiom_bodies = Arc::clone(&self.inner.axiom_bodies);
        let goal_bodies = Arc::clone(&self.inner.goal_bodies);
        let render = move |job_cancellation: CancellationToken| {
            let support_text = support
                .role_neutral_bodies()
                .iter()
                .map(AsRef::as_ref)
                .collect::<Vec<&str>>();
            let axiom_text = axiom_bodies
                .iter()
                .map(PreparedBodyRef::tptp_body)
                .collect::<Vec<_>>();
            let goal_text = goal_bodies
                .iter()
                .map(PreparedBodyRef::tptp_body)
                .collect::<Vec<_>>();
            let query = render_query(
                &support_text,
                &axiom_text,
                &goal_text,
                premise_role,
                &job_cancellation,
            )?;
            let content_identity = content_identity(domain, query.as_bytes());
            Ok((content_identity, Arc::<[u8]>::from(query.into_bytes())))
        };
        let (content_identity, bytes) = match &self.inner.context {
            EntailmentContext::Legacy(context) => {
                context.run_cpu_job(admission, cancellation, render).await
            }
            EntailmentContext::FixedAmbient(context) => {
                context.run_cpu_job(admission, cancellation, render).await
            }
        }
        .map_err(cpu_encoding_error)?;
        let publication = artifacts.publish_query(content_identity, bytes);
        tokio::pin!(publication);
        let query_artifact = tokio::select! {
            biased;
            _ = cancellation.cancelled() => return Err(EncodingError::Cancelled),
            result = &mut publication => result.map_err(publication_error)?,
        };
        Ok(Self {
            inner: Arc::new(EntailmentData {
                identity: Arc::clone(&self.inner.identity),
                context: self.inner.context.clone(),
                fixed_ambient_identity: self.inner.fixed_ambient_identity.clone(),
                constants: Arc::clone(&self.inner.constants),
                support: self.inner.support.clone(),
                axiom_bodies: Arc::clone(&self.inner.axiom_bodies),
                goal_bodies: Arc::clone(&self.inner.goal_bodies),
                query_artifact,
                premise_role,
            }),
        })
    }

    /// Resolve the query artifact at the existing Vampire path boundary.
    pub fn vampire_problem(
        &self,
        artifacts: &ArtifactStore,
    ) -> Result<VampireProblem, FailureReport> {
        if artifacts.task_identity() != self.task_identity()
            || artifacts.backend_id() != self.inner.query_artifact.backend_id()
        {
            return Err(FailureReport::encoding_preparation(
                FailureKind::InfrastructureFailure,
                FailureScope::RunGlobal,
                "entailment query was resolved through another run backend",
            ));
        }
        let query = artifacts.resolve(self.inner.query_artifact)?;
        Ok(
            VampireProblem::new(Arc::clone(&self.inner.identity), query.path())
                .with_query_artifact(self.inner.query_artifact)
                .with_premise_role(self.inner.premise_role),
        )
    }
}

fn same_prepared_bodies(left: &[PreparedBodyRef], right: &[PreparedBodyRef]) -> bool {
    left.len() == right.len()
        && left.iter().zip(right).all(|(left, right)| {
            left.context_id() == right.context_id()
                && left.source().same_identity(right.source())
                && left.body_id() == right.body_id()
                && left.fol_identity() == right.fol_identity()
                && left.tptp_body() == right.tptp_body()
                && left.constants() == right.constants()
                && left.preparation_revision() == right.preparation_revision()
                && left.theorem_id() == right.theorem_id()
                && left.semantic_version() == right.semantic_version()
                && left.encoding_version() == right.encoding_version()
        })
}

fn same_support_block(left: &SupportBlockRef, right: &SupportBlockRef) -> bool {
    left.context_id() == right.context_id()
        && left.constant_keys() == right.constant_keys()
        && left.block_id() == right.block_id()
        && left.role_neutral_bodies() == right.role_neutral_bodies()
        && left.preparation_revision() == right.preparation_revision()
}

// ------------------------------------------------------------
// Source Validation And Assembly
// ------------------------------------------------------------

/// Assemble exact prepared bodies without invoking Vampire.
///
/// Validation, constant collection, rendering, and hashing run as retained
/// context-owned CPU work. The encoding context must therefore remain live
/// until assembly completes.
pub async fn assemble_entailment(
    context: &SolverEncodingContext,
    admission: &SolverAdmission,
    artifacts: &ArtifactStore,
    axiom_bodies: impl Into<Arc<[PreparedBodyRef]>>,
    goal_bodies: impl Into<Arc<[PreparedBodyRef]>>,
    cancellation: &CancellationToken,
) -> Result<Entailment, EncodingError> {
    let axiom_bodies = axiom_bodies.into();
    let goal_bodies = goal_bodies.into();
    let validation_context = context.clone();
    let validation_artifacts = artifacts.clone();
    let validation_axioms = Arc::clone(&axiom_bodies);
    let validation_goals = Arc::clone(&goal_bodies);
    let constants = context
        .run_cpu_job(admission, cancellation, move |job_cancellation| {
            require_not_cancelled(&job_cancellation)?;
            validate_inputs(
                &validation_context,
                &validation_artifacts,
                &validation_axioms,
                &validation_goals,
            )
            .map_err(encoding_cpu_failure)?;
            let constants =
                exact_constant_union(&validation_axioms, &validation_goals, &job_cancellation)?;
            require_not_cancelled(&job_cancellation)?;
            Ok(constants)
        })
        .await
        .map_err(cpu_encoding_error)?;
    let support = context
        .prepare_support_block(
            admission,
            artifacts,
            constants.iter().cloned(),
            cancellation,
        )
        .await?;
    let assembly_context = context.clone();
    let assembly_constants = constants.clone();
    let assembly_support = support.clone();
    let assembly_axioms = Arc::clone(&axiom_bodies);
    let assembly_goals = Arc::clone(&goal_bodies);
    let prepared = context
        .run_cpu_job(admission, cancellation, move |job_cancellation| {
            require_not_cancelled(&job_cancellation)?;
            validate_support(&assembly_context, &assembly_constants, &assembly_support)
                .map_err(encoding_cpu_failure)?;
            require_not_cancelled(&job_cancellation)?;
            let support_text = assembly_support
                .role_neutral_bodies()
                .iter()
                .map(AsRef::as_ref)
                .collect::<Vec<&str>>();
            let axiom_text = assembly_axioms
                .iter()
                .map(PreparedBodyRef::tptp_body)
                .collect::<Vec<_>>();
            let goal_text = assembly_goals
                .iter()
                .map(PreparedBodyRef::tptp_body)
                .collect::<Vec<_>>();
            let query = render_query(
                &support_text,
                &axiom_text,
                &goal_text,
                PremiseRole::Axiom,
                &job_cancellation,
            )?;
            let identity = structural_identity(
                &assembly_context,
                &assembly_constants,
                &assembly_support,
                &assembly_axioms,
                &assembly_goals,
                &job_cancellation,
            )?;
            let query_content_identity = content_identity("whiel-query-v1", query.as_bytes());
            require_not_cancelled(&job_cancellation)?;
            Ok(PreparedQuery {
                identity,
                content_identity: query_content_identity,
                bytes: query.into_bytes().into(),
            })
        })
        .await
        .map_err(cpu_encoding_error)?;

    let publication = artifacts.publish_query(prepared.content_identity, prepared.bytes);
    tokio::pin!(publication);
    let query_artifact = tokio::select! {
        biased;
        _ = cancellation.cancelled() => return Err(EncodingError::Cancelled),
        result = &mut publication => result.map_err(publication_error)?,
    };

    Ok(Entailment {
        inner: Arc::new(EntailmentData {
            identity: prepared.identity,
            context: EntailmentContext::Legacy(context.clone()),
            fixed_ambient_identity: None,
            constants: constants.into(),
            support,
            axiom_bodies,
            goal_bodies,
            query_artifact,
            premise_role: PremiseRole::Axiom,
        }),
    })
}

/// Assemble one complete fixed-ambient package prepared by Lean.
///
/// The structural identity is retained whole. Rust validates ownership and
/// renders the already-prepared TPTP bodies, but does not inspect formulas or
/// relation-name constructors.
#[allow(clippy::too_many_arguments)]
pub(crate) async fn assemble_fixed_ambient_entailment_with_support(
    context: &FixedAmbientEncodingContext,
    admission: &SolverAdmission,
    artifacts: &ArtifactStore,
    worker_entailment_identity: Value,
    axiom_bodies: impl Into<Arc<[PreparedBodyRef]>>,
    goal_bodies: impl Into<Arc<[PreparedBodyRef]>>,
    support: SupportBlockRef,
    cancellation: &CancellationToken,
) -> Result<Entailment, EncodingError> {
    let axiom_bodies = axiom_bodies.into();
    let goal_bodies = goal_bodies.into();
    let validation_context = context.clone();
    let validation_artifacts = artifacts.clone();
    let validation_axioms = Arc::clone(&axiom_bodies);
    let validation_goals = Arc::clone(&goal_bodies);
    let validation_support = support.clone();
    let identity_for_job = worker_entailment_identity.clone();
    let prepared = context
        .run_cpu_job(admission, cancellation, move |job_cancellation| {
            require_not_cancelled(&job_cancellation)?;
            validate_fixed_ambient_inputs(
                &validation_context,
                &validation_artifacts,
                &validation_axioms,
                &validation_goals,
                &validation_support,
            )
            .map_err(encoding_cpu_failure)?;
            let constants =
                exact_constant_union(&validation_axioms, &validation_goals, &job_cancellation)?;
            if validation_support.constant_keys() != constants {
                return Err(encoding_cpu_failure(local_malformed(
                    "fixed-ambient support constants differ from the exact body union",
                )));
            }
            require_not_cancelled(&job_cancellation)?;
            let support_text = validation_support
                .role_neutral_bodies()
                .iter()
                .map(AsRef::as_ref)
                .collect::<Vec<&str>>();
            let axiom_text = validation_axioms
                .iter()
                .map(PreparedBodyRef::tptp_body)
                .collect::<Vec<_>>();
            let goal_text = validation_goals
                .iter()
                .map(PreparedBodyRef::tptp_body)
                .collect::<Vec<_>>();
            let query = render_query(
                &support_text,
                &axiom_text,
                &goal_text,
                PremiseRole::Axiom,
                &job_cancellation,
            )?;
            let identity = fixed_ambient_structural_identity(
                &validation_context,
                &identity_for_job,
                &constants,
                &validation_support,
                &validation_axioms,
                &validation_goals,
                &job_cancellation,
            )?;
            let query_content_identity =
                content_identity("whiel-fixed-ambient-query-v1", query.as_bytes());
            Ok((
                PreparedQuery {
                    identity,
                    content_identity: query_content_identity,
                    bytes: query.into_bytes().into(),
                },
                constants,
            ))
        })
        .await
        .map_err(cpu_encoding_error)?;
    let (prepared, constants) = prepared;
    let publication = artifacts.publish_query(prepared.content_identity, prepared.bytes);
    tokio::pin!(publication);
    let query_artifact = tokio::select! {
        biased;
        _ = cancellation.cancelled() => return Err(EncodingError::Cancelled),
        result = &mut publication => result.map_err(publication_error)?,
    };
    Ok(Entailment {
        inner: Arc::new(EntailmentData {
            identity: prepared.identity,
            context: EntailmentContext::FixedAmbient(context.clone()),
            fixed_ambient_identity: Some(Arc::new(worker_entailment_identity)),
            constants: constants.into(),
            support,
            axiom_bodies,
            goal_bodies,
            query_artifact,
            premise_role: PremiseRole::Axiom,
        }),
    })
}

struct PreparedQuery {
    identity: Arc<str>,
    content_identity: Arc<str>,
    bytes: Arc<[u8]>,
}

fn require_not_cancelled(cancellation: &CancellationToken) -> Result<(), CpuJobError> {
    if cancellation.is_cancelled() {
        Err(CpuJobError::Cancelled)
    } else {
        Ok(())
    }
}

fn encoding_cpu_failure(error: EncodingError) -> CpuJobError {
    match error {
        EncodingError::Cancelled => CpuJobError::Cancelled,
        EncodingError::Failure(report) => CpuJobError::Failure(report),
    }
}

fn cpu_encoding_error(error: CpuJobError) -> EncodingError {
    match error {
        CpuJobError::Cancelled | CpuJobError::Admission(AdmissionError::Cancelled) => {
            EncodingError::Cancelled
        }
        CpuJobError::Failure(report) | CpuJobError::Admission(AdmissionError::Closed(report)) => {
            EncodingError::Failure(report)
        }
        other => shared_failure(format!("entailment CPU preparation failed: {other}")),
    }
}

fn validate_inputs(
    context: &SolverEncodingContext,
    artifacts: &ArtifactStore,
    axiom_bodies: &[PreparedBodyRef],
    goal_bodies: &[PreparedBodyRef],
) -> Result<(), EncodingError> {
    if artifacts.task_identity() != context.task_identity()
        || artifacts.backend_id() != context.artifact_store().backend_id()
    {
        return Err(shared_failure(
            "artifact backend and entailment context identities differ",
        ));
    }
    if goal_bodies.is_empty() {
        return Err(local_malformed(
            "an entailment requires at least one goal body",
        ));
    }
    for body in axiom_bodies.iter().chain(goal_bodies) {
        if body.context_id() != context.context_id()
            || body.source().task_identity() != context.task_identity()
            || body.semantic_version() != context.task_identity().semantic_version()
            || body.encoding_version() != context.task_identity().encoding_version()
        {
            return Err(shared_failure(
                "prepared entailment body belongs to another task, version, or context",
            ));
        }
        if body.body_id().is_empty()
            || body.fol_identity().is_empty()
            || body.tptp_body().is_empty()
            || body.theorem_id().is_empty()
        {
            return Err(local_malformed(
                "prepared entailment body has an empty required identity or serialization",
            ));
        }
    }
    Ok(())
}

fn validate_fixed_ambient_inputs(
    context: &FixedAmbientEncodingContext,
    artifacts: &ArtifactStore,
    axiom_bodies: &[PreparedBodyRef],
    goal_bodies: &[PreparedBodyRef],
    support: &SupportBlockRef,
) -> Result<(), EncodingError> {
    if artifacts.task_identity() != context.task_identity() {
        return Err(shared_failure(
            "artifact backend and fixed-ambient context identities differ",
        ));
    }
    if goal_bodies.len() != 1 {
        return Err(local_malformed(
            "a fixed-ambient entailment requires exactly one conjecture body",
        ));
    }
    for body in axiom_bodies.iter().chain(goal_bodies) {
        if body.context_id() != context.context_id()
            || body.source().task_identity() != context.task_identity()
            || body.semantic_version() != context.task_identity().semantic_version()
            || body.encoding_version() != context.task_identity().encoding_version()
        {
            return Err(shared_failure(
                "fixed-ambient prepared body belongs to another task, version, or context",
            ));
        }
        if body.body_id().is_empty()
            || body.fol_identity().is_empty()
            || body.tptp_body().is_empty()
            || body.theorem_id().is_empty()
        {
            return Err(local_malformed(
                "fixed-ambient prepared body has an empty required identity or serialization",
            ));
        }
    }
    if support.context_id() != context.context_id()
        || support.role_neutral_bodies().is_empty()
        || support
            .role_neutral_bodies()
            .iter()
            .any(|body| body.is_empty())
    {
        return Err(local_malformed(
            "fixed-ambient support belongs to another context or is incomplete",
        ));
    }
    Ok(())
}

fn exact_constant_union(
    axiom_bodies: &[PreparedBodyRef],
    goal_bodies: &[PreparedBodyRef],
    cancellation: &CancellationToken,
) -> Result<Vec<ConstantKey>, CpuJobError> {
    let mut constants = BTreeSet::new();
    for body in axiom_bodies.iter().chain(goal_bodies) {
        require_not_cancelled(cancellation)?;
        constants.extend(body.constants().iter().cloned());
    }
    Ok(constants.into_iter().collect())
}

fn validate_support(
    context: &SolverEncodingContext,
    constants: &[ConstantKey],
    support: &SupportBlockRef,
) -> Result<(), EncodingError> {
    if support.context_id() != context.context_id() || support.constant_keys() != constants {
        return Err(shared_failure(
            "support cache returned another context or constant union",
        ));
    }
    if support.role_neutral_bodies().is_empty()
        || support
            .role_neutral_bodies()
            .iter()
            .any(|body| body.is_empty())
    {
        return Err(local_malformed(
            "support block has an empty required serialization",
        ));
    }
    Ok(())
}

// ------------------------------------------------------------
// Stable Identity And TPTP Rendering
// ------------------------------------------------------------

fn structural_identity(
    context: &SolverEncodingContext,
    constants: &[ConstantKey],
    support: &SupportBlockRef,
    axiom_bodies: &[PreparedBodyRef],
    goal_bodies: &[PreparedBodyRef],
    cancellation: &CancellationToken,
) -> Result<Arc<str>, CpuJobError> {
    let task = context.task_identity();
    let mut identity = StructuralIdentity::new();
    identity.field("whiel-entailment-v1");
    identity.field(context.context_id());
    identity.field(task.canonical_id());
    identity.field(task.module());
    identity.field(task.namespace());
    identity.field(task.source_digest().as_str());
    identity.field(&task.semantic_version().to_string());
    identity.field(&task.encoding_version().to_string());
    identity.list(constants.iter().map(ConstantKey::as_str));
    identity.field(support.block_id());
    identity.list(support.role_neutral_bodies().iter().map(AsRef::as_ref));
    identity.body_list(axiom_bodies, cancellation)?;
    identity.body_list(goal_bodies, cancellation)?;
    Ok(Arc::from(identity.finish("whiel-entailment-v1")))
}

fn fixed_ambient_structural_identity(
    context: &FixedAmbientEncodingContext,
    worker_entailment_identity: &Value,
    constants: &[ConstantKey],
    support: &SupportBlockRef,
    axiom_bodies: &[PreparedBodyRef],
    goal_bodies: &[PreparedBodyRef],
    cancellation: &CancellationToken,
) -> Result<Arc<str>, CpuJobError> {
    let task = context.task_identity();
    let mut identity = StructuralIdentity::new();
    identity.field("whiel-fixed-ambient-entailment-v1");
    identity.field(context.context_id());
    identity.field(task.canonical_id());
    identity.field(task.module());
    identity.field(task.namespace());
    identity.field(task.source_digest().as_str());
    identity.field(&task.semantic_version().to_string());
    identity.field(&task.encoding_version().to_string());
    identity.field(&canonical_value_sha256(worker_entailment_identity));
    identity.list(constants.iter().map(ConstantKey::as_str));
    identity.field(support.block_id());
    identity.list(support.role_neutral_bodies().iter().map(AsRef::as_ref));
    identity.body_list(axiom_bodies, cancellation)?;
    identity.body_list(goal_bodies, cancellation)?;
    Ok(Arc::from(
        identity.finish("whiel-fixed-ambient-entailment-v1"),
    ))
}

// Read-only exact constructor inputs; no query, artifact-store or solver authority.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct ReplayEntailmentStructure {
    pub allocation: crate::encoding::ReplayFixedAmbientAllocation,
    pub context_id: String,
    pub canonical_id: String,
    pub module: String,
    pub namespace: String,
    pub source_digest: String,
    pub semantic_version: u64,
    pub encoding_version: u64,
    pub worker_entailment_digest: String,
    pub constants: Vec<String>,
    pub support_block_id: String,
    pub support_bodies: Vec<String>,
    pub axiom_bodies: Vec<ReplayPreparedBodyStructure>,
    pub goal_bodies: Vec<ReplayPreparedBodyStructure>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct ReplayPreparedBodyStructure {
    pub source: ReplayPreparedBodySource,
    pub source_id: String,
    pub body_id: String,
    pub fol_identity: String,
    pub theorem_id: String,
    pub semantic_version: u64,
    pub encoding_version: u64,
    pub constants: Vec<String>,
    pub tptp_body: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum ReplayPreparedBodySource {
    Assert,
    QuantifierFree,
}

impl ReplayPreparedBodyStructure {
    fn capture(body: &PreparedBodyRef) -> Self {
        Self {
            source: match body.source() {
                SolverBodySource::Assert(_) => ReplayPreparedBodySource::Assert,
                SolverBodySource::QuantifierFree(_) => ReplayPreparedBodySource::QuantifierFree,
            },
            source_id: body.source().source_id().to_owned(),
            body_id: body.body_id().to_owned(),
            fol_identity: body.fol_identity().to_owned(),
            theorem_id: body.theorem_id().to_owned(),
            semantic_version: body.semantic_version(),
            encoding_version: body.encoding_version(),
            constants: body
                .constants()
                .iter()
                .map(|key| key.as_str().to_owned())
                .collect(),
            tptp_body: body.tptp_body().to_owned(),
        }
    }
}

impl ReplayEntailmentStructure {
    pub(crate) fn verify_allocation(&self) -> bool {
        self.allocation.verify()
            && self.context_id == self.allocation.context_id
            && self.canonical_id == self.allocation.canonical_id
            && self.support_block_id
                == self
                    .allocation
                    .support_id(self.constants.iter().map(String::as_str))
            && self
                .axiom_bodies
                .iter()
                .chain(&self.goal_bodies)
                .all(|body| {
                    body.source == ReplayPreparedBodySource::QuantifierFree
                        && body.body_id == self.allocation.body_id(&body.source_id)
                })
    }
    pub(crate) fn derive_identity(&self) -> String {
        let mut identity = StructuralIdentity::new();
        identity.field("whiel-fixed-ambient-entailment-v1");
        identity.field(&self.context_id);
        identity.field(&self.canonical_id);
        identity.field(&self.module);
        identity.field(&self.namespace);
        identity.field(&self.source_digest);
        identity.field(&self.semantic_version.to_string());
        identity.field(&self.encoding_version.to_string());
        identity.field(&self.worker_entailment_digest);
        identity.list(self.constants.iter().map(String::as_str));
        identity.field(&self.support_block_id);
        identity.list(self.support_bodies.iter().map(String::as_str));
        for bodies in [&self.axiom_bodies, &self.goal_bodies] {
            identity.field(&bodies.len().to_string());
            for body in bodies {
                identity.field(match body.source {
                    ReplayPreparedBodySource::Assert => "assert",
                    ReplayPreparedBodySource::QuantifierFree => "quantifier-free",
                });
                identity.field(&body.source_id);
                identity.field(&body.body_id);
                identity.field(&body.fol_identity);
                identity.field(&body.theorem_id);
                identity.field(&body.semantic_version.to_string());
                identity.field(&body.encoding_version.to_string());
                identity.list(body.constants.iter().map(String::as_str));
                identity.field(&body.tptp_body);
            }
        }
        identity.finish("whiel-fixed-ambient-entailment-v1")
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ReplayEntailmentProjectionError {
    Unsupported,
    SemanticRedaction,
    IdentityMismatch,
}

impl Entailment {
    pub(crate) fn replay_structure(
        &self,
    ) -> Result<ReplayEntailmentStructure, ReplayEntailmentProjectionError> {
        let EntailmentContext::FixedAmbient(context) = &self.inner.context else {
            return Err(ReplayEntailmentProjectionError::Unsupported);
        };
        let worker = self
            .inner
            .fixed_ambient_identity
            .as_deref()
            .ok_or(ReplayEntailmentProjectionError::Unsupported)?;
        let task = context.task_identity();
        let projection = ReplayEntailmentStructure {
            allocation: context.replay_allocation(),
            context_id: context.context_id().to_owned(),
            canonical_id: task.canonical_id().to_owned(),
            module: task.module().to_owned(),
            namespace: task.namespace().to_owned(),
            source_digest: task.source_digest().as_str().to_owned(),
            semantic_version: task.semantic_version(),
            encoding_version: task.encoding_version(),
            worker_entailment_digest: canonical_value_sha256(worker),
            constants: self
                .inner
                .constants
                .iter()
                .map(|key| key.as_str().to_owned())
                .collect(),
            support_block_id: self.inner.support.block_id().to_owned(),
            support_bodies: self
                .inner
                .support
                .role_neutral_bodies()
                .iter()
                .map(|body| body.to_string())
                .collect(),
            axiom_bodies: self
                .inner
                .axiom_bodies
                .iter()
                .map(ReplayPreparedBodyStructure::capture)
                .collect(),
            goal_bodies: self
                .inner
                .goal_bodies
                .iter()
                .map(ReplayPreparedBodyStructure::capture)
                .collect(),
        };
        // Production's full worker schema must independently derive and check
        // worker_entailment_digest; this scalar is this constructor's exact input.
        let bytes = serde_json::to_vec(&projection)
            .map_err(|_| ReplayEntailmentProjectionError::Unsupported)?;
        if crate::framework2::Redaction::changes(&bytes) {
            return Err(ReplayEntailmentProjectionError::SemanticRedaction);
        }
        if !projection.verify_allocation() || projection.derive_identity() != self.identity() {
            return Err(ReplayEntailmentProjectionError::IdentityMismatch);
        }
        Ok(projection)
    }
}

fn content_identity(domain: &str, payload: &[u8]) -> Arc<str> {
    let mut digest = Sha256::new();
    digest.update(payload);
    Arc::from(format!("{domain}:sha256:{}", digest.finalize_hex()))
}

struct StructuralIdentity {
    digest: Sha256,
}

impl StructuralIdentity {
    fn new() -> Self {
        Self {
            digest: Sha256::new(),
        }
    }

    fn field(&mut self, value: &str) {
        // Hash the same length-prefixed byte stream that formerly served as
        // the public identity. The framing keeps every structural field and
        // list boundary exact; SHA-256 keeps the cache key compact.
        self.digest.update(value.len().to_string().as_bytes());
        self.digest.update(b":");
        self.digest.update(value.as_bytes());
    }

    fn list<'a, I>(&mut self, values: I)
    where
        I: IntoIterator<Item = &'a str>,
        I::IntoIter: ExactSizeIterator,
    {
        let values = values.into_iter();
        self.field(&values.len().to_string());
        for value in values {
            self.field(value);
        }
    }

    fn body_list(
        &mut self,
        bodies: &[PreparedBodyRef],
        cancellation: &CancellationToken,
    ) -> Result<(), CpuJobError> {
        self.field(&bodies.len().to_string());
        for body in bodies {
            require_not_cancelled(cancellation)?;
            self.field(match body.source() {
                SolverBodySource::Assert(_) => "assert",
                SolverBodySource::QuantifierFree(_) => "quantifier-free",
            });
            self.field(body.source().source_id());
            self.field(body.body_id());
            self.field(body.fol_identity());
            self.field(body.theorem_id());
            self.field(&body.semantic_version().to_string());
            self.field(&body.encoding_version().to_string());
            self.list(body.constants().iter().map(ConstantKey::as_str));
            // The exact immutable body closes the current PreparedBodyRef
            // identity gap: body_id alone omits relation metadata.
            self.field(body.tptp_body());
        }
        Ok(())
    }

    fn finish(self, domain: &str) -> String {
        format!("{domain}:sha256:{}", self.digest.finalize_hex())
    }
}

/*
  Dependency-free SHA-256 for compact structural cache identities.

  This implementation is deliberately local. It hashes only in-memory
  identity framing and does not replace a cryptographic library elsewhere.
*/

pub(crate) struct Sha256 {
    state: [u32; 8],
    buffer: [u8; 64],
    buffer_len: usize,
    total_len: u64,
}

impl Sha256 {
    const INITIAL_STATE: [u32; 8] = [
        0x6a09_e667,
        0xbb67_ae85,
        0x3c6e_f372,
        0xa54f_f53a,
        0x510e_527f,
        0x9b05_688c,
        0x1f83_d9ab,
        0x5be0_cd19,
    ];

    const ROUND_CONSTANTS: [u32; 64] = [
        0x428a_2f98,
        0x7137_4491,
        0xb5c0_fbcf,
        0xe9b5_dba5,
        0x3956_c25b,
        0x59f1_11f1,
        0x923f_82a4,
        0xab1c_5ed5,
        0xd807_aa98,
        0x1283_5b01,
        0x2431_85be,
        0x550c_7dc3,
        0x72be_5d74,
        0x80de_b1fe,
        0x9bdc_06a7,
        0xc19b_f174,
        0xe49b_69c1,
        0xefbe_4786,
        0x0fc1_9dc6,
        0x240c_a1cc,
        0x2de9_2c6f,
        0x4a74_84aa,
        0x5cb0_a9dc,
        0x76f9_88da,
        0x983e_5152,
        0xa831_c66d,
        0xb003_27c8,
        0xbf59_7fc7,
        0xc6e0_0bf3,
        0xd5a7_9147,
        0x06ca_6351,
        0x1429_2967,
        0x27b7_0a85,
        0x2e1b_2138,
        0x4d2c_6dfc,
        0x5338_0d13,
        0x650a_7354,
        0x766a_0abb,
        0x81c2_c92e,
        0x9272_2c85,
        0xa2bf_e8a1,
        0xa81a_664b,
        0xc24b_8b70,
        0xc76c_51a3,
        0xd192_e819,
        0xd699_0624,
        0xf40e_3585,
        0x106a_a070,
        0x19a4_c116,
        0x1e37_6c08,
        0x2748_774c,
        0x34b0_bcb5,
        0x391c_0cb3,
        0x4ed8_aa4a,
        0x5b9c_ca4f,
        0x682e_6ff3,
        0x748f_82ee,
        0x78a5_636f,
        0x84c8_7814,
        0x8cc7_0208,
        0x90be_fffa,
        0xa450_6ceb,
        0xbef9_a3f7,
        0xc671_78f2,
    ];

    pub(crate) fn new() -> Self {
        Self {
            state: Self::INITIAL_STATE,
            buffer: [0; 64],
            buffer_len: 0,
            total_len: 0,
        }
    }

    pub(crate) fn update(&mut self, mut input: &[u8]) {
        self.total_len = self
            .total_len
            .checked_add(input.len() as u64)
            .expect("structural identity exceeds SHA-256's length domain");

        if self.buffer_len != 0 {
            let copied = (64 - self.buffer_len).min(input.len());
            self.buffer[self.buffer_len..self.buffer_len + copied]
                .copy_from_slice(&input[..copied]);
            self.buffer_len += copied;
            input = &input[copied..];
            if self.buffer_len < 64 {
                return;
            }
            let block = self.buffer;
            self.compress(&block);
            self.buffer_len = 0;
        }

        while input.len() >= 64 {
            let block: &[u8; 64] = input[..64]
                .try_into()
                .expect("the SHA-256 block has exact length");
            self.compress(block);
            input = &input[64..];
        }

        self.buffer[..input.len()].copy_from_slice(input);
        self.buffer_len = input.len();
    }

    pub(crate) fn finalize_hex(mut self) -> String {
        let bit_len = self
            .total_len
            .checked_mul(8)
            .expect("structural identity exceeds SHA-256's bit-length domain");
        self.buffer[self.buffer_len] = 0x80;
        self.buffer_len += 1;

        if self.buffer_len > 56 {
            self.buffer[self.buffer_len..].fill(0);
            let block = self.buffer;
            self.compress(&block);
            self.buffer = [0; 64];
        } else {
            self.buffer[self.buffer_len..56].fill(0);
        }
        self.buffer[56..].copy_from_slice(&bit_len.to_be_bytes());
        let block = self.buffer;
        self.compress(&block);

        let mut result = String::with_capacity(64);
        for word in self.state {
            write!(result, "{word:08x}").expect("writing to a String cannot fail");
        }
        result
    }

    fn compress(&mut self, block: &[u8; 64]) {
        let mut schedule = [0_u32; 64];
        for (word, bytes) in schedule[..16].iter_mut().zip(block.chunks_exact(4)) {
            *word = u32::from_be_bytes(
                bytes
                    .try_into()
                    .expect("a SHA-256 input word has exact length"),
            );
        }
        for index in 16..64 {
            let s0 = schedule[index - 15].rotate_right(7)
                ^ schedule[index - 15].rotate_right(18)
                ^ (schedule[index - 15] >> 3);
            let s1 = schedule[index - 2].rotate_right(17)
                ^ schedule[index - 2].rotate_right(19)
                ^ (schedule[index - 2] >> 10);
            schedule[index] = schedule[index - 16]
                .wrapping_add(s0)
                .wrapping_add(schedule[index - 7])
                .wrapping_add(s1);
        }

        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = self.state;
        for (round, constant) in schedule.iter().zip(Self::ROUND_CONSTANTS) {
            let upper_sigma = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let choice = (e & f) ^ ((!e) & g);
            let temporary1 = h
                .wrapping_add(upper_sigma)
                .wrapping_add(choice)
                .wrapping_add(constant)
                .wrapping_add(*round);
            let lower_sigma = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let majority = (a & b) ^ (a & c) ^ (b & c);
            let temporary2 = lower_sigma.wrapping_add(majority);

            h = g;
            g = f;
            f = e;
            e = d.wrapping_add(temporary1);
            d = c;
            c = b;
            b = a;
            a = temporary1.wrapping_add(temporary2);
        }

        for (state, value) in self.state.iter_mut().zip([a, b, c, d, e, f, g, h]) {
            *state = state.wrapping_add(value);
        }
    }
}

/// Stream one file's bytes through [`Sha256`] and return its lowercase hex
/// digest, without loading the whole file into memory.
///
/// Shared by every crate-internal caller that hashes a file on disk
/// (toolchain-lock pinning, campaign identity recording, and the
/// certification bridge's published-artifact digest); each maps this
/// [`std::io::Error`] into its own error type.
pub(crate) fn hash_file_sha256(path: &Path) -> std::io::Result<String> {
    let mut file = std::fs::File::open(path)?;
    let mut hasher = Sha256::new();
    let mut buffer = [0_u8; 64 * 1024];
    loop {
        let read = file.read(&mut buffer)?;
        if read == 0 {
            break;
        }
        hasher.update(&buffer[..read]);
    }
    Ok(hasher.finalize_hex())
}

/// Render one fixed-ambient problem exactly as
/// [`assemble_fixed_ambient_entailment_with_support`] does, without
/// publishing an artifact.
///
/// Pass 7.5d's differential safety net renders the controller's spliced
/// bodies and the worker's own `prepare_exact_obligation` bodies through
/// this one function and compares the two strings, so "the assembled bytes
/// equal Lean's" is checked on the literal problem text.
pub(crate) fn render_fixed_ambient_query(
    support: &[&str],
    axioms: &[&str],
    goals: &[&str],
) -> Result<String, CpuJobError> {
    // The differential compares a splice against the worker's own
    // rendering, which always writes premises as axioms; the premise role
    // is a search hint applied afterwards and is not what this checks.
    render_query(
        support,
        axioms,
        goals,
        PremiseRole::Axiom,
        &CancellationToken::new(),
    )
}

fn render_query(
    support: &[&str],
    axioms: &[&str],
    goals: &[&str],
    premise_role: PremiseRole,
    cancellation: &CancellationToken,
) -> Result<String, CpuJobError> {
    debug_assert!(!goals.is_empty());
    let estimated_body_bytes = support
        .iter()
        .chain(axioms)
        .chain(goals)
        .map(|body| body.len())
        .sum::<usize>();
    let mut query = String::with_capacity(estimated_body_bytes + 128);

    for (index, body) in support.iter().enumerate() {
        require_not_cancelled(cancellation)?;
        let name = if index == 0 {
            "support_adom".to_string()
        } else {
            format!("support_distinct_{}", index - 1)
        };
        write_declaration(&mut query, &name, "axiom", body);
    }
    // The support block states the active domain and the distinctness of
    // the constants; it is background theory in every launch and keeps its
    // role. Only the premises of this implication follow `premise_role`.
    for (index, body) in axioms.iter().enumerate() {
        require_not_cancelled(cancellation)?;
        write_declaration(
            &mut query,
            &format!("axiom_{index}"),
            premise_role.name(),
            body,
        );
    }

    require_not_cancelled(cancellation)?;
    query.push_str("fof(goal, conjecture, (");
    for (index, body) in goals.iter().enumerate() {
        require_not_cancelled(cancellation)?;
        if index != 0 {
            query.push_str(" & ");
        }
        write!(query, "({body})").expect("writing to a String cannot fail");
    }
    query.push_str(")).\n");
    Ok(query)
}

fn write_declaration(query: &mut String, name: &str, role: &str, body: &str) {
    writeln!(query, "fof({name}, {role}, ({body})).").expect("writing to a String cannot fail");
}

// ------------------------------------------------------------
// Typed Failures
// ------------------------------------------------------------

fn local_malformed(detail: impl Into<String>) -> EncodingError {
    EncodingError::Failure(FailureReport::encoding_preparation(
        FailureKind::MalformedResult,
        FailureScope::LaneLocal,
        detail,
    ))
}

fn shared_failure(detail: impl Into<String>) -> EncodingError {
    EncodingError::Failure(FailureReport::encoding_preparation(
        FailureKind::InfrastructureFailure,
        FailureScope::RunGlobal,
        detail,
    ))
}

fn publication_error(report: FailureReport) -> EncodingError {
    let kind = match report.kind() {
        FailureKind::PublicationFailure => FailureKind::PublicationFailure,
        _ => FailureKind::InfrastructureFailure,
    };
    let detail = format!(
        "publish assembled entailment query: {}",
        report.detail().unwrap_or("artifact backend failure")
    );
    EncodingError::Failure(FailureReport::encoding_preparation(
        kind,
        report.scope(),
        detail,
    ))
}

// ------------------------------------------------------------
// Rendering Tests
// ------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::{PremiseRole, Sha256, StructuralIdentity, render_query};
    use crate::runtime::{CancellationToken, CpuJobError};

    #[test]
    fn rendering_uses_unique_roles_and_one_ordered_goal() {
        let query = render_query(
            &["adom", "c0 != c1"],
            &["p(c0)", "q(c1)"],
            &["first", "second", "third"],
            PremiseRole::Axiom,
            &CancellationToken::new(),
        )
        .unwrap();
        assert_eq!(
            query,
            concat!(
                "fof(support_adom, axiom, (adom)).\n",
                "fof(support_distinct_0, axiom, (c0 != c1)).\n",
                "fof(axiom_0, axiom, (p(c0))).\n",
                "fof(axiom_1, axiom, (q(c1))).\n",
                "fof(goal, conjecture, ((first) & (second) & (third))).\n",
            )
        );
    }

    /// The re-tagged rendering a retry launch runs on. Only the role word
    /// of the premises changes: the support block stays background theory,
    /// the conjecture stays the conjecture, and every name, body and
    /// position is the one the first launch wrote.
    #[test]
    fn a_retry_role_moves_only_the_premises() {
        let render = |role| {
            render_query(
                &["adom", "c0 != c1"],
                &["p(c0)", "q(c1)"],
                &["first", "second"],
                role,
                &CancellationToken::new(),
            )
            .unwrap()
        };
        assert_eq!(
            render(PremiseRole::NegatedConjecture),
            concat!(
                "fof(support_adom, axiom, (adom)).\n",
                "fof(support_distinct_0, axiom, (c0 != c1)).\n",
                "fof(axiom_0, negated_conjecture, (p(c0))).\n",
                "fof(axiom_1, negated_conjecture, (q(c1))).\n",
                "fof(goal, conjecture, ((first) & (second))).\n",
            )
        );
        assert_eq!(
            render(PremiseRole::Axiom)
                .replace(", axiom, (p(c0))", ", negated_conjecture, (p(c0))")
                .replace(", axiom, (q(c1))", ", negated_conjecture, (q(c1))"),
            render(PremiseRole::NegatedConjecture),
            "the two renderings differ in the premise role word and nothing else"
        );
    }

    #[test]
    fn a_premise_role_round_trips_through_its_recorded_name() {
        for role in [PremiseRole::Axiom, PremiseRole::NegatedConjecture] {
            assert_eq!(PremiseRole::from_name(role.name()), Some(role));
        }
        assert_eq!(PremiseRole::default(), PremiseRole::Axiom);
        assert!(PremiseRole::from_name("conjecture").is_none());
    }

    #[test]
    fn rendering_observes_preexisting_cancellation() {
        let cancellation = CancellationToken::new();
        cancellation.cancel();
        assert!(matches!(
            render_query(
                &["adom"],
                &["p(c0)"],
                &["goal"],
                PremiseRole::Axiom,
                &cancellation
            ),
            Err(CpuJobError::Cancelled)
        ));
    }

    #[test]
    fn structural_fields_are_unambiguous_and_stable() {
        let mut first = StructuralIdentity::new();
        first.list(["ab", "c"]);
        let first_again = first.finish("test");

        let mut second = StructuralIdentity::new();
        second.list(["a", "bc"]);
        let second = second.finish("test");

        let mut repeated = StructuralIdentity::new();
        repeated.list(["ab", "c"]);
        assert_ne!(first_again, second);
        assert_eq!(first_again, repeated.finish("test"));
        assert_eq!(first_again.len(), "test:sha256:".len() + 64);
    }

    #[test]
    fn sha256_matches_standard_incremental_vectors() {
        let mut empty = Sha256::new();
        empty.update(b"");
        assert_eq!(
            empty.finalize_hex(),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );

        let mut incremental = Sha256::new();
        incremental.update(b"a");
        incremental.update(b"b");
        incremental.update(b"c");
        assert_eq!(
            incremental.finalize_hex(),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );

        let mut two_blocks = Sha256::new();
        two_blocks.update(b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq");
        assert_eq!(
            two_blocks.finalize_hex(),
            "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
        );
    }
}
