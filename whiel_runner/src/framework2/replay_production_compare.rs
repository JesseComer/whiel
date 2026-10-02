//! Production correspondence after independent native-owner verification.
//!
//! The caller owns a provisional mapping transaction and commits it only after
//! the complete state, feedback, and wire comparison succeeds. These visitors
//! never confer receipt, artifact, or certificate authority on a projection.

use serde::{Deserialize, Serialize};

use crate::entailment::assembly::ReplayEntailmentStructure;
use crate::entailment::{ReplaySpecializedTerminalDetail, ReplaySpecializedTerminalProjection};

use super::production::*;
use super::replay_identity::{PhysicalAttemptId, ReplayDivergence};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(super) enum ReplayProductionIdentity {
    Catalog,
    Partition,
    CheckRequest,
    Backend,
    ArtifactBackendDigest,
    ContextAllocation,
    PreparedBody,
    SupportBlock,
    Entailment,
    Preparation,
    Job,
    Terminal,
    ProductionReceipt,
    SemanticReuse,
    EvidenceIdentity,
    RouteDisplay,
}

pub(super) trait ReplayProductionBindings {
    fn bind_identity(
        &mut self,
        kind: ReplayProductionIdentity,
        old: &str,
        live: &str,
        path: &str,
    ) -> Result<(), ReplayDivergence>;
    fn require_identity(
        &self,
        kind: ReplayProductionIdentity,
        old: &str,
        live: &str,
        path: &str,
    ) -> Result<(), ReplayDivergence>;
    fn bind_artifact(
        &mut self,
        old: &ReplayArtifactIdentity,
        live: &ReplayArtifactIdentity,
        path: &str,
    ) -> Result<(), ReplayDivergence>;
    fn bind_attempt(
        &mut self,
        old: PhysicalAttemptId,
        live: PhysicalAttemptId,
        path: &str,
    ) -> Result<(), ReplayDivergence>;
}
fn divergent(path: &str, reason: &str) -> ReplayDivergence {
    ReplayDivergence {
        path: path.into(),
        reason: reason.into(),
    }
}
fn exact<T: PartialEq>(old: &T, live: &T, path: &str) -> Result<(), ReplayDivergence> {
    if old == live {
        Ok(())
    } else {
        Err(divergent(
            path,
            "production semantic or structural field differs",
        ))
    }
}
fn child(path: &str, field: &str) -> String {
    format!("{path}/{field}")
}
fn owner_verified(
    result: Result<(), ReplayProductionError>,
    path: &str,
) -> Result<(), ReplayDivergence> {
    result.map_err(|_| divergent(path, "production owner constructor verification failed"))
}

struct Compare<'a, B: ReplayProductionBindings + ?Sized> {
    bindings: &'a mut B,
}
impl<B: ReplayProductionBindings + ?Sized> Compare<'_, B> {
    fn require(
        &self,
        kind: ReplayProductionIdentity,
        old: &str,
        live: &str,
        path: &str,
    ) -> Result<(), ReplayDivergence> {
        self.bindings.require_identity(kind, old, live, path)
    }
    fn bind(
        &mut self,
        kind: ReplayProductionIdentity,
        old: &str,
        live: &str,
        path: &str,
    ) -> Result<(), ReplayDivergence> {
        self.bindings.bind_identity(kind, old, live, path)
    }
    fn artifact(
        &mut self,
        old: &ReplayArtifactIdentity,
        live: &ReplayArtifactIdentity,
        path: &str,
    ) -> Result<ReplayArtifactIdentity, ReplayDivergence> {
        exact(&old.kind, &live.kind, &child(path, "kind"))?;
        self.require(
            ReplayProductionIdentity::Backend,
            old.backend.as_str(),
            live.backend.as_str(),
            &child(path, "backend"),
        )?;
        self.bindings.bind_artifact(old, live, path)?;
        // The closed artifact DTO consists solely of checked backend/local id
        // and exact kind. No artifact contents or old capability are returned.
        Ok(live.clone())
    }
    fn artifacts(
        &mut self,
        old: &[ReplayArtifactIdentity],
        live: &[ReplayArtifactIdentity],
        path: &str,
    ) -> Result<Vec<ReplayArtifactIdentity>, ReplayDivergence> {
        exact(&old.len(), &live.len(), path)?;
        old.iter()
            .zip(live)
            .enumerate()
            .map(|(i, (old, live))| self.artifact(old, live, &format!("{path}/{i}")))
            .collect()
    }
    fn structure(
        &mut self,
        old: &ReplayEntailmentStructure,
        live: &ReplayEntailmentStructure,
        path: &str,
    ) -> Result<(), ReplayDivergence> {
        if !old.verify_allocation() || !live.verify_allocation() {
            return Err(divergent(
                path,
                "allocation constructor verification failed",
            ));
        }
        let mut mapped = old.clone();
        exact(
            &old.allocation.canonical_id,
            &live.allocation.canonical_id,
            &child(path, "allocation/canonical_id"),
        )?;
        self.bind(
            ReplayProductionIdentity::ContextAllocation,
            &old.context_id,
            &live.context_id,
            &child(path, "context_id"),
        )?;
        mapped.allocation.allocation_sequence = live.allocation.allocation_sequence;
        mapped
            .allocation
            .context_id
            .clone_from(&live.allocation.context_id);
        mapped.context_id.clone_from(&live.context_id);
        // Bodies pair by exact axiom/goal position and source semantics, never
        // by a generated name or completion order.
        for (old_bodies, live_bodies, label) in [
            (&mut mapped.axiom_bodies, &live.axiom_bodies, "axiom_bodies"),
            (&mut mapped.goal_bodies, &live.goal_bodies, "goal_bodies"),
        ] {
            exact(&old_bodies.len(), &live_bodies.len(), &child(path, label))?;
            for (i, (old_body, live_body)) in old_bodies.iter_mut().zip(live_bodies).enumerate() {
                let body_path = format!("{path}/{label}/{i}");
                let original_id = old_body.body_id.clone();
                old_body.body_id.clone_from(&live_body.body_id);
                exact(old_body, live_body, &body_path)?;
                self.bind(
                    ReplayProductionIdentity::PreparedBody,
                    &original_id,
                    &live_body.body_id,
                    &child(&body_path, "body_id"),
                )?;
            }
        }
        exact(&old.constants, &live.constants, &child(path, "constants"))?;
        exact(
            &old.support_bodies,
            &live.support_bodies,
            &child(path, "support_bodies"),
        )?;
        self.bind(
            ReplayProductionIdentity::SupportBlock,
            &old.support_block_id,
            &live.support_block_id,
            &child(path, "support_block_id"),
        )?;
        mapped.support_block_id.clone_from(&live.support_block_id);
        exact(&mapped, live, path)
    }
    fn fixed(
        &mut self,
        old: &ReplayFixedAmbientJobFields,
        live: &ReplayFixedAmbientJobFields,
        bind_preparation: bool,
        path: &str,
    ) -> Result<ReplayFixedAmbientJobFields, ReplayDivergence> {
        owner_verified(old.verify_bindings(), path)?;
        owner_verified(live.verify_bindings(), path)?;
        self.require(
            ReplayProductionIdentity::Entailment,
            &old.entailment_identity.0,
            &live.entailment_identity.0,
            &child(path, "entailment_identity"),
        )?;
        // Job/obligation/worker/empty-request inputs do not contain an allocation
        // identity. Their complete values, including lists and hashes, are exact.
        exact(&old.job_id, &live.job_id, &child(path, "job_id"))?;
        exact(
            &old.obligation_identity,
            &live.obligation_identity,
            &child(path, "obligation_identity"),
        )?;
        exact(
            &old.worker_entailment_identity,
            &live.worker_entailment_identity,
            &child(path, "worker_entailment_identity"),
        )?;
        exact(
            &old.empty_request_identity,
            &live.empty_request_identity,
            &child(path, "empty_request_identity"),
        )?;
        let mut mapped = old.clone();
        mapped.entailment_identity = live.entailment_identity.clone();
        mapped.preparation_identity.entailment_identity =
            live.preparation_identity.entailment_identity.clone();
        mapped.preparation_digest = live.preparation_digest.clone();
        mapped.query_artifact = self.artifact(
            &old.query_artifact,
            &live.query_artifact,
            &child(path, "query_artifact"),
        )?;
        exact(&mapped, live, path)?;
        if bind_preparation {
            self.bind(
                ReplayProductionIdentity::Job,
                old.job_id.as_str(),
                live.job_id.as_str(),
                &child(path, "job_id"),
            )?;
            self.bind(
                ReplayProductionIdentity::Preparation,
                old.preparation_digest.as_str(),
                live.preparation_digest.as_str(),
                &child(path, "preparation_digest"),
            )?;
        } else {
            self.require(
                ReplayProductionIdentity::Job,
                old.job_id.as_str(),
                live.job_id.as_str(),
                &child(path, "job_id"),
            )?;
            self.require(
                ReplayProductionIdentity::Preparation,
                old.preparation_digest.as_str(),
                live.preparation_digest.as_str(),
                &child(path, "preparation_digest"),
            )?;
        }
        Ok(mapped)
    }
    fn preparation(
        &mut self,
        old: &ReplayPreparedProjection,
        live: &ReplayPreparedProjection,
    ) -> Result<(), ReplayDivergence> {
        owner_verified(old.verify(), "/preparation/old")?;
        owner_verified(live.verify(), "/preparation/live")?;
        self.require(
            ReplayProductionIdentity::Catalog,
            old.catalog_digest.as_str(),
            live.catalog_digest.as_str(),
            "/preparation/catalog_digest",
        )?;
        self.require(
            ReplayProductionIdentity::Partition,
            old.partition_digest.as_str(),
            live.partition_digest.as_str(),
            "/preparation/partition_digest",
        )?;
        self.require(
            ReplayProductionIdentity::CheckRequest,
            old.control_request_digest.as_str(),
            live.control_request_digest.as_str(),
            "/preparation/control_request_digest",
        )?;
        self.structure(
            &old.entailment_structure,
            &live.entailment_structure,
            "/preparation/entailment_structure",
        )?;
        self.bind(
            ReplayProductionIdentity::Entailment,
            &old.fixed_ambient_job.entailment_identity.0,
            &live.fixed_ambient_job.entailment_identity.0,
            "/preparation/fixed_ambient_job/entailment_identity",
        )?;
        let mut mapped = old.clone();
        mapped.entailment_structure = live.entailment_structure.clone();
        mapped.fixed_ambient_job = self.fixed(
            &old.fixed_ambient_job,
            &live.fixed_ambient_job,
            true,
            "/preparation/fixed_ambient_job",
        )?;
        mapped.catalog_digest = live.catalog_digest.clone();
        mapped.partition_digest = live.partition_digest.clone();
        mapped.control_request_digest = live.control_request_digest.clone();
        match (&mut mapped.control_subject, &live.control_subject) {
            (
                ReplayControlSubject::Clause { request_digest, .. },
                ReplayControlSubject::Clause {
                    request_digest: live_digest,
                    ..
                },
            )
            | (
                ReplayControlSubject::Termination { request_digest, .. },
                ReplayControlSubject::Termination {
                    request_digest: live_digest,
                    ..
                },
            ) => *request_digest = live_digest.clone(),
            _ => {
                return Err(divergent(
                    "/preparation/control_subject",
                    "control subject variant differs",
                ));
            }
        }
        exact(&mapped, live, "/preparation")
    }
}

pub(super) fn compare_preparation<B: ReplayProductionBindings + ?Sized>(
    old: &ReplayPreparedProjection,
    live: &ReplayPreparedProjection,
    bindings: &mut B,
) -> Result<(), ReplayDivergence> {
    Compare { bindings }.preparation(old, live)
}

impl<B: ReplayProductionBindings + ?Sized> Compare<'_, B> {
    fn failure(
        &mut self,
        old: &ReplayPrivateFailure,
        live: &ReplayPrivateFailure,
        path: &str,
    ) -> Result<ReplayPrivateFailure, ReplayDivergence> {
        let mut mapped = old.clone();
        mapped.artifacts =
            self.artifacts(&old.artifacts, &live.artifacts, &child(path, "artifacts"))?;
        // Commitment, presence, origin/kind/scope/retryability all remain exact.
        // Only the native owner ever reads/reconstructs the underlying detail.
        exact(&mapped, live, path)?;
        Ok(mapped)
    }
    fn optional_failure(
        &mut self,
        old: &Option<ReplayPrivateFailure>,
        live: &Option<ReplayPrivateFailure>,
        path: &str,
    ) -> Result<Option<ReplayPrivateFailure>, ReplayDivergence> {
        match (old, live) {
            (None, None) => Ok(None),
            (Some(old), Some(live)) => self.failure(old, live, path).map(Some),
            _ => Err(divergent(path, "private failure presence differs")),
        }
    }
    fn terminal(
        &mut self,
        old: &ReplaySpecializedTerminalProjection,
        live: &ReplaySpecializedTerminalProjection,
        path: &str,
    ) -> Result<(), ReplayDivergence> {
        self.require(
            ReplayProductionIdentity::Entailment,
            &old.entailment_identity,
            &live.entailment_identity,
            &child(path, "entailment_identity"),
        )?;
        let mut mapped = old.clone();
        mapped
            .entailment_identity
            .clone_from(&live.entailment_identity);
        self.bindings
            .bind_attempt(old.attempt_id, live.attempt_id, &child(path, "attempt_id"))?;
        mapped.attempt_id = live.attempt_id;
        mapped.query_artifact = self.artifact(
            &old.query_artifact,
            &live.query_artifact,
            &child(path, "query_artifact"),
        )?;
        mapped.constructor_references = self.artifacts(
            &old.constructor_references,
            &live.constructor_references,
            &child(path, "constructor_references"),
        )?;
        // Native terminal summaries sort/deduplicate physical references. Pair
        // the complete original ordered inputs first, then run that exact rule;
        // pairing sorted outputs would confuse legitimate allocation permutations.
        mapped.references = mapped.constructor_references.clone();
        mapped.references.push(mapped.query_artifact.clone());
        mapped.references.sort_unstable_by_key(|a| a.local_id);
        mapped.references.dedup();
        exact(
            &mapped.references,
            &live.references,
            &child(path, "references"),
        )?;
        use ReplaySpecializedTerminalDetail as D;
        match (&mut mapped.detail, &live.detail) {
            (
                D::TimedOut { peer_failure, .. },
                D::TimedOut {
                    peer_failure: live_failure,
                    ..
                },
            )
            | (
                D::CancelledSolver { peer_failure, .. },
                D::CancelledSolver {
                    peer_failure: live_failure,
                    ..
                },
            ) => {
                *peer_failure = self.optional_failure(
                    peer_failure,
                    live_failure,
                    &child(path, "detail/peer_failure"),
                )?
            }
            (
                D::Failure { failure, .. },
                D::Failure {
                    failure: live_failure,
                    ..
                },
            ) => *failure = self.failure(failure, live_failure, &child(path, "detail/failure"))?,
            (
                D::CancelledRefutation { source },
                D::CancelledRefutation {
                    source: live_source,
                },
            )
            | (
                D::UnvalidatedRefutation { source },
                D::UnvalidatedRefutation {
                    source: live_source,
                },
            ) => *source = self.artifact(source, live_source, &child(path, "detail/source"))?,
            (
                D::CancelledEmpty { retained_proof },
                D::CancelledEmpty {
                    retained_proof: live_proof,
                },
            ) => {
                *retained_proof = self.artifact(
                    retained_proof,
                    live_proof,
                    &child(path, "detail/retained_proof"),
                )?
            }
            (D::Proved { .. }, D::Proved { .. })
            | (D::RefutedModel { .. }, D::RefutedModel { .. })
            | (D::RefutedEmpty { .. }, D::RefutedEmpty { .. })
            | (D::RefutedEmptyAfterProof { .. }, D::RefutedEmptyAfterProof { .. }) => {}
            _ => {
                return Err(divergent(
                    &child(path, "detail"),
                    "terminal outcome variant differs",
                ));
            }
        }
        // No digest evidence is accepted without the caller's prior two-sided
        // private-owner verification. Full typed equality checks every other field.
        mapped = mapped.with_replay_digest(
            ReplaySha256::parse(live.digest())
                .map_err(|_| divergent(path, "invalid terminal digest"))?,
        );
        exact(&mapped, live, path)?;
        self.bind(
            ReplayProductionIdentity::Terminal,
            old.digest(),
            live.digest(),
            &child(path, "terminal_result_digest"),
        )
    }
    fn associations(
        &mut self,
        old: &[ReplayArtifactAssociation],
        live: &[ReplayArtifactAssociation],
        path: &str,
    ) -> Result<(), ReplayDivergence> {
        exact(&old.len(), &live.len(), path)?;
        for (i, (old, live)) in old.iter().zip(live).enumerate() {
            let p = format!("{path}/{i}");
            exact(&old.role, &live.role, &child(&p, "role"))?;
            let mut mapped = old.clone();
            mapped.artifact =
                self.artifact(&old.artifact, &live.artifact, &child(&p, "artifact"))?;
            exact(&mapped, live, &p)?;
        }
        Ok(())
    }
    fn request(
        &self,
        old: &ReplaySha256,
        live: &ReplaySha256,
        path: &str,
    ) -> Result<ReplaySha256, ReplayDivergence> {
        self.require(
            ReplayProductionIdentity::CheckRequest,
            old.as_str(),
            live.as_str(),
            path,
        )?;
        Ok(live.clone())
    }
    fn physical(
        &mut self,
        old: PhysicalAttemptId,
        live: PhysicalAttemptId,
        path: &str,
    ) -> Result<PhysicalAttemptId, ReplayDivergence> {
        self.bindings.bind_attempt(old, live, path)?;
        Ok(live)
    }
    fn production(
        &mut self,
        old: &ReplayProductionProjection,
        live: &ReplayProductionProjection,
        old_artifacts: &[ReplayArtifactAssociation],
        live_artifacts: &[ReplayArtifactAssociation],
    ) -> Result<(), ReplayDivergence> {
        use ReplayProductionProjection as P;
        let (old_digest, live_digest, category) = match (old, live) {
            (
                P::RuntimeProof {
                    fields: old,
                    original_digest: old_digest,
                    terminal: old_terminal,
                },
                P::RuntimeProof {
                    fields: live,
                    original_digest: live_digest,
                    terminal: live_terminal,
                },
            ) => {
                self.terminal(old_terminal, live_terminal, "/production/terminal")?;
                let mut mapped = (**old).clone();
                mapped.fixed_ambient_job = self.fixed(
                    &old.fixed_ambient_job,
                    &live.fixed_ambient_job,
                    false,
                    "/production/fields/fixed_ambient_job",
                )?;
                mapped.request_digest = self.request(
                    &old.request_digest,
                    &live.request_digest,
                    "/production/fields/request_digest",
                )?;
                self.require(
                    ReplayProductionIdentity::Catalog,
                    old.catalog_digest.as_str(),
                    live.catalog_digest.as_str(),
                    "/production/fields/catalog_digest",
                )?;
                mapped.catalog_digest = live.catalog_digest.clone();
                mapped.attempt =
                    self.physical(old.attempt, live.attempt, "/production/fields/attempt")?;
                mapped.query_artifact = self.artifact(
                    &old.query_artifact,
                    &live.query_artifact,
                    "/production/fields/query_artifact",
                )?;
                mapped.proof_artifact = self.artifact(
                    &old.proof_artifact,
                    &live.proof_artifact,
                    "/production/fields/proof_artifact",
                )?;
                mapped.terminal_artifact = self.artifact(
                    &old.terminal_artifact,
                    &live.terminal_artifact,
                    "/production/fields/terminal_artifact",
                )?;
                mapped.empty_check_artifact = self.artifact(
                    &old.empty_check_artifact,
                    &live.empty_check_artifact,
                    "/production/fields/empty_check_artifact",
                )?;
                self.require(
                    ReplayProductionIdentity::Terminal,
                    old.terminal_result_digest.as_str(),
                    live.terminal_result_digest.as_str(),
                    "/production/fields/terminal_result_digest",
                )?;
                mapped.terminal_result_digest = live.terminal_result_digest.clone();
                mapped.artifact_backend_digest = live.artifact_backend_digest.clone();
                exact(&mapped, live.as_ref(), "/production/fields")?;
                self.bind(
                    ReplayProductionIdentity::ArtifactBackendDigest,
                    old.artifact_backend_digest.as_str(),
                    live.artifact_backend_digest.as_str(),
                    "/production/fields/artifact_backend_digest",
                )?;
                (
                    old_digest,
                    live_digest,
                    ReplayProductionIdentity::ProductionReceipt,
                )
            }
            (
                P::Protected {
                    fields: old,
                    original_digest: old_digest,
                },
                P::Protected {
                    fields: live,
                    original_digest: live_digest,
                },
            ) => {
                let mut mapped = (**old).clone();
                mapped.fixed_ambient_job = self.fixed(
                    &old.fixed_ambient_job,
                    &live.fixed_ambient_job,
                    false,
                    "/production/fields/fixed_ambient_job",
                )?;
                mapped.request_digest = self.request(
                    &old.request_digest,
                    &live.request_digest,
                    "/production/fields/request_digest",
                )?;
                exact(&mapped, live.as_ref(), "/production/fields")?;
                (
                    old_digest,
                    live_digest,
                    ReplayProductionIdentity::ProductionReceipt,
                )
            }
            (
                P::Progress {
                    fields: old,
                    original_digest: old_digest,
                    terminal: old_terminal,
                },
                P::Progress {
                    fields: live,
                    original_digest: live_digest,
                    terminal: live_terminal,
                },
            ) => {
                self.terminal(old_terminal, live_terminal, "/production/terminal")?;
                let mut mapped = (**old).clone();
                mapped.fixed_ambient_job = self.fixed(
                    &old.fixed_ambient_job,
                    &live.fixed_ambient_job,
                    false,
                    "/production/fields/fixed_ambient_job",
                )?;
                mapped.request_digest = self.request(
                    &old.request_digest,
                    &live.request_digest,
                    "/production/fields/request_digest",
                )?;
                mapped.attempt =
                    self.physical(old.attempt, live.attempt, "/production/fields/attempt")?;
                mapped.terminal_artifact = self.artifact(
                    &old.terminal_artifact,
                    &live.terminal_artifact,
                    "/production/fields/terminal_artifact",
                )?;
                mapped.peer_failure = self.optional_failure(
                    &old.peer_failure,
                    &live.peer_failure,
                    "/production/fields/peer_failure",
                )?;
                self.require(
                    ReplayProductionIdentity::Terminal,
                    old.terminal_result_digest.as_str(),
                    live.terminal_result_digest.as_str(),
                    "/production/fields/terminal_result_digest",
                )?;
                mapped.terminal_result_digest = live.terminal_result_digest.clone();
                exact(&mapped, live.as_ref(), "/production/fields")?;
                (
                    old_digest,
                    live_digest,
                    ReplayProductionIdentity::ProductionReceipt,
                )
            }
            (
                P::ValidatedRefutation {
                    fields: old,
                    original_digest: old_digest,
                    terminal: old_terminal,
                },
                P::ValidatedRefutation {
                    fields: live,
                    original_digest: live_digest,
                    terminal: live_terminal,
                },
            ) => {
                self.terminal(old_terminal, live_terminal, "/production/terminal")?;
                let mut mapped = (**old).clone();
                mapped.fixed_ambient_job = self.fixed(
                    &old.fixed_ambient_job,
                    &live.fixed_ambient_job,
                    false,
                    "/production/fields/fixed_ambient_job",
                )?;
                mapped.request_digest = self.request(
                    &old.request_digest,
                    &live.request_digest,
                    "/production/fields/request_digest",
                )?;
                mapped.attempt =
                    self.physical(old.attempt, live.attempt, "/production/fields/attempt")?;
                mapped.terminal_artifact = self.artifact(
                    &old.terminal_artifact,
                    &live.terminal_artifact,
                    "/production/fields/terminal_artifact",
                )?;
                mapped.source_artifact = self.artifact(
                    &old.source_artifact,
                    &live.source_artifact,
                    "/production/fields/source_artifact",
                )?;
                mapped.validation_artifact = self.artifact(
                    &old.validation_artifact,
                    &live.validation_artifact,
                    "/production/fields/validation_artifact",
                )?;
                self.require(
                    ReplayProductionIdentity::Terminal,
                    old.terminal_result_digest.as_str(),
                    live.terminal_result_digest.as_str(),
                    "/production/fields/terminal_result_digest",
                )?;
                mapped.terminal_result_digest = live.terminal_result_digest.clone();
                exact(&mapped, live.as_ref(), "/production/fields")?;
                (
                    old_digest,
                    live_digest,
                    ReplayProductionIdentity::ProductionReceipt,
                )
            }
            (
                P::SemanticReuse {
                    fields: old,
                    original_digest: old_digest,
                    current_request_digest: old_request,
                    semantic_key_identity: old_key,
                },
                P::SemanticReuse {
                    fields: live,
                    original_digest: live_digest,
                    current_request_digest: live_request,
                    semantic_key_identity: live_key,
                },
            ) => {
                exact(&old_artifacts.len(), &0, "/production/artifacts")?;
                exact(&live_artifacts.len(), &0, "/production/artifacts")?;
                self.request(
                    old_request,
                    live_request,
                    "/production/current_request_digest",
                )?;
                exact(old_key, live_key, "/production/semantic_key_identity")?;
                let mut mapped = (**old).clone();
                mapped.original_request_digest = self.request(
                    &old.original_request_digest,
                    &live.original_request_digest,
                    "/production/fields/original_request_digest",
                )?;
                // Missing original evidence is a dependency, never permission to
                // infer its mapping from this reuse wrapper. Preserve map errors.
                self.require(
                    ReplayProductionIdentity::EvidenceIdentity,
                    old.original_evidence_identity.as_str(),
                    live.original_evidence_identity.as_str(),
                    "/production/fields/original_evidence_identity",
                )?;
                mapped.original_evidence_identity = live.original_evidence_identity.clone();
                exact(&mapped, live.as_ref(), "/production/fields")?;
                (
                    old_digest,
                    live_digest,
                    ReplayProductionIdentity::SemanticReuse,
                )
            }
            _ => return Err(divergent("/production", "production route variant differs")),
        };
        self.associations(old_artifacts, live_artifacts, "/production/artifacts")?;
        self.bind(
            category,
            old_digest.as_str(),
            live_digest.as_str(),
            "/production/original_digest",
        )
    }
}

/// Both projections must first pass the corresponding fresh native owner's
/// two-sided verifier (including private terminal/progress reconstruction).
/// The caller discards its provisional maps on any returned error.
pub(super) fn compare_production<B: ReplayProductionBindings + ?Sized>(
    old: &ReplayProductionProjection,
    live: &ReplayProductionProjection,
    old_artifact_associations: &[ReplayArtifactAssociation],
    live_artifact_associations: &[ReplayArtifactAssociation],
    bindings: &mut B,
) -> Result<(), ReplayDivergence> {
    Compare { bindings }.production(
        old,
        live,
        old_artifact_associations,
        live_artifact_associations,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::encoding::canonical_value_sha256;
    use serde_json::{Value, json};
    use std::collections::BTreeMap;

    #[derive(Clone, Default)]
    struct Maps {
        identities: BTreeMap<(ReplayProductionIdentity, String), String>,
        reverse: BTreeMap<(ReplayProductionIdentity, String), String>,
        artifacts: BTreeMap<(String, u64), (String, u64)>,
        artifact_reverse: BTreeMap<(String, u64), (String, u64)>,
        attempts: BTreeMap<PhysicalAttemptId, PhysicalAttemptId>,
        attempt_reverse: BTreeMap<PhysicalAttemptId, PhysicalAttemptId>,
    }
    fn pair<K: Ord + Clone + PartialEq>(
        forward: &mut BTreeMap<K, K>,
        reverse: &mut BTreeMap<K, K>,
        old: K,
        live: K,
        path: &str,
    ) -> Result<(), ReplayDivergence> {
        if forward.get(&old).is_some_and(|value| value != &live)
            || reverse.get(&live).is_some_and(|value| value != &old)
        {
            return Err(divergent(path, "bijection conflict"));
        }
        forward.insert(old.clone(), live.clone());
        reverse.insert(live, old);
        Ok(())
    }
    impl ReplayProductionBindings for Maps {
        fn bind_identity(
            &mut self,
            kind: ReplayProductionIdentity,
            old: &str,
            live: &str,
            path: &str,
        ) -> Result<(), ReplayDivergence> {
            let old_key = (kind, old.to_owned());
            let live_key = (kind, live.to_owned());
            if self
                .identities
                .get(&old_key)
                .is_some_and(|value| value != live)
                || self
                    .reverse
                    .get(&live_key)
                    .is_some_and(|value| value != old)
            {
                return Err(divergent(path, "bijection conflict"));
            }
            self.identities.insert(old_key, live.into());
            self.reverse.insert(live_key, old.into());
            Ok(())
        }
        fn require_identity(
            &self,
            kind: ReplayProductionIdentity,
            old: &str,
            live: &str,
            path: &str,
        ) -> Result<(), ReplayDivergence> {
            match self.identities.get(&(kind, old.into())) {
                Some(mapped) if mapped == live => Ok(()),
                Some(_) => Err(divergent(path, "bijection conflict")),
                None => Err(divergent(path, &format!("missing dependency: {kind:?}"))),
            }
        }
        fn bind_artifact(
            &mut self,
            old: &ReplayArtifactIdentity,
            live: &ReplayArtifactIdentity,
            path: &str,
        ) -> Result<(), ReplayDivergence> {
            pair(
                &mut self.artifacts,
                &mut self.artifact_reverse,
                (old.backend.0.clone(), old.local_id),
                (live.backend.0.clone(), live.local_id),
                path,
            )
        }
        fn bind_attempt(
            &mut self,
            old: PhysicalAttemptId,
            live: PhysicalAttemptId,
            path: &str,
        ) -> Result<(), ReplayDivergence> {
            pair(
                &mut self.attempts,
                &mut self.attempt_reverse,
                old,
                live,
                path,
            )
        }
    }
    fn h(c: char) -> String {
        c.to_string().repeat(64)
    }
    fn decode<T: serde::de::DeserializeOwned>(value: Value) -> T {
        serde_json::from_value(value).unwrap()
    }
    fn prepared(sequence: u64, backend: char, query_id: u64) -> ReplayPreparedProjection {
        // Constructor-shaped DTO fixture, not a native solver receipt. It uses
        // the actual allocation/structural identity verifiers; route tests below
        // exercise only the visitor after the documented native-owner boundary.
        let scope = json!({"kind":"whiel_framework_ii_fixed_ambient_task","version":2,"semantic_version":1,"encoding_version":1,"task_canonical_id":"Example0001","task_module":"Task","task_namespace":"Task","task_source_sha256":h('c'),"ambient_scope":["whiel-framework-ii-fixed-ambient-scope-v1",[["R",1]],[]]});
        let snapshot = json!({"kind":"whiel_fixed_ambient_snapshot","version":1,"rows":[{"clause_id":0,"level":0,"identity":{"kind":"whiel_fixed_ambient_clause","version":1,"formula":["true"]},"canonical_source":"true"}]});
        let selector = json!({"kind":"initialization","clause_id":0});
        let obligation = json!({"kind":"whiel_fixed_ambient_obligation","version":1,"scope_identity":scope,"snapshot":snapshot,"selector":selector});
        let worker = json!({"axioms":[{"kind":"whiel_qf_formula","version":3,"formula":["true"]}],"conjecture":{"kind":"whiel_qf_formula","version":3,"formula":["false"]}});
        let job = canonical_value_sha256(
            &json!({"kind":"whiel_fixed_ambient_validity_job","version":1,"obligation_identity":obligation,"worker_entailment_identity":worker}),
        );
        let empty = json!({"kind":"whiel_fixed_ambient_empty_counterexample_request","version":1,"scope_identity":scope,"obligation_identity":obligation,"worker_entailment_identity":worker});
        let allocation = crate::encoding::ReplayFixedAmbientAllocation {
            canonical_id: "Example0001".into(),
            allocation_sequence: sequence,
            context_id: format!("fixed-ambient-Example0001-{sequence}"),
        };
        let body = |source: &str, tptp: &str| json!({"source":"quantifier_free","source_id":source,"body_id":allocation.body_id(source),"fol_identity":format!("fol-{source}"),"theorem_id":format!("Theorem.{source}"),"semantic_version":1,"encoding_version":1,"constants":[],"tptp_body":tptp});
        let structure: ReplayEntailmentStructure = decode(
            json!({"allocation":allocation,"context_id":allocation.context_id,"canonical_id":"Example0001","module":"Task","namespace":"Task","source_digest":h('c'),"semantic_version":1,"encoding_version":1,"worker_entailment_digest":canonical_value_sha256(&worker),"constants":[],"support_block_id":allocation.support_id(std::iter::empty::<&str>()),"support_bodies":["fof(support,axiom,$true)."],"axiom_bodies":[body("axiom","$true")],"goal_bodies":[body("goal","$false")]}),
        );
        let entailment = structure.derive_identity();
        let prep = json!({"kind":"whiel_fixed_ambient_obligation_preparation","version":1,"scope_identity":scope,"obligation_identity":obligation,"worker_entailment_identity":worker,"job_id":job,"empty_request_identity":empty,"empty_request_digest":canonical_value_sha256(&empty),"entailment_identity":entailment});
        let fixed = json!({"preparation_identity":prep,"preparation_digest":canonical_value_sha256(&prep),"obligation_identity":obligation,"obligation_digest":canonical_value_sha256(&obligation),"worker_entailment_identity":worker,"job_id":job,"empty_request_identity":empty,"empty_request_digest":canonical_value_sha256(&empty),"entailment_identity":entailment,"query_artifact":{"backend":backend.to_string().repeat(32),"local_id":query_id,"kind":"Query"}});
        let request = json!({"kind":"whiel_framework_ii_fixed_ambient_check_request","version":1,"attempt_ordinal":0,"scope_identity":scope,"snapshot_identity":snapshot,"selector":selector});
        let digest = canonical_value_sha256(&request);
        let result: ReplayPreparedProjection = decode(
            json!({"fixed_ambient_job":fixed,"entailment_structure":structure,"control_request_digest":digest,"control_subject":{"subject":"clause","identity":request,"request_digest":digest,"level":0,"launch_suppressed":false},"control_target":selector,"control_snapshot":snapshot,"scope_digest":canonical_value_sha256(&scope),"catalog_digest":h('a'),"partition_digest":h('b'),"framework_context_digest":canonical_value_sha256(&obligation)}),
        );
        result.verify().unwrap();
        result
    }
    fn roots(old: &ReplayPreparedProjection, live: &ReplayPreparedProjection) -> Maps {
        let mut maps = Maps::default();
        for (kind, old, live) in [
            (
                ReplayProductionIdentity::Catalog,
                old.catalog_digest.as_str(),
                live.catalog_digest.as_str(),
            ),
            (
                ReplayProductionIdentity::Partition,
                old.partition_digest.as_str(),
                live.partition_digest.as_str(),
            ),
            (
                ReplayProductionIdentity::CheckRequest,
                old.control_request_digest.as_str(),
                live.control_request_digest.as_str(),
            ),
            (
                ReplayProductionIdentity::Backend,
                old.fixed_ambient_job.query_artifact.backend.as_str(),
                live.fixed_ambient_job.query_artifact.backend.as_str(),
            ),
        ] {
            maps.bind_identity(kind, old, live, "fixture roots")
                .unwrap();
        }
        maps
    }
    fn artifact(
        prepared: &ReplayPreparedProjection,
        id: u64,
        kind: ReplayArtifactKind,
    ) -> ReplayArtifactIdentity {
        ReplayArtifactIdentity {
            backend: prepared.fixed_ambient_job.query_artifact.backend.clone(),
            local_id: id,
            kind,
        }
    }
    #[test]
    fn fresh_allocations_rederive_complete_preparation_and_require_roots() {
        let old = prepared(2, '0', 1);
        let live = prepared(19, '1', 90);
        let mut maps = roots(&old, &live);
        compare_preparation(&old, &live, &mut maps).unwrap();
        maps.require_identity(
            ReplayProductionIdentity::Entailment,
            &old.fixed_ambient_job.entailment_identity.0,
            &live.fixed_ambient_job.entailment_identity.0,
            "entailment",
        )
        .unwrap();
        assert_ne!(
            old.fixed_ambient_job.preparation_digest,
            live.fixed_ambient_job.preparation_digest
        );
        let mut missing = Maps::default();
        let error = compare_preparation(&old, &live, &mut missing).unwrap_err();
        assert!(error.reason.starts_with("missing dependency:"));
        assert_eq!(error.path, "/preparation/catalog_digest");
        let mut bad = live.clone();
        bad.entailment_structure.allocation.allocation_sequence += 1;
        assert!(compare_preparation(&old, &bad, &mut roots(&old, &live)).is_err());
        let mut bad = live.clone();
        bad.fixed_ambient_job.preparation_digest = ReplaySha256::parse(&h('f')).unwrap();
        assert!(compare_preparation(&old, &bad, &mut roots(&old, &live)).is_err());
    }
    #[test]
    fn body_support_and_worker_semantics_cannot_hide_behind_reallocated_ids() {
        let old = prepared(2, '0', 1);
        let live = prepared(19, '1', 90);
        for field in [
            "tptp_body",
            "source_id",
            "fol_identity",
            "theorem_id",
            "semantic_version",
            "constants",
        ] {
            let mut value = serde_json::to_value(&live.entailment_structure).unwrap();
            value["axiom_bodies"][0][field] = match field {
                "semantic_version" => json!(2),
                "constants" => json!(["data:0"]),
                _ => json!("changed"),
            };
            let bad: ReplayEntailmentStructure = decode(value);
            assert!(
                Compare {
                    bindings: &mut roots(&old, &live)
                }
                .structure(&old.entailment_structure, &bad, "/structure")
                .is_err(),
                "{field}"
            );
        }
        let mut bad = live.entailment_structure.clone();
        bad.support_bodies[0].push_str("changed");
        assert!(
            Compare {
                bindings: &mut roots(&old, &live)
            }
            .structure(&old.entailment_structure, &bad, "/structure")
            .is_err()
        );
        let mut bad = live.entailment_structure.clone();
        bad.worker_entailment_digest = h('f');
        assert!(
            Compare {
                bindings: &mut roots(&old, &live)
            }
            .structure(&old.entailment_structure, &bad, "/structure")
            .is_err()
        );
    }
    fn terminal(
        prepared: &ReplayPreparedProjection,
        attempt: u64,
        source_id: u64,
    ) -> ReplaySpecializedTerminalProjection {
        let source = artifact(prepared, source_id, ReplayArtifactKind::Model);
        let query = prepared.fixed_ambient_job.query_artifact.clone();
        let mut refs = vec![source.clone(), query.clone()];
        refs.sort_unstable_by_key(|a| a.local_id);
        refs.dedup();
        decode(
            json!({"entailment_identity":prepared.fixed_ambient_job.entailment_identity,"attempt_id":attempt,"query_artifact":query,"constructor_references":[source,source],"references":refs,"detail":{"kind":"unvalidated_refutation","source":source},"terminal_result_digest":h(if attempt==7{'d'}else{'e'})}),
        )
    }
    #[test]
    fn terminal_pairs_constructor_roles_before_physical_sort_and_preserves_multiplicity() {
        let old_prepared = prepared(2, '0', 1);
        let live_prepared = prepared(19, '1', 90);
        let mut maps = roots(&old_prepared, &live_prepared);
        compare_preparation(&old_prepared, &live_prepared, &mut maps).unwrap();
        let old = terminal(&old_prepared, 7, 20);
        let live = terminal(&live_prepared, 23, 10);
        assert_eq!(old.references[0].kind, ReplayArtifactKind::Query);
        assert_eq!(live.references[0].kind, ReplayArtifactKind::Model);
        Compare {
            bindings: &mut maps,
        }
        .terminal(&old, &live, "/terminal")
        .unwrap();
        assert_eq!(maps.attempts[&PhysicalAttemptId(7)], PhysicalAttemptId(23));
        let mut bad = live.clone();
        bad.constructor_references.pop();
        assert!(
            Compare {
                bindings: &mut maps.clone()
            }
            .terminal(&old, &bad, "/terminal")
            .is_err()
        );
        let mut bad = live.clone();
        bad.references.reverse();
        assert!(
            Compare {
                bindings: &mut maps.clone()
            }
            .terminal(&old, &bad, "/terminal")
            .is_err()
        );
        let mut bad = live;
        bad.detail = ReplaySpecializedTerminalDetail::CancelledRefutation {
            source: artifact(&live_prepared, 10, ReplayArtifactKind::Model),
        };
        assert!(
            Compare {
                bindings: &mut maps
            }
            .terminal(&old, &bad, "/terminal")
            .is_err()
        );
    }
    #[test]
    fn private_commitments_artifact_roles_and_reverse_collisions_remain_exact() {
        let old = prepared(2, '0', 1);
        let live = prepared(19, '1', 90);
        let maps = roots(&old, &live);
        let failure = |p: &ReplayPreparedProjection, id| ReplayPrivateFailure {
            origin: ReplayFailureOrigin::VampireRace,
            kind: ReplayFailureKind::ProcessFailure,
            retryable: false,
            scope: ReplayFailureScope::LaneLocal,
            detail_digest: Some(ReplaySha256::parse(&h('a')).unwrap()),
            artifacts: vec![artifact(p, id, ReplayArtifactKind::FailureDiagnostic)],
        };
        let old_failure = failure(&old, 2);
        let live_failure = failure(&live, 4);
        Compare {
            bindings: &mut maps.clone(),
        }
        .failure(&old_failure, &live_failure, "/failure")
        .unwrap();
        let mut bad = live_failure.clone();
        bad.detail_digest = None;
        assert!(
            Compare {
                bindings: &mut maps.clone()
            }
            .failure(&old_failure, &bad, "/failure")
            .is_err()
        );
        let mut bad = live_failure.clone();
        bad.artifacts.clear();
        assert!(
            Compare {
                bindings: &mut maps.clone()
            }
            .failure(&old_failure, &bad, "/failure")
            .is_err()
        );
        let old_assoc = ReplayArtifactAssociation {
            role: ReplayArtifactRole::Proof {},
            artifact: artifact(&old, 2, ReplayArtifactKind::Proof),
        };
        let live_assoc = ReplayArtifactAssociation {
            role: ReplayArtifactRole::RouteReceipt {},
            artifact: artifact(&live, 4, ReplayArtifactKind::Proof),
        };
        assert!(
            Compare {
                bindings: &mut maps.clone()
            }
            .associations(&[old_assoc], &[live_assoc], "/artifacts")
            .is_err()
        );
        let mut maps = maps;
        let mut compare = Compare {
            bindings: &mut maps,
        };
        compare
            .artifact(
                &artifact(&old, 2, ReplayArtifactKind::Proof),
                &artifact(&live, 4, ReplayArtifactKind::Proof),
                "/first",
            )
            .unwrap();
        assert!(
            compare
                .artifact(
                    &artifact(&old, 3, ReplayArtifactKind::Proof),
                    &artifact(&live, 4, ReplayArtifactKind::Proof),
                    "/second"
                )
                .is_err()
        );
    }
    fn progress_projection(
        prepared: &ReplayPreparedProjection,
        terminal: &ReplaySpecializedTerminalProjection,
        trace: u64,
    ) -> ReplayProductionProjection {
        let fields = json!({"domain":"whiel-framework-ii-entailment-progress-v3","request_digest":prepared.control_request_digest,"job_id":prepared.fixed_ambient_job.job_id,"semantic_vc_digest":prepared.fixed_ambient_job.obligation_digest,"fixed_ambient_job":prepared.fixed_ambient_job,"reason":"unvalidated_refutation","attempt":terminal.attempt_id,"next_fmb_start_size":null,"previous_proof_allowance_ns":"100","current_proof_allowance_ns":"200","peer_failure":null,"terminal_artifact":artifact(prepared,trace,ReplayArtifactKind::RuntimeTrace),"terminal_result_digest":terminal.digest()});
        decode(
            json!({"route":"progress","original_digest":canonical_value_sha256(&fields),"fields":fields,"terminal":terminal}),
        )
    }
    #[test]
    fn progress_route_checks_full_fields_and_all_associations_after_preparation() {
        let old_prepared = prepared(2, '0', 1);
        let live_prepared = prepared(19, '1', 90);
        let mut maps = roots(&old_prepared, &live_prepared);
        compare_preparation(&old_prepared, &live_prepared, &mut maps).unwrap();
        let old = progress_projection(&old_prepared, &terminal(&old_prepared, 7, 20), 30);
        let live = progress_projection(&live_prepared, &terminal(&live_prepared, 23, 10), 40);
        let associations = |p: &ReplayPreparedProjection, trace, receipt| {
            vec![
                ReplayArtifactAssociation {
                    role: ReplayArtifactRole::Query {},
                    artifact: p.fixed_ambient_job.query_artifact.clone(),
                },
                ReplayArtifactAssociation {
                    role: ReplayArtifactRole::TerminalTrace {},
                    artifact: artifact(p, trace, ReplayArtifactKind::RuntimeTrace),
                },
                ReplayArtifactAssociation {
                    role: ReplayArtifactRole::ProgressReceipt {},
                    artifact: artifact(p, receipt, ReplayArtifactKind::Witness),
                },
            ]
        };
        let old_artifacts = associations(&old_prepared, 30, 31);
        let live_artifacts = associations(&live_prepared, 40, 41);
        compare_production(
            &old,
            &live,
            &old_artifacts,
            &live_artifacts,
            &mut maps.clone(),
        )
        .unwrap();
        for field in [
            "current_proof_allowance_ns",
            "next_fmb_start_size",
            "semantic_vc_digest",
        ] {
            let mut bad = serde_json::to_value(&live).unwrap();
            bad["fields"][field] = match field {
                "next_fmb_start_size" => json!(3),
                "semantic_vc_digest" => json!(h('f')),
                _ => json!("300"),
            };
            let bad = decode(bad);
            assert!(
                compare_production(
                    &old,
                    &bad,
                    &old_artifacts,
                    &live_artifacts,
                    &mut maps.clone()
                )
                .is_err(),
                "{field}"
            );
        }
        assert!(
            compare_production(
                &old,
                &live,
                &old_artifacts,
                &live_artifacts[..2],
                &mut maps.clone()
            )
            .is_err()
        );
        let mut swapped = live_artifacts.clone();
        swapped.swap(1, 2);
        assert!(compare_production(&old, &live, &old_artifacts, &swapped, &mut maps).is_err());
    }
    fn reuse(prepared: &ReplayPreparedProjection, old: bool) -> ReplayProductionProjection {
        let key = json!({"role":"initialization","kind":"whiel_framework_ii_semantic_vc_key","version":9,"task_identity":{"canonical_id":"Example0001","module":"Task","namespace":"Task","source_sha256":h('c'),"semantic_version":1,"encoding_version":1},"scope_identity":prepared.fixed_ambient_job.obligation_identity.scope_identity,"conjecture":{"identity_sha256":h('f')},"tagged_premises":[{"tag":"pre","identity":null}]});
        let fields = json!({"kind":"whiel_framework_ii_semantic_reuse","version":9,"reuse_kind":"proof_subsumption","semantic_vc_key":canonical_value_sha256(&key),"matched_tagged_premises":[{"tag":"pre","identity":null}],"original_request_digest":h(if old{'d'}else{'e'}),"original_evidence_identity":h(if old{'4'}else{'5'})});
        decode(
            json!({"route":"semantic_reuse","fields":fields,"original_digest":canonical_value_sha256(&fields),"current_request_digest":prepared.control_request_digest,"semantic_key_identity":key}),
        )
    }
    #[test]
    fn semantic_reuse_requires_previously_verified_original_evidence() {
        let old_prepared = prepared(2, '0', 1);
        let live_prepared = prepared(19, '1', 90);
        let mut maps = roots(&old_prepared, &live_prepared);
        maps.bind_identity(
            ReplayProductionIdentity::CheckRequest,
            &h('d'),
            &h('e'),
            "original request",
        )
        .unwrap();
        let old = reuse(&old_prepared, true);
        let live = reuse(&live_prepared, false);
        let error = compare_production(&old, &live, &[], &[], &mut maps).unwrap_err();
        assert_eq!(error.path, "/production/fields/original_evidence_identity");
        assert_eq!(error.reason, "missing dependency: EvidenceIdentity");
        maps.bind_identity(
            ReplayProductionIdentity::EvidenceIdentity,
            &h('4'),
            &h('5'),
            "checked original evidence",
        )
        .unwrap();
        compare_production(&old, &live, &[], &[], &mut maps.clone()).unwrap();
        let mut bad = serde_json::to_value(live).unwrap();
        bad["fields"]["matched_tagged_premises"] = json!([]);
        let bad = decode(bad);
        assert!(compare_production(&old, &bad, &[], &[], &mut maps).is_err());
    }
    fn terminal_variant(
        prepared: &ReplayPreparedProjection,
        attempt: u64,
        detail: Value,
        refs: Vec<ReplayArtifactIdentity>,
    ) -> Value {
        let mut sorted = refs.clone();
        sorted.push(prepared.fixed_ambient_job.query_artifact.clone());
        sorted.sort_unstable_by_key(|a| a.local_id);
        sorted.dedup();
        json!({"entailment_identity":prepared.fixed_ambient_job.entailment_identity,"attempt_id":attempt,"query_artifact":prepared.fixed_ambient_job.query_artifact,"constructor_references":refs,"references":sorted,"detail":detail,"terminal_result_digest":h(if attempt==7{'d'}else{'e'})})
    }
    fn other_route(
        prepared: &ReplayPreparedProjection,
        old: bool,
        route: &str,
    ) -> ReplayProductionProjection {
        let id = if old { 2 } else { 10 };
        let attempt = if old { 7 } else { 23 };
        let fixed = &prepared.fixed_ambient_job;
        if route == "protected" {
            let fields = json!({"domain":"whiel-framework-ii-protected-theorem-selection-v3","request_digest":prepared.control_request_digest,"selector_registry_digest":h('a'),"rule":{"kind":"edb_precondition_initialization","source_conjunct":h('b'),"target_clause":0,"target_context":fixed.obligation_digest},"source_route_digest":h('c'),"source_formula_digest":h('b'),"target_vc_digest":fixed.obligation_digest,"fixed_ambient_job":fixed,"theorem_name":"Whiel.Synthesis.FrameworkII.FixedAmbient.EdbPrecondition.initVC_valid","registry_entry_digest":h('f')});
            return decode(
                json!({"route":route,"original_digest":canonical_value_sha256(&fields),"fields":fields}),
            );
        }
        let (fields, terminal) = if route == "validated_refutation" {
            let validation = json!({"kind":"whiel_framework_ii_base_refutation_validation","version":1,"obligation_identity":fixed.obligation_identity,"interpretation_identity":{"kind":"whiel_framework_ii_finite_interpretation","version":1,"schema_relations":[{"key":"R","arity":1}],"carrier_identity":{"kind":"whiel_framework_ii_finite_carrier","version":1,"carrier_keys":["data:0"]},"instance_identity":{"kind":"whiel_source_instance","version":1,"relations":[{"key":"R","arity":1,"rows":[["data:0"]]}]}},"axioms_hold":true,"conjecture_holds":false,"validated_refutation":true});
            let source = artifact(prepared, id, ReplayArtifactKind::Model);
            let witness = artifact(prepared, id + 1, ReplayArtifactKind::Witness);
            let validation_digest = canonical_value_sha256(&validation);
            let terminal = terminal_variant(
                prepared,
                attempt,
                json!({"kind":"refuted_model","validation_digest":validation_digest}),
                vec![source.clone(), witness.clone()],
            );
            let fields = json!({"domain":"whiel-framework-ii-validated-finite-refutation-v4","request_digest":prepared.control_request_digest,"job_id":fixed.job_id,"semantic_vc_digest":fixed.obligation_digest,"fixed_ambient_job":fixed,"attempt":attempt,"terminal_artifact":artifact(prepared,id+2,ReplayArtifactKind::RuntimeTrace),"terminal_result_digest":terminal["terminal_result_digest"],"source_artifact":source,"validation_identity":validation,"validation_digest":validation_digest,"validation_artifact":witness});
            (fields, terminal)
        } else {
            use std::sync::Arc;
            let invocation = SolverInvocationIdentity::from_parts(
                Arc::from("vampire"),
                Arc::from("version"),
                Arc::from("/fixture/vampire"),
                Arc::from(h('a')),
                Arc::from("platform"),
                Arc::from("architecture"),
                vec![Arc::from("--safe")],
            )
            .unwrap();
            let profile = LeancheckCertificationProfile::new(
                ProofSearchProfile::Direct,
                "profile-v1",
                invocation.clone(),
                None,
                h('b'),
                h('c'),
                h('d'),
                h('e'),
                h('f'),
            )
            .unwrap();
            let invocation_json = json!({"tool":invocation.tool(),"version":invocation.version(),"resolved_path":invocation.resolved_path(),"binary_digest":invocation.binary_digest(),"platform":invocation.platform(),"architecture":invocation.architecture(),"arguments":invocation.arguments().iter().map(|a|a.as_ref()).collect::<Vec<_>>(),"identity_digest":invocation.identity_digest()});
            let profile_json = json!({"profile":"direct","profile_version":profile.profile_version(),"leancheck_invocation":invocation_json,"permitted_cadical":null,"vamplean_digest":profile.vamplean_digest(),"generator_digest":profile.generator_digest(),"output_contract_digest":profile.output_contract_digest(),"transformer_digest":profile.transformer_digest(),"lean_bridge_digest":profile.lean_bridge_digest(),"profile_digest":profile.profile_digest()});
            let proof = artifact(prepared, id, ReplayArtifactKind::Proof);
            let empty = artifact(prepared, id + 1, ReplayArtifactKind::EmptyInstanceCheck);
            let terminal = terminal_variant(
                prepared,
                attempt,
                json!({"kind":"proved","proof_strategy":"direct","empty_check_digest":h('a')}),
                vec![proof.clone(), empty.clone()],
            );
            let fields = json!({"domain":"whiel-framework-ii-runtime-proof-receipt-v3","task_digest":h('c'),"catalog_digest":prepared.catalog_digest,"artifact_backend_digest":canonical_value_sha256(&json!({"domain":"whiel-artifact-backend-v1","task_digest":h('c'),"backend":fixed.query_artifact.backend})),"semantic_version":1,"encoding_version":1,"framework_ii_context_digest":fixed.obligation_digest,"request_digest":prepared.control_request_digest,"job_id":fixed.job_id,"semantic_vc_digest":fixed.obligation_digest,"query_digest":h('f'),"query_bytes":42,"attempt":attempt,"terminal_result_digest":terminal["terminal_result_digest"],"empty_check_digest":h('a'),"winner":"direct","runtime_invocation":invocation_json,"certification_profile":profile_json,"fixed_ambient_job":fixed,"query_artifact":fixed.query_artifact,"proof_artifact":proof,"terminal_artifact":artifact(prepared,id+2,ReplayArtifactKind::RuntimeTrace),"empty_check_artifact":empty});
            (fields, terminal)
        };
        decode(
            json!({"route":route,"original_digest":canonical_value_sha256(&fields),"fields":fields,"terminal":terminal}),
        )
    }
    #[test]
    fn runtime_protected_and_refutation_visitors_preserve_their_complete_semantics() {
        let old_prepared = prepared(2, '0', 1);
        let live_prepared = prepared(19, '1', 90);
        let mut maps = roots(&old_prepared, &live_prepared);
        compare_preparation(&old_prepared, &live_prepared, &mut maps).unwrap();
        // These are visitor fixtures. The independent native owner verifier is
        // tested in production.rs and remains a required caller precondition.
        for (route, mutation) in [
            ("runtime_proof", "/fields/runtime_invocation/arguments/0"),
            ("protected", "/fields/theorem_name"),
            (
                "validated_refutation",
                "/fields/validation_identity/interpretation_identity/instance_identity/relations/0/rows/0/0",
            ),
        ] {
            let old = other_route(&old_prepared, true, route);
            let live = other_route(&live_prepared, false, route);
            let old_artifacts = vec![ReplayArtifactAssociation {
                role: ReplayArtifactRole::RouteReceipt {},
                artifact: artifact(&old_prepared, 31, ReplayArtifactKind::Witness),
            }];
            let live_artifacts = vec![ReplayArtifactAssociation {
                role: ReplayArtifactRole::RouteReceipt {},
                artifact: artifact(&live_prepared, 41, ReplayArtifactKind::Witness),
            }];
            compare_production(
                &old,
                &live,
                &old_artifacts,
                &live_artifacts,
                &mut maps.clone(),
            )
            .unwrap();
            let mut bad = serde_json::to_value(live).unwrap();
            *bad.pointer_mut(mutation).unwrap() = json!("different semantic value");
            let bad = decode(bad);
            assert!(
                compare_production(
                    &old,
                    &bad,
                    &old_artifacts,
                    &live_artifacts,
                    &mut maps.clone()
                )
                .is_err(),
                "{route}"
            );
        }
    }
}
