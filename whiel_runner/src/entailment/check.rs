//! Source-level entailment checks and exact proof reuse.

use std::fmt;
use std::future::Future;
use std::sync::{Arc, LockResult, Mutex, MutexGuard};
use std::time::Duration;

use serde_json::json;

use crate::artifact::{ArtifactKind, ArtifactRef, ArtifactStore, AttemptId, ScopeTag};
use crate::encoding::{EncodingError, NativeEmptyCheck, NativeEmptyOutcome, SolverEncodingContext};
use crate::failure::{FailureKind, FailureOrigin, FailureReport, FailureScope};
use crate::runtime::{CancellationToken, SolverAdmission};
use crate::vampire::{
    CancelledVampireInvocation, FmbSize, VampireInvocationOutcome, VampireMode, VampireProof,
    VampireRequest, VampireRequestError, VampireResult, VampireSearchBudget, VampireWorkerCommand,
    run_vampire,
};

use super::assembly::{Entailment, Sha256};
use super::model::{DecodedInstance, EmptyInstanceError};

// ------------------------------------------------------------
// Attempt Scope
// ------------------------------------------------------------

/// One unique execution scope for an immutable entailment.
#[derive(Clone, Debug)]
pub struct EntailmentAttemptScope {
    entailment_identity: Arc<str>,
    attempt_id: AttemptId,
    query_artifact: ArtifactRef,
    artifacts: ArtifactStore,
}

impl EntailmentAttemptScope {
    pub fn entailment_identity(&self) -> &str {
        &self.entailment_identity
    }

    pub fn attempt_id(&self) -> AttemptId {
        self.attempt_id
    }

    pub fn artifacts(&self) -> &ArtifactStore {
        &self.artifacts
    }

    pub fn query_artifact(&self) -> ArtifactRef {
        self.query_artifact
    }

    pub fn provenance(&self) -> Vec<ScopeTag> {
        self.artifacts.scope_tags()
    }
}

impl ArtifactStore {
    /// Allocate one attempt before any solver or empty-check launch.
    ///
    /// The id comes from the store's monotone allocator in call order, and
    /// call order is not check order: a fixed-ambient sweep dispatches its
    /// launches concurrently, so the ids of one sweep are handed out as the
    /// launches reach this point and a rerun of the same fixture may
    /// permute them. An `AttemptId` is therefore a within-run handle — an
    /// artifact scope, the key a retained countermodel is addressed by
    /// while the run is live — and never a reproducible name for a check.
    /// The reproducible name is the controller's ledger row ordinal (see
    /// `framework2::ledger`).
    pub fn begin_entailment_attempt(
        &self,
        entailment: &Entailment,
    ) -> Result<EntailmentAttemptScope, FailureReport> {
        if self.task_identity() != entailment.task_identity()
            || self.backend_id() != entailment.query_artifact().backend_id()
        {
            return Err(FailureReport::encoding_preparation(
                FailureKind::InfrastructureFailure,
                FailureScope::RunGlobal,
                "entailment attempt belongs to another run backend",
            ));
        }
        let attempt_id = self.next_attempt_id()?;
        let artifacts = self.scoped(ScopeTag::Attempt(attempt_id));
        let query_artifact = entailment.query_artifact();
        Ok(EntailmentAttemptScope {
            entailment_identity: entailment.identity_arc(),
            attempt_id,
            query_artifact,
            artifacts,
        })
    }
}

// ------------------------------------------------------------
// Logical Results
// ------------------------------------------------------------

/// Durable evidence from the native empty-instance side check.
#[derive(Clone, Debug)]
pub struct EmptyCheckEvidence {
    entailment_identity: Arc<str>,
    artifact: ArtifactRef,
    evidence_digest: Arc<str>,
    elapsed: Duration,
}

impl EmptyCheckEvidence {
    pub fn entailment_identity(&self) -> &str {
        &self.entailment_identity
    }

    pub fn artifact(&self) -> ArtifactRef {
        self.artifact
    }

    /// SHA-256 of the exact payload committed to the evidence artifact.
    pub fn evidence_digest(&self) -> &str {
        &self.evidence_digest
    }

    pub fn elapsed(&self) -> Duration {
        self.elapsed
    }
}

/// Shared successful resolution of one exact retained model.
#[doc(hidden)]
#[derive(Clone, Debug)]
pub struct DecodedModelCache(Arc<Mutex<Option<DecodedInstance>>>);

impl DecodedModelCache {
    fn new() -> Self {
        Self(Arc::new(Mutex::new(None)))
    }

    pub(crate) fn lock(&self) -> LockResult<MutexGuard<'_, Option<DecodedInstance>>> {
        self.0.lock()
    }
}

/// One untrusted counterexample to the checked entailment.
#[derive(Clone, Debug)]
pub enum EntailmentCounterexample {
    Model {
        entailment_identity: Arc<str>,
        context: SolverEncodingContext,
        model: crate::vampire::VampireModel,
        decoded: DecodedModelCache,
    },
    Empty {
        entailment_identity: Arc<str>,
        input: DecodedInstance,
        evidence: ArtifactRef,
    },
}

impl EntailmentCounterexample {
    #[cfg(test)]
    pub(crate) fn model_for_test(
        context: SolverEncodingContext,
        model: crate::vampire::VampireModel,
    ) -> Self {
        Self::Model {
            entailment_identity: Arc::from(model.problem_identity()),
            context,
            model,
            decoded: DecodedModelCache::new(),
        }
    }

    #[cfg(test)]
    pub(crate) fn poison_decoded_model_cache(&self) {
        let Self::Model { decoded, .. } = self else {
            panic!("only a model counterexample has a decoded-model cache");
        };
        let cache = decoded.clone();
        assert!(
            std::thread::spawn(move || {
                let _guard = cache.0.lock().expect("fresh decoded-model cache");
                panic!("intentional decoded-model cache poison");
            })
            .join()
            .is_err()
        );
    }

    pub fn entailment_identity(&self) -> &str {
        match self {
            Self::Model {
                entailment_identity,
                ..
            }
            | Self::Empty {
                entailment_identity,
                ..
            } => entailment_identity,
        }
    }

    pub fn model(&self) -> Option<&crate::vampire::VampireModel> {
        match self {
            Self::Model { model, .. } => Some(model),
            Self::Empty { .. } => None,
        }
    }

    pub fn empty_input(&self) -> Option<&DecodedInstance> {
        match self {
            Self::Empty { input, .. } => Some(input),
            Self::Model { .. } => None,
        }
    }

    pub(crate) fn empty_evidence(&self) -> Option<ArtifactRef> {
        match self {
            Self::Empty { evidence, .. } => Some(*evidence),
            Self::Model { .. } => None,
        }
    }

    pub(crate) fn context(&self) -> Option<&SolverEncodingContext> {
        match self {
            Self::Model { context, .. } => Some(context),
            Self::Empty { .. } => None,
        }
    }

    pub(crate) fn decoded_model(&self) -> Option<&DecodedModelCache> {
        match self {
            Self::Model { decoded, .. } => Some(decoded),
            Self::Empty { .. } => None,
        }
    }
}

/// The logical or nonlogical result of one complete check.
#[derive(Clone, Debug)]
pub enum EntailmentCheckResult {
    Proved {
        proof: VampireProof,
        empty_evidence: EmptyCheckEvidence,
    },
    Refuted(EntailmentCounterexample),
    TimedOut {
        next_fmb_start_size: Option<FmbSize>,
        peer_failure: Option<FailureReport>,
    },
    Failure {
        report: FailureReport,
        next_fmb_start_size: Option<FmbSize>,
    },
}

/// Cancellation remains control flow outside a logical result.
#[derive(Clone, Debug)]
pub enum CancelledEntailmentCheck {
    Vampire(CancelledVampireInvocation),
    EmptyCheck { retained_proof: VampireProof },
}

/// Complete invocation outcome, including outer runtime control.
#[derive(Clone, Debug)]
pub enum EntailmentInvocationOutcome {
    Result(EntailmentCheckResult),
    Cancelled(CancelledEntailmentCheck),
    RunFailure(FailureReport),
}

/// Maintenance-facing provenance for one complete check invocation.
///
/// Attempt allocation can fail before an identity exists. A completed attempt
/// has one compact terminal artifact when the caller selects the detailed API.
#[derive(Clone, Debug)]
pub struct EntailmentCheckReport {
    attempt_id: Option<AttemptId>,
    terminal_artifact: Option<ArtifactRef>,
    terminal_result_digest: Option<Arc<str>>,
    outcome: EntailmentInvocationOutcome,
}

/// F2-specific terminal material resolved after raw Vampire work completes.
pub(crate) struct SpecializedEntailmentTerminal<T> {
    class: &'static str,
    references: Vec<ArtifactRef>,
    detail: serde_json::Value,
    outcome: T,
}

impl<T> SpecializedEntailmentTerminal<T> {
    pub(crate) fn new(
        class: &'static str,
        references: Vec<ArtifactRef>,
        detail: serde_json::Value,
        outcome: T,
    ) -> Result<Self, FailureReport> {
        if !matches!(
            class,
            "proved" | "refuted" | "timed_out" | "failure" | "canceled" | "inconclusive"
        ) {
            return Err(FailureReport::encoding_preparation(
                FailureKind::InfrastructureFailure,
                FailureScope::RunGlobal,
                "a specialized entailment resolver returned an unknown terminal class",
            ));
        }
        Ok(Self {
            class,
            references,
            detail,
            outcome,
        })
    }
}

/// Detailed result of a typed non-F1 closer on one preallocated attempt.
pub(crate) struct SpecializedEntailmentCheckReport<T> {
    replay_terminal: Option<Arc<ReplaySpecializedTerminalOwner>>,
    attempt_id: AttemptId,
    terminal_artifact: ArtifactRef,
    terminal_result_digest: Arc<str>,
    outcome: T,
}

impl<T> SpecializedEntailmentCheckReport<T> {
    pub(crate) fn replay_terminal(&self) -> Option<Arc<ReplaySpecializedTerminalOwner>> {
        self.replay_terminal.clone()
    }
    pub(crate) fn attempt_id(&self) -> AttemptId {
        self.attempt_id
    }

    pub(crate) fn terminal_artifact(&self) -> ArtifactRef {
        self.terminal_artifact
    }

    pub(crate) fn terminal_result_digest(&self) -> &str {
        &self.terminal_result_digest
    }

    pub(crate) fn outcome(&self) -> &T {
        &self.outcome
    }
}

impl EntailmentCheckReport {
    pub fn attempt_id(&self) -> Option<AttemptId> {
        self.attempt_id
    }

    pub fn terminal_artifact(&self) -> Option<ArtifactRef> {
        self.terminal_artifact
    }

    /// SHA-256 of the exact committed terminal-row payload.
    pub fn terminal_result_digest(&self) -> Option<&str> {
        self.terminal_result_digest.as_deref()
    }

    pub fn outcome(&self) -> &EntailmentInvocationOutcome {
        &self.outcome
    }

    pub fn into_outcome(self) -> EntailmentInvocationOutcome {
        self.outcome
    }
}

// ------------------------------------------------------------
// CheckEntailment
// ------------------------------------------------------------

/// Run or reuse Vampire, then check the empty-instance side case.
#[allow(clippy::too_many_arguments)]
pub async fn check_entailment<B>(
    entailment: &Entailment,
    artifacts: &ArtifactStore,
    search_budget: B,
    mode: VampireMode,
    command: VampireWorkerCommand,
    admission: SolverAdmission,
    cancellation: CancellationToken,
) -> EntailmentInvocationOutcome
where
    B: Into<VampireSearchBudget>,
{
    let attempt = match artifacts.begin_entailment_attempt(entailment) {
        Ok(attempt) => attempt,
        Err(report) => return failure_outcome(report, None),
    };
    run_entailment_attempt(
        entailment,
        &attempt,
        search_budget.into(),
        mode,
        command,
        admission,
        cancellation,
    )
    .await
}

/// Run one check and retain the exact attempt identity and terminal summary.
///
/// This API is additive. `check_entailment` keeps its original artifact and
/// failure behavior for callers which do not need maintenance-attempt history.
#[allow(clippy::too_many_arguments)]
pub async fn check_entailment_detailed<B>(
    entailment: &Entailment,
    artifacts: &ArtifactStore,
    search_budget: B,
    mode: VampireMode,
    command: VampireWorkerCommand,
    admission: SolverAdmission,
    cancellation: CancellationToken,
) -> EntailmentCheckReport
where
    B: Into<VampireSearchBudget>,
{
    let attempt = match artifacts.begin_entailment_attempt(entailment) {
        Ok(attempt) => attempt,
        Err(report) => {
            return EntailmentCheckReport {
                attempt_id: None,
                terminal_artifact: None,
                terminal_result_digest: None,
                outcome: failure_outcome(report, None),
            };
        }
    };
    check_entailment_attempt_detailed(
        entailment,
        &attempt,
        search_budget.into(),
        mode,
        command,
        admission,
        cancellation,
    )
    .await
}

/// Run a detailed check through a caller-preallocated attempt scope.
///
/// Concurrent schedulers use this form when they must publish a Pending audit
/// transition with the final `AttemptId` before launching solver work.
#[allow(clippy::too_many_arguments)]
pub async fn check_entailment_attempt_detailed<B>(
    entailment: &Entailment,
    attempt: &EntailmentAttemptScope,
    search_budget: B,
    mode: VampireMode,
    command: VampireWorkerCommand,
    admission: SolverAdmission,
    cancellation: CancellationToken,
) -> EntailmentCheckReport
where
    B: Into<VampireSearchBudget>,
{
    if attempt.entailment_identity() != entailment.identity()
        || attempt.query_artifact() != entailment.query_artifact()
        || attempt.artifacts().task_identity() != entailment.task_identity()
    {
        return EntailmentCheckReport {
            attempt_id: Some(attempt.attempt_id()),
            terminal_artifact: None,
            terminal_result_digest: None,
            outcome: EntailmentInvocationOutcome::RunFailure(FailureReport::encoding_preparation(
                FailureKind::InfrastructureFailure,
                FailureScope::RunGlobal,
                "preallocated attempt does not belong to the checked entailment",
            )),
        };
    }
    let outcome = run_entailment_attempt(
        entailment,
        attempt,
        search_budget.into(),
        mode,
        command,
        admission,
        cancellation,
    )
    .await;
    let mut terminal_artifact = None;
    let mut terminal_result_digest = None;
    let frontier = retained_frontier(&outcome);
    let outcome = Arc::new(outcome);
    let summary_entailment = entailment.clone();
    let summary_attempt = attempt.clone();
    let summary_outcome = Arc::clone(&outcome);
    let summary = terminal_summary(
        &summary_entailment,
        &summary_attempt,
        summary_outcome.as_ref(),
    );
    drop(summary_outcome);
    let summary_digest = Arc::<str>::from(sha256_bytes(&summary));
    let publication = attempt
        .artifacts()
        .publish_required_deferred_async(ArtifactKind::RuntimeTrace, move || Ok(summary))
        .await;
    let mut outcome = Arc::try_unwrap(outcome).unwrap_or_else(|_| {
        EntailmentInvocationOutcome::RunFailure(FailureReport::encoding_preparation(
            FailureKind::InfrastructureFailure,
            FailureScope::RunGlobal,
            "required-artifact builder retained its entailment outcome after joining",
        ))
    });
    match publication {
        Ok(reference) => {
            terminal_artifact = Some(reference);
            terminal_result_digest = Some(summary_digest);
        }
        Err(report) => outcome = failure_outcome(report, frontier),
    }
    EntailmentCheckReport {
        attempt_id: Some(attempt.attempt_id()),
        terminal_artifact,
        terminal_result_digest,
        outcome,
    }
}

/// Run or reuse Vampire under one exact attempt, then invoke a typed closer.
///
/// The fixed-ambient framework uses this seam for its snapshot-bound empty and finite-model
/// validation operations. The existing F1 entry point remains unchanged and
/// continues to use its source-instance closer. Terminal publication happens
/// only after `resolve` has completed and returned one fully classified value.
#[allow(clippy::too_many_arguments)]
pub(crate) async fn check_entailment_attempt_detailed_with_resolver<B, F, Fut, T>(
    entailment: &Entailment,
    attempt: &EntailmentAttemptScope,
    search_budget: B,
    mode: VampireMode,
    command: VampireWorkerCommand,
    admission: SolverAdmission,
    cancellation: CancellationToken,
    resolve: F,
) -> Result<SpecializedEntailmentCheckReport<T>, FailureReport>
where
    B: Into<VampireSearchBudget>,
    F: FnOnce(VampireInvocationOutcome) -> Fut,
    Fut: Future<Output = Result<SpecializedEntailmentTerminal<T>, FailureReport>>,
{
    if attempt.entailment_identity() != entailment.identity()
        || attempt.query_artifact() != entailment.query_artifact()
        || attempt.artifacts().task_identity() != entailment.task_identity()
    {
        return Err(FailureReport::encoding_preparation(
            FailureKind::InfrastructureFailure,
            FailureScope::RunGlobal,
            "preallocated specialized attempt does not belong to the checked entailment",
        ));
    }
    let vampire = run_or_reuse_vampire(
        entailment,
        attempt,
        search_budget.into(),
        mode,
        command,
        admission,
        cancellation.clone(),
    )
    .await;
    let terminal = resolve(vampire).await?;
    publish_specialized_entailment_terminal(entailment, attempt, &cancellation, terminal).await
}

/// Publish one specialized terminal row on an attempt whose classification
/// is already settled.
///
/// [`check_entailment_attempt_detailed_with_resolver`] ends here after its
/// resolver runs. The fixed-ambient framework also reaches it directly: when a semantic
/// dictionary proof entry's empty-instance recheck finds a counterexample,
/// the attempt is fully classified before any Vampire invocation, and it
/// still needs the exact terminal row every other resolved attempt
/// publishes.
pub(crate) async fn publish_specialized_entailment_terminal<T>(
    entailment: &Entailment,
    attempt: &EntailmentAttemptScope,
    cancellation: &CancellationToken,
    terminal: SpecializedEntailmentTerminal<T>,
) -> Result<SpecializedEntailmentCheckReport<T>, FailureReport> {
    if attempt.entailment_identity() != entailment.identity()
        || attempt.query_artifact() != entailment.query_artifact()
        || attempt.artifacts().task_identity() != entailment.task_identity()
    {
        return Err(FailureReport::encoding_preparation(
            FailureKind::InfrastructureFailure,
            FailureScope::RunGlobal,
            "preallocated specialized attempt does not belong to the checked entailment",
        ));
    }
    let summary = specialized_terminal_summary(entailment, attempt, &terminal);
    let terminal_result_digest = Arc::<str>::from(sha256_bytes(&summary));
    let replay_terminal = ReplaySpecializedTerminalOwner::capture(
        entailment,
        attempt,
        &terminal,
        &terminal_result_digest,
    )
    .ok()
    .map(Arc::new);
    if cancellation.should_stop() {
        return Err(closed_publication_failure(
            "specialized entailment terminal publication",
        ));
    }
    let terminal_artifact = attempt
        .artifacts()
        .publish_required_deferred_async(ArtifactKind::RuntimeTrace, move || Ok(summary))
        .await?;
    Ok(SpecializedEntailmentCheckReport {
        replay_terminal,
        attempt_id: attempt.attempt_id(),
        terminal_artifact,
        terminal_result_digest,
        outcome: terminal.outcome,
    })
}

fn specialized_terminal_summary<T>(
    entailment: &Entailment,
    attempt: &EntailmentAttemptScope,
    terminal: &SpecializedEntailmentTerminal<T>,
) -> Arc<[u8]> {
    let mut references = terminal.references.clone();
    references.push(entailment.query_artifact());
    references.sort_unstable_by_key(|reference| reference.local_id());
    references.dedup();
    Arc::from(
        json!({
            "kind": "entailment_attempt_terminal",
            "entailment_identity": entailment.identity(),
            "attempt_id": attempt.attempt_id().get(),
            "outcome": terminal.class,
            "references": references.iter().map(artifact_summary).collect::<Vec<_>>(),
            "detail": terminal.detail,
        })
        .to_string()
        .into_bytes(),
    )
}

fn sha256_bytes(bytes: &[u8]) -> String {
    let mut digest = Sha256::new();
    digest.update(bytes);
    digest.finalize_hex()
}

fn terminal_summary(
    entailment: &Entailment,
    attempt: &EntailmentAttemptScope,
    outcome: &EntailmentInvocationOutcome,
) -> Arc<[u8]> {
    let (class, references, detail) = match outcome {
        EntailmentInvocationOutcome::RunFailure(report) => (
            "failure",
            report.artifact_references().to_vec(),
            json!({ "failure": failure_summary(report) }),
        ),
        EntailmentInvocationOutcome::Cancelled(cancelled) => (
            "canceled",
            cancelled_artifact_references(cancelled),
            serde_json::Value::Null,
        ),
        EntailmentInvocationOutcome::Result(result) => match result {
            EntailmentCheckResult::Proved {
                proof,
                empty_evidence,
            } => (
                "proved",
                vec![
                    entailment.query_artifact(),
                    proof.output(),
                    empty_evidence.artifact(),
                ],
                json!({ "proof_strategy": proof.strategy().as_str() }),
            ),
            EntailmentCheckResult::Refuted(counterexample) => {
                let mut references = vec![entailment.query_artifact()];
                if let Some(model) = counterexample.model() {
                    references.push(model.output());
                }
                if let Some(evidence) = counterexample.empty_evidence() {
                    references.push(evidence);
                }
                ("refuted", references, serde_json::Value::Null)
            }
            EntailmentCheckResult::TimedOut {
                next_fmb_start_size,
                peer_failure,
            } => {
                let mut references = vec![entailment.query_artifact()];
                if let Some(report) = peer_failure {
                    references.extend_from_slice(report.artifact_references());
                }
                (
                    "timed_out",
                    references,
                    json!({
                        "next_fmb_start_size": next_fmb_start_size.map(FmbSize::get),
                        "peer_failure": peer_failure.as_ref().map(failure_summary),
                    }),
                )
            }
            EntailmentCheckResult::Failure {
                report,
                next_fmb_start_size,
            } => {
                let mut references = vec![entailment.query_artifact()];
                references.extend_from_slice(report.artifact_references());
                (
                    "failure",
                    references,
                    json!({
                        "next_fmb_start_size": next_fmb_start_size.map(FmbSize::get),
                        "failure": failure_summary(report),
                    }),
                )
            }
        },
    };
    let mut references = references;
    references.sort_unstable_by_key(|reference| reference.local_id());
    references.dedup();
    let payload = json!({
        "kind": "entailment_attempt_terminal",
        "entailment_identity": entailment.identity(),
        "attempt_id": attempt.attempt_id().get(),
        "outcome": class,
        "references": references.iter().map(artifact_summary).collect::<Vec<_>>(),
        "detail": detail,
    });
    Arc::from(payload.to_string().into_bytes())
}

fn cancelled_artifact_references(cancelled: &CancelledEntailmentCheck) -> Vec<ArtifactRef> {
    match cancelled {
        CancelledEntailmentCheck::Vampire(cancelled) => {
            let mut references = cancelled.artifact_references().to_vec();
            if let Some(report) = cancelled.peer_failure() {
                references.extend_from_slice(report.artifact_references());
            }
            references
        }
        CancelledEntailmentCheck::EmptyCheck { retained_proof } => vec![retained_proof.output()],
    }
}

fn retained_frontier(outcome: &EntailmentInvocationOutcome) -> Option<FmbSize> {
    match outcome {
        EntailmentInvocationOutcome::Result(EntailmentCheckResult::TimedOut {
            next_fmb_start_size,
            ..
        })
        | EntailmentInvocationOutcome::Result(EntailmentCheckResult::Failure {
            next_fmb_start_size,
            ..
        }) => *next_fmb_start_size,
        _ => None,
    }
}

fn artifact_summary(reference: &ArtifactRef) -> serde_json::Value {
    json!({
        "backend": reference.backend_id().to_string(),
        "local_id": reference.local_id(),
        "kind": format!("{:?}", reference.kind()),
    })
}

fn failure_summary(report: &FailureReport) -> serde_json::Value {
    json!({
        "origin": format!("{:?}", report.origin()),
        "kind": format!("{:?}", report.kind()),
        "retryable": report.retryable(),
        "scope": format!("{:?}", report.scope()),
        "detail": report.detail(),
    })
}

#[allow(clippy::too_many_arguments)]
async fn run_entailment_attempt(
    entailment: &Entailment,
    attempt: &EntailmentAttemptScope,
    search_budget: VampireSearchBudget,
    mode: VampireMode,
    command: VampireWorkerCommand,
    admission: SolverAdmission,
    cancellation: CancellationToken,
) -> EntailmentInvocationOutcome {
    let vampire = run_or_reuse_vampire(
        entailment,
        attempt,
        search_budget,
        mode,
        command,
        admission.clone(),
        cancellation.clone(),
    )
    .await;

    let vampire = match vampire {
        VampireInvocationOutcome::Result(result) => result,
        VampireInvocationOutcome::Cancelled(cancelled) => {
            return EntailmentInvocationOutcome::Cancelled(CancelledEntailmentCheck::Vampire(
                cancelled,
            ));
        }
        VampireInvocationOutcome::RunFailure(report) => {
            return EntailmentInvocationOutcome::RunFailure(report);
        }
    };

    match vampire {
        VampireResult::Proved(proof) => {
            finish_proof(entailment, attempt, proof, &admission, &cancellation).await
        }
        VampireResult::Refuted(model) => EntailmentInvocationOutcome::Result(
            EntailmentCheckResult::Refuted(EntailmentCounterexample::Model {
                entailment_identity: entailment.identity_arc(),
                context: entailment.context().clone(),
                model,
                decoded: DecodedModelCache::new(),
            }),
        ),
        VampireResult::TimedOut {
            next_fmb_start_size,
            peer_failure,
        } => EntailmentInvocationOutcome::Result(EntailmentCheckResult::TimedOut {
            next_fmb_start_size,
            peer_failure,
        }),
        VampireResult::Failure {
            report,
            next_fmb_start_size,
        } => EntailmentInvocationOutcome::Result(EntailmentCheckResult::Failure {
            report,
            next_fmb_start_size,
        }),
    }
}

#[allow(clippy::too_many_arguments)]
async fn run_or_reuse_vampire(
    entailment: &Entailment,
    attempt: &EntailmentAttemptScope,
    search_budget: VampireSearchBudget,
    mode: VampireMode,
    command: VampireWorkerCommand,
    admission: SolverAdmission,
    cancellation: CancellationToken,
) -> VampireInvocationOutcome {
    if let Some(stopped) = stopped_before_retention(&cancellation, "fixed-ambient Vampire dispatch")
    {
        return stopped;
    }
    let retained_proof = entailment.retained_proof(attempt.attempt_id());
    let retained_model = entailment.retained_model(attempt.attempt_id());
    match (retained_proof, retained_model) {
        (Some(_), Some(_)) => {
            return VampireInvocationOutcome::RunFailure(FailureReport::encoding_preparation(
                FailureKind::InfrastructureFailure,
                FailureScope::RunGlobal,
                "one entailment attempt retained conflicting proof and model outcomes",
            ));
        }
        (Some(proof), None) => {
            return VampireInvocationOutcome::Result(VampireResult::Proved(proof));
        }
        (None, Some(model)) => {
            return VampireInvocationOutcome::Result(VampireResult::Refuted(model));
        }
        (None, None) => {}
    }

    let problem = match entailment.vampire_problem(attempt.artifacts()) {
        Ok(problem) => problem,
        Err(report) => return raw_failure(report),
    };
    let request = match VampireRequest::from_preallocated(
        problem,
        mode,
        command,
        attempt.attempt_id(),
        attempt.artifacts().clone(),
        admission,
        search_budget,
    ) {
        Ok(request) => request,
        Err(error) => return request_failure(error),
    };
    match run_vampire(request, cancellation.clone()).await {
        VampireInvocationOutcome::Result(VampireResult::Proved(proof)) => {
            if let Some(stopped) =
                stopped_before_retention(&cancellation, "fixed-ambient retained proof publication")
            {
                return stopped;
            }
            match entailment.retain_proof(attempt.attempt_id(), proof) {
                Ok(proof) => VampireInvocationOutcome::Result(VampireResult::Proved(proof)),
                Err(EncodingError::Failure(report)) => raw_failure(report),
                Err(EncodingError::Cancelled) => {
                    unreachable!("in-memory proof retention cannot be cancelled")
                }
            }
        }
        VampireInvocationOutcome::Result(VampireResult::Refuted(model)) => {
            if let Some(stopped) =
                stopped_before_retention(&cancellation, "fixed-ambient retained model publication")
            {
                return stopped;
            }
            match entailment.retain_model(attempt.attempt_id(), model) {
                Ok(model) => VampireInvocationOutcome::Result(VampireResult::Refuted(model)),
                Err(EncodingError::Failure(report)) => raw_failure(report),
                Err(EncodingError::Cancelled) => {
                    unreachable!("in-memory model retention cannot be cancelled")
                }
            }
        }
        outcome => outcome,
    }
}

/// Classify a stop observed where an invocation would retain its result.
///
/// A run stop or an expired deadline closes the publication window, so the
/// boundary fails closed. A cooperative scope-local stop is ordinary control
/// flow: this invocation lost a race whose owner has already selected the
/// result it keeps, so it reports the same cancellation the owner would have
/// seen had the stop arrived one moment earlier, inside the worker race.
fn stopped_before_retention(
    cancellation: &CancellationToken,
    boundary: &str,
) -> Option<VampireInvocationOutcome> {
    // Sample the cancellation before the window, never after: a run stop is
    // published before the cancellation which accompanies it, so only this
    // order guarantees that a cancellation seen here carries its own stop.
    // Reading the window first could observe it still open and downgrade a
    // genuine run stop to a cooperative one.
    let cancelled = cancellation.is_cancelled();
    if cancellation.publication_closed() {
        return Some(raw_failure(closed_publication_failure(boundary)));
    }
    cancelled.then(|| {
        VampireInvocationOutcome::Cancelled(CancelledVampireInvocation::cooperative_stop())
    })
}

fn closed_publication_failure(boundary: &str) -> FailureReport {
    FailureReport::encoding_preparation(
        FailureKind::InfrastructureFailure,
        FailureScope::RunGlobal,
        format!("{boundary} stopped after run cancellation or deadline expiry"),
    )
}

async fn finish_proof(
    entailment: &Entailment,
    attempt: &EntailmentAttemptScope,
    proof: VampireProof,
    admission: &SolverAdmission,
    cancellation: &CancellationToken,
) -> EntailmentInvocationOutcome {
    let empty = entailment
        .context()
        .check_empty_counterexample(
            admission,
            attempt.artifacts(),
            entailment.identity_arc(),
            entailment.axiom_bodies(),
            entailment.goal_bodies(),
            cancellation,
        )
        .await;
    match empty {
        Ok(empty) => empty_result(entailment, proof, empty),
        Err(EncodingError::Cancelled) => {
            EntailmentInvocationOutcome::Cancelled(CancelledEntailmentCheck::EmptyCheck {
                retained_proof: proof,
            })
        }
        Err(EncodingError::Failure(report)) => failure_outcome(report, None),
    }
}

fn empty_result(
    entailment: &Entailment,
    proof: VampireProof,
    empty: NativeEmptyCheck,
) -> EntailmentInvocationOutcome {
    match empty.outcome {
        NativeEmptyOutcome::NoCounterexample => {
            EntailmentInvocationOutcome::Result(EntailmentCheckResult::Proved {
                proof,
                empty_evidence: EmptyCheckEvidence {
                    entailment_identity: entailment.identity_arc(),
                    artifact: empty.evidence,
                    evidence_digest: empty.evidence_digest,
                    elapsed: empty.elapsed,
                },
            })
        }
        NativeEmptyOutcome::Counterexample(assignment) => {
            let input = DecodedInstance::empty_active_domain(
                entailment.context().task(),
                assignment
                    .iter()
                    .map(|entry| (entry.relation_key.clone(), entry.value)),
            );
            match input {
                Ok(input) => EntailmentInvocationOutcome::Result(EntailmentCheckResult::Refuted(
                    EntailmentCounterexample::Empty {
                        entailment_identity: entailment.identity_arc(),
                        input,
                        evidence: empty.evidence,
                    },
                )),
                Err(error) => failure_outcome(empty_instance_failure(error), None),
            }
        }
    }
}

// ------------------------------------------------------------
// Failure Conversion
// ------------------------------------------------------------

fn raw_failure(report: FailureReport) -> VampireInvocationOutcome {
    if report.scope() == FailureScope::RunGlobal {
        VampireInvocationOutcome::RunFailure(report)
    } else {
        VampireInvocationOutcome::Result(VampireResult::Failure {
            report,
            next_fmb_start_size: None,
        })
    }
}

fn failure_outcome(
    report: FailureReport,
    next_fmb_start_size: Option<FmbSize>,
) -> EntailmentInvocationOutcome {
    if report.scope() == FailureScope::RunGlobal {
        EntailmentInvocationOutcome::RunFailure(report)
    } else {
        EntailmentInvocationOutcome::Result(EntailmentCheckResult::Failure {
            report,
            next_fmb_start_size,
        })
    }
}

fn request_failure(error: VampireRequestError) -> VampireInvocationOutcome {
    match error {
        VampireRequestError::Artifact(report) => raw_failure(report),
        VampireRequestError::InsufficientCapacity {
            required,
            available,
        } => VampireInvocationOutcome::RunFailure(FailureReport::admission_authority(format!(
            "Vampire requires {required} slots but only {available} exist"
        ))),
        VampireRequestError::ZeroLocalLimit => raw_failure(FailureReport::encoding_preparation(
            FailureKind::MalformedResult,
            FailureScope::LaneLocal,
            "an entailment local limit must be positive",
        )),
        VampireRequestError::ZeroInitialLimit => raw_failure(FailureReport::encoding_preparation(
            FailureKind::MalformedResult,
            FailureScope::LaneLocal,
            "an entailment retry baseline must be positive",
        )),
        VampireRequestError::InitialLimitExceedsTotal { initial, total } => {
            raw_failure(FailureReport::encoding_preparation(
                FailureKind::MalformedResult,
                FailureScope::LaneLocal,
                format!("entailment retry baseline {initial:?} exceeds total allowance {total:?}"),
            ))
        }
        VampireRequestError::UnboundedProofCasc => {
            VampireInvocationOutcome::RunFailure(FailureReport::admission_authority(
                "a configured proof CASC share requires a finite entailment limit",
            ))
        }
        VampireRequestError::UnboundedSerialPair => {
            VampireInvocationOutcome::RunFailure(FailureReport::admission_authority(
                "a strict-serial proof/FMB entailment requires finite per-lane budgets",
            ))
        }
        VampireRequestError::UnrepresentableProofCascLimit { limit } => {
            VampireInvocationOutcome::RunFailure(FailureReport::admission_authority(format!(
                "entailment limit {limit:?} exceeds Vampire's safe exact CASC time-limit range",
            )))
        }
    }
}

fn empty_instance_failure(error: EmptyInstanceError) -> FailureReport {
    FailureReport::try_new(
        FailureOrigin::ModelDecoding,
        FailureKind::MalformedResult,
        false,
        FailureScope::LaneLocal,
        Some(format!(
            "empty-check worker returned an invalid instance: {error}"
        )),
        Vec::new(),
    )
    .expect("model decoding permits malformed results")
}

impl fmt::Display for EntailmentInvocationOutcome {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Result(_) => formatter.write_str("entailment result"),
            Self::Cancelled(_) => formatter.write_str("entailment cancelled"),
            Self::RunFailure(report) => write!(
                formatter,
                "entailment run failure: {}",
                report.detail().unwrap_or("unspecified")
            ),
        }
    }
}

// Typed immutable evidence retained by the existing terminal owner. It grants
// no old artifact capability and never exports a private failure detail.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct ReplaySpecializedTerminalProjection {
    pub(crate) entailment_identity: String,
    pub(crate) attempt_id: crate::framework2::replay_identity::PhysicalAttemptId,
    pub(crate) query_artifact: crate::framework2::ReplayArtifactIdentity,
    pub(crate) constructor_references: Vec<crate::framework2::ReplayArtifactIdentity>,
    pub(crate) references: Vec<crate::framework2::ReplayArtifactIdentity>,
    pub(crate) detail: ReplaySpecializedTerminalDetail,
    terminal_result_digest: crate::framework2::ReplaySha256,
}
impl ReplaySpecializedTerminalProjection {
    pub(crate) fn digest(&self) -> &str {
        &self.terminal_result_digest.0
    }
    pub(crate) fn with_replay_digest(&self, digest: crate::framework2::ReplaySha256) -> Self {
        let mut copy = self.clone();
        copy.terminal_result_digest = digest;
        copy
    }
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub(crate) enum ReplaySpecializedTerminalDetail {
    Proved {
        proof_strategy: ReplayProofStrategy,
        empty_check_digest: crate::framework2::ReplaySha256,
    },
    RefutedModel {
        validation_digest: crate::framework2::ReplaySha256,
    },
    RefutedEmpty {
        validation_digest: crate::framework2::ReplaySha256,
    },
    RefutedEmptyAfterProof {
        proof_strategy: ReplayProofStrategy,
        validation_digest: crate::framework2::ReplaySha256,
    },
    TimedOut {
        #[serde(deserialize_with = "replay_terminal_nullable")]
        next_fmb_start_size: Option<u64>,
        #[serde(deserialize_with = "replay_terminal_nullable")]
        peer_failure: Option<crate::framework2::ReplayPrivateFailure>,
    },
    Failure {
        #[serde(deserialize_with = "replay_terminal_nullable")]
        next_fmb_start_size: Option<u64>,
        failure: crate::framework2::ReplayPrivateFailure,
    },
    CancelledSolver {
        #[serde(deserialize_with = "replay_terminal_nullable")]
        next_fmb_start_size: Option<u64>,
        #[serde(deserialize_with = "replay_terminal_nullable")]
        peer_failure: Option<crate::framework2::ReplayPrivateFailure>,
        capture_warnings: Vec<String>,
    },
    CancelledRefutation {
        source: crate::framework2::ReplayArtifactIdentity,
    },
    CancelledEmpty {
        retained_proof: crate::framework2::ReplayArtifactIdentity,
    },
    UnvalidatedRefutation {
        source: crate::framework2::ReplayArtifactIdentity,
    },
}
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum ReplayProofStrategy {
    Direct,
    #[serde(rename = "casc_2025")]
    Casc2025,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ReplayTerminalError {
    UnsupportedSchema,
    SemanticRedaction,
    PrivateDetailMismatch,
    ConstructorDigestMismatch,
}

pub(crate) struct ReplaySpecializedTerminalOwner {
    projection: ReplaySpecializedTerminalProjection,
    private_detail: Option<String>,
}
impl fmt::Debug for ReplaySpecializedTerminalOwner {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ReplaySpecializedTerminalOwner")
            .field("digest", &self.projection.digest())
            .finish_non_exhaustive()
    }
}
fn replay_terminal_nullable<'de, D, T>(d: D) -> Result<Option<T>, D::Error>
where
    D: serde::Deserializer<'de>,
    T: serde::Deserialize<'de>,
{
    <Option<T> as serde::Deserialize>::deserialize(d)
}
fn replay_terminal_decode<T: serde::de::DeserializeOwned>(
    v: &serde_json::Value,
) -> Result<T, ReplayTerminalError> {
    serde_json::from_value(v.clone()).map_err(|_| ReplayTerminalError::UnsupportedSchema)
}
fn replay_terminal_sha(v: &str) -> Result<crate::framework2::ReplaySha256, ReplayTerminalError> {
    replay_terminal_decode(&json!(v))
}

#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct ReplayTerminalRawFailure {
    origin: crate::framework2::ReplayFailureOrigin,
    kind: crate::framework2::ReplayFailureKind,
    retryable: bool,
    scope: crate::framework2::ReplayFailureScope,
    #[serde(deserialize_with = "replay_terminal_nullable")]
    detail: Option<String>,
    artifacts: Vec<crate::framework2::ReplayArtifactIdentity>,
}
impl ReplayTerminalRawFailure {
    fn capture(
        self,
    ) -> Result<(crate::framework2::ReplayPrivateFailure, Option<String>), ReplayTerminalError>
    {
        if self
            .detail
            .as_ref()
            .is_some_and(|s| crate::framework2::Redaction::changes(s.as_bytes()))
        {
            return Err(ReplayTerminalError::SemanticRedaction);
        }
        let detail_digest = self
            .detail
            .as_ref()
            .map(|detail| {
                replay_terminal_sha(&crate::encoding::canonical_value_sha256(&json!(detail)))
            })
            .transpose()?;
        Ok((
            crate::framework2::ReplayPrivateFailure {
                origin: self.origin,
                kind: self.kind,
                retryable: self.retryable,
                scope: self.scope,
                detail_digest,
                artifacts: self.artifacts,
            },
            self.detail,
        ))
    }
}

impl ReplaySpecializedTerminalOwner {
    pub(crate) fn projection(&self) -> &ReplaySpecializedTerminalProjection {
        &self.projection
    }

    fn capture<T>(
        entailment: &Entailment,
        attempt: &EntailmentAttemptScope,
        terminal: &SpecializedEntailmentTerminal<T>,
        digest: &str,
    ) -> Result<Self, ReplayTerminalError> {
        // The raw bytes are private and transient. Scan before producing any
        // commitment, including a commitment to a withheld diagnostic.
        let raw = serde_json::to_vec(&terminal.detail)
            .map_err(|_| ReplayTerminalError::UnsupportedSchema)?;
        if crate::framework2::Redaction::changes(&raw) {
            return Err(ReplayTerminalError::SemanticRedaction);
        }
        let (detail, private_detail) =
            capture_replay_terminal_detail(terminal.class, &terminal.detail)?;
        let mut references = terminal.references.clone();
        references.push(entailment.query_artifact());
        references.sort_unstable_by_key(|reference| reference.local_id());
        references.dedup();
        let references = references
            .iter()
            .map(|r| {
                crate::framework2::ReplayArtifactIdentity::capture(*r)
                    .map_err(|_| ReplayTerminalError::UnsupportedSchema)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let owner = Self {
            projection: ReplaySpecializedTerminalProjection {
                entailment_identity: entailment.identity().to_owned(),
                attempt_id: crate::framework2::replay_identity::PhysicalAttemptId(
                    attempt.attempt_id().get(),
                ),
                query_artifact: crate::framework2::ReplayArtifactIdentity::capture(
                    entailment.query_artifact(),
                )
                .map_err(|_| ReplayTerminalError::UnsupportedSchema)?,
                constructor_references: terminal
                    .references
                    .iter()
                    .map(|r| {
                        crate::framework2::ReplayArtifactIdentity::capture(*r)
                            .map_err(|_| ReplayTerminalError::UnsupportedSchema)
                    })
                    .collect::<Result<_, _>>()?,
                references,
                detail,
                terminal_result_digest: replay_terminal_sha(digest)?,
            },
            private_detail,
        };
        owner.verify_replay_projection(&owner.projection)?;
        Ok(owner)
    }

    pub(crate) fn verify_replay_projection(
        &self,
        recorded: &ReplaySpecializedTerminalProjection,
    ) -> Result<(), ReplayTerminalError> {
        // Both constructor hashes are checked using the same private current
        // detail only after its recorded commitment matches exactly. Public
        // semantic correspondence is checked separately by the run owner.
        for projection in [&self.projection, recorded] {
            let mut references = projection.constructor_references.clone();
            references.push(projection.query_artifact.clone());
            references.sort_unstable_by_key(|r| r.local_id);
            references.dedup();
            if references != projection.references {
                return Err(ReplayTerminalError::ConstructorDigestMismatch);
            }
            let detail =
                replay_terminal_detail_value(&projection.detail, self.private_detail.as_deref())?;
            let value = json!({
                "kind": "entailment_attempt_terminal",
                "entailment_identity": projection.entailment_identity,
                "attempt_id": projection.attempt_id.0,
                "outcome": replay_terminal_class(&projection.detail),
                "references": projection.references,
                "detail": detail,
            });
            let bytes = value.to_string().into_bytes();
            if crate::framework2::Redaction::changes(&bytes) {
                return Err(ReplayTerminalError::SemanticRedaction);
            }
            if sha256_bytes(&bytes) != projection.digest() {
                return Err(ReplayTerminalError::ConstructorDigestMismatch);
            }
            if projection
                .references
                .windows(2)
                .any(|w| w[0].local_id >= w[1].local_id)
            {
                return Err(ReplayTerminalError::UnsupportedSchema);
            }
        }
        Ok(())
    }
}

fn capture_replay_terminal_detail(
    class: &str,
    value: &serde_json::Value,
) -> Result<(ReplaySpecializedTerminalDetail, Option<String>), ReplayTerminalError> {
    use ReplaySpecializedTerminalDetail as D;
    #[derive(serde::Deserialize)]
    #[serde(deny_unknown_fields)]
    struct Proved {
        proof_strategy: ReplayProofStrategy,
        empty_check_digest: crate::framework2::ReplaySha256,
    }
    #[derive(serde::Deserialize)]
    #[serde(deny_unknown_fields)]
    struct Refuted {
        validation_digest: crate::framework2::ReplaySha256,
    }
    #[derive(serde::Deserialize)]
    #[serde(deny_unknown_fields)]
    struct RefutedEmpty {
        validation_digest: crate::framework2::ReplaySha256,
        refutation_source: String,
    }
    #[derive(serde::Deserialize)]
    #[serde(deny_unknown_fields)]
    struct RefutedProof {
        proof_strategy: ReplayProofStrategy,
        validation_digest: crate::framework2::ReplaySha256,
        refutation_source: String,
    }
    #[derive(serde::Deserialize)]
    #[serde(deny_unknown_fields)]
    struct TimedOut {
        #[serde(deserialize_with = "replay_terminal_nullable")]
        next_fmb_start_size: Option<u64>,
        #[serde(deserialize_with = "replay_terminal_nullable")]
        peer_failure: Option<ReplayTerminalRawFailure>,
    }
    #[derive(serde::Deserialize)]
    #[serde(deny_unknown_fields)]
    struct Failed {
        #[serde(deserialize_with = "replay_terminal_nullable")]
        next_fmb_start_size: Option<u64>,
        failure: ReplayTerminalRawFailure,
    }
    #[derive(serde::Deserialize)]
    #[serde(deny_unknown_fields)]
    struct Cancelled {
        #[serde(deserialize_with = "replay_terminal_nullable")]
        next_fmb_start_size: Option<u64>,
        #[serde(deserialize_with = "replay_terminal_nullable")]
        peer_failure: Option<ReplayTerminalRawFailure>,
        capture_warnings: Vec<String>,
    }
    #[derive(serde::Deserialize)]
    #[serde(deny_unknown_fields)]
    struct CancelledRefutation {
        phase: String,
        source: crate::framework2::ReplayArtifactIdentity,
    }
    #[derive(serde::Deserialize)]
    #[serde(deny_unknown_fields)]
    struct CancelledEmpty {
        phase: String,
        retained_proof: crate::framework2::ReplayArtifactIdentity,
    }
    #[derive(serde::Deserialize)]
    #[serde(deny_unknown_fields)]
    struct Unvalidated {
        reason: String,
        source: crate::framework2::ReplayArtifactIdentity,
    }
    fn optional_failure(
        raw: Option<ReplayTerminalRawFailure>,
    ) -> Result<
        (
            Option<crate::framework2::ReplayPrivateFailure>,
            Option<String>,
        ),
        ReplayTerminalError,
    > {
        match raw {
            None => Ok((None, None)),
            Some(raw) => raw.capture().map(|(f, d)| (Some(f), d)),
        }
    }
    match class {
        "proved" => {
            let p: Proved = replay_terminal_decode(value)?;
            Ok((
                D::Proved {
                    proof_strategy: p.proof_strategy,
                    empty_check_digest: p.empty_check_digest,
                },
                None,
            ))
        }
        "refuted" if value.get("proof_strategy").is_some() => {
            let p: RefutedProof = replay_terminal_decode(value)?;
            if p.refutation_source != "empty_counterexample" {
                return Err(ReplayTerminalError::UnsupportedSchema);
            }
            Ok((
                D::RefutedEmptyAfterProof {
                    proof_strategy: p.proof_strategy,
                    validation_digest: p.validation_digest,
                },
                None,
            ))
        }
        "refuted" if value.get("refutation_source").is_some() => {
            let p: RefutedEmpty = replay_terminal_decode(value)?;
            if p.refutation_source != "empty_counterexample" {
                return Err(ReplayTerminalError::UnsupportedSchema);
            }
            Ok((
                D::RefutedEmpty {
                    validation_digest: p.validation_digest,
                },
                None,
            ))
        }
        "refuted" => {
            let p: Refuted = replay_terminal_decode(value)?;
            Ok((
                D::RefutedModel {
                    validation_digest: p.validation_digest,
                },
                None,
            ))
        }
        "timed_out" => {
            let p: TimedOut = replay_terminal_decode(value)?;
            let (f, d) = optional_failure(p.peer_failure)?;
            Ok((
                D::TimedOut {
                    next_fmb_start_size: p.next_fmb_start_size,
                    peer_failure: f,
                },
                d,
            ))
        }
        "failure" => {
            let p: Failed = replay_terminal_decode(value)?;
            let (f, d) = p.failure.capture()?;
            Ok((
                D::Failure {
                    next_fmb_start_size: p.next_fmb_start_size,
                    failure: f,
                },
                d,
            ))
        }
        "canceled" if value.get("capture_warnings").is_some() => {
            let p: Cancelled = replay_terminal_decode(value)?;
            let (f, d) = optional_failure(p.peer_failure)?;
            Ok((
                D::CancelledSolver {
                    next_fmb_start_size: p.next_fmb_start_size,
                    peer_failure: f,
                    capture_warnings: p.capture_warnings,
                },
                d,
            ))
        }
        "canceled" if value.get("source").is_some() => {
            let p: CancelledRefutation = replay_terminal_decode(value)?;
            if p.phase != "finite_refutation_validation" {
                return Err(ReplayTerminalError::UnsupportedSchema);
            }
            Ok((D::CancelledRefutation { source: p.source }, None))
        }
        "canceled" => {
            let p: CancelledEmpty = replay_terminal_decode(value)?;
            if p.phase != "empty_counterexample_check" {
                return Err(ReplayTerminalError::UnsupportedSchema);
            }
            Ok((
                D::CancelledEmpty {
                    retained_proof: p.retained_proof,
                },
                None,
            ))
        }
        "inconclusive" => {
            let p: Unvalidated = replay_terminal_decode(value)?;
            if p.reason != "unvalidated_refutation" {
                return Err(ReplayTerminalError::UnsupportedSchema);
            }
            Ok((D::UnvalidatedRefutation { source: p.source }, None))
        }
        _ => Err(ReplayTerminalError::UnsupportedSchema),
    }
}
fn replay_terminal_class(detail: &ReplaySpecializedTerminalDetail) -> &'static str {
    use ReplaySpecializedTerminalDetail as D;
    match detail {
        D::Proved { .. } => "proved",
        D::RefutedModel { .. } | D::RefutedEmpty { .. } | D::RefutedEmptyAfterProof { .. } => {
            "refuted"
        }
        D::TimedOut { .. } => "timed_out",
        D::Failure { .. } => "failure",
        D::CancelledSolver { .. } | D::CancelledRefutation { .. } | D::CancelledEmpty { .. } => {
            "canceled"
        }
        D::UnvalidatedRefutation { .. } => "inconclusive",
    }
}
fn replay_terminal_failure_value(
    failure: &crate::framework2::ReplayPrivateFailure,
    detail: Option<&str>,
) -> Result<serde_json::Value, ReplayTerminalError> {
    let commitment = detail.map(|d| crate::encoding::canonical_value_sha256(&json!(d)));
    if commitment.as_deref() != failure.detail_digest.as_ref().map(|d| d.0.as_str()) {
        return Err(ReplayTerminalError::PrivateDetailMismatch);
    }
    Ok(
        json!({"origin":failure.origin,"kind":failure.kind,"retryable":failure.retryable,"scope":failure.scope,"detail":detail,"artifacts":failure.artifacts}),
    )
}
fn replay_terminal_detail_value(
    value: &ReplaySpecializedTerminalDetail,
    private: Option<&str>,
) -> Result<serde_json::Value, ReplayTerminalError> {
    use ReplaySpecializedTerminalDetail as D;
    let frontier = match value {
        D::TimedOut {
            next_fmb_start_size,
            ..
        }
        | D::Failure {
            next_fmb_start_size,
            ..
        }
        | D::CancelledSolver {
            next_fmb_start_size,
            ..
        } => *next_fmb_start_size,
        _ => None,
    };
    if frontier == Some(0) {
        return Err(ReplayTerminalError::UnsupportedSchema);
    }
    let value = match value {
        D::Proved {
            proof_strategy,
            empty_check_digest,
        } => json!({"proof_strategy":proof_strategy,"empty_check_digest":empty_check_digest}),
        D::RefutedModel { validation_digest } => json!({"validation_digest":validation_digest}),
        D::RefutedEmpty { validation_digest } => {
            json!({"validation_digest":validation_digest,"refutation_source":"empty_counterexample"})
        }
        D::RefutedEmptyAfterProof {
            proof_strategy,
            validation_digest,
        } => {
            json!({"proof_strategy":proof_strategy,"validation_digest":validation_digest,"refutation_source":"empty_counterexample"})
        }
        D::TimedOut {
            next_fmb_start_size,
            peer_failure,
        } => {
            json!({"next_fmb_start_size":next_fmb_start_size,"peer_failure":peer_failure.as_ref().map(|f|replay_terminal_failure_value(f,private)).transpose()?})
        }
        D::Failure {
            next_fmb_start_size,
            failure,
        } => {
            json!({"next_fmb_start_size":next_fmb_start_size,"failure":replay_terminal_failure_value(failure,private)?})
        }
        D::CancelledSolver {
            next_fmb_start_size,
            peer_failure,
            capture_warnings,
        } => {
            json!({"next_fmb_start_size":next_fmb_start_size,"peer_failure":peer_failure.as_ref().map(|f|replay_terminal_failure_value(f,private)).transpose()?,"capture_warnings":capture_warnings})
        }
        D::CancelledRefutation { source } => {
            json!({"phase":"finite_refutation_validation","source":source})
        }
        D::CancelledEmpty { retained_proof } => {
            json!({"phase":"empty_counterexample_check","retained_proof":retained_proof})
        }
        D::UnvalidatedRefutation { source } => {
            json!({"reason":"unvalidated_refutation","source":source})
        }
    };
    Ok(value)
}

#[cfg(test)]
mod retention_boundary_tests {
    use super::*;

    fn classify(cancellation: &CancellationToken) -> Option<VampireInvocationOutcome> {
        stopped_before_retention(cancellation, "boundary under test")
    }

    fn is_cooperative_stop(outcome: &Option<VampireInvocationOutcome>) -> bool {
        matches!(outcome, Some(VampireInvocationOutcome::Cancelled(_)))
    }

    fn is_closed_window(outcome: &Option<VampireInvocationOutcome>) -> bool {
        matches!(
            outcome,
            Some(VampireInvocationOutcome::RunFailure(report))
                if report.scope() == FailureScope::RunGlobal
        )
    }

    /*
      The boundary keeps the three stops apart, and a run stop dominates a
      cooperative one in either arrival order: only a scope which stopped
      itself, and nothing else, may discard its late result.
    */
    #[tokio::test]
    async fn every_stop_reaches_its_own_classification() {
        let running = CancellationToken::new();
        assert!(classify(&running).is_none());

        let cooperative = CancellationToken::new();
        cooperative.cancel_cooperatively();
        assert!(is_cooperative_stop(&classify(&cooperative)));

        let run_stop = CancellationToken::new();
        run_stop.cancel();
        assert!(is_closed_window(&classify(&run_stop)));

        let cooperative_then_run_stop = CancellationToken::new();
        cooperative_then_run_stop.cancel_cooperatively();
        cooperative_then_run_stop.cancel();
        assert!(is_closed_window(&classify(&cooperative_then_run_stop)));

        let run_stop_then_cooperative = CancellationToken::new();
        run_stop_then_cooperative.cancel();
        run_stop_then_cooperative.cancel_cooperatively();
        assert!(is_closed_window(&classify(&run_stop_then_cooperative)));

        let expired = CancellationToken::new();
        let deadline = tokio::time::Instant::now() + Duration::from_millis(10);
        assert!(expired.bind_absolute_deadline(deadline));
        tokio::time::sleep_until(deadline).await;
        assert!(is_closed_window(&classify(&expired)));
    }
}

#[cfg(test)]
mod replay_terminal_tests {
    use super::*;
    fn artifact(id: u64, kind: &str) -> crate::framework2::ReplayArtifactIdentity {
        serde_json::from_value(json!({"backend":"0".repeat(32),"local_id":id,"kind":kind})).unwrap()
    }
    fn hash(p: &ReplaySpecializedTerminalProjection, detail: Option<&str>) -> String {
        sha256_bytes(json!({"kind":"entailment_attempt_terminal","entailment_identity":p.entailment_identity,"attempt_id":p.attempt_id.0,"outcome":replay_terminal_class(&p.detail),"references":p.references,"detail":replay_terminal_detail_value(&p.detail,detail).unwrap()}).to_string().as_bytes())
    }
    fn owner() -> ReplaySpecializedTerminalOwner {
        let raw = json!({"origin":"VampireFiniteModelBuilding","kind":"ProcessFailure","retryable":true,"scope":"LaneLocal","detail":"private benign diagnostic","artifacts":[artifact(9,"FailureDiagnostic")]});
        let (failure, private_detail) = replay_terminal_decode::<ReplayTerminalRawFailure>(&raw)
            .unwrap()
            .capture()
            .unwrap();
        let mut projection = ReplaySpecializedTerminalProjection {
            entailment_identity: "semantic-entailment".into(),
            attempt_id: crate::framework2::replay_identity::PhysicalAttemptId(7),
            query_artifact: artifact(3, "Query"),
            constructor_references: vec![artifact(9, "FailureDiagnostic")],
            references: vec![artifact(3, "Query"), artifact(9, "FailureDiagnostic")],
            detail: ReplaySpecializedTerminalDetail::Failure {
                next_fmb_start_size: Some(4),
                failure,
            },
            terminal_result_digest: replay_terminal_sha(&"0".repeat(64)).unwrap(),
        };
        projection.terminal_result_digest =
            replay_terminal_sha(&hash(&projection, private_detail.as_deref())).unwrap();
        ReplaySpecializedTerminalOwner {
            projection,
            private_detail,
        }
    }
    #[test]
    fn replay_terminal_private_detail_is_committed_and_never_exported() {
        let owner = owner();
        owner.verify_replay_projection(owner.projection()).unwrap();
        assert!(
            !serde_json::to_string(owner.projection())
                .unwrap()
                .contains("private benign diagnostic")
        );
        assert!(!format!("{owner:?}").contains("private benign diagnostic"));
        let mut changed = owner.projection.clone();
        if let ReplaySpecializedTerminalDetail::Failure { failure, .. } = &mut changed.detail {
            failure.detail_digest = Some(replay_terminal_sha(&"1".repeat(64)).unwrap());
        }
        assert_eq!(
            owner.verify_replay_projection(&changed),
            Err(ReplayTerminalError::PrivateDetailMismatch)
        );
    }
    #[test]
    fn replay_terminal_changed_hidden_artifact_or_outer_hash_fails() {
        let owner = owner();
        let mut changed = owner.projection.clone();
        if let ReplaySpecializedTerminalDetail::Failure { failure, .. } = &mut changed.detail {
            failure.artifacts[0].local_id += 1;
        }
        assert_eq!(
            owner.verify_replay_projection(&changed),
            Err(ReplayTerminalError::ConstructorDigestMismatch)
        );
        let mut changed = owner.projection.clone();
        changed.terminal_result_digest = replay_terminal_sha(&"2".repeat(64)).unwrap();
        assert_eq!(
            owner.verify_replay_projection(&changed),
            Err(ReplayTerminalError::ConstructorDigestMismatch)
        );
    }
    #[test]
    fn replay_terminal_two_sided_constructor_accepts_only_exact_detail_commitment() {
        let owner = owner();
        let mut recorded = owner.projection.clone();
        recorded.attempt_id.0 = 17;
        recorded.query_artifact.local_id = 30;
        recorded.constructor_references[0].local_id = 2;
        if let ReplaySpecializedTerminalDetail::Failure { failure, .. } = &mut recorded.detail {
            failure.artifacts[0].local_id = 2;
        }
        recorded.references = vec![
            recorded.constructor_references[0].clone(),
            recorded.query_artifact.clone(),
        ];
        recorded.terminal_result_digest =
            replay_terminal_sha(&hash(&recorded, owner.private_detail.as_deref())).unwrap();
        owner.verify_replay_projection(&recorded).unwrap();
        recorded
            .constructor_references
            .push(recorded.query_artifact.clone());
        // Constructor input multiplicity is preserved for graph comparison;
        // native sort/dedup correctly leaves the original hash unchanged.
        owner.verify_replay_projection(&recorded).unwrap();
        recorded.references.reverse();
        assert!(owner.verify_replay_projection(&recorded).is_err());
    }
    #[test]
    fn replay_terminal_secret_unknown_field_and_zero_frontier_are_rejected() {
        let raw = json!({"origin":"VampireFiniteModelBuilding","kind":"ProcessFailure","retryable":true,"scope":"LaneLocal","detail":"Authorization: Bearer sk-secret-token","artifacts":[]});
        assert_eq!(
            replay_terminal_decode::<ReplayTerminalRawFailure>(&raw)
                .unwrap()
                .capture()
                .unwrap_err(),
            ReplayTerminalError::SemanticRedaction
        );
        let owner = owner();
        let mut wire = serde_json::to_value(owner.projection()).unwrap();
        wire["detail"]["ignored"] = json!(true);
        assert!(serde_json::from_value::<ReplaySpecializedTerminalProjection>(wire).is_err());
        let mut bad = owner.projection.clone();
        if let ReplaySpecializedTerminalDetail::Failure {
            next_fmb_start_size,
            ..
        } = &mut bad.detail
        {
            *next_fmb_start_size = Some(0);
        }
        assert_eq!(
            owner.verify_replay_projection(&bad),
            Err(ReplayTerminalError::UnsupportedSchema)
        );
    }
}
