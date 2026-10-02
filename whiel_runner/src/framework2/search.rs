//! Persistent pre-certificate AgentHoudini search orchestration.
//!
//! This module deliberately stops after fixed-ambient stabilization. It owns
//! no termination check, frozen validity evidence, validity certificate, or
//! complete public AgentHoudini entry point.

use std::collections::BTreeMap;
use std::future::Future;
use std::panic::{AssertUnwindSafe, catch_unwind, resume_unwind};
use std::sync::{Arc, Mutex};
use std::task::Poll;
use std::time::Duration;

use tokio::time::Instant;

use crate::artifact::{
    ArtifactBackendDiagnostics, ArtifactKind, ArtifactRef, ArtifactStore, BackendId, Retention,
    ScopeTag,
};
use crate::failure::{FailureKind, FailureOrigin, FailureReport, FailureScope};
use crate::runtime::{
    CancellationToken, RuntimeResourcePolicy, SolverAdmission, SolverAdmissionClass,
};
use crate::task::{SynthesisTask, TaskIdentity};

use super::admission::FrameworkIIAdmissionContext;
use super::agent::{
    Agent, AgentConsultationPolicy, AgentHoudiniAttempt, AgentProvider, AgentResponseValidator,
    HoudiniProposal,
};
use super::counterexample::{
    CounterexampleProvenance, CounterexampleRejection, CounterexampleValidation,
    FrameworkIICounterexampleError, FrozenCounterexampleRecord, ValidatedCounterexample,
};
use super::feedback::{
    AgentFeedbackError, AgentFeedbackPolicy, AgentSearchFeedback, PreCertificateAgentHoudiniState,
};
use super::freeze::{CoreFreezeError, FrameworkIITerminationProof, FrozenLeveledCore};
use super::host_limits::HostLimitDisagreement;
use super::ledger::{FrameworkIICheckRole, LevelAttemptLedger, LevelLedgerRow};
use super::production::{FrameworkIIQueryChecker, FrameworkIIRetryPolicy};
use super::proposal::{FrameworkIIEpochOutcome, run_framework_ii_proposal_epoch_under_control};
use super::publication::RunConfiguration;
use super::snapshot::{LeveledCandidateSnapshot, LeveledCoreHandle};
use super::solver::FrameworkIISolverContext;
use super::stabilization::{
    CurrentFrameworkIIRoot, FrameworkIIChecker, FrameworkIIRootCoverage, LeveledHoudiniState,
};
use super::tools::AgentToolPolicy;
use super::types::FrameworkIILevel;

// ------------------------------------------------------------
// Immutable Limits And Persistent Runtime
// ------------------------------------------------------------

/// Record identity of one run's published attempt history.
pub const ATTEMPT_HISTORY_KIND: &str = "whiel_framework_ii_attempt_history";
pub const ATTEMPT_HISTORY_VERSION: u64 = 1;
/// Artifact scope the attempt-history record is published under, so a
/// manifest reader tells it apart from the provider transcript's own frames.
pub const ATTEMPT_HISTORY_SCOPE: &str = "attempt-history";

/// Where the attempt-history publication reports itself to the run.
///
/// The search consumes itself on the way to its outcome, so the one place
/// that publishes this record cannot return anything to the caller. This
/// shared slot carries the published reference, or the refusal, back to the
/// run that owns the report: a record that was refused is named in the run's
/// own output instead of disappearing.
#[derive(Clone, Default)]
pub struct AttemptHistoryPublication(Arc<Mutex<Option<Result<ArtifactRef, String>>>>);

impl AttemptHistoryPublication {
    pub fn new() -> Self {
        Self::default()
    }

    /// The first outcome recorded for this run, if the record was attempted.
    pub fn outcome(&self) -> Option<Result<ArtifactRef, String>> {
        self.0.lock().ok().and_then(|slot| slot.clone())
    }

    fn record(&self, outcome: Result<ArtifactRef, String>) {
        if let Ok(mut slot) = self.0.lock()
            && slot.is_none()
        {
            *slot = Some(outcome);
        }
    }
}

/// One ledger row, projected to the same fields its own row digest is taken
/// over. This is the controller's record of the round, not a presentation:
/// nothing is summarized, truncated or re-ordered here.
fn attempt_history_row(ledger: &LevelAttemptLedger, row: &LevelLedgerRow) -> serde_json::Value {
    match row {
        LevelLedgerRow::Attempt(attempt) => {
            let request = attempt.request();
            serde_json::json!({
                "row": "attempt",
                "row_ordinal": attempt.row_ordinal(),
                "clause": request.clause().get(),
                "level": request.level().get(),
                "role": request.role().identity_name(),
                "request_digest": request.request_digest(),
                "partition_digest": request.snapshot().partition_digest(),
                "invalidated": ledger.is_invalidated(attempt.row_ordinal()),
                "outcome": attempt.outcome().identity_fields(),
                "previous_row_digest": attempt.previous_digest(),
                "row_digest": attempt.row_digest(),
            })
        }
        LevelLedgerRow::Invalidation(invalidation) => serde_json::json!({
            "row": "invalidation",
            "row_ordinal": row.row_ordinal(),
            "invalidated_attempt": invalidation.invalidated_attempt(),
            "target": invalidation.target().get(),
            "cause": invalidation.cause().map(crate::houdini::ClauseId::get),
            "reason": invalidation.reason().identity_name(),
            "previous_row_digest": invalidation.previous_digest(),
            "row_digest": invalidation.row_digest(),
        }),
    }
}

/// One transport attempt against the proposer, named by the same outcome
/// vocabulary the provider transcript publishes.
fn consultation_history_row(attempt: &AgentHoudiniAttempt) -> serde_json::Value {
    serde_json::json!({
        "consultation_digest": attempt.consultation_digest(),
        "request_digest": attempt.request_digest(),
        "validation_ordinal": attempt.validation_ordinal(),
        "transport_ordinal": attempt.transport_ordinal(),
        "response_digest": attempt.response_digest(),
        "outcome": super::transcript::TranscriptOutcome::from(attempt.outcome()),
        "same_request_retry": attempt.same_request_retry(),
    })
}

/// Default call-local limit on one `validate_counterexample` worker call.
///
/// This is a host option, not run policy: it bounds one Lean evaluation of a
/// submitted instance, and its expiry terminates the worker process serving
/// that call (the pool replaces and replays it) and becomes an ordinary
/// `timeout` counterexample rejection. The run's own cancellation and
/// absolute deadline stay in force underneath it.
pub const DEFAULT_COUNTEREXAMPLE_VALIDATION_LIMIT: Duration = Duration::from_secs(30);

/// Immutable run limits for the bounded pre-certificate search seam.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PreCertificateAgentHoudiniLimits {
    overall_limit: Duration,
    consultation_limit: Option<Duration>,
    /// Optional bound on the number of outer consultations one run may hold.
    ///
    /// `None` — the default — means the run deadline, the optional
    /// consultation deadline, and the run's cancellation token are the only
    /// guards on how long a search may go on, which is what the contract
    /// states (`houdini.tex` Section 4.7: no functional bound, only safety
    /// guards on wall time, file space, and memory). This is not a contract
    /// limit and not a host limit on the proposer; a host that sets one is
    /// making a resource statement, and exhausting it ends the run as the
    /// run-global resource fault
    /// [`crate::failure::FailureKind::IterationLimitExhausted`], never as a
    /// verdict on a proposal.
    iteration_limit: Option<u64>,
    counterexample_validation_limit: Duration,
}

impl PreCertificateAgentHoudiniLimits {
    /// Ordinary limits, with the built-in
    /// [`DEFAULT_COUNTEREXAMPLE_VALIDATION_LIMIT`].
    pub fn new(
        overall_limit: Duration,
        consultation_limit: Option<Duration>,
        iteration_limit: Option<u64>,
    ) -> Self {
        Self::new_with_counterexample_limit(
            overall_limit,
            consultation_limit,
            iteration_limit,
            DEFAULT_COUNTEREXAMPLE_VALIDATION_LIMIT,
        )
    }

    /// Limits with an explicit call-local counterexample-validation limit.
    pub fn new_with_counterexample_limit(
        overall_limit: Duration,
        consultation_limit: Option<Duration>,
        iteration_limit: Option<u64>,
        counterexample_validation_limit: Duration,
    ) -> Self {
        Self {
            overall_limit,
            consultation_limit,
            iteration_limit,
            counterexample_validation_limit,
        }
    }

    pub fn overall_limit(self) -> Duration {
        self.overall_limit
    }

    pub fn consultation_limit(self) -> Option<Duration> {
        self.consultation_limit
    }

    /// The run's optional consultation bound, absent by default.
    pub fn iteration_limit(self) -> Option<u64> {
        self.iteration_limit
    }

    pub fn counterexample_validation_limit(self) -> Duration {
        self.counterexample_validation_limit
    }
}

/// Live run-owned authorities which must survive a stabilization handoff.
///
/// The unique [`crate::ArtifactBackendOwner`] remains outside this async seam;
/// the retained store keeps the same backend live but cannot settle it.
/// Runtime capabilities are intentionally not observable after construction:
///
/// ```compile_fail
/// use whiel_runner::PreCertificateAgentHoudiniRuntime;
///
/// fn leak_artifacts<C>(runtime: &PreCertificateAgentHoudiniRuntime<C>) {
///     let _ = runtime.artifacts();
/// }
/// ```
pub struct PreCertificateAgentHoudiniRuntime<C> {
    admission: FrameworkIIAdmissionContext,
    solver: FrameworkIISolverContext,
    solver_admission: SolverAdmission,
    checker: C,
    artifacts: ArtifactStore,
    cancellation: CancellationToken,
    /// Always `false`: the agent path never enables
    /// `compress_core`, and unlike `tool_policy` this is not a constructor
    /// parameter, so there is no way for a caller to set it otherwise. [`PreCertificateAgentHoudiniSearch::new`] compares this
    /// fixed expectation against the paired [`LeveledHoudiniState`]'s actual
    /// `compress_core()`, which also catches the state having enabled it.
    compress_core: bool,
    /// The typed host option (Pass 7.5c) selecting which tools the provider
    /// may call. Drift-checked against the paired [`LeveledHoudiniState`]'s
    /// `tool_policy()` in [`PreCertificateAgentHoudiniSearch::new`].
    tool_policy: AgentToolPolicy,
    /// Where the attempt-history record reports its publication. A caller
    /// that wants the outcome in its own report binds its own slot with
    /// [`PreCertificateAgentHoudiniRuntime::reporting_attempt_history`];
    /// otherwise the record is published and nobody reads the receipt.
    attempt_history: AttemptHistoryPublication,
}

impl<C> PreCertificateAgentHoudiniRuntime<C> {
    /// `tool_policy` is the caller's independently sourced expectation for
    /// the typed host option baked into the paired [`LeveledHoudiniState`]
    /// (see [`bind_fixed_ambient_framework_ii`]). It must agree with the
    /// exact value that state was constructed with, both on first
    /// construction and on any later resume:
    /// [`PreCertificateAgentHoudiniSearch::new`] fails closed on
    /// disagreement, the same way it already does for task, scope, and
    /// encoding-context identity.
    ///
    /// [`bind_fixed_ambient_framework_ii`]: super::bootstrap::bind_fixed_ambient_framework_ii
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        admission: FrameworkIIAdmissionContext,
        solver: FrameworkIISolverContext,
        solver_admission: SolverAdmission,
        checker: C,
        artifacts: ArtifactStore,
        cancellation: CancellationToken,
        tool_policy: AgentToolPolicy,
    ) -> Self {
        Self {
            admission,
            solver,
            solver_admission,
            checker,
            artifacts,
            cancellation,
            compress_core: false,
            tool_policy,
            attempt_history: AttemptHistoryPublication::new(),
        }
    }

    /// Report this run's attempt-history publication into `slot`.
    pub fn reporting_attempt_history(mut self, slot: AttemptHistoryPublication) -> Self {
        self.attempt_history = slot;
        self
    }
}

// ------------------------------------------------------------
// Persistent Search State And Pre-Termination Handoff
// ------------------------------------------------------------

/// One persistent minimal AgentHoudini search before Step-7 termination work.
pub struct PreCertificateAgentHoudiniSearch<S, C> {
    task: Arc<SynthesisTask>,
    agent: Agent<S>,
    houdini: LeveledHoudiniState,
    feedback: PreCertificateAgentHoudiniState,
    runtime: PreCertificateAgentHoudiniRuntime<C>,
    limits: PreCertificateAgentHoudiniLimits,
    absolute_deadline: Instant,
    iteration: u64,
    last_consultation_failure: Option<FailureReport>,
    last_verification_failure: Option<FailureReport>,
}

impl<S, C: FrameworkIIChecker> PreCertificateAgentHoudiniSearch<S, C> {
    /// Synchronous construction is for process-free or stateless providers.
    /// A caller with an already-started endpoint must use
    /// `new_with_joined_cleanup` so setup failure joins that endpoint.
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        task: Arc<SynthesisTask>,
        agent: Agent<S>,
        houdini: LeveledHoudiniState,
        runtime: PreCertificateAgentHoudiniRuntime<C>,
        limits: PreCertificateAgentHoudiniLimits,
        absolute_deadline: Instant,
        feedback_policy: AgentFeedbackPolicy,
    ) -> Result<Self, FailureReport> {
        Self::new_recoverable(
            task,
            agent,
            houdini,
            runtime,
            limits,
            absolute_deadline,
            feedback_policy,
        )
        .map_err(|(report, _agent)| report)
    }

    /// Construct a run from a started endpoint, joining it before reporting any
    /// setup failure. A failed join cannot be hidden by the original error.
    #[allow(clippy::too_many_arguments)]
    pub async fn new_with_joined_cleanup(
        task: Arc<SynthesisTask>,
        agent: Agent<S>,
        houdini: LeveledHoudiniState,
        runtime: PreCertificateAgentHoudiniRuntime<C>,
        limits: PreCertificateAgentHoudiniLimits,
        absolute_deadline: Instant,
        feedback_policy: AgentFeedbackPolicy,
    ) -> Result<Self, FailureReport>
    where
        S: AgentProvider,
    {
        match Self::new_recoverable(
            task,
            agent,
            houdini,
            runtime,
            limits,
            absolute_deadline,
            feedback_policy,
        ) {
            Ok(search) => Ok(search),
            Err((report, mut agent)) => {
                agent
                    .shutdown(crate::proposer_api::wire::ShutdownReason::Failure)
                    .await;
                Err(agent.shutdown_failure().unwrap_or(report))
            }
        }
    }

    #[allow(clippy::too_many_arguments, clippy::result_large_err)]
    fn new_recoverable(
        task: Arc<SynthesisTask>,
        agent: Agent<S>,
        houdini: LeveledHoudiniState,
        runtime: PreCertificateAgentHoudiniRuntime<C>,
        limits: PreCertificateAgentHoudiniLimits,
        absolute_deadline: Instant,
        feedback_policy: AgentFeedbackPolicy,
    ) -> Result<Self, (FailureReport, Agent<S>)> {
        let preparation = (|| {
            if runtime.artifacts.task_identity() != task.identity()
                || runtime.admission.scope().task_identity() != task.identity()
                || runtime.solver.scope() != runtime.admission.scope()
                || houdini.catalog().scope() != runtime.admission.scope()
                || runtime.solver.encoding().context_id()
                    != runtime.admission.encoding().context_id()
                || !runtime
                    .admission
                    .encoding()
                    .matches_admission_authority(&runtime.solver_admission)
                || runtime.solver_admission.class() != SolverAdmissionClass::General
                || !runtime.checker.matches_search_runtime(
                    &runtime.solver,
                    &runtime.artifacts,
                    &runtime.solver_admission,
                    &runtime.cancellation,
                )
                || runtime.compress_core != houdini.compress_core()
                || &runtime.tool_policy != houdini.tool_policy()
            {
                return Err(search_state_failure(
                    "pre-certificate AgentHoudini authorities disagree at construction",
                ));
            }
            // The run's host limits have a single source, the feedback policy.
            // A checker that carries its own copy — the production checker
            // does, for countermodel retention — must carry that same copy, or
            // the standing presentation would state one limit while the
            // dictionary applied another. The controller state's level bound is
            // reconciled against the same policy inside the feedback session,
            // which fails closed on a contradiction.
            if let Some(disagreement) =
                checker_host_limit_disagreement(&runtime.checker, &feedback_policy)
            {
                return Err(search_state_failure(format!(
                    "pre-certificate AgentHoudini host limits disagree at construction: {disagreement}"
                )));
            }
            let remaining = absolute_deadline.saturating_duration_since(Instant::now());
            if remaining > limits.overall_limit {
                return Err(search_state_failure(
                    "pre-certificate AgentHoudini deadline exceeds its overall limit",
                ));
            }
            // Pass 7.5g: the run policy is bound to the artifact store's run
            // identity here, at the one point every entry into a run passes
            // through. The first construction persists it; an in-process resume
            // over the same store recomputes it from the same live authorities
            // and is refused if it disagrees, so later work never proceeds under
            // a policy the earlier work was not done under.
            let configuration = RunConfiguration::new(
                houdini.compress_core(),
                houdini.max_level().map(FrameworkIILevel::get),
                runtime.checker.retry_policy(),
                runtime.checker.retry_premise_role(),
                houdini.tool_policy(),
                runtime.artifacts.retention(),
            )
            .map_err(|error| {
                search_state_failure(format!(
                    "the run's own policy cannot be recorded exactly: {error}"
                ))
            })?;
            runtime
                .artifacts
                .bind_run_configuration(configuration.to_json())?;
            let feedback = PreCertificateAgentHoudiniState::new(
                Arc::clone(&task),
                &runtime.artifacts,
                &houdini,
                remaining,
                feedback_policy,
            )
            .map_err(feedback_failure)?;
            if !runtime
                .cancellation
                .bind_absolute_deadline(absolute_deadline)
            {
                return Err(search_state_failure(
                    "pre-certificate AgentHoudini cancellation already owns another deadline",
                ));
            }
            Ok(feedback)
        })();
        let feedback = match preparation {
            Ok(feedback) => feedback,
            Err(report) => return Err((report, agent)),
        };
        Ok(Self {
            task,
            agent,
            houdini,
            feedback,
            runtime,
            limits,
            absolute_deadline,
            iteration: 0,
            last_consultation_failure: None,
            last_verification_failure: None,
        })
    }

    fn remaining_time(&self) -> Duration {
        self.absolute_deadline
            .saturating_duration_since(Instant::now())
    }

    async fn join_operation_cleanup(&self) {
        self.runtime.solver_admission.wait_for_solver_idle().await;
        self.runtime.artifacts.wait_for_background_work().await;
    }

    /// Publish this run's attempt history as one immutable record.
    ///
    /// Only the `Valid` handoff exposes these rows in memory, and only while
    /// the process lives; a timed-out, exhausted, interrupted, failed or
    /// invalid run has no handoff at all. Publishing here — from the one
    /// place every terminal path passes through — is what makes the rounds a
    /// run actually performed readable afterwards, whichever way it settled.
    ///
    /// The record is provenance, so it follows `RuntimeTrace` retention: a
    /// run that keeps no payloads writes none. Publication goes through the
    /// store's own staging and atomic promotion under its size guards, so a
    /// refusal leaves no partial record; it is diagnostic and never
    /// reclassifies a settled result. A refusal is reported into the run's
    /// [`AttemptHistoryPublication`] rather than discarded, so a run whose
    /// history was refused says so instead of looking like a run that never
    /// published one.
    fn publish_attempt_history(&self, outcome: &str, report: Option<&FailureReport>) {
        if self.runtime.artifacts.retention() != Retention::All {
            return;
        }
        let ledger = self.houdini.attempts();
        let rows = ledger
            .rows()
            .iter()
            .map(|row| attempt_history_row(ledger, row))
            .collect::<Vec<_>>();
        let consultations = self
            .agent
            .attempt_history()
            .iter()
            .map(consultation_history_row)
            .collect::<Vec<_>>();
        let record = serde_json::json!({
            "kind": ATTEMPT_HISTORY_KIND,
            "version": ATTEMPT_HISTORY_VERSION,
            "outcome": outcome,
            "canonical_id": self.task.identity().canonical_id(),
            "run_digest": self.houdini.catalog().instance_digest(),
            "iteration": self.iteration,
            "proposal_revision": self.houdini.proposal_revision(),
            "termination_attempts_total": self.houdini.termination_attempts_total(),
            "max_level_stops_total": self.houdini.max_level_stops_total(),
            "consultations": consultations,
            "ledger": rows,
            "failure": report.map(|report| serde_json::json!({
                "origin": format!("{:?}", report.origin()),
                "kind": format!("{:?}", report.kind()),
                "scope": format!("{:?}", report.scope()),
                "retryable": report.retryable(),
                "detail": report.detail(),
            })),
        });
        let bytes = match serde_json::to_vec(&record) {
            Ok(bytes) => bytes,
            Err(error) => {
                self.runtime
                    .attempt_history
                    .record(Err(format!("serialize attempt history: {error}")));
                return;
            }
        };
        let published = self
            .runtime
            .artifacts
            .scoped(ScopeTag::named(ATTEMPT_HISTORY_SCOPE))
            .publish(ArtifactKind::RuntimeTrace, bytes.into_boxed_slice());
        self.runtime
            .attempt_history
            .record(published.map_err(|report| {
                format!(
                    "publish attempt history: {:?}: {}",
                    report.kind(),
                    report.detail().unwrap_or("publication refused")
                )
            }));
    }

    async fn finish_failure(&mut self, report: FailureReport) -> SearchCompletion
    where
        S: AgentProvider,
    {
        let reason = if self.runtime.cancellation.is_cancelled() {
            crate::proposer_api::wire::ShutdownReason::Cancelled
        } else {
            crate::proposer_api::wire::ShutdownReason::Failure
        };
        self.agent.shutdown(reason).await;
        self.join_operation_cleanup().await;
        let report = self.closed_run_report().unwrap_or(report);
        self.agent.record_replay_final(
            &self.houdini,
            &self.feedback,
            super::replay_correspondence::ReplayFinalOutcome::failure(&report),
        );
        self.publish_attempt_history("failure", Some(&report));
        SearchCompletion::Failure(report)
    }

    /// The epoch's termination check proved the postcondition on this Core:
    /// the search ends valid with the frozen Core.
    async fn finish_valid(
        &mut self,
        core: LeveledCoreHandle,
        termination: FrameworkIITerminationProof,
    ) -> SearchCompletion
    where
        S: AgentProvider,
    {
        self.agent
            .shutdown(crate::proposer_api::wire::ShutdownReason::Complete)
            .await;
        self.join_operation_cleanup().await;
        match self.closed_run_report() {
            Some(report) => {
                self.agent.record_replay_final(
                    &self.houdini,
                    &self.feedback,
                    super::replay_correspondence::ReplayFinalOutcome::failure(&report),
                );
                self.publish_attempt_history("failure", Some(&report));
                SearchCompletion::Failure(report)
            }
            None => {
                self.agent.record_replay_final(
                    &self.houdini,
                    &self.feedback,
                    super::replay_correspondence::ReplayFinalOutcome::valid(&termination),
                );
                self.publish_attempt_history("valid", None);
                SearchCompletion::Valid { core, termination }
            }
        }
    }

    /// Lean validated a submitted counterexample: the run ends invalid with
    /// the frozen record (agent report, "Search termination").
    async fn finish_invalid(&mut self, record: FrozenCounterexampleRecord) -> SearchCompletion
    where
        S: AgentProvider,
    {
        self.agent
            .shutdown(crate::proposer_api::wire::ShutdownReason::Complete)
            .await;
        self.join_operation_cleanup().await;
        match self.closed_run_report() {
            Some(report) => {
                self.agent.record_replay_final(
                    &self.houdini,
                    &self.feedback,
                    super::replay_correspondence::ReplayFinalOutcome::failure(&report),
                );
                self.publish_attempt_history("failure", Some(&report));
                SearchCompletion::Failure(report)
            }
            None => {
                self.agent.record_replay_final(
                    &self.houdini,
                    &self.feedback,
                    super::replay_correspondence::ReplayFinalOutcome::invalid(&record),
                );
                self.publish_attempt_history("invalid", None);
                SearchCompletion::Invalid(Box::new(record))
            }
        }
    }

    async fn publish_next_feedback(
        &mut self,
        latest: &AgentSearchFeedback,
    ) -> Result<(), FailureReport> {
        let remaining = self.remaining_time();
        let mut staged = self.feedback.clone();
        staged
            .build_next_feedback(&self.houdini, latest, remaining)
            .map_err(feedback_failure)?;
        tokio::task::yield_now().await;
        if let Some(report) = self.closed_run_report() {
            return Err(report);
        }
        self.feedback = staged;
        Ok(())
    }

    fn closed_run_report(&self) -> Option<FailureReport> {
        if let Some(report) = self.agent.shutdown_failure() {
            return Some(report);
        }
        if self
            .runtime
            .cancellation
            .cancelled_before(self.absolute_deadline)
        {
            Some(interrupted_report())
        } else if Instant::now() >= self.absolute_deadline {
            self.runtime
                .cancellation
                .cancel_for_deadline(self.absolute_deadline);
            Some(FailureReport::overall_timeout(self.limits.overall_limit))
        } else if self.runtime.cancellation.is_cancelled() {
            Some(interrupted_report())
        } else {
            None
        }
    }

    fn consultation_timeout_report(&self) -> FailureReport {
        let iterations_left = self
            .limits
            .iteration_limit
            .is_none_or(|limit| self.iteration < limit);
        let retryable = iterations_left && Instant::now() < self.absolute_deadline;
        FailureReport::try_new(
            FailureOrigin::AgentConsultation,
            FailureKind::ConsultationTimeout,
            retryable,
            FailureScope::LaneLocal,
            Some(format!(
                "AgentHoudini consultation {} exceeded its explicit local limit",
                self.iteration
            )),
            Vec::new(),
        )
        .expect("the standard consultation-timeout pair is valid")
    }

    /// The resource statement a host's optional consultation bound makes
    /// when it is exhausted: a run-global, non-retryable resource fault,
    /// never a verdict on a proposal. Reached only where the host set one.
    fn iteration_limit_report(&self, limit: u64) -> FailureReport {
        FailureReport::try_new(
            FailureOrigin::RunControl,
            FailureKind::IterationLimitExhausted,
            false,
            FailureScope::RunGlobal,
            Some(format!(
                "AgentHoudini exhausted the host's bound of {limit} outer consultations"
            )),
            Vec::new(),
        )
        .expect("the standard iteration-limit pair is valid")
    }
}

impl<S: AgentProvider, C: FrameworkIIChecker + FrameworkIIQueryChecker>
    PreCertificateAgentHoudiniSearch<S, C>
{
    /// Run bounded consultations until invalidity, operational failure, or the
    /// exact pre-termination stabilization handoff.
    pub async fn run(mut self) -> PreCertificateAgentHoudiniOutcome<S, C> {
        // The caught future borrows the search. Keep its provider outside that
        // future so a checker/engine panic cannot drop the only awaited cleanup
        // authority while an idle endpoint, descendant or capture is still live.
        match catch_future_unwind(self.run_inner()).await {
            Ok(SearchCompletion::Failure(report)) => {
                PreCertificateAgentHoudiniOutcome::Failure(report)
            }
            Ok(SearchCompletion::Invalid(record)) => {
                PreCertificateAgentHoudiniOutcome::Invalid(record)
            }
            Ok(SearchCompletion::Valid { core, termination }) => {
                PreCertificateAgentHoudiniOutcome::Valid(Box::new(
                    PreCertificateAgentHoudiniHandoff {
                        core,
                        termination,
                        frozen: None,
                        handed_out: false,
                        search: self,
                    },
                ))
            }
            Err(payload) => {
                if let Some(recorder) = self.agent.replay_recorder() {
                    recorder.final_owner(Err(super::ReplayCaptureError::OwnerInvariant));
                }
                self.runtime.cancellation.cancel();
                self.agent
                    .shutdown(crate::proposer_api::wire::ShutdownReason::Failure)
                    .await;
                self.join_operation_cleanup().await;
                resume_unwind(payload);
            }
        }
    }

    async fn run_inner(&mut self) -> SearchCompletion {
        loop {
            if let Some(report) = self.closed_run_report() {
                return self.finish_failure(report).await;
            }
            if let Some(limit) = self.limits.iteration_limit
                && self.iteration >= limit
            {
                let report = self.iteration_limit_report(limit);
                return self.finish_failure(report).await;
            }

            let remaining = self.remaining_time();
            let mut refreshed_feedback = self.feedback.clone();
            if let Err(report) = refreshed_feedback
                .refresh_current_feedback(&self.houdini, remaining)
                .map_err(feedback_failure)
            {
                return self.finish_failure(report).await;
            }
            tokio::task::yield_now().await;
            if let Some(report) = self.closed_run_report() {
                return self.finish_failure(report).await;
            }
            self.feedback = refreshed_feedback;
            self.iteration = match self.iteration.checked_add(1) {
                Some(iteration) => iteration,
                None => {
                    return self
                        .finish_failure(search_state_failure(
                            "AgentHoudini iteration accounting overflowed",
                        ))
                        .await;
                }
            };

            let consultation = self.run_consultation().await;
            match consultation {
                ConsultationRun::OverallTimedOut => {
                    let report = FailureReport::overall_timeout(self.limits.overall_limit);
                    return self.finish_failure(report).await;
                }
                ConsultationRun::Cancelled => {
                    return self.finish_failure(interrupted_report()).await;
                }
                _ => {}
            }
            if let Some(report) = self.closed_run_report() {
                if let ConsultationRun::Completed(proposal) = &consultation
                    && !self.agent.discard_completed_proposal(
                        self.feedback.feedback().consultation_digest(),
                        proposal,
                    )
                {
                    return self
                        .finish_failure(search_state_failure(
                            "a controller-discarded Agent result did not match the exact last attempt",
                        ))
                        .await;
                }
                return self.finish_failure(report).await;
            }
            match consultation {
                ConsultationRun::OverallTimedOut | ConsultationRun::Cancelled => unreachable!(),
                ConsultationRun::UnexpectedCancellation => {
                    return self
                        .finish_failure(search_state_failure(
                            "an AgentHoudini consultation stopped without controller cancellation",
                        ))
                        .await;
                }
                ConsultationRun::Failure(report) => {
                    return self.finish_failure(report).await;
                }
                ConsultationRun::LocalTimedOut => {
                    let report = self.consultation_timeout_report();
                    if let Err(report) = self.publish_consultation_failure(report).await {
                        return self.finish_failure(report).await;
                    }
                }
                ConsultationRun::Completed(HoudiniProposal::Failure(report)) => {
                    // A run-global consultation failure ends the run. A
                    // lane-local one is published to the proposer and the
                    // search holds the next consultation, which is what the
                    // contract's "the next consultation is held" means; a
                    // run-global one — a resource fault, the run's memory
                    // guards among them — is not recoverable that way, and
                    // publishing it and looping re-enters the same failure
                    // on the same state until the run deadline (Milestone
                    // 7.5 review, finding 7).
                    if report.scope() == FailureScope::RunGlobal {
                        return self.finish_failure(report).await;
                    }
                    if let Err(report) = self.publish_consultation_failure(report).await {
                        return self.finish_failure(report).await;
                    }
                }
                ConsultationRun::Completed(HoudiniProposal::CandidateCounterexample(proposal)) => {
                    // A counterexample submission never runs an epoch: it is
                    // validated in Lean and either ends the run invalid or
                    // becomes a `counterexample_rejected` event with no state
                    // change at all (agent report, Alg. Search).
                    match self.validate_counterexample(*proposal).await {
                        CounterexampleStep::Invalid(record) => {
                            return self.finish_invalid(*record).await;
                        }
                        CounterexampleStep::Finish(report) => {
                            return self.finish_failure(report).await;
                        }
                        CounterexampleStep::Continue(latest) => {
                            if let Err(report) = self.publish_next_feedback(&latest).await {
                                return self.finish_failure(report).await;
                            }
                        }
                    }
                }
                ConsultationRun::Completed(HoudiniProposal::CandidateClauses(proposal)) => {
                    let operation = run_framework_ii_proposal_epoch_under_control(
                        &mut self.houdini,
                        &mut self.runtime.checker,
                        *proposal,
                        &self.runtime.cancellation,
                    );
                    let outcome = await_overall_operation(
                        operation,
                        &self.runtime.cancellation,
                        self.absolute_deadline,
                    )
                    .await;
                    let result = match outcome {
                        OverallOperation::TimedOut => {
                            let report = FailureReport::overall_timeout(self.limits.overall_limit);
                            return self.finish_failure(report).await;
                        }
                        OverallOperation::Cancelled => {
                            return self.finish_failure(interrupted_report()).await;
                        }
                        OverallOperation::Completed(Err(error)) => {
                            return self
                                .finish_failure(search_state_failure(format!(
                                    "fixed-ambient proposal dispatch failed closed: {error}"
                                )))
                                .await;
                        }
                        OverallOperation::Completed(Ok(result)) => result,
                    };
                    // Record this round's submitted identities before
                    // building the next push, so its `last_round` reports
                    // each one's current outcome. A rolled-back epoch
                    // records none: it left the partition as it began, so
                    // it produced no outcome for its batch and the next
                    // push's `last_round` is empty for it, with the
                    // `failure` event saying what happened to the round.
                    self.feedback
                        .record_round_proposals(result.round_outcomes().iter().copied());
                    let latest = match result.into_outcome() {
                        FrameworkIIEpochOutcome::Proved { core, termination } => {
                            return self.finish_valid(core, termination).await;
                        }
                        FrameworkIIEpochOutcome::Failure(report) => {
                            self.last_verification_failure = Some(report.clone());
                            if report.scope() == FailureScope::RunGlobal {
                                return self.finish_failure(report).await;
                            }
                            match AgentSearchFeedback::failure(&self.houdini, report) {
                                Ok(latest) => latest,
                                Err(error) => {
                                    return self.finish_failure(feedback_failure(error)).await;
                                }
                            }
                        }
                        // The postcondition is still open: the epoch's
                        // termination check on its Core was refuted — the
                        // event names the checker attempt whose countermodel
                        // the `countermodel` tool serves — or was
                        // inconclusive with its reason.
                        FrameworkIIEpochOutcome::Refuted { attempt } => {
                            match AgentSearchFeedback::postcondition_open_refuted(
                                &self.houdini,
                                attempt,
                            ) {
                                Ok(latest) => latest,
                                Err(error) => {
                                    return self.finish_failure(feedback_failure(error)).await;
                                }
                            }
                        }
                        // The run's own cancellation stopped the epoch: the
                        // postcondition is not "still open", nothing was
                        // learned, and there is no next consultation.
                        FrameworkIIEpochOutcome::Cancelled => {
                            return self.finish_failure(interrupted_report()).await;
                        }
                        FrameworkIIEpochOutcome::Inconclusive { reason } => {
                            match AgentSearchFeedback::postcondition_open_inconclusive(
                                &self.houdini,
                                reason,
                            ) {
                                Ok(latest) => latest,
                                Err(error) => {
                                    return self.finish_failure(feedback_failure(error)).await;
                                }
                            }
                        }
                    };
                    if let Err(report) = self.publish_next_feedback(&latest).await {
                        return self.finish_failure(report).await;
                    }
                }
            }
            // A provider and every downstream boundary may complete
            // synchronously. Cooperatively yield between outer iterations
            // so sibling cancellation and deadline drivers can run;
            // the loop top rechecks both before starting another consultation.
            tokio::task::yield_now().await;
        }
    }

    /// Validate one submitted counterexample in Lean under a call-local
    /// timeout.
    ///
    /// The worker call runs against a fresh call-scoped cancellation token,
    /// raced by [`await_consultation_operation`] against that call-local
    /// limit, the run's own cancellation, and the run's absolute deadline —
    /// exactly the arbitration a consultation gets. Cancelling the
    /// call-scoped token terminates the worker process serving the call, so
    /// the pool retires it, replaces it, and replays its name-environment
    /// prefix on the next request; the expired call becomes an ordinary
    /// `timeout` rejection and the search continues.
    async fn validate_counterexample(
        &mut self,
        proposal: super::agent::AgentCounterexampleProposal,
    ) -> CounterexampleStep {
        let (input, binding) = proposal.into_parts();
        let call_cancellation = CancellationToken::new();
        let call = {
            let operation = self.runtime.solver.validate_counterexample(
                &input,
                &self.runtime.solver_admission,
                &call_cancellation,
            );
            await_consultation_operation(
                operation,
                &call_cancellation,
                &self.runtime.cancellation,
                self.absolute_deadline,
                Some(self.limits.counterexample_validation_limit),
            )
            .await
        };
        match classify_counterexample_call(call, self.limits.counterexample_validation_limit) {
            CounterexampleCall::Validated(validated) => {
                CounterexampleStep::Invalid(Box::new(FrozenCounterexampleRecord::freeze(
                    validated,
                    self.task.identity().clone(),
                    self.runtime.solver.scope().identity_sha256(),
                    CounterexampleProvenance::Consultation(Box::new(binding)),
                )))
            }
            CounterexampleCall::Rejected(rejection) => {
                match AgentSearchFeedback::counterexample_rejected(
                    &self.houdini,
                    rejection.code(),
                    rejection.reason(),
                ) {
                    Ok(latest) => CounterexampleStep::Continue(latest),
                    Err(error) => CounterexampleStep::Finish(feedback_failure(error)),
                }
            }
            CounterexampleCall::LaneFailure(report) => {
                self.last_verification_failure = Some(report.clone());
                match AgentSearchFeedback::failure(&self.houdini, report) {
                    Ok(latest) => CounterexampleStep::Continue(latest),
                    Err(error) => CounterexampleStep::Finish(feedback_failure(error)),
                }
            }
            CounterexampleCall::RunFailure(report) => {
                self.last_verification_failure = Some(report.clone());
                CounterexampleStep::Finish(report)
            }
            CounterexampleCall::OverallTimedOut => CounterexampleStep::Finish(
                FailureReport::overall_timeout(self.limits.overall_limit),
            ),
            CounterexampleCall::Interrupted => {
                CounterexampleStep::Finish(self.closed_run_report().unwrap_or_else(|| {
                    search_state_failure(
                        "counterexample validation reported cancellation without controller \
                         cancellation",
                    )
                }))
            }
        }
    }

    async fn run_consultation(&mut self) -> ConsultationRun {
        let consultation_cancellation = CancellationToken::new();
        let run_cancellation = self.runtime.cancellation.clone();
        let feedback = self.feedback.feedback().clone();
        let consultation_digest = feedback.consultation_digest().to_string();
        let query: &dyn FrameworkIIQueryChecker = &self.runtime.checker;
        let validator = AgentResponseValidator::new(
            &self.task,
            &self.houdini,
            &self.runtime.admission,
            &self.runtime.solver,
            &self.runtime.solver_admission,
            &self.feedback,
            Some(query),
        );
        let local_deadline = strictly_earlier_consultation_deadline(
            Instant::now(),
            self.limits.consultation_limit,
            self.absolute_deadline,
        );
        self.agent.set_request_deadline(local_deadline);
        let operation =
            self.agent
                .get_houdini_proposal(&feedback, &validator, &consultation_cancellation);
        match await_consultation_operation_until(
            operation,
            &consultation_cancellation,
            &run_cancellation,
            self.absolute_deadline,
            local_deadline,
        )
        .await
        {
            ConsultationOperation::Completed(Ok(proposal)) => ConsultationRun::Completed(proposal),
            ConsultationOperation::Completed(Err(_)) => {
                if run_cancellation.cancelled_before(self.absolute_deadline) {
                    ConsultationRun::Cancelled
                } else if Instant::now() >= self.absolute_deadline {
                    run_cancellation.cancel_for_deadline(self.absolute_deadline);
                    ConsultationRun::OverallTimedOut
                } else if run_cancellation.is_cancelled() {
                    ConsultationRun::Cancelled
                } else {
                    ConsultationRun::UnexpectedCancellation
                }
            }
            ConsultationOperation::LocalTimedOutAfterCompletion(Ok(proposal)) => {
                if self
                    .agent
                    .discard_completed_proposal(&consultation_digest, &proposal)
                {
                    ConsultationRun::LocalTimedOut
                } else {
                    ConsultationRun::Failure(search_state_failure(
                        "a deadline-discarded Agent candidate did not match the exact last accepted attempt",
                    ))
                }
            }
            ConsultationOperation::LocalTimedOutAfterCompletion(Err(_)) => {
                ConsultationRun::LocalTimedOut
            }
            ConsultationOperation::OverallTimedOutAfterCompletion(Ok(proposal)) => {
                if self
                    .agent
                    .discard_completed_proposal(&consultation_digest, &proposal)
                {
                    ConsultationRun::OverallTimedOut
                } else {
                    ConsultationRun::Failure(search_state_failure(
                        "an overall-deadline-discarded Agent result did not match the exact last accepted attempt",
                    ))
                }
            }
            ConsultationOperation::OverallTimedOutAfterCompletion(Err(_)) => {
                ConsultationRun::OverallTimedOut
            }
            ConsultationOperation::LocalTimedOut => ConsultationRun::LocalTimedOut,
            ConsultationOperation::OverallTimedOut => ConsultationRun::OverallTimedOut,
            ConsultationOperation::Cancelled => ConsultationRun::Cancelled,
        }
    }

    async fn publish_consultation_failure(
        &mut self,
        report: FailureReport,
    ) -> Result<(), FailureReport> {
        let latest = AgentSearchFeedback::failure(&self.houdini, report.clone())
            .map_err(feedback_failure)?;
        self.publish_next_feedback(&latest).await?;
        self.last_consultation_failure = Some(report);
        Ok(())
    }
}

// Only terminal data crosses the borrowing unwind boundary. The owning search
// is moved into the public handoff after all fallible asynchronous work finishes.
enum SearchCompletion {
    Failure(FailureReport),
    Valid {
        core: LeveledCoreHandle,
        termination: FrameworkIITerminationProof,
    },
    Invalid(Box<FrozenCounterexampleRecord>),
}

async fn catch_future_unwind<F: Future>(future: F) -> std::thread::Result<F::Output> {
    tokio::pin!(future);
    std::future::poll_fn(move |context| {
        match catch_unwind(AssertUnwindSafe(|| future.as_mut().poll(context))) {
            Ok(Poll::Ready(output)) => Poll::Ready(Ok(output)),
            Ok(Poll::Pending) => Poll::Pending,
            Err(payload) => Poll::Ready(Err(payload)),
        }
    })
    .await
}

/// Only results publishable by the pre-certificate search seam.
pub enum PreCertificateAgentHoudiniOutcome<S, C> {
    Failure(FailureReport),
    /// An epoch's termination check proved the postcondition on its Core; the
    /// handoff carries that frozen Core.
    Valid(Box<PreCertificateAgentHoudiniHandoff<S, C>>),
    /// Lean validated an agent-submitted counterexample; the run ends here
    /// with the frozen record its `Certificate/Invalid.lean` is built from.
    Invalid(Box<FrozenCounterexampleRecord>),
}

impl<S, C> std::fmt::Debug for PreCertificateAgentHoudiniOutcome<S, C> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Failure(report) => formatter.debug_tuple("Failure").field(report).finish(),
            Self::Valid(handoff) => formatter.debug_tuple("Valid").field(handoff).finish(),
            Self::Invalid(record) => formatter
                .debug_struct("Invalid")
                .field("instance_identity", &record.instance_identity())
                .field("fuel_consumed", &record.fuel_consumed())
                .finish_non_exhaustive(),
        }
    }
}

/// Exact live state transferred to later termination work without a claim.
///
/// Public callers receive only an owned inspection snapshot, never the live
/// search controller carried by this handoff:
///
/// ```compile_fail
/// use whiel_runner::PreCertificateAgentHoudiniHandoff;
///
/// fn leak_search<S, C>(handoff: &PreCertificateAgentHoudiniHandoff<S, C>) {
///     let _ = handoff.search();
/// }
/// ```
pub struct PreCertificateAgentHoudiniHandoff<S, C> {
    core: LeveledCoreHandle,
    /// The proof of *this* Core's termination check. Nothing else can
    /// authorize the freeze (Pass 7.5f).
    termination: FrameworkIITerminationProof,
    /// This run's frozen record, computed at most once and shared by every
    /// reader of it.
    frozen: Option<FrozenLeveledCore>,
    /// Whether [`Self::freeze_core`] has already handed the record out. A
    /// run freezes once.
    handed_out: bool,
    search: PreCertificateAgentHoudiniSearch<S, C>,
}

/// Value-only diagnostics for the retained runtime authorities.
///
/// This snapshot grants no admission, solver, artifact, or cancellation
/// capability. Its booleans and counters are observational, not proof
/// authority.
#[derive(Clone, Debug)]
pub struct PreCertificateAgentHoudiniRuntimeInspection {
    task_identity: TaskIdentity,
    scope_identity_sha256: Arc<str>,
    encoding_context_id: Arc<str>,
    artifact_backend_id: BackendId,
    admission_class: SolverAdmissionClass,
    resource_policy: RuntimeResourcePolicy,
    checker_matches_runtime: bool,
    cancellation_requested: bool,
    deadline_elapsed: bool,
    artifact_diagnostics: ArtifactBackendDiagnostics,
}

impl PreCertificateAgentHoudiniRuntimeInspection {
    pub fn task_identity(&self) -> &TaskIdentity {
        &self.task_identity
    }

    pub fn scope_identity_sha256(&self) -> &str {
        &self.scope_identity_sha256
    }

    pub fn encoding_context_id(&self) -> &str {
        &self.encoding_context_id
    }

    pub fn artifact_backend_id(&self) -> BackendId {
        self.artifact_backend_id
    }

    pub fn admission_class(&self) -> SolverAdmissionClass {
        self.admission_class
    }

    pub fn resource_policy(&self) -> RuntimeResourcePolicy {
        self.resource_policy
    }

    pub fn checker_matches_runtime(&self) -> bool {
        self.checker_matches_runtime
    }

    pub fn cancellation_requested(&self) -> bool {
        self.cancellation_requested
    }

    pub fn deadline_elapsed(&self) -> bool {
        self.deadline_elapsed
    }

    pub fn artifact_diagnostics(&self) -> &ArtifactBackendDiagnostics {
        &self.artifact_diagnostics
    }
}

/// Owned, read-only snapshot of one pre-termination handoff.
///
/// No field retains the live catalog, solver, checker, admission, artifact
/// store, encoding context, cancellation token, or Agent source.
#[derive(Clone, Debug)]
pub struct PreCertificateAgentHoudiniInspection {
    core: LeveledCoreHandle,
    core_is_current: bool,
    proposal_revision: u64,
    catalog_instance_digest: Arc<str>,
    catalog_len: usize,
    root_coverage: FrameworkIIRootCoverage,
    current_roots:
        BTreeMap<(crate::houdini::ClauseId, FrameworkIICheckRole), CurrentFrameworkIIRoot>,
    ledger: LevelAttemptLedger,
    agent_policy: AgentConsultationPolicy,
    attempt_history: Arc<[AgentHoudiniAttempt]>,
    limits: PreCertificateAgentHoudiniLimits,
    absolute_deadline: Instant,
    iteration: u64,
    feedback_iteration: u64,
    consultation_digest: Arc<str>,
    runtime: PreCertificateAgentHoudiniRuntimeInspection,
    max_level_stops_total: u64,
    termination_attempts_total: u64,
    preparation_time_total: Duration,
    solver_time_total: Duration,
    preparations_total: u64,
    worker_round_trips_total: u64,
}

impl PreCertificateAgentHoudiniInspection {
    pub fn core(&self) -> &LeveledCoreHandle {
        &self.core
    }

    pub fn core_is_current(&self) -> bool {
        self.core_is_current
    }

    pub fn proposal_revision(&self) -> u64 {
        self.proposal_revision
    }

    pub fn catalog_instance_digest(&self) -> &str {
        &self.catalog_instance_digest
    }

    pub fn catalog_len(&self) -> usize {
        self.catalog_len
    }

    pub fn root_coverage(&self) -> &FrameworkIIRootCoverage {
        &self.root_coverage
    }

    pub fn current_root(
        &self,
        clause: crate::houdini::ClauseId,
        role: FrameworkIICheckRole,
    ) -> Option<&CurrentFrameworkIIRoot> {
        self.current_roots.get(&(clause, role))
    }

    pub fn ledger(&self) -> &LevelAttemptLedger {
        &self.ledger
    }

    pub fn agent_policy(&self) -> &AgentConsultationPolicy {
        &self.agent_policy
    }

    pub fn attempt_history(&self) -> &[AgentHoudiniAttempt] {
        &self.attempt_history
    }

    pub fn limits(&self) -> PreCertificateAgentHoudiniLimits {
        self.limits
    }

    pub fn absolute_deadline(&self) -> Instant {
        self.absolute_deadline
    }

    pub fn iteration(&self) -> u64 {
        self.iteration
    }

    pub fn feedback_iteration(&self) -> u64 {
        self.feedback_iteration
    }

    pub fn consultation_digest(&self) -> &str {
        &self.consultation_digest
    }

    pub fn runtime(&self) -> &PreCertificateAgentHoudiniRuntimeInspection {
        &self.runtime
    }

    /// Cumulative count of promotions declined because the clause already
    /// sat at the run's level bound, so it stayed pending there.
    pub fn max_level_stops_total(&self) -> u64 {
        self.max_level_stops_total
    }

    /// Cumulative count of termination checks this run has run: one per
    /// epoch.
    pub fn termination_attempts_total(&self) -> u64 {
        self.termination_attempts_total
    }

    /// Cumulative wall time of every obligation preparation this run has
    /// recorded: splicing the problem out of the run's opaque-piece cache
    /// plus whatever worker round trips that cache missed on. Zero
    /// contribution from a dictionary-reuse or protected-theorem row.
    pub fn preparation_time_total(&self) -> Duration {
        self.preparation_time_total
    }

    /// Pass 7.5c: cumulative wall time of every solver launch this run has
    /// recorded.
    pub fn solver_time_total(&self) -> Duration {
        self.solver_time_total
    }

    /// Count of checks this run has recorded that performed a fresh
    /// obligation preparation, distinct from a dictionary reuse or
    /// protected-theorem selection. Not a worker round-trip count: a
    /// preparation whose pieces are all cached contacts no worker.
    pub fn preparations_total(&self) -> u64 {
        self.preparations_total
    }

    /// Count of worker round trips the run's opaque-piece cache actually
    /// made: `prepare_clause_pieces` plus `prepare_task_pieces` plus
    /// `prepare_support_block`. This is the real worker traffic behind
    /// [`Self::preparations_total`], read from
    /// `FrameworkIISolverContext::piece_cache_stats`.
    pub fn worker_round_trips_total(&self) -> u64 {
        self.worker_round_trips_total
    }
}

impl<S: AgentProvider, C: FrameworkIIChecker> PreCertificateAgentHoudiniHandoff<S, C> {
    pub fn inspection(
        &self,
    ) -> Result<PreCertificateAgentHoudiniInspection, super::catalog::FrameworkIIStateError> {
        let current_core = self.search.houdini.core();
        let core_is_current = self.core.core_digest() == current_core.core_digest()
            && self.core.snapshot().same_partition(current_core.snapshot());
        let root_coverage = self.search.houdini.root_coverage()?;
        let mut current_roots = BTreeMap::new();
        for clause in self.core.snapshot().canonical_order() {
            for role in [
                FrameworkIICheckRole::Initialization,
                FrameworkIICheckRole::Maintenance,
            ] {
                if let Some(root) = self.search.houdini.current_root(*clause, role) {
                    current_roots.insert((*clause, role), root.clone());
                }
            }
        }
        let runtime = &self.search.runtime;
        let feedback = self.search.feedback.feedback();
        Ok(PreCertificateAgentHoudiniInspection {
            core: self.core.clone(),
            core_is_current,
            proposal_revision: self.search.houdini.proposal_revision(),
            catalog_instance_digest: Arc::from(self.search.houdini.catalog().instance_digest()),
            catalog_len: self.search.houdini.catalog().len()?,
            root_coverage,
            current_roots,
            ledger: self.search.houdini.attempts().clone(),
            agent_policy: self.search.agent.policy().clone(),
            attempt_history: self.search.agent.attempt_history().into(),
            limits: self.search.limits,
            absolute_deadline: self.search.absolute_deadline,
            iteration: self.search.iteration,
            feedback_iteration: feedback.iteration(),
            consultation_digest: Arc::from(feedback.consultation_digest()),
            max_level_stops_total: self.search.houdini.max_level_stops_total(),
            termination_attempts_total: self.search.houdini.termination_attempts_total(),
            preparation_time_total: self.search.houdini.preparation_time_total(),
            solver_time_total: self.search.houdini.solver_time_total(),
            preparations_total: self.search.houdini.preparations_total(),
            worker_round_trips_total: runtime.solver.piece_cache_stats().worker_round_trips(),
            runtime: PreCertificateAgentHoudiniRuntimeInspection {
                task_identity: self.search.task.identity().clone(),
                scope_identity_sha256: Arc::from(runtime.admission.scope().identity_sha256()),
                encoding_context_id: Arc::from(runtime.admission.encoding().context_id()),
                artifact_backend_id: runtime.artifacts.backend_id(),
                admission_class: runtime.solver_admission.class(),
                resource_policy: runtime.solver_admission.policy(),
                checker_matches_runtime: runtime.checker.matches_search_runtime(
                    &runtime.solver,
                    &runtime.artifacts,
                    &runtime.solver_admission,
                    &runtime.cancellation,
                ),
                cancellation_requested: runtime.cancellation.is_cancelled(),
                deadline_elapsed: runtime.cancellation.deadline_elapsed(),
                artifact_diagnostics: runtime.artifacts.diagnostics(),
            },
        })
    }

    /// Freeze this run's final Core (Pass 7.5f).
    ///
    /// The record is immutable and ordered: the Core's clauses in canonical
    /// level order with their Lean-issued identities and canonical sources,
    /// the task and scope identities, and one closed profile label per job,
    /// read from the run's search provenance. It is authorized only by the
    /// termination proof this handoff carries, which is the proof of this
    /// exact Core; a refuted or inconclusive termination check never
    /// reaches a handoff at all.
    ///
    /// Freeze-once: a second call is refused with
    /// [`CoreFreezeError::AlreadyFrozen`] rather than producing a second
    /// record.
    pub fn freeze_core(&mut self) -> Result<FrozenLeveledCore, CoreFreezeError> {
        if self.handed_out {
            return Err(CoreFreezeError::AlreadyFrozen);
        }
        let frozen = self.frozen_core()?.clone();
        self.handed_out = true;
        Ok(frozen)
    }

    /// This run's frozen Core, computed on first demand and shared.
    ///
    /// The record a run freezes is a pure function of the Core it proved,
    /// so a reader that only needs to *name* the result — the acceptance
    /// record written before certification starts — reads it through here
    /// rather than consuming the single freeze [`Self::freeze_core`] hands
    /// to certification. There is still exactly one record: the second
    /// caller is given the one the first computed.
    pub fn frozen_core(&mut self) -> Result<&FrozenLeveledCore, CoreFreezeError> {
        if self.frozen.is_none() {
            let frozen = self.compute_freeze()?;
            self.frozen = Some(frozen);
        }
        Ok(self.frozen.as_ref().expect("the record was just computed"))
    }

    /// The immutable snapshot of the Core this run proved.
    ///
    /// Read-only, and the same snapshot [`Self::frozen_core`] freezes, so a
    /// record rendered from it names exactly the clauses the certification
    /// re-admits.
    pub fn core_snapshot(&self) -> &Arc<LeveledCandidateSnapshot> {
        self.core.snapshot()
    }

    fn compute_freeze(&self) -> Result<FrozenLeveledCore, CoreFreezeError> {
        // The run's own CASC portfolio policy, read from the checker that
        // applied it: disabled, a Core carrying a `casc_2025` label
        // contradicts the run that produced it and is refused here rather
        // than carried into certification.
        let casc_portfolio = self
            .search
            .runtime
            .checker
            .retry_policy()
            .map(FrameworkIIRetryPolicy::casc_portfolio)
            .unwrap_or_default();
        FrozenLeveledCore::freeze_under(
            &self.core,
            self.search.runtime.admission.scope(),
            &self.termination,
            &self
                .search
                .runtime
                .checker
                .search_profile_provenance(self.core.snapshot()),
            casc_portfolio,
        )
    }

    /// The run's clause catalog, read only.
    ///
    /// Pass 7.5f's certification re-admits the frozen clauses and requires
    /// each one to intern to the exact identity and catalog id the freeze
    /// recorded, so it needs the very catalog this run interned them in.
    /// This grants no registration or mutation capability: the catalog's
    /// own API decides what a shared reference can do, and certification
    /// only reads through it.
    pub fn catalog(&self) -> &super::catalog::LeveledClauseCatalog {
        self.search.houdini.catalog()
    }

    #[allow(dead_code)] // Step 7 will consume these exact live authorities.
    pub(crate) fn into_live_parts(
        self,
    ) -> (LeveledCoreHandle, PreCertificateAgentHoudiniSearch<S, C>) {
        (self.core, self.search)
    }
}

impl<S, C> std::fmt::Debug for PreCertificateAgentHoudiniHandoff<S, C> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("PreCertificateAgentHoudiniHandoff")
            .field("core_digest", &self.core.core_digest())
            .field("iteration", &self.search.iteration)
            .field("iteration_limit", &self.search.limits.iteration_limit)
            .field("absolute_deadline", &self.search.absolute_deadline)
            .field(
                "artifact_backend",
                &self.search.runtime.artifacts.backend_id(),
            )
            .finish_non_exhaustive()
    }
}

// ------------------------------------------------------------
// Deadline Arbitration
// ------------------------------------------------------------

/// The classified result of one `validate_counterexample` worker call, before
/// any feedback is built from it.
#[derive(Debug)]
pub(super) enum CounterexampleCall {
    Validated(ValidatedCounterexample),
    Rejected(CounterexampleRejection),
    /// A lane-local worker failure: it becomes a `failure` event and the
    /// search continues.
    LaneFailure(FailureReport),
    /// A run-global worker failure: the run ends here.
    RunFailure(FailureReport),
    OverallTimedOut,
    Interrupted,
}

/// Map one raced `validate_counterexample` call onto its search effect.
///
/// The call-local limit is the only outcome that becomes an ordinary
/// rejection: the worker never decided, its process was terminated, and the
/// run itself is untouched. The run's own cancellation and absolute deadline
/// keep their usual meanings.
pub(super) fn classify_counterexample_call(
    call: ConsultationOperation<Result<CounterexampleValidation, FrameworkIICounterexampleError>>,
    call_limit: Duration,
) -> CounterexampleCall {
    match call {
        ConsultationOperation::Completed(Ok(CounterexampleValidation::Validated(validated))) => {
            CounterexampleCall::Validated(validated)
        }
        ConsultationOperation::Completed(Ok(CounterexampleValidation::Rejected(rejection))) => {
            CounterexampleCall::Rejected(rejection)
        }
        ConsultationOperation::Completed(Err(FrameworkIICounterexampleError::Failure(report))) => {
            if report.scope() == FailureScope::RunGlobal {
                CounterexampleCall::RunFailure(report)
            } else {
                CounterexampleCall::LaneFailure(report)
            }
        }
        ConsultationOperation::Completed(Err(FrameworkIICounterexampleError::Cancelled))
        | ConsultationOperation::Cancelled => CounterexampleCall::Interrupted,
        ConsultationOperation::LocalTimedOut
        | ConsultationOperation::LocalTimedOutAfterCompletion(_) => {
            CounterexampleCall::Rejected(CounterexampleRejection::timeout(format!(
                "Lean did not decide this instance within the host's {call_limit:?} \
                 counterexample validation limit."
            )))
        }
        ConsultationOperation::OverallTimedOut
        | ConsultationOperation::OverallTimedOutAfterCompletion(_) => {
            CounterexampleCall::OverallTimedOut
        }
    }
}

// ------------------------------------------------------------
// Validating One Already Recorded Witness
// ------------------------------------------------------------

/// Slack between the call-local counterexample-validation limit and the
/// run-level deadline a single-call validation runs under, so that the
/// call-local limit is the one that fires and becomes an ordinary `timeout`
/// rejection rather than a run-level timeout.
const RECORDED_WITNESS_DEADLINE_SLACK: Duration = Duration::from_secs(1);

/// What Lean answered about one already recorded witness.
#[derive(Debug)]
pub enum RecordedWitnessValidation {
    Validated(Box<ValidatedCounterexample>),
    /// Lean's own typed rejection, verbatim — including the `timeout`
    /// rejection the call-local validation limit produces when Lean does
    /// not decide the instance inside it.
    Rejected(CounterexampleRejection),
    /// The worker lane failed.
    Failure(FailureReport),
}

/// Validate one already recorded witness through Lean's own
/// `validate_counterexample`, under the same call-local limit the search
/// applies to an agent's submission.
///
/// This is the entry point the certificate CLI's `--witness` mode uses, and
/// it is the search's own arbitration, not a copy of it: the worker call
/// runs against a fresh call-scoped cancellation token raced by
/// [`await_consultation_operation`] against `limits`'
/// `counterexample_validation_limit`, and the outcome is classified by the
/// same [`classify_counterexample_call`] the search uses. Cancelling the
/// call-scoped token terminates the worker process serving the call, so the
/// pool retires and replaces it, and the expired call becomes an ordinary
/// `timeout` rejection rather than a verdict on the instance.
///
/// The limit is therefore applied for real. A record built from the
/// returned witness must state that same limit as its fuel policy, since
/// that is the only guard the replay ran under.
pub async fn validate_recorded_witness(
    solver: &FrameworkIISolverContext,
    admission: &SolverAdmission,
    limits: PreCertificateAgentHoudiniLimits,
    witness: &serde_json::Value,
) -> RecordedWitnessValidation {
    let limit = limits.counterexample_validation_limit();
    let call_cancellation = CancellationToken::new();
    // One call is this whole step, so there is no run to cancel around it;
    // the run-level deadline exists only to sit strictly after the
    // call-local one.
    let run_cancellation = CancellationToken::new();
    let absolute_deadline = Instant::now() + limit + RECORDED_WITNESS_DEADLINE_SLACK;
    let call = {
        let operation = solver.validate_counterexample(witness, admission, &call_cancellation);
        await_consultation_operation(
            operation,
            &call_cancellation,
            &run_cancellation,
            absolute_deadline,
            Some(limit),
        )
        .await
    };
    match classify_counterexample_call(call, limit) {
        CounterexampleCall::Validated(validated) => {
            RecordedWitnessValidation::Validated(Box::new(validated))
        }
        CounterexampleCall::Rejected(rejection) => RecordedWitnessValidation::Rejected(rejection),
        CounterexampleCall::LaneFailure(report) | CounterexampleCall::RunFailure(report) => {
            RecordedWitnessValidation::Failure(report)
        }
        CounterexampleCall::OverallTimedOut => {
            RecordedWitnessValidation::Failure(FailureReport::overall_timeout(limit))
        }
        CounterexampleCall::Interrupted => RecordedWitnessValidation::Failure(interrupted_report()),
    }
}

/// What one counterexample validation did to the run.
enum CounterexampleStep {
    /// Lean validated the instance; the run ends invalid.
    Invalid(Box<FrozenCounterexampleRecord>),
    /// The run ends without a result, with this report.
    Finish(FailureReport),
    /// The search continues with this latest event.
    Continue(AgentSearchFeedback),
}

#[derive(Debug)]
enum ConsultationRun {
    Completed(HoudiniProposal),
    LocalTimedOut,
    OverallTimedOut,
    Cancelled,
    UnexpectedCancellation,
    Failure(FailureReport),
}

pub(super) enum ConsultationOperation<T> {
    Completed(T),
    LocalTimedOutAfterCompletion(T),
    OverallTimedOutAfterCompletion(T),
    LocalTimedOut,
    OverallTimedOut,
    Cancelled,
}

pub(super) enum OverallOperation<T> {
    Completed(T),
    TimedOut,
    Cancelled,
}

pub(super) fn strictly_earlier_consultation_deadline(
    start: Instant,
    consultation_limit: Option<Duration>,
    overall_deadline: Instant,
) -> Option<Instant> {
    consultation_limit
        .and_then(|limit| start.checked_add(limit))
        .filter(|deadline| *deadline < overall_deadline)
}

pub(super) async fn await_consultation_operation<F, T>(
    operation: F,
    consultation_cancellation: &CancellationToken,
    run_cancellation: &CancellationToken,
    overall_deadline: Instant,
    consultation_limit: Option<Duration>,
) -> ConsultationOperation<T>
where
    F: Future<Output = T>,
{
    let local_deadline = strictly_earlier_consultation_deadline(
        Instant::now(),
        consultation_limit,
        overall_deadline,
    );
    await_consultation_operation_until(
        operation,
        consultation_cancellation,
        run_cancellation,
        overall_deadline,
        local_deadline,
    )
    .await
}

async fn await_consultation_operation_until<F, T>(
    operation: F,
    consultation_cancellation: &CancellationToken,
    run_cancellation: &CancellationToken,
    overall_deadline: Instant,
    local_deadline: Option<Instant>,
) -> ConsultationOperation<T>
where
    F: Future<Output = T>,
{
    assert!(
        consultation_cancellation
            .bind_absolute_deadline(local_deadline.unwrap_or(overall_deadline)),
        "one consultation owns one immutable effective deadline"
    );
    if run_cancellation.cancelled_before(overall_deadline) {
        consultation_cancellation.cancel_from(run_cancellation);
        return ConsultationOperation::Cancelled;
    }
    if Instant::now() >= overall_deadline {
        run_cancellation.cancel_for_deadline(overall_deadline);
        consultation_cancellation.cancel_from(run_cancellation);
        return ConsultationOperation::OverallTimedOut;
    }
    if run_cancellation.is_cancelled() {
        consultation_cancellation.cancel_from(run_cancellation);
        return ConsultationOperation::Cancelled;
    }
    if let Some(deadline) = local_deadline.filter(|deadline| Instant::now() >= *deadline) {
        consultation_cancellation.cancel_for_deadline(deadline);
        return ConsultationOperation::LocalTimedOut;
    }
    let operation = operation;
    tokio::pin!(operation);
    let overall = tokio::time::sleep_until(overall_deadline);
    tokio::pin!(overall);

    if let Some(local_deadline) = local_deadline {
        let local = tokio::time::sleep_until(local_deadline);
        tokio::pin!(local);
        tokio::select! {
            biased;
            _ = run_cancellation.cancelled() => {
                consultation_cancellation.cancel_from(run_cancellation);
                let result = operation.await;
                if run_cancellation.cancelled_before(overall_deadline) {
                    ConsultationOperation::Cancelled
                } else {
                    run_cancellation.cancel_for_deadline(overall_deadline);
                    ConsultationOperation::OverallTimedOutAfterCompletion(result)
                }
            }
            _ = &mut local => {
                consultation_cancellation.cancel_for_deadline(local_deadline);
                tokio::select! {
                    biased;
                    _ = run_cancellation.cancelled() => {
                        let result = operation.await;
                        if run_cancellation.cancelled_before(overall_deadline) {
                            ConsultationOperation::Cancelled
                        } else {
                            run_cancellation.cancel_for_deadline(overall_deadline);
                            ConsultationOperation::OverallTimedOutAfterCompletion(result)
                        }
                    }
                    _ = &mut overall => {
                        run_cancellation.cancel_for_deadline(overall_deadline);
                        let result = operation.await;
                        if run_cancellation.cancelled_before(overall_deadline) {
                            ConsultationOperation::Cancelled
                        } else {
                            ConsultationOperation::OverallTimedOutAfterCompletion(result)
                        }
                    }
                    result = &mut operation => {
                        if run_cancellation.cancelled_before(overall_deadline) {
                            ConsultationOperation::Cancelled
                        } else if Instant::now() >= overall_deadline {
                            run_cancellation.cancel_for_deadline(overall_deadline);
                            ConsultationOperation::OverallTimedOutAfterCompletion(result)
                        } else if run_cancellation.is_cancelled() {
                            ConsultationOperation::Cancelled
                        } else {
                            ConsultationOperation::LocalTimedOutAfterCompletion(result)
                        }
                    }
                }
            }
            _ = &mut overall => {
                run_cancellation.cancel_for_deadline(overall_deadline);
                consultation_cancellation.cancel_from(run_cancellation);
                let result = operation.await;
                if run_cancellation.cancelled_before(overall_deadline) {
                    ConsultationOperation::Cancelled
                } else {
                    ConsultationOperation::OverallTimedOutAfterCompletion(result)
                }
            }
            result = &mut operation => {
                if run_cancellation.cancelled_before(overall_deadline) {
                    consultation_cancellation.cancel_from(run_cancellation);
                    ConsultationOperation::Cancelled
                } else if Instant::now() >= overall_deadline {
                    run_cancellation.cancel_for_deadline(overall_deadline);
                    consultation_cancellation.cancel_from(run_cancellation);
                    ConsultationOperation::OverallTimedOutAfterCompletion(result)
                } else if Instant::now() >= local_deadline {
                    consultation_cancellation.cancel_for_deadline(local_deadline);
                    ConsultationOperation::LocalTimedOutAfterCompletion(result)
                } else if run_cancellation.is_cancelled() {
                    consultation_cancellation.cancel_from(run_cancellation);
                    ConsultationOperation::Cancelled
                } else {
                    ConsultationOperation::Completed(result)
                }
            }
        }
    } else {
        tokio::select! {
            biased;
            _ = run_cancellation.cancelled() => {
                consultation_cancellation.cancel_from(run_cancellation);
                let result = operation.await;
                if run_cancellation.cancelled_before(overall_deadline) {
                    ConsultationOperation::Cancelled
                } else {
                    run_cancellation.cancel_for_deadline(overall_deadline);
                    ConsultationOperation::OverallTimedOutAfterCompletion(result)
                }
            }
            _ = &mut overall => {
                run_cancellation.cancel_for_deadline(overall_deadline);
                consultation_cancellation.cancel_from(run_cancellation);
                let result = operation.await;
                if run_cancellation.cancelled_before(overall_deadline) {
                    ConsultationOperation::Cancelled
                } else {
                    ConsultationOperation::OverallTimedOutAfterCompletion(result)
                }
            }
            result = &mut operation => {
                if run_cancellation.cancelled_before(overall_deadline) {
                    consultation_cancellation.cancel_from(run_cancellation);
                    ConsultationOperation::Cancelled
                } else if Instant::now() >= overall_deadline {
                    run_cancellation.cancel_for_deadline(overall_deadline);
                    consultation_cancellation.cancel_from(run_cancellation);
                    ConsultationOperation::OverallTimedOutAfterCompletion(result)
                } else if run_cancellation.is_cancelled() {
                    consultation_cancellation.cancel_from(run_cancellation);
                    ConsultationOperation::Cancelled
                } else {
                    ConsultationOperation::Completed(result)
                }
            }
        }
    }
}

pub(super) async fn await_overall_operation<F, T>(
    operation: F,
    cancellation: &CancellationToken,
    absolute_deadline: Instant,
) -> OverallOperation<T>
where
    F: Future<Output = T>,
{
    if cancellation.cancelled_before(absolute_deadline) {
        return OverallOperation::Cancelled;
    }
    if Instant::now() >= absolute_deadline {
        cancellation.cancel_for_deadline(absolute_deadline);
        return OverallOperation::TimedOut;
    }
    if cancellation.is_cancelled() {
        return OverallOperation::Cancelled;
    }
    let operation = operation;
    tokio::pin!(operation);
    let deadline = tokio::time::sleep_until(absolute_deadline);
    tokio::pin!(deadline);
    tokio::select! {
        biased;
        _ = cancellation.cancelled() => {
            let _ = operation.await;
            if cancellation.cancelled_before(absolute_deadline) {
                OverallOperation::Cancelled
            } else {
                cancellation.cancel_for_deadline(absolute_deadline);
                OverallOperation::TimedOut
            }
        }
        _ = &mut deadline => {
            cancellation.cancel_for_deadline(absolute_deadline);
            let _ = operation.await;
            if cancellation.cancelled_before(absolute_deadline) {
                OverallOperation::Cancelled
            } else {
                OverallOperation::TimedOut
            }
        }
        result = &mut operation => {
            if cancellation.cancelled_before(absolute_deadline) {
                OverallOperation::Cancelled
            } else if Instant::now() >= absolute_deadline {
                cancellation.cancel_for_deadline(absolute_deadline);
                OverallOperation::TimedOut
            } else if cancellation.is_cancelled() {
                OverallOperation::Cancelled
            } else {
                OverallOperation::Completed(result)
            }
        }
    }
}

fn feedback_failure(error: AgentFeedbackError) -> FailureReport {
    search_state_failure(format!(
        "construct exact bounded AgentHoudini feedback: {error}"
    ))
}

fn search_state_failure(detail: impl Into<String>) -> FailureReport {
    FailureReport::try_new(
        FailureOrigin::RunControl,
        FailureKind::InfrastructureFailure,
        false,
        FailureScope::RunGlobal,
        Some(detail.into()),
        Vec::new(),
    )
    .expect("pre-certificate state failures use an approved run-control pair")
}

fn interrupted_report() -> FailureReport {
    FailureReport::try_new(
        FailureOrigin::RunControl,
        FailureKind::Interrupted,
        false,
        FailureScope::RunGlobal,
        Some("AgentHoudini search was cancelled by its run owner".to_string()),
        Vec::new(),
    )
    .expect("pre-certificate cancellation uses the standard interrupted pair")
}

/// The first host limit on which a checker's own configuration disagrees with
/// the run's feedback policy, or `None` when they agree.
///
/// The run's host limits have a single source, the feedback policy. A checker
/// that keeps its own copy — the production checker does, for countermodel
/// retention — must carry that same copy, or the standing presentation would
/// state one limit while the dictionary applied another. A checker that
/// carries no host-limit configuration at all (every deterministic test
/// adapter) is not checked.
fn checker_host_limit_disagreement<C: FrameworkIIChecker>(
    checker: &C,
    policy: &AgentFeedbackPolicy,
) -> Option<HostLimitDisagreement> {
    policy
        .host_limits()
        .first_disagreement(checker.host_limits()?)
}

#[cfg(test)]
mod host_limit_agreement_tests {
    use super::*;
    use crate::framework2::catalog::FrameworkIIStateError;
    use crate::framework2::feedback::AgentFeedbackLimits;
    use crate::framework2::host_limits::HostLimits;
    use crate::framework2::ledger::FrameworkIICheckRequest;
    use crate::framework2::stabilization::{FrameworkIICheckExecution, sealed};

    /// A checker that reports exactly the host limits it was built with. The
    /// trait is sealed, so only the crate's own tests can stand in for the
    /// production checker here.
    struct FixedLimitChecker(Option<HostLimits>);

    impl sealed::Sealed for FixedLimitChecker {}

    impl FrameworkIIChecker for FixedLimitChecker {
        fn host_limits(&self) -> Option<&HostLimits> {
            self.0.as_ref()
        }

        fn check<'a>(
            &'a mut self,
            _request: FrameworkIICheckRequest,
        ) -> std::pin::Pin<
            Box<
                dyn std::future::Future<
                        Output = Result<FrameworkIICheckExecution, FrameworkIIStateError>,
                    > + Send
                    + 'a,
            >,
        > {
            Box::pin(std::future::ready(Err(
                FrameworkIIStateError::InvalidEvidence("test checker never checks"),
            )))
        }
    }

    fn policy_with(host_limits: HostLimits) -> AgentFeedbackPolicy {
        AgentFeedbackPolicy::new(AgentFeedbackLimits {
            host_limits,
            ..AgentFeedbackLimits::default()
        })
        .expect("a positive host limit is a valid policy")
    }

    /// Pass 7.7b, item 3: the checker's limits and the policy's are one
    /// value, and a run whose two authorities disagree fails closed.
    #[test]
    fn a_checker_that_carries_other_limits_disagrees_with_the_policy() {
        let limits = HostLimits {
            countermodel_retention_tuples: Some(2),
            ..HostLimits::UNBOUNDED
        };
        let policy = policy_with(limits);

        // Agreement: the single-source wiring the bootstrap builds.
        assert_eq!(
            checker_host_limit_disagreement(&FixedLimitChecker(Some(limits)), &policy),
            None
        );

        // A checker left unconfigured while the policy declares a limit.
        let disagreement = checker_host_limit_disagreement(
            &FixedLimitChecker(Some(HostLimits::UNBOUNDED)),
            &policy,
        )
        .expect("an unconfigured checker disagrees with a declared limit");
        assert_eq!(disagreement.limit(), "countermodel_retention_tuples");
        assert_eq!(disagreement.policy(), Some(2));
        assert_eq!(disagreement.other(), None);

        // The reverse: a checker bounded where the policy is not.
        let disagreement = checker_host_limit_disagreement(
            &FixedLimitChecker(Some(limits)),
            &policy_with(HostLimits::UNBOUNDED),
        )
        .expect("a checker limit the policy never declared disagrees");
        assert_eq!(disagreement.policy(), None);
        assert_eq!(disagreement.other(), Some(2));

        // A checker with no host-limit configuration is not checked.
        assert_eq!(
            checker_host_limit_disagreement(&FixedLimitChecker(None), &policy),
            None
        );
    }
}

#[cfg(test)]
#[path = "search_panic_tests.rs"]
mod panic_cleanup_tests;
