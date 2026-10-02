use std::sync::Arc;

use crate::artifact::{ArtifactKind, ArtifactRef, AttemptId, ScopeTag, StagedArtifact};
use crate::failure::{FailureKind, FailureOrigin, FailureReport, FailureScope};
use crate::runtime::CancellationToken;

use super::command::{
    FmbSize, VampireInvocationProfile, VampireWorkerMode, VampireWorkerRequest, invocation,
};
use super::process::{CaptureConfig, ProcessOutput, ProcessStartError, StopReason};
use super::protocol::{DEFAULT_MAX_PROTOCOL_LINE_BYTES, ProtocolSummary, SzsStatus};

/*
  This is the typed boundary for one Vampire process. It deliberately
  does not race proof search against FMB or assign deadline meaning to
  cancellation; Phase 2B owns that arbitration.
*/

// ------------------------------------------------------------
// Output Capture Policy
// ------------------------------------------------------------

const DEFAULT_DIAGNOSTIC_BYTES: usize = 64 * 1024;
const MAX_DIAGNOSTIC_BYTES: usize = 1024 * 1024;
const MAX_PROTOCOL_LINE_BYTES: usize = 1024 * 1024;

#[derive(Clone, Copy, Debug)]
pub struct VampireCapturePolicy {
    diagnostic_bytes_per_stream: usize,
    max_protocol_line_bytes: usize,
    max_total_output_bytes: Option<u64>,
    retain_full_inconclusive_output: bool,
}

impl VampireCapturePolicy {
    pub fn diagnostic_bytes_per_stream(mut self, bytes: usize) -> Self {
        self.diagnostic_bytes_per_stream = bytes.min(MAX_DIAGNOSTIC_BYTES);
        self
    }

    pub fn max_protocol_line_bytes(mut self, bytes: usize) -> Self {
        self.max_protocol_line_bytes = bytes.clamp(1, MAX_PROTOCOL_LINE_BYTES);
        self
    }

    pub fn max_total_output_bytes(mut self, bytes: Option<u64>) -> Self {
        self.max_total_output_bytes = bytes;
        self
    }

    pub fn retain_full_inconclusive_output(mut self, retain: bool) -> Self {
        self.retain_full_inconclusive_output = retain;
        self
    }
}

impl Default for VampireCapturePolicy {
    fn default() -> Self {
        Self {
            diagnostic_bytes_per_stream: DEFAULT_DIAGNOSTIC_BYTES,
            max_protocol_line_bytes: DEFAULT_MAX_PROTOCOL_LINE_BYTES,
            max_total_output_bytes: None,
            retain_full_inconclusive_output: false,
        }
    }
}

// ------------------------------------------------------------
// Typed Worker Evidence And Outcomes
// ------------------------------------------------------------

/*
  A proof or model contains compact metadata and one stable reference
  to complete framed stdout. The payload remains untrusted until the
  later decoder or certification boundary accepts it.
*/

#[derive(Clone, Debug)]
pub struct VampireProof {
    problem_identity: Arc<str>,
    attempt_id: AttemptId,
    query_artifact: Option<ArtifactRef>,
    output: ArtifactRef,
    szs_status: &'static str,
    strategy: VampireProofStrategy,
    invocation: VampireInvocationProfile,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VampireProofStrategy {
    Direct,
    Casc2025,
}

impl VampireProofStrategy {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Direct => "direct",
            Self::Casc2025 => "casc_2025",
        }
    }
}

impl VampireProof {
    pub fn problem_identity(&self) -> &str {
        &self.problem_identity
    }

    pub fn attempt_id(&self) -> AttemptId {
        self.attempt_id
    }

    pub fn output(&self) -> ArtifactRef {
        self.output
    }

    /// Return the exact assembled query when this proof came from Phase 2D.
    pub fn query_artifact(&self) -> Option<ArtifactRef> {
        self.query_artifact
    }

    pub fn szs_status(&self) -> &'static str {
        self.szs_status
    }

    pub fn strategy(&self) -> VampireProofStrategy {
        self.strategy
    }

    pub fn invocation(&self) -> &VampireInvocationProfile {
        &self.invocation
    }
}

#[derive(Clone, Debug)]
pub struct VampireModel {
    problem_identity: Arc<str>,
    attempt_id: AttemptId,
    query_artifact: Option<ArtifactRef>,
    output: ArtifactRef,
    szs_status: &'static str,
    invocation: VampireInvocationProfile,
}

impl VampireModel {
    #[cfg(test)]
    pub(crate) fn for_test(
        problem_identity: impl Into<Arc<str>>,
        attempt_id: AttemptId,
        output: ArtifactRef,
    ) -> Self {
        Self {
            problem_identity: problem_identity.into(),
            attempt_id,
            query_artifact: None,
            output,
            szs_status: "CounterSatisfiable",
            invocation: VampireInvocationProfile::for_test(),
        }
    }

    pub fn problem_identity(&self) -> &str {
        &self.problem_identity
    }

    pub fn attempt_id(&self) -> AttemptId {
        self.attempt_id
    }

    pub fn output(&self) -> ArtifactRef {
        self.output
    }

    /// Return the exact assembled query when this model came from Phase 2D.
    pub fn query_artifact(&self) -> Option<ArtifactRef> {
        self.query_artifact
    }

    pub fn szs_status(&self) -> &'static str {
        self.szs_status
    }

    pub fn invocation(&self) -> &VampireInvocationProfile {
        &self.invocation
    }
}

#[derive(Clone, Debug)]
pub enum VampireResult {
    Proved(VampireProof),
    Refuted(VampireModel),
    TimedOut {
        next_fmb_start_size: Option<FmbSize>,
        peer_failure: Option<FailureReport>,
    },
    Failure {
        report: FailureReport,
        next_fmb_start_size: Option<FmbSize>,
    },
}

#[derive(Clone, Debug)]
pub struct CancelledVampireWorker {
    next_fmb_start_size: Option<FmbSize>,
    prior_failure: Option<FailureReport>,
    artifact_references: Vec<ArtifactRef>,
    capture_warnings: Vec<String>,
}

impl CancelledVampireWorker {
    pub(crate) fn from_prior_capture(
        artifact_references: Vec<ArtifactRef>,
        capture_warnings: Vec<String>,
    ) -> Self {
        Self {
            next_fmb_start_size: None,
            prior_failure: None,
            artifact_references,
            capture_warnings,
        }
    }

    pub(crate) fn set_prior_failure(&mut self, prior_failure: Option<FailureReport>) {
        self.prior_failure = prior_failure;
    }

    pub(crate) fn extend_prior_capture(
        &mut self,
        artifact_references: &[ArtifactRef],
        capture_warnings: &[String],
    ) {
        for reference in artifact_references {
            if !self.artifact_references.contains(reference) {
                self.artifact_references.push(*reference);
            }
        }
        self.capture_warnings.extend_from_slice(capture_warnings);
    }

    pub fn next_fmb_start_size(&self) -> Option<FmbSize> {
        self.next_fmb_start_size
    }

    pub fn prior_failure(&self) -> Option<&FailureReport> {
        self.prior_failure.as_ref()
    }

    pub fn artifact_references(&self) -> &[ArtifactRef] {
        &self.artifact_references
    }

    pub fn capture_warnings(&self) -> &[String] {
        &self.capture_warnings
    }
}

#[derive(Clone, Debug)]
pub enum VampireWorkerOutcome {
    Result(VampireResult),
    Cancelled(CancelledVampireWorker),
    RunFailure(FailureReport),
}

// ------------------------------------------------------------
// Single-Worker Execution
// ------------------------------------------------------------

/// Run exactly one proof-search or finite-model-building worker.
///
/// Cancellation remains control flow. The Phase 2B owner decides whether a
/// cancellation represents a local timeout, a peer result, or run shutdown.
pub fn run_single_vampire_worker(
    request: VampireWorkerRequest,
    cancellation: CancellationToken,
    capture_policy: VampireCapturePolicy,
) -> VampireWorkerOutcome {
    if cancellation.is_cancelled() {
        return cancelled(None, Vec::new(), Vec::new());
    }
    let origin = mode_origin(&request.mode);
    let artifacts = request
        .artifacts
        .scoped(ScopeTag::solver(mode_name(&request.mode)));
    let invocation = match invocation(&request) {
        Ok(invocation) => invocation,
        Err(detail) => {
            return failure_outcome(
                origin,
                FailureKind::ProcessFailure,
                detail,
                Vec::new(),
                None,
            );
        }
    };
    let invocation_profile = invocation.profile();

    // Stdout can contain solver evidence, so it always streams to a
    // stage. Full stderr is staged only under the opt-in debug policy.
    let stdout_artifacts = artifacts.scoped(ScopeTag::named("stdout"));
    let (stdout_stage, stdout_writer) = match stdout_artifacts.begin_staged_payload() {
        Ok(staged) => staged,
        Err(report) => {
            return required_artifact_failure_outcome(
                origin,
                "stage Vampire stdout",
                report,
                Vec::new(),
                None,
            );
        }
    };
    let mut initial_capture_warnings = Vec::new();
    let (stderr_stage, stderr_writer) = if capture_policy.retain_full_inconclusive_output {
        let stderr_artifacts = artifacts.scoped(ScopeTag::named("stderr"));
        match stderr_artifacts.begin_staged_payload() {
            Ok((stage, writer)) => (Some(stage), Some(writer)),
            Err(report) if report.scope() == FailureScope::RunGlobal => {
                return VampireWorkerOutcome::RunFailure(report);
            }
            Err(report) => {
                initial_capture_warnings.push(artifact_failure_detail(
                    "stage optional Vampire stderr",
                    &report,
                ));
                (None, None)
            }
        }
    } else {
        (None, None)
    };

    let process = super::process::run(
        &invocation,
        stdout_writer,
        stderr_writer,
        cancellation,
        CaptureConfig {
            diagnostic_bytes: capture_policy.diagnostic_bytes_per_stream,
            protocol_line_bytes: capture_policy.max_protocol_line_bytes,
            max_total_output_bytes: capture_policy.max_total_output_bytes,
        },
    );
    match process {
        Err(ProcessStartError::Cancelled) => cancelled(None, Vec::new(), initial_capture_warnings),
        Err(ProcessStartError::RunFailure(detail)) => run_failure_outcome(origin, detail),
        Err(ProcessStartError::Failed(detail)) => failure_with_captures(
            &artifacts,
            origin,
            FailureKind::ProcessFailure,
            detail,
            None,
            None,
            stdout_stage,
            stderr_stage,
            capture_policy,
            initial_capture_warnings,
        ),
        Ok(process) => finish_worker(
            request,
            artifacts,
            process,
            invocation_profile,
            stdout_stage,
            stderr_stage,
            capture_policy,
            initial_capture_warnings,
        ),
    }
}

#[allow(clippy::too_many_arguments)]
fn finish_worker(
    request: VampireWorkerRequest,
    artifacts: crate::ArtifactStore,
    process: ProcessOutput,
    invocation_profile: VampireInvocationProfile,
    stdout_stage: StagedArtifact,
    stderr_stage: Option<StagedArtifact>,
    capture_policy: VampireCapturePolicy,
    initial_capture_warnings: Vec<String>,
) -> VampireWorkerOutcome {
    let origin = mode_origin(&request.mode);
    let mut protocol = process.stdout.protocol.clone();
    protocol.merge(process.stderr.protocol.clone());
    let frontier = match request.mode {
        VampireWorkerMode::ProofOnly | VampireWorkerMode::ProofCasc => None,
        VampireWorkerMode::FmbOnly(_) => protocol.last_fmb_frontier(),
    };

    // Cleanup failure makes the run unsafe. It takes precedence over
    // cancellation and every solver-level classification.
    if let Some(cleanup_error) = &process.cleanup_error {
        return run_failure_outcome(
            origin,
            diagnostic_detail(
                &format!("Vampire process-tree cleanup failed: {cleanup_error}"),
                Some(&process),
            ),
        );
    }
    if let Some(report) = artifacts.resource_failure() {
        return VampireWorkerOutcome::RunFailure(report);
    }
    if process.reason == StopReason::Cancelled {
        return cancelled_with_captures(
            frontier,
            &process,
            stdout_stage,
            stderr_stage,
            capture_policy,
            initial_capture_warnings,
        );
    }
    if process.reason == StopReason::CaptureFailed
        || process.stdout.error.is_some()
        || process.stderr.error.is_some()
    {
        return failure_with_captures(
            &artifacts,
            origin,
            FailureKind::InfrastructureFailure,
            "Vampire output capture failed".to_string(),
            Some(&process),
            frontier,
            stdout_stage,
            stderr_stage,
            capture_policy,
            initial_capture_warnings,
        );
    }
    // Stdout that does not parse is a fault of this launch whatever else
    // it contains, and it keeps that precedence on every path — including
    // a nonzero exit, which is otherwise classified before the conclusion
    // is looked at. A stage whose output is malformed is therefore never
    // read as an ordinary limit stop or as a bare process failure, and so
    // never escalates into a second stage that would hide it.
    if protocol.stdout_is_malformed() {
        return failure_with_captures(
            &artifacts,
            origin,
            FailureKind::MalformedResult,
            "Vampire emitted an incomplete or inconsistent conclusive result".to_string(),
            Some(&process),
            frontier,
            stdout_stage,
            stderr_stage,
            capture_policy,
            initial_capture_warnings,
        );
    }
    let status = match &process.status {
        Ok(status) if status.success() => status,
        // The pinned solver exits nonzero when it stops itself at a limit
        // it was given — its wall clock or its memory. Every stage states
        // its limit, so this is the ordinary end of a launch that ran out
        // of what it was allowed, exactly as the runner's own backstop kill
        // is: the lane is inconclusive, the key keeps its place on the
        // retry ladder, and the diagnostics the solver printed are kept. A
        // nonzero exit with no such report of the stage's own is still a
        // process failure.
        Ok(status) if stopped_at_stated_limit(&request.mode, &protocol) => {
            return failure_with_captures(
                &artifacts,
                origin,
                FailureKind::CheckTimeout,
                format!("Vampire stopped at a limit it was given: {status}"),
                Some(&process),
                frontier,
                stdout_stage,
                stderr_stage,
                capture_policy,
                initial_capture_warnings,
            );
        }
        Ok(status) => {
            return failure_with_captures(
                &artifacts,
                origin,
                FailureKind::ProcessFailure,
                format!("Vampire exited unsuccessfully: {status}"),
                Some(&process),
                frontier,
                stdout_stage,
                stderr_stage,
                capture_policy,
                initial_capture_warnings,
            );
        }
        Err(error) => {
            return failure_with_captures(
                &artifacts,
                origin,
                FailureKind::ProcessFailure,
                format!("wait for Vampire process: {error}"),
                Some(&process),
                frontier,
                stdout_stage,
                stderr_stage,
                capture_policy,
                initial_capture_warnings,
            );
        }
    };
    let _ = status;

    let conclusion = classify(&request.mode, &protocol);
    match conclusion {
        Conclusion::Proof(status) => match stdout_stage.commit(ArtifactKind::Proof) {
            Ok(output) => {
                /*
                  Nothing reads a runtime proof back: outcomes are
                  stdout-authoritative and certification re-runs Vampire from
                  scratch, so outside detailed diagnostics this payload is
                  provenance no one consults. Discarding it as the job ends
                  bounds peak disk use, which pruning at settlement cannot.
                  A discard failure must never fail an otherwise proved job.
                */
                let _ = artifacts.discard(output);
                let strategy = match request.mode {
                    VampireWorkerMode::ProofOnly => VampireProofStrategy::Direct,
                    VampireWorkerMode::ProofCasc => VampireProofStrategy::Casc2025,
                    VampireWorkerMode::FmbOnly(_) => {
                        unreachable!("FMB mode cannot produce a proof conclusion")
                    }
                };
                request
                    .command
                    .telemetry()
                    .increment(format!("solver.proof_winners.{}", strategy.as_str()), 1);
                VampireWorkerOutcome::Result(VampireResult::Proved(VampireProof {
                    problem_identity: request.problem.identity_arc(),
                    attempt_id: request.attempt_id,
                    query_artifact: request.problem.query_artifact(),
                    output,
                    szs_status: status,
                    strategy,
                    invocation: invocation_profile,
                }))
            }
            Err(report) => required_artifact_failure_outcome(
                origin,
                "publish complete Vampire proof",
                report,
                Vec::new(),
                frontier,
            ),
        },
        Conclusion::Model(status) => match stdout_stage.commit(ArtifactKind::Model) {
            Ok(output) => VampireWorkerOutcome::Result(VampireResult::Refuted(VampireModel {
                problem_identity: request.problem.identity_arc(),
                attempt_id: request.attempt_id,
                query_artifact: request.problem.query_artifact(),
                output,
                szs_status: status,
                invocation: invocation_profile,
            })),
            Err(report) => required_artifact_failure_outcome(
                origin,
                "publish complete Vampire model",
                report,
                Vec::new(),
                frontier,
            ),
        },
        Conclusion::Malformed => failure_with_captures(
            &artifacts,
            origin,
            FailureKind::MalformedResult,
            "Vampire emitted an incomplete or inconsistent conclusive result".to_string(),
            Some(&process),
            frontier,
            stdout_stage,
            stderr_stage,
            capture_policy,
            initial_capture_warnings,
        ),
        Conclusion::Unknown => failure_with_captures(
            &artifacts,
            origin,
            FailureKind::SolverUnknown,
            "Vampire terminated without the worker mode's conclusive result".to_string(),
            Some(&process),
            frontier,
            stdout_stage,
            stderr_stage,
            capture_policy,
            initial_capture_warnings,
        ),
    }
}

// ------------------------------------------------------------
// Solver Result Classification
// ------------------------------------------------------------

enum Conclusion {
    Proof(&'static str),
    Model(&'static str),
    Unknown,
    Malformed,
}

/// Whether this stage's own final report was that it stopped at a limit
/// the runner gave it.
///
/// The question is about the process the runner started, not about
/// anything printed inside it. A portfolio runs its schedule as child
/// strategies and echoes each one's own termination, so a limit report in
/// its stream is ordinarily a child's; the parent's own last word is an
/// SZS status, which no child prints, and a parent that died instead of
/// finishing prints none. A single-strategy stage terminates once and its
/// report is its own, so there it is enough that the report is the last
/// thing the stage said.
fn stopped_at_stated_limit(mode: &VampireWorkerMode, protocol: &ProtocolSummary) -> bool {
    match mode {
        VampireWorkerMode::ProofCasc => protocol.ends_with_timeout_status(),
        VampireWorkerMode::ProofOnly | VampireWorkerMode::FmbOnly(_) => {
            protocol.ends_with_resource_limit()
        }
    }
}

fn classify(mode: &VampireWorkerMode, protocol: &ProtocolSummary) -> Conclusion {
    if protocol.stdout_is_malformed() {
        return Conclusion::Malformed;
    }
    match mode {
        VampireWorkerMode::ProofOnly | VampireWorkerMode::ProofCasc
            if protocol.has_complete_proof_output() =>
        {
            // All three establish the conjecture and are recorded under
            // the exact word the solver used. `ContradictoryAxioms` names
            // premises that are inconsistent among themselves, which entail
            // the conjecture along with everything else. It depends on the
            // roles the premises were written under, not on the formulas:
            // the same check reports it while its premises are axioms and
            // plain `Theorem` once a retry writes them as goal-derived, so
            // the label distinguishes that case only on a first launch.
            match protocol.last_status() {
                Some(SzsStatus::Theorem) => Conclusion::Proof("Theorem"),
                Some(SzsStatus::Unsatisfiable) => Conclusion::Proof("Unsatisfiable"),
                Some(SzsStatus::ContradictoryAxioms) => Conclusion::Proof("ContradictoryAxioms"),
                _ => Conclusion::Malformed,
            }
        }
        VampireWorkerMode::ProofOnly | VampireWorkerMode::ProofCasc => {
            match protocol.last_status() {
                Some(
                    SzsStatus::Theorem | SzsStatus::Unsatisfiable | SzsStatus::ContradictoryAxioms,
                ) => Conclusion::Malformed,
                _ if protocol.proof_started() || protocol.proof_complete() => Conclusion::Malformed,
                _ => Conclusion::Unknown,
            }
        }
        VampireWorkerMode::FmbOnly(_) if protocol.has_complete_model_output() => {
            Conclusion::Model("CounterSatisfiable")
        }
        VampireWorkerMode::FmbOnly(_) => match protocol.last_status() {
            Some(SzsStatus::CounterSatisfiable) => Conclusion::Malformed,
            _ if protocol.model_started() || protocol.model_complete() => Conclusion::Malformed,
            _ => Conclusion::Unknown,
        },
    }
}

// ------------------------------------------------------------
// Artifact And Failure Handling
// ------------------------------------------------------------

#[allow(clippy::too_many_arguments)]
fn failure_with_captures(
    artifacts: &crate::ArtifactStore,
    origin: FailureOrigin,
    kind: FailureKind,
    summary: String,
    process: Option<&ProcessOutput>,
    frontier: Option<FmbSize>,
    stdout_stage: StagedArtifact,
    stderr_stage: Option<StagedArtifact>,
    policy: VampireCapturePolicy,
    initial_capture_warnings: Vec<String>,
) -> VampireWorkerOutcome {
    let mut references = Vec::new();
    let mut optional_capture_warnings = initial_capture_warnings;
    if policy.retain_full_inconclusive_output && process.is_some_and(captures_are_complete) {
        if let Err(report) = retain_optional_trace(
            stdout_stage,
            "retain full Vampire stdout",
            &mut references,
            &mut optional_capture_warnings,
        ) {
            return VampireWorkerOutcome::RunFailure(report);
        }
        if let Some(stderr_stage) = stderr_stage
            && let Err(report) = retain_optional_trace(
                stderr_stage,
                "retain full Vampire stderr",
                &mut references,
                &mut optional_capture_warnings,
            )
        {
            return VampireWorkerOutcome::RunFailure(report);
        }
    }
    let summary = if optional_capture_warnings.is_empty() {
        summary
    } else {
        format!(
            "{summary}\noptional capture warnings: {}",
            optional_capture_warnings.join("; ")
        )
    };
    let detail = diagnostic_detail(&summary, process);
    let diagnostic_artifacts = artifacts.scoped(ScopeTag::named("diagnostic"));
    match diagnostic_artifacts.publish(
        ArtifactKind::FailureDiagnostic,
        detail.as_bytes().to_vec().into_boxed_slice(),
    ) {
        Ok(reference) => references.push(reference),
        Err(report) => {
            let action =
                format!("publish Vampire failure diagnostic while recording {kind:?}: {summary}");
            return required_artifact_failure_outcome(
                origin, &action, report, references, frontier,
            );
        }
    }
    failure_outcome(origin, kind, detail, references, frontier)
}

fn cancelled_with_captures(
    frontier: Option<FmbSize>,
    process: &ProcessOutput,
    stdout_stage: StagedArtifact,
    stderr_stage: Option<StagedArtifact>,
    policy: VampireCapturePolicy,
    initial_capture_warnings: Vec<String>,
) -> VampireWorkerOutcome {
    let mut references = Vec::new();
    let mut capture_warnings = initial_capture_warnings;
    if policy.retain_full_inconclusive_output && captures_are_complete(process) {
        if let Err(report) = retain_optional_trace(
            stdout_stage,
            "retain cancelled Vampire stdout",
            &mut references,
            &mut capture_warnings,
        ) {
            return VampireWorkerOutcome::RunFailure(report);
        }
        if let Some(stderr_stage) = stderr_stage
            && let Err(report) = retain_optional_trace(
                stderr_stage,
                "retain cancelled Vampire stderr",
                &mut references,
                &mut capture_warnings,
            )
        {
            return VampireWorkerOutcome::RunFailure(report);
        }
    }
    cancelled(frontier, references, capture_warnings)
}

fn retain_optional_trace(
    stage: StagedArtifact,
    action: &str,
    references: &mut Vec<ArtifactRef>,
    warnings: &mut Vec<String>,
) -> Result<(), FailureReport> {
    match stage.commit(ArtifactKind::RuntimeTrace) {
        Ok(reference) => references.push(reference),
        Err(report) if report.scope() == FailureScope::RunGlobal => return Err(report),
        Err(report) => warnings.push(artifact_failure_detail(action, &report)),
    }
    Ok(())
}

fn captures_are_complete(process: &ProcessOutput) -> bool {
    process.stdout.error.is_none() && process.stderr.error.is_none()
}

fn diagnostic_detail(summary: &str, process: Option<&ProcessOutput>) -> String {
    let Some(process) = process else {
        return summary.to_string();
    };
    let mut protocol = process.stdout.protocol.clone();
    protocol.merge(process.stderr.protocol.clone());
    format!(
        "{summary}\nstatus={:?}\ncleanup={}\nprotocol timeout={} invalid-utf8={} overlong={} malformed={}\nstdout bytes seen/staged={}/{}\nstderr bytes seen/staged={}/{}\nstdout capture error={}\nstderr capture error={}\nstdout diagnostic:\n{}\nstderr diagnostic:\n{}",
        process.status,
        process.cleanup_error.as_deref().unwrap_or("none"),
        protocol.timeout_observed(),
        protocol.invalid_utf8_count(),
        protocol.overlong_protocol_line_count(),
        protocol.malformed_protocol_line_count(),
        process.stdout.bytes_seen,
        process.stdout.bytes_staged,
        process.stderr.bytes_seen,
        process.stderr.bytes_staged,
        process.stdout.error.as_deref().unwrap_or("none"),
        process.stderr.error.as_deref().unwrap_or("none"),
        String::from_utf8_lossy(&process.stdout.diagnostic),
        String::from_utf8_lossy(&process.stderr.diagnostic),
    )
}

fn failure_outcome(
    origin: FailureOrigin,
    kind: FailureKind,
    detail: String,
    references: Vec<ArtifactRef>,
    frontier: Option<FmbSize>,
) -> VampireWorkerOutcome {
    let report = FailureReport::try_new(
        origin,
        kind,
        false,
        FailureScope::LaneLocal,
        Some(detail),
        references,
    )
    .expect("Vampire workers use only permitted failure classifications");
    VampireWorkerOutcome::Result(VampireResult::Failure {
        report,
        next_fmb_start_size: frontier,
    })
}

fn run_failure_outcome(origin: FailureOrigin, detail: String) -> VampireWorkerOutcome {
    let report = FailureReport::try_new(
        origin,
        FailureKind::InfrastructureFailure,
        false,
        FailureScope::RunGlobal,
        Some(detail),
        Vec::new(),
    )
    .expect("Vampire cleanup failures use a permitted classification");
    VampireWorkerOutcome::RunFailure(report)
}

fn cancelled(
    frontier: Option<FmbSize>,
    artifact_references: Vec<ArtifactRef>,
    capture_warnings: Vec<String>,
) -> VampireWorkerOutcome {
    VampireWorkerOutcome::Cancelled(CancelledVampireWorker {
        next_fmb_start_size: frontier,
        prior_failure: None,
        artifact_references,
        capture_warnings,
    })
}

fn required_artifact_failure_outcome(
    origin: FailureOrigin,
    action: &str,
    report: FailureReport,
    mut references: Vec<ArtifactRef>,
    frontier: Option<FmbSize>,
) -> VampireWorkerOutcome {
    if report.scope() == FailureScope::RunGlobal {
        return VampireWorkerOutcome::RunFailure(report);
    }

    // Required payload publication is part of the solver result boundary.
    // Preserve its typed artifact classification so an outer race retains the
    // lost-evidence failure whenever no peer independently proves or refutes
    // the exact query.
    if report.origin() == FailureOrigin::ArtifactSettlement
        && matches!(
            report.kind(),
            FailureKind::PublicationFailure | FailureKind::InfrastructureFailure
        )
    {
        for reference in report.artifact_references() {
            if !references.contains(reference) {
                references.push(*reference);
            }
        }
        let report = FailureReport::try_new(
            report.origin(),
            report.kind(),
            report.retryable(),
            report.scope(),
            report.detail().map(str::to_owned),
            references,
        )
        .expect("preserving a valid artifact failure keeps a permitted classification");
        return VampireWorkerOutcome::Result(VampireResult::Failure {
            report,
            next_fmb_start_size: frontier,
        });
    }

    failure_outcome(
        origin,
        FailureKind::InfrastructureFailure,
        artifact_failure_detail(action, &report),
        references,
        frontier,
    )
}

fn artifact_failure_detail(action: &str, report: &FailureReport) -> String {
    match report.detail() {
        Some(detail) => format!("{action}: {detail}"),
        None => action.to_string(),
    }
}

// ------------------------------------------------------------
// Mode Metadata
// ------------------------------------------------------------

fn mode_origin(mode: &VampireWorkerMode) -> FailureOrigin {
    match mode {
        VampireWorkerMode::ProofOnly | VampireWorkerMode::ProofCasc => {
            FailureOrigin::VampireProofSearch
        }
        VampireWorkerMode::FmbOnly(_) => FailureOrigin::VampireFiniteModelBuilding,
    }
}

fn mode_name(mode: &VampireWorkerMode) -> &'static str {
    match mode {
        VampireWorkerMode::ProofOnly => "vampire-proof",
        VampireWorkerMode::ProofCasc => "vampire-proof-casc",
        VampireWorkerMode::FmbOnly(_) => "vampire-fmb",
    }
}

// ------------------------------------------------------------
// Tests
// ------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn proof_mode_rejects_a_status_without_a_complete_proof() {
        let mut summary = ProtocolSummary::default();
        summary.observe(
            super::super::protocol::ProtocolStream::Stdout,
            0,
            super::super::protocol::ProtocolEvent::Status(SzsStatus::Theorem),
        );
        assert!(matches!(
            classify(&VampireWorkerMode::ProofOnly, &summary),
            Conclusion::Malformed
        ));
    }

    #[test]
    fn malformed_stdout_dominates_solver_unknown() {
        let mut summary = ProtocolSummary::default();
        summary.observe(
            super::super::protocol::ProtocolStream::Stdout,
            0,
            super::super::protocol::ProtocolEvent::Malformed(
                super::super::protocol::ProtocolIssue::MalformedSzsLine,
            ),
        );
        assert!(matches!(
            classify(&VampireWorkerMode::ProofOnly, &summary),
            Conclusion::Malformed
        ));
    }

    #[test]
    fn capture_policy_caps_caller_controlled_memory() {
        let policy = VampireCapturePolicy::default()
            .diagnostic_bytes_per_stream(usize::MAX)
            .max_protocol_line_bytes(usize::MAX);
        assert_eq!(policy.diagnostic_bytes_per_stream, MAX_DIAGNOSTIC_BYTES);
        assert_eq!(policy.max_protocol_line_bytes, MAX_PROTOCOL_LINE_BYTES);
    }

    #[test]
    fn required_publication_failure_keeps_its_artifact_classification() {
        let report = FailureReport::artifact(
            FailureKind::PublicationFailure,
            FailureScope::LaneLocal,
            "required proof publication failed",
        );
        let VampireWorkerOutcome::Result(VampireResult::Failure { report, .. }) =
            required_artifact_failure_outcome(
                FailureOrigin::VampireProofSearch,
                "publish complete Vampire proof",
                report,
                Vec::new(),
                None,
            )
        else {
            panic!("required lane-local publication must remain a typed worker failure")
        };
        assert_eq!(report.origin(), FailureOrigin::ArtifactSettlement);
        assert_eq!(report.kind(), FailureKind::PublicationFailure);
        assert_eq!(report.scope(), FailureScope::LaneLocal);
    }
}
