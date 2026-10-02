//! Bounded admission of untrusted AgentHoudini responses.
//!
//! The provider sees only an immutable serialized request. Rust validates the
//! outer response protocol and accounting, while Lean remains the authority
//! for clauses and source instances. No value is published to the Houdini
//! state in this module.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::panic::{AssertUnwindSafe, catch_unwind, resume_unwind};
use std::sync::Arc;
use std::task::Poll;

use serde_json::{Value, json};

use crate::encoding::{bytes_sha256, canonical_value_sha256};
use crate::failure::{FailureKind, FailureOrigin, FailureReport, FailureScope};
use crate::houdini::ClauseId;
use crate::proposer_api::{ProposerCleanupError, ProposerTerminalFailure, wire::ShutdownReason};
use crate::runtime::{CancellationToken, SolverAdmission};
use crate::task::SynthesisTask;

#[cfg(test)]
use super::transcript::ResponseChunkAccounting;
pub use crate::proposer_api::{
    AgentProvider, AgentPush, AgentResponseLimitExceeded, AgentResponseWriter,
    AgentSourceCancellation, AgentSourceCleanupFuture, AgentSourceFuture, AgentSourceOutcome,
};

use super::admission::{FrameworkIIAdmissionContext, FrameworkIIAdmissionError};
use super::catalog::FrameworkIIStateError;
use super::feedback::{
    AgentClauseDropReference, AgentClauseIdentity, AgentFeedback, PreCertificateAgentHoudiniState,
};
use super::host_limits::{HOST_LIMIT_CODE, HostLimitRefusal};
use super::ledger::FrameworkIIDeadReason;
use super::production::FrameworkIIQueryChecker;
use super::proposal::{FrameworkIIProposalDrop, FrameworkIIProposalEpoch};
use super::solver::FrameworkIISolverContext;
use super::stabilization::LeveledHoudiniState;
use super::strict_json::{StrictJsonError, decode_strict_json};
use super::tools::{AgentToolDispatcher, AgentToolPolicy, AgentToolResources};
use super::transcript::{
    TranscriptCoordinates, TranscriptEvent, TranscriptLifecycle, TranscriptRecorder,
    TranscriptStream,
};
use super::types::{AdmissionCorrection, AdmissionOutcome, ExtendedClause, FrameworkIILevel};

use crate::proposer_api::proposals::{
    RawAgentHoudiniResponse, RawClauseIdentity, RawDropReference, RawResponseBinding,
};
pub(crate) use crate::proposer_api::version::AGENT_HOUDINI_PROTOCOL_VERSION;
const MAXIMUM_AGENT_POLICY_BYTES: usize = 64 * 1024 * 1024;
const MAXIMUM_AGENT_POLICY_ITEMS: usize = 1_000_000;
const MAXIMUM_ATTEMPT_HISTORY_RECORDS: usize = 1_000_000;
const MAXIMUM_TRANSPORT_RETRIES: usize = 8;
const MAXIMUM_CONSULTATIONS: usize = 65_536;
const MAXIMUM_CORRECTION_TEXT_BYTES: usize = 4 * 1024;
const MINIMUM_CORRECTION_BYTES: usize = 4 * 1024;

// ------------------------------------------------------------
// Validated Consultation Policy
// ------------------------------------------------------------

/// Safety guards for response framing, correction, and request accounting.
///
/// Nothing here bounds what the proposer may propose. Every limit that does
/// — the proposal size, the clause-text size, the drop count, the reply
/// size, the catalog size, the level bound — lives in [`HostLimits`] on the
/// feedback policy, is absent by default, and is stated to the proposer in
/// the standing presentation when set.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgentConsultationLimits {
    /// Byte bound on the push this host itself serializes. The host builds
    /// the document, so this is a self-consistency guard on the run's own
    /// memory, not a limit on the proposer, and exceeding it is a resource
    /// fault.
    pub max_request_bytes: usize,
    /// How many diagnostics one correction carries, and how many bytes it
    /// occupies. The contract states the correction carries "a bounded
    /// number of diagnostics"; this is the host's own message, never a
    /// limit on what the proposer may send.
    pub max_correction_diagnostics: usize,
    pub max_correction_bytes: usize,
    /// Memory bound on the retained attempt history for the whole run.
    ///
    /// This is one of the three safety guards the fixed-ambient path keeps
    /// (`houdini.tex` Section 4.7, "Resource limits"), and the only one that
    /// lives here:
    ///
    /// 1. **Deadlines** — the run deadline, the optional consultation
    ///    deadline, and the call-local `validate_counterexample` timeout
    ///    (`search.rs`). An expiry ends the bounded operation as a failure.
    /// 2. **Generated file space** — when configured, the artifact store
    ///    charges staged payload streams before writes. Direct generated
    ///    certificate files instead fall under sampled campaign workspace
    ///    checks, which are not a hard filesystem quota.
    /// 3. **Retained buffers** — this bound caps retained attempt rows;
    ///    host document and transport byte bounds constrain their specific
    ///    buffers (`max_request_bytes` here, `max_feedback_bytes` on the
    ///    feedback policy, and `MAX_ENCODING_FRAME_BYTES` on transport).
    ///    These guards do not bound total process memory or RSS.
    ///
    /// The feedback policy keeps no second bound on the ledger's length.
    /// This is the configured cap on retained attempt-history records,
    /// not a bound on all other allocations in a long run.
    ///
    /// A guard's failure is a resource fault — here `SourceExhausted`, which
    /// ends the run — never a correction and never a verdict on a proposal.
    /// It is not a correction allowance either: corrections within one
    /// consultation are unlimited, because a rejected submission changes no
    /// state, and the deadlines are what bound a looping provider.
    pub max_attempt_history_records: usize,
    pub max_transport_retries_per_request: usize,
    /// Optional bound on the number of consultations one run may hold.
    /// `None` — the default — means the run deadline and the optional
    /// consultation deadline are the only guards, which is what the
    /// contract states; exhausting a bound that is set is a resource fault.
    pub max_consultations: Option<usize>,
}

impl Default for AgentConsultationLimits {
    fn default() -> Self {
        Self {
            max_request_bytes: 9 * 1024 * 1024,
            max_correction_diagnostics: 64,
            max_correction_bytes: 256 * 1024,
            max_attempt_history_records: MAXIMUM_ATTEMPT_HISTORY_RECORDS,
            max_transport_retries_per_request: 0,
            max_consultations: None,
        }
    }
}

/// A checked policy with a stable nonsemantic digest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgentConsultationPolicy {
    limits: AgentConsultationLimits,
    digest: Arc<str>,
    maximum_history_records: usize,
}

impl AgentConsultationPolicy {
    /// Checked request limits, independent of the proposer's conversation policy.
    pub fn new(limits: AgentConsultationLimits) -> Result<Self, AgentConsultationPolicyError> {
        let byte_limits = [limits.max_request_bytes, limits.max_correction_bytes];
        if byte_limits.contains(&0)
            || byte_limits
                .iter()
                .any(|limit| *limit > MAXIMUM_AGENT_POLICY_BYTES)
            || limits.max_correction_bytes < MINIMUM_CORRECTION_BYTES
            || limits.max_correction_bytes > limits.max_request_bytes
        {
            return Err(AgentConsultationPolicyError::InvalidByteLimits);
        }
        if limits.max_correction_diagnostics == 0
            || limits.max_correction_diagnostics > MAXIMUM_AGENT_POLICY_ITEMS
            || limits
                .max_consultations
                .is_some_and(|limit| limit == 0 || limit > MAXIMUM_CONSULTATIONS)
            || !(1..=MAXIMUM_ATTEMPT_HISTORY_RECORDS).contains(&limits.max_attempt_history_records)
            || limits.max_transport_retries_per_request > MAXIMUM_TRANSPORT_RETRIES
        {
            return Err(AgentConsultationPolicyError::InvalidItemLimits);
        }
        let maximum_history_records = limits.max_attempt_history_records;
        let fields = json!({
            "domain": "whiel-proposer-request-policy-v1",
            "max_request_bytes": limits.max_request_bytes,
            "max_correction_diagnostics": limits.max_correction_diagnostics,
            "max_correction_bytes": limits.max_correction_bytes,
            "max_attempt_history_records": limits.max_attempt_history_records,
            "max_transport_retries_per_request": limits.max_transport_retries_per_request,
            "max_consultations": limits.max_consultations,
        });
        Ok(Self {
            limits,
            digest: Arc::from(canonical_value_sha256(&fields)),
            maximum_history_records,
        })
    }

    pub fn limits(&self) -> &AgentConsultationLimits {
        &self.limits
    }

    pub fn digest(&self) -> &str {
        &self.digest
    }

    pub fn maximum_history_records(&self) -> usize {
        self.maximum_history_records
    }
}

impl Default for AgentConsultationPolicy {
    fn default() -> Self {
        Self::new(AgentConsultationLimits::default())
            .expect("the built-in AgentHoudini consultation limits are valid")
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AgentConsultationPolicyError {
    InvalidByteLimits,
    InvalidItemLimits,
    ArithmeticOverflow,
}

impl fmt::Display for AgentConsultationPolicyError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidByteLimits => {
                formatter.write_str("AgentHoudini byte limits are inconsistent or out of range")
            }
            Self::InvalidItemLimits => {
                formatter.write_str("AgentHoudini item limits are inconsistent or out of range")
            }
            Self::ArithmeticOverflow => {
                formatter.write_str("AgentHoudini policy accounting overflowed")
            }
        }
    }
}

impl std::error::Error for AgentConsultationPolicyError {}

// ------------------------------------------------------------
// Serialized Provider Boundary
// ------------------------------------------------------------

#[derive(Clone)]
pub(super) struct AgentRequestAuthority {
    pub(super) feedback: Arc<AgentFeedback>,
    pub(super) validation_ordinal: usize,
}

impl AgentPush {
    pub(super) fn replay_feedback(
        &self,
    ) -> Result<&AgentFeedback, super::replay_correspondence::ReplayCaptureError> {
        Ok(&self.authority.feedback)
    }
    pub(super) fn replay_policy(&self) -> &AgentConsultationPolicy {
        &self.replay_policy
    }
}

/// Exact bounded bytes returned for one exact provider request.
#[derive(Clone)]
pub struct AgentHoudiniResponse {
    bytes: Arc<[u8]>,
    digest: Arc<str>,
    request_digest: Arc<str>,
    authority: Arc<AgentRequestAuthority>,
}

impl AgentHoudiniResponse {
    fn capture(bytes: Vec<u8>, request: &AgentPush) -> Self {
        Self {
            digest: Arc::from(bytes_sha256(&bytes)),
            bytes: bytes.into(),
            request_digest: Arc::clone(&request.digest),
            authority: Arc::clone(&request.authority),
        }
    }

    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }

    pub fn digest(&self) -> &str {
        &self.digest
    }

    pub fn request_digest(&self) -> &str {
        &self.request_digest
    }

    pub fn consultation_digest(&self) -> &str {
        self.authority.feedback.consultation_digest()
    }
}

impl fmt::Debug for AgentHoudiniResponse {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("AgentHoudiniResponse")
            .field("digest", &self.digest)
            .field("request_digest", &self.request_digest)
            .field("encoded_bytes", &self.bytes.len())
            .finish_non_exhaustive()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgentCorrectionDiagnostic {
    code: Arc<str>,
    message: Arc<str>,
    item_index: Option<usize>,
    path: Option<Arc<str>>,
    /// Where in the clause text the failure was found, when the admission
    /// diagnostic that produced this one located it. `item_index` says which
    /// clause of the submission; this says where inside it, which is the
    /// difference between rewriting a clause and reading it.
    offset: Option<usize>,
    /// Present exactly on a `host_limit` diagnostic: `{limit, value,
    /// observed}`, naming which of the run's optional limits refused the
    /// submission. Absent on every diagnostic that reports a real defect.
    ///
    /// Boxed, with `details`, to keep one diagnostic small enough to travel in
    /// an ordinary `Result` error.
    host_limit: Option<Box<Value>>,
    /// Present on a diagnostic that can say exactly which keys were wrong:
    /// `{missing, unexpected, changed}`, each a sorted list of key names at
    /// `path`. A proposer that copied the wrong object gets the three lists
    /// rather than a sentence it cannot act on.
    details: Option<Box<Value>>,
}

impl AgentCorrectionDiagnostic {
    pub fn code(&self) -> &str {
        &self.code
    }

    pub fn message(&self) -> &str {
        &self.message
    }

    pub fn item_index(&self) -> Option<usize> {
        self.item_index
    }

    pub fn path(&self) -> Option<&str> {
        self.path.as_deref()
    }

    /// The position in the clause text the admission diagnostic located.
    pub fn offset(&self) -> Option<usize> {
        self.offset
    }

    /// The `{limit, value, observed}` object of a `host_limit` diagnostic.
    pub fn host_limit(&self) -> Option<&Value> {
        self.host_limit.as_deref()
    }

    /// The `{missing, unexpected, changed}` key lists, when the diagnostic
    /// can name them.
    pub fn details(&self) -> Option<&Value> {
        self.details.as_deref()
    }

    fn wire_value(&self) -> Value {
        let mut value = json!({
            "code": self.code.as_ref(),
            "message": self.message.as_ref(),
            "item_index": self.item_index,
            "path": self.path.as_deref(),
        });
        if let Some(offset) = self.offset {
            value
                .as_object_mut()
                .expect("a diagnostic wire value is an object")
                .insert("offset".to_string(), json!(offset));
        }
        if let Some(host_limit) = &self.host_limit {
            value
                .as_object_mut()
                .expect("a diagnostic wire value is an object")
                .insert("host_limit".to_string(), (**host_limit).clone());
        }
        if let Some(details) = &self.details {
            value
                .as_object_mut()
                .expect("a diagnostic wire value is an object")
                .insert("details".to_string(), (**details).clone());
        }
        value
    }
}

/// One sanitized correction bound to the immediately rejected response.
#[derive(Clone)]
pub struct AgentHoudiniCorrection {
    consultation_digest: Arc<str>,
    rejected_response_digest: Arc<str>,
    correction_ordinal: usize,
    diagnostics: Arc<[AgentCorrectionDiagnostic]>,
    wire: Arc<Value>,
    encoded_bytes: usize,
}

impl AgentHoudiniCorrection {
    pub fn consultation_digest(&self) -> &str {
        &self.consultation_digest
    }

    pub fn rejected_response_digest(&self) -> &str {
        &self.rejected_response_digest
    }

    pub fn correction_ordinal(&self) -> usize {
        self.correction_ordinal
    }

    pub fn diagnostics(&self) -> &[AgentCorrectionDiagnostic] {
        &self.diagnostics
    }

    pub fn encoded_bytes(&self) -> usize {
        self.encoded_bytes
    }

    fn wire_value(&self) -> &Value {
        &self.wire
    }
}

impl fmt::Debug for AgentHoudiniCorrection {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("AgentHoudiniCorrection")
            .field("consultation_digest", &self.consultation_digest)
            .field("rejected_response_digest", &self.rejected_response_digest)
            .field("correction_ordinal", &self.correction_ordinal)
            .field("diagnostic_count", &self.diagnostics.len())
            .field("encoded_bytes", &self.encoded_bytes)
            .finish_non_exhaustive()
    }
}

// ------------------------------------------------------------
// Exact Attempt History
// ------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AgentRequestAttemptOutcome {
    Received,
    Accepted,
    Correctable,
    ValidationFailure,
    OversizedResponse,
    SourceExhausted,
    NoResponse,
    TransportFailure,
    SourceProtocolFailure,
    Cancelled,
    RecordingFailure,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgentHoudiniAttempt {
    consultation_digest: Arc<str>,
    request_digest: Arc<str>,
    validation_ordinal: usize,
    transport_ordinal: usize,
    response_digest: Option<Arc<str>>,
    outcome: AgentRequestAttemptOutcome,
    same_request_retry: bool,
}

impl AgentHoudiniAttempt {
    pub fn consultation_digest(&self) -> &str {
        &self.consultation_digest
    }

    pub fn request_digest(&self) -> &str {
        &self.request_digest
    }

    pub fn validation_ordinal(&self) -> usize {
        self.validation_ordinal
    }

    pub fn transport_ordinal(&self) -> usize {
        self.transport_ordinal
    }

    pub fn response_digest(&self) -> Option<&str> {
        self.response_digest.as_deref()
    }

    pub fn outcome(&self) -> AgentRequestAttemptOutcome {
        self.outcome
    }

    pub fn same_request_retry(&self) -> bool {
        self.same_request_retry
    }
}

// ------------------------------------------------------------
// Admitted Proposals
// ------------------------------------------------------------

/// A fully admitted proposal or typed consultation failure.
#[derive(Clone, Debug)]
pub enum HoudiniProposal {
    CandidateClauses(Box<FrameworkIIProposalEpoch>),
    /// One counterexample submission, returned to the search loop unapplied
    /// (agent report, Alg. Session: "If r is a counterexample input: return
    /// r"). No clause is admitted and no epoch runs; the search loop
    /// validates the instance in Lean.
    CandidateCounterexample(Box<AgentCounterexampleProposal>),
    Failure(FailureReport),
}

/// The exact consultation one submission was bound to.
///
/// These are the controller's own digests, taken from the feedback that built
/// the push, never the agent's echo of them: the echo has already been
/// compared against these by [`validate_outer_binding`] before this is built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgentConsultationBinding {
    task_digest: Arc<str>,
    scope_digest: Arc<str>,
    run_digest: Arc<str>,
    consultation_digest: Arc<str>,
    state_snapshot_digest: Arc<str>,
    validation_manifest_digest: Arc<str>,
    request_digest: Arc<str>,
    validation_ordinal: usize,
}

impl AgentConsultationBinding {
    fn from_response(response: &AgentHoudiniResponse) -> Self {
        let feedback = &response.authority.feedback;
        Self {
            task_digest: Arc::from(feedback.task_digest()),
            scope_digest: Arc::from(feedback.scope_digest()),
            run_digest: Arc::from(feedback.run_digest()),
            consultation_digest: Arc::from(feedback.consultation_digest()),
            state_snapshot_digest: Arc::from(feedback.state_snapshot_digest()),
            validation_manifest_digest: Arc::from(feedback.validation_manifest_digest()),
            request_digest: Arc::clone(&response.request_digest),
            validation_ordinal: response.authority.validation_ordinal,
        }
    }

    pub fn task_digest(&self) -> &str {
        &self.task_digest
    }

    pub fn scope_digest(&self) -> &str {
        &self.scope_digest
    }

    pub fn run_digest(&self) -> &str {
        &self.run_digest
    }

    pub fn consultation_digest(&self) -> &str {
        &self.consultation_digest
    }

    pub fn state_snapshot_digest(&self) -> &str {
        &self.state_snapshot_digest
    }

    pub fn validation_manifest_digest(&self) -> &str {
        &self.validation_manifest_digest
    }

    pub fn request_digest(&self) -> &str {
        &self.request_digest
    }

    pub fn validation_ordinal(&self) -> usize {
        self.validation_ordinal
    }

    /// Rebuild a binding from an already persisted durable record.
    ///
    /// Crate-internal, and provenance only: a rebuilt binding is recorded
    /// beside a counterexample so a reader can see which consultation
    /// submitted it. It grants nothing, is never used to authorize a push
    /// or a response, and every live value still comes from
    /// [`Self::from_response`], which reads the controller's own feedback
    /// rather than the agent's echo of it.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn from_parts(
        task_digest: impl Into<Arc<str>>,
        scope_digest: impl Into<Arc<str>>,
        run_digest: impl Into<Arc<str>>,
        consultation_digest: impl Into<Arc<str>>,
        state_snapshot_digest: impl Into<Arc<str>>,
        validation_manifest_digest: impl Into<Arc<str>>,
        request_digest: impl Into<Arc<str>>,
        validation_ordinal: usize,
    ) -> Self {
        Self {
            task_digest: task_digest.into(),
            scope_digest: scope_digest.into(),
            run_digest: run_digest.into(),
            consultation_digest: consultation_digest.into(),
            state_snapshot_digest: state_snapshot_digest.into(),
            validation_manifest_digest: validation_manifest_digest.into(),
            request_digest: request_digest.into(),
            validation_ordinal,
        }
    }

    /// Build a binding directly. Test-only: every production value comes
    /// from [`Self::from_response`], which reads the controller's own
    /// feedback rather than the agent's echo of it.
    #[cfg(test)]
    pub(crate) fn for_test(consultation_digest: &str, validation_ordinal: usize) -> Self {
        Self {
            task_digest: Arc::from("0".repeat(64)),
            scope_digest: Arc::from("1".repeat(64)),
            run_digest: Arc::from("2".repeat(64)),
            consultation_digest: Arc::from(consultation_digest),
            state_snapshot_digest: Arc::from("3".repeat(64)),
            validation_manifest_digest: Arc::from("4".repeat(64)),
            request_digest: Arc::from("5".repeat(64)),
            validation_ordinal,
        }
    }
}

/// One counterexample submission on its way to the search loop.
///
/// The instance is opaque: `input` is exactly the JSON value the provider
/// submitted, and nothing between here and the Lean `validate_counterexample`
/// worker call reads it.
#[derive(Clone, Debug)]
pub struct AgentCounterexampleProposal {
    input: Value,
    binding: AgentConsultationBinding,
}

impl AgentCounterexampleProposal {
    /// The agent's own instance JSON, untouched.
    pub fn input(&self) -> &Value {
        &self.input
    }

    pub fn binding(&self) -> &AgentConsultationBinding {
        &self.binding
    }

    /// Consume this proposal into its opaque instance and its binding.
    pub fn into_parts(self) -> (Value, AgentConsultationBinding) {
        (self.input, self.binding)
    }
}

/// Out-of-band cancellation; no partial typed proposal accompanies it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AgentConsultationCancelled;

/// Content/infrastructure result of validating one bounded response.
#[derive(Clone, Debug)]
pub enum AgentResponseValidation {
    Accepted(HoudiniProposal),
    Correctable(AgentHoudiniCorrection),
    Failure(FailureReport),
}

/// Runtime-only authorities used by response validation.
///
/// `feedback_state` and `query` (Pass 7.5c) are the dispatcher's own read
/// access to the ledger/houdini state view and the production checker's
/// semantic dictionary: threaded here so [`Agent::get_houdini_proposal`] can
/// hand them to the tool surface it serves during one consultation the same
/// way it already hands the surface `state`'s tool policy and proposal
/// revision. `query` is `None` only where no checker exists at all (a
/// consultation exercised purely at the clause-admission boundary, with no
/// search loop and hence no dictionary to query); every real search binds a
/// production checker and therefore always supplies `Some`.
pub struct AgentResponseValidator<'a> {
    task: &'a SynthesisTask,
    state: &'a LeveledHoudiniState,
    admission: &'a FrameworkIIAdmissionContext,
    solver: &'a FrameworkIISolverContext,
    solver_admission: &'a SolverAdmission,
    feedback_state: &'a PreCertificateAgentHoudiniState,
    query: Option<&'a dyn FrameworkIIQueryChecker>,
}

impl<'a> AgentResponseValidator<'a> {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        task: &'a SynthesisTask,
        state: &'a LeveledHoudiniState,
        admission: &'a FrameworkIIAdmissionContext,
        solver: &'a FrameworkIISolverContext,
        solver_admission: &'a SolverAdmission,
        feedback_state: &'a PreCertificateAgentHoudiniState,
        query: Option<&'a dyn FrameworkIIQueryChecker>,
    ) -> Self {
        Self {
            task,
            state,
            admission,
            solver,
            solver_admission,
            feedback_state,
            query,
        }
    }
}

// ------------------------------------------------------------
// Strict Raw Response Grammar
// ------------------------------------------------------------

// ------------------------------------------------------------
// Provider Push And Correction Construction
// ------------------------------------------------------------

/// Build one Pass 7.5c consultation-session push: the outer binding (the
/// same eight fields the pre-session request carried), the standing
/// session content from [`AgentFeedback::push_value`] (never `summary`, the
/// paged `clauses` list, or the paged `ledger` rows), and any optional
/// correction. `feedback.to_json_value()` is not reachable from this path.
fn build_push(
    feedback: &AgentFeedback,
    correction: Option<&AgentHoudiniCorrection>,
    validation_ordinal: usize,
    policy: &AgentConsultationPolicy,
    tool_policy: &AgentToolPolicy,
    state_revision: u64,
) -> Result<AgentPush, FailureReport> {
    if correction.is_some_and(|correction| {
        correction.consultation_digest() != feedback.consultation_digest()
            || correction.correction_ordinal() != validation_ordinal
    }) {
        return Err(validation_failure(
            "correction authority is detached from its consultation request",
        ));
    }
    let enabled_tools = tool_policy.enabled_names();
    let value = json!({
        "schema_version": AGENT_HOUDINI_PROTOCOL_VERSION,
        "operation": "proposer_observation",
        "binding": {
            "task_digest": feedback.task_digest(),
            "scope_digest": feedback.scope_digest(),
            "run_digest": feedback.run_digest(),
            "consultation_digest": feedback.consultation_digest(),
            "state_snapshot_digest": feedback.state_snapshot_digest(),
            "validation_manifest_digest": feedback.validation_manifest_digest(),
            "validation_ordinal": validation_ordinal,
            "policy_digest": policy.digest(),
        },
        "feedback": feedback.push_value(&enabled_tools, state_revision),
        "correction": correction.map(AgentHoudiniCorrection::wire_value),
    });
    let bytes = serde_json::to_vec(&value)
        .map_err(|_| validation_failure("serialize the bounded AgentHoudini provider push"))?;
    if bytes.len() > policy.limits.max_request_bytes {
        // A memory guard on the document *this host* built, so it is a
        // resource fault that ends the run, never a lane-local consultation
        // failure the search could hold another consultation after: the next
        // push would be built from the same state and be the same size, and
        // the search would re-enter this branch until the run deadline
        // (Milestone 7.5 review, finding 7).
        return Err(resource_fault(
            "the AgentHoudini provider push exceeds the run's request-size memory guard",
        ));
    }
    let observation = serde_json::from_value(value).map_err(|error| {
        validation_failure(&format!("construct typed proposer observation: {error}"))
    })?;
    Ok(AgentPush {
        replay_policy: policy.clone(),
        request_deadline: None,
        observation: Arc::new(observation),
        negotiated_api: crate::proposer_api::NegotiatedApi {
            version: crate::proposer_api::API_VERSION.into(),
            operations: enabled_tools.iter().map(|name| (*name).into()).collect(),
        },
        digest: Arc::from(bytes_sha256(&bytes)),
        bytes: bytes.into(),
        authority: Arc::new(AgentRequestAuthority {
            feedback: Arc::new(feedback.clone()),
            validation_ordinal,
        }),
    })
}

fn make_correction(
    feedback: &AgentFeedback,
    rejected_response_digest: impl Into<Arc<str>>,
    correction_ordinal: usize,
    diagnostics: impl IntoIterator<Item = AgentCorrectionDiagnostic>,
    policy: &AgentConsultationPolicy,
) -> AgentHoudiniCorrection {
    let rejected_response_digest = rejected_response_digest.into();
    let mut diagnostics = diagnostics
        .into_iter()
        .take(policy.limits.max_correction_diagnostics)
        .collect::<Vec<_>>();
    if diagnostics.is_empty() {
        diagnostics.push(fixed_diagnostic(
            "invalid_response",
            "The response is not admissible; submit one corrected response.",
        ));
    }
    for diagnostic in &mut diagnostics {
        diagnostic.code = Arc::from(bound_text(&diagnostic.code, 128, "invalid_response"));
        diagnostic.message = Arc::from(bound_text(
            &diagnostic.message,
            MAXIMUM_CORRECTION_TEXT_BYTES,
            "The response is not admissible.",
        ));
        diagnostic.path = diagnostic
            .path
            .as_deref()
            .map(|path| Arc::from(bound_text(path, 1024, "/response")));
    }
    loop {
        let wire = correction_wire(
            feedback.consultation_digest(),
            &rejected_response_digest,
            correction_ordinal,
            &diagnostics,
        );
        let encoded_bytes = serde_json::to_vec(&wire)
            .expect("a sanitized correction always serializes")
            .len();
        if encoded_bytes <= policy.limits.max_correction_bytes {
            return AgentHoudiniCorrection {
                consultation_digest: Arc::from(feedback.consultation_digest()),
                rejected_response_digest,
                correction_ordinal,
                diagnostics: diagnostics.into(),
                wire: Arc::new(wire),
                encoded_bytes,
            };
        }
        if diagnostics.len() > 1 {
            diagnostics.pop();
            continue;
        }
        diagnostics[0].message = Arc::from("The response is not admissible.");
        diagnostics[0].path = None;
    }
}

fn correction_wire(
    consultation_digest: &str,
    rejected_response_digest: &str,
    correction_ordinal: usize,
    diagnostics: &[AgentCorrectionDiagnostic],
) -> Value {
    json!({
        "schema_version": AGENT_HOUDINI_PROTOCOL_VERSION,
        "binding": {
            "consultation_digest": consultation_digest,
            "rejected_response_digest": rejected_response_digest,
            "correction_ordinal": correction_ordinal,
        },
        "diagnostics": diagnostics
            .iter()
            .map(AgentCorrectionDiagnostic::wire_value)
            .collect::<Vec<_>>(),
    })
}

fn fixed_diagnostic(code: &'static str, message: &'static str) -> AgentCorrectionDiagnostic {
    AgentCorrectionDiagnostic {
        code: Arc::from(code),
        message: Arc::from(message),
        item_index: None,
        path: None,
        offset: None,
        host_limit: None,
        details: None,
    }
}

/// Longest dead formula echoed back in its own refusal. The text is the
/// proposer's own submission, so echoing it leaks nothing; a clause longer
/// than this is named by its opening instead of crowding out the reason.
const MAX_DEAD_CLAUSE_BYTES: usize = 512;

/// A resubmission of a formula that is already permanently dead.
///
/// The formula is named: a proposer keeps no transcript of its own responses,
/// and a dead clause is in none of the three live partitions the push shows,
/// so "propose different content" without saying which content is advice it
/// cannot act on. The text is the one it submitted.
fn dead_clause_diagnostic(
    reason: FrameworkIIDeadReason,
    source: &str,
) -> AgentCorrectionDiagnostic {
    let named = bound_text(source, MAX_DEAD_CLAUSE_BYTES, "the formula you resubmitted");
    AgentCorrectionDiagnostic {
        code: Arc::from("dead_clause_rejected"),
        message: Arc::from(format!(
            "This exact formula is permanently dead and cannot be resubmitted: {named} ({reason})."
        )),
        item_index: None,
        path: None,
        offset: None,
        host_limit: None,
        details: None,
    }
}

/// The one correction a host limit ever produces (`agent_houdini.tex`,
/// "Actions"): the code is always `host_limit`, and the payload names which
/// limit, its value, and what was observed. It is never a defect of the
/// proposal, and there is no per-limit code.
fn host_limit_diagnostic(refusal: &HostLimitRefusal) -> AgentCorrectionDiagnostic {
    AgentCorrectionDiagnostic {
        code: Arc::from(HOST_LIMIT_CODE),
        message: Arc::from(refusal.message()),
        item_index: None,
        path: None,
        offset: None,
        host_limit: Some(Box::new(refusal.wire_value())),
        details: None,
    }
}

fn bound_text<'a>(text: &'a str, maximum: usize, fallback: &'a str) -> &'a str {
    if text.is_empty() {
        return fallback;
    }
    if text.len() <= maximum {
        return text;
    }
    let mut boundary = maximum;
    while !text.is_char_boundary(boundary) {
        boundary -= 1;
    }
    &text[..boundary]
}

fn admission_diagnostics(correction: &AdmissionCorrection) -> Vec<AgentCorrectionDiagnostic> {
    correction
        .diagnostics()
        .iter()
        .map(|diagnostic| AgentCorrectionDiagnostic {
            code: Arc::from(diagnostic.code()),
            message: Arc::from(diagnostic.message()),
            item_index: diagnostic.item_index(),
            path: diagnostic.path().map(Arc::from),
            // Lean locates every lexical and syntax failure. The tool path
            // has always carried that position; the submission path dropped
            // it, leaving `item_index` to name a clause the proposer has no
            // copy of and nothing to say where inside it to look.
            offset: diagnostic.offset(),
            host_limit: None,
            details: None,
        })
        .collect()
}

// ------------------------------------------------------------
// Provider-Neutral Agent And Bounded Correction Loop
// ------------------------------------------------------------

enum AgentRequestAdmission {
    Response {
        response: AgentHoudiniResponse,
        attempt_index: usize,
    },
    Oversized {
        digest: Arc<str>,
        found: usize,
        limit: usize,
    },
    SourceExhausted,
    NoResponse,
    TransportFailure,
    SourceProtocolFailure,
    Cancelled,
    RecordingFailure,
    CleanupFailure(ProposerCleanupError),
    EndpointFailure(ProposerTerminalFailure),
    ResourceFailure(String),
}

/// Stateful provider wrapper with serialized source and attempt history.
pub struct Agent<S> {
    source: S,
    cleanup_failure: Option<ProposerCleanupError>,
    shutdown_joined: bool,
    shutdown_resource_failure: Option<String>,
    request_deadline: Option<tokio::time::Instant>,
    policy: AgentConsultationPolicy,
    attempts: Vec<AgentHoudiniAttempt>,
    consultations: BTreeSet<Arc<str>>,
    recorder: Option<TranscriptRecorder>,
}

impl<S> Agent<S> {
    pub(crate) fn shutdown_failure(&self) -> Option<FailureReport> {
        self.cleanup_failure
            .map(cleanup_failure)
            .or_else(|| self.shutdown_resource_failure.as_ref().map(resource_fault))
    }

    /// The consultation policy this agent applies.
    ///
    /// Deliberately readable without the provider bound: the run
    /// configuration binds to the artifact store's run identity; search is
    /// generic in its provider.
    pub fn policy(&self) -> &AgentConsultationPolicy {
        &self.policy
    }

    /// The run's transport attempts against its proposer.
    ///
    /// Readable without the provider bound for the same reason the policy
    /// is: publishing a run's own history is bookkeeping over rows this
    /// agent already holds, not a consultation.
    pub fn attempt_history(&self) -> &[AgentHoudiniAttempt] {
        &self.attempts
    }
}

impl<S: AgentProvider> Agent<S> {
    pub fn new(source: S, policy: AgentConsultationPolicy) -> Self {
        Self {
            source,
            cleanup_failure: None,
            shutdown_joined: false,
            shutdown_resource_failure: None,
            request_deadline: None,
            policy,
            attempts: Vec::new(),
            consultations: BTreeSet::new(),
            recorder: None,
        }
    }

    pub(crate) fn with_recorder(mut self, recorder: TranscriptRecorder) -> Self {
        self.recorder = Some(recorder);
        self
    }

    pub fn with_default_policy(source: S) -> Self {
        Self::new(source, AgentConsultationPolicy::default())
    }

    pub(super) fn record_replay_final(
        &self,
        state: &super::LeveledHoudiniState,
        feedback: &super::PreCertificateAgentHoudiniState,
        outcome: Result<
            super::replay_correspondence::ReplayFinalOutcome,
            super::ReplayCaptureError,
        >,
    ) {
        if let Some(recorder) = &self.recorder {
            recorder.final_owner(outcome.and_then(|outcome| {
                feedback.replay_final_state_owner(state, &self.policy, outcome)
            }));
        }
    }
    pub(super) fn replay_recorder(&self) -> Option<TranscriptRecorder> {
        self.recorder.clone()
    }

    pub(crate) fn set_request_deadline(&mut self, deadline: Option<tokio::time::Instant>) {
        self.request_deadline = deadline;
    }

    /// Terminal endpoint cleanup is distinct from request quiescence. A failed
    /// cleanup remains latched even if a later redundant shutdown succeeds.
    pub(crate) async fn shutdown(&mut self, reason: ShutdownReason) {
        if self.shutdown_joined {
            return;
        }
        match self.source.shutdown(reason).await {
            Ok(()) => {
                self.shutdown_joined = true;
                if let Some(recorder) = &self.recorder {
                    recorder.lifecycle(TranscriptLifecycle::CleanupJoined);
                }
            }
            Err(error) => {
                self.cleanup_failure.get_or_insert(error);
            }
        }
        // Shutdown itself uses the API budget. Successful fallback cleanup does
        // not erase a resource fault first raised by its final control packet.
        // Real cleanup failure retains priority in shutdown_failure().
        if let Some(detail) = self.source.resource_failure() {
            self.shutdown_resource_failure.get_or_insert(detail);
        }
    }

    /// Reclassify a candidate which completed validation only after the
    /// consultation deadline had taken ownership of the result.
    ///
    /// Candidate proposals must correspond to the exact last accepted attempt.
    /// For a failure proposal, reclassify only a terminal attempt belonging to
    /// this consultation; correction steps remain exact history, while failures
    /// raised before a request legitimately have no current attempt. Returning
    /// `false` exposes an internal accounting defect to the search coordinator
    /// instead of rewriting unrelated history.
    pub(crate) fn discard_completed_proposal(
        &mut self,
        consultation_digest: &str,
        proposal: &HoudiniProposal,
    ) -> bool {
        let last_for_consultation = self
            .attempts
            .last_mut()
            .filter(|attempt| attempt.consultation_digest.as_ref() == consultation_digest);
        match (proposal, last_for_consultation) {
            (
                HoudiniProposal::CandidateClauses(_) | HoudiniProposal::CandidateCounterexample(_),
                Some(attempt),
            ) if attempt.outcome == AgentRequestAttemptOutcome::Accepted => {
                attempt.outcome = AgentRequestAttemptOutcome::Cancelled;
                if let Some(recorder) = &self.recorder {
                    recorder.record(TranscriptEvent::Outcome {
                        coordinates: recorder.current_coordinates(),
                        outcome: AgentRequestAttemptOutcome::Cancelled.into(),
                    });
                }
                true
            }
            (HoudiniProposal::Failure(_), Some(attempt))
                if matches!(
                    attempt.outcome,
                    AgentRequestAttemptOutcome::ValidationFailure
                        | AgentRequestAttemptOutcome::SourceExhausted
                        | AgentRequestAttemptOutcome::NoResponse
                        | AgentRequestAttemptOutcome::TransportFailure
                        | AgentRequestAttemptOutcome::SourceProtocolFailure
                        | AgentRequestAttemptOutcome::RecordingFailure
                ) =>
            {
                attempt.outcome = AgentRequestAttemptOutcome::Cancelled;
                if let Some(recorder) = &self.recorder {
                    recorder.record(TranscriptEvent::Outcome {
                        coordinates: recorder.current_coordinates(),
                        outcome: AgentRequestAttemptOutcome::Cancelled.into(),
                    });
                }
                true
            }
            (HoudiniProposal::Failure(_), None) => true,
            (HoudiniProposal::Failure(_), Some(attempt)) => matches!(
                attempt.outcome,
                AgentRequestAttemptOutcome::Correctable
                    | AgentRequestAttemptOutcome::OversizedResponse
                    | AgentRequestAttemptOutcome::Cancelled
            ),
            _ => false,
        }
    }

    async fn request_houdini_response(
        &mut self,
        request: &AgentPush,
        tool_policy: &AgentToolPolicy,
        state_revision: u64,
        transport_ordinal: usize,
        validator: &AgentResponseValidator<'_>,
        cancellation: &CancellationToken,
    ) -> AgentRequestAdmission {
        let consultation = request.authority.feedback.consultation_digest();
        let validation_ordinal = request.authority.validation_ordinal;
        let same_request_retry = transport_ordinal > 0;
        if let Some(recorder) = &self.recorder {
            recorder.coordinates(TranscriptCoordinates {
                consultation: self.consultations.len().saturating_sub(1) as u64,
                validation: validation_ordinal as u64,
                transport: transport_ordinal as u64,
            });
        }
        if cancellation.is_cancelled() {
            self.record_attempt(
                consultation,
                Arc::clone(&request.digest),
                validation_ordinal,
                transport_ordinal,
                None,
                AgentRequestAttemptOutcome::Cancelled,
                same_request_retry,
            );
            return AgentRequestAdmission::Cancelled;
        }
        let source_cancellation = CancellationToken::new();
        let source_observer = AgentSourceCancellation::new(source_cancellation.clone());
        let tool_surface = AgentToolDispatcher::new(
            tool_policy.clone(),
            state_revision,
            source_observer.clone(),
            AgentToolResources::new(
                Arc::clone(&request.authority.feedback),
                validator.state,
                validator.feedback_state,
                validator.admission,
                validator.solver,
                validator.solver_admission,
                validator.query,
            ),
        );
        let mut response_writer = AgentResponseWriter::new(
            request
                .authority
                .feedback
                .host_limits()
                .get_usize("reply_bytes"),
        );
        if let Some(recorder) = &self.recorder {
            if recorder.status().is_err() {
                return AgentRequestAdmission::RecordingFailure;
            }
            recorder.lifecycle(TranscriptLifecycle::RequestStarted);
            recorder.owner(request);
            recorder.bytes(TranscriptStream::Push, request.bytes(), None);
            if recorder.status().is_err() {
                return AgentRequestAdmission::RecordingFailure;
            }
            response_writer.recorder = Some(recorder.clone());
        }
        let mut source_request = self.source.consult(
            request,
            &tool_surface,
            &mut response_writer,
            source_observer,
        );
        let (outcome, cancelled) = {
            let source_result = std::future::poll_fn(|context| {
                match catch_unwind(AssertUnwindSafe(|| source_request.as_mut().poll(context))) {
                    Ok(Poll::Ready(outcome)) => Poll::Ready(Ok(outcome)),
                    Ok(Poll::Pending) => Poll::Pending,
                    Err(payload) => Poll::Ready(Err(payload)),
                }
            });
            tokio::pin!(source_result);
            tokio::select! {
                biased;
                _ = cancellation.cancelled() => {
                    source_cancellation.cancel_from(cancellation);
                    if let Some(recorder) = &self.recorder {
                        recorder.lifecycle(TranscriptLifecycle::RequestCancelled);
                    }
                    (source_result.await, true)
                },
                outcome = &mut source_result => (outcome, false),
            }
        };
        if let Some(recorder) = &self.recorder {
            match &outcome {
                Ok(outcome) => recorder.record(TranscriptEvent::ProviderOutcome {
                    coordinates: recorder.current_coordinates(),
                    outcome: outcome.into(),
                }),
                Err(_) => recorder.lifecycle(TranscriptLifecycle::RequestPanicked),
            }
        }
        // The response future has stopped producing bytes. Close its
        // request-local lifetime before the mandatory idle join so even a
        // defective source that returned ahead of a child can reap it here.
        if cancellation.is_cancelled() {
            source_cancellation.cancel_from(cancellation);
        } else {
            source_cancellation.cancel();
        }
        drop(source_request);
        let cleanup = self.source.quiesce_request().await;
        if let Err(error) = cleanup {
            self.cleanup_failure.get_or_insert(error);
        }
        if let Some(recorder) = &self.recorder {
            if !cancelled && cancellation.is_cancelled() {
                recorder.lifecycle(TranscriptLifecycle::RequestCancelled);
            }
            if cleanup.is_ok() {
                recorder.lifecycle(TranscriptLifecycle::CleanupJoined);
            }
        }
        let outcome = match outcome {
            Ok(outcome) => outcome,
            Err(payload) => {
                self.shutdown(ShutdownReason::Failure).await;
                resume_unwind(payload)
            }
        };
        if let Err(error) = cleanup {
            return AgentRequestAdmission::CleanupFailure(error);
        }
        if let Some(detail) = self.source.resource_failure() {
            // The guard terminates this completed request before admission. It
            // still owns one history row, using the existing exhausted outcome;
            // dropping the row would hide the attempt and its retry accounting.
            self.record_attempt(
                consultation,
                Arc::clone(&request.digest),
                validation_ordinal,
                transport_ordinal,
                None,
                AgentRequestAttemptOutcome::SourceExhausted,
                same_request_retry,
            );
            return AgentRequestAdmission::ResourceFailure(detail);
        }
        if let Some(failure) = self.source.terminal_failure() {
            return AgentRequestAdmission::EndpointFailure(failure);
        }
        if cancelled || cancellation.is_cancelled() {
            self.record_attempt(
                consultation,
                Arc::clone(&request.digest),
                validation_ordinal,
                transport_ordinal,
                None,
                AgentRequestAttemptOutcome::Cancelled,
                same_request_retry,
            );
            return AgentRequestAdmission::Cancelled;
        }
        if self.recorder.as_ref().is_some_and(|r| r.status().is_err()) {
            self.record_attempt(
                consultation,
                Arc::clone(&request.digest),
                validation_ordinal,
                transport_ordinal,
                None,
                AgentRequestAttemptOutcome::RecordingFailure,
                same_request_retry,
            );
            return AgentRequestAdmission::RecordingFailure;
        }
        if response_writer.limit_exceeded() {
            let digest = response_writer.oversized_event_digest(request.digest());
            self.record_attempt(
                consultation,
                Arc::clone(&request.digest),
                validation_ordinal,
                transport_ordinal,
                Some(Arc::clone(&digest)),
                AgentRequestAttemptOutcome::OversizedResponse,
                same_request_retry,
            );
            return AgentRequestAdmission::Oversized {
                digest,
                found: response_writer.observed_bytes,
                limit: response_writer
                    .maximum_bytes
                    .expect("a reply is oversized only under a reply_bytes host limit"),
            };
        }
        if matches!(
            &outcome,
            AgentSourceOutcome::NoResponse | AgentSourceOutcome::SourceExhausted
        ) && !response_writer.bytes.is_empty()
        {
            let digest: Arc<str> = Arc::from(bytes_sha256(&response_writer.bytes));
            self.record_attempt(
                consultation,
                Arc::clone(&request.digest),
                validation_ordinal,
                transport_ordinal,
                Some(digest),
                AgentRequestAttemptOutcome::SourceProtocolFailure,
                same_request_retry,
            );
            return AgentRequestAdmission::SourceProtocolFailure;
        }
        match outcome {
            AgentSourceOutcome::Response => {
                let response = AgentHoudiniResponse::capture(response_writer.into_bytes(), request);
                let attempt_index = self.record_attempt(
                    consultation,
                    Arc::clone(&request.digest),
                    validation_ordinal,
                    transport_ordinal,
                    Some(Arc::clone(&response.digest)),
                    AgentRequestAttemptOutcome::Received,
                    same_request_retry,
                );
                AgentRequestAdmission::Response {
                    response,
                    attempt_index,
                }
            }
            AgentSourceOutcome::SourceExhausted => {
                self.record_attempt(
                    consultation,
                    Arc::clone(&request.digest),
                    validation_ordinal,
                    transport_ordinal,
                    None,
                    AgentRequestAttemptOutcome::SourceExhausted,
                    same_request_retry,
                );
                AgentRequestAdmission::SourceExhausted
            }
            AgentSourceOutcome::NoResponse => {
                self.record_attempt(
                    consultation,
                    Arc::clone(&request.digest),
                    validation_ordinal,
                    transport_ordinal,
                    None,
                    AgentRequestAttemptOutcome::NoResponse,
                    same_request_retry,
                );
                AgentRequestAdmission::NoResponse
            }
            AgentSourceOutcome::TransportFailure => {
                let partial_digest = (!response_writer.bytes.is_empty())
                    .then(|| Arc::from(bytes_sha256(&response_writer.bytes)));
                self.record_attempt(
                    consultation,
                    Arc::clone(&request.digest),
                    validation_ordinal,
                    transport_ordinal,
                    partial_digest,
                    AgentRequestAttemptOutcome::TransportFailure,
                    same_request_retry,
                );
                AgentRequestAdmission::TransportFailure
            }
        }
    }

    /// Obtain one admitted proposal using correction and same-request retry
    /// rounds inside the exact feedback consultation.
    pub async fn get_houdini_proposal(
        &mut self,
        feedback: &AgentFeedback,
        validator: &AgentResponseValidator<'_>,
        cancellation: &CancellationToken,
    ) -> Result<HoudiniProposal, AgentConsultationCancelled> {
        if let Some(error) = self.cleanup_failure {
            return Ok(HoudiniProposal::Failure(cleanup_failure(error)));
        }
        let result = self
            .consult_houdini(feedback, validator, cancellation)
            .await;
        // The final outcome/correction tap can itself hit the recorder's
        // bound. Do not release an admitted proposal after that failure.
        if result.is_ok()
            && self
                .recorder
                .as_ref()
                .is_some_and(|recorder| recorder.status().is_err())
        {
            if let Some(attempt) = self.attempts.last_mut().filter(|attempt| {
                attempt.consultation_digest.as_ref() == feedback.consultation_digest()
                    && attempt.outcome == AgentRequestAttemptOutcome::Accepted
            }) {
                attempt.outcome = AgentRequestAttemptOutcome::RecordingFailure;
            }
            return Ok(HoudiniProposal::Failure(resource_fault(
                "required provider transcript recording failed",
            )));
        }
        result
    }

    async fn consult_houdini(
        &mut self,
        feedback: &AgentFeedback,
        validator: &AgentResponseValidator<'_>,
        cancellation: &CancellationToken,
    ) -> Result<HoudiniProposal, AgentConsultationCancelled> {
        if cancellation.is_cancelled() {
            return Err(AgentConsultationCancelled);
        }
        if self
            .policy
            .limits
            .max_consultations
            .is_some_and(|limit| self.consultations.len() >= limit)
        {
            return Ok(HoudiniProposal::Failure(agent_failure(
                FailureKind::SourceExhausted,
                "the bounded AgentHoudini consultation source is exhausted",
            )));
        }
        let consultation: Arc<str> = Arc::from(feedback.consultation_digest());
        if self.consultations.contains(&consultation) {
            return Ok(HoudiniProposal::Failure(validation_failure(
                "one AgentHoudini consultation was requested more than once",
            )));
        }
        let attempts_per_response = self
            .policy
            .limits
            .max_transport_retries_per_request
            .saturating_add(1);
        self.consultations.insert(Arc::clone(&consultation));
        let negotiated = match self
            .source
            .api_capabilities()
            .negotiate(&validator.state.tool_policy().enabled_names())
        {
            Ok(value) => value,
            Err(error) => {
                return Ok(HoudiniProposal::Failure(agent_failure(
                    FailureKind::TransportFailure,
                    &format!("proposer API negotiation: {error}"),
                )));
            }
        };
        let tool_policy = AgentToolPolicy::new(
            negotiated
                .operations
                .iter()
                .filter_map(|name| super::tools::AgentTool::from_name(name)),
        );
        let state_revision = validator.state.proposal_revision();
        let mut correction = None;
        // Corrections are unlimited within a consultation: a rejected
        // submission changes no state, and the optional consultation
        // deadline together with the run deadline are the only guards
        // against a provider that never submits an acceptable proposal.
        // The only cap here is the host's memory bound on retained attempt
        // rows.
        let mut validation_ordinal = 0_usize;
        loop {
            if self
                .attempts
                .len()
                .checked_add(attempts_per_response)
                .is_none_or(|needed| needed > self.policy.maximum_history_records)
            {
                // The other memory guard, and unrecoverable for the same
                // reason: the retained history never shrinks, so a next
                // consultation reaches this branch again.
                return Ok(HoudiniProposal::Failure(resource_fault(
                    "the AgentHoudini attempt-history memory guard is reached",
                )));
            }
            let request = match build_push(
                feedback,
                correction.as_ref(),
                validation_ordinal,
                &self.policy,
                &tool_policy,
                state_revision,
            ) {
                Ok(mut request) => {
                    request.negotiated_api = negotiated.clone();
                    request.request_deadline = self.request_deadline;
                    request
                }
                Err(report) => return Ok(HoudiniProposal::Failure(report)),
            };
            for transport_ordinal in 0..=self.policy.limits.max_transport_retries_per_request {
                if validation_ordinal > 0 || transport_ordinal > 0 {
                    // Synchronously ready sources and validators must not
                    // monopolize one poll across correction or transport
                    // rounds. Yield so the consultation owner can observe its
                    // deadline or external cancellation before another request
                    // starts, then recheck the shared consultation token.
                    tokio::task::yield_now().await;
                    if cancellation.is_cancelled() {
                        return Err(AgentConsultationCancelled);
                    }
                }
                match self
                    .request_houdini_response(
                        &request,
                        &tool_policy,
                        state_revision,
                        transport_ordinal,
                        validator,
                        cancellation,
                    )
                    .await
                {
                    AgentRequestAdmission::Response {
                        response,
                        attempt_index,
                    } => {
                        let validation = validator
                            .validate_houdini_response(response, &self.policy, cancellation)
                            .await;
                        if cancellation.is_cancelled() {
                            self.update_attempt(
                                attempt_index,
                                AgentRequestAttemptOutcome::Cancelled,
                            );

                            return Err(AgentConsultationCancelled);
                        }
                        match validation {
                            Err(AgentConsultationCancelled) => {
                                self.update_attempt(
                                    attempt_index,
                                    AgentRequestAttemptOutcome::Cancelled,
                                );

                                return Err(AgentConsultationCancelled);
                            }
                            Ok(AgentResponseValidation::Accepted(proposal)) => {
                                self.update_attempt(
                                    attempt_index,
                                    AgentRequestAttemptOutcome::Accepted,
                                );
                                return Ok(proposal);
                            }
                            Ok(AgentResponseValidation::Failure(report)) => {
                                self.update_attempt(
                                    attempt_index,
                                    AgentRequestAttemptOutcome::ValidationFailure,
                                );

                                return Ok(HoudiniProposal::Failure(report));
                            }
                            Ok(AgentResponseValidation::Correctable(next)) => {
                                self.update_attempt(
                                    attempt_index,
                                    AgentRequestAttemptOutcome::Correctable,
                                );
                                if let Some(recorder) = &self.recorder {
                                    recorder.bytes(
                                        TranscriptStream::Correction,
                                        &serde_json::to_vec(next.wire_value())
                                            .expect("correction JSON serializes"),
                                        None,
                                    );
                                }
                                correction = Some(next);
                                break;
                            }
                        }
                    }
                    AgentRequestAdmission::Oversized {
                        digest,
                        found,
                        limit,
                    } => {
                        correction = Some(make_correction(
                            feedback,
                            digest,
                            validation_ordinal + 1,
                            [host_limit_diagnostic(&HostLimitRefusal::new(
                                "reply_bytes",
                                limit as u64,
                                found as u64,
                            ))],
                            &self.policy,
                        ));
                        if let (Some(recorder), Some(correction)) = (&self.recorder, &correction) {
                            recorder.bytes(
                                TranscriptStream::Correction,
                                &serde_json::to_vec(correction.wire_value())
                                    .expect("correction JSON serializes"),
                                None,
                            );
                        }
                        break;
                    }
                    outcome @ (AgentRequestAdmission::NoResponse
                    | AgentRequestAdmission::TransportFailure) => {
                        let retry = transport_ordinal
                            < self.policy.limits.max_transport_retries_per_request;
                        let (failure_kind, detail) = match outcome {
                            AgentRequestAdmission::NoResponse => (
                                FailureKind::NoResponse,
                                "the Agent source returned no response",
                            ),
                            AgentRequestAdmission::TransportFailure => (
                                FailureKind::TransportFailure,
                                "the Agent response transport failed",
                            ),
                            _ => unreachable!(),
                        };
                        if retry {
                            continue;
                        }

                        return Ok(HoudiniProposal::Failure(agent_failure(
                            failure_kind,
                            detail,
                        )));
                    }
                    AgentRequestAdmission::SourceExhausted => {
                        return Ok(HoudiniProposal::Failure(
                            match self.source.resource_failure() {
                                Some(detail) => resource_fault(detail),
                                None => agent_failure(
                                    FailureKind::SourceExhausted,
                                    "the Agent response source is exhausted",
                                ),
                            },
                        ));
                    }
                    AgentRequestAdmission::ResourceFailure(detail) => {
                        return Ok(HoudiniProposal::Failure(resource_fault(detail)));
                    }
                    AgentRequestAdmission::EndpointFailure(error) => {
                        return Ok(HoudiniProposal::Failure(endpoint_failure(error)));
                    }
                    AgentRequestAdmission::CleanupFailure(error) => {
                        return Ok(HoudiniProposal::Failure(cleanup_failure(error)));
                    }
                    AgentRequestAdmission::RecordingFailure => {
                        return Ok(HoudiniProposal::Failure(resource_fault(
                            "required provider transcript recording failed",
                        )));
                    }
                    AgentRequestAdmission::SourceProtocolFailure => {
                        return Ok(HoudiniProposal::Failure(validation_failure(
                            "the Agent source returned partial bytes with a non-response outcome",
                        )));
                    }
                    AgentRequestAdmission::Cancelled => {
                        return Err(AgentConsultationCancelled);
                    }
                }
            }
            validation_ordinal = match validation_ordinal.checked_add(1) {
                Some(next) => next,
                None => {
                    return Ok(HoudiniProposal::Failure(validation_failure(
                        "AgentHoudini correction accounting overflowed",
                    )));
                }
            };
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn record_attempt(
        &mut self,
        consultation_digest: &str,
        request_digest: Arc<str>,
        validation_ordinal: usize,
        transport_ordinal: usize,
        response_digest: Option<Arc<str>>,
        outcome: AgentRequestAttemptOutcome,
        same_request_retry: bool,
    ) -> usize {
        debug_assert!(self.attempts.len() < self.policy.maximum_history_records);
        let index = self.attempts.len();
        if let Some(recorder) = &self.recorder {
            recorder.record(TranscriptEvent::Outcome {
                coordinates: recorder.current_coordinates(),
                outcome: outcome.into(),
            });
        }
        self.attempts.push(AgentHoudiniAttempt {
            consultation_digest: Arc::from(consultation_digest),
            request_digest,
            validation_ordinal,
            transport_ordinal,
            response_digest,
            outcome,
            same_request_retry,
        });
        index
    }

    fn update_attempt(&mut self, index: usize, outcome: AgentRequestAttemptOutcome) {
        let attempt = self
            .attempts
            .get_mut(index)
            .expect("a just-recorded Agent attempt index remains present");
        debug_assert_eq!(attempt.outcome, AgentRequestAttemptOutcome::Received);
        attempt.outcome = outcome;
        if let Some(recorder) = &self.recorder {
            recorder.record(TranscriptEvent::Outcome {
                coordinates: recorder.current_coordinates(),
                outcome: outcome.into(),
            });
        }
    }
}

// ------------------------------------------------------------
// Atomic Response Admission
// ------------------------------------------------------------

impl AgentResponseValidator<'_> {
    /// Validate one exact response without publishing any state transition.
    pub async fn validate_houdini_response(
        &self,
        response: AgentHoudiniResponse,
        policy: &AgentConsultationPolicy,
        cancellation: &CancellationToken,
    ) -> Result<AgentResponseValidation, AgentConsultationCancelled> {
        require_active_consultation(cancellation)?;
        let context_matches_state = response
            .authority
            .feedback
            .validation_manifest()
            .proposal_context()
            .matches_state(self.state)
            .unwrap_or(false);
        if !context_matches_state
            || self.admission.scope().task_identity() != self.task.identity()
            || self.solver.scope() != self.admission.scope()
            || self.state.catalog().scope() != self.admission.scope()
        {
            require_active_consultation(cancellation)?;
            return Ok(AgentResponseValidation::Failure(validation_failure(
                "AgentHoudini validation authorities disagree before response admission",
            )));
        }
        require_active_consultation(cancellation)?;

        let reply_bytes = response
            .authority
            .feedback
            .host_limits()
            .get_usize("reply_bytes");
        let mut value = match decode_strict_json(response.bytes(), reply_bytes) {
            Ok(value) => value,
            Err(error) => {
                require_active_consultation(cancellation)?;
                return Ok(AgentResponseValidation::Correctable(make_correction(
                    &response.authority.feedback,
                    response.digest.clone(),
                    response.authority.validation_ordinal + 1,
                    [strict_json_diagnostic(error)],
                    policy,
                )));
            }
        };
        if let Some(diagnostic) = reconcile_counterexample_clause_members(&mut value) {
            require_active_consultation(cancellation)?;
            return Ok(AgentResponseValidation::Correctable(make_correction(
                &response.authority.feedback,
                response.digest.clone(),
                response.authority.validation_ordinal + 1,
                [diagnostic],
                policy,
            )));
        }
        let value_for_diagnostics = value.clone();
        let raw: RawAgentHoudiniResponse = match serde_json::from_value(value) {
            Ok(raw) => raw,
            Err(_) => {
                require_active_consultation(cancellation)?;
                return Ok(AgentResponseValidation::Correctable(make_correction(
                    &response.authority.feedback,
                    response.digest.clone(),
                    response.authority.validation_ordinal + 1,
                    [malformed_response_diagnostic(
                        &value_for_diagnostics,
                        &response,
                    )],
                    policy,
                )));
            }
        };
        require_active_consultation(cancellation)?;
        match raw {
            RawAgentHoudiniResponse::CandidateClauses {
                schema_version,
                binding,
                clauses,
                dropped,
            } => {
                let diagnostics = validate_outer_binding(schema_version, &binding, &response);
                if !diagnostics.is_empty() {
                    require_active_consultation(cancellation)?;
                    return Ok(AgentResponseValidation::Correctable(make_correction(
                        &response.authority.feedback,
                        response.digest.clone(),
                        response.authority.validation_ordinal + 1,
                        diagnostics,
                        policy,
                    )));
                }
                self.validate_clause_response(response, clauses, dropped, policy, cancellation)
                    .await
            }
            RawAgentHoudiniResponse::CandidateCounterexample {
                schema_version,
                binding,
                input,
            } => {
                let diagnostics = validate_outer_binding(schema_version, &binding, &response);
                if !diagnostics.is_empty() {
                    require_active_consultation(cancellation)?;
                    return Ok(AgentResponseValidation::Correctable(make_correction(
                        &response.authority.feedback,
                        response.digest.clone(),
                        response.authority.validation_ordinal + 1,
                        diagnostics,
                        policy,
                    )));
                }
                require_active_consultation(cancellation)?;
                accept_counterexample_response(response, input)
            }
        }
    }

    async fn validate_clause_response(
        &self,
        response: AgentHoudiniResponse,
        clauses: Vec<String>,
        raw_drops: Vec<RawDropReference>,
        policy: &AgentConsultationPolicy,
        cancellation: &CancellationToken,
    ) -> Result<AgentResponseValidation, AgentConsultationCancelled> {
        let feedback = &response.authority.feedback;
        let host_limits = *feedback.host_limits();
        // An empty clause is a defect of the proposal, not a host limit, and
        // is reported as one.
        if clauses.iter().any(String::is_empty) {
            return Ok(content_correction(
                &response,
                policy,
                fixed_diagnostic(
                    "empty_clause",
                    "A submitted clause is empty; submit clause text or no clause at all.",
                ),
            ));
        }
        // Every size limit on a submission is one of the run's optional host
        // limits, absent by default. A refusal names the limit and is never
        // a defect of the proposal.
        let longest_clause = clauses.iter().map(String::len).max().unwrap_or(0);
        if let Some(refusal) = host_limits
            .refusal("proposal_size", clauses.len() as u64)
            .or_else(|| host_limits.refusal("clause_text_bytes", longest_clause as u64))
            .or_else(|| host_limits.refusal("drop_references", raw_drops.len() as u64))
        {
            return Ok(content_correction(
                &response,
                policy,
                host_limit_diagnostic(&refusal),
            ));
        }

        let drops = match resolve_drops(feedback, self.state, &raw_drops) {
            Ok(drops) => drops,
            Err(diagnostic) => return Ok(content_correction(&response, policy, diagnostic)),
        };

        let admitted_batch_outcome = self
            .admission
            .admit_clauses(
                &clauses,
                host_limits.clause_text_bytes,
                self.solver_admission,
                cancellation,
            )
            .await;
        require_active_consultation(cancellation)?;
        let admitted_batch = match admitted_batch_outcome {
            Ok(AdmissionOutcome::Accepted(admitted)) => admitted,
            Ok(AdmissionOutcome::Correctable(correction)) => {
                return Ok(AgentResponseValidation::Correctable(make_correction(
                    feedback,
                    response.digest.clone(),
                    response.authority.validation_ordinal + 1,
                    admission_diagnostics(&correction),
                    policy,
                )));
            }
            Err(FrameworkIIAdmissionError::Cancelled) => {
                return Err(AgentConsultationCancelled);
            }
            Err(FrameworkIIAdmissionError::Failure(_)) => {
                return Ok(AgentResponseValidation::Failure(validation_failure(
                    "Lean clause admission infrastructure failed",
                )));
            }
        };

        if admitted_batch.iter().any(|candidate| {
            drops
                .iter()
                .any(|drop| drop.record().formula() == candidate)
        }) {
            return Ok(content_correction(
                &response,
                policy,
                fixed_diagnostic(
                    "drop_submission_conflict",
                    "A response cannot drop and submit the same admitted formula.",
                ),
            ));
        }

        let combined = match combine_candidate_clauses(&admitted_batch) {
            Ok(combined) => combined,
            Err(CombineCandidateError::Infrastructure) => {
                return Ok(AgentResponseValidation::Failure(validation_failure(
                    "admitted formula identities carry conflicting semantic metadata",
                )));
            }
        };
        match self.state.catalog().preflight_submitted_batch(&combined) {
            Ok(()) => {}
            Err(FrameworkIIStateError::ClauseLimitExceeded { found, limit }) => {
                return Ok(content_correction(
                    &response,
                    policy,
                    host_limit_diagnostic(&HostLimitRefusal::new(
                        "catalog_size",
                        limit as u64,
                        found as u64,
                    )),
                ));
            }
            Err(_) => {
                return Ok(AgentResponseValidation::Failure(validation_failure(
                    "preflight the exact current fixed-ambient catalog capacity",
                )));
            }
        }
        // A dead identity (Pass 7.5b) never revives. Reject the resubmission
        // here as a correction, naming the exact reason, before it can reach
        // the proposal boundary's hard fail-closed rejection.
        match self.state.dead_conflict(&combined) {
            Ok(None) => {}
            Ok(Some((index, _, reason))) => {
                let source = combined
                    .get(index)
                    .map(ExtendedClause::canonical_source)
                    .unwrap_or_default();
                return Ok(content_correction(
                    &response,
                    policy,
                    dead_clause_diagnostic(reason, source),
                ));
            }
            Err(_) => {
                return Ok(AgentResponseValidation::Failure(validation_failure(
                    "check the exact current fixed-ambient dead-clause partition",
                )));
            }
        }
        // Lean assigns the minimum level and knows no bound. When the run
        // sets one, a clause above it is rejected at submission with the
        // diagnostic, never parked.
        if let Some(clause) = combined
            .iter()
            .find(|clause| self.state.exceeds_level_bound(clause.minimum_level()))
        {
            let bound = self
                .state
                .max_level()
                .map(FrameworkIILevel::get)
                .unwrap_or(0);
            return Ok(content_correction(
                &response,
                policy,
                host_limit_diagnostic(&HostLimitRefusal::new(
                    "level_bound",
                    bound,
                    clause.minimum_level().get(),
                )),
            ));
        }
        let epoch = match FrameworkIIProposalEpoch::new(
            feedback.validation_manifest().proposal_context().clone(),
            combined,
            drops,
        ) {
            Ok(epoch) => epoch,
            Err(_) => {
                return Ok(AgentResponseValidation::Failure(validation_failure(
                    "construct the exact fixed-ambient proposal epoch",
                )));
            }
        };
        require_active_consultation(cancellation)?;
        Ok(AgentResponseValidation::Accepted(
            HoudiniProposal::CandidateClauses(Box::new(epoch)),
        ))
    }
}

/// A bound `candidate_counterexample` response is accepted as-is and handed
/// to the search loop (agent report, Alg. Session and Section
/// "Counterexample proposals").
///
/// Nothing is admitted, no epoch runs, and the instance is not inspected:
/// Lean's `validate_counterexample` operation is the only thing that ever
/// decodes it. Takes no validator authority because it needs none — the
/// binding and byte limits were already enforced before this point.
fn accept_counterexample_response(
    response: AgentHoudiniResponse,
    input: Value,
) -> Result<AgentResponseValidation, AgentConsultationCancelled> {
    let binding = AgentConsultationBinding::from_response(&response);
    Ok(AgentResponseValidation::Accepted(
        HoudiniProposal::CandidateCounterexample(Box::new(AgentCounterexampleProposal {
            input,
            binding,
        })),
    ))
}

/// Check the envelope a submission must echo, naming each disagreement at the
/// path it actually lives at.
///
/// `schema_version` is a top-level key of the response, not a member of
/// `binding`, so a version disagreement is reported at `$.schema_version`; a
/// proposer told to look for it inside `binding` would be looking for a key
/// that is not there. The two checks are independent, so a submission that
/// got both wrong is told both at once. An empty result is a valid envelope.
fn validate_outer_binding(
    schema_version: u64,
    binding: &RawResponseBinding,
    response: &AgentHoudiniResponse,
) -> Vec<AgentCorrectionDiagnostic> {
    let mut diagnostics = Vec::new();
    if schema_version != AGENT_HOUDINI_PROTOCOL_VERSION {
        diagnostics.push(detailed_diagnostic(
            "wrong_response_binding",
            "Echo the schema_version of this consultation's response example.",
            "$.schema_version",
            json!({"missing": [], "unexpected": [], "changed": ["schema_version"]}),
        ));
    }
    // The submission decoded, so every binding key is present and only values
    // can disagree; the proposer is told which ones.
    let found = json!({
        "task_digest": binding.task_digest,
        "scope_digest": binding.scope_digest,
        "run_digest": binding.run_digest,
        "consultation_digest": binding.consultation_digest,
        "state_snapshot_digest": binding.state_snapshot_digest,
        "validation_manifest_digest": binding.validation_manifest_digest,
        "request_digest": binding.request_digest,
        "validation_ordinal": binding.validation_ordinal,
    });
    if let Some(details) = key_details(&expected_response_binding(response), &found) {
        diagnostics.push(detailed_diagnostic(
            "wrong_response_binding",
            "Copy the binding object of this consultation's response example exactly.",
            "$.binding",
            details,
        ));
    }
    diagnostics
}

/// The exact binding the controller issued with this push's response example.
///
/// A submission echoes it field for field; nothing here is derived by the
/// proposer, and the observation's own `feedback.binding` is a different,
/// shorter object that is never a submission binding.
fn expected_response_binding(response: &AgentHoudiniResponse) -> Value {
    let feedback = &response.authority.feedback;
    json!({
        "task_digest": feedback.task_digest(),
        "scope_digest": feedback.scope_digest(),
        "run_digest": feedback.run_digest(),
        "consultation_digest": feedback.consultation_digest(),
        "state_snapshot_digest": feedback.state_snapshot_digest(),
        "validation_manifest_digest": feedback.validation_manifest_digest(),
        "request_digest": response.request_digest(),
        "validation_ordinal": response.authority.validation_ordinal,
    })
}

/// The three key lists that say what is wrong with `found` against
/// `expected`: keys the submission left out, keys it added, and keys whose
/// value differs. A caller that produced no list at all learns nothing, so
/// `None` means the object matched exactly.
fn key_details(expected: &Value, found: &Value) -> Option<Value> {
    let (expected, found) = (expected.as_object()?, found.as_object()?);
    let missing = expected
        .keys()
        .filter(|key| !found.contains_key(*key))
        .cloned()
        .collect::<Vec<_>>();
    let unexpected = found
        .keys()
        .filter(|key| !expected.contains_key(*key))
        .cloned()
        .collect::<Vec<_>>();
    let changed = expected
        .iter()
        .filter(|(key, value)| found.get(*key).is_some_and(|actual| actual != *value))
        .map(|(key, _)| key.clone())
        .collect::<Vec<_>>();
    (!missing.is_empty() || !unexpected.is_empty() || !changed.is_empty())
        .then(|| json!({"missing": missing, "unexpected": unexpected, "changed": changed}))
}

fn detailed_diagnostic(
    code: &'static str,
    message: &'static str,
    path: &'static str,
    details: Value,
) -> AgentCorrectionDiagnostic {
    AgentCorrectionDiagnostic {
        code: Arc::from(code),
        message: Arc::from(message),
        item_index: None,
        path: Some(Arc::from(path)),
        offset: None,
        host_limit: None,
        details: Some(Box::new(details)),
    }
}

/// Settle a counterexample response that also carries the clause variant's
/// `clauses` and `dropped`, before the strict grammar reads it.
///
/// A proposer working from the clause variant's skeleton fills those two
/// members in out of habit. Empty, they say exactly what the counterexample
/// already says — that this round places no clause and drops none — so they
/// are removed and the instance is judged on its own merits. A non-empty one
/// is clause content no counterexample round can place, and is named here,
/// with the members at fault, rather than left to the shape check, which would
/// report a member the envelope tolerates as simply unexpected.
///
/// Only the two members are touched, and only on this one kind: every other
/// key reaches the grammar exactly as the proposer wrote it.
pub(super) fn reconcile_counterexample_clause_members(
    value: &mut Value,
) -> Option<AgentCorrectionDiagnostic> {
    let object = value.as_object_mut()?;
    if object.get("kind").and_then(Value::as_str) != Some("candidate_counterexample") {
        return None;
    }
    let mut carried = Vec::new();
    for member in ["clauses", "dropped"] {
        match object.get(member) {
            Some(Value::Array(rows)) if rows.is_empty() => {
                object.remove(member);
            }
            Some(_) => carried.push(member.to_owned()),
            None => {}
        }
    }
    (!carried.is_empty()).then(|| {
        detailed_diagnostic(
            "malformed_response",
            "Send clause content as a candidate_clauses response; a counterexample carries none.",
            "$",
            json!({"missing": [], "unexpected": carried, "changed": []}),
        )
    })
}

/// The top-level keys each response variant carries, chosen by the `kind` the
/// submission itself declares.
fn expected_response_keys(kind: Option<&str>) -> Option<&'static [&'static str]> {
    match kind {
        Some("candidate_clauses") => {
            Some(&["binding", "clauses", "dropped", "kind", "schema_version"])
        }
        Some("candidate_counterexample") => Some(&["binding", "input", "kind", "schema_version"]),
        _ => None,
    }
}

/// Say what is wrong with a response that did not decode at all.
///
/// The generic sentence is a dead end for a proposer: it cannot tell a missing
/// `request_digest` from an unknown `kind`. So the shape is checked by hand,
/// outermost first, and the diagnostic names the offending path with the exact
/// keys that were missing, unexpected or changed. The commonest real mistake —
/// echoing the observation's `feedback.binding` instead of the response
/// example's binding — comes back as exactly that list.
fn malformed_response_diagnostic(
    value: &Value,
    response: &AgentHoudiniResponse,
) -> AgentCorrectionDiagnostic {
    let generic = || {
        fixed_diagnostic(
            "malformed_response",
            "Submit exactly one complete supported response variant.",
        )
    };
    let Some(object) = value.as_object() else {
        return generic();
    };
    let kind = object.get("kind").and_then(Value::as_str);
    let Some(keys) = expected_response_keys(kind) else {
        return detailed_diagnostic(
            "malformed_response",
            "The response kind must be candidate_clauses or candidate_counterexample.",
            "$.kind",
            json!({
                "missing": if object.contains_key("kind") { json!([]) } else { json!(["kind"]) },
                "unexpected": Value::Array(Vec::new()),
                "changed": if object.contains_key("kind") { json!(["kind"]) } else { json!([]) },
            }),
        );
    };
    let expected_shape = Value::Object(
        keys.iter()
            .map(|key| ((*key).to_owned(), Value::Null))
            .collect(),
    );
    let mut structure = key_details(&expected_shape, value).unwrap_or(Value::Null);
    if let Some(structure) = structure.as_object_mut() {
        // Only presence is checked here; a value mismatch at the top level is
        // reported by the field's own diagnostic, not by the shape check.
        structure.insert("changed".to_string(), Value::Array(Vec::new()));
        if structure["missing"] != json!([]) || structure["unexpected"] != json!([]) {
            return detailed_diagnostic(
                "malformed_response",
                "The response does not carry exactly this variant's fields.",
                "$",
                Value::Object(structure.clone()),
            );
        }
    }
    match object.get("binding") {
        Some(found) if found.is_object() => {
            match key_details(&expected_response_binding(response), found) {
                Some(details) => detailed_diagnostic(
                    "wrong_response_binding",
                    "Copy the binding object of this consultation's response example exactly.",
                    "$.binding",
                    details,
                ),
                None => generic(),
            }
        }
        // A binding that is present but not an object carries none of the keys
        // it owes, so it is named at its own path with all of them missing
        // rather than falling through to the generic sentence.
        Some(_) => detailed_diagnostic(
            "wrong_response_binding",
            "The binding must be the response example's object, copied exactly.",
            "$.binding",
            json!({
                "missing": expected_response_binding(response)
                    .as_object()
                    .map(|binding| binding.keys().cloned().collect::<Vec<_>>())
                    .unwrap_or_default(),
                "unexpected": Value::Array(Vec::new()),
                "changed": Value::Array(Vec::new()),
            }),
        ),
        None => generic(),
    }
}

fn strict_json_diagnostic(error: StrictJsonError) -> AgentCorrectionDiagnostic {
    match error {
        StrictJsonError::TooLarge { found, limit } => host_limit_diagnostic(
            &HostLimitRefusal::new("reply_bytes", limit as u64, found as u64),
        ),
        StrictJsonError::DuplicateObjectKey => fixed_diagnostic(
            "duplicate_object_key",
            "The response repeats an object key.",
        ),
        StrictJsonError::Empty | StrictJsonError::Malformed => fixed_diagnostic(
            "malformed_json",
            "The response must contain exactly one complete JSON value.",
        ),
        StrictJsonError::InvalidLimit => fixed_diagnostic(
            "malformed_response",
            "The response cannot be decoded under the current policy.",
        ),
    }
}

fn content_correction(
    response: &AgentHoudiniResponse,
    policy: &AgentConsultationPolicy,
    diagnostic: AgentCorrectionDiagnostic,
) -> AgentResponseValidation {
    AgentResponseValidation::Correctable(make_correction(
        &response.authority.feedback,
        response.digest.clone(),
        response.authority.validation_ordinal + 1,
        [diagnostic],
        policy,
    ))
}

fn resolve_drops(
    feedback: &AgentFeedback,
    state: &LeveledHoudiniState,
    raw_drops: &[RawDropReference],
) -> Result<Vec<FrameworkIIProposalDrop>, AgentCorrectionDiagnostic> {
    let mut seen_ids = BTreeSet::new();
    let mut seen_authorizations = BTreeSet::new();
    let mut drops = Vec::with_capacity(raw_drops.len());
    for raw in raw_drops {
        if !seen_ids.insert(raw.clause.clause_id)
            || !seen_authorizations.insert(raw.authorization_digest.as_str())
        {
            return Err(fixed_diagnostic(
                "duplicate_drop",
                "A response repeats one clause drop.",
            ));
        }
        // A drop targets a pending clause, never a committed (Core) or
        // dead one: `drop_references()` unifies the deprecated per-clause
        // page and the push's own `pending` entries, so this covers both
        // shares.
        let Some(reference) = feedback
            .drop_references()
            .find(|reference| raw_drop_matches(raw, reference))
        else {
            let clause_id = ClauseId::from_catalog_ordinal(raw.clause.clause_id);
            if feedback.validation_manifest().is_core_clause(clause_id) {
                return Err(fixed_diagnostic(
                    "core_clause_not_droppable",
                    "Core clauses cannot be dropped.",
                ));
            }
            if state.is_dead(clause_id) {
                return Err(fixed_diagnostic(
                    "drop_target_not_eligible",
                    "This clause is already dead and is not drop-eligible; drops target pending clauses only.",
                ));
            }
            return Err(fixed_diagnostic(
                "unauthorized_drop",
                "A drop is not an exact eligible reference shown in this consultation.",
            ));
        };
        let drop = feedback
            .validation_manifest()
            .resolve_shown_drop(reference)
            .ok_or_else(|| {
                fixed_diagnostic(
                    "unauthorized_drop",
                    "A drop is stale, foreign, settled, or otherwise ineligible.",
                )
            })?;
        drops.push(drop);
    }
    Ok(drops)
}

fn raw_drop_matches(raw: &RawDropReference, reference: &AgentClauseDropReference) -> bool {
    raw.consultation_digest == reference.consultation_digest()
        && raw.authorization_digest == reference.authorization_digest()
        && raw_identity_matches(&raw.clause, reference.clause())
}

fn raw_identity_matches(raw: &RawClauseIdentity, identity: &AgentClauseIdentity) -> bool {
    raw.clause_id == identity.clause_id().get()
        && raw.record_digest == identity.record_digest()
        && raw.formula_digest == identity.formula_digest()
        && !identity.contradicted_by(raw.canonical_source.as_deref(), raw.display.as_deref())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CombineCandidateError {
    Infrastructure,
}

/// The epoch's batch is exactly what the provider submitted, deduplicated by
/// identity and put in canonical order.
///
/// Nothing else is injected: every pending clause is returned to its minimum
/// level and re-checked by the epoch itself, so re-submitting the pending
/// frontier here would only re-register identities the controller already
/// holds.
fn combine_candidate_clauses(
    admitted: &[ExtendedClause],
) -> Result<Vec<ExtendedClause>, CombineCandidateError> {
    let mut by_identity = BTreeMap::<String, ExtendedClause>::new();
    for clause in admitted.iter().cloned() {
        let identity = clause.identity_intern_key().to_owned();
        if let Some(existing) = by_identity.get(&identity) {
            if !existing.semantic_metadata_matches(&clause) {
                return Err(CombineCandidateError::Infrastructure);
            }
            continue;
        }
        by_identity.insert(identity, clause);
    }
    let mut clauses = by_identity.into_values().collect::<Vec<_>>();
    clauses.sort_by(|left, right| {
        left.registration_order_key()
            .cmp(right.registration_order_key())
            .then_with(|| left.identity_intern_key().cmp(right.identity_intern_key()))
    });
    Ok(clauses)
}

fn require_active_consultation(
    cancellation: &CancellationToken,
) -> Result<(), AgentConsultationCancelled> {
    if cancellation.is_cancelled() {
        Err(AgentConsultationCancelled)
    } else {
        Ok(())
    }
}

fn endpoint_failure(error: ProposerTerminalFailure) -> FailureReport {
    FailureReport::try_new(
        FailureOrigin::RunControl,
        FailureKind::InfrastructureFailure,
        false,
        FailureScope::RunGlobal,
        Some(error.to_string()),
        Vec::new(),
    )
    .expect("terminal proposer fault is a run-control infrastructure failure")
}

fn cleanup_failure(error: ProposerCleanupError) -> FailureReport {
    FailureReport::try_new(
        FailureOrigin::RunControl,
        FailureKind::InfrastructureFailure,
        false,
        FailureScope::RunGlobal,
        Some(error.to_string()),
        Vec::new(),
    )
    .expect("proposer cleanup failure is a run-control infrastructure failure")
}

fn validation_failure(detail: &str) -> FailureReport {
    FailureReport::try_new(
        FailureOrigin::ResponseValidation,
        FailureKind::ValidationInfrastructureFailure,
        false,
        FailureScope::RunGlobal,
        Some(detail.to_owned()),
        Vec::new(),
    )
    .expect("response validation uses its sole permitted failure classification")
}

/// A **resource fault**: one of the run's memory guards fired, and the run
/// ends.
///
/// Distinct from [`agent_failure`] in the one respect that matters here, its
/// scope. A lane-local consultation failure is published to the proposer as
/// a `failure` event and the search holds the next consultation; a memory
/// guard is not recoverable that way, because nothing a next consultation
/// could do makes the document smaller — the host builds it — so a
/// lane-local classification livelocks the search loop until the run
/// deadline (Milestone 7.5 review, finding 7). `houdini.tex` Section 4.7:
/// a guard's failure is a resource fault, and a resource fault ends the run.
fn resource_fault(detail: impl Into<String>) -> FailureReport {
    FailureReport::try_new(
        FailureOrigin::AgentConsultation,
        FailureKind::SourceExhausted,
        false,
        FailureScope::RunGlobal,
        Some(detail.into()),
        Vec::new(),
    )
    .expect("Agent consultation resource faults use permitted classifications")
}

fn agent_failure(kind: FailureKind, detail: &str) -> FailureReport {
    debug_assert!(matches!(
        kind,
        FailureKind::SourceExhausted
            | FailureKind::CorrectionExhausted
            | FailureKind::NoResponse
            | FailureKind::TransportFailure
    ));
    FailureReport::try_new(
        FailureOrigin::AgentConsultation,
        kind,
        false,
        FailureScope::LaneLocal,
        Some(detail.to_owned()),
        Vec::new(),
    )
    .expect("Agent consultation helpers use permitted failure classifications")
}

// Reuse the actual outer parser for a deliberately unsupported counterexample
// input shape. The input is inspected only to classify the closed negative
// envelope and is never exported or rewritten; replay compares its full raw
// bytes after editing independently checked binding scalar tokens.
pub(super) fn replay_unsupported_counterexample_binding(
    bytes: &[u8],
) -> Option<super::replay_identity::ResponseBindingV1> {
    let raw: RawAgentHoudiniResponse =
        serde_json::from_value(decode_strict_json(bytes, None).ok()?).ok()?;
    let RawAgentHoudiniResponse::CandidateCounterexample {
        schema_version,
        binding,
        input,
    } = raw
    else {
        return None;
    };
    if schema_version != AGENT_HOUDINI_PROTOCOL_VERSION
        || serde_json::from_value::<super::replay_identity::ProgramInstanceV1>(input).is_ok()
    {
        return None;
    }
    Some(super::replay_identity::ResponseBindingV1 {
        task_digest: binding.task_digest,
        scope_digest: binding.scope_digest,
        run_digest: binding.run_digest,
        consultation_digest: binding.consultation_digest,
        state_snapshot_digest: binding.state_snapshot_digest,
        validation_manifest_digest: binding.validation_manifest_digest,
        request_digest: binding.request_digest,
        validation_ordinal: binding.validation_ordinal as u64,
    })
}

#[cfg(test)]
pub(crate) use tests::{fixture_push_for_negotiated_api, fixture_push_for_tools};

#[cfg(test)]
mod tests {
    use std::path::PathBuf;
    use std::sync::atomic::{AtomicU64, Ordering};
    use std::time::Duration;

    use super::*;
    use crate::artifact::{ArtifactStoreConfig, new_artifact_store};
    use crate::task::RelationKey;

    use super::super::catalog::LeveledClauseCatalog;
    use super::super::feedback::{AgentFeedbackPolicy, PreCertificateAgentHoudiniState};
    use super::super::types::{FixedAmbientTaskScope, FrameworkIILevel, FrameworkIIRelation};

    static NEXT_DISPATCH_DIRECTORY: AtomicU64 = AtomicU64::new(0);

    fn dispatch_directory(label: &str) -> PathBuf {
        std::env::temp_dir().join(format!(
            "whiel_agent_dispatch_{label}_{}_{}",
            std::process::id(),
            NEXT_DISPATCH_DIRECTORY.fetch_add(1, Ordering::Relaxed),
        ))
    }

    fn dispatch_task(canonical_id: &str) -> SynthesisTask {
        let source = r#"{
          "format_version":4,
          "semantic_version":1,
          "encoding_version":1,
          "identity":{
            "canonical_id":"DISPATCH_TASK",
            "module":"Whiel.Test.AgentDispatch",
            "namespace":"Whiel.Test.AgentDispatch",
            "source_sha256":"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
          },
          "schema":{"expression":"Whiel.Test.AgentDispatch.inputPreproc.prophecySchema","display":"{R}"},
          "original":{
            "pre":{"expression":"Whiel.Test.AgentDispatch.inputPre","display":"true"},
            "command":{"expression":"Whiel.Test.AgentDispatch.inputCmd","display":"SKIP"},
            "post":{"expression":"Whiel.Test.AgentDispatch.inputPost","display":"true"}
          },
          "preprocessed":{
            "pre":{"expression":"Whiel.Test.AgentDispatch.inputPreproc.liftedLoop.preAssert","display":"true"},
            "command":{"expression":"Whiel.Test.AgentDispatch.inputPreproc.liftedLoop.cmd","display":"SKIP"},
            "post":{"expression":"Whiel.Test.AgentDispatch.inputPreproc.liftedLoop.postAssert","display":"true"}
          },
          "preprocessing_evidence":{"expression":"Whiel.Test.AgentDispatch.inputPreproc"},
          "solver":{
            "schema_relations":[{"key":"o:p::R","arity":1}],
            "task_constants":[],
            "preprocessed_pre":{
              "source_id":"task.preprocessed_pre",
              "expression":"Whiel.Test.AgentDispatch.inputPreproc.liftedLoop.preAssert",
              "no_bound_expression":"Whiel.Test.AgentDispatch.inputPreproc.liftedLoop.preAssert_noBound",
              "constants":[],"relations":[]
            },
            "preprocessed_post":{
              "source_id":"task.preprocessed_post",
              "expression":"Whiel.Test.AgentDispatch.inputPreproc.liftedLoop.postAssert",
              "no_bound_expression":"Whiel.Test.AgentDispatch.inputPreproc.liftedLoop.postAssert_noBound",
              "constants":[],"relations":[]
            },
            "loop_guard":{"source_id":"task.loop_guard","constants":[],"relations":[]},
            "negated_loop_guard":{"source_id":"task.negated_loop_guard","constants":[],"relations":[]}
          }
        }"#;
        SynthesisTask::from_fixed_ambient_json(&source.replace("DISPATCH_TASK", canonical_id))
            .unwrap()
    }

    fn dispatch_scope(task: &SynthesisTask) -> FixedAmbientTaskScope {
        let relation = FrameworkIIRelation::new(RelationKey::from_lean_scope("o:p::R").unwrap(), 1);
        FixedAmbientTaskScope::new(
            task.identity().clone(),
            json!({"kind":"dispatch_scope","relation":"o:p::R"}),
            json!({"display":"R"}),
            vec![relation.clone()],
            vec![relation],
            Vec::new(),
        )
    }

    fn dispatch_feedback(
        task: &SynthesisTask,
        scope: &FixedAmbientTaskScope,
        run_marker: char,
    ) -> AgentFeedback {
        let catalog =
            LeveledClauseCatalog::new(scope.clone(), run_marker.to_string().repeat(64)).unwrap();
        let state = LeveledHoudiniState::new(catalog).unwrap();
        let (owner, artifacts) = new_artifact_store(
            task,
            ArtifactStoreConfig::new(dispatch_directory("feedback")),
        )
        .unwrap();
        let feedback = PreCertificateAgentHoudiniState::new(
            Arc::new(task.clone()),
            &artifacts,
            &state,
            Duration::from_secs(30),
            AgentFeedbackPolicy::default(),
        )
        .unwrap()
        .feedback()
        .clone();
        drop(artifacts);
        owner.settle().unwrap();
        feedback
    }

    pub(crate) fn fixture_push_for_tools(policy: &AgentToolPolicy) -> AgentPush {
        let task = dispatch_task("PythonMcpComposition");
        let scope = dispatch_scope(&task);
        let feedback = dispatch_feedback(&task, &scope, 'a');
        build_push(
            &feedback,
            None,
            0,
            &AgentConsultationPolicy::default(),
            policy,
            0,
        )
        .unwrap()
    }

    /// The production path stamps the push with the agreement reached against
    /// the endpoint's own declaration, which a compatible lower revision keeps
    /// below B's constant. Fixtures that consult such an endpoint need the same.
    pub(crate) fn fixture_push_for_negotiated_api(
        policy: &AgentToolPolicy,
        negotiated: crate::proposer_api::NegotiatedApi,
    ) -> AgentPush {
        let mut push = fixture_push_for_tools(policy);
        push.negotiated_api = negotiated;
        push
    }

    #[test]
    fn request_deadline_metadata_is_exact_optional_and_does_not_change_binding() {
        let mut push = fixture_push_for_tools(&AgentToolPolicy::default());
        let bytes = push.bytes().to_vec();
        let digest = push.digest().to_owned();
        assert_eq!(push.remaining_request_budget_ns().unwrap(), None);
        push.request_deadline = Some(tokio::time::Instant::now() + Duration::from_secs(2));
        let remaining = push.remaining_request_budget_ns().unwrap().unwrap();
        assert!(remaining > 0 && remaining <= 2_000_000_000);
        push.request_deadline = Some(tokio::time::Instant::now() - Duration::from_secs(1));
        assert_eq!(push.remaining_request_budget_ns().unwrap(), Some(0));
        push.request_deadline =
            Some(tokio::time::Instant::now() + Duration::from_secs(20_000_000_000));
        assert_eq!(
            push.remaining_request_budget_ns().unwrap_err().kind(),
            std::io::ErrorKind::InvalidData
        );
        assert_eq!(push.bytes(), bytes);
        assert_eq!(push.digest(), digest);
    }

    fn raw_binding() -> Value {
        json!({
            "task_digest": "a".repeat(64),
            "scope_digest": "b".repeat(64),
            "run_digest": "c".repeat(64),
            "consultation_digest": "d".repeat(64),
            "state_snapshot_digest": "e".repeat(64),
            "validation_manifest_digest": "f".repeat(64),
            "request_digest": "2".repeat(64),
            "validation_ordinal": 0,
        })
    }

    fn decode_raw(value: Value) -> Result<RawAgentHoudiniResponse, serde_json::Error> {
        serde_json::from_value(value)
    }

    #[test]
    fn default_request_policy_has_no_correction_limit_and_zero_transport_retries() {
        let policy = AgentConsultationPolicy::default();
        assert_eq!(AGENT_HOUDINI_PROTOCOL_VERSION, 4);
        assert_eq!(policy.limits().max_transport_retries_per_request, 0);
        assert_eq!(
            policy.maximum_history_records(),
            policy.limits().max_attempt_history_records
        );
        assert_eq!(policy.digest().len(), 64);
    }

    #[test]
    fn request_policy_digest_has_a_new_domain_and_no_conversation_setting() {
        let policy = AgentConsultationPolicy::default();
        let limits = policy.limits();
        let mut fields = json!({
            "domain":"whiel-proposer-request-policy-v1",
            "max_request_bytes":limits.max_request_bytes,
            "max_correction_diagnostics":limits.max_correction_diagnostics,
            "max_correction_bytes":limits.max_correction_bytes,
            "max_attempt_history_records":limits.max_attempt_history_records,
            "max_transport_retries_per_request":limits.max_transport_retries_per_request,
            "max_consultations":limits.max_consultations,
        });
        assert_eq!(policy.digest(), canonical_value_sha256(&fields));
        fields["domain"] = json!("whiel-agent-consultation-policy-v4");
        fields["session_mode"] = json!("fresh");
        assert_ne!(policy.digest(), canonical_value_sha256(&fields));
    }

    #[test]
    fn typed_observation_preserves_all_default_information_and_binding() {
        let task = dispatch_task("DefaultPromptCompatibility");
        let scope = dispatch_scope(&task);
        let feedback = dispatch_feedback(&task, &scope, 'a');
        let push = build_push(
            &feedback,
            None,
            0,
            &AgentConsultationPolicy::default(),
            &AgentToolPolicy::default(),
            0,
        )
        .unwrap();
        let canonical: Value = serde_json::from_slice(push.bytes()).unwrap();
        assert_eq!(serde_json::to_value(push.observation()).unwrap(), canonical);
        let before = push.bytes().to_vec();
        let mut local_copy = push.observation().clone();
        local_copy.feedback.core.clear();
        local_copy.binding.run_digest = "local editing conveys no authority".into();
        assert_eq!(push.bytes(), before);
        assert_eq!(push.observation().binding.run_digest, feedback.run_digest());
        let example = push.candidate_clauses_example().unwrap();
        assert!(example["binding"].get("policy_digest").is_none());
        assert_eq!(example["binding"]["request_digest"], push.digest());
        assert_eq!(example["binding"]["validation_ordinal"], 0);
        let frozen: Value = serde_json::from_str(include_str!(
            "../proposer_api/wire/fixtures/observation.json"
        ))
        .unwrap();
        let frozen_example: Value = serde_json::from_str(include_str!(
            "../proposer_api/wire/fixtures/response-example.json"
        ))
        .unwrap();
        // Scoped read capabilities contain a fresh secret per construction.
        // Freeze every presentation byte except the three dependent digests;
        // their live consistency with B authority is checked above.
        let substitutions = [
            (
                canonical["binding"]["consultation_digest"]
                    .as_str()
                    .unwrap(),
                frozen["binding"]["consultation_digest"].as_str().unwrap(),
            ),
            (
                canonical["binding"]["validation_manifest_digest"]
                    .as_str()
                    .unwrap(),
                frozen["binding"]["validation_manifest_digest"]
                    .as_str()
                    .unwrap(),
            ),
            (
                push.digest(),
                frozen_example["binding"]["request_digest"]
                    .as_str()
                    .unwrap(),
            ),
        ];
        let normalize = |mut text: String| {
            for (actual, target) in substitutions {
                text = text.replace(actual, target);
            }
            text
        };
        assert_eq!(
            serde_json::from_str::<Value>(&normalize(canonical.to_string())).unwrap(),
            frozen
        );
        assert_eq!(
            serde_json::from_str::<Value>(&normalize(example.to_string())).unwrap(),
            frozen_example
        );
        assert_eq!(
            push.negotiated_api().version,
            crate::proposer_api::API_VERSION
        );
    }

    #[test]
    fn provider_request_omits_the_retired_library_contract() {
        let task = dispatch_task("AgentRequestF2Only");
        let scope = dispatch_scope(&task);
        let feedback = dispatch_feedback(&task, &scope, 'f');
        let policy = AgentConsultationPolicy::default();
        let request =
            build_push(&feedback, None, 0, &policy, &AgentToolPolicy::default(), 0).unwrap();
        let value: Value = serde_json::from_slice(request.bytes()).unwrap();
        assert_eq!(
            value["schema_version"],
            json!(AGENT_HOUDINI_PROTOCOL_VERSION)
        );
        assert!(value["binding"].get("prior_active_plan_digest").is_none());

        let encoded = String::from_utf8(request.bytes().to_vec()).unwrap();
        for retired in [
            "finite_validity",
            "library_selection",
            "active_selection_plan",
            "library_rejection",
        ] {
            assert!(!encoded.contains(retired), "request exposes {retired}");
        }
    }

    #[test]
    fn push_never_carries_summary_clauses_or_ledger_keys() {
        fn assert_no_forbidden_keys(value: &Value) {
            match value {
                Value::Object(map) => {
                    for forbidden in ["summary", "clauses", "ledger"] {
                        assert!(
                            !map.contains_key(forbidden),
                            "push exposes forbidden key {forbidden}"
                        );
                    }
                    for nested in map.values() {
                        assert_no_forbidden_keys(nested);
                    }
                }
                Value::Array(items) => {
                    for item in items {
                        assert_no_forbidden_keys(item);
                    }
                }
                _ => {}
            }
        }

        let task = dispatch_task("AgentPushOmitsPagedKeys");
        let scope = dispatch_scope(&task);
        let feedback = dispatch_feedback(&task, &scope, '9');
        let policy = AgentConsultationPolicy::default();
        let push = build_push(&feedback, None, 0, &policy, &AgentToolPolicy::default(), 0).unwrap();
        let value: Value = serde_json::from_slice(push.bytes()).unwrap();
        assert_no_forbidden_keys(value.get("feedback").expect("push carries feedback"));
        assert_eq!(value["operation"], json!("proposer_observation"));
        assert_eq!(
            value["feedback"]["tools"],
            json!(AgentToolPolicy::default().enabled_names())
        );
        assert_eq!(value["feedback"]["state_revision"], json!(0));
    }

    #[test]
    fn previous_agent_protocol_version_fails_outer_binding_validation() {
        let task = dispatch_task("AgentRequestProtocolV1");
        let scope = dispatch_scope(&task);
        let feedback = dispatch_feedback(&task, &scope, 'a');
        let policy = AgentConsultationPolicy::default();
        let request =
            build_push(&feedback, None, 0, &policy, &AgentToolPolicy::default(), 0).unwrap();
        let response = AgentHoudiniResponse::capture(Vec::new(), &request);
        let binding = RawResponseBinding {
            task_digest: feedback.task_digest().to_owned(),
            scope_digest: feedback.scope_digest().to_owned(),
            run_digest: feedback.run_digest().to_owned(),
            consultation_digest: feedback.consultation_digest().to_owned(),
            state_snapshot_digest: feedback.state_snapshot_digest().to_owned(),
            validation_manifest_digest: feedback.validation_manifest_digest().to_owned(),
            request_digest: request.digest().to_owned(),
            validation_ordinal: request.validation_ordinal(),
        };

        // The version is a top-level key, so an old client is told about
        // `$.schema_version` and not sent looking inside a correct binding.
        let diagnostics = validate_outer_binding(1, &binding, &response);
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].path(), Some("$.schema_version"));
        assert!(
            validate_outer_binding(AGENT_HOUDINI_PROTOCOL_VERSION, &binding, &response).is_empty()
        );
    }

    #[test]
    fn policy_rejects_unbounded_or_inconsistent_limits() {
        for limits in [
            AgentConsultationLimits {
                max_attempt_history_records: 0,
                ..AgentConsultationLimits::default()
            },
            AgentConsultationLimits {
                max_transport_retries_per_request: MAXIMUM_TRANSPORT_RETRIES + 1,
                ..AgentConsultationLimits::default()
            },
            AgentConsultationLimits {
                max_consultations: Some(0),
                ..AgentConsultationLimits::default()
            },
            AgentConsultationLimits {
                max_correction_bytes: MINIMUM_CORRECTION_BYTES - 1,
                ..AgentConsultationLimits::default()
            },
        ] {
            assert!(AgentConsultationPolicy::new(limits).is_err());
        }
    }

    #[test]
    fn response_writer_retains_only_its_exact_cap() {
        let mut writer = AgentResponseWriter::new(Some(4));
        assert_eq!(writer.maximum_bytes(), Some(4));
        writer.write_chunk(b"abc").unwrap();
        let error = writer.write_chunk(b"defgh").unwrap_err();
        assert_eq!(error.limit(), 4);
        assert_eq!(writer.bytes, b"abcd");
        assert_eq!(writer.observed_bytes, 8);
        assert!(writer.limit_exceeded());
        assert!(writer.write_chunk(b"ignored").is_err());
        assert_eq!(writer.bytes, b"abcd");
        let debug = format!("{writer:?}");
        assert!(!debug.contains("abcd"));
        assert!(!debug.contains("ignored"));
    }

    /// The default: no `reply_bytes` host limit, so the sink retains every
    /// byte it is handed and never reports an oversized reply.
    #[test]
    fn an_unlimited_response_writer_retains_everything() {
        let mut writer = AgentResponseWriter::new(None);
        assert_eq!(writer.maximum_bytes(), None);
        let chunk = vec![b'x'; 1_000_000];
        writer.write_chunk(&chunk).unwrap();
        writer.write_chunk(&chunk).unwrap();
        assert_eq!(writer.bytes.len(), 2_000_000);
        assert!(!writer.limit_exceeded());
    }

    #[test]
    fn strict_raw_grammar_accepts_only_minimal_supported_variants() {
        assert!(matches!(
            decode_raw(json!({
                "kind": "candidate_clauses",
                "schema_version": AGENT_HOUDINI_PROTOCOL_VERSION,
                "binding": raw_binding(),
                "clauses": ["E = E"],
                "dropped": [],
            })),
            Ok(RawAgentHoudiniResponse::CandidateClauses { .. })
        ));
        assert!(matches!(
            decode_raw(json!({
                "kind": "candidate_counterexample",
                "schema_version": AGENT_HOUDINI_PROTOCOL_VERSION,
                "binding": raw_binding(),
                "input": {"relations": []},
            })),
            Ok(RawAgentHoudiniResponse::CandidateCounterexample { .. })
        ));
    }

    #[test]
    fn raw_grammar_rejects_levels_theorems_partial_and_mixed_variants() {
        let invalid = [
            json!({
                "kind": "candidate_clauses",
                "schema_version": AGENT_HOUDINI_PROTOCOL_VERSION,
                "binding": raw_binding(),
                "clauses": [],
                "dropped": [],
                "level": 0,
            }),
            json!({
                "kind": "candidate_clauses",
                "schema_version": AGENT_HOUDINI_PROTOCOL_VERSION,
                "binding": raw_binding(),
                "clauses": [],
                "dropped": [],
                "new_theorem": {"statement": "secret"},
            }),
            json!({
                "kind": "candidate_clauses",
                "schema_version": AGENT_HOUDINI_PROTOCOL_VERSION,
                "binding": raw_binding(),
                "clauses": [],
            }),
            json!({
                "kind": "candidate_clauses",
                "schema_version": AGENT_HOUDINI_PROTOCOL_VERSION,
                "binding": raw_binding(),
                "clauses": [],
                "dropped": [],
                "input": {"relations": []},
            }),
            json!({
                "kind": "failure",
                "schema_version": AGENT_HOUDINI_PROTOCOL_VERSION,
                "binding": raw_binding(),
            }),
        ];
        assert!(invalid.into_iter().all(|value| decode_raw(value).is_err()));
    }

    fn counterexample(extra: Value) -> Value {
        let mut value = json!({
            "kind": "candidate_counterexample",
            "schema_version": AGENT_HOUDINI_PROTOCOL_VERSION,
            "binding": raw_binding(),
            "input": {"relations": []},
        });
        let object = value
            .as_object_mut()
            .expect("the counterexample template is an object");
        for (key, member) in extra.as_object().expect("the extra members are an object") {
            object.insert(key.clone(), member.clone());
        }
        value
    }

    /// The clause variant's two members, left empty beside a counterexample,
    /// place nothing and drop nothing: they are removed and the instance is
    /// read exactly as if they had never been written.
    #[test]
    fn an_empty_clauses_or_dropped_member_beside_a_counterexample_is_ignored() {
        for extra in [
            json!({"clauses": []}),
            json!({"dropped": []}),
            json!({"clauses": [], "dropped": []}),
        ] {
            let mut value = counterexample(extra);
            assert!(reconcile_counterexample_clause_members(&mut value).is_none());
            assert_eq!(value, counterexample(json!({})));
            assert!(matches!(
                decode_raw(value),
                Ok(RawAgentHoudiniResponse::CandidateCounterexample { .. })
            ));
        }
    }

    #[test]
    fn a_counterexample_carrying_real_clause_content_is_named_at_its_members() {
        for (extra, named) in [
            (
                json!({"clauses": ["(op_zR = \u{2205}[2])"]}),
                vec!["clauses"],
            ),
            (json!({"dropped": [{"clause": 1}]}), vec!["dropped"]),
            (json!({"clauses": "none"}), vec!["clauses"]),
            (json!({"dropped": null}), vec!["dropped"]),
            (
                json!({"clauses": ["(op_zR = \u{2205}[2])"], "dropped": [1]}),
                vec!["clauses", "dropped"],
            ),
            (json!({"clauses": [], "dropped": [1]}), vec!["dropped"]),
        ] {
            let mut value = counterexample(extra);
            let diagnostic = reconcile_counterexample_clause_members(&mut value)
                .expect("clause content beside a counterexample is refused");
            assert_eq!(diagnostic.code(), "malformed_response");
            assert_eq!(diagnostic.path(), Some("$"));
            assert_eq!(
                diagnostic.details(),
                Some(&json!({"missing": [], "unexpected": named, "changed": []}))
            );
        }
    }

    /// The tolerance is the counterexample's alone: a clause response keeps
    /// both members, and every other key of either kind reaches the grammar
    /// exactly as it was written.
    #[test]
    fn the_clause_variant_and_every_other_key_pass_through_unchanged() {
        for value in [
            json!({
                "kind": "candidate_clauses",
                "schema_version": AGENT_HOUDINI_PROTOCOL_VERSION,
                "binding": raw_binding(),
                "clauses": [],
                "dropped": [],
            }),
            counterexample(json!({"level": 0})),
            json!({"kind": "candidate_counterexample"}),
            json!([1]),
        ] {
            let mut reconciled = value.clone();
            assert!(reconcile_counterexample_clause_members(&mut reconciled).is_none());
            assert_eq!(reconciled, value);
        }
    }

    #[test]
    fn recording_observes_every_chunk_and_limit_decision() {
        use super::super::transcript::{TranscriptHeader, TranscriptPins};
        let pins = TranscriptPins {
            task_digest: "a".repeat(64),
            source_digest: "b".repeat(64),
            scope_digest: "c".repeat(64),
            policy_digest: "d".repeat(64),
            runner_digest: "e".repeat(64),
            worker_digest: "f".repeat(64),
            lean_digest: "1".repeat(64),
            vampire_digest: "2".repeat(64),
            profile_digest: "3".repeat(64),
        };
        let recorder = TranscriptRecorder::new(
            TranscriptHeader::new("fixture".into(), "test".into(), pins),
            65536,
        )
        .unwrap();
        let task = dispatch_task("RecordedChunks");
        let directory = dispatch_directory("recorded-chunks");
        let (owner, artifacts) =
            new_artifact_store(&task, ArtifactStoreConfig::new(&directory)).unwrap();
        let mut writer = AgentResponseWriter::new(Some(4));
        writer.recorder = Some(recorder.clone());
        assert!(writer.write_chunk(b"ab").is_ok());
        assert!(writer.write_chunk(b"cdef").is_err());
        assert!(writer.write_chunk(&[0xff]).is_err());
        assert_eq!(writer.bytes, b"abcd");
        let recorded = recorder.finish(&artifacts).unwrap();
        let decoded =
            super::super::transcript::VerifiedTranscript::read(recorded.frames(), recorded.head())
                .unwrap();
        let counts: Vec<_> = decoded
            .events()
            .iter()
            .cloned()
            .map(|event| match event {
                TranscriptEvent::Bytes {
                    bytes,
                    accounting: Some(accounting),
                    ..
                } => (bytes, accounting),
                _ => panic!("unexpected event"),
            })
            .collect();
        assert_eq!(
            counts[0],
            (
                b"ab".to_vec(),
                ResponseChunkAccounting {
                    accepted: true,
                    maximum_bytes: Some(4),
                    observed_bytes: 2,
                    retained_bytes: 2
                }
            )
        );
        assert_eq!(
            counts[1],
            (
                b"cdef".to_vec(),
                ResponseChunkAccounting {
                    accepted: false,
                    maximum_bytes: Some(4),
                    observed_bytes: 6,
                    retained_bytes: 4
                }
            )
        );
        assert_eq!(
            counts[2],
            (
                vec![0xff],
                ResponseChunkAccounting {
                    accepted: false,
                    maximum_bytes: Some(4),
                    observed_bytes: 7,
                    retained_bytes: 4
                }
            )
        );
        drop(artifacts);
        owner.settle().unwrap();
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn raw_grammar_rejects_retired_library_and_plan_fields() {
        let invalid = [
            json!({
                "kind": "candidate_clauses",
                "schema_version": AGENT_HOUDINI_PROTOCOL_VERSION,
                "binding": raw_binding(),
                "clauses": [],
                "dropped": [],
                "library_selections": [],
            }),
            json!({
                "kind": "candidate_clauses",
                "schema_version": AGENT_HOUDINI_PROTOCOL_VERSION,
                "binding": raw_binding(),
                "clauses": [],
                "dropped": [],
                "library_selections": [{
                    "entry_id": "epsilon_max",
                    "target": {"kind": "termination"},
                    "instantiation": {"kind": "opaque"},
                }],
            }),
            json!({
                "kind": "candidate_clauses",
                "schema_version": AGENT_HOUDINI_PROTOCOL_VERSION,
                "binding": {
                    "task_digest": "a".repeat(64),
                    "scope_digest": "b".repeat(64),
                    "run_digest": "c".repeat(64),
                    "consultation_digest": "d".repeat(64),
                    "state_snapshot_digest": "e".repeat(64),
                    "validation_manifest_digest": "f".repeat(64),
                    "prior_active_plan_digest": "1".repeat(64),
                    "request_digest": "2".repeat(64),
                    "validation_ordinal": 0,
                },
                "clauses": [],
                "dropped": [],
            }),
        ];
        assert!(invalid.into_iter().all(|value| decode_raw(value).is_err()));
    }

    /// A refused submission says which keys were wrong.
    ///
    /// The realistic failure is a proposer that echoes the observation's own
    /// `feedback.binding` — six digests — and adds `validation_ordinal`,
    /// leaving out the `request_digest` only the response example carries. A
    /// sentence saying the response is malformed gives it nothing to change,
    /// so the correction names the missing, unexpected and changed keys at the
    /// exact path.
    #[test]
    fn a_refused_submission_names_the_binding_keys_it_got_wrong() {
        let task = dispatch_task("AgentBindingDetails");
        let scope = dispatch_scope(&task);
        let feedback = dispatch_feedback(&task, &scope, '7');
        let policy = AgentConsultationPolicy::default();
        let push = build_push(&feedback, None, 0, &policy, &AgentToolPolicy::default(), 0).unwrap();
        let response = AgentHoudiniResponse::capture(Vec::new(), &push);
        let example = push.candidate_clauses_example().unwrap();
        let exact = example["binding"].clone();

        // The observation's binding plus an ordinal: no request digest.
        let mut echoed = exact.as_object().unwrap().clone();
        echoed.remove("request_digest");
        echoed.insert("policy_digest".to_string(), json!("copied from the push"));
        let wrong = json!({
            "schema_version": AGENT_HOUDINI_PROTOCOL_VERSION,
            "kind": "candidate_clauses",
            "binding": Value::Object(echoed),
            "clauses": [],
            "dropped": [],
        });
        let diagnostic = malformed_response_diagnostic(&wrong, &response);
        assert_eq!(diagnostic.code(), "wrong_response_binding");
        assert_eq!(diagnostic.path(), Some("$.binding"));
        assert_eq!(
            diagnostic.details(),
            Some(&json!({
                "missing": ["request_digest"],
                "unexpected": ["policy_digest"],
                "changed": [],
            }))
        );

        // A whole field of the variant missing is named at the document root.
        let short = json!({
            "schema_version": AGENT_HOUDINI_PROTOCOL_VERSION,
            "kind": "candidate_clauses",
            "binding": exact.clone(),
        });
        let diagnostic = malformed_response_diagnostic(&short, &response);
        assert_eq!(diagnostic.code(), "malformed_response");
        assert_eq!(diagnostic.path(), Some("$"));
        assert_eq!(
            diagnostic.details(),
            Some(&json!({
                "missing": ["clauses", "dropped"],
                "unexpected": [],
                "changed": [],
            }))
        );

        // An unknown kind is named at its own path.
        let diagnostic =
            malformed_response_diagnostic(&json!({"kind": "candidate_guess"}), &response);
        assert_eq!(diagnostic.path(), Some("$.kind"));
        assert_eq!(diagnostic.details().unwrap()["changed"], json!(["kind"]));

        // A submission that decodes but carries another consultation's value
        // is told which value moved, not that something is wrong somewhere.
        let mut stale = exact.as_object().unwrap().clone();
        stale.insert("consultation_digest".to_string(), json!("0".repeat(64)));
        let raw: RawResponseBinding = serde_json::from_value(Value::Object(stale)).unwrap();
        let diagnostics = validate_outer_binding(AGENT_HOUDINI_PROTOCOL_VERSION, &raw, &response);
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].code(), "wrong_response_binding");
        assert_eq!(diagnostics[0].path(), Some("$.binding"));
        assert_eq!(
            diagnostics[0].details(),
            Some(&json!({
                "missing": [],
                "unexpected": [],
                "changed": ["consultation_digest"],
            }))
        );
        // A wrong protocol version is named at its own top-level path, and an
        // otherwise exact binding draws no second diagnostic.
        let raw: RawResponseBinding = serde_json::from_value(exact).unwrap();
        let diagnostics =
            validate_outer_binding(AGENT_HOUDINI_PROTOCOL_VERSION + 1, &raw, &response);
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].path(), Some("$.schema_version"));
        assert_eq!(
            diagnostics[0].details().unwrap()["changed"],
            json!(["schema_version"])
        );

        // A binding that is present but not an object is named at its own
        // path with every key it owes, not as an unexplained malformed
        // response.
        let not_an_object = json!({
            "schema_version": AGENT_HOUDINI_PROTOCOL_VERSION,
            "kind": "candidate_clauses",
            "binding": "copied the digest string instead",
            "clauses": [],
            "dropped": [],
        });
        let diagnostic = malformed_response_diagnostic(&not_an_object, &response);
        assert_eq!(diagnostic.code(), "wrong_response_binding");
        assert_eq!(diagnostic.path(), Some("$.binding"));
        assert_eq!(
            diagnostic.details().unwrap()["missing"],
            json!([
                "consultation_digest",
                "request_digest",
                "run_digest",
                "scope_digest",
                "state_snapshot_digest",
                "task_digest",
                "validation_manifest_digest",
                "validation_ordinal",
            ])
        );
    }

    /// A counterexample submission is returned to the search loop as-is: no
    /// clause admission, no epoch, and the instance reaches the record
    /// unmodified as a JSON value: every member, in place, with its own
    /// nesting. Object member order is not preserved (`serde_json` is built
    /// without `preserve_order`, so members are read back in key order), and
    /// nothing depends on it.
    #[test]
    fn a_counterexample_response_is_accepted_opaquely_without_admission() {
        let task = dispatch_task("AgentCounterexampleAccepted");
        let scope = dispatch_scope(&task);
        let feedback = dispatch_feedback(&task, &scope, '6');
        let policy = AgentConsultationPolicy::default();
        let push = build_push(&feedback, None, 0, &policy, &AgentToolPolicy::default(), 0).unwrap();
        let response = AgentHoudiniResponse::capture(Vec::new(), &push);
        let instance = json!({
            "relations": [{"name": "o:p::E", "rows": [["num:1", "num:2"]]}],
            "unexpected": {"nested": [1, 2, {"deeper": null}]},
        });

        let validation = accept_counterexample_response(response, instance.clone()).unwrap();
        let AgentResponseValidation::Accepted(HoudiniProposal::CandidateCounterexample(proposal)) =
            validation
        else {
            panic!("a bound counterexample response must be accepted as a counterexample proposal");
        };
        assert_eq!(proposal.input(), &instance);
        assert_eq!(
            serde_json::to_string(proposal.input()).unwrap(),
            serde_json::to_string(&instance).unwrap()
        );
        assert_eq!(proposal.binding().task_digest(), feedback.task_digest());
        assert_eq!(
            proposal.binding().consultation_digest(),
            feedback.consultation_digest()
        );
        assert_eq!(proposal.binding().validation_ordinal(), 0);
    }

    /// There is no counterexample fuel bound to configure, and no
    /// consultation bound either: the run deadline and the call-local
    /// timeout are the guards. The default policy names neither.
    #[test]
    fn the_default_consultation_policy_bounds_neither_fuel_nor_consultations() {
        let default = AgentConsultationLimits::default();
        assert_eq!(default.max_consultations, None);
        let bounded = AgentConsultationPolicy::new(AgentConsultationLimits {
            max_consultations: Some(8),
            ..AgentConsultationLimits::default()
        })
        .unwrap();
        assert_ne!(
            AgentConsultationPolicy::default().digest(),
            bounded.digest()
        );
    }

    /// Lean assigns the minimum level and knows no bound. When a run sets
    /// one, a clause above it is rejected at submission with the single
    /// `host_limit` code naming `level_bound` — never parked, and never
    /// reaching an epoch.
    #[test]
    fn a_clause_above_the_level_bound_is_rejected_with_its_own_diagnostic() {
        use super::super::types::ExtendedClause;

        let task = dispatch_task("AgentLevelBound");
        let scope = dispatch_scope(&task);
        let catalog = LeveledClauseCatalog::new(scope.clone(), "7".repeat(64)).unwrap();
        let state =
            LeveledHoudiniState::new_with_max_level(catalog, Some(FrameworkIILevel::ONE)).unwrap();

        let within = ExtendedClause::new(
            scope.clone(),
            json!(["level-bound", "within"]),
            "01-within".to_string(),
            "within".to_string(),
            vec!["o:p::R".to_string()],
            true,
            FrameworkIILevel::ONE,
        );
        let above = ExtendedClause::new(
            scope,
            json!(["level-bound", "above"]),
            "02-above".to_string(),
            "above".to_string(),
            vec!["o:p::R".to_string()],
            true,
            FrameworkIILevel::new(2),
        );
        assert!(!state.exceeds_level_bound(within.minimum_level()));
        assert!(state.exceeds_level_bound(above.minimum_level()));

        let diagnostic = host_limit_diagnostic(&HostLimitRefusal::new(
            "level_bound",
            state.max_level().unwrap().get(),
            above.minimum_level().get(),
        ));
        assert_eq!(diagnostic.code(), "host_limit");
        assert_eq!(
            diagnostic.host_limit(),
            Some(&json!({"limit": "level_bound", "value": 1, "observed": 2}))
        );
        assert!(diagnostic.message().contains("level_bound"));
        assert!(
            diagnostic
                .message()
                .contains("not a defect of the proposal"),
            "a host limit is never reported as a defect of the proposal"
        );

        // A run with no bound never rejects: the halting rule ends a scan on
        // its own.
        let unbounded_catalog =
            LeveledClauseCatalog::new(state.catalog().scope().clone(), "8".repeat(64)).unwrap();
        let unbounded = LeveledHoudiniState::new(unbounded_catalog).unwrap();
        assert!(unbounded.max_level().is_none());
        assert!(!unbounded.exceeds_level_bound(above.minimum_level()));
    }

    #[tokio::test]
    async fn core_clause_drop_is_rejected_and_pending_clause_drop_is_accepted_and_final() {
        use std::future::Future;
        use std::pin::Pin;

        use super::super::ledger::{
            FrameworkIICheckEvidence, FrameworkIICheckOutcome, FrameworkIICheckRequest,
            FrameworkIIInconclusiveReason,
        };
        use super::super::proposal::{FrameworkIIEpochOutcome, run_framework_ii_proposal_epoch};
        use super::super::snapshot::LeveledCandidateSnapshot;
        use super::super::stabilization::{FrameworkIICheckExecution, FrameworkIIChecker};
        use super::super::types::ExtendedClause;

        /// Proves every clause check except `stuck`, whose checks are always
        /// inconclusive, so that clause ends the scan pending. The
        /// termination check is refuted, the ordinary outcome of an epoch.
        struct DropEligibilityChecker {
            stuck: &'static str,
        }

        impl super::super::stabilization::sealed::Sealed for DropEligibilityChecker {}

        impl FrameworkIIChecker for DropEligibilityChecker {
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
                let evidence = FrameworkIICheckEvidence::new(
                    request.request_digest(),
                    format!("drop-eligibility:{}", request.request_digest()),
                )
                .unwrap();
                let stuck = request
                    .snapshot()
                    .records()
                    .get(&request.clause())
                    .is_some_and(|record| record.formula().display() == self.stuck);
                let outcome = if stuck {
                    FrameworkIICheckOutcome::Inconclusive {
                        reason: FrameworkIIInconclusiveReason::TimedOut,
                        progress: evidence,
                    }
                } else {
                    FrameworkIICheckOutcome::Proved(evidence)
                };
                Box::pin(std::future::ready(Ok(FrameworkIICheckExecution::Applied(
                    outcome,
                ))))
            }

            fn check_termination<'a>(
                &'a mut self,
                _core: Arc<LeveledCandidateSnapshot>,
            ) -> Pin<
                Box<
                    dyn Future<Output = Result<FrameworkIICheckExecution, FrameworkIIStateError>>
                        + Send
                        + 'a,
                >,
            > {
                Box::pin(std::future::ready(Ok(FrameworkIICheckExecution::Applied(
                    FrameworkIICheckOutcome::Refuted(
                        FrameworkIICheckEvidence::new(
                            "c".repeat(64),
                            "drop-eligibility-termination",
                        )
                        .unwrap(),
                    ),
                ))))
            }
        }

        let task = dispatch_task("AgentDropEligibility");
        let scope = dispatch_scope(&task);
        let catalog = LeveledClauseCatalog::new(scope.clone(), "3".repeat(64)).unwrap();
        let mut state = LeveledHoudiniState::new(catalog).unwrap();

        let core_clause = ExtendedClause::new(
            scope.clone(),
            json!(["drop-eligibility", "core"]),
            "01-core".to_string(),
            "core".to_string(),
            vec!["o:p::R".to_string()],
            true,
            FrameworkIILevel::ZERO,
        );
        let pending_clause = ExtendedClause::new(
            scope.clone(),
            json!(["drop-eligibility", "pending"]),
            "02-pending".to_string(),
            "pending".to_string(),
            vec!["o:p::R".to_string()],
            true,
            FrameworkIILevel::ZERO,
        );

        // One epoch registers both: the first commits, the second never
        // decides and ends the scan pending.
        let context = state.proposal_context().unwrap();
        let epoch = FrameworkIIProposalEpoch::new(
            context,
            [core_clause.clone(), pending_clause.clone()],
            [],
        )
        .unwrap();
        let mut checker = DropEligibilityChecker { stuck: "pending" };
        let outcome = run_framework_ii_proposal_epoch(&mut state, &mut checker, epoch)
            .await
            .unwrap();
        assert!(matches!(
            outcome.outcome(),
            FrameworkIIEpochOutcome::Refuted { .. }
        ));

        let core_id = state.catalog().find(&core_clause).unwrap().unwrap();
        let pending_id = state.catalog().find(&pending_clause).unwrap().unwrap();
        assert!(state.committed_levels().contains_key(&core_id));
        assert!(state.pending_levels().contains_key(&pending_id));

        let (owner, artifacts) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(dispatch_directory("drop-eligibility")),
        )
        .unwrap();
        let feedback_state = PreCertificateAgentHoudiniState::new(
            Arc::new(task.clone()),
            &artifacts,
            &state,
            Duration::from_secs(30),
            AgentFeedbackPolicy::default(),
        )
        .unwrap();
        let feedback = feedback_state.feedback().clone();
        let wire = feedback.push_value(&[], 0);

        // A forged drop naming the Core clause's exact shown identity (but
        // an arbitrary authorization digest, since Core clauses are never
        // shown a genuine one) is rejected with the specific Core reason.
        let core_entries = wire["core"].as_array().unwrap();
        assert_eq!(core_entries.len(), 1);
        let core_wire_clause = core_entries[0]["clause"].clone();
        let core_drop_raw: RawDropReference = serde_json::from_value(json!({
            "clause": core_wire_clause,
            "consultation_digest": feedback.consultation_digest(),
            "authorization_digest": "0".repeat(64),
        }))
        .unwrap();
        let core_rejection =
            resolve_drops(&feedback, &state, std::slice::from_ref(&core_drop_raw)).unwrap_err();
        assert_eq!(core_rejection.code(), "core_clause_not_droppable");

        // The pending clause's own push entry carries the drop reference.
        assert!(wire.get("retry").is_none());
        let pending_entries = wire["pending"].as_array().unwrap();
        assert_eq!(pending_entries.len(), 1);
        let pending_drop_wire = pending_entries[0]["drop_reference"].clone();
        assert!(!pending_drop_wire.is_null());
        let pending_drop_raw: RawDropReference = serde_json::from_value(pending_drop_wire).unwrap();
        let mut accepted = resolve_drops(&feedback, &state, &[pending_drop_raw]).unwrap();
        assert_eq!(accepted.len(), 1);
        let pending_drop = accepted.remove(0);
        assert_eq!(pending_drop.id(), pending_id);

        // Applying the drop moves the clause to dead-by-drop; a later epoch
        // that submits a fresh clause does not revive it.
        let drop_context = state.proposal_context().unwrap();
        let drop_epoch = FrameworkIIProposalEpoch::new(drop_context, [], [pending_drop]).unwrap();
        let mut drop_checker = DropEligibilityChecker { stuck: "pending" };
        let drop_outcome =
            run_framework_ii_proposal_epoch(&mut state, &mut drop_checker, drop_epoch)
                .await
                .unwrap();
        assert!(!matches!(
            drop_outcome.outcome(),
            FrameworkIIEpochOutcome::Failure(_)
        ));
        assert!(state.is_dropped(pending_id));

        let novel_clause = ExtendedClause::new(
            scope.clone(),
            json!(["drop-eligibility", "novel"]),
            "03-novel".to_string(),
            "novel".to_string(),
            vec!["o:p::R".to_string()],
            true,
            FrameworkIILevel::ZERO,
        );
        let novel_context = state.proposal_context().unwrap();
        let novel_epoch = FrameworkIIProposalEpoch::new(novel_context, [novel_clause], []).unwrap();
        let mut novel_checker = DropEligibilityChecker { stuck: "pending" };
        let novel_outcome =
            run_framework_ii_proposal_epoch(&mut state, &mut novel_checker, novel_epoch)
                .await
                .unwrap();
        assert!(!matches!(
            novel_outcome.outcome(),
            FrameworkIIEpochOutcome::Failure(_)
        ));
        assert!(
            state.is_dropped(pending_id),
            "a dropped clause revives only by its own exact resubmission"
        );
        assert!(!state.pending_levels().contains_key(&pending_id));

        let hidden_policy = AgentFeedbackPolicy::new(super::super::feedback::AgentFeedbackLimits {
            clause_page_items: 1,
            ..super::super::feedback::AgentFeedbackLimits::default()
        })
        .unwrap();
        let refreshed = PreCertificateAgentHoudiniState::new(
            Arc::new(task.clone()),
            &artifacts,
            &state,
            Duration::from_secs(30),
            hidden_policy,
        )
        .unwrap();
        let manifest = refreshed.feedback().validation_manifest();
        let old_identity = manifest.read_clause_identity(pending_id).unwrap();
        assert!(manifest.resolve_shown_clause(&old_identity).is_none());
        assert!(manifest.resolve_read_clause(&old_identity).is_some());
        let forged = AgentClauseIdentity::from_wire_fields(
            pending_id,
            "0".repeat(64),
            old_identity.formula_digest().to_owned(),
        );
        assert!(manifest.resolve_read_clause(&forged).is_none());
        assert!(state.is_dropped(pending_id));

        drop(artifacts);
        owner.settle().unwrap();
    }
    /// An admission diagnostic keeps the position Lean computed for it.
    ///
    /// The proposer has no copy of the clause list it sent, so `item_index`
    /// alone names a clause it cannot look at; the offset is what makes the
    /// refusal answerable without spending a round on `validate_clauses`.
    #[test]
    fn a_submission_path_admission_diagnostic_carries_its_offset() {
        use super::super::types::{AdmissionCorrection, AdmissionDiagnostic};

        let correction = AdmissionCorrection::new(vec![
            AdmissionDiagnostic::new(
                "clause_syntax_error".to_owned(),
                "clause does not match the surface grammar".to_owned(),
                Some(6),
                None,
                Some(97),
            ),
            AdmissionDiagnostic::new(
                "clause_schema_error".to_owned(),
                "clause is not well formed over the ambient schema".to_owned(),
                Some(1),
                Some("$.clauses".to_owned()),
                None,
            ),
        ]);
        let diagnostics = admission_diagnostics(&correction);
        assert_eq!(diagnostics[0].offset(), Some(97));
        assert_eq!(diagnostics[0].item_index(), Some(6));
        assert_eq!(diagnostics[0].wire_value()["offset"], json!(97));
        // A diagnostic that located nothing carries no offset at all rather
        // than a null a reader has to tell from a position.
        assert_eq!(diagnostics[1].offset(), None);
        assert_eq!(diagnostics[1].wire_value().get("offset"), None);
    }

    /// A dead-clause refusal names the formula it refused.
    #[test]
    fn a_dead_clause_refusal_names_the_formula_the_proposer_sent() {
        let reason = FrameworkIIDeadReason::ProphecyFreeInitializationRefuted { attempt: 9 };
        let diagnostic = dead_clause_diagnostic(reason, "(op_zT = \u{2205}[2])");
        assert_eq!(diagnostic.code(), "dead_clause_rejected");
        assert!(diagnostic.message().contains("(op_zT = \u{2205}[2])"));
        // A formula past the echo bound is cut, never dropped, and never
        // crowds the reason out of the message.
        let long = "x".repeat(MAX_DEAD_CLAUSE_BYTES * 2);
        let diagnostic = dead_clause_diagnostic(reason, &long);
        assert!(diagnostic.message().len() < long.len());
        assert!(diagnostic.message().contains("ledger attempt 9"));
        // An identity with no readable source says so instead of naming "".
        let diagnostic = dead_clause_diagnostic(reason, "");
        assert!(diagnostic.message().contains("the formula you resubmitted"));
    }
}
