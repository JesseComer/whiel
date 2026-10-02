//! Versioned proposer lifecycle and bounded response contract.
//! Host-only construction and transcript accounting grant no Houdini mutation.

use super::agent::AgentRequestAuthority;
use crate::encoding::{bytes_sha256, canonical_value_sha256};
use crate::framework2::AgentConsultationPolicy;
use crate::framework2::transcript::{
    ResponseChunkAccounting, TranscriptRecorder, TranscriptStream,
};
use crate::proposer_api::{AgentTool, AgentToolSurface};
use crate::runtime::CancellationToken;
use serde_json::{Value, json};
use std::fmt;
use std::future::Future;
use std::pin::Pin;
use std::sync::Arc;

/// One immutable, already-sanitized verifier observation.
#[derive(Clone)]
pub struct AgentPush {
    pub(super) replay_policy: AgentConsultationPolicy,
    pub(super) request_deadline: Option<tokio::time::Instant>,
    pub(super) observation: Arc<crate::proposer_api::ObservationSnapshot>,
    pub(super) negotiated_api: crate::proposer_api::NegotiatedApi,
    pub(super) bytes: Arc<[u8]>,
    pub(super) digest: Arc<str>,
    pub(super) authority: Arc<AgentRequestAuthority>,
}

impl AgentPush {
    /// Remaining time under B's actual local consultation deadline. This is
    /// transport metadata, not part of the immutable observation or binding.
    /// `None` means no separate consultation deadline; the enclosing run still
    /// enforces its overall deadline. Expired deadlines return zero.
    pub fn remaining_request_budget_ns(&self) -> std::io::Result<Option<u64>> {
        self.request_deadline
            .map(|deadline| {
                u64::try_from(
                    deadline
                        .saturating_duration_since(tokio::time::Instant::now())
                        .as_nanos(),
                )
                .map_err(|_| {
                    std::io::Error::new(
                        std::io::ErrorKind::InvalidData,
                        "remaining request budget exceeds the wire range",
                    )
                })
            })
            .transpose()
    }

    pub fn observation(&self) -> &crate::proposer_api::ObservationSnapshot {
        &self.observation
    }

    pub fn negotiated_api(&self) -> &crate::proposer_api::NegotiatedApi {
        &self.negotiated_api
    }

    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }

    pub fn digest(&self) -> &str {
        &self.digest
    }

    /// Engine-approved empty response envelope for outer proposer presentation.
    /// Its binding is derived from this exact immutable push, never supplied by C.
    pub fn candidate_clauses_example(&self) -> Option<Value> {
        let value = serde_json::to_value(&self.observation.binding).ok()?;
        let mut binding = value.as_object()?.clone();
        binding.remove("policy_digest");
        binding.insert("request_digest".into(), json!(self.digest()));
        Some(
            json!({"schema_version":crate::proposer_api::version::AGENT_HOUDINI_PROTOCOL_VERSION,"kind":"candidate_clauses","binding":binding,"clauses":[],"dropped":[]}),
        )
    }

    pub fn validation_ordinal(&self) -> usize {
        self.authority.validation_ordinal
    }
}

impl fmt::Debug for AgentPush {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("AgentPush")
            .field("digest", &self.digest)
            .field("encoded_bytes", &self.bytes.len())
            .field("validation_ordinal", &self.authority.validation_ordinal)
            .finish_non_exhaustive()
    }
}

/// A terminal endpoint fault is operational, independent of both a resource
/// refusal and the ability to join cleanup. Ordinary request failure or source
/// exhaustion does not set this status.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProposerTerminalFailure {
    ProtocolViolation,
    EndpointExited,
    EndpointFailure,
}
impl fmt::Display for ProposerTerminalFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::ProtocolViolation => "proposer endpoint violated the protocol",
            Self::EndpointExited => "proposer endpoint exited before completion",
            Self::EndpointFailure => "proposer endpoint failed",
        })
    }
}
impl std::error::Error for ProposerTerminalFailure {}

/// Provider result. Content bytes acquire authority only after validation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AgentSourceOutcome {
    Response,
    SourceExhausted,
    NoResponse,
    TransportFailure,
}

pub type AgentSourceFuture<'a> = Pin<Box<dyn Future<Output = AgentSourceOutcome> + Send + 'a>>;
pub type AgentSourceCleanupFuture<'a> = crate::proposer_api::wire::ProposerCleanupFuture<'a>;

/// Read-only observer for cancellation of one source request.
#[derive(Clone, Debug)]
pub struct AgentSourceCancellation {
    token: CancellationToken,
}

impl AgentSourceCancellation {
    pub(crate) fn new(token: CancellationToken) -> Self {
        Self { token }
    }

    pub fn is_cancelled(&self) -> bool {
        self.token.is_cancelled()
    }

    pub async fn cancelled(&self) {
        self.token.cancelled().await;
    }

    /// Read the owner's cancellation cause after `cancelled()` resolves.
    /// Exact owner timestamps distinguish a deadline from an earlier external
    /// stop even when this observer runs after the deadline. Ordinary request
    /// closure is `Cancelled`; the host classifies its own failures separately.
    pub fn reason(&self) -> crate::proposer_api::wire::CancellationReason {
        if self.token.cancelled_at_or_after_deadline() {
            crate::proposer_api::wire::CancellationReason::Deadline
        } else {
            crate::proposer_api::wire::CancellationReason::Cancelled
        }
    }

    /// The underlying token (Pass 7.5c): the `validate_clauses` tool body
    /// forwards it unchanged to the engine evaluation adapter's worker
    /// operation, so a cancelled consultation also cancels an in-flight
    /// evaluation rather than leaving it to run to completion unread.
    pub(crate) fn token(&self) -> &CancellationToken {
        &self.token
    }
}

/// Agent-owned bounded sink for one raw provider response.
///
/// A source streams bytes into this sink instead of constructing a complete
/// unbounded body. Once the cap is crossed, the sink retains at most the cap
/// and rejects every subsequent chunk.
pub struct AgentResponseWriter {
    pub(super) bytes: Vec<u8>,
    /// The run's optional `reply_bytes` host limit. `None` — the default —
    /// accepts a reply of any size.
    pub(super) maximum_bytes: Option<usize>,
    pub(super) observed_bytes: usize,
    pub(super) limit_exceeded: bool,
    pub(super) recorder: Option<TranscriptRecorder>,
}

impl fmt::Debug for AgentResponseWriter {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("AgentResponseWriter")
            .field("maximum_bytes", &self.maximum_bytes)
            .field("observed_bytes", &self.observed_bytes)
            .field("retained_bytes", &self.bytes.len())
            .field("limit_exceeded", &self.limit_exceeded)
            .finish_non_exhaustive()
    }
}

impl AgentResponseWriter {
    pub(crate) fn discard_for_resource_failure(&mut self) {
        self.bytes.clear();
        self.observed_bytes = 0;
        self.limit_exceeded = false;
    }
    pub(super) fn new(maximum_bytes: Option<usize>) -> Self {
        Self {
            bytes: Vec::new(),
            maximum_bytes,
            observed_bytes: 0,
            limit_exceeded: false,
            recorder: None,
        }
    }

    #[cfg(test)]
    pub(crate) fn fixture_for_tests(maximum_bytes: Option<usize>) -> Self {
        Self::new(maximum_bytes)
    }

    #[cfg(test)]
    pub(crate) fn fixture_bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// The run's `reply_bytes` host limit, or `None` when it sets none.
    pub fn maximum_bytes(&self) -> Option<usize> {
        self.maximum_bytes
    }

    pub fn write_chunk(&mut self, chunk: &[u8]) -> Result<(), AgentResponseLimitExceeded> {
        let result = self.write_chunk_inner(chunk);
        if let Some(recorder) = &self.recorder {
            recorder.bytes(
                TranscriptStream::Response,
                chunk,
                Some(ResponseChunkAccounting {
                    accepted: result.is_ok(),
                    maximum_bytes: self.maximum_bytes,
                    observed_bytes: self.observed_bytes,
                    retained_bytes: self.bytes.len(),
                }),
            );
        }
        result
    }

    fn write_chunk_inner(&mut self, chunk: &[u8]) -> Result<(), AgentResponseLimitExceeded> {
        self.observed_bytes = self.observed_bytes.saturating_add(chunk.len());
        let Some(maximum) = self.maximum_bytes else {
            self.bytes.extend_from_slice(chunk);
            return Ok(());
        };
        if self.limit_exceeded {
            return Err(AgentResponseLimitExceeded { limit: maximum });
        }
        let remaining = maximum.saturating_sub(self.bytes.len());
        if chunk.len() > remaining {
            self.bytes.extend_from_slice(&chunk[..remaining]);
            self.limit_exceeded = true;
            return Err(AgentResponseLimitExceeded { limit: maximum });
        }
        self.bytes.extend_from_slice(chunk);
        Ok(())
    }

    pub(super) fn limit_exceeded(&self) -> bool {
        self.limit_exceeded
    }

    pub(super) fn oversized_event_digest(&self, request_digest: &str) -> Arc<str> {
        Arc::from(canonical_value_sha256(&json!({
            "domain": "whiel-oversized-agent-response-v1",
            "request_digest": request_digest,
            "maximum_bytes": self.maximum_bytes,
            "observed_bytes_at_least": self.observed_bytes,
            "bounded_prefix_digest": bytes_sha256(&self.bytes),
        })))
    }

    pub(super) fn into_bytes(self) -> Vec<u8> {
        self.bytes
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AgentResponseLimitExceeded {
    limit: usize,
}

impl AgentResponseLimitExceeded {
    pub fn limit(&self) -> usize {
        self.limit
    }
}

impl fmt::Display for AgentResponseLimitExceeded {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "Agent response exceeds this run's {}-byte reply_bytes host limit",
            self.limit
        )
    }
}

impl std::error::Error for AgentResponseLimitExceeded {}

/// Provider-neutral consultation session which receives no root-runtime or
/// semantic authority.
///
/// One `consult` call is one pushed document followed by a small tool
/// surface the proposer may call before submitting its response. Neither the
/// push nor the queries grant semantic mutation authority. Request cancellation
/// revokes the query surface. `quiesce_request` joins all in-flight request work
/// after the consultation future is dropped, including after a polling panic;
/// it does not shut down the input-scoped endpoint or idle proposer-owned work.
/// `shutdown` is terminal and joins the endpoint and all its owned descendants.
/// Both hooks are idempotent and return an explicit error when cleanup cannot be
/// established. Cleanup errors prevent successful admission or certification.
/// Constructing/destroying consultation futures and constructing/polling cleanup
/// futures must not panic. Work begins only when a consultation future is polled.
pub trait AgentProvider: Send {
    fn api_capabilities(&self) -> crate::proposer_api::ApiCapabilities {
        crate::proposer_api::ApiCapabilities::current(
            AgentTool::ALL
                .into_iter()
                .map(|tool| tool.name().to_owned()),
        )
    }

    fn resource_failure(&self) -> Option<String> {
        None
    }

    fn terminal_failure(&self) -> Option<ProposerTerminalFailure> {
        None
    }

    fn consult<'a>(
        &'a mut self,
        push: &'a AgentPush,
        tools: &'a dyn AgentToolSurface,
        response: &'a mut AgentResponseWriter,
        cancellation: AgentSourceCancellation,
    ) -> AgentSourceFuture<'a>;

    fn quiesce_request(&mut self) -> crate::proposer_api::wire::ProposerCleanupFuture<'_>;

    fn shutdown(
        &mut self,
        reason: crate::proposer_api::wire::ShutdownReason,
    ) -> crate::proposer_api::wire::ProposerCleanupFuture<'_>;
}
