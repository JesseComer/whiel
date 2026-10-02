//! Owner-held, bounded recording of actual provider traffic.
//!
//! Raw bytes live only in the bounded pending buffer. Redaction precedes every
//! digest and publication. A closed transcript is immutable; correspondence
//! evidence belongs to a separate artifact, never to this byte chain.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::io::{self, Write};
use std::ops::ControlFlow;
use std::sync::{Arc, Mutex};

use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::artifact::{ArtifactKind, ArtifactRef, ArtifactStore, Retention, ScopeTag};
use crate::encoding::bytes_sha256;

use super::agent::{
    Agent, AgentConsultationPolicy, AgentProvider, AgentPush, AgentResponseWriter,
    AgentSourceCancellation, AgentSourceCleanupFuture, AgentSourceFuture,
};
use super::strict_json::decode_strict_json;
use super::tools::{AgentToolResponseFuture, AgentToolSurface};

pub const TRANSCRIPT_VERSION: u64 = 3;
/// Artifact scope the consultation frames are published under.
///
/// A run publishes other root-scoped `runtime_trace` records — protected
/// theorem selection, for one — so the frames of a consultation record need a
/// scope of their own for a manifest reader to select exactly the chain
/// without parsing payloads. The frame format and its version are unaffected.
pub const CONSULTATION_RECORD_SCOPE: &str = "consultation-records";
pub const DEFAULT_TRANSCRIPT_READ_BYTES: usize = 64 * 1024 * 1024;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TranscriptCoordinates {
    pub consultation: u64,
    pub validation: u64,
    pub transport: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TranscriptPins {
    pub task_digest: String,
    pub source_digest: String,
    pub scope_digest: String,
    pub policy_digest: String,
    pub runner_digest: String,
    pub worker_digest: String,
    pub lean_digest: String,
    pub vampire_digest: String,
    pub profile_digest: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TranscriptHeader {
    pub version: u64,
    pub proposer_identity: String,
    pub source_run_identity: String,
    pub proposal_schema: u64,
    pub feedback_schema: u64,
    pub presentation_schema: u64,
    pub pins: TranscriptPins,
}

/// The toolchain half of a run's identity pins, resolved once by the host.
///
/// The run itself owns the other half — task, source, scope and policy — so
/// only what the host verified against its own lock is passed in here.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TranscriptToolchainPins {
    pub runner_digest: String,
    pub worker_digest: String,
    pub lean_digest: String,
    pub vampire_digest: String,
    pub profile_digest: String,
}

impl TranscriptHeader {
    /// The header one live run records under.
    ///
    /// The four run-owned pins are read from the run's own authorities, so a
    /// production recording carries exactly the identities the acceptance
    /// fixture states by hand. Nothing here starts, inspects or names a
    /// provider beyond the identity its host already resolved.
    pub fn for_live_run(
        proposer_identity: String,
        task: &crate::task::SynthesisTask,
        state: &super::LeveledHoudiniState,
        policy: &AgentConsultationPolicy,
        toolchain: TranscriptToolchainPins,
    ) -> Self {
        let scope = state.catalog().scope();
        Self::new(
            proposer_identity,
            state.catalog().instance_digest().to_owned(),
            TranscriptPins {
                task_digest: crate::encoding::canonical_value_sha256(
                    &super::catalog::task_identity_fields(scope),
                ),
                source_digest: task.identity().source_digest().as_str().to_owned(),
                scope_digest: scope.identity_sha256().to_owned(),
                policy_digest: policy.digest().to_owned(),
                runner_digest: toolchain.runner_digest,
                worker_digest: toolchain.worker_digest,
                lean_digest: toolchain.lean_digest,
                vampire_digest: toolchain.vampire_digest,
                profile_digest: toolchain.profile_digest,
            },
        )
    }

    pub fn new(
        proposer_identity: String,
        source_run_identity: String,
        pins: TranscriptPins,
    ) -> Self {
        Self {
            version: TRANSCRIPT_VERSION,
            proposer_identity,
            source_run_identity,
            proposal_schema: super::agent::AGENT_HOUDINI_PROTOCOL_VERSION,
            feedback_schema: super::feedback::AGENT_FEEDBACK_SCHEMA_VERSION,
            presentation_schema: super::feedback::AGENT_PRESENTATION_SCHEMA_VERSION,
            pins,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TranscriptStream {
    Push,
    Response,
    Correction,
}

impl TranscriptStream {
    fn semantic(self) -> bool {
        matches!(self, Self::Push | Self::Response | Self::Correction)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ResponseChunkAccounting {
    pub accepted: bool,
    #[serde(deserialize_with = "required_nullable")]
    pub maximum_bytes: Option<usize>,
    pub observed_bytes: usize,
    pub retained_bytes: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum TranscriptEvent {
    FinalOwnerProjection {
        projection: Box<super::ReplayFinalStateProjection>,
    },
    FinalOwnerUnavailable {
        reason: super::ReplayCaptureError,
    },
    OwnerProjection {
        coordinates: TranscriptCoordinates,
        projection: Box<super::replay_correspondence::ReplayPushProjection>,
    },
    OwnerUnavailable {
        coordinates: TranscriptCoordinates,
        reason: super::replay_correspondence::ReplayCaptureError,
    },
    Bytes {
        coordinates: TranscriptCoordinates,
        stream: TranscriptStream,
        bytes: Vec<u8>,
        #[serde(deserialize_with = "required_nullable")]
        accounting: Option<ResponseChunkAccounting>,
    },
    ToolCall {
        coordinates: TranscriptCoordinates,
        call_id: u64,
        name: String,
        arguments: Vec<u8>,
    },
    ToolResponse {
        coordinates: TranscriptCoordinates,
        call_id: u64,
        response: Vec<u8>,
    },
    Lifecycle {
        coordinates: TranscriptCoordinates,
        event: TranscriptLifecycle,
    },
    Outcome {
        coordinates: TranscriptCoordinates,
        outcome: TranscriptOutcome,
    },
    ProviderOutcome {
        coordinates: TranscriptCoordinates,
        outcome: TranscriptProviderOutcome,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TranscriptLifecycle {
    RequestStarted,
    RequestCancelled,
    RequestPanicked,
    CleanupJoined,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TranscriptOutcome {
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TranscriptProviderOutcome {
    Response,
    SourceExhausted,
    NoResponse,
    TransportFailure,
}
impl From<&super::agent::AgentSourceOutcome> for TranscriptProviderOutcome {
    fn from(value: &super::agent::AgentSourceOutcome) -> Self {
        match value {
            super::agent::AgentSourceOutcome::Response => Self::Response,
            super::agent::AgentSourceOutcome::SourceExhausted => Self::SourceExhausted,
            super::agent::AgentSourceOutcome::NoResponse => Self::NoResponse,
            super::agent::AgentSourceOutcome::TransportFailure => Self::TransportFailure,
        }
    }
}

impl From<super::agent::AgentRequestAttemptOutcome> for TranscriptOutcome {
    fn from(value: super::agent::AgentRequestAttemptOutcome) -> Self {
        use super::agent::AgentRequestAttemptOutcome as A;
        match value {
            A::Received => Self::Received,
            A::Accepted => Self::Accepted,
            A::Correctable => Self::Correctable,
            A::ValidationFailure => Self::ValidationFailure,
            A::OversizedResponse => Self::OversizedResponse,
            A::SourceExhausted => Self::SourceExhausted,
            A::NoResponse => Self::NoResponse,
            A::TransportFailure => Self::TransportFailure,
            A::SourceProtocolFailure => Self::SourceProtocolFailure,
            A::Cancelled => Self::Cancelled,
            A::RecordingFailure => Self::RecordingFailure,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ReplayIneligibility {
    SemanticRedaction,
    PayloadNotRetained,
    IncompleteToolCall,
    MissingOwnerEvidence,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
enum Record {
    Header {
        header: TranscriptHeader,
    },
    Event {
        event: TranscriptEvent,
    },
    Closed {
        event_count: u64,
        ineligible: Vec<ReplayIneligibility>,
    },
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Frame {
    version: u64,
    ordinal: u64,
    #[serde(deserialize_with = "required_nullable")]
    previous_digest: Option<String>,
    payload: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TranscriptError {
    LimitExceeded,
    Closed,
    Poisoned,
    Malformed,
    UnsupportedVersion,
    BrokenChain {
        ordinal: usize,
    },
    Incomplete,
    NotReplayable(Vec<ReplayIneligibility>),
    /// The frames could not be published. `published` counts the frames that
    /// were promoted before the refusal, and is 0 for every refusal the
    /// staging pass raises.
    Publication {
        published: usize,
    },
    InvalidEvent,
}

impl fmt::Display for TranscriptError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "provider transcript: {self:?}")
    }
}
impl std::error::Error for TranscriptError {}

struct Pending {
    header: TranscriptHeader,
    events: Vec<TranscriptEvent>,
    bytes: usize,
    maximum_bytes: usize,
    next_call: u64,
    coordinates: TranscriptCoordinates,
    error: Option<TranscriptError>,
    closed: bool,
    final_owner: Option<Arc<super::ReplayFinalStateOwner>>,
}

/// An owner-held recording handle. Its private final comparison owner retains
/// fresh checked evidence; only inert projections enter the transcript. Never
/// place this handle or its opaque comparison owner in a provider push.
#[derive(Clone)]
pub struct TranscriptRecorder(Arc<Mutex<Pending>>);

impl TranscriptRecorder {
    pub fn new(header: TranscriptHeader, maximum_bytes: usize) -> Result<Self, TranscriptError> {
        check_header_version(&header)?;
        let bytes =
            encoded_size(&header, maximum_bytes).map_err(|_| TranscriptError::LimitExceeded)?;
        if bytes > maximum_bytes {
            return Err(TranscriptError::LimitExceeded);
        }
        Ok(Self(Arc::new(Mutex::new(Pending {
            header,
            events: Vec::new(),
            bytes,
            maximum_bytes,
            next_call: 0,
            coordinates: TranscriptCoordinates {
                consultation: 0,
                validation: 0,
                transport: 0,
            },
            error: None,
            closed: false,
            final_owner: None,
        }))))
    }

    pub fn final_state_owner(&self) -> Option<Arc<super::ReplayFinalStateOwner>> {
        self.0
            .lock()
            .ok()
            .and_then(|pending| pending.final_owner.clone())
    }
    pub(crate) fn final_owner(
        &self,
        result: Result<super::ReplayFinalStateOwner, super::ReplayCaptureError>,
    ) {
        match result {
            Ok(owner) => {
                let Ok(mut pending) = self.0.lock() else {
                    return;
                };
                if pending.error.is_some() || pending.closed {
                    return;
                }
                if pending.final_owner.is_some() {
                    pending.error = Some(TranscriptError::InvalidEvent);
                    return;
                }
                if encoded_size(
                    owner.projection(),
                    pending.maximum_bytes.saturating_sub(pending.bytes),
                )
                .is_err()
                {
                    pending.error = Some(TranscriptError::LimitExceeded);
                    return;
                }
                let event = TranscriptEvent::FinalOwnerProjection {
                    projection: Box::new(owner.projection().clone()),
                };
                push_event(&mut pending, event);
                if pending.error.is_none() {
                    pending.final_owner = Some(Arc::new(owner));
                }
            }
            Err(reason) => self.record(TranscriptEvent::FinalOwnerUnavailable { reason }),
        }
    }
    pub fn status(&self) -> Result<(), TranscriptError> {
        let pending = self.0.lock().map_err(|_| TranscriptError::Poisoned)?;
        match &pending.error {
            Some(error) => Err(error.clone()),
            None if pending.closed => Err(TranscriptError::Closed),
            None => Ok(()),
        }
    }

    pub(crate) fn coordinates(&self, coordinates: TranscriptCoordinates) {
        if let Ok(mut pending) = self.0.lock() {
            pending.coordinates = coordinates;
        }
    }

    pub(crate) fn current_coordinates(&self) -> TranscriptCoordinates {
        self.0
            .lock()
            .map(|p| p.coordinates)
            .unwrap_or(TranscriptCoordinates {
                consultation: 0,
                validation: 0,
                transport: 0,
            })
    }

    pub fn record(&self, event: TranscriptEvent) {
        let Ok(mut pending) = self.0.lock() else {
            return;
        };
        push_event(&mut pending, event);
    }

    pub(crate) fn owner(&self, push: &super::AgentPush) {
        let remaining = match self.0.lock() {
            Ok(p) if p.error.is_none() && !p.closed => p.maximum_bytes.saturating_sub(p.bytes),
            _ => return,
        };
        let coordinates = self.current_coordinates();
        match super::replay_correspondence::ReplayPushProjection::capture_bounded(push, remaining) {
            Ok(projection) => self.record(TranscriptEvent::OwnerProjection {
                coordinates,
                projection: Box::new(projection),
            }),
            Err(super::replay_correspondence::ReplayCaptureError::LimitExceeded) => {
                if let Ok(mut p) = self.0.lock() {
                    p.error = Some(TranscriptError::LimitExceeded);
                }
            }
            Err(reason) => self.record(TranscriptEvent::OwnerUnavailable {
                coordinates,
                reason,
            }),
        }
    }

    pub(crate) fn bytes(
        &self,
        stream: TranscriptStream,
        bytes: &[u8],
        accounting: Option<ResponseChunkAccounting>,
    ) {
        // Refuse before copying a provider-controlled chunk.
        if !self.can_copy(bytes.len()) {
            return;
        }
        self.record(TranscriptEvent::Bytes {
            coordinates: self.current_coordinates(),
            stream,
            bytes: bytes.to_vec(),
            accounting,
        });
    }

    fn can_copy(&self, bytes: usize) -> bool {
        let Ok(mut pending) = self.0.lock() else {
            return false;
        };
        if pending.error.is_some() || pending.closed {
            return false;
        }
        if bytes > pending.maximum_bytes.saturating_sub(pending.bytes) {
            pending.error = Some(TranscriptError::LimitExceeded);
            return false;
        }
        true
    }

    fn encode<T: Serialize>(&self, value: &T) -> Option<Vec<u8>> {
        let mut pending = self.0.lock().ok()?;
        if pending.error.is_some() || pending.closed {
            return None;
        }
        let remaining = pending.maximum_bytes.saturating_sub(pending.bytes);
        match encoded_size(value, remaining) {
            Ok(_) => serde_json::to_vec(value).ok(),
            Err(_) => {
                pending.error = Some(TranscriptError::LimitExceeded);
                None
            }
        }
    }

    pub(crate) fn lifecycle(&self, event: TranscriptLifecycle) {
        self.record(TranscriptEvent::Lifecycle {
            coordinates: self.current_coordinates(),
            event,
        });
    }

    fn tool_call(
        &self,
        coordinates: TranscriptCoordinates,
        name: &str,
        args: &Value,
    ) -> Option<u64> {
        // Id allocation and invocation publication share one linearization
        // point even when provider tools are called from different threads.
        let mut pending = self.0.lock().ok()?;
        if pending.error.is_some() || pending.closed {
            return None;
        }
        let remaining = pending.maximum_bytes.saturating_sub(pending.bytes);
        if name.len() > remaining || encoded_size(args, remaining - name.len()).is_err() {
            pending.error = Some(TranscriptError::LimitExceeded);
            return None;
        }
        let call_id = pending.next_call;
        let Some(next_call) = call_id.checked_add(1) else {
            pending.error = Some(TranscriptError::LimitExceeded);
            return None;
        };
        let arguments = serde_json::to_vec(args).ok()?;
        push_event(
            &mut pending,
            TranscriptEvent::ToolCall {
                coordinates,
                call_id,
                name: name.to_owned(),
                arguments,
            },
        );
        if pending.error.is_some() {
            return None;
        }
        pending.next_call = next_call;
        Some(call_id)
    }

    /// Seal exactly once, sanitize the bounded pending buffer, then publish
    /// the immutable frames as one staged set of RuntimeTrace records under
    /// the recording's own scope. Any publication failure returns an error
    /// and no usable closure receipt; the error says how many frames were
    /// promoted, which is none for every refusal raised while staging.
    /// CertificateOnly returns no bytes.
    pub fn finish(&self, store: &ArtifactStore) -> Result<RecordedTranscript, TranscriptError> {
        let (mut header, mut events) = {
            let mut pending = self.0.lock().map_err(|_| TranscriptError::Poisoned)?;
            if let Some(error) = &pending.error {
                return Err(error.clone());
            }
            if pending.closed {
                return Err(TranscriptError::Closed);
            }
            pending.closed = true;
            (pending.header.clone(), std::mem::take(&mut pending.events))
        };
        let incomplete_calls = validate_events(&events)?;
        let header_changed = sanitize_header(&mut header)?;
        let semantic_changed = redact_events(&mut events) || header_changed;
        let mut ineligible = Vec::new();
        if validate_owner_events(&events)? {
            ineligible.push(ReplayIneligibility::MissingOwnerEvidence);
        }
        if incomplete_calls {
            ineligible.push(ReplayIneligibility::IncompleteToolCall);
        }
        if semantic_changed {
            ineligible.push(ReplayIneligibility::SemanticRedaction);
        }
        let retained = store.retention() == Retention::All;
        if !retained {
            ineligible.push(ReplayIneligibility::PayloadNotRetained);
        }
        let event_count = events.len() as u64;
        let records = std::iter::once(Record::Header { header })
            .chain(events.into_iter().map(|event| Record::Event { event }))
            .chain(std::iter::once(Record::Closed {
                event_count,
                ineligible: ineligible.clone(),
            }));
        let mut payloads = Vec::new();
        let mut previous_digest = None;
        for (ordinal, record) in records.enumerate() {
            let payload = serde_json::to_vec(&record).map_err(|_| TranscriptError::Malformed)?;
            let frame = Frame {
                version: TRANSCRIPT_VERSION,
                ordinal: ordinal as u64,
                previous_digest,
                payload,
            };
            let bytes = serde_json::to_vec(&frame).map_err(|_| TranscriptError::Malformed)?;
            previous_digest = Some(bytes_sha256(&bytes));
            payloads.push(bytes);
        }
        // The whole chain is staged before any frame is promoted, so a refused
        // recording leaves no prefix behind and the closure receipt is either
        // complete or absent.
        let artifacts = store
            .scoped(ScopeTag::named(CONSULTATION_RECORD_SCOPE))
            .publish_set(ArtifactKind::RuntimeTrace, &payloads)
            .map_err(|failure| {
                let error = TranscriptError::Publication {
                    published: failure.published().len(),
                };
                if let Ok(mut pending) = self.0.lock() {
                    pending.error = Some(error.clone());
                }
                error
            })?;
        let frames = if retained { payloads } else { Vec::new() };
        Ok(RecordedTranscript {
            frames,
            artifacts,
            head: previous_digest.ok_or(TranscriptError::Incomplete)?,
            ineligible,
        })
    }
}

pub struct RecordedTranscript {
    frames: Vec<Vec<u8>>,
    artifacts: Vec<ArtifactRef>,
    head: String,
    ineligible: Vec<ReplayIneligibility>,
}

impl RecordedTranscript {
    pub fn frames(&self) -> &[Vec<u8>] {
        &self.frames
    }
    pub fn artifacts(&self) -> &[ArtifactRef] {
        &self.artifacts
    }
    pub fn head(&self) -> &str {
        &self.head
    }
    pub fn ineligibility(&self) -> &[ReplayIneligibility] {
        &self.ineligible
    }
    pub fn require_replayable(&self) -> Result<(), TranscriptError> {
        if self.ineligible.is_empty() {
            Ok(())
        } else {
            Err(TranscriptError::NotReplayable(self.ineligible.clone()))
        }
    }
}

pub struct VerifiedTranscript {
    header: TranscriptHeader,
    events: Vec<TranscriptEvent>,
    ineligible: Vec<ReplayIneligibility>,
    head: String,
}

impl VerifiedTranscript {
    pub fn header(&self) -> &TranscriptHeader {
        &self.header
    }
    pub fn events(&self) -> &[TranscriptEvent] {
        &self.events
    }
    pub fn ineligibility(&self) -> &[ReplayIneligibility] {
        &self.ineligible
    }
    pub fn head(&self) -> &str {
        &self.head
    }

    /// `expected_head` comes from the owner's retained closure receipt. A hash
    /// chain detects mutation; it does not authenticate an untrusted author.
    pub fn read(frames: &[Vec<u8>], expected_head: &str) -> Result<Self, TranscriptError> {
        Self::read_bounded(frames, expected_head, DEFAULT_TRANSCRIPT_READ_BYTES)
    }

    pub fn read_bounded(
        frames: &[Vec<u8>],
        expected_head: &str,
        maximum_bytes: usize,
    ) -> Result<Self, TranscriptError> {
        frames.iter().try_fold(0usize, |size, frame| {
            size.checked_add(frame.len())
                .filter(|size| *size <= maximum_bytes)
                .ok_or(TranscriptError::LimitExceeded)
        })?;
        let mut previous = None;
        let mut header = None;
        let mut events = Vec::new();
        let mut closed = None;
        for (ordinal, bytes) in frames.iter().enumerate() {
            let frame: Frame = strict_decode(bytes)?;
            if frame.version != TRANSCRIPT_VERSION {
                return Err(TranscriptError::UnsupportedVersion);
            }
            if frame.ordinal != ordinal as u64 || frame.previous_digest != previous {
                return Err(TranscriptError::BrokenChain { ordinal });
            }
            if closed.is_some() {
                return Err(TranscriptError::BrokenChain { ordinal });
            }
            let record: Record = strict_decode(&frame.payload)?;
            match record {
                Record::Header { header: value } if ordinal == 0 => {
                    check_header_version(&value)?;
                    header = Some(value);
                }
                Record::Event { event } if header.is_some() => events.push(event),
                Record::Closed {
                    event_count,
                    ineligible,
                } if header.is_some() && event_count == events.len() as u64 => {
                    closed = Some(ineligible)
                }
                _ => return Err(TranscriptError::BrokenChain { ordinal }),
            }
            previous = Some(bytes_sha256(bytes));
        }
        if previous.as_deref() != Some(expected_head) {
            return Err(TranscriptError::BrokenChain {
                ordinal: frames.len(),
            });
        }
        let ineligible = closed.ok_or(TranscriptError::Incomplete)?;
        let incomplete_calls = validate_events(&events)?;
        if validate_owner_events(&events)?
            != ineligible.contains(&ReplayIneligibility::MissingOwnerEvidence)
        {
            return Err(TranscriptError::InvalidEvent);
        }
        if incomplete_calls != ineligible.contains(&ReplayIneligibility::IncompleteToolCall) {
            return Err(TranscriptError::InvalidEvent);
        }
        Ok(Self {
            header: header.ok_or(TranscriptError::Incomplete)?,
            events,
            ineligible,
            head: expected_head.to_owned(),
        })
    }

    pub fn require_complete_search(
        &self,
    ) -> Result<&super::ReplayFinalStateProjection, TranscriptError> {
        self.require_replayable()?;
        self.final_state_projection()
            .ok_or(TranscriptError::Incomplete)
    }
    pub fn final_state_projection(&self) -> Option<&super::ReplayFinalStateProjection> {
        self.events.iter().find_map(|event| match event {
            TranscriptEvent::FinalOwnerProjection { projection } => Some(projection.as_ref()),
            _ => None,
        })
    }
    pub fn require_replayable(&self) -> Result<(), TranscriptError> {
        if self.ineligible.is_empty() {
            Ok(())
        } else {
            Err(TranscriptError::NotReplayable(self.ineligible.clone()))
        }
    }
}

fn push_event(pending: &mut Pending, event: TranscriptEvent) {
    if pending.closed {
        pending.error = Some(TranscriptError::Closed);
        return;
    }
    if pending.error.is_some() {
        return;
    }
    let Some(size) = encoded_size(&event, pending.maximum_bytes.saturating_sub(pending.bytes))
        .ok()
        .and_then(|size| pending.bytes.checked_add(size))
    else {
        pending.error = Some(TranscriptError::LimitExceeded);
        return;
    };
    if size > pending.maximum_bytes {
        pending.error = Some(TranscriptError::LimitExceeded);
        return;
    }
    pending.bytes = size;
    pending.events.push(event);
}

fn check_header_version(header: &TranscriptHeader) -> Result<(), TranscriptError> {
    if header.version != TRANSCRIPT_VERSION
        || header.proposal_schema != super::agent::AGENT_HOUDINI_PROTOCOL_VERSION
        || header.feedback_schema != super::feedback::AGENT_FEEDBACK_SCHEMA_VERSION
        || header.presentation_schema != super::feedback::AGENT_PRESENTATION_SCHEMA_VERSION
    {
        return Err(TranscriptError::UnsupportedVersion);
    }
    Ok(())
}

fn required_nullable<'de, D, T>(deserializer: D) -> Result<Option<T>, D::Error>
where
    D: serde::Deserializer<'de>,
    T: Deserialize<'de>,
{
    Option::<T>::deserialize(deserializer)
}

fn validate_events(events: &[TranscriptEvent]) -> Result<bool, TranscriptError> {
    // Observed counts describe original attempted bytes. Redaction is
    // length-preserving and must not alter these ordinary writer decisions.
    let mut responses: BTreeMap<TranscriptCoordinates, (Option<usize>, usize, usize, bool)> =
        BTreeMap::new();
    let mut calls = BTreeMap::new();
    let mut completed = BTreeSet::new();
    let mut next_call = 0;
    for event in events {
        match event {
            TranscriptEvent::Bytes {
                coordinates,
                stream: TranscriptStream::Response,
                bytes,
                accounting,
            } => {
                let count = accounting.as_ref().ok_or(TranscriptError::InvalidEvent)?;
                let state =
                    responses
                        .entry(*coordinates)
                        .or_insert((count.maximum_bytes, 0, 0, false));
                if state.0 != count.maximum_bytes {
                    return Err(TranscriptError::InvalidEvent);
                }
                state.1 = state.1.saturating_add(bytes.len());
                let accepted = match state.0 {
                    None => {
                        state.2 += bytes.len();
                        true
                    }
                    Some(maximum) if !state.3 => {
                        let remaining = maximum.saturating_sub(state.2);
                        state.2 += bytes.len().min(remaining);
                        state.3 = bytes.len() > remaining;
                        !state.3
                    }
                    Some(_) => false,
                };
                if count.accepted != accepted
                    || count.observed_bytes != state.1
                    || count.retained_bytes != state.2
                {
                    return Err(TranscriptError::InvalidEvent);
                }
            }
            TranscriptEvent::Bytes {
                accounting: Some(_),
                ..
            } => return Err(TranscriptError::InvalidEvent),
            TranscriptEvent::ToolCall {
                coordinates,
                call_id,
                ..
            } => {
                if *call_id != next_call {
                    return Err(TranscriptError::InvalidEvent);
                }
                next_call += 1;
                calls.insert(*call_id, *coordinates);
            }
            TranscriptEvent::ToolResponse {
                coordinates,
                call_id,
                ..
            } => {
                if calls.get(call_id) != Some(coordinates) || !completed.insert(*call_id) {
                    return Err(TranscriptError::InvalidEvent);
                }
            }
            _ => {}
        }
    }
    Ok(calls.len() != completed.len())
}

fn strict_decode<T: serde::de::DeserializeOwned>(bytes: &[u8]) -> Result<T, TranscriptError> {
    let value = decode_strict_json(bytes, None).map_err(|_| TranscriptError::Malformed)?;
    serde_json::from_value(value).map_err(|_| TranscriptError::Malformed)
}

/// Delegation preserves the provider's authority and fallible joined cleanup.
pub struct RecordingProvider<S> {
    source: S,
    recorder: Option<TranscriptRecorder>,
}

impl<S: AgentProvider> RecordingProvider<S> {
    pub fn agent(
        source: S,
        policy: AgentConsultationPolicy,
        recorder: TranscriptRecorder,
    ) -> Agent<Self> {
        Self::optional_agent(source, policy, Some(recorder))
    }

    /// The same wrapper with recording made optional, so one run shape covers
    /// both retention policies.
    ///
    /// `None` installs no recorder at either layer: the provider's tools are
    /// passed straight through and the agent holds no recording handle, so a
    /// run that retains nothing neither copies provider bytes nor can fail a
    /// consultation on a recording fault.
    pub fn optional_agent(
        source: S,
        policy: AgentConsultationPolicy,
        recorder: Option<TranscriptRecorder>,
    ) -> Agent<Self> {
        let agent = Agent::new(
            Self {
                source,
                recorder: recorder.clone(),
            },
            policy,
        );
        match recorder {
            Some(recorder) => agent.with_recorder(recorder),
            None => agent,
        }
    }
}

impl<S: AgentProvider> AgentProvider for RecordingProvider<S> {
    fn api_capabilities(&self) -> crate::proposer_api::ApiCapabilities {
        self.source.api_capabilities()
    }

    fn consult<'a>(
        &'a mut self,
        push: &'a AgentPush,
        tools: &'a dyn AgentToolSurface,
        response: &'a mut AgentResponseWriter,
        cancellation: AgentSourceCancellation,
    ) -> AgentSourceFuture<'a> {
        // The handle is a shared owner, so cloning it here keeps the tool
        // surface's borrow disjoint from the delegated mutable source.
        let recorder = self.recorder.clone();
        Box::pin(async move {
            match &recorder {
                Some(recorder) => {
                    let recording_tools = RecordingTools {
                        tools,
                        recorder,
                        coordinates: recorder.current_coordinates(),
                    };
                    self.source
                        .consult(push, &recording_tools, response, cancellation)
                        .await
                }
                None => {
                    self.source
                        .consult(push, tools, response, cancellation)
                        .await
                }
            }
        })
    }

    fn resource_failure(&self) -> Option<String> {
        self.source.resource_failure()
    }
    fn terminal_failure(&self) -> Option<crate::proposer_api::ProposerTerminalFailure> {
        self.source.terminal_failure()
    }
    fn quiesce_request(&mut self) -> AgentSourceCleanupFuture<'_> {
        self.source.quiesce_request()
    }
    fn shutdown(
        &mut self,
        reason: crate::proposer_api::wire::ShutdownReason,
    ) -> AgentSourceCleanupFuture<'_> {
        self.source.shutdown(reason)
    }
}

struct RecordingTools<'a> {
    tools: &'a dyn AgentToolSurface,
    recorder: &'a TranscriptRecorder,
    coordinates: TranscriptCoordinates,
}

impl AgentToolSurface for RecordingTools<'_> {
    fn call<'a>(&'a self, name: &'a str, args: Value) -> AgentToolResponseFuture<'a> {
        // Allocate and record at invocation, before polling or completion.
        let call = self.recorder.tool_call(self.coordinates, name, &args);
        Box::pin(async move {
            let response = self.tools.call(name, args).await;
            if let (Some(call_id), Some(bytes)) = (call, self.recorder.encode(&response)) {
                self.recorder.record(TranscriptEvent::ToolResponse {
                    coordinates: self.coordinates,
                    call_id,
                    response: bytes,
                });
            }
            response
        })
    }
}

// Fixed credential name/pattern deny-list. Length-preserving masks retain
// exact response chunk boundaries and byte-limit accounting. Stream assembly
// is bounded by the recorder's explicit total byte cap, including diagnostics.
//
// Every durable projection in this crate asks the deny-list about its own
// bytes before emitting anything derived from them, so this runs many times
// per check on payload-sized input. It therefore reads the payload without
// copying it, lowering it, or scanning it once per pattern: one pass finds
// the JSON-shaped secrets and one pass finds the loose ones, and a position
// is only matched against the patterns that could begin with its own byte.

/// Names whose value is a credential wherever the name appears.
const DENIED_NAMES: [&[u8]; 9] = [
    b"api_key",
    b"api-key",
    b"apikey",
    b"access_token",
    b"refresh_token",
    b"authorization",
    b"password",
    b"client_secret",
    b"openai_api_key",
];

/// Patterns that are the credential itself rather than its name. `bearer `
/// names what follows it; `sk-` is part of the secret and is masked with it.
const CREDENTIAL_PREFIXES: [&[u8]; 2] = [b"sk-", b"bearer "];

/// The credential prefixes a match could begin with at a byte, case-blind.
fn credential_prefixes_at(byte: u8) -> &'static [&'static [u8]] {
    match byte.to_ascii_lowercase() {
        b's' => &[CREDENTIAL_PREFIXES[0]],
        b'b' => &[CREDENTIAL_PREFIXES[1]],
        _ => &[],
    }
}

/// The denied names a match could begin with at a byte, case-blind. A name
/// nested in another (`api_key` inside `openai_api_key`) is still reached,
/// because its own first byte selects it at its own position.
fn denied_names_at(byte: u8) -> &'static [&'static [u8]] {
    match byte.to_ascii_lowercase() {
        b'a' => &[
            DENIED_NAMES[0],
            DENIED_NAMES[1],
            DENIED_NAMES[2],
            DENIED_NAMES[3],
            DENIED_NAMES[5],
        ],
        b'r' => &[DENIED_NAMES[4]],
        b'p' => &[DENIED_NAMES[6]],
        b'c' => &[DENIED_NAMES[7]],
        b'o' => &[DENIED_NAMES[8]],
        _ => &[],
    }
}

fn starts_with_ignore_ascii_case(haystack: &[u8], needle: &[u8]) -> bool {
    haystack.len() >= needle.len() && haystack[..needle.len()].eq_ignore_ascii_case(needle)
}

/// Case-blind substring search, filtered on the needle's first byte so a
/// payload without one is a single scan. The needles here are ASCII, so this
/// agrees with a search over an ASCII-lowered copy.
fn contains_ignore_ascii_case(haystack: &[u8], needle: &[u8]) -> bool {
    if needle.is_empty() || haystack.len() < needle.len() {
        return needle.is_empty();
    }
    let first = needle[0];
    let upper = first.to_ascii_uppercase();
    let lower = first.to_ascii_lowercase();
    haystack[..=haystack.len() - needle.len()]
        .iter()
        .enumerate()
        .filter(|(_, byte)| **byte == lower || **byte == upper)
        .any(|(index, _)| haystack[index..index + needle.len()].eq_ignore_ascii_case(needle))
}

fn denied_name_bytes(value: &[u8]) -> bool {
    DENIED_NAMES
        .iter()
        .any(|name| name.len() == value.len() && value.eq_ignore_ascii_case(name))
}

/// A JSON string body that already is its own content: no escape, no control
/// byte, valid UTF-8. Decoding such a string would only copy it.
fn plain_json_string(raw: &[u8]) -> Option<&str> {
    if raw.iter().any(|&byte| byte == b'\\' || byte < 0x20) {
        return None;
    }
    std::str::from_utf8(raw).ok()
}

/// Visit every masked span. Order is unspecified; the caller masks each one
/// with the same byte, and a caller that only asks whether anything is masked
/// stops at the first.
fn visit_redaction_spans(
    bytes: &[u8],
    visit: &mut impl FnMut(usize, usize) -> ControlFlow<()>,
) -> ControlFlow<()> {
    visit_json_secret_spans(bytes, visit)?;
    visit_loose_secret_spans(bytes, visit)
}

/// Secrets in the shape of a JSON string: a denied name or argument flag whose
/// value follows, and any string that carries a credential pattern itself.
fn visit_json_secret_spans(
    bytes: &[u8],
    visit: &mut impl FnMut(usize, usize) -> ControlFlow<()>,
) -> ControlFlow<()> {
    let mut pos = 0;
    while pos < bytes.len() {
        if bytes[pos] != b'"' {
            pos += 1;
            continue;
        }
        let start = pos;
        pos += 1;
        while pos < bytes.len() {
            if bytes[pos] == b'\\' && pos + 1 < bytes.len() {
                pos += 2;
                continue;
            }
            if bytes[pos] == b'"' {
                break;
            }
            pos += 1;
        }
        if pos == bytes.len() {
            break;
        }
        let end = pos;
        pos += 1;
        let owned;
        let decoded: &str = match plain_json_string(&bytes[start + 1..end]) {
            Some(plain) => plain,
            None => match serde_json::from_slice::<String>(&bytes[start..=end]) {
                Ok(decoded) => {
                    owned = decoded;
                    owned.as_str()
                }
                Err(_) => continue,
            },
        };
        let decoded = decoded.as_bytes();
        if contains_ignore_ascii_case(decoded, CREDENTIAL_PREFIXES[0])
            || contains_ignore_ascii_case(decoded, CREDENTIAL_PREFIXES[1])
        {
            visit(start + 1, end)?;
        }
        let argument_flag = decoded.starts_with(b"--")
            && denied_name_bytes(&decoded[decoded.iter().take_while(|b| **b == b'-').count()..]);
        if !denied_name_bytes(decoded) && !argument_flag {
            continue;
        }
        let mut value_start = pos;
        while value_start < bytes.len() && bytes[value_start].is_ascii_whitespace() {
            value_start += 1;
        }
        let separator = if argument_flag { b',' } else { b':' };
        if bytes.get(value_start) != Some(&separator) {
            continue;
        }
        value_start += 1;
        while value_start < bytes.len() && bytes[value_start].is_ascii_whitespace() {
            value_start += 1;
        }
        if bytes.get(value_start) == Some(&b'"') {
            value_start += 1;
            let mut value_end = value_start;
            while value_end < bytes.len() {
                if bytes[value_end] == b'\\' && value_end + 1 < bytes.len() {
                    value_end += 2;
                    continue;
                }
                if bytes[value_end] == b'"' {
                    break;
                }
                value_end += 1;
            }
            visit(value_start, value_end)?;
        } else {
            visit(value_start, json_value_end(bytes, value_start))?;
        }
    }
    ControlFlow::Continue(())
}

/// Secrets outside any JSON string: a credential pattern anywhere in the
/// bytes, and a denied name followed by its value as a flag, a JSON member or
/// a `name=value` pair. Every start position is examined, so overlapping
/// occurrences are all found.
fn visit_loose_secret_spans(
    bytes: &[u8],
    visit: &mut impl FnMut(usize, usize) -> ControlFlow<()>,
) -> ControlFlow<()> {
    for start in 0..bytes.len() {
        let tail = &bytes[start..];
        let byte = tail[0];
        for prefix in credential_prefixes_at(byte) {
            if !starts_with_ignore_ascii_case(tail, prefix) {
                continue;
            }
            // `bearer ` names the credential that follows it; `sk-` is the
            // start of the credential, so it is masked along with it.
            let value_start = start
                + if *prefix == CREDENTIAL_PREFIXES[1] {
                    prefix.len()
                } else {
                    0
                };
            let mut end = start + prefix.len();
            while end < bytes.len() && credential_byte(bytes[end]) {
                end += 1;
            }
            if end > value_start {
                visit(value_start, end)?;
            }
        }
        for name in denied_names_at(byte) {
            if !starts_with_ignore_ascii_case(tail, name) {
                continue;
            }
            let mut pos = start + name.len();
            let flag_value = start >= 2
                && &bytes[start - 2..start] == b"--"
                && bytes
                    .get(pos)
                    .is_some_and(|byte| byte.is_ascii_whitespace() || *byte == 0);
            if flag_value {
                while pos < bytes.len() && (bytes[pos].is_ascii_whitespace() || bytes[pos] == 0) {
                    pos += 1;
                }
                let begin = pos;
                while pos < bytes.len() && credential_byte(bytes[pos]) {
                    pos += 1;
                }
                if pos > begin {
                    visit(begin, pos)?;
                }
                continue;
            }
            while pos < bytes.len() && matches!(bytes[pos], b' ' | b'\t' | b'\"' | b'\'') {
                pos += 1;
            }
            if pos == bytes.len() || !matches!(bytes[pos], b':' | b'=') {
                continue;
            }
            pos += 1;
            while pos < bytes.len() && bytes[pos].is_ascii_whitespace() {
                pos += 1;
            }
            let quote = bytes
                .get(pos)
                .copied()
                .filter(|b| matches!(b, b'\"' | b'\''));
            if quote.is_some() {
                pos += 1;
            }
            let begin = pos;
            while pos < bytes.len()
                && match quote {
                    Some(q) => bytes[pos] != q,
                    None => credential_byte(bytes[pos]),
                }
            {
                if quote.is_some() && bytes[pos] == b'\\' && pos + 1 < bytes.len() {
                    pos += 1;
                }
                pos += 1;
            }
            if pos > begin {
                visit(begin, pos)?;
            }
        }
    }
    ControlFlow::Continue(())
}

fn redact(bytes: &mut [u8]) -> bool {
    let mut spans = Vec::new();
    let _ = visit_redaction_spans(bytes, &mut |start, end| {
        spans.push((start, end));
        ControlFlow::Continue(())
    });
    let changed = !spans.is_empty();
    for (start, end) in spans {
        bytes[start..end].fill(b'*');
    }
    changed
}

/// The deny-list as it read before it was made cheap: two payload copies, an
/// ASCII-lowered copy of the input and one naive scan per pattern. Kept as the
/// oracle the differential test compares the single-pass reader against.
#[cfg(test)]
fn redact_reference(bytes: &mut [u8]) -> bool {
    let lower: Vec<u8> = bytes.iter().map(u8::to_ascii_lowercase).collect();
    let mut spans = json_secret_spans_reference(bytes);
    for prefix in [b"sk-".as_slice(), b"bearer "] {
        for start in 0..bytes.len() {
            if lower[start..].starts_with(prefix) {
                let value_start = start
                    + if prefix == b"bearer " {
                        prefix.len()
                    } else {
                        0
                    };
                let mut end = start + prefix.len();
                while end < bytes.len() && credential_byte(bytes[end]) {
                    end += 1;
                }
                if end > value_start {
                    spans.push((value_start, end));
                }
            }
        }
    }
    for name in [
        b"api_key".as_slice(),
        b"api-key",
        b"apikey",
        b"access_token",
        b"refresh_token",
        b"authorization",
        b"password",
        b"client_secret",
        b"openai_api_key",
    ] {
        for start in 0..bytes.len() {
            if !lower[start..].starts_with(name) {
                continue;
            }
            let mut pos = start + name.len();
            let flag_value = start >= 2
                && &bytes[start - 2..start] == b"--"
                && bytes
                    .get(pos)
                    .is_some_and(|byte| byte.is_ascii_whitespace() || *byte == 0);
            if flag_value {
                while pos < bytes.len() && (bytes[pos].is_ascii_whitespace() || bytes[pos] == 0) {
                    pos += 1;
                }
                let begin = pos;
                while pos < bytes.len() && credential_byte(bytes[pos]) {
                    pos += 1;
                }
                if pos > begin {
                    spans.push((begin, pos));
                }
                continue;
            }
            while pos < bytes.len() && matches!(bytes[pos], b' ' | b'\t' | b'\"' | b'\'') {
                pos += 1;
            }
            if pos == bytes.len() || !matches!(bytes[pos], b':' | b'=') {
                continue;
            }
            pos += 1;
            while pos < bytes.len() && bytes[pos].is_ascii_whitespace() {
                pos += 1;
            }
            let quote = bytes
                .get(pos)
                .copied()
                .filter(|b| matches!(b, b'\"' | b'\''));
            if quote.is_some() {
                pos += 1;
            }
            let begin = pos;
            while pos < bytes.len()
                && match quote {
                    Some(q) => bytes[pos] != q,
                    None => credential_byte(bytes[pos]),
                }
            {
                if quote.is_some() && bytes[pos] == b'\\' && pos + 1 < bytes.len() {
                    pos += 1;
                }
                pos += 1;
            }
            if pos > begin {
                spans.push((begin, pos));
            }
        }
    }
    let changed = !spans.is_empty();
    for (start, end) in spans {
        bytes[start..end].fill(b'*');
    }
    changed
}

#[cfg(test)]
fn denied_name(value: &str) -> bool {
    matches!(
        value.to_ascii_lowercase().as_str(),
        "api_key"
            | "api-key"
            | "apikey"
            | "access_token"
            | "refresh_token"
            | "authorization"
            | "password"
            | "client_secret"
            | "openai_api_key"
    )
}

#[cfg(test)]
fn json_secret_spans_reference(bytes: &[u8]) -> Vec<(usize, usize)> {
    let mut spans = Vec::new();
    let mut pos = 0;
    while pos < bytes.len() {
        if bytes[pos] != b'"' {
            pos += 1;
            continue;
        }
        let start = pos;
        pos += 1;
        while pos < bytes.len() {
            if bytes[pos] == b'\\' && pos + 1 < bytes.len() {
                pos += 2;
                continue;
            }
            if bytes[pos] == b'"' {
                break;
            }
            pos += 1;
        }
        if pos == bytes.len() {
            break;
        }
        let end = pos;
        pos += 1;
        let Ok(decoded) = serde_json::from_slice::<String>(&bytes[start..=end]) else {
            continue;
        };
        let lower = decoded.to_ascii_lowercase();
        if lower.contains("sk-") || lower.contains("bearer ") {
            spans.push((start + 1, end));
        }
        let argument_flag =
            decoded.starts_with("--") && denied_name(decoded.trim_start_matches('-'));
        if !denied_name(&decoded) && !argument_flag {
            continue;
        }
        let mut value_start = pos;
        while value_start < bytes.len() && bytes[value_start].is_ascii_whitespace() {
            value_start += 1;
        }
        let separator = if argument_flag { b',' } else { b':' };
        if bytes.get(value_start) != Some(&separator) {
            continue;
        }
        value_start += 1;
        while value_start < bytes.len() && bytes[value_start].is_ascii_whitespace() {
            value_start += 1;
        }
        if bytes.get(value_start) == Some(&b'"') {
            value_start += 1;
            let mut value_end = value_start;
            while value_end < bytes.len() {
                if bytes[value_end] == b'\\' && value_end + 1 < bytes.len() {
                    value_end += 2;
                    continue;
                }
                if bytes[value_end] == b'"' {
                    break;
                }
                value_end += 1;
            }
            spans.push((value_start, value_end));
        } else {
            spans.push((value_start, json_value_end(bytes, value_start)));
        }
    }
    spans
}

fn json_value_end(bytes: &[u8], start: usize) -> usize {
    let mut depth = 0usize;
    let mut quoted = false;
    let mut pos = start;
    while pos < bytes.len() {
        let byte = bytes[pos];
        if quoted {
            if byte == b'\\' && pos + 1 < bytes.len() {
                pos += 2;
                continue;
            }
            if byte == b'"' {
                quoted = false;
            }
        } else {
            match byte {
                b'"' => quoted = true,
                b'{' | b'[' => depth += 1,
                b'}' | b']' if depth == 0 => return pos,
                b'}' | b']' => {
                    depth -= 1;
                    if depth == 0 {
                        return pos + 1;
                    }
                }
                b',' if depth == 0 => return pos,
                byte if depth == 0 && byte.is_ascii_whitespace() => return pos,
                _ => {}
            }
        }
        pos += 1;
    }
    pos
}

fn credential_byte(byte: u8) -> bool {
    !byte.is_ascii_whitespace() && !matches!(byte, b'"' | b'\'' | b',' | b'}' | b']' | b';' | 0)
}

fn sanitize_header(header: &mut TranscriptHeader) -> Result<bool, TranscriptError> {
    let mut value = serde_json::to_value(&*header).map_err(|_| TranscriptError::Malformed)?;
    fn strings(value: &mut Value) -> bool {
        match value {
            Value::String(s) => {
                let mut bytes = s.as_bytes().to_vec();
                let changed = redact(&mut bytes);
                *s = String::from_utf8(bytes).expect("ASCII masking preserves UTF-8");
                changed
            }
            Value::Array(items) => items
                .iter_mut()
                .fold(false, |changed, item| strings(item) | changed),
            Value::Object(items) => items
                .values_mut()
                .fold(false, |changed, item| strings(item) | changed),
            _ => false,
        }
    }
    let changed = strings(&mut value);
    *header = serde_json::from_value(value).map_err(|_| TranscriptError::Malformed)?;
    Ok(changed)
}

fn redact_events(events: &mut [TranscriptEvent]) -> bool {
    let mut streams: BTreeMap<(TranscriptCoordinates, TranscriptStream), Vec<usize>> =
        BTreeMap::new();
    let mut semantic = events.iter().any(|event| {
        matches!(
            event,
            TranscriptEvent::OwnerUnavailable {
                reason: super::replay_correspondence::ReplayCaptureError::SemanticRedaction,
                ..
            } | TranscriptEvent::FinalOwnerUnavailable {
                reason: super::ReplayCaptureError::SemanticRedaction
            }
        )
    });
    for (index, event) in events.iter_mut().enumerate() {
        match event {
            TranscriptEvent::Bytes {
                coordinates,
                stream,
                ..
            } => {
                streams
                    .entry((*coordinates, *stream))
                    .or_default()
                    .push(index);
            }
            TranscriptEvent::ToolCall {
                name, arguments, ..
            } => {
                let mut bytes = name.as_bytes().to_vec();
                semantic |= redact(&mut bytes) | redact(arguments);
                *name = String::from_utf8(bytes).expect("ASCII masking preserves UTF-8");
            }
            TranscriptEvent::ToolResponse { response, .. } => semantic |= redact(response),
            _ => {}
        }
    }
    for ((_, stream), indices) in streams {
        let mut joined = Vec::new();
        for &index in &indices {
            if let TranscriptEvent::Bytes { bytes, .. } = &events[index] {
                joined.extend_from_slice(bytes);
            }
        }
        let changed = redact(&mut joined);
        semantic |= changed && stream.semantic();
        let mut start = 0;
        for index in indices {
            if let TranscriptEvent::Bytes { bytes, .. } = &mut events[index] {
                let end = start + bytes.len();
                bytes.copy_from_slice(&joined[start..end]);
                start = end;
            }
        }
    }
    if semantic {
        for event in events.iter_mut() {
            if matches!(event, TranscriptEvent::FinalOwnerProjection { .. }) {
                *event = TranscriptEvent::FinalOwnerUnavailable {
                    reason: super::ReplayCaptureError::SemanticRedaction,
                };
            }
            if let TranscriptEvent::OwnerProjection { coordinates, .. } = event {
                *event = TranscriptEvent::OwnerUnavailable {
                    coordinates: *coordinates,
                    reason: super::replay_correspondence::ReplayCaptureError::SemanticRedaction,
                };
            }
        }
        // Derived wire digests could include raw secret bytes. Retain no such
        // digest in an ineligible recording; the sanitized chain is fresh.
        // Scan whole streams again so a derived hash split between chunks is
        // masked too. This changes only the non-replayable sanitized copy.
        let mut groups: BTreeMap<(TranscriptCoordinates, TranscriptStream), Vec<usize>> =
            BTreeMap::new();
        for (index, event) in events.iter_mut().enumerate() {
            match event {
                TranscriptEvent::Bytes {
                    coordinates,
                    stream,
                    ..
                } => {
                    groups
                        .entry((*coordinates, *stream))
                        .or_default()
                        .push(index);
                }
                TranscriptEvent::ToolCall { arguments, .. } => mask_derived_digests(arguments),
                TranscriptEvent::ToolResponse { response, .. } => mask_derived_digests(response),
                _ => {}
            }
        }
        for indices in groups.values() {
            let mut joined = Vec::new();
            for &index in indices {
                if let TranscriptEvent::Bytes { bytes, .. } = &events[index] {
                    joined.extend_from_slice(bytes);
                }
            }
            mask_derived_digests(&mut joined);
            let mut start = 0;
            for &index in indices {
                if let TranscriptEvent::Bytes { bytes, .. } = &mut events[index] {
                    let end = start + bytes.len();
                    bytes.copy_from_slice(&joined[start..end]);
                    start = end;
                }
            }
        }
    }
    semantic
}

fn mask_derived_digests(bytes: &mut [u8]) {
    for word in bytes.split_mut(|b| !b.is_ascii_hexdigit()) {
        if word.len() == 64 {
            word.fill(b'*');
        }
    }
}

/// The same fixed deny-list used by the recorder. Owner projections may test
/// private diagnostic bytes before emitting a derived digest; the raw detail
/// itself need never leave its existing owner.
pub struct Redaction;
impl Redaction {
    /// Whether the deny-list would mask anything. The payload is read where
    /// it lies and the answer is settled at the first masked span.
    pub fn changes(bytes: &[u8]) -> bool {
        visit_redaction_spans(bytes, &mut |_, _| ControlFlow::Break(())).is_break()
    }
}

struct SizeCounter {
    size: usize,
    maximum: usize,
}
impl Write for SizeCounter {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        let size = self
            .size
            .checked_add(bytes.len())
            .filter(|&size| size <= self.maximum)
            .ok_or_else(|| io::Error::other("transcript byte limit"))?;
        self.size = size;
        Ok(bytes.len())
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}
pub(super) fn encoded_size<T: Serialize>(
    value: &T,
    maximum: usize,
) -> Result<usize, serde_json::Error> {
    let mut counter = SizeCounter { size: 0, maximum };
    serde_json::to_writer(&mut counter, value)?;
    Ok(counter.size)
}

fn validate_owner_events(events: &[TranscriptEvent]) -> Result<bool, TranscriptError> {
    let mut missing = false;
    let mut pushes = BTreeSet::new();
    let mut final_seen = false;
    for (index, event) in events.iter().enumerate() {
        if final_seen
            && !matches!(
                event,
                TranscriptEvent::Lifecycle {
                    event: TranscriptLifecycle::CleanupJoined,
                    ..
                }
            )
        {
            return Err(TranscriptError::InvalidEvent);
        }
        match event {
            TranscriptEvent::FinalOwnerProjection { .. } => {
                if final_seen {
                    return Err(TranscriptError::InvalidEvent);
                }
                final_seen = true;
            }
            TranscriptEvent::FinalOwnerUnavailable { .. } => {
                if final_seen {
                    return Err(TranscriptError::InvalidEvent);
                }
                final_seen = true;
                missing = true;
            }
            TranscriptEvent::OwnerProjection {
                coordinates,
                projection,
            } => {
                let Some(TranscriptEvent::Bytes {
                    coordinates: next,
                    stream: TranscriptStream::Push,
                    bytes,
                    ..
                }) = events.get(index + 1)
                else {
                    return Err(TranscriptError::InvalidEvent);
                };
                if coordinates != next || projection.verify_push(bytes).is_err() {
                    return Err(TranscriptError::InvalidEvent);
                }
            }
            TranscriptEvent::OwnerUnavailable { coordinates, .. } => {
                let Some(TranscriptEvent::Bytes {
                    coordinates: next,
                    stream: TranscriptStream::Push,
                    ..
                }) = events.get(index + 1)
                else {
                    return Err(TranscriptError::InvalidEvent);
                };
                if coordinates != next {
                    return Err(TranscriptError::InvalidEvent);
                }
                missing = true;
            }
            TranscriptEvent::Bytes {
                coordinates,
                stream: TranscriptStream::Push,
                ..
            } => {
                if !pushes.insert(*coordinates) {
                    return Err(TranscriptError::InvalidEvent);
                }
                if !matches!(index.checked_sub(1).and_then(|i|events.get(i)),Some(TranscriptEvent::OwnerProjection{coordinates:previous,..}|TranscriptEvent::OwnerUnavailable{coordinates:previous,..})if previous==coordinates)
                {
                    missing = true;
                }
            }
            TranscriptEvent::Bytes {
                coordinates,
                stream: TranscriptStream::Response | TranscriptStream::Correction,
                ..
            }
            | TranscriptEvent::ToolCall { coordinates, .. }
            | TranscriptEvent::ToolResponse { coordinates, .. } => {
                if !pushes.contains(coordinates) {
                    missing = true;
                }
            }
            _ => {}
        }
    }
    Ok(missing)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::artifact::{ArtifactStoreConfig, new_artifact_store};
    use crate::task::SynthesisTask;
    use std::sync::atomic::{AtomicU64, Ordering};

    static NEXT: AtomicU64 = AtomicU64::new(0);
    fn header() -> TranscriptHeader {
        TranscriptHeader::new(
            "offline-fixture".into(),
            "run-a".into(),
            TranscriptPins {
                task_digest: "a".repeat(64),
                source_digest: "b".repeat(64),
                scope_digest: "c".repeat(64),
                policy_digest: "d".repeat(64),
                runner_digest: "e".repeat(64),
                worker_digest: "f".repeat(64),
                lean_digest: "1".repeat(64),
                vampire_digest: "2".repeat(64),
                profile_digest: "3".repeat(64),
            },
        )
    }

    fn seal(mut events: Vec<TranscriptEvent>, retention: Retention) -> RecordedTranscript {
        let mut counts = BTreeMap::new();
        for event in &mut events {
            if let TranscriptEvent::Bytes {
                coordinates,
                stream: TranscriptStream::Response,
                bytes,
                accounting,
            } = event
            {
                let count = counts.entry(*coordinates).or_insert(0usize);
                *count += bytes.len();
                if accounting.is_none() {
                    *accounting = Some(ResponseChunkAccounting {
                        accepted: true,
                        maximum_bytes: None,
                        observed_bytes: *count,
                        retained_bytes: *count,
                    });
                }
            }
        }
        let task = artifact_test_task("Transcript");
        let path = std::env::temp_dir().join(format!(
            "whiel-transcript-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        let (owner, store) =
            new_artifact_store(&task, ArtifactStoreConfig::new(&path).retention(retention))
                .unwrap();
        let recorder = TranscriptRecorder::new(header(), 1024 * 1024).unwrap();
        for event in events {
            recorder.record(event);
        }
        let recorded = recorder.finish(&store).unwrap();
        assert!(matches!(
            recorder.finish(&store),
            Err(TranscriptError::Closed)
        ));
        for &artifact in recorded.artifacts() {
            assert_eq!(store.is_retained(artifact), retention == Retention::All);
        }
        drop(store);
        owner.settle().unwrap();
        std::fs::remove_dir_all(path).unwrap();
        recorded
    }

    fn bytes(stream: TranscriptStream, bytes: &[u8]) -> TranscriptEvent {
        TranscriptEvent::Bytes {
            coordinates: TranscriptCoordinates {
                consultation: 2,
                validation: 3,
                transport: 1,
            },
            stream,
            bytes: bytes.to_vec(),
            accounting: None,
        }
    }

    #[test]
    fn exact_chain_roundtrip_and_mutation_refusals() {
        let events = vec![
            bytes(TranscriptStream::Response, b"{bad"),
            bytes(TranscriptStream::Response, &[0xff, b'}']),
        ];
        let recording = seal(events.clone(), Retention::All);
        let decoded = VerifiedTranscript::read(recording.frames(), recording.head()).unwrap();
        let recorded_bytes: Vec<_> = decoded
            .events
            .iter()
            .filter_map(|event| match event {
                TranscriptEvent::Bytes { bytes, .. } => Some(bytes.clone()),
                _ => None,
            })
            .collect();
        let source_bytes: Vec<_> = events
            .iter()
            .filter_map(|event| match event {
                TranscriptEvent::Bytes { bytes, .. } => Some(bytes.clone()),
                _ => None,
            })
            .collect();
        assert_eq!(recorded_bytes, source_bytes);
        assert!(
            decoded
                .ineligibility()
                .contains(&ReplayIneligibility::MissingOwnerEvidence)
        );
        let mut reordered = recording.frames.clone();
        reordered.swap(1, 2);
        assert!(VerifiedTranscript::read(&reordered, recording.head()).is_err());
        let mut duplicated = recording.frames.clone();
        duplicated.insert(1, duplicated[1].clone());
        assert!(VerifiedTranscript::read(&duplicated, recording.head()).is_err());
        let mut omitted = recording.frames.clone();
        omitted.remove(1);
        assert!(VerifiedTranscript::read(&omitted, recording.head()).is_err());
        let mut changed = recording.frames.clone();
        changed[1].push(b' ');
        assert!(VerifiedTranscript::read(&changed, recording.head()).is_err());
        let mut incomplete = recording.frames.clone();
        incomplete.pop();
        let head = bytes_sha256(incomplete.last().unwrap());
        assert!(matches!(
            VerifiedTranscript::read(&incomplete, &head),
            Err(TranscriptError::Incomplete)
        ));
    }

    #[test]
    fn proposer_lifecycle_and_outcomes_have_closed_exact_records() {
        let coordinates = TranscriptCoordinates {
            consultation: 4,
            validation: 2,
            transport: 1,
        };
        let mut events = Vec::new();
        for event in [
            TranscriptLifecycle::RequestStarted,
            TranscriptLifecycle::RequestCancelled,
            TranscriptLifecycle::RequestPanicked,
            TranscriptLifecycle::CleanupJoined,
        ] {
            events.push(TranscriptEvent::Lifecycle { coordinates, event });
        }
        for outcome in [
            TranscriptProviderOutcome::Response,
            TranscriptProviderOutcome::SourceExhausted,
            TranscriptProviderOutcome::NoResponse,
            TranscriptProviderOutcome::TransportFailure,
        ] {
            events.push(TranscriptEvent::ProviderOutcome {
                coordinates,
                outcome,
            });
        }
        let recording = seal(events.clone(), Retention::All);
        let decoded = VerifiedTranscript::read(recording.frames(), recording.head()).unwrap();
        assert_eq!(decoded.events(), events);
        for event in &events {
            let mut wire = serde_json::to_value(event).unwrap();
            wire["unrecognized"] = Value::Bool(true);
            assert!(strict_decode::<TranscriptEvent>(&serde_json::to_vec(&wire).unwrap()).is_err());
        }
        for event in [
            serde_json::json!({"kind":"child_started","coordinates":coordinates,"pid":913}),
            serde_json::json!({"kind":"child_exited","coordinates":coordinates,"code":0,"signal":null}),
            serde_json::json!({"kind":"lifecycle","coordinates":coordinates,"event":"fresh_consultation"}),
        ] {
            assert!(
                strict_decode::<TranscriptEvent>(&serde_json::to_vec(&event).unwrap()).is_err()
            );
        }
        for stream in [
            "child_prompt",
            "child_argv",
            "child_stdout",
            "child_stderr",
            "child_closing_prose",
        ] {
            assert!(serde_json::from_value::<TranscriptStream>(serde_json::json!(stream)).is_err());
        }
    }

    #[test]
    fn unknown_nested_frame_fields_and_duplicates_refused() {
        let recording = seal(Vec::new(), Retention::All);
        let mut frames = recording.frames.clone();
        let mut frame: Value = serde_json::from_slice(&frames[0]).unwrap();
        frame["unknown"] = Value::Bool(true);
        frames[0] = serde_json::to_vec(&frame).unwrap();
        assert!(matches!(
            VerifiedTranscript::read(&frames, recording.head()),
            Err(TranscriptError::Malformed)
        ));
        assert!(strict_decode::<Frame>(br#"{"version":1,"version":1}"#).is_err());
    }

    #[test]
    fn every_stream_redacts_secret_split_at_every_boundary() {
        let secret = b"API_KEY=sk-live-very-private";
        for stream in [
            TranscriptStream::Push,
            TranscriptStream::Response,
            TranscriptStream::Correction,
        ] {
            for split in 0..=secret.len() {
                let mut events = vec![
                    bytes(stream, &secret[..split]),
                    bytes(stream, &secret[split..]),
                ];
                assert_eq!(redact_events(&mut events), stream.semantic());
                let joined: Vec<_> = events
                    .iter()
                    .flat_map(|event| match event {
                        TranscriptEvent::Bytes { bytes, .. } => bytes.clone(),
                        _ => unreachable!(),
                    })
                    .collect();
                assert_eq!(joined.len(), secret.len());
                assert!(!joined.windows(8).any(|w| w == b"sk-live-"));
                assert!(!joined.windows(12).any(|w| w == b"very-private"));
            }
        }
    }

    #[test]
    fn semantic_redaction_removes_dependent_raw_digest_and_blocks_replay() {
        let secret = b"sk-live-very-private";
        let raw_digest = bytes_sha256(secret);
        let correction = format!("{{\"rejected_response_digest\":\"{raw_digest}\"}}");
        let recording = seal(
            vec![
                bytes(TranscriptStream::Response, secret),
                bytes(TranscriptStream::Correction, correction.as_bytes()),
            ],
            Retention::All,
        );
        assert_eq!(
            recording.ineligibility(),
            &[
                ReplayIneligibility::MissingOwnerEvidence,
                ReplayIneligibility::SemanticRedaction
            ]
        );
        let decoded = VerifiedTranscript::read(recording.frames(), recording.head()).unwrap();
        assert!(decoded.require_replayable().is_err());
        let all = serde_json::to_vec(&decoded.events).unwrap();
        // Event byte fields are arrays; inspect decoded stream bytes directly.
        assert!(!all.is_empty());
        for event in decoded.events {
            if let TranscriptEvent::Bytes { bytes, .. } = event {
                assert!(
                    !bytes
                        .windows(raw_digest.len())
                        .any(|w| w == raw_digest.as_bytes())
                );
                assert!(!bytes.windows(secret.len()).any(|w| w == secret));
            }
        }
    }

    #[test]
    fn certificate_only_transcript_does_not_claim_replayable_payload() {
        let no_payload = seal(
            vec![bytes(TranscriptStream::Response, b"{}")],
            Retention::CertificateOnly,
        );
        assert!(no_payload.frames().is_empty());
        assert_eq!(
            no_payload.ineligibility(),
            &[
                ReplayIneligibility::MissingOwnerEvidence,
                ReplayIneligibility::PayloadNotRetained
            ]
        );
        assert!(no_payload.require_replayable().is_err());
    }

    #[test]
    fn recording_limit_is_sticky_and_checked_before_chunk_copy() {
        let recorder = TranscriptRecorder::new(header(), 4096).unwrap();
        recorder.bytes(TranscriptStream::Response, &[0; 8192], None);
        assert_eq!(recorder.status(), Err(TranscriptError::LimitExceeded));
        recorder.bytes(TranscriptStream::Response, b"small", None);
        assert!(recorder.0.lock().unwrap().events.is_empty());
    }

    #[test]
    fn escaped_credential_names_values_and_dependent_chunked_hashes_are_redacted() {
        for raw in [
            br#"{"api\u005fkey":"private\"continued"}"#.as_slice(),
            br#"{"value":"sk\u002dprivate"}"#,
            br#"{"Authorization":"Bearer private\"continued"}"#,
        ] {
            let mut copy = raw.to_vec();
            assert!(redact(&mut copy));
            assert_eq!(copy.len(), raw.len());
            assert!(!copy.windows(7).any(|window| window == b"private"));
            assert!(!copy.windows(9).any(|window| window == b"continued"));
            serde_json::from_slice::<Value>(&copy).unwrap();
        }
        let hash = bytes_sha256(b"sk-private");
        let mut events = vec![
            bytes(TranscriptStream::Push, b"sk-private"),
            bytes(TranscriptStream::Response, &hash.as_bytes()[..20]),
            bytes(TranscriptStream::Response, &hash.as_bytes()[20..]),
        ];
        assert!(redact_events(&mut events));
        for event in events.into_iter().skip(1) {
            let TranscriptEvent::Bytes { bytes, .. } = event else {
                unreachable!()
            };
            assert!(bytes.iter().all(|&byte| byte == b'*'));
        }
    }

    #[test]
    fn header_and_every_tool_field_are_sanitized_before_retention() {
        let mut header = header();
        header.proposer_identity = "API_KEY=private".into();
        assert!(sanitize_header(&mut header).unwrap());
        assert!(!header.proposer_identity.contains("private"));
        let coordinates = TranscriptCoordinates {
            consultation: 0,
            validation: 0,
            transport: 0,
        };
        let recording = seal(
            vec![
                TranscriptEvent::ToolCall {
                    coordinates,
                    call_id: 0,
                    name: "sk-private".into(),
                    arguments: br#"{"password":"private"}"#.to_vec(),
                },
                TranscriptEvent::ToolResponse {
                    coordinates,
                    call_id: 0,
                    response: br#"{"message":"Bearer private"}"#.to_vec(),
                },
            ],
            Retention::All,
        );
        assert!(recording.require_replayable().is_err());
        let verified = VerifiedTranscript::read(recording.frames(), recording.head()).unwrap();
        for event in verified.events {
            match event {
                TranscriptEvent::ToolCall {
                    name, arguments, ..
                } => {
                    assert!(!name.contains("private"));
                    assert!(!String::from_utf8(arguments).unwrap().contains("private"));
                }
                TranscriptEvent::ToolResponse { response, .. } => {
                    assert!(!String::from_utf8(response).unwrap().contains("private"))
                }
                _ => unreachable!(),
            }
        }
    }

    #[test]
    fn argv_credentials_are_redacted_in_separate_arguments() {
        for raw in [
            b"--api-key private --other value".as_slice(),
            b"--api-key\0private\0--other\0value",
            br#"["--api-key","private","--other","value"]"#,
        ] {
            let mut copy = raw.to_vec();
            assert!(redact(&mut copy));
            assert!(!copy.windows(7).any(|window| window == b"private"));
            assert_eq!(copy.len(), raw.len());
        }
        for raw in [
            br#"{"api_key":{"nested":"private"}}"#.as_slice(),
            br#"{"password":["private",{"another":"private"}]}"#,
        ] {
            let mut copy = raw.to_vec();
            assert!(redact(&mut copy));
            assert!(!copy.windows(7).any(|window| window == b"private"));
            assert_eq!(copy.len(), raw.len());
        }
        assert!(Redaction::changes(b"Authorization: Bearer private"));
        assert!(!Redaction::changes(b"ordinary diagnostic"));
    }

    /// Inputs that separate the single-pass reader from a naive one: every
    /// spelling and escape of a denied name, a credential pattern inside a
    /// JSON string, overlapping and adjacent occurrences, digests, empty and
    /// non-UTF-8 bytes, and the boundaries where a match would run off the end.
    fn differential_corpus() -> Vec<Vec<u8>> {
        let mut corpus: Vec<Vec<u8>> = [
            b"".as_slice(),
            b"ordinary diagnostic",
            b"--api_key",
            b"--api_key private",
            b"--api-key\0private\0--other\0value",
            b"--API_KEY  private --other value",
            b"--openai_api_key private",
            b"api_key",
            b"apikey=private",
            b"ApiKey: 'private'",
            b"access_token = private, refresh_token = other",
            b"client_secret:\"pri\\\"vate\" password : private",
            b"Authorization: Bearer private",
            b"authorization:bearer",
            b"bearer ",
            b"sk-",
            b"sk-sk-sk-private",
            b"SK-PRIVATE and Bearer TOKEN",
            b"a sentence about a password, an apikey and authorization in prose",
            br#"{"api_key":"private"}"#,
            br#"{"api_key":{"nested":"private"}}"#,
            br#"{"password":["private",{"another":"private"}]}"#,
            br#"{"api\u005fkey":"private\"continued"}"#,
            br#"{"value":"sk\u002dprivate"}"#,
            br#"{"Authorization":"Bearer private\"continued"}"#,
            br#"{"api_key":""}"#,
            br#"{"api_key":}"#,
            br#"{"api_key" : 12345, "other": true}"#,
            br#"["--api-key","private","--other","value"]"#,
            br#"["--api-key"]"#,
            br#"{"unterminated":"value"#,
            br#""lone string with sk- inside""#,
            br#"{"note":"nothing to see"}"#,
            b"\"\\ud800\"",
            b"e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
            b"digest e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 end",
        ]
        .into_iter()
        .map(<[u8]>::to_vec)
        .collect();
        // Raw bytes a recorder can meet: invalid UTF-8, a control byte inside
        // a JSON string, and a NUL beside a denied name.
        corpus.push(vec![0xff, 0xfe, b'a', b'p', b'i', b'_', b'k', b'e', b'y']);
        corpus.push(b"{\"api_key\":\"pri\x01vate\"}".to_vec());
        corpus.push(br#"{"api_key":"pr"#.iter().copied().chain([0xc3]).collect());
        corpus.push(b"--api_key\0\0private".to_vec());
        // Every prefix of a payload, so a pattern that would run past the end
        // is exercised at each cut.
        let full = br#"{"openai_api_key":"sk-private","Authorization":"Bearer x"}"#;
        for cut in 0..=full.len() {
            corpus.push(full[..cut].to_vec());
        }
        // Fixed-seed strings over the alphabet these rules react to, so the
        // comparison covers shapes nobody thought to write down. The sequence
        // is deterministic, so a disagreement reproduces exactly.
        let alphabet = b"\"\\{}[],:= \t\0'-_akeypsBR1\x01\xff";
        let mut state = 0x2545_f491_4f6c_dd1d_u64;
        for length in 0..600 {
            let mut word = Vec::with_capacity(length % 40);
            for _ in 0..(length % 40) {
                state = state
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                word.push(alphabet[((state >> 33) as usize) % alphabet.len()]);
            }
            corpus.push(word);
        }
        corpus
    }

    #[test]
    fn the_single_pass_deny_list_masks_exactly_what_the_reference_masks() {
        for raw in differential_corpus() {
            let mut fast = raw.clone();
            let mut reference = raw.clone();
            let fast_changed = redact(&mut fast);
            let reference_changed = redact_reference(&mut reference);
            assert_eq!(
                fast_changed,
                reference_changed,
                "changed flag differs on {:?}",
                String::from_utf8_lossy(&raw)
            );
            assert_eq!(
                fast,
                reference,
                "masked bytes differ on {:?}: {:?} against {:?}",
                String::from_utf8_lossy(&raw),
                String::from_utf8_lossy(&fast),
                String::from_utf8_lossy(&reference)
            );
            assert_eq!(fast.len(), raw.len(), "masking preserves length");
            assert_eq!(
                Redaction::changes(&raw),
                reference_changed,
                "the boolean-only reader differs on {:?}",
                String::from_utf8_lossy(&raw)
            );
        }
    }

    #[test]
    fn publication_failure_and_reader_bound_fail_closed() {
        let task = artifact_test_task("TranscriptFailure");
        let path = std::env::temp_dir().join(format!(
            "whiel-transcript-failure-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        let (owner, store) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(&path).payload_budget(Some(1)),
        )
        .unwrap();
        let recorder = TranscriptRecorder::new(header(), 4096).unwrap();
        assert!(matches!(
            recorder.finish(&store),
            Err(TranscriptError::Publication { published: 0 })
        ));
        assert_eq!(
            recorder.status(),
            Err(TranscriptError::Publication { published: 0 })
        );
        drop(store);
        owner.settle().unwrap();
        std::fs::remove_dir_all(path).unwrap();
        let recording = seal(vec![], Retention::All);
        assert!(matches!(
            VerifiedTranscript::read_bounded(recording.frames(), recording.head(), 1),
            Err(TranscriptError::LimitExceeded)
        ));
        let mut wrong = header();
        wrong.presentation_schema += 1;
        assert!(matches!(
            TranscriptRecorder::new(wrong, 4096),
            Err(TranscriptError::UnsupportedVersion)
        ));
    }

    struct OutOfOrderTools;
    impl AgentToolSurface for OutOfOrderTools {
        fn call<'a>(&'a self, name: &'a str, args: Value) -> AgentToolResponseFuture<'a> {
            Box::pin(async move {
                if args["attempt"] == 1 {
                    tokio::task::yield_now().await;
                }
                super::super::tools::AgentToolResponse::err(
                    name,
                    4,
                    "no_refutation",
                    args.to_string(),
                )
            })
        }
    }

    #[tokio::test]
    async fn concurrent_tool_completions_pair_by_invocation_id() {
        let recorder = TranscriptRecorder::new(header(), 65536).unwrap();
        let tools = RecordingTools {
            tools: &OutOfOrderTools,
            recorder: &recorder,
            coordinates: recorder.current_coordinates(),
        };
        let first = tools.call("countermodel", serde_json::json!({"attempt":1}));
        let second = tools.call("countermodel", serde_json::json!({"attempt":2}));
        tokio::join!(first, second);
        let events = recorder.0.lock().unwrap().events.clone();
        let completion_ids: Vec<_> = events
            .iter()
            .filter_map(|event| match event {
                TranscriptEvent::ToolResponse { call_id, .. } => Some(*call_id),
                _ => None,
            })
            .collect();
        assert_eq!(completion_ids, [1, 0]);
        let recording = seal(events, Retention::All);
        assert!(
            recording
                .ineligibility()
                .contains(&ReplayIneligibility::MissingOwnerEvidence)
        );
        let mut broken = recorder.0.lock().unwrap().events.clone();
        broken.push(broken.last().unwrap().clone());
        assert!(matches!(
            validate_events(&broken),
            Err(TranscriptError::InvalidEvent)
        ));
    }

    #[test]
    fn concurrent_invocations_allocate_and_publish_ids_atomically() {
        let recorder = TranscriptRecorder::new(header(), 1024 * 1024).unwrap();
        let tools = RecordingTools {
            tools: &OutOfOrderTools,
            recorder: &recorder,
            coordinates: recorder.current_coordinates(),
        };
        let barrier = std::sync::Barrier::new(16);
        std::thread::scope(|scope| {
            for _ in 0..16 {
                scope.spawn(|| {
                    barrier.wait();
                    for _ in 0..8 {
                        drop(tools.call("countermodel", serde_json::json!({"attempt":1})));
                    }
                });
            }
        });
        let events = recorder.0.lock().unwrap().events.clone();
        let call_ids: Vec<_> = events
            .iter()
            .filter_map(|event| match event {
                TranscriptEvent::ToolCall { call_id, .. } => Some(*call_id),
                _ => None,
            })
            .collect();
        assert_eq!(call_ids, (0..128).collect::<Vec<_>>());
        assert_eq!(validate_events(&events), Ok(true));
    }

    #[test]
    fn uncompleted_tool_call_is_recorded_but_not_replayable() {
        let recorder = TranscriptRecorder::new(header(), 65536).unwrap();
        let tools = RecordingTools {
            tools: &OutOfOrderTools,
            recorder: &recorder,
            coordinates: recorder.current_coordinates(),
        };
        drop(tools.call("countermodel", serde_json::json!({"attempt":1})));
        let recording = seal(recorder.0.lock().unwrap().events.clone(), Retention::All);
        assert_eq!(
            recording.ineligibility(),
            &[
                ReplayIneligibility::MissingOwnerEvidence,
                ReplayIneligibility::IncompleteToolCall
            ]
        );
        VerifiedTranscript::read(recording.frames(), recording.head()).unwrap();
        assert!(recording.require_replayable().is_err());
    }

    #[test]
    fn transcript_v3_rejects_prior_headers_and_requires_owner_evidence_for_traffic() {
        for version in [1, 2] {
            let mut old = header();
            old.version = version;
            assert!(matches!(
                TranscriptRecorder::new(old, 4096),
                Err(TranscriptError::UnsupportedVersion)
            ));
        }
        let mut legacy = serde_json::to_value(header()).unwrap();
        let object = legacy.as_object_mut().unwrap();
        let proposer = object.remove("proposer_identity").unwrap();
        let schema = object.remove("proposal_schema").unwrap();
        object.insert("provider_identity".into(), proposer);
        object.insert("agent_protocol".into(), schema);
        assert!(strict_decode::<TranscriptHeader>(&serde_json::to_vec(&legacy).unwrap()).is_err());
        let recording = seal(vec![bytes(TranscriptStream::Push, b"{}")], Retention::All);
        assert_eq!(
            recording.ineligibility(),
            &[ReplayIneligibility::MissingOwnerEvidence]
        );
        VerifiedTranscript::read(recording.frames(), recording.head())
            .unwrap()
            .require_replayable()
            .unwrap_err();
    }
    #[test]
    fn unavailable_owner_must_be_adjacent_to_exact_coordinate_push() {
        let coordinate = TranscriptCoordinates {
            consultation: 0,
            validation: 0,
            transport: 0,
        };
        let events = vec![TranscriptEvent::OwnerUnavailable {
            coordinates: coordinate,
            reason: super::super::replay_correspondence::ReplayCaptureError::UnsupportedSchema,
        }];
        assert!(validate_owner_events(&events).is_err());
        let mut events = events;
        events.push(TranscriptEvent::Bytes {
            coordinates: coordinate,
            stream: TranscriptStream::Push,
            bytes: b"{}".to_vec(),
            accounting: None,
        });
        assert!(validate_owner_events(&events).unwrap());
        if let TranscriptEvent::Bytes { coordinates, .. } = &mut events[1] {
            coordinates.transport = 1;
        }
        assert!(validate_owner_events(&events).is_err());
    }

    fn artifact_test_task(name: &str) -> SynthesisTask {
        SynthesisTask::from_json(
            &format!(
                r#"{{
                  "format_version":3,"semantic_version":1,"encoding_version":1,
                  "identity":{{"canonical_id":"{name}","module":"Whiel.Test.{name}","namespace":"Whiel.Test.{name}","source_sha256":"0000000000000000000000000000000000000000000000000000000000000000"}},
                  "schema":{{"expression":"Whiel.Test.{name}.programSchema","display":"schema"}},
                  "original":{{"pre":{{"expression":"Whiel.Test.{name}.inputPre","display":"true"}},"command":{{"expression":"Whiel.Test.{name}.inputCmd","display":"SKIP"}},"post":{{"expression":"Whiel.Test.{name}.inputPost","display":"true"}}}},
                  "preprocessed":{{"pre":{{"expression":"Whiel.Test.{name}.inputPreproc.loopPre","display":"true"}},"command":{{"expression":"Whiel.Test.{name}.inputPreproc.loopCmd","display":"SKIP"}},"post":{{"expression":"Whiel.Test.{name}.inputPreproc.loopPost","display":"true"}}}},
                  "preprocessing_evidence":{{"expression":"Whiel.Test.{name}.inputPreproc"}},
                  "solver":{{"schema_relations":[{{"key":"rel:R:0","arity":1}}],"task_constants":[],
                    "preprocessed_pre":{{"source_id":"task.preprocessed_pre","expression":"Whiel.Test.{name}.inputPreproc.loopPre","no_bound_expression":"Whiel.Test.{name}.inputPreproc.loopPre_noBound","constants":[],"relations":["rel:R:0"]}},
                    "preprocessed_post":{{"source_id":"task.preprocessed_post","expression":"Whiel.Test.{name}.inputPreproc.loopPost","no_bound_expression":"Whiel.Test.{name}.inputPreproc.loopPost_noBound","constants":[],"relations":["rel:R:0"]}},
                    "loop_guard":{{"source_id":"task.loop_guard","constants":[],"relations":["rel:R:0"]}},
                    "negated_loop_guard":{{"source_id":"task.negated_loop_guard","constants":[],"relations":["rel:R:0"]}}}}
                }}"#
            ),
        )
        .unwrap()
    }
}
