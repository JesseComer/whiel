//! Bounded, incremental recognition of Vampire's line protocol.

use super::FmbSize;

/*
  This parser recognizes only the small Vampire protocol needed by
  the process boundary. It does not decode proof or model payloads.

  Logical evidence is stdout-authoritative and requires a matching,
  nonempty, complete SZS envelope plus a compatible SZS status.
*/

// ------------------------------------------------------------
// Protocol Vocabulary
// ------------------------------------------------------------

pub(crate) const DEFAULT_MAX_PROTOCOL_LINE_BYTES: usize = 16 * 1024;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SzsStatus {
    Theorem,
    Unsatisfiable,
    ContradictoryAxioms,
    Satisfiable,
    CounterSatisfiable,
    GaveUp,
    Timeout,
    Unknown,
    Other,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum EnvelopeKind {
    Proof,
    FiniteModel,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ProtocolIssue {
    InvalidUtf8,
    OverlongProtocolLine,
    UnterminatedProtocolLine,
    UnknownSzsStatus,
    MalformedSzsLine,
    InvalidFmbFrontier,
    EmptyEnvelope(EnvelopeKind),
    NestedEnvelope {
        open: EnvelopeKind,
        found: EnvelopeKind,
    },
    UnexpectedEnvelopeEnd(EnvelopeKind),
    MismatchedEnvelopeEnd {
        open: EnvelopeKind,
        found: EnvelopeKind,
    },
    UnclosedEnvelope(EnvelopeKind),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ProtocolEvent {
    Status(SzsStatus),
    EnvelopeStarted(EnvelopeKind),
    EnvelopeComplete(EnvelopeKind),
    TimeoutMarker,
    MemoryLimitMarker,
    FmbFrontier(FmbSize),
    Malformed(ProtocolIssue),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct OpenEnvelope {
    kind: EnvelopeKind,
    has_payload_line: bool,
}

// ------------------------------------------------------------
// Incremental Stream Parser
// ------------------------------------------------------------

/*
  One parser belongs to one byte stream. It recognizes only
  newline-terminated lines during `push`. `finish` rejects a
  protocol-looking EOF fragment instead of treating a partial
  marker as evidence.
*/
#[derive(Debug)]
pub(crate) struct ProtocolParser {
    max_line_bytes: usize,
    line: Vec<u8>,
    overlong: bool,
    overlong_protocol_line: bool,
    open_envelope: Option<OpenEnvelope>,
}

impl ProtocolParser {
    pub(crate) fn new(max_line_bytes: usize) -> Self {
        let max_line_bytes = max_line_bytes.max(1);
        Self {
            max_line_bytes,
            line: Vec::with_capacity(max_line_bytes.min(1024)),
            overlong: false,
            overlong_protocol_line: false,
            open_envelope: None,
        }
    }

    pub(crate) fn push(&mut self, mut bytes: &[u8], emit: &mut impl FnMut(ProtocolEvent)) {
        while !bytes.is_empty() {
            let newline = bytes.iter().position(|byte| *byte == b'\n');
            let (fragment, remainder) = match newline {
                Some(index) => (&bytes[..index], &bytes[index + 1..]),
                None => (bytes, &[][..]),
            };

            self.append_fragment(fragment);
            if newline.is_some() {
                self.complete_line(emit);
            }
            bytes = remainder;
        }
    }

    pub(crate) fn finish(&mut self, emit: &mut impl FnMut(ProtocolEvent)) {
        if self.overlong {
            if self.overlong_protocol_line {
                emit(ProtocolEvent::Malformed(
                    ProtocolIssue::OverlongProtocolLine,
                ));
            }
        } else if !self.line.is_empty() {
            if std::str::from_utf8(&self.line).is_err() {
                emit(ProtocolEvent::Malformed(ProtocolIssue::InvalidUtf8));
            } else if looks_like_protocol_prefix(&self.line) {
                emit(ProtocolEvent::Malformed(
                    ProtocolIssue::UnterminatedProtocolLine,
                ));
            }
        }
        self.reset_line();

        if let Some(open) = self.open_envelope.take() {
            emit(ProtocolEvent::Malformed(ProtocolIssue::UnclosedEnvelope(
                open.kind,
            )));
        }
    }

    fn append_fragment(&mut self, fragment: &[u8]) {
        if self.overlong || fragment.is_empty() {
            return;
        }

        let remaining = self.max_line_bytes.saturating_sub(self.line.len());
        if fragment.len() <= remaining {
            self.line.extend_from_slice(fragment);
            return;
        }

        self.line.extend_from_slice(&fragment[..remaining]);
        self.overlong = true;
        self.overlong_protocol_line = looks_like_protocol_prefix(&self.line);
    }

    fn complete_line(&mut self, emit: &mut impl FnMut(ProtocolEvent)) {
        if self.overlong {
            if self.overlong_protocol_line {
                emit(ProtocolEvent::Malformed(
                    ProtocolIssue::OverlongProtocolLine,
                ));
            } else if let Some(open) = self.open_envelope.as_mut() {
                open.has_payload_line = true;
            }
            self.reset_line();
            return;
        }

        let line = self.line.strip_suffix(b"\r").unwrap_or(&self.line);
        let line = match std::str::from_utf8(line) {
            Ok(line) => line,
            Err(_) => {
                emit(ProtocolEvent::Malformed(ProtocolIssue::InvalidUtf8));
                self.reset_line();
                return;
            }
        };
        Self::parse_line(&mut self.open_envelope, line, emit);
        self.reset_line();
    }

    fn parse_line(
        open_envelope: &mut Option<OpenEnvelope>,
        line: &str,
        emit: &mut impl FnMut(ProtocolEvent),
    ) {
        let line = line.trim_start();
        let protocol = line.strip_prefix('%').map(str::trim_start).unwrap_or(line);

        if starts_with_word_ignore_ascii_case(protocol, "SZS") {
            Self::parse_szs_line(open_envelope, protocol, emit);
            return;
        }

        // Evidence payload is opaque here. In particular, a proof or model
        // line that resembles FMB progress must not move the restart frontier.
        if let Some(open) = open_envelope.as_mut() {
            if !line.trim().is_empty() {
                open.has_payload_line = true;
            }
            return;
        }

        if starts_with_word(protocol, "TRYING") {
            match parse_fmb_frontier(protocol) {
                Some(frontier) => emit(ProtocolEvent::FmbFrontier(frontier)),
                None => emit(ProtocolEvent::Malformed(ProtocolIssue::InvalidFmbFrontier)),
            }
            return;
        }

        if is_timeout_diagnostic(protocol) {
            emit(ProtocolEvent::TimeoutMarker);
        }
        if is_memory_limit_diagnostic(protocol) {
            emit(ProtocolEvent::MemoryLimitMarker);
        }
    }

    fn parse_szs_line(
        open_envelope: &mut Option<OpenEnvelope>,
        line: &str,
        emit: &mut impl FnMut(ProtocolEvent),
    ) {
        let mut words = line.split_ascii_whitespace();
        if !words
            .next()
            .is_some_and(|word| word.eq_ignore_ascii_case("SZS"))
        {
            emit(ProtocolEvent::Malformed(ProtocolIssue::MalformedSzsLine));
            return;
        }

        match words.next() {
            Some(word) if word.eq_ignore_ascii_case("status") => {
                let Some(raw_status) = words.next() else {
                    emit(ProtocolEvent::Malformed(ProtocolIssue::MalformedSzsLine));
                    return;
                };
                let Some(status) = parse_szs_status(raw_status) else {
                    emit(ProtocolEvent::Malformed(ProtocolIssue::UnknownSzsStatus));
                    return;
                };
                emit(ProtocolEvent::Status(status));
                if status == SzsStatus::Timeout {
                    emit(ProtocolEvent::TimeoutMarker);
                }
            }
            Some(word) if word.eq_ignore_ascii_case("output") => {
                let Some(action) = words.next() else {
                    emit(ProtocolEvent::Malformed(ProtocolIssue::MalformedSzsLine));
                    return;
                };
                let Some(raw_kind) = words.next() else {
                    emit(ProtocolEvent::Malformed(ProtocolIssue::MalformedSzsLine));
                    return;
                };
                let Some(kind) = parse_envelope_kind(raw_kind) else {
                    // Vampire also frames non-evidence diagnostics such as
                    // Saturation and Definitions. Ignore those sections. A
                    // misspelled target cannot become evidence because the
                    // required Proof/FiniteModel envelope remains absent.
                    return;
                };
                if action.eq_ignore_ascii_case("start") {
                    Self::start_envelope(open_envelope, kind, emit);
                } else if action.eq_ignore_ascii_case("end") {
                    Self::end_envelope(open_envelope, kind, emit);
                } else {
                    emit(ProtocolEvent::Malformed(ProtocolIssue::MalformedSzsLine));
                }
            }
            _ => emit(ProtocolEvent::Malformed(ProtocolIssue::MalformedSzsLine)),
        }
    }

    fn start_envelope(
        open_envelope: &mut Option<OpenEnvelope>,
        kind: EnvelopeKind,
        emit: &mut impl FnMut(ProtocolEvent),
    ) {
        let found = OpenEnvelope {
            kind,
            has_payload_line: false,
        };
        if let Some(open) = open_envelope.replace(found) {
            emit(ProtocolEvent::Malformed(ProtocolIssue::NestedEnvelope {
                open: open.kind,
                found: kind,
            }));
        }
        emit(ProtocolEvent::EnvelopeStarted(kind));
    }

    fn end_envelope(
        open_envelope: &mut Option<OpenEnvelope>,
        kind: EnvelopeKind,
        emit: &mut impl FnMut(ProtocolEvent),
    ) {
        match *open_envelope {
            None => emit(ProtocolEvent::Malformed(
                ProtocolIssue::UnexpectedEnvelopeEnd(kind),
            )),
            Some(open) if open.kind == kind => {
                *open_envelope = None;
                if open.has_payload_line {
                    emit(ProtocolEvent::EnvelopeComplete(kind));
                } else {
                    emit(ProtocolEvent::Malformed(ProtocolIssue::EmptyEnvelope(kind)));
                }
            }
            Some(open) => emit(ProtocolEvent::Malformed(
                ProtocolIssue::MismatchedEnvelopeEnd {
                    open: open.kind,
                    found: kind,
                },
            )),
        }
    }

    fn reset_line(&mut self) {
        self.line.clear();
        self.overlong = false;
        self.overlong_protocol_line = false;
    }
}

// ------------------------------------------------------------
// Stream-Aware Protocol Summary
// ------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ProtocolStream {
    Stdout,
    Stderr,
}

impl ProtocolStream {
    fn index(self) -> usize {
        match self {
            Self::Stdout => 0,
            Self::Stderr => 1,
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct StreamSummary {
    last_status: Option<(u64, SzsStatus)>,
    last_fmb_frontier: Option<(u64, FmbSize)>,
    last_timeout_marker: Option<u64>,
    last_memory_limit_marker: Option<u64>,
    proof_started: Option<u64>,
    proof_complete: Option<u64>,
    model_started: Option<u64>,
    model_complete: Option<u64>,
    invalid_utf8: u64,
    overlong_protocol_lines: u64,
    malformed_protocol_lines: u64,
}

impl StreamSummary {
    /// The sequence of the last protocol event this stream carried, if it
    /// carried any. Malformed lines are deliberately not events here: they
    /// are counted, and a malformed stream is classified as malformed
    /// before any of this is consulted.
    fn last_event(&self) -> Option<u64> {
        self.last_event_before_limit_markers()
            .max(self.last_limit_marker())
    }

    /// The sequence of the last protocol event other than a resource-limit
    /// marker.
    ///
    /// The markers are excluded because an SZS `Timeout` status emits one
    /// of its own, immediately after itself: comparing a status against
    /// the marker it produced would always say the status came first.
    fn last_event_before_limit_markers(&self) -> Option<u64> {
        [
            self.last_status.map(|(sequence, _)| sequence),
            self.last_fmb_frontier.map(|(sequence, _)| sequence),
            self.proof_started,
            self.proof_complete,
            self.model_started,
            self.model_complete,
        ]
        .into_iter()
        .flatten()
        .max()
    }

    fn last_limit_marker(&self) -> Option<u64> {
        self.last_timeout_marker.max(self.last_memory_limit_marker)
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct ProtocolSummary {
    streams: [StreamSummary; 2],
}

impl ProtocolSummary {
    /*
      Sequence numbers are unique across both pumps. They record
      pump-observation order, not unknowable cross-pipe emission
      order. Logical evidence is never stitched across pipes.
    */
    pub(crate) fn observe(&mut self, stream: ProtocolStream, sequence: u64, event: ProtocolEvent) {
        let summary = &mut self.streams[stream.index()];
        match event {
            ProtocolEvent::Status(status) => {
                replace_if_later(&mut summary.last_status, (sequence, status));
                if status == SzsStatus::Timeout {
                    replace_sequence_if_later(&mut summary.last_timeout_marker, sequence);
                }
            }
            ProtocolEvent::EnvelopeStarted(EnvelopeKind::Proof) => {
                replace_sequence_if_later(&mut summary.proof_started, sequence);
            }
            ProtocolEvent::EnvelopeStarted(EnvelopeKind::FiniteModel) => {
                replace_sequence_if_later(&mut summary.model_started, sequence);
            }
            ProtocolEvent::EnvelopeComplete(EnvelopeKind::Proof) => {
                replace_sequence_if_later(&mut summary.proof_complete, sequence);
            }
            ProtocolEvent::EnvelopeComplete(EnvelopeKind::FiniteModel) => {
                replace_sequence_if_later(&mut summary.model_complete, sequence);
            }
            ProtocolEvent::MemoryLimitMarker => {
                replace_sequence_if_later(&mut summary.last_memory_limit_marker, sequence);
            }
            ProtocolEvent::TimeoutMarker => {
                replace_sequence_if_later(&mut summary.last_timeout_marker, sequence);
            }
            ProtocolEvent::FmbFrontier(frontier) => {
                replace_if_later(&mut summary.last_fmb_frontier, (sequence, frontier));
            }
            ProtocolEvent::Malformed(issue) => {
                summary.malformed_protocol_lines =
                    summary.malformed_protocol_lines.saturating_add(1);
                match issue {
                    ProtocolIssue::InvalidUtf8 => {
                        summary.invalid_utf8 = summary.invalid_utf8.saturating_add(1);
                    }
                    ProtocolIssue::OverlongProtocolLine => {
                        summary.overlong_protocol_lines =
                            summary.overlong_protocol_lines.saturating_add(1);
                    }
                    _ => {}
                }
            }
        }
    }

    pub(crate) fn merge(&mut self, other: Self) {
        for (summary, other) in self.streams.iter_mut().zip(other.streams) {
            if let Some(candidate) = other.last_status {
                replace_if_later(&mut summary.last_status, candidate);
            }
            if let Some(candidate) = other.last_fmb_frontier {
                replace_if_later(&mut summary.last_fmb_frontier, candidate);
            }
            if let Some(sequence) = other.last_memory_limit_marker {
                replace_sequence_if_later(&mut summary.last_memory_limit_marker, sequence);
            }
            if let Some(sequence) = other.last_timeout_marker {
                replace_sequence_if_later(&mut summary.last_timeout_marker, sequence);
            }
            if let Some(sequence) = other.proof_started {
                replace_sequence_if_later(&mut summary.proof_started, sequence);
            }
            if let Some(sequence) = other.proof_complete {
                replace_sequence_if_later(&mut summary.proof_complete, sequence);
            }
            if let Some(sequence) = other.model_started {
                replace_sequence_if_later(&mut summary.model_started, sequence);
            }
            if let Some(sequence) = other.model_complete {
                replace_sequence_if_later(&mut summary.model_complete, sequence);
            }
            summary.invalid_utf8 = summary.invalid_utf8.saturating_add(other.invalid_utf8);
            summary.overlong_protocol_lines = summary
                .overlong_protocol_lines
                .saturating_add(other.overlong_protocol_lines);
            summary.malformed_protocol_lines = summary
                .malformed_protocol_lines
                .saturating_add(other.malformed_protocol_lines);
        }
    }

    /* Vampire's evidence protocol and FMB progress are stdout-authoritative. */
    pub(crate) fn last_status(&self) -> Option<SzsStatus> {
        self.stream(ProtocolStream::Stdout)
            .last_status
            .map(|(_, status)| status)
    }

    pub(crate) fn last_fmb_frontier(&self) -> Option<FmbSize> {
        self.stream(ProtocolStream::Stdout)
            .last_fmb_frontier
            .map(|(_, frontier)| frontier)
    }

    pub(crate) fn timeout_observed(&self) -> bool {
        self.streams
            .iter()
            .any(|summary| summary.last_timeout_marker.is_some())
    }

    /// Whether the last thing stdout said was that the solver had stopped
    /// at a resource limit it was given — its wall clock or its memory.
    ///
    /// The *last* thing, not merely something it once said: a portfolio
    /// echoes every child strategy's own limit termination, so a stream
    /// that contains a limit report says nothing on its own about how the
    /// process this runner started ended. What a single-strategy stage
    /// says last is its own termination.
    pub(crate) fn ends_with_resource_limit(&self) -> bool {
        let summary = self.stream(ProtocolStream::Stdout);
        matches!(
            (summary.last_limit_marker(), summary.last_event()),
            (Some(limit), Some(last)) if limit == last
        )
    }

    /// Whether stdout's last word was an SZS status reporting that the
    /// solver had run out of the time it was given.
    ///
    /// This is the portfolio's own final report. Its children print
    /// termination diagnostics but never an SZS status, so a status line
    /// in a portfolio's stream came from the parent; a parent that died
    /// instead of finishing prints none at all.
    pub(crate) fn ends_with_timeout_status(&self) -> bool {
        let summary = self.stream(ProtocolStream::Stdout);
        matches!(
            (summary.last_status, summary.last_event_before_limit_markers()),
            (Some((sequence, SzsStatus::Timeout)), Some(last)) if sequence == last
        )
    }

    pub(crate) fn proof_started(&self) -> bool {
        self.stream(ProtocolStream::Stdout).proof_started.is_some()
    }

    pub(crate) fn proof_complete(&self) -> bool {
        self.stream(ProtocolStream::Stdout).proof_complete.is_some()
    }

    pub(crate) fn model_started(&self) -> bool {
        self.stream(ProtocolStream::Stdout).model_started.is_some()
    }

    pub(crate) fn model_complete(&self) -> bool {
        self.stream(ProtocolStream::Stdout).model_complete.is_some()
    }

    /// Whether stdout carries one complete proof under a status that
    /// establishes the conjecture.
    ///
    /// `ContradictoryAxioms` is one of them: premises that are inconsistent
    /// among themselves entail everything, so the conjecture does follow,
    /// and the solver reports it under that word to say *how*. The word is
    /// a property of the problem's roles, not of its formulas: a check
    /// whose premises are inconsistent reports `ContradictoryAxioms` while
    /// they are written as axioms and plain `Theorem` once a retry writes
    /// the same formulas as goal-derived. Nothing about what is accepted
    /// changes — both have always been proofs — but on a retry the case is
    /// no longer distinguishable from an ordinary proof by the status word
    /// or the recorded conclusion label.
    pub(crate) fn has_complete_proof_output(&self) -> bool {
        let stdout = self.stream(ProtocolStream::Stdout);
        stdout.malformed_protocol_lines == 0
            && stdout.proof_complete.is_some()
            && stdout.last_status.is_some_and(|(_, status)| {
                matches!(
                    status,
                    SzsStatus::Theorem | SzsStatus::Unsatisfiable | SzsStatus::ContradictoryAxioms
                )
            })
    }

    pub(crate) fn has_complete_model_output(&self) -> bool {
        let stdout = self.stream(ProtocolStream::Stdout);
        stdout.malformed_protocol_lines == 0
            && stdout.model_complete.is_some()
            && stdout
                .last_status
                .is_some_and(|(_, status)| status == SzsStatus::CounterSatisfiable)
    }

    pub(crate) fn stdout_is_malformed(&self) -> bool {
        self.stream(ProtocolStream::Stdout).malformed_protocol_lines != 0
    }

    pub(crate) fn invalid_utf8_count(&self) -> u64 {
        self.streams
            .iter()
            .map(|summary| summary.invalid_utf8)
            .fold(0, u64::saturating_add)
    }

    pub(crate) fn overlong_protocol_line_count(&self) -> u64 {
        self.streams
            .iter()
            .map(|summary| summary.overlong_protocol_lines)
            .fold(0, u64::saturating_add)
    }

    pub(crate) fn malformed_protocol_line_count(&self) -> u64 {
        self.streams
            .iter()
            .map(|summary| summary.malformed_protocol_lines)
            .fold(0, u64::saturating_add)
    }

    fn stream(&self, stream: ProtocolStream) -> &StreamSummary {
        &self.streams[stream.index()]
    }
}

// ------------------------------------------------------------
// Protocol Parsing Helpers
// ------------------------------------------------------------

fn replace_if_later<T>(current: &mut Option<(u64, T)>, candidate: (u64, T)) {
    if current
        .as_ref()
        .is_none_or(|(sequence, _)| candidate.0 > *sequence)
    {
        *current = Some(candidate);
    }
}

fn replace_sequence_if_later(current: &mut Option<u64>, candidate: u64) {
    if current.is_none_or(|sequence| candidate > sequence) {
        *current = Some(candidate);
    }
}

fn parse_szs_status(raw: &str) -> Option<SzsStatus> {
    if raw.eq_ignore_ascii_case("Theorem") {
        Some(SzsStatus::Theorem)
    } else if raw.eq_ignore_ascii_case("Unsatisfiable") {
        Some(SzsStatus::Unsatisfiable)
    } else if raw.eq_ignore_ascii_case("ContradictoryAxioms") {
        Some(SzsStatus::ContradictoryAxioms)
    } else if raw.eq_ignore_ascii_case("Satisfiable") {
        Some(SzsStatus::Satisfiable)
    } else if raw.eq_ignore_ascii_case("CounterSatisfiable") {
        Some(SzsStatus::CounterSatisfiable)
    } else if raw.eq_ignore_ascii_case("GaveUp") {
        Some(SzsStatus::GaveUp)
    } else if raw.eq_ignore_ascii_case("Timeout") {
        Some(SzsStatus::Timeout)
    } else if raw.eq_ignore_ascii_case("Unknown") {
        Some(SzsStatus::Unknown)
    } else if raw.bytes().all(|byte| byte.is_ascii_alphabetic()) {
        Some(SzsStatus::Other)
    } else {
        None
    }
}

fn parse_envelope_kind(raw: &str) -> Option<EnvelopeKind> {
    if raw.eq_ignore_ascii_case("Proof") {
        Some(EnvelopeKind::Proof)
    } else if raw.eq_ignore_ascii_case("FiniteModel") {
        Some(EnvelopeKind::FiniteModel)
    } else {
        None
    }
}

fn parse_fmb_frontier(line: &str) -> Option<FmbSize> {
    let rest = line.get("TRYING".len()..)?.trim();
    let digits = rest.strip_prefix('[')?.strip_suffix(']')?;
    if digits.is_empty() || !digits.bytes().all(|byte| byte.is_ascii_digit()) {
        return None;
    }
    FmbSize::new(digits.parse().ok()?)
}

fn starts_with_word(line: &str, word: &str) -> bool {
    line.strip_prefix(word).is_some_and(|rest| {
        rest.is_empty() || rest.starts_with(|character: char| character.is_ascii_whitespace())
    })
}

fn starts_with_word_ignore_ascii_case(line: &str, word: &str) -> bool {
    let Some(prefix) = line.get(..word.len()) else {
        return false;
    };
    prefix.eq_ignore_ascii_case(word)
        && line.get(word.len()..).is_some_and(|rest| {
            rest.is_empty() || rest.starts_with(|character: char| character.is_ascii_whitespace())
        })
}

fn is_timeout_diagnostic(line: &str) -> bool {
    let line = line.trim();
    line.eq_ignore_ascii_case("Time limit reached")
        || line.eq_ignore_ascii_case("Time limit reached!")
        || line.eq_ignore_ascii_case("Termination reason: Time limit")
}

/// The solver stopping itself at the memory it was told it may use. Like a
/// time limit, this is the launch running out of a resource it was given,
/// not a fault: the lane is inconclusive and the key stays on the ladder.
///
/// The two spellings are the pinned solver's own: its termination-reason
/// table prints `Memory limit`, and its result writer prints
/// `Memory limit exceeded!`. Neither can be produced on a host whose
/// memory limit the solver does not enforce — its own option help names
/// macOS — so this arm is exercised only where the limit binds. An
/// out-of-memory kill by the operating system prints nothing at all and is
/// a process failure, which is what it is.
fn is_memory_limit_diagnostic(line: &str) -> bool {
    let line = line.trim();
    line.eq_ignore_ascii_case("Memory limit exceeded")
        || line.eq_ignore_ascii_case("Memory limit exceeded!")
        || line.eq_ignore_ascii_case("Termination reason: Memory limit")
}

fn looks_like_protocol_prefix(line: &[u8]) -> bool {
    let line = trim_ascii_start(line);
    let line = line
        .strip_prefix(b"%")
        .map(trim_ascii_start)
        .unwrap_or(line);
    could_start_ascii_case_insensitive(line, b"SZS")
        || could_start_ascii_case_insensitive(line, b"TRYING")
        || could_start_ascii_case_insensitive(line, b"Time limit reached")
        || could_start_ascii_case_insensitive(line, b"Termination reason: Time limit")
        || could_start_ascii_case_insensitive(line, b"Memory limit exceeded")
        || could_start_ascii_case_insensitive(line, b"Termination reason: Memory limit")
}

fn trim_ascii_start(mut bytes: &[u8]) -> &[u8] {
    while bytes.first().is_some_and(u8::is_ascii_whitespace) {
        bytes = &bytes[1..];
    }
    bytes
}

fn could_start_ascii_case_insensitive(bytes: &[u8], prefix: &[u8]) -> bool {
    let common = bytes.len().min(prefix.len());
    bytes[..common].eq_ignore_ascii_case(&prefix[..common])
}

// ------------------------------------------------------------
// Tests
// ------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_chunks(max_line_bytes: usize, chunks: &[&[u8]]) -> ProtocolSummary {
        let mut parser = ProtocolParser::new(max_line_bytes);
        let mut summary = ProtocolSummary::default();
        let mut sequence = 0_u64;
        let mut observe = |event| {
            summary.observe(ProtocolStream::Stdout, sequence, event);
            sequence += 1;
        };
        for chunk in chunks {
            parser.push(chunk, &mut observe);
        }
        parser.finish(&mut observe);
        summary
    }

    #[test]
    fn recognizes_split_proof_protocol() {
        let summary = parse_chunks(
            256,
            &[
                b"% SZS status Theo",
                b"rem for p\r\n% SZS output start Proof for p\nproof\n",
                b"% SZS output end Proof for p\n",
            ],
        );
        assert_eq!(summary.last_status(), Some(SzsStatus::Theorem));
        assert!(summary.proof_started());
        assert!(summary.proof_complete());
        assert!(summary.has_complete_proof_output());
        assert!(!summary.model_complete());
        assert_eq!(summary.malformed_protocol_line_count(), 0);
    }

    #[test]
    fn requires_a_matching_complete_model_envelope() {
        let summary = parse_chunks(
            256,
            &[
                b"% SZS status CounterSatisfiable for p\n",
                b"% SZS output start FiniteModel for p\nmodel\n",
                b"% SZS output end Proof for p\n",
            ],
        );
        assert_eq!(summary.last_status(), Some(SzsStatus::CounterSatisfiable));
        assert!(summary.model_started());
        assert!(!summary.model_complete());
        assert_eq!(summary.malformed_protocol_line_count(), 2);
    }

    #[test]
    fn recognizes_a_complete_finite_model_envelope() {
        let summary = parse_chunks(
            256,
            &[
                b"% SZS status CounterSatisfiable for p\n",
                b"% SZS output start FiniteModel for p\nmodel\n",
                b"% SZS output end FiniteModel for p\n",
            ],
        );
        assert!(summary.model_started());
        assert!(summary.model_complete());
        assert!(summary.has_complete_model_output());
        assert_eq!(summary.malformed_protocol_line_count(), 0);
    }

    #[test]
    fn contradictory_axioms_is_a_real_proof_status() {
        let summary = parse_chunks(
            256,
            &[
                b"% SZS status ContradictoryAxioms for p\n",
                b"% SZS output start Proof for p\nproof\n",
                b"% SZS output end Proof for p\n",
            ],
        );
        assert_eq!(summary.last_status(), Some(SzsStatus::ContradictoryAxioms));
        assert!(summary.has_complete_proof_output());
    }

    #[test]
    fn satisfiable_does_not_refute_a_conjecture_problem() {
        let summary = parse_chunks(
            256,
            &[
                b"% SZS status Satisfiable for p\n",
                b"% SZS output start FiniteModel for p\nmodel\n",
                b"% SZS output end FiniteModel for p\n",
            ],
        );
        assert!(summary.model_complete());
        assert!(!summary.has_complete_model_output());
    }

    #[test]
    fn retains_only_positive_complete_fmb_frontiers() {
        let summary = parse_chunks(256, &[b"% TRYING [2]\n% TRY", b"ING [0]\n% TRYING [19]\n"]);
        assert_eq!(summary.last_fmb_frontier().unwrap().get(), 19);
        assert_eq!(summary.malformed_protocol_line_count(), 1);
    }

    #[test]
    fn recognizes_status_and_text_timeout_markers() {
        let summary = parse_chunks(
            256,
            &[b"% SZS status Timeout for p\n% Termination reason: Time limit\n"],
        );
        assert_eq!(summary.last_status(), Some(SzsStatus::Timeout));
        assert!(summary.timeout_observed());
    }

    #[test]
    fn timeout_words_inside_proof_payload_are_not_protocol() {
        let summary = parse_chunks(
            256,
            &[
                b"% SZS status Theorem for p\n",
                b"% SZS output start Proof for p\nTime limit reached\n",
                b"% SZS output end Proof for p\n",
            ],
        );
        assert!(!summary.timeout_observed());
        assert!(summary.has_complete_proof_output());
    }

    #[test]
    fn fmb_frontier_words_inside_evidence_payload_are_not_progress() {
        let summary = parse_chunks(
            256,
            &[
                b"% TRYING [3]\n",
                b"% SZS status Theorem for p\n",
                b"% SZS output start Proof for p\nTRYING [999]\n",
                b"% SZS output end Proof for p\n",
            ],
        );
        assert_eq!(summary.last_fmb_frontier(), FmbSize::new(3));
        assert!(summary.has_complete_proof_output());
    }

    #[test]
    fn unrelated_szs_output_sections_do_not_invalidate_evidence_protocol() {
        let summary = parse_chunks(
            256,
            &[
                b"% SZS output start Saturation.\n",
                b"% SZS output end Saturation.\n",
                b"% SZS status GaveUp for p\n",
            ],
        );
        assert_eq!(summary.last_status(), Some(SzsStatus::GaveUp));
        assert!(!summary.stdout_is_malformed());
    }

    #[test]
    fn invalid_utf8_is_flagged_without_panicking() {
        let summary = parse_chunks(32, &[b"% SZS status \xff\n"]);
        assert_eq!(summary.invalid_utf8_count(), 1);
        assert_eq!(summary.malformed_protocol_line_count(), 1);
        assert_eq!(summary.last_status(), None);
    }

    #[test]
    fn overlong_protocol_line_is_discarded_with_bounded_storage() {
        let summary = parse_chunks(
            12,
            &[b"% SZS status Theorem with arbitrarily long suffix\n"],
        );
        assert_eq!(summary.overlong_protocol_line_count(), 1);
        assert_eq!(summary.last_status(), None);
    }

    #[test]
    fn overlong_ordinary_evidence_line_is_not_a_protocol_error() {
        let mut parser = ProtocolParser::new(8);
        let mut events = Vec::new();
        parser.push(b"12345678901234567890 proof payload", &mut |event| {
            events.push(event)
        });
        assert!(parser.line.len() <= 8);
        parser.push(b"\n", &mut |event| events.push(event));
        parser.finish(&mut |event| events.push(event));

        let mut summary = ProtocolSummary::default();
        for (sequence, event) in events.into_iter().enumerate() {
            summary.observe(ProtocolStream::Stdout, sequence as u64, event);
        }
        assert_eq!(summary.overlong_protocol_line_count(), 0);
        assert_eq!(summary.malformed_protocol_line_count(), 0);
    }

    #[test]
    fn overlong_payload_line_still_makes_the_envelope_nonempty() {
        let summary = parse_chunks(
            64,
            &[
                b"% SZS status Theorem for p\n",
                b"% SZS output start Proof for p\n",
                &[b'x'; 128],
                b"\n% SZS output end Proof for p\n",
            ],
        );
        assert!(summary.proof_complete());
        assert!(summary.has_complete_proof_output());
    }

    #[test]
    fn empty_envelope_is_not_complete_evidence() {
        let summary = parse_chunks(
            256,
            &[
                b"% SZS status Theorem for p\n",
                b"% SZS output start Proof for p\n",
                b"% SZS output end Proof for p\n",
            ],
        );
        assert!(summary.proof_started());
        assert!(!summary.proof_complete());
        assert!(!summary.has_complete_proof_output());
        assert_eq!(summary.malformed_protocol_line_count(), 1);
    }

    #[test]
    fn later_malformed_output_invalidates_same_stream_evidence() {
        let summary = parse_chunks(
            256,
            &[
                b"% SZS status Theorem for p\n",
                b"% SZS output start Proof for p\nproof\n",
                b"% SZS output end Proof for p\n",
                b"% SZS status Not-A-Status for p\n",
            ],
        );
        assert!(summary.proof_complete());
        assert!(summary.stdout_is_malformed());
        assert!(!summary.has_complete_proof_output());
    }

    #[test]
    fn unterminated_protocol_fragment_is_never_evidence() {
        let summary = parse_chunks(256, &[b"% SZS status Theorem"]);
        assert_eq!(summary.last_status(), None);
        assert_eq!(summary.malformed_protocol_line_count(), 1);
    }

    #[test]
    fn every_byte_split_preserves_protocol_recognition() {
        let output = b"% SZS status Theorem for p\n% SZS output start Proof for p\nproof\n% SZS output end Proof for p\n% TRYING [23]\n";
        for split in 0..=output.len() {
            let summary = parse_chunks(256, &[&output[..split], &output[split..]]);
            assert!(summary.has_complete_proof_output(), "split {split}");
            assert_eq!(summary.last_fmb_frontier().unwrap().get(), 23);
        }
    }

    #[test]
    fn merged_streams_do_not_stitch_logical_evidence() {
        let mut stdout = ProtocolSummary::default();
        stdout.observe(
            ProtocolStream::Stdout,
            1,
            ProtocolEvent::EnvelopeStarted(EnvelopeKind::Proof),
        );
        stdout.observe(
            ProtocolStream::Stdout,
            2,
            ProtocolEvent::EnvelopeComplete(EnvelopeKind::Proof),
        );
        stdout.observe(
            ProtocolStream::Stdout,
            5,
            ProtocolEvent::FmbFrontier(FmbSize::new(11).unwrap()),
        );

        let mut stderr = ProtocolSummary::default();
        stderr.observe(
            ProtocolStream::Stderr,
            4,
            ProtocolEvent::Status(SzsStatus::Theorem),
        );
        stderr.observe(
            ProtocolStream::Stderr,
            6,
            ProtocolEvent::FmbFrontier(FmbSize::new(17).unwrap()),
        );

        stdout.merge(stderr);
        assert_eq!(stdout.last_status(), None);
        assert_eq!(stdout.last_fmb_frontier().unwrap().get(), 11);
        assert!(!stdout.has_complete_proof_output());
    }
}
