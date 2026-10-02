//! Lean-owned validation of one agent-proposed counterexample instance.
//!
//! The instance is opaque to Rust. This module passes the agent's own JSON
//! through to the `validate_counterexample` fixed-ambient worker operation
//! unmodified as a JSON value and decodes only the typed verdict Lean answers
//! with: either a canonical validated instance with the fuel it actually
//! consumed, or a typed rejection code and reason. Rust never parses,
//! canonicalizes, rewrites, or otherwise interprets the instance itself — not
//! on the way in, not on the way out, and not when the frozen record is later
//! handed back to `emit_invalid_certificate`. Pass-through is at the value
//! level, not the byte level: `serde_json` is built without `preserve_order`,
//! so object members are re-serialized in key order. Nothing on this path
//! depends on member order, and the instance identity Lean issues is the
//! digest of Lean's own canonical re-emission rather than of the submitted
//! text.

use std::fmt;
use std::sync::Arc;

use serde::Deserialize;
use serde_json::{Value, json};

use crate::encoding::{EncodingError, FixedAmbientWorkerOperation};
use crate::failure::{FailureKind, FailureReport, FailureScope};
use crate::runtime::{CancellationToken, SolverAdmission};
use crate::task::TaskIdentity;

use super::agent::AgentConsultationBinding;
use super::solver::FrameworkIISolverContext;

/// Rejection code Rust itself raises when a `validate_counterexample` call
/// exceeds the host's call-local timeout. It is deliberately outside the
/// vocabulary Lean answers with (see [`LEAN_COUNTEREXAMPLE_REJECTION_CODES`]):
/// the worker never decided anything, its process was terminated, and the
/// pool replaced it.
pub const COUNTEREXAMPLE_TIMEOUT_CODE: &str = "timeout";

/// The rejection vocabulary the Lean codec/evaluator answers with, recorded
/// here for documentation and for the pinning tests. Rust does not enforce
/// membership: a rejection can only ever end a counterexample submission,
/// never accept one, so an unrecognized code is carried through to the agent
/// verbatim rather than escalated into a run-global failure.
///
/// Every code but the last is a verdict on the submission itself.
/// `internal_error` is Lean's own defensive assertion failing closed: it says
/// the validation path could not stand behind its result, not that the agent
/// proposed anything wrong. It is reported to the agent like any other
/// rejection rather than accepted, and it is not expected to occur.
/// There is no size code: an instance is never refused for being large
/// (Pass 7.7b). There is no fuel code either: Lean's replay runs under an
/// unreachable structural fuel, so exhausting it is a fault of the
/// validation path and Lean reports it as `internal_error`.
pub const LEAN_COUNTEREXAMPLE_REJECTION_CODES: [&str; 6] = [
    "malformed",
    "unknown_relation",
    "precondition_fails",
    "postcondition_holds",
    "not_quantifier_free",
    "internal_error",
];

/// Longest rejection reason carried into the next push. A longer reason is
/// truncated on a character boundary rather than failing the run.
const MAX_REJECTION_REASON_BYTES: usize = 1024;

/// Longest rejection code accepted from the worker.
const MAX_REJECTION_CODE_BYTES: usize = 64;

// ------------------------------------------------------------
// Validation Verdict
// ------------------------------------------------------------

/// One counterexample instance Lean decoded, precondition-checked, and ran to
/// a postcondition-violating halt, with the fuel that halt consumed.
///
/// `instance` is Lean's own canonical rendering of the agent's submission and
/// stays opaque to Rust: it is stored, frozen, and handed back to
/// `emit_invalid_certificate` unread.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValidatedCounterexample {
    instance: Value,
    instance_identity: Arc<str>,
    fuel_consumed: u64,
}

impl ValidatedCounterexample {
    pub fn instance(&self) -> &Value {
        &self.instance
    }

    pub fn instance_identity(&self) -> &str {
        &self.instance_identity
    }

    /// The fuel the native evaluator actually consumed reaching the halting
    /// state, which is frozen with the record and re-used verbatim by the
    /// `Invalid.lean` kernel check.
    pub fn fuel_consumed(&self) -> u64 {
        self.fuel_consumed
    }

    /// Build a validated counterexample directly. Test-only: every
    /// production value comes from [`decode_counterexample_validation`],
    /// which is the one place a worker verdict is admitted.
    #[cfg(test)]
    pub(crate) fn for_test(instance: Value, instance_identity: &str, fuel_consumed: u64) -> Self {
        Self {
            instance,
            instance_identity: Arc::from(instance_identity),
            fuel_consumed,
        }
    }
}

/// Why a submitted counterexample was not accepted.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CounterexampleRejection {
    code: Arc<str>,
    reason: Arc<str>,
}

impl CounterexampleRejection {
    /// The host's own rejection for a call that exceeded its call-local
    /// timeout, after the worker process was terminated.
    pub fn timeout(detail: impl AsRef<str>) -> Self {
        Self {
            code: Arc::from(COUNTEREXAMPLE_TIMEOUT_CODE),
            reason: Arc::from(sanitize_reason(
                detail.as_ref(),
                COUNTEREXAMPLE_TIMEOUT_CODE,
            )),
        }
    }

    pub fn code(&self) -> &str {
        &self.code
    }

    pub fn reason(&self) -> &str {
        &self.reason
    }
}

/// Lean's verdict on one submitted counterexample instance.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CounterexampleValidation {
    Validated(ValidatedCounterexample),
    Rejected(CounterexampleRejection),
}

// ------------------------------------------------------------
// Frozen Record
// ------------------------------------------------------------

/// The immutable evidence one validated counterexample ends a run with.
///
/// Everything the `Invalid` certificate is later built from lives here: the
/// canonical instance, its Lean-issued identity, the fuel actually consumed,
/// the task and scope identities it was validated against, and the exact
/// consultation that submitted it.
///
/// There is no fuel bound to record: the replay runs under Lean's own
/// unreachable structural fuel and is guarded only by the call-local
/// wall-clock timeout, so the fuel consumed is the whole of what the record
/// freezes (`agent_houdini.tex`, "Counterexample proposals").
#[derive(Clone, Debug)]
pub struct FrozenCounterexampleRecord {
    instance: Value,
    instance_identity: Arc<str>,
    fuel_consumed: u64,
    task_identity: TaskIdentity,
    scope_identity_sha256: Arc<str>,
    provenance: CounterexampleProvenance,
}

/// Where one frozen counterexample came from.
///
/// Provenance is not authority: an instance is a counterexample because
/// Lean validated it against the immutable input triple, never because of
/// how it reached Lean. It is recorded so a durable record says honestly
/// which route produced it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CounterexampleProvenance {
    /// The agent consultation whose response submitted the instance.
    Consultation(Box<AgentConsultationBinding>),
    /// A witness the corpus already recorded, replayed through the same
    /// Lean validation with no consultation behind it. `source` names where
    /// the witness was read from, for the record alone.
    RecordedWitness { source: Arc<str> },
}

impl CounterexampleProvenance {
    /// The stable wire label of this provenance.
    pub fn kind(&self) -> &'static str {
        match self {
            Self::Consultation(_) => "consultation",
            Self::RecordedWitness { .. } => "recorded_witness",
        }
    }
}

impl FrozenCounterexampleRecord {
    pub(crate) fn freeze(
        validated: ValidatedCounterexample,
        task_identity: TaskIdentity,
        scope_identity_sha256: impl Into<Arc<str>>,
        provenance: CounterexampleProvenance,
    ) -> Self {
        Self {
            instance: validated.instance,
            instance_identity: validated.instance_identity,
            fuel_consumed: validated.fuel_consumed,
            task_identity,
            scope_identity_sha256: scope_identity_sha256.into(),
            provenance,
        }
    }

    /// Rebuild one frozen record from a durable `Counterexample.json`.
    ///
    /// This constructor grants nothing: the rebuilt record still has to go
    /// back through Lean's own `admitFrozen` re-decode and re-check before
    /// any certificate is emitted from it, exactly as the search's own
    /// record does.
    pub(crate) fn rehydrate(
        instance: Value,
        instance_identity: impl Into<Arc<str>>,
        fuel_consumed: u64,
        task_identity: TaskIdentity,
        scope_identity_sha256: impl Into<Arc<str>>,
        provenance: CounterexampleProvenance,
    ) -> Self {
        Self {
            instance,
            instance_identity: instance_identity.into(),
            fuel_consumed,
            task_identity,
            scope_identity_sha256: scope_identity_sha256.into(),
            provenance,
        }
    }

    /// Lean's canonical instance, opaque to Rust.
    pub fn instance(&self) -> &Value {
        &self.instance
    }

    pub fn instance_identity(&self) -> &str {
        &self.instance_identity
    }

    pub fn fuel_consumed(&self) -> u64 {
        self.fuel_consumed
    }

    pub fn task_identity(&self) -> &TaskIdentity {
        &self.task_identity
    }

    pub fn scope_identity_sha256(&self) -> &str {
        &self.scope_identity_sha256
    }

    /// The consultation that submitted this instance, when one did.
    pub fn consultation(&self) -> Option<&AgentConsultationBinding> {
        match &self.provenance {
            CounterexampleProvenance::Consultation(binding) => Some(binding),
            CounterexampleProvenance::RecordedWitness { .. } => None,
        }
    }

    pub fn provenance(&self) -> &CounterexampleProvenance {
        &self.provenance
    }
}

// ------------------------------------------------------------
// Worker Operation
// ------------------------------------------------------------

impl FrameworkIISolverContext {
    /// Ask Lean to decode and check one opaque counterexample instance.
    ///
    /// `input` is the agent's own JSON value; it is embedded in the request
    /// payload unchanged and never inspected here. The request carries no
    /// fuel bound and the instance no size bound: Lean replays under its own
    /// unreachable structural fuel, and the caller's call-local timeout is
    /// the only guard — cancelling `cancellation` terminates the worker
    /// process serving this call, and its expiry is a `timeout` rejection of
    /// the call, never a verdict on the instance.
    pub async fn validate_counterexample(
        &self,
        input: &Value,
        admission: &SolverAdmission,
        cancellation: &CancellationToken,
    ) -> Result<CounterexampleValidation, FrameworkIICounterexampleError> {
        let response = self
            .encoding()
            .execute(
                admission,
                cancellation,
                FixedAmbientWorkerOperation::ValidateCounterexample,
                json!({"input": input}),
            )
            .await
            .map_err(FrameworkIICounterexampleError::from)?;
        decode_counterexample_validation(response.payload)
    }
}

#[derive(Deserialize)]
#[serde(tag = "status", rename_all = "snake_case", deny_unknown_fields)]
enum WireCounterexampleValidation {
    Counterexample {
        fuel_consumed: u64,
        instance_identity: String,
        instance: Value,
    },
    Rejected {
        code: String,
        reason: String,
    },
}

fn decode_counterexample_validation(
    payload: Value,
) -> Result<CounterexampleValidation, FrameworkIICounterexampleError> {
    let wire: WireCounterexampleValidation = serde_json::from_value(payload).map_err(|error| {
        validation_failure(format!(
            "decode fixed-ambient counterexample validation: {error}"
        ))
    })?;
    match wire {
        WireCounterexampleValidation::Counterexample {
            fuel_consumed,
            instance_identity,
            instance,
        } => {
            if !is_sha256_hex(&instance_identity) {
                return Err(validation_failure(
                    "validated counterexample carries no sha256 instance identity",
                ));
            }
            if instance.is_null() {
                return Err(validation_failure(
                    "validated counterexample carries no canonical instance",
                ));
            }
            Ok(CounterexampleValidation::Validated(
                ValidatedCounterexample {
                    instance,
                    instance_identity: Arc::from(instance_identity),
                    fuel_consumed,
                },
            ))
        }
        WireCounterexampleValidation::Rejected { code, reason } => {
            let code = code.trim();
            if code.is_empty()
                || code.len() > MAX_REJECTION_CODE_BYTES
                || !code
                    .bytes()
                    .all(|byte| byte.is_ascii_lowercase() || byte == b'_' || byte.is_ascii_digit())
            {
                return Err(validation_failure(
                    "rejected counterexample carries no well-formed rejection code",
                ));
            }
            Ok(CounterexampleValidation::Rejected(
                CounterexampleRejection {
                    code: Arc::from(code),
                    reason: Arc::from(sanitize_reason(&reason, code)),
                },
            ))
        }
    }
}

fn is_sha256_hex(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

/// Make one worker-authored reason safe to place in the next push: control
/// characters become spaces and the text is truncated on a character
/// boundary. A reason that says nothing falls back to the code, so the agent
/// always sees something addressable.
fn sanitize_reason(reason: &str, code: &str) -> String {
    let mut sanitized = String::with_capacity(reason.len().min(MAX_REJECTION_REASON_BYTES));
    for character in reason.chars() {
        let character = if character.is_control() {
            ' '
        } else {
            character
        };
        if sanitized.len() + character.len_utf8() > MAX_REJECTION_REASON_BYTES {
            break;
        }
        sanitized.push(character);
    }
    let trimmed = sanitized.trim();
    if trimmed.is_empty() {
        code.to_string()
    } else {
        trimmed.to_string()
    }
}

// ------------------------------------------------------------
// Errors
// ------------------------------------------------------------

fn validation_failure(detail: impl Into<String>) -> FrameworkIICounterexampleError {
    FrameworkIICounterexampleError::Failure(FailureReport::encoding_preparation(
        FailureKind::MalformedResult,
        FailureScope::RunGlobal,
        detail,
    ))
}

#[derive(Clone, Debug)]
pub enum FrameworkIICounterexampleError {
    Cancelled,
    Failure(FailureReport),
}

impl FrameworkIICounterexampleError {
    pub fn failure(&self) -> Option<&FailureReport> {
        match self {
            Self::Cancelled => None,
            Self::Failure(report) => Some(report),
        }
    }
}

impl From<EncodingError> for FrameworkIICounterexampleError {
    fn from(error: EncodingError) -> Self {
        match error {
            EncodingError::Cancelled => Self::Cancelled,
            EncodingError::Failure(report) => Self::Failure(report),
        }
    }
}

impl fmt::Display for FrameworkIICounterexampleError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Cancelled => {
                formatter.write_str("fixed-ambient counterexample validation was cancelled")
            }
            Self::Failure(report) => write!(
                formatter,
                "fixed-ambient counterexample validation failed: origin={:?} kind={:?} detail={}",
                report.origin(),
                report.kind(),
                report.detail().unwrap_or("none")
            ),
        }
    }
}

impl std::error::Error for FrameworkIICounterexampleError {}

// ------------------------------------------------------------
// Tests
// ------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn validated_payload(fuel_consumed: u64) -> Value {
        json!({
            "status": "counterexample",
            "fuel_consumed": fuel_consumed,
            "instance_identity": "c".repeat(64),
            "instance": {"relations": [{"name": "o:p::E", "rows": [["num:1", "num:2"]]}]},
        })
    }

    #[test]
    fn decodes_a_validated_counterexample_without_touching_its_instance() {
        let instance = json!({
            "relations": [{"name": "o:p::E", "rows": [["num:1", "num:2"]]}],
            "nested": {"deep": [1, {"deeper": null}]},
        });
        let payload = json!({
            "status": "counterexample",
            "fuel_consumed": 12,
            "instance_identity": "a".repeat(64),
            "instance": instance.clone(),
        });
        let decoded = decode_counterexample_validation(payload).unwrap();
        let CounterexampleValidation::Validated(validated) = decoded else {
            panic!("a well-formed counterexample payload must validate");
        };
        assert_eq!(validated.instance(), &instance);
        assert_eq!(validated.fuel_consumed(), 12);
        assert_eq!(validated.instance_identity(), "a".repeat(64));
    }

    /// No fuel figure is ever too large: there is no host bound to compare
    /// it against. A nonhex identity is still refused.
    #[test]
    fn any_fuel_figure_decodes_but_a_nonhex_identity_does_not() {
        assert!(decode_counterexample_validation(validated_payload(u64::MAX)).is_ok());
        let mut payload = validated_payload(1);
        payload["instance_identity"] = json!("not-a-digest");
        assert!(decode_counterexample_validation(payload).is_err());
    }

    #[test]
    fn rejects_an_unknown_field_or_status() {
        let mut payload = validated_payload(1);
        payload["unexpected"] = json!(true);
        assert!(decode_counterexample_validation(payload).is_err());
        assert!(
            decode_counterexample_validation(json!({"status": "maybe"})).is_err(),
            "an unsupported status must not decode"
        );
    }

    #[test]
    fn decodes_every_lean_rejection_code_and_sanitizes_its_reason() {
        for code in LEAN_COUNTEREXAMPLE_REJECTION_CODES {
            let payload = json!({
                "status": "rejected",
                "code": code,
                "reason": format!("the instance\u{0007} was rejected: {code}"),
            });
            let decoded = decode_counterexample_validation(payload).unwrap();
            let CounterexampleValidation::Rejected(rejection) = decoded else {
                panic!("a rejected payload must not validate");
            };
            assert_eq!(rejection.code(), code);
            assert!(!rejection.reason().contains('\u{0007}'));
            assert!(rejection.reason().ends_with(code));
        }
    }

    #[test]
    fn an_empty_reason_falls_back_to_the_code_and_a_long_one_is_truncated() {
        let payload = json!({"status": "rejected", "code": "malformed", "reason": "   "});
        let decoded = decode_counterexample_validation(payload).unwrap();
        let CounterexampleValidation::Rejected(rejection) = decoded else {
            panic!("a rejected payload must not validate");
        };
        assert_eq!(rejection.reason(), "malformed");

        let payload = json!({
            "status": "rejected",
            "code": "internal_error",
            "reason": "x".repeat(MAX_REJECTION_REASON_BYTES * 2),
        });
        let decoded = decode_counterexample_validation(payload).unwrap();
        let CounterexampleValidation::Rejected(rejection) = decoded else {
            panic!("a rejected payload must not validate");
        };
        assert!(rejection.reason().len() <= MAX_REJECTION_REASON_BYTES);
    }

    #[test]
    fn rejects_a_malformed_rejection_code() {
        for code in ["", "  ", "Malformed", "has space", &"c".repeat(65)] {
            let payload = json!({"status": "rejected", "code": code, "reason": "why"});
            assert!(
                decode_counterexample_validation(payload).is_err(),
                "code {code:?} must not decode"
            );
        }
    }

    #[test]
    fn the_host_timeout_rejection_is_outside_leans_own_vocabulary() {
        assert_eq!(COUNTEREXAMPLE_TIMEOUT_CODE, "timeout");
        assert!(!LEAN_COUNTEREXAMPLE_REJECTION_CODES.contains(&COUNTEREXAMPLE_TIMEOUT_CODE));
        // Pass 7.7b, item 11: Lean's unreachable replay fuel is reported as
        // an internal fault, so there is no fuel code in the vocabulary.
        assert!(!LEAN_COUNTEREXAMPLE_REJECTION_CODES.contains(&"out_of_fuel"));
        let rejection = CounterexampleRejection::timeout("call-local limit of 30s expired");
        assert_eq!(rejection.code(), "timeout");
        assert_eq!(rejection.reason(), "call-local limit of 30s expired");
    }
}
