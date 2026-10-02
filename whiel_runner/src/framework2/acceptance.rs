//! Records written the moment the untrusted verifier accepts.
//!
//! Certification costs minutes and gigabytes and can fail or time out. Until
//! it succeeded, nothing durable named what the search had found: the frozen
//! Core and the validated counterexample lived in memory only, and a failed
//! certification lost the result outright. This module closes that gap.
//!
//! At acceptance — after the search's own phase has finished and before any
//! certification starts — a run writes into the input's run directory:
//!
//! - `Core.json` for a valid result, or `Counterexample.json` for an invalid
//!   one: the same durable record the certificate build publishes, written
//!   by the same renderer, so a later publication that refuses a *differing*
//!   record finds the one it would have written itself;
//! - [`ACCEPTED_RECORD_NAME`], a small envelope naming that record, the
//!   verdict, the search's timing, the input's task identity, and — for a
//!   valid result — the frozen Core's own canonical payload, which is what a
//!   later `campaign certify` checks the input's identity against.
//!
//! The records authorize nothing on their own. A `Core.json` is an input to
//! a certificate build, not a certificate; the kernel-checked tree is still
//! the only thing that says a result holds.

use std::path::{Path, PathBuf};
use std::time::Duration;

use serde_json::{Value, json};

use super::certificate::{CORE_RECORD_NAME, core_record_text};
use super::counterexample::FrozenCounterexampleRecord;
use super::freeze::CoreFreezeError;
use super::publication::{
    COUNTEREXAMPLE_RECORD_FILE, CounterexampleFuelPolicy, DurableCounterexampleRecord,
    PublicationError, write_record_atomically,
};
use super::search::PreCertificateAgentHoudiniOutcome;
use super::snapshot::LeveledCandidateSnapshot;
use crate::framework2::{AgentProvider, FrameworkIIChecker};
use crate::task::TaskIdentity;

/// The `kind` of the acceptance envelope.
pub const ACCEPTED_RECORD_KIND: &str = "whiel_search_acceptance";

/// The version of the acceptance envelope.
///
/// A run directory is an input to `campaign certify`, so its layout is an
/// interface: a reader that does not know this version fails closed rather
/// than guessing what the members mean.
pub const ACCEPTED_RECORD_VERSION: u64 = 1;

/// The file name of the acceptance envelope, beside the record it names.
pub const ACCEPTED_RECORD_NAME: &str = "Accepted.json";

/// The verdict one acceptance names.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AcceptedVerdict {
    Valid,
    Invalid,
}

impl AcceptedVerdict {
    /// The verdict's own label, as the envelope spells it.
    pub fn name(self) -> &'static str {
        match self {
            Self::Valid => "valid",
            Self::Invalid => "invalid",
        }
    }

    /// The durable record this verdict is recorded as.
    pub fn record_name(self) -> &'static str {
        match self {
            Self::Valid => CORE_RECORD_NAME,
            Self::Invalid => COUNTEREXAMPLE_RECORD_FILE,
        }
    }

    /// The uncertified status an input carries when its run stops here.
    pub fn uncertified_status(self) -> &'static str {
        match self {
            Self::Valid => "valid_uncertified",
            Self::Invalid => "invalid_uncertified",
        }
    }
}

/// What one acceptance wrote.
#[derive(Clone, Debug)]
pub struct WrittenAcceptance {
    verdict: AcceptedVerdict,
    record: PathBuf,
    envelope: PathBuf,
}

impl WrittenAcceptance {
    pub fn verdict(&self) -> AcceptedVerdict {
        self.verdict
    }

    /// The durable record: `Core.json` or `Counterexample.json`.
    pub fn record(&self) -> &Path {
        &self.record
    }

    /// The acceptance envelope beside it.
    pub fn envelope(&self) -> &Path {
        &self.envelope
    }
}

/// Why an acceptance could not be recorded.
#[derive(Debug)]
pub enum AcceptanceRecordError {
    /// The proved Core did not freeze, so there is no payload to name.
    Freeze(CoreFreezeError),
    /// A record could not be installed durably.
    Record(Box<PublicationError>),
}

impl std::fmt::Display for AcceptanceRecordError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Freeze(error) => write!(
                formatter,
                "the accepted Core did not freeze for its record: {error}"
            ),
            Self::Record(error) => write!(formatter, "{error}"),
        }
    }
}

impl std::error::Error for AcceptanceRecordError {}

/// Everything one acceptance record needs beyond the outcome itself.
pub struct AcceptanceRecordRequest<'a> {
    /// The run's own directory for this input. The records go here, beside
    /// where the `Certificate/` tree will be published.
    pub input_directory: &'a Path,
    /// The run's fuel policy, as the search applied it: an invalid record
    /// states the policy its replay must hold to.
    pub fuel_policy: CounterexampleFuelPolicy,
    /// How long the untrusted search itself took, up to acceptance.
    pub search_elapsed: Duration,
    /// The allowance that search ran under.
    pub search_limit: Duration,
}

/// Write the durable record and its envelope for one accepted outcome.
///
/// Returns `Ok(None)` for a failed search, which has nothing to record.
///
/// The valid record is rendered by [`core_record_text`] — the very function
/// the certificate build writes its own `Core.json` with — over the snapshot
/// the freeze is taken from. That is not a convenience: publication refuses
/// a record on disk that differs from the one it would write, so a record
/// rendered any other way would fail a good run at its last step.
pub fn record_acceptance<S, C>(
    outcome: &mut PreCertificateAgentHoudiniOutcome<S, C>,
    request: AcceptanceRecordRequest<'_>,
) -> Result<Option<WrittenAcceptance>, AcceptanceRecordError>
where
    S: AgentProvider,
    C: FrameworkIIChecker,
{
    match outcome {
        PreCertificateAgentHoudiniOutcome::Failure(_) => Ok(None),
        PreCertificateAgentHoudiniOutcome::Valid(handoff) => {
            let bytes = accepted_core_record_bytes(handoff.core_snapshot());
            let payload = handoff
                .frozen_core()
                .map_err(AcceptanceRecordError::Freeze)?
                .payload();
            let identity = task_identity_record_from_payload(&payload);
            write_acceptance(
                &request,
                AcceptedVerdict::Valid,
                &bytes,
                identity,
                Some(payload),
            )
        }
        PreCertificateAgentHoudiniOutcome::Invalid(record) => {
            let bytes = durable_counterexample_bytes(record, request.fuel_policy);
            let identity = task_identity_record(record.task_identity());
            write_acceptance(&request, AcceptedVerdict::Invalid, &bytes, identity, None)
        }
    }
}

/// The exact bytes the certificate build writes as its own `Core.json`.
///
/// One renderer, called from both places. Publication refuses a record on
/// disk that differs from the one it would write, so a second renderer here
/// would fail a good run at its last step, after every job had been proved.
pub(super) fn accepted_core_record_bytes(snapshot: &LeveledCandidateSnapshot) -> Vec<u8> {
    core_record_text(snapshot).into_bytes()
}

/// The exact bytes the invalid publication writes beside the input.
///
/// Byte-for-byte, because the record check at publication compares bytes:
/// the same value, serialized the same way, is what makes the acceptance
/// record and the published one the same record rather than two.
fn durable_counterexample_bytes(
    record: &FrozenCounterexampleRecord,
    fuel_policy: CounterexampleFuelPolicy,
) -> Vec<u8> {
    let durable = DurableCounterexampleRecord::new(record.clone(), fuel_policy);
    serde_json::to_vec_pretty(&durable.to_json())
        .expect("counterexample record JSON is always serializable")
}

fn write_acceptance(
    request: &AcceptanceRecordRequest<'_>,
    verdict: AcceptedVerdict,
    record_bytes: &[u8],
    task_identity: Value,
    core: Option<Value>,
) -> Result<Option<WrittenAcceptance>, AcceptanceRecordError> {
    let record = request.input_directory.join(verdict.record_name());
    write_record_atomically(&record, record_bytes)
        .map_err(|error| AcceptanceRecordError::Record(Box::new(error)))?;
    let envelope_value = json!({
        "kind": ACCEPTED_RECORD_KIND,
        "version": ACCEPTED_RECORD_VERSION,
        "verdict": verdict.name(),
        "record": verdict.record_name(),
        "task_identity": task_identity,
        "search": {
            "elapsed_seconds": request.search_elapsed.as_secs_f64(),
            "limit_seconds": request.search_limit.as_secs_f64(),
        },
        "core": core,
    });
    let envelope = request.input_directory.join(ACCEPTED_RECORD_NAME);
    let mut envelope_bytes =
        serde_json::to_vec_pretty(&envelope_value).expect("the acceptance envelope serializes");
    envelope_bytes.push(b'\n');
    write_record_atomically(&envelope, &envelope_bytes)
        .map_err(|error| AcceptanceRecordError::Record(Box::new(error)))?;
    Ok(Some(WrittenAcceptance {
        verdict,
        record,
        envelope,
    }))
}

/// The task identity fields of one live identity, exactly as the frozen
/// Core's own payload renders them.
///
/// It is the payload's own renderer, not a copy of it: the envelope lifts
/// this object straight out of `FrozenLeveledCore::payload()` for a valid
/// result, and a deferred certification compares the live binding's against
/// it, so two renderers that drifted would report an unchanged input as
/// changed.
pub fn task_identity_record(identity: &TaskIdentity) -> Value {
    super::catalog::task_identity_fields_of(identity)
}

/// The task identity and scope digest one worker manifest names, decoded
/// without binding a worker pool, a solver or a catalog.
///
/// A re-check of a certificate that is already standing needs to know only
/// whether the input is still the input it was built for. Decoding the
/// manifest answers that; binding the whole runtime to ask it would cost a
/// worker process per input for a question the descriptor already settles.
pub fn task_identity_from_worker_manifest(descriptor: &Value) -> Result<(Value, String), String> {
    let bootstrap = super::admission::FixedAmbientTaskBootstrap::from_json(descriptor.clone())
        .map_err(|error| format!("read the worker's manifest: {error}"))?;
    Ok((
        task_identity_record(bootstrap.task().identity()),
        bootstrap.scope().identity_sha256().to_owned(),
    ))
}

/// The task identity a frozen Core payload carries, so the envelope states
/// one identity rather than two that could drift apart.
fn task_identity_record_from_payload(payload: &Value) -> Value {
    payload.get("task_identity").cloned().unwrap_or(Value::Null)
}

/// Read one acceptance envelope, failing closed on a kind or version this
/// host does not define.
pub fn read_acceptance_envelope(path: &Path) -> Result<AcceptanceEnvelope, String> {
    let bytes = std::fs::read(path).map_err(|error| format!("read {}: {error}", path.display()))?;
    let value: Value = serde_json::from_slice(&bytes)
        .map_err(|error| format!("parse {}: {error}", path.display()))?;
    if value.get("kind").and_then(Value::as_str) != Some(ACCEPTED_RECORD_KIND)
        || value.get("version").and_then(Value::as_u64) != Some(ACCEPTED_RECORD_VERSION)
    {
        return Err(format!(
            "{} is not a {ACCEPTED_RECORD_KIND} v{ACCEPTED_RECORD_VERSION} record",
            path.display()
        ));
    }
    let verdict = match value.get("verdict").and_then(Value::as_str) {
        Some("valid") => AcceptedVerdict::Valid,
        Some("invalid") => AcceptedVerdict::Invalid,
        _ => return Err(format!("{} names no known verdict", path.display())),
    };
    Ok(AcceptanceEnvelope {
        verdict,
        task_identity: value.get("task_identity").cloned().unwrap_or(Value::Null),
        core: value.get("core").cloned().filter(|core| !core.is_null()),
        search_elapsed_seconds: value
            .get("search")
            .and_then(|search| search.get("elapsed_seconds"))
            .and_then(Value::as_f64),
    })
}

/// One decoded acceptance envelope.
#[derive(Clone, Debug)]
pub struct AcceptanceEnvelope {
    verdict: AcceptedVerdict,
    task_identity: Value,
    core: Option<Value>,
    search_elapsed_seconds: Option<f64>,
}

impl AcceptanceEnvelope {
    pub fn verdict(&self) -> AcceptedVerdict {
        self.verdict
    }

    /// The task identity recorded at acceptance. A later certification
    /// refuses an input whose own identity differs from this.
    pub fn task_identity(&self) -> &Value {
        &self.task_identity
    }

    /// The frozen Core payload, for a valid acceptance.
    pub fn core(&self) -> Option<&Value> {
        self.core.as_ref()
    }

    /// How long the untrusted search took, as the campaign runner measured
    /// it. The envelope is where that measurement survives a lost
    /// `result.json`.
    pub fn search_elapsed_seconds(&self) -> Option<f64> {
        self.search_elapsed_seconds
    }
}

/// The search half of one settled run, released without certifying it.
///
/// The records are already on disk; what remains is to stop owning the
/// run's resources. Both are consumed here for the same reason
/// [`super::publication::settle_search_outcome`] consumes them: the run is
/// over either way.
pub async fn release_without_certifying<S, C>(
    outcome: PreCertificateAgentHoudiniOutcome<S, C>,
    resources: super::publication::SettlementResources,
) -> Result<(), super::publication::SettlementError>
where
    S: AgentProvider,
    C: FrameworkIIChecker,
{
    // The handoff still borrows the live search; dropping it first is what
    // lets the solver pool shut down with nothing left running against it.
    drop(outcome);
    let super::publication::SettlementResources { solver, artifacts } = resources;
    let shutdown = solver.shutdown().await;
    let backend = artifacts.settle();
    if let Err(error) = shutdown {
        return Err(super::publication::SettlementError::Shutdown(
            error.to_string(),
        ));
    }
    backend.map_err(super::publication::SettlementError::Settlement)
}
