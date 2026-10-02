//! Typed additive adapter to the existing Python certificate authorities.
//!
//! The bridge is a one-shot subprocess. Rust supplies exact task identity and
//! candidate data; the legacy procedures still build and typecheck the
//! unchanged validity and invalidity certificates.

use std::ffi::{OsStr, OsString};
use std::fs::{File, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::mpsc;
use std::thread;
use std::time::{Duration, Instant};
use std::time::{SystemTime, UNIX_EPOCH};

use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::entailment::assembly::Sha256;
use crate::runtime::CancellationToken;
#[cfg(any(target_os = "macos", target_os = "linux"))]
use crate::runtime::process_tree::{ProcessRegistry, signal_group, signal_identity};
use crate::task::SynthesisTask;

const BRIDGE_FORMAT_VERSION: u64 = 1;
const MAX_REQUEST_BYTES: usize = 16 * 1024 * 1024;
const MAX_RESPONSE_BYTES: usize = 16 * 1024 * 1024;
const MAX_STDERR_BYTES: usize = 64 * 1024;
const POLL_INTERVAL: Duration = Duration::from_millis(10);
const TERMINATION_GRACE: Duration = Duration::from_millis(100);
const CLEANUP_GRACE: Duration = Duration::from_millis(750);
static NEXT_OUTPUT_TOKEN: AtomicU64 = AtomicU64::new(1);

// ------------------------------------------------------------
// Public Protocol Types
// ------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CertificationOperation {
    CertifyValid,
    CertifyInvalid,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CertifiedClassification {
    Valid,
    Invalid,
}

#[derive(Clone, Debug, PartialEq)]
pub struct CertificationFailure {
    pub kind: String,
    pub phase: String,
    pub message: String,
    pub elapsed_sec: Option<f64>,
    pub process_status: Option<String>,
    pub returncode: Option<i32>,
    pub stdout_sha256: Option<String>,
    pub stderr_sha256: Option<String>,
    pub witness: Option<WitnessArtifactRef>,
    pub diagnostic: Option<CertificationDiagnosticRef>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WitnessArtifactRef {
    pub path: PathBuf,
    pub sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertificationDiagnosticRef {
    pub path: PathBuf,
    pub sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertifiedBundle {
    pub classification: CertifiedClassification,
    pub bundle: PathBuf,
    pub certificate: PathBuf,
    pub certificate_sha256: String,
    pub witness: Option<WitnessArtifactRef>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum CertificationOutcome {
    Certified(CertifiedBundle),
    Rejected(CertificationRejection),
    Failed(CertificationFailure),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertificationRejection {
    pub kind: String,
    pub message: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ValidityCertificationLimits {
    /// Final solver limit. `None` adds no final-certification-specific limit.
    pub final_search: Option<Duration>,
    /// Final Lean limit. `None` adds no final-certification-specific limit.
    pub lean: Option<Duration>,
    pub max_heartbeats: u64,
    /// Outer bridge limit. `None` leaves the legacy authority in control.
    pub bridge: Option<Duration>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InvalidityCertificationLimits {
    pub runtime: Duration,
    /// Final Lean limit. `None` adds no final-certification-specific limit.
    pub lean: Option<Duration>,
    pub max_heartbeats: u64,
    /// Outer bridge limit. `None` leaves the legacy authority in control.
    pub bridge: Option<Duration>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CertificationBridgeError {
    InvalidRequest(String),
    Launch(String),
    Transport(String),
    TimedOut,
    Cancelled,
    ProcessFailed { status: Option<i32>, stderr: String },
    MalformedResponse(String),
    Cleanup(String),
}

impl std::fmt::Display for CertificationBridgeError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidRequest(detail) => {
                write!(formatter, "invalid certification request: {detail}")
            }
            Self::Launch(detail) => write!(formatter, "start certification bridge: {detail}"),
            Self::Transport(detail) => write!(formatter, "certification transport: {detail}"),
            Self::TimedOut => write!(formatter, "certification bridge timed out"),
            Self::Cancelled => write!(formatter, "certification bridge was cancelled"),
            Self::ProcessFailed { status, stderr } => {
                write!(
                    formatter,
                    "certification bridge exited with {status:?}: {stderr}"
                )
            }
            Self::MalformedResponse(detail) => {
                write!(formatter, "malformed certification response: {detail}")
            }
            Self::Cleanup(detail) => write!(formatter, "certification cleanup failed: {detail}"),
        }
    }
}

impl std::error::Error for CertificationBridgeError {}

// ------------------------------------------------------------
// Bridge Command
// ------------------------------------------------------------

#[derive(Clone, Debug)]
pub struct CertificationBridgeCommand {
    executable: OsString,
    arguments: Arc<[OsString]>,
    repository: PathBuf,
    next_request: Arc<AtomicU64>,
}

impl CertificationBridgeCommand {
    pub fn new(executable: impl Into<OsString>, repository: impl Into<PathBuf>) -> Self {
        Self {
            executable: executable.into(),
            arguments: Arc::from([]),
            repository: repository.into(),
            next_request: Arc::new(AtomicU64::new(1)),
        }
    }

    pub fn python(repository: impl Into<PathBuf>) -> Self {
        Self::new("python3", repository).with_arguments(["-m", "whiel_synth.certification_bridge"])
    }

    pub fn with_arguments<I, S>(mut self, arguments: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: AsRef<OsStr>,
    {
        self.arguments = arguments
            .into_iter()
            .map(|argument| argument.as_ref().to_os_string())
            .collect::<Vec<_>>()
            .into();
        self
    }

    /// Executable used by the retained certification bridge command.
    pub fn executable(&self) -> &OsStr {
        &self.executable
    }

    /// Exact fixed arguments which precede each bridge request.
    pub fn arguments(&self) -> &[OsString] {
        &self.arguments
    }

    /// Repository authority used to resolve bridge-owned paths.
    pub fn repository(&self) -> &Path {
        &self.repository
    }

    pub fn certify_valid<I, S>(
        &self,
        task: &SynthesisTask,
        core: I,
        work_directory: impl AsRef<Path>,
        solution_directory: impl AsRef<Path>,
        limits: ValidityCertificationLimits,
        cancellation: &CancellationToken,
    ) -> Result<CertificationOutcome, CertificationBridgeError>
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let mut core = core.into_iter().map(Into::into).collect::<Vec<_>>();
        if core.iter().any(|formula| formula.trim().is_empty()) {
            return Err(CertificationBridgeError::InvalidRequest(
                "Core contains an empty formula".to_string(),
            ));
        }
        core.sort();
        if core.windows(2).any(|pair| pair[0] == pair[1]) {
            return Err(CertificationBridgeError::InvalidRequest(
                "Core contains duplicate canonical formulas".to_string(),
            ));
        }
        let request_id = self.allocate_request_id()?;
        let work_directory = self.absolute_under_repository(work_directory.as_ref())?;
        let solution_directory = self.absolute_under_repository(solution_directory.as_ref())?;
        let output_lease = OutputLease::acquire(&solution_directory)?;
        let request = ValidityRequest {
            format_version: BRIDGE_FORMAT_VERSION,
            request_id,
            operation: CertificationOperation::CertifyValid,
            task_identity: TaskIdentityEnvelope::from(task),
            work_directory: work_directory.clone(),
            solution_directory: solution_directory.clone(),
            output_token: output_lease.token().to_string(),
            core,
            final_search_limit_seconds: optional_whole_positive_seconds(
                limits.final_search,
                "final search",
            )?,
            lean_limit_seconds: optional_whole_positive_seconds(limits.lean, "Lean")?,
            max_heartbeats: positive(limits.max_heartbeats, "max_heartbeats")?,
        };
        let result = self.invoke(
            &request,
            request_id,
            CertificationOperation::CertifyValid,
            task,
            &work_directory,
            &solution_directory,
            None,
            limits.bridge,
            cancellation,
        );
        settle_bridge_output(result, output_lease)
    }

    #[allow(clippy::too_many_arguments)]
    pub fn certify_invalid(
        &self,
        task: &SynthesisTask,
        input_instance: Value,
        fuel: u64,
        work_directory: impl AsRef<Path>,
        solution_directory: impl AsRef<Path>,
        limits: InvalidityCertificationLimits,
        cancellation: &CancellationToken,
    ) -> Result<CertificationOutcome, CertificationBridgeError> {
        let request_id = self.allocate_request_id()?;
        let work_directory = self.absolute_under_repository(work_directory.as_ref())?;
        let solution_directory = self.absolute_under_repository(solution_directory.as_ref())?;
        let output_lease = OutputLease::acquire(&solution_directory)?;
        let request = InvalidityRequest {
            format_version: BRIDGE_FORMAT_VERSION,
            request_id,
            operation: CertificationOperation::CertifyInvalid,
            task_identity: TaskIdentityEnvelope::from(task),
            work_directory: work_directory.clone(),
            solution_directory: solution_directory.clone(),
            output_token: output_lease.token().to_string(),
            input_instance,
            fuel: positive(fuel, "fuel")?,
            runtime_limit_seconds: whole_positive_seconds(limits.runtime, "runtime")?,
            lean_limit_seconds: optional_whole_positive_seconds(limits.lean, "Lean")?,
            max_heartbeats: positive(limits.max_heartbeats, "max_heartbeats")?,
        };
        let result = self.invoke(
            &request,
            request_id,
            CertificationOperation::CertifyInvalid,
            task,
            &work_directory,
            &solution_directory,
            Some(&request.input_instance),
            limits.bridge,
            cancellation,
        );
        settle_bridge_output(result, output_lease)
    }

    #[allow(clippy::too_many_arguments)]
    fn invoke<T: Serialize>(
        &self,
        request: &T,
        request_id: u64,
        operation: CertificationOperation,
        task: &SynthesisTask,
        work_directory: &Path,
        solution_directory: &Path,
        expected_input: Option<&Value>,
        limit: Option<Duration>,
        cancellation: &CancellationToken,
    ) -> Result<CertificationOutcome, CertificationBridgeError> {
        let encoded = serde_json::to_vec(request).map_err(|error| {
            CertificationBridgeError::InvalidRequest(format!("encode request: {error}"))
        })?;
        if encoded.len() > MAX_REQUEST_BYTES {
            return Err(CertificationBridgeError::InvalidRequest(format!(
                "encoded request has {} bytes; maximum is {MAX_REQUEST_BYTES}",
                encoded.len()
            )));
        }
        let capture = run_bridge_process(self, &encoded, limit, cancellation)?;
        if !capture.status.success() {
            return Err(CertificationBridgeError::ProcessFailed {
                status: capture.status.code(),
                stderr: bounded_text(&capture.stderr, MAX_STDERR_BYTES),
            });
        }
        let raw: BridgeResponse = serde_json::from_slice(&capture.stdout).map_err(|error| {
            CertificationBridgeError::MalformedResponse(format!("decode JSON: {error}"))
        })?;
        validate_response(
            raw,
            request_id,
            operation,
            task,
            work_directory,
            solution_directory,
            expected_input,
        )
    }

    fn allocate_request_id(&self) -> Result<u64, CertificationBridgeError> {
        self.next_request
            .fetch_update(Ordering::AcqRel, Ordering::Acquire, |current| {
                current.checked_add(1)
            })
            .map_err(|_| {
                CertificationBridgeError::InvalidRequest(
                    "certification request identity space exhausted".to_string(),
                )
            })
    }

    fn absolute_under_repository(&self, path: &Path) -> Result<PathBuf, CertificationBridgeError> {
        let repository = self.repository.canonicalize().map_err(|error| {
            CertificationBridgeError::InvalidRequest(format!("resolve repository: {error}"))
        })?;
        let absolute = if path.is_absolute() {
            path.to_path_buf()
        } else {
            repository.join(path)
        };
        let resolved = resolve_allow_missing(&absolute)?;
        if !resolved.starts_with(&repository) {
            return Err(CertificationBridgeError::InvalidRequest(
                "certification directory escapes the repository".to_string(),
            ));
        }
        Ok(resolved)
    }
}

// ------------------------------------------------------------
// Wire Representation
// ------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct TaskIdentityEnvelope {
    canonical_id: String,
    module: String,
    namespace: String,
    source_sha256: String,
    semantic_version: u64,
    encoding_version: u64,
}

impl From<&SynthesisTask> for TaskIdentityEnvelope {
    fn from(task: &SynthesisTask) -> Self {
        let identity = task.identity();
        Self {
            canonical_id: identity.canonical_id().to_string(),
            module: identity.module().to_string(),
            namespace: identity.namespace().to_string(),
            source_sha256: identity.source_digest().as_str().to_string(),
            semantic_version: identity.semantic_version(),
            encoding_version: identity.encoding_version(),
        }
    }
}

#[derive(Serialize)]
struct ValidityRequest {
    format_version: u64,
    request_id: u64,
    operation: CertificationOperation,
    task_identity: TaskIdentityEnvelope,
    work_directory: PathBuf,
    solution_directory: PathBuf,
    output_token: String,
    core: Vec<String>,
    final_search_limit_seconds: Option<u64>,
    lean_limit_seconds: Option<u64>,
    max_heartbeats: u64,
}

#[derive(Serialize)]
struct InvalidityRequest {
    format_version: u64,
    request_id: u64,
    operation: CertificationOperation,
    task_identity: TaskIdentityEnvelope,
    work_directory: PathBuf,
    solution_directory: PathBuf,
    output_token: String,
    input_instance: Value,
    fuel: u64,
    runtime_limit_seconds: u64,
    lean_limit_seconds: Option<u64>,
    max_heartbeats: u64,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
#[serde(tag = "status", rename_all = "snake_case")]
enum BridgeResponse {
    Certified {
        format_version: u64,
        request_id: u64,
        operation: CertificationOperation,
        task_identity: TaskIdentityEnvelope,
        classification: CertifiedClassification,
        bundle: PathBuf,
        certificate: PathBuf,
        certificate_sha256: String,
        #[serde(default)]
        witness: Option<WitnessEnvelope>,
    },
    Failed {
        format_version: u64,
        request_id: u64,
        operation: CertificationOperation,
        task_identity: TaskIdentityEnvelope,
        failure: FailureEnvelope,
        #[serde(default)]
        witness: Option<WitnessEnvelope>,
        #[serde(default)]
        diagnostic: Option<ArtifactEnvelope>,
    },
    Rejected {
        format_version: u64,
        request_id: u64,
        operation: CertificationOperation,
        task_identity: TaskIdentityEnvelope,
        rejection: RejectionEnvelope,
    },
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ArtifactEnvelope {
    path: PathBuf,
    sha256: String,
}

type WitnessEnvelope = ArtifactEnvelope;

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RejectionEnvelope {
    kind: String,
    message: String,
}

#[derive(Deserialize, PartialEq)]
#[serde(deny_unknown_fields)]
struct FailureEnvelope {
    kind: String,
    phase: String,
    message: String,
    #[serde(default)]
    elapsed_sec: Option<f64>,
    #[serde(default)]
    process_status: Option<String>,
    #[serde(default)]
    returncode: Option<i32>,
    #[serde(default)]
    stdout_hash: Option<String>,
    #[serde(default)]
    stderr_hash: Option<String>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WitnessRecord {
    format_version: u64,
    task_identity: TaskIdentityEnvelope,
    input_instance: Value,
    output_instance: Value,
    fuel: u64,
    runtime: WitnessRuntimeRecord,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WitnessRuntimeRecord {
    stdout_sha256: String,
    stderr_sha256: String,
    elapsed_sec: f64,
    process_status: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct DiagnosticRecord {
    format_version: u64,
    task_identity: TaskIdentityEnvelope,
    operation: CertificationOperation,
    failure: FailureEnvelope,
}

fn validate_response(
    response: BridgeResponse,
    request_id: u64,
    operation: CertificationOperation,
    task: &SynthesisTask,
    work_directory: &Path,
    solution_directory: &Path,
    expected_input: Option<&Value>,
) -> Result<CertificationOutcome, CertificationBridgeError> {
    let expected_identity = TaskIdentityEnvelope::from(task);
    if solution_directory.exists() && !solution_directory.is_dir() {
        return Err(CertificationBridgeError::MalformedResponse(
            "bridge output path is not a solution directory".to_string(),
        ));
    }
    match response {
        BridgeResponse::Certified {
            format_version,
            request_id: returned_id,
            operation: returned_operation,
            task_identity,
            classification,
            bundle,
            certificate,
            certificate_sha256,
            witness,
        } => {
            validate_envelope(
                format_version,
                returned_id,
                returned_operation,
                &task_identity,
                request_id,
                operation,
                &expected_identity,
            )?;
            let expected_classification = match operation {
                CertificationOperation::CertifyValid => CertifiedClassification::Valid,
                CertificationOperation::CertifyInvalid => CertifiedClassification::Invalid,
            };
            if classification != expected_classification || !valid_sha256(&certificate_sha256) {
                return Err(CertificationBridgeError::MalformedResponse(
                    "certified response does not name the exact requested bundle".to_string(),
                ));
            }
            let certificate =
                validate_published_certificate(&bundle, &certificate, solution_directory)?;
            let actual_digest = file_sha256(&certificate)?;
            if !certificate_sha256.eq_ignore_ascii_case(&actual_digest) {
                return Err(CertificationBridgeError::MalformedResponse(
                    "certificate hash does not match the published file".to_string(),
                ));
            }
            let witness = match (operation, witness, expected_input) {
                (CertificationOperation::CertifyValid, None, None) => None,
                (CertificationOperation::CertifyInvalid, Some(witness), Some(input)) => {
                    Some(validate_witness(witness, task, work_directory, input)?)
                }
                _ => {
                    return Err(CertificationBridgeError::MalformedResponse(
                        "certified response has an invalid Witness reference".to_string(),
                    ));
                }
            };
            Ok(CertificationOutcome::Certified(CertifiedBundle {
                classification,
                bundle,
                certificate,
                certificate_sha256,
                witness,
            }))
        }
        BridgeResponse::Failed {
            format_version,
            request_id: returned_id,
            operation: returned_operation,
            task_identity,
            failure,
            witness,
            diagnostic,
        } => {
            validate_envelope(
                format_version,
                returned_id,
                returned_operation,
                &task_identity,
                request_id,
                operation,
                &expected_identity,
            )?;
            if solution_directory.exists() {
                return Err(CertificationBridgeError::MalformedResponse(
                    "failed certification published a solution bundle".to_string(),
                ));
            }
            let witness = match (operation, witness, expected_input) {
                (CertificationOperation::CertifyValid, None, None) => None,
                (CertificationOperation::CertifyInvalid, None, Some(_)) => None,
                (CertificationOperation::CertifyInvalid, Some(witness), Some(input)) => {
                    Some(validate_witness(witness, task, work_directory, input)?)
                }
                _ => {
                    return Err(CertificationBridgeError::MalformedResponse(
                        "failed response has an invalid Witness reference".to_string(),
                    ));
                }
            };
            validate_failure_metadata(&failure)?;
            let diagnostic = match diagnostic {
                Some(diagnostic) => Some(validate_diagnostic(
                    diagnostic,
                    task,
                    work_directory,
                    operation,
                    &failure,
                )?),
                None => None,
            };
            Ok(CertificationOutcome::Failed(CertificationFailure {
                kind: bounded_string(failure.kind, 256),
                phase: bounded_string(failure.phase, 256),
                message: bounded_string(failure.message, 4096),
                elapsed_sec: failure.elapsed_sec,
                process_status: failure
                    .process_status
                    .map(|value| bounded_string(value, 256)),
                returncode: failure.returncode,
                stdout_sha256: failure.stdout_hash,
                stderr_sha256: failure.stderr_hash,
                witness,
                diagnostic,
            }))
        }
        BridgeResponse::Rejected {
            format_version,
            request_id: returned_id,
            operation: returned_operation,
            task_identity,
            rejection,
        } => {
            validate_envelope(
                format_version,
                returned_id,
                returned_operation,
                &task_identity,
                request_id,
                operation,
                &expected_identity,
            )?;
            if operation != CertificationOperation::CertifyInvalid
                || expected_input.is_none()
                || solution_directory.exists()
            {
                return Err(CertificationBridgeError::MalformedResponse(
                    "rejected response is invalid for this certification request".to_string(),
                ));
            }
            Ok(CertificationOutcome::Rejected(CertificationRejection {
                kind: bounded_string(rejection.kind, 256),
                message: bounded_string(rejection.message, 4096),
            }))
        }
    }
}

fn validate_failure_metadata(failure: &FailureEnvelope) -> Result<(), CertificationBridgeError> {
    if failure
        .elapsed_sec
        .is_some_and(|elapsed| !elapsed.is_finite() || elapsed < 0.0)
        || failure
            .stdout_hash
            .as_deref()
            .is_some_and(|digest| !valid_sha256(digest))
        || failure
            .stderr_hash
            .as_deref()
            .is_some_and(|digest| !valid_sha256(digest))
    {
        return Err(CertificationBridgeError::MalformedResponse(
            "failure response has malformed diagnostic metadata".to_string(),
        ));
    }
    Ok(())
}

fn validate_envelope(
    format_version: u64,
    returned_id: u64,
    returned_operation: CertificationOperation,
    returned_identity: &TaskIdentityEnvelope,
    expected_id: u64,
    expected_operation: CertificationOperation,
    expected_identity: &TaskIdentityEnvelope,
) -> Result<(), CertificationBridgeError> {
    if format_version != BRIDGE_FORMAT_VERSION
        || returned_id != expected_id
        || returned_operation != expected_operation
        || returned_identity != expected_identity
    {
        return Err(CertificationBridgeError::MalformedResponse(
            "response envelope does not match the exact request".to_string(),
        ));
    }
    Ok(())
}

fn validate_witness(
    witness: WitnessEnvelope,
    task: &SynthesisTask,
    work_directory: &Path,
    expected_input: &Value,
) -> Result<WitnessArtifactRef, CertificationBridgeError> {
    if !valid_sha256(&witness.sha256) {
        return Err(CertificationBridgeError::MalformedResponse(
            "Witness reference lacks one regular artifact and SHA-256".to_string(),
        ));
    }
    let expected_directory = work_directory.join("required/witnesses");
    let path = validate_regular_artifact_path(&witness.path, &expected_directory, "Witness")?;
    let file_name = path.file_name().and_then(OsStr::to_str).unwrap_or_default();
    let key = file_name.strip_suffix(".json").unwrap_or_default();
    if !valid_sha256(key) {
        return Err(CertificationBridgeError::MalformedResponse(
            "Witness artifact has an invalid identity name".to_string(),
        ));
    }
    let actual_digest = file_sha256(&path)?;
    if !witness.sha256.eq_ignore_ascii_case(&actual_digest) {
        return Err(CertificationBridgeError::MalformedResponse(
            "Witness hash does not match the retained artifact".to_string(),
        ));
    }
    let bytes = std::fs::read(&path).map_err(|error| {
        CertificationBridgeError::MalformedResponse(format!("read Witness artifact: {error}"))
    })?;
    let record: WitnessRecord = serde_json::from_slice(&bytes).map_err(|error| {
        CertificationBridgeError::MalformedResponse(format!("decode Witness artifact: {error}"))
    })?;
    if record.format_version != 1
        || record.task_identity != TaskIdentityEnvelope::from(task)
        || record.input_instance != *expected_input
        || !record.output_instance.is_object()
        || record.fuel == 0
        || !valid_sha256(&record.runtime.stdout_sha256)
        || !valid_sha256(&record.runtime.stderr_sha256)
        || !record.runtime.elapsed_sec.is_finite()
        || record.runtime.elapsed_sec < 0.0
        || record.runtime.process_status != "completed"
    {
        return Err(CertificationBridgeError::MalformedResponse(
            "Witness artifact does not match the exact task and input".to_string(),
        ));
    }
    let expected_key = witness_identity_key(&record.task_identity, &record.input_instance)?;
    if !key.eq_ignore_ascii_case(&expected_key) {
        return Err(CertificationBridgeError::MalformedResponse(
            "Witness artifact name does not match its task and input".to_string(),
        ));
    }
    Ok(WitnessArtifactRef {
        path,
        sha256: actual_digest,
    })
}

fn validate_diagnostic(
    diagnostic: ArtifactEnvelope,
    task: &SynthesisTask,
    work_directory: &Path,
    operation: CertificationOperation,
    expected_failure: &FailureEnvelope,
) -> Result<CertificationDiagnosticRef, CertificationBridgeError> {
    if !valid_sha256(&diagnostic.sha256) {
        return Err(CertificationBridgeError::MalformedResponse(
            "certification diagnostic has an invalid SHA-256".to_string(),
        ));
    }
    let path = validate_regular_artifact_path(
        &diagnostic.path,
        &work_directory.join("required/certification-diagnostics"),
        "certification diagnostic",
    )?;
    let file_name = path.file_name().and_then(OsStr::to_str).unwrap_or_default();
    let key = file_name.strip_suffix(".json").unwrap_or_default();
    if !valid_sha256(key) {
        return Err(CertificationBridgeError::MalformedResponse(
            "certification diagnostic has an invalid identity name".to_string(),
        ));
    }
    let actual_digest = file_sha256(&path)?;
    if !diagnostic.sha256.eq_ignore_ascii_case(&actual_digest)
        || !key.eq_ignore_ascii_case(&actual_digest)
    {
        return Err(CertificationBridgeError::MalformedResponse(
            "certification diagnostic hash does not match the retained artifact".to_string(),
        ));
    }
    let bytes = std::fs::read(&path).map_err(|error| {
        CertificationBridgeError::MalformedResponse(format!(
            "read certification diagnostic: {error}"
        ))
    })?;
    let record: DiagnosticRecord = serde_json::from_slice(&bytes).map_err(|error| {
        CertificationBridgeError::MalformedResponse(format!(
            "decode certification diagnostic: {error}"
        ))
    })?;
    validate_failure_metadata(&record.failure)?;
    if record.format_version != 1
        || record.task_identity != TaskIdentityEnvelope::from(task)
        || record.operation != operation
        || record.failure != *expected_failure
    {
        return Err(CertificationBridgeError::MalformedResponse(
            "certification diagnostic does not match the exact request".to_string(),
        ));
    }
    Ok(CertificationDiagnosticRef {
        path,
        sha256: actual_digest,
    })
}

fn validate_regular_artifact_path(
    path: &Path,
    expected_directory: &Path,
    label: &str,
) -> Result<PathBuf, CertificationBridgeError> {
    reject_symlink_components(path, label)?;
    reject_symlink_components(expected_directory, label)?;
    let metadata = std::fs::symlink_metadata(path).map_err(|error| {
        CertificationBridgeError::MalformedResponse(format!("inspect {label} artifact: {error}"))
    })?;
    if !metadata.file_type().is_file() {
        return Err(CertificationBridgeError::MalformedResponse(format!(
            "{label} artifact is not one regular file"
        )));
    }
    let resolved = path.canonicalize().map_err(|error| {
        CertificationBridgeError::MalformedResponse(format!("resolve {label} artifact: {error}"))
    })?;
    let directory = expected_directory.canonicalize().map_err(|error| {
        CertificationBridgeError::MalformedResponse(format!(
            "resolve required {label} directory: {error}"
        ))
    })?;
    if resolved != path || resolved.parent() != Some(directory.as_path()) {
        return Err(CertificationBridgeError::MalformedResponse(format!(
            "{label} artifact is outside its exact canonical directory"
        )));
    }
    Ok(resolved)
}

fn validate_published_certificate(
    returned_bundle: &Path,
    returned_certificate: &Path,
    expected_bundle: &Path,
) -> Result<PathBuf, CertificationBridgeError> {
    if returned_bundle != expected_bundle
        || returned_certificate != expected_bundle.join("Certificate.lean")
    {
        return Err(CertificationBridgeError::MalformedResponse(
            "certified response does not name the exact requested bundle".to_string(),
        ));
    }
    reject_symlink_components(expected_bundle, "certificate bundle")?;
    reject_symlink_components(returned_certificate, "certificate")?;
    let bundle_metadata = std::fs::symlink_metadata(expected_bundle).map_err(|error| {
        CertificationBridgeError::MalformedResponse(format!("inspect certificate bundle: {error}"))
    })?;
    let certificate_metadata =
        std::fs::symlink_metadata(returned_certificate).map_err(|error| {
            CertificationBridgeError::MalformedResponse(format!("inspect certificate: {error}"))
        })?;
    if !bundle_metadata.file_type().is_dir() || !certificate_metadata.file_type().is_file() {
        return Err(CertificationBridgeError::MalformedResponse(
            "published certificate is not one regular file in one regular bundle".to_string(),
        ));
    }
    let canonical_bundle = expected_bundle.canonicalize().map_err(|error| {
        CertificationBridgeError::MalformedResponse(format!("resolve certificate bundle: {error}"))
    })?;
    let canonical_certificate = returned_certificate.canonicalize().map_err(|error| {
        CertificationBridgeError::MalformedResponse(format!("resolve certificate: {error}"))
    })?;
    if canonical_bundle != expected_bundle
        || canonical_certificate != returned_certificate
        || canonical_certificate.parent() != Some(canonical_bundle.as_path())
    {
        return Err(CertificationBridgeError::MalformedResponse(
            "published certificate escapes its exact canonical bundle".to_string(),
        ));
    }
    Ok(canonical_certificate)
}

fn reject_symlink_components(path: &Path, label: &str) -> Result<(), CertificationBridgeError> {
    let mut current = PathBuf::new();
    for component in path.components() {
        current.push(component.as_os_str());
        match std::fs::symlink_metadata(&current) {
            Ok(metadata) if metadata.file_type().is_symlink() => {
                return Err(CertificationBridgeError::MalformedResponse(format!(
                    "{label} path contains a symbolic link"
                )));
            }
            Ok(_) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => {
                return Err(CertificationBridgeError::MalformedResponse(format!(
                    "inspect {label} path: {error}"
                )));
            }
        }
    }
    Ok(())
}

fn witness_identity_key(
    identity: &TaskIdentityEnvelope,
    input: &Value,
) -> Result<String, CertificationBridgeError> {
    let canonical = canonical_json(&serde_json::json!({
        "task_identity": identity,
        "input_instance": input,
    }))?;
    let mut digest = Sha256::new();
    digest.update(&canonical);
    Ok(digest.finalize_hex())
}

fn canonical_json(value: &Value) -> Result<Vec<u8>, CertificationBridgeError> {
    fn sorted(value: &Value) -> Value {
        match value {
            Value::Object(entries) => {
                let mut keys = entries.keys().collect::<Vec<_>>();
                keys.sort();
                let mut result = serde_json::Map::new();
                for key in keys {
                    result.insert(key.clone(), sorted(&entries[key]));
                }
                Value::Object(result)
            }
            Value::Array(values) => Value::Array(values.iter().map(sorted).collect()),
            _ => value.clone(),
        }
    }
    serde_json::to_vec(&sorted(value)).map_err(|error| {
        CertificationBridgeError::MalformedResponse(format!(
            "encode canonical artifact identity: {error}"
        ))
    })
}

// ------------------------------------------------------------
// Owned One-Shot Process
// ------------------------------------------------------------

struct ProcessCapture {
    status: std::process::ExitStatus,
    stdout: Vec<u8>,
    stderr: Vec<u8>,
}

fn run_bridge_process(
    command: &CertificationBridgeCommand,
    request: &[u8],
    limit: Option<Duration>,
    cancellation: &CancellationToken,
) -> Result<ProcessCapture, CertificationBridgeError> {
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    return Err(CertificationBridgeError::Launch(
        "owned process-tree supervision is unavailable on this platform".to_string(),
    ));

    if cancellation.is_cancelled() {
        return Err(CertificationBridgeError::Cancelled);
    }
    let started = Instant::now();
    let mut invocation = Command::new(&command.executable);
    invocation
        .args(command.arguments.iter())
        .current_dir(&command.repository)
        .env("WHIEL_OUTER_PROCESS_GROUP", "1")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        invocation.process_group(0);
    }
    let mut child = invocation
        .spawn()
        .map_err(|error| CertificationBridgeError::Launch(error.to_string()))?;
    let pid = child.id();
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    let mut registry = ProcessRegistry::new(pid).map_err(|error| {
        let mut cleanup = Vec::new();
        record_signal(
            signal_group(pid, libc::SIGKILL),
            "kill unregistered bridge",
            &mut cleanup,
        );
        let _ = child.kill();
        let _ = child.wait();
        CertificationBridgeError::Launch(if cleanup.is_empty() {
            error
        } else {
            format!("{error}; {}", cleanup.join("; "))
        })
    })?;

    let mut stdin = child.stdin.take().expect("piped bridge stdin exists");
    let stdout = child.stdout.take().expect("piped bridge stdout exists");
    let stderr = child.stderr.take().expect("piped bridge stderr exists");
    let stdout_thread = thread::spawn(move || capture_stream(stdout, MAX_RESPONSE_BYTES, false));
    let stderr_thread = thread::spawn(move || capture_stream(stderr, MAX_STDERR_BYTES, true));
    let request = request.to_vec();
    let (stdin_sender, stdin_receiver) = mpsc::sync_channel(1);
    let stdin_thread = thread::spawn(move || {
        let result = stdin
            .write_all(&request)
            .and_then(|_| stdin.flush())
            .map_err(|error| format!("write request: {error}"));
        let _ = stdin_sender.send(result.clone());
        result
    });

    let forced_error = loop {
        registry.refresh();
        match observe_exit(pid) {
            Ok(true) => break None,
            Ok(false) => {}
            Err(error) => {
                break Some(CertificationBridgeError::Transport(format!(
                    "observe bridge exit: {error}"
                )));
            }
        }
        if let Ok(Err(error)) = stdin_receiver.try_recv() {
            break Some(CertificationBridgeError::Transport(error));
        }
        if cancellation.is_cancelled() {
            break Some(CertificationBridgeError::Cancelled);
        }
        if limit.is_some_and(|value| started.elapsed() >= value) {
            break Some(CertificationBridgeError::TimedOut);
        }
        thread::sleep(POLL_INTERVAL);
    };
    let status = cleanup_process(&mut child, &mut registry, forced_error.is_some());
    let stdin_result = stdin_thread
        .join()
        .map_err(|_| CertificationBridgeError::Transport("stdin transport panicked".to_string()))?;
    let stdout = stdout_thread.join().map_err(|_| {
        CertificationBridgeError::Transport("stdout capture panicked".to_string())
    })??;
    let stderr = stderr_thread.join().map_err(|_| {
        CertificationBridgeError::Transport("stderr capture panicked".to_string())
    })??;
    let status = status.map_err(CertificationBridgeError::Cleanup)?;
    if let Some(error) = forced_error {
        return Err(error);
    }
    stdin_result.map_err(CertificationBridgeError::Transport)?;
    Ok(ProcessCapture {
        status,
        stdout,
        stderr,
    })
}

fn capture_stream(
    mut stream: impl Read,
    maximum: usize,
    retain_suffix: bool,
) -> Result<Vec<u8>, CertificationBridgeError> {
    let mut retained = Vec::new();
    let mut total = 0usize;
    let mut buffer = [0_u8; 8192];
    loop {
        let count = stream.read(&mut buffer).map_err(|error| {
            CertificationBridgeError::Transport(format!("read bridge output: {error}"))
        })?;
        if count == 0 {
            break;
        }
        total = total.saturating_add(count);
        if retain_suffix {
            retained.extend_from_slice(&buffer[..count]);
            if retained.len() > maximum {
                retained.drain(..retained.len() - maximum);
            }
        } else if retained.len() < maximum {
            let remaining = maximum - retained.len();
            retained.extend_from_slice(&buffer[..count.min(remaining)]);
        }
    }
    if !retain_suffix && total > maximum {
        return Err(CertificationBridgeError::MalformedResponse(format!(
            "response has {total} bytes; maximum is {maximum}"
        )));
    }
    Ok(retained)
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
fn cleanup_process(
    child: &mut Child,
    registry: &mut ProcessRegistry,
    force: bool,
) -> Result<std::process::ExitStatus, String> {
    let mut errors = Vec::new();
    registry.refresh();
    if force {
        signal_owned(registry, child.id(), libc::SIGTERM, &mut errors);
        let deadline = Instant::now() + TERMINATION_GRACE;
        while Instant::now() < deadline {
            registry.refresh();
            if registry.owned_live_descendants(child.id()).is_empty()
                && observe_exit(child.id()).unwrap_or(false)
            {
                break;
            }
            thread::sleep(POLL_INTERVAL);
        }
    }
    signal_owned(registry, child.id(), libc::SIGKILL, &mut errors);
    if let Err(error) = child.kill()
        && error.kind() != std::io::ErrorKind::InvalidInput
    {
        errors.push(format!("kill direct certification bridge: {error}"));
    }
    let deadline = Instant::now() + CLEANUP_GRACE;
    let mut survivors = registry.owned_live_descendants(child.id());
    while !survivors.is_empty() && Instant::now() < deadline {
        for process in &survivors {
            record_signal(
                signal_identity(&process.identity, libc::SIGKILL),
                "kill bridge descendant",
                &mut errors,
            );
        }
        thread::sleep(POLL_INTERVAL);
        registry.refresh();
        survivors = registry.owned_live_descendants(child.id());
    }
    if !survivors.is_empty() {
        errors.push(format!(
            "owned certification descendants survived cleanup: {:?}",
            survivors
                .iter()
                .map(|process| process.identity.pid)
                .collect::<Vec<_>>()
        ));
    }
    let status = child.wait().map_err(|error| {
        errors.push(format!("reap certification bridge: {error}"));
        errors.join("; ")
    })?;
    if errors.is_empty() {
        Ok(status)
    } else {
        Err(errors.join("; "))
    }
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
fn signal_owned(registry: &mut ProcessRegistry, group: u32, signal: i32, errors: &mut Vec<String>) {
    registry.refresh();
    let mut descendants = registry.owned_live_descendants(group);
    descendants.sort_by_key(|process| std::cmp::Reverse(process.depth));
    for process in descendants {
        record_signal(
            signal_identity(&process.identity, signal),
            "signal certification descendant",
            errors,
        );
    }
    record_signal(
        signal_group(group, signal),
        "signal certification group",
        errors,
    );
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
fn record_signal(result: std::io::Result<()>, label: &str, errors: &mut Vec<String>) {
    if let Err(error) = result
        && !matches!(error.raw_os_error(), Some(libc::ESRCH) | Some(libc::EPERM))
    {
        errors.push(format!("{label}: {error}"));
    }
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
fn observe_exit(pid: u32) -> std::io::Result<bool> {
    let mut information = std::mem::MaybeUninit::<libc::siginfo_t>::zeroed();
    let result = unsafe {
        libc::waitid(
            libc::P_PID,
            pid as libc::id_t,
            information.as_mut_ptr(),
            libc::WEXITED | libc::WNOHANG | libc::WNOWAIT,
        )
    };
    if result != 0 {
        let error = std::io::Error::last_os_error();
        if error.kind() == std::io::ErrorKind::Interrupted {
            return Ok(false);
        }
        return Err(error);
    }
    let information = unsafe { information.assume_init() };
    Ok(unsafe { information.si_pid() } != 0)
}

// ------------------------------------------------------------
// Validation Helpers
// ------------------------------------------------------------

struct OutputLease {
    file: File,
    solution: PathBuf,
    token: String,
}

impl OutputLease {
    fn acquire(solution: &Path) -> Result<Self, CertificationBridgeError> {
        #[cfg(not(any(target_os = "macos", target_os = "linux")))]
        return Err(CertificationBridgeError::InvalidRequest(
            "certification output locking is unavailable on this platform".to_string(),
        ));

        let parent = solution.parent().ok_or_else(|| {
            CertificationBridgeError::InvalidRequest("solution directory has no parent".to_string())
        })?;
        std::fs::create_dir_all(parent).map_err(|error| {
            CertificationBridgeError::InvalidRequest(format!(
                "create certification output parent: {error}"
            ))
        })?;
        reject_symlink_components(parent, "certification output parent")?;
        if std::fs::symlink_metadata(solution).is_ok() {
            return Err(CertificationBridgeError::InvalidRequest(
                "solution directory already exists".to_string(),
            ));
        }
        let mut path_digest = Sha256::new();
        path_digest.update(solution.as_os_str().as_encoded_bytes());
        let lock_path = parent.join(format!(
            ".certification-{}.lock",
            path_digest.finalize_hex()
        ));
        let mut options = OpenOptions::new();
        options.create(true).truncate(false).read(true).write(true);
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        {
            use std::os::unix::fs::OpenOptionsExt;
            options.custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC);
        }
        let mut file = options.open(&lock_path).map_err(|error| {
            CertificationBridgeError::InvalidRequest(format!(
                "open certification output lock: {error}"
            ))
        })?;
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        {
            use std::os::fd::AsRawFd;
            let result = unsafe { libc::flock(file.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) };
            if result != 0 {
                return Err(CertificationBridgeError::InvalidRequest(
                    "solution directory is already owned by another certification".to_string(),
                ));
            }
        }
        if std::fs::symlink_metadata(solution).is_ok() {
            return Err(CertificationBridgeError::InvalidRequest(
                "solution directory appeared while acquiring certification ownership".to_string(),
            ));
        }
        let sequence = NEXT_OUTPUT_TOKEN.fetch_add(1, Ordering::Relaxed);
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_nanos();
        let mut token_digest = Sha256::new();
        token_digest.update(solution.as_os_str().as_encoded_bytes());
        token_digest.update(&std::process::id().to_le_bytes());
        token_digest.update(&sequence.to_le_bytes());
        token_digest.update(&nanos.to_le_bytes());
        let token = token_digest.finalize_hex();
        file.set_len(0).map_err(|error| {
            CertificationBridgeError::InvalidRequest(format!(
                "reset certification output lock: {error}"
            ))
        })?;
        file.seek(SeekFrom::Start(0)).map_err(|error| {
            CertificationBridgeError::InvalidRequest(format!(
                "seek certification output lock: {error}"
            ))
        })?;
        file.write_all(token.as_bytes())
            .and_then(|_| file.sync_all())
            .map_err(|error| {
                CertificationBridgeError::InvalidRequest(format!(
                    "record certification output ownership: {error}"
                ))
            })?;
        Ok(Self {
            file,
            solution: solution.to_path_buf(),
            token,
        })
    }

    fn token(&self) -> &str {
        &self.token
    }

    fn stage(&self) -> PathBuf {
        self.solution.with_file_name(format!(
            "{}.stage-{}",
            self.solution
                .file_name()
                .and_then(OsStr::to_str)
                .unwrap_or("solution"),
            self.token
        ))
    }
}

impl Drop for OutputLease {
    fn drop(&mut self) {
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        {
            use std::os::fd::AsRawFd;
            let _ = unsafe { libc::flock(self.file.as_raw_fd(), libc::LOCK_UN) };
        }
    }
}

fn settle_bridge_output(
    result: Result<CertificationOutcome, CertificationBridgeError>,
    lease: OutputLease,
) -> Result<CertificationOutcome, CertificationBridgeError> {
    let result = if matches!(result, Ok(CertificationOutcome::Certified(_))) {
        match std::fs::symlink_metadata(lease.stage()) {
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => return result,
            Ok(_) => Err(CertificationBridgeError::MalformedResponse(
                "certified response left its owned staging bundle behind".to_string(),
            )),
            Err(error) => Err(CertificationBridgeError::Cleanup(format!(
                "inspect certification staging bundle: {error}"
            ))),
        }
    } else {
        result
    };
    if let Err(cleanup) = rollback_bridge_output(&lease) {
        let original = match &result {
            Ok(CertificationOutcome::Failed(failure)) => {
                format!("certification failed: {}", failure.message)
            }
            Ok(CertificationOutcome::Rejected(rejection)) => {
                format!("certification rejected: {}", rejection.message)
            }
            Ok(CertificationOutcome::Certified(_)) => unreachable!(),
            Err(error) => error.to_string(),
        };
        return Err(CertificationBridgeError::Cleanup(format!(
            "{original}; rollback failed: {cleanup}"
        )));
    }
    result
}

fn rollback_bridge_output(lease: &OutputLease) -> Result<(), String> {
    remove_owned_output(&lease.solution, "unaccepted solution bundle")?;
    remove_owned_output(&lease.stage(), "certification staging bundle")?;
    Ok(())
}

fn remove_owned_output(path: &Path, label: &str) -> Result<(), String> {
    let metadata = match std::fs::symlink_metadata(path) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(()),
        Err(error) => return Err(format!("inspect {label}: {error}")),
    };
    if metadata.file_type().is_dir() {
        std::fs::remove_dir_all(path).map_err(|error| format!("remove {label}: {error}"))
    } else {
        std::fs::remove_file(path).map_err(|error| format!("remove {label}: {error}"))
    }
}

fn whole_positive_seconds(
    duration: Duration,
    label: &str,
) -> Result<u64, CertificationBridgeError> {
    if duration.is_zero() || duration.subsec_nanos() != 0 {
        return Err(CertificationBridgeError::InvalidRequest(format!(
            "{label} limit must be a positive whole number of seconds"
        )));
    }
    Ok(duration.as_secs())
}

fn optional_whole_positive_seconds(
    duration: Option<Duration>,
    label: &str,
) -> Result<Option<u64>, CertificationBridgeError> {
    duration
        .map(|value| whole_positive_seconds(value, label))
        .transpose()
}

fn positive(value: u64, label: &str) -> Result<u64, CertificationBridgeError> {
    if value == 0 {
        return Err(CertificationBridgeError::InvalidRequest(format!(
            "{label} must be positive"
        )));
    }
    Ok(value)
}

fn normalize_lexically(path: &Path) -> PathBuf {
    use std::path::Component;
    let mut normalized = PathBuf::new();
    for component in path.components() {
        match component {
            Component::CurDir => {}
            Component::ParentDir => {
                normalized.pop();
            }
            _ => normalized.push(component.as_os_str()),
        }
    }
    normalized
}

fn resolve_allow_missing(path: &Path) -> Result<PathBuf, CertificationBridgeError> {
    let normalized = normalize_lexically(path);
    let mut existing = normalized.as_path();
    let mut suffix = Vec::new();
    while !existing.exists() {
        let name = existing.file_name().ok_or_else(|| {
            CertificationBridgeError::InvalidRequest(
                "certification path has no existing ancestor".to_string(),
            )
        })?;
        suffix.push(name.to_os_string());
        existing = existing.parent().ok_or_else(|| {
            CertificationBridgeError::InvalidRequest(
                "certification path has no existing ancestor".to_string(),
            )
        })?;
    }
    let mut resolved = existing.canonicalize().map_err(|error| {
        CertificationBridgeError::InvalidRequest(format!(
            "resolve certification path ancestor: {error}"
        ))
    })?;
    for component in suffix.into_iter().rev() {
        resolved.push(component);
    }
    Ok(resolved)
}

fn valid_sha256(value: &str) -> bool {
    value.len() == 64 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

fn file_sha256(path: &Path) -> Result<String, CertificationBridgeError> {
    crate::entailment::assembly::hash_file_sha256(path).map_err(|error| {
        CertificationBridgeError::MalformedResponse(format!("hash published certificate: {error}"))
    })
}

fn bounded_string(mut value: String, maximum: usize) -> String {
    if value.len() <= maximum {
        return value;
    }
    let mut boundary = maximum;
    while !value.is_char_boundary(boundary) {
        boundary -= 1;
    }
    value.truncate(boundary);
    value.push('…');
    value
}

fn bounded_text(bytes: &[u8], maximum: usize) -> String {
    let start = bytes.len().saturating_sub(maximum);
    String::from_utf8_lossy(&bytes[start..]).into_owned()
}
