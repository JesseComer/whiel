//! Lean-owned fixed-ambient certificate emission and proof packaging.
//!
//! `emit_certificate` and `package_proof` are thin typed wrappers over the
//! `emit_certificate`/`package_proof` fixed-ambient worker operations
//! (`Whiel/Synthesis/FrameworkII/FixedAmbient/CertificateEmitter.lean`).
//! Rust never constructs or interprets certificate source; it only decodes
//! and structurally validates the JSON Lean returns.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::sync::Arc;

use serde::{Deserialize, Serialize};
use serde_json::{Value, json};

use crate::encoding::{EncodingError, FixedAmbientWorkerOperation, bytes_sha256};
use crate::failure::{FailureKind, FailureReport, FailureScope};
use crate::runtime::{CancellationToken, SolverAdmission};

use super::counterexample::FrozenCounterexampleRecord;
use super::snapshot::LeveledCandidateSnapshot;
use super::solver::FrameworkIISolverContext;

const CERTIFICATE_BUNDLE_KIND: &str = "whiel_fixed_ambient_certificate_bundle";
const CERTIFICATE_BUNDLE_VERSION: u64 = 2;
pub(super) const EMPTY_DOMAIN_ENCODING_VERSION: u64 = 1;

/// The declaration name an `Invalid` bundle's certificate theorem must end
/// with. Its type is the negated input triple.
const INVALID_CERTIFICATE_THEOREM: &str = "input_hoare_triple_invalid";

/// The module an `Invalid` bundle's certificate theorem must live in.
const INVALID_CERTIFICATE_MODULE_SUFFIX: &str = ".Certificate.Invalid";

/// Largest number of source files an `Invalid` bundle may carry. The shape
/// is one certificate module plus, at most, a small handful of supporting
/// modules; anything larger is not a counterexample certificate.
const MAX_INVALID_BUNDLE_ARTIFACTS: usize = 8;

/// Which target one decoded bundle certifies.
///
/// The two shapes are validated differently and never interchangeably: a
/// `Valid` bundle carries exactly the `2N+1` proof jobs of its frozen Core,
/// while an `Invalid` bundle carries no jobs at all and depends only on the
/// frozen counterexample instance and its frozen fuel.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CertificateBundleShape {
    Valid,
    Invalid,
}

// ------------------------------------------------------------
// Decoded Certificate Bundle
// ------------------------------------------------------------

/// One deterministic artifact staged by the Lean certificate emitter.
#[derive(Clone, Debug)]
pub struct CertificateArtifact {
    pub relative_path: String,
    pub contents: String,
}

/// Portable operational metadata for the exact job's empty-domain proof.
/// CNF meaning and the checked theorem are owned by Lean, not this transport.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CertificateEmptyCheck {
    pub encoding_version: u64,
    pub cnf_relative_path: String,
    pub cnf_sha256: String,
    pub lrat_relative_path: String,
    pub module_relative_path: String,
    pub module: String,
    pub theorem: String,
}

/// Operational handoff for one opaque leancheck problem.
///
/// The wire job object carries no `tptp` field of its own — Lean emits the
/// problem text only as the bundle artifact at `problem_relative_path`
/// (`CertificateEmitter.ProofJob.toJson`). Decoding cross-references that
/// artifact into `tptp` and verifies its digest against `problem_sha256`.
#[derive(Clone, Debug)]
pub struct CertificateJob {
    pub id: String,
    pub role: String,
    pub ordinal: u64,
    pub clause_id: Option<u64>,
    pub level: Option<u64>,
    pub selector_identity: Value,
    pub job_identity: Value,
    pub job_digest: String,
    pub problem_relative_path: String,
    pub problem_sha256: String,
    pub leancheck_output_relative_path: String,
    pub proof_module_relative_path: String,
    pub proof_module: String,
    pub proof_namespace: String,
    pub proof_theorem: String,
    pub reconstruction_module: String,
    pub empty_check: CertificateEmptyCheck,
}

/// Complete in-memory result of one `emit_certificate` request.
#[derive(Clone, Debug)]
pub struct CertificateBundle {
    pub input_identity: Value,
    pub scope_identity: Value,
    pub snapshot_identity: Value,
    pub input_source_sha256: String,
    pub core_size: u64,
    pub certificate_module: String,
    pub certificate_theorem: String,
    pub artifacts: Vec<CertificateArtifact>,
    pub jobs: Vec<CertificateJob>,
}

/// Complete in-memory result of one `package_proof` request.
#[derive(Clone, Debug)]
pub struct PackagedProof {
    pub job_id: String,
    pub proof_namespace: String,
    pub packaged: String,
    pub packaged_sha256: String,
}

// ------------------------------------------------------------
// Strict Worker Responses
// ------------------------------------------------------------

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WireCertificateBundle {
    kind: String,
    version: u64,
    input_identity: Value,
    scope_identity: Value,
    snapshot_identity: Value,
    input_source_sha256: String,
    core_size: u64,
    certificate_module: String,
    certificate_theorem: String,
    artifacts: Vec<WireCertificateArtifact>,
    jobs: Vec<WireCertificateJob>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WireCertificateArtifact {
    relative_path: String,
    contents_sha256: String,
    contents: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WireCertificateJob {
    id: String,
    role: String,
    ordinal: u64,
    clause_id: Option<u64>,
    level: Option<u64>,
    selector_identity: Value,
    job_identity: Value,
    job_digest: String,
    problem_relative_path: String,
    problem_sha256: String,
    leancheck_output_relative_path: String,
    proof_module_relative_path: String,
    proof_module: String,
    proof_namespace: String,
    proof_theorem: String,
    reconstruction_module: String,
    empty_check: CertificateEmptyCheck,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WirePackagedProof {
    job_id: String,
    proof_namespace: String,
    packaged: String,
    packaged_sha256: String,
}

fn decode_certificate_bundle(
    payload: Value,
    shape: CertificateBundleShape,
) -> Result<CertificateBundle, FrameworkIICertificateError> {
    let wire: WireCertificateBundle = decode_payload(payload, "fixed-ambient certificate bundle")?;
    if wire.kind != CERTIFICATE_BUNDLE_KIND || wire.version != CERTIFICATE_BUNDLE_VERSION {
        return Err(validation_failure(
            "fixed-ambient certificate bundle has a retired or unsupported kind/version",
        ));
    }
    match shape {
        CertificateBundleShape::Valid => {
            let Some(expected_job_count) = wire
                .core_size
                .checked_mul(2)
                .and_then(|doubled| doubled.checked_add(1))
            else {
                return Err(validation_failure(
                    "fixed-ambient certificate bundle core_size overflows the exact 2N+1 job count",
                ));
            };
            if wire.jobs.len() as u64 != expected_job_count {
                return Err(validation_failure(
                    "fixed-ambient certificate bundle does not carry the exact 2N+1 jobs",
                ));
            }
        }
        // An `Invalid` certificate is closed by a kernel decision over the
        // frozen instance and fuel, so it must reference no solver work at
        // all: no jobs, no Core, and no problem, raw-output, packaged-proof,
        // or reconstruction artifact.
        CertificateBundleShape::Invalid => {
            if !wire.jobs.is_empty() || wire.core_size != 0 {
                return Err(validation_failure(
                    "invalid-certificate bundle carries proof jobs or a nonempty Core",
                ));
            }
            if !wire
                .certificate_module
                .ends_with(INVALID_CERTIFICATE_MODULE_SUFFIX)
                || !wire
                    .certificate_theorem
                    .ends_with(INVALID_CERTIFICATE_THEOREM)
            {
                return Err(validation_failure(
                    "invalid-certificate bundle does not declare Certificate.Invalid's negated theorem",
                ));
            }
            if wire.artifacts.is_empty() || wire.artifacts.len() > MAX_INVALID_BUNDLE_ARTIFACTS {
                return Err(validation_failure(
                    "invalid-certificate bundle carries no file, or more files than its shape allows",
                ));
            }
            let mut has_invalid_module = false;
            for artifact in &wire.artifacts {
                if !artifact.relative_path.starts_with("Benchmark/")
                    || !artifact.relative_path.contains("/Certificate/")
                    || !artifact.relative_path.ends_with(".lean")
                {
                    return Err(validation_failure(
                        "invalid-certificate bundle stages a file outside its own certificate tree",
                    ));
                }
                for job_tree in [
                    "VampireArtifacts",
                    "VampireProofJobs",
                    "Reconstructions",
                    "EmptyCexCheck",
                ] {
                    if artifact.relative_path.contains(job_tree) {
                        return Err(validation_failure(
                            "invalid-certificate bundle references solver job artifacts",
                        ));
                    }
                }
                has_invalid_module |= artifact
                    .relative_path
                    .ends_with("/Certificate/Invalid.lean");
            }
            if !has_invalid_module {
                return Err(validation_failure(
                    "invalid-certificate bundle does not carry Certificate/Invalid.lean",
                ));
            }
        }
    }

    let mut artifacts_by_path: BTreeMap<String, String> = BTreeMap::new();
    for artifact in &wire.artifacts {
        if bytes_sha256(artifact.contents.as_bytes()) != artifact.contents_sha256 {
            return Err(validation_failure(
                "fixed-ambient certificate artifact digest disagrees with its contents",
            ));
        }
        if artifacts_by_path
            .insert(artifact.relative_path.clone(), artifact.contents.clone())
            .is_some()
        {
            return Err(validation_failure(
                "fixed-ambient certificate bundle repeats an artifact relative path",
            ));
        }
    }

    let mut jobs = Vec::with_capacity(wire.jobs.len());
    let mut empty_modules = BTreeSet::new();
    let mut empty_theorems = BTreeSet::new();
    let mut job_ids = BTreeSet::new();
    for job in wire.jobs {
        validate_empty_check(
            &job.empty_check,
            &job.id,
            &wire.certificate_module,
            &wire.certificate_theorem,
            &artifacts_by_path,
        )?;
        if !job_ids.insert(job.id.clone())
            || !empty_modules.insert(job.empty_check.module.clone())
            || !empty_theorems.insert(job.empty_check.theorem.clone())
        {
            return Err(validation_failure(
                "fixed-ambient certificate repeats an empty-check job, module or theorem",
            ));
        }
        let tptp = artifacts_by_path
            .get(&job.problem_relative_path)
            .ok_or_else(|| {
                validation_failure("fixed-ambient certificate job's problem artifact is missing")
            })?;
        if bytes_sha256(tptp.as_bytes()) != job.problem_sha256 {
            return Err(validation_failure(
                "fixed-ambient certificate job problem_sha256 disagrees with its problem artifact",
            ));
        }
        jobs.push(CertificateJob {
            id: job.id,
            role: job.role,
            ordinal: job.ordinal,
            clause_id: job.clause_id,
            level: job.level,
            selector_identity: job.selector_identity,
            job_identity: job.job_identity,
            job_digest: job.job_digest,
            problem_relative_path: job.problem_relative_path,
            problem_sha256: job.problem_sha256,
            leancheck_output_relative_path: job.leancheck_output_relative_path,
            proof_module_relative_path: job.proof_module_relative_path,
            proof_module: job.proof_module,
            proof_namespace: job.proof_namespace,
            proof_theorem: job.proof_theorem,
            reconstruction_module: job.reconstruction_module,
            empty_check: job.empty_check,
        });
    }

    Ok(CertificateBundle {
        input_identity: wire.input_identity,
        scope_identity: wire.scope_identity,
        snapshot_identity: wire.snapshot_identity,
        input_source_sha256: wire.input_source_sha256,
        core_size: wire.core_size,
        certificate_module: wire.certificate_module,
        certificate_theorem: wire.certificate_theorem,
        artifacts: wire
            .artifacts
            .into_iter()
            .map(|artifact| CertificateArtifact {
                relative_path: artifact.relative_path,
                contents: artifact.contents,
            })
            .collect(),
        jobs,
    })
}

fn valid_identifier(value: &str) -> bool {
    let mut bytes = value.bytes();
    bytes
        .next()
        .is_some_and(|b| b.is_ascii_alphabetic() || b == b'_')
        && bytes.all(|b| b.is_ascii_alphanumeric() || b == b'_')
}

fn validate_empty_check(
    check: &CertificateEmptyCheck,
    job_id: &str,
    certificate_module: &str,
    certificate_theorem: &str,
    artifacts: &BTreeMap<String, String>,
) -> Result<(), FrameworkIICertificateError> {
    let Some(module_prefix) = certificate_module.strip_suffix(".Valid") else {
        return Err(validation_failure(
            "empty check has no valid certificate module prefix",
        ));
    };
    let Some((namespace, _)) = certificate_theorem.rsplit_once('.') else {
        return Err(validation_failure(
            "empty check has no certificate theorem namespace",
        ));
    };
    let prefix = format!("{module_prefix}.EmptyCexCheck.");
    let Some(stem) = check.module.strip_prefix(&prefix) else {
        return Err(validation_failure("empty check names a foreign module"));
    };
    let Some(theorem) = check.theorem.strip_prefix(&format!("{namespace}.")) else {
        return Err(validation_failure("empty check names a foreign theorem"));
    };
    if check.encoding_version != EMPTY_DOMAIN_ENCODING_VERSION
        || !valid_identifier(job_id)
        || !valid_identifier(stem)
        || !valid_identifier(theorem)
        || !module_prefix.split('.').all(valid_identifier)
        || !namespace.split('.').all(valid_identifier)
    {
        return Err(validation_failure(
            "empty check has an unsupported encoding or unsafe identity",
        ));
    }
    let resources = format!(
        "{}/EmptyCexCheck/Resources/{job_id}",
        module_prefix.replace('.', "/")
    );
    if check.cnf_relative_path != format!("{resources}.cnf")
        || check.lrat_relative_path != format!("{resources}.lrat")
        || check.module_relative_path != format!("{}.lean", check.module.replace('.', "/"))
    {
        return Err(validation_failure(
            "empty check paths disagree with its job/module identity",
        ));
    }
    let Some(cnf) = artifacts.get(&check.cnf_relative_path) else {
        return Err(validation_failure("empty check CNF artifact is missing"));
    };
    if bytes_sha256(cnf.as_bytes()) != check.cnf_sha256 {
        return Err(validation_failure(
            "empty check CNF digest disagrees with its artifact",
        ));
    }
    if !artifacts.contains_key(&check.module_relative_path)
        || artifacts.contains_key(&check.lrat_relative_path)
    {
        return Err(validation_failure(
            "empty check module is missing or LRAT output is prepopulated",
        ));
    }
    Ok(())
}

/// The exact `emit_invalid_certificate` request payload of one frozen
/// record: Lean's own canonical instance passed back untouched, the fuel
/// that instance actually consumed, and the identity Lean issued for it.
/// Nothing else about the run reaches the emitter.
pub(super) fn invalid_certificate_payload(record: &FrozenCounterexampleRecord) -> Value {
    json!({
        "instance": record.instance(),
        "fuel": record.fuel_consumed(),
        "instance_identity": record.instance_identity(),
    })
}

fn decode_packaged_proof(
    payload: Value,
    job_id: &str,
    proof_namespace: &str,
) -> Result<PackagedProof, FrameworkIICertificateError> {
    let wire: WirePackagedProof = decode_payload(payload, "fixed-ambient packaged proof")?;
    if wire.job_id != job_id || wire.proof_namespace != proof_namespace {
        return Err(validation_failure(
            "fixed-ambient proof packaging echoed another job or namespace",
        ));
    }
    if bytes_sha256(wire.packaged.as_bytes()) != wire.packaged_sha256 {
        return Err(validation_failure(
            "fixed-ambient packaged proof digest disagrees with its contents",
        ));
    }
    Ok(PackagedProof {
        job_id: wire.job_id,
        proof_namespace: wire.proof_namespace,
        packaged: wire.packaged,
        packaged_sha256: wire.packaged_sha256,
    })
}

// ------------------------------------------------------------
// Worker Operations
// ------------------------------------------------------------

impl FrameworkIISolverContext {
    /// Emit the pure certificate plan for one frozen fixed-ambient Core.
    ///
    /// The snapshot must belong to this context's own task scope; the
    /// returned bundle's `kind`/`version` tag, exact `2N+1` job count, and
    /// every job's `problem_sha256` against its problem artifact are
    /// validated before this returns.
    pub async fn emit_certificate(
        &self,
        snapshot: &Arc<LeveledCandidateSnapshot>,
        admission: &SolverAdmission,
        cancellation: &CancellationToken,
    ) -> Result<CertificateBundle, FrameworkIICertificateError> {
        if snapshot.scope() != self.scope() {
            return Err(validation_failure(
                "fixed-ambient certificate emission received another task's snapshot",
            ));
        }
        let response = self
            .encoding()
            .execute(
                admission,
                cancellation,
                FixedAmbientWorkerOperation::EmitCertificate,
                json!({"snapshot": snapshot.worker_payload()}),
            )
            .await
            .map_err(FrameworkIICertificateError::from)?;
        decode_certificate_bundle(response.payload, CertificateBundleShape::Valid)
    }

    /// Emit the `Invalid` certificate for one frozen counterexample record.
    ///
    /// The payload carries only what the record froze: Lean's own canonical
    /// instance (opaque to Rust and passed back untouched), the fuel that
    /// instance actually consumed, and the instance identity Lean issued.
    /// The returned bundle is validated as an
    /// [`CertificateBundleShape::Invalid`] bundle: no jobs, no Core, and no
    /// solver artifacts.
    pub async fn emit_invalid_certificate(
        &self,
        record: &FrozenCounterexampleRecord,
        admission: &SolverAdmission,
        cancellation: &CancellationToken,
    ) -> Result<CertificateBundle, FrameworkIICertificateError> {
        if record.task_identity() != self.scope().task_identity()
            || record.scope_identity_sha256() != self.scope().identity_sha256()
        {
            return Err(validation_failure(
                "invalid-certificate emission received another task's counterexample record",
            ));
        }
        let response = self
            .encoding()
            .execute(
                admission,
                cancellation,
                FixedAmbientWorkerOperation::EmitInvalidCertificate,
                invalid_certificate_payload(record),
            )
            .await
            .map_err(FrameworkIICertificateError::from)?;
        decode_certificate_bundle(response.payload, CertificateBundleShape::Invalid)
    }

    /// Package one leancheck proof into its proof module.
    ///
    /// `job_id` and `proof_namespace` must match the values Lean echoes back;
    /// the packaged module's digest is verified before this returns.
    ///
    /// `extra_imports` is the allow-list a proof transformation asks for:
    /// the Whiel-owned modules whose tactics the rewritten text calls (see
    /// [`super::proof_transform`]). It is a *request*, not an authority —
    /// `packageProof` admits only the imports it pins itself, and refuses
    /// anything else, so a wrong or widened list fails the build closed
    /// rather than importing something unexpected into a certificate.
    pub async fn package_proof(
        &self,
        job_id: &str,
        proof_namespace: &str,
        proof_text: &[u8],
        extra_imports: &[String],
        admission: &SolverAdmission,
        cancellation: &CancellationToken,
    ) -> Result<PackagedProof, FrameworkIICertificateError> {
        let proof_text = std::str::from_utf8(proof_text).map_err(|_| {
            validation_failure("leancheck proof submitted for packaging is not valid UTF-8")
        })?;
        let response = self
            .encoding()
            .execute(
                admission,
                cancellation,
                FixedAmbientWorkerOperation::PackageProof,
                json!({
                    "extra_imports": extra_imports,
                    "job_id": job_id,
                    "proof_namespace": proof_namespace,
                    "raw_output": proof_text,
                }),
            )
            .await
            .map_err(FrameworkIICertificateError::from)?;
        decode_packaged_proof(response.payload, job_id, proof_namespace)
    }
}

// ------------------------------------------------------------
// Errors
// ------------------------------------------------------------

fn decode_payload<T: for<'de> Deserialize<'de>>(
    value: Value,
    label: &str,
) -> Result<T, FrameworkIICertificateError> {
    serde_json::from_value(value)
        .map_err(|error| validation_failure(format!("decode {label}: {error}")))
}

fn validation_failure(detail: impl Into<String>) -> FrameworkIICertificateError {
    FrameworkIICertificateError::Failure(FailureReport::encoding_preparation(
        FailureKind::MalformedResult,
        FailureScope::RunGlobal,
        detail,
    ))
}

#[derive(Clone, Debug)]
pub enum FrameworkIICertificateError {
    Cancelled,
    Failure(FailureReport),
}

impl FrameworkIICertificateError {
    pub fn failure(&self) -> Option<&FailureReport> {
        match self {
            Self::Cancelled => None,
            Self::Failure(report) => Some(report),
        }
    }
}

impl From<EncodingError> for FrameworkIICertificateError {
    fn from(error: EncodingError) -> Self {
        match error {
            EncodingError::Cancelled => Self::Cancelled,
            EncodingError::Failure(report) => Self::Failure(report),
        }
    }
}

impl fmt::Display for FrameworkIICertificateError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Cancelled => {
                formatter.write_str("fixed-ambient certificate operation was cancelled")
            }
            Self::Failure(report) => write!(
                formatter,
                "fixed-ambient certificate operation failed: origin={:?} kind={:?} detail={}",
                report.origin(),
                report.kind(),
                report.detail().unwrap_or("none")
            ),
        }
    }
}

impl std::error::Error for FrameworkIICertificateError {}

// ------------------------------------------------------------
// Tests
// ------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_job(problem_sha256: &str) -> Value {
        json!({
            "id": "candidate_init_clause_0",
            "role": "initialization",
            "ordinal": 0,
            "clause_id": 0,
            "level": 0,
            "selector_identity": {"kind": "initialization", "clause_id": 0},
            "job_identity": {"kind": "whiel_fixed_ambient_certificate_job"},
            "job_digest": "d".repeat(64),
            "problem_relative_path": "Benchmark/Example0001/Certificate/VampireArtifacts/jobs/candidate_init_clause_0/problem.p",
            "problem_sha256": problem_sha256,
            "leancheck_output_relative_path": "Benchmark/Example0001/Certificate/VampireArtifacts/jobs/candidate_init_clause_0/leancheck.lean",
            "proof_module_relative_path": "Benchmark/Example0001/Certificate/VampireProofJobs/InitClause0.lean",
            "proof_module": "Benchmark.Example0001.Certificate.VampireProofJobs.InitClause0",
            "proof_namespace": "Whiel.Benchmark.Example0001.Certificate.VampireProofs.InitClause0",
            "proof_theorem": "fullProof",
            "reconstruction_module": "Benchmark.Example0001.Certificate.Reconstructions.InitClause0",
            "empty_check": {
                "encoding_version": EMPTY_DOMAIN_ENCODING_VERSION,
                "cnf_relative_path": "Benchmark/Example0001/Certificate/EmptyCexCheck/Resources/candidate_init_clause_0.cnf",
                "cnf_sha256": bytes_sha256(b"p cnf 1 2\n1 0\n-1 0\n"),
                "lrat_relative_path": "Benchmark/Example0001/Certificate/EmptyCexCheck/Resources/candidate_init_clause_0.lrat",
                "module_relative_path": "Benchmark/Example0001/Certificate/EmptyCexCheck/InitClause0.lean",
                "module": "Benchmark.Example0001.Certificate.EmptyCexCheck.InitClause0",
                "theorem": "Whiel.Benchmark.Example0001.Certificate.initNoEmpty0",
            },
        })
    }

    fn sample_bundle(core_size: u64, jobs: Vec<Value>) -> Value {
        let tptp = "fof(dummy, axiom, $true).\n";
        let contents_sha256 = bytes_sha256(tptp.as_bytes());
        json!({
            "kind": CERTIFICATE_BUNDLE_KIND,
            "version": CERTIFICATE_BUNDLE_VERSION,
            "input_identity": {"kind": "whiel_fixed_ambient_certificate_input"},
            "scope_identity": {"kind": "fixed"},
            "snapshot_identity": {"kind": "whiel_fixed_ambient_snapshot"},
            "input_source_sha256": "a".repeat(64),
            "core_size": core_size,
            "certificate_module": "Benchmark.Example0001.Certificate.Valid",
            "certificate_theorem": "Whiel.Benchmark.Example0001.Certificate.input_hoare_triple_valid",
            "artifacts": [
                {
                    "relative_path": "Benchmark/Example0001/Certificate/VampireArtifacts/jobs/candidate_init_clause_0/problem.p",
                    "contents_sha256": contents_sha256,
                    "contents": tptp,
                },
                {
                    "relative_path": "Benchmark/Example0001/Certificate/EmptyCexCheck/Resources/candidate_init_clause_0.cnf",
                    "contents_sha256": bytes_sha256(b"p cnf 1 2\n1 0\n-1 0\n"),
                    "contents": "p cnf 1 2\n1 0\n-1 0\n",
                },
                {
                    "relative_path": "Benchmark/Example0001/Certificate/EmptyCexCheck/InitClause0.lean",
                    "contents_sha256": bytes_sha256(b"-- empty proof module\n"),
                    "contents": "-- empty proof module\n",
                }
            ],
            "jobs": jobs,
        })
    }

    #[test]
    fn decodes_a_well_formed_bundle_and_cross_references_tptp() {
        let tptp = "fof(dummy, axiom, $true).\n";
        let problem_sha256 = bytes_sha256(tptp.as_bytes());
        // core_size 0 requires exactly one (2*0+1) job.
        let bundle = sample_bundle(0, vec![sample_job(&problem_sha256)]);
        let decoded = decode_certificate_bundle(bundle, CertificateBundleShape::Valid).unwrap();
        assert_eq!(decoded.jobs.len(), 1);
        assert_eq!(decoded.jobs[0].problem_sha256, problem_sha256);
    }

    #[test]
    fn rejects_a_retired_kind_or_version() {
        let tptp = "fof(dummy, axiom, $true).\n";
        let problem_sha256 = bytes_sha256(tptp.as_bytes());
        let mut bundle = sample_bundle(0, vec![sample_job(&problem_sha256)]);
        bundle["kind"] = json!("whiel_legacy_certificate_bundle");
        assert!(decode_certificate_bundle(bundle, CertificateBundleShape::Valid).is_err());

        let mut bundle = sample_bundle(0, vec![sample_job(&problem_sha256)]);
        bundle["version"] = json!(1);
        assert!(decode_certificate_bundle(bundle, CertificateBundleShape::Valid).is_err());
    }

    #[test]
    fn rejects_a_job_count_that_is_not_exactly_2n_plus_1() {
        let tptp = "fof(dummy, axiom, $true).\n";
        let problem_sha256 = bytes_sha256(tptp.as_bytes());
        let bundle = sample_bundle(1, vec![sample_job(&problem_sha256)]);
        assert!(decode_certificate_bundle(bundle, CertificateBundleShape::Valid).is_err());
    }

    #[test]
    fn rejects_a_job_whose_problem_sha256_disagrees_with_its_artifact() {
        let tptp = "fof(dummy, axiom, $true).\n";
        let problem_sha256 = bytes_sha256(tptp.as_bytes());
        let mut bundle = sample_bundle(0, vec![sample_job(&problem_sha256)]);
        bundle["jobs"][0]["problem_sha256"] = json!("f".repeat(64));
        assert!(decode_certificate_bundle(bundle, CertificateBundleShape::Valid).is_err());
    }

    #[test]
    fn rejects_an_artifact_whose_digest_disagrees_with_its_contents() {
        let tptp = "fof(dummy, axiom, $true).\n";
        let problem_sha256 = bytes_sha256(tptp.as_bytes());
        let mut bundle = sample_bundle(0, vec![sample_job(&problem_sha256)]);
        bundle["artifacts"][0]["contents_sha256"] = json!("f".repeat(64));
        assert!(decode_certificate_bundle(bundle, CertificateBundleShape::Valid).is_err());
    }

    #[test]
    fn rejects_an_unknown_field_anywhere_in_the_bundle() {
        let tptp = "fof(dummy, axiom, $true).\n";
        let problem_sha256 = bytes_sha256(tptp.as_bytes());
        let mut bundle = sample_bundle(0, vec![sample_job(&problem_sha256)]);
        bundle["unexpected"] = json!(true);
        assert!(decode_certificate_bundle(bundle, CertificateBundleShape::Valid).is_err());
    }

    #[test]
    fn empty_checks_require_exact_resources_and_strict_metadata() {
        let tptp = "fof(dummy, axiom, $true).\n";
        let base = sample_bundle(0, vec![sample_job(&bytes_sha256(tptp.as_bytes()))]);
        for (field, value) in [
            ("encoding_version", json!(2)),
            ("cnf_sha256", json!("0".repeat(64))),
            ("cnf_relative_path", json!("../foreign.cnf")),
            (
                "lrat_relative_path",
                json!("Benchmark/Example0001/Certificate/VampireArtifacts/proof.lrat"),
            ),
            (
                "module",
                json!("Benchmark.Example0002.Certificate.EmptyCexCheck.InitClause0"),
            ),
            (
                "module_relative_path",
                json!("Benchmark/Example0001/Certificate/EmptyCexCheck/Other.lean"),
            ),
            (
                "theorem",
                json!("Whiel.Benchmark.Example0002.Certificate.initNoEmpty0"),
            ),
            ("extra", json!(true)),
        ] {
            let mut bundle = base.clone();
            bundle["jobs"][0]["empty_check"][field] = value;
            assert!(
                decode_certificate_bundle(bundle, CertificateBundleShape::Valid).is_err(),
                "{field}"
            );
        }
        for field in [
            "encoding_version",
            "cnf_relative_path",
            "cnf_sha256",
            "lrat_relative_path",
            "module_relative_path",
            "module",
            "theorem",
        ] {
            let mut bundle = base.clone();
            bundle["jobs"][0]["empty_check"]
                .as_object_mut()
                .unwrap()
                .remove(field);
            assert!(
                decode_certificate_bundle(bundle, CertificateBundleShape::Valid).is_err(),
                "{field}"
            );
        }
        for index in [1, 2] {
            let mut bundle = base.clone();
            bundle["artifacts"].as_array_mut().unwrap().remove(index);
            assert!(decode_certificate_bundle(bundle, CertificateBundleShape::Valid).is_err());
        }
        let mut bundle = base;
        let lrat = bundle["jobs"][0]["empty_check"]["lrat_relative_path"].clone();
        bundle["artifacts"].as_array_mut().unwrap().push(json!({
            "relative_path": lrat, "contents_sha256": bytes_sha256(b""), "contents": ""
        }));
        assert!(decode_certificate_bundle(bundle, CertificateBundleShape::Valid).is_err());
    }

    #[test]
    fn decodes_a_matching_packaged_proof() {
        let packaged = "import VampLean\nopen VampLean\nnamespace foo\ntheorem fullProof := trivial\nend foo\n";
        let packaged_sha256 = bytes_sha256(packaged.as_bytes());
        let payload = json!({
            "job_id": "candidate_init_clause_0",
            "proof_namespace": "foo",
            "packaged": packaged,
            "packaged_sha256": packaged_sha256,
        });
        let decoded = decode_packaged_proof(payload, "candidate_init_clause_0", "foo").unwrap();
        assert_eq!(decoded.packaged, packaged);
    }

    #[test]
    fn rejects_a_packaged_proof_that_echoes_another_job_or_namespace() {
        let packaged = "import VampLean\n";
        let packaged_sha256 = bytes_sha256(packaged.as_bytes());
        let payload = json!({
            "job_id": "other_job",
            "proof_namespace": "foo",
            "packaged": packaged,
            "packaged_sha256": packaged_sha256,
        });
        assert!(decode_packaged_proof(payload, "candidate_init_clause_0", "foo").is_err());
    }

    #[test]
    fn rejects_a_packaged_proof_whose_digest_disagrees_with_its_contents() {
        let packaged = "import VampLean\n";
        let payload = json!({
            "job_id": "candidate_init_clause_0",
            "proof_namespace": "foo",
            "packaged": packaged,
            "packaged_sha256": "f".repeat(64),
        });
        assert!(decode_packaged_proof(payload, "candidate_init_clause_0", "foo").is_err());
    }

    fn sample_invalid_bundle() -> Value {
        let source = "import Benchmark.Example0002.Input\ntheorem input_hoare_triple_invalid : True := trivial\n";
        json!({
            "kind": CERTIFICATE_BUNDLE_KIND,
            "version": CERTIFICATE_BUNDLE_VERSION,
            "input_identity": {"kind": "whiel_fixed_ambient_certificate_input"},
            "scope_identity": {"kind": "fixed"},
            "snapshot_identity": {"kind": "whiel_fixed_ambient_counterexample"},
            "input_source_sha256": "a".repeat(64),
            "core_size": 0,
            "certificate_module": "Benchmark.Example0002.Certificate.Invalid",
            "certificate_theorem": "Whiel.Benchmark.Example0002.Certificate.input_hoare_triple_invalid",
            "artifacts": [
                {
                    "relative_path": "Benchmark/Example0002/Certificate/Invalid.lean",
                    "contents_sha256": bytes_sha256(source.as_bytes()),
                    "contents": source,
                }
            ],
            "jobs": [],
        })
    }

    #[test]
    fn decodes_a_zero_job_invalid_bundle() {
        let decoded =
            decode_certificate_bundle(sample_invalid_bundle(), CertificateBundleShape::Invalid)
                .unwrap();
        assert!(decoded.jobs.is_empty());
        assert_eq!(decoded.core_size, 0);
        assert_eq!(decoded.artifacts.len(), 1);
        assert_eq!(
            decoded.artifacts[0].relative_path,
            "Benchmark/Example0002/Certificate/Invalid.lean"
        );
        assert!(
            decoded
                .certificate_theorem
                .ends_with("input_hoare_triple_invalid")
        );
    }

    /// The zero-job relaxation belongs to the `Invalid` shape alone: a
    /// `Valid` bundle still has to carry exactly `2N+1` jobs, and an
    /// `Invalid` bundle may carry none at all.
    #[test]
    fn the_two_shapes_never_accept_each_other() {
        assert!(
            decode_certificate_bundle(sample_invalid_bundle(), CertificateBundleShape::Valid)
                .is_err()
        );
        let tptp = "fof(dummy, axiom, $true).\n";
        let problem_sha256 = bytes_sha256(tptp.as_bytes());
        let valid = sample_bundle(0, vec![sample_job(&problem_sha256)]);
        assert!(decode_certificate_bundle(valid, CertificateBundleShape::Invalid).is_err());
    }

    /// The emitted certificate may depend only on the frozen instance and
    /// fuel, so no solver job artifact and no foreign file may ride along.
    #[test]
    fn an_invalid_bundle_may_not_reference_job_artifacts_or_foreign_files() {
        let extra_artifact = |relative_path: &str| {
            let mut bundle = sample_invalid_bundle();
            let contents = "-- staged\n";
            bundle["artifacts"].as_array_mut().unwrap().push(json!({
                "relative_path": relative_path,
                "contents_sha256": bytes_sha256(contents.as_bytes()),
                "contents": contents,
            }));
            bundle
        };
        for relative_path in [
            "Benchmark/Example0002/Certificate/VampireArtifacts/jobs/j/problem.p",
            "Benchmark/Example0002/Certificate/VampireProofJobs/InitClause0.lean",
            "Benchmark/Example0002/Certificate/Reconstructions/InitClause0.lean",
            "Benchmark/Example0002/Certificate/EmptyCexCheck/InitClause0.lean",
            "Whiel/Elsewhere.lean",
            "Benchmark/Example0002/Certificate/notes.txt",
        ] {
            assert!(
                decode_certificate_bundle(
                    extra_artifact(relative_path),
                    CertificateBundleShape::Invalid
                )
                .is_err(),
                "an invalid bundle must not stage {relative_path}"
            );
        }

        let mut jobbed = sample_invalid_bundle();
        let tptp = "fof(dummy, axiom, $true).\n";
        jobbed["jobs"] = json!([sample_job(&bytes_sha256(tptp.as_bytes()))]);
        assert!(decode_certificate_bundle(jobbed, CertificateBundleShape::Invalid).is_err());

        let mut renamed = sample_invalid_bundle();
        renamed["certificate_theorem"] =
            json!("Whiel.Benchmark.Example0002.Certificate.input_hoare_triple_valid");
        assert!(decode_certificate_bundle(renamed, CertificateBundleShape::Invalid).is_err());

        let mut without_module = sample_invalid_bundle();
        without_module["artifacts"][0]["relative_path"] =
            json!("Benchmark/Example0002/Certificate/Support.lean");
        assert!(
            decode_certificate_bundle(without_module, CertificateBundleShape::Invalid).is_err()
        );
    }
}
