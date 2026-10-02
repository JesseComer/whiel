//! `certificate build` command: durable fixed-ambient certificate
//! construction from a frozen, checked-in record.
//!
//! This module never runs a leveled Houdini search. It has three modes,
//! one per kind of frozen record, and exactly one may be named:
//!
//! - `--core ROWS.json` rebuilds a `Valid` tree. A Core rows file records
//!   the exact level already assigned to each clause by an earlier search;
//!   every `Valid` build, a campaign's or this command's, writes one as
//!   `Core.json` beside the tree it publishes (see
//!   `Benchmark/Example0001/Core.json`); this mode re-admits those
//!   exact sources, places them at their recorded levels directly (no
//!   stabilization), and reproves every certificate job with the pinned
//!   `leancheck` Vampire via [`build_certificate`].
//!
//!   This is the one path that publishes without a separate revalidation
//!   receipt, and it is sound for the reason revalidation exists: the rule
//!   is that no source authorizes a result until it has been *freshly*
//!   checked, and `build_certificate` does that check itself, in this
//!   process, on this tree. It stages every module from the bundle Lean
//!   just emitted, compiles each one from source into its own throwaway
//!   `olean` overlay, elaborates a generated `Check.lean` at the exact
//!   immutable `Input.lean` declaration type, and audits the theorem's
//!   axiom closure to exactly std3 — the same four steps
//!   [`revalidate_certificate_tree`] performs — before the tree is promoted
//!   at all. Revalidating the promoted tree again would re-run the identical
//!   checks over identical bytes. What revalidation adds is a *second*
//!   opinion on a tree this process did not just check: Pass 7.5f's private
//!   candidate, a tree left over from an earlier stage, or a tree already
//!   checked in. `--counterexample` and `--witness` do go through it,
//!   because [`publish_invalid_in_phase`] publishes trees in exactly that
//!   class.
//!
//!   [`revalidate_certificate_tree`]: crate::framework2::revalidate_certificate_tree
//! - `--counterexample RECORD.json` rebuilds an `Invalid` tree the same
//!   way, from the durable record Pass 7.5g's `Invalid` publication writes
//!   beside the input (`Counterexample.json`). Lean re-decodes the
//!   canonical instance and re-checks that its frozen fuel still refutes
//!   the immutable input triple before the zero-job bundle is emitted, and
//!   the built tree is revalidated — a fresh Lean build, the exact negated
//!   input-triple type, an exact-std3 audit — before it is published.
//! - `--witness WITNESS.json` validates one already recorded witness
//!   through Lean's own `validate_counterexample`, freezes the durable
//!   record it answers with, and then takes exactly the
//!   `--counterexample` path over that record. This is how a corpus task
//!   whose witness was recorded in its metadata gets its first
//!   `Counterexample.json` and `Certificate/Invalid.lean`.
//!
//! It never launches any scripting interpreter or the legacy certification
//! bridge; the only external processes it starts are `lake` (to build the
//! fixed-ambient encoding worker and the Lean modules imported by generated
//! certificates), that worker itself, and — inside [`build_certificate`] and
//! the revalidation — `lean` and the pinned leancheck Vampire.

use std::collections::BTreeMap;
use std::io::Write;
use std::num::NonZeroUsize;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Duration;

use serde::Deserialize;
use serde_json::{Value, json};

use crate::encoding::{FixedAmbientWorkerCommand, FixedAmbientWorkerPoolConfig};
#[cfg(feature = "test-hooks")]
use crate::framework2::CertificateBuildHooks;
use crate::framework2::CertificateBundleShape;
use crate::framework2::{
    AgentToolPolicy, CertificateBuildError, CertificateBuildReceipt, CertificateBuildRequest,
    CertificateJob, CoreFreezeError, CounterexampleFuelPolicy, CounterexampleProvenance,
    DurableCounterexampleRecord, ExtendedClauseOrigin, FrameworkIIAdmissionContext,
    FrameworkIILevel, FrameworkIISolverContext, HostLimits, LeancheckProfile,
    LeveledCandidateSnapshot, LeveledHoudiniState, PinnedLeancheckVampire,
    PreCertificateAgentHoudiniLimits, ProofSearchProfile, ProofTransformRecord,
    PublishInvalidRequest, PublishedInvalid, RecordedWitnessValidation,
    bind_fixed_ambient_framework_ii, build_certificate, publish_invalid_in_phase,
    validate_recorded_witness,
};
use crate::framework2::{CORE_RECORD_NAME, CORE_ROWS_KIND, CORE_ROWS_VERSION};
use crate::houdini::ClauseId;
use crate::runtime::phase::{PhaseCancellation, PhaseStop};
use crate::runtime::{CancellationToken, RuntimeResourcePolicy, SolverAdmission};
use crate::task::TaskIdentity;
use crate::{AdmissionOutcome, create_general_solver_admission};

const RECEIPT_KIND: &str = "whiel_certificate_build_receipt";
/// 1 -> 2 in Pass 7.5g: the receipt names the certificate shape and, for
/// an `Invalid` build, the durable record it was rebuilt from and the
/// revalidation that authorized it; `requested_profile` is null for a shape
/// that runs no solver, and `destination` names the published tree rather
/// than the build's own intermediate one. A reader pinned to v1 fails
/// closed on the version rather than reading a null profile as `direct`.
///
/// 2 -> 3 in Pass 7.9a: every job row records the deterministic proof
/// transformations that ran between the solver and the packaging —
/// `canonical_sha256`, `transformed_sha256`, and the ordered `transforms`
/// list of `{id, version, outcome, input_sha256, output_sha256, detail}`.
/// `raw_sha256` keeps its meaning: the verbatim solver stdout, which is
/// still what is staged under `VampireArtifacts/`.
///
/// 3 -> 4 in Pass 7.9b: `raw_sha256` still names the verbatim solver
/// stdout, but that text is no longer stored anywhere — it carries the
/// four volatile solver comment lines — and `canonical_sha256` now names
/// the file staged under `VampireArtifacts/jobs/<job>/leancheck.lean`.
/// What those lines measured moves into the new per-job `timing` object,
/// and into the certificate's own `timing.csv` (at the tree's own root
/// since certificate slimming Milestone A; `VampireArtifacts/` itself is
/// evidence, moved out of the published tree or dropped before that
/// milestone's build promotes it). A reader pinned to v3 fails closed
/// rather than reading `raw_sha256` as the digest of a published file.
const RECEIPT_VERSION: u64 = 4;
const DEFAULT_TIME_LIMIT_SECONDS: u64 = 60;
const WORKER_TARGET: &str = "fixed_ambient_encoding_worker";
const WORKER_RELATIVE_PATH: &str = ".lake/build/bin/fixed_ambient_encoding_worker";
// Certificate modules are compiled with `lean` directly, outside Lake's
// dependency scheduler. Prepare every repository module they may import
// before constructing the private certificate overlay.
const CERTIFICATE_PREREQUISITE_TARGETS: [&str; 6] = [
    "VampLean",
    "Mathlib.Tactic.Linter.UnusedTactic",
    "Mathlib.Tactic.Sat.FromLRAT",
    "Whiel.Vampire.ClauseProjection",
    "Whiel.Vampire.EmptyDomainLRAT",
    "Whiel.Synthesis.FrameworkII.FixedAmbient.CertifyJob",
];

pub const CERTIFICATE_USAGE: &str = "\
Usage:
  whiel-symbolic certificate build --input CANONICAL_ID --destination DIR (--core ROWS.json |
                                   --counterexample RECORD.json | --witness WITNESS.json) [OPTIONS]

Exactly one frozen record selects the mode:
  --core PATH                Frozen Core rows file (whiel_framework_ii_core_rows v1 JSON); builds
                               Certificate/Valid.lean
  --counterexample PATH      Durable counterexample record (whiel_framework_ii_counterexample v1
                               JSON, normally Counterexample.json beside the input); rebuilds
                               Certificate/Invalid.lean from it
  --witness PATH             One recorded witness instance in the agent's own proposal shape
                               ({\"relations\": [{\"name\": ..., \"rows\": [[...]]}]}); Lean validates
                               it, this command freezes the durable record beside the input, and
                               then builds Certificate/Invalid.lean from that record
  --witness-source TEXT      Where that witness was recorded, written into the durable record's
                               provenance (default: the --witness path); --witness only
  --validation-limit-seconds N
                             Call-local wall-clock limit enforced on the Lean validate_counterexample
                               call, and the fuel policy the durable record then states (default: the
                               run authority's own DEFAULT_COUNTEREXAMPLE_VALIDATION_LIMIT, 30s);
                               --witness only. Its expiry is a `timeout` rejection of the call, never
                               a verdict on the instance.

Options:
  --input ID                 Canonical benchmark id (must match the worker's own describe identity)
  --destination DIR          Where the finished Certificate/ tree is written (must not exist)
  --repo PATH                Repository root (default: current directory)
  --staging DIR               Private staging parent directory
                               (default: a fresh sibling of DESTINATION, so the final promotion
                               stays on its filesystem)
  --profile direct|casc_2025 Leancheck profile forced on every job (default: direct); --core only,
                              since an Invalid certificate is closed by a kernel decision and runs
                              no solver at all. This is for regenerating one certificate under a
                              fixed profile. A live campaign build instead selects each job's
                              profile from the search-phase winner recorded per row, from the
                              frozen Core record's own profile labels.
  --time-limit-seconds N     Per-job leancheck Vampire deadline (default: 60); --core only
  --evidence DIR             Where the staged solver-evidence subtree (per-job problem.p and
                               normalized leancheck.lean) is moved once the build succeeds; must not
                               already exist. Absent: the evidence is dropped, and the published tree
                               never carries it either way. --core only, since an Invalid certificate
                               runs no solver and has no evidence to keep.
  --worker PATH               Fixed-ambient worker executable (default: Lake builds and locates it;
                               certificate Lean prerequisites are prepared in either case)
  --receipt PATH              Where the JSON build receipt is written
                               (default: <destination's parent>/<CANONICAL_ID>.certificate-receipt.json)
  -h, --help                  Print this help

In --counterexample and --witness mode the durable record is written to (or, when it is already
there and identical, read from) Counterexample.json in the destination's parent directory, which is
the benchmark directory holding the immutable Input.lean.

Exit codes:
  0  the certificate build succeeded
  2  a `certificate build` argument, bootstrap, or lock-resolution failure (this subcommand's own
     code for that class of failure; unrelated to the `task`/`suite` grammar's own exit code 2,
     which instead reports an otherwise-successful run that left work incomplete)
  3  the certificate build itself failed after bootstrapping (see `CertificateBuildError`)
";

// ------------------------------------------------------------
// Configuration And Parsing
// ------------------------------------------------------------

/// Which frozen record this build is driven by, and therefore which
/// certificate shape it produces.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CertificateSource {
    /// A frozen Core rows file: build `Certificate/Valid.lean`.
    Core(PathBuf),
    /// A durable counterexample record: build `Certificate/Invalid.lean`.
    Counterexample(PathBuf),
    /// A recorded witness instance: validate it through Lean, freeze the
    /// durable record, then build `Certificate/Invalid.lean` from it.
    /// The second component names where the witness was recorded, for the
    /// record's own provenance.
    Witness(PathBuf, String),
}

#[derive(Clone, Debug)]
pub struct CertificateBuildConfig {
    pub input: String,
    pub source: CertificateSource,
    pub destination: PathBuf,
    pub repository: PathBuf,
    pub staging: Option<PathBuf>,
    pub profile: ProofSearchProfile,
    pub time_limit_seconds: u64,
    /// Where the staged solver-evidence subtree is moved once the build
    /// succeeds; `None` drops it. `--core` only. See
    /// [`crate::framework2::CertificateBuildRequest::evidence_destination`].
    pub evidence: Option<PathBuf>,
    /// The call-local limit `--witness` mode enforces on Lean's
    /// `validate_counterexample` call, and therefore the fuel policy the
    /// durable record states. Defaults to the run authority's own
    /// [`crate::framework2::DEFAULT_COUNTEREXAMPLE_VALIDATION_LIMIT`], so an
    /// invocation that names nothing runs under the limit the search itself
    /// applies.
    pub validation_limit: Duration,
    pub worker: Option<PathBuf>,
    pub receipt: Option<PathBuf>,
}

pub fn parse_certificate_build_arguments(
    arguments: &[String],
) -> Result<CertificateBuildConfig, String> {
    let mut input = None;
    let mut core = None;
    let mut counterexample = None;
    let mut witness = None;
    let mut witness_source = None;
    let mut profile_named = false;
    let mut time_limit_named = false;
    let mut evidence = None;
    let mut validation_limit = None;
    let mut destination = None;
    let mut repository = PathBuf::from(".");
    let mut staging = None;
    let mut profile = ProofSearchProfile::Direct;
    let mut time_limit_seconds = DEFAULT_TIME_LIMIT_SECONDS;
    let mut worker = None;
    let mut receipt = None;

    let mut index = 0;
    while index < arguments.len() {
        let option = arguments[index].as_str();
        match option {
            "--input" => {
                input = Some(crate::cli::take_value(arguments, &mut index, option)?.to_string())
            }
            "--core" => {
                core = Some(PathBuf::from(crate::cli::take_value(
                    arguments, &mut index, option,
                )?))
            }
            "--counterexample" => {
                counterexample = Some(PathBuf::from(crate::cli::take_value(
                    arguments, &mut index, option,
                )?))
            }
            "--witness" => {
                witness = Some(PathBuf::from(crate::cli::take_value(
                    arguments, &mut index, option,
                )?))
            }
            "--witness-source" => {
                witness_source =
                    Some(crate::cli::take_value(arguments, &mut index, option)?.to_string())
            }
            "--destination" => {
                destination = Some(PathBuf::from(crate::cli::take_value(
                    arguments, &mut index, option,
                )?))
            }
            "--repo" => {
                repository = PathBuf::from(crate::cli::take_value(arguments, &mut index, option)?)
            }
            "--staging" => {
                staging = Some(PathBuf::from(crate::cli::take_value(
                    arguments, &mut index, option,
                )?))
            }
            "--profile" => {
                profile_named = true;
                profile = match crate::cli::take_value(arguments, &mut index, option)? {
                    "direct" => ProofSearchProfile::Direct,
                    "casc_2025" => ProofSearchProfile::Casc2025,
                    other => return Err(format!("unknown --profile {other:?}")),
                }
            }
            "--validation-limit-seconds" => {
                let value = crate::cli::take_value(arguments, &mut index, option)?;
                // Any positive whole number of seconds. The value is a
                // guard on one replay, not work the command performs, so
                // there is no upper cap for it to sit under: a host that
                // states a very long guard has said only that it does not
                // want the replay stopped (Milestone 7.5 review, finding
                // 10).
                let seconds = value
                    .parse::<u64>()
                    .ok()
                    .filter(|seconds| *seconds > 0)
                    .ok_or_else(|| {
                        format!("{option} requires a positive whole number of seconds")
                    })?;
                validation_limit = Some(Duration::from_secs(seconds));
            }
            "--time-limit-seconds" => {
                time_limit_named = true;
                let value = crate::cli::take_value(arguments, &mut index, option)?;
                time_limit_seconds = value
                    .parse::<u64>()
                    .ok()
                    .filter(|seconds| *seconds > 0)
                    .ok_or_else(|| {
                        format!("{option} requires a positive whole number of seconds")
                    })?;
            }
            "--evidence" => {
                evidence = Some(PathBuf::from(crate::cli::take_value(
                    arguments, &mut index, option,
                )?))
            }
            "--worker" => {
                worker = Some(PathBuf::from(crate::cli::take_value(
                    arguments, &mut index, option,
                )?))
            }
            "--receipt" => {
                receipt = Some(PathBuf::from(crate::cli::take_value(
                    arguments, &mut index, option,
                )?))
            }
            other => return Err(format!("unknown option {other:?}")),
        }
        index += 1;
    }

    let named: Vec<CertificateSource> = [
        core.map(CertificateSource::Core),
        counterexample.map(CertificateSource::Counterexample),
        witness.map(|path| {
            let source = witness_source
                .clone()
                .unwrap_or_else(|| path.display().to_string());
            CertificateSource::Witness(path, source)
        }),
    ]
    .into_iter()
    .flatten()
    .collect();
    let source = match named.len() {
        0 => return Err("one of --core, --counterexample, or --witness is required".to_string()),
        1 => named.into_iter().next().expect("exactly one source"),
        _ => {
            return Err(
                "--core, --counterexample, and --witness select the mode and are mutually \
                 exclusive"
                    .to_string(),
            );
        }
    };
    // The solver options belong to the `Valid` batch alone: an `Invalid`
    // certificate is closed by a kernel decision over the frozen instance
    // and runs no solver at all, so silently accepting them there would
    // state a profile and a deadline that nothing applies.
    if witness_source.is_some() && !matches!(source, CertificateSource::Witness(_, _)) {
        return Err("--witness-source applies to --witness only".to_string());
    }
    // The validation limit is applied to exactly one thing: the Lean
    // `validate_counterexample` call `--witness` mode makes. Naming it in a
    // mode that makes no such call would state a limit nothing enforces,
    // which is the defect this option exists to fix.
    if validation_limit.is_some() && !matches!(source, CertificateSource::Witness(_, _)) {
        return Err("--validation-limit-seconds applies to --witness only".to_string());
    }
    if !matches!(source, CertificateSource::Core(_)) && (profile_named || time_limit_named) {
        return Err(
            "--profile and --time-limit-seconds apply to --core only; an Invalid certificate \
             runs no solver"
                .to_string(),
        );
    }
    // An Invalid certificate never had evidence to keep: it runs no solver
    // at all, so naming a destination for it would promise something this
    // mode cannot produce.
    if evidence.is_some() && !matches!(source, CertificateSource::Core(_)) {
        return Err(
            "--evidence applies to --core only; an Invalid certificate runs no solver and has \
             no evidence"
                .to_string(),
        );
    }

    Ok(CertificateBuildConfig {
        input: input.ok_or_else(|| "--input is required".to_string())?,
        source,
        destination: destination.ok_or_else(|| "--destination is required".to_string())?,
        repository,
        staging,
        profile,
        time_limit_seconds,
        evidence,
        validation_limit: validation_limit
            .unwrap_or(crate::framework2::DEFAULT_COUNTEREXAMPLE_VALIDATION_LIMIT),
        worker,
        receipt,
    })
}

// ------------------------------------------------------------
// Core Rows File
// ------------------------------------------------------------

#[derive(Deserialize)]
struct CoreRowsFile {
    kind: String,
    version: u64,
    rows: Vec<CoreRow>,
}

#[derive(Deserialize, Clone)]
pub(crate) struct CoreRow {
    level: u64,
    source: String,
}

/// Which leancheck profile each job of a rebuild runs under.
///
/// A rebuild from a record has to reproduce the labels the run's own freeze
/// closed over, because a condition the portfolio proved is not in general
/// reachable by the direct strategy within a certificate job's allowance.
#[derive(Clone, Debug)]
pub(crate) enum RecordJobProfiles {
    /// One profile for every job, as `certificate build --profile` names.
    Constant(ProofSearchProfile),
    /// The labels the frozen Core recorded, keyed by canonical source: a
    /// rebuild re-admits the clauses and Lean issues fresh ids for them, so
    /// the source is the only thing the record and the rebuild agree on.
    Recorded(RecordedCoreProfiles),
}

/// The per-job profile labels one frozen Core payload carries.
#[derive(Clone, Debug)]
pub(crate) struct RecordedCoreProfiles {
    by_source: BTreeMap<String, (ProofSearchProfile, ProofSearchProfile)>,
    termination: ProofSearchProfile,
}

impl RecordedCoreProfiles {
    /// Read the labels out of a frozen Core payload, as the acceptance
    /// envelope carries it. A payload whose rows or labels cannot be read
    /// is refused: certifying under a guessed profile is what this exists
    /// to prevent.
    pub(crate) fn from_frozen_payload(payload: &Value) -> Result<Self, String> {
        let rows = payload
            .get("rows")
            .and_then(Value::as_array)
            .ok_or("the recorded Core payload carries no rows")?;
        let mut by_source = BTreeMap::new();
        for row in rows {
            let source = row
                .get("canonical_source")
                .and_then(Value::as_str)
                .ok_or("a recorded Core row carries no canonical source")?;
            by_source.insert(
                source.to_owned(),
                (
                    read_profile(row.get("initialization_profile"))?,
                    read_profile(row.get("step_profile"))?,
                ),
            );
        }
        Ok(Self {
            by_source,
            termination: read_profile(payload.get("termination_profile"))?,
        })
    }

    /// The initialization and step labels recorded for the clause with this
    /// canonical source.
    pub(crate) fn clause_labels(
        &self,
        canonical_source: &str,
    ) -> Option<(ProofSearchProfile, ProofSearchProfile)> {
        self.by_source.get(canonical_source).copied()
    }

    /// The label recorded for the termination condition.
    pub(crate) fn termination(&self) -> ProofSearchProfile {
        self.termination
    }
}

fn read_profile(value: Option<&Value>) -> Result<ProofSearchProfile, String> {
    match value.and_then(Value::as_str) {
        Some("direct") => Ok(ProofSearchProfile::Direct),
        Some("casc_2025") => Ok(ProofSearchProfile::Casc2025),
        _ => Err("a recorded Core carries an unreadable profile label".to_owned()),
    }
}

/// A fresh sibling of `destination` to stage under when `--staging` is not
/// given, so [`build_certificate`]'s final promotion (an ordinary rename)
/// stays on the destination's own filesystem instead of defaulting to the
/// system temp directory, which is commonly a separate filesystem (e.g. a
/// tmpfs) and would force the cross-filesystem copy fallback on every run.
fn default_staging_root(destination: &Path) -> Result<PathBuf, String> {
    let parent = destination.parent().ok_or_else(|| {
        format!(
            "--destination {} has no parent directory to stage a sibling under",
            destination.display()
        )
    })?;
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_err(|error| format!("read system clock: {error}"))?
        .as_nanos();
    Ok(parent.join(format!(".staging-{}-{nanos}", std::process::id())))
}

/// Read whichever frozen record this invocation names.
pub(crate) fn load_build_source(source: &CertificateSource) -> Result<LoadedSource, String> {
    match source {
        CertificateSource::Core(path) => load_core_rows(path).map(LoadedSource::Core),
        CertificateSource::Counterexample(path) => {
            read_json(path).map(LoadedSource::Counterexample)
        }
        CertificateSource::Witness(path, recorded_at) => {
            read_json(path).map(|witness| LoadedSource::Witness(witness, recorded_at.clone()))
        }
    }
}

fn read_json(path: &Path) -> Result<Value, String> {
    let bytes = std::fs::read(path).map_err(|error| format!("read {}: {error}", path.display()))?;
    serde_json::from_slice(&bytes).map_err(|error| format!("parse {}: {error}", path.display()))
}

fn load_core_rows(path: &Path) -> Result<Vec<CoreRow>, String> {
    let bytes = std::fs::read(path).map_err(|error| format!("read {}: {error}", path.display()))?;
    let file: CoreRowsFile = serde_json::from_slice(&bytes)
        .map_err(|error| format!("parse {}: {error}", path.display()))?;
    if file.kind != CORE_ROWS_KIND || file.version != CORE_ROWS_VERSION {
        return Err(format!(
            "{} is not a {CORE_ROWS_KIND} v{CORE_ROWS_VERSION} file",
            path.display()
        ));
    }
    if file.rows.is_empty() {
        return Err(format!("{} carries no Core rows", path.display()));
    }
    Ok(file.rows)
}

// ------------------------------------------------------------
// Lean Prerequisites And Worker Resolution
// ------------------------------------------------------------

pub(crate) fn resolve_or_build_worker(
    repository_root: &Path,
    worker: Option<&Path>,
) -> Result<PathBuf, String> {
    resolve_or_build_worker_with_cancellation(repository_root, worker, &CancellationToken::new())
}

pub(crate) fn resolve_or_build_worker_with_cancellation(
    repository_root: &Path,
    worker: Option<&Path>,
    cancellation: &CancellationToken,
) -> Result<PathBuf, String> {
    if cancellation.should_stop() {
        return Err("worker admission interrupted".into());
    }
    let explicit_worker = if let Some(worker) = worker {
        let resolved = if worker.is_absolute() {
            worker.to_path_buf()
        } else {
            repository_root.join(worker)
        };
        Some(
            resolved
                .canonicalize()
                .map_err(|error| format!("resolve worker: {error}"))?,
        )
    } else {
        None
    };
    let mut build_arguments = vec![
        "LEAN_NUM_THREADS=2".into(),
        "bash".into(),
        repository_root
            .join("scripts/lake_build_watched.sh")
            .into_os_string(),
    ];
    if explicit_worker.is_none() {
        build_arguments.push(WORKER_TARGET.into());
    }
    build_arguments.extend(
        CERTIFICATE_PREREQUISITE_TARGETS
            .iter()
            .map(|target| (*target).into()),
    );
    bootstrap_output(
        Path::new("/usr/bin/env"),
        &build_arguments,
        repository_root,
        cancellation,
    )?;
    if let Some(worker) = explicit_worker {
        return Ok(worker);
    }
    repository_root
        .join(WORKER_RELATIVE_PATH)
        .canonicalize()
        .map_err(|error| format!("resolve built worker: {error}"))
}

pub(crate) fn fetch_worker_manifest(
    worker: &Path,
    repository_root: &Path,
    canonical_id: &str,
) -> Result<Value, String> {
    fetch_worker_manifest_with_cancellation(
        worker,
        repository_root,
        canonical_id,
        &CancellationToken::new(),
    )
}

pub(crate) fn fetch_worker_manifest_with_cancellation(
    worker: &Path,
    repository_root: &Path,
    canonical_id: &str,
    cancellation: &CancellationToken,
) -> Result<Value, String> {
    let output = bootstrap_output(
        worker,
        &["manifest".into(), canonical_id.into()],
        repository_root,
        cancellation,
    )?;
    serde_json::from_slice(&output).map_err(|error| format!("parse worker manifest: {error}"))
}

fn bootstrap_output(
    executable: &Path,
    arguments: &[std::ffi::OsString],
    repository_root: &Path,
    cancellation: &CancellationToken,
) -> Result<Vec<u8>, String> {
    use crate::vampire::process::{SpawnError, SpawnedProcess};
    use std::io::Read;
    use std::sync::atomic::{AtomicBool, Ordering};
    if cancellation.should_stop() {
        return Err("worker admission interrupted".into());
    }
    let mut process = SpawnedProcess::spawn(executable, arguments, repository_root).map_err(
        |error| match error {
            SpawnError::Failed(detail) | SpawnError::CleanupFailed(detail) => detail,
        },
    )?;
    let pipes = process.take_pipes()?;
    let failed = AtomicBool::new(false);
    std::thread::scope(|scope| {
        let capture = |mut source: Box<dyn Read + Send>| {
            let mut output = Vec::new();
            let mut buffer = [0; 8192];
            loop {
                match source.read(&mut buffer) {
                    Ok(0) => break,
                    Ok(count) if output.len() + count <= 16 * 1024 * 1024 => {
                        output.extend_from_slice(&buffer[..count])
                    }
                    Ok(_) | Err(_) => {
                        failed.store(true, Ordering::Release);
                        break;
                    }
                }
            }
            output
        };
        let stdout = scope.spawn(move || capture(Box::new(pipes.stdout)));
        let stderr = scope.spawn(move || capture(Box::new(pipes.stderr)));
        let exit = process.supervise(cancellation, &failed);
        let stdout = stdout
            .join()
            .map_err(|_| "worker stdout capture panicked")?;
        let stderr = stderr
            .join()
            .map_err(|_| "worker stderr capture panicked")?;
        if let Some(error) = exit.cleanup_error {
            return Err(error);
        }
        if cancellation.should_stop() {
            return Err("worker admission interrupted".into());
        }
        if failed.load(Ordering::Acquire) {
            return Err("worker output exceeded capture limit or failed".into());
        }
        if !exit.status.map_err(|error| error.to_string())?.success() {
            return Err(format!(
                "worker admission command failed: {}",
                String::from_utf8_lossy(&stderr)
            ));
        }
        Ok(stdout)
    })
}

// ------------------------------------------------------------
// Execution
// ------------------------------------------------------------

pub(crate) enum CertificateCliError {
    Bootstrap(String),
    Build(CertificateBuildError),
    /// An `Invalid` publication failed: the record did not rebuild its
    /// certificate, the built tree did not revalidate, or the destination
    /// was already taken.
    Publish(Box<crate::framework2::PublicationError>),
    /// The input on disk is no longer the input the record was frozen
    /// against. Nothing is built: a certificate rebuilt from a record of
    /// one input would close a theorem about another.
    InputChanged(String),
    /// The build's own phase stopped it: its allowance expired
    /// (`deadline`) or the caller interrupted it.
    Stopped {
        deadline: bool,
        detail: String,
    },
}

impl CertificateCliError {
    pub(crate) fn detail(&self) -> String {
        match self {
            Self::Bootstrap(detail) | Self::InputChanged(detail) => detail.clone(),
            Self::Stopped { detail, .. } => detail.clone(),
            Self::Build(error) => error.to_string(),
            Self::Publish(error) => error.to_string(),
        }
    }
}

/// Parse, bootstrap, and run one `certificate build` invocation, printing a
/// short status line (or the failure detail) to `writer`.
///
/// Returns the process exit code directly: `0` on success, `2` for
/// bootstrap/lock/argument failures, `3` for [`CertificateBuildError`].
/// The outer `Result::Err` case is reserved for failures so structural they
/// cannot be attributed to this run at all (currently unreachable; kept for
/// symmetry with [`crate::cli::execute_cli`]'s contract).
pub fn execute_certificate_build_cli<W: Write>(
    config: CertificateBuildConfig,
    mut writer: W,
) -> Result<i32, String> {
    let repository_root = config.repository.canonicalize().map_err(|error| {
        format!(
            "cannot resolve repository {}: {error}",
            config.repository.display()
        )
    })?;
    if !repository_root.join("Whiel.lean").is_file() {
        eprintln!(
            "error: {} does not look like the Whiel repository root",
            repository_root.display()
        );
        return Ok(2);
    }

    let source = match load_build_source(&config.source) {
        Ok(source) => source,
        Err(message) => {
            eprintln!("error: {message}");
            return Ok(2);
        }
    };
    let worker_path = match resolve_or_build_worker(&repository_root, config.worker.as_deref()) {
        Ok(path) => path,
        Err(message) => {
            eprintln!("error: {message}");
            return Ok(2);
        }
    };
    let descriptor = match fetch_worker_manifest(&worker_path, &repository_root, &config.input) {
        Ok(descriptor) => descriptor,
        Err(message) => {
            eprintln!("error: {message}");
            return Ok(2);
        }
    };
    let pinned = match PinnedLeancheckVampire::from_lock(&repository_root) {
        Ok(pinned) => pinned,
        Err(error) => {
            eprintln!("error: resolve the pinned leancheck Vampire: {error}");
            return Ok(2);
        }
    };
    if config.destination.exists() {
        eprintln!(
            "error: certificate destination already exists: {}",
            config.destination.display()
        );
        return Ok(2);
    }
    let (staging_root, staging_is_ours) = match config.staging.clone() {
        Some(path) => (path, false),
        None => match default_staging_root(&config.destination) {
            Ok(path) => (path, true),
            Err(message) => {
                eprintln!("error: {message}");
                return Ok(2);
            }
        },
    };
    if let Err(error) = std::fs::create_dir_all(&staging_root) {
        eprintln!(
            "error: create staging root {}: {error}",
            staging_root.display()
        );
        return Ok(2);
    }

    let tokio_runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .map_err(|error| format!("create the async runtime: {error}"))?;

    let outcome = tokio_runtime.block_on(build_certificate_from_record(BuildFromRecord {
        repository_root: repository_root.clone(),
        worker_path,
        descriptor,
        input: config.input.clone(),
        source,
        profile: RecordJobProfiles::Constant(config.profile),
        time_limit_seconds: config.time_limit_seconds,
        evidence: config.evidence.clone(),
        validation_limit: config.validation_limit,
        staging_root: staging_root.clone(),
        destination: config.destination.clone(),
        pinned: pinned.clone(),
        // The standalone command is told which input to build against and
        // checks the worker's own canonical id; it holds no earlier record
        // of the input's digests to compare against.
        expected_task_identity: None,
        expected_scope_identity_sha256: None,
        // This command runs one build with no campaign workspace around it;
        // its own destination is the benchmark directory it was handed.
        space_guard: None,
        // This command has no interruption relay of its own and states no
        // whole-build allowance; its per-job `--time-limit-seconds` is what
        // bounds the solver.
        cancellation: CancellationToken::new(),
        certification_limit: None,
    }));

    // A staging root this command created for itself is removed again
    // when the build has emptied it, so a build under a benchmark
    // directory leaves nothing behind beside the tree it published.
    if staging_is_ours {
        let _ = std::fs::remove_dir(&staging_root);
    }

    match outcome {
        Ok(BuildOutcome { receipt, published }) => {
            if let Some(published) = published.as_ref() {
                let _ = writeln!(
                    writer,
                    "counterexample record: {}",
                    published.record().display()
                );
            } else if let Some(parent) = receipt.destination.parent() {
                let _ = writeln!(
                    writer,
                    "core record: {}",
                    parent.join(CORE_RECORD_NAME).display()
                );
            }
            let published_tree = published
                .as_ref()
                .map(|published| published.certificate())
                .unwrap_or(receipt.destination.as_path());
            let receipt_path = config.receipt.clone().unwrap_or_else(|| {
                config
                    .destination
                    .parent()
                    .unwrap_or_else(|| Path::new("."))
                    .join(format!("{}.certificate-receipt.json", config.input))
            });
            let payload = receipt_json(
                &config,
                &receipt,
                published_tree,
                published.as_ref(),
                pinned.sha256(),
            );
            if let Some(parent) = receipt_path.parent()
                && let Err(error) = std::fs::create_dir_all(parent)
            {
                eprintln!(
                    "error: create {} for the build receipt: {error}",
                    parent.display()
                );
                return Ok(2);
            }
            if let Err(error) = std::fs::write(
                &receipt_path,
                serde_json::to_vec_pretty(&payload).expect("receipt JSON is always serializable"),
            ) {
                eprintln!(
                    "error: write build receipt {}: {error}",
                    receipt_path.display()
                );
                return Ok(2);
            }
            let _ = writeln!(
                writer,
                "certificate build succeeded: {} (receipt: {})",
                published_tree.display(),
                receipt_path.display()
            );
            Ok(0)
        }
        Err(CertificateCliError::Bootstrap(message)) => {
            eprintln!("error: {message}");
            Ok(2)
        }
        Err(CertificateCliError::Build(error)) => {
            eprintln!("certificate build failed: {error}");
            Ok(3)
        }
        Err(CertificateCliError::Publish(error)) => {
            eprintln!("certificate build failed: {error}");
            Ok(3)
        }
        Err(CertificateCliError::InputChanged(detail)) => {
            eprintln!("certificate build failed: {detail}");
            Ok(3)
        }
        Err(CertificateCliError::Stopped { detail, .. }) => {
            eprintln!("certificate build failed: {detail}");
            Ok(3)
        }
    }
}

/// One loaded frozen record, ready to build from.
pub(crate) enum LoadedSource {
    Core(Vec<CoreRow>),
    /// The durable record's raw JSON. It is decoded only once the bound
    /// task and scope identities exist to decode it against.
    Counterexample(Value),
    /// One recorded witness instance, opaque here: only Lean reads it,
    /// together with the provenance label for where it was recorded.
    Witness(Value, String),
}

/// Everything one `certificate build` invocation needs after bootstrap.
///
/// `campaign certify` drives the same structure as a library call: that is
/// what makes the deferred path the standalone path, rather than a second
/// certifier that could drift from it.
pub(crate) struct BuildFromRecord {
    pub(crate) repository_root: PathBuf,
    pub(crate) worker_path: PathBuf,
    pub(crate) descriptor: Value,
    pub(crate) input: String,
    pub(crate) source: LoadedSource,
    pub(crate) profile: RecordJobProfiles,
    pub(crate) time_limit_seconds: u64,
    /// `--evidence`; `--core` only. See [`CertificateBuildConfig::evidence`].
    pub(crate) evidence: Option<PathBuf>,
    pub(crate) validation_limit: Duration,
    pub(crate) staging_root: PathBuf,
    pub(crate) destination: PathBuf,
    pub(crate) pinned: PinnedLeancheckVampire,
    /// The task identity the record was frozen against, when the caller
    /// recorded one. The bound worker's own identity must equal it or
    /// nothing is built: a record of one input never certifies another.
    pub(crate) expected_task_identity: Option<Value>,
    /// The scope digest the record was frozen under, when the caller
    /// recorded one. The in-process certification checks this too
    /// (`readmit_frozen_core`); without it a change to the scope encoding
    /// would surface as an opaque build failure rather than as the stale
    /// record it is.
    pub(crate) expected_scope_identity_sha256: Option<String>,
    /// The caller's workspace guard, when it has one. Publication checks it
    /// at every phase boundary, so a certification that fills the disk is
    /// refused rather than discovered by an IO error.
    pub(crate) space_guard: Option<Arc<crate::framework2::resource_limits::SpaceGuard>>,
    /// The caller's own cancellation root, deadline-free. Everything this
    /// build starts — the worker pool, the solver, `lean` and the pinned
    /// Vampire — runs under a phase child of it, so an interruption reaches
    /// a build already in flight instead of only stopping the next one.
    pub(crate) cancellation: CancellationToken,
    /// The whole build's allowance, bound as an absolute deadline on that
    /// same phase. One mechanism for the deadline and the signal, as the
    /// in-process certification uses: a limit that merely dropped the future
    /// would leave the run's own shutdown unperformed.
    pub(crate) certification_limit: Option<Duration>,
}

/// What one finished build produced.
pub(crate) struct BuildOutcome {
    pub(crate) receipt: CertificateBuildReceipt,
    /// Present exactly for the two `Invalid` modes, naming the durable
    /// record the tree was built from.
    pub(crate) published: Option<PublishedInvalid>,
}

pub(crate) async fn build_certificate_from_record(
    request: BuildFromRecord,
) -> Result<BuildOutcome, CertificateCliError> {
    let BuildFromRecord {
        repository_root,
        worker_path,
        descriptor,
        input,
        source,
        profile,
        time_limit_seconds,
        evidence,
        validation_limit,
        staging_root,
        destination,
        pinned,
        expected_task_identity,
        expected_scope_identity_sha256,
        space_guard,
        cancellation: external,
        certification_limit,
    } = request;
    let solver_admission = create_general_solver_admission(
        RuntimeResourcePolicy::agent_only(1, 1)
            .map_err(|error| CertificateCliError::Bootstrap(error.to_string()))?,
    )
    .map_err(|error| CertificateCliError::Bootstrap(error.to_string()))?;
    // The build's own phase: it relays the caller's interruption and carries
    // the allowance as an absolute deadline, so a stop reaches the children
    // rather than merely abandoning the future that owns them.
    let phase = PhaseCancellation::new(&external).map_err(|_| {
        CertificateCliError::Bootstrap(
            "a certificate build requires a deadline-free cancellation root".into(),
        )
    })?;
    if let Some(limit) = certification_limit {
        let deadline = tokio::time::Instant::now()
            .checked_add(limit)
            .ok_or_else(|| {
                CertificateCliError::Bootstrap(
                    "the certification allowance overflows the monotonic clock".into(),
                )
            })?;
        if !phase.token().bind_absolute_deadline(deadline) {
            return Err(CertificateCliError::Bootstrap(
                "the certification phase already owns a deadline".into(),
            ));
        }
    }
    let cancellation = phase.token().clone();
    let pool = FixedAmbientWorkerPoolConfig::new(
        FixedAmbientWorkerCommand::new(worker_path, &repository_root),
        1,
    )
    .map_err(|error| CertificateCliError::Bootstrap(error.to_string()))?;

    let catalog_instance_digest =
        crate::encoding::bytes_sha256(format!("whiel-certificate-cli-{input}").as_bytes());
    let bound = bind_fixed_ambient_framework_ii(
        descriptor,
        pool,
        catalog_instance_digest,
        // The certificate CLI only replays already checked rows and never
        // runs a scan or consults a proposer, so it sets no host limit at
        // all — the same default the agent path uses, and in particular no
        // level bound.
        HostLimits::UNBOUNDED,
        // The certificate CLI, like the agent path, never enables
        // `compress_core` (Pass 7.5b): it only replays already checked rows.
        false,
        // The certificate CLI never runs a live consultation, so the tool
        // policy never takes effect here either; the default (every tool
        // enabled) keeps this state consistent with `LeveledHoudiniState`'s
        // own default.
        AgentToolPolicy::default(),
        &solver_admission,
        &cancellation,
    )
    .await
    .map_err(|error| CertificateCliError::Bootstrap(error.to_string()))?;

    if bound.task().identity().canonical_id() != input {
        let found = bound.task().identity().canonical_id().to_string();
        let (_task, _admission, solver, _houdini) = bound.into_parts();
        let _ = solver.shutdown().await;
        return Err(CertificateCliError::Bootstrap(format!(
            "--input {input} does not match the worker's own canonical id {found}"
        )));
    }
    let changed = expected_task_identity
        .as_ref()
        .and_then(|expected| {
            let live = crate::framework2::task_identity_record(bound.task().identity());
            (&live != expected).then(|| {
                format!(
                    "{input} is no longer the input this record was frozen against; \
                     recorded {expected}, found {live}"
                )
            })
        })
        .or_else(|| {
            let expected = expected_scope_identity_sha256.as_deref()?;
            let live = bound.solver().scope().identity_sha256();
            (live != expected).then(|| {
                format!(
                    "{input}'s scope no longer matches the one this record was frozen under; \
                     recorded {expected}, found {live}"
                )
            })
        });
    if let Some(detail) = changed {
        let (_task, _admission, solver, _houdini) = bound.into_parts();
        let _ = solver.shutdown().await;
        return Err(CertificateCliError::InputChanged(detail));
    }
    let (task, admission, solver, houdini) = bound.into_parts();

    let result = match source {
        LoadedSource::Core(rows) => run_build_after_bind(
            &repository_root,
            &admission,
            &solver,
            &houdini,
            &solver_admission,
            &cancellation,
            rows,
            profile,
            time_limit_seconds,
            evidence,
            staging_root,
            destination,
            &pinned,
        )
        .await
        .map(|receipt| BuildOutcome {
            receipt,
            published: None,
        }),
        LoadedSource::Counterexample(record) => {
            run_invalid_build_after_bind(
                &repository_root,
                &solver,
                &solver_admission,
                &phase,
                certification_limit,
                task.identity(),
                &record,
                staging_root,
                destination,
                space_guard.as_ref(),
            )
            .await
        }
        LoadedSource::Witness(witness, recorded_at) => {
            // One authority for the limit and for the record's fuel policy:
            // the same `PreCertificateAgentHoudiniLimits` value is what the
            // validation actually runs under and what the record then
            // states.
            let limits = witness_validation_limits(validation_limit);
            match run_witness_validation(&solver, &solver_admission, limits, &witness, &recorded_at)
                .await
            {
                Ok(validated) => {
                    let fuel_policy = match CounterexampleFuelPolicy::new(
                        limits.counterexample_validation_limit(),
                    ) {
                        Ok(policy) => policy,
                        Err(error) => Err(CertificateCliError::Bootstrap(format!(
                            "record the witness validation's fuel policy: {error}"
                        )))?,
                    };
                    let record = DurableCounterexampleRecord::new(validated, fuel_policy);
                    run_invalid_build_after_bind(
                        &repository_root,
                        &solver,
                        &solver_admission,
                        &phase,
                        certification_limit,
                        task.identity(),
                        &record.to_json(),
                        staging_root,
                        destination,
                        space_guard.as_ref(),
                    )
                    .await
                }
                Err(error) => Err(error),
            }
        }
    };

    let shutdown = solver.shutdown().await;
    // The phase is joined after the pool, so the relay it spawned is gone
    // before this returns and the stop reason is final.
    let completed = phase.finish().await;
    if let Err(error) = shutdown {
        // A failed shutdown never masks a real build outcome; it is only
        // surfaced when the build itself otherwise succeeded.
        if result.is_ok() {
            return Err(CertificateCliError::Bootstrap(format!(
                "shut down the fixed-ambient worker pool: {error}"
            )));
        }
    }
    // A stop the phase observed classifies the outcome even when the build
    // reported something else on its way out: the allowance and the
    // interruption are what actually ended it.
    match completed.map(|completed| completed.stop) {
        Ok(Some(PhaseStop::DeadlineExpired)) => Err(CertificateCliError::Stopped {
            deadline: true,
            detail: match certification_limit {
                Some(limit) => format!(
                    "certification exceeded its {} second allowance",
                    limit.as_secs_f64()
                ),
                None => "certification stopped on a deadline it did not set".to_string(),
            },
        }),
        Ok(Some(PhaseStop::Interrupted)) => Err(CertificateCliError::Stopped {
            deadline: false,
            detail: "certification was interrupted".to_string(),
        }),
        Ok(None) => result,
        Err(error) => match result {
            Ok(_) => Err(CertificateCliError::Bootstrap(format!(
                "certification phase cleanup: {error}"
            ))),
            Err(original) => Err(original),
        },
    }
}

#[allow(clippy::too_many_arguments)]
async fn run_build_after_bind(
    repository_root: &Path,
    admission: &FrameworkIIAdmissionContext,
    solver: &FrameworkIISolverContext,
    houdini: &LeveledHoudiniState,
    solver_admission: &SolverAdmission,
    cancellation: &CancellationToken,
    rows: Vec<CoreRow>,
    profile: RecordJobProfiles,
    time_limit_seconds: u64,
    evidence: Option<PathBuf>,
    staging_root: PathBuf,
    destination: PathBuf,
    pinned: &PinnedLeancheckVampire,
) -> Result<CertificateBuildReceipt, CertificateCliError> {
    let sources: Vec<String> = rows.iter().map(|row| row.source.clone()).collect();
    let admitted = admission
        .admit_clauses(&sources, None, solver_admission, cancellation)
        .await
        .map_err(|error| CertificateCliError::Bootstrap(format!("admit Core rows: {error}")))?;
    let AdmissionOutcome::Accepted(clauses) = admitted else {
        return Err(CertificateCliError::Bootstrap(
            "the Core rows were not accepted verbatim; a correction is required".to_string(),
        ));
    };
    if clauses.len() != rows.len() {
        return Err(CertificateCliError::Bootstrap(format!(
            "admitted {} clauses for {} Core rows",
            clauses.len(),
            rows.len()
        )));
    }

    let registered = houdini
        .catalog()
        .register_batch(
            0,
            clauses
                .iter()
                .cloned()
                .map(|clause| (clause, ExtendedClauseOrigin::Submitted)),
        )
        .map_err(|error| CertificateCliError::Bootstrap(format!("register Core rows: {error}")))?;

    let mut source_to_id: BTreeMap<String, ClauseId> = BTreeMap::new();
    for id in registered.ids().iter().copied() {
        let record = houdini
            .catalog()
            .record(id)
            .map_err(|error| CertificateCliError::Bootstrap(error.to_string()))?;
        source_to_id.insert(record.formula().canonical_source().to_string(), id);
    }

    let mut level_of = BTreeMap::new();
    for row in &rows {
        let id = source_to_id.get(&row.source).copied().ok_or_else(|| {
            CertificateCliError::Bootstrap(format!(
                "Core row source has no matching registered clause: {}",
                row.source
            ))
        })?;
        level_of.insert(id, FrameworkIILevel::new(row.level));
    }

    // The protected precondition rows are part of every Core at level zero.
    // A live search places them there itself; a rebuild from recorded rows
    // has to do the same, or the obligations lose the precondition.
    for id in houdini
        .catalog()
        .reserved_system_ids()
        .map_err(|error| CertificateCliError::Bootstrap(error.to_string()))?
    {
        level_of.entry(id).or_insert(FrameworkIILevel::ZERO);
    }

    let snapshot = LeveledCandidateSnapshot::build(houdini.catalog(), None, level_of)
        .map_err(|error| CertificateCliError::Bootstrap(error.to_string()))?;

    // Resolve the recorded labels against the ids this rebuild interned —
    // every clause the snapshot places, protected precondition rows
    // included — so the closure the builder calls per job is a lookup
    // rather than a second decode.
    let labels: Option<BTreeMap<u64, (ProofSearchProfile, ProofSearchProfile)>> = match &profile {
        RecordJobProfiles::Constant(_) => None,
        RecordJobProfiles::Recorded(recorded) => Some(
            snapshot
                .records()
                .iter()
                .filter_map(|(id, record)| {
                    recorded
                        .clause_labels(record.formula().canonical_source())
                        .map(|labels| (id.get(), labels))
                })
                .collect(),
        ),
    };
    let profiles = move |job: &CertificateJob| {
        let selected = match &profile {
            RecordJobProfiles::Constant(profile) => *profile,
            RecordJobProfiles::Recorded(recorded) => match job.role.as_str() {
                "termination" => {
                    if job.clause_id.is_some() {
                        return Err(CoreFreezeError::TerminationJobNamesAClause);
                    }
                    recorded.termination()
                }
                role => {
                    let clause_id = job
                        .clause_id
                        .ok_or_else(|| CoreFreezeError::JobHasNoClause(role.to_owned()))?;
                    let labels = labels
                        .as_ref()
                        .and_then(|labels| labels.get(&clause_id))
                        .ok_or(CoreFreezeError::JobNamesAnUnfrozenClause(clause_id))?;
                    match role {
                        "initialization" => labels.0,
                        "maintenance" => labels.1,
                        other => {
                            return Err(CoreFreezeError::UnrecognizedRole(other.to_owned()));
                        }
                    }
                }
            },
        };
        Ok::<_, CoreFreezeError>(LeancheckProfile::new(selected))
    };

    build_certificate(CertificateBuildRequest {
        solver,
        admission: solver_admission,
        snapshot: Arc::new(snapshot),
        pinned,
        profiles: &profiles,
        time_limit_seconds,
        // Regenerating a checked-in tree stays strictly sequential; the
        // coordinator's concurrent path belongs to Pass 7.5f's
        // certification of a live frozen Core.
        concurrency: NonZeroUsize::new(1).expect("one is nonzero"),
        repository_root: repository_root.to_path_buf(),
        staging_root,
        destination,
        evidence_destination: evidence,
        cancellation,
        #[cfg(feature = "test-hooks")]
        hooks: CertificateBuildHooks::default(),
    })
    .await
    .map_err(CertificateCliError::Build)
}

// ------------------------------------------------------------
// Invalid Certificates From A Frozen Record
// ------------------------------------------------------------

/// Build and publish one `Invalid` certificate from a durable record.
///
/// The record is decoded strictly against the bound task and scope
/// identities — a record written for another input, another scope, or by a
/// version this host does not understand is refused before anything is
/// built — and then handed to [`publish_invalid_in_phase`], which sends it
/// back through Lean's own re-decode and re-check, revalidates the built
/// tree with a fresh Lean build at the exact negated input type and an
/// exact-std3 audit, writes `Counterexample.json` beside the input, and
/// only then renames the tree into place.
///
/// The publication runs under this command's own phase rather than opening
/// a second one: the build's allowance is already bound there, and the
/// runtime does not nest a phase on another phase's child.
#[allow(clippy::too_many_arguments)]
async fn run_invalid_build_after_bind(
    repository_root: &Path,
    solver: &FrameworkIISolverContext,
    solver_admission: &SolverAdmission,
    phase: &PhaseCancellation,
    certification_limit: Option<Duration>,
    identity: &TaskIdentity,
    record: &Value,
    staging_root: PathBuf,
    destination: PathBuf,
    space_guard: Option<&Arc<crate::framework2::resource_limits::SpaceGuard>>,
) -> Result<BuildOutcome, CertificateCliError> {
    let record =
        DurableCounterexampleRecord::from_json(record, identity, solver.scope().identity_sha256())
            .map_err(|error| {
                CertificateCliError::Bootstrap(format!(
                    "read the durable counterexample record: {error}"
                ))
            })?;
    let input_directory = destination
        .parent()
        .ok_or_else(|| {
            CertificateCliError::Bootstrap(format!(
                "--destination {} has no parent benchmark directory to write {} into",
                destination.display(),
                crate::framework2::COUNTEREXAMPLE_RECORD_FILE
            ))
        })?
        .to_path_buf();
    let published = publish_invalid_in_phase(
        PublishInvalidRequest {
            space_guard,
            solver,
            admission: solver_admission,
            record: &record,
            input_namespace: identity.namespace(),
            repository_root: repository_root.to_path_buf(),
            staging_root,
            input_directory,
            destination,
            external_cancellation: phase.token(),
            certification_limit,
            #[cfg(feature = "test-hooks")]
            hooks: CertificateBuildHooks::default(),
        },
        phase,
    )
    .await
    .map_err(|error| CertificateCliError::Publish(Box::new(error)))?;
    Ok(BuildOutcome {
        receipt: published.receipt().clone(),
        published: Some(published),
    })
}

/// The limits authority one `--witness` validation runs under.
///
/// This command runs no search, so the overall limit and the iteration
/// limit have nothing to bound; the field that does apply is the call-local
/// `counterexample_validation_limit`, and building the whole authority
/// rather than passing a bare `Duration` is what keeps this command's limit
/// the same kind of value the search's is, read back out of the same
/// accessor by the same enforcement path.
fn witness_validation_limits(validation_limit: Duration) -> PreCertificateAgentHoudiniLimits {
    PreCertificateAgentHoudiniLimits::new_with_counterexample_limit(
        validation_limit,
        None,
        None,
        validation_limit,
    )
}

/// Validate one recorded witness through Lean and freeze its record.
///
/// The witness is opaque here, exactly as an agent's own submission is:
/// this passes it to Lean unmodified and keeps only Lean's typed verdict. A
/// rejection is reported with Lean's own code, not reinterpreted.
///
/// The call runs through [`validate_recorded_witness`], the search's own
/// limit-enforcing path: a fresh call-scoped cancellation token raced
/// against `limits`' call-local validation limit, so the limit the record
/// will state as its fuel policy is the limit the replay actually ran
/// under. An expiry is Lean-shaped — a `timeout` rejection of the call, not
/// a verdict on the instance — and this command reports it as the rejection
/// it is.
async fn run_witness_validation(
    solver: &FrameworkIISolverContext,
    solver_admission: &SolverAdmission,
    limits: PreCertificateAgentHoudiniLimits,
    witness: &Value,
    recorded_at: &str,
) -> Result<crate::framework2::FrozenCounterexampleRecord, CertificateCliError> {
    match validate_recorded_witness(solver, solver_admission, limits, witness).await {
        RecordedWitnessValidation::Validated(validated) => {
            Ok(crate::framework2::FrozenCounterexampleRecord::freeze(
                *validated,
                solver.scope().task_identity().clone(),
                solver.scope().identity_sha256(),
                CounterexampleProvenance::RecordedWitness {
                    source: recorded_at.into(),
                },
            ))
        }
        RecordedWitnessValidation::Rejected(rejection) => {
            Err(CertificateCliError::Bootstrap(format!(
                "Lean rejected the recorded witness ({}): {}",
                rejection.code(),
                rejection.reason()
            )))
        }
        RecordedWitnessValidation::Failure(report) => Err(CertificateCliError::Bootstrap(format!(
            "validate the recorded witness: origin={:?} kind={:?} detail={}",
            report.origin(),
            report.kind(),
            report.detail().unwrap_or("none")
        ))),
    }
}

// ------------------------------------------------------------
// Receipt Rendering
// ------------------------------------------------------------

fn profile_name(profile: ProofSearchProfile) -> &'static str {
    match profile {
        ProofSearchProfile::Direct => "direct",
        ProofSearchProfile::Casc2025 => "casc_2025",
    }
}

fn receipt_json(
    config: &CertificateBuildConfig,
    receipt: &CertificateBuildReceipt,
    destination: &Path,
    published: Option<&PublishedInvalid>,
    pinned_vampire_sha256: &str,
) -> Value {
    json!({
        "kind": RECEIPT_KIND,
        "version": RECEIPT_VERSION,
        "crate_version": env!("CARGO_PKG_VERSION"),
        "canonical_id": config.input,
        "requested_profile": match &config.source {
            CertificateSource::Core(_) => Value::String(profile_name(config.profile).to_string()),
            // An Invalid certificate runs no solver, so it has no profile.
            CertificateSource::Counterexample(_) | CertificateSource::Witness(_, _) => Value::Null,
        },
        "input_identity": receipt.input_identity,
        "scope_identity": receipt.scope_identity,
        "snapshot_identity": receipt.snapshot_identity,
        "lean_binary": receipt.lean_binary.to_string_lossy(),
        "lake_lean_path_digest": receipt.lake_lean_path_digest,
        "axioms": receipt.axioms,
        "destination": destination.to_string_lossy(),
        "shape": match receipt.shape {
            CertificateBundleShape::Valid => "valid",
            CertificateBundleShape::Invalid => "invalid",
        },
        "certificate_module": receipt.certificate_module,
        "certificate_theorem": receipt.certificate_theorem,
        "counterexample_record": published
            .map(|published| Value::String(published.record().to_string_lossy().into_owned()))
            .unwrap_or(Value::Null),
        "revalidation": published
            .map(|published| {
                json!({
                    "source_sha256": published.revalidation().source_digest,
                    "telescope_normalized_sha256": published
                        .revalidation()
                        .telescope_normalized_digest,
                    "axioms": published.revalidation().axioms,
                    "modules": published.revalidation().modules,
                })
            })
            .unwrap_or(Value::Null),
        "pinned_leancheck_vampire_sha256": pinned_vampire_sha256,
        "jobs": receipt
            .jobs
            .iter()
            .map(|job| {
                json!({
                    "id": job.id,
                    "profile": profile_name(job.profile.profile()),
                    "invocation_identity": job.invocation_identity,
                    "raw_sha256": job.raw_sha256,
                    "canonical_sha256": job.canonical_sha256,
                    "transformed_sha256": job.transformed_sha256,
                    "transforms": job
                        .transforms
                        .iter()
                        .map(ProofTransformRecord::to_json)
                        .collect::<Vec<_>>(),
                    "packaged_sha256": job.packaged_sha256,
                    "elapsed_seconds": job.elapsed.as_secs_f64(),
                    // Everything the dropped volatile solver lines used to
                    // publish inside a module, plus the `lean` wall of the
                    // two modules this job owns. The same numbers are in
                    // the published tree's own timing.csv, at its root.
                    "timing": json!({
                        "vampire_elapsed_seconds": job.measurements.vampire_elapsed_seconds,
                        "vampire_peak_memory_mb": job.measurements.vampire_peak_memory_mb,
                        "transform_seconds": job.transform_elapsed.as_secs_f64(),
                        "proof_module_lean_seconds": job
                            .proof_module_lean_elapsed
                            .map(|elapsed| elapsed.as_secs_f64()),
                        "reconstruction_lean_seconds": job
                            .reconstruction_lean_elapsed
                            .map(|elapsed| elapsed.as_secs_f64()),
                    }),
                })
            })
            .collect::<Vec<_>>(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn args(pieces: &[&str]) -> Vec<String> {
        pieces.iter().map(|piece| piece.to_string()).collect()
    }

    // Exercise the real bootstrap dispatch without launching Lake or Lean.
    // The fixture refuses success unless both generated-proof imports are
    // requested, even when an already-built worker is supplied explicitly.
    #[cfg(unix)]
    fn check_generated_proof_bootstrap(explicit_worker: bool) {
        use std::fs;
        use std::time::{SystemTime, UNIX_EPOCH};

        struct Scratch(PathBuf);
        impl Drop for Scratch {
            fn drop(&mut self) {
                let _ = fs::remove_dir_all(&self.0);
            }
        }
        let scratch = Scratch(std::env::temp_dir().join(format!(
            "whiel-certificate-bootstrap-{}-{}",
            std::process::id(),
            SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos()
        )));
        let repository = &scratch.0;
        fs::create_dir_all(repository.join("scripts")).unwrap();
        fs::write(
            repository.join("scripts/lake_build_watched.sh"),
            r#"set -eu
[ "$LEAN_NUM_THREADS" = 2 ]
for prerequisite in Whiel.Vampire.ClauseProjection Whiel.Vampire.EmptyDomainLRAT; do
    case " $* " in
        *" $prerequisite "*) ;;
        *) printf 'missing generated-proof prerequisite: %s\n' "$prerequisite" >&2; exit 7 ;;
    esac
done
printf '%s\n' "$@" > bootstrap-targets.txt
case " $* " in
    *" fixed_ambient_encoding_worker "*)
        mkdir -p .lake/build/bin
        : > .lake/build/bin/fixed_ambient_encoding_worker
        ;;
esac
"#,
        )
        .unwrap();
        let explicit_path = Path::new("provided-worker");
        if explicit_worker {
            fs::write(repository.join(explicit_path), "already built worker").unwrap();
        }
        let worker = resolve_or_build_worker(repository, explicit_worker.then_some(explicit_path))
            .expect("bootstrap prepares imports required only by generated proofs");
        let expected_worker = repository.join(if explicit_worker {
            explicit_path
        } else {
            Path::new(WORKER_RELATIVE_PATH)
        });
        assert_eq!(worker, expected_worker.canonicalize().unwrap());
        let targets = fs::read_to_string(repository.join("bootstrap-targets.txt")).unwrap();
        assert_eq!(
            targets.lines().any(|target| target == WORKER_TARGET),
            !explicit_worker,
            "an explicit worker is reused while proof prerequisites are still prepared"
        );
    }

    #[cfg(unix)]
    #[test]
    fn default_worker_bootstrap_prepares_generated_proof_imports() {
        check_generated_proof_bootstrap(false);
    }

    #[cfg(unix)]
    #[test]
    fn explicit_worker_bootstrap_prepares_generated_proof_imports() {
        check_generated_proof_bootstrap(true);
    }

    /// `--evidence` reaches the parsed config unchanged, and only applies
    /// alongside `--core`: an `Invalid` build runs no solver and has no
    /// evidence to keep, so naming a destination for it would promise
    /// something that mode cannot produce.
    #[test]
    fn evidence_is_accepted_with_core_and_reaches_the_config() {
        let config = parse_certificate_build_arguments(&args(&[
            "--input",
            "Example0001",
            "--destination",
            "DESTINATION",
            "--core",
            "ROWS.json",
            "--evidence",
            "EVIDENCE_DIR",
        ]))
        .expect("--evidence is accepted alongside --core");
        assert_eq!(config.evidence, Some(PathBuf::from("EVIDENCE_DIR")));
    }

    #[test]
    fn evidence_is_refused_outside_core_mode() {
        let error = parse_certificate_build_arguments(&args(&[
            "--input",
            "Example0001",
            "--destination",
            "DESTINATION",
            "--counterexample",
            "RECORD.json",
            "--evidence",
            "EVIDENCE_DIR",
        ]))
        .unwrap_err();
        assert!(
            error.contains("--evidence applies to --core only"),
            "{error}"
        );

        let error = parse_certificate_build_arguments(&args(&[
            "--input",
            "Example0001",
            "--destination",
            "DESTINATION",
            "--witness",
            "WITNESS.json",
            "--evidence",
            "EVIDENCE_DIR",
        ]))
        .unwrap_err();
        assert!(
            error.contains("--evidence applies to --core only"),
            "{error}"
        );
    }

    #[test]
    fn evidence_requires_a_value() {
        let error = parse_certificate_build_arguments(&args(&[
            "--input",
            "Example0001",
            "--destination",
            "DESTINATION",
            "--core",
            "ROWS.json",
            "--evidence",
        ]))
        .unwrap_err();
        assert_eq!(error, "--evidence requires a value");
    }

    #[test]
    fn absent_evidence_defaults_to_none() {
        let config = parse_certificate_build_arguments(&args(&[
            "--input",
            "Example0001",
            "--destination",
            "DESTINATION",
            "--core",
            "ROWS.json",
        ]))
        .expect("a --core build without --evidence is otherwise complete");
        assert_eq!(config.evidence, None);
    }
}
