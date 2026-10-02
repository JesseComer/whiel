//! End-to-end durable fixed-ambient certificate construction.
//!
//! [`build_certificate`] drives the whole pipeline described in
//! `Whiel/Synthesis/FrameworkII/FixedAmbient/CertificateEmitter.lean`'s
//! module doc comment from a bound solver context to a checked-in-shaped
//! `Certificate/` tree: it emits the pure plan
//! ([`super::certificate_ops::emit_certificate`]), runs the pinned
//! leancheck Vampire on every opaque problem, packages each raw proof
//! ([`super::certificate_ops::package_proof`]), stages every artifact under
//! a private working directory, typechecks the whole staged tree against a
//! throwaway `olean` overlay (never the real checkout), moves the staged
//! solver-evidence subtree out to a caller-supplied directory (or drops it),
//! and only then promotes the result. Every step fails closed and the
//! staging directory is always removed, on success or failure. No scripting
//! interpreter is ever invoked; the only child processes this module
//! launches are pinned CaDiCaL, `lake` and `lean`
//! (the pinned leancheck Vampire itself is launched by
//! [`super::leancheck::LeancheckRun`]).

use std::collections::BTreeMap;
use std::num::NonZeroUsize;
use std::path::{Path, PathBuf};
use std::process::Stdio;
use std::sync::Arc;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};
use std::{fmt, io};

use serde::{Deserialize, Serialize};
use serde_json::Value;
use tokio::io::AsyncReadExt;
use tokio::process::Command;

use crate::encoding::bytes_sha256;
use crate::failure::FailureReport;
use crate::runtime::owned_path::{OwnedDirectory, PathLease, entry_exists, rename_noreplace};
use crate::runtime::{CancellationToken, SolverAdmission};

use super::certificate_ops::{
    CertificateBundle, CertificateBundleShape, CertificateJob, EMPTY_DOMAIN_ENCODING_VERSION,
    FrameworkIICertificateError,
};
use super::counterexample::FrozenCounterexampleRecord;
use super::freeze::CoreFreezeError;
use super::leancheck::{
    LeancheckError, LeancheckProfile, LeancheckRun, PinnedKernelLratCadical, PinnedLeancheckVampire,
};
use super::production::ProofSearchProfile;
use super::proof_transform::{
    KernelSatContext, ProofTransformError, ProofTransformId, ProofTransformRecord,
    apply_proof_transforms,
    canonical::{SolverMeasurements, normalize_telescope_order, solver_measurements},
    lrat::PreparedLratSolver,
    mark_rolled_back, plan_proof_sat,
};
use super::snapshot::LeveledCandidateSnapshot;
use super::solver::FrameworkIISolverContext;

/// The exact axiom set every certificate theorem must depend on and no
/// other: Lean's standard "classical, choice-using, quotient" trio.
const STD3_AXIOMS: [&str; 3] = ["propext", "Classical.choice", "Quot.sound"];

// One wall budget for an optional candidate's compilation.
const PROOF_CANDIDATE_BUDGET: Duration = Duration::from_secs(60);

const BUILD_SETTINGS_FILE: &str = "certificate-build-settings.json";

// Diagnostic events only: a killed process leaves a start without a finish,
// which the harness reports as incomplete instead of a successful duration.
struct PhaseLog<'a> {
    id: u64,
    phase: &'static str,
    subject: String,
    started: Instant,
    cancellation: &'a CancellationToken,
    finished: bool,
}

impl<'a> PhaseLog<'a> {
    fn new(phase: &'static str, subject: &str, cancellation: &'a CancellationToken) -> Self {
        static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
        let log = Self {
            id: NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
            phase,
            subject: subject.into(),
            started: Instant::now(),
            cancellation,
            finished: false,
        };
        eprintln!(
            "certificate phase: {}",
            serde_json::json!({
                "version": 1, "id": log.id, "phase": phase, "subject": subject, "event": "start"
            })
        );
        log
    }

    fn finish(&mut self, outcome: &str) {
        self.finished = true;
        eprintln!(
            "certificate phase: {}",
            serde_json::json!({
                "version": 1, "id": self.id, "phase": self.phase, "subject": self.subject,
                "event": "finish", "outcome": outcome,
                "elapsed_seconds": self.started.elapsed().as_secs_f64()
            })
        );
    }

    fn success(&mut self) {
        self.finish("success");
    }
}

impl Drop for PhaseLog<'_> {
    fn drop(&mut self) {
        if !self.finished {
            self.finish(if self.cancellation.should_stop() {
                "cancelled"
            } else {
                "failure"
            });
        }
    }
}

pub(crate) fn certificate_solver_jobs(requested: NonZeroUsize) -> Result<NonZeroUsize, String> {
    resolve_solver_jobs(std::env::var("WHIEL_CERTIFICATE_SOLVER_JOBS"), requested)
}

impl CertificateBuildRequest<'_> {
    pub(crate) fn configured_solver_jobs(requested: NonZeroUsize) -> Result<NonZeroUsize, String> {
        certificate_solver_jobs(requested)
    }
}

fn resolve_solver_jobs(
    value: Result<String, std::env::VarError>,
    requested: NonZeroUsize,
) -> Result<NonZeroUsize, String> {
    match value {
        Err(std::env::VarError::NotPresent) => Ok(requested),
        Ok(value) => value
            .parse::<NonZeroUsize>()
            .map_err(|_| "WHIEL_CERTIFICATE_SOLVER_JOBS must be a positive integer".into()),
        Err(error) => Err(format!("WHIEL_CERTIFICATE_SOLVER_JOBS: {error}")),
    }
}

async fn record_build_settings(
    stage_src: &Path,
    bundle: &CertificateBundle,
    solver_jobs: usize,
    admission: &SolverAdmission,
) -> Result<(), CertificateBuildError> {
    let settings = serde_json::json!({
        "kind": "whiel_certificate_build_settings",
        "version": 1,
        "solver_jobs": solver_jobs,
        "preparation_packaging_cpu_worker_limit": admission.policy().max_cpu_workers(),
        "compiler": if lake_compilation_enabled()? { "lake" } else { "sequential" },
        "lean_num_threads": std::env::var("LEAN_NUM_THREADS").ok(),
        "pipeline": "solve-and-package-then-compile",
    });
    eprintln!("certificate settings: {settings}");
    // This is diagnostic provenance, never proof evidence. It remains in
    // the promoted tree even when disposable Vampire artifacts are stripped.
    let relative = format!(
        "{}/{BUILD_SETTINGS_FILE}",
        bundle
            .certificate_module
            .rsplit_once('.')
            .expect("validated certificate module")
            .0
            .replace('.', "/")
    );
    let bytes = serde_json::to_vec_pretty(&settings)
        .map_err(|error| CertificateBuildError::Io(error.to_string()))?;
    write_staged(stage_src, &relative, &bytes).await
}

// Certifier-only controls. The default preserves the sequential backend;
// a zero candidate timeout delegates the whole-attempt limit to the caller.
fn lake_compilation_enabled() -> Result<bool, CertificateBuildError> {
    match std::env::var("WHIEL_CERTIFICATE_COMPILER").as_deref() {
        Err(std::env::VarError::NotPresent) | Ok("sequential") => Ok(false),
        Ok("lake") => Ok(true),
        _ => Err(CertificateBuildError::Io(
            "WHIEL_CERTIFICATE_COMPILER must be sequential or lake".into(),
        )),
    }
}

fn candidate_budget() -> Result<Option<Duration>, CertificateBuildError> {
    match std::env::var("WHIEL_CERTIFICATE_CANDIDATE_TIMEOUT_SECONDS") {
        Err(std::env::VarError::NotPresent) => {
            Ok((!lake_compilation_enabled()?).then_some(PROOF_CANDIDATE_BUDGET))
        }
        Ok(value) => value
            .parse::<u64>()
            .map(|seconds| (seconds != 0).then(|| Duration::from_secs(seconds)))
            .map_err(|_| {
                CertificateBuildError::Io(
                    "WHIEL_CERTIFICATE_CANDIDATE_TIMEOUT_SECONDS must be a nonnegative integer"
                        .into(),
                )
            }),
        Err(error) => Err(CertificateBuildError::Io(error.to_string())),
    }
}

// ------------------------------------------------------------
// Request And Hooks
// ------------------------------------------------------------

/// One request to build a durable certificate tree from a frozen Core.
pub struct CertificateBuildRequest<'a> {
    pub solver: &'a FrameworkIISolverContext,
    pub admission: &'a SolverAdmission,
    pub snapshot: Arc<LeveledCandidateSnapshot>,
    pub pinned: &'a PinnedLeancheckVampire,
    /// Chooses one [`LeancheckProfile`] per job. Called exactly once per
    /// job; there is deliberately no retry of the same job under another
    /// profile.
    pub profiles: &'a dyn Fn(&CertificateJob) -> Result<LeancheckProfile, CoreFreezeError>,
    pub time_limit_seconds: u64,
    /// How many jobs of this build may be solved and packaged at once.
    ///
    /// `1` keeps the original strictly sequential bundle-order pass, which
    /// is what the `certificate build` CLI and every regeneration of a
    /// checked-in tree use. Pass 7.5f's certification of a frozen Core
    /// raises it, and the result mapping stays deterministic either way:
    /// receipts are indexed by bundle position, not by completion order,
    /// and a failed build reports the failure of the lowest-numbered job.
    pub concurrency: NonZeroUsize,
    pub repository_root: PathBuf,
    /// Parent directory under which a fresh, uniquely named staging
    /// directory is created and (always) removed again.
    pub staging_root: PathBuf,
    /// Where the finished `Certificate/` tree is moved on success. Must
    /// not already exist.
    pub destination: PathBuf,
    /// Where the staged solver-evidence subtree (per-job `problem.p` and
    /// normalized `leancheck.lean`) is moved just before the `Certificate`
    /// tree is promoted. `None` drops it instead: nothing under it is
    /// promoted or kept anywhere.
    ///
    /// Must lie outside both `staging_root` and `destination`; a path that
    /// already exists is refused
    /// ([`CertificateBuildError::EvidenceDestinationExists`]) rather than
    /// merged into or overwritten. The evidence move happens before the
    /// tree is promoted: if promotion then fails, the evidence directory
    /// this build just created is removed again (best effort), so a retry
    /// starts clean.
    pub evidence_destination: Option<PathBuf>,
    pub cancellation: &'a CancellationToken,
    /// Test-only staging-directory mutation hooks; see
    /// [`CertificateBuildHooks`]. Compiled only under the `test-hooks`
    /// feature (see that type's doc comment), so this field does not exist
    /// — and cannot be set to inject tampering into a real build — in an
    /// ordinary release build.
    #[cfg(feature = "test-hooks")]
    pub hooks: CertificateBuildHooks,
}

/// One request to build a durable `Invalid` certificate tree from a frozen
/// counterexample record.
///
/// There is no `pinned`, `profiles`, or `time_limit_seconds` here because
/// there is nothing to solve: an `Invalid` certificate is closed by a kernel
/// decision over the frozen instance and its frozen fuel, so the bundle
/// carries no proof jobs and no solver ever runs.
pub struct InvalidCertificateBuildRequest<'a> {
    pub solver: &'a FrameworkIISolverContext,
    pub admission: &'a SolverAdmission,
    /// The record the search froze when Lean validated the counterexample.
    pub record: &'a FrozenCounterexampleRecord,
    pub repository_root: PathBuf,
    /// Parent directory under which a fresh, uniquely named staging
    /// directory is created and (always) removed again.
    pub staging_root: PathBuf,
    /// Where the finished `Certificate/` tree is moved on success. Must
    /// not already exist.
    pub destination: PathBuf,
    pub cancellation: &'a CancellationToken,
    /// Test-only staging-directory mutation hooks; see
    /// [`CertificateBuildHooks`].
    #[cfg(feature = "test-hooks")]
    pub hooks: CertificateBuildHooks,
}

/// A staging-directory mutation hook: see [`CertificateBuildHooks`].
#[cfg(feature = "test-hooks")]
pub type CertificateBuildHook = Box<dyn Fn(&Path) + Send + Sync>;

/// A per-module staging mutation hook, taking the stage and the dotted
/// module about to be compiled: see [`CertificateBuildHooks`].
#[cfg(feature = "test-hooks")]
pub type CertificateModuleHook = Box<dyn Fn(&Path, &str) + Send + Sync>;

#[cfg(feature = "test-hooks")]
pub type CertificateCandidateBudgetHook = Box<dyn Fn(&str, usize) -> Duration + Send + Sync>;

/// Test-only hooks that mutate the staging directory between build stages.
///
/// Every callback is a no-op by default. Production callers never set
/// these; they exist so tests can inject tampering, build failures, and
/// wrong-theorem-type scenarios without hand-authoring certificate source.
/// Compiled only under the `test-hooks` feature, which `cargo test` enables
/// automatically (see `Cargo.toml`'s self dev-dependency) and an ordinary
/// `cargo build --release` never does, so this fixture seam is absent from
/// release binaries entirely rather than merely undocumented.
#[cfg(feature = "test-hooks")]
#[doc(hidden)]
#[derive(Default)]
pub struct CertificateBuildHooks {
    /// Runs after every emitted artifact has been written to the stage.
    pub after_emit: Option<CertificateBuildHook>,
    /// Runs after every job has been solved and packaged.
    pub after_solve: Option<CertificateBuildHook>,
    /// Runs after the Input overlay is in place, before any `lean` build.
    pub before_build: Option<CertificateBuildHook>,
    /// Runs before each initial module and each new fallback candidate,
    /// with the dotted module about to be compiled. Lake's initial hooks
    /// run before its batch starts. It is the only seam that
    /// can reach a candidate the gate staged itself, so it is what a test
    /// uses to exhaust a chain.
    pub before_module_compile: Option<CertificateModuleHook>,
    /// Overrides the compile-plus-audit budget for a module and zero-based
    /// candidate attempt. Overrides the certifier's configured limit.
    pub candidate_budget: Option<CertificateCandidateBudgetHook>,
}

// ------------------------------------------------------------
// Receipt
// ------------------------------------------------------------

/// Durable evidence of one solved and packaged certificate job.
#[derive(Clone, Debug)]
pub struct CertificateJobReceipt {
    pub id: String,
    /// The job's own role, as Lean emitted it: `initialization`,
    /// `maintenance` (the step condition), or `termination`.
    pub role: String,
    /// The job's position in the bundle's canonical `2N+1` order.
    pub ordinal: u64,
    /// The Core clause this job's condition is about; absent exactly for
    /// the termination job.
    pub clause_id: Option<u64>,
    /// The level the clause is frozen at; absent for the termination job.
    pub level: Option<u64>,
    pub profile: LeancheckProfile,
    pub invocation_identity: Value,
    /// The verbatim solver stdout. It carries the four volatile comment
    /// lines and is therefore *not* what gets staged; this digest names
    /// the bytes the solver actually produced, and
    /// [`Self::canonical_sha256`] names the file kept beside the problem.
    pub raw_sha256: String,
    /// The canonical text, which is what stays staged under
    /// `VampireArtifacts/jobs/<job>/leancheck.lean` while the build runs —
    /// evidence, moved out to a caller-supplied directory or dropped before
    /// the tree is promoted (see
    /// [`CertificateBuildRequest::evidence_destination`]): the raw stdout
    /// after line-ending normalization, the volatile solver lines out, the
    /// certificate resource policy in, the hygiene check, and the
    /// emitter's own import/section checks. It is also the last candidate
    /// the compile gate's chain can retreat to — except on a job whose
    /// AVATAR refutation the kernel-SAT step replaced, where the chain
    /// stops above it.
    pub canonical_sha256: String,
    /// The text actually handed to `packageProof`, after every applied
    /// rewrite. Equal to `canonical_sha256` when nothing was rewritten or
    /// when the compile gate rolled a candidate back.
    pub transformed_sha256: String,
    /// Every rewrite that ran, in the one fixed order, with its outcome.
    pub transforms: Vec<ProofTransformRecord>,
    pub packaged_sha256: String,
    pub elapsed: Duration,
    /// What the dropped volatile comment lines measured. Recorded here
    /// and in the certificate's own `timing.csv` (at the tree root, always
    /// promoted) precisely because it may not be published inside a
    /// module: it changes between two runs of the same problem.
    pub measurements: SolverMeasurements,
    /// Wall clock of the whole transformation pipeline for this job.
    pub transform_elapsed: Duration,
    /// Wall clock of the `lean` invocation that compiled this job's
    /// published proof module during preparation — the accepted candidate
    /// where the compile gate walked the chain, not the rejected ones.
    /// `None` if the module never reached the compile loop.
    pub proof_module_lean_elapsed: Option<Duration>,
    /// Wall clock of the one `lean` invocation that compiled this job's
    /// reconstruction module.
    pub reconstruction_lean_elapsed: Option<Duration>,
}

impl CertificateJobReceipt {
    /// Record that the compile gate rejected a candidate and packaged the
    /// next one down the chain instead.
    ///
    /// Only the rewrites *that candidate gave up* are marked rolled back,
    /// so a job whose slice was rejected but whose projection still
    /// stands says exactly that.
    fn record_transform_fallback(&mut self, candidate: &PackagedCandidate) {
        self.transformed_sha256 = candidate.text_sha256.clone();
        self.packaged_sha256 = candidate.packaged_sha256.clone();
        mark_rolled_back(&mut self.transforms, &candidate.dropped);
    }
}

/// Complete durable evidence of one finished certificate build.
///
/// Rust never persists this by itself; the caller decides where (and
/// whether) to write it.
#[derive(Clone, Debug)]
pub struct CertificateBuildReceipt {
    pub input_identity: Value,
    pub scope_identity: Value,
    pub snapshot_identity: Value,
    pub jobs: Vec<CertificateJobReceipt>,
    pub lean_binary: PathBuf,
    pub lake_lean_path_digest: String,
    pub axioms: Vec<String>,
    pub destination: PathBuf,
    /// The root certificate module the theorem lives in, exactly as Lean
    /// declared it. Carried so a later revalidation of the promoted tree
    /// (Pass 7.5g) elaborates the same declaration rather than guessing one
    /// from the tree's file names.
    pub certificate_module: String,
    /// The theorem the tree closes, exactly as Lean declared it.
    pub certificate_theorem: String,
    /// Which target that theorem was elaborated at.
    pub shape: CertificateBundleShape,
}

// ------------------------------------------------------------
// Build
// ------------------------------------------------------------

/// Build one durable certificate tree, failing closed at every step.
///
/// See the module doc comment for the full pipeline. The staging
/// directory under `request.staging_root` is always removed before this
/// returns, whether it succeeds, fails, or is cancelled; no leancheck
/// Vampire or `lean` child survives a failed or cancelled run.
pub async fn build_certificate(
    request: CertificateBuildRequest<'_>,
) -> Result<CertificateBuildReceipt, CertificateBuildError> {
    let _lease = certificate_destination_lease(&request.destination)?;
    build_certificate_unleased(request, None).await
}

/// Internal builds may use an absent child of an exclusively owned attempt
/// parent instead of leaving a persistent output lock inside that private tree.
pub(crate) async fn build_certificate_in_owned_directory(
    request: CertificateBuildRequest<'_>,
    parent: &OwnedDirectory,
) -> Result<CertificateBuildReceipt, CertificateBuildError> {
    check_owned_destination(parent, &request.destination)?;
    build_certificate_unleased(request, Some(parent.path())).await
}

/// `owning_private_root` is the exclusively owned attempt parent a build
/// through [`build_certificate_in_owned_directory`] builds under (the
/// campaign's private candidate tree); `None` for the public
/// [`build_certificate`] entry, which owns no such parent.
async fn build_certificate_unleased(
    request: CertificateBuildRequest<'_>,
    owning_private_root: Option<&Path>,
) -> Result<CertificateBuildReceipt, CertificateBuildError> {
    if entry_exists(&request.destination)
        .map_err(|error| CertificateBuildError::Io(format!("inspect destination: {error}")))?
    {
        return Err(CertificateBuildError::DestinationExists(
            request.destination.clone(),
        ));
    }
    check_evidence_destination(
        request.evidence_destination.as_deref(),
        &request.staging_root,
        &request.destination,
        owning_private_root,
    )?;
    let stage = StageGuard::new(fresh_stage_dir(&request.staging_root)?);
    run_build(&request, stage.path()).await
}

/// Refuse an evidence destination this build cannot use: one that already
/// exists, one that lies inside the staging tree it would be moved out of,
/// or one that lies inside (or contains) the certificate destination it
/// would be promoted beside.
///
/// Checked before anything is built, by plain path containment — the same
/// discipline [`check_owned_destination`] uses for the private-builder
/// capability, not a filesystem-identity check. `evidence_destination` is
/// always the calling process's own configuration, never untrusted input
/// crossing a trust boundary.
fn check_evidence_destination(
    evidence_destination: Option<&Path>,
    staging_root: &Path,
    destination: &Path,
    owning_private_root: Option<&Path>,
) -> Result<(), CertificateBuildError> {
    let Some(evidence_destination) = evidence_destination else {
        return Ok(());
    };
    if entry_exists(evidence_destination).map_err(|error| {
        CertificateBuildError::Io(format!(
            "inspect evidence destination {}: {error}",
            evidence_destination.display()
        ))
    })? {
        return Err(CertificateBuildError::EvidenceDestinationExists(
            evidence_destination.to_path_buf(),
        ));
    }
    // P3's third clause: the evidence directory must lie outside the
    // campaign's candidate private tree too, not only the staging tree it
    // is moved out of and the certificate destination it is promoted
    // beside. `owning_private_root` is that private tree's own exclusively
    // owned root when this build runs under one (`Some`, from
    // `build_certificate_in_owned_directory`) and absent for the public
    // `build_certificate` entry, which owns no such tree.
    let mut conflicts = vec![staging_root, destination];
    if let Some(private_root) = owning_private_root {
        conflicts.push(private_root);
    }
    for other in conflicts {
        if paths_conflict(evidence_destination, other) {
            return Err(CertificateBuildError::EvidenceDestinationConflict {
                evidence_destination: evidence_destination.to_path_buf(),
                conflicting_with: other.to_path_buf(),
            });
        }
    }
    Ok(())
}

/// Absolutize a path against the current directory if it is relative, then
/// resolve `.` and `..` components lexically, without touching the
/// filesystem: the paths [`paths_conflict`] compares frequently do not
/// exist yet, so this is not a canonicalization and a symlink is never
/// resolved. That is acceptable here — `evidence_destination` and the
/// paths it is checked against are always the calling process's own
/// configuration, never untrusted input crossing a trust boundary — and
/// necessary, because a lexical `./`- or `..`-bearing path must still be
/// recognized as the same location as its normalized form.
fn normalize_lexically(path: &Path) -> PathBuf {
    let absolute = if path.is_absolute() {
        path.to_path_buf()
    } else {
        std::env::current_dir()
            .map(|current| current.join(path))
            .unwrap_or_else(|_| path.to_path_buf())
    };
    let mut normalized = PathBuf::new();
    for component in absolute.components() {
        match component {
            std::path::Component::CurDir => {}
            std::path::Component::ParentDir => {
                normalized.pop();
            }
            other => normalized.push(other.as_os_str()),
        }
    }
    normalized
}

/// Whether one path lies inside, contains, or equals the other, after
/// lexically normalizing both (see [`normalize_lexically`]).
fn paths_conflict(left: &Path, right: &Path) -> bool {
    let left = normalize_lexically(left);
    let right = normalize_lexically(right);
    left == right || left.starts_with(&right) || right.starts_with(&left)
}

/// Build one durable `Invalid` certificate tree from a frozen counterexample
/// record, failing closed at every step.
///
/// The pipeline is [`build_certificate`]'s with its whole solver stage
/// removed: Lean emits the zero-job bundle, every staged file is compiled,
/// and `Check.lean` elaborates the *negated* input triple
/// (`¬ Whiel.HoareValid inputPre inputCmd inputPost`) before the same exact
/// std3 axiom audit runs and the tree is promoted.
pub async fn build_invalid_certificate(
    request: InvalidCertificateBuildRequest<'_>,
) -> Result<CertificateBuildReceipt, CertificateBuildError> {
    let _lease = certificate_destination_lease(&request.destination)?;
    build_invalid_certificate_unleased(request).await
}

pub(crate) async fn build_invalid_certificate_in_owned_directory(
    request: InvalidCertificateBuildRequest<'_>,
    parent: &OwnedDirectory,
) -> Result<CertificateBuildReceipt, CertificateBuildError> {
    check_owned_destination(parent, &request.destination)?;
    build_invalid_certificate_unleased(request).await
}

async fn build_invalid_certificate_unleased(
    request: InvalidCertificateBuildRequest<'_>,
) -> Result<CertificateBuildReceipt, CertificateBuildError> {
    if entry_exists(&request.destination)
        .map_err(|error| CertificateBuildError::Io(format!("inspect destination: {error}")))?
    {
        return Err(CertificateBuildError::DestinationExists(
            request.destination.clone(),
        ));
    }
    let stage = StageGuard::new(fresh_stage_dir(&request.staging_root)?);
    run_invalid_build(&request, stage.path()).await
}

fn certificate_destination_lease(path: &Path) -> Result<PathLease, CertificateBuildError> {
    PathLease::acquire(path).map_err(|error| {
        CertificateBuildError::Io(format!(
            "acquire certificate destination ownership of {}: {error}",
            path.display()
        ))
    })
}

fn check_owned_destination(
    parent: &OwnedDirectory,
    destination: &Path,
) -> Result<(), CertificateBuildError> {
    if destination.parent() != Some(parent.path()) || destination.file_name().is_none() {
        return Err(CertificateBuildError::Io(
            "private certificate destination is not an immediate child of its owned directory"
                .into(),
        ));
    }
    Ok(())
}

/// Which target the staged tree's `Check.lean` must elaborate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CertificateTarget {
    /// `Whiel.HoareValid inputPre inputCmd inputPost`.
    Positive,
    /// `¬ Whiel.HoareValid inputPre inputCmd inputPost`.
    Negated,
}

impl CertificateTarget {
    fn of_shape(shape: CertificateBundleShape) -> Self {
        match shape {
            CertificateBundleShape::Valid => Self::Positive,
            CertificateBundleShape::Invalid => Self::Negated,
        }
    }

    fn shape(self) -> CertificateBundleShape {
        match self {
            Self::Positive => CertificateBundleShape::Valid,
            Self::Negated => CertificateBundleShape::Invalid,
        }
    }

    fn check_source(self, certificate_module: &str, namespace: &str, theorem: &str) -> String {
        let negation = match self {
            Self::Positive => "",
            Self::Negated => "¬ ",
        };
        format!(
            "import {certificate_module}\n\
             example : {negation}Whiel.HoareValid {namespace}.inputPre {namespace}.inputCmd \
             {namespace}.inputPost := {theorem}\n\
             #print axioms {theorem}\n"
        )
    }
}

/// Removes its staging directory tree on drop, whether `build_certificate`
/// returns normally, is cancelled and its future dropped early, or panics.
/// Removal failure is logged, never swallowed, since a leaked staging
/// directory can otherwise accumulate silently across runs.
struct StageGuard {
    path: PathBuf,
}

impl StageGuard {
    fn new(path: PathBuf) -> Self {
        Self { path }
    }

    fn path(&self) -> &Path {
        &self.path
    }
}

/// Set this variable to keep a build's staging tree after it ends, so a
/// failed job's problem and solver output can be inspected.
pub const KEEP_STAGE_VARIABLE: &str = "WHIEL_KEEP_CERTIFICATE_STAGE";

impl Drop for StageGuard {
    fn drop(&mut self) {
        if std::env::var_os(KEEP_STAGE_VARIABLE).is_some_and(|value| !value.is_empty()) {
            eprintln!(
                "keeping certificate build staging directory {} ({KEEP_STAGE_VARIABLE} is set)",
                self.path.display()
            );
            return;
        }
        if let Err(error) = std::fs::remove_dir_all(&self.path)
            && error.kind() != io::ErrorKind::NotFound
        {
            eprintln!(
                "warning: failed to remove certificate build staging directory {}: {error}",
                self.path.display()
            );
        }
    }
}

/// Attempts [`fresh_stage_dir`] makes before giving up on a colliding
/// candidate name. Collisions require the same process to hit the exact
/// same nanosecond-resolution clock reading twice, which the monotonic
/// counter alone already rules out; this bound only guards against a
/// pathologically unlucky clock, never an expected retry path.
const FRESH_STAGE_DIR_ATTEMPTS: u32 = 8;

/// Create and return a freshly, exclusively created staging directory under
/// `staging_root`, with its `src` and `olean` subdirectories in place.
///
/// Uses `create_dir` (which fails if the target already exists) rather than
/// `create_dir_all` on the unique leaf, so a name collision is detected
/// instead of silently reusing another run's directory. The candidate name
/// combines the process id, a nanosecond clock reading, and a per-process
/// monotonic counter for uniqueness across concurrent calls in one process.
fn fresh_stage_dir(staging_root: &Path) -> Result<PathBuf, CertificateBuildError> {
    static STAGE_DIR_COUNTER: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

    let mut last_collision = None;
    for _ in 0..FRESH_STAGE_DIR_ATTEMPTS {
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_err(|error| CertificateBuildError::Io(format!("read system clock: {error}")))?
            .as_nanos();
        let ordinal = STAGE_DIR_COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let stage = staging_root.join(format!(
            "whiel_certificate_build_{}_{nanos}_{ordinal}",
            std::process::id()
        ));
        match OwnedDirectory::create(stage.clone()) {
            Ok(owned) => {
                std::fs::create_dir_all(stage.join("src")).map_err(|error| {
                    CertificateBuildError::Io(format!("create {}: {error}", stage.display()))
                })?;
                std::fs::create_dir_all(stage.join("olean")).map_err(|error| {
                    CertificateBuildError::Io(format!("create {}: {error}", stage.display()))
                })?;
                return Ok(owned.retain());
            }
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
                last_collision = Some(stage);
            }
            Err(error) => {
                return Err(CertificateBuildError::Io(format!(
                    "create {}: {error}",
                    stage.display()
                )));
            }
        }
    }
    Err(CertificateBuildError::Io(format!(
        "create a fresh staging directory under {}: exhausted {FRESH_STAGE_DIR_ATTEMPTS} \
         attempts, last collision at {}",
        staging_root.display(),
        last_collision
            .expect("the loop only exits here after at least one collision")
            .display()
    )))
}

async fn run_build(
    request: &CertificateBuildRequest<'_>,
    stage: &Path,
) -> Result<CertificateBuildReceipt, CertificateBuildError> {
    let cancellation = request.cancellation;
    let stage_src = stage.join("src");

    check_cancelled(cancellation)?;
    let concurrency =
        certificate_solver_jobs(request.concurrency).map_err(CertificateBuildError::Io)?;

    // (1) Emit the pure certificate plan and stage every artifact.
    let mut emit_phase = PhaseLog::new("emit", "valid", cancellation);
    let bundle = request
        .solver
        .emit_certificate(&request.snapshot, request.admission, cancellation)
        .await
        .map_err(map_certificate_error)?;
    emit_phase.success();
    let identity = cross_check_bundle_identity(request.solver, &bundle)?;
    stage_bundle_artifacts(&stage_src, &bundle).await?;
    record_build_settings(&stage_src, &bundle, concurrency.get(), request.admission).await?;
    #[cfg(feature = "test-hooks")]
    if let Some(hook) = request.hooks.after_emit.as_ref() {
        hook(stage);
    }
    check_cancelled(cancellation)?;

    // (2) Solve, transform and package every job, in bundle order. Each
    //     rewritten module keeps its pre-transformation packaging as the
    //     candidate the compile gate in (3) may fall back to — except an
    //     AVATAR job, whose canonical text still carries `bv_decide`.
    //
    //     The kernel-SAT step's solver is resolved once here, before any
    //     job runs, and lent to all of them: the lock read, the digest
    //     check and the version check are the same for every job, and a
    //     build whose pinned CaDiCaL is missing or wrong fails before it
    //     launches a single Vampire rather than after thirteen.
    let kernel_lrat = PinnedKernelLratCadical::from_lock(&request.repository_root)
        .map_err(|error| CertificateBuildError::KernelLratCadical(error.to_string()))?;
    let solved = solve_and_package_bundle(
        request,
        concurrency,
        &stage_src,
        &stage.join("kernel-sat"),
        &kernel_lrat,
        &bundle,
    )
    .await?;
    let mut jobs = Vec::with_capacity(solved.len());
    let mut empty_resources = Vec::with_capacity(solved.len());
    let mut proof_fallbacks: BTreeMap<String, (usize, ProofFallback)> = BTreeMap::new();
    for (index, job) in solved.into_iter().enumerate() {
        if let Some(fallback) = job.fallback {
            proof_fallbacks.insert(fallback.dotted_module.clone(), (index, fallback));
        }
        empty_resources.push(job.empty_resource);
        jobs.push(job.receipt);
    }
    write_empty_resource_manifest(&stage_src, &identity.canonical_id, empty_resources).await?;
    #[cfg(feature = "test-hooks")]
    if let Some(hook) = request.hooks.after_solve.as_ref() {
        hook(stage);
    }
    check_cancelled(cancellation)?;

    finish_certificate_build(FinishBuildRequest {
        bundle: &bundle,
        identity: &identity,
        jobs,
        proof_fallbacks,
        target: CertificateTarget::Positive,
        core: Some(&request.snapshot),
        repository_root: &request.repository_root,
        destination: &request.destination,
        evidence_destination: request.evidence_destination.as_deref(),
        cancellation,
        stage,
        #[cfg(feature = "test-hooks")]
        hooks: &request.hooks,
    })
    .await
}

async fn run_invalid_build(
    request: &InvalidCertificateBuildRequest<'_>,
    stage: &Path,
) -> Result<CertificateBuildReceipt, CertificateBuildError> {
    let cancellation = request.cancellation;
    let stage_src = stage.join("src");

    check_cancelled(cancellation)?;

    // (1) Emit the zero-job `Invalid` plan from the frozen record alone and
    //     stage every artifact. `emit_invalid_certificate` has already
    //     rejected any bundle that carries a job, a Core, or a solver
    //     artifact, so there is nothing to solve and nothing to package.
    let mut emit_phase = PhaseLog::new("emit", "invalid", cancellation);
    let bundle = request
        .solver
        .emit_invalid_certificate(request.record, request.admission, cancellation)
        .await
        .map_err(map_certificate_error)?;
    emit_phase.success();
    let identity = cross_check_bundle_identity(request.solver, &bundle)?;
    stage_bundle_artifacts(&stage_src, &bundle).await?;
    record_build_settings(&stage_src, &bundle, 0, request.admission).await?;
    #[cfg(feature = "test-hooks")]
    if let Some(hook) = request.hooks.after_emit.as_ref() {
        hook(stage);
    }
    check_cancelled(cancellation)?;
    #[cfg(feature = "test-hooks")]
    if let Some(hook) = request.hooks.after_solve.as_ref() {
        hook(stage);
    }
    check_cancelled(cancellation)?;

    finish_certificate_build(FinishBuildRequest {
        bundle: &bundle,
        identity: &identity,
        jobs: Vec::new(),
        proof_fallbacks: BTreeMap::new(),
        target: CertificateTarget::Negated,
        core: None,
        repository_root: &request.repository_root,
        destination: &request.destination,
        // An `Invalid` certificate runs no solver, so it stages no
        // evidence subtree at all — there is nothing to move.
        evidence_destination: None,
        cancellation,
        stage,
        #[cfg(feature = "test-hooks")]
        hooks: &request.hooks,
    })
    .await
}

/// The task identity a certificate tree is named and referenced by.
struct BundleIdentity {
    canonical_id: String,
    input_namespace: String,
}

/// The task identity Rust already validated when binding the solver context
/// (see `bind_fixed_ambient_framework_ii`) is the trusted source for the
/// canonical id and namespace used to name and reference the certificate
/// tree; the bundle's own `input_identity` is Lean-worker-issued and merely
/// echoed back, so it is cross-checked against the bound task's identity
/// rather than trusted directly.
fn cross_check_bundle_identity(
    solver: &FrameworkIISolverContext,
    bundle: &CertificateBundle,
) -> Result<BundleIdentity, CertificateBuildError> {
    let task_identity = solver.scope().task_identity();
    let canonical_id = task_identity.canonical_id().to_string();
    let input_namespace = task_identity.namespace().to_string();
    let bundle_canonical_id = extract_str(&bundle.input_identity, "canonical_id")?;
    let bundle_namespace = extract_str(&bundle.input_identity, "namespace")?;
    if bundle_canonical_id != canonical_id || bundle_namespace != input_namespace {
        return Err(CertificateBuildError::IdentityMismatch {
            bundle_canonical_id: bundle_canonical_id.to_string(),
            bundle_namespace: bundle_namespace.to_string(),
            task_canonical_id: canonical_id,
            task_namespace: input_namespace,
        });
    }
    Ok(BundleIdentity {
        canonical_id,
        input_namespace,
    })
}

async fn stage_bundle_artifacts(
    stage_src: &Path,
    bundle: &CertificateBundle,
) -> Result<(), CertificateBuildError> {
    for artifact in &bundle.artifacts {
        write_staged(
            stage_src,
            &artifact.relative_path,
            artifact.contents.as_bytes(),
        )
        .await?;
    }
    Ok(())
}

/// One request to finish an already-emitted-and-staged certificate build:
/// see [`finish_certificate_build`].
struct FinishBuildRequest<'a> {
    bundle: &'a CertificateBundle,
    identity: &'a BundleIdentity,
    jobs: Vec<CertificateJobReceipt>,
    /// The unrewritten packaging of every proof module a transformation
    /// changed, by dotted module name, with the index of its job receipt.
    /// The compile gate consumes each entry at most once.
    proof_fallbacks: BTreeMap<String, (usize, ProofFallback)>,
    target: CertificateTarget,
    /// The frozen Core a `Valid` build certifies, written beside the tree as
    /// `Core.json`; an `Invalid` build has none.
    core: Option<&'a LeveledCandidateSnapshot>,
    repository_root: &'a Path,
    destination: &'a Path,
    /// See [`CertificateBuildRequest::evidence_destination`]. Always
    /// `None` for an `Invalid` build, which stages no evidence subtree.
    evidence_destination: Option<&'a Path>,
    cancellation: &'a CancellationToken,
    stage: &'a Path,
    #[cfg(feature = "test-hooks")]
    hooks: &'a CertificateBuildHooks,
}

/// Overlay the compiled Input module, compile every staged certificate
/// module in import order, elaborate `Check.lean` at the bundle's declared
/// target, audit the axiom closure, and promote the tree.
async fn finish_certificate_build(
    request: FinishBuildRequest<'_>,
) -> Result<CertificateBuildReceipt, CertificateBuildError> {
    let FinishBuildRequest {
        bundle,
        identity,
        mut jobs,
        mut proof_fallbacks,
        target,
        core,
        repository_root,
        destination,
        evidence_destination,
        cancellation,
        stage,
        #[cfg(feature = "test-hooks")]
        hooks,
    } = request;
    let stage_src = stage.join("src");
    let stage_olean = stage.join("olean");
    let canonical_id = identity.canonical_id.as_str();

    // (3) Overlay the compiled Input module and resolve the toolchain.
    overlay_input_module(repository_root, &stage_olean, canonical_id, cancellation).await?;
    #[cfg(feature = "test-hooks")]
    if let Some(hook) = hooks.before_build.as_ref() {
        hook(stage);
    }
    check_cancelled(cancellation)?;
    let certificate_root = stage_src
        .join("Benchmark")
        .join(canonical_id)
        .join("Certificate");
    read_certificate_tree(
        &certificate_root,
        Some(&format!("Benchmark.{canonical_id}.Certificate")),
    )?;
    let lean_binary = lake_env_which_lean(repository_root, cancellation).await?;
    let base_lean_path = lake_env_lean_path(repository_root, cancellation).await?;
    // The same effective search path revalidation builds: the staging
    // overlay is the only source for this certificate's own namespace, so a
    // bundle that fails to carry one of its own modules cannot compile
    // against the repository's stale `olean` for it. The two paths run the
    // identical four checks, which is why a `--core` build publishes on its
    // own fresh check without a separate revalidation receipt.
    let lean_path = format!(
        "{}:{}",
        stage_olean.display(),
        shadowed_lean_path(&base_lean_path, &stage.join("shadow"), canonical_id)?
    );

    // Compile every staged certificate module in import order.
    let certificate_prefix = format!("Benchmark.{canonical_id}.Certificate");
    let modules = collect_staged_modules(bundle, &stage_src, &certificate_prefix)?;
    for (importer, (_, imports)) in &modules {
        for module in imports {
            if !modules.contains_key(module) {
                return Err(CertificateBuildError::UnresolvedCertificateImport {
                    importer: importer.clone(),
                    module: module.clone(),
                });
            }
        }
    }
    let order = topological_order(&modules)?;
    let use_lake = lake_compilation_enabled()?;
    let candidate_budget = candidate_budget()?;
    let mut repair_proofs = std::collections::BTreeSet::new();
    if use_lake {
        #[cfg(feature = "test-hooks")]
        if let Some(hook) = hooks.before_module_compile.as_ref() {
            for dotted in &order {
                hook(stage, dotted);
            }
        }
        let built = compile_with_lake(
            &lean_binary,
            &lean_path,
            &stage_src,
            &stage_olean,
            &certificate_prefix,
            &order,
            cancellation,
        )
        .await;
        if let Err(error) = &built
            && !matches!(error, CertificateBuildError::Build { .. })
        {
            return Err(built.expect_err("non-build error branch"));
        }
        for (dotted, (job_index, _)) in &proof_fallbacks {
            let job = &bundle.jobs[*job_index];
            let output = stage_olean
                .join(&job.proof_module_relative_path)
                .with_extension("olean");
            // Presence is only a repair hint, never acceptance evidence.
            // A complete successful Lake build remains mandatory below.
            if !output.is_file() {
                repair_proofs.insert(dotted.clone());
            }
        }
        if repair_proofs.is_empty() {
            built?;
        } else {
            eprintln!(
                "certificate compiler: Lake candidate repair: {} modules",
                repair_proofs.len()
            );
            if let Err(error) = built {
                eprintln!("{error}");
            }
        }
    }
    // Repairs are checked separately. They never overwrite Lake's outputs
    // or satisfy the final checks; Lake must rebuild the selected sources.
    let repair_olean = stage.join("repair-olean");
    let repair_lean_path = format!("{}:{lean_path}", repair_olean.display());
    let compile_olean = if use_lake {
        &repair_olean
    } else {
        &stage_olean
    };
    let compile_path = if use_lake {
        &repair_lean_path
    } else {
        &lean_path
    };
    // Which job each compiled module belongs to, so the `lean` wall of
    // one module lands in the right row of `timing.csv`.
    let mut proof_module_jobs: BTreeMap<&str, usize> = BTreeMap::new();
    let mut reconstruction_module_jobs: BTreeMap<&str, usize> = BTreeMap::new();
    for (index, job) in bundle.jobs.iter().enumerate() {
        proof_module_jobs.insert(job.proof_module.as_str(), index);
        reconstruction_module_jobs.insert(job.reconstruction_module.as_str(), index);
    }
    for dotted in order
        .iter()
        .filter(|dotted| !use_lake || repair_proofs.contains(*dotted))
    {
        let (relative_path, _) = &modules[dotted];
        check_cancelled(cancellation)?;
        #[cfg(feature = "test-hooks")]
        if !use_lake && let Some(hook) = hooks.before_module_compile.as_ref() {
            hook(stage, dotted);
        }
        let candidate_gate = proof_fallbacks
            .get(dotted)
            .map(|(job_index, _)| ProofCandidateGate {
                lean_binary: &lean_binary,
                lean_path: compile_path,
                stage_src: &stage_src,
                stage_olean: compile_olean,
                job: &bundle.jobs[*job_index],
                budget: candidate_budget,
                #[cfg(feature = "test-hooks")]
                budget_hook: hooks.candidate_budget.as_ref(),
            });
        // Missing Lake output does not prove this candidate ran: a failed
        // dependency may have blocked it. Retain candidate zero until Lake
        // supplies reliable identity-bound failure evidence.
        let compiled = if let Some(gate) = candidate_gate.as_ref() {
            gate.run(0, cancellation).await
        } else {
            compile_certificate_module(
                &lean_binary,
                compile_path,
                &stage_src,
                compile_olean,
                relative_path,
                dotted,
                cancellation,
            )
            .await
        };
        // The compile gate for optional transformations. Axiom rejection
        // happens only at the final theorem and never selects a fallback.
        // A type error or compilation timeout advances private
        // preparation to the next packaged candidate down that job's
        // chain — one optional rewrite given up at a time, `LocalPrenex`
        // before `ClauseProjection`, with the kernel-checked AVATAR
        // refutation kept in all of them — and the receipt records
        // exactly the steps given up. The walk closes once: nothing later
        // re-runs it. A module with no candidates left, and a module that
        // never had one, fails the build as it did before any
        // transformation existed.
        match compiled {
            Ok(elapsed) => {
                if !use_lake && let Some(index) = proof_module_jobs.get(dotted.as_str()) {
                    jobs[*index].proof_module_lean_elapsed = Some(elapsed);
                } else if !use_lake
                    && let Some(index) = reconstruction_module_jobs.get(dotted.as_str())
                {
                    jobs[*index].reconstruction_lean_elapsed = Some(elapsed);
                }
            }
            Err(rejection @ CertificateBuildError::Build { .. }) => {
                let Some((job_index, fallback)) = proof_fallbacks.remove(dotted) else {
                    return Err(rejection);
                };
                let mut rejection = rejection;
                let mut accepted = false;
                for (attempt, candidate) in fallback.candidates.iter().enumerate() {
                    write_staged(&stage_src, relative_path, candidate.packaged.as_bytes()).await?;
                    #[cfg(feature = "test-hooks")]
                    if let Some(hook) = hooks.before_module_compile.as_ref() {
                        hook(stage, dotted);
                    }
                    match candidate_gate
                        .as_ref()
                        .expect("a fallback belongs to a proof candidate gate")
                        .run(attempt + 1, cancellation)
                        .await
                    {
                        Ok(elapsed) => {
                            jobs[job_index].record_transform_fallback(candidate);
                            if !use_lake {
                                jobs[job_index].proof_module_lean_elapsed = Some(elapsed);
                            }
                            accepted = true;
                            break;
                        }
                        Err(next @ CertificateBuildError::Build { .. }) => rejection = next,
                        Err(error) => return Err(error),
                    }
                }
                if !accepted {
                    // Every candidate was rejected, so the last rejection
                    // is the build's: there is no proof of this job left
                    // to publish.
                    return Err(rejection);
                }
            }
            Err(error) => return Err(error),
        }
    }

    if use_lake && !repair_proofs.is_empty() {
        // One authoritative rebuild, never an unbounded retry loop.
        // --rehash forces source/dependency hashes to notice the repairs.
        compile_with_lake(
            &lean_binary,
            &lean_path,
            &stage_src,
            &stage_olean,
            &certificate_prefix,
            &order,
            cancellation,
        )
        .await?;
    }

    // (4) Build Check.lean and verify the theorem type and the axiom set.
    let mut check_phase = PhaseLog::new("final_check", &bundle.certificate_theorem, cancellation);
    let check_relative = format!("Benchmark/{canonical_id}/Certificate/Check.lean");
    let check_source = target.check_source(
        &bundle.certificate_module,
        &identity.input_namespace,
        &bundle.certificate_theorem,
    );
    write_staged(&stage_src, &check_relative, check_source.as_bytes()).await?;
    check_cancelled(cancellation)?;
    let check_module = format!("{certificate_prefix}.Check");
    let stdout = compile_check_module(
        &lean_binary,
        &lean_path,
        &stage_src,
        &stage_olean,
        &check_relative,
        &check_module,
        cancellation,
    )
    .await?;
    let axioms = parse_print_axioms(&stdout)?;
    let found: std::collections::BTreeSet<&str> = axioms.iter().map(String::as_str).collect();
    let expected: std::collections::BTreeSet<&str> = STD3_AXIOMS.into_iter().collect();
    if found != expected {
        return Err(CertificateBuildError::Axioms { found: axioms });
    }
    check_phase.success();
    // `Check.lean` is a build-time scratch module (it exists only to force
    // Lean to elaborate the theorem's exact type and print its axioms); it
    // is never part of the emitted certificate shape, so it does not ride
    // along into the destination.
    let check_source_path = safe_relative_join(&stage_src, &check_relative)?;
    std::fs::remove_file(&check_source_path).map_err(|error| {
        CertificateBuildError::Io(format!("remove {}: {error}", check_source_path.display()))
    })?;

    // The timing record. Everything the four volatile solver lines used
    // to publish inside a module — and the `lean` wall of each module
    // besides — is written once, here, at the certificate tree's own
    // root: it is not a `.lean` file, so neither the compile loop above
    // nor the revalidation source digest reads it, and — unlike the
    // solver evidence — it is small and always promoted with the tree, so
    // a reviewer who wants the numbers has them without a receipt.
    //
    // An `Invalid` certificate runs no solver at all — it is closed by a
    // kernel decision on a frozen instance — so it has no timing record,
    // rather than a header with nothing under it.
    if !jobs.is_empty() {
        write_staged(
            &stage_src,
            &format!("Benchmark/{canonical_id}/Certificate/{TIMING_CSV_NAME}"),
            render_timing_csv(&jobs).as_bytes(),
        )
        .await?;
    }

    let certificate_root = stage_src
        .join("Benchmark")
        .join(canonical_id)
        .join("Certificate");

    // (5) Move the staged solver-evidence subtree out of the tree that is
    // about to be promoted, or drop it if the caller asked for nothing.
    // Nothing the kernel checks imports it and revalidation already skips
    // it, so it is retained only for a reviewer who wants to rerun a job —
    // never for anything a later step of this build depends on. An
    // `Invalid` build stages no evidence at all (`jobs` is empty), so
    // there is nothing to move or drop.
    //
    // `evidence_cleanup` is armed the moment evidence actually leaves the
    // tree and disarmed only once the tree is fully promoted: an ordinary
    // early return, a promotion failure, an interrupted future, or an
    // unwind between those two points all remove what was already moved
    // out through the same `Drop`, rather than each such exit needing its
    // own explicit cleanup call.
    let mut evidence_cleanup = EvidenceCleanupGuard::disarmed();
    if !jobs.is_empty() {
        let evidence_source = certificate_root.join(CERTIFICATE_EVIDENCE_SUBTREE);
        match evidence_destination {
            Some(evidence_destination) => {
                move_evidence_out(&evidence_source, evidence_destination).await?;
                evidence_cleanup = EvidenceCleanupGuard::armed(evidence_destination.to_path_buf());
            }
            None => {
                tokio::fs::remove_dir_all(&evidence_source)
                    .await
                    .map_err(|error| {
                        CertificateBuildError::Io(format!(
                            "remove {}: {error}",
                            evidence_source.display()
                        ))
                    })?;
            }
        }
    }

    // (6) Promote the staged Certificate tree to its destination.
    if entry_exists(destination)
        .map_err(|error| CertificateBuildError::Io(format!("inspect destination: {error}")))?
    {
        return Err(CertificateBuildError::DestinationExists(
            destination.to_path_buf(),
        ));
    }
    if let Some(parent) = destination.parent() {
        tokio::fs::create_dir_all(parent).await.map_err(|error| {
            CertificateBuildError::Io(format!("create {}: {error}", parent.display()))
        })?;
    }
    check_cancelled(cancellation)?;
    // Recheck the persistent bytes after compilation and evidence stripping.
    read_certificate_tree(&certificate_root, Some(&certificate_prefix))?;
    promote_certificate_tree(&certificate_root, destination).await?;
    // The tree is fully promoted: any evidence this build already moved
    // out is authorized to stay, and no later failure removes it.
    evidence_cleanup.disarm();

    // (7) Record the frozen Core beside the tree, so the slim record alone
    // regenerates the certificate later.
    if let Some(snapshot) = core {
        write_core_record(destination, snapshot).await?;
    }

    Ok(CertificateBuildReceipt {
        input_identity: bundle.input_identity.clone(),
        scope_identity: bundle.scope_identity.clone(),
        snapshot_identity: bundle.snapshot_identity.clone(),
        jobs,
        lean_binary,
        lake_lean_path_digest: bytes_sha256(base_lean_path.as_bytes()),
        axioms,
        destination: destination.to_path_buf(),
        certificate_module: bundle.certificate_module.clone(),
        certificate_theorem: bundle.certificate_theorem.clone(),
        shape: target.shape(),
    })
}

/// The `kind` of the frozen Core rows record, `Core.json`.
pub const CORE_ROWS_KIND: &str = "whiel_framework_ii_core_rows";
/// The version of the frozen Core rows record.
pub const CORE_ROWS_VERSION: u64 = 1;
/// The file name of the frozen Core rows record, beside `Certificate/`.
pub const CORE_RECORD_NAME: &str = "Core.json";

/// The frozen Core as the rows record `certificate build --core` consumes:
/// one row per committed clause in canonical order, its level and its
/// canonical source. Protected precondition rows are left out: they are
/// installed from the input again whenever the Core is re-admitted.
pub fn core_record_text(snapshot: &LeveledCandidateSnapshot) -> String {
    let records = snapshot.records();
    let rows: Vec<Value> = snapshot
        .canonical_order()
        .iter()
        .filter_map(|id| {
            let record = records.get(id)?;
            if record.is_protected() {
                return None;
            }
            let level = snapshot.level_of(*id)?;
            Some(serde_json::json!({
                "level": level.get(),
                "source": record.formula().canonical_source(),
            }))
        })
        .collect();
    let value = serde_json::json!({
        "kind": CORE_ROWS_KIND,
        "version": CORE_ROWS_VERSION,
        "rows": rows,
    });
    let mut text = serde_json::to_string_pretty(&value).expect("Core rows serialize");
    text.push('\n');
    text
}

/// Write `Core.json` next to the promoted `Certificate/` tree. A record
/// already there with the same rows is left alone; a different one is a
/// conflict, never replaced, exactly as a conflicting counterexample record
/// is treated.
pub(super) async fn write_core_record(
    destination: &Path,
    snapshot: &LeveledCandidateSnapshot,
) -> Result<(), CertificateBuildError> {
    let Some(parent) = destination.parent() else {
        return Ok(());
    };
    let path = parent.join(CORE_RECORD_NAME);
    let text = core_record_text(snapshot);
    if entry_exists(&path).map_err(|error| {
        CertificateBuildError::Io(format!("inspect {}: {error}", path.display()))
    })? {
        let existing = tokio::fs::read_to_string(&path).await.map_err(|error| {
            CertificateBuildError::Io(format!("read {}: {error}", path.display()))
        })?;
        // The same rows in another layout are the same record.
        let same = serde_json::from_str::<Value>(&existing)
            .ok()
            .is_some_and(|value| value == serde_json::from_str::<Value>(&text).unwrap());
        if same {
            return Ok(());
        }
        return Err(CertificateBuildError::Io(format!(
            "{} already holds a different Core record; it is not replaced",
            path.display()
        )));
    }
    tokio::fs::write(&path, text)
        .await
        .map_err(|error| CertificateBuildError::Io(format!("write {}: {error}", path.display())))
}

/// The per-certificate timing record, written beside the solver evidence.
const TIMING_CSV_NAME: &str = "timing.csv";

/// The timing record's own header, pinned so a reader can check it.
const TIMING_CSV_HEADER: &str = "job,profile,vampire_elapsed_s,vampire_peak_mb,transform_s,proof_module_lean_s,\
     reconstruction_lean_s";

/// Render the certificate's `timing.csv`: one row per job, in the
/// bundle's own `2N+1` order, with an empty cell wherever a measurement
/// was not taken rather than a zero that would read as one.
fn render_timing_csv(jobs: &[CertificateJobReceipt]) -> String {
    fn cell(value: Option<f64>) -> String {
        value.map(|value| format!("{value:.3}")).unwrap_or_default()
    }
    let mut rendered = String::from(TIMING_CSV_HEADER);
    rendered.push('\n');
    for job in jobs {
        rendered.push_str(&format!(
            "{},{},{},{},{},{},{}\n",
            job.id,
            match job.profile.profile() {
                ProofSearchProfile::Direct => "direct",
                ProofSearchProfile::Casc2025 => "casc_2025",
            },
            cell(job.measurements.vampire_elapsed_seconds),
            cell(job.measurements.vampire_peak_memory_mb),
            cell(Some(job.transform_elapsed.as_secs_f64())),
            cell(job.proof_module_lean_elapsed.map(|d| d.as_secs_f64())),
            cell(job.reconstruction_lean_elapsed.map(|d| d.as_secs_f64())),
        ));
    }
    rendered
}

/// Solve and package every job of `bundle`, honouring
/// the resolved concurrency and mapping results deterministically.
///
/// At concurrency `1` this retains the sequential fail-fast
/// bundle-order pass. Every job's profile is resolved before any
/// task is spawned — a profile failure must not leave a supervisor running
/// behind it — then every job is dispatched onto its own task under a
/// permit semaphore, results are written into their bundle position rather
/// than their completion position, and the reported failure is the one of
/// the lowest-numbered failed job, so two runs of one fixture fail
/// identically however the launches interleave. Each task rechecks the
/// cancellation just before its own launch, exactly as the sequential pass
/// does. Every dispatched job is awaited before this returns, on success,
/// on failure, and on a join error alike, so no leancheck child outlives
/// the build.
async fn solve_and_package_bundle(
    request: &CertificateBuildRequest<'_>,
    concurrency: NonZeroUsize,
    stage_src: &Path,
    kernel_sat_root: &Path,
    kernel_lrat: &PinnedKernelLratCadical,
    bundle: &CertificateBundle,
) -> Result<Vec<SolvedJob>, CertificateBuildError> {
    let cancellation = request.cancellation;
    check_cancelled(cancellation)?;
    let profiles = resolve_job_profiles(&bundle.jobs, request.profiles)?;

    // Every per-job authority is a cheap handle to shared state, so each
    // task owns its own clone and nothing is borrowed across the spawn.
    let futures = bundle.jobs.iter().zip(profiles).map(|(job, profile)| {
        let solver = request.solver.clone();
        let admission = request.admission.clone();
        let pinned = request.pinned.clone();
        let cancellation = cancellation.clone();
        let stage_src = stage_src.to_path_buf();
        let kernel_sat_root = kernel_sat_root.to_path_buf();
        let kernel_lrat = kernel_lrat.clone();
        let job = job.clone();
        let time_limit_seconds = request.time_limit_seconds;
        async move {
            solve_and_package_job_owned(SolveJobRequest {
                solver: &solver,
                admission: &admission,
                pinned: &pinned,
                kernel_lrat: &kernel_lrat,
                cancellation: &cancellation,
                stage_src: &stage_src,
                kernel_sat_root: &kernel_sat_root,
                job: &job,
                profile,
                time_limit_seconds,
            })
            .await
        }
    });
    run_certificate_jobs(futures, concurrency, cancellation).await
}

// The same coordinator handles one and many jobs. A permit covers the
// complete future, including all sequential solver and packaging work.
async fn run_certificate_jobs<T, F>(
    futures: impl IntoIterator<Item = F>,
    concurrency: NonZeroUsize,
    cancellation: &CancellationToken,
) -> Result<Vec<T>, CertificateBuildError>
where
    T: Send + 'static,
    F: std::future::Future<Output = Result<T, CertificateBuildError>> + Send + 'static,
{
    if concurrency.get() == 1 {
        let mut results = Vec::new();
        for work in futures {
            check_cancelled(cancellation)?;
            results.push(work.await?);
        }
        return Ok(results);
    }
    let permits = Arc::new(tokio::sync::Semaphore::new(concurrency.get()));
    let mut tasks = tokio::task::JoinSet::new();
    let mut count = 0;
    for (index, work) in futures.into_iter().enumerate() {
        count += 1;
        let permits = Arc::clone(&permits);
        let cancellation = cancellation.clone();
        tasks.spawn(async move {
            let outcome = tokio::select! {
                biased;
                _ = cancellation.cancelled() => Err(CertificateBuildError::Cancelled),
                permit = permits.acquire() => match permit {
                    Ok(_permit) => match check_cancelled(&cancellation) {
                        Ok(()) => work.await,
                        Err(error) => Err(error),
                    },
                    Err(_) => Err(CertificateBuildError::Cancelled),
                },
            };
            (index, outcome)
        });
    }

    let mut results: Vec<Option<Result<T, CertificateBuildError>>> =
        (0..count).map(|_| None).collect();
    while let Some(joined) = tasks.join_next().await {
        match joined {
            Ok((index, outcome)) => results[index] = Some(outcome),
            Err(error) => {
                // A panicked or aborted task. Stop the rest and drain the
                // set, so every task that is still running is awaited
                // rather than dropped with its leancheck child alive.
                cancellation.cancel();
                while tasks.join_next().await.is_some() {}
                return Err(CertificateBuildError::Io(format!(
                    "join a certificate job task: {error}"
                )));
            }
        }
    }

    let mut receipts = Vec::with_capacity(results.len());
    for (index, slot) in results.into_iter().enumerate() {
        match slot.ok_or_else(|| {
            CertificateBuildError::Io(format!("certificate job {index} produced no result"))
        })? {
            Ok(solved) => receipts.push(solved),
            Err(error) => return Err(error),
        }
    }
    Ok(receipts)
}

/// Resolve the closed profile label of every job, in bundle order, before
/// any of them is dispatched.
///
/// The concurrent path calls this before it creates its `JoinSet`, so a job
/// whose label cannot be resolved — a certificate job the frozen record does
/// not describe — fails the whole build with no task spawned at all. Doing
/// it inside the dispatch loop would leave the tasks already spawned to be
/// dropped mid-flight on the early return, and a dropped task is not an
/// awaited one: its leancheck supervisor would outlive the build.
fn resolve_job_profiles(
    jobs: &[CertificateJob],
    profiles: &dyn Fn(&CertificateJob) -> Result<LeancheckProfile, CoreFreezeError>,
) -> Result<Vec<LeancheckProfile>, CertificateBuildError> {
    let mut resolved = Vec::with_capacity(jobs.len());
    for job in jobs {
        resolved.push(
            profiles(job).map_err(|error| CertificateBuildError::ProfileSelection {
                job_id: job.id.clone(),
                source: error,
            })?,
        );
    }
    Ok(resolved)
}

/// The owned form of one job dispatch: see [`solve_and_package_bundle`].
struct SolveJobRequest<'a> {
    solver: &'a FrameworkIISolverContext,
    admission: &'a SolverAdmission,
    pinned: &'a PinnedLeancheckVampire,
    /// Resolved once per build; every job gets its own working directory
    /// under `kernel_sat_root` and its own `CadicalLratSolver` over it, so
    /// two concurrently solved jobs never share a `proof.lrat`.
    kernel_lrat: &'a PinnedKernelLratCadical,
    cancellation: &'a CancellationToken,
    stage_src: &'a Path,
    kernel_sat_root: &'a Path,
    job: &'a CertificateJob,
    profile: LeancheckProfile,
    time_limit_seconds: u64,
}

/// One solved and packaged job: its receipt, plus the less-rewritten
/// packagings held back for the compile gate.
struct SolvedJob {
    receipt: CertificateJobReceipt,
    empty_resource: EmptyResourceReceipt,
    fallback: Option<ProofFallback>,
}

/// The chain of packaged proofs one job's module may retreat to when Lean
/// rejects the fully rewritten one, most rewritten first.
///
/// Every candidate is packaged here, at solve time, while the worker is
/// still up and the job's text is still in hand; the gate itself only
/// stages and recompiles. The chain drops the optional rewrites one at a
/// time and never drops the kernel-checked AVATAR refutation, so no entry
/// in it publishes a `bv_decide` reconstruction.
struct ProofFallback {
    /// The proof module these replace, as Lean named it.
    dotted_module: String,
    candidates: Vec<PackagedCandidate>,
}

/// One packaged entry of that chain.
struct PackagedCandidate {
    /// The rewrites given up to reach it, for the receipt.
    dropped: Vec<ProofTransformId>,
    /// Digest of the *transformed* text behind this packaging, which
    /// becomes the job's `transformed_sha256` if it is the one kept.
    text_sha256: String,
    packaged: String,
    packaged_sha256: String,
}

async fn solve_and_package_job_owned(
    request: SolveJobRequest<'_>,
) -> Result<SolvedJob, CertificateBuildError> {
    let SolveJobRequest {
        solver,
        admission,
        pinned,
        kernel_lrat,
        cancellation,
        stage_src,
        kernel_sat_root,
        job,
        profile,
        time_limit_seconds,
    } = request;
    let staged_problem_path = safe_relative_join(stage_src, &job.problem_relative_path)?;
    let staged_problem_bytes = tokio::fs::read(&staged_problem_path)
        .await
        .map_err(|error| {
            CertificateBuildError::Io(format!("read {}: {error}", staged_problem_path.display()))
        })?;
    if bytes_sha256(&staged_problem_bytes) != job.problem_sha256 {
        return Err(CertificateBuildError::Tampered {
            relative_path: job.problem_relative_path.clone(),
        });
    }

    let cnf_path = safe_relative_join(stage_src, &job.empty_check.cnf_relative_path)?;
    let cnf = tokio::fs::read_to_string(&cnf_path)
        .await
        .map_err(|error| {
            CertificateBuildError::Io(format!("read {}: {error}", cnf_path.display()))
        })?;
    if bytes_sha256(cnf.as_bytes()) != job.empty_check.cnf_sha256 {
        return Err(CertificateBuildError::Tampered {
            relative_path: job.empty_check.cnf_relative_path.clone(),
        });
    }
    let deadline = Duration::from_secs(time_limit_seconds);
    let mut solver_phase = PhaseLog::new("vampire", &job.id, cancellation);
    let solved = LeancheckRun::execute(
        pinned,
        profile,
        &staged_problem_bytes,
        deadline,
        cancellation,
    )
    .await
    .map_err(|error| match error {
        LeancheckError::Cancelled => CertificateBuildError::Cancelled,
        other => CertificateBuildError::Solver {
            job_id: job.id.clone(),
            source: other,
        },
    })?;
    solver_phase.success();
    let raw_text = std::str::from_utf8(&solved.raw).map_err(|_| {
        CertificateBuildError::Io(format!(
            "certificate job {} produced leancheck output that is not valid UTF-8",
            job.id
        ))
    })?;
    // Each job has its own root, and each refute call exclusively reserves
    // its own attempt beneath it. Repeated helper IDs cannot overwrite prior
    // DIMACS/trace evidence, which remains with the stage for inspection.
    let transform_started = Instant::now();
    let mut transform_phase = PhaseLog::new("transform", &job.id, cancellation);
    let problems =
        plan_proof_sat(&job.id, raw_text).map_err(CertificateBuildError::ProofTransform)?;
    let mut traces = Vec::with_capacity(problems.len());
    for problem in problems {
        let trace = solve_cnf_with_cadical(
            kernel_lrat.path(),
            kernel_lrat.arguments(),
            &kernel_sat_root.join(&job.id),
            &format!("step-{}", problem.step_id),
            &problem.cnf_source,
            deadline,
            cancellation,
        )
        .await?;
        traces.push((problem, trace));
    }
    let kernel_sat_solver = PreparedLratSolver::new(traces);
    let kernel_sat = KernelSatContext::new(&kernel_sat_solver, kernel_lrat.invocation_identity());
    // Read what the volatile lines measured before the canonical step
    // drops them; this is the only place the raw stdout still exists.
    let measurements = solver_measurements(raw_text);
    let transformed = apply_proof_transforms(&job.id, raw_text, &kernel_sat)
        .map_err(CertificateBuildError::ProofTransform)?;
    let transform_elapsed = transform_started.elapsed();
    transform_phase.success();
    // The *canonical* text is the retained evidence, not the verbatim
    // stdout: a published file may not carry a line whose value changes
    // between two runs of one problem, or the tree stops being a thing a
    // rebuild can reproduce. Everything a transformation targets is still
    // in it — it is the text Vampire emitted, minus the four volatile
    // comments and the two linter options, with the resource prelude at
    // the certificate's own policy.
    write_staged(
        stage_src,
        &job.leancheck_output_relative_path,
        transformed.canonical.as_bytes(),
    )
    .await?;

    // This paired proof stays inside the same complete-job permit. Its
    // resource bytes remain in the portable tree when Vampire evidence leaves.
    let empty_trace = solve_cnf_with_cadical(
        kernel_lrat.path(),
        kernel_lrat.arguments(),
        &kernel_sat_root.join(&job.id),
        &format!("{}-empty-domain", job.id),
        &cnf,
        deadline,
        cancellation,
    )
    .await?;
    write_staged(
        stage_src,
        &job.empty_check.lrat_relative_path,
        empty_trace.as_bytes(),
    )
    .await?;
    let empty_resource = EmptyResourceReceipt::from_job(job, bytes_sha256(empty_trace.as_bytes()))?;

    let mut package_phase = PhaseLog::new("package", &job.id, cancellation);
    let package = |text: String, extra_imports: Vec<String>| async move {
        solver
            .package_proof(
                &job.id,
                &job.proof_namespace,
                text.as_bytes(),
                &extra_imports,
                admission,
                cancellation,
            )
            .await
            .map_err(|error| match error {
                FrameworkIICertificateError::Cancelled => CertificateBuildError::Cancelled,
                FrameworkIICertificateError::Failure(report) => CertificateBuildError::Package {
                    job_id: job.id.clone(),
                    report,
                },
            })
    };

    let packaged = package(
        transformed.transformed.clone(),
        transformed.extra_imports.clone(),
    )
    .await?;
    // A rewritten module is only a *candidate* until it compiles, so
    // every proof the gate may retreat to is packaged here, beside it,
    // while the worker is up: the chain gives up one optional rewrite at
    // a time rather than abandoning the whole rewrite on the first
    // rejection. A job whose AVATAR refutation became a kernel-checked
    // LRAT proof has no candidate below that step — the emitted text
    // closes its helpers by `bv_decide` and may not be published at all —
    // so such a job simply runs out of candidates and fails its build.
    let mut candidates = Vec::with_capacity(transformed.fallback_candidates.len());
    for candidate in &transformed.fallback_candidates {
        let packaged = package(candidate.text.clone(), candidate.extra_imports.clone()).await?;
        candidates.push(PackagedCandidate {
            dropped: candidate.dropped.clone(),
            text_sha256: candidate.sha256.clone(),
            packaged: packaged.packaged,
            packaged_sha256: packaged.packaged_sha256,
        });
    }
    let fallback = (!candidates.is_empty()).then(|| ProofFallback {
        dotted_module: job.proof_module.clone(),
        candidates,
    });
    write_staged(
        stage_src,
        &job.proof_module_relative_path,
        packaged.packaged.as_bytes(),
    )
    .await?;

    package_phase.success();
    Ok(SolvedJob {
        empty_resource,
        receipt: CertificateJobReceipt {
            id: job.id.clone(),
            role: job.role.clone(),
            ordinal: job.ordinal,
            clause_id: job.clause_id,
            level: job.level,
            profile,
            invocation_identity: solved.invocation_identity,
            raw_sha256: solved.raw_sha256,
            canonical_sha256: transformed.canonical_sha256,
            transformed_sha256: transformed.transformed_sha256,
            transforms: transformed.transforms,
            packaged_sha256: packaged.packaged_sha256,
            elapsed: solved.elapsed,
            measurements,
            transform_elapsed,
            proof_module_lean_elapsed: None,
            reconstruction_lean_elapsed: None,
        },
        fallback,
    })
}

// This transport accepts opaque CNF bytes; Lean owns their meaning. M7's
// empty-domain evidence uses the same managed child boundary as AVATAR.
async fn solve_cnf_with_cadical(
    executable: &Path,
    arguments: &[String],
    working_root: &Path,
    label: &str,
    cnf_source: &str,
    limit: Duration,
    cancellation: &CancellationToken,
) -> Result<String, CertificateBuildError> {
    check_cancelled(cancellation)?;
    let directory = OwnedDirectory::fresh(working_root, label)
        .map_err(|error| {
            CertificateBuildError::KernelLratCadical(format!("reserve {label}: {error}"))
        })?
        .retain();
    let cnf_path = directory.join("input.cnf");
    let lrat_path = directory.join("proof.lrat");
    tokio::fs::write(&cnf_path, cnf_source)
        .await
        .map_err(|error| {
            CertificateBuildError::KernelLratCadical(format!("write {label} CNF: {error}"))
        })?;
    let mut command = Command::new(executable);
    command
        .arg(&cnf_path)
        .arg(&lrat_path)
        .args(arguments)
        .current_dir(&directory);
    for (name, _) in std::env::vars_os() {
        if name
            .to_string_lossy()
            .to_uppercase()
            .starts_with("CADICAL_")
        {
            command.env_remove(name);
        }
    }
    command.env("LANG", "C").env("LC_ALL", "C");
    let local = CancellationToken::new();
    let work = run_supervised(command, &local);
    tokio::pin!(work);
    let deadline = tokio::time::Instant::now()
        .checked_add(limit)
        .ok_or_else(|| {
            CertificateBuildError::KernelLratCadical(
                "solver deadline overflows the monotonic clock".into(),
            )
        })?;
    let mut phase = PhaseLog::new("sat", label, cancellation);
    let outcome = tokio::select! {
        biased;
        _ = cancellation.cancelled() => None,
        _ = tokio::time::sleep_until(deadline) => None,
        result = &mut work => Some(result),
    };
    let result = match outcome {
        Some(result) => result,
        None => {
            local.cancel();
            // Keep ownership until child, descendants and captures are joined.
            match work.await {
                Err(CertificateBuildError::Cancelled) | Ok(_) => {}
                Err(error) => return Err(error),
            }
            check_cancelled(cancellation)?;
            return Err(CertificateBuildError::KernelLratCadical(format!(
                "{label} exceeded {limit:?} solver limit"
            )));
        }
    };
    let (status, stdout, stderr) = result?;
    check_cancelled(cancellation)?;
    if tokio::time::Instant::now() >= deadline {
        return Err(CertificateBuildError::KernelLratCadical(format!(
            "{label} exceeded {limit:?} solver limit"
        )));
    }
    if status.code() != Some(20) {
        return Err(CertificateBuildError::KernelLratCadical(format!(
            "{label}: CaDiCaL exited with {:?}{}: {}",
            status.code(),
            if status.code() == Some(10) {
                " (SAT; no refutation)"
            } else {
                ""
            },
            combined_diagnostics(
                &String::from_utf8_lossy(&stdout),
                &String::from_utf8_lossy(&stderr)
            )
        )));
    }
    let trace = tokio::fs::read_to_string(lrat_path)
        .await
        .map_err(|error| {
            CertificateBuildError::KernelLratCadical(format!("read {label} LRAT: {error}"))
        })?;
    check_cancelled(cancellation)?;
    phase.success();
    Ok(trace)
}

// ------------------------------------------------------------
// Staging Filesystem Helpers
// ------------------------------------------------------------

fn safe_relative_join(base: &Path, relative: &str) -> Result<PathBuf, CertificateBuildError> {
    let relative_path = Path::new(relative);
    if relative_path.is_absolute()
        || relative_path
            .components()
            .any(|component| matches!(component, std::path::Component::ParentDir))
    {
        return Err(CertificateBuildError::Io(format!(
            "certificate relative path is not stage-relative: {relative}"
        )));
    }
    Ok(base.join(relative_path))
}

/// Write one staged certificate artifact through `tokio::fs`, so a large
/// payload (a raw leancheck proof, a packaged proof module) never blocks
/// the async executor thread it runs on.
async fn write_staged(
    stage_src: &Path,
    relative_path: &str,
    contents: &[u8],
) -> Result<(), CertificateBuildError> {
    let path = safe_relative_join(stage_src, relative_path)?;
    if let Some(parent) = path.parent() {
        tokio::fs::create_dir_all(parent).await.map_err(|error| {
            CertificateBuildError::Io(format!("create {}: {error}", parent.display()))
        })?;
    }
    tokio::fs::write(&path, contents)
        .await
        .map_err(|error| CertificateBuildError::Io(format!("write {}: {error}", path.display())))
}

/// Move the staged certificate tree to its destination with exactly one
/// rename.
///
/// `staging_root` is ordinarily a sibling of the destination (see
/// [`crate::certificate_cli`]'s default), so this is an ordinary same-
/// filesystem rename. A caller-supplied `--staging` directory can still put
/// staging on a different filesystem than the destination, in which case
/// `rename` fails with `EXDEV` — and that is refused, with the same error
/// and the same message
/// ([`CertificateBuildError::CrossesFilesystems`]) as
/// [`crate::framework2::publication`]'s own publication refusal.
///
/// There is no copy fallback. Promotion here *is* publication on the
/// `--core` path: `certificate build --core` promotes the tree the caller
/// then treats as authority, so the same rule applies as on the `Valid` and
/// `Invalid` publication paths — a copy followed by a removal is not one
/// step, and between them a partial tree stands where a complete one is
/// claimed to be. Stage on the destination's own filesystem instead.
async fn promote_certificate_tree(from: &Path, to: &Path) -> Result<(), CertificateBuildError> {
    if forced_cross_filesystem() {
        return Err(CertificateBuildError::CrossesFilesystems {
            staging: from.to_path_buf(),
            destination: to.to_path_buf(),
        });
    }
    // Promotion itself must refuse an entry that appears after the earlier
    // checks. There is no await or cancellation gap after this final syscall.
    match rename_noreplace(from, to) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
            Err(CertificateBuildError::DestinationExists(to.to_path_buf()))
        }
        Err(error) if is_cross_filesystem_rename_error(&error) => {
            Err(CertificateBuildError::CrossesFilesystems {
                staging: from.to_path_buf(),
                destination: to.to_path_buf(),
            })
        }
        Err(error) => Err(CertificateBuildError::Io(format!(
            "rename {} to {}: {error}",
            from.display(),
            to.display()
        ))),
    }
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
fn is_cross_filesystem_rename_error(error: &io::Error) -> bool {
    error.raw_os_error() == Some(libc::EXDEV)
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
fn is_cross_filesystem_rename_error(_error: &io::Error) -> bool {
    false
}

/// Whether `rename_noreplace`'s underlying syscall rejected the request
/// because the running kernel or the source filesystem does not support an
/// atomic no-replace rename at all, rather than because it found `to`
/// already there (reported through [`io::ErrorKind::AlreadyExists`]
/// instead). [`move_evidence_out`] has already confirmed `to` does not
/// exist moments before making this call, so falling back to a plain copy
/// here remains no-replace in effect: nothing about this error means two
/// writers raced, only that the flag asking for the atomic check could not
/// be honored at all.
#[cfg(target_os = "macos")]
fn is_rename_noreplace_unsupported_error(error: &io::Error) -> bool {
    error.raw_os_error() == Some(libc::ENOTSUP)
}

#[cfg(target_os = "linux")]
fn is_rename_noreplace_unsupported_error(error: &io::Error) -> bool {
    matches!(
        error.raw_os_error(),
        Some(libc::EINVAL) | Some(libc::ENOSYS)
    )
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
fn is_rename_noreplace_unsupported_error(_error: &io::Error) -> bool {
    false
}

/// Move the staged solver-evidence subtree to `to`, which
/// [`check_evidence_destination`] has already confirmed does not exist and
/// does not conflict with the staging tree, the certificate destination, or
/// an owning private tree.
///
/// Tries one rename first. Unlike [`promote_certificate_tree`], a
/// cross-filesystem `to` (a caller-supplied evidence directory can be
/// anywhere) — or one whose filesystem cannot honor an atomic no-replace
/// rename at all — falls back to a recursive copy followed by removing the
/// staged source, because evidence is never the published authority: an
/// interruption mid-copy leaves at most a missing or partial debugging
/// aid, never a half-published certificate standing where a complete one
/// is claimed to be.
async fn move_evidence_out(from: &Path, to: &Path) -> Result<(), CertificateBuildError> {
    if entry_exists(to).map_err(|error| {
        CertificateBuildError::Io(format!(
            "inspect evidence destination {}: {error}",
            to.display()
        ))
    })? {
        return Err(CertificateBuildError::EvidenceDestinationExists(
            to.to_path_buf(),
        ));
    }
    if let Some(parent) = to.parent() {
        tokio::fs::create_dir_all(parent).await.map_err(|error| {
            CertificateBuildError::Io(format!("create {}: {error}", parent.display()))
        })?;
    }
    if forced_cross_filesystem() {
        return copy_evidence_then_remove_blocking(from.to_path_buf(), to.to_path_buf()).await;
    }
    match rename_noreplace(from, to) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => Err(
            CertificateBuildError::EvidenceDestinationExists(to.to_path_buf()),
        ),
        Err(error)
            if is_cross_filesystem_rename_error(&error)
                || is_rename_noreplace_unsupported_error(&error) =>
        {
            copy_evidence_then_remove_blocking(from.to_path_buf(), to.to_path_buf()).await
        }
        Err(error) => Err(CertificateBuildError::Io(format!(
            "move {} to {}: {error}",
            from.display(),
            to.display()
        ))),
    }
}

/// Run the copy-then-remove fallback on a blocking-pool thread: the walk
/// can touch as many files as the batch has jobs, and none of that
/// synchronous I/O may block the async executor thread it would otherwise
/// run on, exactly the discipline [`write_staged`] already follows for one
/// large staged payload.
async fn copy_evidence_then_remove_blocking(
    from: PathBuf,
    to: PathBuf,
) -> Result<(), CertificateBuildError> {
    match tokio::task::spawn_blocking(move || copy_evidence_then_remove(&from, &to)).await {
        Ok(result) => result,
        Err(join_error) => Err(CertificateBuildError::Io(format!(
            "evidence copy fallback panicked: {join_error}"
        ))),
    }
}

/// The synchronous body of the fallback. Any failure here — a partial
/// recursive copy, or removing the staged source afterward — best-effort
/// removes `to` before returning: `to` was confirmed absent moments before
/// this ran, so a partial or even a fully written `to` left behind by a
/// failed attempt would otherwise refuse a retry into the same path with
/// "already exists" for a move that never actually finished.
fn copy_evidence_then_remove(from: &Path, to: &Path) -> Result<(), CertificateBuildError> {
    if let Err(error) = copy_dir_recursive(from, to) {
        remove_evidence_best_effort(to);
        return Err(error);
    }
    if let Err(error) = std::fs::remove_dir_all(from) {
        // The copy itself is complete and correct; only removing the
        // staged source failed. That source lives inside this build's own
        // staging tree, which is removed wholesale when the build ends
        // regardless of outcome, so leaving it behind costs nothing — but
        // reporting this as a failure while leaving the completed `to`
        // standing would still block a retry the same way a partial copy
        // would, so it is removed here too.
        remove_evidence_best_effort(to);
        return Err(CertificateBuildError::Io(format!(
            "remove {}: {error}",
            from.display()
        )));
    }
    Ok(())
}

/// Recursively copy `from` to `to`, the cross-filesystem fallback for
/// [`move_evidence_out`]. Every entry must be a regular file or a
/// directory, exactly as a certificate tree's own entries must be
/// ([`CertificateBuildError::NonRegularTreeEntry`]).
fn copy_dir_recursive(from: &Path, to: &Path) -> Result<(), CertificateBuildError> {
    std::fs::create_dir_all(to)
        .map_err(|error| CertificateBuildError::Io(format!("create {}: {error}", to.display())))?;
    for entry in std::fs::read_dir(from)
        .map_err(|error| CertificateBuildError::Io(format!("read {}: {error}", from.display())))?
    {
        let entry = entry.map_err(|error| {
            CertificateBuildError::Io(format!("read {}: {error}", from.display()))
        })?;
        let file_type = entry.file_type().map_err(|error| {
            CertificateBuildError::Io(format!("stat {}: {error}", entry.path().display()))
        })?;
        let target = to.join(entry.file_name());
        if file_type.is_dir() {
            copy_dir_recursive(&entry.path(), &target)?;
        } else if file_type.is_file() {
            std::fs::copy(entry.path(), &target).map_err(|error| {
                CertificateBuildError::Io(format!(
                    "copy {} to {}: {error}",
                    entry.path().display(),
                    target.display()
                ))
            })?;
        } else {
            return Err(CertificateBuildError::NonRegularTreeEntry {
                path: entry.path().display().to_string(),
            });
        }
    }
    Ok(())
}

/// Best-effort removal of an evidence directory this build already
/// created, when a later step of the same attempt fails closed.
///
/// The evidence move happens before promotion specifically so this can
/// run: a failure after it leaves no half-published `Certificate` tree
/// behind, and removing the evidence it already wrote keeps a retried
/// attempt from refusing on a leftover this one created moments before.
fn remove_evidence_best_effort(path: &Path) {
    if let Err(error) = std::fs::remove_dir_all(path)
        && error.kind() != io::ErrorKind::NotFound
    {
        eprintln!(
            "warning: a failed certificate build could not remove its evidence directory {}: \
             {error}",
            path.display()
        );
    }
}

/// Removes the evidence directory it is armed with when dropped, unless
/// [`Self::disarm`] is called first.
///
/// An explicit cleanup call at each early return cannot reach every way a
/// build can end between the evidence move and a successful promotion — an
/// interrupted future (the build's own cancellation) or an unwind never
/// runs code that was never awaited to completion. Tying the cleanup to
/// `Drop` instead covers all of them, the same discipline [`StageGuard`]
/// already uses for the whole staging tree.
struct EvidenceCleanupGuard {
    path: Option<PathBuf>,
}

impl EvidenceCleanupGuard {
    fn disarmed() -> Self {
        Self { path: None }
    }

    fn armed(path: PathBuf) -> Self {
        Self { path: Some(path) }
    }

    /// The evidence this guard was armed with is now authorized to stay:
    /// the tree it was moved out of has been fully promoted.
    fn disarm(&mut self) {
        self.path = None;
    }
}

impl Drop for EvidenceCleanupGuard {
    fn drop(&mut self) {
        if let Some(path) = self.path.take() {
            remove_evidence_best_effort(&path);
        }
    }
}

/// Whether a test has asked promotion to behave as if its staging tree and
/// destination were on different filesystems.
///
/// A second filesystem cannot be assumed on a developer machine or in CI, so
/// the refusal path is exercised by making the rename behave as the kernel
/// would — exactly as `publication.rs` does for its own refusal. Outside
/// `cfg(test)` there is no such switch and this is a constant `false`.
#[cfg(test)]
fn forced_cross_filesystem() -> bool {
    FORCED_CROSS_FILESYSTEM.with(std::cell::Cell::get)
}

#[cfg(not(test))]
fn forced_cross_filesystem() -> bool {
    false
}

#[cfg(test)]
thread_local! {
    static FORCED_CROSS_FILESYSTEM: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

// ------------------------------------------------------------
// Toolchain Resolution And Overlay
// ------------------------------------------------------------

#[cfg(any(target_os = "macos", target_os = "linux"))]
async fn overlay_input_module(
    repository_root: &Path,
    stage_olean: &Path,
    canonical_id: &str,
    cancellation: &CancellationToken,
) -> Result<(), CertificateBuildError> {
    let module_target = format!("Benchmark.{canonical_id}.Input");
    let mut command = Command::new("lake");
    command
        .current_dir(repository_root)
        .args(["build", &module_target]);
    let (status, _stdout, stderr) = run_supervised(command, cancellation).await?;
    if !status.success() {
        return Err(CertificateBuildError::Io(format!(
            "lake build {module_target} failed: {}",
            String::from_utf8_lossy(&stderr)
        )));
    }
    let source_dir = repository_root
        .join(".lake/build/lib/lean/Benchmark")
        .join(canonical_id);
    let target_dir = stage_olean.join("Benchmark").join(canonical_id);
    std::fs::create_dir_all(&target_dir).map_err(|error| {
        CertificateBuildError::Io(format!("create {}: {error}", target_dir.display()))
    })?;
    for extension in ["olean", "ilean"] {
        let source = source_dir.join(format!("Input.{extension}"));
        if !source.is_file() {
            return Err(CertificateBuildError::Io(format!(
                "missing compiled Input artifact: {}",
                source.display()
            )));
        }
        let target = target_dir.join(format!("Input.{extension}"));
        std::os::unix::fs::symlink(&source, &target).map_err(|error| {
            CertificateBuildError::Io(format!(
                "symlink {} -> {}: {error}",
                target.display(),
                source.display()
            ))
        })?;
    }
    Ok(())
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
async fn overlay_input_module(
    _repository_root: &Path,
    _stage_olean: &Path,
    _canonical_id: &str,
    _cancellation: &CancellationToken,
) -> Result<(), CertificateBuildError> {
    Err(CertificateBuildError::Io(
        "certificate builds are unsupported on this platform".to_string(),
    ))
}

async fn lake_env_which_lean(
    repository_root: &Path,
    cancellation: &CancellationToken,
) -> Result<PathBuf, CertificateBuildError> {
    let mut command = Command::new("lake");
    command
        .current_dir(repository_root)
        .args(["env", "which", "lean"]);
    let (status, stdout, stderr) = run_supervised(command, cancellation).await?;
    if !status.success() {
        return Err(CertificateBuildError::Io(format!(
            "lake env which lean failed: {}",
            String::from_utf8_lossy(&stderr)
        )));
    }
    let text = String::from_utf8_lossy(&stdout);
    let path = text
        .lines()
        .next()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .ok_or_else(|| {
            CertificateBuildError::Io("lake env which lean produced no path".to_string())
        })?;
    Ok(PathBuf::from(path))
}

async fn lake_env_lean_path(
    repository_root: &Path,
    cancellation: &CancellationToken,
) -> Result<String, CertificateBuildError> {
    let mut command = Command::new("lake");
    command
        .current_dir(repository_root)
        .args(["env", "printenv", "LEAN_PATH"]);
    let (status, stdout, stderr) = run_supervised(command, cancellation).await?;
    if !status.success() {
        return Err(CertificateBuildError::Io(format!(
            "lake env printenv LEAN_PATH failed: {}",
            String::from_utf8_lossy(&stderr)
        )));
    }
    let text = String::from_utf8_lossy(&stdout).trim().to_string();
    if text.is_empty() {
        return Err(CertificateBuildError::Io(
            "lake env printenv LEAN_PATH was empty".to_string(),
        ));
    }
    Ok(text)
}

/// The revalidation's effective module search path: `base_lean_path` with
/// every entry that carries a compiled `Benchmark/<id>/Certificate` tree
/// replaced by a shadow of itself with exactly that subtree missing.
///
/// Revalidation compiles a certificate tree's own modules from source into
/// a throwaway overlay, and the overlay is prepended to the search path.
/// Prepending alone is not enough: Lean falls through to the next entry for
/// any module the overlay does not carry, and the repository's own `.lake`
/// build directory ordinarily carries `olean` files for exactly this
/// namespace, left there by an earlier `lake build`. A tree that is missing
/// one of its own modules would then compile against that stale artifact.
/// The shadow leaves the rest of the entry — `Whiel`, `Databases`, every other
/// benchmark, and this benchmark's own compiled `Input` — reachable
/// through symlinks, so only the certificate namespace is taken away.
#[cfg(any(target_os = "macos", target_os = "linux"))]
fn shadowed_lean_path(
    base_lean_path: &str,
    shadow_root: &Path,
    canonical_id: &str,
) -> Result<String, CertificateBuildError> {
    let certificate_relative = Path::new("Benchmark")
        .join(canonical_id)
        .join("Certificate");
    let mut entries = Vec::new();
    for (ordinal, entry) in base_lean_path.split(':').enumerate() {
        if entry.is_empty() || !Path::new(entry).join(&certificate_relative).exists() {
            entries.push(entry.to_string());
            continue;
        }
        let source = Path::new(entry).canonicalize().map_err(|error| {
            CertificateBuildError::Io(format!("resolve the search-path entry {entry}: {error}"))
        })?;
        let shadow = shadow_root.join(ordinal.to_string());
        link_children_except(
            &source,
            &shadow,
            &["Benchmark", canonical_id, "Certificate"],
        )?;
        entries.push(shadow.display().to_string());
    }
    Ok(entries.join(":"))
}

/// Symlink every child of `source` into `mirror`, descending into the head
/// of `excluded` rather than linking it and dropping the last name of
/// `excluded` entirely.
#[cfg(any(target_os = "macos", target_os = "linux"))]
fn link_children_except(
    source: &Path,
    mirror: &Path,
    excluded: &[&str],
) -> Result<(), CertificateBuildError> {
    std::fs::create_dir_all(mirror).map_err(|error| {
        CertificateBuildError::Io(format!("create {}: {error}", mirror.display()))
    })?;
    let Some((head, rest)) = excluded.split_first() else {
        return Ok(());
    };
    let entries = std::fs::read_dir(source).map_err(|error| {
        CertificateBuildError::Io(format!("read {}: {error}", source.display()))
    })?;
    for entry in entries {
        let entry = entry.map_err(|error| {
            CertificateBuildError::Io(format!("read {}: {error}", source.display()))
        })?;
        let name = entry.file_name();
        let target = mirror.join(&name);
        if name.as_os_str() == *head {
            if rest.is_empty() {
                // The excluded leaf: nothing links to it and nothing
                // resolves through it.
                continue;
            }
            link_children_except(&entry.path(), &target, rest)?;
            continue;
        }
        std::os::unix::fs::symlink(entry.path(), &target).map_err(|error| {
            CertificateBuildError::Io(format!(
                "symlink {} -> {}: {error}",
                target.display(),
                entry.path().display()
            ))
        })?;
    }
    Ok(())
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
fn shadowed_lean_path(
    _base_lean_path: &str,
    _shadow_root: &Path,
    _canonical_id: &str,
) -> Result<String, CertificateBuildError> {
    Err(CertificateBuildError::Io(
        "certificate revalidation is unsupported on this platform".to_string(),
    ))
}

// ------------------------------------------------------------
// Module Compilation
// ------------------------------------------------------------

/// Lake owns the dependency scheduling. Only this tree's certificate
/// modules belong to the workspace; dependencies are prebuilt libraries in
/// the same shadowed search order used by the sequential compiler.
async fn compile_with_lake(
    lean_binary: &Path,
    lean_path: &str,
    stage_src: &Path,
    stage_olean: &Path,
    certificate_prefix: &str,
    modules: &[String],
    cancellation: &CancellationToken,
) -> Result<(), CertificateBuildError> {
    let quote = |value: &str| serde_json::to_string(value).expect("serialize string");
    let mut config = format!(
        "name = \"WhielCertificateStage\"\nbuildDir = \"..\"\nleanLibDir = {}\n\n\
         [[lean_lib]]\nname = \"CertificateStage\"\nroots = [{}]\n",
        quote(&stage_olean.to_string_lossy()),
        quote(certificate_prefix),
    );
    // Lake overrides inherited LEAN_PATH with its workspace's paths.
    // Empty local packages expose the already-built dependency directories
    // without making their sources targets or consulting a package server.
    for (index, path) in std::env::split_paths(lean_path).enumerate() {
        if path == stage_olean {
            continue;
        }
        if !path.is_absolute() {
            return Err(CertificateBuildError::Io(
                "certificate dependency paths must be absolute".into(),
            ));
        }
        let relative = format!(".certificate-deps/{index}");
        let dependency = format!(
            "name = \"prebuilt{index}\"\nbuildDir = \".\"\nleanLibDir = {}\n",
            quote(&path.to_string_lossy()),
        );
        write_staged(
            stage_src,
            &format!("{relative}/lakefile.toml"),
            dependency.as_bytes(),
        )
        .await?;
        config.push_str(&format!(
            "\n[[require]]\nname = \"prebuilt{index}\"\npath = {}\n",
            quote(&relative)
        ));
    }
    write_staged(stage_src, "lakefile.toml", config.as_bytes()).await?;
    let mut command = Command::new(lean_binary.with_file_name("lake"));
    command
        .current_dir(stage_src)
        .env("LAKE_NO_CACHE", "1")
        .env("LAKE_ARTIFACT_CACHE", "0")
        .arg("--rehash")
        .arg("build")
        .args(modules.iter().map(|module| format!("{module}:olean")));
    let mut phase = PhaseLog::new("lake", certificate_prefix, cancellation);
    let (status, stdout, stderr) = run_supervised(command, cancellation).await?;
    if !status.success() {
        return Err(CertificateBuildError::Build {
            module: "Lake certificate build".into(),
            diagnostics: combined_diagnostics(
                &String::from_utf8_lossy(&stdout),
                &String::from_utf8_lossy(&stderr),
            ),
        });
    }
    phase.success();
    eprintln!(
        "certificate compiler: Lake completed {} modules",
        modules.len()
    );
    Ok(())
}

// Only optional proof choices use this gate. Reconstruction and the final
// exact-target/exact-std3 check stay fail-fast, and revalidation never makes
// another choice. The terminal fallback still carries mandatory LRAT.
struct ProofCandidateGate<'a> {
    lean_binary: &'a Path,
    lean_path: &'a str,
    stage_src: &'a Path,
    stage_olean: &'a Path,
    job: &'a CertificateJob,
    budget: Option<Duration>,
    #[cfg(feature = "test-hooks")]
    budget_hook: Option<&'a CertificateCandidateBudgetHook>,
}

impl ProofCandidateGate<'_> {
    async fn run(
        &self,
        _attempt: usize,
        cancellation: &CancellationToken,
    ) -> Result<Duration, CertificateBuildError> {
        let mut phase = PhaseLog::new(
            "candidate",
            &format!("{}:{_attempt}", self.job.proof_module),
            cancellation,
        );
        let budget = self.budget;
        #[cfg(feature = "test-hooks")]
        let budget = self
            .budget_hook
            .map_or(budget, |hook| Some(hook(&self.job.proof_module, _attempt)));
        let Some(budget) = budget else {
            let result = self.compile(cancellation).await;
            if result.is_ok() {
                phase.success();
            }
            return result;
        };
        let local = CancellationToken::new();
        let result = run_candidate_with_budget(
            self.compile(&local),
            &local,
            cancellation,
            budget,
            &self.job.proof_module,
        )
        .await;
        if result.is_ok() {
            phase.success();
        }
        result
    }

    async fn compile(
        &self,
        cancellation: &CancellationToken,
    ) -> Result<Duration, CertificateBuildError> {
        compile_certificate_module(
            self.lean_binary,
            self.lean_path,
            self.stage_src,
            self.stage_olean,
            &self.job.proof_module_relative_path,
            &self.job.proof_module,
            cancellation,
        )
        .await
    }
}

async fn run_candidate_with_budget<T>(
    work: impl std::future::Future<Output = Result<T, CertificateBuildError>>,
    local: &CancellationToken,
    cancellation: &CancellationToken,
    budget: Duration,
    module: &str,
) -> Result<T, CertificateBuildError> {
    check_cancelled(cancellation)?;
    let deadline = tokio::time::Instant::now() + budget;
    tokio::pin!(work);
    let timed_out = tokio::select! {
        biased;
        _ = cancellation.cancelled() => false,
        _ = tokio::time::sleep_until(deadline) => true,
        result = &mut work => {
            check_cancelled(cancellation)?;
            if tokio::time::Instant::now() < deadline {
                return result;
            }
            // Even a long single poll cannot accept an expired candidate.
            return Err(candidate_timeout(module, budget));
        }
    };
    // Never abandon a child or its capture tasks by dropping the future.
    // Cancellation makes the supervisor kill/reap and join both captures.
    local.cancel();
    let _ = work.await;
    check_cancelled(cancellation)?;
    if timed_out {
        Err(candidate_timeout(module, budget))
    } else {
        Err(CertificateBuildError::Cancelled)
    }
}

fn candidate_timeout(module: &str, budget: Duration) -> CertificateBuildError {
    CertificateBuildError::Build {
        module: module.to_string(),
        diagnostics: format!("candidate compilation exceeded {budget:?} budget"),
    }
}

async fn run_lean_compile(
    lean_binary: &Path,
    lean_path: &str,
    stage_src: &Path,
    output_olean: &Path,
    source_path: &Path,
    cancellation: &CancellationToken,
) -> Result<(bool, String, String), CertificateBuildError> {
    if let Some(parent) = output_olean.parent() {
        std::fs::create_dir_all(parent).map_err(|error| {
            CertificateBuildError::Io(format!("create {}: {error}", parent.display()))
        })?;
    }
    let mut command = Command::new(lean_binary);
    command
        .env("LEAN_PATH", lean_path)
        .arg(format!("--root={}", stage_src.display()))
        .arg("-o")
        .arg(output_olean)
        .arg(source_path);
    let (status, stdout, stderr) = run_supervised(command, cancellation).await?;
    Ok((
        status.success(),
        String::from_utf8_lossy(&stdout).into_owned(),
        String::from_utf8_lossy(&stderr).into_owned(),
    ))
}

/// Compile one staged certificate module, returning the wall clock of the
/// `lean` invocation itself. That number is evidence about a machine, not
/// about the proof, so it is recorded in the build receipt and in the
/// certificate's `timing.csv` and never written into a module.
async fn compile_certificate_module(
    lean_binary: &Path,
    lean_path: &str,
    stage_src: &Path,
    stage_olean: &Path,
    relative_path: &str,
    dotted_module: &str,
    cancellation: &CancellationToken,
) -> Result<Duration, CertificateBuildError> {
    let mut phase = PhaseLog::new("compile", dotted_module, cancellation);
    let source_path = safe_relative_join(stage_src, relative_path)?;
    let output_olean = safe_relative_join(stage_olean, relative_path)?.with_extension("olean");
    let started = Instant::now();
    let (success, stdout, stderr) = run_lean_compile(
        lean_binary,
        lean_path,
        stage_src,
        &output_olean,
        &source_path,
        cancellation,
    )
    .await?;
    let elapsed = started.elapsed();
    if !success {
        return Err(CertificateBuildError::Build {
            module: dotted_module.to_string(),
            diagnostics: combined_diagnostics(&stdout, &stderr),
        });
    }
    phase.success();
    Ok(elapsed)
}

/// Build `Check.lean` and classify a failure by where it actually came
/// from. `lean` reports elaboration errors (a type mismatch between the
/// packaged proof and the input Hoare triple, in particular) on stdout, not
/// stderr, so a bare non-zero exit is not enough to tell "the certificate
/// theorem does not prove the input triple" apart from "the `lean` process
/// itself failed" (crashed, was signalled, OOM-killed, or found a staged
/// `olean` missing). Stdout carrying a `error:` diagnostic line is Lean's
/// own signal that it reached elaboration and rejected the theorem's type;
/// anything else is a process-level failure, reported as
/// [`CertificateBuildError::LeanProcess`] instead of
/// [`CertificateBuildError::WrongTheoremType`] so the two are never
/// conflated.
async fn compile_check_module(
    lean_binary: &Path,
    lean_path: &str,
    stage_src: &Path,
    stage_olean: &Path,
    relative_path: &str,
    dotted_module: &str,
    cancellation: &CancellationToken,
) -> Result<String, CertificateBuildError> {
    let source_path = safe_relative_join(stage_src, relative_path)?;
    let output_olean = safe_relative_join(stage_olean, relative_path)?.with_extension("olean");
    let (success, stdout, stderr) = run_lean_compile(
        lean_binary,
        lean_path,
        stage_src,
        &output_olean,
        &source_path,
        cancellation,
    )
    .await?;
    if !success {
        let diagnostics = combined_diagnostics(&stdout, &stderr);
        if stdout.contains("error:") {
            return Err(CertificateBuildError::WrongTheoremType { diagnostics });
        }
        return Err(CertificateBuildError::LeanProcess {
            module: dotted_module.to_string(),
            diagnostics,
        });
    }
    Ok(stdout)
}

/// Combine one `lean` invocation's stdout and stderr into one diagnostic
/// string, favoring whichever stream actually carries content.
fn combined_diagnostics(stdout: &str, stderr: &str) -> String {
    match (stdout.trim().is_empty(), stderr.trim().is_empty()) {
        (true, true) => String::new(),
        (false, true) => stdout.to_string(),
        (true, false) => stderr.to_string(),
        (false, false) => format!("stdout:\n{stdout}\nstderr:\n{stderr}"),
    }
}

// ------------------------------------------------------------
// Revalidation Of An Existing Certificate Tree
// ------------------------------------------------------------

/// One request to revalidate an existing certificate source tree.
///
/// Revalidation is the rule Pass 7.5g enforces before any source may
/// authorize a result: no tree — freshly built, cached from an earlier
/// stage of this run, or already checked in — is trusted for the bytes it
/// carries. Every module is compiled again from source into a throwaway
/// `olean` overlay, `Check.lean` is regenerated and elaborated at the
/// exact immutable-`Input.lean` declaration type, and the theorem's axiom
/// closure is audited to exactly std3. Nothing is promoted, moved, or
/// written into the tree.
pub struct CertificateRevalidationRequest<'a> {
    /// The `Certificate/` source tree to revalidate. Read only.
    pub tree: &'a Path,
    /// The benchmark the tree belongs to; its compiled `Input` module is
    /// the one overlaid.
    pub canonical_id: &'a str,
    /// The `Input.lean` declaration namespace the theorem must be stated
    /// over.
    pub input_namespace: &'a str,
    /// The root certificate module carrying the theorem.
    pub certificate_module: &'a str,
    /// The theorem the tree closes.
    pub certificate_theorem: &'a str,
    /// Which target that theorem must elaborate at.
    pub shape: CertificateBundleShape,
    pub repository_root: PathBuf,
    /// Parent directory under which a fresh staging directory is created
    /// and always removed again.
    pub staging_root: PathBuf,
    pub cancellation: &'a CancellationToken,
}

/// What one revalidation established about a certificate tree.
#[derive(Clone, Debug)]
pub struct CertificateRevalidation {
    /// Every module compiled, in the import order they were compiled in.
    pub modules: Vec<String>,
    /// The audited axiom closure: exactly std3, or this is an error.
    pub axioms: Vec<String>,
    /// The `lean` binary the revalidation actually ran.
    pub lean_binary: PathBuf,
    pub lake_lean_path_digest: String,
    /// Digest of exact module sources and required CNF/LRAT resources,
    /// including their manifest, in tree-relative path order.
    /// It names the source this result is authority for and nothing else,
    /// so the tree's solver evidence — which nothing compiles — is not in
    /// it.
    pub source_digest: String,
    /// The same digest, sorting Lean `variable` telescopes canonically
    /// while preserving every resource and manifest byte unchanged.
    ///
    /// Vampire collects generated variable names from an unordered set,
    /// so repeated proofs can have different telescope orders even on
    /// one machine. This comparison normalizes only that generated
    /// `variable` layout; the actual source and the fresh kernel check
    /// retain its original order. Equality is evidence of reproducibility
    /// modulo telescope order, not a claim that a time-limited portfolio
    /// always discovers the same proof. [`Self::source_digest`] retains
    /// the stricter byte-for-byte comparison.
    pub telescope_normalized_digest: String,
}

/// Revalidate one existing certificate source tree. See
/// [`CertificateRevalidationRequest`].
pub async fn revalidate_certificate_tree(
    request: CertificateRevalidationRequest<'_>,
) -> Result<CertificateRevalidation, CertificateBuildError> {
    if !request.tree.is_dir() {
        return Err(CertificateBuildError::Io(format!(
            "certificate tree {} is not a directory",
            request.tree.display()
        )));
    }
    let stage = StageGuard::new(fresh_stage_dir(&request.staging_root)?);
    run_revalidation(&request, stage.path()).await
}

async fn run_revalidation(
    request: &CertificateRevalidationRequest<'_>,
    stage: &Path,
) -> Result<CertificateRevalidation, CertificateBuildError> {
    let cancellation = request.cancellation;
    let canonical_id = request.canonical_id;
    let stage_src = stage.join("src");
    let stage_olean = stage.join("olean");
    let certificate_prefix = format!("Benchmark.{canonical_id}.Certificate");
    let tree_relative = format!("Benchmark/{canonical_id}/Certificate");

    check_cancelled(cancellation)?;
    let sources = read_certificate_tree(request.tree, Some(&certificate_prefix))?;
    if !sources.iter().any(|(path, _)| path.ends_with(".lean")) {
        return Err(CertificateBuildError::Io(format!(
            "certificate tree {} carries no Lean module",
            request.tree.display()
        )));
    }
    let source_digest = certificate_tree_digest(&sources);
    let telescope_normalized_digest = certificate_tree_digest(
        &sources
            .iter()
            .map(|(relative, contents)| {
                (
                    relative.clone(),
                    if relative.ends_with(".lean") {
                        normalize_telescope_order(contents)
                    } else {
                        contents.clone()
                    },
                )
            })
            .collect::<Vec<_>>(),
    );
    for (relative, contents) in &sources {
        write_staged(
            &stage_src,
            &format!("{tree_relative}/{relative}"),
            contents.as_bytes(),
        )
        .await?;
    }
    check_cancelled(cancellation)?;

    // A fresh Lean build, every time: the compiled Input module is rebuilt
    // and overlaid, and every staged module is compiled from source into
    // this run's own throwaway `olean` directory.
    overlay_input_module(
        &request.repository_root,
        &stage_olean,
        canonical_id,
        cancellation,
    )
    .await?;
    check_cancelled(cancellation)?;
    let lean_binary = lake_env_which_lean(&request.repository_root, cancellation).await?;
    let base_lean_path = lake_env_lean_path(&request.repository_root, cancellation).await?;
    // The staging overlay is the only source for this certificate's own
    // namespace: every search-path entry that carries a compiled
    // `Benchmark/<id>/Certificate` tree of its own — the repository's
    // `.lake` build directory, normally — is replaced by a shadow of itself
    // with exactly that subtree left out.
    let lean_path = format!(
        "{}:{}",
        stage_olean.display(),
        shadowed_lean_path(&base_lean_path, &stage.join("shadow"), canonical_id)?
    );

    let mut modules = ModuleGraph::new();
    for (relative, contents) in &sources {
        if !relative.ends_with(".lean") {
            continue;
        }
        let dotted = format!("{certificate_prefix}.{}", relative_module_suffix(relative));
        let imports = parse_certificate_imports(contents, &certificate_prefix);
        modules.insert(dotted, (format!("{tree_relative}/{relative}"), imports));
    }
    // Every import in the certificate's own namespace must be a module of
    // this tree. A tree missing one of its own reconstruction modules would
    // otherwise compile: the shadowed search path keeps the repository's
    // stale `olean` for it out of reach, and this check makes the refusal
    // explicit rather than leaving it to a `lean` "unknown module" message.
    for (importer, (_, imports)) in &modules {
        for module in imports {
            if !modules.contains_key(module) {
                return Err(CertificateBuildError::UnresolvedCertificateImport {
                    importer: importer.clone(),
                    module: module.clone(),
                });
            }
        }
    }
    let order = topological_order(&modules)?;
    if lake_compilation_enabled()? {
        compile_with_lake(
            &lean_binary,
            &lean_path,
            &stage_src,
            &stage_olean,
            &certificate_prefix,
            &order,
            cancellation,
        )
        .await?;
    } else {
        for dotted in &order {
            let (relative_path, _) = &modules[dotted];
            check_cancelled(cancellation)?;
            compile_certificate_module(
                &lean_binary,
                &lean_path,
                &stage_src,
                &stage_olean,
                relative_path,
                dotted,
                cancellation,
            )
            .await?;
        }
    }

    if !modules.contains_key(request.certificate_module) {
        return Err(CertificateBuildError::Io(format!(
            "certificate tree {} carries no {} module",
            request.tree.display(),
            request.certificate_module
        )));
    }
    let target = CertificateTarget::of_shape(request.shape);
    let mut check_phase = PhaseLog::new("final_check", request.certificate_theorem, cancellation);
    let check_relative = format!("{tree_relative}/Check.lean");
    let check_source = target.check_source(
        request.certificate_module,
        request.input_namespace,
        request.certificate_theorem,
    );
    write_staged(&stage_src, &check_relative, check_source.as_bytes()).await?;
    check_cancelled(cancellation)?;
    let stdout = compile_check_module(
        &lean_binary,
        &lean_path,
        &stage_src,
        &stage_olean,
        &check_relative,
        &format!("{certificate_prefix}.Check"),
        cancellation,
    )
    .await?;
    let axioms = parse_print_axioms(&stdout)?;
    let found: std::collections::BTreeSet<&str> = axioms.iter().map(String::as_str).collect();
    let expected: std::collections::BTreeSet<&str> = STD3_AXIOMS.into_iter().collect();
    if found != expected {
        return Err(CertificateBuildError::Axioms { found: axioms });
    }
    check_phase.success();
    Ok(CertificateRevalidation {
        modules: order,
        axioms,
        lean_binary,
        lake_lean_path_digest: bytes_sha256(base_lean_path.as_bytes()),
        source_digest,
        telescope_normalized_digest,
    })
}

/// The one subtree of a certificate whose `.lean` files are evidence
/// rather than modules: `VampireArtifacts/jobs/<id>/leancheck.lean` is the
/// pinned solver's raw emitter output, kept beside its `problem.p` so a
/// reviewer can rerun the job, and it is never imported or compiled. The
/// build stages it from the solver stage rather than from the bundle's own
/// artifact list, and the emitter refuses a bundle that names it
/// (`certificate_ops.rs`).
///
/// A freshly built tree no longer carries this subtree at all: it is moved
/// out to a caller-supplied evidence directory or dropped before the tree
/// is promoted (see [`CertificateBuildRequest::evidence_destination`]).
/// The skip below stays because a tree revalidated here can also be one
/// checked in before that change, which still has it, and because it names
/// exactly what the build itself must not stage as a module while the
/// subtree still sits inside the tree being finished.
const CERTIFICATE_EVIDENCE_SUBTREE: &str = "VampireArtifacts";

const EMPTY_RESOURCE_PREFIX: &str = "EmptyCexCheck/Resources/";
const EMPTY_RESOURCE_MANIFEST: &str = "EmptyCexCheck/Resources/manifest.json";
const EMPTY_RESOURCE_KIND: &str = "whiel_empty_domain_certificate_resources";

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct EmptyResourceReceipt {
    job_id: String,
    encoding_version: u64,
    cnf_relative_path: String,
    cnf_sha256: String,
    lrat_relative_path: String,
    lrat_sha256: String,
    module_relative_path: String,
    module: String,
    theorem: String,
}

impl EmptyResourceReceipt {
    fn from_job(job: &CertificateJob, lrat_sha256: String) -> Result<Self, CertificateBuildError> {
        let check = &job.empty_check;
        let Some((prefix, _)) = check.module.rsplit_once(".EmptyCexCheck.") else {
            return Err(resource_error("empty check has no certificate prefix"));
        };
        let prefix = format!("{}/", prefix.replace('.', "/"));
        let relative = |path: &str| {
            path.strip_prefix(&prefix)
                .map(str::to_owned)
                .ok_or_else(|| resource_error("resource lies outside its certificate"))
        };
        Ok(Self {
            job_id: job.id.clone(),
            encoding_version: check.encoding_version,
            cnf_relative_path: relative(&check.cnf_relative_path)?,
            cnf_sha256: check.cnf_sha256.clone(),
            lrat_relative_path: relative(&check.lrat_relative_path)?,
            lrat_sha256,
            module_relative_path: relative(&check.module_relative_path)?,
            module: check.module.clone(),
            theorem: check.theorem.clone(),
        })
    }
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct EmptyResourceManifest {
    kind: String,
    version: u64,
    jobs: Vec<EmptyResourceReceipt>,
}

fn resource_error(message: &str) -> CertificateBuildError {
    CertificateBuildError::Io(format!("certificate empty-domain resources: {message}"))
}

async fn write_empty_resource_manifest(
    stage_src: &Path,
    canonical_id: &str,
    jobs: Vec<EmptyResourceReceipt>,
) -> Result<(), CertificateBuildError> {
    let manifest = EmptyResourceManifest {
        kind: EMPTY_RESOURCE_KIND.into(),
        version: 1,
        jobs,
    };
    let mut text = serde_json::to_string_pretty(&manifest)
        .map_err(|error| resource_error(&format!("serialize manifest: {error}")))?;
    text.push('\n');
    write_staged(
        stage_src,
        &format!("Benchmark/{canonical_id}/Certificate/{EMPTY_RESOURCE_MANIFEST}"),
        text.as_bytes(),
    )
    .await
}

fn resource_identifier(value: &str) -> bool {
    let mut bytes = value.bytes();
    bytes
        .next()
        .is_some_and(|b| b.is_ascii_alphabetic() || b == b'_')
        && bytes.all(|b| b.is_ascii_alphanumeric() || b == b'_')
}

fn validate_empty_resources(
    sources: &[(String, String)],
    expected_prefix: Option<&str>,
) -> Result<(), CertificateBuildError> {
    let files: BTreeMap<&str, &str> = sources
        .iter()
        .map(|(path, text)| (path.as_str(), text.as_str()))
        .collect();
    let Some(text) = files.get(EMPTY_RESOURCE_MANIFEST) else {
        if files.keys().any(|path| path.starts_with("EmptyCexCheck/")) {
            return Err(resource_error("missing manifest for per-job empty checks"));
        }
        // Legacy certificates have an aggregate EmptyCexCheck.lean and no resources.
        return Ok(());
    };
    let manifest: EmptyResourceManifest = serde_json::from_str(text)
        .map_err(|error| resource_error(&format!("invalid manifest: {error}")))?;
    if manifest.kind != EMPTY_RESOURCE_KIND || manifest.version != 1 || manifest.jobs.is_empty() {
        return Err(resource_error("unsupported or empty manifest"));
    }
    let mut expected_files =
        std::collections::BTreeSet::from([EMPTY_RESOURCE_MANIFEST.to_string()]);
    let mut jobs = std::collections::BTreeSet::new();
    let mut modules = std::collections::BTreeSet::new();
    let mut theorems = std::collections::BTreeSet::new();
    let mut certificate_prefix = None;
    for entry in manifest.jobs {
        let Some((prefix, stem)) = entry.module.rsplit_once(".EmptyCexCheck.") else {
            return Err(resource_error("invalid check module identity"));
        };
        let theorem_prefix = format!("Whiel.{prefix}.");
        let Some(theorem) = entry.theorem.strip_prefix(&theorem_prefix) else {
            return Err(resource_error(
                "check theorem belongs to another certificate",
            ));
        };
        if entry.encoding_version != EMPTY_DOMAIN_ENCODING_VERSION
            || expected_prefix.is_some_and(|expected| expected != prefix)
            || !prefix.starts_with("Benchmark.")
            || !prefix.ends_with(".Certificate")
            || !prefix.split('.').all(resource_identifier)
            || !resource_identifier(stem)
            || !resource_identifier(theorem)
            || !resource_identifier(&entry.job_id)
            || !jobs.insert(entry.job_id.clone())
            || !modules.insert(entry.module.clone())
            || !theorems.insert(entry.theorem.clone())
            || certificate_prefix
                .as_deref()
                .is_some_and(|old| old != prefix)
        {
            return Err(resource_error(
                "unsupported, unsafe or repeated proof identity",
            ));
        }
        certificate_prefix = Some(prefix.to_string());
        if entry.module_relative_path != format!("EmptyCexCheck/{stem}.lean")
            || !files.contains_key(entry.module_relative_path.as_str())
            || entry.cnf_relative_path != format!("{EMPTY_RESOURCE_PREFIX}{}.cnf", entry.job_id)
            || entry.lrat_relative_path != format!("{EMPTY_RESOURCE_PREFIX}{}.lrat", entry.job_id)
        {
            return Err(resource_error(
                "missing check module or inconsistent resource paths",
            ));
        }
        for (path, digest) in [
            (&entry.cnf_relative_path, &entry.cnf_sha256),
            (&entry.lrat_relative_path, &entry.lrat_sha256),
        ] {
            let Some(contents) = files.get(path.as_str()) else {
                return Err(resource_error(&format!("missing {path}")));
            };
            if !expected_files.insert(path.clone()) {
                return Err(resource_error("repeated resource path"));
            }
            if bytes_sha256(contents.as_bytes()) != *digest {
                return Err(CertificateBuildError::Tampered {
                    relative_path: path.clone(),
                });
            }
        }
    }
    if files
        .keys()
        .filter(|path| path.starts_with(EMPTY_RESOURCE_PREFIX))
        .any(|path| !expected_files.contains(*path))
    {
        return Err(resource_error("undeclared file in resource subtree"));
    }
    Ok(())
}

/// Every module and required empty-domain resource of one tree, keyed by its
/// tree-relative slash-separated path, in path order. Evidence under
/// [`CERTIFICATE_EVIDENCE_SUBTREE`] — staged there today, or a survivor
/// there from before evidence was moved out of published trees — is not a
/// module and is not returned. Resource bytes are staged and hashed, not compiled.
fn read_certificate_tree(
    tree: &Path,
    expected_prefix: Option<&str>,
) -> Result<Vec<(String, String)>, CertificateBuildError> {
    let mut sources = Vec::new();
    let mut pending = vec![(tree.to_path_buf(), String::new())];
    while let Some((directory, prefix)) = pending.pop() {
        let entries = std::fs::read_dir(&directory).map_err(|error| {
            CertificateBuildError::Io(format!("read {}: {error}", directory.display()))
        })?;
        for entry in entries {
            let entry = entry.map_err(|error| {
                CertificateBuildError::Io(format!("read {}: {error}", directory.display()))
            })?;
            let name = entry.file_name();
            let Some(name) = name.to_str() else {
                return Err(CertificateBuildError::Io(format!(
                    "certificate tree entry {} has a non-UTF-8 name",
                    entry.path().display()
                )));
            };
            let relative = if prefix.is_empty() {
                name.to_string()
            } else {
                format!("{prefix}/{name}")
            };
            let file_type = entry.file_type().map_err(|error| {
                CertificateBuildError::Io(format!("stat {}: {error}", entry.path().display()))
            })?;
            // `entry.file_type()` is the entry's own type, not its target's,
            // so a symlink is neither a directory nor a regular file here.
            // Anything that is not one of those two is refused rather than
            // skipped: a symlinked module would otherwise leave the compiled
            // set silently while the theorem that needs it still elaborated
            // against whatever `olean` happened to be on the search path.
            if !file_type.is_dir() && !file_type.is_file() {
                return Err(CertificateBuildError::NonRegularTreeEntry {
                    path: entry.path().display().to_string(),
                });
            }
            if file_type.is_dir() {
                if name != CERTIFICATE_EVIDENCE_SUBTREE {
                    pending.push((entry.path(), relative));
                }
            } else if name.ends_with(".lean") || relative.starts_with(EMPTY_RESOURCE_PREFIX) {
                let contents = std::fs::read_to_string(entry.path()).map_err(|error| {
                    CertificateBuildError::Io(format!("read {}: {error}", entry.path().display()))
                })?;
                sources.push((relative, contents));
            }
        }
    }
    sources.sort_by(|left, right| left.0.cmp(&right.0));
    validate_empty_resources(&sources, expected_prefix)?;
    Ok(sources)
}

/// Digest exact Lean sources and persistent proof resources. Disposable
/// Vampire evidence and proof-independent diagnostic sidecars are excluded.
fn certificate_tree_digest(sources: &[(String, String)]) -> String {
    let mut material = String::new();
    for (relative, contents) in sources {
        material.push_str(relative);
        material.push('\n');
        material.push_str(&bytes_sha256(contents.as_bytes()));
        material.push('\n');
    }
    bytes_sha256(material.as_bytes())
}

/// The dotted module suffix of one tree-relative `.lean` path.
fn relative_module_suffix(relative: &str) -> String {
    relative
        .strip_suffix(".lean")
        .unwrap_or(relative)
        .replace('/', ".")
}

// ------------------------------------------------------------
// Import-Order Topological Sort
// ------------------------------------------------------------

/// dotted module name -> (stage-relative source path, its own-tree imports).
type ModuleGraph = BTreeMap<String, (String, Vec<String>)>;

fn collect_staged_modules(
    bundle: &CertificateBundle,
    stage_src: &Path,
    certificate_prefix: &str,
) -> Result<ModuleGraph, CertificateBuildError> {
    let mut relative_paths: BTreeMap<String, String> = BTreeMap::new();
    for artifact in &bundle.artifacts {
        if let Some(stem) = artifact.relative_path.strip_suffix(".lean") {
            relative_paths.insert(stem.replace('/', "."), artifact.relative_path.clone());
        }
    }
    for job in &bundle.jobs {
        relative_paths.insert(
            job.proof_module.clone(),
            job.proof_module_relative_path.clone(),
        );
    }
    let mut modules = ModuleGraph::new();
    for (dotted, relative_path) in relative_paths {
        let source_path = safe_relative_join(stage_src, &relative_path)?;
        let source = std::fs::read_to_string(&source_path).map_err(|error| {
            CertificateBuildError::Io(format!("read {}: {error}", source_path.display()))
        })?;
        let imports = parse_certificate_imports(&source, certificate_prefix);
        modules.insert(dotted, (relative_path, imports));
    }
    Ok(modules)
}

fn parse_certificate_imports(source: &str, certificate_prefix: &str) -> Vec<String> {
    source
        .lines()
        .filter_map(|line| line.trim().strip_prefix("import "))
        .map(str::trim)
        .filter(|module| in_certificate_namespace(module, certificate_prefix))
        .map(str::to_string)
        .collect()
}

/// Whether one dotted module name lies in the certificate's own namespace.
///
/// The test is on component boundaries, not on the raw string: a
/// `Benchmark.<id>.CertificateNotes` module is a different namespace, and
/// treating it as an own-tree import would both misorder the compilation
/// and, since Pass 7.5g's fix, refuse a tree that legitimately imports it.
fn in_certificate_namespace(module: &str, certificate_prefix: &str) -> bool {
    module == certificate_prefix
        || module
            .strip_prefix(certificate_prefix)
            .is_some_and(|rest| rest.starts_with('.'))
}

fn topological_order(modules: &ModuleGraph) -> Result<Vec<String>, CertificateBuildError> {
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum Mark {
        Visiting,
        Done,
    }

    fn visit(
        node: &str,
        modules: &ModuleGraph,
        marks: &mut BTreeMap<String, Mark>,
        order: &mut Vec<String>,
    ) -> Result<(), CertificateBuildError> {
        match marks.get(node) {
            Some(Mark::Done) => return Ok(()),
            Some(Mark::Visiting) => {
                return Err(CertificateBuildError::Io(format!(
                    "certificate module import graph has a cycle at {node}"
                )));
            }
            None => {}
        }
        marks.insert(node.to_string(), Mark::Visiting);
        if let Some((_, imports)) = modules.get(node) {
            for dependency in imports {
                if modules.contains_key(dependency) {
                    visit(dependency, modules, marks, order)?;
                }
            }
        }
        marks.insert(node.to_string(), Mark::Done);
        order.push(node.to_string());
        Ok(())
    }

    let mut marks = BTreeMap::new();
    let mut order = Vec::with_capacity(modules.len());
    for node in modules.keys() {
        visit(node, modules, &mut marks, &mut order)?;
    }
    Ok(order)
}

// ------------------------------------------------------------
// Axiom Output Parsing
// ------------------------------------------------------------

fn parse_print_axioms(stdout: &str) -> Result<Vec<String>, CertificateBuildError> {
    let normalized = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
    if normalized.contains("does not depend on any axioms") {
        return Ok(Vec::new());
    }
    let marker = "axioms: [";
    let start = normalized.find(marker).ok_or_else(|| {
        CertificateBuildError::Io(
            "#print axioms produced no recognizable axiom listing".to_string(),
        )
    })?;
    let after = &normalized[start + marker.len()..];
    let end = after.find(']').ok_or_else(|| {
        CertificateBuildError::Io("#print axioms output has no closing bracket".to_string())
    })?;
    Ok(after[..end]
        .split(',')
        .map(str::trim)
        .filter(|token| !token.is_empty())
        .map(str::to_string)
        .collect())
}

// ------------------------------------------------------------
// Small Shared Helpers
// ------------------------------------------------------------

fn check_cancelled(cancellation: &CancellationToken) -> Result<(), CertificateBuildError> {
    // `should_stop`, not `is_cancelled`: Pass 7.5f gives certification its
    // own independent deadline, bound to this token, and a token that is
    // stopped for any reason — cancelled, or past a deadline bound to it —
    // closes the build the same way. Both dispatch paths make this check
    // before every job's own launch: the sequential pass at the head of its
    // loop, each concurrent task once it holds its permit.
    if cancellation.should_stop() {
        Err(CertificateBuildError::Cancelled)
    } else {
        Ok(())
    }
}

fn extract_str<'v>(value: &'v Value, field: &str) -> Result<&'v str, CertificateBuildError> {
    value.get(field).and_then(Value::as_str).ok_or_else(|| {
        CertificateBuildError::Io(format!("certificate bundle input_identity has no {field}"))
    })
}

fn map_certificate_error(error: FrameworkIICertificateError) -> CertificateBuildError {
    match error {
        FrameworkIICertificateError::Cancelled => CertificateBuildError::Cancelled,
        FrameworkIICertificateError::Failure(report) => CertificateBuildError::Emit(report),
    }
}

/// Per-stream capture cap for every `lake`/`lean` child this module
/// supervises: generous enough that no real build or diagnostic output is
/// ever truncated, while still bounding worst-case memory use against a
/// runaway or misbehaving child.
const MAX_SUPERVISED_OUTPUT_BYTES: usize = 256 * 1024 * 1024;

// Lake's compiler children share its owned group. Keep the guard through
// capture draining, and kill descendants even if the leader failed first.
#[cfg(unix)]
struct CompilerProcessGroup {
    id: u32,
    registry: crate::runtime::process_tree::ProcessRegistry,
}

#[cfg(unix)]
impl CompilerProcessGroup {
    fn kill(&self) {
        let _ = crate::runtime::process_tree::signal_group(self.id, libc::SIGKILL);
    }

    async fn join_descendants(&mut self) -> Result<(), CertificateBuildError> {
        let registry = &mut self.registry;
        let deadline = Instant::now() + Duration::from_secs(5);
        loop {
            registry.refresh();
            let remaining = registry.owned_live_descendants(self.id);
            if remaining.is_empty() {
                return Ok(());
            }
            for child in &remaining {
                let _ =
                    crate::runtime::process_tree::signal_identity(&child.identity, libc::SIGKILL);
            }
            if Instant::now() >= deadline {
                return Err(CertificateBuildError::Io(
                    "compiler descendants did not stop".into(),
                ));
            }
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    }
}

#[cfg(unix)]
impl Drop for CompilerProcessGroup {
    fn drop(&mut self) {
        self.kill();
    }
}

async fn run_supervised(
    mut command: Command,
    cancellation: &CancellationToken,
) -> Result<(std::process::ExitStatus, Vec<u8>, Vec<u8>), CertificateBuildError> {
    check_cancelled(cancellation)?;
    command
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .kill_on_drop(true);
    #[cfg(unix)]
    command.process_group(0);
    let mut child = command
        .spawn()
        .map_err(|error| CertificateBuildError::Io(format!("start process: {error}")))?;
    #[cfg(unix)]
    let mut group = {
        let id = child.id().expect("spawned compiler has a pid");
        match crate::runtime::process_tree::ProcessRegistry::new(id) {
            Ok(registry) => CompilerProcessGroup { id, registry },
            Err(error) => {
                let _ = crate::runtime::process_tree::signal_group(id, libc::SIGKILL);
                let _ = child.wait().await;
                return Err(CertificateBuildError::Io(format!(
                    "track compiler process group: {error}"
                )));
            }
        }
    };
    let stdout = child.stdout.take().expect("stdout is piped");
    let stderr = child.stderr.take().expect("stderr is piped");
    let stdout_task = tokio::spawn(read_to_end_capped(stdout));
    let stderr_task = tokio::spawn(read_to_end_capped(stderr));

    let status = loop {
        tokio::select! {
            biased;
            _ = cancellation.cancelled() => {
                #[cfg(unix)]
                group.kill();
                let _ = child.start_kill();
                let _ = child.wait().await;
                stdout_task.abort();
                stderr_task.abort();
                let _ = stdout_task.await;
                let _ = stderr_task.await;
                #[cfg(unix)]
                group.join_descendants().await?;
                return Err(CertificateBuildError::Cancelled);
            }
            status = child.wait() => break status,
            _ = tokio::time::sleep(Duration::from_millis(20)) => {
                #[cfg(unix)]
                group.registry.refresh();
            }
        }
    };
    #[cfg(unix)]
    {
        group.kill();
        if let Err(error) = group.join_descendants().await {
            stdout_task.abort();
            stderr_task.abort();
            let _ = stdout_task.await;
            let _ = stderr_task.await;
            return Err(error);
        }
    }
    // Captures may outlive the direct process (for example, an inherited
    // pipe). Cancellation must cover their drains as well as child.wait.
    let (stdout_result, stderr_result) = tokio::join!(
        join_supervised_capture(stdout_task, cancellation, "stdout"),
        join_supervised_capture(stderr_task, cancellation, "stderr"),
    );
    check_cancelled(cancellation)?;
    let status =
        status.map_err(|error| CertificateBuildError::Io(format!("wait for process: {error}")))?;
    let (stdout_bytes, stdout_overflowed) = stdout_result?;
    let (stderr_bytes, stderr_overflowed) = stderr_result?;
    if stdout_overflowed {
        return Err(CertificateBuildError::OutputTooLarge {
            stream: "stdout",
            limit: MAX_SUPERVISED_OUTPUT_BYTES,
        });
    }
    if stderr_overflowed {
        return Err(CertificateBuildError::OutputTooLarge {
            stream: "stderr",
            limit: MAX_SUPERVISED_OUTPUT_BYTES,
        });
    }
    Ok((status, stdout_bytes, stderr_bytes))
}

async fn join_supervised_capture(
    mut task: tokio::task::JoinHandle<io::Result<(Vec<u8>, bool)>>,
    cancellation: &CancellationToken,
    stream: &str,
) -> Result<(Vec<u8>, bool), CertificateBuildError> {
    tokio::select! {
        biased;
        _ = cancellation.cancelled() => {
            task.abort();
            let _ = task.await;
            Err(CertificateBuildError::Cancelled)
        }
        result = &mut task => result
            .map_err(|error| CertificateBuildError::Io(format!("join {stream} capture: {error}")))?
            .map_err(|error| CertificateBuildError::Io(format!("read {stream}: {error}"))),
    }
}

/// Read `reader` to EOF, retaining at most [`MAX_SUPERVISED_OUTPUT_BYTES`].
/// Bytes beyond the cap are still drained (never left unread, which would
/// block a child still writing to a full pipe) but discarded; the overflow
/// is reported as a bool rather than silently truncating the capture into
/// an apparently-complete result (see [`run_supervised`]'s typed
/// [`CertificateBuildError::OutputTooLarge`] on it).
async fn read_to_end_capped(
    mut reader: impl tokio::io::AsyncRead + Unpin,
) -> io::Result<(Vec<u8>, bool)> {
    let mut collected = Vec::new();
    let mut overflowed = false;
    let mut buffer = [0_u8; 64 * 1024];
    loop {
        let count = reader.read(&mut buffer).await?;
        if count == 0 {
            break;
        }
        if !overflowed {
            let remaining = MAX_SUPERVISED_OUTPUT_BYTES.saturating_sub(collected.len());
            let take = remaining.min(count);
            collected.extend_from_slice(&buffer[..take]);
            if take < count {
                overflowed = true;
            }
        }
    }
    Ok((collected, overflowed))
}

// ------------------------------------------------------------
// Errors
// ------------------------------------------------------------

/// Errors building one durable certificate tree. Every variant fails
/// closed: the staging directory is removed regardless of which of these
/// is returned.
#[derive(Debug)]
pub enum CertificateBuildError {
    /// Lean-owned certificate-plan emission failed.
    Emit(FailureReport),
    /// A staged problem's bytes disagree with the bundle's own digest for
    /// it, after staging and before solving.
    Tampered { relative_path: String },
    /// The certificate bundle's own `input_identity` disagrees with the
    /// bound task identity Rust already validated.
    IdentityMismatch {
        bundle_canonical_id: String,
        bundle_namespace: String,
        task_canonical_id: String,
        task_namespace: String,
    },
    /// The pinned leancheck Vampire failed on one job (a non-cancellation
    /// [`LeancheckError`]).
    Solver {
        job_id: String,
        source: LeancheckError,
    },
    /// The caller's `profiles` callback failed to select a
    /// [`LeancheckProfile`] for one job.
    ProfileSelection {
        job_id: String,
        source: CoreFreezeError,
    },
    /// Lean-owned proof packaging rejected one job's proof text.
    Package {
        job_id: String,
        report: FailureReport,
    },
    /// One deterministic proof transformation refused the emitted text
    /// (see [`super::proof_transform`]). Each rewrite pins an exact
    /// emitter shape; anything else fails the build closed rather than
    /// being rewritten on a guess.
    ProofTransform(ProofTransformError),
    /// The CaDiCaL pinned by the `kernel_lrat_cadical` toolchain-lock role
    /// could not be resolved, or its bytes or version are not the locked
    /// ones. The build fails rather than substituting another solver: a
    /// substituted solver's trace would still have to validate, but the
    /// certificate would no longer be reproducible from the lock.
    KernelLratCadical(String),
    /// One staged certificate module failed to typecheck.
    Build { module: String, diagnostics: String },
    /// The generated `Check.lean` failed to typecheck with an elaboration
    /// error (stdout carries a `error:` diagnostic line): the packaged
    /// clause proofs do not compose into a proof of the input Hoare triple.
    WrongTheoremType { diagnostics: String },
    /// `lean` failed to build `Check.lean` for a reason other than
    /// rejecting the theorem's type (a crash, a signal, an OOM kill, or a
    /// missing staged `olean`) — distinguished from
    /// [`Self::WrongTheoremType`] by the absence of an `error:` diagnostic
    /// on stdout.
    LeanProcess { module: String, diagnostics: String },
    /// `Check.lean` typechecked, but its `#print axioms` output names
    /// something other than exactly `propext`, `Classical.choice`, and
    /// `Quot.sound`.
    Axioms { found: Vec<String> },
    /// A filesystem or process-launch operation failed.
    Io(String),
    /// One module of the tree imports a module that lies under the
    /// certificate's own `Benchmark.<id>.Certificate` namespace but is not a
    /// module of the tree.
    ///
    /// Nothing may resolve such an import from outside the tree under
    /// revalidation. The repository's `.lake` `olean` tree ordinarily
    /// carries exactly those modules for a checked-in certificate, so a tree
    /// missing one of its own reconstruction modules would otherwise compile
    /// against a stale compiled artifact and be revalidated on evidence it
    /// does not contain.
    UnresolvedCertificateImport { importer: String, module: String },
    /// One entry of the tree is neither a regular file nor a directory (a
    /// symlink, a device, a socket, a fifo).
    ///
    /// A certificate tree is its bytes. An entry whose contents live
    /// somewhere else is refused rather than silently skipped, so a
    /// symlinked module cannot drop out of the compiled set while the
    /// theorem it belongs to still elaborates against a stale `olean`.
    NonRegularTreeEntry { path: String },
    /// A supervised `lake`/`lean` child's captured stream exceeded its
    /// bound (see `MAX_SUPERVISED_OUTPUT_BYTES`) before it finished; the
    /// excess was drained and discarded, not returned truncated as if it
    /// were complete.
    OutputTooLarge { stream: &'static str, limit: usize },
    /// The requested destination already exists.
    DestinationExists(PathBuf),
    /// The staging tree and the promotion destination are on different
    /// filesystems, so promotion could not be one rename.
    ///
    /// Promotion is atomic or it does not happen, exactly as publication is
    /// (`publication.rs`, [`crate::PublicationError::CrossesFilesystems`]):
    /// `certificate build --core` promotes a tree that is then treated as
    /// authority, and there is no copy fallback, because a copy followed by
    /// a removal has an interruption window in which a half-written tree
    /// stands where a complete one is claimed to be.
    CrossesFilesystems {
        staging: PathBuf,
        destination: PathBuf,
    },
    /// The requested evidence destination already exists. Evidence is
    /// moved out, never merged: a caller who wants to retry into the same
    /// path removes what is there first.
    EvidenceDestinationExists(PathBuf),
    /// The requested evidence destination lies inside (or contains) the
    /// staging tree it would be moved out of or the certificate
    /// destination it would be promoted beside.
    EvidenceDestinationConflict {
        evidence_destination: PathBuf,
        conflicting_with: PathBuf,
    },
    /// The build was cancelled before it finished.
    Cancelled,
}

impl fmt::Display for CertificateBuildError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Emit(report) => write!(
                formatter,
                "certificate emission failed: origin={:?} kind={:?} detail={}",
                report.origin(),
                report.kind(),
                report.detail().unwrap_or("none")
            ),
            Self::Tampered { relative_path } => write!(
                formatter,
                "staged certificate artifact was tampered with: {relative_path}"
            ),
            Self::IdentityMismatch {
                bundle_canonical_id,
                bundle_namespace,
                task_canonical_id,
                task_namespace,
            } => write!(
                formatter,
                "certificate bundle input_identity ({bundle_canonical_id}, {bundle_namespace}) \
                 disagrees with the bound task identity ({task_canonical_id}, {task_namespace})"
            ),
            Self::Solver { job_id, source } => {
                write!(
                    formatter,
                    "certificate job {job_id} solver failure: {source}"
                )
            }
            Self::ProfileSelection { job_id, source } => write!(
                formatter,
                "certificate job {job_id} profile selection failed: {source}"
            ),
            Self::Package { job_id, report } => write!(
                formatter,
                "certificate job {job_id} packaging failed: origin={:?} kind={:?} detail={}",
                report.origin(),
                report.kind(),
                report.detail().unwrap_or("none")
            ),
            Self::ProofTransform(source) => write!(formatter, "{source}"),
            Self::KernelLratCadical(message) => write!(
                formatter,
                "the pinned kernel-LRAT CaDiCaL is not usable: {message}"
            ),
            Self::Build {
                module,
                diagnostics,
            } => {
                write!(
                    formatter,
                    "certificate module {module} failed to build: {diagnostics}"
                )
            }
            Self::WrongTheoremType { diagnostics } => write!(
                formatter,
                "certificate theorem does not prove the input Hoare triple: {diagnostics}"
            ),
            Self::LeanProcess {
                module,
                diagnostics,
            } => write!(formatter, "lean failed to build {module}: {diagnostics}"),
            Self::Axioms { found } => write!(
                formatter,
                "certificate theorem depends on unexpected axioms: {found:?}"
            ),
            Self::Io(detail) => write!(formatter, "certificate build I/O error: {detail}"),
            Self::UnresolvedCertificateImport { importer, module } => write!(
                formatter,
                "{importer} imports {module}, which lies under the certificate's own namespace \
                 but is not a module of this tree; nothing outside the tree may resolve it"
            ),
            Self::NonRegularTreeEntry { path } => write!(
                formatter,
                "certificate tree entry {path} is neither a regular file nor a directory"
            ),
            Self::OutputTooLarge { stream, limit } => write!(
                formatter,
                "a supervised process's {stream} exceeded the {limit}-byte capture limit"
            ),
            Self::DestinationExists(path) => write!(
                formatter,
                "certificate destination already exists: {}",
                path.display()
            ),
            // Word for word `PublicationError::CrossesFilesystems`: the two
            // paths refuse the same thing for the same reason, and a caller
            // who hits one and then the other must not have to learn two
            // vocabularies for it.
            Self::CrossesFilesystems {
                staging,
                destination,
            } => write!(
                formatter,
                "the staging tree {} and the publication destination {} are on different \
                 filesystems, so publication cannot be one rename; stage on the \
                 destination's own filesystem (the certificate CLI's default staging root \
                 is a sibling of the destination for exactly this reason)",
                staging.display(),
                destination.display()
            ),
            Self::EvidenceDestinationExists(path) => write!(
                formatter,
                "evidence destination already exists: {}",
                path.display()
            ),
            Self::EvidenceDestinationConflict {
                evidence_destination,
                conflicting_with,
            } => write!(
                formatter,
                "evidence destination {} conflicts with {}: it must lie outside both the \
                 staging tree and the certificate destination",
                evidence_destination.display(),
                conflicting_with.display()
            ),
            Self::Cancelled => formatter.write_str("certificate build was cancelled"),
        }
    }
}

impl std::error::Error for CertificateBuildError {}

// ------------------------------------------------------------
// Tests
// ------------------------------------------------------------

#[cfg(test)]
mod candidate_gate_tests;

#[cfg(test)]
mod tests {
    use super::super::production::ProofSearchProfile;
    use super::*;

    #[test]
    fn public_builder_destination_ownership_excludes_a_publisher() {
        let root = OwnedDirectory::fresh(&std::env::temp_dir(), "whiel-builder-lease").unwrap();
        let destination = root.path().join("Certificate");
        let publisher = PathLease::acquire(&destination).unwrap();
        assert!(certificate_destination_lease(&destination).is_err());
        drop(publisher);
        let builder = certificate_destination_lease(&destination).unwrap();
        assert_eq!(
            PathLease::acquire(&destination).unwrap_err().kind(),
            io::ErrorKind::WouldBlock
        );
        drop(builder);
        drop(PathLease::acquire(&destination).unwrap());
    }

    #[test]
    fn private_builder_capability_only_covers_its_immediate_children() {
        let root = OwnedDirectory::fresh(&std::env::temp_dir(), "whiel-builder-private").unwrap();
        check_owned_destination(&root, &root.path().join("Certificate")).unwrap();
        assert!(check_owned_destination(&root, &root.path().join("nested/Certificate")).is_err());
        assert!(check_owned_destination(&root, &root.path().join("../Certificate")).is_err());
        assert!(check_owned_destination(&root, root.path()).is_err());
        assert_eq!(
            std::fs::read_dir(root.path()).unwrap().count(),
            0,
            "private authorization creates no lock sidecar"
        );
    }

    #[test]
    fn parses_a_multiline_axiom_listing() {
        let stdout = "'foo' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n";
        let axioms = parse_print_axioms(stdout).unwrap();
        assert_eq!(axioms, vec!["propext", "Classical.choice", "Quot.sound"]);
    }

    #[test]
    fn parses_no_axioms_as_empty() {
        let stdout = "'foo' does not depend on any axioms\n";
        let axioms = parse_print_axioms(stdout).unwrap();
        assert!(axioms.is_empty());
    }

    #[test]
    fn rejects_unparseable_axiom_output() {
        assert!(parse_print_axioms("nothing recognizable here").is_err());
    }

    #[test]
    fn topological_order_respects_certificate_scoped_imports() {
        let mut modules = ModuleGraph::new();
        modules.insert(
            "Benchmark.Example0001.Certificate.Jobs".to_string(),
            (
                "Benchmark/Example0001/Certificate/Jobs.lean".to_string(),
                vec!["Benchmark.Example0001.Certificate.Proposal".to_string()],
            ),
        );
        modules.insert(
            "Benchmark.Example0001.Certificate.Proposal".to_string(),
            (
                "Benchmark/Example0001/Certificate/Proposal.lean".to_string(),
                vec![],
            ),
        );
        let order = topological_order(&modules).unwrap();
        let proposal = order
            .iter()
            .position(|module| module == "Benchmark.Example0001.Certificate.Proposal")
            .unwrap();
        let jobs = order
            .iter()
            .position(|module| module == "Benchmark.Example0001.Certificate.Jobs")
            .unwrap();
        assert!(proposal < jobs);
    }

    #[test]
    fn topological_order_rejects_a_cycle() {
        let mut modules = ModuleGraph::new();
        modules.insert(
            "A".to_string(),
            ("A.lean".to_string(), vec!["B".to_string()]),
        );
        modules.insert(
            "B".to_string(),
            ("B.lean".to_string(), vec!["A".to_string()]),
        );
        assert!(topological_order(&modules).is_err());
    }

    /// Milestone 7.5 review, finding 4. Promotion is one rename or it is
    /// refused, on this path as on `publication.rs`'s: `certificate build
    /// --core` promotes a tree that is then treated as authority, so the
    /// cross-filesystem copy fallback that used to stand here was a
    /// publication by copy. The refusal is the same variant shape and the
    /// same message as `PublicationError::CrossesFilesystems`.
    ///
    /// A second filesystem cannot be assumed on a developer machine, so the
    /// refusal is forced on demand, exactly as in `publication.rs`.
    #[tokio::test(flavor = "current_thread")]
    async fn a_promotion_across_filesystems_is_refused_and_never_copies() {
        let scratch = std::env::temp_dir().join(format!(
            "whiel-certificate-cross-device-{}",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&scratch);
        let staged = scratch.join("stage/src/Benchmark/Example0001/Certificate");
        std::fs::create_dir_all(&staged).expect("create the staged tree");
        std::fs::write(staged.join("Valid.lean"), b"-- valid\n").expect("write a module");
        let destination = scratch.join("published/Certificate");

        FORCED_CROSS_FILESYSTEM.with(|forced| forced.set(true));
        let refused = promote_certificate_tree(&staged, &destination)
            .await
            .expect_err("no copy fallback exists");
        FORCED_CROSS_FILESYSTEM.with(|forced| forced.set(false));

        assert!(
            matches!(&refused, CertificateBuildError::CrossesFilesystems { .. }),
            "{refused}"
        );
        let message = refused.to_string();
        assert!(message.contains("one rename"), "{message}");
        assert!(
            message.contains("stage on the destination's own filesystem"),
            "{message}"
        );
        // Nothing was copied: the staged tree is whole and the destination
        // was never made.
        assert!(staged.join("Valid.lean").is_file());
        assert!(!destination.exists());

        // Unforced, the same call promotes with one rename.
        std::fs::create_dir_all(destination.parent().unwrap()).unwrap();
        promote_certificate_tree(&staged, &destination)
            .await
            .expect("one rename promotes");
        assert!(!staged.exists());
        assert!(destination.join("Valid.lean").is_file());

        let _ = std::fs::remove_dir_all(&scratch);
    }

    #[test]
    fn safe_relative_join_rejects_escaping_paths() {
        let base = Path::new("/tmp/stage/src");
        assert!(safe_relative_join(base, "../escape.lean").is_err());
        assert!(safe_relative_join(base, "/absolute.lean").is_err());
        assert!(safe_relative_join(base, "Benchmark/Example0001/Input.lean").is_ok());
    }

    /// P3's third clause (Milestone A review, finding A-4): the evidence
    /// directory must lie outside the campaign's candidate private tree,
    /// not only the staging tree and the certificate destination. Neither
    /// of those two alone catches a path that sits elsewhere inside the
    /// owning private root, so this exercises the private-root check on
    /// its own: `staging_root` and `destination` are chosen so neither
    /// conflicts with `evidence` by itself.
    #[test]
    fn evidence_destination_inside_an_owning_private_root_is_refused() {
        let root =
            OwnedDirectory::fresh(&std::env::temp_dir(), "whiel-evidence-private-root").unwrap();
        let staging_root = root.path().join("staging");
        let destination = root.path().join("elsewhere/Certificate");
        let evidence = root.path().join("SomeOtherSubdir/Evidence");
        assert!(!paths_conflict(&evidence, &staging_root));
        assert!(!paths_conflict(&evidence, &destination));

        // With no owning private root named, `evidence` conflicts with
        // neither of the two paths this check already covers.
        check_evidence_destination(Some(&evidence), &staging_root, &destination, None)
            .expect("no owning private root is named, so nothing conflicts");
        // Naming the private root `evidence` actually sits inside is what
        // this finding requires be refused.
        let error = check_evidence_destination(
            Some(&evidence),
            &staging_root,
            &destination,
            Some(root.path()),
        )
        .expect_err("an evidence destination inside the owning private root is refused");
        assert!(
            matches!(
                &error,
                CertificateBuildError::EvidenceDestinationConflict { conflicting_with, .. }
                    if conflicting_with == root.path()
            ),
            "{error:?}"
        );
    }

    /// Milestone A review, finding A-5: `paths_conflict` normalizes both
    /// paths lexically first, so a `./`- or `..`-bearing path is not
    /// mistaken for a sibling of the location it actually resolves to.
    #[test]
    fn paths_conflict_normalizes_dot_and_dot_dot_components() {
        let base = std::env::temp_dir().join("whiel-evidence-lexical-base");
        let dotted = base.join(".").join("Evidence");
        assert!(paths_conflict(&dotted, &base));
        let via_parent = base.join("child").join("..").join("Evidence");
        assert!(paths_conflict(&via_parent, &base));
        let same_via_parent = base.join("a").join("..").join("a");
        assert!(paths_conflict(&same_via_parent, &base.join("a")));
        let sibling_via_parent = base.join("a").join("..").join("b");
        assert!(!paths_conflict(&sibling_via_parent, &base.join("a")));
    }

    #[test]
    fn normalize_lexically_absolutizes_a_relative_path_against_the_current_directory() {
        let normalized = normalize_lexically(Path::new(
            "./whiel-relative-scratch/../whiel-relative-scratch",
        ));
        assert!(normalized.is_absolute());
        assert!(normalized.ends_with("whiel-relative-scratch"));
    }

    /// Milestone A review, finding A-3(c): the guard removes what it was
    /// armed with only while still armed; disarming (a successful
    /// promotion) leaves it alone.
    #[test]
    fn evidence_cleanup_guard_removes_only_while_armed() {
        let root = OwnedDirectory::fresh(&std::env::temp_dir(), "whiel-evidence-guard").unwrap();
        let evidence = root.path().join("Evidence");
        std::fs::create_dir_all(&evidence).unwrap();
        {
            let mut guard = EvidenceCleanupGuard::armed(evidence.clone());
            guard.disarm();
        }
        assert!(evidence.exists(), "a disarmed guard leaves its path alone");

        {
            let _guard = EvidenceCleanupGuard::armed(evidence.clone());
        }
        assert!(
            !evidence.exists(),
            "an armed guard removes its path on drop"
        );
    }

    /// Milestone A review, finding A-7: `move_evidence_out` itself, forced
    /// onto its copy-then-remove fallback, actually exercises that path —
    /// the flag only changes *which* branch runs, it does not also make
    /// `move_evidence_out` return early before reaching it (that would
    /// leave `to` unwritten and this test would wrongly pass).
    #[tokio::test(flavor = "current_thread")]
    async fn move_evidence_out_forced_cross_filesystem_falls_back_to_copy() {
        let root =
            OwnedDirectory::fresh(&std::env::temp_dir(), "whiel-evidence-copy-fallback").unwrap();
        let from = root.path().join("stage-evidence");
        std::fs::create_dir_all(from.join("jobs/term_check")).unwrap();
        std::fs::write(
            from.join("jobs/term_check/problem.p"),
            b"fof(x, axiom, $true).\n",
        )
        .unwrap();
        let to = root.path().join("evidence");

        FORCED_CROSS_FILESYSTEM.with(|forced| forced.set(true));
        let result = move_evidence_out(&from, &to).await;
        FORCED_CROSS_FILESYSTEM.with(|forced| forced.set(false));

        result.expect("the forced fallback still completes an ordinary copy");
        assert!(
            !from.exists(),
            "the staged source is removed after a successful copy"
        );
        assert_eq!(
            std::fs::read(to.join("jobs/term_check/problem.p")).unwrap(),
            b"fof(x, axiom, $true).\n"
        );
    }

    /// A symlinked entry inside the staged evidence is refused exactly as
    /// a certificate tree's own entries are, and the failed fallback
    /// leaves no partial destination behind to refuse a retry.
    #[tokio::test(flavor = "current_thread")]
    async fn move_evidence_out_forced_cross_filesystem_refuses_a_symlinked_entry() {
        let root =
            OwnedDirectory::fresh(&std::env::temp_dir(), "whiel-evidence-copy-symlink").unwrap();
        let from = root.path().join("stage-evidence");
        std::fs::create_dir_all(&from).unwrap();
        let real = root.path().join("outside.p");
        std::fs::write(&real, b"fof(x, axiom, $true).\n").unwrap();
        std::os::unix::fs::symlink(&real, from.join("problem.p")).unwrap();
        let to = root.path().join("evidence");

        FORCED_CROSS_FILESYSTEM.with(|forced| forced.set(true));
        let error = move_evidence_out(&from, &to).await.unwrap_err();
        FORCED_CROSS_FILESYSTEM.with(|forced| forced.set(false));

        assert!(
            matches!(&error, CertificateBuildError::NonRegularTreeEntry { .. }),
            "{error:?}"
        );
        assert!(
            !to.exists(),
            "a failed fallback leaves no partial destination"
        );
        assert!(from.join("problem.p").is_symlink());
    }

    /// The `Invalid` branch elaborates the negated input triple; the
    /// ordinary branch elaborates the positive one. Both audit the same
    /// theorem's axiom closure.
    #[test]
    fn the_check_module_pins_each_branch_exact_target() {
        let positive = CertificateTarget::Positive.check_source(
            "Benchmark.Example0001.Certificate.Valid",
            "Whiel.Benchmark.Example0001",
            "Whiel.Benchmark.Example0001.Certificate.input_hoare_triple_valid",
        );
        assert!(positive.contains(
            "example : Whiel.HoareValid Whiel.Benchmark.Example0001.inputPre \
             Whiel.Benchmark.Example0001.inputCmd Whiel.Benchmark.Example0001.inputPost := \
             Whiel.Benchmark.Example0001.Certificate.input_hoare_triple_valid"
        ));
        assert!(positive.contains(
            "#print axioms Whiel.Benchmark.Example0001.Certificate.input_hoare_triple_valid"
        ));
        assert!(!positive.contains('¬'));

        let negated = CertificateTarget::Negated.check_source(
            "Benchmark.Example0013.Certificate.Invalid",
            "Whiel.Benchmark.Example0013",
            "Whiel.Benchmark.Example0013.Certificate.input_hoare_triple_invalid",
        );
        assert!(negated.starts_with("import Benchmark.Example0013.Certificate.Invalid\n"));
        assert!(negated.contains(
            "example : ¬ Whiel.HoareValid Whiel.Benchmark.Example0013.inputPre \
             Whiel.Benchmark.Example0013.inputCmd Whiel.Benchmark.Example0013.inputPost := \
             Whiel.Benchmark.Example0013.Certificate.input_hoare_triple_invalid"
        ));
        assert!(negated.contains(
            "#print axioms Whiel.Benchmark.Example0013.Certificate.input_hoare_triple_invalid"
        ));
    }

    /// A `profiles` function that fails on the last job fails the whole
    /// build during resolution, before the concurrent path creates its
    /// `JoinSet`, so no task is ever spawned and none can be abandoned.
    #[test]
    fn a_profile_failure_on_the_last_job_is_found_before_any_dispatch() {
        fn job(ordinal: u64) -> CertificateJob {
            CertificateJob {
                id: format!("job_{ordinal}"),
                role: "initialization".to_string(),
                ordinal,
                clause_id: Some(ordinal),
                level: Some(0),
                selector_identity: Value::Null,
                job_identity: Value::Null,
                job_digest: "0".repeat(64),
                problem_relative_path: format!("problems/{ordinal}.p"),
                problem_sha256: "1".repeat(64),
                leancheck_output_relative_path: format!("out/{ordinal}.txt"),
                proof_module_relative_path: format!("Proof{ordinal}.lean"),
                proof_module: format!("Proof{ordinal}"),
                proof_namespace: "Whiel".to_string(),
                proof_theorem: format!("theorem_{ordinal}"),
                reconstruction_module: "Reconstruction".to_string(),
                empty_check: super::super::certificate_ops::CertificateEmptyCheck {
                    encoding_version: EMPTY_DOMAIN_ENCODING_VERSION,
                    cnf_relative_path: "unused.cnf".into(),
                    cnf_sha256: "0".repeat(64),
                    lrat_relative_path: "unused.lrat".into(),
                    module_relative_path: "Unused.lean".into(),
                    module: "Unused".into(),
                    theorem: "unused".into(),
                },
            }
        }
        let jobs = (0..3).map(job).collect::<Vec<_>>();
        let asked = std::sync::Mutex::new(Vec::new());
        let profiles = |job: &CertificateJob| {
            asked.lock().unwrap().push(job.id.clone());
            if job.ordinal == 2 {
                Err(CoreFreezeError::JobNamesAnUnfrozenClause(2))
            } else {
                Ok(LeancheckProfile::new(ProofSearchProfile::Direct))
            }
        };

        let error = resolve_job_profiles(&jobs, &profiles).unwrap_err();
        assert!(
            matches!(
                error,
                CertificateBuildError::ProfileSelection { ref job_id, .. } if job_id == "job_2"
            ),
            "{error}"
        );
        assert_eq!(
            *asked.lock().unwrap(),
            vec!["job_0", "job_1", "job_2"],
            "resolution runs over the whole bundle before anything is dispatched"
        );

        // Every job resolvable: the labels come back in bundle order.
        let all_direct = |_: &CertificateJob| Ok(LeancheckProfile::new(ProofSearchProfile::Direct));
        assert_eq!(resolve_job_profiles(&jobs, &all_direct).unwrap().len(), 3);
    }

    #[test]
    fn parse_certificate_imports_keeps_only_own_tree_lines() {
        let source =
            "import Benchmark.Example0001.Certificate.Proposal\nimport Whiel.Concrete.Notation\n";
        let imports = parse_certificate_imports(source, "Benchmark.Example0001.Certificate");
        assert_eq!(imports, vec!["Benchmark.Example0001.Certificate.Proposal"]);
    }

    /// Pass 7.5g review, finding 1: the own-namespace test is on component
    /// boundaries. A neighbouring module whose name merely starts with the
    /// prefix is somebody else's, so it is neither ordered as an own-tree
    /// import nor demanded to be a module of the tree.
    #[test]
    fn the_certificate_namespace_test_respects_component_boundaries() {
        let prefix = "Benchmark.Example0001.Certificate";
        assert!(in_certificate_namespace(prefix, prefix));
        assert!(in_certificate_namespace(
            "Benchmark.Example0001.Certificate.Reconstructions.InitClause0",
            prefix
        ));
        assert!(!in_certificate_namespace(
            "Benchmark.Example0001.CertificateNotes",
            prefix
        ));
        assert!(!in_certificate_namespace(
            "Benchmark.Example0001.Input",
            prefix
        ));
        let source = "import Benchmark.Example0001.CertificateNotes\n";
        assert!(parse_certificate_imports(source, prefix).is_empty());
    }

    fn empty_resource_fixture() -> Vec<(String, String)> {
        let cnf = "p cnf 1 2\n1 0\n-1 0\n";
        let lrat = "3 0 1 2 0\n";
        let receipt = EmptyResourceReceipt {
            job_id: "term_check".into(),
            encoding_version: EMPTY_DOMAIN_ENCODING_VERSION,
            cnf_relative_path: format!("{EMPTY_RESOURCE_PREFIX}term_check.cnf"),
            cnf_sha256: bytes_sha256(cnf.as_bytes()),
            lrat_relative_path: format!("{EMPTY_RESOURCE_PREFIX}term_check.lrat"),
            lrat_sha256: bytes_sha256(lrat.as_bytes()),
            module_relative_path: "EmptyCexCheck/TermCheck.lean".into(),
            module: "Benchmark.Example0001.Certificate.EmptyCexCheck.TermCheck".into(),
            theorem: "Whiel.Benchmark.Example0001.Certificate.termNoEmpty".into(),
        };
        let manifest = EmptyResourceManifest {
            kind: EMPTY_RESOURCE_KIND.into(),
            version: 1,
            jobs: vec![receipt.clone()],
        };
        let mut files = vec![
            ("Valid.lean".into(), "-- final theorem\n".into()),
            (
                receipt.module_relative_path,
                "-- exact empty theorem\n".into(),
            ),
            (receipt.cnf_relative_path, cnf.into()),
            (receipt.lrat_relative_path, lrat.into()),
            (
                EMPTY_RESOURCE_MANIFEST.into(),
                serde_json::to_string(&manifest).unwrap(),
            ),
        ];
        files.sort_by(|a, b| a.0.cmp(&b.0));
        files
    }

    #[test]
    fn empty_resources_require_manifest_modules_and_every_exact_file() {
        let files = empty_resource_fixture();
        let prefix = Some("Benchmark.Example0001.Certificate");
        validate_empty_resources(&files, prefix).unwrap();
        assert!(
            validate_empty_resources(&files, Some("Benchmark.Example0002.Certificate")).is_err()
        );
        for required in [
            EMPTY_RESOURCE_MANIFEST,
            "EmptyCexCheck/TermCheck.lean",
            "EmptyCexCheck/Resources/term_check.cnf",
            "EmptyCexCheck/Resources/term_check.lrat",
        ] {
            let mut incomplete = files.clone();
            incomplete.retain(|(path, _)| path != required);
            assert!(
                validate_empty_resources(&incomplete, prefix).is_err(),
                "{required}"
            );
        }
        for extension in [".cnf", ".lrat"] {
            let mut changed = files.clone();
            changed
                .iter_mut()
                .find(|(path, _)| path.ends_with(extension))
                .unwrap()
                .1
                .push('\n');
            assert!(matches!(
                validate_empty_resources(&changed, prefix),
                Err(CertificateBuildError::Tampered { .. })
            ));
            assert_ne!(
                certificate_tree_digest(&files),
                certificate_tree_digest(&changed)
            );
        }
        let mut extra = files.clone();
        extra.push(("EmptyCexCheck/Resources/foreign.lrat".into(), String::new()));
        assert!(validate_empty_resources(&extra, prefix).is_err());
        let mut swapped = files.clone();
        let cnf = swapped
            .iter()
            .find(|(p, _)| p.ends_with(".cnf"))
            .unwrap()
            .1
            .clone();
        swapped
            .iter_mut()
            .find(|(p, _)| p.ends_with(".lrat"))
            .unwrap()
            .1 = cnf;
        assert!(matches!(
            validate_empty_resources(&swapped, prefix),
            Err(CertificateBuildError::Tampered { .. })
        ));
    }

    #[test]
    fn empty_resource_manifests_reject_unsupported_or_unbound_metadata() {
        let base = empty_resource_fixture();
        for field in ["version", "kind", "extra"] {
            let mut files = base.clone();
            let (_, text) = files
                .iter_mut()
                .find(|(p, _)| p == EMPTY_RESOURCE_MANIFEST)
                .unwrap();
            let mut manifest: Value = serde_json::from_str(text).unwrap();
            manifest[field] = serde_json::json!(99);
            *text = manifest.to_string();
            assert!(validate_empty_resources(&files, None).is_err(), "{field}");
        }
        for (field, value) in [
            ("encoding_version", serde_json::json!(2)),
            ("cnf_relative_path", serde_json::json!("../outside.cnf")),
            (
                "module",
                serde_json::json!("Benchmark.Example0002.Certificate.EmptyCexCheck.TermCheck"),
            ),
            ("theorem", serde_json::json!("foreign.theorem")),
            ("extra", serde_json::json!(true)),
        ] {
            let mut files = base.clone();
            let (_, text) = files
                .iter_mut()
                .find(|(p, _)| p == EMPTY_RESOURCE_MANIFEST)
                .unwrap();
            let mut manifest: Value = serde_json::from_str(text).unwrap();
            manifest["jobs"][0][field] = value;
            *text = manifest.to_string();
            assert!(
                validate_empty_resources(&files, Some("Benchmark.Example0001.Certificate"))
                    .is_err(),
                "{field}"
            );
        }
    }

    #[test]
    fn empty_resources_are_read_portably_and_symlinked_resources_are_rejected() {
        let base = std::env::temp_dir().join(format!(
            "whiel-empty-resources-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let original = base.join("original");
        let moved = base.join("moved");
        let files = empty_resource_fixture();
        for (relative, contents) in &files {
            let path = original.join(relative);
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            std::fs::write(path, contents).unwrap();
        }
        std::fs::rename(&original, &moved).unwrap();
        assert_eq!(
            read_certificate_tree(&moved, Some("Benchmark.Example0001.Certificate")).unwrap(),
            files
        );
        let resource = moved.join("EmptyCexCheck/Resources/term_check.cnf");
        let external = base.join("external.cnf");
        std::fs::rename(&resource, &external).unwrap();
        std::os::unix::fs::symlink(&external, &resource).unwrap();
        assert!(matches!(
            read_certificate_tree(&moved, None),
            Err(CertificateBuildError::NonRegularTreeEntry { .. })
        ));
        std::fs::remove_dir_all(base).unwrap();
    }

    /// Pass 7.5g review, finding 1: a tree entry that is neither a regular
    /// file nor a directory is refused, not skipped. A symlinked module
    /// would otherwise leave the compiled set silently.
    #[test]
    fn a_symlinked_tree_entry_is_refused_rather_than_skipped() {
        let base = std::env::temp_dir().join(format!(
            "whiel-certificate-tree-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("the clock is after the epoch")
                .as_nanos()
        ));
        let tree = base.join("Certificate");
        std::fs::create_dir_all(&tree).expect("create the fixture tree");
        std::fs::write(tree.join("Valid.lean"), b"-- valid\n").expect("write a module");
        assert_eq!(
            read_certificate_tree(&tree, None).expect("a tree of regular files reads"),
            vec![("Valid.lean".to_string(), "-- valid\n".to_string())]
        );

        std::fs::write(base.join("Elsewhere.lean"), b"-- elsewhere\n").expect("write a target");
        std::os::unix::fs::symlink(base.join("Elsewhere.lean"), tree.join("Extra.lean"))
            .expect("link a module in from outside the tree");
        let error = read_certificate_tree(&tree, None)
            .expect_err("a symlinked module is refused rather than dropped");
        assert!(
            matches!(&error, CertificateBuildError::NonRegularTreeEntry { path }
                if path.ends_with("Extra.lean")),
            "{error}"
        );
        let _ = std::fs::remove_dir_all(&base);
    }

    /// Pass 7.5g review, finding 1: the effective search path keeps the
    /// certificate's own namespace out of every entry that carries a
    /// compiled copy of it, and leaves everything else — including the
    /// benchmark's own compiled `Input` — reachable.
    #[test]
    fn the_shadowed_search_path_hides_only_the_certificates_own_namespace() {
        let base = std::env::temp_dir().join(format!(
            "whiel-shadow-path-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("the clock is after the epoch")
                .as_nanos()
        ));
        let library = base.join("lib");
        let benchmark = library.join("Benchmark").join("Example0001");
        std::fs::create_dir_all(benchmark.join("Certificate").join("Reconstructions"))
            .expect("create the fixture library");
        std::fs::create_dir_all(library.join("Whiel")).expect("create a sibling namespace");
        for (path, bytes) in [
            (library.join("Whiel").join("Concrete.olean"), &b"whiel"[..]),
            (library.join("Benchmark.olean"), &b"root"[..]),
            (benchmark.join("Input.olean"), &b"input"[..]),
            (
                benchmark.join("Certificate").join("Valid.olean"),
                &b"stale"[..],
            ),
            (
                benchmark
                    .join("Certificate")
                    .join("Reconstructions")
                    .join("InitClause0.olean"),
                &b"stale"[..],
            ),
        ] {
            std::fs::write(path, bytes).expect("write a fixture artifact");
        }
        let untouched = base.join("toolchain");
        std::fs::create_dir_all(&untouched).expect("create an unrelated entry");

        let shadow_root = base.join("shadow");
        let path = shadowed_lean_path(
            &format!("{}:{}", library.display(), untouched.display()),
            &shadow_root,
            "Example0001",
        )
        .expect("the search path shadows");
        let entries: Vec<&str> = path.split(':').collect();
        assert_eq!(entries.len(), 2);
        assert_ne!(entries[0], library.display().to_string());
        assert_eq!(entries[1], untouched.display().to_string());

        let shadow = Path::new(entries[0]);
        // Everything but the certificate namespace still resolves.
        assert!(shadow.join("Whiel/Concrete.olean").is_file());
        assert!(shadow.join("Benchmark.olean").is_file());
        assert!(shadow.join("Benchmark/Example0001/Input.olean").is_file());
        // The certificate namespace does not, at any depth.
        assert!(!shadow.join("Benchmark/Example0001/Certificate").exists());
        assert!(
            !shadow
                .join("Benchmark/Example0001/Certificate/Reconstructions/InitClause0.olean")
                .exists()
        );
        // The real library is untouched.
        assert!(
            benchmark
                .join("Certificate/Reconstructions/InitClause0.olean")
                .is_file()
        );
        let _ = std::fs::remove_dir_all(&base);
    }
}
