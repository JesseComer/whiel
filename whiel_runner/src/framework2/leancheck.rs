//! Pinned leancheck Vampire resolution and opaque process execution.
//!
//! This module launches the repository-pinned `leancheck`-mode Vampire
//! binary and captures its raw output. It never parses or interprets the
//! problem it sends or the proof text it receives; classification is by
//! process facts only (exit status, timeout, cancellation, and whether the
//! `theorem fullProof` marker is present). `--output_mode lean` (part of
//! every pinned argument profile) makes Vampire print a Lean proof script
//! ending in a `theorem fullProof` declaration instead of an ordinary TPTP
//! `% SZS status` line; this is the same success marker the legacy Python
//! verification pipeline uses (`whiel_synth.verification.tier1_bundle`).

use std::ffi::OsString;
use std::fmt;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::thread;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use serde_json::{Value, json};
use tokio::time::{Instant as TokioInstant, sleep_until};

use crate::runtime::CancellationToken;
use crate::vampire::{
    PROOF_CASC_AVATAR, PROOF_CASC_CORES, PROOF_CASC_PROFILE_ID, PROOF_CASC_RANDOM_SEED,
    PROOF_CASC_RANDOMIZE_WORKER_SEEDS, PROOF_CASC_SCHEDULE, PROOF_CASC_SHUFFLE_SCHEDULE_REPEATS,
};

use super::production::ProofSearchProfile;

const LOCK_FILENAME: &str = "toolchain.lock.json";
const LOCK_FORMAT_VERSION: u64 = 3;
const LEANCHECK_ROLE: &str = "leancheck_vampire";
/// A successful leancheck proof's first line, matched with optional leading
/// whitespace (see [`contains_full_proof_theorem`]); never an unanchored
/// substring, so a "theorem fullProof" appearing incidentally inside a
/// diagnostic or comment line can never count.
const FULL_PROOF_MARKER_LINE_PREFIX: &str = "theorem fullProof";
/// The last non-blank line of a complete leancheck proof script. Requiring
/// this too (alongside [`FULL_PROOF_MARKER_LINE_PREFIX`]) rejects a proof
/// truncated by a timeout or crash — which would carry the opening marker
/// but never reach this closing one — as [`LeancheckError::NoTheorem`]
/// instead of accepting a partial script as a packaged success.
const END_VAMPROOF_LINE: &str = "end vamproof";
const MAX_DIAGNOSTIC_BYTES: usize = 4096;

/// Convert a boolean to the Vampire on/off spelling.
const fn on_off(enabled: bool) -> &'static str {
    if enabled { "on" } else { "off" }
}

// ------------------------------------------------------------
// Pinned Argument Profiles
// ------------------------------------------------------------

/// One of the two pinned leancheck-verification argument profiles.
///
/// `Direct` mirrors the legacy deterministic AVATAR-on leancheck profile,
/// a single-core schedule whose AVATAR helpers are rewritten to
/// kernel-checked LRAT before publication. `Casc2025` is the deterministic
/// single-core `casc_2025` portfolio schedule of the search phase with
/// leancheck proof output; there is no per-job fallback between profiles.
///
/// No API accepts extra arguments, and `arguments` returns exactly one of
/// the two pinned vectors. Same-job fallback between profiles is therefore
/// impossible by construction: a caller that wants the other profile must
/// submit a distinct job with a distinct [`LeancheckProfile`], never retry
/// the same job under a different argument vector.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LeancheckProfile(ProofSearchProfile);

impl LeancheckProfile {
    pub fn new(profile: ProofSearchProfile) -> Self {
        Self(profile)
    }

    pub fn profile(self) -> ProofSearchProfile {
        self.0
    }

    fn identity_name(self) -> &'static str {
        match self.0 {
            ProofSearchProfile::Direct => "direct",
            ProofSearchProfile::Casc2025 => "casc_2025",
        }
    }

    /// The exact pinned leancheck argument vector for this profile, with
    /// `time_limit_seconds` substituted for Vampire's `--time_limit` value.
    pub fn arguments(&self, time_limit_seconds: u64) -> Vec<OsString> {
        match self.0 {
            ProofSearchProfile::Direct => [
                "--proof",
                "leancheck",
                "--proof_extra",
                "lean",
                "--skolemization",
                "syntactic",
                "--output_mode",
                "lean",
            ]
            .into_iter()
            .map(OsString::from)
            .chain([
                OsString::from("--time_limit"),
                OsString::from(time_limit_seconds.to_string()),
                OsString::from("--avatar"),
                OsString::from("on"),
                OsString::from("--random_seed"),
                OsString::from("1"),
            ])
            .collect(),
            ProofSearchProfile::Casc2025 => [
                OsString::from("--mode"),
                OsString::from("portfolio"),
                OsString::from("--schedule"),
                OsString::from(PROOF_CASC_SCHEDULE),
                OsString::from("--cores"),
                OsString::from(PROOF_CASC_CORES.to_string()),
                OsString::from("--random_seed"),
                OsString::from(PROOF_CASC_RANDOM_SEED),
                OsString::from("--randomize_seed_for_portfolio_workers"),
                OsString::from(on_off(PROOF_CASC_RANDOMIZE_WORKER_SEEDS)),
                OsString::from("--shuffle_on_schedule_repeats"),
                OsString::from(on_off(PROOF_CASC_SHUFFLE_SCHEDULE_REPEATS)),
                OsString::from("--avatar"),
                OsString::from(on_off(PROOF_CASC_AVATAR)),
                OsString::from("--time_limit"),
                OsString::from(time_limit_seconds.to_string()),
                OsString::from("--proof"),
                OsString::from("leancheck"),
                OsString::from("--proof_extra"),
                OsString::from("lean"),
                OsString::from("--skolemization"),
                OsString::from("syntactic"),
                OsString::from("--output_mode"),
                OsString::from("lean"),
            ]
            .into_iter()
            .collect(),
        }
    }
}

// ------------------------------------------------------------
// Pinned Binary Resolution
// ------------------------------------------------------------

/// The repository-pinned leancheck Vampire binary, verified before launch.
///
/// [`Self::from_lock`] resolves `<repository_root>/toolchain.lock.json`'s
/// `leancheck_vampire` role, reads the binary's bytes, and compares their
/// SHA-256 against the lock. Verification completes before this returns;
/// nothing is launched by this type until [`LeancheckRun::execute`].
#[derive(Clone, Debug)]
pub struct PinnedLeancheckVampire {
    path: PathBuf,
    sha256: Arc<str>,
}

impl PinnedLeancheckVampire {
    pub fn from_lock(repository_root: &Path) -> Result<Self, LeancheckError> {
        let lock_path = repository_root.join(LOCK_FILENAME);
        let bytes = std::fs::read(&lock_path).map_err(|error| {
            LeancheckError::Io(format!("read {}: {error}", lock_path.display()))
        })?;
        let lock: Value = serde_json::from_slice(&bytes)
            .map_err(|error| LeancheckError::Lock(format!("parse {LOCK_FILENAME}: {error}")))?;
        if lock.get("format_version").and_then(Value::as_u64) != Some(LOCK_FORMAT_VERSION) {
            return Err(LeancheckError::Lock(format!(
                "{LOCK_FILENAME} is not format_version {LOCK_FORMAT_VERSION}"
            )));
        }
        let role = lock
            .get("roles")
            .and_then(|roles| roles.get(LEANCHECK_ROLE))
            .and_then(Value::as_object)
            .ok_or_else(|| {
                LeancheckError::Lock(format!("{LOCK_FILENAME} has no {LEANCHECK_ROLE} role"))
            })?;
        let relative = role
            .get("path")
            .and_then(Value::as_str)
            .ok_or_else(|| LeancheckError::Lock(format!("{LEANCHECK_ROLE} role has no path")))?;
        let relative_path = Path::new(relative);
        if relative_path.is_absolute()
            || relative_path
                .components()
                .any(|component| component.as_os_str() == "..")
        {
            return Err(LeancheckError::Lock(format!(
                "{LEANCHECK_ROLE} path is not repository-relative"
            )));
        }
        let path = repository_root.join(relative_path);
        if !path.is_file() {
            return Err(LeancheckError::MissingBinary(path));
        }
        let expected_sha256 = locked_role_sha256(role, LEANCHECK_ROLE)?;
        let actual_sha256 = hash_file(&path)?;
        if actual_sha256 != expected_sha256 {
            return Err(LeancheckError::Sha256Mismatch {
                expected: expected_sha256,
                actual: actual_sha256,
            });
        }
        Ok(Self {
            path,
            sha256: Arc::from(actual_sha256),
        })
    }

    pub fn path(&self) -> &Path {
        &self.path
    }

    pub fn sha256(&self) -> &str {
        &self.sha256
    }

    /// Build a pinned handle without verifying it against a toolchain
    /// lock, for tests that stand in a fake leancheck Vampire script.
    ///
    /// Production code always goes through [`Self::from_lock`]; this
    /// constructor exists only so tests can exercise [`LeancheckRun`]'s
    /// callers against scripted failure, timeout, and cancellation
    /// fixtures without a real pinned binary.
    #[cfg(feature = "test-hooks")]
    #[doc(hidden)]
    pub fn unverified_for_tests(path: PathBuf, sha256: impl Into<Arc<str>>) -> Self {
        Self {
            path,
            sha256: sha256.into(),
        }
    }

    /// Small identity JSON binding the pinned binary to one launch profile.
    pub fn invocation_identity(&self, profile: LeancheckProfile, time_limit_seconds: u64) -> Value {
        json!({
            "kind": "whiel_pinned_leancheck_vampire",
            "path": self.path.to_string_lossy(),
            "sha256": self.sha256.as_ref(),
            "profile_id": PROOF_CASC_PROFILE_ID,
            "profile": profile.identity_name(),
            "arguments": profile
                .arguments(time_limit_seconds)
                .iter()
                .map(|argument| argument.to_string_lossy().into_owned())
                .collect::<Vec<_>>(),
        })
    }
}

// ------------------------------------------------------------
// Pinned Kernel-LRAT CaDiCaL Resolution
// ------------------------------------------------------------

const KERNEL_LRAT_CADICAL_ROLE: &str = "kernel_lrat_cadical";
/// The only resolver this reader implements: the CaDiCaL that ships beside
/// the pinned Lean, which is the one Mathlib's LRAT checker was built
/// against. Any other spelling in the lock is a fail-closed refusal, never
/// a search of the host for something else called `cadical`.
const KERNEL_LRAT_CADICAL_RESOLVER: &str = "adjacent-to-lean";

/// The CaDiCaL pinned by `toolchain.lock.json`'s `kernel_lrat_cadical`
/// role, verified before it is ever launched.
///
/// It is only ever used to produce an LRAT refutation trace for a SAT
/// problem that was read out of Vampire's own emitted text; the trace is
/// then validated and turned into a kernel-checked `lrat_proof`. The binary
/// is therefore outside the trust boundary — a wrong trace cannot make a
/// bad proof pass, only make a good one fail — but it is pinned anyway so a
/// certificate rebuild is reproducible.
#[derive(Clone, Debug)]
pub struct PinnedKernelLratCadical {
    path: PathBuf,
    sha256: Arc<str>,
    version: Arc<str>,
    arguments: Vec<String>,
}

impl PinnedKernelLratCadical {
    /// Resolve, digest-check and then version-check the pinned CaDiCaL.
    ///
    /// The Lean toolchain prefix comes from `lean --print-prefix` run in
    /// `repository_root`, so the binary is the one the repository's own
    /// `lean-toolchain` pin selects.
    pub fn from_lock(repository_root: &Path) -> Result<Self, KernelLratCadicalError> {
        let prefix = lean_toolchain_prefix(repository_root)?;
        Self::from_lock_under_prefix(repository_root, &prefix)
    }

    fn from_lock_under_prefix(
        repository_root: &Path,
        lean_prefix: &Path,
    ) -> Result<Self, KernelLratCadicalError> {
        let lock_path = repository_root.join(LOCK_FILENAME);
        let bytes = std::fs::read(&lock_path).map_err(|error| {
            KernelLratCadicalError::Io(format!("read {}: {error}", lock_path.display()))
        })?;
        let lock: Value = serde_json::from_slice(&bytes).map_err(|error| {
            KernelLratCadicalError::Lock(format!("parse {LOCK_FILENAME}: {error}"))
        })?;
        if lock.get("format_version").and_then(Value::as_u64) != Some(LOCK_FORMAT_VERSION) {
            return Err(KernelLratCadicalError::Lock(format!(
                "{LOCK_FILENAME} is not format_version {LOCK_FORMAT_VERSION}"
            )));
        }
        let role = lock
            .get("roles")
            .and_then(|roles| roles.get(KERNEL_LRAT_CADICAL_ROLE))
            .and_then(Value::as_object)
            .ok_or_else(|| {
                KernelLratCadicalError::Lock(format!(
                    "{LOCK_FILENAME} has no {KERNEL_LRAT_CADICAL_ROLE} role"
                ))
            })?;
        if role.get("resolver").and_then(Value::as_str) != Some(KERNEL_LRAT_CADICAL_RESOLVER) {
            return Err(KernelLratCadicalError::Lock(format!(
                "{KERNEL_LRAT_CADICAL_ROLE} role is not resolved {KERNEL_LRAT_CADICAL_RESOLVER}"
            )));
        }
        let version = role
            .get("version")
            .and_then(Value::as_str)
            .filter(|version| !version.is_empty())
            .ok_or_else(|| {
                KernelLratCadicalError::Lock(format!(
                    "{KERNEL_LRAT_CADICAL_ROLE} role has no version"
                ))
            })?
            .to_string();
        let arguments = role
            .get("arguments")
            .and_then(Value::as_array)
            .and_then(|arguments| {
                arguments
                    .iter()
                    .map(|argument| argument.as_str().map(str::to_string))
                    .collect::<Option<Vec<_>>>()
            })
            .filter(|arguments: &Vec<String>| !arguments.is_empty())
            .ok_or_else(|| {
                KernelLratCadicalError::Lock(format!(
                    "{KERNEL_LRAT_CADICAL_ROLE} role has no arguments"
                ))
            })?;
        let expected_sha256 = locked_role_sha256(role, KERNEL_LRAT_CADICAL_ROLE)
            .map_err(|error| KernelLratCadicalError::Lock(error.to_string()))?;

        let path = lean_prefix.join("bin").join("cadical");
        let metadata = std::fs::symlink_metadata(&path)
            .map_err(|_| KernelLratCadicalError::MissingBinary(path.clone()))?;
        // `inspect_cadical`'s rule: a regular file beside the pinned Lean,
        // never a symlink that could be repointed at another solver.
        if !metadata.is_file() {
            return Err(KernelLratCadicalError::MissingBinary(path));
        }
        // Digest first, then version: the version check runs the binary, so
        // nothing is launched until its bytes are the locked bytes. This is
        // the order [`PinnedLeancheckVampire::from_lock`] and the legacy
        // Python lock reader both use.
        let actual_sha256 =
            crate::entailment::assembly::hash_file_sha256(&path).map_err(|error| {
                KernelLratCadicalError::Io(format!("hash {}: {error}", path.display()))
            })?;
        if actual_sha256 != expected_sha256 {
            return Err(KernelLratCadicalError::Sha256Mismatch {
                expected: expected_sha256,
                actual: actual_sha256,
            });
        }
        let actual_version = cadical_version(&path, repository_root)?;
        if actual_version != version {
            return Err(KernelLratCadicalError::VersionMismatch {
                expected: version,
                actual: actual_version,
            });
        }
        Ok(Self {
            path,
            sha256: Arc::from(actual_sha256),
            version: Arc::from(version),
            arguments,
        })
    }

    pub fn path(&self) -> &Path {
        &self.path
    }

    pub fn sha256(&self) -> &str {
        &self.sha256
    }

    pub fn version(&self) -> &str {
        &self.version
    }

    /// Exactly the locked argument vector; nothing is appended and nothing
    /// is substituted.
    pub fn arguments(&self) -> &[String] {
        &self.arguments
    }

    /// Identity JSON for the build receipt, beside the environment
    /// contract the solver runs under.
    pub fn invocation_identity(&self) -> Value {
        json!({
            "kind": "whiel_pinned_kernel_lrat_cadical",
            "resolver": KERNEL_LRAT_CADICAL_RESOLVER,
            "path": self.path.to_string_lossy(),
            "sha256": self.sha256.as_ref(),
            "version": self.version.as_ref(),
            "arguments": self.arguments.clone(),
            "environment_contract":
                crate::framework2::proof_transform::lrat::CADICAL_ENVIRONMENT_CONTRACT,
        })
    }
}

/// The Lean toolchain prefix the repository's own pin selects.
fn lean_toolchain_prefix(repository_root: &Path) -> Result<PathBuf, KernelLratCadicalError> {
    let output = std::process::Command::new("lean")
        .arg("--print-prefix")
        .current_dir(repository_root)
        .output()
        .map_err(|error| KernelLratCadicalError::Io(format!("run lean --print-prefix: {error}")))?;
    if !output.status.success() {
        return Err(KernelLratCadicalError::Io(format!(
            "lean --print-prefix exited with {:?}",
            output.status.code()
        )));
    }
    let prefix = String::from_utf8_lossy(&output.stdout).trim().to_string();
    if prefix.is_empty() {
        return Err(KernelLratCadicalError::Io(
            "lean --print-prefix printed no toolchain prefix".to_string(),
        ));
    }
    Ok(PathBuf::from(prefix))
}

fn cadical_version(path: &Path, repository_root: &Path) -> Result<String, KernelLratCadicalError> {
    let output = std::process::Command::new(path)
        .arg("--version")
        .current_dir(repository_root)
        .output()
        .map_err(|error| {
            KernelLratCadicalError::Io(format!("run {} --version: {error}", path.display()))
        })?;
    if !output.status.success() {
        return Err(KernelLratCadicalError::Io(format!(
            "{} --version exited with {:?}",
            path.display(),
            output.status.code()
        )));
    }
    Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
}

/// Errors resolving the pinned kernel-LRAT CaDiCaL.
#[derive(Clone, Debug)]
pub enum KernelLratCadicalError {
    /// The toolchain lock is missing, malformed, or names no such role.
    Lock(String),
    /// No regular `cadical` beside the pinned Lean.
    MissingBinary(PathBuf),
    /// The adjacent binary reports a version the lock does not name.
    VersionMismatch { expected: String, actual: String },
    /// The adjacent binary's bytes disagree with the locked digest.
    Sha256Mismatch { expected: String, actual: String },
    /// A filesystem or process-launch operation failed.
    Io(String),
}

impl fmt::Display for KernelLratCadicalError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Lock(detail) => {
                write!(formatter, "pinned kernel-LRAT CaDiCaL lock error: {detail}")
            }
            Self::MissingBinary(path) => write!(
                formatter,
                "the pinned Lean toolchain has no regular adjacent CaDiCaL binary: {}",
                path.display()
            ),
            Self::VersionMismatch { expected, actual } => write!(
                formatter,
                "pinned kernel-LRAT CaDiCaL version mismatch: expected {expected}, found {actual}"
            ),
            Self::Sha256Mismatch { expected, actual } => write!(
                formatter,
                "pinned kernel-LRAT CaDiCaL digest mismatch: expected {expected}, found {actual}"
            ),
            Self::Io(detail) => {
                write!(formatter, "pinned kernel-LRAT CaDiCaL I/O error: {detail}")
            }
        }
    }
}

impl std::error::Error for KernelLratCadicalError {}

fn locked_role_sha256(
    role: &serde_json::Map<String, Value>,
    role_name: &str,
) -> Result<String, LeancheckError> {
    let platform_key = host_platform_key()?;
    let raw = role
        .get("sha256")
        .ok_or_else(|| LeancheckError::Lock(format!("{role_name} role has no sha256")))?;
    let digest = match raw {
        Value::String(value) => value.clone(),
        Value::Object(map) => map
            .get(&platform_key)
            .and_then(Value::as_str)
            .ok_or_else(|| {
                LeancheckError::Lock(format!("{role_name} role has no sha256 for {platform_key}"))
            })?
            .to_string(),
        _ => {
            return Err(LeancheckError::Lock(format!(
                "{role_name} role sha256 is malformed"
            )));
        }
    };
    if digest.len() != 64
        || !digest
            .bytes()
            .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
    {
        return Err(LeancheckError::Lock(format!(
            "{role_name} role sha256 is not lowercase hex-64"
        )));
    }
    Ok(digest)
}

/// `<sysname>-<machine>` (e.g. `Darwin-arm64`), matching the toolchain
/// lock's platform-keyed digests and Python's `platform.system()-
/// platform.machine()` (`whiel_synth.verification.toolchain_lock
/// .host_platform_key`).
#[cfg(any(target_os = "macos", target_os = "linux"))]
fn host_platform_key() -> Result<String, LeancheckError> {
    // SAFETY: `uname` fills a caller-owned, zero-initialized buffer and
    // returns 0 on success; on success every field is a NUL-terminated C
    // string within its fixed-size array.
    unsafe {
        let mut info: libc::utsname = std::mem::zeroed();
        if libc::uname(&mut info) != 0 {
            return Err(LeancheckError::Lock(
                "read host uname(2) identity".to_string(),
            ));
        }
        let sysname = std::ffi::CStr::from_ptr(info.sysname.as_ptr())
            .to_string_lossy()
            .into_owned();
        let machine = std::ffi::CStr::from_ptr(info.machine.as_ptr())
            .to_string_lossy()
            .into_owned();
        Ok(format!("{sysname}-{machine}"))
    }
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
fn host_platform_key() -> Result<String, LeancheckError> {
    Err(LeancheckError::Lock(
        "the pinned leancheck Vampire toolchain lock is unsupported on this platform".to_string(),
    ))
}

fn hash_file(path: &Path) -> Result<String, LeancheckError> {
    crate::entailment::assembly::hash_file_sha256(path)
        .map_err(|error| LeancheckError::Io(format!("hash {}: {error}", path.display())))
}

// ------------------------------------------------------------
// Opaque Process Execution
// ------------------------------------------------------------

/// Opaque result of one successful pinned leancheck run.
#[derive(Clone, Debug)]
pub struct LeancheckOutput {
    /// The child's raw, unparsed stdout bytes.
    pub raw: Vec<u8>,
    pub raw_sha256: String,
    pub elapsed: Duration,
    pub invocation_identity: Value,
}

/// Marker type for launching the pinned leancheck Vampire binary.
pub struct LeancheckRun;

impl LeancheckRun {
    /// Run the pinned leancheck Vampire binary over `problem_bytes`.
    ///
    /// `problem_bytes` is staged to a private temp file and never parsed.
    /// `deadline` both bounds the external process supervision and (rounded
    /// up to whole seconds) becomes the profile's own `--time_limit`. The
    /// pinned binary is re-hashed immediately before this exact launch
    /// (streaming) and rejected with [`LeancheckError::Sha256Mismatch`] if
    /// it disagrees with `pinned`'s already-verified digest, narrowing the
    /// gap between verification (in [`PinnedLeancheckVampire::from_lock`])
    /// and execution. The child leads its own process group — `casc_2025`
    /// runs `--mode portfolio`, which fans out into several worker
    /// processes — and the whole group, not just the direct child, is
    /// killed and reaped on cancellation or deadline expiry, so no
    /// portfolio worker is ever left orphaned. Both captured streams are
    /// bounded; a stream that exceeds the cap is reported as
    /// [`LeancheckError::OutputTooLarge`] rather than silently truncated
    /// into an apparent success. Success requires a zero exit status and a
    /// line starting with `theorem fullProof` followed, eventually, by a
    /// closing `end vamproof` line in stdout, so a proof cut short by a
    /// timeout or a crash classifies as [`LeancheckError::NoTheorem`], never
    /// as a packaged success.
    pub async fn execute(
        pinned: &PinnedLeancheckVampire,
        profile: LeancheckProfile,
        problem_bytes: &[u8],
        deadline: Duration,
        cancellation: &CancellationToken,
    ) -> Result<LeancheckOutput, LeancheckError> {
        if cancellation.is_cancelled() {
            return Err(LeancheckError::Cancelled);
        }

        let launch_sha256 = hash_file(pinned.path())?;
        if launch_sha256 != pinned.sha256() {
            return Err(LeancheckError::Sha256Mismatch {
                expected: pinned.sha256().to_string(),
                actual: launch_sha256,
            });
        }

        let problem_file = TempProblemFile::write(problem_bytes)?;
        let time_limit_seconds = deadline.as_secs().max(1);
        let mut arguments = profile.arguments(time_limit_seconds);
        arguments.push(problem_file.path().as_os_str().to_os_string());
        let cwd = problem_file
            .path()
            .parent()
            .expect("the staged problem file has a parent directory")
            .to_path_buf();
        let executable = pinned.path().to_path_buf();

        let started = Instant::now();
        let captured =
            run_leancheck_process_group(executable, arguments, cwd, deadline, cancellation).await;
        let elapsed = started.elapsed();
        let captured = captured?;

        if !captured.status.success() {
            return Err(LeancheckError::NonZeroExit {
                code: captured.status.code(),
                stderr: bounded_diagnostic(&captured.stderr),
            });
        }
        if !contains_full_proof_theorem(&captured.stdout) {
            return Err(LeancheckError::NoTheorem {
                stderr: bounded_diagnostic(&captured.stderr),
            });
        }

        let raw_sha256 = crate::encoding::bytes_sha256(&captured.stdout);
        let invocation_identity = pinned.invocation_identity(profile, time_limit_seconds);
        Ok(LeancheckOutput {
            raw: captured.stdout,
            raw_sha256,
            elapsed,
            invocation_identity,
        })
    }
}

/// The bounded stdout/stderr of one leancheck Vampire process that actually
/// exited (never one that was cancelled, timed out, or whose capture
/// failed — those are reported as an [`LeancheckError`] before this is
/// constructed).
struct CapturedLeancheckExit {
    status: std::process::ExitStatus,
    stdout: Vec<u8>,
    stderr: Vec<u8>,
}

/// Per-stream capture cap: generous enough that no real leancheck proof
/// output is ever truncated, while still bounding worst-case memory use
/// against a runaway or misbehaving child.
const MAX_CAPTURED_STREAM_BYTES: usize = 256 * 1024 * 1024;

/// Launch the pinned leancheck Vampire in its own process group and
/// supervise it to completion, cancellation, or deadline expiry.
///
/// Bridges [`crate::vampire::process::SpawnedProcess`]'s blocking,
/// thread-based supervision (the same machinery every ordinary Vampire
/// worker launch uses for process-group cleanup) into this async context
/// via [`tokio::task::spawn_blocking`]. `SpawnedProcess::supervise` only
/// understands one [`CancellationToken`], so this combines `cancellation`
/// and `deadline` into one fresh, call-local token before handing it to the
/// blocking supervisor, then tells the two causes apart afterward from
/// `cancellation`'s own state (the combined token itself is never observed
/// outside this function).
#[cfg(any(target_os = "macos", target_os = "linux"))]
async fn run_leancheck_process_group(
    executable: PathBuf,
    arguments: Vec<OsString>,
    cwd: PathBuf,
    deadline: Duration,
    cancellation: &CancellationToken,
) -> Result<CapturedLeancheckExit, LeancheckError> {
    use crate::vampire::process::StopReason;

    let run_token = CancellationToken::new();
    let deadline_instant = TokioInstant::now() + deadline;
    let watcher_token = run_token.clone();
    let caller_cancellation = cancellation.clone();
    let watcher = tokio::spawn(async move {
        tokio::select! {
            _ = caller_cancellation.cancelled() => {}
            _ = sleep_until(deadline_instant) => {}
        }
        watcher_token.cancel();
    });

    let blocking_token = run_token.clone();
    let join_result = tokio::task::spawn_blocking(move || {
        run_leancheck_process_group_blocking(&executable, &arguments, &cwd, &blocking_token)
    })
    .await;
    watcher.abort();

    let outcome = join_result
        .map_err(|error| LeancheckError::Io(format!("join leancheck process task: {error}")))??;

    if let Some(cleanup_error) = outcome.cleanup_error {
        return Err(LeancheckError::Io(format!(
            "leancheck Vampire process-group cleanup failed: {cleanup_error}"
        )));
    }
    match outcome.reason {
        StopReason::Exited => {}
        StopReason::Cancelled => {
            return Err(if cancellation.is_cancelled() {
                LeancheckError::Cancelled
            } else {
                LeancheckError::Timeout
            });
        }
        StopReason::CaptureFailed => {
            return Err(LeancheckError::Io(outcome.stream_error.unwrap_or_else(
                || "leancheck Vampire output capture failed".to_string(),
            )));
        }
    }
    if outcome.stdout_overflowed {
        return Err(LeancheckError::OutputTooLarge {
            stream: "stdout",
            limit: MAX_CAPTURED_STREAM_BYTES,
        });
    }
    if outcome.stderr_overflowed {
        return Err(LeancheckError::OutputTooLarge {
            stream: "stderr",
            limit: MAX_CAPTURED_STREAM_BYTES,
        });
    }
    let status = outcome
        .status
        .map_err(|error| LeancheckError::Io(format!("wait for leancheck Vampire: {error}")))?;
    Ok(CapturedLeancheckExit {
        status,
        stdout: outcome.stdout,
        stderr: outcome.stderr,
    })
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
async fn run_leancheck_process_group(
    _executable: PathBuf,
    _arguments: Vec<OsString>,
    _cwd: PathBuf,
    _deadline: Duration,
    _cancellation: &CancellationToken,
) -> Result<CapturedLeancheckExit, LeancheckError> {
    Err(LeancheckError::Io(
        "leancheck Vampire process-group supervision is unsupported on this platform".to_string(),
    ))
}

/// The blocking, thread-supervised outcome of one leancheck Vampire launch,
/// before [`run_leancheck_process_group`] classifies it into a
/// [`LeancheckError`] or a [`CapturedLeancheckExit`].
#[cfg(any(target_os = "macos", target_os = "linux"))]
struct LeancheckProcessGroupOutcome {
    reason: crate::vampire::process::StopReason,
    status: std::io::Result<std::process::ExitStatus>,
    cleanup_error: Option<String>,
    stdout: Vec<u8>,
    stdout_overflowed: bool,
    stderr: Vec<u8>,
    stderr_overflowed: bool,
    stream_error: Option<String>,
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
fn run_leancheck_process_group_blocking(
    executable: &Path,
    arguments: &[OsString],
    cwd: &Path,
    cancellation: &CancellationToken,
) -> Result<LeancheckProcessGroupOutcome, LeancheckError> {
    use crate::vampire::process::{SpawnError, SpawnedProcess};

    let mut process =
        SpawnedProcess::spawn(executable, arguments, cwd).map_err(|error| match error {
            SpawnError::Failed(detail) | SpawnError::CleanupFailed(detail) => {
                LeancheckError::Io(format!("start leancheck Vampire: {detail}"))
            }
        })?;
    let pipes = process
        .take_pipes()
        .map_err(|error| LeancheckError::Io(format!("take leancheck Vampire pipes: {error}")))?;

    let capture_failed = Arc::new(AtomicBool::new(false));
    let stdout_handle = spawn_capture_thread(
        "leancheck-stdout-capture",
        pipes.stdout,
        Arc::clone(&capture_failed),
    )?;
    let stderr_handle = spawn_capture_thread(
        "leancheck-stderr-capture",
        pipes.stderr,
        Arc::clone(&capture_failed),
    )?;

    // Runs concurrently with both capture threads: it polls for exit or
    // cancellation and, on either, kills and reaps the whole process
    // group (see `SpawnedProcess::supervise`), never just the direct
    // child. Draining both pipes to EOF (below) is what lets a child
    // blocked on a full pipe actually observe that signal and exit.
    let supervised = process.supervise(cancellation, &capture_failed);

    let stdout = join_capture_thread(stdout_handle);
    let stderr = join_capture_thread(stderr_handle);

    Ok(LeancheckProcessGroupOutcome {
        reason: supervised.reason,
        status: supervised.status,
        cleanup_error: supervised.cleanup_error,
        stdout: stdout.bytes,
        stdout_overflowed: stdout.overflowed,
        stderr: stderr.bytes,
        stderr_overflowed: stderr.overflowed,
        stream_error: stdout.error.or(stderr.error),
    })
}

/// One bounded-capture thread's outcome: see [`read_capped`].
#[cfg(any(target_os = "macos", target_os = "linux"))]
struct CapturedStreamBytes {
    bytes: Vec<u8>,
    overflowed: bool,
    error: Option<String>,
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
fn spawn_capture_thread(
    name: &str,
    reader: impl std::io::Read + Send + 'static,
    capture_failed: Arc<AtomicBool>,
) -> Result<thread::JoinHandle<CapturedStreamBytes>, LeancheckError> {
    thread::Builder::new()
        .name(name.to_string())
        .spawn(move || read_capped(reader, MAX_CAPTURED_STREAM_BYTES, &capture_failed))
        .map_err(|error| LeancheckError::Io(format!("start {name} thread: {error}")))
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
fn join_capture_thread(handle: thread::JoinHandle<CapturedStreamBytes>) -> CapturedStreamBytes {
    handle.join().unwrap_or_else(|_| CapturedStreamBytes {
        bytes: Vec::new(),
        overflowed: false,
        error: Some("leancheck capture thread panicked".to_string()),
    })
}

/// Read `reader` to EOF, retaining at most `cap` bytes.
///
/// Bytes beyond `cap` are still drained (never left unread, which would
/// block a child still writing to a full pipe) but discarded; the overflow
/// is reported as a bool rather than silently truncating the capture into
/// an apparently-complete result. A genuine I/O error sets `capture_failed`
/// so the concurrent [`SpawnedProcess::supervise`] loop does not wait out
/// the full deadline for a pipe that will never produce more data.
#[cfg(any(target_os = "macos", target_os = "linux"))]
fn read_capped(
    mut reader: impl std::io::Read,
    cap: usize,
    capture_failed: &AtomicBool,
) -> CapturedStreamBytes {
    let mut collected = Vec::new();
    let mut overflowed = false;
    let mut buffer = [0_u8; 64 * 1024];
    loop {
        match reader.read(&mut buffer) {
            Ok(0) => break,
            Ok(count) => {
                if !overflowed {
                    let remaining = cap.saturating_sub(collected.len());
                    let take = remaining.min(count);
                    collected.extend_from_slice(&buffer[..take]);
                    if take < count {
                        overflowed = true;
                    }
                }
            }
            Err(error) if error.kind() == std::io::ErrorKind::Interrupted => {}
            Err(error) => {
                capture_failed.store(true, Ordering::Release);
                return CapturedStreamBytes {
                    bytes: collected,
                    overflowed,
                    error: Some(format!("read leancheck output: {error}")),
                };
            }
        }
    }
    CapturedStreamBytes {
        bytes: collected,
        overflowed,
        error: None,
    }
}

fn contains_full_proof_theorem(stdout: &[u8]) -> bool {
    let text = String::from_utf8_lossy(stdout);
    let Some(theorem_line) = text
        .lines()
        .position(|line| line.trim_start().starts_with(FULL_PROOF_MARKER_LINE_PREFIX))
    else {
        return false;
    };
    // `end vamproof` closes the proof term itself; real leancheck Vampire
    // output goes on to print trailing `--`-commented run statistics after
    // it, so this only requires the closing line to appear *after* the
    // theorem (never that it be the file's last line), which is still
    // enough to reject a proof cut short mid-term by a timeout or crash —
    // that never reaches `end vamproof` at all.
    text.lines()
        .skip(theorem_line + 1)
        .any(|line| line.trim() == END_VAMPROOF_LINE)
}

fn bounded_diagnostic(bytes: &[u8]) -> String {
    let bound = bytes.len().min(MAX_DIAGNOSTIC_BYTES);
    String::from_utf8_lossy(&bytes[..bound]).into_owned()
}

/// A private staged copy of one opaque problem, removed on drop.
struct TempProblemFile {
    path: PathBuf,
}

static NEXT_TEMP_PROBLEM: AtomicU64 = AtomicU64::new(0);

impl TempProblemFile {
    fn write(problem_bytes: &[u8]) -> Result<Self, LeancheckError> {
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_err(|error| LeancheckError::Io(format!("read system clock: {error}")))?
            .as_nanos();
        Self::write_at(&std::env::temp_dir(), nanos, problem_bytes)
    }

    fn write_at(root: &Path, nanos: u128, problem_bytes: &[u8]) -> Result<Self, LeancheckError> {
        // Clock readings can coincide across concurrent jobs. Never reuse a
        // process-local sequence, even if the clock repeats or moves backward.
        let sequence = NEXT_TEMP_PROBLEM
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |value| {
                value.checked_add(1)
            })
            .map_err(|_| LeancheckError::Io("temporary problem sequence exhausted".to_string()))?;
        let path = root.join(format!(
            "whiel_leancheck_problem_{}_{nanos}_{sequence}.p",
            std::process::id()
        ));
        Self::create(path, problem_bytes)
    }

    fn create(path: PathBuf, problem_bytes: &[u8]) -> Result<Self, LeancheckError> {
        // Exclusive creation also refuses stale files and symlinks. Construct
        // the guard only after ownership is established, so a failed create
        // cannot remove someone else's file, while a failed write removes ours.
        let mut file = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&path)
            .map_err(|error| LeancheckError::Io(format!("create {}: {error}", path.display())))?;
        let staged = Self { path };
        file.write_all(problem_bytes).map_err(|error| {
            LeancheckError::Io(format!("write {}: {error}", staged.path.display()))
        })?;
        Ok(staged)
    }

    fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for TempProblemFile {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.path);
    }
}

// ------------------------------------------------------------
// Errors
// ------------------------------------------------------------

/// Errors resolving the pinned leancheck Vampire binary or running it.
#[derive(Clone, Debug)]
pub enum LeancheckError {
    /// The toolchain lock is missing, malformed, or names no leancheck role.
    Lock(String),
    /// The resolved binary's bytes disagree with the locked digest.
    Sha256Mismatch { expected: String, actual: String },
    /// The locked binary path does not exist or is not a regular file.
    MissingBinary(PathBuf),
    /// A filesystem or process-launch operation failed.
    Io(String),
    /// The run was cancelled before or during execution.
    Cancelled,
    /// The deadline elapsed before the child exited.
    Timeout,
    /// The child exited with a nonzero status (or none, if signal-killed).
    NonZeroExit { code: Option<i32>, stderr: String },
    /// The child exited successfully but stdout has no `theorem fullProof`
    /// marker.
    NoTheorem { stderr: String },
    /// A captured stream exceeded its bound (see `MAX_CAPTURED_STREAM_BYTES`)
    /// before the child finished; the excess was drained and discarded, not
    /// returned truncated as if it were complete.
    OutputTooLarge { stream: &'static str, limit: usize },
}

impl fmt::Display for LeancheckError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Lock(detail) => {
                write!(formatter, "pinned leancheck Vampire lock error: {detail}")
            }
            Self::Sha256Mismatch { expected, actual } => write!(
                formatter,
                "pinned leancheck Vampire digest mismatch: expected {expected}, found {actual}"
            ),
            Self::MissingBinary(path) => write!(
                formatter,
                "pinned leancheck Vampire binary is missing: {}",
                path.display()
            ),
            Self::Io(detail) => write!(formatter, "pinned leancheck Vampire I/O error: {detail}"),
            Self::Cancelled => formatter.write_str("pinned leancheck Vampire run was cancelled"),
            Self::Timeout => {
                formatter.write_str("pinned leancheck Vampire run exceeded its deadline")
            }
            Self::NonZeroExit { code, stderr } => write!(
                formatter,
                "pinned leancheck Vampire exited with status {code:?}: {stderr}"
            ),
            Self::NoTheorem { stderr } => write!(
                formatter,
                "pinned leancheck Vampire produced no theorem fullProof marker: {stderr}"
            ),
            Self::OutputTooLarge { stream, limit } => write!(
                formatter,
                "pinned leancheck Vampire {stream} exceeded the {limit}-byte capture limit"
            ),
        }
    }
}

impl std::error::Error for LeancheckError {}

// ------------------------------------------------------------
// Tests
// ------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::fs::PermissionsExt;

    fn temp_dir(label: &str) -> PathBuf {
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "whiel_leancheck_{label}_{}_{nanos}",
            std::process::id()
        ));
        std::fs::create_dir_all(&path).unwrap();
        path
    }

    fn write_executable(path: &Path, script: &str) {
        std::fs::write(path, script).unwrap();
        let mut permissions = std::fs::metadata(path).unwrap().permissions();
        permissions.set_mode(0o755);
        std::fs::set_permissions(path, permissions).unwrap();
    }

    #[test]
    fn concurrent_problem_files_with_the_same_clock_reading_remain_independent() {
        let root = temp_dir("problem_same_clock");
        let barrier = std::sync::Barrier::new(16);
        let mut staged = std::thread::scope(|scope| {
            let handles: Vec<_> = (0..16)
                .map(|index| {
                    let root = &root;
                    let barrier = &barrier;
                    scope.spawn(move || {
                        let bytes = format!("distinct opaque problem {index}").into_bytes();
                        barrier.wait();
                        let file = TempProblemFile::write_at(root, 42, &bytes).unwrap();
                        (file, bytes)
                    })
                })
                .collect();
            handles
                .into_iter()
                .map(|handle| handle.join().unwrap())
                .collect::<Vec<_>>()
        });
        let paths: std::collections::BTreeSet<_> = staged
            .iter()
            .map(|(file, _)| file.path().to_path_buf())
            .collect();
        assert_eq!(paths.len(), 16);
        let (finished, _) = staged.pop().unwrap();
        let finished_path = finished.path().to_path_buf();
        drop(finished);
        assert!(!finished_path.exists());
        for (file, expected) in &staged {
            assert_eq!(std::fs::read(file.path()).unwrap(), *expected);
        }
        drop(staged);
        std::fs::remove_dir(root).unwrap();
    }

    #[test]
    fn problem_file_creation_neither_overwrites_nor_removes_an_existing_path() {
        let root = temp_dir("problem_existing_path");
        let path = root.join("existing.p");
        std::fs::write(&path, b"unrelated existing input").unwrap();
        assert!(matches!(
            TempProblemFile::create(path.clone(), b"replacement"),
            Err(LeancheckError::Io(_))
        ));
        assert_eq!(std::fs::read(&path).unwrap(), b"unrelated existing input");
        std::fs::remove_file(path).unwrap();
        std::fs::remove_dir(root).unwrap();
    }

    #[test]
    fn direct_arguments_are_pinned_exactly() {
        let profile = LeancheckProfile::new(ProofSearchProfile::Direct);
        let arguments: Vec<String> = profile
            .arguments(60)
            .iter()
            .map(|argument| argument.to_string_lossy().into_owned())
            .collect();
        assert_eq!(
            arguments,
            vec![
                "--proof",
                "leancheck",
                "--proof_extra",
                "lean",
                "--skolemization",
                "syntactic",
                "--output_mode",
                "lean",
                "--time_limit",
                "60",
                "--avatar",
                "on",
                "--random_seed",
                "1",
            ]
        );
    }

    /// The profile version binds both pinned vectors and the toolchain they
    /// are certified under. `v4` turns AVATAR on for `direct`; `v3` already
    /// named the leancheck Vampire whose emitter renders the definition
    /// symbols introduced by `casc_2025` at one consistent arity. The CASC
    /// vector itself is unchanged.
    #[test]
    fn the_casc_profile_version_is_pinned() {
        assert_eq!(
            PROOF_CASC_PROFILE_ID,
            "direct-then-casc-2025-single-core-v4"
        );
    }

    #[test]
    fn casc_2025_arguments_are_pinned_exactly() {
        let profile = LeancheckProfile::new(ProofSearchProfile::Casc2025);
        let arguments: Vec<String> = profile
            .arguments(60)
            .iter()
            .map(|argument| argument.to_string_lossy().into_owned())
            .collect();
        assert_eq!(
            arguments,
            vec![
                "--mode",
                "portfolio",
                "--schedule",
                "casc_2025",
                "--cores",
                "1",
                "--random_seed",
                "1",
                "--randomize_seed_for_portfolio_workers",
                "off",
                "--shuffle_on_schedule_repeats",
                "off",
                "--avatar",
                "on",
                "--time_limit",
                "60",
                "--proof",
                "leancheck",
                "--proof_extra",
                "lean",
                "--skolemization",
                "syntactic",
                "--output_mode",
                "lean",
            ]
        );
    }

    fn write_lock(directory: &Path, binary_relative: &str, sha256: &str) {
        let lock = json!({
            "format_version": LOCK_FORMAT_VERSION,
            "roles": {
                LEANCHECK_ROLE: {
                    "path": binary_relative,
                    "sha256": {
                        host_platform_key().unwrap(): sha256,
                    },
                },
            },
        });
        std::fs::write(
            directory.join(LOCK_FILENAME),
            serde_json::to_vec(&lock).unwrap(),
        )
        .unwrap();
    }

    #[test]
    fn from_lock_succeeds_and_records_the_verified_digest() {
        let root = temp_dir("from_lock_ok");
        let binary_dir = root.join("toolchain/build/vampire-leancheck-test/build");
        std::fs::create_dir_all(&binary_dir).unwrap();
        let binary_path = binary_dir.join("vampire");
        write_executable(&binary_path, "#!/bin/sh\nexit 0\n");
        let sha256 = hash_file(&binary_path).unwrap();
        write_lock(
            &root,
            "toolchain/build/vampire-leancheck-test/build/vampire",
            &sha256,
        );

        let pinned = PinnedLeancheckVampire::from_lock(&root).unwrap();
        assert_eq!(pinned.sha256(), sha256);
        assert_eq!(pinned.path(), binary_path);

        std::fs::remove_dir_all(&root).unwrap();
    }

    #[test]
    fn from_lock_fails_closed_on_sha256_mismatch() {
        let root = temp_dir("from_lock_sha_mismatch");
        let binary_dir = root.join("toolchain/build/vampire-leancheck-test/build");
        std::fs::create_dir_all(&binary_dir).unwrap();
        let binary_path = binary_dir.join("vampire");
        write_executable(&binary_path, "#!/bin/sh\nexit 0\n");
        write_lock(
            &root,
            "toolchain/build/vampire-leancheck-test/build/vampire",
            &"0".repeat(64),
        );

        let error = PinnedLeancheckVampire::from_lock(&root).unwrap_err();
        assert!(matches!(error, LeancheckError::Sha256Mismatch { .. }));

        std::fs::remove_dir_all(&root).unwrap();
    }

    #[test]
    fn from_lock_fails_closed_on_a_missing_binary() {
        let root = temp_dir("from_lock_missing_binary");
        std::fs::create_dir_all(&root).unwrap();
        write_lock(
            &root,
            "toolchain/build/vampire-leancheck-test/build/vampire",
            &"0".repeat(64),
        );

        let error = PinnedLeancheckVampire::from_lock(&root).unwrap_err();
        assert!(matches!(error, LeancheckError::MissingBinary(_)));

        std::fs::remove_dir_all(&root).unwrap();
    }

    #[test]
    fn from_lock_fails_closed_on_a_malformed_lock() {
        let root = temp_dir("from_lock_malformed");
        std::fs::create_dir_all(&root).unwrap();
        std::fs::write(root.join(LOCK_FILENAME), b"not json").unwrap();

        let error = PinnedLeancheckVampire::from_lock(&root).unwrap_err();
        assert!(matches!(error, LeancheckError::Lock(_)));

        std::fs::remove_dir_all(&root).unwrap();

        let root = temp_dir("from_lock_wrong_version");
        std::fs::create_dir_all(&root).unwrap();
        std::fs::write(
            root.join(LOCK_FILENAME),
            serde_json::to_vec(&json!({"format_version": 1, "roles": {}})).unwrap(),
        )
        .unwrap();
        let error = PinnedLeancheckVampire::from_lock(&root).unwrap_err();
        assert!(matches!(error, LeancheckError::Lock(_)));

        std::fs::remove_dir_all(&root).unwrap();
    }

    fn pinned_fixture(root: &Path, script: &str) -> PinnedLeancheckVampire {
        let binary_dir = root.join("bin");
        std::fs::create_dir_all(&binary_dir).unwrap();
        let binary_path = binary_dir.join("vampire");
        write_executable(&binary_path, script);
        let sha256 = hash_file(&binary_path).unwrap();
        write_lock(root, "bin/vampire", &sha256);
        PinnedLeancheckVampire::from_lock(root).unwrap()
    }

    #[tokio::test]
    async fn execute_succeeds_on_the_full_proof_theorem_marker() {
        let root = temp_dir("execute_success");
        let pinned = pinned_fixture(
            &root,
            "#!/bin/sh\nprintf 'theorem fullProof := trivial\\nend vamproof\\n'\nexit 0\n",
        );
        let output = LeancheckRun::execute(
            &pinned,
            LeancheckProfile::new(ProofSearchProfile::Direct),
            b"fof(dummy, axiom, $true).",
            Duration::from_secs(5),
            &CancellationToken::new(),
        )
        .await
        .unwrap();
        assert!(output.raw.starts_with(b"theorem fullProof"));
        assert_eq!(
            output.raw_sha256,
            crate::encoding::bytes_sha256(&output.raw)
        );
        assert_eq!(
            output.invocation_identity["profile_id"],
            json!(PROOF_CASC_PROFILE_ID)
        );

        std::fs::remove_dir_all(&root).unwrap();
    }

    #[tokio::test]
    async fn execute_reports_a_nonzero_exit() {
        let root = temp_dir("execute_nonzero_exit");
        let pinned = pinned_fixture(&root, "#!/bin/sh\necho boom 1>&2\nexit 1\n");
        let error = LeancheckRun::execute(
            &pinned,
            LeancheckProfile::new(ProofSearchProfile::Direct),
            b"fof(dummy, axiom, $true).",
            Duration::from_secs(5),
            &CancellationToken::new(),
        )
        .await
        .unwrap_err();
        match error {
            LeancheckError::NonZeroExit { code, stderr } => {
                assert_eq!(code, Some(1));
                assert!(stderr.contains("boom"));
            }
            other => panic!("expected NonZeroExit, got {other:?}"),
        }

        std::fs::remove_dir_all(&root).unwrap();
    }

    #[tokio::test]
    async fn execute_reports_a_missing_theorem_line() {
        let root = temp_dir("execute_no_theorem");
        let pinned = pinned_fixture(&root, "#!/bin/sh\nprintf 'nothing useful\\n'\nexit 0\n");
        let error = LeancheckRun::execute(
            &pinned,
            LeancheckProfile::new(ProofSearchProfile::Direct),
            b"fof(dummy, axiom, $true).",
            Duration::from_secs(5),
            &CancellationToken::new(),
        )
        .await
        .unwrap_err();
        assert!(matches!(error, LeancheckError::NoTheorem { .. }));

        std::fs::remove_dir_all(&root).unwrap();
    }

    #[tokio::test]
    async fn execute_reports_a_truncated_proof_as_no_theorem() {
        // A `theorem fullProof` line with no closing `end vamproof` (as a
        // timeout or crash mid-write would leave) must not be accepted as a
        // packaged success, and an unanchored occurrence of the marker text
        // inside a comment line must not count as the marker either.
        let root = temp_dir("execute_truncated_proof");
        let pinned = pinned_fixture(
            &root,
            "#!/bin/sh\nprintf 'note: mentions theorem fullProof inline, not at line start\\ntheorem fullProof := by\\n'\nexit 0\n",
        );
        let error = LeancheckRun::execute(
            &pinned,
            LeancheckProfile::new(ProofSearchProfile::Direct),
            b"fof(dummy, axiom, $true).",
            Duration::from_secs(5),
            &CancellationToken::new(),
        )
        .await
        .unwrap_err();
        assert!(
            matches!(error, LeancheckError::NoTheorem { .. }),
            "{error:?}"
        );

        std::fs::remove_dir_all(&root).unwrap();
    }

    fn pid_is_alive(pid: u32) -> bool {
        // SAFETY: signal 0 sends no signal; it only probes whether `pid`
        // exists and is signalable, which is exactly what this checks.
        unsafe { libc::kill(pid as libc::pid_t, 0) == 0 }
    }

    /// A fixture whose direct process (the `sh` interpreter) has its own
    /// live child (`sleep`), mirroring the `casc_2025` portfolio's fan-out
    /// into several worker processes. Writes the child's pid to `pidfile`
    /// before waiting on it, so the test can confirm the *whole* process
    /// group — not just the direct child — was killed.
    fn spawn_group_fixture(root: &Path, pidfile: &Path) -> PinnedLeancheckVampire {
        pinned_fixture(
            root,
            &format!(
                "#!/bin/sh\nsleep 30 &\necho $! > {}\nwait\n",
                pidfile.display()
            ),
        )
    }

    /// Polls (yielding the async executor between attempts, never blocking
    /// it, so a concurrently `tokio::spawn`-ed [`LeancheckRun::execute`]
    /// keeps making progress on a single-threaded test runtime) until the
    /// fixture has written its background child's pid.
    async fn read_child_pid(pidfile: &Path, deadline: Instant) -> u32 {
        loop {
            if let Ok(contents) = std::fs::read_to_string(pidfile)
                && let Ok(pid) = contents.trim().parse::<u32>()
            {
                return pid;
            }
            assert!(
                Instant::now() < deadline,
                "the fixture never wrote its child pid to {}",
                pidfile.display()
            );
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    }

    #[tokio::test]
    async fn execute_kills_and_reaps_on_timeout() {
        let root = temp_dir("execute_timeout");
        let pidfile = root.join("child.pid");
        let pinned = spawn_group_fixture(&root, &pidfile);
        let started = Instant::now();

        let run = tokio::spawn(async move {
            LeancheckRun::execute(
                &pinned,
                LeancheckProfile::new(ProofSearchProfile::Direct),
                b"fof(dummy, axiom, $true).",
                Duration::from_secs(2),
                &CancellationToken::new(),
            )
            .await
        });
        let child_pid = read_child_pid(&pidfile, started + Duration::from_secs(5)).await;
        let error = run.await.unwrap().unwrap_err();
        assert!(matches!(error, LeancheckError::Timeout));
        assert!(started.elapsed() < Duration::from_secs(10));
        assert!(
            !pid_is_alive(child_pid),
            "the portfolio-fixture child (pid {child_pid}) must not survive a timeout"
        );

        std::fs::remove_dir_all(&root).unwrap();
    }

    #[tokio::test]
    async fn execute_stops_promptly_on_cancellation() {
        let root = temp_dir("execute_cancelled");
        let pidfile = root.join("child.pid");
        let pinned = spawn_group_fixture(&root, &pidfile);
        let cancellation = CancellationToken::new();
        let canceller = cancellation.clone();
        let started = Instant::now();

        let run = tokio::spawn(async move {
            LeancheckRun::execute(
                &pinned,
                LeancheckProfile::new(ProofSearchProfile::Direct),
                b"fof(dummy, axiom, $true).",
                Duration::from_secs(30),
                &cancellation,
            )
            .await
        });
        // Wait for the fixture to actually be running (its child pid on
        // disk) before cancelling, rather than racing a fixed timer against
        // the fixture's own startup latency under load — this is what
        // "promptly" means to test: cancellation reacts fast once the run
        // is truly underway, not that it beats an arbitrary clock.
        let child_pid = read_child_pid(&pidfile, started + Duration::from_secs(5)).await;
        canceller.cancel();
        let error = run.await.unwrap().unwrap_err();
        assert!(matches!(error, LeancheckError::Cancelled));
        assert!(started.elapsed() < Duration::from_secs(10));
        assert!(
            !pid_is_alive(child_pid),
            "the portfolio-fixture child (pid {child_pid}) must not survive cancellation"
        );

        std::fs::remove_dir_all(&root).unwrap();
    }

    // ------------------------------------------------------------
    // Pinned Kernel-LRAT CaDiCaL
    // ------------------------------------------------------------

    /// A toolchain lock carrying only the `kernel_lrat_cadical` role.
    fn cadical_lock(role: Value) -> String {
        json!({
            "format_version": LOCK_FORMAT_VERSION,
            "roles": { KERNEL_LRAT_CADICAL_ROLE: role },
        })
        .to_string()
    }

    /// A fake toolchain prefix whose `bin/cadical` reports `version`.
    fn fake_lean_prefix(root: &Path, version: &str) -> PathBuf {
        let prefix = root.join("toolchain");
        std::fs::create_dir_all(prefix.join("bin")).unwrap();
        write_executable(
            &prefix.join("bin").join("cadical"),
            &format!("#!/bin/sh\necho {version}\n"),
        );
        prefix
    }

    fn cadical_digest(prefix: &Path) -> String {
        crate::entailment::assembly::hash_file_sha256(&prefix.join("bin").join("cadical")).unwrap()
    }

    #[test]
    fn the_kernel_lrat_cadical_role_resolves_beside_the_pinned_lean() {
        let root = temp_dir("cadical_ok");
        let prefix = fake_lean_prefix(&root, "2.1.2");
        std::fs::write(
            root.join(LOCK_FILENAME),
            cadical_lock(json!({
                "resolver": "adjacent-to-lean",
                "version": "2.1.2",
                "arguments": ["--lrat", "--binary=false", "--quiet"],
                "sha256": { host_platform_key().unwrap(): cadical_digest(&prefix) },
            })),
        )
        .unwrap();

        let pinned = PinnedKernelLratCadical::from_lock_under_prefix(&root, &prefix).unwrap();
        assert_eq!(pinned.path(), prefix.join("bin").join("cadical"));
        assert_eq!(pinned.version(), "2.1.2");
        assert_eq!(pinned.arguments(), ["--lrat", "--binary=false", "--quiet"]);
        assert_eq!(
            pinned.invocation_identity()["environment_contract"],
            json!("inherit-without-cadical-options-locale-c-v1")
        );

        std::fs::remove_dir_all(&root).unwrap();
    }

    #[test]
    fn a_kernel_lrat_cadical_digest_mismatch_fails_closed() {
        let root = temp_dir("cadical_digest");
        let prefix = fake_lean_prefix(&root, "2.1.2");
        std::fs::write(
            root.join(LOCK_FILENAME),
            cadical_lock(json!({
                "resolver": "adjacent-to-lean",
                "version": "2.1.2",
                "arguments": ["--lrat"],
                "sha256": { host_platform_key().unwrap(): "0".repeat(64) },
            })),
        )
        .unwrap();

        let error = PinnedKernelLratCadical::from_lock_under_prefix(&root, &prefix).unwrap_err();
        assert!(
            matches!(error, KernelLratCadicalError::Sha256Mismatch { .. }),
            "{error}"
        );

        std::fs::remove_dir_all(&root).unwrap();
    }

    #[test]
    fn a_kernel_lrat_cadical_version_mismatch_fails_closed() {
        let root = temp_dir("cadical_version");
        let prefix = fake_lean_prefix(&root, "2.1.3");
        std::fs::write(
            root.join(LOCK_FILENAME),
            cadical_lock(json!({
                "resolver": "adjacent-to-lean",
                "version": "2.1.2",
                "arguments": ["--lrat"],
                "sha256": { host_platform_key().unwrap(): cadical_digest(&prefix) },
            })),
        )
        .unwrap();

        let error = PinnedKernelLratCadical::from_lock_under_prefix(&root, &prefix).unwrap_err();
        assert!(
            matches!(error, KernelLratCadicalError::VersionMismatch { .. }),
            "{error}"
        );

        std::fs::remove_dir_all(&root).unwrap();
    }

    #[test]
    fn a_foreign_kernel_lrat_cadical_resolver_fails_closed() {
        let root = temp_dir("cadical_resolver");
        let prefix = fake_lean_prefix(&root, "2.1.2");
        std::fs::write(
            root.join(LOCK_FILENAME),
            cadical_lock(json!({
                "resolver": "on-path",
                "version": "2.1.2",
                "arguments": ["--lrat"],
                "sha256": { host_platform_key().unwrap(): cadical_digest(&prefix) },
            })),
        )
        .unwrap();

        let error = PinnedKernelLratCadical::from_lock_under_prefix(&root, &prefix).unwrap_err();
        assert!(
            error
                .to_string()
                .contains("is not resolved adjacent-to-lean"),
            "{error}"
        );

        std::fs::remove_dir_all(&root).unwrap();
    }

    #[test]
    fn a_missing_adjacent_cadical_fails_closed() {
        let root = temp_dir("cadical_missing");
        let prefix = root.join("toolchain");
        std::fs::create_dir_all(prefix.join("bin")).unwrap();
        std::fs::write(
            root.join(LOCK_FILENAME),
            cadical_lock(json!({
                "resolver": "adjacent-to-lean",
                "version": "2.1.2",
                "arguments": ["--lrat"],
                "sha256": { host_platform_key().unwrap(): "0".repeat(64) },
            })),
        )
        .unwrap();

        let error = PinnedKernelLratCadical::from_lock_under_prefix(&root, &prefix).unwrap_err();
        assert!(
            matches!(error, KernelLratCadicalError::MissingBinary(_)),
            "{error}"
        );

        std::fs::remove_dir_all(&root).unwrap();
    }

    #[test]
    fn a_symlinked_cadical_is_refused() {
        let root = temp_dir("cadical_symlink");
        let prefix = fake_lean_prefix(&root, "2.1.2");
        let real = prefix.join("bin").join("cadical");
        let moved = prefix.join("bin").join("cadical.real");
        std::fs::rename(&real, &moved).unwrap();
        std::os::unix::fs::symlink(&moved, &real).unwrap();
        std::fs::write(
            root.join(LOCK_FILENAME),
            cadical_lock(json!({
                "resolver": "adjacent-to-lean",
                "version": "2.1.2",
                "arguments": ["--lrat"],
                "sha256": { host_platform_key().unwrap(): "0".repeat(64) },
            })),
        )
        .unwrap();

        let error = PinnedKernelLratCadical::from_lock_under_prefix(&root, &prefix).unwrap_err();
        assert!(
            matches!(error, KernelLratCadicalError::MissingBinary(_)),
            "{error}"
        );

        std::fs::remove_dir_all(&root).unwrap();
    }

    #[test]
    fn the_repository_lock_resolves_the_real_pinned_cadical() {
        // The digest check the certificate build depends on, run against
        // the repository's own lock and toolchain pin. Skipped only when
        // no Lean toolchain is on PATH at all (no elan in this
        // environment); a resolvable toolchain with the wrong CaDiCaL is a
        // failure, never a skip.
        let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .to_path_buf();
        if lean_toolchain_prefix(&repository).is_err() {
            eprintln!("no Lean toolchain on PATH; kernel-LRAT CaDiCaL check skipped");
            return;
        }
        let pinned = PinnedKernelLratCadical::from_lock(&repository).unwrap();
        assert_eq!(pinned.version(), "2.1.2");
        assert_eq!(
            pinned.arguments(),
            [
                "--lrat",
                "--binary=false",
                "--quiet",
                "--shrink=0",
                "--plain",
                "--seed=0"
            ]
        );
        assert_eq!(pinned.sha256().len(), 64);
    }
}
