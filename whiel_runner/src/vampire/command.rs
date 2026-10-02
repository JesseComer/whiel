use std::ffi::{OsStr, OsString};
use std::fmt;
use std::fs::File;
use std::io::Read;
use std::num::NonZeroU64;
use std::path::{Path, PathBuf};
use std::str::FromStr;
use std::sync::Arc;
use std::time::Duration;

use crate::artifact::{ArtifactRef, ArtifactStore, AttemptId, ScopeTag};
use crate::entailment::assembly::{PremiseRole, Sha256};
use crate::telemetry::TelemetryHandle;

// ------------------------------------------------------------
// Proof-Search Configuration
// ------------------------------------------------------------

pub(crate) const PROOF_CASC_SHARE_SCALE: u32 = 1_000_000;
pub(crate) const PROOF_CASC_ALLOCATION_FORMULA: &str =
    "ceil((q_millionths*initial_ns+r_millionths*retry_added_ns)/share_scale)";
pub(crate) const PROOF_CASC_ALLOCATION_ROUNDING: &str = "one_combined_ceiling_to_nanoseconds";
pub(crate) const PROOF_CASC_PROFILE_ID: &str = "direct-then-casc-2025-single-core-v4";
pub(crate) const PROOF_CASC_SCHEDULE: &str = "casc_2025";
pub(crate) const PROOF_CASC_RANDOM_SEED: &str = "1";
pub(crate) const PROOF_CASC_CORES: u32 = 1;
pub(crate) const PROOF_CASC_RANDOMIZE_WORKER_SEEDS: bool = false;
pub(crate) const PROOF_CASC_SHUFFLE_SCHEDULE_REPEATS: bool = false;
pub(crate) const PROOF_CASC_AVATAR: bool = true;
// Vampire parses this option through a 32-bit float and its portfolio code
// multiplies the stored signed deciseconds by 100. Every integer through 2^24
// is represented exactly and that product remains in signed-int range.
const SOLVER_MAX_TIME_LIMIT_DECISECONDS: u32 = 1 << 24;

/// Memory each Vampire process is launched under, in MB.
///
/// This is the pinned build's own release default, passed explicitly so the
/// value a run used is recorded with it and cannot drift when the pinned
/// solver changes. Passing it therefore changes no search.
///
/// It is not a bound anyone should rely on yet. Vampire's own option
/// description says the limit is not honoured on macOS, and an over-limit exit
/// leaves the process with a nonzero status, which this crate classifies as a
/// process failure rather than as an inconclusive result for that lane.
/// Lowering it to a figure that would actually bind is an owner decision that
/// needs that classification settled first.
pub const VAMPIRE_MEMORY_LIMIT_MB: u64 = 131_072;

/// What one Vampire process is planned to occupy, in MB.
///
/// This is a planning figure, not an enforced one: nothing stops a process
/// exceeding it, and [`VAMPIRE_MEMORY_LIMIT_MB`] is what it actually runs
/// under. It exists so a run's default concurrency can be bounded by the
/// memory a machine has, which the hard limit — deliberately far above any
/// real footprint — cannot do. Four gibibytes covers the largest working set
/// measured on this corpus with the portfolio strategy enabled, which peaks
/// above three; an owner who measures otherwise should change it here, where
/// both the default and the warning read it.
pub const VAMPIRE_PLANNED_FOOTPRINT_MB: u64 = 4096;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ProofCascShare(u32);

impl ProofCascShare {
    pub const DISABLED: Self = Self(0);
    pub const CLI_DEFAULT: Self = Self(250_000);
    pub const CLI_RETRY_DEFAULT: Self = Self(750_000);
    pub const ONLY: Self = Self(PROOF_CASC_SHARE_SCALE);

    pub const fn from_millionths(millionths: u32) -> Option<Self> {
        if millionths <= PROOF_CASC_SHARE_SCALE {
            Some(Self(millionths))
        } else {
            None
        }
    }

    pub const fn millionths(self) -> u32 {
        self.0
    }

    pub const fn is_disabled(self) -> bool {
        self.0 == 0
    }

    pub const fn is_casc_only(self) -> bool {
        self.0 == PROOF_CASC_SHARE_SCALE
    }
}

impl Default for ProofCascShare {
    fn default() -> Self {
        Self::DISABLED
    }
}

impl fmt::Display for ProofCascShare {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0 == PROOF_CASC_SHARE_SCALE {
            return formatter.write_str("1");
        }
        let mut fraction = format!("{:06}", self.0);
        while fraction.ends_with('0') {
            fraction.pop();
        }
        if fraction.is_empty() {
            formatter.write_str("0")
        } else {
            write!(formatter, "0.{fraction}")
        }
    }
}

impl FromStr for ProofCascShare {
    type Err = ProofCascShareError;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        let invalid = || ProofCascShareError {
            value: value.to_string(),
        };
        let (whole, fraction) = match value.split_once('.') {
            Some((_whole, "")) => return Err(invalid()),
            Some((whole, fraction)) => (whole, Some(fraction)),
            None => (value, None),
        };
        if !matches!(whole, "0" | "1") {
            return Err(invalid());
        }
        let fraction = fraction.unwrap_or("");
        if fraction.len() > 6
            || (!fraction.is_empty() && !fraction.bytes().all(|byte| byte.is_ascii_digit()))
            || (whole == "1" && fraction.bytes().any(|byte| byte != b'0'))
        {
            return Err(invalid());
        }
        let fraction_value = if fraction.is_empty() {
            0
        } else {
            fraction.parse::<u32>().map_err(|_| invalid())?
                * 10_u32.pow(6 - u32::try_from(fraction.len()).unwrap_or(6))
        };
        let millionths = if whole == "1" {
            PROOF_CASC_SHARE_SCALE
        } else {
            fraction_value
        };
        Self::from_millionths(millionths).ok_or_else(invalid)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofCascShareError {
    value: String,
}

impl fmt::Display for ProofCascShareError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "proof CASC share {:?} must be a decimal from 0 through 1 with at most six fractional digits",
            self.value,
        )
    }
}

impl std::error::Error for ProofCascShareError {}

/// Exact CASC shares for a first attempt and its retry-added time.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ProofCascPolicy {
    initial_share: ProofCascShare,
    retry_added_share: ProofCascShare,
}

impl ProofCascPolicy {
    pub const DISABLED: Self = Self::uniform(ProofCascShare::DISABLED);
    pub const CLI_DEFAULT: Self = Self {
        initial_share: ProofCascShare::CLI_DEFAULT,
        retry_added_share: ProofCascShare::CLI_RETRY_DEFAULT,
    };
    pub const ONLY: Self = Self::uniform(ProofCascShare::ONLY);

    pub const fn new(
        initial_share: ProofCascShare,
        retry_added_share: ProofCascShare,
    ) -> Result<Self, ProofCascPolicyError> {
        if initial_share.is_disabled() && !retry_added_share.is_disabled() {
            return Err(ProofCascPolicyError::DisabledInitialWithRetry);
        }
        if initial_share.is_casc_only() && !retry_added_share.is_casc_only() {
            return Err(ProofCascPolicyError::CascOnlyInitialWithDirectRetry);
        }
        Ok(Self {
            initial_share,
            retry_added_share,
        })
    }

    pub const fn uniform(share: ProofCascShare) -> Self {
        Self {
            initial_share: share,
            retry_added_share: share,
        }
    }

    pub const fn initial_share(self) -> ProofCascShare {
        self.initial_share
    }

    pub const fn retry_added_share(self) -> ProofCascShare {
        self.retry_added_share
    }

    pub const fn is_disabled(self) -> bool {
        self.initial_share.is_disabled()
    }

    pub const fn is_casc_only(self) -> bool {
        self.initial_share.is_casc_only()
    }

    pub(crate) fn split(
        self,
        total_limit: Duration,
        retry_added: Duration,
    ) -> (Duration, Duration) {
        let total_nanoseconds = total_limit.as_nanos();
        let retry_nanoseconds = retry_added.as_nanos();
        let initial_nanoseconds = total_nanoseconds
            .checked_sub(retry_nanoseconds)
            .expect("a validated retry-added allowance cannot exceed its total");
        let scaled_casc = initial_nanoseconds * u128::from(self.initial_share.millionths())
            + retry_nanoseconds * u128::from(self.retry_added_share.millionths());
        let casc_nanoseconds = if scaled_casc == 0 {
            0
        } else {
            scaled_casc.div_ceil(u128::from(PROOF_CASC_SHARE_SCALE))
        };
        let normal_nanoseconds = total_nanoseconds - casc_nanoseconds;
        (
            duration_from_nanoseconds(normal_nanoseconds),
            duration_from_nanoseconds(casc_nanoseconds),
        )
    }
}

impl Default for ProofCascPolicy {
    fn default() -> Self {
        Self::DISABLED
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProofCascPolicyError {
    DisabledInitialWithRetry,
    CascOnlyInitialWithDirectRetry,
}

impl fmt::Display for ProofCascPolicyError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DisabledInitialWithRetry => formatter.write_str(
                "an initial proof CASC share of 0 disables CASC for the entire retry chain",
            ),
            Self::CascOnlyInitialWithDirectRetry => formatter.write_str(
                "an initial proof CASC share of 1 selects CASC for the entire retry chain",
            ),
        }
    }
}

impl std::error::Error for ProofCascPolicyError {}

fn duration_from_nanoseconds(nanoseconds: u128) -> Duration {
    const NANOS_PER_SECOND: u128 = 1_000_000_000;
    let seconds = nanoseconds / NANOS_PER_SECOND;
    let subsecond = nanoseconds % NANOS_PER_SECOND;
    Duration::new(
        u64::try_from(seconds).unwrap_or(u64::MAX),
        u32::try_from(subsecond).unwrap_or(999_999_999),
    )
}

/// One solver stage's own wall-clock limit, in the exact deciseconds the
/// pinned solver's `--time_limit` option takes.
///
/// Every stage the runner launches is told its limit, so the solver stops
/// itself and reports rather than being killed at a deadline it was never
/// given. The pinned solver's own default is 60 seconds whatever the
/// runner intended, and its portfolio schedules scale every strategy slice
/// by this number, so leaving it unstated is neither a longer search nor
/// the same search: it is a different one.
///
/// The value is always a function of the launch's allocation, never of how
/// much wall clock happened to be left when the stage started.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SolverTimeLimit {
    time_limit_deciseconds: NonZeroU64,
}

impl SolverTimeLimit {
    pub(crate) fn for_local_limit(limit: Duration) -> Option<Self> {
        const NANOS_PER_DECISECOND: u128 = 100_000_000;
        let rounded_deciseconds = limit.as_nanos().div_ceil(NANOS_PER_DECISECOND);
        if rounded_deciseconds > u128::from(SOLVER_MAX_TIME_LIMIT_DECISECONDS) {
            return None;
        }
        Some(Self {
            time_limit_deciseconds: NonZeroU64::new(rounded_deciseconds as u64)
                .unwrap_or(NonZeroU64::MIN),
        })
    }

    pub const fn time_limit_deciseconds(self) -> u64 {
        self.time_limit_deciseconds.get()
    }
}

// ------------------------------------------------------------
// Finite-Model Search Configuration
// ------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FmbSize(NonZeroU64);

impl FmbSize {
    pub const ONE: Self = Self(NonZeroU64::MIN);

    pub fn new(value: u64) -> Option<Self> {
        NonZeroU64::new(value).map(Self)
    }

    pub fn get(self) -> u64 {
        self.0.get()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FmbContourStrategy {
    SingleSortedComplete,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FmbOptions {
    pub start_size: FmbSize,
    pub contour_strategy: FmbContourStrategy,
}

impl Default for FmbOptions {
    fn default() -> Self {
        Self {
            start_size: FmbSize::ONE,
            contour_strategy: FmbContourStrategy::SingleSortedComplete,
        }
    }
}

// ------------------------------------------------------------
// Single-Worker Request Types
// ------------------------------------------------------------

/*
  A request owns one preallocated attempt identity. It is not
  Clone: one request represents one process execution attempt.

  VampireProblem is only the Phase 2A bridge to an assembled
  TPTP file. Phase 2D binds this boundary to an exact Entailment.
*/

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VampireWorkerMode {
    ProofOnly,
    ProofCasc,
    FmbOnly(FmbOptions),
}

#[derive(Clone, Debug)]
pub struct VampireProblem {
    identity: Arc<str>,
    path: PathBuf,
    query_artifact: Option<ArtifactRef>,
    premise_role: PremiseRole,
}

impl VampireProblem {
    pub fn new(identity: impl Into<Arc<str>>, path: impl Into<PathBuf>) -> Self {
        Self {
            identity: identity.into(),
            path: path.into(),
            query_artifact: None,
            premise_role: PremiseRole::default(),
        }
    }

    /// Bind the problem path to the immutable query artifact that owns it.
    pub(crate) fn with_query_artifact(mut self, query_artifact: ArtifactRef) -> Self {
        self.query_artifact = Some(query_artifact);
        self
    }

    /// Record the TPTP role the premises in this file are written under, so
    /// the launch record names the search the process was actually given.
    pub(crate) fn with_premise_role(mut self, premise_role: PremiseRole) -> Self {
        self.premise_role = premise_role;
        self
    }

    pub(crate) fn premise_role(&self) -> PremiseRole {
        self.premise_role
    }

    pub fn identity(&self) -> &str {
        &self.identity
    }

    pub(crate) fn identity_arc(&self) -> Arc<str> {
        Arc::clone(&self.identity)
    }

    pub fn path(&self) -> &Path {
        &self.path
    }

    pub(crate) fn query_artifact(&self) -> Option<ArtifactRef> {
        self.query_artifact
    }
}

#[derive(Clone, Debug)]
pub struct VampireWorkerCommand {
    inner: Arc<VampireWorkerCommandData>,
}

/// Exact expanded process profile used by one Vampire worker.
///
/// A durable logical receipt additionally hashes the executable bytes. This
/// value records what the process boundary launched but is not by itself
/// proof or refutation authority.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VampireInvocationProfile {
    executable: PathBuf,
    executable_sha256: Arc<str>,
    arguments: Arc<[OsString]>,
    current_directory: PathBuf,
    mode: &'static str,
    time_limit_deciseconds: Option<u64>,
}

impl VampireInvocationProfile {
    pub fn executable(&self) -> &Path {
        &self.executable
    }

    /// SHA-256 of the exact resolved executable bytes read before launch.
    pub fn executable_sha256(&self) -> &str {
        &self.executable_sha256
    }

    pub fn arguments(&self) -> &[OsString] {
        &self.arguments
    }

    pub fn current_directory(&self) -> &Path {
        &self.current_directory
    }

    pub fn mode(&self) -> &'static str {
        self.mode
    }

    pub fn time_limit_deciseconds(&self) -> Option<u64> {
        self.time_limit_deciseconds
    }

    #[cfg(test)]
    pub(crate) fn for_test() -> Self {
        Self {
            executable: PathBuf::from("test-vampire"),
            executable_sha256: Arc::from(
                "0000000000000000000000000000000000000000000000000000000000000000",
            ),
            arguments: Arc::from([]),
            current_directory: PathBuf::from("."),
            mode: "test",
            time_limit_deciseconds: None,
        }
    }
}

#[derive(Clone, Debug)]
struct VampireWorkerCommandData {
    executable: PathBuf,
    extra_args: Vec<OsString>,
    proof_casc_policy: ProofCascPolicy,
    telemetry: TelemetryHandle,
}

impl VampireWorkerCommand {
    pub fn new(executable: impl Into<PathBuf>) -> Self {
        Self {
            inner: Arc::new(VampireWorkerCommandData {
                executable: executable.into(),
                extra_args: Vec::new(),
                proof_casc_policy: ProofCascPolicy::DISABLED,
                telemetry: TelemetryHandle::disabled(),
            }),
        }
    }

    pub fn with_extra_args<I, S>(mut self, args: I) -> Result<Self, VampireCommandError>
    where
        I: IntoIterator<Item = S>,
        S: Into<OsString>,
    {
        let args = args.into_iter().map(Into::into).collect::<Vec<_>>();
        validate_extra_args(&args)?;
        if !self.inner.proof_casc_policy.is_disabled() {
            validate_proof_casc_extra_args(&args)?;
        }
        Arc::make_mut(&mut self.inner).extra_args = args;
        Ok(self)
    }

    pub fn executable(&self) -> &Path {
        &self.inner.executable
    }

    pub fn with_proof_casc_share(self, share: ProofCascShare) -> Result<Self, VampireCommandError> {
        self.with_proof_casc_policy(ProofCascPolicy::uniform(share))
    }

    pub fn with_proof_casc_policy(
        mut self,
        policy: ProofCascPolicy,
    ) -> Result<Self, VampireCommandError> {
        if !policy.is_disabled() {
            validate_proof_casc_extra_args(&self.inner.extra_args)?;
        }
        Arc::make_mut(&mut self.inner).proof_casc_policy = policy;
        Ok(self)
    }

    /// The same command with the CASC portfolio turned off entirely.
    ///
    /// Infallible where [`Self::with_proof_casc_policy`] is not: the
    /// extra-argument validation exists to keep a caller from setting
    /// portfolio-conflicting arguments *and* a portfolio, and clearing the
    /// portfolio can never create that conflict.
    pub fn without_proof_casc(mut self) -> Self {
        Arc::make_mut(&mut self.inner).proof_casc_policy = ProofCascPolicy::DISABLED;
        self
    }

    /// Return the initial share retained by the legacy scalar API.
    pub fn proof_casc_share(&self) -> ProofCascShare {
        self.inner.proof_casc_policy.initial_share()
    }

    pub fn proof_casc_policy(&self) -> ProofCascPolicy {
        self.inner.proof_casc_policy
    }

    /// Attach an observational sink to every child launched by this command.
    pub fn with_telemetry(mut self, telemetry: TelemetryHandle) -> Self {
        Arc::make_mut(&mut self.inner).telemetry = telemetry;
        self
    }

    pub(crate) fn telemetry(&self) -> &TelemetryHandle {
        &self.inner.telemetry
    }

    pub fn extra_args(&self) -> &[OsString] {
        &self.inner.extra_args
    }
}

#[derive(Debug)]
pub struct VampireWorkerRequest {
    pub(crate) problem: VampireProblem,
    pub(crate) mode: VampireWorkerMode,
    pub(crate) command: VampireWorkerCommand,
    pub(crate) attempt_id: AttemptId,
    pub(crate) artifacts: ArtifactStore,
    /// The limit this one stage states to the solver. `None` only where
    /// the caller has no finite allowance to state at all.
    pub(crate) stage_limit: Option<SolverTimeLimit>,
}

impl VampireWorkerRequest {
    pub fn new(
        problem: VampireProblem,
        mode: VampireWorkerMode,
        command: VampireWorkerCommand,
        artifacts: ArtifactStore,
    ) -> Result<Self, crate::FailureReport> {
        let (attempt_id, artifacts) = allocate_attempt(artifacts)?;
        Ok(Self::from_attempt(
            problem, mode, command, attempt_id, artifacts, None,
        ))
    }

    pub(crate) fn from_attempt(
        problem: VampireProblem,
        mode: VampireWorkerMode,
        command: VampireWorkerCommand,
        attempt_id: AttemptId,
        artifacts: ArtifactStore,
        stage_limit: Option<SolverTimeLimit>,
    ) -> Self {
        // Paired Phase 2B workers use this constructor so both processes
        // retain one logical attempt identity and one attempt scope.
        Self {
            problem,
            mode,
            command,
            attempt_id,
            artifacts,
            stage_limit,
        }
    }

    /// State an explicit solver limit for this one stage.
    pub fn with_time_limit(mut self, stage_limit: SolverTimeLimit) -> Self {
        self.stage_limit = Some(stage_limit);
        self
    }

    pub fn attempt_id(&self) -> AttemptId {
        self.attempt_id
    }
}

pub(crate) fn allocate_attempt(
    artifacts: ArtifactStore,
) -> Result<(AttemptId, ArtifactStore), crate::FailureReport> {
    let attempt_id = artifacts.next_attempt_id()?;
    let artifacts = artifacts.scoped(ScopeTag::Attempt(attempt_id));
    Ok((attempt_id, artifacts))
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VampireCommandError {
    argument: OsString,
}

impl fmt::Display for VampireCommandError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "Vampire extra argument {:?} overrides a worker-owned option",
            self.argument
        )
    }
}

impl std::error::Error for VampireCommandError {}

// ------------------------------------------------------------
// Vampire Invocation Assembly
// ------------------------------------------------------------

pub(crate) struct Invocation {
    pub executable: PathBuf,
    pub args: Vec<OsString>,
    pub cwd: PathBuf,
    pub telemetry: TelemetryHandle,
    pub telemetry_mode: &'static str,
    pub time_limit_deciseconds: Option<u64>,
    /// The role the problem file writes its premises under. It is not part
    /// of the invocation's logical identity — the problem's own bytes carry
    /// it — but the launch record names it beside the argv and the mode.
    pub premise_role: PremiseRole,
    executable_sha256: Arc<str>,
}

impl Invocation {
    pub(crate) fn profile(&self) -> VampireInvocationProfile {
        VampireInvocationProfile {
            executable: self.executable.clone(),
            executable_sha256: Arc::clone(&self.executable_sha256),
            arguments: self.args.clone().into(),
            current_directory: self.cwd.clone(),
            mode: self.telemetry_mode,
            time_limit_deciseconds: self.time_limit_deciseconds,
        }
    }
}

pub(crate) fn invocation(request: &VampireWorkerRequest) -> Result<Invocation, String> {
    validate_extra_args(request.command.extra_args()).map_err(|error| error.to_string())?;
    if matches!(request.mode, VampireWorkerMode::ProofCasc) {
        validate_proof_casc_extra_args(request.command.extra_args())
            .map_err(|error| error.to_string())?;
    }
    let problem = std::fs::canonicalize(request.problem.path())
        .map_err(|error| format!("resolve Vampire problem path: {error}"))?;
    if !problem.is_file() {
        return Err(format!(
            "Vampire problem is not a regular file: {}",
            problem.display()
        ));
    }
    let cwd = problem
        .parent()
        .ok_or_else(|| "Vampire problem has no parent directory".to_string())?
        .to_path_buf();
    let executable = resolve_executable(request.command.executable())?;
    let executable_sha256 = Arc::from(hash_file(&executable)?);
    let mut args = request.command.extra_args().to_vec();
    // Every launch states the memory it runs under, and the wall clock it
    // is allowed, whatever its mode. Both come before the mode's own
    // arguments so one reading of an argv finds the launch's bounds first.
    args.extend([
        OsString::from("--memory_limit"),
        OsString::from(VAMPIRE_MEMORY_LIMIT_MB.to_string()),
    ]);
    if let Some(stage_limit) = request.stage_limit {
        args.extend([
            OsString::from("--time_limit"),
            OsString::from(format!("{}d", stage_limit.time_limit_deciseconds())),
        ]);
    }
    append_worker_arguments(&mut args, &request.mode);
    args.push(problem.into_os_string());
    Ok(Invocation {
        executable,
        args,
        cwd,
        telemetry: request.command.telemetry().clone(),
        telemetry_mode: match request.mode {
            VampireWorkerMode::ProofOnly => "proof_normal",
            VampireWorkerMode::ProofCasc => "proof_casc",
            VampireWorkerMode::FmbOnly(_) => "fmb",
        },
        time_limit_deciseconds: request
            .stage_limit
            .map(SolverTimeLimit::time_limit_deciseconds),
        premise_role: request.problem.premise_role(),
        executable_sha256,
    })
}

fn append_worker_arguments(args: &mut Vec<OsString>, mode: &VampireWorkerMode) {
    match mode {
        VampireWorkerMode::ProofOnly => {
            // TPTP proofs with named inputs let maintenance record
            // which Candidate axioms a proof actually cited, which
            // powers the proof-support step-check shortcut.
            args.extend([
                OsString::from("--proof"),
                OsString::from("tptp"),
                OsString::from("--output_axiom_names"),
                OsString::from("on"),
            ]);
        }
        VampireWorkerMode::ProofCasc => {
            args.extend([
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
                OsString::from("--proof"),
                OsString::from("tptp"),
                OsString::from("--output_axiom_names"),
                OsString::from("on"),
            ]);
        }
        VampireWorkerMode::FmbOnly(options) => {
            args.extend([
                OsString::from("--saturation_algorithm"),
                OsString::from("fmb"),
                OsString::from("--fmb_enumeration_strategy"),
                OsString::from(match options.contour_strategy {
                    FmbContourStrategy::SingleSortedComplete => "contour",
                }),
                OsString::from("--fmb_start_size"),
                OsString::from(options.start_size.get().to_string()),
                OsString::from("--proof"),
                OsString::from("tptp"),
            ]);
        }
    }
}

const fn on_off(enabled: bool) -> &'static str {
    if enabled { "on" } else { "off" }
}

fn resolve_executable(executable: &Path) -> Result<PathBuf, String> {
    if executable.is_absolute() || executable.components().count() > 1 {
        return canonical_executable_candidate(executable);
    }
    let search_path = std::env::var_os("PATH")
        .ok_or_else(|| format!("resolve Vampire executable {:?}: PATH is unset", executable))?;
    for directory in std::env::split_paths(&search_path) {
        let candidate = directory.join(executable);
        if candidate.is_file() {
            return canonical_executable_candidate(&candidate);
        }
    }
    Err(format!(
        "resolve Vampire executable {:?}: no regular file on PATH",
        executable
    ))
}

fn canonical_executable_candidate(executable: &Path) -> Result<PathBuf, String> {
    let canonical = std::fs::canonicalize(executable).map_err(|error| {
        format!(
            "resolve Vampire executable {}: {error}",
            executable.display()
        )
    })?;
    if !canonical.is_file() {
        return Err(format!(
            "Vampire executable is not a regular file: {}",
            canonical.display()
        ));
    }
    Ok(canonical)
}

fn hash_file(path: &Path) -> Result<String, String> {
    let mut file = File::open(path)
        .map_err(|error| format!("open Vampire executable {}: {error}", path.display()))?;
    let mut digest = Sha256::new();
    let mut buffer = [0_u8; 64 * 1024];
    loop {
        let read = file
            .read(&mut buffer)
            .map_err(|error| format!("read Vampire executable {}: {error}", path.display()))?;
        if read == 0 {
            break;
        }
        digest.update(&buffer[..read]);
    }
    Ok(digest.finalize_hex())
}

// ------------------------------------------------------------
// Worker-Owned Option Validation
// ------------------------------------------------------------

/*
  The typed worker mode owns options that select Vampire's mode,
  evidence format, FMB contour, and output protocol. It also reserves
  the deadline option for Phase 2B. Extra tuning arguments must not
  override those guarantees.
*/

fn validate_extra_args(args: &[OsString]) -> Result<(), VampireCommandError> {
    const OWNED: &[&str] = &[
        "--proof",
        "-p",
        "--saturation_algorithm",
        "-sa",
        "--fmb_enumeration_strategy",
        "-fmbes",
        "--fmb_start_size",
        "-fmbss",
        "--time_limit",
        "-t",
        "--mode",
        "--intent",
        "-intent",
        "--schedule",
        "-sched",
        "--schedule_file",
        "--input_syntax",
        "--output_mode",
        "-om",
        "--print_proofs_to_file",
        "-pptf",
        "--cores",
        "--simulated_time_limit",
        "-stl",
        "--memory_limit",
        "-m",
    ];
    reject_owned_options(args, OWNED)
}

fn validate_proof_casc_extra_args(args: &[OsString]) -> Result<(), VampireCommandError> {
    const OWNED: &[&str] = &[
        "--random_seed",
        "-rs",
        "--randomize_seed_for_portfolio_workers",
        "--shuffle_on_schedule_repeats",
        "--avatar",
        "-av",
    ];
    reject_owned_options(args, OWNED)
}

fn reject_owned_options(
    args: &[OsString],
    owned_options: &[&str],
) -> Result<(), VampireCommandError> {
    for argument in args {
        if owned_options
            .iter()
            .any(|owned| option_matches(argument, owned))
        {
            return Err(VampireCommandError {
                argument: argument.clone(),
            });
        }
    }
    Ok(())
}

fn option_matches(argument: &OsStr, option: &str) -> bool {
    argument == option
        || argument
            .to_str()
            .is_some_and(|argument| argument.starts_with(&format!("{option}=")))
}

// ------------------------------------------------------------
// Tests
// ------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fmb_size_is_positive() {
        assert_eq!(FmbSize::new(0), None);
        assert_eq!(FmbSize::new(7).unwrap().get(), 7);
    }

    #[test]
    fn caller_cannot_override_worker_mode() {
        let error = VampireWorkerCommand::new("vampire")
            .with_extra_args(["--proof=off"])
            .unwrap_err();
        assert!(error.to_string().contains("--proof=off"));
        assert!(
            VampireWorkerCommand::new("vampire")
                .with_extra_args(["--random_seed", "7"])
                .is_ok()
        );
    }

    #[test]
    fn caller_cannot_override_any_worker_owned_short_option() {
        for argument in ["-p", "-sa", "-fmbes", "-fmbss", "-t"] {
            assert!(
                VampireWorkerCommand::new("vampire")
                    .with_extra_args([argument])
                    .is_err(),
                "worker-owned option was accepted: {argument}"
            );
        }
        assert!(
            VampireWorkerCommand::new("vampire")
                .with_extra_args(["--time_limit=3"])
                .is_err()
        );
    }

    #[test]
    fn caller_cannot_replace_the_typed_mode_or_parseable_output() {
        for argument in [
            "--mode=portfolio",
            "--intent=sat",
            "--schedule=casc",
            "--schedule_file=custom",
            "--input_syntax=smtlib2",
            "--output_mode=smtcomp",
            "--print_proofs_to_file=proof.out",
            "--cores=8",
            "--simulated_time_limit=1",
        ] {
            assert!(
                VampireWorkerCommand::new("vampire")
                    .with_extra_args([argument])
                    .is_err(),
                "structural option was accepted: {argument}"
            );
        }
    }

    #[test]
    fn casc_owned_tuning_is_rejected_only_when_casc_is_enabled() {
        for argument in [
            "--random_seed=7",
            "--randomize_seed_for_portfolio_workers=on",
            "--shuffle_on_schedule_repeats=on",
            "--avatar=off",
        ] {
            assert!(
                VampireWorkerCommand::new("vampire")
                    .with_extra_args([argument])
                    .is_ok(),
                "disabled CASC changed the direct-only argument contract: {argument}",
            );
            assert!(
                VampireWorkerCommand::new("vampire")
                    .with_extra_args([argument])
                    .unwrap()
                    .with_proof_casc_share(ProofCascShare::CLI_DEFAULT)
                    .is_err(),
                "enabling CASC after its conflicting option was accepted: {argument}",
            );
            assert!(
                VampireWorkerCommand::new("vampire")
                    .with_proof_casc_share(ProofCascShare::CLI_DEFAULT)
                    .unwrap()
                    .with_extra_args([argument])
                    .is_err(),
                "CASC-owned option was accepted after enabling CASC: {argument}",
            );
        }
    }

    #[test]
    fn proof_casc_share_parses_and_formats_exactly() {
        for (source, millionths, canonical) in [
            ("0", 0, "0"),
            ("0.25", 250_000, "0.25"),
            ("0.333333", 333_333, "0.333333"),
            ("1", 1_000_000, "1"),
            ("1.000000", 1_000_000, "1"),
        ] {
            let share = source.parse::<ProofCascShare>().unwrap();
            assert_eq!(share.millionths(), millionths);
            assert_eq!(share.to_string(), canonical);
        }
        for invalid in [
            "",
            ".25",
            "0.",
            "00.25",
            "-0.1",
            "1.000001",
            "1.1",
            "2",
            "NaN",
            "inf",
            "0.1234567",
        ] {
            assert!(
                invalid.parse::<ProofCascShare>().is_err(),
                "invalid share was accepted: {invalid:?}"
            );
        }
    }

    #[test]
    fn proof_casc_policy_splits_initial_and_retry_added_time_exactly() {
        assert_eq!(ProofCascShare::default(), ProofCascShare::DISABLED);
        assert_eq!(ProofCascPolicy::default(), ProofCascPolicy::DISABLED);
        let uniform = ProofCascPolicy::uniform(ProofCascShare::CLI_DEFAULT);
        let (direct, casc) = uniform.split(Duration::from_secs(30), Duration::ZERO);
        assert_eq!(direct, Duration::from_millis(22_500));
        assert_eq!(casc, Duration::from_millis(7_500));

        let adaptive = ProofCascPolicy::CLI_DEFAULT;
        let (direct, casc) = adaptive.split(Duration::from_secs(60), Duration::from_secs(30));
        assert_eq!(direct, Duration::from_secs(30));
        assert_eq!(casc, Duration::from_secs(30));
        let (direct, casc) = adaptive.split(Duration::from_secs(90), Duration::from_secs(60));
        assert_eq!(direct, Duration::from_millis(37_500));
        assert_eq!(casc, Duration::from_millis(52_500));

        let odd = Duration::from_nanos(3);
        let (direct, casc) = uniform.split(odd, Duration::ZERO);
        assert_eq!(direct, Duration::from_nanos(2));
        assert_eq!(casc, Duration::from_nanos(1));
        assert_eq!(direct.checked_add(casc), Some(odd));

        let half = "0.5".parse::<ProofCascShare>().unwrap();
        let half_policy = ProofCascPolicy::new(half, half).unwrap();
        let (direct, casc) = half_policy.split(Duration::from_nanos(2), Duration::from_nanos(1));
        assert_eq!(direct, Duration::from_nanos(1));
        assert_eq!(casc, Duration::from_nanos(1));

        for policy in [ProofCascPolicy::DISABLED, ProofCascPolicy::ONLY] {
            let (direct, casc) = policy.split(Duration::MAX, Duration::MAX);
            assert_eq!(direct.checked_add(casc), Some(Duration::MAX));
        }
    }

    #[test]
    fn proof_casc_policy_endpoints_remain_global_controls() {
        assert_eq!(
            ProofCascPolicy::new(ProofCascShare::DISABLED, ProofCascShare::ONLY),
            Err(ProofCascPolicyError::DisabledInitialWithRetry),
        );
        assert_eq!(
            ProofCascPolicy::new(ProofCascShare::ONLY, ProofCascShare::DISABLED),
            Err(ProofCascPolicyError::CascOnlyInitialWithDirectRetry),
        );
        let command = VampireWorkerCommand::new("vampire")
            .with_proof_casc_share(ProofCascShare::CLI_DEFAULT)
            .unwrap();
        assert_eq!(
            command.proof_casc_policy(),
            ProofCascPolicy::uniform(ProofCascShare::CLI_DEFAULT),
        );
    }

    /// The stage's own limit is stated once, by the launch, before the
    /// mode's arguments; the portfolio contract follows it unchanged.
    #[test]
    fn casc_arguments_are_ordered_single_core_and_deterministic() {
        let mut args = Vec::new();
        append_worker_arguments(&mut args, &VampireWorkerMode::ProofCasc);
        assert_eq!(
            args,
            [
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
                "--proof",
                "tptp",
                "--output_axiom_names",
                "on",
            ]
            .map(OsString::from)
        );
    }

    #[test]
    fn casc_internal_limit_rejects_values_vampire_cannot_represent() {
        let maximum = Duration::from_millis(u64::from(SOLVER_MAX_TIME_LIMIT_DECISECONDS) * 100);
        assert_eq!(
            SolverTimeLimit::for_local_limit(maximum)
                .unwrap()
                .time_limit_deciseconds(),
            u64::from(SOLVER_MAX_TIME_LIMIT_DECISECONDS),
        );
        assert!(SolverTimeLimit::for_local_limit(maximum + Duration::from_nanos(1)).is_none());
    }
}
