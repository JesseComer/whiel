//! Runtime for the current-input campaign command; publication remains host-owned.

use std::collections::{BTreeMap, BTreeSet};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use serde_json::{Value, json};

use super::{CampaignProvider, CampaignRunConfig, numeric_selector, valid_input_id};
use crate::artifact::{ArtifactKind, ArtifactStoreConfig, Retention, new_artifact_store};
use crate::encoding::{
    FixedAmbientWorkerCommand, FixedAmbientWorkerPoolConfig, bytes_sha256, canonical_value_sha256,
};
use crate::framework2::resource_limits::{SpaceGuard, SpaceMonitor};
use crate::framework2::{
    ATTEMPT_HISTORY_SCOPE, AcceptanceRecordRequest, AgentFeedbackLimits, AgentFeedbackPolicy,
    AgentProvider, AgentPush, AgentResponseWriter, AgentSourceCancellation,
    AgentSourceCleanupFuture, AgentSourceFuture, AgentSourceOutcome, AgentToolSurface,
    AttemptHistoryPublication, CONSULTATION_RECORD_SCOPE, CounterexampleFuelPolicy,
    FrameworkIICertificationProfiles, FrameworkIIProductionCheckConfig,
    LeancheckCertificationProfile, LeancheckProfile, PinnedLeancheckVampire,
    PreCertificateAgentHoudiniRuntime, PreCertificateAgentHoudiniSearch, ProofSearchProfile,
    RecordingProvider, SettledSearchOutcome, SettlementPolicy, SettlementResources,
    SolverInvocationIdentity, TranscriptError, TranscriptHeader, TranscriptRecorder,
    TranscriptToolchainPins, bind_fixed_ambient_framework_ii, record_acceptance,
    release_without_certifying, settle_search_outcome,
};
use crate::proposer_host::generic_io::ApiTrafficLimits;
use crate::proposer_host::generic_process::{
    GenericProcessConfig, GenericProcessProposer, GenericProcessResourceStatus,
    GenericProcessScratchLease, GenericProcessStartupError,
};
use crate::runtime::phase::{PhaseCancellation, PhaseStop};
use crate::runtime::{
    CancellationToken, RuntimeResourcePolicy, create_general_solver_admission, interrupt,
};
use crate::vampire::{
    FmbOptions, PROOF_CASC_PROFILE_ID, VampireSearchBudget, VampireWorkerCommand,
};

/// Immediate current Benchmark directories only: no Legacy traversal or fixed cohort.
pub fn discover_inputs(repository: &Path) -> Result<Vec<String>, String> {
    let repository = repository
        .canonicalize()
        .map_err(|error| error.to_string())?;
    let benchmark = repository.join("Benchmark");
    let mut inputs = Vec::new();
    for entry in std::fs::read_dir(&benchmark)
        .map_err(|error| format!("read {}: {error}", benchmark.display()))?
    {
        let entry = entry.map_err(|error| error.to_string())?;
        if !entry
            .file_type()
            .map_err(|error| error.to_string())?
            .is_dir()
        {
            continue;
        }
        let Some(id) = entry.file_name().to_str().map(str::to_owned) else {
            continue;
        };
        if valid_input_id(&id) && entry.path().join("Input.lean").is_file() {
            let source = entry.path().join("Input.lean");
            if source.canonicalize().map_err(|error| error.to_string())? != source {
                return Err(format!(
                    "current input must not be a symlink: {}",
                    source.display()
                ));
            }
            inputs.push(id);
        }
    }
    inputs.sort();
    if inputs.is_empty() {
        return Err("no current Benchmark inputs found".into());
    }
    Ok(inputs)
}

fn selected_inputs(config: &CampaignRunConfig, repository: &Path) -> Result<Vec<String>, String> {
    let inventory = discover_inputs(repository)?;
    resolve_inputs(config, &inventory)
}

fn resolve_inputs(config: &CampaignRunConfig, inventory: &[String]) -> Result<Vec<String>, String> {
    if config.all_inputs {
        return Ok(inventory.to_vec());
    }
    let mut selected = Vec::new();
    let mut seen = BTreeSet::new();
    for selector in &config.inputs {
        let id = if numeric_selector(selector) {
            let mut matches = inventory.iter().filter(|id| {
                id.strip_prefix("Example").is_some_and(|suffix| {
                    numeric_selector(suffix)
                        && suffix.trim_start_matches('0') == selector.trim_start_matches('0')
                })
            });
            let id = matches
                .next()
                .ok_or_else(|| format!("{selector} is not a current numeric Benchmark example"))?;
            if matches.next().is_some() {
                return Err(format!(
                    "{selector} matches multiple Benchmark inputs; use an exact ID"
                ));
            }
            id
        } else {
            inventory
                .iter()
                .find(|id| *id == selector)
                .ok_or_else(|| format!("{selector} is not a current Benchmark input"))?
        };
        if !seen.insert(id.clone()) {
            return Err(format!(
                "--input selects {id} more than once after resolving aliases"
            ));
        }
        selected.push(id.clone());
    }
    Ok(selected)
}

fn resource_limits_record(config: &CampaignRunConfig) -> Value {
    serde_json::to_value(&config.resource_limits).expect("fixed resource limits serialize")
}

/// The finite-model lane every campaign check races against the proof lane.
/// The start size is the default because the per-key retry frontier raises it
/// across attempts, as on every other production search path.
///
/// There is no campaign configuration without it. `FrameworkIIProduction`
/// `CheckConfig::new` takes the options rather than an `Option`, and the
/// campaign's lane count is a constant, so no flag, default or omitted
/// argument can turn a campaign into a proof-only search; expressing one at
/// all means naming the test-only constructor, which this crate's production
/// code never does.
fn campaign_fmb_options(config: &CampaignRunConfig) -> FmbOptions {
    debug_assert!(
        config.budgets.finite_model_lane(),
        "a campaign always races the finite-model lane"
    );
    FmbOptions::default()
}

/// The solver command every check of this campaign launches under.
///
/// A campaign that may escalate carries the split on its command; the
/// launch itself still clears the policy whenever the run's
/// [`crate::framework2::CascPortfolioPolicy`] is disabled, so the two
/// answers cannot disagree.
fn campaign_launch_command(
    config: &CampaignRunConfig,
    executable: &Path,
) -> Result<VampireWorkerCommand, String> {
    VampireWorkerCommand::new(executable)
        .with_proof_casc_policy(config.proof_casc_policy)
        .map_err(|error| error.to_string())
}

/// The direct-search baseline every campaign launch keeps. The production
/// authority derives its own ladder from exactly this, so the two cannot
/// disagree.
const CAMPAIGN_SOLVER_BASELINE: Duration = Duration::from_secs(30);

/// The production ladder's rungs, as multiples of the baseline.
const CAMPAIGN_RETRY_LADDER_MULTIPLES: [u32; 3] = [1, 3, 8];

/// The cumulative launch allowances in force for this run, in seconds.
///
/// A campaign that names no `--retry-allowance` runs the production
/// ladder, which is these multiples of the baseline. Either way the list is
/// what the run actually applies, so the record never has to be read as
/// "whatever the default was at the time".
fn retry_ladder_seconds(config: &CampaignRunConfig) -> Vec<f64> {
    let allowances: Vec<Duration> = match &config.retry_policy_override {
        Some(policy) => policy.allowances().to_vec(),
        None => CAMPAIGN_RETRY_LADDER_MULTIPLES
            .into_iter()
            .map(|multiple| CAMPAIGN_SOLVER_BASELINE * multiple)
            .collect(),
    };
    allowances
        .into_iter()
        .map(|allowance| allowance.as_secs_f64())
        .collect()
}

fn campaign_controls(config: &CampaignRunConfig) -> Value {
    json!({
        "search_limit_seconds": config.search_limits.overall_limit().as_secs_f64(),
        "certification_limit_seconds": config.certification_limit.as_secs_f64(),
        "consultation_limit_seconds": config.search_limits.consultation_limit().map(|limit| limit.as_secs_f64()),
        "transport_retries": config.consultation_policy.limits().max_transport_retries_per_request,
        "certificate_solver_limit_seconds": config.certificate_solver_limit_seconds,
        "counterexample_validation_limit_seconds": config.search_limits.counterexample_validation_limit().as_secs_f64(),
        "iteration_limit": config.search_limits.iteration_limit(),
        // `workers` is the operator's own number, N concurrent checks;
        // `budgets` is everything derived from it, recorded verbatim so two
        // runs are comparable from their settings alone.
        "workers": config.budgets.checks().get(),
        "budgets": config.budgets.record(),
        // When this run certifies what it accepts. It belongs beside the
        // budgets for the same reason they are there: a run directory is
        // only comparable with another if its settings say how it was made.
        "certify": config.certify.name(),
        // The search behaviour two runs must share before their timings or
        // their solved sets mean anything against each other: whether a
        // proof-lane launch may escalate into the `casc_2025` portfolio,
        // and how much of the allowance it gets when it may. The shares are
        // recorded in the exact decimal spelling the solver layer applies.
        "casc_portfolio": config.casc_portfolio.name(),
        "proof_casc_share": config.proof_casc_policy.initial_share().to_string(),
        "proof_casc_retry_share": config.proof_casc_policy.retry_added_share().to_string(),
        // The ladder itself, and not what the split then makes of it: the
        // per-stage limits are fixed functions of a rung and the two
        // shares, so recording them again would be recording the same
        // decision twice and inviting the two copies to disagree.
        "retry_allowance_seconds": retry_ladder_seconds(config),
        // The TPTP role a retry launch writes the check's premises under.
        // It changes no formula, but it changes the search Vampire runs on
        // the same problem, so two runs that disagree on it are no more
        // comparable than two that disagree on the portfolio policy.
        "premise_role_retries": config.retry_premise_role.name(),
        "resource_limits": resource_limits_record(config),
    })
}

fn fresh_label() -> String {
    format!(
        "{}-{}",
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_nanos(),
        std::process::id()
    )
}

fn resolve_path(repository: &Path, path: &Path) -> PathBuf {
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        repository.join(path)
    }
}

/// The key every result of a started search carries: how long the untrusted
/// search itself took, in seconds.
///
/// It is the campaign runner's own measurement on a monotonic clock, taken
/// immediately around the search loop, and it is the search time a campaign
/// reports: it excludes runner and Lean worker startup, record writing and
/// certification of every kind. It is absent — never zero — from a result
/// whose search never started.
pub const SEARCH_SECONDS: &str = "search_seconds";

/// Configuration failures use 2, observed interrupts use 130, and later failures use 3.
#[derive(Debug)]
pub struct CampaignRunError {
    pub exit_code: i32,
    pub(crate) detail: String,
}
impl From<String> for CampaignRunError {
    fn from(detail: String) -> Self {
        Self {
            exit_code: super::CAMPAIGN_FAILED,
            detail,
        }
    }
}
impl From<&str> for CampaignRunError {
    fn from(detail: &str) -> Self {
        detail.to_owned().into()
    }
}
impl std::fmt::Display for CampaignRunError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.detail.fmt(f)
    }
}
impl std::error::Error for CampaignRunError {}

/// A path under `root`, named relative to it, or `None` when it lies
/// elsewhere.
///
/// The root itself becomes `"."` rather than the empty string, which names
/// nothing.
fn under_root(path: &Path, root: &Path) -> Option<String> {
    let rest = path.strip_prefix(root).ok()?;
    Some(if rest.as_os_str().is_empty() {
        ".".to_owned()
    } else {
        rest.to_string_lossy().into_owned()
    })
}

/// A path inside one input's own directory, named relative to it.
///
/// Every record a search writes beside `result.json` is named this way, so a
/// reader resolves it against the directory holding the `result.json` it came
/// from and a run directory that has been copied still reads.
fn beside_result(path: &Path, directory: &Path) -> String {
    match under_root(path, directory) {
        Some(relative) => relative,
        // A record is always written into the input's own directory; name it
        // by its file name rather than by where this machine kept it.
        None => path
            .file_name()
            .map(|name| name.to_string_lossy().into_owned())
            .unwrap_or_default(),
    }
}

/// What a run's own records say about a caller-supplied path that lies
/// outside the repository, such as a proposer argument naming a scratch
/// directory or a provider CLI under the operator's home directory.
///
/// A path outside the repository is not portable, and most of it is not this
/// run's business to disclose either. The choice is made by the path's
/// *position* in the command, never by anything on disk, so the same
/// command line records identically on every machine that could run it: the
/// executable (position 0) is meaningful even off this repository — a
/// python interpreter, a provider CLI — so it is named by its bare file
/// name; every other out-of-repository path is this run's business to hide,
/// not to describe, so it is always this placeholder, with the flag that
/// named it left exactly as the caller wrote it.
const OUTSIDE_REPOSITORY: &str = "<outside-repository>";

/// The recorded spelling of the proposer executable when it lies outside
/// the repository: its bare file name. Position 0 of the command is always
/// the executable, so this does not depend on what this machine finds
/// there at record time — whether it exists, or is executable, is
/// validated separately, right after recording.
fn recorded_outside_executable(path: &Path) -> String {
    path.file_name()
        .map(|name| name.to_string_lossy().into_owned())
        .unwrap_or_else(|| OUTSIDE_REPOSITORY.to_owned())
}

/// A relative path resolved against `repository`, with `.` and `..`
/// components collapsed lexically and no filesystem access: a proposer
/// argument judged here need not exist on this machine, let alone at the
/// location it would resolve to, and it belongs to a different machine by
/// the time it is replayed.
fn resolve_lexically(repository: &Path, path: &Path) -> PathBuf {
    let mut normalized = repository.to_path_buf();
    for component in path.components() {
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

/// Whether a proposer argument names a location outside the repository,
/// resolved against `repository` without touching the filesystem.
///
/// A relative argument that walks back out with `..`
/// (`--proposer-arg=../scratch/x`) is exactly as much an outside path as
/// the same location spelled absolute, and a run's records must not
/// distinguish the two by luck of which form the caller typed. An ordinary
/// relative argument — an in-repository path, a flag, a number, a model
/// name — normalizes to somewhere under `repository` and is left alone.
fn argument_resolves_outside_repository(repository: &Path, path: &Path) -> bool {
    if path.is_absolute() {
        under_root(path, repository).is_none()
    } else {
        under_root(&resolve_lexically(repository, path), repository).is_none()
    }
}

/// The endpoint selection as every run record names it.
fn recorded_proposer(config: &CampaignRunConfig) -> Value {
    json!(
        config
            .proposer
            .as_ref()
            .map(|selection| &selection.recorded)
    )
}

fn resolve_generic_selection(
    config: &mut CampaignRunConfig,
    repository: &Path,
) -> Result<(), String> {
    if let Some(selection) = &mut config.proposer {
        selection.executable = resolve_path(repository, &selection.executable)
            .canonicalize()
            .map_err(|_| "resolve generic proposer executable")?;
        // What the run records: inside the repository, named relative to its
        // root; the executable's own file name, or the placeholder for any
        // other argument, when it lies outside the repository instead.
        if let Some(relative) = under_root(&selection.executable, repository) {
            selection.recorded.executable = relative;
        } else {
            selection.recorded.executable = recorded_outside_executable(&selection.executable);
        }
        for argument in &mut selection.recorded.arguments {
            let path = Path::new(argument.as_str());
            if let Some(relative) = under_root(path, repository) {
                *argument = relative;
            } else if argument_resolves_outside_repository(repository, path) {
                *argument = OUTSIDE_REPOSITORY.to_owned();
            }
        }
        let metadata = std::fs::metadata(&selection.executable)
            .map_err(|_| "inspect generic proposer executable")?;
        if !metadata.is_file()
            || selection.executable.to_str().is_none()
            || selection
                .arguments
                .iter()
                .any(|argument| argument.contains('\0'))
        {
            return Err("generic proposer requires a file path and NUL-free arguments".into());
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            if metadata.permissions().mode() & 0o111 == 0 {
                return Err("generic proposer file is not executable".into());
            }
        }
    }
    if (config.provider == CampaignProvider::Generic) != config.proposer.is_some() {
        return Err("generic proposer selection and executable disagree".into());
    }
    Ok(())
}

pub fn execute_campaign_run_cli(
    mut config: CampaignRunConfig,
    mut output: impl Write,
) -> Result<i32, CampaignRunError> {
    let repository = config
        .repository
        .canonicalize()
        .map_err(|error| format!("resolve repository: {error}"))?;
    let inputs = selected_inputs(&config, &repository)?;
    if !repository.join("Whiel.lean").is_file() {
        return Err("not a Whiel repository".into());
    }
    interrupt::clear();
    interrupt::install().map_err(|error| format!("install interruption handler: {error}"))?;
    let external = CancellationToken::new();
    resolve_generic_selection(&mut config, &repository).map_err(|detail| CampaignRunError {
        exit_code: super::CAMPAIGN_ARGUMENT_FAILURE,
        detail,
    })?;
    let destination = config
        .destination
        .as_ref()
        .map(|path| resolve_path(&repository, path))
        .unwrap_or_else(|| repository.join("artifacts/campaigns").join(fresh_label()));
    if destination.exists() {
        return Err("campaign destination already exists; choose a fresh directory".into());
    }
    // Never permit product output inside the protected checked-in input trees.
    let parent = destination
        .parent()
        .ok_or("campaign destination has no parent")?;
    let existing = parent
        .ancestors()
        .find(|path| path.exists())
        .ok_or("output has no existing ancestor")?
        .canonicalize()
        .map_err(|error| error.to_string())?;
    let protected = [
        "Benchmark",
        "Whiel",
        "VampLean",
        ".git",
        ".lake",
        "toolchain",
    ];
    if protected
        .iter()
        .any(|path| existing.starts_with(repository.join(path)))
    {
        return Err("campaign output overlaps a protected repository tree".into());
    }
    std::fs::create_dir_all(parent).map_err(|error| format!("create output parent: {error}"))?;
    let parent = parent.canonicalize().map_err(|error| error.to_string())?;
    if parent == repository
        || protected
            .iter()
            .any(|path| parent.starts_with(repository.join(path)))
    {
        return Err(
            "campaign output must be outside protected repository trees and repository root".into(),
        );
    }
    let destination = parent.join(
        destination
            .file_name()
            .ok_or("campaign destination has no name")?,
    );
    std::fs::create_dir(&destination)
        .map_err(|error| format!("reserve campaign output: {error}"))?;
    writeln!(output, "campaign output: {}", destination.display())
        .map_err(|error| error.to_string())?;
    let limits = resource_limits_record(&config);
    write_json(
        &destination.join("resource-limits.json"),
        &json!({"schema_version": 2, "limits": limits}),
    )?;
    writeln!(output, "resource limits: {}", limits).map_err(|error| error.to_string())?;
    // Neither the memory estimate nor the core count narrows `checks`,
    // default or explicit; the operator is told when either is exceeded.
    if config.budgets.exceeds_memory_estimate()
        && let Some(estimate) = config.budgets.memory_estimate_checks()
    {
        writeln!(
            output,
            "warning: --workers {} exceeds the {} this machine's memory is \
             estimated to hold ({} lanes per check at a planned {} MB each); \
             honouring it",
            config.budgets.checks(),
            estimate,
            config.budgets.lanes(),
            config.budgets.vampire_planned_footprint_mb(),
        )
        .map_err(|error| error.to_string())?;
    }
    if config.budgets.exceeds_host_parallelism() {
        writeln!(
            output,
            "warning: {} checks at {} lanes each ({} Vampire processes) exceeds this \
             machine's {} logical cores; honouring it",
            config.budgets.checks(),
            config.budgets.lanes(),
            config.budgets.vampire_processes(),
            config.budgets.host_parallelism(),
        )
        .map_err(|error| error.to_string())?;
    }
    let controls = campaign_controls(&config);
    let settings = json!({"schema_version": 3, "inputs": inputs, "controls": controls, "proposer": recorded_proposer(&config)});
    write_json(&destination.join("campaign-settings.json"), &settings)?;
    writeln!(output, "campaign controls: {controls}").map_err(|error| error.to_string())?;
    let space = SpaceGuard::new(
        &config.resource_limits,
        destination.clone(),
        external.clone(),
    );
    // Keep every registered transport directory alive until the monitor joins.
    // Reverse local drop order releases the monitor before these leases.
    let mut scratch_leases = Vec::new();
    let _space_monitor = SpaceMonitor::start(Arc::clone(&space))
        .map_err(|error| format!("start workspace guard: {error}"))?;
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .worker_threads(config.budgets.runtime_worker_threads().get())
        .enable_all()
        .build()
        .map_err(|error| format!("create campaign runtime: {error}"))?;
    let searched = runtime.block_on(async {
        let relay_root = external.clone();
        let relay = tokio::spawn(async move {
            interrupt::wait().await;
            relay_root.cancel();
        });
        let result = run_selected(
            &config,
            &repository,
            &destination,
            inputs,
            &external,
            &space,
            &mut scratch_leases,
            &mut output,
        )
        .await;
        relay.abort();
        let _ = relay.await;
        result
    })?;
    // `deferred` is one campaign in two phases, not two commands: the very
    // phase `campaign certify --run DIR` performs runs here once the last
    // input's search is over, so the two modes cannot reach different
    // statuses from the same records. It runs whenever any input was
    // accepted, not only when every one was: an input whose search failed is
    // no reason to leave the others uncertified, and the phase recomputes the
    // run's own exit code from the results it finds afterwards.
    //
    // It does not run after a workspace failure. A certification is the part
    // of a campaign that spends gigabytes per input, and starting it on a
    // workspace that has already tripped its own guard would fill the disk
    // rather than finish the run.
    if config.certify == super::CertifyMode::Deferred && !external.is_cancelled() {
        if let Some(detail) = space.failure() {
            writeln!(
                output,
                "certification phase skipped: the workspace guard already refused this run ({detail})"
            )
            .map_err(|error| error.to_string())?;
            return Ok(searched);
        }
        // The searches are done: the tokio runtime and every resource they
        // owned are released before a certification claims the machine. The
        // workspace guard is not one of them — it keeps watching the same
        // tree the certification now writes into.
        drop(runtime);
        writeln!(output, "certification phase: {}", destination.display())
            .map_err(|error| error.to_string())?;
        return super::certify_phase::certify_run_directory(
            &deferred_certify_config(&config, &repository, &destination),
            Some(&space),
            &mut output,
        );
    }
    Ok(searched)
}

/// The certification phase's own settings, taken from the run's.
///
/// Everything the phase needs is already a campaign control; only the
/// certify-side concurrency is new, and it takes its documented default
/// because `campaign run`'s own `--workers` counts concurrent clause
/// checks, which is not what bounds a certification job.
fn deferred_certify_config(
    config: &CampaignRunConfig,
    repository: &Path,
    destination: &Path,
) -> super::CampaignCertifyConfig {
    super::CampaignCertifyConfig {
        // The resolved paths, not the configured ones: the phase reads both
        // from here rather than taking them again as parameters, so there is
        // no second copy to keep in step.
        run: destination.to_path_buf(),
        repository: repository.to_path_buf(),
        worker: config.worker.clone(),
        jobs: super::default_jobs(),
        retention: config.retention,
        certification_limit: config.certification_limit,
        certificate_solver_limit_seconds: config.certificate_solver_limit_seconds,
        // The run's own workspace allowances; the guard itself is inherited,
        // so these are carried for the record rather than to start a second
        // monitor over the same tree.
        resource_limits: config.resource_limits.clone(),
        // This path always inherits a live guard (`certify_run_directory`'s
        // `inherited_space`), so it never resolves its own limits from a
        // recorded run and the distinction this marks does not apply; every
        // field reads as given so nothing downstream reconsiders it.
        workspace_limits_given: crate::framework2::resource_limits::WorkspaceLimitsGiven::ALL,
    }
}

#[allow(clippy::too_many_arguments)]
async fn run_selected(
    config: &CampaignRunConfig,
    repository: &Path,
    destination: &Path,
    inputs: Vec<String>,
    external: &CancellationToken,
    space: &Arc<SpaceGuard>,
    scratch_leases: &mut Vec<GenericProcessScratchLease>,
    output: &mut impl Write,
) -> Result<i32, String> {
    let mut results = Vec::new();
    let selected_inputs = inputs.clone();
    let mut api_resource_failure = None;
    for input in inputs {
        if api_resource_failure.is_some()
            || space.checkpoint().await.is_err()
            || external.is_cancelled()
        {
            break;
        }
        let directory = destination.join(&input);
        std::fs::create_dir(&directory).map_err(|error| error.to_string())?;
        writeln!(output, "{input}: admission").map_err(|error| error.to_string())?;
        let mut resources = InputApiResources::default();
        let result = match run_one(
            config,
            repository,
            &input,
            &directory,
            external,
            space,
            scratch_leases,
            &mut resources,
            output,
        )
        .await
        {
            Ok(result) => result,
            Err(error) => json!({"input":input,"status":"failed","detail":error}),
        };
        api_resource_failure = resources.failure();
        let mut result = if let Some(detail) = space.failure() {
            // The workspace refusal replaces the verdict, not the
            // measurement: an input whose search ran and then hit the guard
            // still reports how long that search took.
            let mut refused = json!({"input":input,"status":"resource_exhausted","detail":detail});
            if let Some(seconds) = result.get(SEARCH_SECONDS)
                && let Some(object) = refused.as_object_mut()
            {
                object.insert(SEARCH_SECONDS.into(), seconds.clone());
            }
            refused
        } else {
            result
        };
        result["campaign_controls"] = campaign_controls(config);
        result["schema_version"] = json!(3);
        result["proposer"] = recorded_proposer(config);
        write_json(&directory.join("result.json"), &result)?;
        writeln!(
            output,
            "{input}: {} (result: {})",
            result["status"].as_str().unwrap_or("failed"),
            directory.join("result.json").display()
        )
        .map_err(|error| error.to_string())?;
        results.push(result);
    }
    let completed = results
        .iter()
        .filter_map(|result| result["input"].as_str())
        .collect::<std::collections::BTreeSet<_>>();
    let unrun_inputs = selected_inputs
        .iter()
        .filter(|input| !completed.contains(input.as_str()))
        .cloned()
        .collect::<Vec<_>>();
    let resource_failure = api_resource_failure.or_else(|| space.failure());
    if let Some(detail) = &resource_failure {
        let _ = writeln!(output, "{detail}");
    }
    let interrupted = external.is_cancelled() && resource_failure.is_none();
    let complete = !interrupted && resource_failure.is_none() && unrun_inputs.is_empty();
    // Two different questions, answered separately so no reader can mistake
    // one for the other: whether every input reached a checked certificate,
    // and whether every input's untrusted search reached a verdict at all.
    let all_certified = complete
        && results
            .iter()
            .all(|result| matches!(result["status"].as_str(), Some("valid" | "invalid")));
    // Acceptance is a fact the run wrote to disk, so it is read back from
    // there rather than inferred from a status string: an input whose
    // certification failed was still accepted, and its record is still
    // beside it, which is exactly what these records exist to state.
    let all_accepted = complete
        && selected_inputs.iter().all(|input| {
            destination
                .join(input)
                .join(crate::framework2::ACCEPTED_RECORD_NAME)
                .is_file()
        });
    // The uncertified exit code is for work still to come, not for work that
    // failed: a run where every input is accepted but one certification
    // failed exits 3, not 4.
    let awaiting_certification = results.iter().all(|result| {
        matches!(
            result["status"].as_str(),
            Some("valid" | "invalid" | "valid_uncertified" | "invalid_uncertified")
        )
    });
    write_json(
        &destination.join("summary.json"),
        &json!({"schema_version":3,"interrupted":interrupted,"all_certified":all_certified,"all_accepted":all_accepted,"resource_failure":resource_failure,"selected_inputs":selected_inputs,"unrun_inputs":unrun_inputs,"campaign_controls":campaign_controls(config),"results":results}),
    )?;
    Ok(if interrupted {
        130
    } else if all_certified {
        0
    } else if all_accepted && awaiting_certification {
        super::CAMPAIGN_UNCERTIFIED
    } else {
        3
    })
}

fn write_json(path: &Path, value: &Value) -> Result<(), String> {
    let mut bytes = serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    std::fs::write(path, bytes).map_err(|error| format!("write {}: {error}", path.display()))
}

enum CommandProvider {
    Generic(Box<GenericProcessProposer>),
    None,
}

// This observer retains only B's traffic accounting, not endpoint authority.
// It survives the consuming search and sees a refusal first made at shutdown.
#[derive(Default)]
struct InputApiResources {
    endpoint: Option<GenericProcessResourceStatus>,
    startup_failure: Option<String>,
}

impl InputApiResources {
    fn record_startup_error(&mut self, error: &std::io::Error) {
        if matches!(
            startup_error(error),
            Some(
                GenericProcessStartupError::ResourceExhausted
                    | GenericProcessStartupError::ResourceExhaustedCleanupFailed(_)
            )
        ) {
            self.startup_failure = Some(GenericProcessStartupError::ResourceExhausted.to_string());
        }
    }

    fn failure(&self) -> Option<String> {
        self.startup_failure
            .clone()
            .or_else(|| self.endpoint.as_ref().and_then(|status| status.failure()))
    }
}
impl AgentProvider for CommandProvider {
    fn api_capabilities(&self) -> crate::proposer_api::ApiCapabilities {
        match self {
            Self::Generic(provider) => provider.api_capabilities(),
            Self::None => crate::proposer_api::ApiCapabilities::current([]),
        }
    }

    fn resource_failure(&self) -> Option<String> {
        match self {
            Self::Generic(provider) => provider.resource_failure(),
            Self::None => None,
        }
    }
    fn terminal_failure(&self) -> Option<crate::proposer_api::ProposerTerminalFailure> {
        match self {
            Self::Generic(provider) => provider.terminal_failure(),
            Self::None => None,
        }
    }

    fn consult<'a>(
        &'a mut self,
        push: &'a AgentPush,
        tools: &'a dyn AgentToolSurface,
        response: &'a mut AgentResponseWriter,
        cancellation: AgentSourceCancellation,
    ) -> AgentSourceFuture<'a> {
        match self {
            Self::Generic(provider) => provider.consult(push, tools, response, cancellation),
            Self::None => Box::pin(async { AgentSourceOutcome::SourceExhausted }),
        }
    }
    fn quiesce_request(&mut self) -> AgentSourceCleanupFuture<'_> {
        match self {
            Self::Generic(provider) => provider.quiesce_request(),
            Self::None => Box::pin(async { Ok(()) }),
        }
    }
    fn shutdown(
        &mut self,
        reason: crate::proposer_api::wire::ShutdownReason,
    ) -> AgentSourceCleanupFuture<'_> {
        match self {
            Self::Generic(provider) => provider.shutdown(reason),
            Self::None => Box::pin(async { Ok(()) }),
        }
    }
}

async fn provider(
    config: &CampaignRunConfig,
    space: &Arc<SpaceGuard>,
    scratch_leases: &mut Vec<GenericProcessScratchLease>,
    resources: &mut InputApiResources,
    cancellation: &CancellationToken,
) -> std::io::Result<CommandProvider> {
    if config.provider == CampaignProvider::None {
        return Ok(CommandProvider::None);
    }
    if let Some(selection) = &config.proposer {
        let mut process = GenericProcessConfig::new(
            selection.executable.clone(),
            selection
                .arguments
                .iter()
                .map(std::ffi::OsString::from)
                .collect(),
        );
        process.traffic_limits = ApiTrafficLimits {
            bytes: config.resource_limits.api_traffic_bytes,
            messages: config.resource_limits.api_messages,
        };
        let permitted = config
            .tool_policy
            .enabled()
            .iter()
            .map(|tool| tool.name())
            .collect::<Vec<_>>();
        let mut endpoint =
            match GenericProcessProposer::start(process, &permitted, cancellation).await {
                Ok(endpoint) => endpoint,
                Err(error) => {
                    resources.record_startup_error(&error);
                    return Err(error);
                }
            };
        resources.endpoint = Some(endpoint.resource_status());
        register_endpoint_workspace(&mut endpoint, space, scratch_leases, cancellation).await?;
        return Ok(CommandProvider::Generic(Box::new(endpoint)));
    }
    Err(std::io::Error::other("generic proposer executable absent"))
}

async fn register_endpoint_workspace(
    endpoint: &mut GenericProcessProposer,
    space: &Arc<SpaceGuard>,
    scratch_leases: &mut Vec<GenericProcessScratchLease>,
    cancellation: &CancellationToken,
) -> std::io::Result<()> {
    scratch_leases.push(endpoint.scratch_lease());
    space.register(endpoint.scratch_directory().to_path_buf());
    if let Err(failure) = space.checkpoint_with_cancellation(cancellation).await {
        endpoint
            .shutdown(crate::proposer_api::wire::ShutdownReason::Failure)
            .await
            .map_err(|cleanup| {
                std::io::Error::other(format!(
                    "{failure}; generic proposer workspace cleanup failed: {cleanup}"
                ))
            })?;
        if space.failure().is_none() {
            if endpoint.resource_failure().is_some() {
                return Err(std::io::Error::other(
                    GenericProcessStartupError::ResourceExhausted,
                ));
            }
            if cancellation.is_cancelled() {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::Interrupted,
                    GenericProcessStartupError::Cancelled,
                ));
            }
        }
        return Err(std::io::Error::other(failure));
    }
    Ok(())
}

// Only an explicitly cancelled startup can inherit the phase's stop reason.
// A protocol/setup failure or failed cleanup retains its own failure even if
// cleanup completes after the search deadline.
fn startup_failure_status(
    error: &std::io::Error,
    stop: Option<PhaseStop>,
) -> Option<(&'static str, crate::failure::FailureKind)> {
    if !matches!(
        startup_error(error),
        Some(GenericProcessStartupError::Cancelled)
    ) {
        return None;
    }
    match stop {
        Some(PhaseStop::DeadlineExpired) => Some((
            "search_timeout",
            crate::failure::FailureKind::OverallTimeout,
        )),
        Some(PhaseStop::Interrupted) => {
            Some(("interrupted", crate::failure::FailureKind::Interrupted))
        }
        None => None,
    }
}

fn startup_error(error: &std::io::Error) -> Option<&GenericProcessStartupError> {
    error
        .get_ref()
        .and_then(|cause| cause.downcast_ref::<GenericProcessStartupError>())
}

/// The status and `failure_kind` one settlement error is recorded under.
///
/// The status names the **phase** the failure happened in, in every
/// certify mode. Freezing the proved Core, settling the artifact backend
/// and shutting the solver pool down all belong to the search and its
/// settlement — a run that never entered a certification phase cannot have
/// failed to certify — while certification and publication belong to the
/// certification phase whether it ran inline, deferred, or was reached
/// only because an accepted input's records had to be published. Every
/// record carries a `failure_kind`, which is what tells a reader which
/// kind of `incomplete` or `certification_failed` this is.
fn settlement_failure_status(
    error: &crate::framework2::SettlementError,
) -> (&'static str, &'static str) {
    use crate::framework2::{AggregateCertificationError, PublicationError, SettlementError};
    match error {
        SettlementError::Certification(error)
            if matches!(**error, AggregateCertificationError::DeadlineExpired(_)) =>
        {
            ("certification_timeout", "CheckTimeout")
        }
        SettlementError::Certification(error)
            if matches!(**error, AggregateCertificationError::Interrupted) =>
        {
            ("interrupted", "Interrupted")
        }
        SettlementError::Publication(error)
            if matches!(**error, PublicationError::DeadlineExpired(_)) =>
        {
            ("certification_timeout", "CheckTimeout")
        }
        SettlementError::Publication(error) if matches!(**error, PublicationError::Interrupted) => {
            ("interrupted", "Interrupted")
        }
        SettlementError::Certification(_) => {
            ("certification_failed", "CertificateConstructionFailure")
        }
        SettlementError::Publication(_) => ("certification_failed", "PublicationFailure"),
        SettlementError::Freeze(_) => ("incomplete", "StateInvariantViolation"),
        SettlementError::Shutdown(_) => ("incomplete", "InfrastructureFailure"),
        SettlementError::Settlement(report) => ("incomplete", failure_kind_name(report.kind())),
    }
}

/// The `failure_kind` name a record carries, spelled exactly as the
/// variant is, which is what every other producer of the field writes.
fn failure_kind_name(kind: crate::failure::FailureKind) -> &'static str {
    match kind {
        crate::failure::FailureKind::PublicationFailure => "PublicationFailure",
        crate::failure::FailureKind::ManifestFailure => "ManifestFailure",
        crate::failure::FailureKind::StateInvariantViolation => "StateInvariantViolation",
        _ => "InfrastructureFailure",
    }
}

fn search_failure_record(
    input: &str,
    report: &crate::failure::FailureReport,
    api_resource_failure: Option<&str>,
) -> Value {
    use crate::failure::{FailureKind, FailureOrigin, FailureScope};
    // Source exhaustion by itself is a normal proposer outcome. Only the
    // authoritative run-global budget refusal receives this projection. In
    // particular, the controller's cleanup infrastructure error still wins.
    if report.origin() == FailureOrigin::AgentConsultation
        && report.kind() == FailureKind::SourceExhausted
        && report.scope() == FailureScope::RunGlobal
        && let Some(detail) = api_resource_failure
    {
        return json!({"input":input,"status":"resource_exhausted","detail":detail});
    }
    let status = match report.kind() {
        FailureKind::OverallTimeout => "search_timeout",
        FailureKind::Interrupted => "interrupted",
        _ => "incomplete",
    };
    json!({"input":input,"status":status,"failure_kind":format!("{:?}",report.kind()),"detail":report.detail()})
}

// The campaign owns a fresh input directory before any worker or endpoint
// starts. Reserve its staging parent exclusively; certificate builders create
// their own fresh children below it and retain their existing typed errors.
fn reserve_campaign_staging(directory: &Path) -> std::io::Result<PathBuf> {
    if !std::fs::symlink_metadata(directory)?.is_dir() {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "campaign input directory must be an owned directory, not a symlink",
        ));
    }
    let staging = directory.join("staging");
    std::fs::create_dir(&staging).map_err(|error| {
        std::io::Error::new(
            error.kind(),
            format!("reserve certificate staging {}: {error}", staging.display()),
        )
    })?;
    Ok(staging)
}

#[allow(clippy::too_many_arguments)]
async fn run_one(
    config: &CampaignRunConfig,
    repository: &Path,
    input: &str,
    directory: &Path,
    external: &CancellationToken,
    space: &Arc<SpaceGuard>,
    scratch_leases: &mut Vec<GenericProcessScratchLease>,
    resources: &mut InputApiResources,
    output: &mut impl Write,
) -> Result<Value, String> {
    space.checkpoint().await?;
    let staging_root = reserve_campaign_staging(directory).map_err(|error| error.to_string())?;
    let fuel_policy =
        CounterexampleFuelPolicy::new(config.search_limits.counterexample_validation_limit())
            .map_err(|error| error.to_string())?;
    let pinned =
        PinnedLeancheckVampire::from_lock(repository).map_err(|error| error.to_string())?;
    let (profiles, version) =
        certification_profiles(repository, &pinned, config.certificate_solver_limit_seconds)?;
    let boot_repo = repository.to_path_buf();
    let boot_worker = config.worker.clone();
    let boot_cancel = external.clone();
    let boot_input = input.to_owned();
    let (worker, descriptor) = tokio::task::spawn_blocking(move || {
        let worker = crate::certificate_cli::resolve_or_build_worker_with_cancellation(
            &boot_repo,
            boot_worker.as_deref(),
            &boot_cancel,
        )?;
        let descriptor = crate::certificate_cli::fetch_worker_manifest_with_cancellation(
            &worker,
            &boot_repo,
            &boot_input,
            &boot_cancel,
        )?;
        Ok::<_, String>((worker, descriptor))
    })
    .await
    .map_err(|error| error.to_string())??;
    let solver_admission = create_general_solver_admission(
        RuntimeResourcePolicy::agent_only(
            config.budgets.vampire_processes().get(),
            config.budgets.cpu_permits().get(),
        )
        .map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    let worker_binary = worker.clone();
    let pool = FixedAmbientWorkerPoolConfig::new(
        FixedAmbientWorkerCommand::new(worker, repository),
        config.budgets.lean_workers().get(),
    )
    .map_err(|error| error.to_string())?;
    let catalog_digest = bytes_sha256(
        format!("whiel-campaign:{}:{}", directory.display(), fresh_label()).as_bytes(),
    );
    let bound = bind_fixed_ambient_framework_ii(
        descriptor,
        pool,
        catalog_digest,
        config.host_limits,
        false,
        config.tool_policy.clone(),
        &solver_admission,
        external,
    )
    .await
    .map_err(|error| error.to_string())?;
    let (task, admission, solver, houdini) = bound.into_parts();
    if task.identity().canonical_id() != input {
        let _ = solver.shutdown().await;
        return Err("selected input differs from worker's checked task identity".into());
    }
    // Recording is bound to retention: a run that keeps every payload records
    // every consultation, and a run that keeps only what backs its terminal
    // result records none, so the default run's traffic is neither copied nor
    // able to fail a consultation on a recording fault.
    let recorder = if config.retention == Retention::All {
        let header = match transcript_toolchain_pins(repository, &worker_binary, &pinned, &profiles)
        {
            Ok(toolchain) => TranscriptHeader::for_live_run(
                proposer_identity(config),
                &task,
                &houdini,
                &config.consultation_policy,
                toolchain,
            ),
            Err(error) => {
                let _ = solver.shutdown().await;
                return Err(error);
            }
        };
        // The recording copies the run's API traffic, so the run's own traffic
        // budget bounds it: a recording that outgrows what the run was allowed
        // to exchange is a fault, not a silent truncation.
        let budget =
            usize::try_from(config.resource_limits.api_traffic_bytes).unwrap_or(usize::MAX);
        match TranscriptRecorder::new(header, budget) {
            Ok(recorder) => Some(recorder),
            Err(error) => {
                let _ = solver.shutdown().await;
                return Err(format!("bind consultation recording: {error}"));
            }
        }
    } else {
        None
    };
    // The search consumes itself on the way to its outcome, so its
    // attempt-history publication reports through this slot instead: the run's
    // own report names the record, or the refusal that lost it.
    let attempt_history = AttemptHistoryPublication::new();
    let (owner, artifacts) = match new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.join("artifacts"))
            .retention(config.retention)
            .payload_budget(Some(config.resource_limits.artifact_bytes))
            .payload_file_budget(Some(config.resource_limits.artifact_files)),
    ) {
        Ok(value) => value,
        Err(error) => {
            let _ = solver.shutdown().await;
            return Err(format!(
                "{:?}: {}",
                error.kind(),
                error.detail().unwrap_or("artifact setup failed")
            ));
        }
    };
    if let Err(detail) = space.checkpoint().await {
        let _ = solver.shutdown().await;
        let _ = owner.settle();
        return Err(detail);
    }
    let phase = match PhaseCancellation::new(external) {
        Ok(phase) => phase,
        Err(_) => {
            let _ = solver.shutdown().await;
            let _ = owner.settle();
            return Err("external cancellation already has a phase deadline".into());
        }
    };
    let mut startup_failure = None;
    let setup = async {
        let production = FrameworkIIProductionCheckConfig::new(
            artifacts.clone(),
            solver_admission.clone(),
            VampireSearchBudget::finite(CAMPAIGN_SOLVER_BASELINE),
            campaign_fmb_options(config),
            campaign_launch_command(config, pinned.path())?,
            phase.token().clone(),
            version,
            profiles,
        )
        .map_err(|error| error.to_string())?;
        let retry = config.resolve_retry_policy(production.retry_policy());
        let checker = solver.clone().production_checker(
            production
                .with_retry_policy(retry)
                .with_retry_premise_role(config.retry_premise_role)
                .with_host_limits(config.host_limits),
        );
        let runtime = PreCertificateAgentHoudiniRuntime::new(
            admission.clone(),
            solver.clone(),
            solver_admission.clone(),
            checker,
            artifacts.clone(),
            phase.token().clone(),
            config.tool_policy.clone(),
        )
        .reporting_attempt_history(attempt_history.clone());
        let feedback = AgentFeedbackPolicy::new(AgentFeedbackLimits {
            host_limits: config.host_limits,
            resource_limits: Some(config.resource_limits.clone()),
            ..AgentFeedbackLimits::default()
        })
        .map_err(|error| error.to_string())?;
        let deadline = tokio::time::Instant::now()
            .checked_add(config.search_limits.overall_limit())
            .ok_or("search limit overflows clock")?;
        // Start the endpoint only after all preceding fallible setup. The
        // joined constructor owns cleanup if its remaining authority checks fail.
        if !phase.token().bind_absolute_deadline(deadline) {
            return Err("search cancellation already owns another deadline".into());
        }
        let provider = match provider(config, space, scratch_leases, resources, phase.token()).await
        {
            Ok(provider) => provider,
            Err(error) => {
                let detail = error.to_string();
                startup_failure = Some(error);
                return Err(detail);
            }
        };
        PreCertificateAgentHoudiniSearch::new_with_joined_cleanup(
            Arc::clone(&task),
            RecordingProvider::optional_agent(
                provider,
                config.consultation_policy.clone(),
                recorder.clone(),
            ),
            houdini,
            runtime,
            config.search_limits,
            deadline,
            feedback,
        )
        .await
        .map_err(|error| {
            format!(
                "{:?}: {}",
                error.kind(),
                error.detail().unwrap_or("search construction failed")
            )
        })
    }
    .await;
    let search = match setup {
        Ok(search) => search,
        Err(error) => {
            let phase_result = phase.finish().await;
            let solver_result = solver.shutdown().await;
            let artifact_result = owner.settle();
            // All owners are joined before classification. Cleanup failure
            // dominates cancellation and retains the original startup detail.
            let mut cleanup_failures = Vec::new();
            if let Err(failure) = &phase_result {
                cleanup_failures.push(format!("search relay cleanup: {failure}"));
            }
            if let Err(failure) = solver_result {
                cleanup_failures.push(format!("solver cleanup: {failure}"));
            }
            if let Err(failure) = artifact_result {
                cleanup_failures.push(format!("artifact cleanup: {failure:?}"));
            }
            if !cleanup_failures.is_empty() {
                return Err(format!("{error}; {}", cleanup_failures.join("; ")));
            }
            let stop = phase_result.expect("cleanup failure handled").stop;
            if startup_failure.as_ref().is_some_and(|failure| {
                matches!(
                    startup_error(failure),
                    Some(GenericProcessStartupError::ResourceExhausted)
                )
            }) {
                return Ok(json!({"input":input,"status":"resource_exhausted","detail":error}));
            }
            if let Some((status, kind)) = startup_failure
                .as_ref()
                .and_then(|failure| startup_failure_status(failure, stop))
            {
                return Ok(
                    json!({"input":input,"status":status,"failure_kind":format!("{kind:?}"),"detail":error}),
                );
            }
            return Err(error);
        }
    };
    // Reporting failure must not bypass owned solver/artifact cleanup.
    let _ = writeln!(
        output,
        "{input}: search ({} seconds)",
        config.search_limits.overall_limit().as_secs_f64()
    );
    let _ = space.checkpoint().await;
    let search_started = std::time::Instant::now();
    let outcome = search.run().await;
    let search_elapsed = search_started.elapsed();
    // Seal and publish the consultation records before settlement, so every
    // outcome keeps them: settlement consumes the backend owner, and only the
    // Valid arm of it publishes anything of its own. The search has stopped
    // recording by now, so a later cleanup failure cannot cost the records.
    let consultation_records =
        recorder
            .as_ref()
            .map(|recorder| match recorder.finish(&artifacts) {
                Ok(recorded) => {
                    let _ = writeln!(
                        output,
                        "{input}: consultation records ({} frames)",
                        recorded.artifacts().len()
                    );
                    // Name what to read, not just how much of it there is: the
                    // manifest kind and scope that select exactly this chain,
                    // and the record ids of its frames in chain order.
                    json!({
                        "frames": recorded.artifacts().len(),
                        "head": recorded.head(),
                        "kind": ArtifactKind::RuntimeTrace,
                        "scope": ["root", CONSULTATION_RECORD_SCOPE],
                        "artifact_ids": recorded
                            .artifacts()
                            .iter()
                            .map(|artifact| artifact.local_id())
                            .collect::<Vec<_>>(),
                    })
                }
                Err(error) => {
                    let detail = error.to_string();
                    let _ = writeln!(
                        output,
                        "{input}: consultation records unavailable ({detail})"
                    );
                    let published = match error {
                        TranscriptError::Publication { published } => published,
                        _ => 0,
                    };
                    json!({
                        "error": detail,
                        "published_frames": published,
                        "kind": ArtifactKind::RuntimeTrace,
                        "scope": ["root", CONSULTATION_RECORD_SCOPE],
                    })
                }
            });
    let phase_result = phase.finish().await;
    if let Err(error) = phase_result {
        drop(outcome);
        let _ = solver.shutdown().await;
        let _ = owner.settle();
        return Err(format!("search relay cleanup: {error}"));
    }
    let _ = space.checkpoint().await;
    // The records come first, in every mode. Certification can fail or time
    // out; when it does, what the search found must still be on disk, and
    // the record is what a later `campaign certify` rebuilds from.
    let mut outcome = outcome;
    let accepted = match record_acceptance(
        &mut outcome,
        AcceptanceRecordRequest {
            input_directory: directory,
            fuel_policy,
            search_elapsed,
            search_limit: config.search_limits.overall_limit(),
        },
    ) {
        Ok(accepted) => accepted,
        Err(error) => {
            let detail = error.to_string();
            // A Core that will not freeze is a certification failure, not a
            // campaign-driver failure: the search reached its result and the
            // record is what could not be made from it.
            let status = match &error {
                crate::framework2::AcceptanceRecordError::Freeze(_) => Some("certification_failed"),
                _ => None,
            };
            let released = release_without_certifying(
                outcome,
                SettlementResources {
                    solver,
                    artifacts: owner,
                },
            )
            .await;
            let detail = match released {
                Ok(()) => detail,
                Err(cleanup) => format!("{detail}; {cleanup}"),
            };
            return match status {
                Some(status) => {
                    let mut report = json!({"input":input,"status":status,"detail":detail});
                    attach_run_records(
                        &mut report,
                        search_elapsed,
                        consultation_records,
                        &attempt_history,
                    );
                    Ok(report)
                }
                None => Err(detail),
            };
        }
    };
    if let Some(accepted) = &accepted {
        let _ = writeln!(
            output,
            "{input}: accepted {} (record: {})",
            accepted.verdict().name(),
            accepted.record().display()
        );
    }
    if !config.certify.certifies_inline()
        && let Some(accepted) = &accepted
    {
        let _ = writeln!(output, "{input}: settlement without certification");
        let status = accepted.verdict().uncertified_status();
        let record = beside_result(accepted.record(), directory);
        let envelope = beside_result(accepted.envelope(), directory);
        let released = release_without_certifying(
            outcome,
            SettlementResources {
                solver,
                artifacts: owner,
            },
        )
        .await;
        // The staging parent this input reserved was never entered: a later
        // `campaign certify` stages under its own fresh root rather than
        // re-reserving this one.
        let _ = std::fs::remove_dir(&staging_root);
        released.map_err(|error| error.to_string())?;
        let mut report = json!({
            "input": input,
            "status": status,
            "record": record,
            "accepted": envelope,
        });
        attach_run_records(
            &mut report,
            search_elapsed,
            consultation_records,
            &attempt_history,
        );
        return Ok(report);
    }
    let _ = writeln!(output, "{input}: settlement");
    let result = settle_search_outcome(
        outcome,
        SettlementPolicy {
            space_guard: Some(space),
            admission: &admission,
            solver_admission: &solver_admission,
            pinned: &pinned,
            canonical_id: input,
            input_namespace: task.identity().namespace(),
            repository_root: repository.to_path_buf(),
            staging_root,
            private_root: directory.join("private"),
            input_directory: directory.to_path_buf(),
            destination: directory.join("Certificate"),
            time_limit_seconds: config.certificate_solver_limit_seconds,
            certification_limit: config.certification_limit,
            concurrency: config.budgets.certification_jobs(),
            fuel_policy,
            retention: config.retention,
            external_cancellation: external,
            #[cfg(feature = "test-hooks")]
            hooks: crate::framework2::CertificateBuildHooks::default(),
        },
        SettlementResources {
            solver,
            artifacts: owner,
        },
    )
    .await;
    let report = match result {
        // The module and theorem are recorded beside the claim they support:
        // a later `campaign certify` over this directory revalidates the
        // published tree before letting the claim stand, and a tree it
        // cannot name it cannot check.
        Ok(SettledSearchOutcome::Valid(published)) => {
            json!({"input":input,"status":"valid","certificate":beside_result(published.certificate(),directory),"axioms":published.revalidation().axioms,"certificate_module":published.receipt().certificate_module,"certificate_theorem":published.receipt().certificate_theorem})
        }
        Ok(SettledSearchOutcome::Invalid(published)) => {
            json!({"input":input,"status":"invalid","certificate":beside_result(published.certificate(),directory),"counterexample":beside_result(&directory.join("Counterexample.json"),directory),"axioms":published.revalidation().axioms,"certificate_module":published.receipt().certificate_module,"certificate_theorem":published.receipt().certificate_theorem})
        }
        Ok(SettledSearchOutcome::Failure(report)) => {
            search_failure_record(input, &report, resources.failure().as_deref())
        }
        Err(error) => {
            let (status, kind) = settlement_failure_status(&error);
            json!({"input":input,"status":status,"failure_kind":kind,"detail":error.to_string()})
        }
    };
    let mut report = report;
    attach_run_records(
        &mut report,
        search_elapsed,
        consultation_records,
        &attempt_history,
    );
    Ok(report)
}

/// Attach what the search itself produced to whatever result it reached.
///
/// The records and the search's own duration belong to the search, not to
/// the certification, so every terminal report that ran one carries them:
/// the inline result, the uncertified one, and the failed one alike. A run
/// that never reached [`SEARCH_SECONDS`] has no such key rather than a zero
/// that would read as an instant search.
fn attach_run_records(
    report: &mut Value,
    search_elapsed: Duration,
    consultation_records: Option<Value>,
    attempt_history: &AttemptHistoryPublication,
) {
    if let Some(object) = report.as_object_mut() {
        object.insert(SEARCH_SECONDS.into(), json!(search_elapsed.as_secs_f64()));
    }
    if let Some(records) = consultation_records
        && let Some(object) = report.as_object_mut()
    {
        object.insert("consultation_records".into(), records);
    }
    // A run that attempted its attempt history reports what became of it, so a
    // refused record is visible instead of indistinguishable from a run that
    // published none.
    if let Some(published) = attempt_history.outcome()
        && let Some(object) = report.as_object_mut()
    {
        let record = match published {
            Ok(artifact) => json!({
                "kind": ArtifactKind::RuntimeTrace,
                "scope": ["root", ATTEMPT_HISTORY_SCOPE],
                "artifact_id": artifact.local_id(),
            }),
            Err(detail) => json!({"error": detail}),
        };
        object.insert("attempt_history".into(), record);
    }
}

/// The run's provider-neutral proposer identity for its recording.
///
/// B names no model, vendor or product here. The identity is a digest over
/// the endpoint selection the host already wrote to `campaign-settings.json`,
/// so a record is attributable to its run without the transcript carrying a
/// command line that may itself hold something private.
fn proposer_identity(config: &CampaignRunConfig) -> String {
    format!(
        "generic-endpoint:{}",
        canonical_value_sha256(&recorded_proposer(config))
    )
}

/// Resolve the toolchain half of a run's recording identity.
///
/// Every pin is a digest the host can re-derive from what it already
/// verified: the running verifier, the worker it launched, the locked Lean
/// role for this platform, the pinned leancheck Vampire, and the two
/// certification profiles this run would publish under.
fn transcript_toolchain_pins(
    repository: &Path,
    worker: &Path,
    pinned: &PinnedLeancheckVampire,
    profiles: &FrameworkIICertificationProfiles,
) -> Result<TranscriptToolchainPins, String> {
    let runner = std::env::current_exe()
        .map_err(|error| format!("resolve the running verifier: {error}"))?;
    let digest = |path: &Path| {
        crate::entailment::assembly::hash_file_sha256(path)
            .map_err(|error| format!("hash {}: {error}", path.display()))
    };
    let lock: Value = serde_json::from_slice(
        &std::fs::read(repository.join("toolchain.lock.json"))
            .map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    Ok(TranscriptToolchainPins {
        runner_digest: digest(&runner)?,
        worker_digest: digest(worker)?,
        // The lock pins Lean per platform, so the host's own platform is part
        // of the identity rather than an unstated assumption.
        lean_digest: canonical_value_sha256(&json!({
            "lean_toolchain": lock["lean_toolchain"],
            "role": lock["roles"]["lean"],
            "os": std::env::consts::OS,
            "arch": std::env::consts::ARCH,
        })),
        vampire_digest: pinned.sha256().to_owned(),
        profile_digest: canonical_value_sha256(&json!({
            "direct": profiles.direct().profile_digest(),
            "casc_2025": profiles.casc_2025().profile_digest(),
        })),
    })
}

fn pinned_vamplean_digest(repository: &Path, lock: &Value) -> Result<String, String> {
    let role = &lock["roles"]["vamplean_runtime"];
    let source = role["path"]
        .as_str()
        .filter(|path| !path.is_empty())
        .ok_or("VampLean source path missing or invalid")?;
    let relative = Path::new(source);
    if relative.is_absolute()
        || relative
            .components()
            .any(|part| matches!(part, std::path::Component::ParentDir))
    {
        return Err("VampLean source path must be repository-relative without `..`".into());
    }
    // Resolve lexically so the supported .lake -> .lake.nosync layout works.
    let digest = bytes_sha256(
        &std::fs::read(repository.join(relative))
            .map_err(|error| format!("read VampLean source {source}: {error}"))?,
    );
    if role["sha256"].as_str() != Some(&digest) {
        return Err("VampLean source differs from toolchain lock".into());
    }
    Ok(digest)
}

/// Build provenance metadata from the pinned binary, actual profile argv and
/// exact current source files. Fresh certificate construction independently
/// resolves and checks its authoritative tools, Lean targets and std3 closure.
fn certification_profiles(
    repository: &Path,
    pinned: &PinnedLeancheckVampire,
    time_limit_seconds: u64,
) -> Result<(FrameworkIICertificationProfiles, String), String> {
    let lock: Value = serde_json::from_slice(
        &std::fs::read(repository.join("toolchain.lock.json"))
            .map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    let version = lock["roles"]["leancheck_vampire"]["version_contains"]
        .as_array()
        .ok_or("Vampire version pin missing")?
        .iter()
        .map(|part| part.as_str().ok_or("invalid Vampire version pin"))
        .collect::<Result<Vec<_>, _>>()?
        .join("; ");
    let digest = |paths: &[&str]| -> Result<String, String> {
        let mut files = BTreeMap::new();
        for path in paths {
            files.insert(
                *path,
                bytes_sha256(
                    &std::fs::read(repository.join(path))
                        .map_err(|error| format!("read profile source {path}: {error}"))?,
                ),
            );
        }
        Ok(canonical_value_sha256(&json!(files)))
    };
    let vamplean = pinned_vamplean_digest(repository, &lock)?;
    let generator = digest(&["Whiel/Synthesis/FrameworkII/FixedAmbient/CertificateEmitter.lean"])?;
    let contract = digest(&[
        "Whiel/Synthesis/FrameworkII/FixedAmbient/CertificateJobs.lean",
        "whiel_runner/src/framework2/certificate.rs",
        "whiel_runner/src/runtime/owned_path.rs",
    ])?;
    let transformer = digest(&[
        "whiel_runner/src/framework2/proof_transform/mod.rs",
        "whiel_runner/src/framework2/proof_transform/canonical.rs",
        "whiel_runner/src/framework2/proof_transform/prenex.rs",
        "whiel_runner/src/framework2/proof_transform/projection.rs",
        "whiel_runner/src/framework2/proof_transform/lrat.rs",
        "whiel_runner/src/runtime/owned_path.rs",
    ])?;
    let bridge = digest(&[
        "Whiel/Synthesis/FrameworkII/FixedAmbient/Worker.lean",
        "Whiel/Synthesis/Runtime/FixedAmbientWorker.lean",
    ])?;
    let cadical = crate::framework2::PinnedKernelLratCadical::from_lock(repository)
        .map_err(|error| error.to_string())?;
    let cadical_invocation = SolverInvocationIdentity::from_parts(
        Arc::from("cadical"),
        Arc::from(cadical.version()),
        Arc::from(cadical.path().to_string_lossy().as_ref()),
        Arc::from(cadical.sha256()),
        Arc::from(std::env::consts::OS),
        Arc::from(std::env::consts::ARCH),
        cadical
            .arguments()
            .iter()
            .map(|arg| Arc::from(arg.as_str()))
            .collect(),
    )
    .map_err(|error| error.to_string())?;
    let make = |kind| {
        let invocation = certification_invocation(pinned, &version, kind, time_limit_seconds)?;
        LeancheckCertificationProfile::new(
            kind,
            PROOF_CASC_PROFILE_ID,
            invocation,
            Some(cadical_invocation.clone()),
            vamplean.clone(),
            generator.clone(),
            contract.clone(),
            transformer.clone(),
            bridge.clone(),
        )
        .map_err(|error| error.to_string())
    };
    let profiles = FrameworkIICertificationProfiles::new(
        make(ProofSearchProfile::Direct)?,
        make(ProofSearchProfile::Casc2025)?,
    )
    .map_err(|error| error.to_string())?;
    Ok((profiles, version))
}

fn certification_invocation(
    pinned: &PinnedLeancheckVampire,
    version: &str,
    profile: ProofSearchProfile,
    time_limit_seconds: u64,
) -> Result<SolverInvocationIdentity, String> {
    let arguments = LeancheckProfile::new(profile)
        .arguments(time_limit_seconds)
        .iter()
        .map(|arg| Arc::<str>::from(arg.to_string_lossy().as_ref()))
        .collect();
    SolverInvocationIdentity::from_parts(
        Arc::from("vampire"),
        Arc::from(version),
        Arc::from(pinned.path().to_string_lossy().as_ref()),
        Arc::from(pinned.sha256()),
        Arc::from(std::env::consts::OS),
        Arc::from(std::env::consts::ARCH),
        arguments,
    )
    .map_err(|error| error.to_string())
}

#[cfg(test)]
mod vamplean_pin_tests {
    use super::*;

    const SOURCE: &[u8] = b"namespaced runtime fixture\n";
    const SOURCE_PATH: &str = ".lake/packages/vamp_lean/VampLean.lean";

    struct Scratch(PathBuf);

    impl Scratch {
        fn new() -> Self {
            let root = std::env::temp_dir().join(format!("whiel-vamplean-pin-{}", fresh_label()));
            std::fs::create_dir_all(&root).unwrap();
            Self(root)
        }

        fn write_source(&self) {
            let path = self.0.join(SOURCE_PATH);
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            std::fs::write(path, SOURCE).unwrap();
        }
    }

    impl Drop for Scratch {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    fn lock() -> Value {
        json!({"roles": {"vamplean_runtime": {
            "path": SOURCE_PATH,
            "sha256": bytes_sha256(SOURCE),
        }}})
    }

    #[test]
    fn dependency_source_is_hashed_at_the_locked_path() {
        let root = Scratch::new();
        root.write_source();
        assert_eq!(
            pinned_vamplean_digest(&root.0, &lock()).unwrap(),
            bytes_sha256(SOURCE)
        );
    }

    #[test]
    fn missing_or_malformed_source_paths_are_rejected() {
        let root = Scratch::new();
        root.write_source();
        for path in [Value::Null, json!(17), json!("")] {
            let mut pin = lock();
            pin["roles"]["vamplean_runtime"]["path"] = path;
            assert_eq!(
                pinned_vamplean_digest(&root.0, &pin).unwrap_err(),
                "VampLean source path missing or invalid"
            );
        }
        assert!(pinned_vamplean_digest(&root.0, &json!({})).is_err());
    }

    #[test]
    fn absolute_and_parent_traversal_paths_are_rejected() {
        let root = Scratch::new();
        root.write_source();
        for path in [
            json!(root.0.join(SOURCE_PATH)),
            json!("../VampLean.lean"),
            json!(".lake/../VampLean.lean"),
        ] {
            let mut pin = lock();
            pin["roles"]["vamplean_runtime"]["path"] = path;
            assert_eq!(
                pinned_vamplean_digest(&root.0, &pin).unwrap_err(),
                "VampLean source path must be repository-relative without `..`"
            );
        }
    }

    #[test]
    fn missing_source_is_rejected_without_a_vendor_fallback() {
        let root = Scratch::new();
        let vendor = root.0.join("VampLean/Runtime.lean");
        std::fs::create_dir_all(vendor.parent().unwrap()).unwrap();
        std::fs::write(vendor, SOURCE).unwrap();
        assert!(
            pinned_vamplean_digest(&root.0, &lock())
                .unwrap_err()
                .starts_with("read VampLean source")
        );
    }

    #[test]
    fn mismatched_bytes_or_missing_digest_are_rejected() {
        let root = Scratch::new();
        root.write_source();
        let mut missing = lock();
        missing["roles"]["vamplean_runtime"]
            .as_object_mut()
            .unwrap()
            .remove("sha256");
        assert_eq!(
            pinned_vamplean_digest(&root.0, &missing).unwrap_err(),
            "VampLean source differs from toolchain lock"
        );
        std::fs::write(root.0.join(SOURCE_PATH), b"different runtime").unwrap();
        assert_eq!(
            pinned_vamplean_digest(&root.0, &lock()).unwrap_err(),
            "VampLean source differs from toolchain lock"
        );
    }

    #[cfg(unix)]
    #[test]
    fn cloud_sync_lake_symlink_is_supported() {
        let root = Scratch::new();
        std::fs::create_dir(root.0.join(".lake.nosync")).unwrap();
        std::os::unix::fs::symlink(".lake.nosync", root.0.join(".lake")).unwrap();
        root.write_source();
        assert_eq!(
            pinned_vamplean_digest(&root.0, &lock()).unwrap(),
            bytes_sha256(SOURCE)
        );
    }
}

#[cfg(test)]
mod search_timing_tests {
    use super::*;

    /// Every result of a started search carries the runner's own search
    /// time, whatever the search or the certification then did with it.
    ///
    /// One writer serves every arm — the certified one, the uncertified one,
    /// the failed one and the certification failure — so a new arm cannot
    /// quietly omit the measurement a campaign reports as its search time.
    #[test]
    fn every_started_search_reports_its_own_duration() {
        let history = AttemptHistoryPublication::new();
        for status in [
            "valid",
            "invalid",
            "valid_uncertified",
            "invalid_uncertified",
            "certification_failed",
            "certification_timeout",
            "search_timeout",
            "incomplete",
            "interrupted",
        ] {
            let mut report = json!({"input": "Example0001", "status": status});
            attach_run_records(&mut report, Duration::from_millis(1500), None, &history);
            assert_eq!(
                report[SEARCH_SECONDS], 1.5,
                "{status} must report its search time"
            );
        }
    }

    /// A workspace refusal replaces the verdict, not the measurement; and a
    /// result that never reached the search loop carries no key at all
    /// rather than a zero that would read as an instant search.
    #[test]
    fn a_search_that_never_started_reports_no_duration() {
        let searched = json!({"input":"Example0001","status":"valid",SEARCH_SECONDS:12.5});
        let mut refused = json!({"input":"Example0001","status":"resource_exhausted"});
        if let Some(seconds) = searched.get(SEARCH_SECONDS)
            && let Some(object) = refused.as_object_mut()
        {
            object.insert(SEARCH_SECONDS.into(), seconds.clone());
        }
        assert_eq!(refused[SEARCH_SECONDS], 12.5);

        // The driver's own pre-search failures build their result without
        // the writer above, so the key is absent rather than zero.
        let unstarted =
            json!({"input":"Example0001","status":"failed","detail":"no toolchain pin"});
        assert!(unstarted.get(SEARCH_SECONDS).is_none());
    }
}

#[cfg(test)]
mod cli_control_tests {
    use super::*;
    use crate::entailment::PremiseRole;

    fn parse(args: &[&str]) -> CampaignRunConfig {
        crate::campaign_cli::parse_campaign_run_arguments(
            &args
                .iter()
                .map(|value| (*value).to_owned())
                .collect::<Vec<_>>(),
        )
        .unwrap()
    }

    #[test]
    fn aliases_resolve_against_inventory_without_integer_or_padding_assumptions() {
        let inventory = [
            "Example0000",
            "Example0001",
            "Example0013",
            "ExampleG160",
            "NamedCase",
        ]
        .map(str::to_owned);
        let config = parse(&["--no-proposer", "--input", "13,0001,NamedCase,0"]);
        assert_eq!(
            resolve_inputs(&config, &inventory).unwrap(),
            ["Example0013", "Example0001", "NamedCase", "Example0000"]
        );
        assert_eq!(
            resolve_inputs(&parse(&["--no-proposer", "--all"]), &inventory).unwrap(),
            inventory
        );
        for selection in ["160", "2", "1,Example0001", "0001,1"] {
            assert!(
                resolve_inputs(&parse(&["--no-proposer", "--input", selection]), &inventory)
                    .is_err()
            );
        }
        let ambiguous = ["Example01".to_owned(), "Example0001".to_owned()];
        assert!(resolve_inputs(&parse(&["--no-proposer", "--input", "1"]), &ambiguous).is_err());
        assert_eq!(
            resolve_inputs(
                &parse(&["--no-proposer", "--input", "Example01"]),
                &ambiguous
            )
            .unwrap(),
            ["Example01"]
        );
        let huge = "1234567890123456789012345678901234567890";
        assert_eq!(
            resolve_inputs(
                &parse(&["--no-proposer", "--input", huge]),
                &[format!("Example{huge}")]
            )
            .unwrap(),
            [format!("Example{huge}")]
        );
    }

    /// Even the narrowest campaign races both lanes. A pair that is admitted
    /// only one process runs its lanes one after the other
    /// (`vampire::race::run_pair_serial`), which would make `--workers 1` a
    /// different search from `--workers 2` rather than a narrower one; the
    /// derived Vampire budget is `checks × lanes` precisely so that cannot
    /// happen.
    #[test]
    fn the_narrowest_campaign_still_races_both_lanes() {
        for arguments in [
            vec!["--no-proposer", "--input", "1", "--workers", "1"],
            vec!["--no-proposer", "--input", "1"],
        ] {
            let config = parse(&arguments);
            let budgets = config.budgets;
            assert_eq!(budgets.lanes().get(), 2);
            assert!(budgets.vampire_processes().get() >= 2);
            let policy = RuntimeResourcePolicy::agent_only(
                budgets.vampire_processes().get(),
                budgets.cpu_permits().get(),
            )
            .unwrap();
            // `VampireMode::ProofAndFmb` asks for two processes and is granted
            // `min(2, max_vampire_processes)`; two keeps the lanes concurrent.
            assert!(policy.max_vampire_processes() >= 2);
        }
    }

    /// A campaign cannot be configured without the finite-model lane: the
    /// options are a value, not an `Option`, and the recorded lane count says
    /// the same thing.
    /// A settlement failure is recorded under the phase it happened in,
    /// the same way in every certify mode, and always with the
    /// `failure_kind` that says which failure it was. A run that never
    /// entered a certification phase cannot have failed to certify; a run
    /// that did cannot have its certification failure recorded as an
    /// incomplete search.
    #[test]
    fn a_settlement_failure_is_recorded_under_the_phase_it_happened_in() {
        use crate::framework2::{
            AggregateCertificationError, CoreFreezeError, PublicationError, SettlementError,
        };
        assert_eq!(
            settlement_failure_status(&SettlementError::Freeze(
                CoreFreezeError::TaskIdentityMismatch
            )),
            ("incomplete", "StateInvariantViolation")
        );
        assert_eq!(
            settlement_failure_status(&SettlementError::Shutdown("pool".into())),
            ("incomplete", "InfrastructureFailure")
        );
        assert_eq!(
            settlement_failure_status(&SettlementError::Publication(Box::new(
                PublicationError::Interrupted
            ))),
            ("interrupted", "Interrupted")
        );
        assert_eq!(
            settlement_failure_status(&SettlementError::Certification(Box::new(
                AggregateCertificationError::Interrupted
            ))),
            ("interrupted", "Interrupted")
        );
        assert_eq!(
            settlement_failure_status(&SettlementError::Certification(Box::new(
                AggregateCertificationError::Io("no room".into())
            ))),
            ("certification_failed", "CertificateConstructionFailure")
        );
        // The mode does not enter into it: the same error is the same
        // record whether the run certified inline, deferred, or not at all.
        for mode in ["inline", "deferred", "never"] {
            let config = parse(&["--no-proposer", "--input", "1", "--certify", mode]);
            assert_eq!(config.certify.name(), mode);
        }
    }

    #[test]
    fn the_campaign_check_configuration_enables_the_finite_model_lane() {
        let config = parse(&["--no-proposer", "--input", "1"]);
        assert!(config.budgets.finite_model_lane());
        assert_eq!(
            campaign_fmb_options(&config),
            FmbOptions::default(),
            "a campaign check races the finite-model lane"
        );
        let controls = campaign_controls(&config);
        assert_eq!(controls["budgets"]["finite_model_lane"], true);
        assert_eq!(controls["budgets"]["lanes"], 2);
    }

    #[test]
    fn custom_solver_allowance_reaches_recorded_native_invocations_and_controls() {
        let config = parse(&[
            "--no-proposer",
            "--input",
            "1",
            "--certificate-solver-limit",
            "17",
            "--consultation-limit",
            "0.125",
            "--transport-retries",
            "2",
        ]);
        let pinned = PinnedLeancheckVampire::unverified_for_tests(
            PathBuf::from("/fixture/vampire"),
            "a".repeat(64),
        );
        for profile in [ProofSearchProfile::Direct, ProofSearchProfile::Casc2025] {
            let invocation = certification_invocation(
                &pinned,
                "fixture-version",
                profile,
                config.certificate_solver_limit_seconds,
            )
            .unwrap();
            let arguments = invocation
                .arguments()
                .iter()
                .map(AsRef::as_ref)
                .collect::<Vec<&str>>();
            assert!(
                arguments
                    .windows(2)
                    .any(|pair| pair == ["--time_limit", "17"])
            );
            assert!(
                !arguments
                    .windows(2)
                    .any(|pair| pair == ["--time_limit", "60"])
            );
        }
        let controls = campaign_controls(&config);
        assert_eq!(controls["certificate_solver_limit_seconds"], 17);
        assert_eq!(controls["consultation_limit_seconds"], 0.125);
        assert_eq!(controls["transport_retries"], 2);
        assert_eq!(controls["certification_limit_seconds"], 600.0);
        assert!(
            campaign_controls(&parse(&["--no-proposer", "--input", "1"]))["consultation_limit_seconds"].is_null()
        );
    }

    /// The launch allowances a run applies are recorded with it. They are
    /// a search setting like any other — two runs whose keys get 30/90/240
    /// seconds and 5/12.5 seconds are not comparable — and the default is
    /// recorded as the list it is rather than left to be inferred.
    #[test]
    fn the_effective_retry_ladder_is_recorded_whether_or_not_a_flag_named_it() {
        assert_eq!(
            retry_ladder_seconds(&parse(&["--no-proposer", "--input", "1"])),
            [30.0, 90.0, 240.0]
        );
        assert_eq!(
            retry_ladder_seconds(&parse(&[
                "--no-proposer",
                "--input",
                "1",
                "--retry-allowance",
                "5",
                "--retry-allowance",
                "12.5",
            ])),
            [5.0, 12.5]
        );
        let controls = campaign_controls(&parse(&["--no-proposer", "--input", "1"]));
        assert_eq!(
            controls["retry_allowance_seconds"],
            json!([30.0, 90.0, 240.0])
        );
    }

    /// The premise role a retry launch renders under is a search setting,
    /// so it is recorded like the ladder and the portfolio policy, and the
    /// ablation value stays reachable.
    #[test]
    fn the_retry_premise_role_is_recorded_and_its_ablation_is_reachable() {
        let default = parse(&["--no-proposer", "--input", "1"]);
        assert_eq!(default.retry_premise_role, PremiseRole::NegatedConjecture);
        assert_eq!(
            campaign_controls(&default)["premise_role_retries"],
            "negated_conjecture"
        );
        let ablation = parse(&[
            "--no-proposer",
            "--input",
            "1",
            "--retry-premise-role",
            "axiom",
        ]);
        assert_eq!(ablation.retry_premise_role, PremiseRole::Axiom);
        assert_eq!(
            campaign_controls(&ablation)["premise_role_retries"],
            "axiom"
        );
    }

    /// The portfolio policy and both shares reach the launch command and
    /// the recorded settings, and `--casc-portfolio off` reproduces a
    /// direct-only run's command exactly.
    #[test]
    fn the_casc_portfolio_reaches_the_launch_command_and_the_recorded_controls() {
        let executable = PathBuf::from("/fixture/vampire");

        let default = parse(&["--no-proposer", "--input", "1"]);
        let command = campaign_launch_command(&default, &executable).unwrap();
        assert_eq!(
            command.proof_casc_policy(),
            crate::vampire::ProofCascPolicy::CLI_DEFAULT
        );
        let controls = campaign_controls(&default);
        assert_eq!(controls["casc_portfolio"], "enabled");
        assert_eq!(controls["proof_casc_share"], "0.25");
        assert_eq!(controls["proof_casc_retry_share"], "0.75");

        let off = parse(&["--no-proposer", "--input", "1", "--casc-portfolio", "off"]);
        let command = campaign_launch_command(&off, &executable).unwrap();
        assert!(
            command.proof_casc_policy().is_disabled(),
            "a disabled run launches the same command a CASC-free run always did"
        );
        let untouched = VampireWorkerCommand::new(&executable);
        assert_eq!(command.executable(), untouched.executable());
        assert_eq!(
            command.proof_casc_policy(),
            untouched.proof_casc_policy(),
            "`off` is today's command, not a variant of it"
        );
        let controls = campaign_controls(&off);
        assert_eq!(controls["casc_portfolio"], "disabled");
        assert_eq!(controls["proof_casc_share"], "0");
        assert_eq!(controls["proof_casc_retry_share"], "0");

        let tuned = parse(&[
            "--no-proposer",
            "--input",
            "1",
            "--proof-casc-share",
            "0.4",
            "--proof-casc-retry-share",
            "0.9",
        ]);
        let controls = campaign_controls(&tuned);
        assert_eq!(controls["proof_casc_share"], "0.4");
        assert_eq!(controls["proof_casc_retry_share"], "0.9");
        assert_eq!(
            campaign_launch_command(&tuned, &executable)
                .unwrap()
                .proof_casc_policy()
                .initial_share()
                .to_string(),
            "0.4"
        );
    }
}

#[cfg(test)]
mod resource_tests {
    use super::*;

    #[test]
    fn startup_cleanup_priority_does_not_erase_a_concurrent_resource_failure() {
        use crate::proposer_api::wire::ProposerCleanupError;
        for (cause, resource) in [
            (GenericProcessStartupError::ResourceExhausted, true),
            (
                GenericProcessStartupError::ResourceExhaustedCleanupFailed(
                    ProposerCleanupError::TimedOut,
                ),
                true,
            ),
            (
                GenericProcessStartupError::CleanupFailed(ProposerCleanupError::TimedOut),
                false,
            ),
            (GenericProcessStartupError::Cancelled, false),
        ] {
            let error = std::io::Error::other(cause);
            let mut resources = InputApiResources::default();
            resources.record_startup_error(&error);
            assert_eq!(resources.failure().is_some(), resource);
            assert_eq!(startup_error(&error), Some(&cause));
            if let GenericProcessStartupError::ResourceExhaustedCleanupFailed(_) = cause {
                assert!(startup_failure_status(&error, Some(PhaseStop::DeadlineExpired)).is_none());
                assert_ne!(
                    startup_error(&error),
                    Some(&GenericProcessStartupError::ResourceExhausted)
                );
                assert!(error.to_string().starts_with("proposer startup cleanup:"));
            }
        }
    }

    #[test]
    fn api_resource_projection_preserves_source_and_cleanup_failure_classification() {
        use crate::failure::{FailureKind, FailureOrigin, FailureReport, FailureScope};
        for (origin, kind, scope, budget, expected) in [
            (
                FailureOrigin::AgentConsultation,
                FailureKind::SourceExhausted,
                FailureScope::RunGlobal,
                Some("API allowance"),
                "resource_exhausted",
            ),
            (
                FailureOrigin::AgentConsultation,
                FailureKind::SourceExhausted,
                FailureScope::LaneLocal,
                Some("API allowance"),
                "incomplete",
            ),
            (
                FailureOrigin::AgentConsultation,
                FailureKind::SourceExhausted,
                FailureScope::RunGlobal,
                None,
                "incomplete",
            ),
            (
                FailureOrigin::RunControl,
                FailureKind::InfrastructureFailure,
                FailureScope::RunGlobal,
                Some("API allowance"),
                "incomplete",
            ),
            (
                FailureOrigin::RunControl,
                FailureKind::IterationLimitExhausted,
                FailureScope::RunGlobal,
                None,
                "incomplete",
            ),
        ] {
            let report = FailureReport::try_new(
                origin,
                kind,
                false,
                scope,
                Some("original failure".into()),
                Vec::new(),
            )
            .unwrap();
            let value = search_failure_record("Example0001", &report, budget);
            assert_eq!(value["status"], expected);
            if expected == "resource_exhausted" {
                assert_eq!(value["detail"], budget.unwrap());
                assert!(value["failure_kind"].is_null());
            } else {
                assert_eq!(value["detail"], "original failure");
                assert_eq!(value["failure_kind"], format!("{kind:?}"));
            }
        }
    }

    #[test]
    fn campaign_staging_is_exclusive_and_does_not_follow_symlinks() {
        let root = std::env::temp_dir().join(format!(
            "whiel-campaign-staging-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir(&root).unwrap();
        let owned = root.join("input");
        std::fs::create_dir(&owned).unwrap();
        let staging = reserve_campaign_staging(&owned).unwrap();
        assert_eq!(staging, owned.join("staging"));
        assert!(std::fs::symlink_metadata(&staging).unwrap().is_dir());
        std::fs::write(staging.join("keep"), "owned").unwrap();
        assert_eq!(
            reserve_campaign_staging(&owned).unwrap_err().kind(),
            std::io::ErrorKind::AlreadyExists
        );
        assert_eq!(
            std::fs::read_to_string(staging.join("keep")).unwrap(),
            "owned"
        );

        let outside = root.join("outside");
        std::fs::create_dir(&outside).unwrap();
        let linked_input = root.join("linked-input");
        std::os::unix::fs::symlink(&outside, &linked_input).unwrap();
        assert_eq!(
            reserve_campaign_staging(&linked_input).unwrap_err().kind(),
            std::io::ErrorKind::InvalidInput
        );
        assert!(!outside.join("staging").exists());
        for label in ["existing-file", "existing-link"] {
            let input = root.join(label);
            std::fs::create_dir(&input).unwrap();
            let entry = input.join("staging");
            if label == "existing-file" {
                std::fs::write(&entry, "keep").unwrap();
            } else {
                std::os::unix::fs::symlink(&outside, &entry).unwrap();
            }
            assert_eq!(
                reserve_campaign_staging(&input).unwrap_err().kind(),
                std::io::ErrorKind::AlreadyExists
            );
        }
        assert_eq!(std::fs::read_dir(&outside).unwrap().count(), 0);
        std::fs::remove_dir_all(root).unwrap();
    }

    #[tokio::test]
    async fn generic_transport_workspace_is_sampled_and_retained_until_guard_finishes() {
        for (oversized_at_registration, cancelled_scan, shutdown_budget) in [
            (false, false, false),
            (true, false, false),
            (false, true, false),
            (false, true, true),
        ] {
            let directory = PathBuf::from("/tmp").join(format!(
                "whiel-campaign-root-{}-{}",
                std::process::id(),
                SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .unwrap()
                    .as_nanos()
            ));
            let campaign = directory.join("campaign");
            std::fs::create_dir_all(&campaign).unwrap();
            let log = directory.join("endpoint.jsonl");
            let python = std::process::Command::new("python3")
                .args(["-c", "import sys; print(sys.executable)"])
                .output()
                .unwrap();
            assert!(python.status.success());
            let mut configuration = GenericProcessConfig::new(
                PathBuf::from(String::from_utf8(python.stdout).unwrap().trim()),
                vec![
                    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                        .join("src/proposer_host/fixtures/generic_endpoint.py")
                        .into_os_string(),
                    "no_response".into(),
                    log.clone().into_os_string(),
                ],
            );
            configuration.startup_timeout = Duration::from_secs(3);
            configuration.shutdown_timeout = Duration::from_secs(1);
            if shutdown_budget {
                configuration.traffic_limits.messages = 2;
            }
            let cancellation = CancellationToken::new();
            let mut endpoint = GenericProcessProposer::start(configuration, &[], &cancellation)
                .await
                .unwrap();
            let scratch = endpoint.scratch_directory().to_path_buf();
            let payload = scratch.join("transport-spool");
            let limits = crate::framework2::resource_limits::CampaignResourceLimits {
                minimum_free_bytes: 1,
                workspace_bytes: 64,
                ..Default::default()
            };
            let space = SpaceGuard::new(&limits, campaign, CancellationToken::new());
            let mut leases = Vec::new();
            if oversized_at_registration {
                std::fs::write(&payload, [b'x'; 65]).unwrap();
            }
            if cancelled_scan {
                cancellation.cancel();
            }
            let registered =
                register_endpoint_workspace(&mut endpoint, &space, &mut leases, &cancellation)
                    .await;
            assert_eq!(leases.len(), 1);
            if oversized_at_registration || cancelled_scan {
                let error = registered.unwrap_err();
                if cancelled_scan {
                    assert!(space.failure().is_none());
                    let expected = if shutdown_budget {
                        GenericProcessStartupError::ResourceExhausted
                    } else {
                        GenericProcessStartupError::Cancelled
                    };
                    assert_eq!(startup_error(&error), Some(&expected));
                } else {
                    assert!(error.to_string().contains("resource_exhausted"));
                }
                // Registration failure must join protocol shutdown or resource
                // fallback before returning; the lease still retains the root.
                assert_eq!(
                    std::fs::read_to_string(&log).unwrap().lines().any(|line| {
                        serde_json::from_str::<Value>(line).unwrap()["kind"] == "shutdown"
                    }),
                    !shutdown_budget
                );
                drop(endpoint);
                assert!(scratch.is_dir());
            } else {
                registered.unwrap();
                endpoint
                    .shutdown(crate::proposer_api::wire::ShutdownReason::Failure)
                    .await
                    .unwrap();
                drop(endpoint);
                assert!(scratch.is_dir());
                space.checkpoint().await.unwrap();
                // This root is outside the campaign output; only explicit
                // transport-root registration makes its bytes count.
                std::fs::write(&payload, [b'x'; 65]).unwrap();
                assert!(
                    space
                        .checkpoint()
                        .await
                        .unwrap_err()
                        .contains("resource_exhausted")
                );
            }
            drop(leases);
            assert!(!scratch.exists());
            std::fs::remove_dir_all(directory).unwrap();
        }
    }
    #[tokio::test]
    async fn workspace_exhaustion_stops_input_admission_and_is_not_an_interrupt() {
        let directory = std::env::temp_dir().join(format!(
            "whiel-campaign-space-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir(&directory).unwrap();
        std::fs::write(directory.join("occupied"), b"xx").unwrap();
        let mut config = crate::campaign_cli::parse_campaign_run_arguments(&[
            "--no-proposer".into(),
            "--input".into(),
            "Example0001,Example0002".into(),
        ])
        .unwrap();
        config.resource_limits.workspace_bytes = 1;
        config.resource_limits.minimum_free_bytes = 1;
        let cancellation = CancellationToken::new();
        let guard = SpaceGuard::new(
            &config.resource_limits,
            directory.clone(),
            cancellation.clone(),
        );
        let mut output = Vec::new();
        let code = run_selected(
            &config,
            &directory,
            &directory,
            config.inputs.clone(),
            &cancellation,
            &guard,
            &mut Vec::new(),
            &mut output,
        )
        .await
        .unwrap();
        assert_eq!(code, 3);
        assert!(!directory.join("Example0001").exists());
        assert!(!directory.join("Example0002").exists());
        let summary: Value =
            serde_json::from_slice(&std::fs::read(directory.join("summary.json")).unwrap())
                .unwrap();
        assert_eq!(summary["interrupted"], false);
        assert_eq!(summary["all_certified"], false);
        assert_eq!(
            summary["unrun_inputs"],
            json!(["Example0001", "Example0002"])
        );
        assert!(
            summary["resource_failure"]
                .as_str()
                .unwrap()
                .contains("resource_exhausted")
        );
        std::fs::remove_dir_all(directory).unwrap();
    }
}

#[cfg(test)]
mod startup_classification_tests {
    use super::*;
    use std::io::{Error, ErrorKind};

    #[test]
    fn elapsed_deadline_does_not_mask_protocol_setup_or_cleanup_failure() {
        for failure in [
            Error::new(ErrorKind::InvalidData, "invalid hello"),
            Error::new(ErrorKind::Interrupted, "unrelated IO interruption"),
            Error::new(ErrorKind::TimedOut, GenericProcessStartupError::TimedOut),
            Error::other(GenericProcessStartupError::CleanupFailed(
                crate::proposer_api::ProposerCleanupError::TimedOut,
            )),
        ] {
            for stop in [
                None,
                Some(PhaseStop::DeadlineExpired),
                Some(PhaseStop::Interrupted),
            ] {
                assert_eq!(startup_failure_status(&failure, stop), None);
            }
        }
        assert_eq!(
            startup_failure_status(&Error::other(GenericProcessStartupError::Cancelled), None,),
            None,
        );
    }

    #[tokio::test]
    async fn cancelled_startup_uses_the_joined_phase_stop_reason() {
        for interrupted in [false, true] {
            let external = CancellationToken::new();
            let phase = PhaseCancellation::new(&external).unwrap();
            assert!(
                phase.token().bind_absolute_deadline(
                    tokio::time::Instant::now() + Duration::from_millis(20)
                )
            );
            if interrupted {
                external.cancel();
            }
            tokio::time::timeout(Duration::from_secs(1), phase.token().cancelled())
                .await
                .unwrap();
            let completion = phase.finish().await.unwrap();
            let classified = startup_failure_status(
                &Error::other(GenericProcessStartupError::Cancelled),
                completion.stop,
            );
            assert_eq!(
                classified,
                Some(if interrupted {
                    ("interrupted", crate::failure::FailureKind::Interrupted)
                } else {
                    (
                        "search_timeout",
                        crate::failure::FailureKind::OverallTimeout,
                    )
                })
            );
        }
    }
}
