//! Current Benchmark campaign command and policy parsing.

use crate::framework2::resource_limits::CampaignResourceLimits;
use std::collections::BTreeSet;
use std::num::NonZeroUsize;
use std::path::PathBuf;
use std::time::Duration;

use crate::artifact::Retention;
use crate::entailment::PremiseRole;
use crate::framework2::{
    AgentConsultationLimits, AgentConsultationPolicy, AgentTool, AgentToolPolicy,
    CascPortfolioPolicy, DEFAULT_COUNTEREXAMPLE_VALIDATION_LIMIT, FrameworkIIRetryPolicy,
    HostLimits, PreCertificateAgentHoudiniLimits,
};
use crate::vampire::{ProofCascPolicy, ProofCascShare};

pub const CAMPAIGN_ARGUMENT_FAILURE: i32 = 2;
pub const CAMPAIGN_FAILED: i32 = 3;
/// Every selected input was accepted, and none of them was certified.
///
/// Its own code, distinct from success and from failure: a script that reads
/// 0 as "certified" must not read an uncertified run as certified, and a
/// script that reads 3 as "something went wrong" must not read a deliberate
/// two-step run as a failure.
pub const CAMPAIGN_UNCERTIFIED: i32 = 4;

#[path = "campaign_budgets.rs"]
mod budgets;
#[path = "campaign_certify.rs"]
mod certify_phase;
#[path = "campaign_run.rs"]
mod runtime;
pub use budgets::{
    CAMPAIGN_CHECK_LANES, CAMPAIGN_FINITE_MODEL_LANE, CampaignBudgets, host_memory_bytes,
    host_parallelism,
};
pub use certify_phase::{
    CAMPAIGN_CERTIFY_USAGE, CampaignCertifyConfig, default_jobs, execute_campaign_certify_cli,
    parse_campaign_certify_arguments,
};
pub use runtime::{CampaignRunError, SEARCH_SECONDS, discover_inputs, execute_campaign_run_cli};

pub const CAMPAIGN_USAGE: &str = "\
Usage:
  whiel-symbolic campaign run (--input ID[,ID...] | --all)
    (--proposer-executable PATH | --no-proposer) [OPTIONS]

Inputs are discovered from the current Benchmark/*/Input.lean inventory.
Each input gets a fresh run directory and independently checked Certificate tree.

  --repo PATH                Repository root (default: current directory)
  --input ID[,ID...]         Single input or subset; may repeat; 1/0001 selects Example0001
  --all                      Every current immediate Benchmark input
  --destination DIR          Fresh campaign output root (default: artifacts/campaigns/<fresh-id>)
  --proposer-executable PATH Generic wire-3 proposer executable; relative paths use --repo
  --proposer-arg VALUE       One opaque argument; may repeat, including --help or an empty value
                            No shell splitting; endpoint starts in a private working directory
  --no-proposer              Generic exhausted-source diagnostic; no proposer process
  --api-traffic-bytes N      API transport bytes per input (default: 1073741824)
  --api-messages N           API transport messages per input (default: 16384)

  --worker PATH             Existing fixed-ambient worker; otherwise build under watchdog;
                            certificate Lean prerequisites are prepared in either case
  --workers N               Clause checks run at once; every other concurrency
                            budget is derived from it and recorded with the run.
                            Default: floor(logical cores / 2), at least 1 and at
                            most 4. An explicit value is always honoured; either
                            a default or an explicit value that exceeds the
                            memory estimate, or whose checks x lanes exceeds the
                            logical core count, is honoured with a warning. Each
                            check races a proof lane against a finite-model
                            lane, so lanes is 2
  --search-limit SECONDS     Search allowance per input (default: 600); excludes admission
  --certification-limit SECONDS
                            Independent certification allowance per input (default: 600)
  --consultation-limit SECONDS
                            Optional whole-consultation allowance, including corrections/retries
  --transport-retries N     Additional provider attempts per request (0..8; default: 0)
  --certificate-solver-limit SECONDS
                            Positive whole seconds per Valid Leancheck job (default: 60)
  --iteration-limit N       Optional positive consultation count guard
  --counterexample-validation-limit SECONDS
                            Call-local validation allowance (default: 30)
  --retry-allowance SECONDS  Repeatable increasing solver allowances; default production ladder
  --retry-premise-role axiom|negated_conjecture
                            The TPTP role a retry launch writes its premises under
                            (default: negated_conjecture). A first launch always writes
                            them as axioms
  --casc-portfolio on|off   Whether a proof-lane launch may escalate into the casc_2025
                            portfolio (default: on). `off` runs every allowance direct
  --proof-casc-share FRACTION
                            The portfolio's share of a launch's initial proof allowance
                            (default: 0.25); a decimal in [0,1] with at most six digits
  --proof-casc-retry-share FRACTION
                            The portfolio's share of retry-added time (default: 0.75)
  --tools name,name,...     Optional countermodel,strongest_refutations,history,ledger,
                            validate_clauses,evaluate_clauses tools (default: all)
  --no-tools                Disable optional tools; submit remains available
  --artifact-bytes N        (default: 4294967296 staged bytes per input)
  --artifact-files N        (default: 50000 payload file creations per input)
  --workspace-bytes N       (default: 8589934592 live bytes per campaign;
                            68719476736 under --retention all with no
                            explicit --workspace-* flag)
  --workspace-files N       (default: 100000 live regular files per campaign;
                            1000000 under --retention all with no
                            explicit --workspace-* flag)
  --minimum-free-bytes N    (default: 2147483648 per involved filesystem)
  --workspace-entries N     (default: 200000 visited entries per scan;
                            2000000 under --retention all with no
                            explicit --workspace-* flag)
  --workspace-directories N (default: 25000 directories per scan;
                            250000 under --retention all with no
                            explicit --workspace-* flag)
  --retention certificate-only|all (default: certificate-only)
  --certify inline|deferred|never (default: inline)
                            inline certifies each input right after its own search;
                            deferred searches every input first and certifies them in
                            one final phase; never stops at acceptance and leaves the
                            run directory for `campaign certify --run DIR`

Optional host limits (absent by default): --catalog-size, --clause-text-bytes,
--countermodel-retention-tuples, --drop-references, --evaluation-cost, --level-bound,
--proposal-size, --pushed-core, --reply-bytes, --strongest-refutations (each takes N).
Generic B has no agent session policy.

Outputs: <root>/<ID>/result.json, the acceptance records Accepted.json and Core.json or
Counterexample.json written the moment the untrusted verifier accepts, and, only after
checked publication, Certificate/.
Exit codes: 0 every input certified; 2 arguments/bootstrap failure; 3 incomplete or
failed input; 4 every selected input accepted and the uncertified ones still awaiting
certification; 130 interrupted.
Legacy inputs and unknown options are refused.
  -h, --help                Print this help
";

/// When, if ever, `campaign run` certifies what its search accepted.
///
/// Certification is deterministic, consults no proposer, and costs minutes
/// and gigabytes per input. Separating it from the search lets a supervised
/// or paid-for campaign end when the search ends, and lets the certifier be
/// rerun later from the records the search left.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum CertifyMode {
    /// Certify each input immediately after its own search, in process.
    #[default]
    Inline,
    /// Search every input first, then certify them all in one final phase.
    Deferred,
    /// Stop at acceptance. `campaign certify --run DIR` finishes the job,
    /// possibly later and on another machine.
    Never,
}

impl CertifyMode {
    pub fn name(self) -> &'static str {
        match self {
            Self::Inline => "inline",
            Self::Deferred => "deferred",
            Self::Never => "never",
        }
    }

    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "inline" => Some(Self::Inline),
            "deferred" => Some(Self::Deferred),
            "never" => Some(Self::Never),
            _ => None,
        }
    }

    /// Whether an input's own search is followed by its certification.
    pub fn certifies_inline(self) -> bool {
        matches!(self, Self::Inline)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CampaignProvider {
    Generic,
    None,
}

/// Opaque caller-selected launch metadata, never authenticated agent provenance.
///
/// [`executable`](Self::executable) is what B starts, so it is resolved
/// against `--repo` and canonicalized. [`recorded`](Self::recorded) is what
/// the run's own files say instead: a run directory is meant to be copied to
/// another machine and certified there, so its records name a path inside the
/// repository relative to the repository root and leave everything else
/// exactly as the caller wrote it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EndpointSelection {
    pub executable: PathBuf,
    pub arguments: Vec<String>,
    pub recorded: RecordedEndpoint,
}

/// The portable spelling of one endpoint selection.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct RecordedEndpoint {
    pub executable: String,
    pub arguments: Vec<String>,
}

#[derive(Clone, Debug)]
pub struct CampaignRunConfig {
    pub inputs: Vec<String>,
    pub all_inputs: bool,
    pub repository: PathBuf,
    pub destination: Option<PathBuf>,
    pub worker: Option<PathBuf>,
    /// Every concurrency budget of the run, derived from `--workers`.
    pub budgets: CampaignBudgets,
    pub provider: CampaignProvider,
    pub proposer: Option<EndpointSelection>,
    pub consultation_policy: AgentConsultationPolicy,
    pub host_limits: HostLimits,
    pub tool_policy: AgentToolPolicy,
    pub retention: Retention,
    pub resource_limits: CampaignResourceLimits,
    pub search_limits: PreCertificateAgentHoudiniLimits,
    pub certification_limit: Duration,
    pub certificate_solver_limit_seconds: u64,
    // None preserves the production authority's baseline and retry ladder.
    pub retry_policy_override: Option<FrameworkIIRetryPolicy>,
    /// The TPTP role a retry launch writes this run's premises under. The
    /// first launch of a check always writes them as axioms, so `Axiom`
    /// here is the pre-`--retry-premise-role` behaviour throughout.
    pub retry_premise_role: PremiseRole,
    pub casc_portfolio: CascPortfolioPolicy,
    /// How a launch's proof allowance is divided between the direct
    /// strategy and the `casc_2025` portfolio. A run whose
    /// [`Self::casc_portfolio`] is disabled carries
    /// [`ProofCascPolicy::DISABLED`] here, so the settings it records state
    /// the split it actually performed rather than one it never reached.
    pub proof_casc_policy: ProofCascPolicy,
    /// When this run certifies what it accepts.
    pub certify: CertifyMode,
}

impl CampaignRunConfig {
    pub fn resolve_retry_policy(
        &self,
        authority: &FrameworkIIRetryPolicy,
    ) -> FrameworkIIRetryPolicy {
        self.retry_policy_override
            .as_ref()
            .unwrap_or(authority)
            .clone()
            .with_casc_portfolio(self.casc_portfolio)
    }
}

pub fn parse_campaign_run_arguments(arguments: &[String]) -> Result<CampaignRunConfig, String> {
    let mut inputs = Vec::new();
    let mut all_inputs = false;
    let mut repository = PathBuf::from(".");
    let mut destination = None;
    let mut worker = None;
    let mut workers = None;
    let mut proposer_executable = None;
    let mut proposer_arguments = Vec::new();
    let mut host_limits = HostLimits::UNBOUNDED;
    let mut tool_policy = AgentToolPolicy::all_enabled();
    let mut retention = Retention::CertificateOnly;
    let mut resource_limits = CampaignResourceLimits::default();
    let mut search_limit = Duration::from_secs(600);
    let mut certification_limit = Duration::from_secs(600);
    let mut certificate_solver_limit_seconds = 60;
    let mut consultation_limit = None;
    let mut consultation_limits = AgentConsultationLimits::default();
    let mut validation_limit = DEFAULT_COUNTEREXAMPLE_VALIDATION_LIMIT;
    let mut iteration_limit = None;
    let mut retry_allowances = Vec::new();
    let mut retry_premise_role = PremiseRole::NegatedConjecture;
    let mut certify = CertifyMode::default();
    let mut casc_portfolio = CascPortfolioPolicy::Enabled;
    let mut casc_initial_share = None;
    let mut casc_retry_share = None;
    let mut seen = BTreeSet::new();
    let mut index = 0;
    while index < arguments.len() {
        let option = arguments[index].as_str();
        if let Some(argument) = option.strip_prefix("--proposer-arg=") {
            if argument.contains('\0') {
                return Err("proposer arguments must not contain NUL".into());
            }
            proposer_arguments.push(argument.to_owned());
            index += 1;
            continue;
        }
        if !matches!(option, "--retry-allowance" | "--input" | "--proposer-arg")
            && !seen.insert(option)
        {
            return Err(format!("{option} may be supplied only once"));
        }
        match option {
            "--input" => inputs.extend(
                value(arguments, &mut index, option)?
                    .split(',')
                    .map(|input| input.trim().to_owned()),
            ),
            "--all" => all_inputs = true,
            "--proposer-executable" => {
                let executable = value(arguments, &mut index, option)?;
                if executable.is_empty() || executable.contains('\0') {
                    return Err("--proposer-executable requires a nonempty path without NUL".into());
                }
                proposer_executable = Some(PathBuf::from(executable));
            }
            "--proposer-arg" => {
                // The next token is C's argument, even when it begins with '-'.
                index += 1;
                let argument = arguments
                    .get(index)
                    .ok_or("--proposer-arg requires a value")?;
                if argument.contains('\0') {
                    return Err("proposer arguments must not contain NUL".into());
                }
                proposer_arguments.push(argument.to_owned());
            }
            "--no-proposer" => {}
            "--repo" => repository = value(arguments, &mut index, option)?.into(),
            "--destination" => {
                destination = Some(PathBuf::from(value(arguments, &mut index, option)?))
            }
            "--worker" => worker = Some(PathBuf::from(value(arguments, &mut index, option)?)),
            "--workers" => {
                let count = integer(value(arguments, &mut index, option)?, option)?;
                workers = Some(
                    usize::try_from(count)
                        .ok()
                        .and_then(NonZeroUsize::new)
                        .ok_or_else(|| {
                            "--workers requires a positive host-sized integer".to_owned()
                        })?,
                );
            }
            "--compress-core" => {
                return Err("--compress-core is unsupported for this campaign command".into());
            }
            "--casc-portfolio" => {
                casc_portfolio = match value(arguments, &mut index, option)? {
                    "on" => CascPortfolioPolicy::Enabled,
                    "off" => CascPortfolioPolicy::Disabled,
                    _ => return Err("--casc-portfolio requires on or off".into()),
                };
            }
            "--proof-casc-share" => {
                casc_initial_share = Some(share(value(arguments, &mut index, option)?)?);
            }
            "--proof-casc-retry-share" => {
                casc_retry_share = Some(share(value(arguments, &mut index, option)?)?);
            }
            "--api-traffic-bytes"
            | "--api-messages"
            | "--artifact-bytes"
            | "--artifact-files"
            | "--workspace-bytes"
            | "--workspace-files"
            | "--minimum-free-bytes"
            | "--workspace-entries"
            | "--workspace-directories" => {
                let amount = integer(value(arguments, &mut index, option)?, option)?;
                if amount == 0 {
                    return Err(format!("{option} requires a positive integer"));
                }
                match option {
                    "--api-traffic-bytes" => resource_limits.api_traffic_bytes = amount,
                    "--api-messages" => resource_limits.api_messages = amount,
                    "--artifact-bytes" => resource_limits.artifact_bytes = amount,
                    "--artifact-files" => resource_limits.artifact_files = amount,
                    "--workspace-bytes" => resource_limits.workspace_bytes = amount,
                    "--workspace-files" => resource_limits.workspace_files = amount,
                    "--minimum-free-bytes" => resource_limits.minimum_free_bytes = amount,
                    "--workspace-entries" => resource_limits.workspace_entries = amount,
                    "--workspace-directories" => resource_limits.workspace_directories = amount,
                    _ => unreachable!(),
                }
            }
            "--certify" => {
                certify = CertifyMode::parse(value(arguments, &mut index, option)?)
                    .ok_or("--certify requires inline, deferred or never")?;
            }
            "--retention" => {
                retention = match value(arguments, &mut index, option)? {
                    "all" => Retention::All,
                    "certificate-only" => Retention::CertificateOnly,
                    _ => return Err("--retention requires all or certificate-only".into()),
                };
            }
            "--tools" => {
                if seen.contains("--no-tools") {
                    return Err("--tools and --no-tools are mutually exclusive".into());
                }
                let mut tools = BTreeSet::new();
                for name in value(arguments, &mut index, option)?.split(',') {
                    let tool = AgentTool::from_name(name).ok_or_else(|| {
                        "--tools requires exact optional tool names; submit is always available"
                            .to_owned()
                    })?;
                    if !tools.insert(tool) {
                        return Err("--tools must not repeat a tool".into());
                    }
                }
                tool_policy = AgentToolPolicy::new(tools);
            }
            "--no-tools" => {
                if seen.contains("--tools") {
                    return Err("--tools and --no-tools are mutually exclusive".into());
                }
                tool_policy = AgentToolPolicy::none_enabled();
            }
            "--retry-allowance" => {
                retry_allowances.push(seconds(value(arguments, &mut index, option)?, option)?)
            }
            "--retry-premise-role" => {
                retry_premise_role = PremiseRole::from_name(value(arguments, &mut index, option)?)
                    .ok_or("--retry-premise-role requires axiom or negated_conjecture")?;
            }
            "--search-limit" => {
                search_limit = seconds(value(arguments, &mut index, option)?, option)?
            }
            "--certification-limit" => {
                certification_limit = seconds(value(arguments, &mut index, option)?, option)?
            }
            "--consultation-limit" => {
                consultation_limit = Some(seconds(value(arguments, &mut index, option)?, option)?)
            }
            "--transport-retries" => {
                consultation_limits.max_transport_retries_per_request =
                    usize::try_from(integer(value(arguments, &mut index, option)?, option)?)
                        .map_err(|_| "--transport-retries exceeds the host integer range")?;
            }
            "--certificate-solver-limit" => {
                certificate_solver_limit_seconds =
                    integer(value(arguments, &mut index, option)?, option)?;
                if certificate_solver_limit_seconds == 0 {
                    return Err("--certificate-solver-limit requires positive whole seconds".into());
                }
            }
            "--counterexample-validation-limit" => {
                validation_limit = seconds(value(arguments, &mut index, option)?, option)?
            }
            "--iteration-limit" => {
                let count = integer(value(arguments, &mut index, option)?, option)?;
                if count == 0 {
                    return Err("--iteration-limit requires a positive integer".into());
                }
                iteration_limit = Some(count);
            }
            "--catalog-size" => {
                host_limits.catalog_size =
                    Some(integer(value(arguments, &mut index, option)?, option)?)
            }
            "--clause-text-bytes" => {
                host_limits.clause_text_bytes =
                    Some(integer(value(arguments, &mut index, option)?, option)?)
            }
            "--countermodel-retention-tuples" => {
                host_limits.countermodel_retention_tuples =
                    Some(integer(value(arguments, &mut index, option)?, option)?)
            }
            "--drop-references" => {
                host_limits.drop_references =
                    Some(integer(value(arguments, &mut index, option)?, option)?)
            }
            "--evaluation-cost" => {
                host_limits.evaluation_cost =
                    Some(integer(value(arguments, &mut index, option)?, option)?)
            }
            "--level-bound" => {
                host_limits.level_bound =
                    Some(integer(value(arguments, &mut index, option)?, option)?)
            }
            "--proposal-size" => {
                host_limits.proposal_size =
                    Some(integer(value(arguments, &mut index, option)?, option)?)
            }
            "--pushed-core" => {
                host_limits.pushed_core =
                    Some(integer(value(arguments, &mut index, option)?, option)?)
            }
            "--reply-bytes" => {
                host_limits.reply_bytes =
                    Some(integer(value(arguments, &mut index, option)?, option)?)
            }
            "--strongest-refutations" => {
                host_limits.strongest_refutations =
                    Some(integer(value(arguments, &mut index, option)?, option)?)
            }
            // Avoid reflecting secret-bearing unknown options into stderr.
            _ => return Err("unknown campaign option; see `campaign run --help`".into()),
        }
        index += 1;
    }
    // Under `--retention all`, an omitted `--workspace-*` flag takes the
    // raised default a retained campaign needs instead of the ordinary
    // per-input one; an explicit flag always wins for its own limit.
    if retention == Retention::All {
        if !seen.contains("--workspace-bytes") {
            resource_limits.workspace_bytes =
                crate::framework2::resource_limits::RETAINED_WORKSPACE_BYTES;
        }
        if !seen.contains("--workspace-files") {
            resource_limits.workspace_files =
                crate::framework2::resource_limits::RETAINED_WORKSPACE_FILES;
        }
        if !seen.contains("--workspace-entries") {
            resource_limits.workspace_entries =
                crate::framework2::resource_limits::RETAINED_WORKSPACE_ENTRIES;
        }
        if !seen.contains("--workspace-directories") {
            resource_limits.workspace_directories =
                crate::framework2::resource_limits::RETAINED_WORKSPACE_DIRECTORIES;
        }
    }
    if all_inputs != inputs.is_empty() {
        return Err("select either --all or one or more --input IDs".into());
    }
    let mut unique = BTreeSet::new();
    for input in &inputs {
        if !valid_input_id(input) && !numeric_selector(input) {
            return Err(
                "--input requires safe canonical Benchmark IDs or ASCII example numbers".into(),
            );
        }
        if !unique.insert(input) {
            return Err("--input must not repeat an ID".into());
        }
    }
    if proposer_executable.is_some() && seen.contains("--no-proposer") {
        return Err("--proposer-executable and --no-proposer are mutually exclusive".into());
    }
    if proposer_executable.is_none() && !proposer_arguments.is_empty() {
        return Err("--proposer-arg requires --proposer-executable".into());
    }
    let provider = if proposer_executable.is_some() {
        CampaignProvider::Generic
    } else if seen.contains("--no-proposer") {
        CampaignProvider::None
    } else {
        return Err("select --proposer-executable PATH or --no-proposer".into());
    };
    let proposer = proposer_executable.map(|executable| EndpointSelection {
        recorded: RecordedEndpoint {
            executable: executable.to_string_lossy().into_owned(),
            arguments: proposer_arguments.clone(),
        },
        executable,
        arguments: proposer_arguments,
    });
    let retry_policy_override = if retry_allowances.is_empty() {
        None
    } else {
        Some(FrameworkIIRetryPolicy::new(retry_allowances).map_err(|error| error.to_string())?)
    };
    // A share a disabled run would not apply is refused rather than
    // recorded: a run whose settings state a split it never performed is
    // not comparable with one that performed it.
    if !casc_portfolio.is_enabled() && (casc_initial_share.is_some() || casc_retry_share.is_some())
    {
        return Err(
            "--proof-casc-share and --proof-casc-retry-share require --casc-portfolio on".into(),
        );
    }
    let proof_casc_policy = match (casc_initial_share, casc_retry_share) {
        _ if !casc_portfolio.is_enabled() => ProofCascPolicy::DISABLED,
        (None, None) => ProofCascPolicy::CLI_DEFAULT,
        (Some(initial), None) => ProofCascPolicy::uniform(initial),
        (None, Some(retry)) => ProofCascPolicy::new(ProofCascShare::CLI_DEFAULT, retry)
            .map_err(|error| error.to_string())?,
        (Some(initial), Some(retry)) => {
            ProofCascPolicy::new(initial, retry).map_err(|error| error.to_string())?
        }
    };
    Ok(CampaignRunConfig {
        inputs,
        all_inputs,
        repository,
        destination,
        worker,
        budgets: CampaignBudgets::for_host(workers),
        provider,
        proposer,
        consultation_policy: AgentConsultationPolicy::new(consultation_limits)
            .map_err(|error| error.to_string())?,
        host_limits,
        tool_policy,
        retention,
        resource_limits,
        search_limits: PreCertificateAgentHoudiniLimits::new_with_counterexample_limit(
            search_limit,
            consultation_limit,
            iteration_limit,
            validation_limit,
        ),
        certification_limit,
        certificate_solver_limit_seconds,
        retry_policy_override,
        retry_premise_role,
        casc_portfolio,
        proof_casc_policy,
        certify,
    })
}

/// One `[0,1]` CASC share, in the exact decimal spelling the solver layer
/// stores: at most six fractional digits, so the recorded value is the
/// value applied.
fn share(value: &str) -> Result<ProofCascShare, String> {
    value
        .parse::<ProofCascShare>()
        .map_err(|error| error.to_string())
}

fn value<'a>(arguments: &'a [String], index: &mut usize, option: &str) -> Result<&'a str, String> {
    let value = crate::cli::take_value(arguments, index, option)?;
    if value.starts_with('-') {
        return Err(format!("{option} requires a value"));
    }
    Ok(value)
}

fn integer(value: &str, option: &str) -> Result<u64, String> {
    if !value.bytes().all(|byte| byte.is_ascii_digit()) {
        return Err(format!("{option} requires an unsigned integer"));
    }
    value
        .parse()
        .map_err(|_| format!("{option} requires an unsigned 64-bit integer"))
}

fn seconds(value: &str, option: &str) -> Result<Duration, String> {
    let amount = value
        .parse::<f64>()
        .ok()
        .filter(|amount| amount.is_finite() && *amount > 0.0)
        .ok_or_else(|| format!("{option} requires positive finite seconds"))?;
    let duration = Duration::try_from_secs_f64(amount)
        .map_err(|_| format!("{option} is outside the supported duration range"))?;
    if duration.is_zero() || duration.as_nanos() > u128::from(u64::MAX) {
        return Err(format!(
            "{option} cannot be represented as positive u64 nanoseconds"
        ));
    }
    Ok(duration)
}

pub(crate) fn valid_input_id(input: &str) -> bool {
    input
        .as_bytes()
        .first()
        .is_some_and(u8::is_ascii_alphabetic)
        && input
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
}

pub(crate) fn numeric_selector(input: &str) -> bool {
    !input.is_empty() && input.bytes().all(|byte| byte.is_ascii_digit())
}
