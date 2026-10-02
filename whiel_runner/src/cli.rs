//! Dependency-free command-line contract for the symbolic runner.

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::time::Duration;

use crate::campaign::{CampaignRuntimeConfig, CampaignSelection, default_run_name, run_campaign};
use crate::certification::CertificationBridgeCommand;
use crate::encoding::ProposalRealization;
use crate::reporting::{OutputFormat, Reporter};
use crate::telemetry::TelemetryLevel;
use crate::vampire::{ProofCascPolicy, ProofCascShare, VampireWorkerCommand};

pub const USAGE: &str = "\
Usage:
  whiel-symbolic task ID [OPTIONS]
  whiel-symbolic suite NAME [OPTIONS]
  whiel-symbolic campaign run (--input ID[,ID...] | --all)
    (--proposer-executable PATH | --no-proposer) [OPTIONS]
                              (see `campaign run --help`)
  whiel-symbolic campaign certify --run DIR [OPTIONS]
                              (see `campaign certify --help`)
  whiel-symbolic certificate build --input ID --core ROWS.json --destination DIR [OPTIONS]
                                 (see `certificate_cli::CERTIFICATE_USAGE`)

Options:
  --repo PATH                   Repository root (default: current directory)
  --catalog PATH                Catalog JSON (default: Legacy/Benchmark2/Catalog.json)
  --dispatcher PATH             Compiled Lean dispatcher
  --vampire PATH                Vampire executable (default: VAMPIRE_BIN or vampire)
  --python PATH                 Python used by the certification bridge
  --certification-bridge PATH   Python bridge script (default: module bridge)
  --run-name NAME               Fresh directory name under artifacts/symbolic-houdini
  --task-limit SECONDS          Per-task lane/search deadline (default: 600)
  --campaign-limit SECONDS      Optional campaign search deadline
  --search-limit SECONDS        Initial Vampire search limit (default: 30)
  --proof-casc-share FRACTION   Initial proof-lane CASC share (default: 0.25)
  --proof-casc-retry-share F    CASC share of retry-added time (default: 0.75)
  --encoding-workers COUNT      Persistent Lean workers per task (default: 2)
  --enumerator NAME             seeded, capped, fast, or reference (default: seeded)
  --telemetry LEVEL             off, aggregate, or detailed (default: aggregate)
  --artifact-allowance GB       Cap run artifact output in whole GB (default: unbounded)
  --artifact-file-allowance N   Cap per-task artifact payload files (default: unbounded)
  --progress-interval VALUE     Progress seconds or off (default: 10)
  --format FORMAT               quiet, normal, verbose, or jsonl (default: normal)
  --log-maintenance-history     Enable best-effort cold maintenance history
  --strict-history              Make enabled history failures fatal
  -h, --help                    Print this help
";

#[derive(Clone, Debug)]
pub struct CliConfig {
    pub selection: CampaignSelection,
    pub repository: PathBuf,
    pub catalog: Option<PathBuf>,
    pub dispatcher: Option<PathBuf>,
    pub vampire: Option<PathBuf>,
    pub python: PathBuf,
    pub certification_bridge: Option<PathBuf>,
    pub run_name: String,
    pub per_task_limit: Duration,
    pub campaign_limit: Option<Duration>,
    pub search_limit: Duration,
    pub proof_casc_policy: ProofCascPolicy,
    pub encoding_workers: usize,
    pub proposal_realization: ProposalRealization,
    pub telemetry_level: TelemetryLevel,
    pub artifact_allowance_bytes: Option<u64>,
    pub artifact_file_allowance: Option<u64>,
    pub progress_interval: Option<Duration>,
    pub output_format: OutputFormat,
    pub log_maintenance_history: bool,
    pub fail_on_history_log_error: bool,
}

#[derive(Clone, Debug)]
pub enum CliAction {
    Help,
    /// `certificate build -h`/`--help` (or a bare `certificate` with no
    /// further arguments): print `certificate_cli::CERTIFICATE_USAGE`
    /// specifically, rather than the generic top-level [`USAGE`] the plain
    /// [`Self::Help`] variant prints.
    CertificateHelp,
    CampaignHelp,
    /// `campaign certify -h`/`--help`: this subcommand's own usage.
    CampaignCertifyHelp,
    CampaignRun(Result<Box<crate::campaign_cli::CampaignRunConfig>, String>),
    CampaignCertify(Result<Box<crate::campaign_cli::CampaignCertifyConfig>, String>),
    Run(Box<CliConfig>),
    /// `Err` carries an argument-parsing failure for `certificate build`.
    /// It is threaded through (rather than returned as `parse_cli_args`'s
    /// own `Err`) so the caller can report it with this subcommand's own
    /// exit code (`2`) instead of the generic top-level parse-error code
    /// (`1`) the `task`/`suite` grammar uses.
    CertificateBuild(Result<Box<crate::certificate_cli::CertificateBuildConfig>, String>),
}

pub fn parse_cli_args<I, S>(arguments: I) -> Result<CliAction, String>
where
    I: IntoIterator<Item = S>,
    S: Into<OsString>,
{
    let arguments = arguments
        .into_iter()
        .map(Into::into)
        .map(|value| {
            value
                .into_string()
                .map_err(|_| "command-line arguments must be UTF-8".to_string())
        })
        .collect::<Result<Vec<_>, _>>()?;
    if arguments.is_empty() {
        return Ok(CliAction::Help);
    }
    if arguments[0] == "campaign" {
        let mut proposer_argument = false;
        if arguments.iter().any(|value| {
            if proposer_argument {
                proposer_argument = false;
                return false;
            }
            if value == "--proposer-arg" {
                proposer_argument = true;
                return false;
            }
            value == "-h" || value == "--help"
        }) {
            return Ok(if arguments.get(1).map(String::as_str) == Some("certify") {
                CliAction::CampaignCertifyHelp
            } else {
                CliAction::CampaignHelp
            });
        }
        if arguments.get(1).map(String::as_str) == Some("certify") {
            return Ok(CliAction::CampaignCertify(
                crate::campaign_cli::parse_campaign_certify_arguments(&arguments[2..])
                    .map(Box::new),
            ));
        }
        if arguments.get(1).map(String::as_str) != Some("run") {
            return Ok(CliAction::CampaignRun(Err(
                "expected `campaign run` or `campaign certify`".to_string(),
            )));
        }
        return Ok(CliAction::CampaignRun(
            crate::campaign_cli::parse_campaign_run_arguments(&arguments[2..]).map(Box::new),
        ));
    }
    if arguments[0] == "certificate" {
        if arguments
            .iter()
            .any(|value| value == "-h" || value == "--help")
        {
            return Ok(CliAction::CertificateHelp);
        }
        if arguments.get(1).map(String::as_str) != Some("build") {
            return Ok(CliAction::CertificateBuild(Err(
                "expected `certificate build`".to_string(),
            )));
        }
        let config = crate::certificate_cli::parse_certificate_build_arguments(&arguments[2..])
            .map(Box::new);
        return Ok(CliAction::CertificateBuild(config));
    }
    if arguments
        .iter()
        .any(|value| value == "-h" || value == "--help")
    {
        return Ok(CliAction::Help);
    }
    if arguments.len() < 2 {
        return Err("expected `task ID` or `suite NAME`".to_string());
    }
    let selection = match arguments[0].as_str() {
        "task" => CampaignSelection::Task(arguments[1].clone()),
        "suite" => CampaignSelection::Suite(arguments[1].clone()),
        other => return Err(format!("unknown selection mode {other:?}")),
    };
    if arguments[1].is_empty() || arguments[1].starts_with('-') {
        return Err("task ID or suite name must be nonempty".to_string());
    }
    if arguments[1].len() > 128 {
        return Err("task ID or suite name exceeds 128 bytes".to_string());
    }

    let mut config = CliConfig {
        selection,
        repository: PathBuf::from("."),
        catalog: None,
        dispatcher: None,
        vampire: None,
        python: PathBuf::from("python3"),
        certification_bridge: None,
        run_name: default_run_name(),
        per_task_limit: Duration::from_secs(600),
        campaign_limit: None,
        search_limit: Duration::from_secs(30),
        proof_casc_policy: ProofCascPolicy::CLI_DEFAULT,
        encoding_workers: 2,
        proposal_realization: ProposalRealization::default(),
        telemetry_level: TelemetryLevel::Aggregate,
        artifact_allowance_bytes: None,
        artifact_file_allowance: None,
        progress_interval: Some(Duration::from_secs(10)),
        output_format: OutputFormat::Normal,
        log_maintenance_history: false,
        fail_on_history_log_error: false,
    };
    let mut proof_casc_initial_override = None;
    let mut proof_casc_retry_override = None;
    let mut index = 2;
    while index < arguments.len() {
        let option = arguments[index].as_str();
        match option {
            "--log-maintenance-history" => config.log_maintenance_history = true,
            "--strict-history" => {
                config.log_maintenance_history = true;
                config.fail_on_history_log_error = true;
            }
            "--repo" => {
                config.repository = PathBuf::from(take_value(&arguments, &mut index, option)?)
            }
            "--catalog" => {
                config.catalog = Some(PathBuf::from(take_value(&arguments, &mut index, option)?))
            }
            "--dispatcher" => {
                config.dispatcher = Some(PathBuf::from(take_value(&arguments, &mut index, option)?))
            }
            "--vampire" => {
                config.vampire = Some(PathBuf::from(take_value(&arguments, &mut index, option)?))
            }
            "--python" => {
                config.python = PathBuf::from(take_value(&arguments, &mut index, option)?)
            }
            "--certification-bridge" => {
                config.certification_bridge =
                    Some(PathBuf::from(take_value(&arguments, &mut index, option)?))
            }
            "--run-name" => {
                config.run_name = take_value(&arguments, &mut index, option)?.to_string()
            }
            "--task-limit" => {
                config.per_task_limit =
                    parse_duration(take_value(&arguments, &mut index, option)?, option)?
            }
            "--campaign-limit" => {
                config.campaign_limit = Some(parse_duration(
                    take_value(&arguments, &mut index, option)?,
                    option,
                )?)
            }
            "--search-limit" => {
                config.search_limit =
                    parse_duration(take_value(&arguments, &mut index, option)?, option)?
            }
            "--proof-casc-share" => {
                let value = take_value(&arguments, &mut index, option)?;
                proof_casc_initial_override = Some(
                    value
                        .parse::<ProofCascShare>()
                        .map_err(|error| error.to_string())?,
                );
            }
            "--proof-casc-retry-share" => {
                let value = take_value(&arguments, &mut index, option)?;
                proof_casc_retry_override = Some(
                    value
                        .parse::<ProofCascShare>()
                        .map_err(|error| error.to_string())?,
                );
            }
            "--encoding-workers" => {
                config.encoding_workers = take_value(&arguments, &mut index, option)?
                    .parse::<usize>()
                    .ok()
                    .filter(|value| *value > 0)
                    .ok_or_else(|| "--encoding-workers requires a positive integer".to_string())?;
            }
            "--enumerator" => {
                let value = take_value(&arguments, &mut index, option)?;
                config.proposal_realization = ProposalRealization::parse_cli(value)
                    .ok_or_else(|| format!("unknown enumerator {value:?}"))?;
            }
            "--artifact-allowance" => {
                let value = take_value(&arguments, &mut index, option)?;
                let gigabytes: u64 = value
                    .parse()
                    .map_err(|_| format!("{option} expects whole gigabytes, got {value:?}"))?;
                config.artifact_allowance_bytes = Some(gigabytes * (1 << 30));
            }
            "--artifact-file-allowance" => {
                let value = take_value(&arguments, &mut index, option)?;
                config.artifact_file_allowance = Some(
                    value
                        .parse::<u64>()
                        .ok()
                        .filter(|files| *files > 0)
                        .ok_or_else(|| {
                            format!("{option} expects a positive whole file count, got {value:?}")
                        })?,
                );
            }
            "--telemetry" => {
                config.telemetry_level = match take_value(&arguments, &mut index, option)? {
                    "off" => TelemetryLevel::Off,
                    "aggregate" => TelemetryLevel::Aggregate,
                    "detailed" => TelemetryLevel::Detailed,
                    value => return Err(format!("unknown telemetry level {value:?}")),
                }
            }
            "--progress-interval" => {
                let value = take_value(&arguments, &mut index, option)?;
                config.progress_interval = if value == "off" {
                    None
                } else {
                    Some(parse_duration(value, option)?)
                };
            }
            "--format" => {
                let value = take_value(&arguments, &mut index, option)?;
                config.output_format = OutputFormat::parse(value)
                    .ok_or_else(|| format!("unknown output format {value:?}"))?;
            }
            other => return Err(format!("unknown option {other:?}")),
        }
        index += 1;
    }
    config.proof_casc_policy = match (proof_casc_initial_override, proof_casc_retry_override) {
        (None, None) => ProofCascPolicy::CLI_DEFAULT,
        (Some(initial), None) => ProofCascPolicy::uniform(initial),
        (None, Some(retry)) => ProofCascPolicy::new(ProofCascShare::CLI_DEFAULT, retry)
            .map_err(|error| error.to_string())?,
        (Some(initial), Some(retry)) => {
            ProofCascPolicy::new(initial, retry).map_err(|error| error.to_string())?
        }
    };
    Ok(CliAction::Run(Box::new(config)))
}

impl CliConfig {
    pub fn resolve(self) -> Result<(CampaignRuntimeConfig, OutputFormat), String> {
        let repository = self.repository.canonicalize().map_err(|error| {
            format!(
                "cannot resolve repository {}: {error}",
                self.repository.display()
            )
        })?;
        if !repository.join("Whiel.lean").is_file() {
            return Err(format!(
                "{} does not look like the Whiel repository root",
                repository.display()
            ));
        }
        let catalog = resolve_path(
            &repository,
            self.catalog
                .unwrap_or_else(|| PathBuf::from("Legacy/Benchmark2/Catalog.json")),
        );
        let dispatcher = resolve_path(
            &repository,
            self.dispatcher
                .unwrap_or_else(|| PathBuf::from(".lake/build/bin/benchmark_encoding_worker")),
        );
        let vampire_path = self.vampire.unwrap_or_else(default_vampire_path);
        let vampire = VampireWorkerCommand::new(resolve_program(&repository, vampire_path))
            .with_proof_casc_policy(self.proof_casc_policy)
            .map_err(|error| error.to_string())?;
        let certification_bridge = if let Some(script) = self.certification_bridge {
            CertificationBridgeCommand::new(self.python, &repository)
                .with_arguments([resolve_path(&repository, script).into_os_string()])
        } else {
            CertificationBridgeCommand::new(self.python, &repository)
                .with_arguments(["-m", "whiel_synth.certification_bridge"])
        };
        let output_format = self.output_format;
        Ok((
            CampaignRuntimeConfig {
                repository,
                catalog,
                dispatcher,
                vampire,
                certification_bridge,
                run_name: self.run_name,
                selection: self.selection,
                per_task_limit: self.per_task_limit,
                campaign_limit: self.campaign_limit,
                search_limit: self.search_limit,
                encoding_workers: self.encoding_workers,
                proposal_realization: self.proposal_realization,
                telemetry_level: self.telemetry_level,
                artifact_allowance_bytes: self.artifact_allowance_bytes,
                artifact_file_allowance: self.artifact_file_allowance,
                progress_interval: self.progress_interval,
                output_format,
                log_maintenance_history: self.log_maintenance_history,
                fail_on_history_log_error: self.fail_on_history_log_error,
            },
            output_format,
        ))
    }
}

pub fn execute_cli<W: std::io::Write>(config: CliConfig, writer: W) -> Result<i32, String> {
    let (runtime, output_format) = config.resolve()?;
    let mut reporter = Reporter::new(output_format, writer);
    crate::runtime::interrupt::clear();
    crate::runtime::interrupt::install()
        .map_err(|error| format!("install interrupt handler: {error}"))?;
    let execution = run_campaign(runtime, &mut reporter).map_err(|error| error.to_string())?;
    let incomplete = execution.completed_tasks != execution.selected_tasks
        || execution.timeouts > 0
        || execution.failures > 0
        || execution.known_mismatches > 0
        || execution.campaign_limit_reached;
    if let Some(signal) = execution.interrupted_signal {
        return Ok(128 + signal);
    }
    Ok(if incomplete { 2 } else { 0 })
}

/// Consume and return the value following `option` at `arguments[*index]`,
/// advancing `*index` past it. Shared by every crate-internal CLI argument
/// grammar (`task`/`suite` here, `certificate build` in
/// [`crate::certificate_cli`]).
pub(crate) fn take_value<'a>(
    arguments: &'a [String],
    index: &mut usize,
    option: &str,
) -> Result<&'a str, String> {
    *index += 1;
    arguments
        .get(*index)
        .map(String::as_str)
        .filter(|value| !value.is_empty())
        .ok_or_else(|| format!("{option} requires a value"))
}

fn parse_duration(value: &str, option: &str) -> Result<Duration, String> {
    let seconds = value
        .parse::<f64>()
        .ok()
        .filter(|seconds| seconds.is_finite() && *seconds > 0.0)
        .ok_or_else(|| format!("{option} requires positive finite seconds"))?;
    Duration::try_from_secs_f64(seconds)
        .map_err(|_| format!("{option} is outside the supported duration range"))
}

fn resolve_path(repository: &Path, path: PathBuf) -> PathBuf {
    if path.is_absolute() {
        path
    } else {
        repository.join(path)
    }
}

fn resolve_program(repository: &Path, path: PathBuf) -> PathBuf {
    if path.components().count() == 1 {
        path
    } else {
        resolve_path(repository, path)
    }
}

fn default_vampire_path() -> PathBuf {
    if let Some(path) = std::env::var_os("VAMPIRE_BIN") {
        return PathBuf::from(path);
    }
    let legacy = PathBuf::from("/opt/vampire/build/vampire");
    if legacy.is_file() {
        legacy
    } else {
        PathBuf::from("vampire")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parser_accepts_single_task_and_runtime_controls() {
        let CliAction::Run(config) = parse_cli_args([
            "task",
            "Example0012",
            "--task-limit",
            "1.5",
            "--campaign-limit",
            "10",
            "--proof-casc-share",
            "0.5",
            "--enumerator",
            "fast",
            "--telemetry",
            "detailed",
            "--format",
            "jsonl",
            "--strict-history",
        ])
        .unwrap() else {
            panic!("expected run action")
        };
        assert_eq!(
            config.selection,
            CampaignSelection::Task("Example0012".to_string())
        );
        assert_eq!(config.per_task_limit, Duration::from_millis(1_500));
        assert_eq!(config.campaign_limit, Some(Duration::from_secs(10)));
        assert_eq!(
            config.proof_casc_policy,
            ProofCascPolicy::uniform("0.5".parse().unwrap()),
        );
        assert_eq!(config.proposal_realization, ProposalRealization::FastV1);
        assert_eq!(config.telemetry_level, TelemetryLevel::Detailed);
        assert_eq!(config.output_format, OutputFormat::JsonLines);
        assert!(config.log_maintenance_history);
        assert!(config.fail_on_history_log_error);
    }

    #[test]
    fn parser_rejects_zero_limits_and_unknown_options() {
        assert!(parse_cli_args(["suite", "all", "--task-limit", "0"]).is_err());
        assert!(parse_cli_args(["suite", "all", "--surprise"]).is_err());
        assert!(parse_cli_args(["suite", "all", "--enumerator", "tuned-for-example"]).is_err());
        for value in ["-0.1", "1.1", "NaN", "0.1234567"] {
            assert!(parse_cli_args(["suite", "all", "--proof-casc-share", value]).is_err());
            assert!(parse_cli_args(["suite", "all", "--proof-casc-retry-share", value]).is_err());
        }
    }

    #[test]
    fn enumerator_selection_is_campaign_global() {
        let CliAction::Run(defaulted) = parse_cli_args(["task", "Example0012"]).unwrap() else {
            panic!("expected task run action")
        };
        let CliAction::Run(suite) =
            parse_cli_args(["suite", "all", "--enumerator", "fast"]).unwrap()
        else {
            panic!("expected suite run action")
        };
        let CliAction::Run(task) =
            parse_cli_args(["task", "Example0012", "--enumerator", "fast"]).unwrap()
        else {
            panic!("expected task run action")
        };

        assert_eq!(
            defaulted.proposal_realization,
            ProposalRealization::SeededV1
        );
        assert_eq!(defaulted.proof_casc_policy, ProofCascPolicy::CLI_DEFAULT);
        assert_eq!(suite.proposal_realization, ProposalRealization::FastV1);
        assert_eq!(task.proposal_realization, ProposalRealization::FastV1);
    }

    #[test]
    fn proof_casc_share_accepts_disabled_and_casc_only_controls() {
        for (value, expected) in [("0", ProofCascShare::DISABLED), ("1", ProofCascShare::ONLY)] {
            let CliAction::Run(config) =
                parse_cli_args(["task", "Example0012", "--proof-casc-share", value]).unwrap()
            else {
                panic!("expected run action")
            };
            assert_eq!(config.proof_casc_policy, ProofCascPolicy::uniform(expected));
        }
    }

    #[test]
    fn proof_casc_retry_share_is_exact_and_option_order_independent() {
        for arguments in [
            [
                "task",
                "Example0012",
                "--proof-casc-share",
                "0.2",
                "--proof-casc-retry-share",
                "0.8",
            ],
            [
                "task",
                "Example0012",
                "--proof-casc-retry-share",
                "0.8",
                "--proof-casc-share",
                "0.2",
            ],
        ] {
            let CliAction::Run(config) = parse_cli_args(arguments).unwrap() else {
                panic!("expected run action")
            };
            assert_eq!(
                config.proof_casc_policy,
                ProofCascPolicy::new("0.2".parse().unwrap(), "0.8".parse().unwrap()).unwrap(),
            );
        }

        let CliAction::Run(retry_only) =
            parse_cli_args(["task", "Example0012", "--proof-casc-retry-share", "0.5"]).unwrap()
        else {
            panic!("expected run action")
        };
        assert_eq!(
            retry_only.proof_casc_policy,
            ProofCascPolicy::new(ProofCascShare::CLI_DEFAULT, "0.5".parse().unwrap()).unwrap(),
        );

        assert!(
            parse_cli_args([
                "task",
                "Example0012",
                "--proof-casc-share",
                "0",
                "--proof-casc-retry-share",
                "0.75",
            ])
            .is_err()
        );
        assert!(
            parse_cli_args([
                "task",
                "Example0012",
                "--proof-casc-share",
                "1",
                "--proof-casc-retry-share",
                "0.75",
            ])
            .is_err()
        );
    }
}
