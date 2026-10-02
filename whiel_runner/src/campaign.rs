//! Canonical benchmark selection and manifest export.
//!
//! This module reads only generated corpus metadata and the compiled Lean
//! dispatcher's supported-ID list.  A known benchmark classification is
//! retained for post-run comparison; it never influences task execution.

use std::collections::{BTreeSet, HashSet};
use std::ffi::OsString;
use std::fmt;
use std::fs::{self, File};
use std::io::{BufWriter, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Stdio};
use std::sync::mpsc::{self, RecvTimeoutError};
use std::thread;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

#[cfg(any(target_os = "macos", target_os = "linux"))]
use std::os::unix::process::CommandExt;

use serde::{Deserialize, Serialize};

use crate::certification::CertificationBridgeCommand;
use crate::encoding::{
    EncodingWorkerCommand, EncodingWorkerPoolConfig, ProposalRealization,
    REFERENCE_PROPOSAL_VERSION,
};
use crate::failure::{FailureKind, FailureOrigin, FailureReport, FailureScope};
use crate::houdini::{CertificationRuntime, VerificationParameters};
use crate::reporting::{
    CAMPAIGN_SCHEMA_VERSION, CampaignEvent, KnownComparison, OutputFormat, Reporter,
    TaskResultContext, TaskResultRecord, TelemetryRecord, TerminalClassification,
};
use crate::runtime::RuntimeResourcePolicy;
#[cfg(any(target_os = "macos", target_os = "linux"))]
use crate::runtime::process_tree::{ProcessRegistry, signal_group, signal_identity};
use crate::symbolic::{
    SymbolicHoudiniPolicy, SymbolicHoudiniRuntime, WLimitGrowth, normalize_symbolic_verification,
    symbolic_houdini,
};
use crate::task::SynthesisTask;
use crate::telemetry::{
    ReferenceFeatureSetTelemetry, TelemetryConfig, TelemetryHandle, TelemetryLevel,
    TelemetrySession,
};
use crate::vampire::{
    PROOF_CASC_ALLOCATION_FORMULA, PROOF_CASC_ALLOCATION_ROUNDING, PROOF_CASC_AVATAR,
    PROOF_CASC_CORES, PROOF_CASC_PROFILE_ID, PROOF_CASC_RANDOM_SEED,
    PROOF_CASC_RANDOMIZE_WORKER_SEEDS, PROOF_CASC_SCHEDULE, PROOF_CASC_SHARE_SCALE,
    PROOF_CASC_SHUFFLE_SCHEDULE_REPEATS, VampireWorkerCommand,
};

const MAX_DISPATCH_DIAGNOSTIC_BYTES: usize = 2_048;
const MAX_DISPATCH_STDOUT_BYTES: usize = 1_048_576;
const MAX_TASK_MANIFEST_BYTES: u64 = 16 * 1_048_576;
const MAX_DISPATCH_SETUP_TIME: Duration = Duration::from_secs(30);
const CAMPAIGN_CONFIGURATION_SCHEMA_VERSION: u64 = 6;

// ------------------------------------------------------------
// Catalog Selection
// ------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KnownClassification {
    Valid,
    Invalid,
    Unknown,
}

impl KnownClassification {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Valid => "valid",
            Self::Invalid => "invalid",
            Self::Unknown => "unknown",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CampaignTask {
    canonical_id: String,
    /// Opaque catalog metadata. Selection must not interpret this value.
    known_classification: serde_json::Value,
}

impl CampaignTask {
    pub fn canonical_id(&self) -> &str {
        &self.canonical_id
    }

    /// Read this value only after synthesis returns.
    fn known_classification(&self) -> KnownClassification {
        parse_known_classification(&self.known_classification)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CampaignSelection {
    Task(String),
    Suite(String),
}

#[derive(Debug)]
pub enum CampaignError {
    Io { path: PathBuf, detail: String },
    InvalidCatalog(String),
    InvalidSelection(String),
    Dispatcher(String),
    DispatcherTimeout { operation: String, limit: Duration },
    InvalidManifest(String),
    Configuration(String),
    Output(String),
}

impl fmt::Display for CampaignError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io { path, detail } => write!(formatter, "{}: {detail}", path.display()),
            Self::InvalidCatalog(detail) => {
                write!(formatter, "invalid benchmark catalog: {detail}")
            }
            Self::InvalidSelection(detail) => write!(formatter, "invalid task selection: {detail}"),
            Self::Dispatcher(detail) => write!(formatter, "benchmark dispatcher failed: {detail}"),
            Self::DispatcherTimeout { operation, limit } => write!(
                formatter,
                "benchmark dispatcher timed out during {operation} after {limit:?}"
            ),
            Self::InvalidManifest(detail) => write!(formatter, "invalid task manifest: {detail}"),
            Self::Configuration(detail) => {
                write!(formatter, "invalid campaign configuration: {detail}")
            }
            Self::Output(detail) => write!(formatter, "campaign output failed: {detail}"),
        }
    }
}

// ------------------------------------------------------------
// Campaign Execution
// ------------------------------------------------------------

#[derive(Clone, Debug)]
pub struct CampaignRuntimeConfig {
    pub repository: PathBuf,
    pub catalog: PathBuf,
    pub dispatcher: PathBuf,
    pub vampire: VampireWorkerCommand,
    pub certification_bridge: CertificationBridgeCommand,
    pub run_name: String,
    pub selection: CampaignSelection,
    /// Bounds synthesis lane/search work. Required cleanup and artifact
    /// settlement may extend wall time after this deadline.
    pub per_task_limit: Duration,
    /// Bounds remaining lane/search work across the campaign, not mandatory
    /// cleanup or artifact settlement.
    pub campaign_limit: Option<Duration>,
    pub search_limit: Duration,
    pub encoding_workers: usize,
    /// One benchmark-blind proposal implementation for the full campaign.
    /// It cannot vary by task identity, suite membership, or expected answer.
    pub proposal_realization: ProposalRealization,
    pub telemetry_level: TelemetryLevel,
    /// Whole-run ceiling on published artifact bytes, clamped at run start
    /// to the free space at the artifact root. `None` leaves it unbounded.
    pub artifact_allowance_bytes: Option<u64>,
    /// Per-task ceiling on artifact payload files created on disk. File
    /// count, not bytes, is what overwhelms per-file bookkeeping such as
    /// a cloud-sync engine's record queue. `None` leaves it unbounded.
    pub artifact_file_allowance: Option<u64>,
    pub progress_interval: Option<Duration>,
    pub output_format: OutputFormat,
    pub log_maintenance_history: bool,
    pub fail_on_history_log_error: bool,
}

#[derive(Clone, Debug)]
struct EffectiveSynthesisConfiguration {
    verification: VerificationParameters,
    policy: SymbolicHoudiniPolicy,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CampaignExecution {
    pub interrupted_signal: Option<i32>,
    pub selected_tasks: usize,
    pub completed_tasks: usize,
    pub timeouts: usize,
    pub failures: usize,
    pub known_mismatches: usize,
    pub campaign_limit_reached: bool,
    pub run_root: PathBuf,
    pub results_path: PathBuf,
    pub process_peak_rss_bytes: Option<u64>,
    pub waited_children_peak_rss_bytes: Option<u64>,
}

pub fn default_run_name() -> String {
    let seconds = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or(Duration::ZERO)
        .as_secs();
    format!("run-{seconds}-{}", std::process::id())
}

fn effective_synthesis_configuration(
    config: &CampaignRuntimeConfig,
) -> Result<EffectiveSynthesisConfiguration, CampaignError> {
    let verification = normalize_symbolic_verification(
        VerificationParameters::new(
            config.search_limit,
            RuntimeResourcePolicy::default_symbolic(),
        )
        .map_err(|detail| CampaignError::Configuration(detail.to_string()))?,
    );
    Ok(EffectiveSynthesisConfiguration {
        verification,
        policy: SymbolicHoudiniPolicy::default(),
    })
}

pub fn run_campaign<W: Write>(
    config: CampaignRuntimeConfig,
    reporter: &mut Reporter<W>,
) -> Result<CampaignExecution, CampaignError> {
    validate_runtime_config(&config)?;
    let effective = effective_synthesis_configuration(&config)?;
    let campaign_started = Instant::now();
    let listing_limit = setup_limit(&config, campaign_started.elapsed()).ok_or_else(|| {
        CampaignError::DispatcherTimeout {
            operation: "supported-task listing".to_string(),
            limit: config.campaign_limit.unwrap_or(MAX_DISPATCH_SETUP_TIME),
        }
    })?;
    let supported =
        dispatcher_supported_ids(&config.dispatcher, &config.repository, listing_limit)?;
    let tasks = load_campaign_tasks(&config.catalog, &supported, &config.selection)?;
    let run_root = reserve_campaign_root(&config.repository, &config.run_name)?;
    let mut journal = CampaignJournal::create(run_root.join("results.jsonl"))?;
    let (selection_kind, selection_name) = match &config.selection {
        CampaignSelection::Task(id) => ("task", id.as_str()),
        CampaignSelection::Suite(suite) => ("suite", suite.as_str()),
    };
    write_campaign_configuration(
        &run_root,
        &config,
        &effective,
        selection_kind,
        selection_name,
        tasks.len(),
    )?;
    emit(
        reporter,
        &mut journal,
        &CampaignEvent::CampaignStart {
            schema_version: CAMPAIGN_SCHEMA_VERSION,
            selection_kind: selection_kind.to_string(),
            selection_name: selection_name.to_string(),
            task_count: tasks.len() as u64,
            artifact_root: run_root
                .strip_prefix(&config.repository)
                .unwrap_or(&run_root)
                .to_string_lossy()
                .into_owned(),
        },
    )?;

    let mut valid = 0_u64;
    let mut invalid = 0_u64;
    let mut timeouts = 0_u64;
    let mut failures = 0_u64;
    let mut known_matches = 0_u64;
    let mut known_mismatches = 0_u64;
    let mut completed = 0_usize;
    let mut campaign_limit_reached = false;
    let mut process_peak_rss_bytes = None;
    let mut waited_children_peak_rss_bytes = None;

    for (offset, selected) in tasks.iter().enumerate() {
        if crate::runtime::interrupt::requested().is_some() {
            break;
        }
        let Some(task_limit) = effective_task_limit(
            config.per_task_limit,
            config.campaign_limit,
            campaign_started.elapsed(),
        ) else {
            campaign_limit_reached = true;
            break;
        };
        let index = offset + 1;
        emit(
            reporter,
            &mut journal,
            &CampaignEvent::TaskStart {
                schema_version: CAMPAIGN_SCHEMA_VERSION,
                canonical_id: selected.canonical_id().to_string(),
                index: index as u64,
                total: tasks.len() as u64,
                task_overall_limit_milliseconds: crate::reporting::duration_milliseconds(
                    task_limit,
                ),
                campaign_remaining_milliseconds: config.campaign_limit.and_then(|limit| {
                    limit
                        .checked_sub(campaign_started.elapsed())
                        .map(crate::reporting::duration_milliseconds)
                }),
            },
        )?;
        let task_started = Instant::now();
        let task_root = run_root.join(selected.canonical_id());
        let manifest_path = task_root.join("task-manifest.json");
        let manifest_limit = MAX_DISPATCH_SETUP_TIME.min(task_limit);
        let task = export_task_manifest(
            &config.dispatcher,
            &config.repository,
            selected.canonical_id(),
            &manifest_path,
            manifest_limit,
        );
        let (result, telemetry_report) = match task {
            Err(error) => (
                crate::symbolic::SynthesisResult::Failure(manifest_failure_report(&error)),
                TelemetrySession::disabled().finish(),
            ),
            Ok(task) => match remaining_synthesis_limit(
                config.per_task_limit,
                task_started.elapsed(),
                config.campaign_limit,
                campaign_started.elapsed(),
            ) {
                None => {
                    campaign_limit_reached |= config
                        .campaign_limit
                        .is_some_and(|limit| campaign_started.elapsed() >= limit);
                    (
                        crate::symbolic::SynthesisResult::Failure(FailureReport::overall_timeout(
                            task_limit,
                        )),
                        TelemetrySession::disabled().finish(),
                    )
                }
                Some(remaining) => {
                    let telemetry_session = TelemetrySession::start(TelemetryConfig::new(
                        task_root.join("telemetry"),
                        config.telemetry_level,
                    ));
                    let telemetry_handle = telemetry_session.handle();
                    let result = run_symbolic_task_with_progress(
                        &config,
                        &effective,
                        &task,
                        &task_root,
                        remaining,
                        &telemetry_handle,
                        reporter,
                        &mut journal,
                        index,
                        tasks.len(),
                        task_started,
                    )?;
                    telemetry_handle.record_terminal_outcome(terminal_name(&result));
                    (result, telemetry_session.finish())
                }
            },
        };
        process_peak_rss_bytes = maximum_optional(
            process_peak_rss_bytes,
            telemetry_report.snapshot.memory.process_peak_rss_bytes,
        );
        waited_children_peak_rss_bytes = maximum_optional(
            waited_children_peak_rss_bytes,
            telemetry_report
                .snapshot
                .memory
                .waited_children_peak_rss_bytes,
        );
        let task_artifact_root = task_root.join("solver-artifacts");
        let result_context = TaskResultContext::new(
            selected.canonical_id(),
            index,
            tasks.len(),
            &task_artifact_root,
            &config.repository,
            // This is deliberately the first read of the known status on the
            // execution path.  It cannot steer synthesis.
            selected.known_classification(),
        );
        let record = TaskResultRecord::new(
            result_context,
            task_started.elapsed(),
            &result,
            TelemetryRecord::from_report(&telemetry_report, &config.repository),
        );
        match record.terminal.classification() {
            TerminalClassification::Valid => valid += 1,
            TerminalClassification::Invalid => invalid += 1,
            TerminalClassification::Timeout => timeouts += 1,
            TerminalClassification::Failure => failures += 1,
        }
        match record.known_comparison {
            KnownComparison::Match => known_matches += 1,
            KnownComparison::Mismatch => known_mismatches += 1,
            KnownComparison::UnknownBaseline | KnownComparison::NoSynthesisClassification => {}
        }
        emit(
            reporter,
            &mut journal,
            &CampaignEvent::TaskResult {
                schema_version: CAMPAIGN_SCHEMA_VERSION,
                result: Box::new(record),
            },
        )?;
        completed += 1;
        campaign_limit_reached |= config
            .campaign_limit
            .is_some_and(|limit| campaign_started.elapsed() >= limit);
    }

    emit(
        reporter,
        &mut journal,
        &CampaignEvent::CampaignSummary {
            schema_version: CAMPAIGN_SCHEMA_VERSION,
            task_count: completed as u64,
            valid,
            invalid,
            timeouts,
            failures,
            known_matches,
            known_mismatches,
            elapsed_milliseconds: crate::reporting::duration_milliseconds(
                campaign_started.elapsed(),
            ),
            campaign_limit_reached,
            process_peak_rss_bytes,
            waited_children_peak_rss_bytes,
        },
    )?;
    journal.finish()?;
    let interrupted_signal = crate::runtime::interrupt::requested();
    if let Some(signal) = interrupted_signal {
        eprintln!(
            "symbolic: interrupted by signal {signal}; completed tasks are settled under {}",
            run_root.display()
        );
    }
    let results_path = journal.path().to_path_buf();
    Ok(CampaignExecution {
        interrupted_signal,
        selected_tasks: tasks.len(),
        completed_tasks: completed,
        timeouts: timeouts as usize,
        failures: failures as usize,
        known_mismatches: known_mismatches as usize,
        campaign_limit_reached,
        run_root,
        results_path,
        process_peak_rss_bytes,
        waited_children_peak_rss_bytes,
    })
}

#[allow(clippy::too_many_arguments)]
fn run_symbolic_task_with_progress<W: Write>(
    config: &CampaignRuntimeConfig,
    effective: &EffectiveSynthesisConfiguration,
    task: &SynthesisTask,
    task_root: &Path,
    task_limit: Duration,
    telemetry: &TelemetryHandle,
    reporter: &mut Reporter<W>,
    journal: &mut CampaignJournal,
    index: usize,
    total: usize,
    task_started: Instant,
) -> Result<crate::symbolic::SynthesisResult, CampaignError> {
    let Some(interval) = live_progress_interval(config) else {
        return run_symbolic_task(config, effective, task, task_root, task_limit, telemetry);
    };
    thread::scope(|scope| {
        let (sender, receiver) = mpsc::sync_channel(1);
        let worker = scope.spawn(move || {
            let result =
                run_symbolic_task(config, effective, task, task_root, task_limit, telemetry);
            let _ = sender.send(());
            result
        });
        loop {
            match receiver.recv_timeout(interval) {
                Ok(()) | Err(RecvTimeoutError::Disconnected) => break,
                Err(RecvTimeoutError::Timeout) => {
                    let snapshot = telemetry.progress_snapshot();
                    emit(
                        reporter,
                        journal,
                        &CampaignEvent::TaskProgress {
                            schema_version: CAMPAIGN_SCHEMA_VERSION,
                            canonical_id: task.identity().canonical_id().to_string(),
                            index: index as u64,
                            total: total as u64,
                            elapsed_milliseconds: crate::reporting::duration_milliseconds(
                                task_started.elapsed(),
                            ),
                            inv_epochs: snapshot.inv_epochs,
                            proposed_clauses: snapshot.proposed_clauses,
                            initialized_clauses: snapshot.initialized_clauses,
                            core_admissions: snapshot.core_admissions,
                            highest_w_index: snapshot.highest_w_index,
                            highest_safe_fmb_frontier: snapshot.highest_safe_fmb_frontier,
                        },
                    )?;
                }
            }
        }
        worker.join().map_err(|_| {
            CampaignError::Configuration("symbolic task supervisor panicked".to_string())
        })?
    })
}

fn live_progress_interval(config: &CampaignRuntimeConfig) -> Option<Duration> {
    // Fixed-size progress exists at every telemetry level. Only this explicit
    // CLI control disables periodic progress records.
    config.progress_interval
}

fn run_symbolic_task(
    config: &CampaignRuntimeConfig,
    effective: &EffectiveSynthesisConfiguration,
    task: &SynthesisTask,
    task_root: &Path,
    task_limit: Duration,
    telemetry: &TelemetryHandle,
) -> Result<crate::symbolic::SynthesisResult, CampaignError> {
    let encoding_command = EncodingWorkerCommand::new(&config.dispatcher, &config.repository)
        .arguments([
            OsString::from("worker"),
            OsString::from(task.identity().canonical_id()),
        ]);
    let encoding_workers = EncodingWorkerPoolConfig::new(encoding_command, config.encoding_workers)
        .map_err(|detail| CampaignError::Configuration(detail.to_string()))?
        .proposal_realization(config.proposal_realization);
    let certification = CertificationRuntime::new(
        config.certification_bridge.clone(),
        task_root.join("certification-work"),
        task_root.join("solution"),
    );
    let runtime = SymbolicHoudiniRuntime::new(
        task_root.join("solver-artifacts"),
        encoding_workers,
        config.vampire.clone(),
        certification,
    )
    .with_telemetry(telemetry.clone())
    .with_artifact_allowance(config.artifact_allowance_bytes)
    .with_artifact_file_allowance(config.artifact_file_allowance);
    Ok(symbolic_houdini(
        task,
        task_limit,
        effective.verification.clone(),
        effective.policy.clone(),
        config.log_maintenance_history,
        config.fail_on_history_log_error,
        runtime,
    ))
}

fn effective_task_limit(
    per_task: Duration,
    campaign: Option<Duration>,
    elapsed: Duration,
) -> Option<Duration> {
    let Some(campaign) = campaign else {
        return Some(per_task);
    };
    let remaining = campaign.checked_sub(elapsed)?;
    if remaining.is_zero() {
        None
    } else {
        Some(per_task.min(remaining))
    }
}

fn setup_limit(config: &CampaignRuntimeConfig, elapsed: Duration) -> Option<Duration> {
    match config.campaign_limit {
        None => Some(MAX_DISPATCH_SETUP_TIME),
        Some(limit) => limit
            .checked_sub(elapsed)
            .filter(|remaining| !remaining.is_zero())
            .map(|remaining| remaining.min(MAX_DISPATCH_SETUP_TIME)),
    }
}

fn remaining_synthesis_limit(
    per_task: Duration,
    task_elapsed: Duration,
    campaign: Option<Duration>,
    campaign_elapsed: Duration,
) -> Option<Duration> {
    let task_remaining = per_task
        .checked_sub(task_elapsed)
        .filter(|remaining| !remaining.is_zero())?;
    match campaign {
        None => Some(task_remaining),
        Some(limit) => limit
            .checked_sub(campaign_elapsed)
            .filter(|remaining| !remaining.is_zero())
            .map(|remaining| task_remaining.min(remaining)),
    }
}

fn terminal_name(result: &crate::symbolic::SynthesisResult) -> &'static str {
    match result {
        crate::symbolic::SynthesisResult::Valid(_) => "valid",
        crate::symbolic::SynthesisResult::Invalid(_) => "invalid",
        crate::symbolic::SynthesisResult::Failure(report)
            if report.kind() == FailureKind::OverallTimeout =>
        {
            "timeout"
        }
        crate::symbolic::SynthesisResult::Failure(_) => "failure",
    }
}

fn manifest_failure_report(error: &CampaignError) -> FailureReport {
    let kind = match error {
        CampaignError::InvalidManifest(_) => FailureKind::MalformedResult,
        CampaignError::Dispatcher(_) | CampaignError::DispatcherTimeout { .. } => {
            FailureKind::ProcessFailure
        }
        CampaignError::Io { .. }
        | CampaignError::InvalidCatalog(_)
        | CampaignError::InvalidSelection(_)
        | CampaignError::Configuration(_)
        | CampaignError::Output(_) => FailureKind::InfrastructureFailure,
    };
    FailureReport::try_new(
        FailureOrigin::EncodingPreparation,
        kind,
        false,
        FailureScope::RunGlobal,
        Some(error.to_string()),
        Vec::new(),
    )
    .expect("manifest failures use approved encoding-preparation pairs")
}

fn maximum_optional(left: Option<u64>, right: Option<u64>) -> Option<u64> {
    match (left, right) {
        (Some(left), Some(right)) => Some(left.max(right)),
        (Some(value), None) | (None, Some(value)) => Some(value),
        (None, None) => None,
    }
}

fn validate_runtime_config(config: &CampaignRuntimeConfig) -> Result<(), CampaignError> {
    if config.per_task_limit.is_zero() {
        return Err(CampaignError::Configuration(
            "per-task limit must be positive".to_string(),
        ));
    }
    if config.campaign_limit.is_some_and(|limit| limit.is_zero()) {
        return Err(CampaignError::Configuration(
            "campaign limit must be positive when present".to_string(),
        ));
    }
    if config.search_limit.is_zero() {
        return Err(CampaignError::Configuration(
            "search limit must be positive".to_string(),
        ));
    }
    if config.encoding_workers == 0 {
        return Err(CampaignError::Configuration(
            "encoding worker count must be positive".to_string(),
        ));
    }
    if config
        .progress_interval
        .is_some_and(|interval| interval.is_zero())
    {
        return Err(CampaignError::Configuration(
            "progress interval must be positive when present".to_string(),
        ));
    }
    validate_run_name(&config.run_name)
}

fn validate_run_name(value: &str) -> Result<(), CampaignError> {
    let valid = !value.is_empty()
        && value.len() <= 96
        && value != "."
        && value != ".."
        && value
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_' | b'.'));
    if valid {
        Ok(())
    } else {
        Err(CampaignError::Configuration(format!(
            "unsafe run name {value:?}; use at most 96 ASCII letters, digits, '.', '-', or '_'"
        )))
    }
}

fn reserve_campaign_root(repository: &Path, run_name: &str) -> Result<PathBuf, CampaignError> {
    let artifact_base = repository.join("artifacts");
    reject_symlink(&artifact_base)?;
    let artifacts = artifact_base.join("symbolic-houdini");
    reject_symlink(&artifacts)?;
    fs::create_dir_all(&artifacts).map_err(|error| CampaignError::Io {
        path: artifacts.clone(),
        detail: error.to_string(),
    })?;
    let run_root = artifacts.join(run_name);
    fs::create_dir(&run_root).map_err(|error| CampaignError::Io {
        path: run_root.clone(),
        detail: format!("reserve fresh run directory: {error}"),
    })?;
    Ok(run_root)
}

fn reject_symlink(path: &Path) -> Result<(), CampaignError> {
    if fs::symlink_metadata(path).is_ok_and(|metadata| metadata.file_type().is_symlink()) {
        Err(CampaignError::Configuration(format!(
            "refuse symlinked artifact directory {}",
            path.display()
        )))
    } else {
        Ok(())
    }
}

fn emit<W: Write>(
    reporter: &mut Reporter<W>,
    journal: &mut CampaignJournal,
    event: &CampaignEvent,
) -> Result<(), CampaignError> {
    journal.emit(event)?;
    reporter
        .emit(event)
        .map_err(|error| CampaignError::Output(error.to_string()))
}

struct CampaignJournal {
    path: PathBuf,
    writer: BufWriter<File>,
}

#[derive(Serialize)]
struct CampaignConfigurationRecord<'a> {
    schema_version: u64,
    runner_package_version: &'static str,
    runner_executable: String,
    runner_executable_sha256: String,
    terminal_output_format: &'static str,
    selection_kind: &'a str,
    selection_name: &'a str,
    selected_task_count: u64,
    catalog: String,
    catalog_identity: FileIdentityRecord,
    dispatcher: String,
    dispatcher_identity: FileIdentityRecord,
    vampire: String,
    vampire_identity: FileIdentityRecord,
    vampire_extra_arguments: Vec<String>,
    vampire_proof_policy: VampireProofPolicyConfigurationRecord,
    certification_executable: String,
    certification_executable_identity: FileIdentityRecord,
    certification_arguments: Vec<String>,
    certification_repository: String,
    certification_bridge_identity: FileIdentityRecord,
    per_task_limit_nanoseconds: u64,
    campaign_limit_nanoseconds: Option<u64>,
    encoding_workers: u64,
    telemetry_level: TelemetryLevel,
    progress_interval_nanoseconds: Option<u64>,
    log_maintenance_history: bool,
    fail_on_history_log_error: bool,
    proposal_realization_id: &'static str,
    proposal_realization_version: u64,
    verification: VerificationConfigurationRecord,
    symbolic_policy: SymbolicPolicyConfigurationRecord,
    reference_schedule_id: String,
    reference_features: ReferenceFeatureSetTelemetry,
}

#[derive(Serialize)]
struct FileIdentityRecord {
    path: String,
    sha256: Option<String>,
    unavailable_reason: Option<String>,
}

#[derive(Serialize)]
struct VampireProofPolicyConfigurationRecord {
    profile_id: &'static str,
    initial_casc_share_millionths: u32,
    retry_added_casc_share_millionths: u32,
    share_scale: u32,
    allocation_formula: &'static str,
    allocation_rounding: &'static str,
    casc_schedule: &'static str,
    casc_cores: u64,
    random_seed: &'static str,
    randomize_worker_seeds: bool,
    shuffle_schedule_repeats: bool,
    avatar: bool,
    internal_limit_unit: &'static str,
    internal_limit_derivation: &'static str,
    external_deadline_authoritative: bool,
}

#[derive(Serialize)]
struct VerificationConfigurationRecord {
    search_limit_nanoseconds: u64,
    maintenance_retry_increment_nanoseconds: Vec<u64>,
    bulk_init_limit_nanoseconds: u64,
    bulk_maint_limit_nanoseconds: u64,
    init_first_attempt_limit_nanoseconds: Vec<u64>,
    init_attempt_limit_nanoseconds: Vec<u64>,
    search_term_limit_nanoseconds: u64,
    search_term_retry_increment_nanoseconds: Vec<u64>,
    final_certification_limit_nanoseconds: Option<u64>,
    max_vampire_processes: u64,
    cex_reserved_vampire_processes: u64,
    max_inv_vampire_processes: u64,
    max_cpu_workers: u64,
}

#[derive(Serialize)]
struct SymbolicPolicyConfigurationRecord {
    admit_higher_w_layers: bool,
    w_fresh_batch_size: u64,
    w_retry_batch_size: u64,
    w_initial_limit_nanoseconds: u64,
    w_limit_growth: String,
}

fn write_campaign_configuration(
    run_root: &Path,
    config: &CampaignRuntimeConfig,
    effective: &EffectiveSynthesisConfiguration,
    selection_kind: &str,
    selection_name: &str,
    selected_task_count: usize,
) -> Result<(), CampaignError> {
    let path = run_root.join("campaign-config.json");
    let staging = run_root.join("campaign-config.json.part");
    let runner_executable = std::env::current_exe().map_err(|error| CampaignError::Io {
        path: PathBuf::from("current executable"),
        detail: error.to_string(),
    })?;
    let resources = effective.verification.resources();
    let w_search = effective.policy.w_search();
    let proof_casc_policy = config.vampire.proof_casc_policy();
    let certification_executable = PathBuf::from(config.certification_bridge.executable());
    let certification_bridge = certification_bridge_source(&config.certification_bridge);
    let record = CampaignConfigurationRecord {
        schema_version: CAMPAIGN_CONFIGURATION_SCHEMA_VERSION,
        runner_package_version: env!("CARGO_PKG_VERSION"),
        runner_executable: display_campaign_path(&config.repository, &runner_executable),
        runner_executable_sha256: file_sha256(&runner_executable)?,
        terminal_output_format: config.output_format.as_str(),
        selection_kind,
        selection_name,
        selected_task_count: u64::try_from(selected_task_count).unwrap_or(u64::MAX),
        catalog: display_campaign_path(&config.repository, &config.catalog),
        catalog_identity: file_identity_record(&config.repository, &config.catalog),
        dispatcher: display_campaign_path(&config.repository, &config.dispatcher),
        dispatcher_identity: file_identity_record(&config.repository, &config.dispatcher),
        vampire: display_campaign_path(&config.repository, config.vampire.executable()),
        vampire_identity: file_identity_record(&config.repository, config.vampire.executable()),
        vampire_extra_arguments: config
            .vampire
            .extra_args()
            .iter()
            .map(|argument| argument.to_string_lossy().into_owned())
            .collect(),
        vampire_proof_policy: VampireProofPolicyConfigurationRecord {
            profile_id: PROOF_CASC_PROFILE_ID,
            initial_casc_share_millionths: proof_casc_policy.initial_share().millionths(),
            retry_added_casc_share_millionths: proof_casc_policy.retry_added_share().millionths(),
            share_scale: PROOF_CASC_SHARE_SCALE,
            allocation_formula: PROOF_CASC_ALLOCATION_FORMULA,
            allocation_rounding: PROOF_CASC_ALLOCATION_ROUNDING,
            casc_schedule: PROOF_CASC_SCHEDULE,
            casc_cores: u64::from(PROOF_CASC_CORES),
            random_seed: PROOF_CASC_RANDOM_SEED,
            randomize_worker_seeds: PROOF_CASC_RANDOMIZE_WORKER_SEEDS,
            shuffle_schedule_repeats: PROOF_CASC_SHUFFLE_SCHEDULE_REPEATS,
            avatar: PROOF_CASC_AVATAR,
            internal_limit_unit: "deciseconds",
            internal_limit_derivation: "ceil(shared-deadline-remaining-at-casc-launch/100ms)",
            external_deadline_authoritative: true,
        },
        certification_executable: config
            .certification_bridge
            .executable()
            .to_string_lossy()
            .into_owned(),
        certification_executable_identity: file_identity_record(
            &config.repository,
            &certification_executable,
        ),
        certification_arguments: config
            .certification_bridge
            .arguments()
            .iter()
            .map(|argument| argument.to_string_lossy().into_owned())
            .collect(),
        certification_repository: display_campaign_path(
            &config.repository,
            config.certification_bridge.repository(),
        ),
        certification_bridge_identity: match certification_bridge {
            Ok(path) => file_identity_record(&config.repository, &path),
            Err(reason) => FileIdentityRecord {
                path: "unresolved".to_string(),
                sha256: None,
                unavailable_reason: Some(reason),
            },
        },
        per_task_limit_nanoseconds: duration_nanoseconds(config.per_task_limit),
        campaign_limit_nanoseconds: config.campaign_limit.map(duration_nanoseconds),
        encoding_workers: u64::try_from(config.encoding_workers).unwrap_or(u64::MAX),
        telemetry_level: config.telemetry_level,
        progress_interval_nanoseconds: config.progress_interval.map(duration_nanoseconds),
        log_maintenance_history: config.log_maintenance_history,
        fail_on_history_log_error: config.fail_on_history_log_error,
        proposal_realization_id: config.proposal_realization.realization_id(),
        proposal_realization_version: config.proposal_realization.realization_version(),
        verification: VerificationConfigurationRecord {
            search_limit_nanoseconds: duration_nanoseconds(effective.verification.search_limit()),
            maintenance_retry_increment_nanoseconds: effective
                .verification
                .maintenance_retry_increments()
                .iter()
                .copied()
                .map(duration_nanoseconds)
                .collect(),
            bulk_init_limit_nanoseconds: duration_nanoseconds(
                effective.verification.bulk_init_limit(),
            ),
            bulk_maint_limit_nanoseconds: duration_nanoseconds(
                effective.verification.bulk_maint_limit(),
            ),
            init_first_attempt_limit_nanoseconds: effective
                .verification
                .init_first_attempt_limits()
                .iter()
                .copied()
                .map(duration_nanoseconds)
                .collect(),
            init_attempt_limit_nanoseconds: effective
                .verification
                .init_attempt_limits()
                .into_iter()
                .map(duration_nanoseconds)
                .collect(),
            search_term_limit_nanoseconds: duration_nanoseconds(
                effective.verification.search_term_limit(),
            ),
            search_term_retry_increment_nanoseconds: effective
                .verification
                .search_term_retry_increments()
                .iter()
                .copied()
                .map(duration_nanoseconds)
                .collect(),
            final_certification_limit_nanoseconds: effective
                .verification
                .final_certification_limit()
                .map(duration_nanoseconds),
            max_vampire_processes: usize_record(resources.max_vampire_processes()),
            cex_reserved_vampire_processes: usize_record(
                resources.cex_reserved_vampire_processes(),
            ),
            max_inv_vampire_processes: usize_record(resources.max_inv_vampire_processes()),
            max_cpu_workers: usize_record(resources.max_cpu_workers()),
        },
        symbolic_policy: SymbolicPolicyConfigurationRecord {
            admit_higher_w_layers: effective.policy.admit_higher_w_layers(),
            w_fresh_batch_size: usize_record(w_search.fresh_batch_size()),
            w_retry_batch_size: usize_record(w_search.retry_batch_size()),
            w_initial_limit_nanoseconds: duration_nanoseconds(w_search.initial_limit()),
            w_limit_growth: w_limit_growth_record(w_search.limit_growth()),
        },
        reference_schedule_id: format!(
            "lean-reference-v{REFERENCE_PROPOSAL_VERSION}-all-enabled-diagonal"
        ),
        reference_features: ReferenceFeatureSetTelemetry::all_enabled(),
    };
    let file = File::options()
        .write(true)
        .create_new(true)
        .open(&staging)
        .map_err(|error| CampaignError::Io {
            path: staging.clone(),
            detail: format!("create campaign configuration: {error}"),
        })?;
    let mut writer = BufWriter::new(file);
    serde_json::to_writer_pretty(&mut writer, &record)
        .map_err(|error| CampaignError::Output(format!("write campaign configuration: {error}")))?;
    writer
        .write_all(b"\n")
        .and_then(|()| writer.flush())
        .map_err(|error| CampaignError::Io {
            path: staging.clone(),
            detail: format!("flush campaign configuration: {error}"),
        })?;
    drop(writer);
    fs::rename(&staging, &path).map_err(|error| CampaignError::Io {
        path,
        detail: format!("publish campaign configuration: {error}"),
    })
}

fn duration_nanoseconds(duration: Duration) -> u64 {
    duration.as_nanos().min(u128::from(u64::MAX)) as u64
}

fn usize_record(value: usize) -> u64 {
    u64::try_from(value).unwrap_or(u64::MAX)
}

fn w_limit_growth_record(growth: WLimitGrowth) -> String {
    match growth {
        WLimitGrowth::Linear(increment) => {
            format!("linear:{}ns", duration_nanoseconds(increment))
        }
        WLimitGrowth::Geometric(factor) => format!("geometric:{factor}"),
    }
}

fn file_sha256(path: &Path) -> Result<String, CampaignError> {
    crate::entailment::assembly::hash_file_sha256(path).map_err(|error| CampaignError::Io {
        path: path.to_path_buf(),
        detail: format!("hash file: {error}"),
    })
}

fn file_identity_record(repository: &Path, path: &Path) -> FileIdentityRecord {
    let displayed = display_campaign_path(repository, path);
    let resolved = if path.is_absolute() {
        path.to_path_buf()
    } else if path.components().count() > 1 {
        repository.join(path)
    } else {
        return FileIdentityRecord {
            path: displayed,
            sha256: None,
            unavailable_reason: Some(
                "bare program name is resolved through PATH only when launched".to_string(),
            ),
        };
    };
    match fs::metadata(&resolved) {
        Ok(metadata) if metadata.is_file() => match file_sha256(&resolved) {
            Ok(sha256) => FileIdentityRecord {
                path: display_campaign_path(repository, &resolved),
                sha256: Some(sha256),
                unavailable_reason: None,
            },
            Err(error) => FileIdentityRecord {
                path: display_campaign_path(repository, &resolved),
                sha256: None,
                unavailable_reason: Some(format!("could not hash file: {error}")),
            },
        },
        Ok(_) => FileIdentityRecord {
            path: display_campaign_path(repository, &resolved),
            sha256: None,
            unavailable_reason: Some("path is not a regular file".to_string()),
        },
        Err(error) => FileIdentityRecord {
            path: display_campaign_path(repository, &resolved),
            sha256: None,
            unavailable_reason: Some(format!("file metadata unavailable: {error}")),
        },
    }
}

fn certification_bridge_source(command: &CertificationBridgeCommand) -> Result<PathBuf, String> {
    let arguments = command.arguments();
    if arguments.len() >= 2
        && arguments[0] == "-m"
        && arguments[1] == "whiel_synth.certification_bridge"
    {
        return Ok(command
            .repository()
            .join("whiel_synth/certification_bridge.py"));
    }
    let Some(first) = arguments.first() else {
        return Err("bridge command has no identifiable module or script file".to_string());
    };
    let path = PathBuf::from(first);
    if path.as_os_str().to_string_lossy().starts_with('-') {
        Err("bridge command does not expose an identifiable script file".to_string())
    } else if path.is_absolute() {
        Ok(path)
    } else {
        Ok(command.repository().join(path))
    }
}

fn display_campaign_path(repository: &Path, path: &Path) -> String {
    let displayed = path
        .strip_prefix(repository)
        .unwrap_or(path)
        .to_string_lossy()
        .into_owned();
    if displayed.is_empty() {
        ".".to_string()
    } else {
        displayed
    }
}

impl CampaignJournal {
    fn create(path: PathBuf) -> Result<Self, CampaignError> {
        let file = File::options()
            .write(true)
            .create_new(true)
            .open(&path)
            .map_err(|error| CampaignError::Io {
                path: path.clone(),
                detail: format!("create campaign result journal: {error}"),
            })?;
        Ok(Self {
            path,
            writer: BufWriter::new(file),
        })
    }

    fn emit(&mut self, event: &CampaignEvent) -> Result<(), CampaignError> {
        serde_json::to_writer(&mut self.writer, event)
            .map_err(|error| CampaignError::Output(format!("write campaign result: {error}")))?;
        self.writer
            .write_all(b"\n")
            .and_then(|()| self.writer.flush())
            .map_err(|error| CampaignError::Io {
                path: self.path.clone(),
                detail: format!("flush campaign result journal: {error}"),
            })
    }

    fn finish(&mut self) -> Result<(), CampaignError> {
        self.writer.flush().map_err(|error| CampaignError::Io {
            path: self.path.clone(),
            detail: format!("finish campaign result journal: {error}"),
        })
    }

    fn path(&self) -> &Path {
        &self.path
    }
}

impl std::error::Error for CampaignError {}

#[derive(Debug, Deserialize)]
struct RawCatalog {
    cases: Vec<RawCatalogCase>,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct RawCatalogCase {
    canonical_id: String,
    #[serde(default)]
    root: Option<String>,
    #[serde(default)]
    current_classification: serde_json::Value,
    suites: Vec<String>,
}

pub fn load_campaign_tasks(
    catalog_path: &Path,
    supported_ids: &BTreeSet<String>,
    selection: &CampaignSelection,
) -> Result<Vec<CampaignTask>, CampaignError> {
    let text = fs::read_to_string(catalog_path).map_err(|error| CampaignError::Io {
        path: catalog_path.to_path_buf(),
        detail: error.to_string(),
    })?;
    let catalog: RawCatalog = serde_json::from_str(&text)
        .map_err(|error| CampaignError::InvalidCatalog(error.to_string()))?;
    let mut seen = HashSet::new();
    let mut selected = Vec::new();
    let mut requested_seen = false;
    let mut unsupported = Vec::new();

    for case in catalog.cases {
        validate_canonical_id(&case.canonical_id)?;
        if !seen.insert(case.canonical_id.clone()) {
            return Err(CampaignError::InvalidCatalog(format!(
                "duplicate canonical ID {}",
                case.canonical_id
            )));
        }
        let root = case.root.as_deref().unwrap_or("Benchmark");
        if !matches!(root, "Benchmark" | "Obstructed") {
            return Err(CampaignError::InvalidCatalog(format!(
                "unexpected root for {}: {root:?}",
                case.canonical_id
            )));
        }
        let is_selected = match selection {
            CampaignSelection::Task(id) => case.canonical_id == *id,
            CampaignSelection::Suite(suite) => {
                root == "Benchmark" && case.suites.iter().any(|value| value == suite)
            }
        };
        if !is_selected {
            continue;
        }
        requested_seen = true;
        if !supported_ids.contains(&case.canonical_id) {
            unsupported.push(case.canonical_id);
            continue;
        }
        selected.push(CampaignTask {
            canonical_id: case.canonical_id,
            known_classification: case.current_classification,
        });
    }

    if !requested_seen {
        let requested = match selection {
            CampaignSelection::Task(id) => format!("unknown task {id}"),
            CampaignSelection::Suite(suite) => format!("unknown or empty suite {suite}"),
        };
        return Err(CampaignError::InvalidSelection(requested));
    }
    if !unsupported.is_empty() {
        unsupported.sort();
        return Err(CampaignError::InvalidSelection(format!(
            "selected catalog tasks are absent from the compiled dispatcher: {}",
            bounded_join(&unsupported, 12)
        )));
    }
    selected.sort_by(|left, right| left.canonical_id.cmp(&right.canonical_id));
    Ok(selected)
}

fn parse_known_classification(value: &serde_json::Value) -> KnownClassification {
    match value.as_str() {
        Some("valid") => KnownClassification::Valid,
        Some("invalid") => KnownClassification::Invalid,
        Some("unknown") | None | Some(_) => KnownClassification::Unknown,
    }
}

fn validate_canonical_id(value: &str) -> Result<(), CampaignError> {
    let valid = value.len() == 11
        && value.starts_with("Example")
        && value[7..].bytes().all(|byte| byte.is_ascii_digit());
    if valid {
        Ok(())
    } else {
        Err(CampaignError::InvalidCatalog(format!(
            "unsafe canonical ID {value:?}"
        )))
    }
}

// ------------------------------------------------------------
// Compiled Dispatcher Boundary
// ------------------------------------------------------------

pub fn dispatcher_supported_ids(
    dispatcher: &Path,
    repository: &Path,
    limit: Duration,
) -> Result<BTreeSet<String>, CampaignError> {
    let mut command = Command::new(dispatcher);
    command.arg("list").current_dir(repository);
    let output = run_dispatcher_bounded(command, limit, "supported-task listing")?;
    if !output.status.success() {
        return Err(CampaignError::Dispatcher(format!(
            "list exited with {}; stderr={}",
            output.status,
            bounded_capture(&output.stderr, output.stderr_truncated)
        )));
    }
    if output.stdout_truncated {
        return Err(CampaignError::Dispatcher(format!(
            "supported-task listing exceeded {MAX_DISPATCH_STDOUT_BYTES} bytes"
        )));
    }
    let stdout = std::str::from_utf8(&output.stdout)
        .map_err(|error| CampaignError::Dispatcher(format!("list output is not UTF-8: {error}")))?;
    let mut ids = BTreeSet::new();
    for line in stdout.lines() {
        let id = line.trim();
        if id.is_empty() {
            continue;
        }
        validate_canonical_id(id).map_err(|error| CampaignError::Dispatcher(error.to_string()))?;
        if !ids.insert(id.to_string()) {
            return Err(CampaignError::Dispatcher(format!(
                "list returned duplicate ID {id}"
            )));
        }
    }
    if ids.is_empty() {
        return Err(CampaignError::Dispatcher(
            "list returned no supported IDs".to_string(),
        ));
    }
    Ok(ids)
}

pub fn export_task_manifest(
    dispatcher: &Path,
    repository: &Path,
    canonical_id: &str,
    output_path: &Path,
    limit: Duration,
) -> Result<SynthesisTask, CampaignError> {
    validate_canonical_id(canonical_id)
        .map_err(|error| CampaignError::InvalidSelection(error.to_string()))?;
    if let Some(parent) = output_path.parent() {
        fs::create_dir_all(parent).map_err(|error| CampaignError::Io {
            path: parent.to_path_buf(),
            detail: error.to_string(),
        })?;
    }
    let mut command = Command::new(dispatcher);
    command
        .args(["manifest", canonical_id])
        .arg(output_path)
        .current_dir(repository);
    let output = run_dispatcher_bounded(
        command,
        limit,
        &format!("manifest export for {canonical_id}"),
    )?;
    if !output.status.success() {
        return Err(CampaignError::Dispatcher(format!(
            "manifest {canonical_id} exited with {}; stderr={}",
            output.status,
            bounded_capture(&output.stderr, output.stderr_truncated)
        )));
    }
    let text = read_bounded_manifest(output_path)?;
    let task = SynthesisTask::from_json(&text)
        .map_err(|error| CampaignError::InvalidManifest(error.to_string()))?;
    if task.identity().canonical_id() != canonical_id {
        return Err(CampaignError::InvalidManifest(format!(
            "dispatcher returned task {} for requested {canonical_id}",
            task.identity().canonical_id()
        )));
    }
    Ok(task)
}

#[derive(Debug)]
struct BoundedCommandOutput {
    status: ExitStatus,
    stdout: Vec<u8>,
    stdout_truncated: bool,
    stderr: Vec<u8>,
    stderr_truncated: bool,
}

fn run_dispatcher_bounded(
    mut command: Command,
    limit: Duration,
    operation: &str,
) -> Result<BoundedCommandOutput, CampaignError> {
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    {
        let _ = (&mut command, limit, operation);
        return Err(CampaignError::Configuration(
            "owned dispatcher process trees require macOS or Linux".to_string(),
        ));
    }
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    command.process_group(0);
    command.stdout(Stdio::piped()).stderr(Stdio::piped());
    let display = format!("{:?}", command.get_program());
    let mut child = command.spawn().map_err(|error| {
        CampaignError::Dispatcher(format!("could not start {display}: {error}"))
    })?;
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    let mut registry = ProcessRegistry::new(child.id()).map_err(|error| {
        let _ = signal_group(child.id(), libc::SIGKILL);
        let _ = child.kill();
        let _ = child.wait();
        CampaignError::Dispatcher(format!("register dispatcher process tree: {error}"))
    })?;
    let stdout = child
        .stdout
        .take()
        .ok_or_else(|| CampaignError::Dispatcher("dispatcher stdout was not piped".to_string()))?;
    let stderr = child
        .stderr
        .take()
        .ok_or_else(|| CampaignError::Dispatcher("dispatcher stderr was not piped".to_string()))?;
    let stdout_reader = thread::spawn(move || drain_bounded(stdout, MAX_DISPATCH_STDOUT_BYTES));
    let stderr_reader = thread::spawn(move || drain_bounded(stderr, MAX_DISPATCH_DIAGNOSTIC_BYTES));
    let started = Instant::now();
    let status = loop {
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        registry.refresh();
        match child.try_wait() {
            Ok(Some(status)) => break status,
            Ok(None) if started.elapsed() < limit => {
                thread::sleep(
                    Duration::from_millis(10).min(limit.saturating_sub(started.elapsed())),
                );
            }
            Ok(None) => {
                #[cfg(any(target_os = "macos", target_os = "linux"))]
                cleanup_dispatcher_tree(&mut child, &mut registry);
                let _ = stdout_reader.join();
                let _ = stderr_reader.join();
                return Err(CampaignError::DispatcherTimeout {
                    operation: operation.to_string(),
                    limit,
                });
            }
            Err(error) => {
                #[cfg(any(target_os = "macos", target_os = "linux"))]
                cleanup_dispatcher_tree(&mut child, &mut registry);
                let _ = stdout_reader.join();
                let _ = stderr_reader.join();
                return Err(CampaignError::Dispatcher(format!(
                    "observe {operation}: {error}"
                )));
            }
        }
    };
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    cleanup_dispatcher_tree(&mut child, &mut registry);
    let (stdout, stdout_truncated) = stdout_reader
        .join()
        .map_err(|_| CampaignError::Dispatcher("stdout drain panicked".to_string()))?
        .map_err(|error| CampaignError::Dispatcher(format!("read stdout: {error}")))?;
    let (stderr, stderr_truncated) = stderr_reader
        .join()
        .map_err(|_| CampaignError::Dispatcher("stderr drain panicked".to_string()))?
        .map_err(|error| CampaignError::Dispatcher(format!("read stderr: {error}")))?;
    Ok(BoundedCommandOutput {
        status,
        stdout,
        stdout_truncated,
        stderr,
        stderr_truncated,
    })
}

fn drain_bounded(mut reader: impl Read, maximum: usize) -> Result<(Vec<u8>, bool), std::io::Error> {
    let mut retained = Vec::with_capacity(maximum.min(8_192));
    let mut buffer = [0_u8; 8_192];
    let mut truncated = false;
    loop {
        let read = reader.read(&mut buffer)?;
        if read == 0 {
            break;
        }
        let remaining = maximum.saturating_sub(retained.len());
        retained.extend_from_slice(&buffer[..read.min(remaining)]);
        truncated |= read > remaining;
    }
    Ok((retained, truncated))
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
fn cleanup_dispatcher_tree(child: &mut std::process::Child, registry: &mut ProcessRegistry) {
    let group = child.id();
    registry.refresh();
    let descendants = registry.owned_live_descendants(group);
    let _ = signal_group(group, libc::SIGKILL);
    for process in descendants {
        let _ = signal_identity(&process.identity, libc::SIGKILL);
    }
    let _ = child.kill();
    let _ = child.wait();
}

fn read_bounded_manifest(path: &Path) -> Result<String, CampaignError> {
    let file = fs::File::open(path).map_err(|error| CampaignError::Io {
        path: path.to_path_buf(),
        detail: error.to_string(),
    })?;
    let mut bytes = Vec::new();
    file.take(MAX_TASK_MANIFEST_BYTES + 1)
        .read_to_end(&mut bytes)
        .map_err(|error| CampaignError::Io {
            path: path.to_path_buf(),
            detail: error.to_string(),
        })?;
    if bytes.len() as u64 > MAX_TASK_MANIFEST_BYTES {
        return Err(CampaignError::InvalidManifest(format!(
            "manifest exceeds {MAX_TASK_MANIFEST_BYTES} bytes"
        )));
    }
    String::from_utf8(bytes)
        .map_err(|error| CampaignError::InvalidManifest(format!("manifest is not UTF-8: {error}")))
}

fn bounded_capture(bytes: &[u8], truncated: bool) -> String {
    let mut value = String::from_utf8_lossy(bytes).replace(['\n', '\r'], " ");
    if truncated {
        value.push_str("...<truncated>");
    }
    value
}

fn bounded_join(values: &[String], maximum: usize) -> String {
    let mut result = values
        .iter()
        .take(maximum)
        .cloned()
        .collect::<Vec<_>>()
        .join(", ");
    if values.len() > maximum {
        result.push_str(&format!(", ... ({} more)", values.len() - maximum));
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_runtime_config(repository: PathBuf) -> CampaignRuntimeConfig {
        CampaignRuntimeConfig {
            catalog: repository.join("Legacy/Benchmark2/Catalog.json"),
            dispatcher: repository.join(".lake/build/bin/benchmark_encoding_worker"),
            vampire: VampireWorkerCommand::new("vampire")
                .with_proof_casc_policy(crate::vampire::ProofCascPolicy::CLI_DEFAULT)
                .unwrap(),
            certification_bridge: CertificationBridgeCommand::new("python3", &repository),
            repository,
            run_name: "test-run".to_string(),
            selection: CampaignSelection::Task("Example0012".to_string()),
            per_task_limit: Duration::from_secs(60),
            campaign_limit: None,
            search_limit: Duration::from_secs(7),
            encoding_workers: 1,
            proposal_realization: ProposalRealization::ReferenceV3,
            telemetry_level: TelemetryLevel::Detailed,
            artifact_allowance_bytes: None,
            artifact_file_allowance: None,
            progress_interval: Some(Duration::from_secs(1)),
            output_format: OutputFormat::Normal,
            log_maintenance_history: false,
            fail_on_history_log_error: false,
        }
    }

    fn supported(values: &[&str]) -> BTreeSet<String> {
        values.iter().map(|value| (*value).to_string()).collect()
    }

    fn write_catalog(text: &str) -> PathBuf {
        let path = std::env::temp_dir().join(format!(
            "whiel-campaign-catalog-{}-{}.json",
            std::process::id(),
            std::thread::current().name().unwrap_or("unnamed")
        ));
        fs::write(&path, text).unwrap();
        path
    }

    #[test]
    fn persisted_symbolic_configuration_records_bulk_checks_as_disabled() {
        let repository = std::env::temp_dir().join(format!(
            "whiel-campaign-effective-config-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let run_root = repository.join("run");
        fs::create_dir_all(&run_root).unwrap();
        let config = test_runtime_config(repository.clone());
        let effective = effective_synthesis_configuration(&config).unwrap();

        assert_eq!(effective.verification.bulk_init_limit(), Duration::ZERO);
        assert_eq!(effective.verification.bulk_maint_limit(), Duration::ZERO);
        write_campaign_configuration(&run_root, &config, &effective, "task", "Example0012", 1)
            .unwrap();
        let persisted: serde_json::Value =
            serde_json::from_slice(&fs::read(run_root.join("campaign-config.json")).unwrap())
                .unwrap();
        assert_eq!(
            persisted["verification"]["bulk_init_limit_nanoseconds"],
            serde_json::json!(0)
        );
        assert_eq!(
            persisted["verification"]["bulk_maint_limit_nanoseconds"],
            serde_json::json!(0)
        );
        fs::remove_dir_all(repository).unwrap();
    }

    #[test]
    fn telemetry_off_does_not_disable_configured_periodic_progress() {
        let mut config = test_runtime_config(PathBuf::from("/repository"));
        config.telemetry_level = TelemetryLevel::Off;
        config.progress_interval = Some(Duration::from_millis(250));
        assert_eq!(
            live_progress_interval(&config),
            Some(Duration::from_millis(250))
        );
        config.progress_interval = None;
        assert_eq!(live_progress_interval(&config), None);
    }

    #[test]
    fn suite_selection_is_sorted_and_keeps_post_run_status() {
        let path = write_catalog(
            r#"{"cases":[
              {"canonicalId":"Example0002","currentClassification":"invalid","suites":["all"]},
              {"canonicalId":"Example0012","currentClassification":"valid","suites":["all"]},
              {"canonicalId":"Example0003","currentClassification":"unknown","suites":["other"]}
            ]}"#,
        );
        let selected = load_campaign_tasks(
            &path,
            &supported(&["Example0012", "Example0002", "Example0003"]),
            &CampaignSelection::Suite("all".to_string()),
        )
        .unwrap();
        fs::remove_file(path).unwrap();
        assert_eq!(
            selected
                .iter()
                .map(CampaignTask::canonical_id)
                .collect::<Vec<_>>(),
            ["Example0002", "Example0012"]
        );
        assert_eq!(
            selected[0].known_classification(),
            KnownClassification::Invalid
        );
    }

    #[test]
    fn suite_excludes_obstructed_root_but_explicit_task_remains_available() {
        let path = write_catalog(
            r#"{"cases":[
              {"canonicalId":"Example0012","currentClassification":"valid","suites":["all"]},
              {"canonicalId":"Example0002","root":"Obstructed","currentClassification":"unknown","suites":["all"]}
            ]}"#,
        );
        let supported = supported(&["Example0012", "Example0002"]);
        let suite = load_campaign_tasks(
            &path,
            &supported,
            &CampaignSelection::Suite("all".to_string()),
        )
        .unwrap();
        assert_eq!(
            suite
                .iter()
                .map(CampaignTask::canonical_id)
                .collect::<Vec<_>>(),
            ["Example0012"]
        );
        let explicit = load_campaign_tasks(
            &path,
            &supported,
            &CampaignSelection::Task("Example0002".to_string()),
        )
        .unwrap();
        fs::remove_file(path).unwrap();
        assert_eq!(explicit[0].canonical_id(), "Example0002");
    }

    #[test]
    fn selection_rejects_unknown_catalog_root() {
        let path = write_catalog(
            r#"{"cases":[
              {"canonicalId":"Example0012","root":"Elsewhere","currentClassification":"valid","suites":["all"]}
            ]}"#,
        );
        let error = load_campaign_tasks(
            &path,
            &supported(&["Example0012"]),
            &CampaignSelection::Suite("all".to_string()),
        )
        .unwrap_err();
        fs::remove_file(path).unwrap();
        assert!(error.to_string().contains("unexpected root"));
    }

    #[test]
    fn selection_keeps_novel_or_malformed_status_opaque_until_post_run_read() {
        let path = write_catalog(
            r#"{"cases":[
              {"canonicalId":"Example0012","currentClassification":"future-status","suites":["all"]},
              {"canonicalId":"Example0002","currentClassification":{"unexpected":true},"suites":["all"]},
              {"canonicalId":"Example0003","suites":["all"]}
            ]}"#,
        );
        let selected = load_campaign_tasks(
            &path,
            &supported(&["Example0012", "Example0002", "Example0003"]),
            &CampaignSelection::Suite("all".to_string()),
        )
        .expect("baseline metadata cannot block synthesis selection");
        fs::remove_file(path).unwrap();

        assert_eq!(selected.len(), 3);
        assert!(
            selected
                .iter()
                .all(|task| task.known_classification() == KnownClassification::Unknown)
        );
    }

    #[test]
    fn campaign_configuration_hashes_named_files_and_reports_path_only_programs() {
        let repository = std::env::temp_dir().join(format!(
            "whiel-campaign-identities-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let run_root = repository.join("run");
        fs::create_dir_all(&run_root).unwrap();
        let catalog = repository.join("catalog.json");
        let dispatcher = repository.join("dispatcher");
        let vampire = repository.join("vampire");
        let bridge = repository.join("bridge.py");
        fs::write(&catalog, b"catalog").unwrap();
        fs::write(&dispatcher, b"dispatcher").unwrap();
        fs::write(&vampire, b"vampire").unwrap();
        fs::write(&bridge, b"bridge").unwrap();

        let mut config = test_runtime_config(repository.clone());
        config.catalog = catalog.clone();
        config.dispatcher = dispatcher.clone();
        config.vampire = VampireWorkerCommand::new(&vampire)
            .with_proof_casc_policy(crate::vampire::ProofCascPolicy::CLI_DEFAULT)
            .unwrap();
        config.proposal_realization = ProposalRealization::FastV1;
        config.certification_bridge = CertificationBridgeCommand::new("python3", &repository)
            .with_arguments([bridge.clone().into_os_string()]);
        let effective = effective_synthesis_configuration(&config).unwrap();
        write_campaign_configuration(&run_root, &config, &effective, "task", "Example0012", 1)
            .unwrap();
        let persisted: serde_json::Value =
            serde_json::from_slice(&fs::read(run_root.join("campaign-config.json")).unwrap())
                .unwrap();

        assert_eq!(persisted["schema_version"], 6);
        assert_eq!(
            persisted["vampire_proof_policy"]["profile_id"],
            PROOF_CASC_PROFILE_ID,
        );
        assert_eq!(
            persisted["vampire_proof_policy"]["initial_casc_share_millionths"],
            250_000,
        );
        assert_eq!(
            persisted["vampire_proof_policy"]["retry_added_casc_share_millionths"],
            750_000,
        );
        assert_eq!(persisted["vampire_proof_policy"]["share_scale"], 1_000_000,);
        assert_eq!(
            persisted["vampire_proof_policy"]["allocation_formula"],
            "ceil((q_millionths*initial_ns+r_millionths*retry_added_ns)/share_scale)",
        );
        assert_eq!(
            persisted["vampire_proof_policy"]["allocation_rounding"],
            "one_combined_ceiling_to_nanoseconds",
        );
        assert_eq!(
            persisted["vampire_proof_policy"]["casc_schedule"],
            PROOF_CASC_SCHEDULE,
        );
        assert_eq!(persisted["vampire_proof_policy"]["casc_cores"], 1);
        assert_eq!(persisted["vampire_proof_policy"]["random_seed"], "1");
        assert_eq!(
            persisted["vampire_proof_policy"]["randomize_worker_seeds"],
            false,
        );
        assert_eq!(
            persisted["vampire_proof_policy"]["shuffle_schedule_repeats"],
            false,
        );
        assert_eq!(persisted["vampire_proof_policy"]["avatar"], true);
        assert_eq!(
            persisted["vampire_proof_policy"]["internal_limit_unit"],
            "deciseconds",
        );
        assert_eq!(
            persisted["vampire_proof_policy"]["internal_limit_derivation"],
            "ceil(shared-deadline-remaining-at-casc-launch/100ms)",
        );
        assert_eq!(
            persisted["vampire_proof_policy"]["external_deadline_authoritative"],
            true,
        );
        assert_eq!(persisted["proposal_realization_id"], "lean-fast-v1");
        assert_eq!(persisted["proposal_realization_version"], 1);
        assert_eq!(
            persisted["verification"]["init_first_attempt_limit_nanoseconds"],
            serde_json::json!([1_000_000_000_u64]),
        );
        assert_eq!(
            persisted["verification"]["init_attempt_limit_nanoseconds"],
            serde_json::json!([1_000_000_000_u64, 7_000_000_000_u64]),
        );
        for field in [
            "catalog_identity",
            "dispatcher_identity",
            "vampire_identity",
            "certification_bridge_identity",
        ] {
            assert_eq!(
                persisted[field]["sha256"].as_str().map(str::len),
                Some(64),
                "{field}"
            );
            assert!(persisted[field]["unavailable_reason"].is_null());
        }
        assert!(persisted["certification_executable_identity"]["sha256"].is_null());
        assert!(
            persisted["certification_executable_identity"]["unavailable_reason"]
                .as_str()
                .unwrap()
                .contains("PATH")
        );
        fs::remove_dir_all(repository).unwrap();
    }

    #[test]
    fn unsupported_selected_task_fails_closed() {
        let path = write_catalog(
            r#"{"cases":[
              {"canonicalId":"Example0012","currentClassification":"valid","suites":["all"]}
            ]}"#,
        );
        let error = load_campaign_tasks(
            &path,
            &BTreeSet::new(),
            &CampaignSelection::Suite("all".to_string()),
        )
        .unwrap_err();
        fs::remove_file(path).unwrap();
        assert!(
            error
                .to_string()
                .contains("absent from the compiled dispatcher")
        );
    }

    #[test]
    fn campaign_journal_persists_stable_json_lines_independent_of_terminal_format() {
        let path = std::env::temp_dir().join(format!(
            "whiel-campaign-journal-{}-{}.jsonl",
            std::process::id(),
            std::thread::current().name().unwrap_or("unnamed")
        ));
        let start = CampaignEvent::CampaignStart {
            schema_version: CAMPAIGN_SCHEMA_VERSION,
            selection_kind: "task".to_string(),
            selection_name: "Example0012".to_string(),
            task_count: 1,
            artifact_root: "artifacts/run".to_string(),
        };
        let progress = CampaignEvent::TaskProgress {
            schema_version: CAMPAIGN_SCHEMA_VERSION,
            canonical_id: "Example0012".to_string(),
            index: 1,
            total: 1,
            elapsed_milliseconds: 10,
            inv_epochs: 1,
            proposed_clauses: 2,
            initialized_clauses: 0,
            core_admissions: 0,
            highest_w_index: Some(0),
            highest_safe_fmb_frontier: None,
        };
        let mut journal = CampaignJournal::create(path.clone()).unwrap();
        let mut terminal = Vec::new();
        let mut reporter = Reporter::new(OutputFormat::Quiet, &mut terminal);
        emit(&mut reporter, &mut journal, &start).unwrap();
        emit(&mut reporter, &mut journal, &progress).unwrap();
        journal.finish().unwrap();

        let persisted = fs::read_to_string(&path).unwrap();
        let decoded = persisted
            .lines()
            .map(|line| serde_json::from_str::<CampaignEvent>(line).unwrap())
            .collect::<Vec<_>>();
        assert_eq!(decoded, vec![start, progress]);
        assert!(terminal.is_empty());
        fs::remove_file(path).unwrap();
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn bounded_dispatcher_timeout_kills_pipe_holding_descendant() {
        let pid_path = std::env::temp_dir().join(format!(
            "whiel-dispatch-descendant-{}-{}.pid",
            std::process::id(),
            std::thread::current().name().unwrap_or("unnamed")
        ));
        let script = format!(
            "sleep 60 & echo $! > '{}'; wait",
            pid_path.to_string_lossy()
        );
        let mut command = Command::new("/bin/sh");
        command.args(["-c", &script]);
        let started = Instant::now();
        let error = run_dispatcher_bounded(
            command,
            Duration::from_millis(100),
            "descendant cleanup test",
        )
        .unwrap_err();
        assert!(matches!(error, CampaignError::DispatcherTimeout { .. }));
        assert!(started.elapsed() < Duration::from_secs(3));
        let pid = fs::read_to_string(&pid_path)
            .unwrap()
            .trim()
            .parse::<i32>()
            .unwrap();
        assert_pid_stops(pid);
        fs::remove_file(pid_path).unwrap();
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn successful_dispatcher_cleans_lingering_pipe_holder() {
        let pid_path = std::env::temp_dir().join(format!(
            "whiel-dispatch-success-descendant-{}-{}.pid",
            std::process::id(),
            std::thread::current().name().unwrap_or("unnamed")
        ));
        let script = format!(
            "sleep 60 & echo $! > '{}'; exit 0",
            pid_path.to_string_lossy()
        );
        let mut command = Command::new("/bin/sh");
        command.args(["-c", &script]);
        let started = Instant::now();
        let output = run_dispatcher_bounded(
            command,
            Duration::from_secs(1),
            "successful descendant cleanup test",
        )
        .unwrap();
        assert!(output.status.success());
        assert!(started.elapsed() < Duration::from_secs(3));
        let pid = fs::read_to_string(&pid_path)
            .unwrap()
            .trim()
            .parse::<i32>()
            .unwrap();
        assert_pid_stops(pid);
        fs::remove_file(pid_path).unwrap();
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    fn assert_pid_stops(pid: i32) {
        let deadline = Instant::now() + Duration::from_secs(2);
        loop {
            let result = unsafe { libc::kill(pid, 0) };
            if result != 0 {
                break;
            }
            if Instant::now() >= deadline {
                let _ = unsafe { libc::kill(pid, libc::SIGKILL) };
                panic!("dispatcher descendant {pid} survived timeout cleanup");
            }
            thread::sleep(Duration::from_millis(10));
        }
    }
}
