//! `campaign certify --run DIR`: the deterministic half of a campaign,
//! run on its own.
//!
//! A run directory that stopped at acceptance holds, per input, the durable
//! record the search froze (`Core.json` or `Counterexample.json`) and the
//! envelope naming it (`Accepted.json`). This command turns those records
//! into published `Certificate/` trees by the standalone build path — the
//! same one `certificate build --core` and `--counterexample` take, called
//! as a library — and rewrites the run's own `result.json` and
//! `summary.json` to say so.
//!
//! A run directory is untrusted input to this command: it may have been
//! written by another machine, edited, or half-written by a crash. So:
//!
//! - **An input is certified only if a fresh check says so.** A standing
//!   `Certificate/` tree is never taken at its word from a status string.
//!   Its input's identity is re-checked and the tree is revalidated by the
//!   same [`revalidate_certificate_tree`] the inline publication uses — a
//!   fresh Lean build at the exact input declaration type with an
//!   exactly-std3 axiom audit — before its claim is allowed to stand. An
//!   empty or unnamed tree is never "certified".
//! - **It certifies this input.** The identity recorded at acceptance is
//!   checked against the input on disk before anything is built. A changed
//!   input gets its own status and no certificate: a tree rebuilt from
//!   another input's record would close a theorem about something else.
//! - **It is resumable, and it never destroys what it did not make.** An
//!   interrupted certify leaves only its own staging root behind and the
//!   next run clears it; a published tree is never removed to make room; an
//!   input the command never entered keeps the status it had.
//! - **One certify at a time per run directory.** The phase takes an
//!   exclusive lock on it, so two commands cannot race each other's staging,
//!   destinations and summary.
//!
//! [`revalidate_certificate_tree`]: crate::framework2::revalidate_certificate_tree

use std::io::Write;
use std::num::NonZeroUsize;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use serde_json::{Value, json};

use super::{CampaignRunError, SEARCH_SECONDS, host_memory_bytes, valid_input_id};
use crate::artifact::Retention;
use crate::certificate_cli::{
    BuildFromRecord, CertificateCliError, CertificateSource, RecordJobProfiles,
    RecordedCoreProfiles, build_certificate_from_record, fetch_worker_manifest_with_cancellation,
    load_build_source, resolve_or_build_worker_with_cancellation,
};
use crate::framework2::resource_limits::{
    CampaignResourceLimits, SpaceGuard, SpaceMonitor, WorkspaceLimitsGiven,
};
use crate::framework2::{
    ACCEPTED_RECORD_NAME, AcceptedVerdict, CertificateBundleShape, CertificateRevalidationRequest,
    PinnedLeancheckVampire, ProofSearchProfile, VALID_EVIDENCE_DIRECTORY, read_acceptance_envelope,
    revalidate_certificate_tree,
};
use crate::runtime::{CancellationToken, interrupt};

/// The staging parent one certify reserves under an input's directory.
///
/// Its own name, distinct from the search's `staging`: a certify that was
/// interrupted leaves this behind and the next one removes it, without ever
/// touching what the search reserved.
const CERTIFY_STAGING_DIRECTORY: &str = "certify-staging";

/// The exclusive lock one certification phase holds on a run directory.
///
/// A directory, because creating one is the atomic test-and-set every
/// filesystem offers. A second command finds it and refuses by name rather
/// than racing the first one's staging, destinations and summary.
const CERTIFY_LOCK_DIRECTORY: &str = ".certify-lock";

/// The published tree's name beside the record.
const CERTIFICATE_DIRECTORY: &str = "Certificate";

/// The input's own result file inside a run directory.
const RESULT_FILE: &str = "result.json";

/// Bytes of memory one concurrent certify job is assumed to need. Each job
/// is a Lean process elaborating a whole certificate module.
const MEMORY_PER_JOB_BYTES: u64 = 4 * 1024 * 1024 * 1024;

/// Memory left to the rest of the machine when the default is derived.
///
/// A default that claimed every gigabyte would leave nothing for the
/// operating system, the editor, or whatever else the operator is running,
/// and the reading below is total physical memory rather than free memory.
const MEMORY_HEADROOM_BYTES: u64 = 4 * 1024 * 1024 * 1024;

pub const CAMPAIGN_CERTIFY_USAGE: &str = "\
Usage:
  whiel-symbolic campaign certify --run DIR [OPTIONS]

Certifies every accepted, uncertified input of a campaign run directory from the records
its search left (Accepted.json plus Core.json or Counterexample.json), publishes
Certificate/ beside each record, and rewrites that input's result.json and the run's
summary.json.

  --run DIR                 Campaign run directory (required)
  --repo PATH               Repository root (default: current directory)
  --worker PATH             Existing fixed-ambient worker; otherwise build under watchdog
  --jobs N                  Inputs certified at once (default: min(cores / 2,
                            (memory - 4 GB) / 4 GB), at least 1). It is a hard knob on a
                            shared machine: each job is a whole Lean elaboration
  --certification-limit SECONDS
                            Certification allowance per input (default: 600)
  --certificate-solver-limit SECONDS
                            Positive whole seconds per Valid Leancheck job (default: 60)
  --retention certificate-only|all (default: certificate-only)
                            all keeps each valid build's solver evidence as
                            CertificateEvidence/ beside its certificate
  --workspace-bytes N       (default: 8589934592 live bytes under the run directory;
                            68719476736 under --retention all with no
                            explicit --workspace-* flag)
  --workspace-files N       (default: 100000 live regular files;
                            1000000 under --retention all with no
                            explicit --workspace-* flag)
  --minimum-free-bytes N    (default: 2147483648 per involved filesystem)
  --workspace-entries N     (default: 200000 visited entries per scan;
                            2000000 under --retention all with no
                            explicit --workspace-* flag)
  --workspace-directories N (default: 25000 directories per scan;
                            250000 under --retention all with no
                            explicit --workspace-* flag)
  -h, --help                Print this help

An input that already carries a Certificate/ tree its own result claims is re-checked
rather than trusted: its identity is compared against Accepted.json and the tree is
revalidated with a fresh Lean build before the claim is allowed to stand. An input whose
declarations changed since it was accepted is reported as input_changed and is not
certified. A published tree is never replaced or removed.

One certify runs at a time per run directory; a second is refused.

Exit codes: 0 every selected input certified; 2 arguments/bootstrap failure; 3 some input
is neither certified nor awaiting certification; 4 every input accepted and the
uncertified ones still awaiting certification; 130 interrupted.
";

#[derive(Clone, Debug)]
pub struct CampaignCertifyConfig {
    pub run: PathBuf,
    pub repository: PathBuf,
    pub worker: Option<PathBuf>,
    pub jobs: NonZeroUsize,
    pub retention: Retention,
    pub certification_limit: Duration,
    pub certificate_solver_limit_seconds: u64,
    /// The workspace allowances the phase runs under. A certification is
    /// the part of a campaign that spends gigabytes, so it is guarded the
    /// same way the search is.
    pub resource_limits: CampaignResourceLimits,
    /// Which of `resource_limits`' five workspace-guard fields the caller
    /// actually asked for, so a standalone certify can tell an explicit
    /// flag from the ordinary `--retention`-keyed default before it
    /// considers adopting the run's own recorded limits instead. See
    /// [`resolve_standalone_resource_limits`].
    pub workspace_limits_given: WorkspaceLimitsGiven,
}

pub fn parse_campaign_certify_arguments(
    arguments: &[String],
) -> Result<CampaignCertifyConfig, String> {
    let mut run = None;
    let mut repository = PathBuf::from(".");
    let mut worker = None;
    let mut jobs = None;
    let mut retention = Retention::CertificateOnly;
    let mut certification_limit = Duration::from_secs(600);
    let mut certificate_solver_limit_seconds = 60;
    let mut resource_limits = CampaignResourceLimits::default();
    let mut workspace_bytes_given = false;
    let mut workspace_files_given = false;
    let mut minimum_free_bytes_given = false;
    let mut workspace_entries_given = false;
    let mut workspace_directories_given = false;
    let mut index = 0;
    while index < arguments.len() {
        let option = arguments[index].as_str();
        match option {
            "--run" => run = Some(PathBuf::from(take(arguments, &mut index, option)?)),
            "--repo" => repository = PathBuf::from(take(arguments, &mut index, option)?),
            "--worker" => worker = Some(PathBuf::from(take(arguments, &mut index, option)?)),
            "--jobs" => {
                jobs = Some(
                    take(arguments, &mut index, option)?
                        .parse::<usize>()
                        .ok()
                        .and_then(NonZeroUsize::new)
                        .ok_or("--jobs requires a positive integer")?,
                )
            }
            "--certification-limit" => {
                certification_limit = seconds(take(arguments, &mut index, option)?, option)?
            }
            "--certificate-solver-limit" => {
                certificate_solver_limit_seconds = take(arguments, &mut index, option)?
                    .parse::<u64>()
                    .ok()
                    .filter(|seconds| *seconds > 0)
                    .ok_or("--certificate-solver-limit requires positive whole seconds")?;
            }
            "--workspace-bytes"
            | "--workspace-files"
            | "--minimum-free-bytes"
            | "--workspace-entries"
            | "--workspace-directories" => {
                let amount = take(arguments, &mut index, option)?
                    .parse::<u64>()
                    .ok()
                    .filter(|amount| *amount > 0)
                    .ok_or_else(|| format!("{option} requires a positive integer"))?;
                match option {
                    "--workspace-bytes" => {
                        resource_limits.workspace_bytes = amount;
                        workspace_bytes_given = true;
                    }
                    "--workspace-files" => {
                        resource_limits.workspace_files = amount;
                        workspace_files_given = true;
                    }
                    "--minimum-free-bytes" => {
                        resource_limits.minimum_free_bytes = amount;
                        minimum_free_bytes_given = true;
                    }
                    "--workspace-entries" => {
                        resource_limits.workspace_entries = amount;
                        workspace_entries_given = true;
                    }
                    "--workspace-directories" => {
                        resource_limits.workspace_directories = amount;
                        workspace_directories_given = true;
                    }
                    _ => unreachable!(),
                }
            }
            "--retention" => {
                retention = match take(arguments, &mut index, option)? {
                    "all" => Retention::All,
                    "certificate-only" => Retention::CertificateOnly,
                    _ => return Err("--retention requires all or certificate-only".into()),
                }
            }
            _ => {
                return Err(
                    "unknown campaign certify option; see `campaign certify --help`".into(),
                );
            }
        }
        index += 1;
    }
    // Under `--retention all`, an omitted `--workspace-*` flag takes the
    // raised default a retained run needs instead of the ordinary one;
    // `campaign run` applies the same rule for the same reason.
    if retention == Retention::All {
        if !workspace_bytes_given {
            resource_limits.workspace_bytes =
                crate::framework2::resource_limits::RETAINED_WORKSPACE_BYTES;
        }
        if !workspace_files_given {
            resource_limits.workspace_files =
                crate::framework2::resource_limits::RETAINED_WORKSPACE_FILES;
        }
        if !workspace_entries_given {
            resource_limits.workspace_entries =
                crate::framework2::resource_limits::RETAINED_WORKSPACE_ENTRIES;
        }
        if !workspace_directories_given {
            resource_limits.workspace_directories =
                crate::framework2::resource_limits::RETAINED_WORKSPACE_DIRECTORIES;
        }
    }
    Ok(CampaignCertifyConfig {
        run: run.ok_or("--run is required")?,
        repository,
        worker,
        jobs: jobs.unwrap_or_else(default_jobs),
        retention,
        certification_limit,
        certificate_solver_limit_seconds,
        resource_limits,
        workspace_limits_given: WorkspaceLimitsGiven {
            workspace_bytes: workspace_bytes_given,
            workspace_files: workspace_files_given,
            minimum_free_bytes: minimum_free_bytes_given,
            workspace_entries: workspace_entries_given,
            workspace_directories: workspace_directories_given,
        },
    })
}

fn take<'a>(arguments: &'a [String], index: &mut usize, option: &str) -> Result<&'a str, String> {
    let value = crate::cli::take_value(arguments, index, option)?;
    if value.starts_with('-') {
        return Err(format!("{option} requires a value"));
    }
    Ok(value)
}

fn seconds(value: &str, option: &str) -> Result<Duration, String> {
    let amount = value
        .parse::<f64>()
        .ok()
        .filter(|amount| amount.is_finite() && *amount > 0.0)
        .ok_or_else(|| format!("{option} requires positive finite seconds"))?;
    Duration::try_from_secs_f64(amount)
        .map_err(|_| format!("{option} is outside the supported duration range"))
}

/// How many inputs a machine certifies at once by default.
///
/// Two ceilings, whichever is lower: half the cores, because a job is also
/// a Vampire and a Lean elaboration rather than one thread, and the
/// machine's memory *less a whole job's headroom* divided by what one Lean
/// certificate elaboration needs. At least one, so a small machine still
/// certifies, slowly.
pub fn default_jobs() -> NonZeroUsize {
    let cores = super::host_parallelism() / 2;
    let by_memory = host_memory_bytes()
        .map(|bytes| {
            usize::try_from(bytes.saturating_sub(MEMORY_HEADROOM_BYTES) / MEMORY_PER_JOB_BYTES)
                .unwrap_or(usize::MAX)
        })
        .unwrap_or(1);
    NonZeroUsize::new(cores.min(by_memory).max(1)).expect("a floor of one is positive")
}

pub fn execute_campaign_certify_cli(
    mut config: CampaignCertifyConfig,
    mut output: impl Write,
) -> Result<i32, CampaignRunError> {
    config.repository = config
        .repository
        .canonicalize()
        .map_err(|error| format!("resolve repository: {error}"))?;
    if !config.repository.join("Whiel.lean").is_file() {
        return Err("not a Whiel repository".into());
    }
    config.run = config
        .run
        .canonicalize()
        .map_err(|error| format!("resolve run directory: {error}"))?;
    interrupt::clear();
    interrupt::install().map_err(|error| format!("install interruption handler: {error}"))?;
    certify_run_directory(&config, None, &mut output)
}

/// An exclusive claim on one run directory for the duration of a phase.
#[derive(Debug)]
struct RunDirectoryLock {
    path: PathBuf,
}

impl RunDirectoryLock {
    fn take(run: &Path) -> Result<Self, CampaignRunError> {
        let path = run.join(CERTIFY_LOCK_DIRECTORY);
        std::fs::create_dir(&path).map_err(|error| CampaignRunError {
            exit_code: super::CAMPAIGN_ARGUMENT_FAILURE,
            detail: if error.kind() == std::io::ErrorKind::AlreadyExists {
                format!(
                    "another certification already holds {}; wait for it to finish, or remove \
                     that directory if no command is running",
                    path.display()
                )
            } else {
                format!("claim {}: {error}", path.display())
            },
        })?;
        Ok(Self { path })
    }
}

impl Drop for RunDirectoryLock {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir(&self.path);
    }
}

/// The certification phase over one already-resolved run directory.
///
/// `campaign certify` is this with its own bootstrap in front of it, and
/// `campaign run --certify deferred` is this called once after the last
/// input's search: one phase, so the two modes cannot diverge. A caller
/// that already owns a workspace guard passes it in rather than starting a
/// second one over the same tree.
pub(super) fn certify_run_directory(
    config: &CampaignCertifyConfig,
    inherited_space: Option<&Arc<SpaceGuard>>,
    output: &mut impl Write,
) -> Result<i32, CampaignRunError> {
    let inner = crate::framework2::CertificateBuildRequest::configured_solver_jobs(
        NonZeroUsize::new(1).expect("one is nonzero"),
    )?;
    validate_certification_concurrency(config.jobs, inner)?;
    let run = config.run.as_path();
    let repository = config.repository.as_path();
    let summary_path = run.join("summary.json");
    if !summary_path.is_file() {
        return Err(CampaignRunError {
            exit_code: super::CAMPAIGN_ARGUMENT_FAILURE,
            detail: format!("{} is not a campaign run directory", run.display()),
        });
    }
    let _lock = RunDirectoryLock::take(run)?;
    let external = CancellationToken::new();
    // A certification spends gigabytes per input, so it is guarded like the
    // search is: the monitor cancels this phase's own root, which every
    // bound worker, solver and Lean child already reads. A standalone
    // certify (no inherited guard) resolves its own limits first, since
    // those may need to be adopted from the run's own recorded settings.
    let (space, _monitor) = match inherited_space {
        Some(space) => (Arc::clone(space), None),
        None => {
            let resource_limits = resolve_standalone_resource_limits(config, run, output)?;
            let space = SpaceGuard::new(&resource_limits, run.to_path_buf(), external.clone());
            let monitor = SpaceMonitor::start(Arc::clone(&space))
                .map_err(|error| format!("start the certification workspace guard: {error}"))?;
            (space, Some(monitor))
        }
    };
    let mut summary: Value = read_json(&summary_path)?;
    let (pending, refused) = pending_inputs(run)?;
    for outcome in &refused {
        report(output, outcome);
        rewrite_result(run, outcome)?;
    }
    if pending.is_empty() {
        writeln!(
            output,
            "no accepted input to certify or re-check in {}",
            run.display()
        )
        .map_err(|error| error.to_string())?;
    } else {
        // One worker for the whole phase. Resolving it builds the Lean
        // prerequisites under the watchdog, which is the expensive part and
        // has nothing to do with which input is being certified.
        let worker = resolve_or_build_worker_with_cancellation(
            repository,
            config.worker.as_deref(),
            &external,
        )
        .map_err(|detail| CampaignRunError {
            exit_code: super::CAMPAIGN_ARGUMENT_FAILURE,
            detail,
        })?;
        let pinned =
            PinnedLeancheckVampire::from_lock(repository).map_err(|error| CampaignRunError {
                exit_code: super::CAMPAIGN_ARGUMENT_FAILURE,
                detail: format!("resolve the pinned leancheck Vampire: {error}"),
            })?;
        let outcomes = certify_pending(
            config, run, repository, &worker, &pinned, &space, pending, &external,
        );
        for outcome in &outcomes {
            report(output, outcome);
        }
    }
    if let Some(detail) = space.failure() {
        let _ = writeln!(output, "{detail}");
    }
    apply_to_summary(&mut summary, run)?;
    write_json(&summary_path, &summary)?;
    // The workspace guard stops the phase through the same token a signal
    // does, but a refused guard is a resource failure of this run, not an
    // operator's interruption, and must not exit as one.
    let interrupted = external.is_cancelled() && space.failure().is_none();
    Ok(exit_code(&summary, interrupted))
}

fn validate_certification_concurrency(
    outer: NonZeroUsize,
    inner: NonZeroUsize,
) -> Result<(), String> {
    if outer.get() > 1 && inner.get() > 1 {
        return Err("campaign certification requires --jobs 1 when WHIEL_CERTIFICATE_SOLVER_JOBS exceeds one".into());
    }
    Ok(())
}

fn report(output: &mut impl Write, outcome: &CertifyOutcome) {
    let _ = writeln!(
        output,
        "{}: {}{}",
        outcome.id,
        outcome.status,
        outcome
            .detail
            .as_ref()
            .map(|detail| format!(" ({detail})"))
            .unwrap_or_default()
    );
}

/// What this command intends to do with one accepted input.
enum CertifyIntent {
    /// No tree stands here: build one from the record.
    Build,
    /// A tree stands here and the input's own result claims it. Re-check
    /// the identity and revalidate the tree before letting that claim
    /// stand; nothing is built and nothing is removed.
    Recheck {
        module: String,
        theorem: String,
        shape: CertificateBundleShape,
    },
}

/// One input the command intends to certify or to re-check.
struct PendingInput {
    id: String,
    directory: PathBuf,
    verdict: AcceptedVerdict,
    task_identity: Value,
    scope_identity_sha256: Option<String>,
    /// The per-job profile labels this input's acceptance envelope
    /// recorded; absent exactly for an invalid verdict, which has no Core
    /// and no solver jobs to label.
    core_profiles: Option<RecordedCoreProfiles>,
    intent: CertifyIntent,
}

/// What became of one input.
struct CertifyOutcome {
    id: String,
    status: &'static str,
    detail: Option<String>,
    /// Named relative to the input's own directory, never by machine
    /// location: a run directory is certified wherever it has been copied to.
    certificate: Option<String>,
    record: Option<String>,
    axioms: Option<Vec<String>>,
    certificate_module: Option<String>,
    certificate_theorem: Option<String>,
}

impl CertifyOutcome {
    fn refused(id: &str, status: &'static str, detail: String) -> Self {
        Self {
            id: id.to_owned(),
            status,
            detail: Some(detail),
            certificate: None,
            record: None,
            axioms: None,
            certificate_module: None,
            certificate_theorem: None,
        }
    }
}

/// Every accepted input of the run, with what this command will do to it,
/// plus the ones it refuses before binding anything.
///
/// Reading the whole directory first is what makes the phase's shape
/// knowable before a worker is built. Nothing here decides that an input is
/// certified: a standing tree only earns a `Recheck`, which still has to
/// pass a fresh revalidation.
fn pending_inputs(
    run: &Path,
) -> Result<(Vec<PendingInput>, Vec<CertifyOutcome>), CampaignRunError> {
    let mut pending = Vec::new();
    let mut refused = Vec::new();
    let mut entries = std::fs::read_dir(run)
        .map_err(|error| format!("read {}: {error}", run.display()))?
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| error.to_string())?;
    entries.sort_by_key(std::fs::DirEntry::file_name);
    for entry in entries {
        let Some(id) = entry.file_name().to_str().map(str::to_owned) else {
            continue;
        };
        if !valid_input_id(&id) {
            continue;
        }
        let directory = entry.path();
        // The same guard the search applies to its own input directory: this
        // command builds under it, and promotes a tree and a record into it,
        // so it must own the directory rather than follow a link out of the
        // run tree.
        match std::fs::symlink_metadata(&directory) {
            Ok(metadata) if metadata.is_dir() => {}
            Ok(_) => {
                refused.push(CertifyOutcome::refused(
                    &id,
                    "certification_failed",
                    "a run directory entry must be an owned directory, not a symlink".into(),
                ));
                continue;
            }
            Err(error) => {
                refused.push(CertifyOutcome::refused(
                    &id,
                    "certification_failed",
                    format!("inspect {}: {error}", directory.display()),
                ));
                continue;
            }
        }
        let envelope_path = directory.join(ACCEPTED_RECORD_NAME);
        if !envelope_path.is_file() {
            // A record without its envelope is the half of an interrupted
            // acceptance that cannot be read; say so rather than passing
            // over the directory in silence.
            for verdict in [AcceptedVerdict::Valid, AcceptedVerdict::Invalid] {
                if directory.join(verdict.record_name()).is_file() {
                    refused.push(CertifyOutcome::refused(
                        &id,
                        "certification_failed",
                        format!(
                            "{} stands here without its {ACCEPTED_RECORD_NAME} envelope, so what \
                             it records cannot be checked against this input",
                            verdict.record_name()
                        ),
                    ));
                    break;
                }
            }
            continue;
        }
        let envelope = read_acceptance_envelope(&envelope_path).map_err(CampaignRunError::from)?;
        let verdict = envelope.verdict();
        let scope_identity_sha256 = envelope
            .core()
            .and_then(|core| core.get("scope_identity_sha256"))
            .and_then(Value::as_str)
            .map(str::to_owned);
        // A valid acceptance whose recorded labels cannot be read is
        // refused here rather than rebuilt under a guessed profile.
        let core_profiles = match envelope.core() {
            Some(core) => match RecordedCoreProfiles::from_frozen_payload(core) {
                Ok(recorded) => Some(recorded),
                Err(detail) => {
                    refused.push(CertifyOutcome::refused(
                        &id,
                        "certification_failed",
                        format!("{ACCEPTED_RECORD_NAME}: {detail}"),
                    ));
                    continue;
                }
            },
            None => None,
        };
        let intent = if directory.join(CERTIFICATE_DIRECTORY).exists() {
            let result = recorded_result(&directory);
            let status = result
                .as_ref()
                .and_then(|value| value.get("status"))
                .and_then(Value::as_str)
                .unwrap_or("absent")
                .to_owned();
            let module = result
                .as_ref()
                .and_then(|value| value.get("certificate_module"))
                .and_then(Value::as_str)
                .map(str::to_owned);
            let theorem = result
                .as_ref()
                .and_then(|value| value.get("certificate_theorem"))
                .and_then(Value::as_str)
                .map(str::to_owned);
            match (status.as_str(), module, theorem) {
                ("valid" | "invalid", Some(module), Some(theorem)) => CertifyIntent::Recheck {
                    module,
                    theorem,
                    shape: match verdict {
                        AcceptedVerdict::Valid => CertificateBundleShape::Valid,
                        AcceptedVerdict::Invalid => CertificateBundleShape::Invalid,
                    },
                },
                ("valid" | "invalid", _, _) => {
                    refused.push(CertifyOutcome::refused(
                        &id,
                        "certification_unchecked",
                        format!(
                            "a {CERTIFICATE_DIRECTORY} tree stands here but its own result names \
                             no certificate module or theorem, so it cannot be revalidated; \
                             re-run this input's search, or remove the tree to rebuild it"
                        ),
                    ));
                    continue;
                }
                _ => {
                    refused.push(CertifyOutcome::refused(
                        &id,
                        "certification_unchecked",
                        format!(
                            "a {CERTIFICATE_DIRECTORY} tree stands here but the recorded status \
                             is {status}; a published tree is never replaced or removed"
                        ),
                    ));
                    continue;
                }
            }
        } else {
            CertifyIntent::Build
        };
        pending.push(PendingInput {
            id,
            directory,
            verdict,
            task_identity: envelope.task_identity().clone(),
            scope_identity_sha256,
            core_profiles,
            intent,
        });
    }
    Ok((pending, refused))
}

/// One input's own recorded result, when it has a readable one.
fn recorded_result(directory: &Path) -> Option<Value> {
    let bytes = std::fs::read(directory.join(RESULT_FILE)).ok()?;
    serde_json::from_slice(&bytes).ok()
}

/// Certify the pending inputs, at most `--jobs` of them at once.
///
/// Each job owns a thread and a single-threaded runtime of its own, and so
/// its own sequential Lean chain: one certificate build holds a worker
/// pool, a Vampire and a `lean` elaboration that are not interchangeable
/// between jobs, and a build future is bound to the thread it started on.
/// The resolved worker, the pinned Vampire, the workspace guard and the
/// repository are the parts every job shares, and they are resolved once
/// before any job starts.
///
/// Each job writes its own `result.json` as soon as it finishes, so an
/// interrupted phase keeps every input it did complete.
#[allow(clippy::too_many_arguments)]
fn certify_pending(
    config: &CampaignCertifyConfig,
    run: &Path,
    repository: &Path,
    worker: &Path,
    pinned: &PinnedLeancheckVampire,
    space: &Arc<SpaceGuard>,
    pending: Vec<PendingInput>,
    external: &CancellationToken,
) -> Vec<CertifyOutcome> {
    let queue = Mutex::new(std::collections::VecDeque::from(pending));
    let outcomes = Mutex::new(Vec::new());
    let watching = AtomicBool::new(true);
    std::thread::scope(|scope| {
        // One observer turns the process signal into this phase's own
        // cancellation, which every bound worker and solver already reads.
        let watcher = scope.spawn(|| {
            while watching.load(Ordering::Acquire) {
                if interrupt::requested().is_some() {
                    external.cancel();
                    return;
                }
                std::thread::sleep(Duration::from_millis(100));
            }
        });
        let mut workers = Vec::new();
        for _ in 0..config.jobs.get() {
            workers.push(scope.spawn(|| {
                let runtime = match tokio::runtime::Builder::new_current_thread()
                    .enable_all()
                    .build()
                {
                    Ok(runtime) => runtime,
                    Err(error) => {
                        let _ = writeln!(
                            std::io::stderr(),
                            "error: create a certify job runtime: {error}"
                        );
                        return;
                    }
                };
                loop {
                    let Some(input) = queue.lock().expect("the certify queue").pop_front() else {
                        return;
                    };
                    // An input this phase never entered keeps the status it
                    // already has. Overwriting a `valid_uncertified` with
                    // `interrupted` would erase the very fact the acceptance
                    // record exists to state.
                    if external.is_cancelled() {
                        continue;
                    }
                    let outcome = runtime.block_on(certify_one(
                        config, repository, worker, pinned, space, &input, external,
                    ));
                    // Durable before the phase ends: a crash after this
                    // keeps the work rather than repeating it.
                    if let Err(error) = rewrite_result(run, &outcome) {
                        let _ = writeln!(
                            std::io::stderr(),
                            "error: record {}'s result: {error}",
                            outcome.id
                        );
                    }
                    outcomes.lock().expect("the certify outcomes").push(outcome);
                }
            }));
        }
        for worker in workers {
            let _ = worker.join();
        }
        // The observer is released only once no job is left to cancel, and
        // joined here so the scope does not wait out its whole poll.
        watching.store(false, Ordering::Release);
        let _ = watcher.join();
    });
    let mut outcomes = outcomes.into_inner().expect("the certify outcomes");
    outcomes.sort_by(|left, right| left.id.cmp(&right.id));
    outcomes
}

#[allow(clippy::too_many_arguments)]
async fn certify_one(
    config: &CampaignCertifyConfig,
    repository: &Path,
    worker: &Path,
    pinned: &PinnedLeancheckVampire,
    space: &Arc<SpaceGuard>,
    input: &PendingInput,
    external: &CancellationToken,
) -> CertifyOutcome {
    let failed =
        |status: &'static str, detail: String| CertifyOutcome::refused(&input.id, status, detail);
    // Leftovers of an interrupted certify are this command's own; removing
    // them on entry is what makes a resumed run a fresh one.
    let staging_root = input.directory.join(CERTIFY_STAGING_DIRECTORY);
    if staging_root.exists()
        && let Err(error) = std::fs::remove_dir_all(&staging_root)
    {
        return failed(
            "certification_failed",
            format!("clear {}: {error}", staging_root.display()),
        );
    }
    if let Err(error) = std::fs::create_dir_all(&staging_root) {
        return failed(
            "certification_failed",
            format!("reserve {}: {error}", staging_root.display()),
        );
    }
    let outcome = match &input.intent {
        CertifyIntent::Recheck {
            module,
            theorem,
            shape,
        } => {
            recheck_one(
                repository,
                worker,
                input,
                module,
                theorem,
                *shape,
                &staging_root,
                external,
            )
            .await
        }
        CertifyIntent::Build => {
            build_one(
                config,
                repository,
                worker,
                pinned,
                space,
                input,
                &staging_root,
                external,
            )
            .await
        }
    };
    let _ = std::fs::remove_dir_all(&staging_root);
    outcome
}

/// Re-check a tree that is already standing, without building anything.
///
/// The identity recorded at acceptance is compared against the input on
/// disk, and then the tree goes through the very revalidation the inline
/// publication performs: a fresh Lean build of every module from source, the
/// theorem elaborated at the exact `Input.lean` declaration type, and an
/// axiom closure audited to exactly std3. A tree that does not pass is
/// reported and left exactly where it is.
#[allow(clippy::too_many_arguments)]
async fn recheck_one(
    repository: &Path,
    worker: &Path,
    input: &PendingInput,
    module: &str,
    theorem: &str,
    shape: CertificateBundleShape,
    staging_root: &Path,
    external: &CancellationToken,
) -> CertifyOutcome {
    let failed =
        |status: &'static str, detail: String| CertifyOutcome::refused(&input.id, status, detail);
    let descriptor =
        match fetch_worker_manifest_with_cancellation(worker, repository, &input.id, external) {
            Ok(descriptor) => descriptor,
            Err(detail) => return failed("certification_unchecked", detail),
        };
    let (identity, scope_digest) =
        match crate::framework2::task_identity_from_worker_manifest(&descriptor) {
            Ok(named) => named,
            Err(detail) => return failed("certification_unchecked", detail),
        };
    if identity != input.task_identity {
        return failed(
            "input_changed",
            format!(
                "{} is no longer the input this certificate was built for; recorded {}, found {}",
                input.id, input.task_identity, identity
            ),
        );
    }
    if let Some(expected) = &input.scope_identity_sha256
        && expected != &scope_digest
    {
        return failed(
            "input_changed",
            format!(
                "{}'s scope no longer matches the one this certificate was built under; \
                 recorded {expected}, found {scope_digest}",
                input.id
            ),
        );
    }
    let namespace = identity
        .get("namespace")
        .and_then(Value::as_str)
        .unwrap_or_default()
        .to_owned();
    let tree = input.directory.join(CERTIFICATE_DIRECTORY);
    match revalidate_certificate_tree(CertificateRevalidationRequest {
        tree: &tree,
        canonical_id: &input.id,
        input_namespace: &namespace,
        certificate_module: module,
        certificate_theorem: theorem,
        shape,
        repository_root: repository.to_path_buf(),
        staging_root: staging_root.to_path_buf(),
        cancellation: external,
    })
    .await
    {
        Ok(revalidation) => CertifyOutcome {
            id: input.id.clone(),
            status: match input.verdict {
                AcceptedVerdict::Valid => "valid",
                AcceptedVerdict::Invalid => "invalid",
            },
            detail: None,
            certificate: Some(CERTIFICATE_DIRECTORY.to_owned()),
            record: Some(input.verdict.record_name().to_owned()),
            axioms: Some(revalidation.axioms.clone()),
            certificate_module: Some(module.to_owned()),
            certificate_theorem: Some(theorem.to_owned()),
        },
        Err(error) => failed(
            "certification_unchecked",
            format!("the standing certificate tree did not revalidate: {error}"),
        ),
    }
}

/// Which profile each job of this input's rebuild runs under.
///
/// The labels the run's own freeze closed over, read from the acceptance
/// envelope's frozen Core payload. `Core.json` carries a clause's level and
/// source only, so the envelope beside it is where a deferred certification
/// learns which profile proved each condition — and a condition the
/// portfolio proved is not in general reachable by the direct strategy
/// inside a certificate job's allowance. An invalid verdict has no Core and
/// no solver jobs to label.
fn record_job_profiles(input: &PendingInput) -> RecordJobProfiles {
    match &input.core_profiles {
        Some(recorded) => RecordJobProfiles::Recorded(recorded.clone()),
        None => RecordJobProfiles::Constant(ProofSearchProfile::Direct),
    }
}

/// Build and publish one certificate from the record beside it.
#[allow(clippy::too_many_arguments)]
async fn build_one(
    config: &CampaignCertifyConfig,
    repository: &Path,
    worker: &Path,
    pinned: &PinnedLeancheckVampire,
    space: &Arc<SpaceGuard>,
    input: &PendingInput,
    staging_root: &Path,
    external: &CancellationToken,
) -> CertifyOutcome {
    let failed =
        |status: &'static str, detail: String| CertifyOutcome::refused(&input.id, status, detail);
    let record = input.directory.join(input.verdict.record_name());
    if !record.is_file() {
        return failed(
            "certification_failed",
            format!("{} is missing", record.display()),
        );
    }
    let source = match input.verdict {
        AcceptedVerdict::Valid => CertificateSource::Core(record.clone()),
        AcceptedVerdict::Invalid => CertificateSource::Counterexample(record.clone()),
    };
    let loaded = match load_build_source(&source) {
        Ok(loaded) => loaded,
        Err(detail) => return failed("certification_failed", detail),
    };
    let descriptor =
        match fetch_worker_manifest_with_cancellation(worker, repository, &input.id, external) {
            Ok(descriptor) => descriptor,
            Err(detail) => return failed("certification_failed", detail),
        };
    let evidence = match (input.verdict, config.retention) {
        (AcceptedVerdict::Valid, Retention::All) => {
            Some(input.directory.join(VALID_EVIDENCE_DIRECTORY))
        }
        _ => None,
    };
    let request = BuildFromRecord {
        repository_root: repository.to_path_buf(),
        worker_path: worker.to_path_buf(),
        descriptor,
        input: input.id.clone(),
        source: loaded,
        profile: record_job_profiles(input),
        time_limit_seconds: config.certificate_solver_limit_seconds,
        evidence,
        validation_limit: crate::framework2::DEFAULT_COUNTEREXAMPLE_VALIDATION_LIMIT,
        staging_root: staging_root.to_path_buf(),
        destination: input.directory.join(CERTIFICATE_DIRECTORY),
        pinned: pinned.clone(),
        expected_task_identity: Some(input.task_identity.clone()),
        expected_scope_identity_sha256: input.scope_identity_sha256.clone(),
        space_guard: Some(Arc::clone(space)),
        // The allowance and the interruption are one mechanism inside the
        // build, so a stop reaches the Lean and Vampire children it owns
        // instead of merely abandoning the future that owns them.
        cancellation: external.clone(),
        certification_limit: Some(config.certification_limit),
    };
    match build_certificate_from_record(request).await {
        Err(CertificateCliError::Stopped { deadline, detail }) => failed(
            if deadline {
                "certification_timeout"
            } else if space.failure().is_some() {
                // The guard stops the build through the same token a signal
                // does; the input was stopped for space, not by an operator.
                "resource_exhausted"
            } else {
                "interrupted"
            },
            detail,
        ),
        Err(CertificateCliError::InputChanged(detail)) => failed("input_changed", detail),
        Err(error) => failed("certification_failed", error.detail()),
        Ok(outcome) => CertifyOutcome {
            id: input.id.clone(),
            status: match input.verdict {
                AcceptedVerdict::Valid => "valid",
                AcceptedVerdict::Invalid => "invalid",
            },
            detail: None,
            certificate: Some(CERTIFICATE_DIRECTORY.to_owned()),
            record: Some(input.verdict.record_name().to_owned()),
            axioms: Some(outcome.receipt.axioms.clone()),
            certificate_module: Some(outcome.receipt.certificate_module.clone()),
            certificate_theorem: Some(outcome.receipt.certificate_theorem.clone()),
        },
    }
}

/// Rewrite one input's `result.json`, keeping everything the run recorded
/// about its search and replacing only what certification decides.
///
/// A file that is missing or will not parse is rebuilt rather than treated
/// as fatal: the acceptance envelope beside it is the authority on what the
/// search found, and one truncated result must not stop a whole run
/// directory from being certified.
fn rewrite_result(run: &Path, outcome: &CertifyOutcome) -> Result<(), CampaignRunError> {
    let directory = run.join(&outcome.id);
    let path = directory.join(RESULT_FILE);
    let mut result = recorded_result(&directory)
        .filter(Value::is_object)
        .unwrap_or_else(|| rebuilt_result(&directory, &outcome.id));
    let Some(object) = result.as_object_mut() else {
        return Err(format!("{} is not a JSON object", path.display()).into());
    };
    object.insert("status".into(), json!(outcome.status));
    match &outcome.detail {
        Some(detail) => {
            object.insert("detail".into(), json!(detail));
        }
        None => {
            object.remove("detail");
        }
    }
    if let Some(certificate) = &outcome.certificate {
        object.insert("certificate".into(), json!(certificate));
    }
    if let Some(axioms) = &outcome.axioms {
        object.insert("axioms".into(), json!(axioms));
    }
    // The module and theorem a later re-check revalidates the tree with. A
    // tree whose result does not name them cannot be checked at all, which
    // is why they are recorded next to the claim they support.
    if let Some(module) = &outcome.certificate_module {
        object.insert("certificate_module".into(), json!(module));
    }
    if let Some(theorem) = &outcome.certificate_theorem {
        object.insert("certificate_theorem".into(), json!(theorem));
    }
    if outcome.status == "invalid"
        && let Some(record) = &outcome.record
    {
        object.insert("counterexample".into(), json!(record));
    }
    write_json(&path, &result)
}

/// The minimum result an input can be given back when its own was lost.
///
/// It states what the acceptance envelope still proves — the input, its
/// verdict and the record naming it — rather than inventing controls the
/// run no longer has.
fn rebuilt_result(directory: &Path, id: &str) -> Value {
    let mut result = json!({"input": id, "schema_version": 3});
    if let Ok(envelope) = read_acceptance_envelope(&directory.join(ACCEPTED_RECORD_NAME))
        && let Some(object) = result.as_object_mut()
    {
        object.insert("record".into(), json!(envelope.verdict().record_name()));
        object.insert("accepted".into(), json!(ACCEPTED_RECORD_NAME));
        // The search's own duration survives a lost result, because the
        // envelope recorded it at acceptance. Certification never measures
        // search time and never overwrites it.
        if let Some(seconds) = envelope.search_elapsed_seconds() {
            object.insert(SEARCH_SECONDS.into(), json!(seconds));
        }
    }
    result
}

/// Re-read every input's `result.json` into the run summary and recompute
/// the two whole-run booleans from them.
///
/// Reading them back rather than patching the summary in memory is what
/// makes a second certify of the same directory agree with the first: the
/// results on disk are the record, and the summary is a view of them.
fn apply_to_summary(summary: &mut Value, run: &Path) -> Result<(), CampaignRunError> {
    let Some(object) = summary.as_object_mut() else {
        return Err("the run summary is not a JSON object".into());
    };
    let selected = object
        .get("selected_inputs")
        .and_then(Value::as_array)
        .cloned()
        .unwrap_or_default();
    let mut results = Vec::new();
    let mut accepted = 0;
    for input in &selected {
        let Some(id) = input.as_str() else { continue };
        let directory = run.join(id);
        if directory.join(ACCEPTED_RECORD_NAME).is_file() {
            accepted += 1;
        }
        if let Some(result) = recorded_result(&directory) {
            results.push(result);
        }
    }
    let complete = object
        .get("unrun_inputs")
        .and_then(Value::as_array)
        .is_none_or(|unrun| unrun.is_empty())
        && object.get("interrupted") != Some(&json!(true))
        && object.get("resource_failure").is_none_or(Value::is_null)
        && results.len() == selected.len();
    let all_certified = complete
        && results
            .iter()
            .all(|result| matches!(result["status"].as_str(), Some("valid" | "invalid")));
    // Acceptance is a fact about the search, recorded on disk, so it is read
    // from the records rather than inferred from a status string: an input
    // whose certification failed was still accepted, and that is exactly
    // what this milestone made visible.
    let all_accepted = complete && accepted == selected.len();
    object.insert("results".into(), json!(results));
    object.insert("all_certified".into(), json!(all_certified));
    object.insert("all_accepted".into(), json!(all_accepted));
    Ok(())
}

fn exit_code(summary: &Value, interrupted: bool) -> i32 {
    if interrupted {
        return 130;
    }
    if summary["all_certified"] == json!(true) {
        return 0;
    }
    // The uncertified code says "accepted, and certification is still to
    // come". It is therefore only for inputs a later certification could
    // still finish. A refusal that re-running cannot resolve — a changed
    // input, a tree that will not revalidate, a build that failed — is a
    // failure of this run and takes the failure code, so nothing reads it as
    // work merely outstanding.
    let awaiting = summary["results"].as_array().is_some_and(|results| {
        results.iter().all(|result| {
            matches!(
                result["status"].as_str(),
                Some("valid" | "invalid" | "valid_uncertified" | "invalid_uncertified")
            )
        })
    });
    if summary["all_accepted"] == json!(true) && awaiting {
        return super::CAMPAIGN_UNCERTIFIED;
    }
    super::CAMPAIGN_FAILED
}

/// The workspace guard a standalone `campaign certify --run DIR` starts
/// under, when it is not inheriting one from `campaign run --certify
/// deferred`.
///
/// A run's own settings recorded whatever workspace allowances that run
/// actually ran under — raised, for instance, by that run's own
/// `--retention all` — but `campaign certify` parses its own `--retention`
/// and workspace flags independently, defaulting to the small
/// `certificate-only` figures. A certify invoked with no `--workspace-*` /
/// `--minimum-free-bytes` flag at all is not asking for those small
/// figures; it is asking for whatever the run needs. So, field by field: an
/// explicit flag always wins; an omitted one adopts the run's own recorded
/// limit; and if the run's settings cannot be read at all, every omitted
/// field falls back to the ordinary `--retention`-keyed default already
/// resolved by [`parse_campaign_certify_arguments`], and this says so on
/// `output` rather than failing silently open or closed.
fn resolve_standalone_resource_limits(
    config: &CampaignCertifyConfig,
    run: &Path,
    output: &mut impl Write,
) -> Result<CampaignResourceLimits, CampaignRunError> {
    let given = &config.workspace_limits_given;
    if given.all_given() {
        return Ok(config.resource_limits.clone());
    }
    match recorded_resource_limits(run) {
        Ok(recorded) => {
            let mut limits = config.resource_limits.clone();
            if !given.workspace_bytes {
                limits.workspace_bytes = recorded.workspace_bytes;
            }
            if !given.workspace_files {
                limits.workspace_files = recorded.workspace_files;
            }
            if !given.minimum_free_bytes {
                limits.minimum_free_bytes = recorded.minimum_free_bytes;
            }
            if !given.workspace_entries {
                limits.workspace_entries = recorded.workspace_entries;
            }
            if !given.workspace_directories {
                limits.workspace_directories = recorded.workspace_directories;
            }
            writeln!(
                output,
                "workspace guard: adopted this run's own recorded limits from {}",
                run.join("campaign-settings.json").display()
            )
            .map_err(|error| error.to_string())?;
            Ok(limits)
        }
        Err(detail) => {
            writeln!(
                output,
                "workspace guard: could not read this run's recorded limits ({detail}); \
                 using the --retention-keyed default instead",
            )
            .map_err(|error| error.to_string())?;
            Ok(config.resource_limits.clone())
        }
    }
}

/// The run's own `controls.resource_limits`, as `campaign run` wrote it to
/// `campaign-settings.json`.
fn recorded_resource_limits(run: &Path) -> Result<CampaignResourceLimits, String> {
    let path = run.join("campaign-settings.json");
    let bytes =
        std::fs::read(&path).map_err(|error| format!("read {}: {error}", path.display()))?;
    let settings: Value = serde_json::from_slice(&bytes)
        .map_err(|error| format!("parse {}: {error}", path.display()))?;
    let recorded = settings
        .get("controls")
        .and_then(|controls| controls.get("resource_limits"))
        .ok_or_else(|| format!("{} has no controls.resource_limits", path.display()))?;
    serde_json::from_value(recorded.clone())
        .map_err(|error| format!("{} controls.resource_limits: {error}", path.display()))
}

fn read_json(path: &Path) -> Result<Value, CampaignRunError> {
    let bytes = std::fs::read(path).map_err(|error| format!("read {}: {error}", path.display()))?;
    serde_json::from_slice(&bytes)
        .map_err(|error| format!("parse {}: {error}", path.display()).into())
}

/// Install one JSON record atomically.
///
/// A plain write can be interrupted halfway, and a truncated `result.json`
/// or `summary.json` is exactly the state a resumed certify must be able to
/// read. The bytes are written to a fresh neighbour and renamed over the
/// destination in one step instead.
fn write_json(path: &Path, value: &Value) -> Result<(), CampaignRunError> {
    let mut bytes = serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    let parent = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let temporary = parent.join(format!(
        ".{}.{}.partial",
        path.file_name()
            .and_then(std::ffi::OsStr::to_str)
            .unwrap_or("record"),
        std::process::id()
    ));
    std::fs::write(&temporary, &bytes)
        .map_err(|error| format!("write {}: {error}", temporary.display()))?;
    std::fs::rename(&temporary, path).map_err(|error| {
        let _ = std::fs::remove_file(&temporary);
        format!("install {}: {error}", path.display())
    })?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn certificate_concurrency_refuses_nested_parallelism() {
        let one = NonZeroUsize::new(1).unwrap();
        let two = NonZeroUsize::new(2).unwrap();
        assert!(validate_certification_concurrency(one, one).is_ok());
        assert!(validate_certification_concurrency(one, two).is_ok());
        assert!(validate_certification_concurrency(two, one).is_ok());
        assert!(
            validate_certification_concurrency(two, two)
                .unwrap_err()
                .contains("--jobs 1")
        );
    }

    fn parse(arguments: &[&str]) -> Result<CampaignCertifyConfig, String> {
        parse_campaign_certify_arguments(
            &arguments
                .iter()
                .map(|value| (*value).to_owned())
                .collect::<Vec<_>>(),
        )
    }

    fn scratch(label: &str) -> PathBuf {
        let root = std::env::temp_dir().join(format!(
            "whiel-certify-{label}-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir_all(&root).unwrap();
        root
    }

    #[test]
    fn a_run_directory_is_required_and_unknown_options_are_refused() {
        assert_eq!(parse(&[]).unwrap_err(), "--run is required");
        assert!(
            parse(&["--run", "out", "--surprise", "x"])
                .unwrap_err()
                .contains("unknown campaign certify option")
        );
        assert!(parse(&["--run", "out", "--jobs", "0"]).is_err());
        assert!(parse(&["--run", "out", "--retention", "some"]).is_err());
        assert!(parse(&["--run", "out", "--workspace-bytes", "0"]).is_err());
    }

    #[test]
    fn the_defaults_are_the_documented_ones() {
        let config = parse(&["--run", "out"]).unwrap();
        assert_eq!(config.certification_limit, Duration::from_secs(600));
        assert_eq!(config.certificate_solver_limit_seconds, 60);
        assert_eq!(config.retention, Retention::CertificateOnly);
        assert_eq!(config.jobs, default_jobs());
        assert!(config.jobs.get() >= 1);
        assert_eq!(
            config.resource_limits.minimum_free_bytes,
            CampaignResourceLimits::default().minimum_free_bytes
        );
        let guarded = parse(&["--run", "out", "--minimum-free-bytes", "5"]).unwrap();
        assert_eq!(guarded.resource_limits.minimum_free_bytes, 5);
    }

    /// `campaign certify` follows the same retained-workspace rule as
    /// `campaign run`: `--retention all` alone raises the four workspace
    /// limits, an explicit flag still wins for its own limit, and
    /// `--minimum-free-bytes` is untouched either way.
    #[test]
    fn retention_all_raises_workspace_defaults_unless_told_otherwise() {
        let retained = parse(&["--run", "out", "--retention", "all"])
            .unwrap()
            .resource_limits;
        assert_eq!(
            (
                retained.workspace_bytes,
                retained.workspace_files,
                retained.minimum_free_bytes,
                retained.workspace_entries,
                retained.workspace_directories
            ),
            (68719476736, 1000000, 2147483648, 2000000, 250000)
        );
        let overridden = parse(&[
            "--run",
            "out",
            "--retention",
            "all",
            "--workspace-bytes",
            "1",
        ])
        .unwrap()
        .resource_limits;
        assert_eq!(overridden.workspace_bytes, 1);
        assert_eq!(overridden.workspace_files, 1000000);
    }

    /// Every explicit `--workspace-*`/`--minimum-free-bytes` flag is
    /// tracked, independent of `--retention`, so a standalone certify can
    /// later tell "this is the plain default" from "the operator asked for
    /// this number" before it considers adopting a run's own recorded
    /// limits.
    #[test]
    fn explicit_workspace_flags_are_tracked_one_by_one() {
        let bare = parse(&["--run", "out"]).unwrap().workspace_limits_given;
        assert_eq!(bare, WorkspaceLimitsGiven::default());
        assert!(!bare.all_given());
        let all = parse(&[
            "--run",
            "out",
            "--workspace-bytes",
            "1",
            "--workspace-files",
            "1",
            "--minimum-free-bytes",
            "1",
            "--workspace-entries",
            "1",
            "--workspace-directories",
            "1",
        ])
        .unwrap()
        .workspace_limits_given;
        assert_eq!(all, WorkspaceLimitsGiven::ALL);
        assert!(all.all_given());
        let one = parse(&["--run", "out", "--minimum-free-bytes", "1"])
            .unwrap()
            .workspace_limits_given;
        assert_eq!(
            one,
            WorkspaceLimitsGiven {
                minimum_free_bytes: true,
                ..WorkspaceLimitsGiven::default()
            }
        );
    }

    /// F1: a standalone `campaign certify --run DIR` given no `--workspace-*`
    /// flag adopts the run's own recorded `controls.resource_limits` from
    /// `campaign-settings.json`, not its own small `certificate-only`
    /// default — the same tree `campaign run --retention all` was allowed
    /// to grow to needs the same allowance to certify.
    #[test]
    fn a_standalone_certify_adopts_the_runs_recorded_limits_when_no_flag_is_given() {
        let run = scratch("recorded-limits");
        let recorded = CampaignResourceLimits {
            workspace_bytes: crate::framework2::resource_limits::RETAINED_WORKSPACE_BYTES,
            workspace_files: crate::framework2::resource_limits::RETAINED_WORKSPACE_FILES,
            minimum_free_bytes: 999,
            workspace_entries: crate::framework2::resource_limits::RETAINED_WORKSPACE_ENTRIES,
            workspace_directories:
                crate::framework2::resource_limits::RETAINED_WORKSPACE_DIRECTORIES,
            ..CampaignResourceLimits::default()
        };
        std::fs::write(
            run.join("campaign-settings.json"),
            serde_json::to_vec(&json!({
                "schema_version": 3,
                "controls": {"resource_limits": recorded},
            }))
            .unwrap(),
        )
        .unwrap();
        let mut output = Vec::new();
        let config = parse(&["--run", run.to_str().unwrap()]).unwrap();
        let resolved = resolve_standalone_resource_limits(&config, &run, &mut output).unwrap();
        assert_eq!(resolved, recorded);
        assert!(
            String::from_utf8(output)
                .unwrap()
                .contains("adopted this run's own recorded limits")
        );

        // An explicit flag still wins for its own limit.
        let overridden =
            parse(&["--run", run.to_str().unwrap(), "--minimum-free-bytes", "5"]).unwrap();
        let mut output = Vec::new();
        let resolved = resolve_standalone_resource_limits(&overridden, &run, &mut output).unwrap();
        assert_eq!(resolved.minimum_free_bytes, 5);
        assert_eq!(resolved.workspace_bytes, recorded.workspace_bytes);

        // A caller that gave every flag never reads the run's settings at all.
        let fully_explicit = parse(&[
            "--run",
            run.to_str().unwrap(),
            "--workspace-bytes",
            "1",
            "--workspace-files",
            "1",
            "--minimum-free-bytes",
            "1",
            "--workspace-entries",
            "1",
            "--workspace-directories",
            "1",
        ])
        .unwrap();
        let mut output = Vec::new();
        let resolved =
            resolve_standalone_resource_limits(&fully_explicit, &run, &mut output).unwrap();
        assert_eq!(resolved, fully_explicit.resource_limits);
        assert!(output.is_empty());
    }

    /// F1's fallback: a run whose settings are missing or unreadable falls
    /// back to the ordinary `--retention`-keyed default already computed at
    /// parse time, and says so rather than failing or silently guessing.
    #[test]
    fn a_standalone_certify_falls_back_when_the_runs_settings_cannot_be_read() {
        let run = scratch("unreadable-settings");
        let config = parse(&["--run", run.to_str().unwrap(), "--retention", "all"]).unwrap();
        let mut output = Vec::new();
        let resolved = resolve_standalone_resource_limits(&config, &run, &mut output).unwrap();
        assert_eq!(resolved, config.resource_limits);
        assert_eq!(
            resolved.workspace_bytes,
            crate::framework2::resource_limits::RETAINED_WORKSPACE_BYTES
        );
        assert!(
            String::from_utf8(output)
                .unwrap()
                .contains("could not read this run's recorded limits")
        );
    }

    /// The memory ceiling has to be a real reading, not a silent fallback,
    /// and it has to leave the machine something: the reading is total
    /// physical memory, so a default that divided all of it by a job's
    /// appetite would claim the whole machine.
    #[test]
    fn the_default_job_count_reads_the_machine_and_leaves_it_headroom() {
        let memory = host_memory_bytes().expect("this platform reports its physical memory");
        assert!(
            memory >= 1024 * 1024 * 1024,
            "an implausible memory reading of {memory} bytes"
        );
        let by_memory =
            usize::try_from(memory.saturating_sub(MEMORY_HEADROOM_BYTES) / MEMORY_PER_JOB_BYTES)
                .unwrap();
        assert_eq!(
            default_jobs().get(),
            (super::super::host_parallelism() / 2).min(by_memory).max(1)
        );
        assert!(
            u64::try_from(default_jobs().get()).unwrap() * MEMORY_PER_JOB_BYTES
                <= memory
                    .saturating_sub(MEMORY_HEADROOM_BYTES)
                    .max(MEMORY_PER_JOB_BYTES),
            "the default must not claim the whole machine"
        );
    }

    /// Acceptance is a fact on disk, not a status string: an input whose
    /// certification failed was still accepted, which is the property this
    /// milestone exists to make visible.
    #[test]
    fn the_summary_booleans_follow_the_records_and_results_on_disk() {
        let root = scratch("summary");
        // `awaiting` is whether a later certification could still finish the
        // run: an accepted input whose certification failed keeps
        // `all_accepted`, but the run exits 3 rather than 4, because
        // re-running would not resolve it on its own.
        for (statuses, accept, certified, accepted, awaiting) in [
            (["valid", "invalid"], [true, true], true, true, true),
            (
                ["valid", "invalid_uncertified"],
                [true, true],
                false,
                true,
                true,
            ),
            (
                ["valid", "certification_failed"],
                [true, true],
                false,
                true,
                false,
            ),
            (["valid", "input_changed"], [true, true], false, true, false),
            (
                ["valid", "search_timeout"],
                [true, false],
                false,
                false,
                false,
            ),
        ] {
            let run = root.join(statuses.join("-"));
            let inputs = ["Example0001", "Example0013"];
            for ((input, status), accepted) in inputs.iter().zip(statuses).zip(accept) {
                std::fs::create_dir_all(run.join(input)).unwrap();
                write_json(
                    &run.join(input).join(RESULT_FILE),
                    &json!({"input": input, "status": status}),
                )
                .unwrap();
                if accepted {
                    std::fs::write(run.join(input).join(ACCEPTED_RECORD_NAME), b"{}").unwrap();
                }
            }
            let mut summary = json!({
                "selected_inputs": inputs,
                "unrun_inputs": [],
                "interrupted": false,
                "resource_failure": Value::Null,
                "results": [],
            });
            apply_to_summary(&mut summary, &run).unwrap();
            assert_eq!(summary["all_certified"], json!(certified), "{statuses:?}");
            assert_eq!(summary["all_accepted"], json!(accepted), "{statuses:?}");
            assert_eq!(summary["results"].as_array().unwrap().len(), 2);
            assert_eq!(exit_code(&summary, true), 130);
            let expected = if certified {
                0
            } else if accepted && awaiting {
                super::super::CAMPAIGN_UNCERTIFIED
            } else {
                super::super::CAMPAIGN_FAILED
            };
            assert_eq!(exit_code(&summary, false), expected, "{statuses:?}");
        }
        std::fs::remove_dir_all(&root).unwrap();
    }

    /// A run directory read from somewhere other than where it was written.
    ///
    /// Nothing the search records names a machine location, so relocating the
    /// directory changes nothing a later certification reads: the envelope,
    /// the record beside it and the rewritten result are all found and named
    /// relative to the input's own directory.
    #[test]
    fn a_relocated_run_directory_is_read_and_rewritten_by_its_own_relative_names() {
        let written = scratch("relocated-written");
        let directory = written.join("Example0001");
        std::fs::create_dir_all(&directory).unwrap();
        std::fs::write(
            directory.join(ACCEPTED_RECORD_NAME),
            serde_json::to_vec_pretty(&json!({
                "kind": "whiel_search_acceptance",
                "version": 1,
                "verdict": "valid",
                "record": "Core.json",
                "task_identity": {"canonical_id": "Example0001"},
                "search": {"elapsed_seconds": 7.5, "limit_seconds": 600.0},
                "core": {
                "scope_identity_sha256": "a".repeat(64),
                "rows": [{"canonical_source": "alpha",
                          "initialization_profile": "direct",
                          "step_profile": "direct"}],
                "termination_profile": "direct",
            },
            }))
            .unwrap(),
        )
        .unwrap();
        std::fs::write(directory.join("Core.json"), b"{}").unwrap();
        write_json(
            &directory.join(RESULT_FILE),
            &json!({"input":"Example0001","status":"valid_uncertified",
                    "record":"Core.json","accepted":ACCEPTED_RECORD_NAME,
                    SEARCH_SECONDS: 7.5}),
        )
        .unwrap();

        let elsewhere = scratch("relocated-read");
        std::fs::remove_dir_all(&elsewhere).ok();
        std::fs::rename(&written, &elsewhere).unwrap();

        let (pending, refused) = pending_inputs(&elsewhere).unwrap();
        assert!(refused.is_empty(), "a relocated directory refuses nothing");
        assert_eq!(pending.len(), 1);
        assert_eq!(pending[0].id, "Example0001");
        assert_eq!(pending[0].directory, elsewhere.join("Example0001"));
        assert!(matches!(pending[0].intent, CertifyIntent::Build));

        rewrite_result(
            &elsewhere,
            &CertifyOutcome {
                id: "Example0001".into(),
                status: "valid",
                detail: None,
                certificate: Some(CERTIFICATE_DIRECTORY.to_owned()),
                record: Some("Core.json".to_owned()),
                axioms: Some(vec!["propext".into()]),
                certificate_module: Some("Benchmark.Example0001.Certificate.Valid".into()),
                certificate_theorem: Some("input_hoare_triple_valid".into()),
            },
        )
        .unwrap();
        let result = recorded_result(&elsewhere.join("Example0001")).unwrap();
        assert_eq!(result["status"], "valid");
        assert_eq!(result[SEARCH_SECONDS], 7.5);
        for field in ["record", "accepted", "certificate"] {
            let value = result[field].as_str().unwrap();
            assert!(
                !Path::new(value).is_absolute(),
                "{field} names a machine location: {value}"
            );
        }
        // The rebuilt result takes the same relative names when the recorded
        // one is lost, so a truncated file costs no portability either.
        std::fs::write(
            elsewhere.join("Example0001").join(RESULT_FILE),
            b"{truncated",
        )
        .unwrap();
        let rebuilt = rebuilt_result(&elsewhere.join("Example0001"), "Example0001");
        assert_eq!(rebuilt["record"], "Core.json");
        assert_eq!(rebuilt["accepted"], ACCEPTED_RECORD_NAME);
        std::fs::remove_dir_all(&elsewhere).unwrap();
    }

    /// A tree nobody can name is never called certified, and a tree whose
    /// result claims it is re-checked rather than trusted.
    #[test]
    fn a_standing_tree_is_rechecked_and_an_unnamed_one_is_refused() {
        let root = scratch("intent");
        let write_input = |id: &str, result: Value, tree: bool| {
            let directory = root.join(id);
            std::fs::create_dir_all(&directory).unwrap();
            std::fs::write(
                directory.join(ACCEPTED_RECORD_NAME),
                serde_json::to_vec_pretty(&json!({
                    "kind": "whiel_search_acceptance",
                    "version": 1,
                    "verdict": "valid",
                    "record": "Core.json",
                    "task_identity": {"canonical_id": id},
                    "search": {"elapsed_seconds": 1.0, "limit_seconds": 2.0},
                    "core": {
                    "scope_identity_sha256": "a".repeat(64),
                    "rows": [{"canonical_source": "alpha",
                              "initialization_profile": "direct",
                              "step_profile": "direct"}],
                    "termination_profile": "direct",
                },
                }))
                .unwrap(),
            )
            .unwrap();
            if tree {
                std::fs::create_dir_all(directory.join(CERTIFICATE_DIRECTORY)).unwrap();
            }
            write_json(&directory.join(RESULT_FILE), &result).unwrap();
        };
        // Claimed and nameable: re-checked, never skipped.
        write_input(
            "Example0001",
            json!({"input":"Example0001","status":"valid",
                   "certificate_module":"Benchmark.Example0001.Certificate.Valid",
                   "certificate_theorem":"input_hoare_triple_valid"}),
            true,
        );
        // Claimed but unnameable: an empty tree with a hand-written status
        // is exactly this case, and it is never read as certified.
        write_input(
            "Example0002",
            json!({"input":"Example0002","status":"valid"}),
            true,
        );
        // Nothing standing: an ordinary build.
        write_input(
            "Example0003",
            json!({"input":"Example0003","status":"valid_uncertified"}),
            false,
        );
        let (pending, refused) = pending_inputs(&root).unwrap();
        let built = pending
            .iter()
            .map(|input| {
                (
                    input.id.as_str(),
                    matches!(input.intent, CertifyIntent::Build),
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(built, [("Example0001", false), ("Example0003", true)]);
        assert_eq!(
            pending[0].scope_identity_sha256.as_deref(),
            Some(&*"a".repeat(64))
        );
        assert_eq!(refused.len(), 1);
        assert_eq!(refused[0].id, "Example0002");
        assert_eq!(refused[0].status, "certification_unchecked");
        std::fs::remove_dir_all(&root).unwrap();
    }

    /// A lost or truncated result is rebuilt from the envelope beside it,
    /// not treated as fatal: one unreadable file must not stop a whole run
    /// directory from being certified.
    #[test]
    fn an_unreadable_result_is_rebuilt_rather_than_bricking_the_run() {
        let root = scratch("rebuild");
        let directory = root.join("Example0001");
        std::fs::create_dir_all(&directory).unwrap();
        std::fs::write(
            directory.join(ACCEPTED_RECORD_NAME),
            serde_json::to_vec_pretty(&json!({
                "kind": "whiel_search_acceptance",
                "version": 1,
                "verdict": "invalid",
                "record": "Counterexample.json",
                "task_identity": {"canonical_id": "Example0001"},
                "search": {"elapsed_seconds": 1.0, "limit_seconds": 2.0},
                "core": Value::Null,
            }))
            .unwrap(),
        )
        .unwrap();
        std::fs::write(directory.join(RESULT_FILE), b"{truncated").unwrap();
        let outcome = CertifyOutcome {
            id: "Example0001".into(),
            status: "invalid",
            detail: None,
            certificate: Some(CERTIFICATE_DIRECTORY.to_owned()),
            record: Some("Counterexample.json".to_owned()),
            axioms: Some(vec!["propext".into()]),
            certificate_module: Some("Benchmark.Example0001.Certificate.Invalid".into()),
            certificate_theorem: Some("input_hoare_triple_invalid".into()),
        };
        rewrite_result(&root, &outcome).unwrap();
        let written = recorded_result(&directory).expect("the rebuilt result parses");
        assert_eq!(written["status"], "invalid");
        assert_eq!(written["input"], "Example0001");
        // Certification never measures search time, so the envelope's own
        // figure is what a rebuilt result carries.
        assert_eq!(written[SEARCH_SECONDS], 1.0);
        assert_eq!(written["certificate_theorem"], "input_hoare_triple_invalid");
        // The rebuilt result names the envelope beside it, not where this
        // machine keeps it: the directory may be certified somewhere else.
        assert_eq!(written["accepted"], ACCEPTED_RECORD_NAME);
        assert_eq!(written["certificate"], CERTIFICATE_DIRECTORY);
        assert_eq!(written["counterexample"], "Counterexample.json");
        std::fs::remove_dir_all(&root).unwrap();
    }

    /// Certification rewrites the verdict, never the search's own duration.
    #[test]
    fn rewriting_a_result_preserves_the_search_time_the_run_measured() {
        let root = scratch("preserve");
        let directory = root.join("Example0001");
        std::fs::create_dir_all(&directory).unwrap();
        write_json(
            &directory.join(RESULT_FILE),
            &json!({
                "input": "Example0001",
                "status": "valid_uncertified",
                SEARCH_SECONDS: 42.25,
            }),
        )
        .unwrap();
        let outcome = CertifyOutcome {
            id: "Example0001".into(),
            status: "valid",
            detail: None,
            certificate: Some(CERTIFICATE_DIRECTORY.to_owned()),
            record: Some("Core.json".to_owned()),
            axioms: Some(vec!["propext".into()]),
            certificate_module: Some("Benchmark.Example0001.Certificate.Valid".into()),
            certificate_theorem: Some("input_hoare_triple_valid".into()),
        };
        rewrite_result(&root, &outcome).unwrap();
        let written = recorded_result(&directory).unwrap();
        assert_eq!(written["status"], "valid");
        assert_eq!(written[SEARCH_SECONDS], 42.25);
        std::fs::remove_dir_all(&root).unwrap();
    }

    /// A deferred certification rebuilds each job under the label the run's
    /// own freeze recorded, so a condition the portfolio proved is not
    /// re-proved under the direct profile it could not reach.
    #[test]
    fn a_portfolio_label_in_the_envelope_reaches_the_rebuild() {
        let root = scratch("recorded-labels");
        let directory = root.join("Example0001");
        std::fs::create_dir_all(&directory).unwrap();
        std::fs::write(
            directory.join(ACCEPTED_RECORD_NAME),
            serde_json::to_vec_pretty(&json!({
                "kind": "whiel_search_acceptance",
                "version": 1,
                "verdict": "valid",
                "record": "Core.json",
                "task_identity": {"canonical_id": "Example0001"},
                "search": {"elapsed_seconds": 1.0, "limit_seconds": 2.0},
                "core": {
                    "scope_identity_sha256": "a".repeat(64),
                    "rows": [
                        {"canonical_source": "alpha",
                         "initialization_profile": "direct",
                         "step_profile": "casc_2025"},
                        {"canonical_source": "beta",
                         "initialization_profile": "direct",
                         "step_profile": "direct"},
                    ],
                    "termination_profile": "direct",
                },
            }))
            .unwrap(),
        )
        .unwrap();
        std::fs::write(directory.join("Core.json"), b"{}").unwrap();
        let (pending, refused) = pending_inputs(&root).unwrap();
        assert!(
            refused.is_empty(),
            "a readable acceptance was refused: {:?}",
            refused
                .iter()
                .map(|outcome| outcome.status)
                .collect::<Vec<_>>()
        );
        let recorded = pending[0]
            .core_profiles
            .as_ref()
            .expect("a valid acceptance carries its Core's labels");
        assert_eq!(
            recorded.clause_labels("alpha"),
            Some((ProofSearchProfile::Direct, ProofSearchProfile::Casc2025))
        );
        assert_eq!(recorded.termination(), ProofSearchProfile::Direct);
        assert!(matches!(
            record_job_profiles(&pending[0]),
            RecordJobProfiles::Recorded(_)
        ));
        std::fs::remove_dir_all(&root).unwrap();
    }

    /// One certify at a time per run directory; the second says so.
    #[test]
    fn a_second_certification_of_one_run_directory_is_refused() {
        let root = scratch("lock");
        let first = RunDirectoryLock::take(&root).unwrap();
        let error = RunDirectoryLock::take(&root).unwrap_err();
        assert_eq!(error.exit_code, super::super::CAMPAIGN_ARGUMENT_FAILURE);
        assert!(error.to_string().contains("another certification"));
        drop(first);
        // The claim is released with the phase, so the next command runs.
        RunDirectoryLock::take(&root).unwrap();
        std::fs::remove_dir_all(&root).unwrap();
    }
}
