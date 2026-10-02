//! Bounded human output and stable machine-readable campaign records.

use std::collections::BTreeMap;
use std::io::{self, Write};
use std::path::Path;
use std::time::Duration;

use serde::{Deserialize, Serialize};

use crate::artifact::ArtifactRef;
use crate::campaign::KnownClassification;
use crate::failure::FailureKind;
use crate::symbolic::SynthesisResult;
use crate::telemetry::TelemetryReport;

pub const CAMPAIGN_SCHEMA_VERSION: u64 = 2;
const MAX_FAILURE_DETAIL_BYTES: usize = 512;
const MAX_TELEMETRY_ERRORS: usize = 8;
const MAX_TELEMETRY_ERROR_BYTES: usize = 256;
const MAX_MISSING_MEASUREMENTS: usize = 32;
const MAX_MEASUREMENT_LIMITATIONS: usize = 16;
const MAX_MEASUREMENT_NOTE_BYTES: usize = 384;
const MAX_INVARIANT_CLAUSES: usize = 32;
const MAX_INVARIANT_CLAUSE_BYTES: usize = 256;
const MAX_COUNTEREXAMPLE_BYTES: usize = 2_048;

// ------------------------------------------------------------
// Stable Records
// ------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OutputFormat {
    Quiet,
    Normal,
    Verbose,
    JsonLines,
}

impl OutputFormat {
    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "quiet" => Some(Self::Quiet),
            "normal" => Some(Self::Normal),
            "verbose" => Some(Self::Verbose),
            "jsonl" => Some(Self::JsonLines),
            _ => None,
        }
    }

    pub fn as_str(self) -> &'static str {
        match self {
            Self::Quiet => "quiet",
            Self::Normal => "normal",
            Self::Verbose => "verbose",
            Self::JsonLines => "jsonl",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TerminalClassification {
    Valid,
    Invalid,
    Timeout,
    Failure,
}

impl TerminalClassification {
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Valid => "valid",
            Self::Invalid => "invalid",
            Self::Timeout => "timeout",
            Self::Failure => "failure",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum KnownComparison {
    Match,
    Mismatch,
    UnknownBaseline,
    NoSynthesisClassification,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ArtifactIdentityRecord {
    pub backend_id: String,
    pub local_id: u64,
    pub kind: String,
    pub repo_relative_path: String,
    /// False when the payload was discarded under certificate-only
    /// retention. The path still says where it lived, so a reader can tell
    /// "pruned by policy" from "missing unexpectedly" instead of finding an
    /// absent file with no explanation.
    #[serde(default = "default_retained")]
    pub retained: bool,
}

fn default_retained() -> bool {
    true
}

impl ArtifactIdentityRecord {
    fn retained(reference: ArtifactRef, artifact_root: &Path, repository: &Path) -> Self {
        Self {
            backend_id: reference.backend_id().to_string(),
            local_id: reference.local_id(),
            kind: debug_name(reference.kind()),
            repo_relative_path: display_path(&reference.retained_path(artifact_root), repository),
            retained: true,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FailureRecord {
    pub origin: String,
    pub kind: String,
    pub retryable: bool,
    pub scope: String,
    pub detail: Option<String>,
    pub artifacts: Vec<ArtifactIdentityRecord>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InvariantRecord {
    pub clause_count: u64,
    pub clauses: Vec<String>,
    pub omitted_clauses: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CounterexampleRecord {
    pub source_w_index: Option<u64>,
    pub compact_json: String,
    pub serialized_bytes: u64,
    pub truncated: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "classification", rename_all = "snake_case")]
pub enum TerminalRecord {
    Valid {
        certificate: ArtifactIdentityRecord,
        acceptance_record: ArtifactIdentityRecord,
        invariant: InvariantRecord,
    },
    Invalid {
        certificate: ArtifactIdentityRecord,
        witness: ArtifactIdentityRecord,
        acceptance_record: ArtifactIdentityRecord,
        counterexample: CounterexampleRecord,
    },
    Failure {
        failure: FailureRecord,
    },
    Timeout {
        failure: FailureRecord,
    },
}

impl TerminalRecord {
    pub fn classification(&self) -> TerminalClassification {
        match self {
            Self::Valid { .. } => TerminalClassification::Valid,
            Self::Invalid { .. } => TerminalClassification::Invalid,
            Self::Timeout { .. } => TerminalClassification::Timeout,
            Self::Failure { .. } => TerminalClassification::Failure,
        }
    }
}

impl TerminalRecord {
    fn from_result(result: &SynthesisResult, artifact_root: &Path, repository: &Path) -> Self {
        match result {
            SynthesisResult::Valid(valid) => Self::Valid {
                certificate: ArtifactIdentityRecord::retained(
                    valid.certificate,
                    artifact_root,
                    repository,
                ),
                acceptance_record: ArtifactIdentityRecord::retained(
                    valid.record,
                    artifact_root,
                    repository,
                ),
                invariant: bounded_invariant(&valid.invariant),
            },
            SynthesisResult::Invalid(invalid) => Self::Invalid {
                certificate: ArtifactIdentityRecord::retained(
                    invalid.certificate,
                    artifact_root,
                    repository,
                ),
                witness: ArtifactIdentityRecord::retained(
                    invalid.witness,
                    artifact_root,
                    repository,
                ),
                acceptance_record: ArtifactIdentityRecord::retained(
                    invalid.record,
                    artifact_root,
                    repository,
                ),
                counterexample: bounded_counterexample(
                    &invalid.counterexample,
                    invalid.source_w_index,
                ),
            },
            SynthesisResult::Failure(failure) => {
                let failure_record = FailureRecord {
                    origin: debug_name(failure.origin()),
                    kind: debug_name(failure.kind()),
                    retryable: failure.retryable(),
                    scope: debug_name(failure.scope()),
                    detail: failure
                        .detail()
                        .map(|detail| bounded_text(detail, MAX_FAILURE_DETAIL_BYTES)),
                    artifacts: failure
                        .artifact_references()
                        .iter()
                        .copied()
                        .map(|reference| {
                            ArtifactIdentityRecord::retained(reference, artifact_root, repository)
                        })
                        .collect(),
                };
                if failure.kind() == FailureKind::OverallTimeout {
                    Self::Timeout {
                        failure: failure_record,
                    }
                } else {
                    Self::Failure {
                        failure: failure_record,
                    }
                }
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TelemetryRecord {
    pub level: String,
    pub measurement_complete: bool,
    pub elapsed_milliseconds: u64,
    pub counters: BTreeMap<String, u64>,
    pub dispositions: BTreeMap<String, u64>,
    pub wave_count: u64,
    pub formula_birth_count: u64,
    pub dropped_detailed_events: u64,
    pub process_peak_rss_bytes: Option<u64>,
    pub waited_children_peak_rss_bytes: Option<u64>,
    pub errors: Vec<String>,
    #[serde(default)]
    pub missing_measurements: Vec<String>,
    #[serde(default)]
    pub omitted_missing_measurements: u64,
    #[serde(default)]
    pub limitations: Vec<String>,
    #[serde(default)]
    pub omitted_limitations: u64,
    pub summary_path: Option<String>,
    pub events_path: Option<String>,
}

impl TelemetryRecord {
    pub fn from_report(report: &TelemetryReport, repository: &Path) -> Self {
        let snapshot = &report.snapshot;
        let (missing_measurements, omitted_missing_measurements) = bounded_items(
            &snapshot.missing_measurements,
            MAX_MISSING_MEASUREMENTS,
            MAX_MEASUREMENT_NOTE_BYTES,
        );
        let (limitations, omitted_limitations) = bounded_items(
            &snapshot.limitations,
            MAX_MEASUREMENT_LIMITATIONS,
            MAX_MEASUREMENT_NOTE_BYTES,
        );
        Self {
            level: debug_name(snapshot.level),
            measurement_complete: snapshot.measurement_complete,
            elapsed_milliseconds: snapshot.elapsed_nanoseconds / 1_000_000,
            counters: snapshot.counters.clone(),
            dispositions: snapshot.dispositions.clone(),
            wave_count: snapshot.waves.len() as u64,
            formula_birth_count: snapshot.formula_births.len() as u64,
            dropped_detailed_events: snapshot.dropped_detailed_events,
            process_peak_rss_bytes: snapshot.memory.process_peak_rss_bytes,
            waited_children_peak_rss_bytes: snapshot.memory.waited_children_peak_rss_bytes,
            errors: snapshot
                .errors
                .iter()
                .take(MAX_TELEMETRY_ERRORS)
                .map(|error| bounded_text(error, MAX_TELEMETRY_ERROR_BYTES))
                .collect(),
            missing_measurements,
            omitted_missing_measurements,
            limitations,
            omitted_limitations,
            summary_path: report
                .summary_path
                .as_deref()
                .map(|path| display_path(path, repository)),
            events_path: report
                .events_path
                .as_deref()
                .map(|path| display_path(path, repository)),
        }
    }

    fn missing_measurement_count(&self) -> u64 {
        u64::try_from(self.missing_measurements.len())
            .unwrap_or(u64::MAX)
            .saturating_add(self.omitted_missing_measurements)
    }

    fn limitation_count(&self) -> u64 {
        u64::try_from(self.limitations.len())
            .unwrap_or(u64::MAX)
            .saturating_add(self.omitted_limitations)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TaskResultRecord {
    pub canonical_id: String,
    pub index: u64,
    pub total: u64,
    pub elapsed_milliseconds: u64,
    pub terminal: TerminalRecord,
    pub known_classification: String,
    pub known_comparison: KnownComparison,
    pub telemetry: TelemetryRecord,
}

pub(crate) struct TaskResultContext<'a> {
    canonical_id: &'a str,
    index: usize,
    total: usize,
    artifact_root: &'a Path,
    repository: &'a Path,
    known: KnownClassification,
}

impl<'a> TaskResultContext<'a> {
    pub(crate) fn new(
        canonical_id: &'a str,
        index: usize,
        total: usize,
        artifact_root: &'a Path,
        repository: &'a Path,
        known: KnownClassification,
    ) -> Self {
        Self {
            canonical_id,
            index,
            total,
            artifact_root,
            repository,
            known,
        }
    }
}

impl TaskResultRecord {
    pub(crate) fn new(
        context: TaskResultContext<'_>,
        elapsed: Duration,
        result: &SynthesisResult,
        telemetry: TelemetryRecord,
    ) -> Self {
        let terminal =
            TerminalRecord::from_result(result, context.artifact_root, context.repository);
        let known_comparison = compare_known(&terminal.classification(), context.known);
        Self {
            canonical_id: context.canonical_id.to_string(),
            index: context.index as u64,
            total: context.total as u64,
            elapsed_milliseconds: duration_milliseconds(elapsed),
            terminal,
            known_classification: context.known.as_str().to_string(),
            known_comparison,
            telemetry,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "event", rename_all = "snake_case")]
pub enum CampaignEvent {
    CampaignStart {
        schema_version: u64,
        selection_kind: String,
        selection_name: String,
        task_count: u64,
        artifact_root: String,
    },
    TaskStart {
        schema_version: u64,
        canonical_id: String,
        index: u64,
        total: u64,
        task_overall_limit_milliseconds: u64,
        campaign_remaining_milliseconds: Option<u64>,
    },
    TaskProgress {
        schema_version: u64,
        canonical_id: String,
        index: u64,
        total: u64,
        elapsed_milliseconds: u64,
        inv_epochs: u64,
        proposed_clauses: u64,
        #[serde(alias = "initialization_proofs")]
        initialized_clauses: u64,
        core_admissions: u64,
        highest_w_index: Option<u64>,
        highest_safe_fmb_frontier: Option<u64>,
    },
    TaskResult {
        schema_version: u64,
        result: Box<TaskResultRecord>,
    },
    CampaignSummary {
        schema_version: u64,
        task_count: u64,
        valid: u64,
        invalid: u64,
        timeouts: u64,
        failures: u64,
        known_matches: u64,
        known_mismatches: u64,
        elapsed_milliseconds: u64,
        campaign_limit_reached: bool,
        process_peak_rss_bytes: Option<u64>,
        waited_children_peak_rss_bytes: Option<u64>,
    },
}

// ------------------------------------------------------------
// Output Rendering
// ------------------------------------------------------------

pub struct Reporter<W> {
    format: OutputFormat,
    writer: W,
}

impl<W: Write> Reporter<W> {
    pub fn new(format: OutputFormat, writer: W) -> Self {
        Self { format, writer }
    }

    pub fn emit(&mut self, event: &CampaignEvent) -> io::Result<()> {
        match self.format {
            OutputFormat::JsonLines => {
                serde_json::to_writer(&mut self.writer, event)?;
                self.writer.write_all(b"\n")
            }
            OutputFormat::Quiet => self.emit_human(event, false, true),
            OutputFormat::Normal => self.emit_human(event, false, false),
            OutputFormat::Verbose => self.emit_human(event, true, false),
        }
    }

    pub fn into_inner(self) -> W {
        self.writer
    }

    pub fn supports_progress(&self) -> bool {
        matches!(
            self.format,
            OutputFormat::Normal | OutputFormat::Verbose | OutputFormat::JsonLines
        )
    }

    fn emit_human(&mut self, event: &CampaignEvent, verbose: bool, quiet: bool) -> io::Result<()> {
        match event {
            CampaignEvent::CampaignStart {
                selection_kind,
                selection_name,
                task_count,
                artifact_root,
                ..
            } if !quiet => writeln!(
                self.writer,
                "symbolic: {selection_kind} {selection_name} ({task_count} tasks; artifacts={artifact_root})"
            ),
            CampaignEvent::TaskStart {
                canonical_id,
                index,
                total,
                task_overall_limit_milliseconds,
                campaign_remaining_milliseconds,
                ..
            } if !quiet => writeln!(
                self.writer,
                "[{index}/{total}] {canonical_id}: starting (task_limit={:.3}s campaign_remaining={})",
                *task_overall_limit_milliseconds as f64 / 1_000.0,
                campaign_remaining_milliseconds.map_or_else(
                    || "unlimited".to_string(),
                    |value| format!("{:.3}s", value as f64 / 1_000.0)
                )
            ),
            CampaignEvent::TaskProgress {
                canonical_id,
                index,
                total,
                elapsed_milliseconds,
                inv_epochs,
                proposed_clauses,
                initialized_clauses,
                core_admissions,
                highest_w_index,
                highest_safe_fmb_frontier,
                ..
            } if !quiet => writeln!(
                self.writer,
                "[{index}/{total}] {canonical_id}: progress elapsed={:.3}s inv_epochs={inv_epochs} proposed={proposed_clauses} initialized={initialized_clauses} core={core_admissions} highest_w={} fmb_frontier={}",
                *elapsed_milliseconds as f64 / 1_000.0,
                highest_w_index
                    .map_or_else(|| "unavailable".to_string(), |value| value.to_string()),
                highest_safe_fmb_frontier
                    .map_or_else(|| "unavailable".to_string(), |value| value.to_string()),
            ),
            CampaignEvent::TaskResult { result, .. } => {
                writeln!(
                    self.writer,
                    "[{}/{}] {}: {} ({:.3}s; known={} {:?})",
                    result.index,
                    result.total,
                    result.canonical_id,
                    result.terminal.classification().as_str(),
                    result.elapsed_milliseconds as f64 / 1_000.0,
                    result.known_classification,
                    result.known_comparison
                )?;
                match &result.terminal {
                    TerminalRecord::Valid {
                        certificate,
                        acceptance_record,
                        invariant,
                    } => writeln!(
                        self.writer,
                        "  certificate: {} ({}#{}); acceptance_record: {} ({}#{}); invariant={:?}; omitted_clauses={}",
                        certificate.repo_relative_path,
                        certificate.backend_id,
                        certificate.local_id,
                        acceptance_record.repo_relative_path,
                        acceptance_record.backend_id,
                        acceptance_record.local_id,
                        invariant.clauses,
                        invariant.omitted_clauses
                    )?,
                    TerminalRecord::Invalid {
                        certificate,
                        witness,
                        acceptance_record,
                        counterexample,
                    } => writeln!(
                        self.writer,
                        "  certificate: {} ({}#{}); witness: {} ({}#{}); acceptance_record: {} ({}#{}); source_w_index={:?}; counterexample={}; counterexample_truncated={}",
                        certificate.repo_relative_path,
                        certificate.backend_id,
                        certificate.local_id,
                        witness.repo_relative_path,
                        witness.backend_id,
                        witness.local_id,
                        acceptance_record.repo_relative_path,
                        acceptance_record.backend_id,
                        acceptance_record.local_id,
                        counterexample.source_w_index,
                        counterexample.compact_json,
                        counterexample.truncated
                    )?,
                    TerminalRecord::Timeout { failure } => writeln!(
                        self.writer,
                        "  timeout: core_admissions={} highest_w={} {}",
                        result
                            .telemetry
                            .dispositions
                            .get("core_admission")
                            .copied()
                            .map_or_else(
                                || {
                                    if result.telemetry.level == "off" {
                                        "unavailable".to_string()
                                    } else {
                                        "0".to_string()
                                    }
                                },
                                |value| value.to_string()
                            ),
                        result
                            .telemetry
                            .counters
                            .get("cex.highest_w_index")
                            .copied()
                            .map_or_else(|| "unavailable".to_string(), |value| value.to_string()),
                        failure.detail.as_deref().unwrap_or("no bounded diagnostic")
                    )?,
                    TerminalRecord::Failure { failure } => writeln!(
                        self.writer,
                        "  failure: {}/{} {}",
                        failure.origin,
                        failure.kind,
                        failure.detail.as_deref().unwrap_or("no bounded diagnostic")
                    )?,
                }
                if verbose {
                    writeln!(
                        self.writer,
                        "  telemetry: waves={} formulas={} complete={} missing={} limitations={} errors={} dropped={} summary={}",
                        result.telemetry.wave_count,
                        result.telemetry.formula_birth_count,
                        result.telemetry.measurement_complete,
                        result.telemetry.missing_measurement_count(),
                        result.telemetry.limitation_count(),
                        result.telemetry.errors.len(),
                        result.telemetry.dropped_detailed_events,
                        result.telemetry.summary_path.as_deref().unwrap_or("none")
                    )?;
                }
                Ok(())
            }
            CampaignEvent::CampaignSummary {
                task_count,
                valid,
                invalid,
                timeouts,
                failures,
                known_matches,
                known_mismatches,
                elapsed_milliseconds,
                campaign_limit_reached,
                process_peak_rss_bytes,
                waited_children_peak_rss_bytes,
                ..
            } => writeln!(
                self.writer,
                "summary: tasks={task_count} valid={valid} invalid={invalid} timeouts={timeouts} failures={failures} known_matches={known_matches} known_mismatches={known_mismatches} elapsed={:.3}s campaign_limit_reached={campaign_limit_reached} peak_rss_bytes={} waited_children_peak_rss_bytes={}",
                *elapsed_milliseconds as f64 / 1_000.0,
                process_peak_rss_bytes
                    .map_or_else(|| "unavailable".to_string(), |value| value.to_string()),
                waited_children_peak_rss_bytes
                    .map_or_else(|| "unavailable".to_string(), |value| value.to_string()),
            ),
            _ => Ok(()),
        }
    }
}

pub fn compare_known(
    observed: &TerminalClassification,
    known: KnownClassification,
) -> KnownComparison {
    match (observed, known) {
        (TerminalClassification::Failure | TerminalClassification::Timeout, _) => {
            KnownComparison::NoSynthesisClassification
        }
        (_, KnownClassification::Unknown) => KnownComparison::UnknownBaseline,
        (TerminalClassification::Valid, KnownClassification::Valid)
        | (TerminalClassification::Invalid, KnownClassification::Invalid) => KnownComparison::Match,
        _ => KnownComparison::Mismatch,
    }
}

pub fn duration_milliseconds(duration: Duration) -> u64 {
    duration.as_millis().min(u128::from(u64::MAX)) as u64
}

fn bounded_items(values: &[String], maximum: usize, maximum_bytes: usize) -> (Vec<String>, u64) {
    let retained = values
        .iter()
        .take(maximum)
        .map(|value| bounded_text(value, maximum_bytes))
        .collect::<Vec<_>>();
    let omitted = values.len().saturating_sub(retained.len());
    (retained, u64::try_from(omitted).unwrap_or(u64::MAX))
}

fn bounded_text(value: &str, maximum: usize) -> String {
    let one_line = value.replace(['\n', '\r'], " ");
    if one_line.len() <= maximum {
        return one_line;
    }
    let mut boundary = maximum;
    while !one_line.is_char_boundary(boundary) {
        boundary -= 1;
    }
    format!("{}...<truncated>", &one_line[..boundary])
}

fn bounded_invariant(invariant: &[String]) -> InvariantRecord {
    let clauses = invariant
        .iter()
        .take(MAX_INVARIANT_CLAUSES)
        .map(|clause| bounded_text(clause, MAX_INVARIANT_CLAUSE_BYTES))
        .collect::<Vec<_>>();
    InvariantRecord {
        clause_count: invariant.len() as u64,
        omitted_clauses: invariant.len().saturating_sub(clauses.len()) as u64,
        clauses,
    }
}

fn bounded_counterexample(
    counterexample: &serde_json::Value,
    source_w_index: Option<u64>,
) -> CounterexampleRecord {
    let serialized = serde_json::to_string(counterexample)
        .unwrap_or_else(|error| format!("<counterexample serialization failed: {error}>"));
    let serialized_bytes = serialized.len() as u64;
    let compact_json = bounded_text(&serialized, MAX_COUNTEREXAMPLE_BYTES);
    CounterexampleRecord {
        source_w_index,
        truncated: serialized.len() > MAX_COUNTEREXAMPLE_BYTES,
        compact_json,
        serialized_bytes,
    }
}

fn display_path(path: &Path, repository: &Path) -> String {
    path.strip_prefix(repository)
        .unwrap_or(path)
        .to_string_lossy()
        .into_owned()
}

fn debug_name(value: impl std::fmt::Debug) -> String {
    let source = format!("{value:?}");
    let mut result = String::with_capacity(source.len() + 4);
    for (index, character) in source.chars().enumerate() {
        if character.is_ascii_uppercase() {
            if index > 0 {
                result.push('_');
            }
            result.push(character.to_ascii_lowercase());
        } else {
            result.push(character);
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    fn telemetry() -> TelemetryRecord {
        TelemetryRecord {
            level: "aggregate".to_string(),
            measurement_complete: true,
            elapsed_milliseconds: 1,
            counters: BTreeMap::new(),
            dispositions: BTreeMap::new(),
            wave_count: 2,
            formula_birth_count: 3,
            dropped_detailed_events: 0,
            process_peak_rss_bytes: Some(1_024),
            waited_children_peak_rss_bytes: Some(2_048),
            errors: Vec::new(),
            missing_measurements: Vec::new(),
            omitted_missing_measurements: 0,
            limitations: Vec::new(),
            omitted_limitations: 0,
            summary_path: Some("artifacts/run/summary.json".to_string()),
            events_path: None,
        }
    }

    fn result(terminal: TerminalRecord) -> TaskResultRecord {
        let classification = terminal.classification();
        TaskResultRecord {
            canonical_id: "Example0012".to_string(),
            index: 1,
            total: 1,
            elapsed_milliseconds: 10,
            terminal,
            known_classification: "valid".to_string(),
            known_comparison: compare_known(&classification, KnownClassification::Valid),
            telemetry: telemetry(),
        }
    }

    #[test]
    fn json_lines_round_trip_every_terminal_classification() {
        let artifact = ArtifactIdentityRecord {
            backend_id: "00000000000000000000000000000001".to_string(),
            local_id: 1,
            kind: "certificate".to_string(),
            repo_relative_path:
                "artifacts/symbolic-houdini/test/Example0012/solver-artifacts/run-00000000000000000000000000000001/required/artifact-00000000000000000001.bin"
                    .to_string(),
            retained: true,
        };
        let terminals = [
            TerminalRecord::Valid {
                certificate: artifact.clone(),
                acceptance_record: artifact.clone(),
                invariant: InvariantRecord {
                    clause_count: 1,
                    clauses: vec!["x = x".to_string()],
                    omitted_clauses: 0,
                },
            },
            TerminalRecord::Invalid {
                certificate: artifact.clone(),
                witness: artifact.clone(),
                acceptance_record: artifact.clone(),
                counterexample: CounterexampleRecord {
                    source_w_index: Some(2),
                    compact_json: "{}".to_string(),
                    serialized_bytes: 2,
                    truncated: false,
                },
            },
            TerminalRecord::Failure {
                failure: FailureRecord {
                    origin: "runcontrol".to_string(),
                    kind: "infrastructurefailure".to_string(),
                    retryable: false,
                    scope: "runglobal".to_string(),
                    detail: Some("bounded".to_string()),
                    artifacts: Vec::new(),
                },
            },
            TerminalRecord::Timeout {
                failure: FailureRecord {
                    origin: "runcontrol".to_string(),
                    kind: "overalltimeout".to_string(),
                    retryable: false,
                    scope: "runglobal".to_string(),
                    detail: Some("bounded".to_string()),
                    artifacts: Vec::new(),
                },
            },
        ];
        let mut reporter = Reporter::new(OutputFormat::JsonLines, Vec::new());
        for terminal in terminals {
            reporter
                .emit(&CampaignEvent::TaskResult {
                    schema_version: CAMPAIGN_SCHEMA_VERSION,
                    result: Box::new(result(terminal)),
                })
                .unwrap();
        }
        let output = String::from_utf8(reporter.into_inner()).unwrap();
        let parsed = output
            .lines()
            .map(|line| serde_json::from_str::<CampaignEvent>(line).unwrap())
            .collect::<Vec<_>>();
        assert_eq!(parsed.len(), 4);
        assert!(output.contains("repo_relative_path"));
        assert!(output.contains("artifact-00000000000000000001.bin"));
    }

    #[test]
    fn human_terminal_output_prints_retained_certificate_and_witness_paths() {
        let artifact = ArtifactIdentityRecord {
            backend_id: "00000000000000000000000000000001".to_string(),
            local_id: 1,
            kind: "certificate".to_string(),
            repo_relative_path: "artifacts/run/required/certificate.lean".to_string(),
            retained: true,
        };
        let witness = ArtifactIdentityRecord {
            backend_id: artifact.backend_id.clone(),
            local_id: 2,
            kind: "witness".to_string(),
            repo_relative_path: "artifacts/run/required/witness.json".to_string(),
            retained: true,
        };
        let terminals = [
            TerminalRecord::Valid {
                certificate: artifact.clone(),
                acceptance_record: artifact.clone(),
                invariant: InvariantRecord {
                    clause_count: 0,
                    clauses: Vec::new(),
                    omitted_clauses: 0,
                },
            },
            TerminalRecord::Invalid {
                certificate: artifact.clone(),
                witness,
                acceptance_record: artifact,
                counterexample: CounterexampleRecord {
                    source_w_index: Some(0),
                    compact_json: "{}".to_string(),
                    serialized_bytes: 2,
                    truncated: false,
                },
            },
        ];
        let mut reporter = Reporter::new(OutputFormat::Normal, Vec::new());
        for terminal in terminals {
            reporter
                .emit(&CampaignEvent::TaskResult {
                    schema_version: CAMPAIGN_SCHEMA_VERSION,
                    result: Box::new(result(terminal)),
                })
                .unwrap();
        }
        let output = String::from_utf8(reporter.into_inner()).unwrap();
        assert!(output.contains("certificate: artifacts/run/required/certificate.lean"));
        assert!(output.contains("witness: artifacts/run/required/witness.json"));
        assert!(output.len() < 2_000);
    }

    #[test]
    fn normal_failure_output_is_bounded_and_never_prints_payload_lines() {
        let terminal = TerminalRecord::Failure {
            failure: FailureRecord {
                origin: "run_control".to_string(),
                kind: "infrastructure_failure".to_string(),
                retryable: false,
                scope: "run_global".to_string(),
                detail: Some(bounded_text(&format!("{}\nsecret", "x".repeat(900)), 512)),
                artifacts: Vec::new(),
            },
        };
        let mut reporter = Reporter::new(OutputFormat::Normal, Vec::new());
        reporter
            .emit(&CampaignEvent::TaskResult {
                schema_version: CAMPAIGN_SCHEMA_VERSION,
                result: Box::new(result(terminal)),
            })
            .unwrap();
        let output = String::from_utf8(reporter.into_inner()).unwrap();
        assert!(!output.contains("\nsecret"));
        assert!(output.len() < 1_200);
        assert!(output.contains("<truncated>"));
    }

    #[test]
    fn telemetry_record_preserves_bounded_missing_measurements_and_limitations() {
        let mut report = crate::telemetry::TelemetrySession::disabled().finish();
        report.snapshot.measurement_complete = false;
        report.snapshot.missing_measurements = (0..40)
            .map(|index| format!("missing-{index}-{}\nsecond-line", "x".repeat(600)))
            .collect();
        report.snapshot.limitations = (0..20)
            .map(|index| format!("limitation-{index}-{}\nsecond-line", "y".repeat(600)))
            .collect();

        let record = TelemetryRecord::from_report(&report, Path::new("/repository"));
        assert!(!record.measurement_complete);
        assert_eq!(record.missing_measurements.len(), MAX_MISSING_MEASUREMENTS);
        assert_eq!(record.omitted_missing_measurements, 8);
        assert_eq!(record.limitations.len(), MAX_MEASUREMENT_LIMITATIONS);
        assert_eq!(record.omitted_limitations, 4);
        assert_eq!(record.missing_measurement_count(), 40);
        assert_eq!(record.limitation_count(), 20);
        assert!(
            record
                .missing_measurements
                .iter()
                .chain(&record.limitations)
                .all(|item| !item.contains('\n') && item.len() < MAX_MEASUREMENT_NOTE_BYTES + 32)
        );
    }

    #[test]
    fn verbose_output_reports_bounded_telemetry_completeness_counts() {
        let terminal = TerminalRecord::Failure {
            failure: FailureRecord {
                origin: "run_control".to_string(),
                kind: "infrastructure_failure".to_string(),
                retryable: false,
                scope: "run_global".to_string(),
                detail: Some("bounded".to_string()),
                artifacts: Vec::new(),
            },
        };
        let mut result = result(terminal);
        result.telemetry.measurement_complete = false;
        result.telemetry.missing_measurements = vec!["first".to_string(), "second".to_string()];
        result.telemetry.omitted_missing_measurements = 3;
        result.telemetry.limitations = vec!["known limitation".to_string()];
        result.telemetry.omitted_limitations = 2;
        result.telemetry.errors = vec!["bounded error".to_string()];

        let mut reporter = Reporter::new(OutputFormat::Verbose, Vec::new());
        reporter
            .emit(&CampaignEvent::TaskResult {
                schema_version: CAMPAIGN_SCHEMA_VERSION,
                result: Box::new(result),
            })
            .unwrap();
        let output = String::from_utf8(reporter.into_inner()).unwrap();
        assert!(output.contains("complete=false missing=5 limitations=3 errors=1"));
        assert!(!output.contains("known limitation"));
        assert!(output.len() < 2_000);
    }

    #[test]
    fn invariant_and_counterexample_terminal_metadata_are_bounded() {
        let invariant = vec!["x".repeat(1_000); 100];
        let bounded = bounded_invariant(&invariant);
        assert_eq!(bounded.clause_count, 100);
        assert_eq!(bounded.clauses.len(), MAX_INVARIANT_CLAUSES);
        assert_eq!(bounded.omitted_clauses, 68);
        assert!(bounded.clauses.iter().all(|clause| clause.len() < 300));

        let counterexample = serde_json::json!({"payload": "x".repeat(10_000)});
        let bounded = bounded_counterexample(&counterexample, Some(7));
        assert_eq!(bounded.source_w_index, Some(7));
        assert!(bounded.truncated);
        assert!(bounded.compact_json.len() < 2_100);
    }

    #[test]
    fn normal_mode_emits_one_bounded_progress_record() {
        let mut reporter = Reporter::new(OutputFormat::Normal, Vec::new());
        assert!(reporter.supports_progress());
        reporter
            .emit(&CampaignEvent::TaskProgress {
                schema_version: CAMPAIGN_SCHEMA_VERSION,
                canonical_id: "Example0012".to_string(),
                index: 1,
                total: 2,
                elapsed_milliseconds: 12_000,
                inv_epochs: 3,
                proposed_clauses: 40,
                initialized_clauses: 12,
                core_admissions: 2,
                highest_w_index: None,
                highest_safe_fmb_frontier: Some(8),
            })
            .unwrap();
        let output = String::from_utf8(reporter.into_inner()).unwrap();
        assert!(output.contains("initialized=12"));
        assert!(output.contains("highest_w=unavailable"));
        assert!(output.contains("fmb_frontier=8"));
        assert!(output.len() < 512);
    }

    #[test]
    fn telemetry_off_timeout_retains_core_and_highest_w_progress() {
        let session = crate::telemetry::TelemetrySession::disabled();
        let handle = session.handle();
        handle.record_core_admission(4);
        handle.observe_max("cex.highest_w_index", 12);
        let telemetry = TelemetryRecord::from_report(&session.finish(), Path::new("/repository"));
        assert_eq!(telemetry.level, "off");

        let terminal = TerminalRecord::Timeout {
            failure: FailureRecord {
                origin: "run_control".to_string(),
                kind: "overall_timeout".to_string(),
                retryable: false,
                scope: "run_global".to_string(),
                detail: Some("deadline reached".to_string()),
                artifacts: Vec::new(),
            },
        };
        let mut task = result(terminal);
        task.telemetry = telemetry;
        let mut reporter = Reporter::new(OutputFormat::Normal, Vec::new());
        reporter
            .emit(&CampaignEvent::TaskResult {
                schema_version: CAMPAIGN_SCHEMA_VERSION,
                result: Box::new(task),
            })
            .unwrap();
        let output = String::from_utf8(reporter.into_inner()).unwrap();
        assert!(output.contains("core_admissions=1 highest_w=12"));
    }
}
