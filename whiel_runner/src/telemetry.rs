//! Versioned, observational synthesis telemetry.
//!
//! Telemetry is not part of the logical result. Aggregate counters are
//! lossless for the lifetime of one process. Detailed events use a bounded
//! background queue and report every dropped event.

use std::collections::{BTreeMap, BTreeSet};
use std::fs::{self, File};
use std::io::{self, BufWriter, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::mpsc::{self, SyncSender, TrySendError};
use std::sync::{Arc, Mutex};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

use serde::{Deserialize, Serialize};
use serde_json::Value;

pub const TELEMETRY_SCHEMA_VERSION: u64 = 6;
pub const DEFAULT_EVENT_QUEUE_CAPACITY: usize = 16_384;

// ------------------------------------------------------------
// Configuration And Public Records
// ------------------------------------------------------------

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TelemetryLevel {
    #[default]
    Off,
    Aggregate,
    Detailed,
}

#[derive(Clone, Debug)]
pub struct TelemetryConfig {
    root: PathBuf,
    level: TelemetryLevel,
    event_queue_capacity: usize,
}

impl TelemetryConfig {
    pub fn new(root: impl Into<PathBuf>, level: TelemetryLevel) -> Self {
        Self {
            root: root.into(),
            level,
            event_queue_capacity: DEFAULT_EVENT_QUEUE_CAPACITY,
        }
    }

    pub fn event_queue_capacity(mut self, capacity: usize) -> Result<Self, &'static str> {
        if capacity == 0 {
            return Err("the telemetry event queue must have positive capacity");
        }
        self.event_queue_capacity = capacity;
        Ok(self)
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReferenceParametersTelemetry {
    pub max_ra_ops: u64,
    pub max_selection_condition_nodes: u64,
    pub max_projection_excess: u64,
    pub max_output_arity: u64,
    pub max_clause_width: u64,
}

impl ReferenceParametersTelemetry {
    pub fn at_reference_stage(stage: u64) -> Self {
        Self {
            max_ra_ops: stage,
            max_selection_condition_nodes: stage,
            max_projection_excess: stage,
            max_output_arity: stage,
            max_clause_width: stage,
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReferenceFeatureSetTelemetry {
    pub enabled_ra_bases: Vec<String>,
    pub enabled_ra_operators: Vec<String>,
    pub enabled_atom_kinds: Vec<String>,
    pub enabled_literal_signs: Vec<String>,
}

impl ReferenceFeatureSetTelemetry {
    pub fn all_enabled() -> Self {
        Self {
            enabled_ra_bases: ["top", "empty", "relation", "singleton"]
                .map(str::to_string)
                .into(),
            enabled_ra_operators: ["selection", "projection", "product", "union", "difference"]
                .map(str::to_string)
                .into(),
            enabled_atom_kinds: ["equality", "containment"].map(str::to_string).into(),
            enabled_literal_signs: ["positive", "negative"].map(str::to_string).into(),
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct RunConfigurationTelemetry {
    pub task_canonical_id: String,
    pub overall_limit_nanoseconds: u64,
    pub search_limit_nanoseconds: u64,
    pub proof_casc_profile_id: String,
    pub proof_casc_initial_share_millionths: u32,
    pub proof_casc_retry_added_share_millionths: u32,
    pub proof_casc_share_scale: u32,
    pub proof_casc_allocation_formula: String,
    pub proof_casc_allocation_rounding: String,
    pub maintenance_retry_increment_nanoseconds: Vec<u64>,
    pub bulk_init_limit_nanoseconds: u64,
    pub bulk_maint_limit_nanoseconds: u64,
    pub init_first_attempt_limit_nanoseconds: Vec<u64>,
    pub init_attempt_limit_nanoseconds: Vec<u64>,
    pub search_term_limit_nanoseconds: u64,
    pub search_term_retry_increment_nanoseconds: Vec<u64>,
    pub final_certification_limit_nanoseconds: Option<u64>,
    pub max_vampire_processes: u64,
    pub cex_reserved_vampire_processes: u64,
    pub max_inv_vampire_processes: u64,
    pub max_cpu_workers: u64,
    pub encoding_worker_count: u64,
    pub admit_higher_w_layers: bool,
    pub w_fresh_batch_size: u64,
    pub w_retry_batch_size: u64,
    pub w_initial_limit_nanoseconds: u64,
    pub w_limit_growth: String,
    pub log_maintenance_history: bool,
    pub fail_on_history_log_error: bool,
    pub proposal_realization_id: String,
    pub proposal_realization_version: u64,
    pub reference_schedule_id: String,
    pub reference_features: ReferenceFeatureSetTelemetry,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct InvEpochTelemetry {
    pub epoch: u64,
    pub next_reference_stage: u64,
    pub next_reference_parameters: ReferenceParametersTelemetry,
    pub reference_features: ReferenceFeatureSetTelemetry,
    pub proposal_size: u64,
    pub catalog_size: u64,
    pub core_size: u64,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct FormulaShape {
    pub clause_width: u64,
    pub positive_literals: u64,
    pub negative_literals: u64,
    pub equalities: u64,
    pub containments: u64,
    pub ra_root_constructors: BTreeMap<String, u64>,
    pub ra_nodes: u64,
    pub ra_cost: u64,
    pub ra_cost_bin: String,
    pub selection_condition_nodes: u64,
    pub projection_count: u64,
    pub maximum_projection_excess: u64,
    pub output_arity: u64,
    pub constant_occurrences: u64,
    pub relation_occurrences: u64,
    pub serialized_size_bytes: u64,
    pub serialized_size_bin: String,
    pub normalized_structural_skeleton: String,
    pub operator_provenance: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FormulaBirthTelemetry {
    pub clause_id: Option<u64>,
    pub registered_unique: bool,
    pub stage: u64,
    pub source_id: String,
    pub shape: FormulaShape,
    pub minimal_eligibility: ReferenceParametersTelemetry,
    pub binding_dimensions: Vec<String>,
    pub schedule_slack_at_birth: ReferenceParametersTelemetry,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WClauseTelemetry {
    pub clause_id: u64,
    pub w_indices: Vec<u64>,
    pub shape: Option<FormulaShape>,
    pub reference_eligibility: Option<ReferenceParametersTelemetry>,
    pub reference_eligibility_note: String,
}

/// One Lean-constructed W formula prepared for CEX search, including formulas
/// that are never published to the INV Catalog.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WAttemptFormulaTelemetry {
    pub w_index: u64,
    pub shape: FormulaShape,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct WaveTelemetry {
    pub stage: u64,
    pub parameters: ReferenceParametersTelemetry,
    pub reference_features: ReferenceFeatureSetTelemetry,
    pub page_count: u64,
    pub worker_stage_batch_evaluations: u64,
    pub prior_slice_evaluations: u64,
    /// Exact scalar population from Lean. Occurrences removed by equality
    /// deduplication have no per-occurrence identity in the current protocol.
    pub stage_delta_decoded_formula_occurrences: Option<u64>,
    pub stage_delta_equality_distinct_formulas: Option<u64>,
    pub stage_delta_equality_deduplicated_occurrences: Option<u64>,
    pub cumulative_decoded_formula_occurrences: Option<u64>,
    pub cumulative_equality_distinct_formulas: Option<u64>,
    pub cumulative_equality_deduplicated_occurrences: Option<u64>,
    /// Stable stage-local work units from the selected proposal realization.
    pub generator_work_units: u64,
    /// Lower-width incremental traversal nodes; zero for the reference path.
    pub fresh_traversal_nodes: u64,
    pub fresh_no_fresh_prunes: u64,
    pub fresh_too_short_prunes: u64,
    pub emitted_formulas: u64,
    pub wave_registration_attempts: u64,
    pub registered_unique_formulas: u64,
    pub previously_seen_formulas: u64,
    pub cumulative_registration_rechecks: u64,
    pub cumulative_proposal_size: u64,
    pub cumulative_catalog_size: u64,
    pub lean_enumeration_nanoseconds: Option<u64>,
    pub transport_and_rust_validation_nanoseconds: Option<u64>,
    pub reference_wave_inclusive_nanoseconds: u64,
    pub registration_and_formula_preparation_nanoseconds: Option<u64>,
    pub catalog_registration_nanoseconds: Option<u64>,
    pub formula_body_preparation_nanoseconds: Option<u64>,
}

#[derive(Clone, Copy, Debug)]
pub struct WaveRegistrationTelemetry {
    pub stage: u64,
    pub wave_registration_attempts: u64,
    pub registered_unique_formulas: u64,
    pub previously_seen_formulas: u64,
    pub cumulative_registration_rechecks: u64,
    pub cumulative_catalog_size: u64,
    pub registration_and_formula_preparation_duration: Duration,
    pub catalog_registration_duration: Duration,
    pub formula_body_preparation_duration: Duration,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct MemoryTelemetry {
    pub process_peak_rss_bytes: Option<u64>,
    pub waited_children_peak_rss_bytes: Option<u64>,
    pub source: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TelemetrySnapshot {
    pub schema_version: u64,
    pub level: TelemetryLevel,
    pub measurement_complete: bool,
    pub elapsed_nanoseconds: u64,
    pub counters: BTreeMap<String, u64>,
    pub duration_nanoseconds: BTreeMap<String, u64>,
    pub dispositions: BTreeMap<String, u64>,
    pub run_configuration: Option<RunConfigurationTelemetry>,
    pub inv_epochs: Vec<InvEpochTelemetry>,
    pub waves: Vec<WaveTelemetry>,
    pub formula_births: Vec<FormulaBirthTelemetry>,
    pub w_clauses: Vec<WClauseTelemetry>,
    pub w_attempt_formulas: Vec<WAttemptFormulaTelemetry>,
    pub final_core_clause_ids: Vec<u64>,
    pub final_formula_dispositions: BTreeMap<u64, String>,
    pub terminal_outcome: Option<String>,
    pub derived: DerivedTelemetry,
    pub dropped_detailed_events: u64,
    pub errors: Vec<String>,
    pub missing_measurements: Vec<String>,
    pub limitations: Vec<String>,
    pub memory: MemoryTelemetry,
}

/// Constant-size telemetry needed for one campaign progress record.
///
/// Unlike [`TelemetryHandle::snapshot`], this view does not clone collections,
/// derive aggregate analyses, or sample process memory.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct ProgressTelemetrySnapshot {
    pub(crate) inv_epochs: u64,
    pub(crate) proposed_clauses: u64,
    pub(crate) initialized_clauses: u64,
    pub(crate) core_admissions: u64,
    pub(crate) highest_w_index: Option<u64>,
    pub(crate) highest_safe_fmb_frontier: Option<u64>,
}

const NO_PROGRESS_MAXIMUM: u64 = u64::MAX;

/// Fixed-size live progress shared by every telemetry level, including off.
///
/// This keeps periodic and terminal status available without enabling the
/// aggregate maps, detailed event queue, writer thread, or derived analyses.
#[derive(Debug)]
struct ProgressTelemetry {
    inv_epochs: AtomicU64,
    proposed_clauses: AtomicU64,
    initialized_clauses: AtomicU64,
    core_admissions: AtomicU64,
    highest_w_index: AtomicU64,
    highest_safe_fmb_frontier: AtomicU64,
}

impl Default for ProgressTelemetry {
    fn default() -> Self {
        Self {
            inv_epochs: AtomicU64::new(0),
            proposed_clauses: AtomicU64::new(0),
            initialized_clauses: AtomicU64::new(0),
            core_admissions: AtomicU64::new(0),
            highest_w_index: AtomicU64::new(NO_PROGRESS_MAXIMUM),
            highest_safe_fmb_frontier: AtomicU64::new(NO_PROGRESS_MAXIMUM),
        }
    }
}

impl ProgressTelemetry {
    fn snapshot(&self) -> ProgressTelemetrySnapshot {
        ProgressTelemetrySnapshot {
            inv_epochs: self.inv_epochs.load(Ordering::Relaxed),
            proposed_clauses: self.proposed_clauses.load(Ordering::Relaxed),
            initialized_clauses: self.initialized_clauses.load(Ordering::Relaxed),
            core_admissions: self.core_admissions.load(Ordering::Relaxed),
            highest_w_index: load_optional_maximum(&self.highest_w_index),
            highest_safe_fmb_frontier: load_optional_maximum(&self.highest_safe_fmb_frontier),
        }
    }
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct DerivedTelemetry {
    pub stage_yield: Vec<StageYieldTelemetry>,
    pub shape_yield: Vec<ShapeYieldTelemetry>,
    pub parameter_dimension_yield: Vec<ParameterDimensionYieldTelemetry>,
    pub solver_yield: SolverYieldTelemetry,
    pub time_by_disposition_nanoseconds: BTreeMap<String, u64>,
    pub final_core_births: Vec<FinalCoreBirthTelemetry>,
    pub schedule_imbalance: Vec<ScheduleImbalanceTelemetry>,
    pub final_core_parameter_envelope: Option<ReferenceParametersTelemetry>,
    pub formulas_exceeding_final_core_envelope: BTreeMap<String, u64>,
    pub note: String,
}

/// Terminal survival, pruning, and Core yield for one exact value of one
/// reference-enumerator parameter. Each ordinary formula is attributed by its
/// recorded minimal-eligibility vector, not merely by the stage that emitted it.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct ParameterDimensionYieldTelemetry {
    pub dimension: String,
    pub minimal_eligibility_value: u64,
    pub registered_unique_population: u64,
    pub terminal_core_population: u64,
    pub emitted_to_terminal_core_numerator: u64,
    pub emitted_to_terminal_core_denominator: u64,
    pub attributed_clause_solver_attempts: u64,
    pub solver_calls_per_terminal_core_numerator: u64,
    pub solver_calls_per_terminal_core_denominator: u64,
    pub final_disposition_populations: BTreeMap<String, u64>,
    /// Registered formulas with a known non-pruned terminal INV disposition.
    pub survival_numerator: u64,
    /// Registered formulas with a terminal disposition prefixed by `pruned_`.
    pub pruning_numerator: u64,
    /// All registered unique formulas in this dimension/value row.
    pub survival_pruning_denominator: u64,
    /// Formulas counted in either the survival or pruning numerator.
    pub terminal_disposition_classified_population: u64,
    /// Formulas without a classified terminal disposition.
    pub terminal_disposition_unclassified_population: u64,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct StageYieldTelemetry {
    pub stage: u64,
    pub registered_unique_population: u64,
    pub final_core_population: u64,
    pub emitted_to_core_numerator: u64,
    pub emitted_to_core_denominator: u64,
    pub attributed_clause_solver_attempts: u64,
    pub solver_calls_per_core_numerator: u64,
    pub solver_calls_per_core_denominator: u64,
    pub final_disposition_populations: BTreeMap<String, u64>,
    pub survival_numerator: u64,
    pub pruning_numerator: u64,
    pub survival_pruning_denominator: u64,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct ShapeYieldTelemetry {
    pub shape_key: String,
    pub registered_unique_population: u64,
    pub final_core_population: u64,
    pub emitted_to_core_numerator: u64,
    pub emitted_to_core_denominator: u64,
    pub attributed_clause_solver_attempts: u64,
    pub solver_calls_per_core_numerator: u64,
    pub solver_calls_per_core_denominator: u64,
    pub final_disposition_populations: BTreeMap<String, u64>,
    pub survival_numerator: u64,
    pub pruning_numerator: u64,
    pub survival_pruning_denominator: u64,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct SolverYieldTelemetry {
    pub total_vampire_requests: u64,
    pub attributed_clause_solver_attempts: u64,
    pub final_core_population: u64,
    pub solver_calls_per_core_numerator: u64,
    pub solver_calls_per_core_denominator: u64,
    pub attribution_note: String,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct FinalCoreBirthTelemetry {
    pub clause_id: u64,
    pub source_kind: String,
    pub reference_stage: Option<u64>,
    pub w_indices: Vec<u64>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ScheduleImbalanceTelemetry {
    pub dimension: String,
    pub first_useful_value: Option<u64>,
    pub first_useful_stage: Option<u64>,
    pub latest_first_useful_stage: u64,
    pub intervening_stage_count: u64,
    pub registered_formulas_while_waiting: u64,
}

#[derive(Clone, Debug)]
pub struct TelemetryReport {
    pub snapshot: TelemetrySnapshot,
    pub summary_path: Option<PathBuf>,
    pub events_path: Option<PathBuf>,
}

// ------------------------------------------------------------
// Session And Hot-Path Handle
// ------------------------------------------------------------

#[derive(Clone, Debug)]
pub struct TelemetryHandle {
    inner: Option<Arc<TelemetryInner>>,
    progress: Arc<ProgressTelemetry>,
}

#[derive(Debug)]
pub struct TelemetrySpan {
    telemetry: TelemetryHandle,
    key: &'static str,
    started: Option<Instant>,
}

impl TelemetrySpan {
    pub fn finish(mut self) -> Option<Duration> {
        self.finish_inner()
    }

    fn finish_inner(&mut self) -> Option<Duration> {
        let elapsed = self.started.take().map(|started| started.elapsed())?;
        self.telemetry.add_duration(self.key, elapsed);
        Some(elapsed)
    }
}

impl Drop for TelemetrySpan {
    fn drop(&mut self) {
        let _ = self.finish_inner();
    }
}

#[derive(Debug)]
pub struct TelemetrySession {
    handle: TelemetryHandle,
    root: Option<PathBuf>,
    writer: Option<JoinHandle<()>>,
}

#[derive(Debug)]
struct TelemetryInner {
    level: TelemetryLevel,
    started: Instant,
    aggregate: Mutex<TelemetryAggregate>,
    detailed: Option<SyncSender<DetailedMessage>>,
    writer_stop: Arc<AtomicBool>,
    dropped: AtomicU64,
    writer_error: Arc<Mutex<Option<String>>>,
}

#[derive(Debug, Default)]
struct TelemetryAggregate {
    counters: BTreeMap<String, u64>,
    durations: BTreeMap<String, u64>,
    dispositions: BTreeMap<String, u64>,
    run_configuration: Option<RunConfigurationTelemetry>,
    inv_epochs: Vec<InvEpochTelemetry>,
    waves: Vec<WaveTelemetry>,
    formula_births: Vec<FormulaBirthTelemetry>,
    w_clauses: BTreeMap<u64, BTreeSet<u64>>,
    w_clause_shapes: BTreeMap<u64, (FormulaShape, Option<ReferenceParametersTelemetry>)>,
    w_attempt_formula_shapes: BTreeMap<u64, FormulaShape>,
    initialized_clause_ids: BTreeSet<u64>,
    core_clause_ids: BTreeSet<u64>,
    final_formula_dispositions: BTreeMap<u64, String>,
    clause_solver_attempts: BTreeMap<u64, u64>,
    terminal_outcome: Option<String>,
    errors: Vec<String>,
}

#[derive(Debug)]
enum DetailedMessage {
    Event(DetailedEvent),
}

#[derive(Debug, Serialize)]
struct DetailedEvent {
    schema_version: u64,
    elapsed_nanoseconds: u64,
    kind: String,
    payload: Value,
}

impl TelemetrySession {
    pub fn disabled() -> Self {
        Self {
            handle: TelemetryHandle::disabled(),
            root: None,
            writer: None,
        }
    }

    /// Start one best-effort telemetry session.
    ///
    /// Setup failure disables output and marks the eventual report incomplete;
    /// it never changes the synthesis result.
    pub fn start(config: TelemetryConfig) -> Self {
        if config.level == TelemetryLevel::Off {
            return Self::disabled();
        }
        let mut setup_error = None;
        if let Err(error) = fs::create_dir_all(&config.root) {
            setup_error = Some(format!("create telemetry directory: {error}"));
        }

        let writer_error = Arc::new(Mutex::new(None));
        let writer_stop = Arc::new(AtomicBool::new(false));
        let (detailed, writer) =
            if config.level == TelemetryLevel::Detailed && setup_error.is_none() {
                let events_path = config.root.join("events.jsonl");
                match File::create(&events_path) {
                    Ok(file) => {
                        let (sender, receiver) = mpsc::sync_channel(config.event_queue_capacity);
                        let thread_error = Arc::clone(&writer_error);
                        let thread_stop = Arc::clone(&writer_stop);
                        let writer = thread::Builder::new()
                            .name("whiel-telemetry-writer".to_string())
                            .spawn(move || {
                                write_detailed_events(file, receiver, thread_stop, thread_error)
                            })
                            .ok();
                        if writer.is_none() {
                            setup_error = Some("start telemetry writer thread".to_string());
                            (None, None)
                        } else {
                            // The thread writes through a separate cell. Its final
                            // error is copied into the aggregate during finish.
                            (Some(sender), writer)
                        }
                    }
                    Err(error) => {
                        setup_error = Some(format!("create detailed telemetry stream: {error}"));
                        (None, None)
                    }
                }
            } else {
                (None, None)
            };

        let mut aggregate = TelemetryAggregate::default();
        if let Some(error) = setup_error {
            aggregate.errors.push(error);
        }
        let inner = Arc::new(TelemetryInner {
            level: config.level,
            started: Instant::now(),
            aggregate: Mutex::new(aggregate),
            detailed,
            writer_stop,
            dropped: AtomicU64::new(0),
            writer_error,
        });
        Self {
            handle: TelemetryHandle {
                inner: Some(inner),
                progress: Arc::new(ProgressTelemetry::default()),
            },
            root: Some(config.root),
            writer,
        }
    }

    pub fn handle(&self) -> TelemetryHandle {
        self.handle.clone()
    }

    /// Settle the writer and create the terminal report.
    ///
    /// Callers must first quiesce every runtime component that owns a cloned
    /// handle. Production symbolic orchestration does so before this boundary.
    pub fn finish(mut self) -> TelemetryReport {
        if let Some(inner) = &self.handle.inner {
            inner.writer_stop.store(true, Ordering::Release);
        }
        if let Some(writer) = self.writer.take() {
            // The detailed stream is part of the task's settled measurement.
            // Join it before taking the summary snapshot so no writer can
            // mutate an artifact after the task result is published.
            if writer.join().is_err()
                && let Some(inner) = &self.handle.inner
            {
                inner.record_error("telemetry writer panicked".to_string());
            }
        }

        let mut snapshot = self.handle.snapshot();
        let mut summary_path = None;
        let events_path = self.root.as_ref().and_then(|root| {
            let path = root.join("events.jsonl");
            path.exists().then_some(path)
        });
        if let Some(root) = &self.root {
            let path = root.join("summary.json");
            match write_json(&path, &snapshot) {
                Ok(()) => summary_path = Some(path),
                Err(error) => {
                    snapshot.measurement_complete = false;
                    snapshot
                        .errors
                        .push(format!("write telemetry summary: {error}"));
                }
            }
        }
        TelemetryReport {
            snapshot,
            summary_path,
            events_path,
        }
    }
}

impl TelemetryHandle {
    pub fn disabled() -> Self {
        Self {
            inner: None,
            progress: Arc::new(ProgressTelemetry::default()),
        }
    }

    pub fn level(&self) -> TelemetryLevel {
        self.inner
            .as_ref()
            .map_or(TelemetryLevel::Off, |inner| inner.level)
    }

    pub fn is_enabled(&self) -> bool {
        self.inner.is_some()
    }

    pub fn start_span(&self) -> Option<Instant> {
        self.is_enabled().then(Instant::now)
    }

    /// Record one inclusive span on every return path in its lexical scope.
    pub fn span(&self, key: &'static str) -> Option<TelemetrySpan> {
        self.is_enabled().then(|| TelemetrySpan {
            telemetry: self.clone(),
            key,
            started: Some(Instant::now()),
        })
    }

    pub fn finish_span(
        &self,
        key: impl Into<String>,
        started: Option<Instant>,
    ) -> Option<Duration> {
        let elapsed = started.map(|started| started.elapsed())?;
        self.add_duration(key, elapsed);
        Some(elapsed)
    }

    pub fn increment<K>(&self, key: K, amount: u64)
    where
        K: AsRef<str> + Into<String>,
    {
        match key.as_ref() {
            "inv.epochs" => {
                atomic_saturating_add(&self.progress.inv_epochs, amount);
            }
            "catalog.registered_unique" => {
                atomic_saturating_add(&self.progress.proposed_clauses, amount);
            }
            _ => {}
        }
        let Some(inner) = &self.inner else { return };
        let mut aggregate = inner.lock_aggregate();
        saturating_add(&mut aggregate.counters, key.into(), amount);
    }

    pub fn observe_max<K>(&self, key: K, observed: u64)
    where
        K: AsRef<str> + Into<String>,
    {
        match key.as_ref() {
            "cex.highest_w_index" => {
                atomic_observe_max(&self.progress.highest_w_index, observed);
            }
            "cex.highest_safe_fmb_frontier" => {
                atomic_observe_max(&self.progress.highest_safe_fmb_frontier, observed);
            }
            _ => {}
        }
        let Some(inner) = &self.inner else { return };
        let mut aggregate = inner.lock_aggregate();
        let value = aggregate.counters.entry(key.into()).or_default();
        *value = (*value).max(observed);
    }

    pub fn add_duration(&self, key: impl Into<String>, duration: Duration) {
        let Some(inner) = &self.inner else { return };
        let nanoseconds = duration.as_nanos().min(u128::from(u64::MAX)) as u64;
        let mut aggregate = inner.lock_aggregate();
        saturating_add(&mut aggregate.durations, key.into(), nanoseconds);
    }

    pub fn record_disposition(&self, disposition: impl Into<String>, amount: u64) {
        let Some(inner) = &self.inner else { return };
        let mut aggregate = inner.lock_aggregate();
        saturating_add(&mut aggregate.dispositions, disposition.into(), amount);
    }

    /// Record clauses whose initialization status has durably become proved.
    /// Duplicate observations are harmless and do not inflate progress.
    pub(crate) fn record_initialized_clauses(&self, clause_ids: impl IntoIterator<Item = u64>) {
        if let Some(inner) = &self.inner {
            let mut aggregate = inner.lock_aggregate();
            aggregate.initialized_clause_ids.extend(clause_ids);
            self.progress.initialized_clauses.store(
                u64::try_from(aggregate.initialized_clause_ids.len()).unwrap_or(u64::MAX),
                Ordering::Relaxed,
            );
        } else {
            let amount = clause_ids
                .into_iter()
                .fold(0_u64, |count, _| count.saturating_add(1));
            atomic_saturating_add(&self.progress.initialized_clauses, amount);
        }
    }

    pub fn record_wave(&self, wave: WaveTelemetry) {
        let Some(inner) = &self.inner else { return };
        inner.lock_aggregate().waves.push(wave);
    }

    /// Record the immutable configuration for one symbolic run.
    /// Repeating the same configuration is harmless. A conflicting record
    /// marks telemetry incomplete without changing synthesis behavior.
    pub fn record_run_configuration(&self, configuration: RunConfigurationTelemetry) {
        let Some(inner) = &self.inner else { return };
        let mut aggregate = inner.lock_aggregate();
        match &aggregate.run_configuration {
            None => aggregate.run_configuration = Some(configuration),
            Some(existing) if existing == &configuration => {}
            Some(_) => aggregate
                .errors
                .push("conflicting symbolic run configuration telemetry".to_string()),
        }
    }

    /// Record the parameter vector visible at one INV epoch boundary.
    pub fn record_inv_epoch(&self, epoch: InvEpochTelemetry) {
        let Some(inner) = &self.inner else { return };
        inner.lock_aggregate().inv_epochs.push(epoch);
    }

    pub fn update_wave_registration(&self, update: WaveRegistrationTelemetry) {
        let Some(inner) = &self.inner else { return };
        let mut aggregate = inner.lock_aggregate();
        let Some(wave) = aggregate
            .waves
            .iter_mut()
            .rev()
            .find(|wave| wave.stage == update.stage)
        else {
            aggregate.errors.push(format!(
                "catalog telemetry has no wave for stage {}",
                update.stage
            ));
            return;
        };
        wave.wave_registration_attempts = update.wave_registration_attempts;
        wave.registered_unique_formulas = update.registered_unique_formulas;
        wave.previously_seen_formulas = update.previously_seen_formulas;
        wave.cumulative_registration_rechecks = update.cumulative_registration_rechecks;
        wave.cumulative_catalog_size = update.cumulative_catalog_size;
        wave.registration_and_formula_preparation_nanoseconds = Some(
            update
                .registration_and_formula_preparation_duration
                .as_nanos()
                .min(u128::from(u64::MAX)) as u64,
        );
        wave.catalog_registration_nanoseconds = Some(
            update
                .catalog_registration_duration
                .as_nanos()
                .min(u128::from(u64::MAX)) as u64,
        );
        wave.formula_body_preparation_nanoseconds = Some(
            update
                .formula_body_preparation_duration
                .as_nanos()
                .min(u128::from(u64::MAX)) as u64,
        );
    }

    pub fn record_formula_birth(&self, birth: FormulaBirthTelemetry) {
        let Some(inner) = &self.inner else { return };
        inner.lock_aggregate().formula_births.push(birth);
    }

    pub fn record_w_clause(
        &self,
        clause_id: u64,
        w_index: u64,
        shape: Option<(FormulaShape, Option<ReferenceParametersTelemetry>)>,
    ) {
        let Some(inner) = &self.inner else { return };
        let mut aggregate = inner.lock_aggregate();
        aggregate
            .w_clauses
            .entry(clause_id)
            .or_default()
            .insert(w_index);
        if let Some(shape) = shape {
            match aggregate.w_clause_shapes.get(&clause_id) {
                None => {
                    aggregate.w_clause_shapes.insert(clause_id, shape);
                }
                Some(existing) if existing == &shape => {}
                Some(_) => aggregate.errors.push(format!(
                    "conflicting W-clause shape telemetry for clause {clause_id}"
                )),
            }
        }
    }

    pub fn record_w_attempt_formula(&self, w_index: u64, shape: FormulaShape) {
        let Some(inner) = &self.inner else { return };
        let mut aggregate = inner.lock_aggregate();
        match aggregate.w_attempt_formula_shapes.get(&w_index) {
            None => {
                aggregate.w_attempt_formula_shapes.insert(w_index, shape);
            }
            Some(existing) if existing == &shape => {}
            Some(_) => aggregate.errors.push(format!(
                "conflicting attempted W-formula shape telemetry for index {w_index}"
            )),
        }
    }

    /// Attribute one per-clause solver query to its dense Catalog identity.
    /// Bulk and non-clause queries remain visible only in global counters.
    pub fn record_clause_solver_attempt(&self, clause_id: u64) {
        let Some(inner) = &self.inner else { return };
        let mut aggregate = inner.lock_aggregate();
        let attempts = aggregate
            .clause_solver_attempts
            .entry(clause_id)
            .or_default();
        *attempts = attempts.saturating_add(1);
    }

    /// Replace the observed terminal status for one clause. This is a
    /// snapshot label, not an additional semantic Houdini disposition.
    pub fn record_final_formula_disposition(&self, clause_id: u64, disposition: impl Into<String>) {
        let Some(inner) = &self.inner else { return };
        inner
            .lock_aggregate()
            .final_formula_dispositions
            .insert(clause_id, disposition.into());
    }

    pub fn record_core_admission(&self, clause_id: u64) {
        if let Some(inner) = &self.inner {
            let mut aggregate = inner.lock_aggregate();
            aggregate.core_clause_ids.insert(clause_id);
            self.progress.core_admissions.store(
                u64::try_from(aggregate.core_clause_ids.len()).unwrap_or(u64::MAX),
                Ordering::Relaxed,
            );
        } else {
            // Runtime callers report only the durable non-member -> Core
            // transition. Keeping this scalar avoids a ClauseId set in off mode.
            atomic_saturating_add(&self.progress.core_admissions, 1);
        }
    }

    pub fn record_terminal_outcome(&self, outcome: impl Into<String>) {
        let Some(inner) = &self.inner else { return };
        inner.lock_aggregate().terminal_outcome = Some(outcome.into());
    }

    pub fn event(&self, kind: impl Into<String>, payload: Value) {
        let Some(inner) = &self.inner else { return };
        let Some(sender) = &inner.detailed else {
            return;
        };
        if inner.writer_stop.load(Ordering::Acquire) {
            inner.dropped.fetch_add(1, Ordering::Relaxed);
            return;
        }
        let message = DetailedMessage::Event(DetailedEvent {
            schema_version: TELEMETRY_SCHEMA_VERSION,
            elapsed_nanoseconds: elapsed_nanoseconds(inner.started),
            kind: kind.into(),
            payload,
        });
        match sender.try_send(message) {
            Ok(()) => {}
            Err(TrySendError::Full(_)) | Err(TrySendError::Disconnected(_)) => {
                inner.dropped.fetch_add(1, Ordering::Relaxed);
            }
        }
    }

    /// Build a detailed payload only when detailed telemetry is enabled.
    /// The subsequent bounded send can still drop a constructed payload.
    pub fn event_with(&self, kind: impl Into<String>, payload: impl FnOnce() -> Value) {
        let Some(inner) = &self.inner else { return };
        if inner.detailed.is_none() {
            return;
        }
        self.event(kind, payload());
    }

    pub fn record_error(&self, error: impl Into<String>) {
        if let Some(inner) = &self.inner {
            inner.record_error(error.into());
        }
    }

    /// Read only the fixed-size counters needed for live campaign progress.
    pub(crate) fn progress_snapshot(&self) -> ProgressTelemetrySnapshot {
        self.progress.snapshot()
    }

    pub fn snapshot(&self) -> TelemetrySnapshot {
        let Some(inner) = &self.inner else {
            let progress = self.progress.snapshot();
            let mut counters = BTreeMap::new();
            counters.insert("inv.epochs".to_string(), progress.inv_epochs);
            counters.insert(
                "catalog.registered_unique".to_string(),
                progress.proposed_clauses,
            );
            if let Some(value) = progress.highest_w_index {
                counters.insert("cex.highest_w_index".to_string(), value);
            }
            if let Some(value) = progress.highest_safe_fmb_frontier {
                counters.insert("cex.highest_safe_fmb_frontier".to_string(), value);
            }
            let mut dispositions = BTreeMap::new();
            dispositions.insert("core_admission".to_string(), progress.core_admissions);
            return TelemetrySnapshot {
                schema_version: TELEMETRY_SCHEMA_VERSION,
                level: TelemetryLevel::Off,
                measurement_complete: true,
                elapsed_nanoseconds: 0,
                counters,
                duration_nanoseconds: BTreeMap::new(),
                dispositions,
                run_configuration: None,
                inv_epochs: Vec::new(),
                waves: Vec::new(),
                formula_births: Vec::new(),
                w_clauses: Vec::new(),
                w_attempt_formulas: Vec::new(),
                final_core_clause_ids: Vec::new(),
                final_formula_dispositions: BTreeMap::new(),
                terminal_outcome: None,
                derived: DerivedTelemetry::default(),
                dropped_detailed_events: 0,
                errors: Vec::new(),
                missing_measurements: Vec::new(),
                limitations: Vec::new(),
                memory: sample_peak_memory(),
            };
        };
        let aggregate = inner.lock_aggregate();
        let dropped = inner.dropped.load(Ordering::Relaxed);
        let mut errors = aggregate.errors.clone();
        if let Some(error) = inner
            .writer_error
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .clone()
        {
            errors.push(error);
        }
        let final_core_clause_ids = aggregate
            .core_clause_ids
            .iter()
            .copied()
            .collect::<Vec<_>>();
        let w_clauses = aggregate
            .w_clauses
            .iter()
            .map(|(clause_id, w_indices)| WClauseTelemetry {
                clause_id: *clause_id,
                w_indices: w_indices.iter().copied().collect(),
                shape: aggregate
                    .w_clause_shapes
                    .get(clause_id)
                    .map(|(shape, _)| shape.clone()),
                reference_eligibility: aggregate
                    .w_clause_shapes
                    .get(clause_id)
                    .and_then(|(_, eligibility)| eligibility.clone()),
                reference_eligibility_note: aggregate.w_clause_shapes.get(clause_id).map_or_else(
                    || "unavailable".to_string(),
                    |(_, eligibility)| {
                        if eligibility.is_some() {
                            "syntactic_disjunctive_clause".to_string()
                        } else {
                            "not_applicable_to_general_qf_w_formula".to_string()
                        }
                    },
                ),
            })
            .collect::<Vec<_>>();
        let w_attempt_formulas = aggregate
            .w_attempt_formula_shapes
            .iter()
            .map(|(w_index, shape)| WAttemptFormulaTelemetry {
                w_index: *w_index,
                shape: shape.clone(),
            })
            .collect::<Vec<_>>();
        let terminal_outcome = aggregate.terminal_outcome.clone();
        let memory = sample_peak_memory();
        let missing_measurements = required_measurement_gaps(&aggregate, &memory);
        let limitations = measurement_limitations();
        let derived = derive_telemetry(DerivedTelemetryInput {
            waves: &aggregate.waves,
            births: &aggregate.formula_births,
            core: &aggregate.core_clause_ids,
            final_dispositions: &aggregate.final_formula_dispositions,
            clause_solver_attempts: &aggregate.clause_solver_attempts,
            w_clauses: &aggregate.w_clauses,
            counters: &aggregate.counters,
            durations: &aggregate.durations,
            terminal: terminal_outcome.as_deref(),
        });
        TelemetrySnapshot {
            schema_version: TELEMETRY_SCHEMA_VERSION,
            level: inner.level,
            measurement_complete: errors.is_empty()
                && dropped == 0
                && missing_measurements.is_empty(),
            elapsed_nanoseconds: elapsed_nanoseconds(inner.started),
            counters: aggregate.counters.clone(),
            duration_nanoseconds: aggregate.durations.clone(),
            dispositions: aggregate.dispositions.clone(),
            run_configuration: aggregate.run_configuration.clone(),
            inv_epochs: aggregate.inv_epochs.clone(),
            waves: aggregate.waves.clone(),
            formula_births: aggregate.formula_births.clone(),
            w_clauses,
            w_attempt_formulas,
            final_core_clause_ids,
            final_formula_dispositions: aggregate.final_formula_dispositions.clone(),
            terminal_outcome,
            derived,
            dropped_detailed_events: dropped,
            errors,
            missing_measurements,
            limitations,
            memory,
        }
    }
}

impl TelemetryInner {
    fn lock_aggregate(&self) -> std::sync::MutexGuard<'_, TelemetryAggregate> {
        self.aggregate
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
    }

    fn record_error(&self, error: String) {
        self.lock_aggregate().errors.push(error);
    }
}

struct DerivedTelemetryInput<'a> {
    waves: &'a [WaveTelemetry],
    births: &'a [FormulaBirthTelemetry],
    core: &'a BTreeSet<u64>,
    final_dispositions: &'a BTreeMap<u64, String>,
    clause_solver_attempts: &'a BTreeMap<u64, u64>,
    w_clauses: &'a BTreeMap<u64, BTreeSet<u64>>,
    counters: &'a BTreeMap<String, u64>,
    durations: &'a BTreeMap<String, u64>,
    terminal: Option<&'a str>,
}

fn derive_telemetry(input: DerivedTelemetryInput<'_>) -> DerivedTelemetry {
    let DerivedTelemetryInput {
        waves,
        births,
        core,
        final_dispositions,
        clause_solver_attempts,
        w_clauses,
        counters,
        durations,
        terminal,
    } = input;
    let mut by_stage = BTreeMap::<u64, YieldAccumulator>::new();
    let mut by_shape = BTreeMap::<String, YieldAccumulator>::new();
    let mut by_parameter = BTreeMap::<(String, u64), YieldAccumulator>::new();
    for birth in births.iter().filter(|birth| birth.registered_unique) {
        let clause_id = birth.clause_id;
        let is_core = clause_id.is_some_and(|id| core.contains(&id));
        let attempts = clause_id
            .and_then(|id| clause_solver_attempts.get(&id).copied())
            .unwrap_or(0);
        let disposition = clause_id.and_then(|id| final_dispositions.get(&id));
        by_stage
            .entry(birth.stage)
            .or_default()
            .record(is_core, attempts, disposition);
        by_shape
            .entry(formula_shape_key(&birth.shape))
            .or_default()
            .record(is_core, attempts, disposition);
        for (dimension, value) in parameter_dimensions(&birth.minimal_eligibility) {
            by_parameter
                .entry((dimension.to_string(), value))
                .or_default()
                .record(is_core, attempts, disposition);
        }
    }
    for wave in waves {
        let stage = by_stage.entry(wave.stage).or_default();
        stage.population = stage.population.max(wave.registered_unique_formulas);
    }
    let stage_yield = by_stage
        .into_iter()
        .map(|(stage, yield_data)| yield_data.into_stage(stage))
        .collect();
    let shape_yield = by_shape
        .into_iter()
        .map(|(shape_key, yield_data)| yield_data.into_shape(shape_key))
        .collect();
    let parameter_dimension_yield = by_parameter
        .into_iter()
        .map(|((dimension, value), yield_data)| yield_data.into_parameter(dimension, value))
        .collect();

    let core_births = births
        .iter()
        .filter(|birth| {
            birth.registered_unique && birth.clause_id.is_some_and(|id| core.contains(&id))
        })
        .collect::<Vec<_>>();
    let final_core_births = core
        .iter()
        .map(|clause_id| {
            if let Some(birth) = core_births
                .iter()
                .find(|birth| birth.clause_id == Some(*clause_id))
            {
                FinalCoreBirthTelemetry {
                    clause_id: *clause_id,
                    source_kind: "reference".to_string(),
                    reference_stage: Some(birth.stage),
                    w_indices: Vec::new(),
                }
            } else if let Some(w_indices) = w_clauses.get(clause_id) {
                FinalCoreBirthTelemetry {
                    clause_id: *clause_id,
                    source_kind: "w_layer".to_string(),
                    reference_stage: None,
                    w_indices: w_indices.iter().copied().collect(),
                }
            } else {
                FinalCoreBirthTelemetry {
                    clause_id: *clause_id,
                    source_kind: "other".to_string(),
                    reference_stage: None,
                    w_indices: Vec::new(),
                }
            }
        })
        .collect::<Vec<_>>();
    let envelope = (terminal == Some("valid") && !core_births.is_empty()).then(|| {
        ReferenceParametersTelemetry {
            max_ra_ops: core_births
                .iter()
                .map(|birth| birth.minimal_eligibility.max_ra_ops)
                .max()
                .unwrap_or(0),
            max_selection_condition_nodes: core_births
                .iter()
                .map(|birth| birth.minimal_eligibility.max_selection_condition_nodes)
                .max()
                .unwrap_or(0),
            max_projection_excess: core_births
                .iter()
                .map(|birth| birth.minimal_eligibility.max_projection_excess)
                .max()
                .unwrap_or(0),
            max_output_arity: core_births
                .iter()
                .map(|birth| birth.minimal_eligibility.max_output_arity)
                .max()
                .unwrap_or(0),
            max_clause_width: core_births
                .iter()
                .map(|birth| birth.minimal_eligibility.max_clause_width)
                .max()
                .unwrap_or(0),
        }
    });
    let mut exceeding = BTreeMap::new();
    if let Some(limit) = &envelope {
        for (name, count) in [
            (
                "max_ra_ops",
                births
                    .iter()
                    .filter(|birth| birth.registered_unique)
                    .filter(|birth| birth.minimal_eligibility.max_ra_ops > limit.max_ra_ops)
                    .count(),
            ),
            (
                "max_selection_condition_nodes",
                births
                    .iter()
                    .filter(|birth| birth.registered_unique)
                    .filter(|birth| {
                        birth.minimal_eligibility.max_selection_condition_nodes
                            > limit.max_selection_condition_nodes
                    })
                    .count(),
            ),
            (
                "max_projection_excess",
                births
                    .iter()
                    .filter(|birth| birth.registered_unique)
                    .filter(|birth| {
                        birth.minimal_eligibility.max_projection_excess
                            > limit.max_projection_excess
                    })
                    .count(),
            ),
            (
                "max_output_arity",
                births
                    .iter()
                    .filter(|birth| birth.registered_unique)
                    .filter(|birth| {
                        birth.minimal_eligibility.max_output_arity > limit.max_output_arity
                    })
                    .count(),
            ),
            (
                "max_clause_width",
                births
                    .iter()
                    .filter(|birth| birth.registered_unique)
                    .filter(|birth| {
                        birth.minimal_eligibility.max_clause_width > limit.max_clause_width
                    })
                    .count(),
            ),
        ] {
            exceeding.insert(name.to_string(), u64::try_from(count).unwrap_or(u64::MAX));
        }
    }
    let schedule_imbalance = schedule_imbalance(&core_births, births);
    let time_by_disposition_nanoseconds = durations
        .iter()
        .filter_map(|(key, value)| {
            key.strip_prefix("disposition.")
                .map(|disposition| (disposition.to_string(), *value))
        })
        .collect();
    let attributed_clause_solver_attempts = clause_solver_attempts
        .values()
        .copied()
        .fold(0_u64, u64::saturating_add);
    let total_vampire_requests = counters
        .get("solver.vampire_requests")
        .copied()
        .unwrap_or(0);
    let solver_yield = SolverYieldTelemetry {
        total_vampire_requests,
        attributed_clause_solver_attempts,
        final_core_population: core.len() as u64,
        solver_calls_per_core_numerator: attributed_clause_solver_attempts,
        solver_calls_per_core_denominator: core.len() as u64,
        attribution_note: "Per-clause attribution includes ordinary initialization and maintenance queries. Bulk, W-search, termination, certification, and other Vampire requests remain only in total_vampire_requests."
            .to_string(),
    };
    let note = if terminal == Some("valid") {
        "Reference-stage, shape, and parameter-dimension yield use registered unique ordinary formulas as their denominators. Parameter rows use each formula's minimal-eligibility value. W-layer Core members are listed separately. Schedule imbalance is observational until a controlled replay confirms it."
    } else {
        "No certified final Core is available. Stage, shape, and parameter-dimension survival/pruning populations are terminal INV snapshots over registered unique ordinary formulas. Parameter rows use each formula's minimal-eligibility value; do not infer a causal schedule change without a controlled replay."
    }
    .to_string();
    DerivedTelemetry {
        stage_yield,
        shape_yield,
        parameter_dimension_yield,
        solver_yield,
        time_by_disposition_nanoseconds,
        final_core_births,
        schedule_imbalance,
        final_core_parameter_envelope: envelope,
        formulas_exceeding_final_core_envelope: exceeding,
        note,
    }
}

#[derive(Default)]
struct YieldAccumulator {
    population: u64,
    final_core: u64,
    solver_attempts: u64,
    dispositions: BTreeMap<String, u64>,
    surviving: u64,
    pruned: u64,
}

impl YieldAccumulator {
    fn record(&mut self, is_core: bool, attempts: u64, disposition: Option<&String>) {
        self.population = self.population.saturating_add(1);
        self.final_core = self.final_core.saturating_add(u64::from(is_core));
        self.solver_attempts = self.solver_attempts.saturating_add(attempts);
        if let Some(disposition) = disposition {
            saturating_add(&mut self.dispositions, disposition.clone(), 1);
            if disposition.starts_with("pruned_") {
                self.pruned = self.pruned.saturating_add(1);
            } else if disposition != "unclassified" {
                self.surviving = self.surviving.saturating_add(1);
            }
        }
    }

    fn into_stage(self, stage: u64) -> StageYieldTelemetry {
        StageYieldTelemetry {
            stage,
            registered_unique_population: self.population,
            final_core_population: self.final_core,
            emitted_to_core_numerator: self.final_core,
            emitted_to_core_denominator: self.population,
            attributed_clause_solver_attempts: self.solver_attempts,
            solver_calls_per_core_numerator: self.solver_attempts,
            solver_calls_per_core_denominator: self.final_core,
            final_disposition_populations: self.dispositions,
            survival_numerator: self.surviving,
            pruning_numerator: self.pruned,
            survival_pruning_denominator: self.population,
        }
    }

    fn into_shape(self, shape_key: String) -> ShapeYieldTelemetry {
        ShapeYieldTelemetry {
            shape_key,
            registered_unique_population: self.population,
            final_core_population: self.final_core,
            emitted_to_core_numerator: self.final_core,
            emitted_to_core_denominator: self.population,
            attributed_clause_solver_attempts: self.solver_attempts,
            solver_calls_per_core_numerator: self.solver_attempts,
            solver_calls_per_core_denominator: self.final_core,
            final_disposition_populations: self.dispositions,
            survival_numerator: self.surviving,
            pruning_numerator: self.pruned,
            survival_pruning_denominator: self.population,
        }
    }

    fn into_parameter(
        self,
        dimension: String,
        minimal_eligibility_value: u64,
    ) -> ParameterDimensionYieldTelemetry {
        ParameterDimensionYieldTelemetry {
            dimension,
            minimal_eligibility_value,
            registered_unique_population: self.population,
            terminal_core_population: self.final_core,
            emitted_to_terminal_core_numerator: self.final_core,
            emitted_to_terminal_core_denominator: self.population,
            attributed_clause_solver_attempts: self.solver_attempts,
            solver_calls_per_terminal_core_numerator: self.solver_attempts,
            solver_calls_per_terminal_core_denominator: self.final_core,
            final_disposition_populations: self.dispositions,
            survival_numerator: self.surviving,
            pruning_numerator: self.pruned,
            survival_pruning_denominator: self.population,
            terminal_disposition_classified_population: self.surviving.saturating_add(self.pruned),
            terminal_disposition_unclassified_population: self
                .population
                .saturating_sub(self.surviving.saturating_add(self.pruned)),
        }
    }
}

fn parameter_dimensions(parameters: &ReferenceParametersTelemetry) -> [(&'static str, u64); 5] {
    [
        ("max_ra_ops", parameters.max_ra_ops),
        (
            "max_selection_condition_nodes",
            parameters.max_selection_condition_nodes,
        ),
        ("max_projection_excess", parameters.max_projection_excess),
        ("max_output_arity", parameters.max_output_arity),
        ("max_clause_width", parameters.max_clause_width),
    ]
}

fn formula_shape_key(shape: &FormulaShape) -> String {
    format!(
        "width={};signs={}/{};atoms={}/{};roots={:?};ra={};ra_bin={};sel={};proj={};excess={};arity={};size={};skeleton={};constants={};relations={};provenance={:?}",
        shape.clause_width,
        shape.positive_literals,
        shape.negative_literals,
        shape.equalities,
        shape.containments,
        shape.ra_root_constructors,
        shape.ra_cost,
        shape.ra_cost_bin,
        shape.selection_condition_nodes,
        shape.projection_count,
        shape.maximum_projection_excess,
        shape.output_arity,
        shape.serialized_size_bin,
        shape.normalized_structural_skeleton,
        shape.constant_occurrences,
        shape.relation_occurrences,
        shape.operator_provenance,
    )
}

fn schedule_imbalance(
    core_births: &[&FormulaBirthTelemetry],
    births: &[FormulaBirthTelemetry],
) -> Vec<ScheduleImbalanceTelemetry> {
    let mut first_useful = BTreeMap::<String, u64>::new();
    for birth in core_births {
        for dimension in &birth.binding_dimensions {
            first_useful
                .entry(dimension.clone())
                .and_modify(|value| *value = (*value).min(birth.stage))
                .or_insert(birth.stage);
        }
    }
    let latest = first_useful.values().copied().max().unwrap_or(0);
    if latest == 0 {
        return Vec::new();
    }
    [
        "max_ra_ops",
        "max_selection_condition_nodes",
        "max_projection_excess",
        "max_output_arity",
        "max_clause_width",
    ]
    .into_iter()
    .filter_map(|dimension| {
        let first = first_useful.get(dimension).copied();
        let wait_start = first.unwrap_or(0);
        (wait_start < latest).then(|| ScheduleImbalanceTelemetry {
            dimension: dimension.to_string(),
            first_useful_value: first,
            first_useful_stage: first,
            latest_first_useful_stage: latest,
            intervening_stage_count: latest.saturating_sub(wait_start),
            registered_formulas_while_waiting: u64::try_from(
                births
                    .iter()
                    .filter(|birth| {
                        birth.registered_unique && birth.stage > wait_start && birth.stage <= latest
                    })
                    .count(),
            )
            .unwrap_or(u64::MAX),
        })
    })
    .collect()
}

fn required_measurement_gaps(
    aggregate: &TelemetryAggregate,
    memory: &MemoryTelemetry,
) -> Vec<String> {
    let mut missing = BTreeSet::new();
    let has_counter = |key: &str| aggregate.counters.get(key).copied().unwrap_or(0) > 0;
    let has_duration = |key: &str| aggregate.durations.contains_key(key);

    if aggregate.terminal_outcome.is_none() {
        missing.insert("terminal.outcome");
    }
    for key in [
        "symbolic.entry",
        "symbolic.state_construction",
        "symbolic.artifact_settlement",
    ] {
        if !has_duration(key) {
            missing.insert(key);
        }
    }
    if has_counter("lane.inv.starts") && !has_duration("lane.inv.activity") {
        missing.insert("lane.inv.activity");
    }
    if has_counter("lane.cex.starts") && !has_duration("lane.cex.activity") {
        missing.insert("lane.cex.activity");
    }
    if has_counter("lane.inv.starts") || has_counter("lane.cex.starts") {
        for key in ["symbolic.lane_race", "symbolic.encoding_cleanup"] {
            if !has_duration(key) {
                missing.insert(key);
            }
        }
    }
    if has_counter("solver.vampire_requests") && !has_duration("solver.admission_wait") {
        missing.insert("solver.admission_wait");
    }
    if has_counter("solver.vampire_process_launches")
        && !has_duration("solver.child_process_execution_and_cleanup")
    {
        missing.insert("solver.child_process_execution_and_cleanup");
    }
    if has_counter("houdini.initialization.proof_and_fmb_requests")
        && !has_duration("houdini.initialization.query_inclusive")
    {
        missing.insert("houdini.initialization.query_inclusive");
    }
    if has_counter("houdini.maintenance.proof_and_fmb_requests")
        && !has_duration("houdini.maintenance.query_inclusive")
    {
        missing.insert("houdini.maintenance.query_inclusive");
    }
    if has_counter("inv.certification_attempts") && !has_duration("inv.certification") {
        missing.insert("inv.certification");
    }
    if has_counter("cex.certification_attempts") && !has_duration("cex.certification") {
        missing.insert("cex.certification");
    }
    if !aggregate.waves.is_empty() {
        if aggregate.waves.iter().any(|wave| {
            wave.stage_delta_equality_deduplicated_occurrences
                .is_some_and(|count| count > 0)
        }) {
            missing.insert("reference_wave.pre_registration_duplicate_occurrence_attribution");
        }
        if aggregate
            .waves
            .iter()
            .any(|wave| wave.lean_enumeration_nanoseconds.is_none())
        {
            missing.insert("reference_wave.lean_enumeration_split");
        }
        if aggregate
            .waves
            .iter()
            .any(|wave| wave.transport_and_rust_validation_nanoseconds.is_none())
        {
            missing.insert("reference_wave.transport_and_rust_validation_split");
        }
        if aggregate.waves.iter().any(|wave| {
            wave.registration_and_formula_preparation_nanoseconds
                .is_none()
        }) {
            missing.insert("reference_wave.registration_and_formula_preparation");
        }
        if aggregate
            .waves
            .iter()
            .any(|wave| wave.catalog_registration_nanoseconds.is_none())
        {
            missing.insert("reference_wave.catalog_registration_split");
        }
        if aggregate
            .waves
            .iter()
            .any(|wave| wave.formula_body_preparation_nanoseconds.is_none())
        {
            missing.insert("reference_wave.formula_body_preparation_split");
        }
    }
    if aggregate
        .formula_births
        .iter()
        .filter(|birth| birth.registered_unique)
        .any(|birth| {
            birth
                .clause_id
                .is_none_or(|id| !aggregate.final_formula_dispositions.contains_key(&id))
        })
    {
        missing.insert("formula.final_dispositions");
    }
    if has_counter("symbolic.entry") || has_duration("symbolic.entry") {
        if aggregate.run_configuration.is_none() {
            missing.insert("run.configuration");
        }
        missing.insert("artifact.individual_payload_io");
        missing.insert("memory.task_scoped_peak");
    }
    let observed_inv_epochs = aggregate.counters.get("inv.epochs").copied().unwrap_or(0);
    if has_counter("lane.inv.starts")
        && u64::try_from(aggregate.inv_epochs.len()).unwrap_or(u64::MAX) != observed_inv_epochs
    {
        missing.insert("inv.epoch_parameters");
    }
    if has_counter("solver.vampire_process_launches") {
        missing.insert("memory.concurrent_process_tree_peak");
    }
    if aggregate
        .w_clauses
        .keys()
        .any(|clause_id| !aggregate.w_clause_shapes.contains_key(clause_id))
    {
        missing.insert("w_clause.structural_shape");
    }
    if usize::try_from(
        aggregate
            .counters
            .get("cex.w_bundles_prepared")
            .copied()
            .unwrap_or(0),
    )
    .unwrap_or(usize::MAX)
        != aggregate.w_attempt_formula_shapes.len()
    {
        missing.insert("w_attempt_formula.structural_shape");
    }
    if memory.process_peak_rss_bytes.is_none() {
        missing.insert("memory.process_peak_rss");
    }
    missing.into_iter().map(str::to_string).collect()
}

fn measurement_limitations() -> Vec<String> {
    vec![
        "Lean enumeration, transport, and Rust validation share one inclusive reference-wave span; the worker does not expose a stable internal split."
            .to_string(),
        "Reference-wave Catalog and formula-body timings include cumulative proposal rechecks; population fields expose that repeated work separately."
            .to_string(),
        "Memory reports process peak RSS and waited-child peak RSS separately; it is not a sampled concurrent process-tree sum."
            .to_string(),
        "getrusage memory values are process-lifetime high-water marks; later campaign tasks do not receive isolated task-lifetime peaks."
            .to_string(),
        "Artifact timing currently covers final backend settlement, not every individual payload write."
            .to_string(),
        "Reference duplicate telemetry measures only decoded QFAssertExpr occurrences removed by Lean equality deduplication."
            .to_string(),
        "The current Lean reference-proposal protocol exposes scalar raw/distinct counts and identities only for formulas retained after equality deduplication. It cannot attribute removed pre-registration occurrences to a structural shape or candidate identity without a larger telemetry-aware, paginated protocol."
            .to_string(),
        "Literal-order symmetry variants and repeated literals are excluded by canonical representation construction; they are not measured dispositions."
            .to_string(),
        "Reference-wave tautologies are not classified at the current worker boundary, so tautology counts are unavailable."
            .to_string(),
        "Core-subsumption-before-solver pruning is not implemented in the reference path, so no such disposition is emitted."
            .to_string(),
        "Stage and structural-shape tables cover ordinary reference formulas only; W-layer identities and indices are reported separately."
            .to_string(),
        "A general QF W formula has structural-shape telemetry but no reference-enumerator clause eligibility vector."
            .to_string(),
    ]
}

// ------------------------------------------------------------
// Formula-Shape Extraction
// ------------------------------------------------------------

pub fn reference_formula_shape(
    identity: &str,
    relation_arities: &BTreeMap<String, u64>,
) -> Option<(FormulaShape, ReferenceParametersTelemetry)> {
    let (shape, max_output_arity_requirement) =
        qf_formula_shape_analysis(identity, relation_arities)?;
    let eligibility = ReferenceParametersTelemetry {
        max_ra_ops: shape.ra_cost,
        max_selection_condition_nodes: shape.selection_condition_nodes,
        max_projection_excess: shape.maximum_projection_excess,
        max_output_arity: max_output_arity_requirement,
        max_clause_width: shape.clause_width,
    };
    Some((shape, eligibility))
}

pub fn qf_formula_shape(
    identity: &str,
    relation_arities: &BTreeMap<String, u64>,
) -> Option<FormulaShape> {
    qf_formula_shape_analysis(identity, relation_arities).map(|(shape, _)| shape)
}

fn qf_formula_shape_analysis(
    identity: &str,
    relation_arities: &BTreeMap<String, u64>,
) -> Option<(FormulaShape, u64)> {
    let value: Value = serde_json::from_str(identity).ok()?;
    let mut analysis = ShapeAnalysis::default();
    collect_clause(&value, false, relation_arities, &mut analysis)?;
    let skeleton = structural_skeleton(&value);
    let serialized_size_bytes = u64::try_from(identity.len()).ok()?;
    let shape = FormulaShape {
        clause_width: analysis.clause_width,
        positive_literals: analysis.positive_literals,
        negative_literals: analysis.negative_literals,
        equalities: analysis.equalities,
        containments: analysis.containments,
        ra_root_constructors: analysis.ra_root_constructors,
        ra_nodes: analysis.ra_nodes,
        ra_cost: analysis.ra_cost,
        ra_cost_bin: structural_cost_bin(analysis.ra_cost).to_string(),
        selection_condition_nodes: analysis.selection_condition_nodes,
        projection_count: analysis.projection_count,
        maximum_projection_excess: analysis.maximum_projection_excess,
        output_arity: analysis.output_arity,
        constant_occurrences: analysis.constant_occurrences,
        relation_occurrences: analysis.relation_occurrences,
        serialized_size_bytes,
        serialized_size_bin: size_bin(serialized_size_bytes).to_string(),
        normalized_structural_skeleton: serde_json::to_string(&skeleton).ok()?,
        operator_provenance: analysis.operator_provenance.into_iter().collect(),
    };
    Some((shape, analysis.max_output_arity_requirement))
}

#[derive(Default)]
struct ShapeAnalysis {
    clause_width: u64,
    positive_literals: u64,
    negative_literals: u64,
    equalities: u64,
    containments: u64,
    ra_root_constructors: BTreeMap<String, u64>,
    ra_nodes: u64,
    ra_cost: u64,
    max_output_arity_requirement: u64,
    selection_condition_nodes: u64,
    projection_count: u64,
    maximum_projection_excess: u64,
    output_arity: u64,
    constant_occurrences: u64,
    relation_occurrences: u64,
    operator_provenance: std::collections::BTreeSet<String>,
}

fn collect_clause(
    value: &Value,
    negated: bool,
    relation_arities: &BTreeMap<String, u64>,
    analysis: &mut ShapeAnalysis,
) -> Option<()> {
    let parts = value.as_array()?;
    let tag = parts.first()?.as_str()?;
    if matches!(tag, "true" | "false") && parts.len() == 1 {
        return Some(());
    }
    if matches!(tag, "and" | "or") && parts.len() == 3 {
        collect_clause(&parts[1], negated, relation_arities, analysis)?;
        collect_clause(&parts[2], negated, relation_arities, analysis)?;
        return Some(());
    }
    if tag == "not" && parts.len() == 2 {
        return collect_clause(&parts[1], !negated, relation_arities, analysis);
    }
    analysis.clause_width = analysis.clause_width.saturating_add(1);
    if negated {
        analysis.negative_literals = analysis.negative_literals.saturating_add(1);
    } else {
        analysis.positive_literals = analysis.positive_literals.saturating_add(1);
    }
    match (tag, parts.len()) {
        ("eq", 3) => {
            analysis.equalities = analysis.equalities.saturating_add(1);
            record_root_constructor(&parts[1], analysis)?;
            record_root_constructor(&parts[2], analysis)?;
            let left = collect_expression(&parts[1], relation_arities, analysis)?;
            let right = collect_expression(&parts[2], relation_arities, analysis)?;
            analysis.output_arity = analysis.output_arity.max(left).max(right);
        }
        ("subset", 3) => {
            analysis.containments = analysis.containments.saturating_add(1);
            record_root_constructor(&parts[1], analysis)?;
            record_root_constructor(&parts[2], analysis)?;
            let left = collect_expression(&parts[1], relation_arities, analysis)?;
            let right = collect_expression(&parts[2], relation_arities, analysis)?;
            analysis.output_arity = analysis.output_arity.max(left).max(right);
        }
        ("eq_empty_right" | "eq_empty_left" | "subset_empty_right" | "subset_empty_left", 2) => {
            if tag.starts_with("eq") {
                analysis.equalities = analysis.equalities.saturating_add(1);
            } else {
                analysis.containments = analysis.containments.saturating_add(1);
            }
            record_root_constructor(&parts[1], analysis)?;
            let arity = collect_expression(&parts[1], relation_arities, analysis)?;
            analysis.output_arity = analysis.output_arity.max(arity);
        }
        _ => return None,
    }
    Some(())
}

fn collect_expression(
    value: &Value,
    relation_arities: &BTreeMap<String, u64>,
    analysis: &mut ShapeAnalysis,
) -> Option<u64> {
    let parts = value.as_array()?;
    let tag = parts.first()?.as_str()?;
    analysis.ra_nodes = analysis.ra_nodes.saturating_add(1);
    analysis.operator_provenance.insert(tag.to_string());
    let (arity, cost) = match (tag, parts.len()) {
        ("top", 1) => (0, 0),
        ("empty", 2) => {
            let arity = parts[1].as_str()?.parse().ok()?;
            if !relation_arities
                .values()
                .any(|candidate| *candidate == arity)
            {
                analysis.max_output_arity_requirement =
                    analysis.max_output_arity_requirement.max(arity);
            }
            (arity, 0)
        }
        ("rel", 2) => {
            analysis.relation_occurrences = analysis.relation_occurrences.saturating_add(1);
            (relation_arities.get(parts[1].as_str()?).copied()?, 0)
        }
        ("single", 2) => {
            analysis.constant_occurrences = analysis.constant_occurrences.saturating_add(1);
            (1, 0)
        }
        ("select", 3) => {
            let nodes = selection_nodes(&parts[1], analysis)?;
            analysis.selection_condition_nodes = analysis.selection_condition_nodes.max(nodes);
            let child = collect_expression_summary(&parts[2], relation_arities, analysis)?;
            (child.0, child.1.saturating_add(1))
        }
        ("proj", 3) => {
            analysis.projection_count = analysis.projection_count.saturating_add(1);
            let output = nat_list_length(&parts[1])?;
            let child = collect_expression_summary(&parts[2], relation_arities, analysis)?;
            analysis.maximum_projection_excess = analysis
                .maximum_projection_excess
                .max(output.saturating_sub(child.0));
            (output, child.1.saturating_add(1))
        }
        ("prod", 3) => {
            let left = collect_expression_summary(&parts[1], relation_arities, analysis)?;
            let right = collect_expression_summary(&parts[2], relation_arities, analysis)?;
            (
                left.0.checked_add(right.0)?,
                left.1.saturating_add(right.1).saturating_add(1),
            )
        }
        ("union" | "diff", 3) => {
            let left = collect_expression_summary(&parts[1], relation_arities, analysis)?;
            let right = collect_expression_summary(&parts[2], relation_arities, analysis)?;
            if left.0 != right.0 {
                return None;
            }
            (left.0, left.1.saturating_add(right.1).saturating_add(1))
        }
        _ => return None,
    };
    if matches!(tag, "select" | "proj" | "prod" | "union" | "diff") {
        analysis.max_output_arity_requirement = analysis.max_output_arity_requirement.max(arity);
    }
    analysis.output_arity = analysis.output_arity.max(arity);
    analysis.ra_cost = analysis.ra_cost.max(cost);
    Some(arity)
}

fn record_root_constructor(value: &Value, analysis: &mut ShapeAnalysis) -> Option<()> {
    let tag = value.as_array()?.first()?.as_str()?;
    *analysis
        .ra_root_constructors
        .entry(tag.to_string())
        .or_default() += 1;
    Some(())
}

fn collect_expression_summary(
    value: &Value,
    relation_arities: &BTreeMap<String, u64>,
    analysis: &mut ShapeAnalysis,
) -> Option<(u64, u64)> {
    let previous_max = analysis.ra_cost;
    let arity = collect_expression(value, relation_arities, analysis)?;
    let subtree_max = analysis.ra_cost;
    let exact_cost = expression_cost(value)?;
    analysis.ra_cost = previous_max.max(subtree_max).max(exact_cost);
    Some((arity, exact_cost))
}

fn expression_cost(value: &Value) -> Option<u64> {
    let parts = value.as_array()?;
    match (parts.first()?.as_str()?, parts.len()) {
        ("top" | "empty" | "rel" | "single", _) => Some(0),
        ("select" | "proj", 3) => Some(1_u64.saturating_add(expression_cost(&parts[2])?)),
        ("prod" | "union" | "diff", 3) => Some(
            1_u64
                .saturating_add(expression_cost(&parts[1])?)
                .saturating_add(expression_cost(&parts[2])?),
        ),
        _ => None,
    }
}

fn selection_nodes(value: &Value, analysis: &mut ShapeAnalysis) -> Option<u64> {
    let parts = value.as_array()?;
    let tag = parts.first()?.as_str()?;
    match (tag, parts.len()) {
        ("eq_idx", 3) => Some(1),
        ("eq_const", 3) => {
            analysis.constant_occurrences = analysis.constant_occurrences.saturating_add(1);
            Some(1)
        }
        ("and" | "or", 3) => Some(
            1_u64
                .saturating_add(selection_nodes(&parts[1], analysis)?)
                .saturating_add(selection_nodes(&parts[2], analysis)?),
        ),
        ("not", 2) => Some(1_u64.saturating_add(selection_nodes(&parts[1], analysis)?)),
        _ => None,
    }
}

fn nat_list_length(value: &Value) -> Option<u64> {
    let parts = value.as_array()?;
    match (parts.first()?.as_str()?, parts.len()) {
        ("nil", 1) => Some(0),
        ("cons", 3) => Some(1_u64.saturating_add(nat_list_length(&parts[2])?)),
        _ => None,
    }
}

fn structural_skeleton(value: &Value) -> Value {
    let Some(parts) = value.as_array() else {
        return Value::String("_".to_string());
    };
    let Some(tag) = parts.first().and_then(Value::as_str) else {
        return Value::String("_".to_string());
    };
    let mut result = vec![Value::String(tag.to_string())];
    for child in parts.iter().skip(1) {
        if child.is_array() {
            result.push(structural_skeleton(child));
        } else {
            result.push(Value::String("_".to_string()));
        }
    }
    Value::Array(result)
}

// ------------------------------------------------------------
// Output And Platform Measurements
// ------------------------------------------------------------

fn saturating_add(map: &mut BTreeMap<String, u64>, key: String, amount: u64) {
    let value = map.entry(key).or_default();
    *value = value.saturating_add(amount);
}

fn atomic_saturating_add(value: &AtomicU64, amount: u64) {
    let _ = value.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |current| {
        Some(current.saturating_add(amount))
    });
}

fn atomic_observe_max(value: &AtomicU64, observed: u64) {
    let _ = value.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |current| {
        Some(if current == NO_PROGRESS_MAXIMUM {
            observed
        } else {
            current.max(observed)
        })
    });
}

fn load_optional_maximum(value: &AtomicU64) -> Option<u64> {
    match value.load(Ordering::Relaxed) {
        NO_PROGRESS_MAXIMUM => None,
        observed => Some(observed),
    }
}

fn elapsed_nanoseconds(started: Instant) -> u64 {
    started.elapsed().as_nanos().min(u128::from(u64::MAX)) as u64
}

fn size_bin(bytes: u64) -> &'static str {
    match bytes {
        0..=127 => "000-127",
        128..=511 => "128-511",
        512..=2047 => "512-2047",
        2048..=8191 => "2048-8191",
        _ => "8192+",
    }
}

fn structural_cost_bin(cost: u64) -> &'static str {
    match cost {
        0 => "0",
        1 => "1",
        2..=3 => "2-3",
        4..=7 => "4-7",
        _ => "8+",
    }
}

fn write_detailed_events(
    file: File,
    receiver: mpsc::Receiver<DetailedMessage>,
    stop: Arc<AtomicBool>,
    error: Arc<Mutex<Option<String>>>,
) {
    let mut writer = BufWriter::new(file);
    loop {
        if stop.load(Ordering::Acquire) {
            for DetailedMessage::Event(event) in receiver.try_iter() {
                if !write_detailed_event(&mut writer, &event, &error) {
                    return;
                }
            }
            break;
        }
        match receiver.recv_timeout(Duration::from_millis(25)) {
            Ok(DetailedMessage::Event(event)) => {
                if !write_detailed_event(&mut writer, &event, &error) {
                    return;
                }
            }
            Err(mpsc::RecvTimeoutError::Timeout) => {}
            Err(mpsc::RecvTimeoutError::Disconnected) => break,
        }
    }
    if let Err(problem) = writer.flush() {
        *error
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner()) =
            Some(format!("flush detailed telemetry: {problem}"));
    }
}

fn write_detailed_event(
    writer: &mut BufWriter<File>,
    event: &DetailedEvent,
    error: &Mutex<Option<String>>,
) -> bool {
    if let Err(problem) = serde_json::to_writer(&mut *writer, event)
        .and_then(|()| writer.write_all(b"\n").map_err(serde_json::Error::io))
    {
        *error
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner()) =
            Some(format!("write detailed telemetry: {problem}"));
        false
    } else {
        true
    }
}

fn write_json(path: &Path, value: &impl Serialize) -> io::Result<()> {
    let temporary = path.with_extension("json.tmp");
    let mut file = BufWriter::new(File::create(&temporary)?);
    serde_json::to_writer_pretty(&mut file, value).map_err(io::Error::other)?;
    file.write_all(b"\n")?;
    file.flush()?;
    drop(file);
    fs::rename(temporary, path)
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
fn sample_peak_memory() -> MemoryTelemetry {
    fn usage(who: libc::c_int) -> Option<u64> {
        let mut usage = std::mem::MaybeUninit::<libc::rusage>::zeroed();
        let result = unsafe { libc::getrusage(who, usage.as_mut_ptr()) };
        if result != 0 {
            return None;
        }
        let maximum = unsafe { usage.assume_init() }.ru_maxrss;
        let raw = u64::try_from(maximum).ok()?;
        #[cfg(target_os = "linux")]
        return raw.checked_mul(1024);
        #[cfg(target_os = "macos")]
        return Some(raw);
    }

    MemoryTelemetry {
        process_peak_rss_bytes: usage(libc::RUSAGE_SELF),
        waited_children_peak_rss_bytes: usage(libc::RUSAGE_CHILDREN),
        source:
            "getrusage_ru_maxrss; child value covers waited children, not an additive tree snapshot"
                .to_string(),
    }
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
fn sample_peak_memory() -> MemoryTelemetry {
    MemoryTelemetry {
        process_peak_rss_bytes: None,
        waited_children_peak_rss_bytes: None,
        source: "unavailable".to_string(),
    }
}

// ------------------------------------------------------------
// Focused Unit Tests
// ------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::AtomicBool;
    use std::time::{SystemTime, UNIX_EPOCH};

    fn temporary_root(label: &str) -> PathBuf {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("test clock follows the Unix epoch")
            .as_nanos();
        std::env::temp_dir().join(format!(
            "whiel-telemetry-{label}-{}-{nonce}",
            std::process::id()
        ))
    }

    fn derive_for_test(
        waves: &[WaveTelemetry],
        births: &[FormulaBirthTelemetry],
        core: &BTreeSet<u64>,
        terminal: Option<&str>,
    ) -> DerivedTelemetry {
        derive_telemetry(DerivedTelemetryInput {
            waves,
            births,
            core,
            final_dispositions: &BTreeMap::new(),
            clause_solver_attempts: &BTreeMap::new(),
            w_clauses: &BTreeMap::new(),
            counters: &BTreeMap::new(),
            durations: &BTreeMap::new(),
            terminal,
        })
    }

    #[test]
    fn structural_shape_extracts_clause_and_projection_costs() {
        let identity = r#"["or",["not",["subset",["proj",["cons","0",["cons","1",["nil"]]],["rel","rel:R:0"]],["rel","rel:S:0"]]],["eq_empty_right",["select",["and",["eq_idx","0","1"],["eq_const","0","num:1"]],["rel","rel:T:0"]]]]"#;
        let arities = BTreeMap::from([
            ("rel:R:0".to_string(), 1),
            ("rel:S:0".to_string(), 2),
            ("rel:T:0".to_string(), 2),
        ]);
        let (shape, eligibility) =
            reference_formula_shape(identity, &arities).expect("valid structural identity");
        assert_eq!(shape.clause_width, 2);
        assert_eq!(shape.positive_literals, 1);
        assert_eq!(shape.negative_literals, 1);
        assert_eq!(shape.equalities, 1);
        assert_eq!(shape.containments, 1);
        assert_eq!(shape.projection_count, 1);
        assert_eq!(shape.maximum_projection_excess, 1);
        assert_eq!(shape.selection_condition_nodes, 3);
        assert_eq!(shape.ra_cost, 1);
        assert_eq!(shape.ra_cost_bin, "1");
        assert_eq!(
            shape.ra_root_constructors,
            BTreeMap::from([
                ("proj".to_string(), 1),
                ("rel".to_string(), 1),
                ("select".to_string(), 1),
            ])
        );
        assert_eq!(shape.ra_nodes, 5);
        assert_eq!(eligibility.max_clause_width, 2);
        assert_eq!(eligibility.max_projection_excess, 1);
        assert_eq!(eligibility.max_output_arity, 2);
    }

    #[test]
    fn base_relation_arities_do_not_inflate_minimum_output_arity() {
        let identity = r#"["eq",["rel","rel:R:0"],["empty","7"]]"#;
        let arities = BTreeMap::from([("rel:R:0".to_string(), 7)]);
        let (shape, eligibility) =
            reference_formula_shape(identity, &arities).expect("valid structural identity");

        assert_eq!(shape.output_arity, 7);
        assert_eq!(eligibility.max_output_arity, 0);
        assert_eq!(eligibility.max_ra_ops, 0);
        assert_eq!(
            shape.ra_root_constructors,
            BTreeMap::from([("empty".to_string(), 1), ("rel".to_string(), 1)])
        );
    }

    #[test]
    fn general_qf_shape_accepts_conjunctions_and_truth_constants() {
        let identity = r#"["and",["subset_empty_right",["rel","rel:R:0"]],["true"]]"#;
        let arities = BTreeMap::from([("rel:R:0".to_string(), 2)]);
        let shape = qf_formula_shape(identity, &arities).expect("valid general QF identity");

        assert_eq!(shape.clause_width, 1);
        assert_eq!(shape.positive_literals, 1);
        assert_eq!(shape.containments, 1);
        assert_eq!(shape.output_arity, 2);
    }

    #[test]
    fn derived_roots_are_not_confused_with_nested_ra_nodes() {
        let identity = r#"["subset",["proj",["cons","0",["cons","0",["nil"]]],["rel","rel:R:0"]],["union",["rel","rel:S:0"],["rel","rel:T:0"]]]"#;
        let arities = BTreeMap::from([
            ("rel:R:0".to_string(), 1),
            ("rel:S:0".to_string(), 2),
            ("rel:T:0".to_string(), 2),
        ]);
        let (shape, eligibility) =
            reference_formula_shape(identity, &arities).expect("valid structural identity");

        assert_eq!(
            shape.ra_root_constructors,
            BTreeMap::from([("proj".to_string(), 1), ("union".to_string(), 1)])
        );
        assert_eq!(shape.ra_nodes, 5);
        assert_eq!(shape.maximum_projection_excess, 1);
        assert_eq!(shape.ra_cost, 1);
        assert_eq!(eligibility.max_output_arity, 2);
    }

    #[test]
    fn off_mode_retains_only_fixed_size_progress() {
        let handle = TelemetryHandle::disabled();
        let payload_evaluated = AtomicBool::new(false);

        assert!(!handle.is_enabled());
        assert_eq!(handle.level(), TelemetryLevel::Off);
        assert!(handle.start_span().is_none());
        handle.increment("counter", 1);
        handle.observe_max("maximum", 2);
        handle.add_duration("duration", Duration::from_nanos(3));
        handle.record_disposition("disposition", 4);
        handle.increment("inv.epochs", 2);
        handle.increment("catalog.registered_unique", 5);
        handle.record_initialized_clauses([7, 8]);
        handle.record_core_admission(7);
        handle.observe_max("cex.highest_w_index", 4);
        handle.observe_max("cex.highest_safe_fmb_frontier", 9);
        handle.event_with("disabled", || {
            payload_evaluated.store(true, Ordering::Relaxed);
            serde_json::json!({"must_not": "be built"})
        });
        handle.record_error("ignored");

        assert!(!payload_evaluated.load(Ordering::Relaxed));
        let snapshot = handle.snapshot();
        assert!(snapshot.measurement_complete);
        assert_eq!(snapshot.counters["inv.epochs"], 2);
        assert_eq!(snapshot.counters["catalog.registered_unique"], 5);
        assert_eq!(snapshot.counters["cex.highest_w_index"], 4);
        assert_eq!(snapshot.counters["cex.highest_safe_fmb_frontier"], 9);
        assert!(snapshot.duration_nanoseconds.is_empty());
        assert_eq!(snapshot.dispositions["core_admission"], 1);
        assert!(snapshot.run_configuration.is_none());
        assert!(snapshot.inv_epochs.is_empty());
        assert!(snapshot.waves.is_empty());
        assert!(snapshot.formula_births.is_empty());
        assert!(snapshot.errors.is_empty());
        assert_eq!(snapshot.dropped_detailed_events, 0);
        assert_eq!(
            handle.progress_snapshot(),
            ProgressTelemetrySnapshot {
                inv_epochs: 2,
                proposed_clauses: 5,
                initialized_clauses: 2,
                core_admissions: 1,
                highest_w_index: Some(4),
                highest_safe_fmb_frontier: Some(9),
            }
        );
    }

    #[test]
    fn progress_snapshot_copies_only_fixed_size_live_progress() {
        let root = temporary_root("progress");
        let session =
            TelemetrySession::start(TelemetryConfig::new(&root, TelemetryLevel::Aggregate));
        let handle = session.handle();

        handle.increment("inv.epochs", 3);
        handle.increment("catalog.registered_unique", 40);
        handle.record_initialized_clauses([11, 12, 11]);
        handle.record_initialized_clauses([13]);
        handle.record_core_admission(12);
        handle.record_core_admission(12);
        handle.record_core_admission(13);
        handle.observe_max("cex.highest_w_index", 9);
        handle.observe_max("cex.highest_safe_fmb_frontier", 7);

        assert_eq!(
            handle.progress_snapshot(),
            ProgressTelemetrySnapshot {
                inv_epochs: 3,
                proposed_clauses: 40,
                initialized_clauses: 3,
                core_admissions: 2,
                highest_w_index: Some(9),
                highest_safe_fmb_frontier: Some(7),
            }
        );

        let _ = session.finish();
        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn run_configuration_is_single_and_epoch_parameters_remain_ordered() {
        let session = TelemetrySession::start(TelemetryConfig::new(
            temporary_root("configuration"),
            TelemetryLevel::Aggregate,
        ));
        let handle = session.handle();
        let configuration = RunConfigurationTelemetry {
            task_canonical_id: "task".to_string(),
            reference_schedule_id: "reference-v3".to_string(),
            reference_features: ReferenceFeatureSetTelemetry::all_enabled(),
            ..RunConfigurationTelemetry::default()
        };
        handle.record_run_configuration(configuration.clone());
        handle.record_run_configuration(configuration.clone());
        handle.record_inv_epoch(InvEpochTelemetry {
            epoch: 1,
            next_reference_stage: 0,
            next_reference_parameters: ReferenceParametersTelemetry::at_reference_stage(0),
            reference_features: ReferenceFeatureSetTelemetry::all_enabled(),
            proposal_size: 0,
            catalog_size: 0,
            core_size: 0,
        });
        handle.record_inv_epoch(InvEpochTelemetry {
            epoch: 2,
            next_reference_stage: 1,
            next_reference_parameters: ReferenceParametersTelemetry::at_reference_stage(1),
            reference_features: ReferenceFeatureSetTelemetry::all_enabled(),
            proposal_size: 3,
            catalog_size: 3,
            core_size: 1,
        });

        let snapshot = handle.snapshot();
        assert_eq!(snapshot.run_configuration, Some(configuration.clone()));
        assert_eq!(
            snapshot
                .inv_epochs
                .iter()
                .map(|epoch| epoch.epoch)
                .collect::<Vec<_>>(),
            vec![1, 2]
        );
        assert!(snapshot.errors.is_empty());

        let mut conflicting = configuration;
        conflicting.task_canonical_id = "different".to_string();
        handle.record_run_configuration(conflicting);
        assert!(
            handle
                .snapshot()
                .errors
                .iter()
                .any(|error| error.contains("conflicting symbolic run configuration"))
        );
    }

    #[test]
    fn w_clause_indices_share_one_structural_shape_record() {
        let session = TelemetrySession::start(TelemetryConfig::new(
            temporary_root("w-shape"),
            TelemetryLevel::Aggregate,
        ));
        let handle = session.handle();
        let shape = FormulaShape {
            clause_width: 1,
            ..FormulaShape::default()
        };
        let eligibility = ReferenceParametersTelemetry::at_reference_stage(2);
        handle.increment("cex.w_bundles_prepared", 1);
        handle.record_w_attempt_formula(2, shape.clone());
        handle.record_w_clause(7, 0, Some((shape.clone(), Some(eligibility.clone()))));
        handle.record_w_clause(7, 2, Some((shape.clone(), Some(eligibility.clone()))));

        let snapshot = handle.snapshot();
        assert_eq!(snapshot.w_clauses.len(), 1);
        assert_eq!(snapshot.w_clauses[0].clause_id, 7);
        assert_eq!(snapshot.w_clauses[0].w_indices, vec![0, 2]);
        assert_eq!(snapshot.w_clauses[0].shape, Some(shape));
        assert_eq!(snapshot.w_attempt_formulas.len(), 1);
        assert_eq!(snapshot.w_attempt_formulas[0].w_index, 2);
        assert!(
            !snapshot
                .missing_measurements
                .iter()
                .any(|missing| missing == "w_attempt_formula.structural_shape")
        );
        assert_eq!(
            snapshot.w_clauses[0].reference_eligibility,
            Some(eligibility)
        );
        assert_eq!(
            snapshot.w_clauses[0].reference_eligibility_note,
            "syntactic_disjunctive_clause"
        );
        assert!(
            !snapshot
                .missing_measurements
                .iter()
                .any(|missing| missing == "w_clause.structural_shape")
        );
    }

    #[test]
    fn certification_attempts_require_their_dedicated_timing_split() {
        let session = TelemetrySession::start(TelemetryConfig::new(
            temporary_root("certification-timing"),
            TelemetryLevel::Aggregate,
        ));
        let handle = session.handle();
        handle.increment("cex.certification_attempts", 1);
        assert!(
            handle
                .snapshot()
                .missing_measurements
                .iter()
                .any(|missing| missing == "cex.certification")
        );
        handle.add_duration("cex.certification", Duration::from_nanos(1));
        assert!(
            !handle
                .snapshot()
                .missing_measurements
                .iter()
                .any(|missing| missing == "cex.certification")
        );
    }

    #[test]
    fn final_core_envelope_requires_a_valid_terminal_result() {
        let eligibility = ReferenceParametersTelemetry {
            max_ra_ops: 2,
            max_selection_condition_nodes: 3,
            max_projection_excess: 4,
            max_output_arity: 5,
            max_clause_width: 6,
        };
        let births = vec![FormulaBirthTelemetry {
            clause_id: Some(7),
            registered_unique: true,
            stage: 6,
            source_id: "reference.stage.6".to_string(),
            shape: FormulaShape::default(),
            minimal_eligibility: eligibility.clone(),
            binding_dimensions: vec!["max_clause_width".to_string()],
            schedule_slack_at_birth: ReferenceParametersTelemetry::default(),
        }];
        let core = BTreeSet::from([7]);

        for terminal in [None, Some("invalid"), Some("inconclusive"), Some("failure")] {
            assert!(
                derive_for_test(&[], &births, &core, terminal)
                    .final_core_parameter_envelope
                    .is_none()
            );
        }
        assert_eq!(
            derive_for_test(&[], &births, &core, Some("valid")).final_core_parameter_envelope,
            Some(eligibility)
        );
    }

    #[test]
    fn preexisting_wave_formulas_do_not_enter_unique_yield_denominators() {
        let births = vec![
            FormulaBirthTelemetry {
                clause_id: Some(7),
                registered_unique: true,
                stage: 1,
                source_id: "reference.stage.1.unique".to_string(),
                shape: FormulaShape::default(),
                minimal_eligibility: ReferenceParametersTelemetry::default(),
                binding_dimensions: Vec::new(),
                schedule_slack_at_birth: ReferenceParametersTelemetry::default(),
            },
            FormulaBirthTelemetry {
                clause_id: Some(8),
                registered_unique: false,
                stage: 1,
                source_id: "reference.stage.1.preexisting".to_string(),
                shape: FormulaShape::default(),
                minimal_eligibility: ReferenceParametersTelemetry::at_reference_stage(9),
                binding_dimensions: Vec::new(),
                schedule_slack_at_birth: ReferenceParametersTelemetry::default(),
            },
        ];
        let derived = derive_for_test(&[], &births, &BTreeSet::from([7, 8]), Some("valid"));

        assert_eq!(derived.stage_yield.len(), 1);
        assert_eq!(derived.stage_yield[0].registered_unique_population, 1);
        assert_eq!(derived.stage_yield[0].final_core_population, 1);
        assert_eq!(derived.shape_yield.len(), 1);
        assert_eq!(derived.shape_yield[0].registered_unique_population, 1);
        assert_eq!(
            derived.final_core_parameter_envelope,
            Some(ReferenceParametersTelemetry::default())
        );
    }

    #[test]
    fn derived_reports_join_births_solver_work_dispositions_and_w_layers() {
        let birth = |clause_id, stage, binding_dimensions: &[&str]| FormulaBirthTelemetry {
            clause_id: Some(clause_id),
            registered_unique: true,
            stage,
            source_id: format!("reference.stage.{stage}.{clause_id}"),
            shape: FormulaShape {
                clause_width: clause_id,
                ..FormulaShape::default()
            },
            minimal_eligibility: ReferenceParametersTelemetry::at_reference_stage(stage),
            binding_dimensions: binding_dimensions
                .iter()
                .map(|dimension| (*dimension).to_string())
                .collect(),
            schedule_slack_at_birth: ReferenceParametersTelemetry::default(),
        };
        let births = vec![
            birth(1, 1, &["max_ra_ops"]),
            birth(3, 2, &[]),
            birth(2, 3, &["max_clause_width"]),
        ];
        let core = BTreeSet::from([1, 2, 4]);
        let dispositions = BTreeMap::from([
            (1, "core".to_string()),
            (2, "core".to_string()),
            (3, "pruned_initialization_refutation".to_string()),
            (4, "core".to_string()),
        ]);
        let attempts = BTreeMap::from([(1, 2), (2, 1), (3, 1)]);
        let w_clauses = BTreeMap::from([(4, BTreeSet::from([0, 2]))]);
        let counters = BTreeMap::from([("solver.vampire_requests".to_string(), 10)]);
        let durations =
            BTreeMap::from([("disposition.initialization_query_refuted".to_string(), 17)]);

        let derived = derive_telemetry(DerivedTelemetryInput {
            waves: &[],
            births: &births,
            core: &core,
            final_dispositions: &dispositions,
            clause_solver_attempts: &attempts,
            w_clauses: &w_clauses,
            counters: &counters,
            durations: &durations,
            terminal: Some("valid"),
        });

        assert_eq!(derived.solver_yield.total_vampire_requests, 10);
        assert_eq!(derived.solver_yield.attributed_clause_solver_attempts, 4);
        assert_eq!(derived.solver_yield.final_core_population, 3);
        assert_eq!(derived.stage_yield[1].pruning_numerator, 1);
        assert_eq!(derived.stage_yield[1].survival_pruning_denominator, 1);
        assert_eq!(
            derived.time_by_disposition_nanoseconds["initialization_query_refuted"],
            17
        );
        assert!(derived.final_core_births.iter().any(|birth| {
            birth.clause_id == 4 && birth.source_kind == "w_layer" && birth.w_indices == vec![0, 2]
        }));
        let max_ra = derived
            .schedule_imbalance
            .iter()
            .find(|entry| entry.dimension == "max_ra_ops")
            .expect("earlier useful RA dimension is reported");
        assert_eq!(max_ra.registered_formulas_while_waiting, 2);
        assert!(derived.schedule_imbalance.iter().any(|entry| {
            entry.dimension == "max_projection_excess" && entry.first_useful_value.is_none()
        }));
    }

    #[test]
    fn unsuccessful_runs_report_direct_parameter_dimension_survival_and_pruning() {
        let birth =
            |clause_id: u64, max_ra_ops: u64, max_clause_width: u64| FormulaBirthTelemetry {
                clause_id: Some(clause_id),
                registered_unique: true,
                stage: max_ra_ops.max(max_clause_width),
                source_id: format!("reference.{clause_id}"),
                shape: FormulaShape::default(),
                minimal_eligibility: ReferenceParametersTelemetry {
                    max_ra_ops,
                    max_clause_width,
                    ..ReferenceParametersTelemetry::default()
                },
                binding_dimensions: Vec::new(),
                schedule_slack_at_birth: ReferenceParametersTelemetry::default(),
            };
        let births = vec![
            birth(1, 0, 1),
            birth(2, 1, 1),
            birth(3, 1, 2),
            birth(4, 1, 2),
        ];
        let dispositions = BTreeMap::from([
            (1, "core".to_string()),
            (2, "pruned_initialization_refutation".to_string()),
            (3, "dormant_retention".to_string()),
        ]);
        let attempts = BTreeMap::from([(1, 1), (2, 2), (3, 3), (4, 4)]);
        let derived = derive_telemetry(DerivedTelemetryInput {
            waves: &[],
            births: &births,
            core: &BTreeSet::from([1]),
            final_dispositions: &dispositions,
            clause_solver_attempts: &attempts,
            w_clauses: &BTreeMap::new(),
            counters: &BTreeMap::new(),
            durations: &BTreeMap::new(),
            terminal: Some("timeout"),
        });

        let ra_one = derived
            .parameter_dimension_yield
            .iter()
            .find(|entry| entry.dimension == "max_ra_ops" && entry.minimal_eligibility_value == 1)
            .expect("one row for the exact minimal RA-operator requirement");
        assert_eq!(ra_one.registered_unique_population, 3);
        assert_eq!(ra_one.terminal_core_population, 0);
        assert_eq!(ra_one.attributed_clause_solver_attempts, 9);
        assert_eq!(ra_one.survival_numerator, 1);
        assert_eq!(ra_one.pruning_numerator, 1);
        assert_eq!(ra_one.survival_pruning_denominator, 3);
        assert_eq!(ra_one.terminal_disposition_classified_population, 2);
        assert_eq!(ra_one.terminal_disposition_unclassified_population, 1);
        assert_eq!(
            ra_one.final_disposition_populations,
            BTreeMap::from([
                ("dormant_retention".to_string(), 1),
                ("pruned_initialization_refutation".to_string(), 1),
            ])
        );
        assert!(derived.note.contains("minimal-eligibility value"));
        assert!(derived.note.contains("No certified final Core"));
    }

    #[test]
    fn removed_duplicate_occurrences_are_explicitly_unattributed() {
        let root = temporary_root("unattributed-reference-duplicates");
        let session =
            TelemetrySession::start(TelemetryConfig::new(&root, TelemetryLevel::Aggregate));
        session.handle().record_wave(WaveTelemetry {
            stage_delta_decoded_formula_occurrences: Some(3),
            stage_delta_equality_distinct_formulas: Some(2),
            stage_delta_equality_deduplicated_occurrences: Some(1),
            ..WaveTelemetry::default()
        });

        let snapshot = session.handle().snapshot();
        assert!(snapshot.missing_measurements.iter().any(|measurement| {
            measurement == "reference_wave.pre_registration_duplicate_occurrence_attribution"
        }));
        assert!(snapshot.limitations.iter().any(|limitation| {
            limitation
                .contains("identities only for formulas retained after equality deduplication")
        }));
        let _ = session.finish();
        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn aggregate_json_is_stable_for_one_semantic_snapshot() {
        let session = TelemetrySession::start(TelemetryConfig::new(
            temporary_root("stable"),
            TelemetryLevel::Aggregate,
        ));
        let handle = session.handle();
        handle.increment("z-last", 1);
        handle.increment("a-first", 2);
        handle.record_disposition("z-last", 3);
        handle.record_disposition("a-first", 4);
        let snapshot = handle.snapshot();

        let first = serde_json::to_string_pretty(&snapshot).expect("serialize telemetry");
        let second = serde_json::to_string_pretty(&snapshot).expect("serialize telemetry again");
        assert_eq!(first, second);
        assert!(first.find("\"a-first\"").unwrap() < first.find("\"z-last\"").unwrap());

        let root = session.root.clone().expect("aggregate session output root");
        let report = session.finish();
        let summary =
            fs::read_to_string(report.summary_path.expect("summary path")).expect("read summary");
        serde_json::from_str::<Value>(&summary).expect("summary is stable JSON");
        assert!(summary.ends_with('\n'));
        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn detailed_events_are_versioned_line_delimited_json() {
        let root = temporary_root("jsonl");
        let session =
            TelemetrySession::start(TelemetryConfig::new(&root, TelemetryLevel::Detailed));
        let handle = session.handle();
        handle.event("first", serde_json::json!({"value": 1}));
        handle.event("second", serde_json::json!({"value": 2}));
        let report = session.finish();

        assert!(!report.snapshot.measurement_complete);
        assert!(
            report
                .snapshot
                .missing_measurements
                .iter()
                .any(|measurement| measurement == "terminal.outcome")
        );
        assert_eq!(report.snapshot.dropped_detailed_events, 0);
        let events = fs::read_to_string(report.events_path.expect("events path"))
            .expect("read detailed events");
        let parsed = events
            .lines()
            .map(|line| serde_json::from_str::<Value>(line).expect("one JSON object per line"))
            .collect::<Vec<_>>();
        assert_eq!(parsed.len(), 2);
        assert_eq!(parsed[0]["schema_version"], TELEMETRY_SCHEMA_VERSION);
        assert_eq!(parsed[0]["kind"], "first");
        assert_eq!(parsed[0]["payload"]["value"], 1);
        assert_eq!(parsed[1]["schema_version"], TELEMETRY_SCHEMA_VERSION);
        assert_eq!(parsed[1]["kind"], "second");
        assert_eq!(parsed[1]["payload"]["value"], 2);
        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn bounded_detailed_queue_reports_dropped_events() {
        let root = temporary_root("bounded");
        let session = TelemetrySession::start(
            TelemetryConfig::new(&root, TelemetryLevel::Detailed)
                .event_queue_capacity(1)
                .expect("positive capacity"),
        );
        let handle = session.handle();
        for index in 0..10_000 {
            handle.event("stress", serde_json::json!({"index": index}));
        }
        let report = session.finish();
        assert!(report.summary_path.is_some());
        assert!(report.events_path.is_some());
        assert!(report.snapshot.dropped_detailed_events > 0);
        let _ = fs::remove_dir_all(root);
    }
}
