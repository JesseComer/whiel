//! Readable symbolic INV-lane control flow.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::time::Instant;

use crate::artifact::{ArtifactKind, ArtifactRef, ArtifactStore, HistoryMode, ScopeTag};
use crate::encoding::{
    EncodingError, ProposalRealization, ProposalRevision, SolverEncodingContext,
};
use crate::failure::{FailureKind, FailureOrigin, FailureReport, FailureScope};
use crate::houdini::{
    CertificationRuntime, ClauseCatalog, ClauseFormula, ClauseSet, CoverageLookup, CoverageMode,
    HoudiniExecutionOutcome, HoudiniState, InitializationInvocationOutcome, InitializationStatus,
    LastTermStatus, MaintenancePreparationOutcome, MaintenanceResultClass,
    MaintenanceResultDisposition, MaintenanceTrackHint, MaintenanceTrackKind,
    TerminationInvocationOutcome, TrackLayout, ValidityCertificationOutcome,
    VerificationParameters, certify_valid, check_initialization, houdini, prepare_maintenance,
    register_clauses, term_check,
};
use crate::runtime::{CancellationToken, SolverAdmission, SolverAdmissionClass};
use crate::task::SynthesisTask;
use crate::telemetry::{
    FormulaBirthTelemetry, InvEpochTelemetry, ReferenceFeatureSetTelemetry,
    ReferenceParametersTelemetry, TelemetryHandle, WaveRegistrationTelemetry, WaveTelemetry,
    qf_formula_shape, reference_formula_shape,
};
use crate::vampire::VampireWorkerCommand;

use super::CertifiedSynthesisResult;
use super::w_channel::{ProvedWBatch, WAdmissionIndex, WProofReceiver};

// ------------------------------------------------------------
// Persistent INV State
// ------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SymbolicProposalProgress {
    enumerator_version: u64,
    revision: ProposalRevision,
    last_stage: Option<u64>,
    cumulative_decoded_formula_occurrences: u64,
    cumulative_equality_distinct_formulas: u64,
    cumulative_equality_deduplicated_occurrences: u64,
}

impl SymbolicProposalProgress {
    pub fn enumerator_version(self) -> u64 {
        self.enumerator_version
    }

    pub fn revision(self) -> ProposalRevision {
        self.revision
    }

    pub fn last_stage(self) -> Option<u64> {
        self.last_stage
    }

    pub fn cumulative_decoded_formula_occurrences(self) -> u64 {
        self.cumulative_decoded_formula_occurrences
    }

    pub fn cumulative_equality_distinct_formulas(self) -> u64 {
        self.cumulative_equality_distinct_formulas
    }

    pub fn cumulative_equality_deduplicated_occurrences(self) -> u64 {
        self.cumulative_equality_deduplicated_occurrences
    }
}

#[derive(Debug)]
pub struct SymbolicInvState {
    houdini: HoudiniState,
    proposal: Vec<ClauseFormula>,
    proposal_progress: SymbolicProposalProgress,
    w_admissions: WAdmissionIndex,
    telemetry: TelemetryHandle,
    last_wave_start: usize,
    last_wave_len: usize,
    telemetry_epoch: u64,
    telemetry_maintenance_result: HashMap<crate::houdini::ClauseId, (u64, u64, u8, u8)>,
    telemetry_core: HashSet<crate::houdini::ClauseId>,
}

impl SymbolicInvState {
    pub fn houdini(&self) -> &HoudiniState {
        &self.houdini
    }

    pub fn houdini_mut(&mut self) -> &mut HoudiniState {
        &mut self.houdini
    }

    pub fn proposal(&self) -> &[ClauseFormula] {
        &self.proposal
    }

    pub fn proposal_progress(&self) -> SymbolicProposalProgress {
        self.proposal_progress
    }

    pub fn w_admissions(&self) -> &WAdmissionIndex {
        &self.w_admissions
    }

    /// Attach one observational run telemetry handle before the lane starts.
    pub fn attach_telemetry(&mut self, telemetry: TelemetryHandle) {
        self.houdini.attach_telemetry(telemetry.clone());
        self.telemetry = telemetry;
    }

    pub(crate) fn telemetry_handle(&self) -> TelemetryHandle {
        self.telemetry.clone()
    }
}

pub fn new_symbolic_inv_state(
    task: &SynthesisTask,
    encoding_context: SolverEncodingContext,
    artifacts: &ArtifactStore,
    verification: VerificationParameters,
    admission: SolverAdmission,
    log_maintenance_history: bool,
    fail_on_history_log_error: bool,
) -> Result<SymbolicInvState, FailureReport> {
    let expected_history = match (log_maintenance_history, fail_on_history_log_error) {
        (false, false) => HistoryMode::Disabled,
        (true, false) => HistoryMode::BestEffort,
        (true, true) => HistoryMode::Strict,
        (false, true) => {
            return Err(symbolic_failure(
                FailureKind::InfrastructureFailure,
                FailureScope::RunGlobal,
                "strict maintenance-history failure handling requires history logging",
                Vec::new(),
            ));
        }
    };
    if admission.class() != SolverAdmissionClass::Inv
        || admission.policy() != verification.resources()
        || encoding_context.task_identity() != task.identity()
        || encoding_context.proposal_revision() != ProposalRevision::INITIAL
        || artifacts.diagnostics().history_mode != expected_history
    {
        return Err(symbolic_failure(
            FailureKind::InfrastructureFailure,
            FailureScope::RunGlobal,
            "symbolic INV inputs do not share one fresh task, resource, and history authority",
            Vec::new(),
        ));
    }
    let inv_artifacts = artifacts.scoped(ScopeTag::Inv);
    let enumerator_version = encoding_context
        .proposal_realization()
        .realization_version();
    let catalog = ClauseCatalog::new(task, encoding_context, &inv_artifacts)?;
    let mut houdini = HoudiniState::new(task, verification, admission, catalog)?;
    houdini.set_maintenance_schedule_policy(
        CoverageMode::UseProducerClosed,
        TrackLayout::OrdinaryAndWTracks,
        CoverageLookup::LiteralSubsetThenIncoming,
    )?;
    Ok(SymbolicInvState {
        houdini,
        proposal: Vec::new(),
        proposal_progress: SymbolicProposalProgress {
            enumerator_version,
            revision: ProposalRevision::INITIAL,
            last_stage: None,
            cumulative_decoded_formula_occurrences: 0,
            cumulative_equality_distinct_formulas: 0,
            cumulative_equality_deduplicated_occurrences: 0,
        },
        w_admissions: WAdmissionIndex::default(),
        telemetry: TelemetryHandle::disabled(),
        last_wave_start: 0,
        last_wave_len: 0,
        telemetry_epoch: 0,
        telemetry_maintenance_result: HashMap::new(),
        telemetry_core: HashSet::new(),
    })
}

// ------------------------------------------------------------
// Reference Proposal And Ordinary Preparation
// ------------------------------------------------------------

pub async fn propose_symbolic_clauses(
    state: &mut SymbolicInvState,
    cancellation: &CancellationToken,
) -> Result<(), EncodingError> {
    if state
        .houdini
        .catalog()
        .encoding_context()
        .proposal_revision()
        != state.proposal_progress.revision
    {
        return Err(EncodingError::Failure(symbolic_failure(
            FailureKind::StateInvariantViolation,
            FailureScope::RunGlobal,
            "symbolic proposal progress differs from the encoding authority",
            Vec::new(),
        )));
    }
    let _attempt_span = state.telemetry.span("inv.reference_wave_attempt");
    let started = state.telemetry.is_enabled().then(Instant::now);
    let batch = state
        .houdini
        .catalog()
        .encoding_context()
        .advance_reference_proposal(state.houdini.admission(), cancellation)
        .await?;
    let proposal_realization = state
        .houdini
        .catalog()
        .encoding_context()
        .proposal_realization();
    let stage = batch.stage();
    let revision = batch.revision();
    let worker_wave_len = batch.entries().len();
    let page_count = batch.page_count();
    let cumulative_decoded_formula_occurrences = batch.cumulative_decoded_formula_occurrences();
    let cumulative_equality_distinct_formulas = batch.cumulative_equality_distinct_formulas();
    let cumulative_equality_deduplicated_occurrences =
        batch.cumulative_equality_deduplicated_occurrences();
    let generator_work_units = batch.generator_work_units();
    let fresh_traversal_nodes = batch.fresh_traversal_nodes();
    let fresh_no_fresh_prunes = batch.fresh_no_fresh_prunes();
    let fresh_too_short_prunes = batch.fresh_too_short_prunes();
    let stage_delta_decoded_formula_occurrences = cumulative_decoded_formula_occurrences
        .checked_sub(
            state
                .proposal_progress
                .cumulative_decoded_formula_occurrences,
        )
        .ok_or_else(|| invalid_reference_population("raw occurrence"))?;
    let stage_delta_equality_distinct_formulas = cumulative_equality_distinct_formulas
        .checked_sub(
            state
                .proposal_progress
                .cumulative_equality_distinct_formulas,
        )
        .ok_or_else(|| invalid_reference_population("canonical formula"))?;
    let stage_delta_equality_deduplicated_occurrences =
        cumulative_equality_deduplicated_occurrences
            .checked_sub(
                state
                    .proposal_progress
                    .cumulative_equality_deduplicated_occurrences,
            )
            .ok_or_else(|| invalid_reference_population("canonical duplicate"))?;
    if stage_delta_equality_distinct_formulas != u64::try_from(worker_wave_len).unwrap_or(u64::MAX)
        || stage_delta_equality_deduplicated_occurrences
            != stage_delta_decoded_formula_occurrences
                .saturating_sub(stage_delta_equality_distinct_formulas)
    {
        return Err(invalid_reference_population("exact-wave population"));
    }
    let wave_start = state.proposal.len();
    state.proposal.reserve(worker_wave_len);
    state.proposal.extend(
        batch
            .into_entries()
            .iter()
            .cloned()
            .map(ClauseFormula::from_validated_reference_source),
    );
    let emitted = state.proposal.len().saturating_sub(wave_start);
    if emitted != worker_wave_len {
        return Err(invalid_reference_population("decoded exact-wave emission"));
    }
    state.proposal_progress = SymbolicProposalProgress {
        enumerator_version: state
            .houdini
            .catalog()
            .encoding_context()
            .proposal_realization()
            .realization_version(),
        revision,
        last_stage: Some(stage),
        cumulative_decoded_formula_occurrences,
        cumulative_equality_distinct_formulas,
        cumulative_equality_deduplicated_occurrences,
    };
    state.last_wave_start = wave_start;
    state.last_wave_len = emitted;
    if let Some(started) = started {
        let elapsed = started.elapsed();
        state.telemetry.increment("inv.reference_stages", 1);
        state.telemetry.increment(
            "inv.reference_stage_delta_decoded_formula_occurrences",
            stage_delta_decoded_formula_occurrences,
        );
        state.telemetry.increment(
            "inv.reference_stage_delta_equality_distinct_formulas",
            stage_delta_equality_distinct_formulas,
        );
        state.telemetry.increment(
            "inv.reference_stage_delta_equality_deduplicated_occurrences",
            stage_delta_equality_deduplicated_occurrences,
        );
        state.telemetry.observe_max(
            "inv.reference_cumulative_decoded_formula_occurrences",
            cumulative_decoded_formula_occurrences,
        );
        state.telemetry.observe_max(
            "inv.reference_cumulative_equality_distinct_formulas",
            cumulative_equality_distinct_formulas,
        );
        state.telemetry.observe_max(
            "inv.reference_cumulative_equality_deduplicated_occurrences",
            cumulative_equality_deduplicated_occurrences,
        );
        state.telemetry.increment("inv.reference_pages", page_count);
        state
            .telemetry
            .increment("inv.reference_worker_stage_batch_evaluations", 1);
        let prior_slice_evaluations =
            u64::from(proposal_realization == ProposalRealization::ReferenceV3 && stage > 0);
        if prior_slice_evaluations != 0 {
            state.telemetry.increment(
                "inv.reference_prior_slice_evaluations",
                prior_slice_evaluations,
            );
        }
        state
            .telemetry
            .increment("inv.reference_emitted_formulas", emitted as u64);
        state
            .telemetry
            .increment("inv.proposal_generator_work_units", generator_work_units);
        state
            .telemetry
            .increment("inv.proposal_fresh_traversal_nodes", fresh_traversal_nodes);
        state
            .telemetry
            .increment("inv.proposal_fresh_no_fresh_prunes", fresh_no_fresh_prunes);
        state.telemetry.increment(
            "inv.proposal_fresh_too_short_prunes",
            fresh_too_short_prunes,
        );
        state
            .telemetry
            .add_duration("inv.reference_wave_inclusive", elapsed);
        state.telemetry.record_wave(WaveTelemetry {
            stage,
            parameters: ReferenceParametersTelemetry::at_reference_stage(stage),
            reference_features: ReferenceFeatureSetTelemetry::all_enabled(),
            page_count,
            worker_stage_batch_evaluations: 1,
            prior_slice_evaluations,
            stage_delta_decoded_formula_occurrences: Some(stage_delta_decoded_formula_occurrences),
            stage_delta_equality_distinct_formulas: Some(stage_delta_equality_distinct_formulas),
            stage_delta_equality_deduplicated_occurrences: Some(
                stage_delta_equality_deduplicated_occurrences,
            ),
            cumulative_decoded_formula_occurrences: Some(cumulative_decoded_formula_occurrences),
            cumulative_equality_distinct_formulas: Some(cumulative_equality_distinct_formulas),
            cumulative_equality_deduplicated_occurrences: Some(
                cumulative_equality_deduplicated_occurrences,
            ),
            generator_work_units,
            fresh_traversal_nodes,
            fresh_no_fresh_prunes,
            fresh_too_short_prunes,
            emitted_formulas: emitted as u64,
            wave_registration_attempts: 0,
            registered_unique_formulas: 0,
            previously_seen_formulas: 0,
            cumulative_registration_rechecks: 0,
            cumulative_proposal_size: state.proposal.len() as u64,
            cumulative_catalog_size: state.houdini.catalog().len() as u64,
            lean_enumeration_nanoseconds: None,
            transport_and_rust_validation_nanoseconds: None,
            reference_wave_inclusive_nanoseconds: elapsed.as_nanos().min(u128::from(u64::MAX))
                as u64,
            registration_and_formula_preparation_nanoseconds: None,
            catalog_registration_nanoseconds: None,
            formula_body_preparation_nanoseconds: None,
        });
        state.telemetry.event_with("reference_wave", || {
            serde_json::json!({
                "stage": stage,
                "proposal_realization_id": proposal_realization.realization_id(),
                "proposal_realization_version": proposal_realization.realization_version(),
                "page_count": page_count,
                "worker_stage_batch_evaluations": 1,
                "prior_slice_evaluations": prior_slice_evaluations,
                "stage_delta_decoded_formula_occurrences": stage_delta_decoded_formula_occurrences,
                "stage_delta_equality_distinct_formulas": stage_delta_equality_distinct_formulas,
                "stage_delta_equality_deduplicated_occurrences": stage_delta_equality_deduplicated_occurrences,
                "cumulative_decoded_formula_occurrences": cumulative_decoded_formula_occurrences,
                "cumulative_equality_distinct_formulas": cumulative_equality_distinct_formulas,
                "cumulative_equality_deduplicated_occurrences": cumulative_equality_deduplicated_occurrences,
                "generator_work_units": generator_work_units,
                "fresh_traversal_nodes": fresh_traversal_nodes,
                "fresh_no_fresh_prunes": fresh_no_fresh_prunes,
                "fresh_too_short_prunes": fresh_too_short_prunes,
                "emitted_formulas": emitted,
                "cumulative_proposal_size": state.proposal.len(),
                "reference_wave_inclusive_nanoseconds": elapsed.as_nanos(),
            })
        });
    }
    Ok(())
}

fn invalid_reference_population(population: &str) -> EncodingError {
    EncodingError::Failure(symbolic_failure(
        FailureKind::StateInvariantViolation,
        FailureScope::RunGlobal,
        format!("reference-proposal {population} counts are not one monotone exact wave"),
        Vec::new(),
    ))
}

pub async fn prepare_ordinary_candidates(
    state: &mut SymbolicInvState,
    cancellation: &CancellationToken,
) -> InitializationInvocationOutcome {
    let telemetry_enabled = state.telemetry.is_enabled();
    // Catalog length is O(1). Keep this progress delta at every telemetry
    // level; aggregate-only bookkeeping remains guarded below.
    let catalog_before = state.houdini.catalog().len();
    let started = telemetry_enabled.then(Instant::now);
    let preexisting_wave_ids = if telemetry_enabled {
        current_wave(state)
            .iter()
            .filter_map(|formula| match state.houdini.catalog().find(formula) {
                Ok(id) => id,
                Err(report) => {
                    state.telemetry.record_error(format!(
                        "inspect exact-wave Catalog membership: {}",
                        report.detail().unwrap_or("Catalog lookup failed")
                    ));
                    None
                }
            })
            .collect::<HashSet<_>>()
    } else {
        HashSet::new()
    };
    let (outcome, registration_timing) = state
        .houdini
        .prepare_init_candidates_with_timing(
            state.proposal.iter().cloned(),
            &ClauseSet::new(),
            cancellation,
        )
        .await;
    let catalog_after = state.houdini.catalog().len();
    let registered = catalog_after.saturating_sub(catalog_before);
    state
        .telemetry
        .increment("catalog.registered_unique", registered as u64);
    if let (Some(stage), Some(started)) = (state.proposal_progress.last_stage, started) {
        let elapsed = started.elapsed();
        let wave_attempts = state.last_wave_len;
        let cumulative_attempts = state.proposal.len();
        if registered > wave_attempts {
            state.telemetry.record_error(
                "one ordinary registration added more clauses than the current exact wave",
            );
        }
        let previously_seen = wave_attempts.saturating_sub(registered);
        let cumulative_rechecks = cumulative_attempts.saturating_sub(wave_attempts);
        state
            .telemetry
            .update_wave_registration(WaveRegistrationTelemetry {
                stage,
                wave_registration_attempts: wave_attempts as u64,
                registered_unique_formulas: registered as u64,
                previously_seen_formulas: previously_seen as u64,
                cumulative_registration_rechecks: cumulative_rechecks as u64,
                cumulative_catalog_size: catalog_after as u64,
                registration_and_formula_preparation_duration: elapsed,
                catalog_registration_duration: registration_timing.catalog_registration,
                formula_body_preparation_duration: registration_timing.formula_body_preparation,
            });
        state
            .telemetry
            .increment("catalog.registration_attempts", cumulative_attempts as u64);
        state
            .telemetry
            .increment("catalog.wave_registration_attempts", wave_attempts as u64);
        state.telemetry.increment(
            "catalog.cumulative_registration_rechecks",
            cumulative_rechecks as u64,
        );
        state
            .telemetry
            .increment("catalog.previously_seen", previously_seen as u64);
        state
            .telemetry
            .add_duration("inv.registration_and_init_preparation", elapsed);
        state.telemetry.add_duration(
            "catalog.registration",
            registration_timing.catalog_registration,
        );
        state.telemetry.add_duration(
            "catalog.formula_body_preparation",
            registration_timing.formula_body_preparation,
        );
        record_current_wave_births(state, stage, &preexisting_wave_ids);
    }
    if !matches!(outcome, InitializationInvocationOutcome::Complete)
        || state.houdini.maintenance_failure().is_some()
    {
        return outcome;
    }

    let admitted_w = state.w_admissions.admitted_clauses();
    let mut retained = ClauseSet::new();
    for id in state.houdini.init_candidates() {
        let record = match state.houdini.catalog().record(*id) {
            Ok(record) => record,
            Err(report) => {
                state.houdini.record_frontend_failure(report.clone());
                return if report.scope() == FailureScope::RunGlobal {
                    InitializationInvocationOutcome::RunFailure(report)
                } else {
                    InitializationInvocationOutcome::Complete
                };
            }
        };
        if record.initialization() != InitializationStatus::InitRefuted && !admitted_w.contains(id)
        {
            retained.insert(*id);
        }
    }
    if let Err(report) = state.houdini.retain_init_candidates(retained.clone()) {
        state.houdini.record_frontend_failure(report.clone());
        return failure_initialization_outcome(report);
    }
    for id in retained {
        if let Err(report) = state.houdini.set_track_hint(
            id,
            MaintenanceTrackHint::new(MaintenanceTrackKind::Ordinary, None),
        ) {
            state.houdini.record_frontend_failure(report.clone());
            return failure_initialization_outcome(report);
        }
    }
    InitializationInvocationOutcome::Complete
}

fn current_wave(state: &SymbolicInvState) -> &[ClauseFormula] {
    let end = state
        .last_wave_start
        .saturating_add(state.last_wave_len)
        .min(state.proposal.len());
    &state.proposal[state.last_wave_start..end]
}

fn record_current_wave_births(
    state: &SymbolicInvState,
    stage: u64,
    preexisting: &HashSet<crate::houdini::ClauseId>,
) {
    if !state.telemetry.is_enabled() {
        return;
    }
    let relation_arities = solver_relation_arities(state);
    for formula in current_wave(state) {
        let Ok(Some(id)) = state.houdini.catalog().find(formula) else {
            state
                .telemetry
                .record_error("an emitted reference formula was not registered");
            continue;
        };
        let Some((shape, minimal_eligibility)) =
            reference_formula_shape(formula.identity(), &relation_arities)
        else {
            state
                .telemetry
                .record_error("could not extract a validated reference formula shape");
            continue;
        };
        let binding_dimensions = binding_dimensions(stage, &minimal_eligibility);
        let schedule_slack_at_birth = schedule_slack(stage, &minimal_eligibility);
        let registered_unique = !preexisting.contains(&id);
        state.telemetry.record_formula_birth(FormulaBirthTelemetry {
            clause_id: Some(id.get()),
            registered_unique,
            stage,
            source_id: formula.source().source_id().to_string(),
            shape: shape.clone(),
            minimal_eligibility,
            binding_dimensions,
            schedule_slack_at_birth,
        });
        if !registered_unique {
            continue;
        }
        state.telemetry.event_with("formula_registered", || {
            serde_json::json!({
                "clause_id": id.get(),
                "stage": stage,
                "source_id": formula.source().source_id(),
                "clause_width": shape.clause_width,
                "ra_cost": shape.ra_cost,
                "selection_condition_nodes": shape.selection_condition_nodes,
                "maximum_projection_excess": shape.maximum_projection_excess,
                "output_arity": shape.output_arity,
                "serialized_size_bin": shape.serialized_size_bin,
                "skeleton": shape.normalized_structural_skeleton,
            })
        });
    }
}

fn solver_relation_arities(state: &SymbolicInvState) -> BTreeMap<String, u64> {
    state
        .houdini
        .catalog()
        .encoding_context()
        .task()
        .solver_relations()
        .iter()
        .map(|relation| (relation.key().as_str().to_string(), relation.arity()))
        .collect()
}

fn schedule_slack(
    stage: u64,
    eligibility: &ReferenceParametersTelemetry,
) -> ReferenceParametersTelemetry {
    ReferenceParametersTelemetry {
        max_ra_ops: stage.saturating_sub(eligibility.max_ra_ops),
        max_selection_condition_nodes: stage
            .saturating_sub(eligibility.max_selection_condition_nodes),
        max_projection_excess: stage.saturating_sub(eligibility.max_projection_excess),
        max_output_arity: stage.saturating_sub(eligibility.max_output_arity),
        max_clause_width: stage.saturating_sub(eligibility.max_clause_width),
    }
}

fn binding_dimensions(stage: u64, eligibility: &ReferenceParametersTelemetry) -> Vec<String> {
    [
        ("max_ra_ops", eligibility.max_ra_ops),
        (
            "max_selection_condition_nodes",
            eligibility.max_selection_condition_nodes,
        ),
        ("max_projection_excess", eligibility.max_projection_excess),
        ("max_output_arity", eligibility.max_output_arity),
        ("max_clause_width", eligibility.max_clause_width),
    ]
    .into_iter()
    .filter(|(_, required)| *required == stage)
    .map(|(name, _)| name.to_string())
    .collect()
}

fn record_houdini_telemetry(state: &mut SymbolicInvState) {
    if !state.telemetry.is_enabled() {
        return;
    }
    let mut clauses = state
        .proposal
        .iter()
        .filter_map(|formula| state.houdini.catalog().find(formula).ok().flatten())
        .collect::<HashSet<_>>();
    clauses.extend(state.w_admissions.admitted_clauses());
    clauses.extend(state.houdini.core().iter().copied());
    clauses.extend(state.houdini.init_candidates().iter().copied());
    clauses.extend(state.houdini.active().iter().copied());

    for id in clauses {
        let Ok(record) = state.houdini.catalog().record(id) else {
            state
                .telemetry
                .record_error("could not read one registered clause for telemetry");
            continue;
        };
        if let Some(result) = record.latest_maintenance() {
            let identity = (
                result.candidate_run_id(),
                result.candidate_generation(),
                maintenance_class_code(result.class()),
                maintenance_disposition_code(result.disposition()),
            );
            if state.telemetry_maintenance_result.get(&id) != Some(&identity) {
                state.telemetry_maintenance_result.insert(id, identity);
                let class_name = maintenance_class_name(result.class());
                let disposition_name = maintenance_disposition_name(result.disposition());
                state
                    .telemetry
                    .record_disposition(format!("maintenance_{class_name}"), 1);
                state.telemetry.event_with("clause_maintenance", || {
                    serde_json::json!({
                        "clause_id": id.get(),
                        "candidate_run_id": result.candidate_run_id(),
                        "candidate_generation": result.candidate_generation(),
                        "candidate_size": result.candidate_len(),
                        "result": class_name,
                        "application": disposition_name,
                    })
                });
            }
        }
        if state.houdini.core().contains(&id) && state.telemetry_core.insert(id) {
            state.telemetry.record_disposition("core_admission", 1);
            state.telemetry.record_core_admission(id.get());
            state.telemetry.event_with(
                "core_admission",
                || serde_json::json!({"clause_id": id.get(), "epoch": state.telemetry_epoch}),
            );
        }
    }
}

fn maintenance_class_code(class: MaintenanceResultClass) -> u8 {
    match class {
        MaintenanceResultClass::Proved => 0,
        MaintenanceResultClass::Refuted => 1,
        MaintenanceResultClass::TimedOut => 2,
        MaintenanceResultClass::Failed => 3,
    }
}

fn maintenance_class_name(class: MaintenanceResultClass) -> &'static str {
    match class {
        MaintenanceResultClass::Proved => "proof",
        MaintenanceResultClass::Refuted => "refutation",
        MaintenanceResultClass::TimedOut => "timeout",
        MaintenanceResultClass::Failed => "failure",
    }
}

fn maintenance_disposition_code(disposition: MaintenanceResultDisposition) -> u8 {
    match disposition {
        MaintenanceResultDisposition::Applied => 0,
        MaintenanceResultDisposition::Redundant => 1,
        MaintenanceResultDisposition::Conflicting => 2,
        MaintenanceResultDisposition::CleanupOnly => 3,
        MaintenanceResultDisposition::Canceled => 4,
    }
}

fn maintenance_disposition_name(disposition: MaintenanceResultDisposition) -> &'static str {
    match disposition {
        MaintenanceResultDisposition::Applied => "applied",
        MaintenanceResultDisposition::Redundant => "redundant",
        MaintenanceResultDisposition::Conflicting => "conflicting",
        MaintenanceResultDisposition::CleanupOnly => "cleanup_only",
        MaintenanceResultDisposition::Canceled => "canceled",
    }
}

// ------------------------------------------------------------
// Proved-W Admission
// ------------------------------------------------------------

pub async fn drain_proved_w_batch(
    state: &mut SymbolicInvState,
    receiver: &WProofReceiver,
    cancellation: &CancellationToken,
) -> InitializationInvocationOutcome {
    if state.houdini.maintenance_failure().is_some() {
        return InitializationInvocationOutcome::Complete;
    }
    let restored = state.w_admissions.admitted_clauses();
    if let Err(report) = state.houdini.restore_initialized_candidates(&restored) {
        state.houdini.record_frontend_failure(report.clone());
        return failure_initialization_outcome(report);
    }
    if let Some(batch) = receiver.peek_proved_batch() {
        if !receiver.validate_batch(&batch) {
            return record_symbolic_failure(state, "proved W batch belongs to another receiver");
        }
        let outcome = admit_proved_w_batch(state, &batch, cancellation).await;
        if !matches!(outcome, InitializationInvocationOutcome::Complete)
            || state.houdini.maintenance_failure().is_some()
        {
            return outcome;
        }
        if let Err(report) = install_w_layer_support(state, &batch) {
            state.houdini.record_frontend_failure(report.clone());
            return failure_initialization_outcome(report);
        }
        let restored = state.w_admissions.admitted_clauses();
        if let Err(report) = state.houdini.restore_initialized_candidates(&restored) {
            state.houdini.record_frontend_failure(report.clone());
            return failure_initialization_outcome(report);
        }
        if let Err(detail) = receiver.acknowledge_proved_batch(&batch) {
            return record_symbolic_failure(state, detail);
        }
    }
    InitializationInvocationOutcome::Complete
}

async fn admit_proved_w_batch(
    state: &mut SymbolicInvState,
    batch: &ProvedWBatch,
    cancellation: &CancellationToken,
) -> InitializationInvocationOutcome {
    let registration = register_clauses(
        state.houdini.catalog(),
        state.houdini.admission(),
        batch.entries().iter().map(|entry| entry.formula().clone()),
        cancellation,
    )
    .await;
    match registration {
        crate::houdini::RegisteredClauses::Complete(_) => {}
        crate::houdini::RegisteredClauses::Cancelled { .. } => {
            return InitializationInvocationOutcome::Cancelled;
        }
        crate::houdini::RegisteredClauses::Failure { report, .. } => {
            state.houdini.record_frontend_failure(report.clone());
            return failure_initialization_outcome(report);
        }
    }

    let relation_arities = solver_relation_arities(state);
    for entry in batch.entries() {
        let id = match state.houdini.catalog().find(entry.formula()) {
            Ok(Some(id)) => id,
            Ok(None) => return record_symbolic_failure(state, "registered W formula is absent"),
            Err(report) => {
                state.houdini.record_frontend_failure(report.clone());
                return failure_initialization_outcome(report);
            }
        };
        if let Some(existing) = state.w_admissions.get(entry.index()) {
            if existing.clause_id() != id
                || existing.initialization_evidence() != entry.initialization_evidence()
            {
                return record_symbolic_failure(
                    state,
                    "one W index was replayed with conflicting provenance",
                );
            }
        } else {
            if let Some(bundle) = entry.bundle()
                && let Err(report) = state.houdini.catalog().accept_prepared_maintenance_wp(
                    id,
                    bundle.identity(),
                    bundle.maintenance_wp_body().clone(),
                )
            {
                state.houdini.record_frontend_failure(report.clone());
                return failure_initialization_outcome(report);
            }
            if let Err(report) = state
                .houdini
                .catalog()
                .accept_external_initialization_proof(id, entry.initialization_evidence())
            {
                state.houdini.record_frontend_failure(report.clone());
                return failure_initialization_outcome(report);
            }
            state.telemetry.record_initialized_clauses([id.get()]);
            if state
                .w_admissions
                .insert(entry.index(), id, entry.initialization_evidence())
                .is_err()
            {
                return record_symbolic_failure(state, "conflicting W admission index update");
            }
            state
                .telemetry
                .increment("houdini.initialization.external_proofs", 1);
            state
                .telemetry
                .record_disposition("initialization_external_proof", 1);
            let shape = qf_formula_shape(entry.formula().identity(), &relation_arities)
                .map(|shape| (shape, None));
            if shape.is_none() {
                state
                    .telemetry
                    .record_error("could not extract a validated W-clause shape");
            }
            state
                .telemetry
                .record_w_clause(id.get(), entry.index(), shape);
            state
                .telemetry
                .event_with("initialization_external_proof", || {
                    serde_json::json!({
                        "clause_id": id.get(),
                        "w_index": entry.index(),
                    })
                });
        }
        if entry.index() == 0
            && let Err(report) = state.houdini.reopen_term_for_exact_shortcut(id)
        {
            state.houdini.record_frontend_failure(report.clone());
            return failure_initialization_outcome(report);
        }
        let Some(greatest_index) = state
            .w_admissions
            .indices_for_clause(id)
            .and_then(|indices| indices.iter().copied().max())
        else {
            return record_symbolic_failure(
                state,
                "an admitted W clause has no corresponding W index",
            );
        };
        let order_key = match i64::try_from(greatest_index) {
            Ok(key) => key,
            Err(_) => return record_symbolic_failure(state, "W index exceeds track-order range"),
        };
        if let Err(report) = state.houdini.set_track_hint(
            id,
            MaintenanceTrackHint::new(MaintenanceTrackKind::WLayer, Some(order_key)),
        ) {
            state.houdini.record_frontend_failure(report.clone());
            return failure_initialization_outcome(report);
        }
    }
    InitializationInvocationOutcome::Complete
}

fn install_w_layer_support(
    state: &mut SymbolicInvState,
    batch: &ProvedWBatch,
) -> Result<Vec<ArtifactRef>, FailureReport> {
    let mut provenance = Vec::new();
    let touched = batch
        .entries()
        .iter()
        .map(|entry| entry.index())
        .collect::<HashSet<_>>();
    for index in touched {
        if index > 0
            && let Some(reference) = install_adjacent_support(state, index, index - 1)?
        {
            provenance.push(reference);
        }
        if index < u64::MAX
            && let Some(reference) = install_adjacent_support(state, index + 1, index)?
        {
            provenance.push(reference);
        }
    }
    Ok(provenance)
}

fn install_adjacent_support(
    state: &mut SymbolicInvState,
    source_index: u64,
    target_index: u64,
) -> Result<Option<ArtifactRef>, FailureReport> {
    let (Some(source_clause), Some(target_clause)) = (
        state
            .w_admissions
            .get(source_index)
            .map(|entry| entry.clause_id()),
        state
            .w_admissions
            .get(target_index)
            .map(|entry| entry.clause_id()),
    ) else {
        return Ok(None);
    };
    if let Some(provenance) = state
        .w_admissions
        .support_provenance(source_index, target_index)
    {
        state.houdini.catalog().artifacts().resolve(provenance)?;
        return Ok(None);
    }
    state
        .w_admissions
        .reserve_support_provenance()
        .map_err(|detail| {
            symbolic_failure(
                FailureKind::InfrastructureFailure,
                FailureScope::RunGlobal,
                detail,
                Vec::new(),
            )
        })?;
    let mut base_core = state
        .houdini
        .core()
        .iter()
        .map(|clause| clause.get())
        .collect::<Vec<_>>();
    base_core.sort_unstable();
    let record = serde_json::json!({
        "version": 1,
        "kind": "w_successor_maintenance_support",
        "theorem": "Whiel.Synthesis.WLayer.formula_succ_step",
        "task": {
            "canonical_id": state.houdini.catalog().task_identity().canonical_id(),
            "semantic_version": state.houdini.catalog().task_identity().semantic_version(),
            "encoding_version": state.houdini.catalog().task_identity().encoding_version(),
            "source_sha256": state.houdini.catalog().task_identity().source_digest().as_str(),
        },
        "source": {"w_index": source_index, "clause_id": source_clause.get()},
        "target": {"w_index": target_index, "clause_id": target_clause.get()},
        "base_core": base_core,
    });
    let reference = state
        .houdini
        .catalog()
        .artifacts()
        .publish(
            ArtifactKind::RuntimeTrace,
            record.to_string().into_bytes().into_boxed_slice(),
        )
        .map_err(w_support_publication_failure)?;
    state
        .houdini
        .insert_maint_support(source_clause, target_clause)?;
    state
        .w_admissions
        .record_support_provenance(source_index, target_index, reference)
        .map_err(|detail| {
            symbolic_failure(
                FailureKind::StateInvariantViolation,
                FailureScope::RunGlobal,
                detail,
                vec![reference],
            )
        })?;
    Ok(Some(reference))
}

pub fn apply_w_zero_term_shortcut(state: &mut SymbolicInvState) -> Result<bool, FailureReport> {
    let Some(w_zero) = state.w_admissions.get(0) else {
        return Ok(false);
    };
    state.houdini.apply_exact_term_shortcut(w_zero.clause_id())
}

// ------------------------------------------------------------
// INV Epoch And Lane
// ------------------------------------------------------------

#[derive(Clone, Debug)]
pub struct SymbolicInvRuntime {
    vampire: VampireWorkerCommand,
    certification: CertificationRuntime,
}

impl SymbolicInvRuntime {
    pub fn new(vampire: VampireWorkerCommand, certification: CertificationRuntime) -> Self {
        Self {
            vampire,
            certification,
        }
    }
}

#[derive(Clone, Debug)]
pub enum SymbolicLaneOutcome {
    Terminal(CertifiedSynthesisResult),
    Inconclusive(FailureReport),
    RunFatal(FailureReport),
    Cancelled,
}

#[derive(Clone, Debug)]
pub enum SymbolicEpochOutcome {
    Continue,
    Lane(SymbolicLaneOutcome),
}

pub async fn run_symbolic_inv_epoch(
    task: &SynthesisTask,
    state: &mut SymbolicInvState,
    receiver: &WProofReceiver,
    runtime: &SymbolicInvRuntime,
    cancellation: &CancellationToken,
) -> SymbolicEpochOutcome {
    let _epoch_span = state.telemetry.span("inv.epoch");
    state.telemetry_epoch = state.telemetry_epoch.saturating_add(1);
    state.telemetry.increment("inv.epochs", 1);
    let next_reference_stage = state.proposal_progress.revision().get();
    state.telemetry.record_inv_epoch(InvEpochTelemetry {
        epoch: state.telemetry_epoch,
        next_reference_stage,
        next_reference_parameters: ReferenceParametersTelemetry::at_reference_stage(
            next_reference_stage,
        ),
        reference_features: ReferenceFeatureSetTelemetry::all_enabled(),
        proposal_size: u64::try_from(state.proposal.len()).unwrap_or(u64::MAX),
        catalog_size: u64::try_from(state.houdini.catalog().len()).unwrap_or(u64::MAX),
        core_size: u64::try_from(state.houdini.core().len()).unwrap_or(u64::MAX),
    });
    state.telemetry.event_with("inv_epoch_started", || {
        serde_json::json!({
            "epoch": state.telemetry_epoch,
            "proposal_size": state.proposal.len(),
            "catalog_size": state.houdini.catalog().len(),
            "core_size": state.houdini.core().len(),
        })
    });
    if state.houdini.catalog().task_identity() != task.identity()
        || !receiver.matches_authority(
            task.identity(),
            state.houdini.catalog().artifacts().backend_id(),
        )
    {
        return SymbolicEpochOutcome::Lane(SymbolicLaneOutcome::RunFatal(symbolic_failure(
            FailureKind::InfrastructureFailure,
            FailureScope::RunGlobal,
            "symbolic INV epoch inputs do not share one task and artifact authority",
            Vec::new(),
        )));
    }
    if let Some(report) = state.houdini.maintenance_failure().cloned() {
        return SymbolicEpochOutcome::Lane(classify_failure(report));
    }
    if let Err(error) = propose_symbolic_clauses(state, cancellation).await {
        return encoding_epoch_outcome(error);
    }
    if let Some(outcome) = invocation_epoch_outcome(
        prepare_ordinary_candidates(state, cancellation).await,
        state,
    ) {
        return outcome;
    }
    let initialization_started = state.telemetry.start_span();
    let initialization = check_initialization(
        task,
        &mut state.houdini,
        runtime.vampire.clone(),
        cancellation,
    )
    .await;
    state
        .telemetry
        .finish_span("inv.initialization", initialization_started);
    record_houdini_telemetry(state);
    if let Some(outcome) = invocation_epoch_outcome(initialization, state) {
        return outcome;
    }
    if let Some(outcome) = invocation_epoch_outcome(
        drain_proved_w_batch(state, receiver, cancellation).await,
        state,
    ) {
        return outcome;
    }
    let maintenance_preparation_started = state.telemetry.start_span();
    let maintenance_preparation = prepare_maintenance(task, &mut state.houdini, cancellation).await;
    state.telemetry.finish_span(
        "inv.maintenance_preparation",
        maintenance_preparation_started,
    );
    match maintenance_preparation {
        MaintenancePreparationOutcome::Complete => {}
        MaintenancePreparationOutcome::Cancelled => {
            return SymbolicEpochOutcome::Lane(SymbolicLaneOutcome::Cancelled);
        }
        MaintenancePreparationOutcome::RunFailure(report) => {
            return SymbolicEpochOutcome::Lane(SymbolicLaneOutcome::RunFatal(report));
        }
    }
    let maintenance_started = state.telemetry.start_span();
    let maintenance = houdini(
        task,
        &mut state.houdini,
        runtime.vampire.clone(),
        cancellation,
    )
    .await;
    state
        .telemetry
        .finish_span("inv.maintenance", maintenance_started);
    record_houdini_telemetry(state);
    match maintenance {
        HoudiniExecutionOutcome::Complete => {}
        HoudiniExecutionOutcome::Cancelled => {
            return SymbolicEpochOutcome::Lane(SymbolicLaneOutcome::Cancelled);
        }
        HoudiniExecutionOutcome::Failed(report) => {
            return SymbolicEpochOutcome::Lane(classify_failure(report));
        }
    }
    if let Some(report) = state.houdini.maintenance_failure().cloned() {
        return SymbolicEpochOutcome::Lane(classify_failure(report));
    }

    if matches!(state.houdini.last_term_status(), LastTermStatus::Pending) {
        if let Err(report) = apply_w_zero_term_shortcut(state) {
            return SymbolicEpochOutcome::Lane(classify_failure(report));
        }
        if matches!(state.houdini.last_term_status(), LastTermStatus::Pending) {
            let termination_started = state.telemetry.start_span();
            let termination = term_check(
                task,
                &mut state.houdini,
                runtime.vampire.clone(),
                cancellation,
            )
            .await;
            state
                .telemetry
                .finish_span("inv.termination", termination_started);
            match termination {
                TerminationInvocationOutcome::Complete => {}
                TerminationInvocationOutcome::Cancelled => {
                    return SymbolicEpochOutcome::Lane(SymbolicLaneOutcome::Cancelled);
                }
                TerminationInvocationOutcome::RunFailure(report) => {
                    return SymbolicEpochOutcome::Lane(SymbolicLaneOutcome::RunFatal(report));
                }
            }
        }
    }

    if matches!(state.houdini.last_term_status(), LastTermStatus::Proved) {
        // Validity-certification failure ends the run. Certification input is
        // the exact frozen Core, so a deterministic rejection recurs on every
        // repeat; only transient infrastructure kinds earn one same-core
        // retry, and no failure may revise the invariant or resume search.
        let mut attempt: u32 = 0;
        let outcome = loop {
            attempt += 1;
            state.telemetry.increment("inv.certification_attempts", 1);
            let certification_started = state.telemetry.start_span();
            let certification = certify_valid(
                task,
                &mut state.houdini,
                &runtime.certification,
                cancellation,
            )
            .await;
            state
                .telemetry
                .finish_span("inv.certification", certification_started);
            match certification {
                ValidityCertificationOutcome::Certified(certificate) => {
                    break SymbolicLaneOutcome::Terminal(CertifiedSynthesisResult::Valid(
                        certificate,
                    ));
                }
                ValidityCertificationOutcome::Cancelled => break SymbolicLaneOutcome::Cancelled,
                ValidityCertificationOutcome::Failure(report) => {
                    let will_retry =
                        attempt == 1 && report.retryable() && !cancellation.is_cancelled();
                    state.telemetry.record_error(format!(
                        "validity certification attempt {attempt} failed ({:?}): {}",
                        report.kind(),
                        report.detail().unwrap_or("no detail"),
                    ));
                    state
                        .telemetry
                        .event_with("validity_certification_failed", || {
                            serde_json::json!({
                                "attempt": attempt,
                                "kind": format!("{:?}", report.kind()),
                                "retryable": report.retryable(),
                                "will_retry": will_retry,
                                "detail": report.detail(),
                            })
                        });
                    if !will_retry {
                        break SymbolicLaneOutcome::RunFatal(report);
                    }
                }
            }
        };
        return SymbolicEpochOutcome::Lane(outcome);
    }
    state.telemetry.event_with("inv_epoch_completed", || {
        serde_json::json!({
            "epoch": state.telemetry_epoch,
            "catalog_size": state.houdini.catalog().len(),
            "init_candidates": state.houdini.init_candidates().len(),
            "active": state.houdini.active().len(),
            "core_size": state.houdini.core().len(),
        })
    });
    SymbolicEpochOutcome::Continue
}

pub async fn run_inv_lane(
    task: &SynthesisTask,
    mut state: SymbolicInvState,
    receiver: WProofReceiver,
    runtime: SymbolicInvRuntime,
    cancellation: &CancellationToken,
) -> SymbolicLaneOutcome {
    state.telemetry.increment("lane.inv.starts", 1);
    let _lane_span = state.telemetry.span("lane.inv.activity");
    let outcome = loop {
        match run_symbolic_inv_epoch(task, &mut state, &receiver, &runtime, cancellation).await {
            SymbolicEpochOutcome::Continue => {}
            SymbolicEpochOutcome::Lane(outcome) => break outcome,
        }
    };
    record_final_inv_snapshot(&state);
    outcome
}

fn record_final_inv_snapshot(state: &SymbolicInvState) {
    if !state.telemetry.is_enabled() {
        return;
    }
    let mut clauses = state
        .proposal
        .iter()
        .filter_map(|formula| state.houdini.catalog().find(formula).ok().flatten())
        .collect::<HashSet<_>>();
    clauses.extend(state.w_admissions.admitted_clauses());
    clauses.extend(state.houdini.core().iter().copied());
    clauses.extend(state.houdini.active().iter().copied());
    clauses.extend(state.houdini.init_candidates().iter().copied());

    let mut populations = BTreeMap::<String, u64>::new();
    for id in clauses {
        let disposition = final_formula_disposition(state, id);
        let population = populations.entry(disposition.to_string()).or_default();
        *population = population.saturating_add(1);
        state
            .telemetry
            .record_final_formula_disposition(id.get(), disposition);
    }
    let dormant = populations
        .iter()
        .filter(|(name, _)| name.starts_with("dormant_"))
        .map(|(_, count)| *count)
        .fold(0_u64, u64::saturating_add);
    state
        .telemetry
        .record_disposition("dormant_retention", dormant);
    state.telemetry.event_with("inv_final_populations", || {
        serde_json::json!({
            "populations": populations,
            "catalog_size": state.houdini.catalog().len(),
            "core_size": state.houdini.core().len(),
        })
    });
}

fn final_formula_disposition(
    state: &SymbolicInvState,
    id: crate::houdini::ClauseId,
) -> &'static str {
    if state.houdini.core().contains(&id) {
        return "core";
    }
    if state.houdini.active().contains(&id) {
        return "active";
    }
    let Ok(record) = state.houdini.catalog().record(id) else {
        return "unclassified";
    };
    match record.initialization() {
        InitializationStatus::Unclassified => {
            if state.houdini.init_candidates().contains(&id) {
                "initialization_candidate"
            } else {
                "unclassified"
            }
        }
        InitializationStatus::InitRefuted => "pruned_initialization_refutation",
        InitializationStatus::InitInconclusive => "dormant_initialization_inconclusive",
        InitializationStatus::InitProved => match record.latest_maintenance() {
            None => "dormant_initialized",
            Some(result) => match result.class() {
                MaintenanceResultClass::Refuted => "pruned_maintenance_refutation",
                MaintenanceResultClass::TimedOut => "pruned_maintenance_timeout",
                MaintenanceResultClass::Failed => "pruned_maintenance_failure",
                MaintenanceResultClass::Proved => "dormant_maintenance_proved",
            },
        },
    }
}

// ------------------------------------------------------------
// Failure Projection
// ------------------------------------------------------------

fn invocation_epoch_outcome(
    outcome: InitializationInvocationOutcome,
    state: &SymbolicInvState,
) -> Option<SymbolicEpochOutcome> {
    match outcome {
        InitializationInvocationOutcome::Complete => state
            .houdini
            .maintenance_failure()
            .cloned()
            .map(|report| SymbolicEpochOutcome::Lane(classify_failure(report))),
        InitializationInvocationOutcome::Cancelled => {
            Some(SymbolicEpochOutcome::Lane(SymbolicLaneOutcome::Cancelled))
        }
        InitializationInvocationOutcome::RunFailure(report) => Some(SymbolicEpochOutcome::Lane(
            SymbolicLaneOutcome::RunFatal(report),
        )),
    }
}

fn encoding_epoch_outcome(error: EncodingError) -> SymbolicEpochOutcome {
    SymbolicEpochOutcome::Lane(match error {
        EncodingError::Cancelled => SymbolicLaneOutcome::Cancelled,
        EncodingError::Failure(report) => classify_failure(report),
    })
}

fn classify_failure(report: FailureReport) -> SymbolicLaneOutcome {
    if report.scope() == FailureScope::RunGlobal {
        SymbolicLaneOutcome::RunFatal(report)
    } else {
        SymbolicLaneOutcome::Inconclusive(report)
    }
}

fn failure_initialization_outcome(report: FailureReport) -> InitializationInvocationOutcome {
    if report.scope() == FailureScope::RunGlobal {
        InitializationInvocationOutcome::RunFailure(report)
    } else {
        InitializationInvocationOutcome::Complete
    }
}

fn record_symbolic_failure(
    state: &mut SymbolicInvState,
    detail: impl Into<String>,
) -> InitializationInvocationOutcome {
    let report = symbolic_failure(
        FailureKind::StateInvariantViolation,
        FailureScope::RunGlobal,
        detail,
        Vec::new(),
    );
    state.houdini.record_frontend_failure(report.clone());
    InitializationInvocationOutcome::RunFailure(report)
}

fn symbolic_failure(
    kind: FailureKind,
    scope: FailureScope,
    detail: impl Into<String>,
    artifacts: Vec<crate::artifact::ArtifactRef>,
) -> FailureReport {
    FailureReport::try_new(
        FailureOrigin::InitializationExecution,
        kind,
        false,
        scope,
        Some(detail.into()),
        artifacts,
    )
    .expect("symbolic INV failures use initialization-compatible kinds")
}

fn w_support_publication_failure(report: FailureReport) -> FailureReport {
    symbolic_failure(
        if report.kind() == FailureKind::PublicationFailure {
            FailureKind::PublicationFailure
        } else {
            FailureKind::InfrastructureFailure
        },
        FailureScope::RunGlobal,
        format!(
            "publish W-successor theorem provenance: {}",
            report.detail().unwrap_or("artifact backend failure")
        ),
        report.artifact_references().to_vec(),
    )
}
