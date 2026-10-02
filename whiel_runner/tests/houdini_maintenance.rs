mod support;

use whiel_runner::encoding::{
    EncodingWorkerCommand, EncodingWorkerPoolConfig, QfSolverSource, SolverBodySource,
    SolverEncodingContext, new_solver_encoding_context,
};
use whiel_runner::{
    ArtifactKind, ArtifactStore, ArtifactStoreConfig, CancellationToken, ClauseCatalog,
    ClauseFormula, ClauseId, ClauseSet, ConstantKey, CoverageLookup, CoverageMode, FailureKind,
    FailureScope, HoudiniState, MaintenancePolicy, MaintenancePreparationOutcome,
    MaintenanceTrackHint, MaintenanceTrackKind, RuntimeResourcePolicy, SolverAdmission,
    TrackLayout, VerificationParameters, close_init_coverage, close_maint_coverage,
    create_general_solver_admission, new_artifact_store, prepare_maintenance,
};

// ------------------------------------------------------------
// Shared Caller-Neutral Fixtures
// ------------------------------------------------------------

fn worker_config() -> EncodingWorkerPoolConfig {
    EncodingWorkerPoolConfig::new(
        EncodingWorkerCommand::new(
            support::example_encoding_worker(),
            support::repository_root(),
        ),
        2,
    )
    .expect("positive worker count")
}

fn runtime_policy() -> RuntimeResourcePolicy {
    RuntimeResourcePolicy::agent_only(2, 2).unwrap()
}

fn admission(policy: RuntimeResourcePolicy) -> SolverAdmission {
    create_general_solver_admission(policy).unwrap()
}

fn formula(
    task: &whiel_runner::SynthesisTask,
    canonical: &str,
    source_id: &str,
    relations: &[&str],
) -> ClauseFormula {
    let relations = relations
        .iter()
        .map(|key| {
            task.solver_relations()
                .iter()
                .find(|relation| relation.key().as_str() == *key)
                .unwrap_or_else(|| panic!("unknown fixture relation {key}"))
                .key()
                .clone()
        })
        .collect::<Vec<_>>();
    let source = SolverBodySource::QuantifierFree(
        QfSolverSource::new(task, source_id, Vec::<ConstantKey>::new(), relations).unwrap(),
    );
    ClauseFormula::from_trusted_lean_source(canonical, source).unwrap()
}

fn formulas(task: &whiel_runner::SynthesisTask) -> Vec<ClauseFormula> {
    vec![
        formula(task, "maint.true", "task.phase2c_qf_fixture", &[]),
        formula(
            task,
            "maint.catalog",
            "catalog.clause.0",
            &["rel:E:0", "rel:TBound:0"],
        ),
        formula(
            task,
            "maint.agent",
            "agent_naive.one_off",
            &["rel:E:0", "rel:T:0", "rel:T:1"],
        ),
    ]
}

fn new_state(
    task: &whiel_runner::SynthesisTask,
    artifacts: &ArtifactStore,
    context: &SolverEncodingContext,
) -> HoudiniState {
    let policy = runtime_policy();
    let verification =
        VerificationParameters::new(std::time::Duration::from_secs(2), policy).unwrap();
    let catalog = ClauseCatalog::new(task, context.clone(), artifacts).unwrap();
    HoudiniState::new(task, verification, admission(policy), catalog).unwrap()
}

async fn install_proved_proposal(
    state: &mut HoudiniState,
    proposal: Vec<ClauseFormula>,
) -> ClauseSet {
    let outcome = state
        .prepare_init_candidates(proposal, &ClauseSet::new(), &CancellationToken::new())
        .await;
    assert!(matches!(
        outcome,
        whiel_runner::InitializationInvocationOutcome::Complete
    ));
    let ids = state.init_candidates().clone();
    let evidence = state
        .catalog()
        .artifacts()
        .publish(
            ArtifactKind::InitializationCheck,
            b"fixture InitProved".as_slice().into(),
        )
        .unwrap();
    for id in &ids {
        state
            .catalog()
            .record_initialization(
                *id,
                whiel_runner::InitializationStatus::InitProved,
                evidence,
            )
            .unwrap();
    }
    ids
}

async fn shutdown(
    state: HoudiniState,
    context: SolverEncodingContext,
    artifacts: ArtifactStore,
    owner: whiel_runner::ArtifactBackendOwner,
) {
    context.shutdown().await.unwrap();
    drop(state);
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}

fn ordered(ids: &ClauseSet) -> Vec<ClauseId> {
    let mut ids = ids.iter().copied().collect::<Vec<_>>();
    ids.sort_unstable();
    ids
}

// ------------------------------------------------------------
// Exact WP Preparation And Support Projection
// ------------------------------------------------------------

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn exact_wps_and_noncomposable_support_publish_atomically() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("maintenance_support");
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_state(&task, &artifacts, &context);
    let ids = install_proved_proposal(&mut state, formulas(&task)).await;
    let ids = ordered(&ids);

    state.insert_maint_support(ids[0], ids[0]).unwrap();
    state.insert_maint_support(ids[0], ids[1]).unwrap();
    state.insert_maint_support(ids[1], ids[2]).unwrap();
    let result = prepare_maintenance(&task, &mut state, &CancellationToken::new()).await;
    assert!(matches!(result, MaintenancePreparationOutcome::Complete));
    assert!(
        state.maintenance_failure().is_none(),
        "{:?}",
        state.maintenance_failure()
    );
    assert_eq!(state.active(), &ClauseSet::from_iter(ids.iter().copied()));
    let plan = state.current_maintenance_plan(&task).unwrap();

    assert_eq!(plan.supported_by(ids[0]), &[ids[0]]);
    assert_eq!(plan.supported_by(ids[1]), &[ids[0]]);
    assert_eq!(plan.supported_by(ids[2]), &[ids[1]]);
    assert!(!plan.supported_by(ids[2]).contains(&ids[0]));
    assert_eq!(state.present_support_count(ids[0]), Some(1));
    assert_eq!(state.present_support_count(ids[1]), Some(1));
    assert_eq!(state.present_support_count(ids[2]), Some(1));
    assert_eq!(plan.schedule().tracks().len(), 1);
    assert_eq!(
        plan.schedule().tracks()[0].kind(),
        MaintenanceTrackKind::Default
    );
    assert_eq!(plan.schedule().tracks()[0].targets(), ids.as_slice());
    assert!(plan.closure_metrics().is_none());

    assert_eq!(
        state
            .insert_init_coverage(ids[0], ids[2])
            .unwrap_err()
            .kind(),
        FailureKind::StateInvariantViolation
    );
    assert_eq!(
        state.close_init_coverage().unwrap_err().kind(),
        FailureKind::StateInvariantViolation
    );
    assert_eq!(
        state
            .insert_maint_support(ids[0], ids[2])
            .unwrap_err()
            .kind(),
        FailureKind::StateInvariantViolation
    );
    assert_eq!(
        state
            .insert_maint_coverage(ids[0], ids[2])
            .unwrap_err()
            .kind(),
        FailureKind::StateInvariantViolation
    );
    assert_eq!(
        state
            .set_track_hint(
                ids[0],
                MaintenanceTrackHint::new(MaintenanceTrackKind::Ordinary, None),
            )
            .unwrap_err()
            .kind(),
        FailureKind::StateInvariantViolation
    );
    assert_eq!(
        state
            .set_maintenance_policy(MaintenancePolicy::single_track())
            .unwrap_err()
            .kind(),
        FailureKind::StateInvariantViolation
    );

    for id in ids {
        let record = state.catalog().record(id).unwrap();
        let wp = record.maintenance_wp().expect("exact WP handle");
        let body = record.maintenance_wp_body().expect("complete WP body");
        assert!(wp.source_id().starts_with("__whiel_maintenance_wp__:"));
        assert_eq!(wp.source_id(), body.source().source_id());
        assert!(body.theorem_id().contains("wpLoopFree_eval_iff"));
    }

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn literal_subset_policy_uses_the_sound_incoming_fallback() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("maintenance_lookup_binding");
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_state(&task, &artifacts, &context);
    install_proved_proposal(&mut state, formulas(&task)).await;
    state
        .set_maintenance_policy(MaintenancePolicy::new(
            CoverageMode::UseProducerClosed,
            TrackLayout::SingleTrack,
            CoverageLookup::LiteralSubsetThenIncoming,
        ))
        .unwrap();

    let result = prepare_maintenance(&task, &mut state, &CancellationToken::new()).await;
    assert!(matches!(result, MaintenancePreparationOutcome::Complete));
    assert!(state.maintenance_failure().is_none());
    let plan = state
        .maintenance_plan()
        .expect("the incoming fallback must publish a maintenance plan");
    assert_eq!(
        plan.coverage_lookup(),
        CoverageLookup::LiteralSubsetThenIncoming
    );
    assert!(!state.active().is_empty());

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn producer_supplied_wp_is_reused_without_derived_recomputation() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("maintenance_supplied_wp");
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_state(&task, &artifacts, &context);
    let ids = install_proved_proposal(
        &mut state,
        vec![formula(
            &task,
            "maint.supplied.target",
            "legacy.init.goal",
            &["rel:E:0", "rel:T:0", "rel:T:1", "rel:TBound:0"],
        )],
    )
    .await;
    let id = *ids.iter().next().unwrap();
    let supplied = formula(
        &task,
        "maint.supplied.wp",
        "catalog.wp.0",
        &["rel:E:0", "rel:T:0", "rel:TBound:0"],
    );
    state
        .catalog()
        .prepare_supplied_maintenance_wp(state.admission(), id, supplied, &CancellationToken::new())
        .await
        .unwrap();

    let before = state.catalog().record(id).unwrap();
    assert_eq!(before.maintenance_wp().unwrap().source_id(), "catalog.wp.0");
    assert_eq!(
        before.maintenance_wp_body().unwrap().theorem_id(),
        "Whiel.Vampire.TPTP.roleNeutralBody_stable"
    );

    let result = prepare_maintenance(&task, &mut state, &CancellationToken::new()).await;
    assert!(matches!(result, MaintenancePreparationOutcome::Complete));
    assert!(state.maintenance_failure().is_none());
    let after = state.catalog().record(id).unwrap();
    assert_eq!(after.maintenance_wp().unwrap().source_id(), "catalog.wp.0");
    assert_eq!(
        after.maintenance_wp_body().unwrap().body_id(),
        before.maintenance_wp_body().unwrap().body_id()
    );

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn automatic_wp_matches_the_registered_legacy_maintenance_formula() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("maintenance_exact_wp");
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_state(&task, &artifacts, &context);
    let ids = install_proved_proposal(
        &mut state,
        vec![formula(
            &task,
            "maint.exact.target",
            "legacy.init.goal",
            &["rel:E:0", "rel:T:0", "rel:T:1", "rel:TBound:0"],
        )],
    )
    .await;
    let id = *ids.iter().next().unwrap();
    let base_body = state
        .catalog()
        .record(id)
        .unwrap()
        .formula_body()
        .unwrap()
        .tptp_body()
        .to_owned();
    let expected_source = formula(
        &task,
        "maint.exact.expected",
        "catalog.wp.0",
        &["rel:E:0", "rel:T:0", "rel:TBound:0"],
    );
    let expected = context
        .prepare_solver_bodies(
            state.admission(),
            &artifacts,
            vec![expected_source.source().clone()],
            &CancellationToken::new(),
        )
        .await
        .unwrap()
        .remove(0);

    let result = prepare_maintenance(&task, &mut state, &CancellationToken::new()).await;
    assert!(matches!(result, MaintenancePreparationOutcome::Complete));
    assert!(state.maintenance_failure().is_none());
    let prepared = state.catalog().record(id).unwrap();
    let wp_body = prepared.maintenance_wp_body().unwrap();
    assert_ne!(wp_body.tptp_body(), base_body);
    assert_eq!(wp_body.tptp_body(), expected.tptp_body());
    assert!(wp_body.theorem_id().contains("wpLoopFree_eval_iff"));

    let exposed_source = prepared.maintenance_wp().unwrap().clone();
    let exposed_body_id = wp_body.body_id().to_owned();
    drop(prepared);
    context.shutdown().await.unwrap();
    let warmed = context
        .prepare_solver_bodies(
            state.admission(),
            &artifacts,
            vec![exposed_source],
            &CancellationToken::new(),
        )
        .await
        .unwrap()
        .remove(0);
    assert_eq!(warmed.body_id(), exposed_body_id);

    drop(state);
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}

// ------------------------------------------------------------
// Coverage Direction, Closure, And Track Construction
// ------------------------------------------------------------

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn fallback_closure_lifts_init_in_same_direction_and_keeps_cross_track_edges() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("maintenance_coverage");
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_state(&task, &artifacts, &context);
    let ids = install_proved_proposal(&mut state, formulas(&task)).await;
    let ids = ordered(&ids);

    state.insert_init_coverage(ids[0], ids[1]).unwrap();
    state.close_init_coverage().unwrap();
    state.insert_maint_coverage(ids[1], ids[2]).unwrap();
    state
        .set_track_hint(
            ids[2],
            MaintenanceTrackHint::new(MaintenanceTrackKind::WLayer, Some(7)),
        )
        .unwrap();
    state
        .set_maintenance_policy(MaintenancePolicy::new(
            CoverageMode::ComputeClosure,
            TrackLayout::OrdinaryAndWTracks,
            CoverageLookup::IncomingEdges,
        ))
        .unwrap();

    let result = prepare_maintenance(&task, &mut state, &CancellationToken::new()).await;
    assert!(matches!(result, MaintenancePreparationOutcome::Complete));
    assert!(
        state.maintenance_failure().is_none(),
        "{:?}",
        state.maintenance_failure()
    );
    let plan = state.current_maintenance_plan(&task).unwrap();
    assert_eq!(plan.covered_by(ids[1]), &[ids[0]]);
    assert_eq!(plan.covered_by(ids[2]), &[ids[0], ids[1]]);
    assert_eq!(plan.covered_count(ids[0]), 2);
    assert_eq!(plan.covered_count(ids[1]), 1);
    assert_eq!(plan.covered_count(ids[2]), 0);
    assert!(!plan.covered_by(ids[0]).contains(&ids[0]));

    let tracks = plan.schedule().tracks();
    assert_eq!(tracks.len(), 2);
    assert_eq!(tracks[0].kind(), MaintenanceTrackKind::Ordinary);
    assert_eq!(tracks[0].targets(), &[ids[0], ids[1]]);
    assert_eq!(tracks[1].kind(), MaintenanceTrackKind::WLayer);
    assert_eq!(tracks[1].targets(), &[ids[2]]);
    assert!(plan.covered_by(ids[2]).contains(&ids[0]));

    let metrics = plan.closure_metrics().expect("fallback metrics");
    assert_eq!(metrics.input_edge_count(), 2);
    assert_eq!(metrics.retained_edge_count(), 3);
    assert!(metrics.estimated_retained_bytes() > 0);

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn closure_precedes_filtering_and_preserves_cycle_self_reachability() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("maintenance_close_before_filter");
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let catalog = ClauseCatalog::new(&task, context.clone(), &artifacts).unwrap();
    let clauses = formulas(&task);
    let ids = clauses
        .into_iter()
        .map(|formula| catalog.register_proposed_clause(formula).unwrap())
        .collect::<Vec<_>>();
    let mut init = whiel_runner::InitCoverage::new(&catalog);
    init.insert(&catalog, ids[0], ids[1]).unwrap();
    close_init_coverage(&mut init);
    let mut coverage = whiel_runner::MaintCoverage::new(&catalog, ClauseSet::new()).unwrap();
    coverage.insert(&catalog, ids[1], ids[2]).unwrap();
    let eligible = ClauseSet::from([ids[0], ids[2]]);
    let (closed, metrics) =
        close_maint_coverage(&catalog, &ClauseSet::new(), &eligible, &init, &coverage).unwrap();
    assert!(closed.contains(ids[0], ids[2]));
    assert!(!closed.contains(ids[0], ids[1]));
    assert!(!closed.contains(ids[1], ids[2]));
    assert_eq!(metrics.retained_edge_count(), 1);

    let mut cycle = whiel_runner::MaintCoverage::new(&catalog, ClauseSet::new()).unwrap();
    cycle.insert(&catalog, ids[0], ids[1]).unwrap();
    cycle.insert(&catalog, ids[1], ids[0]).unwrap();
    let both = ClauseSet::from([ids[0], ids[1]]);
    let (closed_cycle, _) =
        close_maint_coverage(&catalog, &ClauseSet::new(), &both, &init, &cycle).unwrap();
    assert!(closed_cycle.contains(ids[0], ids[0]));
    assert!(closed_cycle.contains(ids[1], ids[1]));

    context.shutdown().await.unwrap();
    drop(catalog);
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}

// ------------------------------------------------------------
// Staleness, Rejection, And Cancellation
// ------------------------------------------------------------

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn same_set_new_proposal_invalidates_the_old_plan() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("maintenance_generation");
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_state(&task, &artifacts, &context);
    install_proved_proposal(&mut state, formulas(&task)).await;
    let result = prepare_maintenance(&task, &mut state, &CancellationToken::new()).await;
    assert!(matches!(result, MaintenancePreparationOutcome::Complete));
    assert!(
        state.maintenance_failure().is_none(),
        "{:?}",
        state.maintenance_failure()
    );
    let first_generation = state.proposal_generation();
    let old_plan = state.current_maintenance_plan(&task).unwrap();
    assert!(old_plan.is_current_for(&task, &state));

    let outcome = state
        .prepare_init_candidates(
            formulas(&task),
            &ClauseSet::new(),
            &CancellationToken::new(),
        )
        .await;
    assert!(matches!(
        outcome,
        whiel_runner::InitializationInvocationOutcome::Complete
    ));
    assert_eq!(state.proposal_generation(), first_generation + 1);
    assert!(state.active().is_empty());
    assert!(state.maintenance_plan().is_none());
    assert!(!old_plan.is_current_for(&task, &state));

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn unclassified_or_cancelled_preparation_never_publishes_active() {
    let task = support::export_canonical_task();

    let first_directory = support::TestDir::new("maintenance_unclassified");
    let (first_owner, first_artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(first_directory.path())).unwrap();
    let first_context =
        new_solver_encoding_context(&task, &first_artifacts, worker_config()).unwrap();
    let mut first_state = new_state(&task, &first_artifacts, &first_context);
    let outcome = first_state
        .prepare_init_candidates(
            vec![formulas(&task).remove(0)],
            &ClauseSet::new(),
            &CancellationToken::new(),
        )
        .await;
    assert!(matches!(
        outcome,
        whiel_runner::InitializationInvocationOutcome::Complete
    ));
    let result = prepare_maintenance(&task, &mut first_state, &CancellationToken::new()).await;
    assert!(matches!(result, MaintenancePreparationOutcome::Complete));
    assert!(first_state.active().is_empty());
    assert!(first_state.maintenance_plan().is_none());
    assert_eq!(
        first_state.maintenance_failure().unwrap().kind(),
        FailureKind::StateInvariantViolation
    );
    shutdown(first_state, first_context, first_artifacts, first_owner).await;

    let second_directory = support::TestDir::new("maintenance_cancelled");
    let (second_owner, second_artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(second_directory.path())).unwrap();
    let second_context =
        new_solver_encoding_context(&task, &second_artifacts, worker_config()).unwrap();
    let mut second_state = new_state(&task, &second_artifacts, &second_context);
    let ids = install_proved_proposal(&mut second_state, vec![formulas(&task).remove(0)]).await;
    let cancellation = CancellationToken::new();
    cancellation.cancel();
    let result = prepare_maintenance(&task, &mut second_state, &cancellation).await;
    assert!(matches!(result, MaintenancePreparationOutcome::Cancelled));
    assert!(second_state.active().is_empty());
    assert!(second_state.maintenance_plan().is_none());
    assert!(second_state.maintenance_failure().is_none());
    let id = *ids.iter().next().unwrap();
    assert!(
        second_state
            .catalog()
            .record(id)
            .unwrap()
            .maintenance_wp_body()
            .is_none()
    );
    shutdown(second_state, second_context, second_artifacts, second_owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn shared_task_identity_mismatch_is_run_global() {
    let task = support::export_canonical_task();
    let mut foreign_json: serde_json::Value =
        serde_json::from_str(support::export_canonical_task_json()).unwrap();
    foreign_json["identity"]["canonical_id"] = "ForeignExample0012".into();
    let foreign_task =
        whiel_runner::SynthesisTask::from_json(&serde_json::to_string(&foreign_json).unwrap())
            .unwrap();
    let directory = support::TestDir::new("maintenance_foreign_task");
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_state(&task, &artifacts, &context);

    let result = prepare_maintenance(&foreign_task, &mut state, &CancellationToken::new()).await;
    let MaintenancePreparationOutcome::RunFailure(report) = result else {
        panic!("a shared task-identity mismatch must stop the run")
    };
    assert_eq!(report.scope(), FailureScope::RunGlobal);
    assert_eq!(
        state.maintenance_failure().map(|failure| failure.scope()),
        Some(FailureScope::RunGlobal)
    );

    shutdown(state, context, artifacts, owner).await;
}

#[test]
fn raw_sources_cannot_impersonate_worker_derived_wps() {
    let task = support::sample_task();
    let error = QfSolverSource::new(
        &task,
        "__whiel_maintenance_wp__:raw",
        Vec::<ConstantKey>::new(),
        Vec::new(),
    )
    .unwrap_err();
    assert!(error.contains("reserved derived-source namespace"));
}
