mod support;

use std::ffi::OsString;
use std::path::Path;
use std::time::Duration;

use whiel_runner::encoding::{
    EncodingWorkerCommand, EncodingWorkerPoolConfig, QfSolverSource, SolverBodySource,
    SolverEncodingContext, new_solver_encoding_context,
};
use whiel_runner::{
    ArtifactKind, ArtifactStore, ArtifactStoreConfig, CancellationToken, ClauseCatalog,
    ClauseFormula, ClauseSet, ConstantKey, HoudiniState, InitializationInvocationOutcome,
    InitializationStatus, RuntimeResourcePolicy, SolverAdmission, TelemetryConfig, TelemetryLevel,
    TelemetrySession, VampireWorkerCommand, VerificationParameters, check_initialization,
    create_general_solver_admission, new_artifact_store, prepare_maintenance,
};

// ------------------------------------------------------------
// Shared Phase 3A Fixtures
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

fn vampire_command(fixture: &str, launch_log: Option<&Path>) -> VampireWorkerCommand {
    let mut arguments = vec![
        OsString::from("--fixture"),
        OsString::from(fixture),
        OsString::from("--expect-start"),
        OsString::from("1"),
    ];
    if let Some(path) = launch_log {
        arguments.push(OsString::from("--launch-log"));
        arguments.push(path.as_os_str().to_owned());
    }
    VampireWorkerCommand::new(support::fake_vampire())
        .with_extra_args(arguments)
        .unwrap()
}

fn new_state(
    task: &whiel_runner::SynthesisTask,
    artifacts: &ArtifactStore,
    context: &SolverEncodingContext,
    policy: RuntimeResourcePolicy,
    bulk_init_limit: Duration,
    search_limit: Duration,
) -> HoudiniState {
    let verification = VerificationParameters::new(search_limit, policy)
        .unwrap()
        .with_bulk_init_limit(bulk_init_limit);
    let admission = admission(policy);
    let catalog = ClauseCatalog::new(task, context.clone(), artifacts).unwrap();
    HoudiniState::new(task, verification, admission, catalog).unwrap()
}

async fn install_proposal(state: &mut HoudiniState, clauses: Vec<ClauseFormula>) -> ClauseSet {
    let outcome = state
        .prepare_init_candidates(clauses, &ClauseSet::new(), &CancellationToken::new())
        .await;
    assert!(matches!(outcome, InitializationInvocationOutcome::Complete));
    state.init_candidates().clone()
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

// ------------------------------------------------------------
// Bulk And Persistent Initialization
// ------------------------------------------------------------

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn bulk_proof_classifies_once_and_persists_without_relaunch() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("initialization_bulk_proof");
    let launch_log = directory.path().join("launches");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_state(
        &task,
        &artifacts,
        &context,
        runtime_policy(),
        Duration::from_secs(30),
        Duration::from_secs(30),
    );
    let first_clause = formula(
        &task,
        "QFAssertExpr.true.bulk",
        "task.phase2c_qf_fixture",
        &[],
    );
    let second_clause = formula(
        &task,
        "QFAssertExpr.catalog.bulk",
        "catalog.clause.0",
        &["rel:E:0", "rel:TBound:0"],
    );
    let ids = install_proposal(
        &mut state,
        vec![first_clause.clone(), second_clause.clone()],
    )
    .await;
    assert_eq!(ids.len(), 2);

    let first = check_initialization(
        &task,
        &mut state,
        vampire_command("race-proof-fast", Some(&launch_log)),
        &CancellationToken::new(),
    )
    .await;
    assert!(matches!(first, InitializationInvocationOutcome::Complete));
    assert!(state.bulk_init_proved());
    assert!(state.active().is_empty());
    let mut evidence = None;
    for id in &ids {
        let record = state.catalog().record(*id).unwrap();
        assert_eq!(record.initialization(), InitializationStatus::InitProved);
        let current = record.initialization_evidence().unwrap();
        assert_eq!(current.kind(), ArtifactKind::InitializationCheck);
        assert!(evidence.is_none_or(|known| known == current));
        evidence = Some(current);
    }
    assert_eq!(state.catalog().select_init_proved(&ids).unwrap(), ids);
    let launches_after_first = std::fs::read_to_string(&launch_log)
        .unwrap()
        .lines()
        .count();
    assert_eq!(launches_after_first, 2);

    install_proposal(&mut state, vec![first_clause, second_clause]).await;
    let second = check_initialization(
        &task,
        &mut state,
        vampire_command("unknown", Some(&launch_log)),
        &CancellationToken::new(),
    )
    .await;
    assert!(matches!(second, InitializationInvocationOutcome::Complete));
    assert_eq!(
        std::fs::read_to_string(&launch_log)
            .unwrap()
            .lines()
            .count(),
        launches_after_first
    );
    for id in &ids {
        assert_eq!(
            state
                .catalog()
                .record(*id)
                .unwrap()
                .initialization_evidence(),
            evidence
        );
    }

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn bulk_refutation_falls_back_to_per_clause_classification() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("initialization_bulk_fallback");
    let launch_log = directory.path().join("launches");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_state(
        &task,
        &artifacts,
        &context,
        runtime_policy(),
        Duration::from_secs(3),
        Duration::from_secs(3),
    );
    let telemetry = TelemetrySession::start(TelemetryConfig::new(
        directory.path().join("telemetry"),
        TelemetryLevel::Aggregate,
    ));
    state.attach_telemetry(telemetry.handle());
    let ids = install_proposal(
        &mut state,
        vec![formula(
            &task,
            "QFAssertExpr.bulk.refuted",
            "catalog.clause.0",
            &["rel:E:0", "rel:TBound:0"],
        )],
    )
    .await;
    let id = *ids.iter().next().unwrap();

    let outcome = check_initialization(
        &task,
        &mut state,
        // Both workers finish immediately. FMB remains the only conclusive lane,
        // without making this fallback test depend on a delayed child process.
        vampire_command("race-proof-failure-model", Some(&launch_log)),
        &CancellationToken::new(),
    )
    .await;
    assert!(matches!(outcome, InitializationInvocationOutcome::Complete));
    assert!(!state.bulk_init_proved());
    assert_eq!(
        state.catalog().record(id).unwrap().initialization(),
        InitializationStatus::InitRefuted
    );
    assert_eq!(
        std::fs::read_to_string(&launch_log)
            .unwrap()
            .lines()
            .count(),
        4
    );
    assert!(state.active().is_empty());
    let report = telemetry.finish();
    assert_eq!(
        report
            .snapshot
            .counters
            .get("houdini.initialization.proof_and_fmb_requests"),
        Some(&2)
    );
    assert_eq!(
        report
            .snapshot
            .dispositions
            .get("initialization_bulk_query_refuted"),
        Some(&1)
    );
    assert_eq!(
        report
            .snapshot
            .dispositions
            .get("initialization_clause_query_refuted"),
        Some(&1)
    );
    shutdown(state, context, artifacts, owner).await;
}

// ------------------------------------------------------------
// Per-Clause Outcomes And Coverage
// ------------------------------------------------------------

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn per_clause_timeout_is_inconclusive_and_remains_retry_eligible() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("initialization_timeout");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_state(
        &task,
        &artifacts,
        &context,
        runtime_policy(),
        Duration::ZERO,
        Duration::from_millis(100),
    );
    let telemetry = TelemetrySession::start(TelemetryConfig::new(
        directory.path().join("telemetry"),
        TelemetryLevel::Aggregate,
    ));
    state.attach_telemetry(telemetry.handle());
    let ids = install_proposal(
        &mut state,
        vec![formula(
            &task,
            "QFAssertExpr.timeout",
            "catalog.clause.0",
            &["rel:E:0", "rel:TBound:0"],
        )],
    )
    .await;
    let id = *ids.iter().next().unwrap();

    let outcome = check_initialization(
        &task,
        &mut state,
        vampire_command("race-timeout", None),
        &CancellationToken::new(),
    )
    .await;
    assert!(matches!(outcome, InitializationInvocationOutcome::Complete));
    let record = state.catalog().record(id).unwrap();
    assert_eq!(
        record.initialization(),
        InitializationStatus::InitInconclusive
    );
    assert!(record.initialization_evidence().is_some());
    let evidence = artifacts
        .resolve(record.initialization_evidence().unwrap())
        .unwrap();
    assert!(
        std::fs::read_to_string(evidence.path())
            .unwrap()
            .contains("\"outcome\":\"timed_out\"")
    );
    assert_eq!(
        state.catalog().select_initialization_work(&ids).unwrap(),
        ids
    );
    assert!(state.active().is_empty());
    let report = telemetry.finish();
    assert_eq!(
        report
            .snapshot
            .counters
            .get("houdini.initialization.proof_and_fmb_requests"),
        Some(&1)
    );
    assert_eq!(
        report
            .snapshot
            .dispositions
            .get("initialization_clause_query_timed_out"),
        Some(&1)
    );

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn per_clause_solver_failure_is_inconclusive_but_not_a_timeout() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("initialization_failure");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_state(
        &task,
        &artifacts,
        &context,
        runtime_policy(),
        Duration::ZERO,
        Duration::from_secs(3),
    );
    let telemetry = TelemetrySession::start(TelemetryConfig::new(
        directory.path().join("telemetry"),
        TelemetryLevel::Aggregate,
    ));
    state.attach_telemetry(telemetry.handle());
    let ids = install_proposal(
        &mut state,
        vec![formula(
            &task,
            "QFAssertExpr.failure",
            "catalog.clause.0",
            &["rel:E:0", "rel:TBound:0"],
        )],
    )
    .await;
    let id = *ids.iter().next().unwrap();

    let outcome = check_initialization(
        &task,
        &mut state,
        vampire_command("race-dual-failure", None),
        &CancellationToken::new(),
    )
    .await;
    assert!(matches!(outcome, InitializationInvocationOutcome::Complete));
    let record = state.catalog().record(id).unwrap();
    assert_eq!(
        record.initialization(),
        InitializationStatus::InitInconclusive
    );
    let evidence = artifacts
        .resolve(record.initialization_evidence().unwrap())
        .unwrap();
    let payload = std::fs::read_to_string(evidence.path()).unwrap();
    assert!(payload.contains("\"outcome\":\"failure\""));
    assert!(!payload.contains("\"outcome\":\"timed_out\""));
    let report = telemetry.finish();
    assert_eq!(
        report
            .snapshot
            .counters
            .get("houdini.initialization.proof_and_fmb_requests"),
        Some(&1)
    );
    assert_eq!(
        report
            .snapshot
            .dispositions
            .get("initialization_clause_query_failure"),
        Some(&1)
    );

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn closed_coverage_uses_a_persistent_proved_seed_without_vampire() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("initialization_coverage");
    let launch_log = directory.path().join("launches");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_state(
        &task,
        &artifacts,
        &context,
        runtime_policy(),
        Duration::from_secs(3),
        Duration::from_secs(3),
    );
    let telemetry = TelemetrySession::start(TelemetryConfig::new(
        directory.path().join("telemetry"),
        TelemetryLevel::Aggregate,
    ));
    state.attach_telemetry(telemetry.handle());
    let seed_formula = formula(
        &task,
        "QFAssertExpr.coverage.seed",
        "task.phase2c_qf_fixture",
        &[],
    );
    let seed_ids = install_proposal(&mut state, vec![seed_formula]).await;
    let seed = *seed_ids.iter().next().unwrap();
    let seed_outcome = check_initialization(
        &task,
        &mut state,
        vampire_command("race-proof-fast", Some(&launch_log)),
        &CancellationToken::new(),
    )
    .await;
    assert!(matches!(
        seed_outcome,
        InitializationInvocationOutcome::Complete
    ));
    assert_eq!(
        state.catalog().record(seed).unwrap().initialization(),
        InitializationStatus::InitProved
    );
    let launches = std::fs::read_to_string(&launch_log)
        .unwrap()
        .lines()
        .count();

    let target_ids = install_proposal(
        &mut state,
        vec![formula(
            &task,
            "QFAssertExpr.coverage.target",
            "symbolic.w.0",
            &["rel:E:0", "rel:T:0", "rel:T:1", "rel:TBound:0"],
        )],
    )
    .await;
    let target = *target_ids.iter().next().unwrap();
    state.insert_init_coverage(seed, target).unwrap();
    state.close_init_coverage().unwrap();

    let target_outcome = check_initialization(
        &task,
        &mut state,
        vampire_command("unknown", Some(&launch_log)),
        &CancellationToken::new(),
    )
    .await;
    assert!(matches!(
        target_outcome,
        InitializationInvocationOutcome::Complete
    ));
    let target_record = state.catalog().record(target).unwrap();
    assert_eq!(
        target_record.initialization(),
        InitializationStatus::InitProved
    );
    assert!(state.bulk_init_proved());
    assert_eq!(
        std::fs::read_to_string(&launch_log)
            .unwrap()
            .lines()
            .count(),
        launches
    );
    assert!(state.active().is_empty());
    let report = telemetry.finish();
    assert_eq!(
        report
            .snapshot
            .counters
            .get("houdini.initialization.proof_and_fmb_requests"),
        Some(&1)
    );
    assert_eq!(
        report
            .snapshot
            .counters
            .get("houdini.initialization.coverage_shortcuts"),
        Some(&1)
    );
    assert_eq!(
        report
            .snapshot
            .dispositions
            .get("initialization_bulk_query_proved"),
        Some(&1)
    );
    assert_eq!(
        report
            .snapshot
            .dispositions
            .get("initialization_coverage_shortcut"),
        Some(&1)
    );
    assert!(
        report
            .snapshot
            .duration_nanoseconds
            .get("houdini.initialization.query_inclusive")
            .is_some_and(|duration| *duration > 0)
    );

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_new_individual_proof_covers_later_work_through_a_dormant_intermediate() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("initialization_online_coverage");
    let launch_log = directory.path().join("launches");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_state(
        &task,
        &artifacts,
        &context,
        runtime_policy(),
        Duration::ZERO,
        // This test checks online coverage, not timeout behavior. Leave enough
        // headroom for Lean/Vampire process startup on a loaded test host.
        Duration::from_secs(30),
    );

    let dormant = *install_proposal(
        &mut state,
        vec![formula(
            &task,
            "QFAssertExpr.coverage.dormant",
            "symbolic.w.0",
            &["rel:E:0", "rel:T:0", "rel:T:1", "rel:TBound:0"],
        )],
    )
    .await
    .iter()
    .next()
    .unwrap();
    let current = install_proposal(
        &mut state,
        vec![
            formula(
                &task,
                "QFAssertExpr.coverage.new.seed",
                "task.phase2c_qf_fixture",
                &[],
            ),
            formula(
                &task,
                "QFAssertExpr.coverage.transitive.target",
                "symbolic.w.1",
                &["rel:E:0", "rel:T:0", "rel:T:1", "rel:TBound:0"],
            ),
        ],
    )
    .await;
    let mut ordered = current.iter().copied().collect::<Vec<_>>();
    ordered.sort_unstable();
    let [seed, target] = ordered.as_slice() else {
        panic!("two current initialization candidates")
    };
    state.insert_init_coverage(*seed, dormant).unwrap();
    state.insert_init_coverage(dormant, *target).unwrap();
    state.close_init_coverage().unwrap();

    let outcome = check_initialization(
        &task,
        &mut state,
        vampire_command("race-proof-fast", Some(&launch_log)),
        &CancellationToken::new(),
    )
    .await;
    assert!(matches!(outcome, InitializationInvocationOutcome::Complete));
    assert_eq!(
        state.catalog().record(*seed).unwrap().initialization(),
        InitializationStatus::InitProved
    );
    assert_eq!(
        state.catalog().record(*target).unwrap().initialization(),
        InitializationStatus::InitProved
    );
    assert_eq!(
        state.catalog().record(dormant).unwrap().initialization(),
        InitializationStatus::Unclassified
    );
    assert_ne!(
        state
            .catalog()
            .record(*seed)
            .unwrap()
            .initialization_evidence(),
        state
            .catalog()
            .record(*target)
            .unwrap()
            .initialization_evidence()
    );
    assert_eq!(
        std::fs::read_to_string(&launch_log)
            .unwrap()
            .lines()
            .count(),
        2
    );
    assert!(!state.bulk_init_proved());

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_coverage_cycle_without_a_proved_seed_does_not_bootstrap() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("initialization_coverage_cycle");
    let launch_log = directory.path().join("launches");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_state(
        &task,
        &artifacts,
        &context,
        runtime_policy(),
        Duration::ZERO,
        Duration::from_secs(10),
    );
    let ids = install_proposal(
        &mut state,
        vec![
            formula(
                &task,
                "QFAssertExpr.coverage.cycle.a",
                "symbolic.w.0",
                &["rel:E:0", "rel:T:0", "rel:T:1", "rel:TBound:0"],
            ),
            formula(
                &task,
                "QFAssertExpr.coverage.cycle.b",
                "symbolic.w.1",
                &["rel:E:0", "rel:T:0", "rel:T:1", "rel:TBound:0"],
            ),
        ],
    )
    .await;
    let mut ordered = ids.iter().copied().collect::<Vec<_>>();
    ordered.sort_unstable();
    state.insert_init_coverage(ordered[0], ordered[1]).unwrap();
    state.insert_init_coverage(ordered[1], ordered[0]).unwrap();
    state.close_init_coverage().unwrap();

    let outcome = check_initialization(
        &task,
        &mut state,
        vampire_command("race-model-win", Some(&launch_log)),
        &CancellationToken::new(),
    )
    .await;
    assert!(matches!(outcome, InitializationInvocationOutcome::Complete));
    for id in ordered {
        assert_eq!(
            state.catalog().record(id).unwrap().initialization(),
            InitializationStatus::InitRefuted
        );
    }
    assert_eq!(
        std::fs::read_to_string(&launch_log)
            .unwrap()
            .lines()
            .count(),
        4
    );

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn nonclosed_coverage_fails_before_solver_launch() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("initialization_nonclosed_coverage");
    let launch_log = directory.path().join("launches");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_state(
        &task,
        &artifacts,
        &context,
        runtime_policy(),
        Duration::from_secs(3),
        Duration::from_secs(3),
    );
    let ids = install_proposal(
        &mut state,
        vec![
            formula(
                &task,
                "QFAssertExpr.nonclosed.a",
                "symbolic.w.0",
                &["rel:E:0", "rel:T:0", "rel:T:1", "rel:TBound:0"],
            ),
            formula(
                &task,
                "QFAssertExpr.nonclosed.b",
                "symbolic.w.1",
                &["rel:E:0", "rel:T:0", "rel:T:1", "rel:TBound:0"],
            ),
        ],
    )
    .await;
    let mut ordered = ids.iter().copied().collect::<Vec<_>>();
    ordered.sort_unstable();
    state.insert_init_coverage(ordered[0], ordered[1]).unwrap();

    let outcome = check_initialization(
        &task,
        &mut state,
        vampire_command("race-proof-fast", Some(&launch_log)),
        &CancellationToken::new(),
    )
    .await;
    assert!(matches!(outcome, InitializationInvocationOutcome::Complete));
    assert_eq!(
        state.maintenance_failure().unwrap().kind(),
        whiel_runner::FailureKind::StateInvariantViolation
    );
    assert!(!launch_log.exists());
    for id in ids {
        assert_eq!(
            state.catalog().record(id).unwrap().initialization(),
            InitializationStatus::Unclassified
        );
    }

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn explicit_drop_is_operational_metadata_not_a_classification() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("initialization_explicit_drop");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_state(
        &task,
        &artifacts,
        &context,
        runtime_policy(),
        Duration::ZERO,
        Duration::from_secs(3),
    );
    let clause = formula(
        &task,
        "QFAssertExpr.explicit.drop",
        "catalog.clause.0",
        &["rel:E:0", "rel:TBound:0"],
    );
    let ids = install_proposal(&mut state, vec![clause.clone()]).await;
    let id = *ids.iter().next().unwrap();

    let initialized = check_initialization(
        &task,
        &mut state,
        vampire_command("race-proof-fast", None),
        &CancellationToken::new(),
    )
    .await;
    assert!(matches!(
        initialized,
        InitializationInvocationOutcome::Complete
    ));
    let original_evidence = state
        .catalog()
        .record(id)
        .unwrap()
        .initialization_evidence()
        .unwrap();

    let outcome = state
        .prepare_init_candidates(
            // Validated agent responses forbid this overlap. Keep the lower
            // boundary fail-safe: if one arrives, the explicit drop wins and
            // the clause is not exposed as initialization work.
            vec![clause.clone()],
            &ClauseSet::from([id]),
            &CancellationToken::new(),
        )
        .await;
    assert!(matches!(outcome, InitializationInvocationOutcome::Complete));
    assert!(state.init_candidates().is_empty());
    let record = state.catalog().record(id).unwrap();
    assert!(record.explicitly_dropped());
    assert_eq!(record.initialization(), InitializationStatus::InitProved);
    assert_eq!(record.initialization_evidence(), Some(original_evidence));

    let reintroduced = state
        .prepare_init_candidates(vec![clause], &ClauseSet::new(), &CancellationToken::new())
        .await;
    assert!(matches!(
        reintroduced,
        InitializationInvocationOutcome::Complete
    ));
    assert_eq!(state.init_candidates(), &ClauseSet::from([id]));
    let record = state.catalog().record(id).unwrap();
    assert!(record.explicitly_dropped());
    assert_eq!(record.initialization(), InitializationStatus::InitProved);
    assert_eq!(record.initialization_evidence(), Some(original_evidence));

    let maintenance = prepare_maintenance(&task, &mut state, &CancellationToken::new()).await;
    assert!(matches!(
        maintenance,
        whiel_runner::MaintenancePreparationOutcome::Complete
    ));
    assert_eq!(state.active(), &ClauseSet::from([id]));
    assert!(state.maintenance_failure().is_none());

    shutdown(state, context, artifacts, owner).await;
}

// ------------------------------------------------------------
// Cancellation Boundary
// ------------------------------------------------------------

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn cancellation_retains_completed_per_clause_progress_only() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("initialization_partial_cancel");
    let launch_log = directory.path().join("launches");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_state(
        &task,
        &artifacts,
        &context,
        runtime_policy(),
        Duration::ZERO,
        Duration::from_secs(10),
    );
    let ids = install_proposal(
        &mut state,
        vec![
            formula(
                &task,
                "QFAssertExpr.partial.cancel.first",
                "catalog.clause.0",
                &["rel:E:0", "rel:TBound:0"],
            ),
            formula(
                &task,
                "QFAssertExpr.partial.cancel.second",
                "symbolic.w.0",
                &["rel:E:0", "rel:T:0", "rel:T:1", "rel:TBound:0"],
            ),
        ],
    )
    .await;
    let mut ordered = ids.iter().copied().collect::<Vec<_>>();
    ordered.sort_unstable();
    let cancellation = CancellationToken::new();
    let check_launch_log = launch_log.clone();
    let check = tokio::spawn({
        let task = task.clone();
        let cancellation = cancellation.clone();
        async move {
            let outcome = check_initialization(
                &task,
                &mut state,
                vampire_command("race-first-pair-proof-then-hang", Some(&check_launch_log)),
                &cancellation,
            )
            .await;
            (outcome, state)
        }
    });
    tokio::time::timeout(Duration::from_secs(15), async {
        loop {
            let launched = std::fs::read_to_string(&launch_log)
                .map(|text| text.lines().count())
                .unwrap_or(0);
            if launched == 4 {
                break;
            }
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    })
    .await
    .expect("second initialization Vampire pair did not launch");
    cancellation.cancel();

    let (outcome, state) = check.await.unwrap();
    assert!(matches!(
        outcome,
        InitializationInvocationOutcome::Cancelled
    ));
    assert_eq!(
        state.catalog().record(ordered[0]).unwrap().initialization(),
        InitializationStatus::InitProved
    );
    assert_eq!(
        state.catalog().record(ordered[1]).unwrap().initialization(),
        InitializationStatus::Unclassified
    );
    assert!(state.active().is_empty());

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn cancellation_stops_the_check_without_publishing_a_classification() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("initialization_cancel");
    let launch_log = directory.path().join("launches");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_state(
        &task,
        &artifacts,
        &context,
        runtime_policy(),
        Duration::ZERO,
        Duration::from_secs(10),
    );
    let ids = install_proposal(
        &mut state,
        vec![formula(
            &task,
            "QFAssertExpr.cancel",
            "catalog.clause.0",
            &["rel:E:0", "rel:TBound:0"],
        )],
    )
    .await;
    let id = *ids.iter().next().unwrap();
    let cancellation = CancellationToken::new();
    let check_launch_log = launch_log.clone();
    let check = tokio::spawn({
        let task = task.clone();
        let cancellation = cancellation.clone();
        async move {
            let outcome = check_initialization(
                &task,
                &mut state,
                vampire_command("race-timeout", Some(&check_launch_log)),
                &cancellation,
            )
            .await;
            (outcome, state)
        }
    });
    tokio::time::timeout(Duration::from_secs(5), async {
        loop {
            let launched = std::fs::read_to_string(&launch_log)
                .map(|text| text.lines().count())
                .unwrap_or(0);
            if launched == 2 {
                break;
            }
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    })
    .await
    .expect("initialization Vampire pair did not launch");
    cancellation.cancel();

    let (outcome, state) = check.await.unwrap();
    assert!(matches!(
        outcome,
        InitializationInvocationOutcome::Cancelled
    ));
    assert_eq!(
        state.catalog().record(id).unwrap().initialization(),
        InitializationStatus::Unclassified
    );
    assert!(state.active().is_empty());

    shutdown(state, context, artifacts, owner).await;
}
