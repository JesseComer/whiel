mod support;

use std::ffi::OsString;
use std::fs;
use std::path::Path;
use std::sync::Arc;
use std::time::Duration;

use whiel_runner::encoding::{
    EncodingWorkerCommand, EncodingWorkerPoolConfig, QfSolverSource, SolverBodySource,
    SolverEncodingContext, new_solver_encoding_context,
};
use whiel_runner::{
    ArtifactKind, ArtifactStore, ArtifactStoreConfig, CancellationToken, ClauseCatalog,
    ClauseFormula, ClauseId, ClauseSet, ConstantKey, FailureKind, FailureOrigin,
    HoudiniExecutionOutcome, HoudiniState, InitializationInvocationOutcome, InitializationStatus,
    MaintenanceBlockOutcome, MaintenanceExecutionOutcome, MaintenancePolicy,
    MaintenancePreparationOutcome, MaintenanceResultClass, MaintenanceResultDisposition,
    RuntimeResourcePolicy, SolverAdmission, VampireWorkerCommand, VerificationParameters,
    apply_maintenance_exclusion, create_general_solver_admission, expand_core, houdini,
    new_artifact_store, prepare_maintenance, run_maintenance_block_sequential,
    run_maintenance_blocks_sequential, settle_maintenance_history,
};

// ------------------------------------------------------------
// Shared Sequential-Oracle Fixtures
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

fn runtime_policy(slots: usize) -> RuntimeResourcePolicy {
    RuntimeResourcePolicy::agent_only(slots, 2).unwrap()
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

fn true_formula(task: &whiel_runner::SynthesisTask, canonical: &str) -> ClauseFormula {
    formula(task, canonical, "task.phase2c_qf_fixture", &[])
}

fn false_formula(task: &whiel_runner::SynthesisTask, canonical: &str) -> ClauseFormula {
    formula(task, canonical, "phase2d.false", &[])
}

fn catalog_formula(task: &whiel_runner::SynthesisTask, canonical: &str) -> ClauseFormula {
    formula(
        task,
        canonical,
        "catalog.clause.0",
        &["rel:E:0", "rel:TBound:0"],
    )
}

fn vampire_command(fixture: &str, launch_log: Option<&Path>) -> VampireWorkerCommand {
    vampire_command_at(fixture, 1, launch_log)
}

fn vampire_command_at(
    fixture: &str,
    expected_start: u64,
    launch_log: Option<&Path>,
) -> VampireWorkerCommand {
    let mut arguments = vec![
        OsString::from("--fixture"),
        OsString::from(fixture),
        OsString::from("--expect-start"),
        OsString::from(expected_start.to_string()),
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
    slots: usize,
    search_limit: Duration,
    retry_increments: Vec<Duration>,
) -> HoudiniState {
    let policy = runtime_policy(slots);
    let verification = VerificationParameters::new(search_limit, policy)
        .unwrap()
        .with_bulk_maint_limit(Duration::ZERO)
        .with_maintenance_retry_increments(retry_increments)
        .unwrap();
    let catalog = ClauseCatalog::new(task, context.clone(), artifacts).unwrap();
    HoudiniState::new(task, verification, admission(policy), catalog).unwrap()
}

fn new_bulk_state(
    task: &whiel_runner::SynthesisTask,
    artifacts: &ArtifactStore,
    context: &SolverEncodingContext,
    slots: usize,
    search_limit: Duration,
) -> HoudiniState {
    let policy = runtime_policy(slots);
    let verification = VerificationParameters::new(search_limit, policy).unwrap();
    let catalog = ClauseCatalog::new(task, context.clone(), artifacts).unwrap();
    HoudiniState::new(task, verification, admission(policy), catalog).unwrap()
}

async fn prepare_proved_active(
    task: &whiel_runner::SynthesisTask,
    state: &mut HoudiniState,
    proposal: Vec<ClauseFormula>,
) -> Vec<ClauseId> {
    let outcome = state
        .prepare_init_candidates(proposal, &ClauseSet::new(), &CancellationToken::new())
        .await;
    assert!(matches!(outcome, InitializationInvocationOutcome::Complete));
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
            .record_initialization(*id, InitializationStatus::InitProved, evidence)
            .unwrap();
    }
    let result = prepare_maintenance(task, state, &CancellationToken::new()).await;
    assert!(matches!(result, MaintenancePreparationOutcome::Complete));
    assert!(state.maintenance_failure().is_none());
    let mut ids = ids.into_iter().collect::<Vec<_>>();
    ids.sort_unstable();
    ids
}

/// Prepare one semantically self-supported fixture without launching Vampire.
///
/// The helper is reserved for state-transition and history tests. Its callers
/// use fixtures whose self-support fact is sound, then exercise the exact same
/// maintenance-plan and stable-result boundaries as a solver-backed block.
async fn prepare_self_supported_active(
    task: &whiel_runner::SynthesisTask,
    state: &mut HoudiniState,
    proposal: ClauseFormula,
) -> ClauseId {
    let outcome = state
        .prepare_init_candidates(vec![proposal], &ClauseSet::new(), &CancellationToken::new())
        .await;
    assert!(matches!(outcome, InitializationInvocationOutcome::Complete));
    let id = *state
        .init_candidates()
        .iter()
        .next()
        .expect("one registered fixture clause");
    let evidence = state
        .catalog()
        .artifacts()
        .publish(
            ArtifactKind::InitializationCheck,
            b"fixture InitProved".as_slice().into(),
        )
        .unwrap();
    state
        .catalog()
        .record_initialization(id, InitializationStatus::InitProved, evidence)
        .unwrap();
    state.insert_maint_support(id, id).unwrap();
    let result = prepare_maintenance(task, state, &CancellationToken::new()).await;
    assert!(matches!(result, MaintenancePreparationOutcome::Complete));
    assert_eq!(state.active(), &ClauseSet::from([id]));
    id
}

async fn reprepare(state: &mut HoudiniState, task: &whiel_runner::SynthesisTask) {
    let result = prepare_maintenance(task, state, &CancellationToken::new()).await;
    assert!(matches!(result, MaintenancePreparationOutcome::Complete));
    assert!(state.maintenance_failure().is_none());
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

fn launch_count(path: &Path) -> usize {
    fs::read_to_string(path).unwrap_or_default().lines().count()
}

fn find_file_containing(root: &Path, needle: &str) -> Option<std::path::PathBuf> {
    for entry in fs::read_dir(root).ok()? {
        let path = entry.ok()?.path();
        if path.is_dir() {
            if let Some(found) = find_file_containing(&path, needle) {
                return Some(found);
            }
        } else if fs::read_to_string(&path)
            .ok()
            .is_some_and(|text| text.contains(needle))
        {
            return Some(path);
        }
    }
    None
}

// ------------------------------------------------------------
// Stable Blocks, Support, And Coverage
// ------------------------------------------------------------

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn generic_houdini_consumes_exact_bulk_support_capability() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("phase3e_houdini_bulk_support");
    let launch_log = directory.path().join("launches");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_bulk_state(&task, &artifacts, &context, 2, Duration::from_secs(30));
    let id = prepare_self_supported_active(
        &task,
        &mut state,
        true_formula(&task, "phase3e.bulk.supported"),
    )
    .await;

    let outcome = houdini(
        &task,
        &mut state,
        vampire_command("race-proof-fast", Some(&launch_log)),
        &CancellationToken::new(),
    )
    .await;
    assert!(matches!(outcome, HoudiniExecutionOutcome::Complete));
    assert_eq!(state.core(), &ClauseSet::from([id]));
    assert!(state.active().is_empty());
    assert!(state.maintenance_plan().is_none());
    assert!(!state.bulk_maint_proved());
    assert_eq!(launch_count(&launch_log), 0);

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn generic_houdini_expands_only_after_durable_exact_bulk_proof() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("phase3e_houdini_bulk_proof");
    let launch_log = directory.path().join("launches");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_bulk_state(&task, &artifacts, &context, 2, Duration::from_secs(30));
    let ids = prepare_proved_active(
        &task,
        &mut state,
        vec![true_formula(&task, "phase3e.bulk.proved")],
    )
    .await;

    let outcome = houdini(
        &task,
        &mut state,
        // This test distinguishes bulk evidence from per-target evidence. Its
        // irrelevant FMB peer must finish independently; process-race cleanup
        // and hard-kill escalation have dedicated tests.
        vampire_command("race-fmb-failure-proof", Some(&launch_log)),
        &CancellationToken::new(),
    )
    .await;
    assert!(matches!(outcome, HoudiniExecutionOutcome::Complete));
    assert_eq!(state.core(), &ClauseSet::from([ids[0]]));
    assert!(state.active().is_empty());
    assert!(!state.bulk_maint_proved());
    assert!(launch_count(&launch_log) >= 1);
    assert!(state.artifacts().diagnostics().required_payloads_published >= 1);
    assert!(
        state
            .catalog()
            .record(ids[0])
            .unwrap()
            .latest_maintenance()
            .is_none(),
        "an exact bulk proof is not fabricated into per-target hot evidence"
    );

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn generic_houdini_falls_through_after_bulk_refutation_and_prunes() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("phase3e_houdini_bulk_refuted");
    let launch_log = directory.path().join("launches");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_bulk_state(&task, &artifacts, &context, 2, Duration::from_secs(30));
    let id = prepare_proved_active(
        &task,
        &mut state,
        vec![true_formula(&task, "phase3e.bulk.refuted")],
    )
    .await[0];

    let outcome = houdini(
        &task,
        &mut state,
        vampire_command("race-proof-failure-model", Some(&launch_log)),
        &CancellationToken::new(),
    )
    .await;
    assert!(matches!(outcome, HoudiniExecutionOutcome::Complete));
    assert!(state.core().is_empty());
    assert!(state.active().is_empty());
    assert!(state.maintenance_plan().is_none());
    assert!(!state.bulk_maint_proved());
    assert_eq!(
        launch_count(&launch_log),
        4,
        "bulk and per-clause pairs ran"
    );

    let record = state.catalog().record(id).unwrap();
    let latest = record
        .latest_maintenance()
        .expect("per-clause fallthrough retains compact hot feedback");
    assert_eq!(latest.class(), MaintenanceResultClass::Refuted);
    assert_eq!(latest.disposition(), MaintenanceResultDisposition::Applied);
    assert_eq!(latest.candidate_len(), 1);
    state
        .artifacts()
        .resolve(latest.evidence())
        .expect("hot feedback references durable evidence");

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn generic_houdini_bulk_cancellation_preserves_prepared_state() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("phase3e_houdini_bulk_cancel");
    let launch_log = directory.path().join("launches");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_bulk_state(&task, &artifacts, &context, 2, Duration::from_secs(30));
    let id = prepare_proved_active(
        &task,
        &mut state,
        vec![true_formula(&task, "phase3e.bulk.cancel")],
    )
    .await[0];
    let cancellation = CancellationToken::new();
    let task_copy = task.clone();
    let cancellation_copy = cancellation.clone();
    let launch_log_copy = launch_log.clone();
    let running = tokio::spawn(async move {
        let outcome = houdini(
            &task_copy,
            &mut state,
            vampire_command("race-timeout", Some(&launch_log_copy)),
            &cancellation_copy,
        )
        .await;
        (outcome, state)
    });
    tokio::time::timeout(Duration::from_secs(5), async {
        loop {
            if launch_count(&launch_log) == 2 {
                break;
            }
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    })
    .await
    .expect("bulk Vampire pair did not launch");
    cancellation.cancel();

    let (outcome, state) = running.await.unwrap();
    assert!(matches!(outcome, HoudiniExecutionOutcome::Cancelled));
    assert_eq!(state.active(), &ClauseSet::from([id]));
    assert!(state.maintenance_plan().is_some());
    assert!(state.maintenance_failure().is_none());
    assert!(!state.bulk_maint_proved());
    let record = state.catalog().record(id).unwrap();
    assert!(!record.has_retry_candidate());
    assert!(record.latest_maintenance().is_none());

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn generic_houdini_bulk_proof_runs_with_strict_serial_capacity() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("phase3e_houdini_bulk_capacity");
    let launch_log = directory.path().join("launches");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_bulk_state(&task, &artifacts, &context, 1, Duration::from_secs(30));
    let id = prepare_proved_active(
        &task,
        &mut state,
        vec![true_formula(&task, "phase3e.bulk.capacity")],
    )
    .await[0];

    let outcome = houdini(
        &task,
        &mut state,
        vampire_command("race-proof-fast", Some(&launch_log)),
        &CancellationToken::new(),
    )
    .await;
    assert!(matches!(outcome, HoudiniExecutionOutcome::Complete));
    assert_eq!(state.core(), &ClauseSet::from([id]));
    assert!(state.active().is_empty());
    assert!(state.maintenance_plan().is_none());
    assert!(state.maintenance_failure().is_none());
    assert!(!state.bulk_maint_proved());
    assert_eq!(launch_count(&launch_log), 1);

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn stable_results_expand_into_empty_and_nonempty_core_atomically() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("maintenance_execution_empty");
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
        2,
        Duration::from_secs(30),
        Vec::new(),
    );
    let first_id = prepare_self_supported_active(
        &task,
        &mut state,
        true_formula(&task, "maintenance.execution.true.0"),
    )
    .await;

    let result = run_maintenance_block_sequential(
        &task,
        &mut state,
        vampire_command("race-proof-fast", Some(&launch_log)),
        &CancellationToken::new(),
    )
    .await;
    let MaintenanceExecutionOutcome::Complete(block) = result else {
        panic!("expected a complete stable block: {result:#?}")
    };
    assert_eq!(block.generation().get(), 0);
    assert_eq!(block.outcome(), MaintenanceBlockOutcome::Stable);
    assert_eq!(block.entry_active(), &ClauseSet::from([first_id]));
    assert_eq!(block.candidate(), block.entry_active());
    assert_eq!(block.known_live(), block.entry_active());
    assert_eq!(launch_count(&launch_log), 0);
    assert_eq!(state.active(), block.entry_active());

    expand_core(&mut state, &block).unwrap();
    let first_core = ClauseSet::from([first_id]);
    assert_eq!(state.core(), &first_core);
    assert!(state.init_candidates().is_empty());
    assert!(state.active().is_empty());
    assert!(state.maintenance_plan().is_none());
    assert!(!state.bulk_init_proved());
    assert!(!state.bulk_maint_proved());
    assert_eq!(
        state.artifacts().diagnostics().history_records_constructed,
        0
    );

    let second_id = prepare_self_supported_active(
        &task,
        &mut state,
        false_formula(&task, "maintenance.execution.false.1"),
    )
    .await;
    let second = run_maintenance_block_sequential(
        &task,
        &mut state,
        vampire_command("race-proof-fast", Some(&launch_log)),
        &CancellationToken::new(),
    )
    .await;
    let MaintenanceExecutionOutcome::Complete(second) = second else {
        panic!("expected a complete second stable block: {second:#?}")
    };
    assert_eq!(second.generation().get(), 1);
    assert_eq!(second.outcome(), MaintenanceBlockOutcome::Stable);
    assert_eq!(second.entry_active(), &ClauseSet::from([second_id]));
    assert_eq!(second.candidate(), &ClauseSet::from([first_id, second_id]));
    assert_eq!(second.known_live(), second.entry_active());
    assert_eq!(launch_count(&launch_log), 0);

    expand_core(&mut state, &second).unwrap();
    assert_eq!(state.core(), &ClauseSet::from([first_id, second_id]));
    assert!(state.active().is_empty());

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn expand_core_requires_a_current_stable_result_and_preserves_rejected_state() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("maintenance_execution_expand_nonstable");
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
        2,
        Duration::from_secs(30),
        Vec::new(),
    );
    prepare_proved_active(
        &task,
        &mut state,
        vec![true_formula(
            &task,
            "maintenance.execution.expand.nonstable",
        )],
    )
    .await;
    let result = run_maintenance_block_sequential(
        &task,
        &mut state,
        vampire_command("race-model-win", None),
        &CancellationToken::new(),
    )
    .await;
    let MaintenanceExecutionOutcome::Complete(block) = result else {
        panic!("expected a complete refuted block: {result:#?}")
    };
    assert!(
        matches!(block.outcome(), MaintenanceBlockOutcome::Refuted(_)),
        "unexpected block outcome: {:?}",
        block.outcome()
    );

    let core = state.core().clone();
    let init_candidates = state.init_candidates().clone();
    let active = state.active().clone();
    let plan = Arc::clone(state.maintenance_plan().unwrap());
    let error = expand_core(&mut state, &block).unwrap_err();

    assert_eq!(error.origin(), FailureOrigin::MaintenanceExecution);
    assert_eq!(error.kind(), FailureKind::StateInvariantViolation);
    assert_eq!(state.core(), &core);
    assert_eq!(state.init_candidates(), &init_candidates);
    assert_eq!(state.active(), &active);
    assert!(Arc::ptr_eq(state.maintenance_plan().unwrap(), &plan));

    shutdown(state, context, artifacts, owner).await;

    // A stable result from a superseded maintenance publication is also
    // rejected without modifying the current Core, Active, or plan.
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("maintenance_execution_expand_stale");
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
        2,
        Duration::from_secs(30),
        Vec::new(),
    );
    prepare_proved_active(
        &task,
        &mut state,
        vec![true_formula(&task, "maintenance.execution.expand.stale.0")],
    )
    .await;
    let old = run_maintenance_block_sequential(
        &task,
        &mut state,
        vampire_command("race-proof-fast", None),
        &CancellationToken::new(),
    )
    .await;
    let MaintenanceExecutionOutcome::Complete(old) = old else {
        panic!("expected a complete stable block: {old:#?}")
    };
    assert_eq!(old.outcome(), MaintenanceBlockOutcome::Stable);

    prepare_proved_active(
        &task,
        &mut state,
        vec![false_formula(&task, "maintenance.execution.expand.stale.1")],
    )
    .await;
    let core = state.core().clone();
    let init_candidates = state.init_candidates().clone();
    let active = state.active().clone();
    let plan = Arc::clone(state.maintenance_plan().unwrap());
    let error = expand_core(&mut state, &old).unwrap_err();

    assert_eq!(error.origin(), FailureOrigin::MaintenanceExecution);
    assert_eq!(error.kind(), FailureKind::StateInvariantViolation);
    assert_eq!(state.core(), &core);
    assert_eq!(state.init_candidates(), &init_candidates);
    assert_eq!(state.active(), &active);
    assert!(Arc::ptr_eq(state.maintenance_plan().unwrap(), &plan));

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn support_and_producer_closed_coverage_skip_vampire_online() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("maintenance_execution_shortcuts");
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
        2,
        Duration::from_secs(30),
        Vec::new(),
    );
    let proposal = vec![
        true_formula(&task, "maintenance.execution.source"),
        false_formula(&task, "maintenance.execution.supported"),
        catalog_formula(&task, "maintenance.execution.covered"),
    ];
    let prepared = state
        .prepare_init_candidates(proposal, &ClauseSet::new(), &CancellationToken::new())
        .await;
    assert!(matches!(
        prepared,
        InitializationInvocationOutcome::Complete
    ));
    let mut ids = state.init_candidates().iter().copied().collect::<Vec<_>>();
    ids.sort_unstable();
    let [source, supported, covered] = ids.as_slice() else {
        panic!("three prepared clauses")
    };
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
            .record_initialization(*id, InitializationStatus::InitProved, evidence)
            .unwrap();
    }
    state.insert_maint_support(*source, *supported).unwrap();
    state.insert_maint_coverage(*source, *source).unwrap();
    state.insert_maint_coverage(*source, *covered).unwrap();
    state.insert_maint_coverage(*covered, *source).unwrap();
    state.insert_maint_coverage(*covered, *covered).unwrap();
    let result = prepare_maintenance(&task, &mut state, &CancellationToken::new()).await;
    assert!(matches!(result, MaintenancePreparationOutcome::Complete));
    let plan = state.current_maintenance_plan(&task).unwrap();
    assert_eq!(plan.schedule().tracks()[0].targets()[0], *source);

    let result = run_maintenance_block_sequential(
        &task,
        &mut state,
        vampire_command("race-proof-fast", Some(&launch_log)),
        &CancellationToken::new(),
    )
    .await;
    let MaintenanceExecutionOutcome::Complete(block) = result else {
        panic!("expected a complete shortcut block: {result:#?}")
    };
    assert_eq!(block.outcome(), MaintenanceBlockOutcome::Stable);
    assert_eq!(block.known_live().len(), 3);
    // The source/covered cycle does not bootstrap itself: source must be
    // queried before its edge can justify the covered target.
    assert_eq!(launch_count(&launch_log), 2);

    shutdown(state, context, artifacts, owner).await;
}

// ------------------------------------------------------------
// Exclusion, Fresh Blocks, And Retry State
// ------------------------------------------------------------

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn refutation_prunes_one_target_per_fresh_block() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("maintenance_execution_refute");
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
        2,
        Duration::from_secs(30),
        Vec::new(),
    );
    let ids = prepare_proved_active(
        &task,
        &mut state,
        vec![
            true_formula(&task, "maintenance.execution.refute.0"),
            catalog_formula(&task, "maintenance.execution.refute.1"),
        ],
    )
    .await;

    let outcome = run_maintenance_blocks_sequential(
        &task,
        &mut state,
        // Both workers finish immediately. The FMB result remains the only
        // conclusive branch, so this isolates refutation/pruning from process-
        // tree termination latency; dedicated race tests cover a hanging peer.
        vampire_command("race-proof-failure-model", Some(&launch_log)),
        &CancellationToken::new(),
    )
    .await;
    assert!(matches!(
        outcome,
        MaintenanceExecutionOutcome::Complete(None)
    ));
    assert!(state.active().is_empty());
    assert!(state.maintenance_plan().is_none());
    assert!(state.core().is_empty());
    assert_eq!(launch_count(&launch_log), ids.len() * 2);
    for id in ids {
        let record = state.catalog().record(id).unwrap();
        assert!(
            !record.has_retry_candidate(),
            "clause {} retained retry state: {record:#?}",
            id.get()
        );
        assert_eq!(record.next_retry_tier(), 0);
        assert!(!record.retry_exhausted());
    }

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn excluding_a_support_source_rechecks_its_target_in_a_fresh_block() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("maintenance_execution_support_exclusion");
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
        2,
        Duration::from_secs(30),
        Vec::new(),
    );
    let prepared = state
        .prepare_init_candidates(
            vec![
                false_formula(&task, "maintenance.execution.support.target"),
                true_formula(&task, "maintenance.execution.support.source"),
            ],
            &ClauseSet::new(),
            &CancellationToken::new(),
        )
        .await;
    assert!(matches!(
        prepared,
        InitializationInvocationOutcome::Complete
    ));
    let mut ids = state.init_candidates().iter().copied().collect::<Vec<_>>();
    ids.sort_unstable();
    let [target, source] = ids.as_slice() else {
        panic!("two prepared clauses")
    };
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
            .record_initialization(*id, InitializationStatus::InitProved, evidence)
            .unwrap();
    }
    state.insert_maint_support(*source, *target).unwrap();
    let prepared = prepare_maintenance(&task, &mut state, &CancellationToken::new()).await;
    assert!(matches!(prepared, MaintenancePreparationOutcome::Complete));
    assert_eq!(state.present_support_count(*target), Some(1));

    let command = vampire_command("race-proof-failure-model", Some(&launch_log));
    let first = run_maintenance_block_sequential(
        &task,
        &mut state,
        command.clone(),
        &CancellationToken::new(),
    )
    .await;
    let MaintenanceExecutionOutcome::Complete(first) = first else {
        panic!("expected a complete first block: {first:#?}")
    };
    assert_eq!(first.outcome(), MaintenanceBlockOutcome::Refuted(*source));
    assert_eq!(first.known_live(), &ClauseSet::from([*target]));
    assert_eq!(launch_count(&launch_log), 2);

    apply_maintenance_exclusion(&mut state, &first).unwrap();
    assert_eq!(state.active(), &ClauseSet::from([*target]));
    assert_eq!(state.present_support_count(*target), Some(0));

    let second =
        run_maintenance_block_sequential(&task, &mut state, command, &CancellationToken::new())
            .await;
    let MaintenanceExecutionOutcome::Complete(second) = second else {
        panic!("expected a complete second block: {second:#?}")
    };
    assert_eq!(second.outcome(), MaintenanceBlockOutcome::Refuted(*target));
    assert!(second.known_live().is_empty());
    assert_eq!(launch_count(&launch_log), 4);

    apply_maintenance_exclusion(&mut state, &second).unwrap();
    assert!(state.active().is_empty());
    assert!(state.maintenance_plan().is_none());
    assert!(state.present_support_count(*target).is_none());

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn default_timeout_chain_is_n_2n_3n_then_exhausted_without_launch() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("maintenance_execution_retry");
    let launch_log = directory.path().join("launches");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    // Leave enough wall time for both fixture processes to enter before the
    // local deadline; this test counts launches as well as retry state.
    let base = Duration::from_millis(200);
    let mut state = new_state(&task, &artifacts, &context, 2, base, vec![base, base]);
    let ids = prepare_proved_active(
        &task,
        &mut state,
        vec![true_formula(&task, "maintenance.execution.retry")],
    )
    .await;
    let id = ids[0];

    for expected_launches in [2, 4, 6] {
        let outcome = run_maintenance_blocks_sequential(
            &task,
            &mut state,
            vampire_command("race-timeout", Some(&launch_log)),
            &CancellationToken::new(),
        )
        .await;
        assert!(matches!(
            outcome,
            MaintenanceExecutionOutcome::Complete(None)
        ));
        assert_eq!(launch_count(&launch_log), expected_launches);
        let record = state.catalog().record(id).unwrap();
        assert_eq!(
            record.next_maintenance_allowance(base, &[base, base], &ClauseSet::from([id])),
            if expected_launches == 6 {
                Ok(None)
            } else {
                Ok(Some(
                    base.saturating_mul((expected_launches / 2 + 1) as u32),
                ))
            }
        );
        reprepare(&mut state, &task).await;
    }

    let outcome = run_maintenance_blocks_sequential(
        &task,
        &mut state,
        vampire_command("race-timeout", Some(&launch_log)),
        &CancellationToken::new(),
    )
    .await;
    assert!(matches!(
        outcome,
        MaintenanceExecutionOutcome::Complete(None)
    ));
    assert_eq!(launch_count(&launch_log), 6);
    let record = state.catalog().record(id).unwrap();
    assert!(record.retry_exhausted());
    assert_eq!(record.next_retry_tier(), 2);

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn lane_local_failure_prunes_without_advancing_retry() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("maintenance_execution_failure");
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
        2,
        Duration::from_secs(30),
        vec![Duration::from_secs(10)],
    );
    let id = prepare_proved_active(
        &task,
        &mut state,
        vec![true_formula(&task, "maintenance.execution.failure")],
    )
    .await[0];

    let result = run_maintenance_block_sequential(
        &task,
        &mut state,
        vampire_command("race-dual-failure", None),
        &CancellationToken::new(),
    )
    .await;
    let MaintenanceExecutionOutcome::Complete(block) = result else {
        panic!("expected a target-local failure: {result:#?}")
    };
    assert_eq!(block.outcome(), MaintenanceBlockOutcome::Failed(id));
    assert!(state.maintenance_failure().is_none());
    let record = state.catalog().record(id).unwrap();
    assert!(!record.has_retry_candidate());
    assert_eq!(record.next_retry_tier(), 0);

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn local_failure_reuses_exact_candidate_fmb_frontier_until_conclusive() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("maintenance_execution_failure_frontier");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    // This test checks retained FMB-frontier semantics, not solver speed.
    // Leave startup headroom when the full subprocess-heavy suite runs first.
    let base = Duration::from_secs(30);
    let mut state = new_state(&task, &artifacts, &context, 2, base, vec![base]);
    let id = prepare_proved_active(
        &task,
        &mut state,
        vec![true_formula(
            &task,
            "maintenance.execution.failure.frontier",
        )],
    )
    .await[0];
    let candidate = ClauseSet::from([id]);

    for expected_start in [1, 13] {
        let result = run_maintenance_block_sequential(
            &task,
            &mut state,
            vampire_command_at("race-dual-failure", expected_start, None),
            &CancellationToken::new(),
        )
        .await;
        let MaintenanceExecutionOutcome::Complete(block) = result else {
            panic!("expected a target-local failure: {result:#?}")
        };
        assert_eq!(block.outcome(), MaintenanceBlockOutcome::Failed(id));

        let record = state.catalog().record(id).unwrap();
        assert!(!record.has_retry_candidate());
        assert_eq!(record.next_retry_tier(), 0);
        assert!(!record.retry_exhausted());
        assert_eq!(
            record.next_fmb_start_size().map(|size| size.get()),
            Some(13)
        );
        assert_eq!(
            record.next_maintenance_allowance(base, &[base], &candidate),
            Ok(Some(base))
        );
    }

    let result = run_maintenance_block_sequential(
        &task,
        &mut state,
        vampire_command_at("race-proof-fast", 13, None),
        &CancellationToken::new(),
    )
    .await;
    let MaintenanceExecutionOutcome::Complete(block) = result else {
        panic!("expected a conclusive maintenance result: {result:#?}")
    };
    assert_eq!(block.outcome(), MaintenanceBlockOutcome::Stable);
    let record = state.catalog().record(id).unwrap();
    assert!(!record.has_retry_candidate());
    assert_eq!(record.next_retry_tier(), 0);
    assert!(!record.retry_exhausted());
    assert_eq!(record.next_fmb_start_size(), None);

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn timeout_advances_allowance_and_resumes_exact_candidate_fmb_frontier() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("maintenance_execution_timeout_frontier");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let base = Duration::from_millis(400);
    let retry_increment = Duration::from_secs(5);
    let mut state = new_state(&task, &artifacts, &context, 2, base, vec![retry_increment]);
    let id = prepare_proved_active(
        &task,
        &mut state,
        vec![true_formula(
            &task,
            "maintenance.execution.timeout.frontier",
        )],
    )
    .await[0];
    let candidate = ClauseSet::from([id]);

    let result = run_maintenance_block_sequential(
        &task,
        &mut state,
        vampire_command_at("race-timeout-advanced-frontier", 1, None),
        &CancellationToken::new(),
    )
    .await;
    let MaintenanceExecutionOutcome::Complete(block) = result else {
        panic!("expected a complete timeout result: {result:#?}")
    };
    assert_eq!(block.outcome(), MaintenanceBlockOutcome::TimedOut(id));
    let record = state.catalog().record(id).unwrap();
    assert!(record.has_retry_candidate());
    assert_eq!(record.retry_candidate_len(), Some(1));
    assert_eq!(record.next_retry_tier(), 0);
    assert!(!record.retry_exhausted());
    assert_eq!(
        record.next_fmb_start_size().map(|size| size.get()),
        Some(13)
    );
    assert_eq!(
        record.next_maintenance_allowance(base, &[retry_increment], &candidate),
        Ok(Some(base.saturating_add(retry_increment)))
    );

    let result = run_maintenance_block_sequential(
        &task,
        &mut state,
        vampire_command_at("race-proof-fast", 13, None),
        &CancellationToken::new(),
    )
    .await;
    let MaintenanceExecutionOutcome::Complete(block) = result else {
        panic!("expected an exact-Candidate retry result: {result:#?}")
    };
    assert_eq!(block.outcome(), MaintenanceBlockOutcome::Stable);
    let record = state.catalog().record(id).unwrap();
    assert!(!record.has_retry_candidate());
    assert_eq!(record.next_retry_tier(), 0);
    assert!(!record.retry_exhausted());
    assert_eq!(record.next_fmb_start_size(), None);

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn maintenance_query_contains_the_exact_loop_guard_antecedent() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("maintenance_execution_guard_antecedent");
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
        2,
        Duration::from_secs(30),
        Vec::new(),
    );
    let _id = prepare_proved_active(
        &task,
        &mut state,
        vec![true_formula(
            &task,
            "maintenance.execution.guard.antecedent",
        )],
    )
    .await[0];

    let result = run_maintenance_block_sequential(
        &task,
        &mut state,
        vampire_command("race-proof-fast", None),
        &CancellationToken::new(),
    )
    .await;
    let MaintenanceExecutionOutcome::Complete(block) = result else {
        panic!("expected a complete maintenance result: {result:#?}")
    };
    assert_eq!(block.outcome(), MaintenanceBlockOutcome::Stable);
    let guard = context
        .prepare_loop_guard_body(
            state.admission(),
            state.artifacts(),
            &CancellationToken::new(),
        )
        .await
        .unwrap();
    let query = fs::read_to_string(
        find_file_containing(&directory.path().join("artifacts"), "fof(goal, conjecture")
            .expect("maintenance must retain its assembled query"),
    )
    .unwrap();
    assert!(query.contains(guard.tptp_body()));

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn strict_candidate_shrink_resets_saved_fmb_frontier_to_one() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("maintenance_execution_shrink_frontier");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let base = Duration::from_millis(400);
    let retry_increment = Duration::from_secs(5);
    let mut state = new_state(&task, &artifacts, &context, 2, base, vec![retry_increment]);
    prepare_proved_active(
        &task,
        &mut state,
        vec![
            true_formula(&task, "maintenance.execution.shrink.frontier.0"),
            catalog_formula(&task, "maintenance.execution.shrink.frontier.1"),
        ],
    )
    .await;

    let result = run_maintenance_block_sequential(
        &task,
        &mut state,
        vampire_command_at("race-timeout-advanced-frontier", 1, None),
        &CancellationToken::new(),
    )
    .await;
    let MaintenanceExecutionOutcome::Complete(block) = result else {
        panic!("expected a complete timeout result: {result:#?}")
    };
    let MaintenanceBlockOutcome::TimedOut(target) = block.outcome() else {
        panic!("expected the first target to time out: {block:#?}")
    };
    let retry_formula = state.catalog().record(target).unwrap().formula().clone();
    assert_eq!(
        state
            .catalog()
            .record(target)
            .unwrap()
            .next_fmb_start_size()
            .map(|size| size.get()),
        Some(13)
    );

    apply_maintenance_exclusion(&mut state, &block).unwrap();
    let reproposed = prepare_proved_active(&task, &mut state, vec![retry_formula]).await;
    assert_eq!(reproposed, vec![target]);
    assert_eq!(state.active(), &ClauseSet::from([target]));

    // The fake FMB worker aborts if Houdini does not reset the strict-subset
    // Candidate's start size to one.
    let result = run_maintenance_block_sequential(
        &task,
        &mut state,
        vampire_command_at("race-proof-fast", 1, None),
        &CancellationToken::new(),
    )
    .await;
    let MaintenanceExecutionOutcome::Complete(block) = result else {
        panic!("expected a strict-subset retry result: {result:#?}")
    };
    assert_eq!(block.outcome(), MaintenanceBlockOutcome::Stable);
    assert_eq!(
        state
            .catalog()
            .record(target)
            .unwrap()
            .next_fmb_start_size(),
        None
    );

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn stale_nonstable_result_cannot_mutate_current_maintenance_publication() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("maintenance_execution_stale_exclusion");
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
        2,
        Duration::from_secs(30),
        Vec::new(),
    );
    prepare_proved_active(
        &task,
        &mut state,
        vec![true_formula(
            &task,
            "maintenance.execution.stale.exclusion.old",
        )],
    )
    .await;
    let old = run_maintenance_block_sequential(
        &task,
        &mut state,
        vampire_command("race-model-win", None),
        &CancellationToken::new(),
    )
    .await;
    let MaintenanceExecutionOutcome::Complete(old) = old else {
        panic!("expected an old nonstable block: {old:#?}")
    };
    assert!(matches!(old.outcome(), MaintenanceBlockOutcome::Refuted(_)));

    prepare_proved_active(
        &task,
        &mut state,
        vec![catalog_formula(
            &task,
            "maintenance.execution.stale.exclusion.current",
        )],
    )
    .await;
    let core = state.core().clone();
    let init_candidates = state.init_candidates().clone();
    let active = state.active().clone();
    let counts = active
        .iter()
        .copied()
        .map(|id| (id, state.present_support_count(id)))
        .collect::<Vec<_>>();
    let plan = Arc::clone(state.maintenance_plan().unwrap());

    let error = apply_maintenance_exclusion(&mut state, &old).unwrap_err();
    assert_eq!(error.origin(), FailureOrigin::MaintenanceExecution);
    assert_eq!(error.kind(), FailureKind::StateInvariantViolation);
    assert_eq!(state.core(), &core);
    assert_eq!(state.init_candidates(), &init_candidates);
    assert_eq!(state.active(), &active);
    assert_eq!(
        active
            .iter()
            .copied()
            .map(|id| (id, state.present_support_count(id)))
            .collect::<Vec<_>>(),
        counts
    );
    assert!(Arc::ptr_eq(state.maintenance_plan().unwrap(), &plan));

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn an_explicitly_reproposed_historical_drop_can_reach_core() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("maintenance_execution_reproposed_drop");
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
        2,
        Duration::from_secs(30),
        Vec::new(),
    );
    let clause = true_formula(&task, "maintenance.execution.reproposed.drop");
    let id = prepare_proved_active(&task, &mut state, vec![clause.clone()]).await[0];

    let dropped = state
        .prepare_init_candidates(
            Vec::new(),
            &ClauseSet::from([id]),
            &CancellationToken::new(),
        )
        .await;
    assert!(matches!(dropped, InitializationInvocationOutcome::Complete));
    assert!(state.catalog().record(id).unwrap().explicitly_dropped());

    let reproposed = state
        .prepare_init_candidates(vec![clause], &ClauseSet::new(), &CancellationToken::new())
        .await;
    assert!(matches!(
        reproposed,
        InitializationInvocationOutcome::Complete
    ));
    assert_eq!(state.init_candidates(), &ClauseSet::from([id]));
    state.insert_maint_support(id, id).unwrap();
    let prepared = prepare_maintenance(&task, &mut state, &CancellationToken::new()).await;
    assert!(matches!(prepared, MaintenancePreparationOutcome::Complete));

    let result = run_maintenance_block_sequential(
        &task,
        &mut state,
        vampire_command("race-proof-fast", None),
        &CancellationToken::new(),
    )
    .await;
    let MaintenanceExecutionOutcome::Complete(stable) = result else {
        panic!("expected a stable reproposed-clause block: {result:#?}")
    };
    assert_eq!(stable.outcome(), MaintenanceBlockOutcome::Stable);
    expand_core(&mut state, &stable).unwrap();
    assert_eq!(state.core(), &ClauseSet::from([id]));

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn cancellation_preserves_active_plan_and_retry_state() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("maintenance_execution_cancel");
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
        2,
        Duration::from_secs(30),
        vec![Duration::from_secs(10)],
    );
    let id = prepare_proved_active(
        &task,
        &mut state,
        vec![true_formula(&task, "maintenance.execution.cancel")],
    )
    .await[0];
    let cancellation = CancellationToken::new();
    let task_copy = task.clone();
    let cancellation_copy = cancellation.clone();
    let launch_log_copy = launch_log.clone();
    let check = tokio::spawn(async move {
        let result = run_maintenance_block_sequential(
            &task_copy,
            &mut state,
            vampire_command("race-timeout", Some(&launch_log_copy)),
            &cancellation_copy,
        )
        .await;
        (result, state)
    });
    tokio::time::timeout(Duration::from_secs(5), async {
        loop {
            if launch_count(&launch_log) == 2 {
                break;
            }
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    })
    .await
    .expect("maintenance Vampire pair did not launch");
    cancellation.cancel();

    let (outcome, state) = check.await.unwrap();
    assert!(matches!(outcome, MaintenanceExecutionOutcome::Cancelled));
    assert_eq!(state.active(), &ClauseSet::from([id]));
    assert!(state.maintenance_plan().is_some());
    assert!(state.maintenance_failure().is_none());
    let record = state.catalog().record(id).unwrap();
    assert!(!record.has_retry_candidate());
    assert_eq!(record.next_retry_tier(), 0);

    shutdown(state, context, artifacts, owner).await;
}

// ------------------------------------------------------------
// Fatal Shared-State Failure
// ------------------------------------------------------------

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn strict_serial_capacity_runs_proof_before_fmb() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("maintenance_execution_capacity");
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
        1,
        Duration::from_secs(30),
        Vec::new(),
    );
    let id = prepare_proved_active(
        &task,
        &mut state,
        vec![true_formula(&task, "maintenance.execution.capacity")],
    )
    .await[0];

    let result = run_maintenance_block_sequential(
        &task,
        &mut state,
        vampire_command("race-proof-fast", Some(&launch_log)),
        &CancellationToken::new(),
    )
    .await;
    let MaintenanceExecutionOutcome::Complete(block) = result else {
        panic!("expected a complete serial maintenance result: {result:#?}")
    };
    assert_eq!(block.outcome(), MaintenanceBlockOutcome::Stable);
    assert_eq!(block.entry_active(), &ClauseSet::from([id]));
    assert_eq!(block.candidate(), block.entry_active());
    assert_eq!(block.known_live(), block.entry_active());
    assert_eq!(state.active(), &ClauseSet::from([id]));
    assert!(state.maintenance_plan().is_some());
    assert!(state.maintenance_failure().is_none());
    assert_eq!(launch_count(&launch_log), 1);

    shutdown(state, context, artifacts, owner).await;
}

// ------------------------------------------------------------
// Optional Cold History
// ------------------------------------------------------------

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn enabled_history_records_closed_blocks_and_exclusions_lazily() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("maintenance_execution_history");
    let launch_log = directory.path().join("cancelled-launches");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts"))
            .maintenance_history(true, true),
    )
    .unwrap();
    let marker = artifacts
        .publish(
            ArtifactKind::RuntimeTrace,
            b"required history marker".as_slice().into(),
        )
        .unwrap();
    let run_root = artifacts
        .resolve(marker)
        .unwrap()
        .path()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_state(
        &task,
        &artifacts,
        &context,
        2,
        Duration::from_secs(30),
        Vec::new(),
    );
    assert!(state.maintenance_policy().log_maintenance_history());
    assert!(state.maintenance_policy().fail_on_history_log_error());
    prepare_proved_active(
        &task,
        &mut state,
        vec![
            true_formula(&task, "maintenance.execution.history.0"),
            false_formula(&task, "maintenance.execution.history.1"),
        ],
    )
    .await;
    assert!(!state.active().is_empty());
    assert!(!state.artifacts().diagnostics().history_sink_initialized);

    // Cancellation after launch consumes generation zero, but does not close
    // a block or construct a history record.
    let cancellation = CancellationToken::new();
    let task_copy = task.clone();
    let cancellation_copy = cancellation.clone();
    let launch_log_copy = launch_log.clone();
    let cancelled = tokio::spawn(async move {
        let outcome = run_maintenance_block_sequential(
            &task_copy,
            &mut state,
            vampire_command("race-timeout", Some(&launch_log_copy)),
            &cancellation_copy,
        )
        .await;
        (outcome, state)
    });
    tokio::time::timeout(Duration::from_secs(5), async {
        loop {
            if launch_count(&launch_log) == 2 {
                break;
            }
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    })
    .await
    .expect("maintenance Vampire pair did not launch before cancellation");
    cancellation.cancel();
    let (outcome, mut state) = cancelled.await.unwrap();
    assert!(matches!(outcome, MaintenanceExecutionOutcome::Cancelled));
    assert_eq!(
        state.artifacts().diagnostics().history_records_constructed,
        0
    );

    let first = run_maintenance_block_sequential(
        &task,
        &mut state,
        vampire_command("race-proof-failure-model", None),
        &CancellationToken::new(),
    )
    .await;
    let MaintenanceExecutionOutcome::Complete(first) = first else {
        panic!("expected the first closed history block: {first:#?}")
    };
    assert_eq!(first.generation().get(), 1);
    assert!(matches!(
        first.outcome(),
        MaintenanceBlockOutcome::Refuted(_)
    ));
    assert!(state.artifacts().diagnostics().history_sink_initialized);
    assert_eq!(
        state.artifacts().diagnostics().history_records_constructed,
        1
    );
    apply_maintenance_exclusion(&mut state, &first).unwrap();
    settle_maintenance_history(&mut state).unwrap();
    assert!(state.artifacts().diagnostics().history_sink_initialized);
    assert_eq!(state.artifacts().diagnostics().history_queue_depth, 0);
    assert_eq!(
        state.artifacts().diagnostics().history_records_constructed,
        2
    );

    // A later block reuses the one backend writer and appends rather than
    // replacing the first block's records.
    let second = run_maintenance_block_sequential(
        &task,
        &mut state,
        vampire_command("race-proof-failure-model", None),
        &CancellationToken::new(),
    )
    .await;
    let MaintenanceExecutionOutcome::Complete(second) = second else {
        panic!("expected the later closed history block: {second:#?}")
    };
    assert_eq!(second.generation().get(), 2);
    assert!(matches!(
        second.outcome(),
        MaintenanceBlockOutcome::Refuted(_)
    ));
    assert!(state.artifacts().diagnostics().history_sink_initialized);
    apply_maintenance_exclusion(&mut state, &second).unwrap();
    settle_maintenance_history(&mut state).unwrap();
    let diagnostics = state.artifacts().diagnostics();
    assert!(diagnostics.history_sink_initialized);
    assert_eq!(diagnostics.history_queue_depth, 0);
    assert_eq!(diagnostics.history_records_constructed, 4);
    assert!(diagnostics.history_path_exists);

    let history = fs::read_to_string(run_root.join("history/maintenance.jsonl")).unwrap();
    let records = history
        .lines()
        .map(|line| serde_json::from_str::<serde_json::Value>(line).unwrap())
        .collect::<Vec<_>>();
    assert_eq!(records.len(), 4);
    for record in &records {
        let scope = record["scope"].as_array().expect("history scope array");
        assert_eq!(
            scope.first().and_then(serde_json::Value::as_str),
            Some("root")
        );
        assert!(
            scope
                .iter()
                .any(|tag| { tag.as_str().is_some_and(|tag| tag.starts_with("catalog:")) })
        );
        assert!(scope.iter().any(|tag| tag == "houdini"));
        assert!(scope.iter().any(|tag| {
            tag.as_str()
                .is_some_and(|tag| tag.starts_with("houdini-run:"))
        }));
        assert!(scope.iter().any(|tag| {
            tag.as_str()
                .is_some_and(|tag| tag.starts_with("generation:"))
        }));
        assert!(record["generation"].is_u64());
    }
    assert_eq!(records[0]["event"], "maintenance_generation_state");
    assert_eq!(records[0]["state"], "closed");
    assert_eq!(records[0]["generation"], 1);
    assert!(records[0]["initial_core"].is_array());
    assert_eq!(records[0]["initial_active"].as_array().unwrap().len(), 2);
    assert_eq!(records[0]["outcome"], "refuted");
    assert_eq!(records[1]["event"], "maintenance_exclusion_applied");
    assert_eq!(records[0]["generation"], records[1]["generation"]);
    assert_eq!(records[2]["event"], "maintenance_generation_state");
    assert_eq!(records[2]["state"], "closed");
    assert_eq!(records[2]["generation"], 2);
    assert_eq!(records[3]["event"], "maintenance_exclusion_applied");
    assert_eq!(records[2]["generation"], records[3]["generation"]);

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn history_emits_a_new_baseline_after_core_expansion() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("maintenance_execution_history_new_plan");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts"))
            .maintenance_history(true, true),
    )
    .unwrap();
    let marker = artifacts
        .publish(
            ArtifactKind::RuntimeTrace,
            b"history new-plan marker".as_slice().into(),
        )
        .unwrap();
    let run_root = artifacts
        .resolve(marker)
        .unwrap()
        .path()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_state(
        &task,
        &artifacts,
        &context,
        2,
        Duration::from_secs(30),
        Vec::new(),
    );

    let first_id = prepare_self_supported_active(
        &task,
        &mut state,
        true_formula(&task, "maintenance.execution.history.plan.0"),
    )
    .await;
    let first = run_maintenance_block_sequential(
        &task,
        &mut state,
        vampire_command("race-proof-fast", None),
        &CancellationToken::new(),
    )
    .await;
    let MaintenanceExecutionOutcome::Complete(first) = first else {
        panic!("expected the first stable history block: {first:#?}")
    };
    assert_eq!(first.outcome(), MaintenanceBlockOutcome::Stable);
    expand_core(&mut state, &first).unwrap();

    let second_id = prepare_self_supported_active(
        &task,
        &mut state,
        false_formula(&task, "maintenance.execution.history.plan.1"),
    )
    .await;
    let second = run_maintenance_block_sequential(
        &task,
        &mut state,
        vampire_command("race-proof-fast", None),
        &CancellationToken::new(),
    )
    .await;
    let MaintenanceExecutionOutcome::Complete(second) = second else {
        panic!("expected the second stable history block: {second:#?}")
    };
    assert_eq!(second.outcome(), MaintenanceBlockOutcome::Stable);
    expand_core(&mut state, &second).unwrap();
    settle_maintenance_history(&mut state).unwrap();

    let history = fs::read_to_string(run_root.join("history/maintenance.jsonl")).unwrap();
    let generations = history
        .lines()
        .map(|line| serde_json::from_str::<serde_json::Value>(line).unwrap())
        .filter(|record| {
            record["event"] == "maintenance_generation_state" && record["state"] == "closed"
        })
        .collect::<Vec<_>>();
    assert_eq!(generations.len(), 2);
    assert_eq!(generations[0]["initial_core"].as_array().unwrap().len(), 0);
    assert_eq!(
        generations[0]["initial_active"].as_array().unwrap().len(),
        1
    );
    assert_eq!(generations[1]["initial_core"].as_array().unwrap().len(), 1);
    assert_eq!(
        generations[1]["initial_active"].as_array().unwrap().len(),
        1
    );
    assert_eq!(state.core(), &ClauseSet::from([first_id, second_id]));

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn strict_history_initialization_failure_preserves_the_required_manifest() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("maintenance_execution_history_failure");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts"))
            .maintenance_history(true, true),
    )
    .unwrap();
    let required = artifacts
        .publish(
            ArtifactKind::RuntimeTrace,
            b"required artifact survives history failure"
                .as_slice()
                .into(),
        )
        .unwrap();
    let run_root = artifacts
        .resolve(required)
        .unwrap()
        .path()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf();
    fs::write(
        run_root.join("history"),
        b"block history directory creation",
    )
    .unwrap();

    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_state(
        &task,
        &artifacts,
        &context,
        2,
        Duration::from_secs(30),
        Vec::new(),
    );
    let original_policy = state.maintenance_policy().clone();
    let mismatch = state
        .set_maintenance_policy(MaintenancePolicy::single_track())
        .unwrap_err();
    assert_eq!(mismatch.origin(), FailureOrigin::MaintenanceExecution);
    assert_eq!(mismatch.kind(), FailureKind::StateInvariantViolation);
    assert_eq!(state.maintenance_policy(), &original_policy);
    assert!(state.maintenance_failure().is_none());
    prepare_proved_active(
        &task,
        &mut state,
        vec![true_formula(&task, "maintenance.execution.history.failure")],
    )
    .await;

    let outcome = run_maintenance_block_sequential(
        &task,
        &mut state,
        vampire_command("race-proof-fast", None),
        &CancellationToken::new(),
    )
    .await;
    let MaintenanceExecutionOutcome::Failed(report) = outcome else {
        panic!("strict history initialization must fail the block: {outcome:#?}")
    };
    assert_eq!(report.origin(), FailureOrigin::MaintenanceHistory);
    assert_eq!(report.kind(), FailureKind::HistoryLogFailure);
    assert_eq!(
        state.maintenance_failure().unwrap().origin(),
        FailureOrigin::MaintenanceHistory
    );
    assert!(artifacts.resolve(required).is_ok());

    let resolver = artifacts.clone();
    context.shutdown().await.unwrap();
    drop(state);
    drop(context);
    drop(artifacts);
    let settlement = owner.settle().unwrap_err();
    assert_eq!(settlement.origin(), FailureOrigin::MaintenanceHistory);
    assert_eq!(settlement.kind(), FailureKind::HistoryLogFailure);
    assert!(resolver.resolve(required).is_ok());

    let manifest = fs::read_to_string(run_root.join("manifest.json")).unwrap();
    let manifest = serde_json::from_str::<serde_json::Value>(&manifest).unwrap();
    assert!(
        manifest["artifacts"]
            .as_array()
            .unwrap()
            .iter()
            .any(|record| {
                record["id"].as_u64() == Some(required.local_id())
                    && record["kind"] == "runtime_trace"
            })
    );
}
