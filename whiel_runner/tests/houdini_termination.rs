mod support;

use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Duration;

use whiel_runner::encoding::{
    EncodingWorkerCommand, EncodingWorkerPoolConfig, QfSolverSource, SolverBodySource,
    SolverEncodingContext, new_solver_encoding_context,
};
use whiel_runner::{
    ArtifactKind, ArtifactStore, ArtifactStoreConfig, CancellationToken, ClauseCatalog,
    ClauseFormula, ClauseId, ClauseSet, FailureKind, FailureOrigin, HoudiniExecutionOutcome,
    HoudiniState, InitializationInvocationOutcome, InitializationStatus, LastTermStatus,
    MaintenancePreparationOutcome, RuntimeResourcePolicy, SolverAdmission,
    TerminationInvocationOutcome, VampireWorkerCommand, VerificationParameters,
    create_general_solver_admission, houdini, new_artifact_store, prepare_maintenance, term_check,
};

// ------------------------------------------------------------
// Termination Test Fixtures
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

fn state_with_term_policy(
    task: &whiel_runner::SynthesisTask,
    artifacts: &ArtifactStore,
    context: &SolverEncodingContext,
    limit: Duration,
    increments: Vec<Duration>,
) -> HoudiniState {
    let policy = runtime_policy();
    let verification = VerificationParameters::new(limit, policy)
        .unwrap()
        .with_bulk_maint_limit(Duration::ZERO)
        .with_search_term_limit(limit)
        .unwrap()
        .with_search_term_retry_increments(increments)
        .unwrap();
    let catalog = ClauseCatalog::new(task, context.clone(), artifacts).unwrap();
    HoudiniState::new(task, verification, admission(policy), catalog).unwrap()
}

fn true_formula(task: &whiel_runner::SynthesisTask, canonical: &str) -> ClauseFormula {
    let source = SolverBodySource::QuantifierFree(
        QfSolverSource::new(task, "task.phase2c_qf_fixture", [], []).unwrap(),
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

async fn install_true_core(
    task: &whiel_runner::SynthesisTask,
    state: &mut HoudiniState,
) -> ClauseId {
    let prepared = state
        .prepare_init_candidates(
            vec![true_formula(task, "termination.true.core")],
            &ClauseSet::new(),
            &CancellationToken::new(),
        )
        .await;
    assert!(matches!(
        prepared,
        InitializationInvocationOutcome::Complete
    ));
    let id = *state
        .init_candidates()
        .iter()
        .next()
        .expect("one registered clause");
    let evidence = state
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
    let prepared = prepare_maintenance(task, state, &CancellationToken::new()).await;
    assert!(matches!(prepared, MaintenancePreparationOutcome::Complete));
    let completed = houdini(
        task,
        state,
        vampire_command("race-proof-fast", None),
        &CancellationToken::new(),
    )
    .await;
    assert!(matches!(completed, HoudiniExecutionOutcome::Complete));
    assert_eq!(state.core(), &ClauseSet::from([id]));
    assert!(state.active().is_empty());
    id
}

fn launch_count(path: &Path) -> usize {
    fs::read_to_string(path).unwrap_or_default().lines().count()
}

fn find_file_containing(root: &Path, needle: &str) -> Option<PathBuf> {
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
// Exact Exit Obligation
// ------------------------------------------------------------

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn termination_query_uses_exact_core_and_negated_guard() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("termination_exact_query");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = state_with_term_policy(
        &task,
        &artifacts,
        &context,
        Duration::from_secs(10),
        Vec::new(),
    );
    let id = install_true_core(&task, &mut state).await;
    let core_body = state
        .catalog()
        .record(id)
        .unwrap()
        .formula_body()
        .unwrap()
        .tptp_body()
        .to_string();
    let exit_guard = context
        .prepare_negated_loop_guard_body(
            state.admission(),
            state.artifacts(),
            &CancellationToken::new(),
        )
        .await
        .unwrap()
        .tptp_body()
        .to_string();

    let outcome = term_check(
        &task,
        &mut state,
        vampire_command("race-proof-fast", None),
        &CancellationToken::new(),
    )
    .await;
    assert!(matches!(outcome, TerminationInvocationOutcome::Complete));
    assert!(matches!(state.last_term_status(), LastTermStatus::Proved));

    let query = fs::read_to_string(
        find_file_containing(&directory.path().join("artifacts"), "fof(goal, conjecture")
            .expect("termination must retain its assembled query"),
    )
    .unwrap();
    assert!(query.contains(&format!("fof(axiom_0, axiom, ({core_body})).")));
    assert!(query.contains(&format!("fof(axiom_1, axiom, ({exit_guard})).")));
    assert!(!query.contains("fof(axiom_2, axiom"));

    shutdown(state, context, artifacts, owner).await;
}

// ------------------------------------------------------------
// Cancellation And Retry Policy
// ------------------------------------------------------------

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn pre_cancelled_termination_preserves_pending_without_solver_launch() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("termination_pre_cancelled");
    let launch_log = directory.path().join("launches");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = state_with_term_policy(
        &task,
        &artifacts,
        &context,
        Duration::from_secs(10),
        Vec::new(),
    );
    let cancellation = CancellationToken::new();
    cancellation.cancel();

    let outcome = term_check(
        &task,
        &mut state,
        vampire_command("race-proof-fast", Some(&launch_log)),
        &cancellation,
    )
    .await;
    assert!(matches!(outcome, TerminationInvocationOutcome::Cancelled));
    assert!(matches!(state.last_term_status(), LastTermStatus::Pending));
    assert_eq!(launch_count(&launch_log), 0);

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn termination_retry_allowance_is_cumulative() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("termination_cumulative_retry");
    let launch_log = directory.path().join("launches");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = state_with_term_policy(
        &task,
        &artifacts,
        &context,
        Duration::from_millis(400),
        vec![Duration::from_millis(400)],
    );

    let outcome = term_check(
        &task,
        &mut state,
        vampire_command("race-first-pair-hang-then-delayed-proof", Some(&launch_log)),
        &CancellationToken::new(),
    )
    .await;
    assert!(matches!(outcome, TerminationInvocationOutcome::Complete));
    assert!(matches!(state.last_term_status(), LastTermStatus::Proved));
    assert_eq!(launch_count(&launch_log), 4);

    shutdown(state, context, artifacts, owner).await;
}

// ------------------------------------------------------------
// Failure Translation
// ------------------------------------------------------------

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn terminal_solver_failure_is_mapped_to_termination_status() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("termination_failure_mapping");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = state_with_term_policy(
        &task,
        &artifacts,
        &context,
        Duration::from_secs(10),
        Vec::new(),
    );

    let outcome = term_check(
        &task,
        &mut state,
        vampire_command("race-dual-failure", None),
        &CancellationToken::new(),
    )
    .await;
    assert!(matches!(outcome, TerminationInvocationOutcome::Complete));
    let LastTermStatus::Failure(report) = state.last_term_status() else {
        panic!("terminal solver failure must be retained in lastTermStatus")
    };
    assert_eq!(report.origin(), FailureOrigin::TerminationCheck);
    assert_eq!(report.kind(), FailureKind::ConcurrentWorkerFailures);
    assert!(!report.retryable());

    shutdown(state, context, artifacts, owner).await;
}
