mod support;

use std::ffi::OsString;
use std::time::Duration;

use whiel_runner::encoding::{
    EncodingWorkerCommand, EncodingWorkerPoolConfig, QfSolverSource, SolverBodySource,
    new_solver_encoding_context,
};
use whiel_runner::{
    ArtifactStoreConfig, CancellationToken, CancelledEntailmentCheck, EntailmentCheckResult,
    EntailmentInvocationOutcome, RuntimeResourcePolicy, SolverAdmission, VampireMode,
    VampireWorkerCommand, assemble_entailment, check_entailment, create_general_solver_admission,
    new_artifact_store,
};

fn admission() -> SolverAdmission {
    create_general_solver_admission(RuntimeResourcePolicy::agent_only(2, 2).unwrap()).unwrap()
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn warm_entailment_check_cannot_start_after_artifact_settlement() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("entailment_after_settlement");
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let admission = admission();
    let context = new_solver_encoding_context(
        &task,
        &artifacts,
        EncodingWorkerPoolConfig::new(
            EncodingWorkerCommand::new(
                support::example_encoding_worker(),
                support::repository_root(),
            ),
            1,
        )
        .unwrap(),
    )
    .unwrap();
    let source = SolverBodySource::QuantifierFree(
        QfSolverSource::new(&task, "task.phase2c_qf_fixture", [], []).unwrap(),
    );
    let goal = context
        .prepare_solver_bodies(
            &admission,
            &artifacts,
            vec![source],
            &CancellationToken::new(),
        )
        .await
        .unwrap()
        .remove(0);
    let entailment = assemble_entailment(
        &context,
        &admission,
        &artifacts,
        Vec::new(),
        vec![goal],
        &CancellationToken::new(),
    )
    .await
    .unwrap();
    let command = VampireWorkerCommand::new(support::fake_vampire())
        .with_extra_args([OsString::from("--fixture"), OsString::from("proof")])
        .unwrap();
    let first = check_entailment(
        &entailment,
        &artifacts,
        Some(Duration::from_secs(10)),
        VampireMode::ProofOnly,
        command.clone(),
        admission.clone(),
        CancellationToken::new(),
    )
    .await;
    assert!(matches!(
        first,
        EntailmentInvocationOutcome::Result(EntailmentCheckResult::Proved { .. })
    ));
    context.shutdown().await.unwrap();
    owner.settle().unwrap();

    let second = check_entailment(
        &entailment,
        &artifacts,
        Some(Duration::from_secs(10)),
        VampireMode::ProofOnly,
        command,
        admission,
        CancellationToken::new(),
    )
    .await;
    assert!(matches!(second, EntailmentInvocationOutcome::RunFailure(_)));
}

/*
  A scope owner which selects its own result stops its remaining peers as
  ordinary control flow. A peer observing that stop is canceled, exactly as
  it would have been had the stop arrived while its solver was still running.
  A run stop at the same boundary keeps failing closed: publication after the
  run closed must not be attempted. Neither form reaches a solver launch.
*/
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_cooperative_stop_cancels_the_check_where_a_run_stop_fails_closed() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("entailment_cooperative_stop");
    let launch_log = directory.path().join("vampire-launches");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let admission = admission();
    let context = new_solver_encoding_context(
        &task,
        &artifacts,
        EncodingWorkerPoolConfig::new(
            EncodingWorkerCommand::new(
                support::example_encoding_worker(),
                support::repository_root(),
            ),
            1,
        )
        .unwrap(),
    )
    .unwrap();
    let source = SolverBodySource::QuantifierFree(
        QfSolverSource::new(&task, "task.phase2c_qf_fixture", [], []).unwrap(),
    );
    let goal = context
        .prepare_solver_bodies(
            &admission,
            &artifacts,
            vec![source],
            &CancellationToken::new(),
        )
        .await
        .unwrap()
        .remove(0);
    let entailment = assemble_entailment(
        &context,
        &admission,
        &artifacts,
        Vec::new(),
        vec![goal],
        &CancellationToken::new(),
    )
    .await
    .unwrap();
    let command = VampireWorkerCommand::new(support::fake_vampire())
        .with_extra_args([
            OsString::from("--fixture"),
            OsString::from("proof"),
            OsString::from("--launch-log"),
            launch_log.as_os_str().to_owned(),
        ])
        .unwrap();

    let cooperative = CancellationToken::new();
    cooperative.cancel_cooperatively_for_tests();
    let stopped_scope = check_entailment(
        &entailment,
        &artifacts,
        Some(Duration::from_secs(10)),
        VampireMode::ProofOnly,
        command.clone(),
        admission.clone(),
        cooperative,
    )
    .await;
    assert!(
        matches!(
            stopped_scope,
            EntailmentInvocationOutcome::Cancelled(CancelledEntailmentCheck::Vampire(_))
        ),
        "a cooperative stop did not cancel the check: {stopped_scope:#?}"
    );

    let stopped_run = CancellationToken::new();
    stopped_run.cancel();
    let closed_run = check_entailment(
        &entailment,
        &artifacts,
        Some(Duration::from_secs(10)),
        VampireMode::ProofOnly,
        command,
        admission,
        stopped_run,
    )
    .await;
    assert!(
        matches!(closed_run, EntailmentInvocationOutcome::RunFailure(_)),
        "a run stop did not fail closed: {closed_run:#?}"
    );
    assert!(!launch_log.exists(), "a stopped check launched Vampire");

    context.shutdown().await.unwrap();
    drop(entailment);
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn cancellation_during_empty_check_retains_the_completed_proof() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("entailment_real_empty_cancellation");
    let marker = directory.path().join("empty-started");
    let launch_log = directory.path().join("vampire-launches");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let admission = admission();
    let worker = EncodingWorkerCommand::new(
        support::malformed_empty_encoding_worker(),
        support::repository_root(),
    )
    .arguments([
        OsString::from(support::example_encoding_worker().as_os_str()),
        marker.as_os_str().to_owned(),
    ]);
    let context = new_solver_encoding_context(
        &task,
        &artifacts,
        EncodingWorkerPoolConfig::new(worker, 1).unwrap(),
    )
    .unwrap();
    let source = SolverBodySource::QuantifierFree(
        QfSolverSource::new(&task, "task.phase2c_qf_fixture", [], []).unwrap(),
    );
    let goal = context
        .prepare_solver_bodies(
            &admission,
            &artifacts,
            vec![source],
            &CancellationToken::new(),
        )
        .await
        .unwrap()
        .remove(0);
    let entailment = assemble_entailment(
        &context,
        &admission,
        &artifacts,
        Vec::new(),
        vec![goal],
        &CancellationToken::new(),
    )
    .await
    .unwrap();

    let command = VampireWorkerCommand::new(support::fake_vampire())
        .with_extra_args([
            OsString::from("--fixture"),
            OsString::from("proof"),
            OsString::from("--launch-log"),
            launch_log.as_os_str().to_owned(),
        ])
        .unwrap();
    let cancellation = CancellationToken::new();
    let check = tokio::spawn({
        let entailment = entailment.clone();
        let artifacts = artifacts.clone();
        let admission = admission.clone();
        let cancellation = cancellation.clone();
        async move {
            check_entailment(
                &entailment,
                &artifacts,
                Some(Duration::from_secs(10)),
                VampireMode::ProofOnly,
                command,
                admission,
                cancellation,
            )
            .await
        }
    });
    tokio::time::timeout(Duration::from_secs(10), async {
        while !marker.exists() {
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    })
    .await
    .expect("empty checker did not start");
    cancellation.cancel();

    let result = check.await.unwrap();
    let EntailmentInvocationOutcome::Cancelled(CancelledEntailmentCheck::EmptyCheck {
        retained_proof,
    }) = result
    else {
        panic!("expected cancellation during the empty check: {result:#?}")
    };
    assert_eq!(
        retained_proof.query_artifact(),
        Some(entailment.query_artifact())
    );
    assert_eq!(
        std::fs::read_to_string(&launch_log)
            .unwrap()
            .lines()
            .count(),
        1
    );

    context.shutdown().await.unwrap();
    drop(entailment);
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}
