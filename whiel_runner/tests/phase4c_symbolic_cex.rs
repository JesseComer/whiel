mod support;

use std::ffi::OsString;
use std::fs;
use std::path::Path;
use std::time::Duration;

use whiel_runner::encoding::{
    EncodingError, EncodingWorkerCommand, EncodingWorkerPoolConfig, SolverEncodingContext,
    new_solver_encoding_context,
};
use whiel_runner::{
    ArtifactBackendOwner, ArtifactStore, ArtifactStoreConfig, CancellationToken,
    CertificationBridgeCommand, CertificationRuntime, FailureScope, RuntimeResourcePolicy,
    SymbolicCexRuntime, SymbolicCexState, SymbolicHoudiniPolicy, SymbolicLaneOutcome,
    VampireWorkerCommand, VerificationParameters, WPublicationOutcome,
    create_symbolic_solver_admissions, create_w_proof_channel, ensure_w_layer_bundle,
    new_artifact_store, new_symbolic_cex_state, publish_available_w_proofs, run_cex_lane,
    search_w_counterexamples,
};

// ------------------------------------------------------------
// Shared Phase 4C Fixture
// ------------------------------------------------------------

fn resources() -> RuntimeResourcePolicy {
    RuntimeResourcePolicy::symbolic(4, 2, 2).expect("valid symbolic resource policy")
}

fn verification() -> VerificationParameters {
    VerificationParameters::new(Duration::from_secs(5), resources())
        .expect("positive search limit")
        .with_final_certification_limit(Some(Duration::from_secs(5)))
        .expect("positive certification limit")
}

fn runtime(directory: &Path, mode: &str) -> SymbolicCexRuntime {
    let vampire = VampireWorkerCommand::new(support::fake_vampire())
        .with_extra_args([
            OsString::from("--fixture"),
            OsString::from(mode),
            OsString::from("--expect-start"),
            OsString::from("1"),
            OsString::from("--launch-log"),
            directory.join("vampire-launches.log").into_os_string(),
        ])
        .expect("valid fixture Vampire arguments");
    let repository = support::repository_root();
    let certification = CertificationRuntime::new(
        CertificationBridgeCommand::new("python3", &repository).with_arguments([
            repository
                .join("whiel_runner/tests/fixtures/fake_certification_bridge.py")
                .into_os_string(),
            "success".into(),
        ]),
        directory.join("certification-work"),
        directory.join("solution"),
    );
    SymbolicCexRuntime::new(vampire, certification)
}

fn fresh_state(
    task: &whiel_runner::SynthesisTask,
    directory: &Path,
) -> (
    ArtifactBackendOwner,
    ArtifactStore,
    SolverEncodingContext,
    SymbolicCexState,
) {
    fresh_state_with_policy(task, directory, SymbolicHoudiniPolicy::default())
}

fn fresh_state_with_policy(
    task: &whiel_runner::SynthesisTask,
    directory: &Path,
    policy: SymbolicHoudiniPolicy,
) -> (
    ArtifactBackendOwner,
    ArtifactStore,
    SolverEncodingContext,
    SymbolicCexState,
) {
    let (owner, artifacts) =
        new_artifact_store(task, ArtifactStoreConfig::new(directory.join("artifacts")))
            .expect("artifact store");
    let workers = EncodingWorkerPoolConfig::new(
        EncodingWorkerCommand::new(
            support::example_encoding_worker(),
            support::repository_root(),
        ),
        2,
    )
    .expect("positive worker count");
    let context = new_solver_encoding_context(task, &artifacts, workers).expect("encoding context");
    let (_inv, cex) = create_symbolic_solver_admissions(resources()).expect("admissions");
    let state = new_symbolic_cex_state(
        task,
        context.clone(),
        &artifacts,
        verification(),
        cex,
        policy,
    )
    .expect("symbolic CEX state");
    (owner, artifacts, context, state)
}

async fn settle(
    owner: ArtifactBackendOwner,
    artifacts: ArtifactStore,
    context: SolverEncodingContext,
    state: Option<SymbolicCexState>,
) {
    context.shutdown().await.expect("encoding worker shutdown");
    drop(state);
    drop(context);
    drop(artifacts);
    owner.settle().expect("artifact backend settlement");
}

fn launch_count(directory: &Path) -> usize {
    fs::read_to_string(directory.join("vampire-launches.log"))
        .unwrap_or_default()
        .lines()
        .count()
}

// ------------------------------------------------------------
// Live Serial CEX Scheduling
// ------------------------------------------------------------

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn default_cex_search_uses_a_paired_higher_w_race_but_publishes_only_w_zero() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("phase4c_live_cex");
    let (owner, artifacts, context, mut state) = fresh_state(&task, directory.path());
    let (sender, receiver) = create_w_proof_channel(task.identity(), artifacts.backend_id());
    let cancellation = CancellationToken::new();
    let cancellation_driver = cancellation.clone();
    let log_directory = directory.path().to_path_buf();
    let cex_runtime = runtime(directory.path(), "race-first-pair-proof-then-hang");

    let search = search_w_counterexamples(&task, &mut state, &sender, &cex_runtime, &cancellation);
    let cancel_after_higher_pair = async move {
        for _ in 0..2_000 {
            if launch_count(&log_directory) >= 4 {
                cancellation_driver.cancel();
                return;
            }
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
        panic!("the higher-W proof/FMB pair was not launched");
    };
    let (outcome, ()) = tokio::join!(search, cancel_after_higher_pair);

    assert!(matches!(outcome, SymbolicLaneOutcome::Cancelled));
    assert_eq!(launch_count(directory.path()), 4);
    assert_eq!(state.next_w_index(), 1);
    assert_eq!(state.w_attempt_history(0).len(), 1);
    assert!(state.w_attempt_history(1).is_empty());
    assert!(state.w_was_published(0));
    assert!(!state.w_was_published(1));
    let batch = receiver.peek_proved_batch().expect("W(0) publication");
    assert_eq!(
        batch
            .entries()
            .iter()
            .map(whiel_runner::ProvedWEntry::index)
            .collect::<Vec<_>>(),
        vec![0]
    );

    sender.close();
    drop(sender);
    drop(receiver);
    settle(owner, artifacts, context, Some(state)).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn higher_w_policy_publishes_production_bundles_and_republication_is_idempotent() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("phase4c_higher_w_publication");
    let policy = SymbolicHoudiniPolicy::new(true, Default::default());
    let (owner, artifacts, context, mut state) =
        fresh_state_with_policy(&task, directory.path(), policy);
    let (sender, receiver) = create_w_proof_channel(task.identity(), artifacts.backend_id());
    let cancellation = CancellationToken::new();
    let cancellation_driver = cancellation.clone();
    let cex_runtime = runtime(directory.path(), "race-first-three-pairs-proof-then-hang");

    let search = search_w_counterexamples(&task, &mut state, &sender, &cex_runtime, &cancellation);
    let cancel_after_three_publications = async {
        for _ in 0..2_000 {
            if receiver
                .peek_proved_batch()
                .is_some_and(|batch| batch.entries().len() == 3)
            {
                cancellation_driver.cancel();
                return;
            }
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
        panic!("three higher-W production publications were not observed");
    };
    let (outcome, ()) = tokio::join!(search, cancel_after_three_publications);

    assert!(matches!(outcome, SymbolicLaneOutcome::Cancelled));
    let batch = receiver.peek_proved_batch().expect("three W publications");
    assert_eq!(
        batch
            .entries()
            .iter()
            .map(whiel_runner::ProvedWEntry::index)
            .collect::<Vec<_>>(),
        vec![0, 1, 2]
    );
    let exact_entries = batch.entries().to_vec();
    receiver.acknowledge_proved_batch(&batch).unwrap();
    assert!(receiver.peek_proved_batch().is_none());
    assert_eq!(
        sender.publish_batch(exact_entries).unwrap(),
        WPublicationOutcome::NoChange
    );
    publish_available_w_proofs(&task, &mut state, &sender).unwrap();
    assert!(receiver.peek_proved_batch().is_none());

    sender.close();
    drop(sender);
    drop(receiver);
    settle(owner, artifacts, context, Some(state)).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn cex_lane_closes_publication_on_a_prelaunch_cancellation() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("phase4c_cancelled_lane");
    let (owner, artifacts, context, state) = fresh_state(&task, directory.path());
    let (sender, receiver) = create_w_proof_channel(task.identity(), artifacts.backend_id());
    let cancellation = CancellationToken::new();
    cancellation.cancel();

    let outcome = run_cex_lane(
        &task,
        state,
        sender,
        &runtime(directory.path(), "race-timeout"),
        &cancellation,
    )
    .await;
    assert!(matches!(outcome, SymbolicLaneOutcome::Cancelled));
    assert!(receiver.is_closed_and_empty());
    assert_eq!(launch_count(directory.path()), 0);

    drop(receiver);
    settle(owner, artifacts, context, None).await;
}

// ------------------------------------------------------------
// Bundle-Failure Atomicity
// ------------------------------------------------------------

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn local_and_global_bundle_failures_consume_no_w_attempt_progress() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("phase4c_bundle_failures");
    let (owner, artifacts, context, mut state) = fresh_state(&task, directory.path());
    let cancellation = CancellationToken::new();

    let local = ensure_w_layer_bundle(&task, &mut state, 1, &cancellation)
        .await
        .expect_err("noncontiguous W construction must fail locally");
    assert!(matches!(
        local,
        EncodingError::Failure(ref report) if report.scope() == FailureScope::LaneLocal
    ));
    assert_eq!(state.next_w_index(), 0);
    assert!(state.w_attempt_history(0).is_empty());
    assert_eq!(state.next_w_start_size(0).get(), 1);
    assert!(state.run_fatal().is_none());

    let mismatched_json =
        support::export_canonical_task_json().replace("Example0012", "Example0002");
    let mismatched = whiel_runner::SynthesisTask::from_json(&mismatched_json)
        .expect("consistent mismatched task identity");
    let global = ensure_w_layer_bundle(&mismatched, &mut state, 0, &cancellation)
        .await
        .expect_err("cross-task W construction must fail globally");
    assert!(matches!(
        global,
        EncodingError::Failure(ref report) if report.scope() == FailureScope::RunGlobal
    ));
    assert_eq!(state.next_w_index(), 0);
    assert!(state.w_attempt_history(0).is_empty());
    assert_eq!(state.next_w_start_size(0).get(), 1);
    assert!(state.run_fatal().is_some());
    assert_eq!(launch_count(directory.path()), 0);

    settle(owner, artifacts, context, Some(state)).await;
}
