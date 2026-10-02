mod support;

use std::ffi::OsString;
use std::fs;
use std::path::Path;
use std::time::Duration;

use whiel_runner::encoding::{
    EncodingWorkerCommand, EncodingWorkerPoolConfig, SolverEncodingContext,
    new_solver_encoding_context,
};
use whiel_runner::{
    ArtifactBackendOwner, ArtifactKind, ArtifactStore, ArtifactStoreConfig, CancellationToken,
    CertificationBridgeCommand, CertificationRuntime, CertifiedSynthesisResult, FmbSize,
    RuntimeResourcePolicy, SymbolicCexRuntime, SymbolicCexState, SymbolicHoudiniPolicy,
    VampireWorkerCommand, VerificationParameters, WInitializationInvocationOutcome,
    WRefutationResolutionOutcome, WSearchAttempt, WSearchResult, check_w_initialization,
    create_symbolic_solver_admissions, ensure_w_layer_bundle, new_artifact_store,
    new_symbolic_cex_state, resolve_w_refutation,
};

// These tests exercise model resolution and certification, not deadline
// behavior. Keep their local allowance outside ordinary machine-load jitter;
// timeout/frontier behavior has dedicated bounded fixtures below.
const CONCLUSIVE_FIXTURE_LIMIT: Duration = Duration::from_secs(30);

// ------------------------------------------------------------
// Shared Phase 4B Fixtures
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

fn certification_runtime(directory: &Path, mode: &str) -> CertificationRuntime {
    let repository = support::repository_root();
    let root = certification_root(directory);
    CertificationRuntime::new(
        CertificationBridgeCommand::new("python3", &repository).with_arguments([
            repository
                .join("whiel_runner/tests/fixtures/fake_certification_bridge.py")
                .into_os_string(),
            mode.into(),
        ]),
        root.join("certification-work"),
        root.join("solution"),
    )
}

fn certification_root(directory: &Path) -> std::path::PathBuf {
    support::repository_root()
        .join("whiel_runner/target/phase4b-certification")
        .join(
            directory
                .file_name()
                .expect("test directory has a final component"),
        )
}

fn restore_certification_root(directory: &Path) {
    let root = certification_root(directory);
    if root.exists() {
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(&root, fs::Permissions::from_mode(0o755))
                .expect("restore fixture certification-root permissions");
        }
        fs::remove_dir_all(root).expect("remove fixture certification root");
    }
}

fn vampire_runtime(
    directory: &Path,
    mode: &str,
    start_size: u64,
    certification_mode: &str,
) -> SymbolicCexRuntime {
    let launch_log = directory.join("vampire-launches.log");
    let vampire = VampireWorkerCommand::new(support::fake_vampire())
        .with_extra_args([
            OsString::from("--fixture"),
            OsString::from(mode),
            OsString::from("--expect-start"),
            OsString::from(start_size.to_string()),
            OsString::from("--launch-log"),
            launch_log.into_os_string(),
        ])
        .expect("valid fixture Vampire arguments");
    SymbolicCexRuntime::new(
        vampire,
        certification_runtime(directory, certification_mode),
    )
}

fn launch_count(directory: &Path) -> usize {
    fs::read_to_string(directory.join("vampire-launches.log"))
        .unwrap_or_default()
        .lines()
        .count()
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
    let (owner, artifacts) =
        new_artifact_store(task, ArtifactStoreConfig::new(directory.join("artifacts")))
            .expect("artifact store");
    let context =
        new_solver_encoding_context(task, &artifacts, worker_config()).expect("encoding context");
    let (_inv, cex) = create_symbolic_solver_admissions(resources()).expect("symbolic admissions");
    let state = new_symbolic_cex_state(
        task,
        context.clone(),
        &artifacts,
        verification(),
        cex,
        SymbolicHoudiniPolicy::default(),
    )
    .expect("symbolic CEX state");
    (owner, artifacts, context, state)
}

async fn settle(
    owner: ArtifactBackendOwner,
    artifacts: ArtifactStore,
    context: SolverEncodingContext,
    state: SymbolicCexState,
) {
    context.shutdown().await.expect("encoding worker shutdown");
    drop(state);
    drop(context);
    drop(artifacts);
    owner.settle().expect("artifact backend settlement");
}

// ------------------------------------------------------------
// Exact W Initialization And Durable Search Progress
// ------------------------------------------------------------

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn exact_w_query_persists_the_safe_fmb_frontier_and_attempt_artifacts() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("phase4b_w_frontier");
    let (owner, artifacts, context, mut state) = fresh_state(&task, directory.path());
    let cancellation = CancellationToken::new();

    ensure_w_layer_bundle(&task, &mut state, 0, &cancellation)
        .await
        .expect("construct exact W(0)");
    let first = WSearchAttempt::new(0, FmbSize::ONE, Duration::from_millis(150))
        .expect("bounded first attempt");
    let checked = match check_w_initialization(
        &task,
        &mut state,
        first,
        &vampire_runtime(
            directory.path(),
            "race-timeout-advanced-frontier",
            1,
            "success",
        ),
        &cancellation,
    )
    .await
    {
        WInitializationInvocationOutcome::Result(checked) => checked,
        outcome => panic!("bounded exact W query did not return a result: {outcome:#?}"),
    };
    assert!(matches!(
        checked.result(),
        WSearchResult::TimedOut { next_start_size, .. } if next_start_size.get() == 13
    ));
    assert!(checked.attempt_id().is_some());
    assert!(checked.terminal_artifact().is_some());
    state
        .record_w_initialization(checked)
        .expect("commit exact W timeout");
    assert_eq!(state.next_w_index(), 1);
    assert_eq!(state.next_w_start_size(0).get(), 13);
    assert_eq!(state.w_attempt_history(0).len(), 1);

    let retry = WSearchAttempt::new(0, FmbSize::new(13).unwrap(), Duration::from_millis(300))
        .expect("strictly larger retry effort");
    let checked = match check_w_initialization(
        &task,
        &mut state,
        retry,
        &vampire_runtime(directory.path(), "race-proof-fast", 13, "success"),
        &cancellation,
    )
    .await
    {
        WInitializationInvocationOutcome::Result(checked) => checked,
        outcome => panic!("exact W retry did not return a result: {outcome:#?}"),
    };
    assert!(matches!(checked.result(), WSearchResult::Proved { .. }));
    state
        .record_w_initialization(checked)
        .expect("commit exact W proof");
    assert_eq!(state.w_attempt_history(0).len(), 2);
    assert!(state.w_initialization_evidence(0).is_some());
    // Both race lanes are admitted. A fast proof can cancel the FMB lane either
    // immediately before or immediately after that lane launches its child.
    assert!((3..=4).contains(&launch_count(directory.path())));

    settle(owner, artifacts, context, state).await;
    restore_certification_root(directory.path());
}

// ------------------------------------------------------------
// Model Resolution And Existing Invalidity Certification
// ------------------------------------------------------------

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_w_model_reaches_the_existing_source_certificate_shape_and_stops_search() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("phase4b_w_certificate");
    let (owner, artifacts, context, mut state) = fresh_state(&task, directory.path());
    let cancellation = CancellationToken::new();

    ensure_w_layer_bundle(&task, &mut state, 0, &cancellation)
        .await
        .expect("construct exact W(0)");
    let attempt = WSearchAttempt::new(0, FmbSize::ONE, CONCLUSIVE_FIXTURE_LIMIT).unwrap();
    let runtime = vampire_runtime(directory.path(), "race-source-model-win", 1, "success");
    let checked =
        match check_w_initialization(&task, &mut state, attempt, &runtime, &cancellation).await {
            WInitializationInvocationOutcome::Result(checked) => checked,
            outcome => panic!("W model search did not return a result: {outcome:#?}"),
        };
    let counterexample = match checked.result() {
        WSearchResult::Refuted(counterexample) => counterexample.clone(),
        result => panic!("fixture must return a W refutation: {result:#?}"),
    };
    state
        .record_w_initialization(checked)
        .expect("commit exact W refutation");
    let decoded =
        whiel_runner::resolve_entailment_counterexample(&task, state.artifacts(), &counterexample)
            .expect("decode retained W model");
    whiel_runner::CertificationInstance::from_decoded(&task, &decoded)
        .expect("convert decoded W model to the source Instance shape");
    ensure_w_layer_bundle(&task, &mut state, 1, &cancellation)
        .await
        .expect("prepare later W work before certification");

    let certified = match resolve_w_refutation(
        &task,
        &mut state,
        0,
        &counterexample,
        &runtime,
        &cancellation,
    )
    .await
    {
        WRefutationResolutionOutcome::Certified(certified) => certified,
        outcome => panic!("decoded W model did not certify: {outcome:#?}"),
    };
    assert_eq!(
        artifacts.resolve(certified.certificate).unwrap().kind(),
        ArtifactKind::Certificate
    );
    assert_eq!(
        artifacts.resolve(certified.witness).unwrap().kind(),
        ArtifactKind::Witness
    );
    assert_eq!(
        artifacts.resolve(certified.record).unwrap().kind(),
        ArtifactKind::AcceptanceRecord
    );
    assert!(matches!(
        state.certified_invalid(),
        Some(CertifiedSynthesisResult::Invalid(_))
    ));

    let launches_at_certificate = launch_count(directory.path());
    let later = WSearchAttempt::new(1, FmbSize::ONE, Duration::from_secs(1)).unwrap();
    assert!(matches!(
        check_w_initialization(&task, &mut state, later, &runtime, &cancellation).await,
        WInitializationInvocationOutcome::RunFatal(_)
    ));
    assert_eq!(launch_count(directory.path()), launches_at_certificate);

    settle(owner, artifacts, context, state).await;
    restore_certification_root(directory.path());
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_transient_certification_failure_retries_then_drops_a_deterministic_failure() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("phase4b_w_certification_retry");
    let (owner, artifacts, context, mut state) = fresh_state(&task, directory.path());
    let cancellation = CancellationToken::new();

    ensure_w_layer_bundle(&task, &mut state, 0, &cancellation)
        .await
        .unwrap();
    let attempt = WSearchAttempt::new(0, FmbSize::ONE, CONCLUSIVE_FIXTURE_LIMIT).unwrap();
    let runtime = vampire_runtime(
        directory.path(),
        "race-source-model-win",
        1,
        "transient_then_infrastructure",
    );
    let checked =
        match check_w_initialization(&task, &mut state, attempt, &runtime, &cancellation).await {
            WInitializationInvocationOutcome::Result(checked) => checked,
            outcome => panic!("W model search did not return a result: {outcome:#?}"),
        };
    let counterexample = match checked.result() {
        WSearchResult::Refuted(counterexample) => counterexample.clone(),
        result => panic!("fixture must return a W refutation: {result:#?}"),
    };
    state.record_w_initialization(checked).unwrap();

    assert!(matches!(
        resolve_w_refutation(
            &task,
            &mut state,
            0,
            &counterexample,
            &runtime,
            &cancellation,
        )
        .await,
        WRefutationResolutionOutcome::Recorded
    ));
    let (retry_index, retry_counterexample) = state
        .next_counterexample_resolution()
        .expect("one transient failure enters the retry FIFO");
    assert_eq!(retry_index, 0);
    assert!(matches!(
        resolve_w_refutation(
            &task,
            &mut state,
            retry_index,
            &retry_counterexample,
            &runtime,
            &cancellation,
        )
        .await,
        WRefutationResolutionOutcome::Recorded
    ));
    assert!(
        state.next_counterexample_resolution().is_none(),
        "the second deterministic failure must not re-enter the fair retry FIFO"
    );
    assert!(state.run_fatal().is_none());

    settle(owner, artifacts, context, state).await;
    restore_certification_root(directory.path());
}

#[cfg(unix)]
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn an_immediate_run_global_certification_failure_blocks_the_next_w_launch() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("phase4b_w_immediate_run_global");
    let (owner, artifacts, context, mut state) = fresh_state(&task, directory.path());
    let cancellation = CancellationToken::new();
    ensure_w_layer_bundle(&task, &mut state, 0, &cancellation)
        .await
        .unwrap();
    ensure_w_layer_bundle(&task, &mut state, 1, &cancellation)
        .await
        .unwrap();
    let runtime = vampire_runtime(
        directory.path(),
        "race-source-model-win",
        1,
        "cleanup_failure",
    );
    let checked = match check_w_initialization(
        &task,
        &mut state,
        WSearchAttempt::new(0, FmbSize::ONE, CONCLUSIVE_FIXTURE_LIMIT).unwrap(),
        &runtime,
        &cancellation,
    )
    .await
    {
        WInitializationInvocationOutcome::Result(checked) => checked,
        outcome => panic!("W model search did not return a result: {outcome:#?}"),
    };
    let counterexample = match checked.result() {
        WSearchResult::Refuted(counterexample) => counterexample.clone(),
        result => panic!("fixture must return a W refutation: {result:#?}"),
    };
    state.record_w_initialization(checked).unwrap();
    let launches_before_failure = launch_count(directory.path());
    let outcome = resolve_w_refutation(
        &task,
        &mut state,
        0,
        &counterexample,
        &runtime,
        &cancellation,
    )
    .await;
    assert!(matches!(
        outcome,
        WRefutationResolutionOutcome::RunFatal(ref report)
            if report.scope() == whiel_runner::FailureScope::RunGlobal
    ));
    assert!(state.run_fatal().is_some());
    assert!(state.next_counterexample_resolution().is_none());

    let next = WSearchAttempt::new(1, FmbSize::ONE, Duration::from_secs(1)).unwrap();
    assert!(matches!(
        check_w_initialization(&task, &mut state, next, &runtime, &cancellation).await,
        WInitializationInvocationOutcome::RunFatal(_)
    ));
    assert_eq!(launch_count(directory.path()), launches_before_failure);

    restore_certification_root(directory.path());
    settle(owner, artifacts, context, state).await;
}

#[cfg(unix)]
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_queued_run_global_certification_failure_blocks_the_next_w_launch() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("phase4b_w_queued_run_global");
    let (owner, artifacts, context, mut state) = fresh_state(&task, directory.path());
    let cancellation = CancellationToken::new();
    ensure_w_layer_bundle(&task, &mut state, 0, &cancellation)
        .await
        .unwrap();
    ensure_w_layer_bundle(&task, &mut state, 1, &cancellation)
        .await
        .unwrap();
    let runtime = vampire_runtime(
        directory.path(),
        "race-source-model-win",
        1,
        "transient_then_cleanup",
    );
    let checked = match check_w_initialization(
        &task,
        &mut state,
        WSearchAttempt::new(0, FmbSize::ONE, CONCLUSIVE_FIXTURE_LIMIT).unwrap(),
        &runtime,
        &cancellation,
    )
    .await
    {
        WInitializationInvocationOutcome::Result(checked) => checked,
        outcome => panic!("W model search did not return a result: {outcome:#?}"),
    };
    let counterexample = match checked.result() {
        WSearchResult::Refuted(counterexample) => counterexample.clone(),
        result => panic!("fixture must return a W refutation: {result:#?}"),
    };
    state.record_w_initialization(checked).unwrap();

    assert!(matches!(
        resolve_w_refutation(
            &task,
            &mut state,
            0,
            &counterexample,
            &runtime,
            &cancellation,
        )
        .await,
        WRefutationResolutionOutcome::Recorded
    ));
    let (index, retry_counterexample) = state
        .next_counterexample_resolution()
        .expect("transient failure enters retry FIFO once");
    let outcome = resolve_w_refutation(
        &task,
        &mut state,
        index,
        &retry_counterexample,
        &runtime,
        &cancellation,
    )
    .await;
    assert!(matches!(
        outcome,
        WRefutationResolutionOutcome::RunFatal(ref report)
            if report.scope() == whiel_runner::FailureScope::RunGlobal
    ));
    assert!(state.run_fatal().is_some());
    assert!(state.next_counterexample_resolution().is_none());

    let launches_at_failure = launch_count(directory.path());
    let next = WSearchAttempt::new(1, FmbSize::ONE, Duration::from_secs(1)).unwrap();
    assert!(matches!(
        check_w_initialization(&task, &mut state, next, &runtime, &cancellation).await,
        WInitializationInvocationOutcome::RunFatal(_)
    ));
    assert_eq!(launch_count(directory.path()), launches_at_failure);

    restore_certification_root(directory.path());
    settle(owner, artifacts, context, state).await;
}
