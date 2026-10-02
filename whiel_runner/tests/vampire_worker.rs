mod support;

use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::thread;
use std::time::{Duration, Instant};

use whiel_runner::{
    ArtifactKind, ArtifactStore, ArtifactStoreConfig, CancellationToken, FailureKind,
    FailureOrigin, FailureScope, FmbOptions, FmbSize, VampireCapturePolicy, VampireProblem,
    VampireResult, VampireWorkerCommand, VampireWorkerMode, VampireWorkerOutcome,
    VampireWorkerRequest, new_artifact_store, run_single_vampire_worker,
};

// ------------------------------------------------------------
// Test Request Construction
// ------------------------------------------------------------

fn problem(directory: &support::TestDir) -> PathBuf {
    let problem = directory.path().join("problem.p");
    fs::write(&problem, "fof(goal, conjecture, $true).\n").unwrap();
    problem
}

fn command(arguments: impl IntoIterator<Item = OsString>) -> VampireWorkerCommand {
    VampireWorkerCommand::new(support::fake_vampire())
        .with_extra_args(arguments)
        .unwrap()
}

fn request(
    store: &ArtifactStore,
    problem: &Path,
    mode: VampireWorkerMode,
    arguments: &[&str],
) -> VampireWorkerRequest {
    VampireWorkerRequest::new(
        VampireProblem::new("fixture-entailment", problem),
        mode,
        command(arguments.iter().map(OsString::from)),
        store.clone(),
    )
    .unwrap()
}

// ------------------------------------------------------------
// Proof And Model Results
// ------------------------------------------------------------

#[test]
fn proof_worker_publishes_one_complete_proof() {
    let directory = support::TestDir::new("vampire_proof");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let request = request(
        &store,
        &problem(&directory),
        VampireWorkerMode::ProofOnly,
        &["--fixture", "proof"],
    );
    let attempt = request.attempt_id();

    let outcome = run_single_vampire_worker(
        request,
        CancellationToken::new(),
        VampireCapturePolicy::default(),
    );
    let VampireWorkerOutcome::Result(VampireResult::Proved(proof)) = outcome else {
        panic!("proof fixture was not proved")
    };
    assert_eq!(proof.problem_identity(), "fixture-entailment");
    assert_eq!(proof.attempt_id(), attempt);
    assert_eq!(proof.szs_status(), "Theorem");
    let artifact = store.resolve(proof.output()).unwrap();
    assert_eq!(artifact.kind(), ArtifactKind::Proof);
    assert_eq!(artifact.scope().last().map(String::as_str), Some("stdout"));
    let bytes = fs::read(artifact.path()).unwrap();
    assert!(bytes.ends_with(b"% SZS output end Proof for problem\n"));
    assert_eq!(store.diagnostics().required_payloads_published, 1);
    owner.settle().unwrap();
}

#[test]
fn fmb_worker_uses_complete_contours_and_publishes_one_model() {
    let directory = support::TestDir::new("vampire_model");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let options = FmbOptions {
        start_size: FmbSize::new(7).unwrap(),
        ..FmbOptions::default()
    };
    let request = request(
        &store,
        &problem(&directory),
        VampireWorkerMode::FmbOnly(options),
        &["--fixture", "model", "--expect-start", "7"],
    );

    let outcome = run_single_vampire_worker(
        request,
        CancellationToken::new(),
        VampireCapturePolicy::default(),
    );
    let VampireWorkerOutcome::Result(VampireResult::Refuted(model)) = outcome else {
        panic!("model fixture was not refuted")
    };
    assert_eq!(model.problem_identity(), "fixture-entailment");
    assert_eq!(model.szs_status(), "CounterSatisfiable");
    let artifact = store.resolve(model.output()).unwrap();
    assert_eq!(artifact.kind(), ArtifactKind::Model);
    assert_eq!(artifact.scope().last().map(String::as_str), Some("stdout"));
    let bytes = fs::read(artifact.path()).unwrap();
    assert!(bytes.ends_with(b"% SZS output end FiniteModel for problem\n"));
    assert_eq!(store.diagnostics().required_payloads_published, 1);
    owner.settle().unwrap();
}

#[test]
fn fmb_failure_retains_the_last_safe_frontier() {
    let directory = support::TestDir::new("vampire_fmb_failure");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let request = request(
        &store,
        &problem(&directory),
        VampireWorkerMode::FmbOnly(FmbOptions::default()),
        &["--fixture", "fmb-unknown", "--expect-start", "1"],
    );

    let outcome = run_single_vampire_worker(
        request,
        CancellationToken::new(),
        VampireCapturePolicy::default(),
    );
    let VampireWorkerOutcome::Result(VampireResult::Failure {
        report,
        next_fmb_start_size,
    }) = outcome
    else {
        panic!("expected FMB failure")
    };
    assert_eq!(report.kind(), FailureKind::SolverUnknown);
    assert_eq!(next_fmb_start_size, FmbSize::new(13));
    owner.settle().unwrap();
}

#[test]
fn installed_vampire_single_modes_smoke_test_when_available() {
    let executable = std::env::var_os("VAMPIRE_BIN")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("/opt/vampire/build/vampire"));
    if !executable.is_file() {
        return;
    }
    let directory = support::TestDir::new("installed_vampire");
    let proof_problem = directory.path().join("proof.p");
    fs::write(
        &proof_problem,
        "fof(a, axiom, p).\nfof(goal, conjecture, p).\n",
    )
    .unwrap();
    let model_problem = directory.path().join("model.p");
    fs::write(
        &model_problem,
        "fof(a, axiom, ? [X] : p(X)).\nfof(goal, conjecture, ! [X] : p(X)).\n",
    )
    .unwrap();
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let proof_request = VampireWorkerRequest::new(
        VampireProblem::new("real-proof", proof_problem),
        VampireWorkerMode::ProofOnly,
        VampireWorkerCommand::new(&executable),
        store.clone(),
    )
    .unwrap();
    let model_request = VampireWorkerRequest::new(
        VampireProblem::new("real-model", model_problem),
        VampireWorkerMode::FmbOnly(FmbOptions::default()),
        VampireWorkerCommand::new(&executable),
        store.clone(),
    )
    .unwrap();

    let proof = run_single_vampire_worker(
        proof_request,
        CancellationToken::new(),
        VampireCapturePolicy::default(),
    );
    let model = run_single_vampire_worker(
        model_request,
        CancellationToken::new(),
        VampireCapturePolicy::default(),
    );
    assert!(
        matches!(
            proof,
            VampireWorkerOutcome::Result(VampireResult::Proved(_))
        ),
        "unexpected real proof outcome: {proof:#?}"
    );
    assert!(
        matches!(
            model,
            VampireWorkerOutcome::Result(VampireResult::Refuted(_))
        ),
        "unexpected real model outcome: {model:#?}"
    );
    assert_eq!(store.diagnostics().required_payloads_published, 2);
    owner.settle().unwrap();
}

// ------------------------------------------------------------
// Output And Failure Classification
// ------------------------------------------------------------

#[test]
fn incomplete_proof_is_malformed_and_raw_output_is_discarded_by_default() {
    let directory = support::TestDir::new("vampire_malformed");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let request = request(
        &store,
        &problem(&directory),
        VampireWorkerMode::ProofOnly,
        &["--fixture", "malformed-proof"],
    );

    let outcome = run_single_vampire_worker(
        request,
        CancellationToken::new(),
        VampireCapturePolicy::default(),
    );
    let report = failure_report(&outcome);
    assert_eq!(report.origin(), FailureOrigin::VampireProofSearch);
    assert_eq!(report.kind(), FailureKind::MalformedResult);
    assert_eq!(report.scope(), FailureScope::LaneLocal);
    assert!(!report.retryable());
    assert_eq!(report.artifact_references().len(), 1);
    assert_eq!(
        store
            .resolve(report.artifact_references()[0])
            .unwrap()
            .kind(),
        ArtifactKind::FailureDiagnostic
    );
    assert_eq!(store.diagnostics().required_payloads_published, 1);
    owner.settle().unwrap();
}

#[test]
fn optional_inconclusive_capture_retains_both_complete_streams() {
    let directory = support::TestDir::new("vampire_debug_capture");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let request = request(
        &store,
        &problem(&directory),
        VampireWorkerMode::ProofOnly,
        &["--fixture", "unknown"],
    );

    let outcome = run_single_vampire_worker(
        request,
        CancellationToken::new(),
        VampireCapturePolicy::default().retain_full_inconclusive_output(true),
    );
    let report = failure_report(&outcome);
    assert_eq!(report.kind(), FailureKind::SolverUnknown);
    assert_eq!(report.artifact_references().len(), 3);
    let kinds = report
        .artifact_references()
        .iter()
        .map(|reference| store.resolve(*reference).unwrap().kind())
        .collect::<Vec<_>>();
    assert_eq!(
        kinds,
        vec![
            ArtifactKind::RuntimeTrace,
            ArtifactKind::RuntimeTrace,
            ArtifactKind::FailureDiagnostic,
        ]
    );
    assert_eq!(store.diagnostics().required_payloads_published, 3);
    owner.settle().unwrap();
}

#[test]
fn large_both_pipe_output_is_drained_and_streamed_without_truncation() {
    let directory = support::TestDir::new("vampire_large_output");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let request = request(
        &store,
        &problem(&directory),
        VampireWorkerMode::ProofOnly,
        &["--fixture", "large-proof"],
    );

    let outcome = run_single_vampire_worker(
        request,
        CancellationToken::new(),
        VampireCapturePolicy::default().diagnostic_bytes_per_stream(128),
    );
    let VampireWorkerOutcome::Result(VampireResult::Proved(proof)) = outcome else {
        panic!("large proof fixture was not proved")
    };
    let artifact = store.resolve(proof.output()).unwrap();
    assert!(artifact.byte_len() > 2 * 1024 * 1024);
    assert_eq!(store.diagnostics().required_payloads_published, 1);
    owner.settle().unwrap();
}

#[test]
fn output_limit_stops_and_reaps_a_flooding_worker() {
    let directory = support::TestDir::new("vampire_output_limit");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let request = request(
        &store,
        &problem(&directory),
        VampireWorkerMode::ProofOnly,
        &["--fixture", "flood-forever"],
    );
    let started = Instant::now();

    let outcome = run_single_vampire_worker(
        request,
        CancellationToken::new(),
        VampireCapturePolicy::default().max_total_output_bytes(Some(4096)),
    );
    assert!(started.elapsed() < Duration::from_secs(3));
    assert_eq!(
        failure_report(&outcome).kind(),
        FailureKind::InfrastructureFailure
    );
    owner.settle().unwrap();
}

#[test]
fn nonzero_exit_is_a_process_failure() {
    let directory = support::TestDir::new("vampire_nonzero");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let request = request(
        &store,
        &problem(&directory),
        VampireWorkerMode::ProofOnly,
        &["--fixture", "nonzero"],
    );
    let outcome = run_single_vampire_worker(
        request,
        CancellationToken::new(),
        VampireCapturePolicy::default(),
    );
    assert_eq!(failure_report(&outcome).kind(), FailureKind::ProcessFailure);
    owner.settle().unwrap();
}

#[test]
fn proof_failure_never_exposes_an_fmb_frontier() {
    let directory = support::TestDir::new("vampire_proof_frontier");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let request = request(
        &store,
        &problem(&directory),
        VampireWorkerMode::ProofOnly,
        &["--fixture", "proof-with-frontier"],
    );

    let outcome = run_single_vampire_worker(
        request,
        CancellationToken::new(),
        VampireCapturePolicy::default(),
    );
    let VampireWorkerOutcome::Result(VampireResult::Failure {
        next_fmb_start_size,
        ..
    }) = outcome
    else {
        panic!("expected proof-search failure")
    };
    assert_eq!(next_fmb_start_size, None);
    owner.settle().unwrap();
}

#[test]
fn missing_executable_is_a_process_failure() {
    let directory = support::TestDir::new("vampire_missing_executable");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let request = VampireWorkerRequest::new(
        VampireProblem::new("fixture-entailment", problem(&directory)),
        VampireWorkerMode::ProofOnly,
        VampireWorkerCommand::new(directory.path().join("absent-vampire")),
        store.clone(),
    )
    .unwrap();

    let outcome = run_single_vampire_worker(
        request,
        CancellationToken::new(),
        VampireCapturePolicy::default(),
    );
    assert_eq!(failure_report(&outcome).kind(), FailureKind::ProcessFailure);
    owner.settle().unwrap();
}

#[test]
fn unsafe_backend_failure_is_not_downgraded_to_a_lane_failure() {
    let directory = support::TestDir::new("vampire_settled_backend");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let request = request(
        &store,
        &problem(&directory),
        VampireWorkerMode::ProofOnly,
        &["--fixture", "proof"],
    );
    owner.settle().unwrap();

    let outcome = run_single_vampire_worker(
        request,
        CancellationToken::new(),
        VampireCapturePolicy::default(),
    );
    let VampireWorkerOutcome::RunFailure(report) = outcome else {
        panic!("expected a run-global artifact failure")
    };
    assert_eq!(report.scope(), FailureScope::RunGlobal);
    assert_eq!(report.origin(), FailureOrigin::ArtifactSettlement);
}

#[test]
fn invalid_utf8_cannot_become_a_proof() {
    let directory = support::TestDir::new("vampire_invalid_utf8");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let request = request(
        &store,
        &problem(&directory),
        VampireWorkerMode::ProofOnly,
        &["--fixture", "invalid-utf8-proof"],
    );
    let outcome = run_single_vampire_worker(
        request,
        CancellationToken::new(),
        VampireCapturePolicy::default(),
    );
    assert_eq!(
        failure_report(&outcome).kind(),
        FailureKind::MalformedResult
    );
    owner.settle().unwrap();
}

// ------------------------------------------------------------
// Process Cleanup And Cancellation
// ------------------------------------------------------------

#[cfg(any(target_os = "macos", target_os = "linux"))]
#[test]
fn cancellation_reaps_the_same_group_tree() {
    cancellation_reaps_tree(false);
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
#[test]
fn cancellation_reaps_an_observed_setsid_escapee() {
    cancellation_reaps_tree(true);
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
#[test]
fn fmb_cancellation_retains_the_safe_restart_frontier() {
    let directory = support::TestDir::new("vampire_fmb_frontier");
    let leader_path = directory.path().join("leader.pid");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let arguments = vec![
        OsString::from("--fixture"),
        OsString::from("hang-fmb-frontier"),
        OsString::from("--expect-start"),
        OsString::from("7"),
        OsString::from("--leader-pid"),
        leader_path.clone().into_os_string(),
    ];
    let request = VampireWorkerRequest::new(
        VampireProblem::new("fixture-entailment", problem(&directory)),
        VampireWorkerMode::FmbOnly(FmbOptions {
            start_size: FmbSize::new(7).unwrap(),
            ..FmbOptions::default()
        }),
        command(arguments),
        store.clone(),
    )
    .unwrap();
    let cancellation = CancellationToken::new();
    let child_cancellation = cancellation.clone();
    let handle = thread::spawn(move || {
        run_single_vampire_worker(
            request,
            child_cancellation,
            VampireCapturePolicy::default().retain_full_inconclusive_output(true),
        )
    });
    let leader = read_pid(&leader_path);
    let guard = PidGuard(leader);
    cancellation.cancel();

    let outcome = handle.join().unwrap();
    let VampireWorkerOutcome::Cancelled(cancelled) = outcome else {
        panic!("expected FMB cancellation")
    };
    assert_eq!(cancelled.next_fmb_start_size(), FmbSize::new(7));
    assert_eq!(cancelled.artifact_references().len(), 2);
    let stream_scopes = cancelled
        .artifact_references()
        .iter()
        .map(|reference| {
            store
                .resolve(*reference)
                .unwrap()
                .scope()
                .last()
                .unwrap()
                .clone()
        })
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(
        stream_scopes,
        ["stderr".to_string(), "stdout".to_string()].into()
    );
    assert!(wait_for_process_exit(leader));
    std::mem::forget(guard);
    owner.settle().unwrap();
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
fn cancellation_reaps_tree(escape: bool) {
    let label = if escape { "escape" } else { "group" };
    let directory = support::TestDir::new(&format!("vampire_cancel_{label}"));
    let leader_path = directory.path().join("leader.pid");
    let child_path = directory.path().join("child.pid");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let fixture = if escape {
        "hang-escape-tree"
    } else {
        "hang-tree"
    };
    let arguments = vec![
        OsString::from("--fixture"),
        OsString::from(fixture),
        OsString::from("--leader-pid"),
        leader_path.clone().into_os_string(),
        OsString::from("--child-pid"),
        child_path.clone().into_os_string(),
    ];
    let request = VampireWorkerRequest::new(
        VampireProblem::new("fixture-entailment", problem(&directory)),
        VampireWorkerMode::ProofOnly,
        command(arguments),
        store.clone(),
    )
    .unwrap();
    let cancellation = CancellationToken::new();
    let child_cancellation = cancellation.clone();
    let handle = thread::spawn(move || {
        run_single_vampire_worker(request, child_cancellation, VampireCapturePolicy::default())
    });
    let leader = read_pid(&leader_path);
    let child = read_pid(&child_path);
    let leader_guard = PidGuard(leader);
    let child_guard = PidGuard(child);
    if escape {
        thread::sleep(Duration::from_millis(100));
    }
    cancellation.cancel();
    let started = Instant::now();
    let outcome = handle.join().unwrap();
    assert!(started.elapsed() < Duration::from_secs(3));
    assert!(matches!(outcome, VampireWorkerOutcome::Cancelled(_)));
    assert!(wait_for_process_exit(leader));
    assert!(wait_for_process_exit(child));
    std::mem::forget(leader_guard);
    std::mem::forget(child_guard);
    owner.settle().unwrap();
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
#[test]
fn normal_root_exit_still_reaps_a_pipe_holding_descendant() {
    normal_root_exit_reaps_descendant(false);
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
#[test]
fn normal_root_exit_reaps_an_observed_session_escapee() {
    normal_root_exit_reaps_descendant(true);
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
fn normal_root_exit_reaps_descendant(escape: bool) {
    let directory = support::TestDir::new("vampire_natural_tree_cleanup");
    let child_path = directory.path().join("child.pid");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let arguments = vec![
        OsString::from("--fixture"),
        OsString::from(if escape {
            "exit-with-escape-child"
        } else {
            "exit-with-child"
        }),
        OsString::from("--child-pid"),
        child_path.clone().into_os_string(),
    ];
    let request = VampireWorkerRequest::new(
        VampireProblem::new("fixture-entailment", problem(&directory)),
        VampireWorkerMode::ProofOnly,
        command(arguments),
        store.clone(),
    )
    .unwrap();
    let started = Instant::now();
    let outcome = run_single_vampire_worker(
        request,
        CancellationToken::new(),
        VampireCapturePolicy::default(),
    );
    assert!(started.elapsed() < Duration::from_secs(3));
    assert!(matches!(
        outcome,
        VampireWorkerOutcome::Result(VampireResult::Proved(_))
    ));
    let child = read_pid(&child_path);
    let guard = PidGuard(child);
    assert!(wait_for_process_exit(child));
    std::mem::forget(guard);
    owner.settle().unwrap();
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
#[test]
fn cancellation_while_both_pipes_flood_stops_the_worker() {
    let directory = support::TestDir::new("vampire_cancel_flood");
    let leader_path = directory.path().join("leader.pid");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let arguments = vec![
        OsString::from("--fixture"),
        OsString::from("flood-forever"),
        OsString::from("--leader-pid"),
        leader_path.clone().into_os_string(),
    ];
    let request = VampireWorkerRequest::new(
        VampireProblem::new("fixture-entailment", problem(&directory)),
        VampireWorkerMode::ProofOnly,
        command(arguments),
        store.clone(),
    )
    .unwrap();
    let cancellation = CancellationToken::new();
    let child_cancellation = cancellation.clone();
    let handle = thread::spawn(move || {
        run_single_vampire_worker(request, child_cancellation, VampireCapturePolicy::default())
    });
    let leader = read_pid(&leader_path);
    let guard = PidGuard(leader);
    cancellation.cancel();

    let started = Instant::now();
    let outcome = handle.join().unwrap();
    assert!(started.elapsed() < Duration::from_secs(3));
    assert!(matches!(outcome, VampireWorkerOutcome::Cancelled(_)));
    assert!(wait_for_process_exit(leader));
    std::mem::forget(guard);
    owner.settle().unwrap();
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
#[test]
fn cancellation_before_launch_starts_no_process() {
    let directory = support::TestDir::new("vampire_prelaunch_cancel");
    let leader_path = directory.path().join("leader.pid");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let arguments = vec![
        OsString::from("--fixture"),
        OsString::from("hang-tree"),
        OsString::from("--leader-pid"),
        leader_path.clone().into_os_string(),
    ];
    let request = VampireWorkerRequest::new(
        VampireProblem::new("fixture-entailment", problem(&directory)),
        VampireWorkerMode::ProofOnly,
        command(arguments),
        store.clone(),
    )
    .unwrap();
    let cancellation = CancellationToken::new();
    cancellation.cancel();
    let outcome = run_single_vampire_worker(request, cancellation, VampireCapturePolicy::default());
    assert!(matches!(outcome, VampireWorkerOutcome::Cancelled(_)));
    assert!(!leader_path.exists());
    assert_eq!(store.diagnostics().required_payloads_published, 0);
    owner.settle().unwrap();
}

// ------------------------------------------------------------
// Test Inspection Helpers
// ------------------------------------------------------------

fn failure_report(outcome: &VampireWorkerOutcome) -> &whiel_runner::FailureReport {
    let VampireWorkerOutcome::Result(VampireResult::Failure { report, .. }) = outcome else {
        panic!("expected a Vampire failure")
    };
    report
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
fn read_pid(path: &Path) -> u32 {
    for _ in 0..300 {
        if let Ok(value) = fs::read_to_string(path)
            && let Ok(pid) = value.trim().parse()
        {
            return pid;
        }
        thread::sleep(Duration::from_millis(10));
    }
    panic!("PID file was not written: {}", path.display());
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
fn process_exists(pid: u32) -> bool {
    Command::new("/bin/kill")
        .arg("-0")
        .arg(pid.to_string())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .is_ok_and(|status| status.success())
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
fn wait_for_process_exit(pid: u32) -> bool {
    for _ in 0..200 {
        if !process_exists(pid) {
            return true;
        }
        thread::sleep(Duration::from_millis(10));
    }
    false
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
struct PidGuard(u32);

#[cfg(any(target_os = "macos", target_os = "linux"))]
impl Drop for PidGuard {
    fn drop(&mut self) {
        let _ = Command::new("/bin/kill")
            .args(["-KILL", &self.0.to_string()])
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status();
    }
}
