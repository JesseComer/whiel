mod support;

use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::{Arc, OnceLock};
use std::time::{Duration, Instant};

use whiel_runner::framework2::PinnedLeancheckVampire;
use whiel_runner::{
    ArtifactStore, ArtifactStoreConfig, CancellationToken, FailureKind, FailureOrigin, FmbOptions,
    FmbSize, ProofCascPolicy, ProofCascShare, RuntimeResourcePolicy, SolverAdmission,
    VampireCapturePolicy, VampireInvocationOutcome, VampireMode, VampireProblem,
    VampireProofStrategy, VampireRequest, VampireRequestError, VampireResult, VampireSearchBudget,
    VampireWorkerCommand, create_general_solver_admission, new_artifact_store, run_vampire,
};

// ------------------------------------------------------------
// Test Request Construction
// ------------------------------------------------------------

fn problem(directory: &support::TestDir) -> PathBuf {
    let problem = directory.path().join("problem.p");
    fs::write(&problem, "fof(goal, conjecture, $true).\n").unwrap();
    problem
}

fn request(
    directory: &support::TestDir,
    store: &ArtifactStore,
    admission: SolverAdmission,
    fixture: &str,
    mode: VampireMode,
    local_limit: Option<Duration>,
    extra: &[(&str, &Path)],
) -> VampireRequest {
    request_with_share(
        directory,
        store,
        admission,
        fixture,
        mode,
        local_limit,
        extra,
        ProofCascShare::DISABLED,
    )
}

#[allow(clippy::too_many_arguments)]
fn request_with_share(
    directory: &support::TestDir,
    store: &ArtifactStore,
    admission: SolverAdmission,
    fixture: &str,
    mode: VampireMode,
    local_limit: Option<Duration>,
    extra: &[(&str, &Path)],
    share: ProofCascShare,
) -> VampireRequest {
    request_with_policy_and_budget(
        directory,
        store,
        admission,
        fixture,
        mode,
        local_limit.into(),
        extra,
        ProofCascPolicy::uniform(share),
    )
}

#[allow(clippy::too_many_arguments)]
fn request_with_policy_and_budget(
    directory: &support::TestDir,
    store: &ArtifactStore,
    admission: SolverAdmission,
    fixture: &str,
    mode: VampireMode,
    search_budget: VampireSearchBudget,
    extra: &[(&str, &Path)],
    policy: ProofCascPolicy,
) -> VampireRequest {
    let mut arguments = vec![
        OsString::from("--fixture"),
        OsString::from(fixture),
        OsString::from("--expect-start"),
        OsString::from("1"),
    ];
    for (name, value) in extra {
        arguments.push(OsString::from(name));
        arguments.push(value.as_os_str().to_owned());
    }
    let command = VampireWorkerCommand::new(support::fake_vampire())
        .with_extra_args(arguments)
        .unwrap()
        .with_proof_casc_policy(policy)
        .unwrap();
    VampireRequest::new(
        VampireProblem::new("fixture-entailment", problem(directory)),
        mode,
        command,
        store.clone(),
        admission,
        search_budget,
    )
    .unwrap()
}

fn agent_admission(slots: usize) -> SolverAdmission {
    create_general_solver_admission(RuntimeResourcePolicy::agent_only(slots, 2).unwrap()).unwrap()
}

// ------------------------------------------------------------
// Paired Result Arbitration
// ------------------------------------------------------------

#[cfg(any(target_os = "macos", target_os = "linux"))]
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn proof_winner_stops_and_reaps_the_fmb_tree() {
    let _process_guard = process_test_guard().await;
    let directory = support::TestDir::new("vampire_race_proof");
    let fmb_pid_path = directory.path().join("fmb.pid");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let outcome = run_vampire(
        request(
            &directory,
            &store,
            agent_admission(2),
            "race-proof-win",
            VampireMode::ProofAndFmb(FmbOptions::default()),
            Some(Duration::from_secs(8)),
            &[("--fmb-pid", &fmb_pid_path)],
        ),
        CancellationToken::new(),
    )
    .await;
    assert!(matches!(
        outcome,
        VampireInvocationOutcome::Result(VampireResult::Proved(_))
    ));
    let fmb_pid = read_pid(&fmb_pid_path).await;
    assert!(!process_exists(fmb_pid));
    owner.settle().unwrap();
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn model_winner_stops_and_reaps_the_proof_tree() {
    let _process_guard = process_test_guard().await;
    let directory = support::TestDir::new("vampire_race_model");
    let proof_pid_path = directory.path().join("proof.pid");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let outcome = run_vampire(
        request(
            &directory,
            &store,
            agent_admission(2),
            "race-model-win",
            VampireMode::ProofAndFmb(FmbOptions::default()),
            Some(Duration::from_secs(8)),
            &[("--proof-pid", &proof_pid_path)],
        ),
        CancellationToken::new(),
    )
    .await;
    assert!(matches!(
        outcome,
        VampireInvocationOutcome::Result(VampireResult::Refuted(_))
    ));
    let proof_pid = read_pid(&proof_pid_path).await;
    assert!(!process_exists(proof_pid));
    owner.settle().unwrap();
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn direct_proof_skips_the_configured_casc_tail() {
    let _process_guard = process_test_guard().await;
    let directory = support::TestDir::new("vampire_casc_direct_win");
    let launch_log = directory.path().join("launch.log");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let outcome = run_vampire(
        request_with_share(
            &directory,
            &store,
            agent_admission(2),
            "ladder-normal-proof",
            VampireMode::ProofAndFmb(FmbOptions::default()),
            Some(Duration::from_secs(2)),
            &[("--launch-log", &launch_log)],
            ProofCascShare::CLI_DEFAULT,
        ),
        CancellationToken::new(),
    )
    .await;
    let VampireInvocationOutcome::Result(VampireResult::Proved(proof)) = outcome else {
        panic!("direct proof should win")
    };
    assert_eq!(proof.strategy(), VampireProofStrategy::Direct);
    assert_eq!(proof.invocation().mode(), "proof_normal");
    // The direct stage states its own prefix, not the launch allowance:
    // `finite(2 s)` at the default shares reserves 0.5 s for the portfolio,
    // so the prefix is 1.5 s and the launch record says so.
    assert_eq!(proof.invocation().time_limit_deciseconds(), Some(15));
    assert_eq!(
        proof.invocation().executable(),
        fs::canonicalize(support::fake_vampire()).unwrap()
    );
    assert_eq!(proof.invocation().executable_sha256().len(), 64);
    assert!(
        proof
            .invocation()
            .executable_sha256()
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    );
    assert!(
        proof
            .invocation()
            .arguments()
            .windows(2)
            .any(|pair| pair == ["--proof", "tptp"])
    );
    assert!(
        !proof
            .invocation()
            .arguments()
            .iter()
            .any(|argument| argument == "--mode")
    );
    assert_eq!(launch_count(&launch_log), 2);
    owner.settle().unwrap();
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn direct_cutoff_reaps_normal_then_runs_casc_in_the_same_attempt() {
    let _process_guard = process_test_guard().await;
    let directory = support::TestDir::new("vampire_casc_cutoff");
    let normal_pid_path = directory.path().join("normal.pid");
    let launch_log = directory.path().join("launch.log");
    let maximum_limit = Path::new("5d");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let request = request_with_share(
        &directory,
        &store,
        agent_admission(2),
        "ladder-cutoff-casc-proof",
        VampireMode::ProofAndFmb(FmbOptions::default()),
        Some(Duration::from_secs(2)),
        &[
            ("--normal-proof-pid", &normal_pid_path),
            ("--launch-log", &launch_log),
            ("--max-casc-limit", maximum_limit),
        ],
        ProofCascShare::CLI_DEFAULT,
    );
    let attempt_id = request.attempt_id();
    let outcome = run_vampire(request, CancellationToken::new()).await;
    let VampireInvocationOutcome::Result(VampireResult::Proved(proof)) = outcome else {
        panic!("CASC proof should win after the direct cutoff")
    };
    assert_eq!(proof.strategy(), VampireProofStrategy::Casc2025);
    assert_eq!(proof.invocation().mode(), "proof_casc");
    assert_eq!(
        proof.invocation().executable(),
        fs::canonicalize(support::fake_vampire()).unwrap()
    );
    assert_eq!(proof.invocation().executable_sha256().len(), 64);
    assert!(proof.invocation().time_limit_deciseconds().is_some());
    assert!(
        proof
            .invocation()
            .arguments()
            .windows(2)
            .any(|pair| pair == ["--mode", "portfolio"])
    );
    assert_eq!(proof.attempt_id(), attempt_id);
    assert_eq!(launch_count(&launch_log), 3);
    assert!(!process_exists(read_pid(&normal_pid_path).await));
    owner.settle().unwrap();
}

/// The portfolio's own `--time_limit` is what the `casc_2025` schedule
/// scales every strategy slice by, so it decides which schedule runs, not
/// merely how long it runs for. It is therefore a pure function of the
/// launch's allocation: launches of the same allocation whose direct stages
/// take very different times, give up in different ways and cost very
/// different teardowns all produce a byte-identical portfolio argv.
#[cfg(any(target_os = "macos", target_os = "linux"))]
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn the_portfolio_argv_is_a_function_of_the_allocation_alone() {
    let _process_guard = process_test_guard().await;
    let directory = support::TestDir::new("vampire_casc_argv");
    let argv_log = directory.path().join("casc-argv.log");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    // cumulative(4 s, 16 s) at the command line's defaults: a 6 s direct
    // prefix and a 10 s nominal portfolio tail.
    let budget = VampireSearchBudget::cumulative(Duration::from_secs(4), Duration::from_secs(16));
    let run = |extra: Vec<(&'static str, &'static Path)>| {
        let mut arguments = vec![("--casc-argv-log", argv_log.as_path())];
        arguments.extend(extra);
        request_with_policy_and_budget(
            &directory,
            &store,
            agent_admission(1),
            "ladder-casc-argv",
            VampireMode::ProofOnly,
            budget,
            &arguments,
            ProofCascPolicy::CLI_DEFAULT,
        )
    };

    // Two direct stages that give up 2.5 s apart. Nothing about when they
    // returned may reach the portfolio.
    for delay in ["0", "2500"] {
        let outcome = run(vec![("--direct-delay-ms", Path::new(delay))]);
        let outcome = run_vampire(outcome, CancellationToken::new()).await;
        let VampireInvocationOutcome::Result(VampireResult::Proved(proof)) = outcome else {
            panic!("the portfolio stage should prove after a direct unknown")
        };
        assert_eq!(proof.strategy(), VampireProofStrategy::Casc2025);
    }
    // The same allocation reached by a prefix cutoff instead, whose direct
    // child ignores SIGTERM and so costs a much larger teardown.
    let outcome = run_vampire(
        run(vec![("--direct-hang", Path::new("1"))]),
        CancellationToken::new(),
    )
    .await;
    let VampireInvocationOutcome::Result(VampireResult::Proved(proof)) = outcome else {
        panic!("the portfolio stage should prove after a direct cutoff")
    };
    assert_eq!(proof.strategy(), VampireProofStrategy::Casc2025);

    let recorded = fs::read_to_string(&argv_log).unwrap();
    let launches: Vec<&str> = recorded.lines().collect();
    assert_eq!(launches.len(), 3, "{recorded}");
    assert!(
        launches.windows(2).all(|pair| pair[0] == pair[1]),
        "the portfolio argv moved with the direct stage's wall clock:\n{recorded}"
    );
    // The 10 s share the split reserved, stated exactly, in every case.
    assert!(
        launches[0].contains("--time_limit\u{1f}100d"),
        "{}",
        launches[0]
    );

    owner.settle().unwrap();
}

/// The finite-model lane is never split, so it outlives every proof-lane
/// stage: it states the launch's own outer deadline — the allowance plus
/// the runner's grace per proof stage — and never the bare allowance, which
/// would end it just as the portfolio took over.
#[cfg(any(target_os = "macos", target_os = "linux"))]
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn the_finite_model_lane_states_the_whole_launch_not_a_share_of_it() {
    let _process_guard = process_test_guard().await;
    let directory = support::TestDir::new("vampire_fmb_limit");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    // A 10 s allowance with the portfolio on: the proof lane may run two
    // stages, so the launch's outer deadline is 10 s + 2 × 2 s = 14 s, and
    // that is what the finite-model lane is told.
    let outcome = run_vampire(
        request_with_policy_and_budget(
            &directory,
            &store,
            agent_admission(2),
            "race-model-win",
            VampireMode::ProofAndFmb(FmbOptions::default()),
            VampireSearchBudget::finite(Duration::from_secs(10)),
            &[],
            ProofCascPolicy::CLI_DEFAULT,
        ),
        CancellationToken::new(),
    )
    .await;
    let VampireInvocationOutcome::Result(VampireResult::Refuted(model)) = outcome else {
        panic!("the finite-model lane should win this fixture: {outcome:?}")
    };
    assert_eq!(model.invocation().mode(), "fmb");
    assert_eq!(model.invocation().time_limit_deciseconds(), Some(140));
    owner.settle().unwrap();
}

/// The solver stopping itself at a limit it was given is this launch's
/// ordinary inconclusive end, not a fault: the same outcome the runner's
/// own backstop kill produces, so the key keeps its place on the retry
/// ladder. A nonzero exit that reports no such limit stays a process
/// failure.
#[cfg(any(target_os = "macos", target_os = "linux"))]
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_solver_that_stops_at_its_own_limit_is_a_timeout_not_a_process_failure() {
    let _process_guard = process_test_guard().await;
    let directory = support::TestDir::new("vampire_self_limit");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    for (fixture, expected) in [
        ("self-time-limit", FailureKind::CheckTimeout),
        ("self-memory-limit", FailureKind::CheckTimeout),
        ("nonzero-without-diagnostic", FailureKind::ProcessFailure),
    ] {
        let outcome = run_vampire(
            request(
                &directory,
                &store,
                agent_admission(1),
                fixture,
                VampireMode::FmbOnly(FmbOptions::default()),
                Some(Duration::from_secs(4)),
                &[],
            ),
            CancellationToken::new(),
        )
        .await;
        let VampireInvocationOutcome::Result(VampireResult::Failure { report, .. }) = outcome
        else {
            panic!("{fixture} should report its lane, not conclude: {outcome:?}")
        };
        assert_eq!(report.kind(), expected, "{fixture}");
        assert_eq!(report.origin(), FailureOrigin::VampireFiniteModelBuilding);
        assert_eq!(report.scope(), whiel_runner::FailureScope::LaneLocal);
    }
    owner.settle().unwrap();
}

/// A portfolio echoes every child strategy's own time-limit termination,
/// so a limit report in its stream says nothing about how the process this
/// runner started ended. Only the parent's own final report does — an SZS
/// status, which no child prints. A parent that dies after its children
/// have timed out prints none, and is the process failure it is.
#[cfg(any(target_os = "macos", target_os = "linux"))]
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_portfolio_that_dies_after_its_children_time_out_is_not_a_timeout() {
    let _process_guard = process_test_guard().await;
    let directory = support::TestDir::new("vampire_casc_children");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let budget = VampireSearchBudget::finite(Duration::from_secs(4));
    let run = |fixture: &'static str| {
        request_with_policy_and_budget(
            &directory,
            &store,
            agent_admission(1),
            fixture,
            VampireMode::ProofOnly,
            budget,
            &[],
            ProofCascPolicy::ONLY,
        )
    };

    // The parent reported for itself: this launch ran out of the time it
    // was given.
    let outcome = run_vampire(
        run("casc-children-then-own-timeout"),
        CancellationToken::new(),
    )
    .await;
    let VampireInvocationOutcome::Result(VampireResult::Failure { report, .. }) = outcome else {
        panic!("a portfolio that reports its own time limit is a lane timeout: {outcome:?}")
    };
    assert_eq!(report.kind(), FailureKind::CheckTimeout);

    // The parent said nothing of its own: whatever its children reported,
    // the process failed.
    let outcome = run_vampire(run("casc-children-then-crash"), CancellationToken::new()).await;
    let VampireInvocationOutcome::Result(VampireResult::Failure { report, .. }) = outcome else {
        panic!("a portfolio that dies is a process failure: {outcome:?}")
    };
    assert_eq!(report.kind(), FailureKind::ProcessFailure);

    // And a portfolio that proves after timed-out children still proves.
    let outcome = run_vampire(run("casc-children-then-proof"), CancellationToken::new()).await;
    let VampireInvocationOutcome::Result(VampireResult::Proved(proof)) = outcome else {
        panic!("a portfolio that proves after timed-out children proves: {outcome:?}")
    };
    assert_eq!(proof.strategy(), VampireProofStrategy::Casc2025);

    owner.settle().unwrap();
}

/// Output that does not parse is a fault of the launch whatever else it
/// contains. A truncated proof envelope followed by a time-limit line is
/// malformed, not an ordinary limit stop, and so never escalates into a
/// second stage that would hide it.
#[cfg(any(target_os = "macos", target_os = "linux"))]
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn malformed_output_keeps_its_precedence_over_a_limit_report() {
    let _process_guard = process_test_guard().await;
    let directory = support::TestDir::new("vampire_malformed_limit");
    let launch_log = directory.path().join("launch.log");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let outcome = run_vampire(
        request_with_policy_and_budget(
            &directory,
            &store,
            agent_admission(1),
            "self-time-limit-malformed",
            VampireMode::ProofOnly,
            VampireSearchBudget::cumulative(Duration::from_secs(1), Duration::from_secs(4)),
            &[("--launch-log", &launch_log)],
            ProofCascPolicy::CLI_DEFAULT,
        ),
        CancellationToken::new(),
    )
    .await;
    let VampireInvocationOutcome::Result(VampireResult::Failure { report, .. }) = outcome else {
        panic!("malformed output is a lane failure: {outcome:?}")
    };
    assert_eq!(report.kind(), FailureKind::MalformedResult);
    assert_eq!(
        launch_count(&launch_log),
        1,
        "malformed direct output must not escalate into the portfolio"
    );
    owner.settle().unwrap();
}

/// A direct stage that gives up before its prefix runs out does not hand
/// the portfolio the leftover: the portfolio is scheduled against the share
/// the split reserved for it, whenever it starts. The leftover is wall
/// clock, and a schedule scaled by wall clock is a different schedule every
/// run.
#[cfg(any(target_os = "macos", target_os = "linux"))]
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn early_unknown_still_gives_casc_exactly_its_own_share() {
    let _process_guard = process_test_guard().await;
    let directory = support::TestDir::new("vampire_casc_nominal_share");
    let launch_log = directory.path().join("launch.log");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let started = Instant::now();
    let outcome = run_vampire(
        request_with_policy_and_budget(
            &directory,
            &store,
            agent_admission(2),
            "ladder-unknown-casc-proof",
            VampireMode::ProofAndFmb(FmbOptions::default()),
            VampireSearchBudget::cumulative(Duration::from_secs(1), Duration::from_secs(3)),
            &[
                ("--launch-log", &launch_log),
                // cumulative(1 s, 3 s) with a 0.25 initial share and no
                // retry share: 0.25 s for the portfolio, 2.75 s of direct
                // prefix. The portfolio states 0.25 s however early direct
                // returned.
                ("--expect-casc-limit", Path::new("3d")),
            ],
            ProofCascPolicy::new(ProofCascShare::CLI_DEFAULT, ProofCascShare::DISABLED).unwrap(),
        ),
        CancellationToken::new(),
    )
    .await;
    let elapsed = started.elapsed();
    let VampireInvocationOutcome::Result(VampireResult::Proved(proof)) = outcome else {
        panic!("the portfolio should still run after an early direct unknown")
    };
    assert_eq!(proof.strategy(), VampireProofStrategy::Casc2025);
    assert_eq!(proof.invocation().time_limit_deciseconds(), Some(3));
    assert!(elapsed >= Duration::from_millis(850));
    assert_eq!(launch_count(&launch_log), 3);
    owner.settle().unwrap();
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn malformed_direct_output_does_not_escalate_to_casc() {
    let _process_guard = process_test_guard().await;
    let directory = support::TestDir::new("vampire_casc_malformed_stop");
    let launch_log = directory.path().join("launch.log");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let outcome = run_vampire(
        request_with_share(
            &directory,
            &store,
            agent_admission(2),
            "ladder-malformed-no-casc",
            VampireMode::ProofAndFmb(FmbOptions::default()),
            Some(Duration::from_millis(500)),
            &[("--launch-log", &launch_log)],
            ProofCascShare::CLI_DEFAULT,
        ),
        CancellationToken::new(),
    )
    .await;
    let VampireInvocationOutcome::Result(VampireResult::TimedOut {
        peer_failure: Some(peer_failure),
        ..
    }) = outcome
    else {
        panic!("FMB should retain the deadline after the hard proof failure")
    };
    assert_eq!(peer_failure.kind(), FailureKind::MalformedResult);
    assert_eq!(launch_count(&launch_log), 2);
    owner.settle().unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn direct_process_failure_does_not_escalate_to_casc() {
    let _process_guard = process_test_guard().await;
    let directory = support::TestDir::new("vampire_casc_process_stop");
    let launch_log = directory.path().join("launch.log");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let outcome = run_vampire(
        request_with_share(
            &directory,
            &store,
            agent_admission(1),
            "ladder-direct-process-failure",
            VampireMode::ProofOnly,
            Some(Duration::from_secs(2)),
            &[("--launch-log", &launch_log)],
            ProofCascShare::CLI_DEFAULT,
        ),
        CancellationToken::new(),
    )
    .await;
    let VampireInvocationOutcome::Result(VampireResult::Failure { report, .. }) = outcome else {
        panic!("a direct process failure should be returned without CASC")
    };
    assert_eq!(report.kind(), FailureKind::ProcessFailure);
    assert_eq!(launch_count(&launch_log), 1);
    owner.settle().unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn direct_and_casc_unknowns_are_combined_after_one_escalation() {
    let _process_guard = process_test_guard().await;
    let directory = support::TestDir::new("vampire_casc_both_unknown");
    let launch_log = directory.path().join("launch.log");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let outcome = run_vampire(
        request_with_share(
            &directory,
            &store,
            agent_admission(1),
            "ladder-both-proof-stages-unknown",
            VampireMode::ProofOnly,
            Some(Duration::from_secs(2)),
            &[("--launch-log", &launch_log)],
            ProofCascShare::CLI_DEFAULT,
        ),
        CancellationToken::new(),
    )
    .await;
    let VampireInvocationOutcome::Result(VampireResult::Failure { report, .. }) = outcome else {
        panic!("two clean solver misses should produce one proof-lane failure")
    };
    assert_eq!(report.kind(), FailureKind::SolverUnknown);
    let detail = report.detail().expect("both rung failures are summarized");
    assert!(detail.contains("direct proof stage"));
    assert!(detail.contains("CASC proof stage"));
    assert_eq!(launch_count(&launch_log), 2);
    owner.settle().unwrap();
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn fmb_keeps_its_full_deadline_across_the_proof_switch() {
    let _process_guard = process_test_guard().await;
    let directory = support::TestDir::new("vampire_casc_fmb_survives");
    let normal_pid_path = directory.path().join("normal.pid");
    let casc_pid_path = directory.path().join("casc.pid");
    let launch_log = directory.path().join("launch.log");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let outcome = run_vampire(
        request_with_policy_and_budget(
            &directory,
            &store,
            agent_admission(2),
            "ladder-fmb-survives-switch",
            VampireMode::ProofAndFmb(FmbOptions::default()),
            VampireSearchBudget::cumulative(Duration::from_secs(1), Duration::from_secs(3)),
            &[
                ("--normal-proof-pid", &normal_pid_path),
                ("--casc-proof-pid", &casc_pid_path),
                ("--launch-log", &launch_log),
            ],
            ProofCascPolicy::CLI_DEFAULT,
        ),
        CancellationToken::new(),
    )
    .await;
    assert!(matches!(
        outcome,
        VampireInvocationOutcome::Result(VampireResult::Refuted(_))
    ));
    assert_eq!(launch_count(&launch_log), 3);
    assert!(!process_exists(read_pid(&normal_pid_path).await));
    assert!(!process_exists(read_pid(&casc_pid_path).await));
    owner.settle().unwrap();
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn casc_only_control_skips_the_direct_process() {
    let _process_guard = process_test_guard().await;
    let directory = support::TestDir::new("vampire_casc_only");
    let launch_log = directory.path().join("launch.log");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let outcome = run_vampire(
        request_with_share(
            &directory,
            &store,
            agent_admission(1),
            "ladder-casc-only",
            VampireMode::ProofOnly,
            Some(Duration::from_secs(1)),
            &[("--launch-log", &launch_log)],
            ProofCascShare::ONLY,
        ),
        CancellationToken::new(),
    )
    .await;
    let VampireInvocationOutcome::Result(VampireResult::Proved(proof)) = outcome else {
        panic!("CASC-only proof should succeed")
    };
    assert_eq!(proof.strategy(), VampireProofStrategy::Casc2025);
    assert_eq!(launch_count(&launch_log), 1);
    owner.settle().unwrap();
}

#[test]
fn configured_casc_rejects_an_unbounded_proof_request() {
    let directory = support::TestDir::new("vampire_casc_unbounded");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let error = VampireRequest::new(
        VampireProblem::new("fixture-entailment", problem(&directory)),
        VampireMode::ProofOnly,
        VampireWorkerCommand::new(support::fake_vampire())
            .with_proof_casc_share(ProofCascShare::CLI_DEFAULT)
            .unwrap(),
        store,
        agent_admission(1),
        None,
    )
    .unwrap_err();
    assert!(matches!(error, VampireRequestError::UnboundedProofCasc));
    owner.settle().unwrap();
}

#[test]
fn configured_casc_rejects_a_limit_larger_than_vampire_can_parse() {
    let directory = support::TestDir::new("vampire_casc_limit_overflow");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let error = VampireRequest::new(
        VampireProblem::new("fixture-entailment", problem(&directory)),
        VampireMode::ProofOnly,
        VampireWorkerCommand::new(support::fake_vampire())
            .with_proof_casc_share(ProofCascShare::CLI_DEFAULT)
            .unwrap(),
        store,
        agent_admission(1),
        Some(Duration::MAX),
    )
    .unwrap_err();
    assert!(matches!(
        error,
        VampireRequestError::UnrepresentableProofCascLimit { .. }
    ));
    owner.settle().unwrap();
}

#[test]
fn retry_budget_rejects_zero_or_overlarge_initial_allowances() {
    let directory = support::TestDir::new("vampire_retry_budget_validation");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let make_request = |budget| {
        VampireRequest::new(
            VampireProblem::new("fixture-entailment", problem(&directory)),
            VampireMode::ProofOnly,
            VampireWorkerCommand::new(support::fake_vampire()),
            store.clone(),
            agent_admission(1),
            budget,
        )
    };

    assert!(matches!(
        make_request(VampireSearchBudget::cumulative(
            Duration::ZERO,
            Duration::from_secs(1),
        )),
        Err(VampireRequestError::ZeroInitialLimit),
    ));
    assert!(matches!(
        make_request(VampireSearchBudget::cumulative(
            Duration::from_secs(2),
            Duration::from_secs(1),
        )),
        Err(VampireRequestError::InitialLimitExceedsTotal { .. }),
    ));
    drop(store);
    owner.settle().unwrap();
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn cancellation_during_casc_reaps_casc_and_fmb_without_another_rung() {
    let _process_guard = process_test_guard().await;
    let directory = support::TestDir::new("vampire_casc_cancel");
    let casc_pid_path = directory.path().join("casc.pid");
    let fmb_pid_path = directory.path().join("fmb.pid");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let cancellation = CancellationToken::new();
    let run_cancellation = cancellation.clone();
    let run = tokio::spawn(run_vampire(
        request_with_share(
            &directory,
            &store,
            agent_admission(2),
            "ladder-both-proof-stages-hang",
            VampireMode::ProofAndFmb(FmbOptions::default()),
            Some(Duration::from_secs(5)),
            &[
                ("--casc-proof-pid", &casc_pid_path),
                ("--fmb-pid", &fmb_pid_path),
            ],
            ProofCascShare::ONLY,
        ),
        run_cancellation,
    ));
    let casc_pid = read_pid(&casc_pid_path).await;
    let fmb_pid = read_pid(&fmb_pid_path).await;
    cancellation.cancel();
    assert!(matches!(
        run.await.unwrap(),
        VampireInvocationOutcome::Cancelled(_)
    ));
    assert!(!process_exists(casc_pid));
    assert!(!process_exists(fmb_pid));
    owner.settle().unwrap();
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn cancellation_during_the_direct_prefix_never_launches_casc() {
    let _process_guard = process_test_guard().await;
    let directory = support::TestDir::new("vampire_casc_cancel_direct");
    let normal_pid_path = directory.path().join("normal.pid");
    let fmb_pid_path = directory.path().join("fmb.pid");
    let launch_log = directory.path().join("launch.log");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let cancellation = CancellationToken::new();
    let run = tokio::spawn(run_vampire(
        request_with_share(
            &directory,
            &store,
            agent_admission(2),
            "ladder-both-proof-stages-hang",
            VampireMode::ProofAndFmb(FmbOptions::default()),
            Some(Duration::from_secs(5)),
            &[
                ("--normal-proof-pid", &normal_pid_path),
                ("--fmb-pid", &fmb_pid_path),
                ("--launch-log", &launch_log),
            ],
            ProofCascShare::CLI_DEFAULT,
        ),
        cancellation.clone(),
    ));
    let normal_pid = read_pid(&normal_pid_path).await;
    let fmb_pid = read_pid(&fmb_pid_path).await;
    cancellation.cancel();
    assert!(matches!(
        run.await.unwrap(),
        VampireInvocationOutcome::Cancelled(_)
    ));
    assert_eq!(launch_count(&launch_log), 2);
    assert!(!process_exists(normal_pid));
    assert!(!process_exists(fmb_pid));
    owner.settle().unwrap();
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn both_proof_rungs_share_one_deadline_and_reap_all_processes() {
    let _process_guard = process_test_guard().await;
    let directory = support::TestDir::new("vampire_casc_two_rung_timeout");
    let normal_pid_path = directory.path().join("normal.pid");
    let casc_pid_path = directory.path().join("casc.pid");
    let fmb_pid_path = directory.path().join("fmb.pid");
    let launch_log = directory.path().join("launch.log");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let outcome = run_vampire(
        request_with_share(
            &directory,
            &store,
            agent_admission(2),
            "ladder-both-proof-stages-hang",
            VampireMode::ProofAndFmb(FmbOptions::default()),
            Some(Duration::from_secs(4)),
            &[
                ("--normal-proof-pid", &normal_pid_path),
                ("--casc-proof-pid", &casc_pid_path),
                ("--fmb-pid", &fmb_pid_path),
                ("--launch-log", &launch_log),
            ],
            ProofCascShare::from_millionths(500_000).unwrap(),
        ),
        CancellationToken::new(),
    )
    .await;
    assert!(matches!(
        outcome,
        VampireInvocationOutcome::Result(VampireResult::TimedOut { .. })
    ));
    assert_eq!(launch_count(&launch_log), 3);
    for path in [&normal_pid_path, &casc_pid_path, &fmb_pid_path] {
        assert!(!process_exists(read_pid(path).await));
    }
    owner.settle().unwrap();
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn interrupted_casc_retains_the_direct_unknown_and_both_stage_captures() {
    let _process_guard = process_test_guard().await;
    let directory = support::TestDir::new("vampire_casc_prior_failure");
    let casc_pid_path = directory.path().join("casc.pid");
    let fmb_pid_path = directory.path().join("fmb.pid");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let cancellation = CancellationToken::new();
    let request = request_with_share(
        &directory,
        &store,
        agent_admission(2),
        "ladder-unknown-casc-hang",
        VampireMode::ProofAndFmb(FmbOptions::default()),
        Some(Duration::from_secs(5)),
        &[
            ("--casc-proof-pid", &casc_pid_path),
            ("--fmb-pid", &fmb_pid_path),
        ],
        ProofCascShare::CLI_DEFAULT,
    )
    .with_capture_policy(VampireCapturePolicy::default().retain_full_inconclusive_output(true));
    let run = tokio::spawn(run_vampire(request, cancellation.clone()));
    let casc_pid = read_pid(&casc_pid_path).await;
    let fmb_pid = read_pid(&fmb_pid_path).await;
    cancellation.cancel();
    let VampireInvocationOutcome::Cancelled(cancelled) = run.await.unwrap() else {
        panic!("overall cancellation should remain control flow")
    };
    let prior = cancelled
        .peer_failure()
        .expect("the direct unknown must survive CASC interruption");
    assert_eq!(prior.kind(), FailureKind::SolverUnknown);
    assert!(!prior.artifact_references().is_empty());
    for reference in prior.artifact_references() {
        assert!(cancelled.artifact_references().contains(reference));
    }
    assert!(cancelled.artifact_references().len() >= 3);
    assert!(!process_exists(casc_pid));
    assert!(!process_exists(fmb_pid));
    owner.settle().unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn one_worker_failure_does_not_stop_a_conclusive_peer() {
    let _process_guard = process_test_guard().await;
    for (fixture, expected_refuted) in [
        ("race-proof-failure-model", true),
        ("race-fmb-failure-proof", false),
    ] {
        let directory = support::TestDir::new(fixture);
        let task = support::sample_task();
        let (owner, store) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(directory.path().join("artifacts")),
        )
        .unwrap();
        let outcome = run_vampire(
            request(
                &directory,
                &store,
                agent_admission(2),
                fixture,
                VampireMode::ProofAndFmb(FmbOptions::default()),
                Some(Duration::from_secs(8)),
                &[],
            ),
            CancellationToken::new(),
        )
        .await;
        assert_eq!(
            matches!(
                outcome,
                VampireInvocationOutcome::Result(VampireResult::Refuted(_))
            ),
            expected_refuted
        );
        owner.settle().unwrap();
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn installed_vampire_paired_and_casc_smoke_test_when_available() {
    let _process_guard = process_test_guard().await;
    let executable = std::env::var_os("VAMPIRE_BIN")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("/opt/vampire/build/vampire"));
    if !executable.is_file() {
        return;
    }

    let directory = support::TestDir::new("installed_vampire_race");
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
    let admission = agent_admission(2);

    let proof = run_vampire(
        VampireRequest::new(
            VampireProblem::new("real-paired-proof", proof_problem.clone()),
            VampireMode::ProofAndFmb(FmbOptions::default()),
            VampireWorkerCommand::new(&executable),
            store.clone(),
            admission.clone(),
            Some(Duration::from_secs(10)),
        )
        .unwrap(),
        CancellationToken::new(),
    )
    .await;
    let casc_proof = run_vampire(
        VampireRequest::new(
            VampireProblem::new("real-casc-proof", proof_problem),
            VampireMode::ProofOnly,
            VampireWorkerCommand::new(&executable)
                .with_proof_casc_share(ProofCascShare::ONLY)
                .unwrap(),
            store.clone(),
            admission.clone(),
            Some(Duration::from_secs(10)),
        )
        .unwrap(),
        CancellationToken::new(),
    )
    .await;
    let model = run_vampire(
        VampireRequest::new(
            VampireProblem::new("real-paired-model", model_problem),
            VampireMode::ProofAndFmb(FmbOptions::default()),
            VampireWorkerCommand::new(executable),
            store.clone(),
            admission,
            Some(Duration::from_secs(10)),
        )
        .unwrap(),
        CancellationToken::new(),
    )
    .await;

    let VampireInvocationOutcome::Result(VampireResult::Proved(proof)) = proof else {
        panic!("unexpected real paired proof outcome: {proof:#?}")
    };
    let VampireInvocationOutcome::Result(VampireResult::Refuted(model)) = model else {
        panic!("unexpected real paired model outcome: {model:#?}")
    };
    let VampireInvocationOutcome::Result(VampireResult::Proved(casc_proof)) = casc_proof else {
        panic!("unexpected real CASC proof outcome: {casc_proof:#?}")
    };
    assert_eq!(casc_proof.strategy(), VampireProofStrategy::Casc2025);
    assert_eq!(
        store.resolve(proof.output()).unwrap().kind(),
        whiel_runner::ArtifactKind::Proof
    );
    assert_eq!(
        store.resolve(model.output()).unwrap().kind(),
        whiel_runner::ArtifactKind::Model
    );
    assert_eq!(
        store.resolve(casc_proof.output()).unwrap().kind(),
        whiel_runner::ArtifactKind::Proof
    );
    assert!(store.diagnostics().required_payloads_published >= 3);
    owner.settle().unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn dual_failure_preserves_both_contexts_and_the_fmb_frontier() {
    let _process_guard = process_test_guard().await;
    let directory = support::TestDir::new("vampire_race_dual_failure");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let request = request(
        &directory,
        &store,
        agent_admission(2),
        "race-dual-failure",
        VampireMode::ProofAndFmb(FmbOptions::default()),
        Some(Duration::from_secs(8)),
        &[],
    );
    let attempt = request.attempt_id();
    let outcome = run_vampire(request, CancellationToken::new()).await;
    let VampireInvocationOutcome::Result(VampireResult::Failure {
        report,
        next_fmb_start_size,
    }) = outcome
    else {
        panic!("expected a combined failure")
    };
    assert_eq!(report.origin(), FailureOrigin::VampireRace);
    assert_eq!(report.kind(), FailureKind::ConcurrentWorkerFailures);
    assert_eq!(next_fmb_start_size, FmbSize::new(13));
    let detail = report.detail().unwrap();
    assert!(detail.contains("proof worker"));
    assert!(detail.contains("FMB worker"));
    assert_eq!(report.artifact_references().len(), 2);
    let attempt_scope = format!("entailment-attempt:{}", attempt.get());
    for reference in report.artifact_references() {
        assert!(
            store
                .resolve(*reference)
                .unwrap()
                .scope()
                .iter()
                .any(|scope| scope == &attempt_scope)
        );
    }
    owner.settle().unwrap();
}

// ------------------------------------------------------------
// Deadline And Interruption Semantics
// ------------------------------------------------------------

#[cfg(any(target_os = "macos", target_os = "linux"))]
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn local_timeout_retains_frontier_and_reaps_both_workers() {
    let _process_guard = process_test_guard().await;
    let directory = support::TestDir::new("vampire_race_timeout");
    let proof_pid_path = directory.path().join("proof.pid");
    let fmb_pid_path = directory.path().join("fmb.pid");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let outcome = run_vampire(
        request(
            &directory,
            &store,
            agent_admission(2),
            "race-timeout",
            VampireMode::ProofAndFmb(FmbOptions::default()),
            Some(Duration::from_secs(2)),
            &[
                ("--proof-pid", &proof_pid_path),
                ("--fmb-pid", &fmb_pid_path),
            ],
        ),
        CancellationToken::new(),
    )
    .await;
    let VampireInvocationOutcome::Result(VampireResult::TimedOut {
        next_fmb_start_size,
        peer_failure,
    }) = outcome
    else {
        panic!("expected local timeout")
    };
    assert_eq!(next_fmb_start_size, FmbSize::new(1));
    assert!(peer_failure.is_none());
    assert!(!process_exists(read_pid(&proof_pid_path).await));
    assert!(!process_exists(read_pid(&fmb_pid_path).await));
    assert_eq!(store.diagnostics().required_payloads_published, 1);
    let run_root = fs::read_dir(directory.path().join("artifacts"))
        .unwrap()
        .next()
        .unwrap()
        .unwrap()
        .path();
    let artifact = fs::read_dir(run_root.join("required"))
        .unwrap()
        .next()
        .unwrap()
        .unwrap()
        .path();
    assert!(
        fs::read_to_string(artifact)
            .unwrap()
            .contains("vampire_timeout")
    );
    owner.settle().unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn timeout_preserves_an_earlier_peer_failure() {
    let _process_guard = process_test_guard().await;
    let directory = support::TestDir::new("vampire_race_peer_failure");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let outcome = run_vampire(
        request(
            &directory,
            &store,
            agent_admission(2),
            "race-proof-failure-fmb-hang",
            VampireMode::ProofAndFmb(FmbOptions::default()),
            Some(Duration::from_secs(1)),
            &[],
        ),
        CancellationToken::new(),
    )
    .await;
    let VampireInvocationOutcome::Result(VampireResult::TimedOut {
        next_fmb_start_size,
        peer_failure: Some(peer_failure),
    }) = outcome
    else {
        panic!("expected a timeout with peer failure")
    };
    assert_eq!(next_fmb_start_size, FmbSize::new(1));
    assert_eq!(peer_failure.origin(), FailureOrigin::VampireProofSearch);
    owner.settle().unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn fmb_only_timeout_retains_its_safe_restart_frontier() {
    let _process_guard = process_test_guard().await;
    let directory = support::TestDir::new("vampire_fmb_only_timeout");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let outcome = run_vampire(
        request(
            &directory,
            &store,
            agent_admission(1),
            "hang-fmb-frontier",
            VampireMode::FmbOnly(FmbOptions::default()),
            Some(Duration::from_millis(500)),
            &[],
        ),
        CancellationToken::new(),
    )
    .await;
    let VampireInvocationOutcome::Result(VampireResult::TimedOut {
        next_fmb_start_size,
        peer_failure,
    }) = outcome
    else {
        panic!("expected FMB-only timeout")
    };
    assert_eq!(next_fmb_start_size, FmbSize::new(1));
    assert!(peer_failure.is_none());
    owner.settle().unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn an_unrepresentably_large_local_limit_does_not_panic() {
    let _process_guard = process_test_guard().await;
    let directory = support::TestDir::new("vampire_huge_local_limit");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let outcome = run_vampire(
        request(
            &directory,
            &store,
            agent_admission(1),
            "proof",
            VampireMode::ProofOnly,
            Some(Duration::MAX),
            &[],
        ),
        CancellationToken::new(),
    )
    .await;
    assert!(matches!(
        outcome,
        VampireInvocationOutcome::Result(VampireResult::Proved(_))
    ));
    owner.settle().unwrap();
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn overall_cancellation_is_not_a_local_timeout() {
    let _process_guard = process_test_guard().await;
    let directory = support::TestDir::new("vampire_race_cancel");
    let proof_pid_path = directory.path().join("proof.pid");
    let fmb_pid_path = directory.path().join("fmb.pid");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let cancellation = CancellationToken::new();
    let run_cancellation = cancellation.clone();
    let run = tokio::spawn(run_vampire(
        request(
            &directory,
            &store,
            agent_admission(2),
            "race-timeout",
            VampireMode::ProofAndFmb(FmbOptions::default()),
            None,
            &[
                ("--proof-pid", &proof_pid_path),
                ("--fmb-pid", &fmb_pid_path),
            ],
        ),
        run_cancellation,
    ));
    let proof_pid = read_pid(&proof_pid_path).await;
    let fmb_pid = read_pid(&fmb_pid_path).await;
    cancellation.cancel();
    let outcome = run.await.unwrap();
    let VampireInvocationOutcome::Cancelled(cancelled) = outcome else {
        panic!("overall cancellation was misclassified")
    };
    assert_eq!(cancelled.next_fmb_start_size(), FmbSize::new(1));
    assert!(!process_exists(proof_pid));
    assert!(!process_exists(fmb_pid));
    owner.settle().unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn preexisting_overall_cancellation_launches_no_local_attempt() {
    let directory = support::TestDir::new("vampire_deadline_tie");
    let launch_log = directory.path().join("launch.log");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let cancellation = CancellationToken::new();
    cancellation.cancel();

    let outcome = run_vampire(
        request(
            &directory,
            &store,
            agent_admission(1),
            "proof",
            VampireMode::ProofOnly,
            Some(Duration::from_nanos(1)),
            &[("--launch-log", &launch_log)],
        ),
        cancellation,
    )
    .await;
    assert!(matches!(outcome, VampireInvocationOutcome::Cancelled(_)));
    assert_eq!(launch_count(&launch_log), 0);
    owner.settle().unwrap();
}

// ------------------------------------------------------------
// Admission And Queue Timing
// ------------------------------------------------------------

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn local_limit_starts_after_atomic_pair_admission() {
    let _process_guard = process_test_guard().await;
    let directory = support::TestDir::new("vampire_race_queued_local");
    let holder_pid_path = directory.path().join("holder.pid");
    let launch_log = directory.path().join("launch.log");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let admission = agent_admission(2);
    let holder_cancellation = CancellationToken::new();
    let holder_run_cancellation = holder_cancellation.clone();
    let holder = tokio::spawn(run_vampire(
        request(
            &directory,
            &store,
            admission.clone(),
            "hang-proof",
            VampireMode::ProofOnly,
            None,
            &[
                ("--proof-pid", &holder_pid_path),
                ("--launch-log", &launch_log),
            ],
        ),
        holder_run_cancellation,
    ));
    read_pid(&holder_pid_path).await;

    let queued = tokio::spawn(run_vampire(
        request(
            &directory,
            &store,
            admission,
            "race-proof-fast",
            VampireMode::ProofAndFmb(FmbOptions::default()),
            Some(Duration::from_millis(150)),
            &[("--launch-log", &launch_log)],
        ),
        CancellationToken::new(),
    ));
    tokio::time::sleep(Duration::from_millis(250)).await;
    assert_eq!(launch_count(&launch_log), 1);

    holder_cancellation.cancel();
    assert!(matches!(
        holder.await.unwrap(),
        VampireInvocationOutcome::Cancelled(_)
    ));
    assert!(matches!(
        queued.await.unwrap(),
        VampireInvocationOutcome::Result(VampireResult::Proved(_))
    ));
    owner.settle().unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn queued_cancellation_launches_no_partial_pair() {
    let _process_guard = process_test_guard().await;
    let directory = support::TestDir::new("vampire_race_queued_cancel");
    let holder_pid_path = directory.path().join("holder.pid");
    let launch_log = directory.path().join("launch.log");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let admission = agent_admission(2);
    let holder_cancellation = CancellationToken::new();
    let holder_run_cancellation = holder_cancellation.clone();
    let holder = tokio::spawn(run_vampire(
        request(
            &directory,
            &store,
            admission.clone(),
            "hang-proof",
            VampireMode::ProofOnly,
            None,
            &[
                ("--proof-pid", &holder_pid_path),
                ("--launch-log", &launch_log),
            ],
        ),
        holder_run_cancellation,
    ));
    read_pid(&holder_pid_path).await;

    let queued_cancellation = CancellationToken::new();
    let run_cancellation = queued_cancellation.clone();
    let queued = tokio::spawn(run_vampire(
        request(
            &directory,
            &store,
            admission,
            "race-proof-fast",
            VampireMode::ProofAndFmb(FmbOptions::default()),
            Some(Duration::from_secs(1)),
            &[("--launch-log", &launch_log)],
        ),
        run_cancellation,
    ));
    tokio::time::sleep(Duration::from_millis(50)).await;
    queued_cancellation.cancel();
    assert!(matches!(
        queued.await.unwrap(),
        VampireInvocationOutcome::Cancelled(_)
    ));
    assert_eq!(launch_count(&launch_log), 1);

    holder_cancellation.cancel();
    assert!(matches!(
        holder.await.unwrap(),
        VampireInvocationOutcome::Cancelled(_)
    ));
    owner.settle().unwrap();
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn fatal_timeout_publication_closes_admission_before_capacity_can_escape() {
    let _process_guard = process_test_guard().await;
    let directory = support::TestDir::new("vampire_race_timeout_publication");
    let proof_pid_path = directory.path().join("proof.pid");
    let fmb_pid_path = directory.path().join("fmb.pid");
    let launch_log = directory.path().join("launch.log");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let admission = agent_admission(2);
    let first = tokio::spawn(run_vampire(
        request(
            &directory,
            &store,
            admission.clone(),
            "race-timeout",
            VampireMode::ProofAndFmb(FmbOptions::default()),
            Some(Duration::from_secs(2)),
            &[
                ("--proof-pid", &proof_pid_path),
                ("--fmb-pid", &fmb_pid_path),
                ("--launch-log", &launch_log),
            ],
        ),
        CancellationToken::new(),
    ));
    read_pid(&proof_pid_path).await;
    read_pid(&fmb_pid_path).await;
    assert_eq!(launch_count(&launch_log), 2);

    let queued = tokio::spawn(run_vampire(
        request(
            &directory,
            &store,
            admission,
            "proof",
            VampireMode::ProofOnly,
            Some(Duration::from_secs(2)),
            &[("--launch-log", &launch_log)],
        ),
        CancellationToken::new(),
    ));
    tokio::time::sleep(Duration::from_millis(20)).await;
    assert_eq!(launch_count(&launch_log), 2);

    // This intentionally violates the entry-wrapper settlement order. It
    // forces required timeout publication to return a truthful RunGlobal
    // artifact failure and tests that admission closes before its pair lease
    // could otherwise wake the queued request.
    let settlement_failure = owner.settle().unwrap_err();
    assert_eq!(
        settlement_failure.scope(),
        whiel_runner::FailureScope::RunGlobal
    );

    let VampireInvocationOutcome::RunFailure(first_failure) = first.await.unwrap() else {
        panic!("required timeout-publication failure must stop the run")
    };
    let VampireInvocationOutcome::RunFailure(queued_failure) = queued.await.unwrap() else {
        panic!("queued work must receive the same admission-closing failure")
    };
    assert_eq!(first_failure.origin(), FailureOrigin::ArtifactSettlement);
    assert_eq!(queued_failure.origin(), first_failure.origin());
    assert_eq!(queued_failure.kind(), first_failure.kind());
    assert_eq!(launch_count(&launch_log), 2);
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn dropped_supervisor_during_casc_holds_capacity_through_cleanup() {
    let _process_guard = process_test_guard().await;
    let directory = support::TestDir::new("vampire_race_dropped_supervisor");
    let casc_pid_path = directory.path().join("casc.pid");
    let fmb_pid_path = directory.path().join("fmb.pid");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let admission = agent_admission(2);
    let abandoned = tokio::spawn(run_vampire(
        request_with_share(
            &directory,
            &store,
            admission.clone(),
            "ladder-both-proof-stages-hang",
            VampireMode::ProofAndFmb(FmbOptions::default()),
            Some(Duration::from_secs(5)),
            &[
                ("--casc-proof-pid", &casc_pid_path),
                ("--fmb-pid", &fmb_pid_path),
            ],
            ProofCascShare::ONLY,
        ),
        CancellationToken::new(),
    ));
    let casc_pid = read_pid(&casc_pid_path).await;
    let fmb_pid = read_pid(&fmb_pid_path).await;
    abandoned.abort();
    assert!(abandoned.await.unwrap_err().is_cancelled());

    let successor = tokio::time::timeout(
        Duration::from_secs(8),
        run_vampire(
            request(
                &directory,
                &store,
                admission,
                "race-proof-fast",
                VampireMode::ProofAndFmb(FmbOptions::default()),
                Some(Duration::from_secs(5)),
                &[],
            ),
            CancellationToken::new(),
        ),
    )
    .await
    .expect("capacity must return after abandoned workers finish cleanup");
    assert!(
        matches!(
            &successor,
            VampireInvocationOutcome::Result(VampireResult::Proved(_))
        ),
        "unexpected successor outcome: {successor:?}"
    );
    assert!(!process_exists(casc_pid));
    assert!(!process_exists(fmb_pid));
    owner.settle().unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn one_slot_agent_profile_runs_proof_then_fmb_in_one_attempt() {
    let _process_guard = process_test_guard().await;
    let directory = support::TestDir::new("vampire_race_one_slot");
    let order_log = directory.path().join("serial-order.log");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let request = request(
        &directory,
        &store,
        agent_admission(1),
        "race-proof-failure-model",
        VampireMode::ProofAndFmb(FmbOptions::default()),
        Some(Duration::from_secs(1)),
        &[("--serial-order-log", &order_log)],
    );
    let attempt = request.attempt_id();
    let outcome = run_vampire(request, CancellationToken::new()).await;
    let VampireInvocationOutcome::Result(VampireResult::Refuted(model)) = outcome else {
        panic!("the serial FMB contour should find the fixture model")
    };
    assert_eq!(model.attempt_id(), attempt);
    assert_eq!(fs::read_to_string(order_log).unwrap(), "direct\nfmb\n");
    owner.settle().unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn one_slot_agent_profile_stops_after_a_direct_proof() {
    let _process_guard = process_test_guard().await;
    let directory = support::TestDir::new("vampire_race_one_slot_proof");
    let order_log = directory.path().join("serial-order.log");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let outcome = run_vampire(
        request(
            &directory,
            &store,
            agent_admission(1),
            "race-fmb-failure-proof",
            VampireMode::ProofAndFmb(FmbOptions::default()),
            Some(Duration::from_secs(1)),
            &[("--serial-order-log", &order_log)],
        ),
        CancellationToken::new(),
    )
    .await;
    assert!(matches!(
        outcome,
        VampireInvocationOutcome::Result(VampireResult::Proved(_))
    ));
    assert_eq!(fs::read_to_string(order_log).unwrap(), "direct\n");
    owner.settle().unwrap();
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn one_slot_agent_profile_cancels_and_reaps_the_serial_fmb_stage() {
    let _process_guard = process_test_guard().await;
    let directory = support::TestDir::new("vampire_race_one_slot_cancel");
    let order_log = directory.path().join("serial-order.log");
    let fmb_pid_path = directory.path().join("fmb.pid");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let cancellation = CancellationToken::new();
    let run = tokio::spawn(run_vampire(
        request(
            &directory,
            &store,
            agent_admission(1),
            "race-proof-failure-fmb-hang",
            VampireMode::ProofAndFmb(FmbOptions::default()),
            Some(Duration::from_secs(5)),
            &[
                ("--serial-order-log", &order_log),
                ("--fmb-pid", &fmb_pid_path),
            ],
        ),
        cancellation.clone(),
    ));
    let fmb_pid = read_pid(&fmb_pid_path).await;
    cancellation.cancel();
    assert!(matches!(
        run.await.unwrap(),
        VampireInvocationOutcome::Cancelled(_)
    ));
    assert!(!process_exists(fmb_pid));
    assert_eq!(fs::read_to_string(order_log).unwrap(), "direct\nfmb\n");
    owner.settle().unwrap();
}

#[test]
fn one_slot_agent_profile_rejects_an_unbounded_pair() {
    let directory = support::TestDir::new("vampire_race_one_slot_unbounded");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let error = VampireRequest::new(
        VampireProblem::new("fixture-entailment", problem(&directory)),
        VampireMode::ProofAndFmb(FmbOptions::default()),
        VampireWorkerCommand::new(support::fake_vampire()),
        store,
        agent_admission(1),
        None,
    )
    .unwrap_err();
    assert!(matches!(error, VampireRequestError::UnboundedSerialPair));
    owner.settle().unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn run_global_worker_failure_closes_shared_admission() {
    let _process_guard = process_test_guard().await;
    let first_directory = support::TestDir::new("vampire_poison_first");
    let task = support::sample_task();
    let (first_owner, first_store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(first_directory.path().join("artifacts")),
    )
    .unwrap();
    let admission = agent_admission(1);
    let first = request(
        &first_directory,
        &first_store,
        admission.clone(),
        "proof",
        VampireMode::ProofOnly,
        Some(Duration::from_secs(1)),
        &[],
    );
    first_owner.settle().unwrap();
    let VampireInvocationOutcome::RunFailure(first_failure) =
        run_vampire(first, CancellationToken::new()).await
    else {
        panic!("the settled artifact backend must fail the run")
    };
    assert_eq!(first_failure.origin(), FailureOrigin::ArtifactSettlement);

    let second_directory = support::TestDir::new("vampire_poison_second");
    let (second_owner, second_store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(second_directory.path().join("artifacts")),
    )
    .unwrap();
    let second = request(
        &second_directory,
        &second_store,
        admission,
        "proof",
        VampireMode::ProofOnly,
        Some(Duration::from_secs(1)),
        &[],
    );
    let VampireInvocationOutcome::RunFailure(second_failure) =
        run_vampire(second, CancellationToken::new()).await
    else {
        panic!("closed admission must reject later work")
    };
    assert_eq!(second_failure.origin(), FailureOrigin::ArtifactSettlement);
    assert_eq!(second_failure.kind(), first_failure.kind());
    second_owner.settle().unwrap();
}

// ------------------------------------------------------------
// Process Inspection Helpers
// ------------------------------------------------------------

async fn read_pid(path: &Path) -> u32 {
    tokio::time::timeout(Duration::from_secs(10), async {
        loop {
            if let Ok(value) = fs::read_to_string(path)
                && let Ok(pid) = value.trim().parse()
            {
                return pid;
            }
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    })
    .await
    .unwrap_or_else(|_| panic!("PID file was not written: {}", path.display()))
}

async fn process_test_guard() -> tokio::sync::OwnedSemaphorePermit {
    static PROCESS_TESTS: OnceLock<Arc<tokio::sync::Semaphore>> = OnceLock::new();
    Arc::clone(PROCESS_TESTS.get_or_init(|| Arc::new(tokio::sync::Semaphore::new(1))))
        .acquire_owned()
        .await
        .expect("the process-test semaphore is never closed")
}

fn launch_count(path: &Path) -> usize {
    fs::read_to_string(path).unwrap_or_default().lines().count()
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

// ------------------------------------------------------------
// Real Pinned Solver: Escalation Inside One Launch
// ------------------------------------------------------------

/// One launch, the repository-pinned solver, and a real obligation the
/// direct strategy does not reach.
///
/// `tests/fixtures/casc_escalation_maintenance_problem.p` is one
/// maintenance obligation of a candidate invariant for a current Benchmark
/// input, emitted by the ordinary certificate path. The direct strategy
/// saturates on it without a refutation for minutes; the `casc_2025`
/// portfolio refutes it in well under a second. That is what the
/// escalation buys: the two are different searches, not a slow and a fast
/// route to the same one.
///
/// The launch runs under `cumulative(4 s, 16 s)` and the command line's
/// default shares, so the direct prefix is 6 s and the portfolio inherits
/// the remaining 10 s. Both figures carry an order of magnitude of margin
/// over what the two strategies need, so the test states a capability
/// rather than a race.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn the_pinned_portfolio_proves_what_the_direct_prefix_cannot_in_one_launch() {
    let _process_guard = process_test_guard().await;
    let repository_root = support::repository_root();
    let pinned = PinnedLeancheckVampire::from_lock(&repository_root)
        .expect("the repository-pinned leancheck Vampire resolves");
    let directory = support::TestDir::new("vampire_race_real_casc_escalation");
    let obligation = directory.path().join("obligation.p");
    fs::copy(
        repository_root.join("whiel_runner/tests/fixtures/casc_escalation_maintenance_problem.p"),
        &obligation,
    )
    .unwrap();
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let admission = agent_admission(1);

    let escalating = run_vampire(
        VampireRequest::new(
            VampireProblem::new("real-casc-escalation", obligation.clone()),
            VampireMode::ProofOnly,
            VampireWorkerCommand::new(pinned.path())
                .with_proof_casc_policy(ProofCascPolicy::CLI_DEFAULT)
                .unwrap(),
            store.clone(),
            admission.clone(),
            VampireSearchBudget::cumulative(Duration::from_secs(4), Duration::from_secs(16)),
        )
        .unwrap(),
        CancellationToken::new(),
    )
    .await;
    let VampireInvocationOutcome::Result(VampireResult::Proved(proof)) = &escalating else {
        panic!("the portfolio share did not prove the obligation: {escalating:?}");
    };
    assert_eq!(
        proof.strategy(),
        VampireProofStrategy::Casc2025,
        "the proof came from the portfolio stage, not the direct prefix"
    );

    // The control: the same solver on the same problem under the direct
    // prefix alone reaches nothing, so the proof above is the escalation's
    // and not the allowance's.
    let direct_only = run_vampire(
        VampireRequest::new(
            VampireProblem::new("real-direct-only", obligation),
            VampireMode::ProofOnly,
            VampireWorkerCommand::new(pinned.path()),
            store.clone(),
            admission,
            VampireSearchBudget::finite(Duration::from_secs(6)),
        )
        .unwrap(),
        CancellationToken::new(),
    )
    .await;
    assert!(
        !matches!(
            direct_only,
            VampireInvocationOutcome::Result(VampireResult::Proved(_))
        ),
        "the direct strategy proved the obligation inside its own prefix: {direct_only:?}"
    );

    owner.settle().unwrap();
}

// ------------------------------------------------------------
// Real Pinned Solver: The Premise Role A Retry Renders Under
// ------------------------------------------------------------

/// One search-time check, the repository-pinned solver, and the two
/// renderings of the very same problem.
///
/// `tests/fixtures/goal_tagged_retry_problem.p` is one clause check of a
/// known-correct invariant for `Benchmark/Example5034`: a step
/// (maintenance) obligation, so it carries that input's prophecy relations
/// beside the original ones, with 21 premises — the negated guard and the
/// Core's clauses — and one conjecture. It was emitted by the ordinary
/// search path and is kept verbatim, exactly as a first launch writes it:
/// the premises under the TPTP role `axiom`. Its relation names come from
/// the emitting run's own name environment, so it is a retained artifact
/// rather than something regenerated from this description. Under the
/// direct strategy the solver
/// reaches nothing on it for well over half a minute. The same formulas,
/// with the same names, bodies and order, under the role
/// `negated_conjecture` — asserted as written, not negated, so the same
/// logical problem — are proved in a fraction of a second, because Vampire
/// classifies `axiom` formulas as background theory and deprioritises
/// them, and a check's premises are the hypotheses of the very implication
/// being proved.
///
/// The second rendering is derived here by the one rule the assembly layer
/// applies — the role word of the `axiom_i` declarations, and nothing else
/// — which `entailment::assembly`'s own tests pin on the rendered bytes.
/// This test states the solver-side claim: that the role changes which
/// problems the pinned solver reaches, and that a proof found under the
/// new role still names the premises it cited, so proof-citation parsing
/// by axiom name keeps working.
///
/// Both launches run under a finite 5-second allowance, an order of
/// magnitude either side of what the two renderings need, so the test
/// states a capability rather than a race.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn the_pinned_solver_proves_under_the_retry_premise_role_what_it_cannot_as_axioms() {
    let _process_guard = process_test_guard().await;
    let repository_root = support::repository_root();
    let pinned = PinnedLeancheckVampire::from_lock(&repository_root)
        .expect("the repository-pinned leancheck Vampire resolves");
    let directory = support::TestDir::new("vampire_race_real_premise_role");
    let first_launch = directory.path().join("first_launch.p");
    fs::copy(
        repository_root.join("whiel_runner/tests/fixtures/goal_tagged_retry_problem.p"),
        &first_launch,
    )
    .unwrap();
    let as_written = fs::read_to_string(&first_launch).unwrap();
    let retagged: String = as_written
        .lines()
        .map(|line| {
            if line.starts_with("fof(axiom_") {
                format!(
                    "{}\n",
                    line.replacen(", axiom, ", ", negated_conjecture, ", 1)
                )
            } else {
                format!("{line}\n")
            }
        })
        .collect();
    assert!(retagged.contains("fof(support_adom, axiom, "));
    assert!(retagged.contains("fof(goal, conjecture, "));
    assert_ne!(retagged, as_written);
    let retry_launch = directory.path().join("retry_launch.p");
    fs::write(&retry_launch, &retagged).unwrap();

    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let admission = agent_admission(1);
    let allowance = VampireSearchBudget::finite(Duration::from_secs(5));

    // The control: the first launch's own rendering, which this allowance
    // does not settle.
    let as_axioms = run_vampire(
        VampireRequest::new(
            VampireProblem::new("real-premise-role-axiom", first_launch),
            VampireMode::ProofOnly,
            VampireWorkerCommand::new(pinned.path()),
            store.clone(),
            admission.clone(),
            allowance,
        )
        .unwrap(),
        CancellationToken::new(),
    )
    .await;
    assert!(
        !matches!(
            as_axioms,
            VampireInvocationOutcome::Result(VampireResult::Proved(_))
        ),
        "the axiom-tagged rendering was proved inside the launch allowance: {as_axioms:?}"
    );

    let as_goal = run_vampire(
        VampireRequest::new(
            VampireProblem::new("real-premise-role-negated-conjecture", retry_launch),
            VampireMode::ProofOnly,
            VampireWorkerCommand::new(pinned.path()),
            store.clone(),
            admission,
            allowance,
        )
        .unwrap(),
        CancellationToken::new(),
    )
    .await;
    let VampireInvocationOutcome::Result(VampireResult::Proved(proof)) = &as_goal else {
        panic!("the re-tagged rendering was not proved: {as_goal:?}");
    };
    assert_eq!(
        proof.strategy(),
        VampireProofStrategy::Direct,
        "the direct strategy itself reaches the re-tagged problem"
    );

    // The cited premises are still named by the short TPTP names the
    // assembly layer gives them, which is what a run's proof-citation
    // parsing reads to record a dictionary entry's cited set.
    let resolved = store.resolve(proof.output()).unwrap();
    let proof_text = fs::read_to_string(resolved.path()).unwrap();
    assert!(
        proof_text.contains("negated_conjecture"),
        "the proof reports the role the premises were written under"
    );
    let cited = proof_text
        .split(|character: char| !character.is_ascii_alphanumeric() && character != '_')
        .filter(|token| token.starts_with("axiom_"))
        .collect::<std::collections::BTreeSet<_>>();
    assert!(
        !cited.is_empty(),
        "a proof under the retry role still cites its premises by name"
    );

    owner.settle().unwrap();
}
