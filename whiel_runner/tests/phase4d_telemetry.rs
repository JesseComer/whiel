mod support;

use std::ffi::OsString;
use std::fs;
use std::time::Duration;

use whiel_runner::encoding::{
    EncodingWorkerCommand, EncodingWorkerPoolConfig, ProposalRealization,
    new_solver_encoding_context,
};
use whiel_runner::{
    ArtifactStoreConfig, CancellationToken, FmbOptions, InitializationInvocationOutcome,
    ProofCascPolicy, RegisteredClauses, RuntimeResourcePolicy, TelemetryConfig, TelemetryHandle,
    TelemetryLevel, TelemetrySession, VampireMode, VampireProblem, VampireRequest,
    VampireSearchBudget, VampireWorkerCommand, VerificationParameters,
    create_general_solver_admission, create_symbolic_solver_admissions, new_artifact_store,
    new_symbolic_inv_state, prepare_ordinary_candidates, propose_symbolic_clauses,
    register_clauses, run_vampire,
};

// ------------------------------------------------------------
// Reference-Wave Population Accounting
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
    .proposal_realization(ProposalRealization::ReferenceV3)
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn exact_wave_populations_are_not_reported_as_cumulative_work() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("phase4d_wave_telemetry");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let resources = RuntimeResourcePolicy::symbolic(4, 2, 2).unwrap();
    let (inv, _cex) = create_symbolic_solver_admissions(resources).unwrap();
    let verification = VerificationParameters::new(Duration::from_secs(5), resources).unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_symbolic_inv_state(
        &task,
        context.clone(),
        &artifacts,
        verification,
        inv,
        false,
        false,
    )
    .unwrap();
    let telemetry = TelemetrySession::start(TelemetryConfig::new(
        directory.path().join("telemetry"),
        TelemetryLevel::Aggregate,
    ));
    state.attach_telemetry(telemetry.handle());
    let cancellation = CancellationToken::new();

    for expected_stage in 0..=1 {
        propose_symbolic_clauses(&mut state, &cancellation)
            .await
            .unwrap();
        assert_eq!(state.proposal_progress().last_stage(), Some(expected_stage));
        assert!(matches!(
            prepare_ordinary_candidates(&mut state, &cancellation).await,
            InitializationInvocationOutcome::Complete
        ));
    }

    let report = telemetry.finish();
    assert!(!report.snapshot.measurement_complete);
    assert!(
        report
            .snapshot
            .missing_measurements
            .iter()
            .any(|measurement| measurement == "terminal.outcome")
    );
    assert_eq!(report.snapshot.waves.len(), 2);
    let first = &report.snapshot.waves[0];
    let second = &report.snapshot.waves[1];
    assert_eq!((first.stage, second.stage), (0, 1));

    let first_decoded = first.stage_delta_decoded_formula_occurrences.unwrap();
    let second_decoded = second.stage_delta_decoded_formula_occurrences.unwrap();
    let first_distinct = first.stage_delta_equality_distinct_formulas.unwrap();
    let second_distinct = second.stage_delta_equality_distinct_formulas.unwrap();
    let first_deduplicated = first.stage_delta_equality_deduplicated_occurrences.unwrap();
    let second_deduplicated = second
        .stage_delta_equality_deduplicated_occurrences
        .unwrap();
    assert_eq!(
        first.cumulative_decoded_formula_occurrences,
        Some(first_decoded)
    );
    assert_eq!(
        second.cumulative_decoded_formula_occurrences,
        Some(first_decoded + second_decoded)
    );
    assert_eq!(
        first.cumulative_equality_distinct_formulas,
        Some(first_distinct)
    );
    assert_eq!(
        second.cumulative_equality_distinct_formulas,
        Some(first_distinct + second_distinct)
    );
    assert_eq!(
        first.cumulative_equality_deduplicated_occurrences,
        Some(first_deduplicated)
    );
    assert_eq!(
        second.cumulative_equality_deduplicated_occurrences,
        Some(first_deduplicated + second_deduplicated)
    );
    for wave in [first, second] {
        assert!(wave.page_count > 0);
        assert_eq!(wave.worker_stage_batch_evaluations, wave.page_count);
        assert_eq!(
            wave.prior_slice_evaluations,
            if wave.stage > 0 { wave.page_count } else { 0 }
        );
        assert_eq!(
            wave.stage_delta_equality_distinct_formulas,
            Some(wave.emitted_formulas)
        );
        assert_eq!(wave.wave_registration_attempts, wave.emitted_formulas);
        assert_eq!(wave.registered_unique_formulas, wave.emitted_formulas);
        assert_eq!(wave.previously_seen_formulas, 0);
        assert!(wave.catalog_registration_nanoseconds.is_some());
        assert!(wave.formula_body_preparation_nanoseconds.is_some());
    }
    assert_eq!(first.cumulative_registration_rechecks, 0);
    assert_eq!(
        second.cumulative_registration_rechecks,
        first.cumulative_proposal_size
    );
    assert_eq!(
        second.cumulative_proposal_size,
        first.cumulative_proposal_size + second.emitted_formulas
    );

    let expected_attempts = first
        .cumulative_proposal_size
        .saturating_add(second.cumulative_proposal_size);
    assert_eq!(
        report
            .snapshot
            .counters
            .get("catalog.registration_attempts"),
        Some(&expected_attempts)
    );
    assert_eq!(
        report
            .snapshot
            .counters
            .get("catalog.wave_registration_attempts"),
        Some(&(first.emitted_formulas + second.emitted_formulas))
    );
    assert_eq!(
        report
            .snapshot
            .counters
            .get("catalog.cumulative_registration_rechecks"),
        Some(&first.cumulative_proposal_size)
    );
    assert_eq!(
        report.snapshot.formula_births.len() as u64,
        first.registered_unique_formulas + second.registered_unique_formulas
    );
    assert_eq!(
        report.snapshot.counters.get("inv.reference_pages"),
        Some(&(first.page_count + second.page_count))
    );
    assert_eq!(
        report
            .snapshot
            .counters
            .get("inv.reference_worker_stage_batch_evaluations"),
        Some(&(first.page_count + second.page_count))
    );
    assert_eq!(
        report
            .snapshot
            .counters
            .get("inv.reference_prior_slice_evaluations"),
        Some(&second.page_count)
    );
    for wave in [first, second] {
        let stage = report
            .snapshot
            .derived
            .stage_yield
            .iter()
            .find(|entry| entry.stage == wave.stage)
            .expect("one derived population per emitted wave");
        assert_eq!(
            stage.registered_unique_population,
            wave.registered_unique_formulas
        );
        assert_eq!(
            stage.emitted_to_core_denominator,
            wave.registered_unique_formulas
        );
    }

    context.shutdown().await.unwrap();
    drop(state);
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn telemetry_off_progress_counts_registered_reference_formulas() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("phase4d_off_reference_progress");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let resources = RuntimeResourcePolicy::symbolic(4, 2, 2).unwrap();
    let (inv, _cex) = create_symbolic_solver_admissions(resources).unwrap();
    let verification = VerificationParameters::new(Duration::from_secs(5), resources).unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_symbolic_inv_state(
        &task,
        context.clone(),
        &artifacts,
        verification,
        inv,
        false,
        false,
    )
    .unwrap();
    let telemetry = TelemetryHandle::disabled();
    state.attach_telemetry(telemetry.clone());
    let cancellation = CancellationToken::new();

    propose_symbolic_clauses(&mut state, &cancellation)
        .await
        .unwrap();
    assert!(matches!(
        prepare_ordinary_candidates(&mut state, &cancellation).await,
        InitializationInvocationOutcome::Complete
    ));

    let snapshot = telemetry.snapshot();
    assert_eq!(snapshot.level, TelemetryLevel::Off);
    assert_eq!(
        snapshot.counters.get("catalog.registered_unique"),
        Some(&(state.houdini().catalog().len() as u64))
    );
    assert_eq!(snapshot.counters["catalog.registered_unique"], 1);

    context.shutdown().await.unwrap();
    drop(state);
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn preexisting_exact_wave_formula_is_not_reported_as_newly_registered() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("phase4d_preexisting_wave_telemetry");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let resources = RuntimeResourcePolicy::symbolic(4, 2, 2).unwrap();
    let (inv, _cex) = create_symbolic_solver_admissions(resources).unwrap();
    let verification = VerificationParameters::new(Duration::from_secs(5), resources).unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_symbolic_inv_state(
        &task,
        context.clone(),
        &artifacts,
        verification,
        inv,
        false,
        false,
    )
    .unwrap();
    let telemetry = TelemetrySession::start(TelemetryConfig::new(
        directory.path().join("telemetry"),
        TelemetryLevel::Detailed,
    ));
    state.attach_telemetry(telemetry.handle());
    let cancellation = CancellationToken::new();

    propose_symbolic_clauses(&mut state, &cancellation)
        .await
        .unwrap();
    assert_eq!(state.proposal().len(), 1);
    let preexisting = state.proposal()[0].clone();
    assert!(matches!(
        register_clauses(
            state.houdini().catalog(),
            state.houdini().admission(),
            [preexisting],
            &cancellation,
        )
        .await,
        RegisteredClauses::Complete(_)
    ));
    assert!(matches!(
        prepare_ordinary_candidates(&mut state, &cancellation).await,
        InitializationInvocationOutcome::Complete
    ));

    let report = telemetry.finish();
    let wave = &report.snapshot.waves[0];
    assert_eq!(wave.wave_registration_attempts, 1);
    assert_eq!(wave.registered_unique_formulas, 0);
    assert_eq!(wave.previously_seen_formulas, 1);
    assert_eq!(report.snapshot.formula_births.len(), 1);
    assert!(!report.snapshot.formula_births[0].registered_unique);
    assert_eq!(
        report.snapshot.derived.stage_yield[0].registered_unique_population,
        0
    );
    let events = fs::read_to_string(report.events_path.expect("detailed event path")).unwrap();
    assert!(
        events.lines().all(|line| {
            serde_json::from_str::<serde_json::Value>(line).expect("valid JSONL event")["kind"]
                != "formula_registered"
        }),
        "a preexisting Catalog formula is not a registration birth"
    );

    context.shutdown().await.unwrap();
    drop(state);
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}

// ------------------------------------------------------------
// Solver-Boundary Counters
// ------------------------------------------------------------

#[cfg(any(target_os = "macos", target_os = "linux"))]
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn vampire_counters_measure_requests_admission_and_actual_launches() {
    let directory = support::TestDir::new("phase4d_vampire_telemetry");
    let launch_log = directory.path().join("launches");
    let problem = directory.path().join("problem.p");
    fs::write(&problem, "fof(goal, conjecture, $true).\n").unwrap();
    let task = support::sample_task();
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let telemetry = TelemetrySession::start(TelemetryConfig::new(
        directory.path().join("telemetry"),
        TelemetryLevel::Detailed,
    ));
    let command = VampireWorkerCommand::new(support::fake_vampire())
        .with_extra_args([
            OsString::from("--fixture"),
            OsString::from("ladder-cutoff-casc-proof"),
            OsString::from("--expect-start"),
            OsString::from("1"),
            OsString::from("--launch-log"),
            launch_log.as_os_str().to_owned(),
        ])
        .unwrap()
        .with_proof_casc_policy(ProofCascPolicy::CLI_DEFAULT)
        .unwrap()
        .with_telemetry(telemetry.handle());
    let admission =
        create_general_solver_admission(RuntimeResourcePolicy::agent_only(2, 2).unwrap()).unwrap();
    let request = VampireRequest::new(
        VampireProblem::new("telemetry-fixture", problem),
        VampireMode::ProofAndFmb(FmbOptions::default()),
        command,
        artifacts.clone(),
        admission,
        VampireSearchBudget::cumulative(Duration::from_secs(1), Duration::from_secs(3)),
    )
    .unwrap();

    let outcome = run_vampire(request, CancellationToken::new()).await;
    let actual_launches = fs::read_to_string(&launch_log)
        .expect("fixture launch log")
        .lines()
        .count() as u64;
    let report = telemetry.finish();

    assert_eq!(
        report.snapshot.counters.get("solver.vampire_requests"),
        Some(&1)
    );
    assert_eq!(
        report
            .snapshot
            .counters
            .get("solver.vampire_requests.proof_and_fmb"),
        Some(&1)
    );
    assert_eq!(
        report
            .snapshot
            .counters
            .get("solver.vampire_requested_process_slots"),
        Some(&2)
    );
    assert_eq!(
        report
            .snapshot
            .counters
            .get("solver.vampire_process_launches"),
        Some(&actual_launches)
    );
    let proof_launches = report
        .snapshot
        .counters
        .get("solver.vampire_process_launches.proof")
        .copied()
        .unwrap_or(0);
    let fmb_launches = report
        .snapshot
        .counters
        .get("solver.vampire_process_launches.fmb")
        .copied()
        .unwrap_or(0);
    assert_eq!(proof_launches + fmb_launches, actual_launches);
    assert_eq!(actual_launches, 3);
    assert_eq!(proof_launches, 2);
    assert_eq!(fmb_launches, 1);
    assert_eq!(
        report
            .snapshot
            .counters
            .get("solver.vampire_process_launches.proof_normal"),
        Some(&1),
    );
    assert_eq!(
        report
            .snapshot
            .counters
            .get("solver.vampire_process_launches.proof_casc"),
        Some(&1),
    );
    assert_eq!(
        report
            .snapshot
            .counters
            .get("solver.proof_casc_escalations.direct_cutoff"),
        Some(&1),
    );
    assert_eq!(
        report
            .snapshot
            .counters
            .get("solver.proof_winners.casc_2025"),
        Some(&1),
    );
    assert!(
        report
            .snapshot
            .duration_nanoseconds
            .contains_key("solver.admission_wait")
    );
    for timing in [
        "solver.proof_process_execution_and_cleanup",
        "solver.proof_normal_execution_and_cleanup",
        "solver.proof_casc_execution_and_cleanup",
        "solver.fmb_process_execution_and_cleanup",
    ] {
        assert!(
            report.snapshot.duration_nanoseconds.contains_key(timing),
            "missing proof-ladder timing {timing}",
        );
    }
    let all_events = fs::read_to_string(
        report
            .events_path
            .as_ref()
            .expect("detailed telemetry retains its event stream"),
    )
    .unwrap()
    .lines()
    .map(|line| serde_json::from_str::<serde_json::Value>(line).unwrap())
    .collect::<Vec<_>>();
    let events = all_events
        .iter()
        .filter(|event| event["kind"] == "vampire_process_launched")
        .collect::<Vec<_>>();
    assert_eq!(events.len(), 3);
    let casc_launch = events
        .iter()
        .find(|event| event["payload"]["proof_strategy"] == "casc_2025")
        .expect("one detailed event identifies the CASC launch");
    let casc_limit = casc_launch["payload"]["time_limit_deciseconds"]
        .as_u64()
        .expect("the dynamic CASC limit is auditable");
    assert!((1..=18).contains(&casc_limit));
    let allocation = all_events
        .iter()
        .find(|event| event["kind"] == "proof_casc_allocation")
        .expect("one detailed event records the nominal adaptive allocation");
    assert_eq!(allocation["payload"]["initial_share_millionths"], 250_000);
    assert_eq!(
        allocation["payload"]["retry_added_share_millionths"],
        750_000,
    );
    assert_eq!(
        allocation["payload"]["initial_limit_nanoseconds"],
        1_000_000_000_u64,
    );
    assert_eq!(
        allocation["payload"]["retry_added_nanoseconds"],
        2_000_000_000_u64,
    );
    assert_eq!(
        allocation["payload"]["nominal_direct_prefix_nanoseconds"],
        1_250_000_000_u64,
    );
    assert_eq!(
        allocation["payload"]["nominal_casc_tail_nanoseconds"],
        1_750_000_000_u64,
    );
    let escalation = all_events
        .iter()
        .find(|event| event["kind"] == "proof_casc_escalated")
        .expect("one detailed event records the adaptive handoff");
    assert_eq!(escalation["payload"]["trigger"], "direct_cutoff");
    assert_eq!(
        escalation["payload"]["nominal_casc_tail_nanoseconds"],
        1_750_000_000_u64,
    );

    drop(outcome);
    drop(artifacts);
    owner.settle().unwrap();
}
