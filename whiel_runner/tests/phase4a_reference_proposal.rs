mod support;

use std::ffi::OsString;
use std::fs;
use std::path::Path;
use std::time::Duration;

use whiel_runner::encoding::{
    EncodingWorkerCommand, EncodingWorkerPoolConfig, ProposalRealization,
    REFERENCE_PROPOSAL_VERSION, new_solver_encoding_context,
};
use whiel_runner::{
    ArtifactKind, ArtifactStoreConfig, CancellationToken, ClauseSet, CoverageLookup, CoverageMode,
    InitializationInvocationOutcome, InitializationStatus, MaintenanceBlockOutcome,
    MaintenanceExecutionOutcome, RuntimeResourcePolicy, TrackLayout, VampireWorkerCommand,
    VerificationParameters, create_symbolic_solver_admissions, expand_core, new_artifact_store,
    new_symbolic_inv_state, prepare_maintenance, prepare_ordinary_candidates,
    propose_symbolic_clauses, run_maintenance_block,
};

// ------------------------------------------------------------
// Shared Phase 4A Fixtures
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

fn vampire_command(launch_log: &Path) -> VampireWorkerCommand {
    VampireWorkerCommand::new(support::fake_vampire())
        .with_extra_args([
            OsString::from("--fixture"),
            // Coverage is the subject of this test. Make the irrelevant FMB
            // peer finish inconclusively; paired cancellation and hard-kill
            // escalation have dedicated process tests.
            OsString::from("race-fmb-failure-proof"),
            OsString::from("--expect-start"),
            OsString::from("1"),
            OsString::from("--launch-log"),
            launch_log.as_os_str().to_owned(),
        ])
        .unwrap()
}

fn launch_count(path: &Path) -> usize {
    fs::read_to_string(path).unwrap_or_default().lines().count()
}

// ------------------------------------------------------------
// Trusted Proposal Registration
// ------------------------------------------------------------

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn dynamic_reference_stages_prepare_and_reuse_exact_clause_ids() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("phase4a_reference_catalog");
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
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
    let cancellation = CancellationToken::new();

    propose_symbolic_clauses(&mut state, &cancellation)
        .await
        .unwrap();
    assert_eq!(
        state.proposal_progress().enumerator_version(),
        REFERENCE_PROPOSAL_VERSION
    );
    assert_eq!(state.proposal_progress().last_stage(), Some(0));
    let first = state.proposal()[0].clone();
    let first_identity = first.identity().to_owned();
    let first_display = first.certificate_formula().to_owned();
    assert!(matches!(
        prepare_ordinary_candidates(&mut state, &cancellation).await,
        InitializationInvocationOutcome::Complete
    ));
    let first_id = state
        .houdini()
        .catalog()
        .find(&first)
        .unwrap()
        .expect("registered stage-zero formula");
    let first_record = state.houdini().catalog().record(first_id).unwrap();
    assert_eq!(first_record.formula().identity(), first_identity);
    assert_eq!(first_record.formula().certificate_formula(), first_display);
    assert!(first_record.formula_body().is_some());

    // The public proposal is cumulative even though Lean emits exact finite
    // incremental waves. The earlier identity must remain present after the
    // next complete wave, and Catalog interning must retain the dense ClauseId.
    propose_symbolic_clauses(&mut state, &cancellation)
        .await
        .unwrap();
    assert_eq!(state.proposal_progress().last_stage(), Some(1));
    let repeated = state
        .proposal()
        .iter()
        .find(|formula| formula.identity() == first_identity)
        .expect("the next cumulative stage retains its earlier formula")
        .clone();
    assert_eq!(repeated.source().source_id(), first.source().source_id());
    assert!(matches!(
        prepare_ordinary_candidates(&mut state, &cancellation).await,
        InitializationInvocationOutcome::Complete
    ));
    let repeated_id = state
        .houdini()
        .catalog()
        .find(&repeated)
        .unwrap()
        .expect("registered repeated formula");
    assert_eq!(repeated_id, first_id);

    context.shutdown().await.unwrap();
    drop(state);
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}

async fn run_literal_subset_policy(label: &str, lookup: CoverageLookup) -> (usize, Vec<String>) {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new(label);
    let launch_log = directory.path().join("launches");
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let resources = RuntimeResourcePolicy::symbolic(4, 2, 2).unwrap();
    let (inv, _cex) = create_symbolic_solver_admissions(resources).unwrap();
    let verification = VerificationParameters::new(Duration::from_secs(30), resources).unwrap();
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
    let cancellation = CancellationToken::new();

    // Stage zero contains the empty disjunction. Stage one adds singleton
    // clauses. The former is therefore an exact literal subset of the latter.
    propose_symbolic_clauses(&mut state, &cancellation)
        .await
        .unwrap();
    propose_symbolic_clauses(&mut state, &cancellation)
        .await
        .unwrap();
    assert!(matches!(
        prepare_ordinary_candidates(&mut state, &cancellation).await,
        InitializationInvocationOutcome::Complete
    ));
    let proposal = state.proposal();
    assert!(proposal.len() >= 2);
    let selected = proposal[..2]
        .iter()
        .map(|formula| {
            state
                .houdini()
                .catalog()
                .find(formula)
                .unwrap()
                .expect("reference formula was registered")
        })
        .collect::<ClauseSet>();
    state
        .houdini_mut()
        .retain_init_candidates(selected.clone())
        .unwrap();
    let evidence = state
        .houdini()
        .catalog()
        .artifacts()
        .publish(
            ArtifactKind::InitializationCheck,
            b"Phase 4A exact-coverage fixture".as_slice().into(),
        )
        .unwrap();
    for clause in &selected {
        state
            .houdini()
            .catalog()
            .record_initialization(*clause, InitializationStatus::InitProved, evidence)
            .unwrap();
    }
    state
        .houdini_mut()
        .set_maintenance_schedule_policy(
            CoverageMode::UseProducerClosed,
            TrackLayout::SingleTrack,
            lookup,
        )
        .unwrap();
    assert!(matches!(
        prepare_maintenance(&task, state.houdini_mut(), &cancellation).await,
        whiel_runner::MaintenancePreparationOutcome::Complete
    ));
    let outcome = run_maintenance_block(
        &task,
        state.houdini_mut(),
        vampire_command(&launch_log),
        &cancellation,
    )
    .await;
    let MaintenanceExecutionOutcome::Complete(block) = outcome else {
        panic!("reference-clause maintenance did not complete: {outcome:#?}")
    };
    assert_eq!(block.outcome(), MaintenanceBlockOutcome::Stable);
    expand_core(state.houdini_mut(), &block).unwrap();
    let mut core = state
        .houdini()
        .core()
        .iter()
        .map(|id| {
            state
                .houdini()
                .catalog()
                .record(*id)
                .unwrap()
                .formula()
                .identity()
                .to_owned()
        })
        .collect::<Vec<_>>();
    core.sort();
    let launches = launch_count(&launch_log);

    context.shutdown().await.unwrap();
    drop(state);
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
    (launches, core)
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn exact_literal_subset_coverage_preserves_core_and_skips_vampire() {
    let (incoming_launches, incoming_core) =
        run_literal_subset_policy("phase4a_incoming_only", CoverageLookup::IncomingEdges).await;
    let (subset_launches, subset_core) = run_literal_subset_policy(
        "phase4a_literal_subset",
        CoverageLookup::LiteralSubsetThenIncoming,
    )
    .await;

    assert_eq!(subset_core, incoming_core);
    assert_eq!(incoming_core.len(), 2);
    assert_eq!(incoming_launches, 4);
    assert_eq!(subset_launches, 2);
}
