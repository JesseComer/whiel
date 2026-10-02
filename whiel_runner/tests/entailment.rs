mod support;

use std::collections::BTreeSet;
use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Duration;

use tokio::sync::Barrier;
use tokio::task::JoinSet;
use whiel_runner::encoding::{
    EncodingError, EncodingWorkerCommand, EncodingWorkerPoolConfig, QfSolverSource,
    SolverBodySource, new_solver_encoding_context,
};
use whiel_runner::entailment::{check_entailment_attempt_detailed, check_entailment_detailed};
use whiel_runner::{
    ArtifactKind, ArtifactStore, ArtifactStoreConfig, CancellationToken, CancelledEntailmentCheck,
    ConstantKey, EntailmentCheckResult, EntailmentCounterexample, EntailmentInvocationOutcome,
    FailureKind, FmbOptions, ProofCascShare, RuntimeResourcePolicy, ScopeTag, SolverAdmission,
    VampireMode, VampireWorkerCommand, assemble_entailment, check_entailment,
    create_general_solver_admission, new_artifact_store, resolve_entailment_counterexample,
};

// ------------------------------------------------------------
// Shared Phase 2D Fixtures
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

fn malformed_empty_worker_config() -> EncodingWorkerPoolConfig {
    let command = EncodingWorkerCommand::new(
        support::malformed_empty_encoding_worker(),
        support::repository_root(),
    )
    .arguments([OsString::from(
        support::example_encoding_worker().as_os_str(),
    )]);
    EncodingWorkerPoolConfig::new(command, 1).expect("positive worker count")
}

fn admission(slots: usize) -> SolverAdmission {
    create_general_solver_admission(RuntimeResourcePolicy::agent_only(slots, 2).unwrap()).unwrap()
}

fn qf_source(
    task: &whiel_runner::SynthesisTask,
    source_id: &str,
    constants: &[&str],
    relations: &[&str],
) -> SolverBodySource {
    let constants = constants
        .iter()
        .map(|key| ConstantKey::from_canonical(*key).unwrap())
        .collect::<Vec<_>>();
    let relation_keys = relations
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
    SolverBodySource::QuantifierFree(
        QfSolverSource::new(task, source_id, constants, relation_keys).unwrap(),
    )
}

fn all_relations() -> [&'static str; 4] {
    ["rel:E:0", "rel:T:0", "rel:T:1", "rel:TBound:0"]
}

fn vampire_command(fixture: &str, launch_log: Option<&Path>) -> VampireWorkerCommand {
    let mut args = vec![
        OsString::from("--fixture"),
        OsString::from(fixture),
        OsString::from("--expect-start"),
        OsString::from("1"),
    ];
    if let Some(path) = launch_log {
        args.push(OsString::from("--launch-log"));
        args.push(path.as_os_str().to_owned());
    }
    VampireWorkerCommand::new(support::fake_vampire())
        .with_extra_args(args)
        .unwrap()
}

async fn prepare_one(
    context: &whiel_runner::encoding::SolverEncodingContext,
    admission: &SolverAdmission,
    artifacts: &ArtifactStore,
    source: SolverBodySource,
) -> whiel_runner::encoding::PreparedBodyRef {
    context
        .prepare_solver_bodies(
            admission,
            artifacts,
            vec![source],
            &CancellationToken::new(),
        )
        .await
        .unwrap()
        .remove(0)
}

// ------------------------------------------------------------
// Shared Preparation And Assembly
// ------------------------------------------------------------

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn source_families_share_cached_bulk_assembly() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("entailment_sources");
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let admission = admission(2);
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let all = all_relations();
    let sources = vec![
        SolverBodySource::Assert(task.preprocessed_pre_solver().clone()),
        SolverBodySource::Assert(task.preprocessed_post_solver().clone()),
        qf_source(&task, "catalog.clause.0", &[], &["rel:E:0", "rel:TBound:0"]),
        qf_source(
            &task,
            "catalog.wp.0",
            &[],
            &["rel:E:0", "rel:T:0", "rel:TBound:0"],
        ),
        qf_source(&task, "symbolic.w.0", &[], &all),
        qf_source(&task, "symbolic.w.1", &[], &all),
        qf_source(
            &task,
            "agent_naive.one_off",
            &[],
            &["rel:E:0", "rel:T:0", "rel:T:1"],
        ),
        qf_source(
            &task,
            "catalog.clause.0.alias",
            &[],
            &["rel:E:0", "rel:TBound:0"],
        ),
    ];
    let mut bodies = Vec::new();
    for source in sources {
        let source_id = source.source_id().to_string();
        let mut prepared = context
            .prepare_solver_bodies(
                &admission,
                &artifacts,
                vec![source],
                &CancellationToken::new(),
            )
            .await
            .unwrap_or_else(|error| panic!("prepare {source_id}: {error:#?}"));
        bodies.push(prepared.remove(0));
    }
    assert_eq!(bodies.len(), 8);
    for body in &bodies {
        assert_eq!(body.context_id(), context.context_id());
        assert_eq!(body.source().task_identity(), task.identity());
        assert!(!body.body_id().is_empty());
        assert!(!body.fol_identity().is_empty());
        assert!(!body.tptp_body().is_empty());
        assert!(!body.theorem_id().is_empty());
    }

    context
        .prepare_support_block(&admission, &artifacts, [], &CancellationToken::new())
        .await
        .unwrap();

    let bulk = assemble_entailment(
        &context,
        &admission,
        &artifacts,
        vec![bodies[0].clone(), bodies[2].clone()],
        vec![bodies[3].clone(), bodies[4].clone(), bodies[5].clone()],
        &CancellationToken::new(),
    )
    .await
    .unwrap();
    let query = artifacts.resolve(bulk.query_artifact()).unwrap();
    let text = fs::read_to_string(query.path()).unwrap();
    assert_eq!(text.matches("fof(goal, conjecture").count(), 1);
    let first = text.find(bodies[3].tptp_body()).unwrap();
    let second = text.find(bodies[4].tptp_body()).unwrap();
    let third = text.find(bodies[5].tptp_body()).unwrap();
    assert!(first < second && second < third);
    assert!(text.contains(" & "));

    let published_after_first = artifacts.diagnostics().required_payloads_published;
    let repeated = assemble_entailment(
        &context,
        &admission,
        &artifacts,
        vec![bodies[0].clone(), bodies[2].clone()],
        vec![bodies[3].clone(), bodies[4].clone(), bodies[5].clone()],
        &CancellationToken::new(),
    )
    .await
    .unwrap();
    assert_eq!(bulk.identity(), repeated.identity());
    assert_eq!(bulk.query_artifact(), repeated.query_artifact());
    assert_eq!(
        artifacts.diagnostics().required_payloads_published,
        published_after_first,
        "an exact repeated assembly must not publish another query payload"
    );

    let original_clause = assemble_entailment(
        &context,
        &admission,
        &artifacts,
        Vec::new(),
        vec![bodies[2].clone()],
        &CancellationToken::new(),
    )
    .await
    .unwrap();
    let published_after_original = artifacts.diagnostics().required_payloads_published;
    let aliased_clause = assemble_entailment(
        &context,
        &admission,
        &artifacts,
        Vec::new(),
        vec![bodies[7].clone()],
        &CancellationToken::new(),
    )
    .await
    .unwrap();
    assert_ne!(original_clause.identity(), aliased_clause.identity());
    assert_eq!(
        original_clause.query_artifact(),
        aliased_clause.query_artifact(),
        "distinct source identities with identical query text must share storage"
    );
    assert_eq!(
        artifacts.diagnostics().required_payloads_published,
        published_after_original
    );

    let reordered = assemble_entailment(
        &context,
        &admission,
        &artifacts,
        vec![bodies[0].clone(), bodies[2].clone()],
        vec![bodies[5].clone(), bodies[4].clone(), bodies[3].clone()],
        &CancellationToken::new(),
    )
    .await
    .unwrap();
    assert_ne!(bulk.identity(), reordered.identity());

    context.shutdown().await.unwrap();

    drop(bulk);
    drop(repeated);
    drop(original_clause);
    drop(aliased_clause);
    drop(reordered);
    drop(bodies);
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn concurrent_query_misses_share_one_artifact_and_keep_attempts_distinct() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("entailment_query_dedup");
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let admission = admission(2);
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let axiom = prepare_one(
        &context,
        &admission,
        &artifacts,
        qf_source(&task, "catalog.clause.0", &[], &["rel:E:0", "rel:TBound:0"]),
    )
    .await;
    let goal = prepare_one(
        &context,
        &admission,
        &artifacts,
        qf_source(&task, "task.phase2c_qf_fixture", &[], &[]),
    )
    .await;
    context
        .prepare_support_block(&admission, &artifacts, [], &CancellationToken::new())
        .await
        .unwrap();

    let before = artifacts.diagnostics().required_payloads_published;
    let barrier = Arc::new(Barrier::new(9));
    let mut assemblies = JoinSet::new();
    for _ in 0..8 {
        let barrier = Arc::clone(&barrier);
        let context = context.clone();
        let admission = admission.clone();
        let artifacts = artifacts.clone();
        let axioms: Arc<[whiel_runner::encoding::PreparedBodyRef]> = vec![axiom.clone()].into();
        let goals: Arc<[whiel_runner::encoding::PreparedBodyRef]> = vec![goal.clone()].into();
        assemblies.spawn(async move {
            barrier.wait().await;
            assemble_entailment(
                &context,
                &admission,
                &artifacts,
                axioms,
                goals,
                &CancellationToken::new(),
            )
            .await
            .unwrap()
        });
    }
    barrier.wait().await;

    let mut entailments = Vec::new();
    while let Some(result) = assemblies.join_next().await {
        entailments.push(result.unwrap());
    }
    let query = entailments[0].query_artifact();
    assert!(
        entailments
            .iter()
            .all(|entailment| entailment.query_artifact() == query)
    );
    assert_eq!(
        artifacts.diagnostics().required_payloads_published,
        before + 1,
        "all concurrent misses must coalesce into one query publication"
    );
    let query_record = artifacts.resolve(query).unwrap();
    assert_eq!(query_record.scope(), ["root", "query-store"]);
    assert_eq!(artifacts.diagnostics().ready_query_artifacts, 1);
    assert_eq!(artifacts.diagnostics().in_flight_query_payload_bytes, 0);

    let inv_artifacts = artifacts.scoped(ScopeTag::Inv);
    let cex_artifacts = artifacts.scoped(ScopeTag::Cex);
    let first_attempt = inv_artifacts
        .begin_entailment_attempt(&entailments[0])
        .unwrap();
    let second_attempt = cex_artifacts
        .begin_entailment_attempt(&entailments[1])
        .unwrap();
    assert_ne!(first_attempt.attempt_id(), second_attempt.attempt_id());
    assert_eq!(first_attempt.query_artifact(), query);
    assert_eq!(second_attempt.query_artifact(), query);
    assert!(first_attempt.provenance().contains(&ScopeTag::Inv));
    assert!(second_attempt.provenance().contains(&ScopeTag::Cex));

    context.shutdown().await.unwrap();
    drop(entailments);
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn failed_query_publication_exposes_no_reference_and_can_be_retried() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("entailment_query_retry");
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let admission = admission(2);
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let goal = prepare_one(
        &context,
        &admission,
        &artifacts,
        qf_source(&task, "task.phase2c_qf_fixture", &[], &[]),
    )
    .await;
    context
        .prepare_support_block(&admission, &artifacts, [], &CancellationToken::new())
        .await
        .unwrap();

    let run_root = fs::read_dir(directory.path())
        .unwrap()
        .next()
        .unwrap()
        .unwrap()
        .path();
    let staging = run_root.join("staging");
    fs::remove_dir(&staging).unwrap();
    fs::write(&staging, b"block staged query creation").unwrap();
    let before = artifacts.diagnostics().required_payloads_published;

    let failed = assemble_entailment(
        &context,
        &admission,
        &artifacts,
        Vec::new(),
        vec![goal.clone()],
        &CancellationToken::new(),
    )
    .await;
    let Err(EncodingError::Failure(report)) = failed else {
        panic!("query publication must fail without exposing an entailment")
    };
    assert_eq!(report.kind(), FailureKind::PublicationFailure);
    assert_eq!(artifacts.diagnostics().required_payloads_published, before);

    fs::remove_file(&staging).unwrap();
    fs::create_dir(&staging).unwrap();
    let retried = assemble_entailment(
        &context,
        &admission,
        &artifacts,
        Vec::new(),
        vec![goal],
        &CancellationToken::new(),
    )
    .await
    .unwrap();
    assert_eq!(
        artifacts.diagnostics().required_payloads_published,
        before + 1
    );
    assert_eq!(
        artifacts.resolve(retried.query_artifact()).unwrap().kind(),
        ArtifactKind::Query
    );

    context.shutdown().await.unwrap();
    drop(retried);
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn name_extension_and_collisions_preserve_cached_bodies() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("entailment_names");
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let admission = admission(2);
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let stable_source = qf_source(&task, "task.phase2c_qf_fixture", &[], &[]);
    let stable = prepare_one(&context, &admission, &artifacts, stable_source.clone()).await;
    let stable_text = stable.tptp_body().to_string();

    let colliding = prepare_one(
        &context,
        &admission,
        &artifacts,
        qf_source(
            &task,
            "task.phase2d_qf_colliding_constants",
            &["str:a-b", "str:a_b"],
            &[],
        ),
    )
    .await;
    let names = context.name_env();
    let constant_names = names
        .all_mappings()
        .into_iter()
        .filter(|mapping| mapping.key == "str:a-b" || mapping.key == "str:a_b")
        .map(|mapping| mapping.tptp_name)
        .collect::<Vec<_>>();
    assert_eq!(constant_names.len(), 2);
    assert_ne!(constant_names[0], constant_names[1]);

    let stable_again = prepare_one(&context, &admission, &artifacts, stable_source).await;
    assert_eq!(stable_again.tptp_body(), stable_text);

    let constants = [
        ConstantKey::from_canonical("str:a-b").unwrap(),
        ConstantKey::from_canonical("str:a_b").unwrap(),
    ];
    let support = context
        .prepare_support_block(
            &admission,
            &artifacts,
            constants.clone(),
            &CancellationToken::new(),
        )
        .await
        .unwrap();
    let entailment = assemble_entailment(
        &context,
        &admission,
        &artifacts,
        vec![colliding.clone()],
        vec![colliding],
        &CancellationToken::new(),
    )
    .await
    .unwrap();
    assert_eq!(entailment.constants(), constants);
    assert_eq!(entailment.support_block().block_id(), support.block_id());

    context.shutdown().await.unwrap();
    drop(entailment);
    drop(stable);
    drop(stable_again);
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn strict_constant_extension_preserves_body_and_reuses_exact_support() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("entailment_constant_extension");
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let admission = admission(2);
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();

    let small_source = qf_source(
        &task,
        "task.phase2d_qf_colliding_constants",
        &["str:a-b", "str:a_b"],
        &[],
    );
    let small_body = prepare_one(&context, &admission, &artifacts, small_source.clone()).await;
    let original_text = small_body.tptp_body().to_string();
    let original_body_id = small_body.body_id().to_string();
    let original_revision = small_body.preparation_revision();
    let small_constants = small_body.constants().to_vec();
    let small_support = context
        .prepare_support_block(
            &admission,
            &artifacts,
            small_constants.clone(),
            &CancellationToken::new(),
        )
        .await
        .unwrap();

    let extension_body = prepare_one(
        &context,
        &admission,
        &artifacts,
        qf_source(
            &task,
            "task.phase2c_qf_mixed_constants",
            &["num:10", "str:mixed", "bool:0", "num:2"],
            &[],
        ),
    )
    .await;
    let combined_constants = small_body
        .constants()
        .iter()
        .chain(extension_body.constants())
        .cloned()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    assert!(
        small_constants
            .iter()
            .all(|constant| combined_constants.contains(constant))
    );
    assert!(small_constants.len() < combined_constants.len());
    let combined_support = context
        .prepare_support_block(
            &admission,
            &artifacts,
            combined_constants.clone(),
            &CancellationToken::new(),
        )
        .await
        .unwrap();

    let entailment = assemble_entailment(
        &context,
        &admission,
        &artifacts,
        vec![small_body.clone()],
        vec![extension_body],
        &CancellationToken::new(),
    )
    .await
    .unwrap();
    assert_eq!(entailment.constants(), combined_constants);
    assert_eq!(
        entailment.support_block().block_id(),
        combined_support.block_id()
    );

    // Shut down the workers before all cache checks. Success below proves
    // that the smaller body and both exact support keys are reused.
    context.shutdown().await.unwrap();
    let small_again = prepare_one(&context, &admission, &artifacts, small_source).await;
    assert_eq!(small_again.tptp_body(), original_text);
    assert_eq!(small_again.body_id(), original_body_id);
    assert_eq!(small_again.preparation_revision(), original_revision);

    let small_support_again = context
        .prepare_support_block(
            &admission,
            &artifacts,
            small_constants,
            &CancellationToken::new(),
        )
        .await
        .unwrap();
    let combined_support_again = context
        .prepare_support_block(
            &admission,
            &artifacts,
            combined_constants.clone(),
            &CancellationToken::new(),
        )
        .await
        .unwrap();
    assert_eq!(small_support_again.block_id(), small_support.block_id());
    assert_eq!(
        combined_support_again.block_id(),
        combined_support.block_id()
    );

    drop(entailment);
    drop(small_again);
    drop(small_body);
    drop(small_support);
    drop(small_support_again);
    drop(combined_support);
    drop(combined_support_again);
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}

// ------------------------------------------------------------
// Typed Check Results And Proof Reuse
// ------------------------------------------------------------

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn proof_is_checked_against_the_source_empty_instance() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("entailment_empty");
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let admission = admission(2);
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let false_body = prepare_one(
        &context,
        &admission,
        &artifacts,
        qf_source(&task, "phase2d.false", &[], &[]),
    )
    .await;
    let entailment = assemble_entailment(
        &context,
        &admission,
        &artifacts,
        Vec::new(),
        vec![false_body],
        &CancellationToken::new(),
    )
    .await
    .unwrap();

    let outcome = check_entailment(
        &entailment,
        &artifacts,
        Some(Duration::from_secs(5)),
        VampireMode::ProofOnly,
        vampire_command("proof", None),
        admission,
        CancellationToken::new(),
    )
    .await;
    let EntailmentInvocationOutcome::Result(EntailmentCheckResult::Refuted(
        EntailmentCounterexample::Empty { input, .. },
    )) = outcome
    else {
        panic!("expected an empty source counterexample: {outcome:#?}")
    };
    assert_eq!(input.task_identity(), task.identity());
    assert!(
        input
            .relations()
            .values()
            .all(|relation| relation.true_tuples().is_empty())
    );

    context.shutdown().await.unwrap();
    drop(entailment);
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn raw_nonproof_results_skip_the_empty_worker() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("entailment_raw_results");
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let admission = admission(2);
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let goal = prepare_one(
        &context,
        &admission,
        &artifacts,
        qf_source(&task, "task.phase2c_qf_fixture", &[], &[]),
    )
    .await;
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
    context.shutdown().await.unwrap();

    let refuted = check_entailment(
        &entailment,
        &artifacts,
        Some(Duration::from_secs(5)),
        VampireMode::FmbOnly(FmbOptions::default()),
        vampire_command("model", None),
        admission.clone(),
        CancellationToken::new(),
    )
    .await;
    assert!(matches!(
        refuted,
        EntailmentInvocationOutcome::Result(EntailmentCheckResult::Refuted(
            EntailmentCounterexample::Model { .. }
        ))
    ));

    let timed_out = check_entailment(
        &entailment,
        &artifacts,
        Some(Duration::from_millis(100)),
        VampireMode::ProofAndFmb(FmbOptions::default()),
        vampire_command("race-timeout", None),
        admission.clone(),
        CancellationToken::new(),
    )
    .await;
    let EntailmentInvocationOutcome::Result(EntailmentCheckResult::TimedOut {
        next_fmb_start_size,
        ..
    }) = timed_out
    else {
        panic!("expected a typed timeout: {timed_out:#?}")
    };
    assert_eq!(next_fmb_start_size.unwrap().get(), 1);

    let failed = check_entailment(
        &entailment,
        &artifacts,
        Some(Duration::from_secs(5)),
        VampireMode::ProofOnly,
        vampire_command("unknown", None),
        admission,
        CancellationToken::new(),
    )
    .await;
    assert!(matches!(
        failed,
        EntailmentInvocationOutcome::Result(EntailmentCheckResult::Failure { .. })
    ));

    drop(entailment);
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn retained_model_decodes_to_a_complete_source_instance() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("entailment_model_decode");
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let admission = admission(2);
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let goal = prepare_one(
        &context,
        &admission,
        &artifacts,
        qf_source(&task, "task.phase2c_qf_fixture", &[], &[]),
    )
    .await;
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
    let result = check_entailment(
        &entailment,
        &artifacts,
        Some(Duration::from_secs(5)),
        VampireMode::FmbOnly(FmbOptions::default()),
        vampire_command("source-model", None),
        admission,
        CancellationToken::new(),
    )
    .await;
    let EntailmentInvocationOutcome::Result(EntailmentCheckResult::Refuted(counterexample)) =
        result
    else {
        panic!("expected a model result: {result:#?}")
    };
    let model = counterexample.model().unwrap().output();
    let model_path = artifacts.resolve(model).unwrap().path().to_path_buf();
    let model_bytes = fs::read(&model_path).unwrap();
    let published_before = artifacts.diagnostics().required_payloads_published;
    let input = resolve_entailment_counterexample(&task, &artifacts, &counterexample).unwrap();
    let published_after_first = artifacts.diagnostics().required_payloads_published;
    assert_eq!(published_after_first, published_before + 1);
    assert_eq!(input.relations().len(), task.solver_relations().len());
    assert!(
        input
            .relations()
            .values()
            .all(|relation| { relation.arity() == 2 && relation.true_tuples().is_empty() })
    );

    fs::remove_file(&model_path).unwrap();
    let cached_counterexample = counterexample.clone();
    let cached = resolve_entailment_counterexample(&task, &artifacts, &cached_counterexample)
        .expect("an exact cloned counterexample reuses its retained decoded instance");
    assert_eq!(cached.task_identity(), input.task_identity());
    assert_eq!(cached.relations(), input.relations());
    assert_eq!(
        artifacts.diagnostics().required_payloads_published,
        published_after_first,
        "reuse must not publish another witness artifact"
    );
    fs::write(model_path, model_bytes).unwrap();

    context.shutdown().await.unwrap();
    drop(entailment);
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn installed_vampire_model_decodes_when_available() {
    let executable = std::env::var_os("VAMPIRE_BIN")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("/opt/vampire/build/vampire"));
    if !executable.is_file() {
        return;
    }

    let task = support::export_canonical_task();
    let directory = support::TestDir::new("entailment_real_model");
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let admission = admission(2);
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let goal = prepare_one(
        &context,
        &admission,
        &artifacts,
        qf_source(&task, "phase2d.false", &[], &[]),
    )
    .await;
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
    let result = check_entailment(
        &entailment,
        &artifacts,
        Some(Duration::from_secs(30)),
        VampireMode::FmbOnly(FmbOptions::default()),
        VampireWorkerCommand::new(executable),
        admission,
        CancellationToken::new(),
    )
    .await;
    let EntailmentInvocationOutcome::Result(EntailmentCheckResult::Refuted(counterexample)) =
        result
    else {
        panic!("expected a real finite model: {result:#?}")
    };
    let input = resolve_entailment_counterexample(&task, &artifacts, &counterexample).unwrap();
    assert_eq!(input.relations().len(), task.solver_relations().len());
    assert!(
        input
            .relations()
            .values()
            .any(|relation| { !relation.true_tuples().is_empty() })
    );

    context.shutdown().await.unwrap();
    drop(entailment);
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn proof_survives_a_post_proof_empty_check_interruption() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("entailment_reuse");
    let launch_log = directory.path().join("launches.log");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let admission = admission(2);
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let goal = prepare_one(
        &context,
        &admission,
        &artifacts,
        qf_source(&task, "task.phase2c_qf_fixture", &[], &[]),
    )
    .await;
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
    context.shutdown().await.unwrap();
    let attempt = artifacts.begin_entailment_attempt(&entailment).unwrap();

    let first = check_entailment_attempt_detailed(
        &entailment,
        &attempt,
        Duration::from_secs(5),
        VampireMode::ProofOnly,
        vampire_command("proof", Some(&launch_log)),
        admission.clone(),
        CancellationToken::new(),
    )
    .await;
    let EntailmentInvocationOutcome::Cancelled(CancelledEntailmentCheck::EmptyCheck {
        retained_proof: first_proof,
    }) = first.outcome()
    else {
        panic!("unexpected first outcome: {first:#?}")
    };
    assert_eq!(launch_count(&launch_log), 1);

    let second = check_entailment_attempt_detailed(
        &entailment,
        &attempt,
        Duration::from_secs(5),
        VampireMode::ProofOnly,
        vampire_command("proof", Some(&launch_log)),
        admission,
        CancellationToken::new(),
    )
    .await;
    let EntailmentInvocationOutcome::Cancelled(CancelledEntailmentCheck::EmptyCheck {
        retained_proof: second_proof,
    }) = second.outcome()
    else {
        panic!("unexpected second outcome: {second:#?}")
    };
    assert_eq!(first_proof.attempt_id(), second_proof.attempt_id());
    assert_eq!(first_proof.output(), second_proof.output());
    assert_eq!(launch_count(&launch_log), 1);
    assert_eq!(artifacts.next_attempt_id().unwrap().get(), 1);

    drop(entailment);
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn proof_is_not_reused_across_entailment_attempts() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("entailment_attempt_scoped_proof");
    let launch_log = directory.path().join("launches.log");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let admission = admission(2);
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let goal = prepare_one(
        &context,
        &admission,
        &artifacts,
        qf_source(&task, "task.phase2c_qf_fixture", &[], &[]),
    )
    .await;
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
    context.shutdown().await.unwrap();

    let first_attempt = artifacts.begin_entailment_attempt(&entailment).unwrap();
    let first = check_entailment_attempt_detailed(
        &entailment,
        &first_attempt,
        Duration::from_secs(5),
        VampireMode::ProofOnly,
        vampire_command("proof", Some(&launch_log)),
        admission.clone(),
        CancellationToken::new(),
    )
    .await;
    let EntailmentInvocationOutcome::Cancelled(CancelledEntailmentCheck::EmptyCheck {
        retained_proof: first_proof,
    }) = first.outcome()
    else {
        panic!("unexpected first outcome: {first:#?}")
    };

    let second_attempt = artifacts.begin_entailment_attempt(&entailment).unwrap();
    let second = check_entailment_attempt_detailed(
        &entailment,
        &second_attempt,
        Duration::from_secs(5),
        VampireMode::ProofOnly,
        vampire_command("proof", Some(&launch_log)),
        admission,
        CancellationToken::new(),
    )
    .await;
    let EntailmentInvocationOutcome::Cancelled(CancelledEntailmentCheck::EmptyCheck {
        retained_proof: second_proof,
    }) = second.outcome()
    else {
        panic!("unexpected second outcome: {second:#?}")
    };

    assert_eq!(first_proof.attempt_id(), first_attempt.attempt_id());
    assert_eq!(second_proof.attempt_id(), second_attempt.attempt_id());
    assert_ne!(first_proof.attempt_id(), second_proof.attempt_id());
    assert_eq!(launch_count(&launch_log), 2);

    drop(entailment);
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn complete_model_is_reused_for_the_same_interrupted_attempt() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("entailment_model_reuse");
    let launch_log = directory.path().join("launches.log");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let admission = admission(2);
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let goal = prepare_one(
        &context,
        &admission,
        &artifacts,
        qf_source(&task, "task.phase2c_qf_fixture", &[], &[]),
    )
    .await;
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
    context.shutdown().await.unwrap();
    let attempt = artifacts.begin_entailment_attempt(&entailment).unwrap();

    let first = check_entailment_attempt_detailed(
        &entailment,
        &attempt,
        Duration::from_secs(5),
        VampireMode::FmbOnly(FmbOptions::default()),
        vampire_command("model", Some(&launch_log)),
        admission.clone(),
        CancellationToken::new(),
    )
    .await;
    let EntailmentInvocationOutcome::Result(EntailmentCheckResult::Refuted(first)) =
        first.outcome()
    else {
        panic!("expected the first complete model: {first:#?}")
    };
    let first_model = first.model().unwrap().clone();

    let second = check_entailment_attempt_detailed(
        &entailment,
        &attempt,
        Duration::from_secs(5),
        VampireMode::FmbOnly(FmbOptions::default()),
        vampire_command("model", Some(&launch_log)),
        admission,
        CancellationToken::new(),
    )
    .await;
    let EntailmentInvocationOutcome::Result(EntailmentCheckResult::Refuted(second)) =
        second.outcome()
    else {
        panic!("expected the retained complete model: {second:#?}")
    };
    let second_model = second.model().unwrap();
    assert_eq!(first_model.attempt_id(), second_model.attempt_id());
    assert_eq!(first_model.output(), second_model.output());
    assert_eq!(launch_count(&launch_log), 1);

    drop(entailment);
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn proof_survives_a_post_proof_empty_check_failure() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("entailment_reuse_failure");
    let launch_log = directory.path().join("launches.log");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let admission = admission(2);
    let context =
        new_solver_encoding_context(&task, &artifacts, malformed_empty_worker_config()).unwrap();
    let goal = prepare_one(
        &context,
        &admission,
        &artifacts,
        qf_source(&task, "task.phase2c_qf_fixture", &[], &[]),
    )
    .await;
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
    let attempt = artifacts.begin_entailment_attempt(&entailment).unwrap();

    for _ in 0..2 {
        let result = check_entailment_attempt_detailed(
            &entailment,
            &attempt,
            Duration::from_secs(5),
            VampireMode::ProofOnly,
            vampire_command("proof", Some(&launch_log)),
            admission.clone(),
            CancellationToken::new(),
        )
        .await;
        assert!(matches!(
            result.outcome(),
            EntailmentInvocationOutcome::Result(EntailmentCheckResult::Failure { .. })
        ));
    }
    assert_eq!(launch_count(&launch_log), 1);

    context.shutdown().await.unwrap();
    drop(entailment);
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}

// ------------------------------------------------------------
// Attempt Provenance
// ------------------------------------------------------------

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn attempt_artifacts_retain_complete_typed_provenance() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("entailment_provenance");
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let scoped = artifacts
        .scoped(ScopeTag::Inv)
        .scoped(ScopeTag::Catalog(7))
        .scoped(ScopeTag::Clause(11))
        .scoped(ScopeTag::Generation(3))
        .scoped(ScopeTag::Track(1))
        .scoped(ScopeTag::verification_stage("bulk-maint"));
    let admission = admission(2);
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let goal = prepare_one(
        &context,
        &admission,
        &artifacts,
        qf_source(&task, "task.phase2c_qf_fixture", &[], &[]),
    )
    .await;
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
    let required_before_attempt = artifacts.diagnostics().required_payloads_published;
    let manual_attempt = scoped.begin_entailment_attempt(&entailment).unwrap();
    assert!(
        manual_attempt
            .provenance()
            .contains(&ScopeTag::Attempt(manual_attempt.attempt_id()))
    );
    assert_eq!(manual_attempt.query_artifact(), entailment.query_artifact());
    assert_eq!(
        artifacts.diagnostics().required_payloads_published,
        required_before_attempt,
        "attempt allocation must not publish a payload"
    );
    let report = check_entailment_detailed(
        &entailment,
        &scoped,
        Some(Duration::from_secs(5)),
        VampireMode::ProofOnly,
        vampire_command("proof", None),
        admission,
        CancellationToken::new(),
    )
    .await;
    let terminal = report
        .terminal_artifact()
        .expect("a proof attempt publishes a terminal summary");
    let terminal: serde_json::Value = serde_json::from_str(
        &fs::read_to_string(artifacts.resolve(terminal).unwrap().path()).unwrap(),
    )
    .unwrap();
    assert_eq!(terminal["outcome"], "proved");
    assert_eq!(terminal["detail"]["proof_strategy"], "direct");
    let result = report.into_outcome();
    let EntailmentInvocationOutcome::Result(EntailmentCheckResult::Proved {
        proof,
        empty_evidence,
    }) = result
    else {
        panic!("expected a complete proof: {result:#?}")
    };
    assert_eq!(proof.attempt_id().get(), 1);
    assert_eq!(proof.query_artifact(), Some(entailment.query_artifact()));
    for reference in [proof.output(), empty_evidence.artifact()] {
        let resolved = artifacts.resolve(reference).unwrap();
        for expected in [
            "inv",
            "catalog:7",
            "clause:11",
            "generation:3",
            "track:1",
            "stage:bulk-maint",
            "entailment-attempt:1",
        ] {
            assert!(resolved.scope().iter().any(|tag| tag == expected));
        }
    }
    assert_eq!(
        artifacts
            .resolve(entailment.query_artifact())
            .unwrap()
            .kind(),
        ArtifactKind::Query
    );

    context.shutdown().await.unwrap();
    drop(entailment);
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn casc_winner_is_durable_in_the_entailment_terminal_summary() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("entailment_casc_provenance");
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let admission = admission(1);
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let goal = prepare_one(
        &context,
        &admission,
        &artifacts,
        qf_source(&task, "task.phase2c_qf_fixture", &[], &[]),
    )
    .await;
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
    let command = vampire_command("ladder-casc-only", None)
        .with_proof_casc_share(ProofCascShare::ONLY)
        .unwrap();
    let report = check_entailment_detailed(
        &entailment,
        &artifacts,
        Some(Duration::from_secs(5)),
        VampireMode::ProofOnly,
        command,
        admission,
        CancellationToken::new(),
    )
    .await;
    let terminal = report
        .terminal_artifact()
        .expect("a CASC proof publishes a terminal summary");
    let terminal: serde_json::Value = serde_json::from_str(
        &fs::read_to_string(artifacts.resolve(terminal).unwrap().path()).unwrap(),
    )
    .unwrap();
    assert_eq!(terminal["outcome"], "proved");
    assert_eq!(terminal["detail"]["proof_strategy"], "casc_2025");
    assert!(matches!(
        report.into_outcome(),
        EntailmentInvocationOutcome::Result(EntailmentCheckResult::Proved { .. })
    ));

    context.shutdown().await.unwrap();
    drop(entailment);
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn detailed_check_retains_attempt_and_terminal_summary() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("entailment_detailed");
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let admission = admission(2);
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let goal = prepare_one(
        &context,
        &admission,
        &artifacts,
        qf_source(&task, "task.phase2c_qf_fixture", &[], &[]),
    )
    .await;
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

    let report = check_entailment_detailed(
        &entailment,
        &artifacts,
        Some(Duration::from_millis(100)),
        VampireMode::ProofAndFmb(FmbOptions::default()),
        vampire_command("race-timeout", None),
        admission,
        CancellationToken::new(),
    )
    .await;

    let attempt_id = report.attempt_id().expect("the attempt was allocated");
    let terminal = report
        .terminal_artifact()
        .expect("a complete outcome has a terminal summary");
    assert_eq!(terminal.kind(), ArtifactKind::RuntimeTrace);
    let resolved = artifacts.resolve(terminal).unwrap();
    let summary: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(resolved.path()).unwrap()).unwrap();
    assert_eq!(summary["kind"], "entailment_attempt_terminal");
    assert_eq!(summary["attempt_id"], attempt_id.get());
    assert_eq!(summary["outcome"], "timed_out");
    let retained_frontier = summary["detail"]["next_fmb_start_size"].as_u64();
    assert!(
        matches!(retained_frontier, None | Some(1)),
        "the timeout summary may omit a frontier when cancellation wins before the fixture emits its first complete TRYING line"
    );
    assert!(matches!(
        report.into_outcome(),
        EntailmentInvocationOutcome::Result(EntailmentCheckResult::TimedOut { .. })
    ));

    context.shutdown().await.unwrap();
    drop(entailment);
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn detailed_check_accepts_a_preallocated_attempt_scope() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("entailment_preallocated");
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let admission = admission(2);
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let goal = prepare_one(
        &context,
        &admission,
        &artifacts,
        qf_source(&task, "task.phase2c_qf_fixture", &[], &[]),
    )
    .await;
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
    let attempt = artifacts.begin_entailment_attempt(&entailment).unwrap();

    let report = check_entailment_attempt_detailed(
        &entailment,
        &attempt,
        Some(Duration::from_millis(100)),
        VampireMode::ProofAndFmb(FmbOptions::default()),
        vampire_command("race-timeout", None),
        admission,
        CancellationToken::new(),
    )
    .await;

    assert_eq!(report.attempt_id(), Some(attempt.attempt_id()));
    assert!(report.terminal_artifact().is_some());
    assert!(matches!(
        report.into_outcome(),
        EntailmentInvocationOutcome::Result(EntailmentCheckResult::TimedOut { .. })
    ));

    context.shutdown().await.unwrap();
    drop(entailment);
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}

fn launch_count(path: &Path) -> usize {
    fs::read_to_string(path).unwrap_or_default().lines().count()
}
