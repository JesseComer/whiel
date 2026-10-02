mod support;

use whiel_runner::encoding::{
    EncodingWorkerCommand, EncodingWorkerPoolConfig, QfSolverSource, SolverBodySource,
    new_solver_encoding_context,
};
use whiel_runner::{
    ArtifactKind, ArtifactStoreConfig, CancellationToken, ClauseCatalog, ClauseFormula, ClauseSet,
    ConstantKey, FailureKind, InitCoverage, InitializationStatus, RegisteredClauses,
    RuntimeResourcePolicy, SolverAdmission, close_init_coverage, create_general_solver_admission,
    new_artifact_store, register_clauses,
};

// ------------------------------------------------------------
// Shared Phase 3A Fixtures
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

fn admission() -> SolverAdmission {
    create_general_solver_admission(RuntimeResourcePolicy::agent_only(2, 2).unwrap()).unwrap()
}

fn qf_source(
    task: &whiel_runner::SynthesisTask,
    source_id: &str,
    relations: &[&str],
) -> SolverBodySource {
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
    SolverBodySource::QuantifierFree(
        QfSolverSource::new(task, source_id, Vec::<ConstantKey>::new(), relations).unwrap(),
    )
}

fn formula(
    task: &whiel_runner::SynthesisTask,
    canonical: &str,
    source_id: &str,
    relations: &[&str],
) -> ClauseFormula {
    ClauseFormula::from_trusted_lean_source(canonical, qf_source(task, source_id, relations))
        .unwrap()
}

// ------------------------------------------------------------
// Exact Identity And Compact Records
// ------------------------------------------------------------

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn canonical_formula_identity_is_exact_and_clause_ids_are_dense() {
    let task = support::sample_task();
    let directory = support::TestDir::new("catalog_identity");
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let catalog = ClauseCatalog::new(&task, context.clone(), &artifacts).unwrap();

    let ordinary = formula(
        &task,
        "QFAssertExpr.eq ordinary",
        "catalog.clause.0",
        &["rel:E:0", "rel:TBound:0"],
    );
    let same_syntax_different_source = formula(
        &task,
        "QFAssertExpr.eq ordinary",
        "catalog.clause.0.alias",
        &["rel:E:0", "rel:TBound:0"],
    );
    let different_syntax_different_source = formula(
        &task,
        "QFAssertExpr.eq ordinary.distinct",
        "symbolic.w.1",
        &["rel:E:0", "rel:T:0", "rel:T:1", "rel:TBound:0"],
    );
    let invalid_source_alias = formula(
        &task,
        "QFAssertExpr.eq impossible-source-alias",
        "catalog.clause.0",
        &["rel:E:0", "rel:TBound:0"],
    );

    let first = catalog.register_proposed_clause(ordinary.clone()).unwrap();
    let repeated = catalog
        .register_proposed_clause(same_syntax_different_source)
        .unwrap();
    let second = catalog
        .register_proposed_clause(different_syntax_different_source)
        .unwrap();
    let source_alias_error = catalog
        .register_proposed_clause(invalid_source_alias)
        .unwrap_err();
    assert_eq!(
        source_alias_error.kind(),
        FailureKind::StateInvariantViolation
    );

    assert_eq!(first.get(), 0);
    assert_eq!(repeated, first);
    assert_eq!(second.get(), 1);
    assert_eq!(catalog.len(), 2);
    assert_eq!(catalog.find(&ordinary).unwrap(), Some(first));

    let record = catalog.record(first).unwrap();
    assert_eq!(record.formula().canonical(), ordinary.canonical());
    assert_eq!(record.formula().source().source_id(), "catalog.clause.0");
    assert!(record.formula_body().is_none());
    assert!(record.maintenance_wp().is_none());
    assert!(record.maintenance_wp_body().is_none());
    assert_eq!(record.initialization(), InitializationStatus::Unclassified);
    assert!(record.initialization_evidence().is_none());
    assert!(!record.explicitly_dropped());
    assert!(!record.has_retry_candidate());
    assert_eq!(record.next_retry_tier(), 0);
    assert!(!record.retry_exhausted());

    let candidates = ClauseSet::from([first, second]);
    assert_eq!(
        catalog.select_initialization_work(&candidates).unwrap(),
        candidates
    );
    assert!(catalog.select_init_proved(&candidates).unwrap().is_empty());

    let wrong_kind = catalog
        .artifacts()
        .publish(
            ArtifactKind::RuntimeTrace,
            b"not initialization evidence".as_slice().into(),
        )
        .unwrap();
    let wrong_kind_error = catalog
        .record_initialization(first, InitializationStatus::InitProved, wrong_kind)
        .unwrap_err();
    assert_eq!(wrong_kind_error.kind(), FailureKind::InfrastructureFailure);

    let first_inconclusive = catalog
        .artifacts()
        .publish(
            ArtifactKind::InitializationCheck,
            b"first inconclusive".as_slice().into(),
        )
        .unwrap();
    catalog
        .record_initialization(
            first,
            InitializationStatus::InitInconclusive,
            first_inconclusive,
        )
        .unwrap();
    assert_eq!(
        catalog.select_initialization_work(&candidates).unwrap(),
        candidates
    );

    let first_proof = catalog
        .artifacts()
        .publish(
            ArtifactKind::InitializationCheck,
            b"first proof".as_slice().into(),
        )
        .unwrap();
    catalog
        .record_initialization(first, InitializationStatus::InitProved, first_proof)
        .unwrap();
    let second_refutation = catalog
        .artifacts()
        .publish(
            ArtifactKind::InitializationCheck,
            b"second refutation".as_slice().into(),
        )
        .unwrap();
    catalog
        .record_initialization(second, InitializationStatus::InitRefuted, second_refutation)
        .unwrap();
    assert!(
        catalog
            .select_initialization_work(&candidates)
            .unwrap()
            .is_empty()
    );
    assert_eq!(
        catalog.select_init_proved(&candidates).unwrap(),
        ClauseSet::from([first])
    );

    let late_inconclusive = catalog
        .artifacts()
        .publish(
            ArtifactKind::InitializationCheck,
            b"late inconclusive".as_slice().into(),
        )
        .unwrap();
    catalog
        .record_initialization(
            first,
            InitializationStatus::InitInconclusive,
            late_inconclusive,
        )
        .unwrap();
    let first_record = catalog.record(first).unwrap();
    assert_eq!(
        first_record.initialization(),
        InitializationStatus::InitProved
    );
    assert_eq!(first_record.initialization_evidence(), Some(first_proof));

    let contradictory_refutation = catalog
        .artifacts()
        .publish(
            ArtifactKind::InitializationCheck,
            b"contradictory refutation".as_slice().into(),
        )
        .unwrap();
    let conflict = catalog
        .record_initialization(
            first,
            InitializationStatus::InitRefuted,
            contradictory_refutation,
        )
        .unwrap_err();
    assert_eq!(conflict.kind(), FailureKind::StateInvariantViolation);

    context.shutdown().await.unwrap();
    drop(catalog);
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}

// ------------------------------------------------------------
// Initialization Coverage
// ------------------------------------------------------------

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn init_coverage_closes_in_the_entailment_direction_without_reflexive_padding() {
    let task = support::sample_task();
    let directory = support::TestDir::new("init_coverage");
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let catalog = ClauseCatalog::new(&task, context.clone(), &artifacts).unwrap();
    let other_catalog = ClauseCatalog::new(&task, context.clone(), &artifacts).unwrap();

    let mut ids = Vec::new();
    for index in 0..5 {
        ids.push(
            catalog
                .register_proposed_clause(formula(
                    &task,
                    &format!("coverage.formula.{index}"),
                    &format!("coverage.source.{index}"),
                    &["rel:E:0", "rel:TBound:0"],
                ))
                .unwrap(),
        );
    }
    let [a, b, c, d, e] = ids.as_slice() else {
        panic!("five coverage fixtures")
    };
    let cross_catalog_source_alias = other_catalog
        .register_proposed_clause(formula(
            &task,
            "coverage.formula.conflicting-cross-catalog",
            "coverage.source.0",
            &["rel:E:0", "rel:TBound:0"],
        ))
        .unwrap_err();
    assert_eq!(
        cross_catalog_source_alias.kind(),
        FailureKind::StateInvariantViolation
    );

    let mut coverage = InitCoverage::new(&catalog);
    coverage.insert(&catalog, *a, *b).unwrap();
    coverage.insert(&catalog, *b, *c).unwrap();
    coverage.insert(&catalog, *d, *e).unwrap();
    coverage.insert(&catalog, *e, *d).unwrap();
    assert!(!coverage.is_transitively_closed());

    let cross_catalog = coverage.insert(&other_catalog, *a, *b).unwrap_err();
    assert_eq!(cross_catalog.kind(), FailureKind::InfrastructureFailure);

    let wrong_catalog_evidence = other_catalog
        .artifacts()
        .publish(
            ArtifactKind::InitializationCheck,
            b"wrong catalog".as_slice().into(),
        )
        .unwrap();
    let wrong_catalog_error = catalog
        .record_initialization(*a, InitializationStatus::InitProved, wrong_catalog_evidence)
        .unwrap_err();
    assert_eq!(
        wrong_catalog_error.kind(),
        FailureKind::InfrastructureFailure
    );

    close_init_coverage(&mut coverage);
    assert!(coverage.is_transitively_closed());
    assert!(coverage.contains(*a, *b));
    assert!(coverage.contains(*b, *c));
    assert!(coverage.contains(*a, *c));
    assert!(!coverage.contains(*c, *a));
    assert!(!coverage.contains(*a, *a));
    assert!(!coverage.contains(*b, *b));
    assert!(coverage.contains(*d, *d));
    assert!(coverage.contains(*d, *e));
    assert!(coverage.contains(*e, *d));
    assert!(coverage.contains(*e, *e));

    let closed_edge_count = coverage.edge_count();
    close_init_coverage(&mut coverage);
    assert_eq!(coverage.edge_count(), closed_edge_count);

    context.shutdown().await.unwrap();
    drop(other_catalog);
    drop(catalog);
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}

// ------------------------------------------------------------
// Caller-Neutral Body Preparation
// ------------------------------------------------------------

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn registration_prepares_ordinary_and_w_clauses_through_one_generic_path() {
    let task = support::sample_task();
    let directory = support::TestDir::new("catalog_body_preparation");
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let catalog = ClauseCatalog::new(&task, context.clone(), &artifacts).unwrap();
    let admission = admission();

    let ordinary = formula(
        &task,
        "Certificate.clause0",
        "catalog.clause.0",
        &["rel:E:0", "rel:TBound:0"],
    );
    let w_zero = formula(
        &task,
        "WLayer.formula inputPreproc 0",
        "symbolic.w.0",
        &["rel:E:0", "rel:T:0", "rel:T:1", "rel:TBound:0"],
    );
    let registered = register_clauses(
        &catalog,
        &admission,
        [ordinary.clone(), w_zero.clone()],
        &CancellationToken::new(),
    )
    .await;
    assert!(!registered.was_cancelled());
    assert!(registered.failure().is_none());
    assert_eq!(registered.complete_clauses().unwrap().len(), 2);

    let ordinary_id = catalog.find(&ordinary).unwrap().unwrap();
    let w_zero_id = catalog.find(&w_zero).unwrap().unwrap();
    let ordinary_record = catalog.record(ordinary_id).unwrap();
    let w_zero_record = catalog.record(w_zero_id).unwrap();
    let ordinary_body = ordinary_record.formula_body().unwrap();
    let w_zero_body = w_zero_record.formula_body().unwrap();
    assert_eq!(ordinary_body.source().source_id(), "catalog.clause.0");
    assert_eq!(w_zero_body.source().source_id(), "symbolic.w.0");
    assert_eq!(ordinary_body.context_id(), context.context_id());
    assert_eq!(w_zero_body.context_id(), context.context_id());
    assert!(!ordinary_body.tptp_body().is_empty());
    assert!(!w_zero_body.tptp_body().is_empty());

    let repeated = register_clauses(
        &catalog,
        &admission,
        [ordinary, w_zero],
        &CancellationToken::new(),
    )
    .await;
    assert!(repeated.failure().is_none());
    assert_eq!(catalog.len(), 2);
    assert_eq!(
        catalog
            .record(ordinary_id)
            .unwrap()
            .formula_body()
            .unwrap()
            .body_id(),
        ordinary_body.body_id()
    );
    assert_eq!(
        catalog
            .record(w_zero_id)
            .unwrap()
            .formula_body()
            .unwrap()
            .body_id(),
        w_zero_body.body_id()
    );

    context.shutdown().await.unwrap();
    drop(catalog);
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn one_failed_body_preparation_retains_a_completed_sibling() {
    let task = support::sample_task();
    let directory = support::TestDir::new("catalog_partial_body_preparation");
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let catalog = ClauseCatalog::new(&task, context.clone(), &artifacts).unwrap();
    let admission = admission();
    let valid = formula(
        &task,
        "QFAssertExpr.partial.valid",
        "catalog.clause.0",
        &["rel:E:0", "rel:TBound:0"],
    );
    let invalid = formula(
        &task,
        "QFAssertExpr.partial.invalid",
        "catalog.missing.source",
        &["rel:E:0", "rel:TBound:0"],
    );

    let outcome = register_clauses(
        &catalog,
        &admission,
        [valid.clone(), invalid.clone()],
        &CancellationToken::new(),
    )
    .await;
    let RegisteredClauses::Failure {
        retained_registrations,
        ..
    } = outcome
    else {
        panic!("one rejected worker source must fail the complete batch")
    };
    assert_eq!(retained_registrations.len(), 2);
    let valid_id = catalog.find(&valid).unwrap().unwrap();
    let invalid_id = catalog.find(&invalid).unwrap().unwrap();
    assert!(catalog.record(valid_id).unwrap().formula_body().is_some());
    assert!(catalog.record(invalid_id).unwrap().formula_body().is_none());

    context.shutdown().await.unwrap();
    drop(catalog);
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn cancelled_body_preparation_is_not_a_usable_batch_and_retries_in_place() {
    let task = support::sample_task();
    let directory = support::TestDir::new("catalog_cancelled_preparation");
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let catalog = ClauseCatalog::new(&task, context.clone(), &artifacts).unwrap();
    let admission = admission();
    let clause = formula(
        &task,
        "QFAssertExpr.cancelled.preparation",
        "catalog.clause.0",
        &["rel:E:0", "rel:TBound:0"],
    );
    let cancellation = CancellationToken::new();
    cancellation.cancel();

    let cancelled = register_clauses(&catalog, &admission, [clause.clone()], &cancellation).await;
    let RegisteredClauses::Cancelled {
        retained_registrations,
    } = cancelled
    else {
        panic!("cancelled preparation must remain outer control flow")
    };
    assert_eq!(retained_registrations.len(), 1);
    let id = *retained_registrations.iter().next().unwrap();
    assert!(catalog.record(id).unwrap().formula_body().is_none());

    let completed =
        register_clauses(&catalog, &admission, [clause], &CancellationToken::new()).await;
    assert_eq!(completed.complete_clauses(), Some(&ClauseSet::from([id])));
    assert!(catalog.record(id).unwrap().formula_body().is_some());
    assert_eq!(catalog.len(), 1);

    let cancelled_warm = CancellationToken::new();
    cancelled_warm.cancel();
    let warm_outcome = register_clauses(
        &catalog,
        &admission,
        [catalog.record(id).unwrap().formula().clone()],
        &cancelled_warm,
    )
    .await;
    assert!(matches!(warm_outcome, RegisteredClauses::Cancelled { .. }));

    context.shutdown().await.unwrap();
    drop(catalog);
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}
