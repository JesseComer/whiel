mod support;

use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use serde_json::json;
use whiel_runner::encoding::{
    EncodingWorkerCommand, EncodingWorkerPoolConfig, QfSolverSource, SolverBodySource,
    new_solver_encoding_context,
};
use whiel_runner::{
    ArtifactKind, ArtifactStoreConfig, CancellationToken, CertificationBridgeCommand,
    CertificationInstance, CertificationRuntime, ClauseCatalog, ClauseFormula, ClauseSet,
    ConstantKey, FailureKind, FailureOrigin, HoudiniExecutionOutcome, HoudiniState,
    InitializationInvocationOutcome, InitializationStatus, InvalidityCertificationOutcome,
    MaintenancePreparationOutcome, RuntimeResourcePolicy, ValidityCertificationOutcome,
    VampireWorkerCommand, VerificationParameters, certify_invalid, certify_valid,
    create_general_solver_admission, houdini, new_artifact_store, prepare_maintenance, term_check,
};

static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

const CLAUSE_0: &str = "(E ∪ (π[0, 3] (σ[#1 = #2] (TBound × E)))) ⊆ TBound";
const CLAUSE_2: &str = "T ⊆ TBound";

struct RepositoryDirectory(PathBuf);

impl RepositoryDirectory {
    fn new(label: &str) -> Self {
        let sequence = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock must follow Unix epoch")
            .as_nanos();
        let path = support::repository_root().join(format!(
            "whiel_runner/target/certification-guard-{label}-{}-{nanos}-{sequence}",
            std::process::id()
        ));
        fs::create_dir_all(&path).expect("create wrapper-test directory");
        // Canonicalize so path equality survives symlinked
        // build directories.
        let path = path.canonicalize().expect("canonicalize");
        Self(path)
    }

    fn path(&self) -> &Path {
        &self.0
    }
}

impl Drop for RepositoryDirectory {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn command(mode: &str) -> CertificationBridgeCommand {
    let repository = support::repository_root();
    CertificationBridgeCommand::new("python3", &repository).with_arguments([
        repository
            .join("whiel_runner/tests/fixtures/fake_certification_bridge.py")
            .into_os_string(),
        mode.into(),
    ])
}

fn runtime(directory: &RepositoryDirectory, mode: &str) -> CertificationRuntime {
    CertificationRuntime::new(
        command(mode),
        directory.path().join("bridge-work"),
        directory.path().join("solution"),
    )
}

fn verification() -> VerificationParameters {
    let resources = RuntimeResourcePolicy::agent_only(2, 1).expect("valid resource policy");
    VerificationParameters::new(Duration::from_secs(5), resources)
        .expect("positive search limit")
        .with_final_certification_limit(Some(Duration::from_secs(5)))
        .expect("positive certification limit")
}

fn empty_instance() -> serde_json::Value {
    json!({"E": [], "T": [], "T_2": [], "TBound": []})
}

fn artifact_json(
    artifacts: &whiel_runner::ArtifactStore,
    reference: whiel_runner::ArtifactRef,
) -> serde_json::Value {
    let resolved = artifacts
        .resolve(reference)
        .expect("resolve required record");
    serde_json::from_slice(&fs::read(resolved.path()).expect("read required record"))
        .expect("decode required record")
}

fn fixture_vampire() -> VampireWorkerCommand {
    VampireWorkerCommand::new(support::fake_vampire())
        .with_extra_args(["--fixture", "race-proof-fast", "--expect-start", "1"])
        .expect("valid fixture Vampire arguments")
}

fn formula(
    task: &whiel_runner::SynthesisTask,
    canonical: &str,
    source_id: &str,
    relations: &[&str],
) -> ClauseFormula {
    let relations = relations
        .iter()
        .map(|key| {
            task.solver_relations()
                .iter()
                .find(|relation| relation.key().as_str() == *key)
                .expect("known fixture relation")
                .key()
                .clone()
        })
        .collect::<Vec<_>>();
    let source = SolverBodySource::QuantifierFree(
        QfSolverSource::new(task, source_id, Vec::<ConstantKey>::new(), relations)
            .expect("trusted source"),
    );
    ClauseFormula::from_trusted_lean_source(canonical, source).expect("trusted formula")
}

#[test]
fn typed_instance_rejects_schema_and_tuple_errors() {
    let task = support::sample_task();
    assert!(CertificationInstance::from_json(&task, empty_instance()).is_ok());
    assert!(CertificationInstance::from_json(&task, json!({"E": []})).is_err());
    assert!(
        CertificationInstance::from_json(
            &task,
            json!({"E": [[0]], "T": [], "T_2": [], "TBound": []}),
        )
        .is_err()
    );
    assert!(
        CertificationInstance::from_json(
            &task,
            json!({"E": [[0, 1], [0, 1]], "T": [], "T_2": [], "TBound": []}),
        )
        .is_err()
    );
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn invalidity_wrapper_preserves_certified_and_rejected_outcomes() {
    for (mode, certified) in [("success", true), ("rejected", false)] {
        let task = support::sample_task();
        let directory = RepositoryDirectory::new(mode);
        let (owner, artifacts) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(directory.path().join("artifacts")),
        )
        .expect("artifact store");
        let verification = verification();
        let input = CertificationInstance::from_json(&task, empty_instance())
            .expect("schema-complete source Instance");

        let outcome = certify_invalid(
            &task,
            &verification,
            &artifacts,
            &input,
            &runtime(&directory, mode),
            &CancellationToken::new(),
        )
        .await;
        if certified {
            let InvalidityCertificationOutcome::Certified(result) = outcome else {
                panic!("fixture success must certify");
            };
            assert_eq!(
                artifacts.resolve(result.certificate).unwrap().kind(),
                ArtifactKind::Certificate
            );
            assert_eq!(
                artifacts.resolve(result.witness).unwrap().kind(),
                ArtifactKind::Witness
            );
            assert_eq!(
                artifacts.resolve(result.record).unwrap().kind(),
                ArtifactKind::AcceptanceRecord
            );
            let record = artifact_json(&artifacts, result.record);
            assert_eq!(
                record["fields"]["task_identity"]["canonical_id"],
                task.identity().canonical_id()
            );
            assert_eq!(record["fields"]["logical_input"]["input_byte_len"], 36);
            assert!(record["fields"]["details"]["witness_sha256"].is_string());
            assert_eq!(record["fields"]["evidence"].as_array().unwrap().len(), 1);
            assert_eq!(record["status"], "invalidity_authority_accepted");
        } else {
            let InvalidityCertificationOutcome::Rejected(feedback) = outcome else {
                panic!("complete negative source check must remain Rejected");
            };
            assert_eq!(feedback.task_identity(), task.identity());
            assert_eq!(feedback.backend_id(), artifacts.backend_id());
            assert_eq!(feedback.artifact_references().len(), 1);
            let record = artifact_json(&artifacts, feedback.artifact_references()[0]);
            assert_eq!(
                record["fields"]["task_identity"]["source_sha256"],
                task.identity().source_digest().as_str()
            );
            assert!(record["fields"]["logical_input"]["input_sha256"].is_string());
        }
        drop(artifacts);
        owner.settle().expect("all bridge work was joined");
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn validity_wrapper_certifies_the_exact_stopped_core_with_provenance() {
    let task = support::export_canonical_task();
    let directory = RepositoryDirectory::new("valid-success");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .expect("artifact store");
    let workers = EncodingWorkerPoolConfig::new(
        EncodingWorkerCommand::new(
            support::example_encoding_worker(),
            support::repository_root(),
        ),
        2,
    )
    .expect("positive worker count");
    let context =
        new_solver_encoding_context(&task, &artifacts, workers).expect("encoding context");
    let verification = verification().with_bulk_maint_limit(Duration::ZERO);
    let admission =
        create_general_solver_admission(verification.resources()).expect("valid admission");
    let catalog = ClauseCatalog::new(&task, context.clone(), &artifacts).expect("Catalog");
    let mut state =
        HoudiniState::new(&task, verification, admission, catalog).expect("coherent state");
    let cancellation = CancellationToken::new();

    assert!(matches!(
        state
            .prepare_init_candidates(
                vec![
                    formula(
                        &task,
                        CLAUSE_2,
                        "catalog.clause.2",
                        &["rel:T:0", "rel:TBound:0"],
                    ),
                    formula(
                        &task,
                        CLAUSE_0,
                        "catalog.clause.0",
                        &["rel:E:0", "rel:TBound:0"],
                    ),
                ],
                &ClauseSet::new(),
                &cancellation,
            )
            .await,
        InitializationInvocationOutcome::Complete
    ));
    let clauses = state.init_candidates().clone();
    assert_eq!(clauses.len(), 2);
    let init_evidence = state
        .catalog()
        .artifacts()
        .publish(
            ArtifactKind::InitializationCheck,
            b"fixture InitProved".as_slice().into(),
        )
        .expect("initialization evidence");
    for clause in &clauses {
        state
            .catalog()
            .record_initialization(*clause, InitializationStatus::InitProved, init_evidence)
            .expect("record initialization");
        state
            .insert_maint_support(*clause, *clause)
            .expect("reflexive maintenance support");
    }
    assert!(matches!(
        prepare_maintenance(&task, &mut state, &cancellation).await,
        MaintenancePreparationOutcome::Complete
    ));
    assert!(matches!(
        houdini(&task, &mut state, fixture_vampire(), &cancellation).await,
        HoudiniExecutionOutcome::Complete
    ));
    assert_eq!(state.core(), &clauses);
    assert!(matches!(
        term_check(&task, &mut state, fixture_vampire(), &cancellation).await,
        whiel_runner::TerminationInvocationOutcome::Complete
    ));

    let outcome = certify_valid(
        &task,
        &mut state,
        &runtime(&directory, "success"),
        &cancellation,
    )
    .await;
    let ValidityCertificationOutcome::Certified(result) = outcome else {
        panic!("exact stopped Core must certify: {outcome:#?}");
    };
    assert_eq!(
        artifacts.resolve(result.certificate).unwrap().kind(),
        ArtifactKind::Certificate
    );
    let record = artifact_json(&artifacts, result.record);
    assert_eq!(record["status"], "validity_authority_accepted");
    assert_eq!(record["fields"]["logical_input"]["core_member_count"], 2);
    assert_eq!(
        record["fields"]["logical_input"]["core_byte_len"],
        serde_json::to_vec(&[CLAUSE_0, CLAUSE_2]).unwrap().len()
    );
    assert!(record["fields"]["logical_input"]["core_sha256"].is_string());
    assert!(record["fields"]["details"]["certificate_sha256"].is_string());

    context.shutdown().await.expect("encoding context shutdown");
    drop(state);
    drop(context);
    drop(artifacts);
    owner.settle().expect("all owned work stopped");
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn invalidity_wrapper_permits_only_one_unchanged_transient_retry() {
    let task = support::sample_task();
    let directory = RepositoryDirectory::new("transient-retry");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .expect("artifact store");
    let verification = verification();
    let input = CertificationInstance::from_json(&task, empty_instance())
        .expect("schema-complete source Instance");
    let runtime = runtime(&directory, "transient_timeout");

    for expected_retryable in [true, false] {
        let outcome = certify_invalid(
            &task,
            &verification,
            &artifacts,
            &input,
            &runtime,
            &CancellationToken::new(),
        )
        .await;
        let InvalidityCertificationOutcome::Failure(report) = outcome else {
            panic!("fixture timeout must be a typed failure");
        };
        assert_eq!(report.kind(), FailureKind::CheckTimeout);
        assert_eq!(report.retryable(), expected_retryable);
    }

    drop(artifacts);
    owner.settle().expect("all bridge work was joined");
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn invalidity_retry_identity_includes_run_and_configuration() {
    let task = support::sample_task();
    let directory = RepositoryDirectory::new("retry-identity");
    let runtime = runtime(&directory, "transient_timeout");
    let input = CertificationInstance::from_json(&task, empty_instance())
        .expect("schema-complete source Instance");

    for search_seconds in [5, 6] {
        let (owner, artifacts) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(directory.path().join(format!("artifacts-{search_seconds}"))),
        )
        .expect("artifact store");
        let verification = VerificationParameters::new(
            Duration::from_secs(search_seconds),
            RuntimeResourcePolicy::agent_only(2, 1).expect("valid resource policy"),
        )
        .expect("positive search limit")
        .with_final_certification_limit(Some(Duration::from_secs(5)))
        .expect("positive certification limit");
        let outcome = certify_invalid(
            &task,
            &verification,
            &artifacts,
            &input,
            &runtime,
            &CancellationToken::new(),
        )
        .await;
        let InvalidityCertificationOutcome::Failure(report) = outcome else {
            panic!("fixture timeout must be a typed failure");
        };
        assert!(report.retryable(), "fresh run/configuration gets one retry");
        drop(artifacts);
        owner.settle().expect("all bridge work was joined");
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn deterministic_invalidity_failure_is_never_retryable() {
    let task = support::sample_task();
    let directory = RepositoryDirectory::new("deterministic-failure");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .expect("artifact store");
    let input = CertificationInstance::from_json(&task, empty_instance())
        .expect("schema-complete source Instance");
    let outcome = certify_invalid(
        &task,
        &verification(),
        &artifacts,
        &input,
        &runtime(&directory, "deterministic_infrastructure"),
        &CancellationToken::new(),
    )
    .await;
    let InvalidityCertificationOutcome::Failure(report) = outcome else {
        panic!("deterministic fixture must be a typed failure");
    };
    assert_eq!(report.kind(), FailureKind::InfrastructureFailure);
    assert!(!report.retryable());

    drop(artifacts);
    owner.settle().expect("all bridge work was joined");
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn validity_wrapper_refuses_a_core_without_proved_term() {
    let task = support::sample_task();
    let directory = RepositoryDirectory::new("pending-term");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .expect("artifact store");
    let workers = EncodingWorkerPoolConfig::new(
        EncodingWorkerCommand::new("/usr/bin/false", support::repository_root()),
        1,
    )
    .expect("positive worker count");
    let context =
        new_solver_encoding_context(&task, &artifacts, workers).expect("encoding context");
    let verification = verification();
    let admission =
        create_general_solver_admission(verification.resources()).expect("valid solver admission");
    let catalog = ClauseCatalog::new(&task, context.clone(), &artifacts).expect("Catalog");
    let mut state =
        HoudiniState::new(&task, verification, admission, catalog).expect("coherent Houdini state");

    let outcome = certify_valid(
        &task,
        &mut state,
        &runtime(&directory, "success"),
        &CancellationToken::new(),
    )
    .await;
    let ValidityCertificationOutcome::Failure(report) = outcome else {
        panic!("Pending Term must block certification before bridge launch");
    };
    assert_eq!(report.origin(), FailureOrigin::ValidityCertification);
    assert_eq!(report.kind(), FailureKind::InfrastructureFailure);
    assert!(!directory.path().join("solution").exists());

    context.shutdown().await.expect("encoding context shutdown");
    drop(state);
    drop(context);
    drop(artifacts);
    owner.settle().expect("all owned work stopped");
}
