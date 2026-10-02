mod support;

use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use whiel_runner::encoding::{
    EncodingWorkerCommand, EncodingWorkerPoolConfig, QfSolverSource, SolverBodySource,
    SolverEncodingContext, new_solver_encoding_context,
};
use whiel_runner::{
    ArtifactBackendOwner, ArtifactStore, ArtifactStoreConfig, CancellationToken,
    CertificationBridgeCommand, CertificationRuntime, ClauseCatalog, ClauseFormula, ClauseId,
    ClauseSet, ConstantKey, HoudiniExecutionOutcome, HoudiniState, InitializationInvocationOutcome,
    InitializationStatus, LastTermStatus, MaintenancePreparationOutcome, MaintenanceResultClass,
    RuntimeResourcePolicy, SolverAdmission, TerminationInvocationOutcome,
    ValidityCertificationOutcome, VampireWorkerCommand, VerificationParameters, certify_valid,
    check_initialization, create_general_solver_admission, houdini, new_artifact_store,
    prepare_maintenance, term_check,
};

static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

const CLAUSE_0: &str = "(E ∪ (π[0, 3] (σ[#1 = #2] (TBound × E)))) ⊆ TBound";
const CLAUSE_1: &str = "(E ∪ (π[0, 3] (σ[#1 = #2] (T_2 × E)))) ⊆ T";
const CLAUSE_2: &str = "T ⊆ TBound";

// ------------------------------------------------------------
// External Integration Fixtures
// ------------------------------------------------------------

struct RepositoryDirectory(PathBuf);

impl RepositoryDirectory {
    fn new(label: &str) -> Self {
        let sequence = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock must follow Unix epoch")
            .as_nanos();
        let path = support::repository_root().join(format!(
            "whiel_runner/target/phase3e-{label}-{}-{nanos}-{sequence}",
            std::process::id()
        ));
        fs::create_dir_all(&path).expect("create Phase 3E repository directory");
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

fn real_vampire_command() -> VampireWorkerCommand {
    let executable = std::env::var_os("VAMPIRE_BIN")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("/opt/vampire/build/vampire"));
    assert!(
        executable.is_file(),
        "set VAMPIRE_BIN to the real Vampire executable; missing {}",
        executable.display()
    );
    VampireWorkerCommand::new(executable)
}

fn admission(policy: RuntimeResourcePolicy) -> SolverAdmission {
    create_general_solver_admission(policy).expect("valid solver admission")
}

fn new_state(
    task: &whiel_runner::SynthesisTask,
    artifacts: &ArtifactStore,
    context: &SolverEncodingContext,
    bulk_maint_limit: Duration,
) -> HoudiniState {
    let resources = RuntimeResourcePolicy::agent_only(4, 2).expect("valid runtime policy");
    let verification = VerificationParameters::new(Duration::from_secs(60), resources)
        .expect("positive search limit")
        .with_bulk_maint_limit(bulk_maint_limit)
        .with_search_term_limit(Duration::from_secs(60))
        .expect("positive termination limit");
    let catalog = ClauseCatalog::new(task, context.clone(), artifacts).expect("valid Catalog");
    HoudiniState::new(task, verification, admission(resources), catalog)
        .expect("coherent Houdini state")
}

fn fixture_vampire_command(fixture: &str, launch_log: &Path) -> VampireWorkerCommand {
    VampireWorkerCommand::new(support::fake_vampire())
        .with_extra_args([
            OsString::from("--fixture"),
            OsString::from(fixture),
            OsString::from("--expect-start"),
            OsString::from("1"),
            OsString::from("--launch-log"),
            launch_log.as_os_str().to_owned(),
        ])
        .expect("valid fake Vampire arguments")
}

fn launch_count(path: &Path) -> usize {
    fs::read_to_string(path).unwrap_or_default().lines().count()
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
                .unwrap_or_else(|| panic!("unknown fixture relation {key}"))
                .key()
                .clone()
        })
        .collect::<Vec<_>>();
    let source = SolverBodySource::QuantifierFree(
        QfSolverSource::new(task, source_id, Vec::<ConstantKey>::new(), relations)
            .expect("valid trusted QF source"),
    );
    ClauseFormula::from_trusted_lean_source(canonical, source).expect("nonempty trusted formula")
}

fn known_valid_proposal(task: &whiel_runner::SynthesisTask) -> Vec<ClauseFormula> {
    vec![
        formula(
            task,
            CLAUSE_0,
            "catalog.clause.0",
            &["rel:E:0", "rel:TBound:0"],
        ),
        formula(
            task,
            CLAUSE_1,
            "catalog.clause.1",
            &["rel:E:0", "rel:T:1", "rel:T:0"],
        ),
        formula(
            task,
            CLAUSE_2,
            "catalog.clause.2",
            &["rel:T:0", "rel:TBound:0"],
        ),
    ]
}

async fn run_initialization(
    task: &whiel_runner::SynthesisTask,
    state: &mut HoudiniState,
    proposed: Vec<ClauseFormula>,
    command: &VampireWorkerCommand,
) -> Vec<ClauseId> {
    let cancellation = CancellationToken::new();
    assert!(matches!(
        state
            .prepare_init_candidates(proposed, &ClauseSet::new(), &cancellation)
            .await,
        InitializationInvocationOutcome::Complete
    ));
    assert!(matches!(
        check_initialization(task, state, command.clone(), &cancellation).await,
        InitializationInvocationOutcome::Complete
    ));
    assert!(state.maintenance_failure().is_none());
    let mut ids = state.init_candidates().iter().copied().collect::<Vec<_>>();
    ids.sort_unstable();
    for id in &ids {
        assert_eq!(
            state.catalog().record(*id).unwrap().initialization(),
            InitializationStatus::InitProved,
            "the real initialization authority must prove clause {}",
            id.get()
        );
    }
    ids
}

async fn prepare_and_run_houdini(
    task: &whiel_runner::SynthesisTask,
    state: &mut HoudiniState,
    command: &VampireWorkerCommand,
) {
    let cancellation = CancellationToken::new();
    assert!(matches!(
        prepare_maintenance(task, state, &cancellation).await,
        MaintenancePreparationOutcome::Complete
    ));
    assert!(matches!(
        houdini(task, state, command.clone(), &cancellation).await,
        HoudiniExecutionOutcome::Complete
    ));
    assert!(state.maintenance_failure().is_none());
    assert!(state.active().is_empty());
    assert!(state.maintenance_plan().is_none());
}

fn assert_established_validity_certificate_shape(source: &str) {
    // Split-certificate shape (leancertificate migration, 2026-08-16):
    // one obligation per core clause, tier-stable per-obligation names,
    // generic assembly to the source Hoare triple.
    for marker in [
        "def candidateClause0 : QFAssertExpr Data programSchema :=",
        "def candidateClauses :",
        "def initQF0 : QFEntailment",
        "def stepQF0 : QFEntailment",
        "def termQF : QFEntailment",
        "Synthesis.ClauseObligation.init",
        "Synthesis.ClauseObligation.step",
        "Synthesis.ClauseObligation.termCandidate",
        "def jobs : List Vampire.Job :=",
        "def writeManifest (root : System.FilePath) :",
        "theorem init_no_empty_all",
        "theorem step_no_empty_all",
        "theorem term_no_empty",
        "axiom candidate_init_clause_0_fol_valid",
        "axiom candidate_step_clause_0_fol_valid",
        "axiom candidate_term_fol_valid",
        "theorem candidate_init_fol_facts",
        "theorem candidate_step_fol_facts",
        "theorem input_hoare_triple_valid",
        "Synthesis.SplitCertificate.hoareValid_of_perClause_fol",
    ] {
        assert!(
            source.contains(marker),
            "certificate omits established shape marker {marker:?}"
        );
    }
}

async fn shutdown(
    state: HoudiniState,
    context: SolverEncodingContext,
    artifacts: ArtifactStore,
    owner: ArtifactBackendOwner,
) {
    context.shutdown().await.expect("encoding worker shutdown");
    drop(state);
    drop(context);
    drop(artifacts);
    owner.settle().expect("artifact settlement");
}

// ------------------------------------------------------------
// Live Phase 3E Firewall Tests
// ------------------------------------------------------------

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
#[ignore = "live Lean, Vampire, and legacy certification integration"]
async fn known_valid_proposal_reaches_the_unchanged_real_certificate_shape() {
    let task = support::export_canonical_task();
    let directory = RepositoryDirectory::new("valid-firewall");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("runtime-artifacts")),
    )
    .expect("artifact store");
    let context =
        new_solver_encoding_context(&task, &artifacts, worker_config()).expect("encoding context");
    let mut state = new_state(&task, &artifacts, &context, Duration::from_secs(60));
    let vampire = real_vampire_command();

    let ids = run_initialization(&task, &mut state, known_valid_proposal(&task), &vampire).await;
    assert_eq!(ids.len(), 3);
    prepare_and_run_houdini(&task, &mut state, &vampire).await;
    assert_eq!(state.core().len(), 3);

    assert!(matches!(
        term_check(
            &task,
            &mut state,
            vampire.clone(),
            &CancellationToken::new(),
        )
        .await,
        TerminationInvocationOutcome::Complete
    ));
    assert!(matches!(state.last_term_status(), LastTermStatus::Proved));

    let solution = directory.path().join("solution");
    let runtime = CertificationRuntime::new(
        CertificationBridgeCommand::python(support::repository_root()),
        directory.path().join("certification-work"),
        &solution,
    )
    .with_max_heartbeats(4_000_000)
    .expect("positive heartbeat limit");
    let outcome = certify_valid(&task, &mut state, &runtime, &CancellationToken::new()).await;
    let ValidityCertificationOutcome::Certified(certified) = outcome else {
        panic!("known-valid exact Core did not certify: {outcome:#?}");
    };
    let certificate = artifacts
        .resolve(certified.certificate)
        .expect("retained generated certificate");
    assert_eq!(certificate.kind(), whiel_runner::ArtifactKind::Certificate);
    let generated = fs::read_to_string(certificate.path()).expect("generated certificate");
    assert_established_validity_certificate_shape(&generated);
    let lean = Command::new("lake")
        .args(["env", "lean"])
        .arg(certificate.path())
        .current_dir(support::repository_root())
        .output()
        .expect("launch final Lean certificate audit");
    assert!(
        lean.status.success(),
        "published certificate failed final Lean audit\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&lean.stdout),
        String::from_utf8_lossy(&lean.stderr),
    );

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
#[ignore = "live Lean, Vampire, and legacy certification integration"]
async fn final_certification_rejects_core_contaminated_by_invalid_coverage() {
    let task = support::export_canonical_task();
    let directory = RepositoryDirectory::new("poisoned-firewall");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("runtime-artifacts")),
    )
    .expect("artifact store");
    let context =
        new_solver_encoding_context(&task, &artifacts, worker_config()).expect("encoding context");
    let mut state = new_state(&task, &artifacts, &context, Duration::ZERO);
    let vampire = real_vampire_command();

    // `true` and Clause 2 really pass initialization.  The caller-supplied
    // edge `true -> Clause 2` is nevertheless false MaintCoverage: maintaining
    // `true` does not imply that the loop maintains Clause 2.  Generic Houdini
    // intentionally trusts the relation supplied by its producer.
    let ids = run_initialization(
        &task,
        &mut state,
        vec![
            formula(&task, "true", "task.phase2c_qf_fixture", &[]),
            formula(
                &task,
                CLAUSE_2,
                "catalog.clause.2",
                &["rel:T:0", "rel:TBound:0"],
            ),
        ],
        &vampire,
    )
    .await;
    assert_eq!(ids.len(), 2);
    let source = ids[0];
    let poisoned = ids[1];
    state
        .insert_maint_coverage(source, poisoned)
        .expect("caller-supplied coverage relation");
    let launch_log = directory.path().join("maintenance-launches");
    prepare_and_run_houdini(
        &task,
        &mut state,
        &fixture_vampire_command("race-proof-fast", &launch_log),
    )
    .await;
    assert_eq!(state.core(), &ClauseSet::from([source, poisoned]));
    assert_eq!(
        launch_count(&launch_log),
        2,
        "only the proof/FMB pair for the live coverage source may launch"
    );
    assert_eq!(
        state
            .catalog()
            .record(source)
            .expect("source record")
            .latest_maintenance()
            .expect("source was queried")
            .class(),
        MaintenanceResultClass::Proved
    );
    assert!(
        state
            .catalog()
            .record(poisoned)
            .expect("covered target record")
            .latest_maintenance()
            .is_none(),
        "the poisoned target must enter Core through coverage, not Vampire"
    );

    // Simulate an unsound search-time Term proof so this regression crosses
    // the same state-bound production guard as a real synthesis result.  The
    // fresh final authority must still reject the poisoned exact Core.
    let term_log = directory.path().join("termination-launches");
    assert!(matches!(
        term_check(
            &task,
            &mut state,
            fixture_vampire_command("race-proof-fast", &term_log),
            &CancellationToken::new(),
        )
        .await,
        TerminationInvocationOutcome::Complete
    ));
    assert!(matches!(state.last_term_status(), LastTermStatus::Proved));

    let solution = directory.path().join("solution");
    let runtime = CertificationRuntime::new(
        CertificationBridgeCommand::python(support::repository_root()),
        directory.path().join("certification-work"),
        &solution,
    )
    .with_max_heartbeats(4_000_000)
    .expect("positive heartbeat limit");
    let outcome = certify_valid(&task, &mut state, &runtime, &CancellationToken::new()).await;
    let ValidityCertificationOutcome::Failure(failure) = outcome else {
        panic!("fresh certification accepted a Core poisoned by invalid coverage: {outcome:#?}");
    };
    assert_eq!(
        failure.origin(),
        whiel_runner::FailureOrigin::ValidityCertification
    );
    assert!(
        !failure.artifact_references().is_empty(),
        "final-certification rejection must retain diagnostic evidence"
    );
    assert!(
        !solution.exists(),
        "rejected certification published a bundle"
    );

    shutdown(state, context, artifacts, owner).await;
}
