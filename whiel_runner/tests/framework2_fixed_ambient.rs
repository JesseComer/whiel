//! Live fixed-ambient integration coverage.
//!
//! Every test binds the checked-in `Example0001` fixture through the
//! Lean `fixed_ambient_encoding_worker` executable, so Rust never authors a
//! task, a clause identity, or an obligation. The fault proxy wraps that
//! worker to exercise restart, replay, stall, and cancellation paths.

mod support;

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, OnceLock};
use std::time::{Duration, Instant};

use serde_json::{Value, json};

use whiel_runner::encoding::{
    FIXED_AMBIENT_WORKER_FORMAT_VERSION, FixedAmbientWorkerCommand, FixedAmbientWorkerOperation,
    FixedAmbientWorkerPoolConfig, FixedAmbientWorkerRequestEnvelope,
    FixedAmbientWorkerResponseEnvelope, MAX_ENCODING_FRAME_BYTES, NameEnvRevision, NameMapping,
    NameMappingKind, TaskNameEnv, WorkerResponseStatus,
};
use whiel_runner::framework2::{
    ATTEMPT_HISTORY_KIND, ATTEMPT_HISTORY_SCOPE, ATTEMPT_HISTORY_VERSION, AcceptanceRecordRequest,
    AcceptedVerdict, AgentFeedbackPolicy, AgentSearchFeedback, CONSULTATION_RECORD_SCOPE,
    CertificateBuildHooks, CoreFreezeError, CounterexampleFuelPolicy,
    DEFAULT_CERTIFICATION_CONCURRENCY, DurableCounterexampleRecord, FrameworkIISemanticReuseKind,
    FrozenLeveledCore, PinnedLeancheckVampire, PreCertificateAgentHoudiniState, PublicationError,
    PublishInvalidRequest, RecordingProvider, RunConfiguration, SettledSearchOutcome,
    SettlementPolicy, SettlementResources, TranscriptEvent, TranscriptHeader, TranscriptLifecycle,
    TranscriptOutcome, TranscriptPins, TranscriptRecorder, TranscriptStream, VerifiedTranscript,
    publish_invalid, record_acceptance, release_without_certifying, settle_search_outcome,
};
use whiel_runner::framing::{read_frame, write_frame};
use whiel_runner::{
    Agent, AgentConsultationLimits, AgentConsultationPolicy, AgentProvider, AgentPush,
    AgentRequestAttemptOutcome, AgentResponseValidator, AgentResponseWriter,
    AgentSourceCancellation, AgentSourceCleanupFuture, AgentSourceFuture, AgentSourceOutcome,
    AgentTool, AgentToolPolicy, AgentToolSurface, ArtifactKind, ArtifactStore, ArtifactStoreConfig,
    BoundFixedAmbientFrameworkII, CancellationToken, CascPortfolioPolicy, ClauseId,
    ExtendedClauseOrigin, FailureKind, FailureOrigin, FailureScope, FmbOptions,
    FrameworkIIAdmissionContext, FrameworkIIAdmissionError, FrameworkIICertificationProfiles,
    FrameworkIICheckOutcome, FrameworkIICheckRole, FrameworkIIInconclusiveReason, FrameworkIILevel,
    FrameworkIIProductionCheckConfig, FrameworkIISolverContext, FrameworkIIStateError, HostLimits,
    HoudiniProposal, InvalidCertificateBuildRequest, LeancheckCertificationProfile, LevelLedgerRow,
    LeveledHoudiniState, LeveledStabilizationOutcome, PreCertificateAgentHoudiniLimits,
    PreCertificateAgentHoudiniOutcome, PreCertificateAgentHoudiniRuntime,
    PreCertificateAgentHoudiniSearch, PremiseRole, ProofCascShare, ProofSearchProfile, Retention,
    RuntimeResourcePolicy, SolverAdmission, SolverInvocationIdentity, SynthesisTask,
    VampireSearchBudget, VampireWorkerCommand, bind_fixed_ambient_framework_ii,
    build_invalid_certificate, create_general_solver_admission, new_artifact_store,
    read_run_configuration, stabilize_leveled_houdini,
    stabilize_leveled_houdini_with_system_clauses,
};

// ------------------------------------------------------------
// Fixture Sources And Worker Commands
// ------------------------------------------------------------

/// Level-zero ordinary program clause over the input's `T` row.
const LEVEL_ZERO_CLAUSE: &str = "(op_zT = ∅[2])";
/// Level-one clause mentioning the prophecy copy of `T`.
const LEVEL_ONE_CLAUSE: &str = "(yp_zT = ∅[2])";
/// A second level-zero clause, over the `S` row.
const SECOND_LEVEL_ZERO_CLAUSE: &str = "(op_zS = ∅[2])";
/// Opaque Lean key of the prophecy copy of `T`.
const PROPHECY_T_KEY: &str = "y:p::T";
/// The real checked-in Example0001 invariant, in canonical form: the
/// level-zero ordinary clause and the level-one prophecy clause that
/// `Benchmark/Example0001/Core.json` records and
/// `Benchmark/Example0001/Certificate/` is built from. Unlike the synthetic
/// clauses above, these are conditions the pinned leancheck Vampire can
/// actually prove, so a live run that proposes them certifies.
const CANONICAL_LEVEL_ZERO_CLAUSE: &str =
    "(op_zS = (op_zE ∪ π[0,3] (σ[#1 = #2] ((op_zE × op_zT)))))";
const CANONICAL_LEVEL_ONE_CLAUSE: &str = "(π[0,3] (σ[#1 = #2] ((op_zT × yp_zT))) ⊆ yp_zT)";
/// A level-zero clause over the unassigned EDB row `E`, refutable at
/// initialization by any model with a populated `E` that satisfies the
/// computed precondition (`T = ∅` and `S = E ∪ π[0,3](σ[#1 = #2](E × T))`).
const EDB_CLAUSE: &str = "(op_zE = ∅[2])";

static FIXED_AMBIENT_WORKER: OnceLock<PathBuf> = OnceLock::new();
static FAULT_PROXY: OnceLock<PathBuf> = OnceLock::new();
static FIXTURE_DESCRIPTOR: OnceLock<Value> = OnceLock::new();
static REFUTABLE_DESCRIPTOR: OnceLock<Value> = OnceLock::new();

/// The registered production task.
const PRODUCTION_TASK_ID: &str = "Example0001";
/// The registered refutable twin (Pass 7.5e).
const REFUTABLE_TASK_ID: &str = "Example0013";

fn fixed_ambient_worker() -> &'static Path {
    FIXED_AMBIENT_WORKER
        .get_or_init(|| {
            let repository = support::repository_root();
            let build = Command::new("lake")
                .args(["build", "fixed_ambient_encoding_worker"])
                .current_dir(&repository)
                .output()
                .expect("build fixed-ambient encoding worker");
            assert!(
                build.status.success(),
                "Lean fixed-ambient worker build failed\nstdout:\n{}\nstderr:\n{}",
                String::from_utf8_lossy(&build.stdout),
                String::from_utf8_lossy(&build.stderr)
            );
            repository.join(".lake/build/bin/fixed_ambient_encoding_worker")
        })
        .as_path()
}

fn fault_proxy() -> &'static Path {
    FAULT_PROXY
        .get_or_init(|| {
            let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
            let source = manifest.join("tests/fixtures/framework2_restart_encoding_worker.rs");
            let output_directory = manifest.join("target/test-fixtures");
            fs::create_dir_all(&output_directory).expect("create fixture output directory");
            let executable = output_directory.join(format!(
                "framework2-restart-encoding-worker-{}",
                std::process::id()
            ));
            let output = Command::new("rustc")
                .args(["--edition", "2024"])
                .arg(source)
                .arg("-o")
                .arg(&executable)
                .output()
                .expect("compile fixed-ambient worker proxy");
            assert!(
                output.status.success(),
                "fixed-ambient worker proxy compile failed\nstdout:\n{}\nstderr:\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
            executable
        })
        .as_path()
}

/// The one-shot Lean manifest of one registered canonical id.
fn manifest_for(canonical_id: &str) -> Value {
    let output = Command::new(fixed_ambient_worker())
        .args(["manifest", canonical_id])
        .current_dir(support::repository_root())
        .output()
        .expect("run the fixed-ambient fixture manifest");
    assert!(
        output.status.success(),
        "fixture manifest for {canonical_id} failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    serde_json::from_slice(&output.stdout).expect("fixture manifest emits one JSON value")
}

/// The one-shot Lean manifest that bootstraps the V5 fixture in Rust.
fn fixture_descriptor() -> Value {
    FIXTURE_DESCRIPTOR
        .get_or_init(|| manifest_for(PRODUCTION_TASK_ID))
        .clone()
}

/// The refutable twin's descriptor: same schema, precondition and command
/// under a postcondition a two-edge instance refutes.
fn refutable_descriptor() -> Value {
    REFUTABLE_DESCRIPTOR
        .get_or_init(|| manifest_for(REFUTABLE_TASK_ID))
        .clone()
}

fn worker_pool(workers: usize) -> FixedAmbientWorkerPoolConfig {
    FixedAmbientWorkerPoolConfig::new(
        FixedAmbientWorkerCommand::new(fixed_ambient_worker(), support::repository_root()),
        workers,
    )
    .expect("positive worker count")
}

fn fault_pool(directory: &support::TestDir, mode: &str) -> (FixedAmbientWorkerPoolConfig, PathBuf) {
    let marker = directory.path().join(format!("{mode}.marker"));
    let command = FixedAmbientWorkerCommand::new(fault_proxy(), support::repository_root())
        .arguments([
            OsString::from(fixed_ambient_worker().as_os_str()),
            OsString::from(directory.path().join(format!("{mode}.state"))),
            OsString::from(marker.as_os_str()),
            OsString::from(mode),
        ]);
    (
        FixedAmbientWorkerPoolConfig::new(command, 1).expect("one worker"),
        marker,
    )
}

fn agent_admission(vampire_processes: usize, workers: usize) -> SolverAdmission {
    create_general_solver_admission(
        RuntimeResourcePolicy::agent_only(vampire_processes, workers).unwrap(),
    )
    .unwrap()
}

async fn bind(
    pool: FixedAmbientWorkerPoolConfig,
    catalog_digit: char,
    max_level: Option<FrameworkIILevel>,
    admission: &SolverAdmission,
    cancellation: &CancellationToken,
) -> BoundFixedAmbientFrameworkII {
    bind_task(
        PRODUCTION_TASK_ID,
        pool,
        catalog_digit,
        max_level,
        admission,
        cancellation,
    )
    .await
}

/// Bind one registered canonical id through its own Lean descriptor.
async fn bind_task(
    canonical_id: &str,
    pool: FixedAmbientWorkerPoolConfig,
    catalog_digit: char,
    max_level: Option<FrameworkIILevel>,
    admission: &SolverAdmission,
    cancellation: &CancellationToken,
) -> BoundFixedAmbientFrameworkII {
    let descriptor = if canonical_id == PRODUCTION_TASK_ID {
        fixture_descriptor()
    } else {
        refutable_descriptor()
    };
    let bound = bind_fixed_ambient_framework_ii(
        descriptor,
        pool,
        catalog_digit.to_string().repeat(64),
        // The run's host limits are its single source; this suite declares
        // only the level bound it wants and leaves every other limit unset.
        HostLimits {
            level_bound: max_level.map(FrameworkIILevel::get),
            ..HostLimits::UNBOUNDED
        },
        false,
        AgentToolPolicy::default(),
        admission,
        cancellation,
    )
    .await
    .expect("bind the checked-in fixed-ambient fixture");
    assert_eq!(bound.task().identity().canonical_id(), canonical_id);
    // Pass 7.5d: every live suite runs the differential safety net, so a
    // controller-assembled problem that differs from the worker's own
    // `prepare_exact_obligation` output fails the run.
    bound.solver().set_assembly_differential(true);
    bound
}

fn certification_profiles() -> FrameworkIICertificationProfiles {
    let invocation = |profile: &str| {
        SolverInvocationIdentity::from_parts(
            Arc::from("vampire"),
            Arc::from("fixture-leancheck"),
            Arc::from("/fixture/pinned-vampire"),
            Arc::from("a".repeat(64)),
            Arc::from(std::env::consts::OS),
            Arc::from(std::env::consts::ARCH),
            vec![Arc::from(profile)],
        )
        .unwrap()
    };
    let profile = |kind, name: &str| {
        LeancheckCertificationProfile::new(
            kind,
            format!("fixture-{name}-v1"),
            invocation(name),
            None,
            "b".repeat(64),
            "c".repeat(64),
            "d".repeat(64),
            "e".repeat(64),
            "f".repeat(64),
        )
        .unwrap()
    };
    FrameworkIICertificationProfiles::new(
        profile(ProofSearchProfile::Direct, "direct"),
        profile(ProofSearchProfile::Casc2025, "casc-2025"),
    )
    .unwrap()
}

/// A production check configuration: both lanes race, as they do in a
/// campaign. The Vampire stand-in must answer a finite-model call as well as a
/// proof call, and the admission must grant the two slots the race takes.
fn production_config(
    artifacts: &ArtifactStore,
    admission: &SolverAdmission,
    fmb: FmbOptions,
    command: VampireWorkerCommand,
    cancellation: &CancellationToken,
) -> FrameworkIIProductionCheckConfig {
    FrameworkIIProductionCheckConfig::new(
        artifacts.clone(),
        admission.clone(),
        VampireSearchBudget::finite(Duration::from_secs(5)),
        fmb,
        command,
        cancellation.clone(),
        "fixture-vampire",
        certification_profiles(),
    )
    .unwrap()
}

/// A proof-only configuration, for a test whose subject is the proof lane or
/// the search's control flow and whose Vampire stand-in answers one proof call
/// and nothing else. It is not what a campaign runs: a condition it cannot
/// prove comes back inconclusive, never refuted.
fn proof_only_production_config(
    artifacts: &ArtifactStore,
    admission: &SolverAdmission,
    command: VampireWorkerCommand,
    cancellation: &CancellationToken,
) -> FrameworkIIProductionCheckConfig {
    FrameworkIIProductionCheckConfig::new_proof_only_not_a_campaign_configuration(
        artifacts.clone(),
        admission.clone(),
        VampireSearchBudget::finite(Duration::from_secs(5)),
        command,
        cancellation.clone(),
        "fixture-vampire",
        certification_profiles(),
    )
    .unwrap()
}

/// A Vampire stand-in for the ambient fixture: the first finite-model call
/// returns a genuine one-element countermodel in which only the EDB row `C`
/// is populated, the first direct call gives up, and every later direct call
/// proves its problem.
fn refuting_model_vampire(directory: &Path) -> VampireWorkerCommand {
    let script = directory.join("ambient-model-vampire.py");
    let state = directory.join("ambient-model-vampire.state");
    fs::write(
        &script,
        r#"import fcntl
import sys
from pathlib import Path

state_path = Path(sys.argv[1])
arguments = sys.argv[2:]
is_fmb = "--saturation_algorithm" in arguments
mode = "fmb" if is_fmb else "direct"
state_path.parent.mkdir(parents=True, exist_ok=True)
with state_path.open("a+", encoding="utf-8") as state:
    fcntl.flock(state.fileno(), fcntl.LOCK_EX)
    state.seek(0)
    seen = [line.rstrip("\n") for line in state]
    ordinal = seen.count(mode)
    state.write(mode + "\n")
    state.flush()
    fcntl.flock(state.fileno(), fcntl.LOCK_UN)

relations = {
    "op_zE": 2, "op_zS": 2, "op_zT": 2, "yp_zS": 2,
    "yp_zT": 2,
}
populated = {"op_zE", "op_zS"}
if is_fmb and ordinal == 0:
    print("% TRYING [1]")
    print("% SZS status CounterSatisfiable for problem")
    print("% SZS output start FiniteModel for problem")
    print("tff('declare_$i1',type,'fmb_$i_1':$i).")
    print("tff('finite_domain_$i',axiom,! [X:$i] : X = 'fmb_$i_1').")
    for name, arity in relations.items():
        signature = "$i>$o" if arity == 1 else "($i*$i)>$o"
        args = ",".join(["'fmb_$i_1'"] * arity)
        negation = "" if name in populated else "~"
        print(f"tff(declare_{name},type,{name}:{signature}).")
        print(f"tff(predicate_{name},axiom,{negation}{name}({args})).")
    print("% SZS output end FiniteModel for problem")
elif is_fmb:
    print("% TRYING [13]")
    print("% SZS status GaveUp for problem")
elif ordinal == 0:
    print("% SZS status GaveUp for problem")
else:
    print("% SZS status Theorem for problem")
    print("% SZS output start Proof for problem")
    print("1. $false [fixture]")
    print("% SZS output end Proof for problem")
"#,
    )
    .expect("write the ambient finite-model Vampire fixture");
    VampireWorkerCommand::new("python3")
        .with_extra_args([script.into_os_string(), state.into_os_string()])
        .expect("ambient finite-model Vampire fixture arguments")
}

/// A Vampire stand-in whose only decided answer is a finite model on the
/// *second* finite-model call of the run. Every direct call gives up, so the
/// first check of the run is inconclusive and the epoch's termination check
/// — the second finite-model call — is the one that receives the real,
/// Lean-validated countermodel.
fn termination_refuting_vampire(directory: &Path) -> VampireWorkerCommand {
    let script = directory.join("termination-model-vampire.py");
    let state = directory.join("termination-model-vampire.state");
    fs::write(
        &script,
        r#"import fcntl
import sys
from pathlib import Path

state_path = Path(sys.argv[1])
arguments = sys.argv[2:]
is_fmb = "--saturation_algorithm" in arguments
mode = "fmb" if is_fmb else "direct"
state_path.parent.mkdir(parents=True, exist_ok=True)
with state_path.open("a+", encoding="utf-8") as state:
    fcntl.flock(state.fileno(), fcntl.LOCK_EX)
    state.seek(0)
    seen = [line.rstrip("\n") for line in state]
    ordinal = seen.count(mode)
    state.write(mode + "\n")
    state.flush()
    fcntl.flock(state.fileno(), fcntl.LOCK_UN)

# A two-element carrier is required: over a one-element domain the
# postcondition
#     pi[0,3](sigma[#1=#2](T x T)) subseteq T
# holds vacuously. With T = S = {(a,b),(b,a)} the guard (S != T) is false,
# so the termination premise {not guard} holds, while the projection yields
# {(a,a),(b,b)}, which T does not contain: a genuine countermodel.
tuples = {
    "op_zE": [],
    "op_zS": [("1", "2"), ("2", "1")],
    "op_zT": [("1", "2"), ("2", "1")],
    "yp_zS": [],
    "yp_zT": [],
}
if is_fmb and ordinal == 1:
    print("% TRYING [1]")
    print("% SZS status CounterSatisfiable for problem")
    print("% SZS output start FiniteModel for problem")
    print("tff('declare_$i1',type,'fmb_$i_1':$i).")
    print("tff('declare_$i2',type,'fmb_$i_2':$i).")
    print("tff('finite_domain_$i',axiom,! [X:$i] : (X = 'fmb_$i_1' | X = 'fmb_$i_2')).")
    for name, rows in tuples.items():
        print(f"tff(declare_{name},type,{name}:($i*$i)>$o).")
        literals = []
        for left in ("1", "2"):
            for right in ("1", "2"):
                sign = "" if (left, right) in rows else "~"
                literals.append(
                    f"{sign}{name}('fmb_$i_{left}','fmb_$i_{right}')"
                )
        print(f"tff(predicate_{name},axiom," + " & ".join(literals) + ").")
    print("% SZS output end FiniteModel for problem")
else:
    print("% SZS status GaveUp for problem")
"#,
    )
    .expect("write the termination finite-model Vampire fixture");
    VampireWorkerCommand::new("python3")
        .with_extra_args([script.into_os_string(), state.into_os_string()])
        .expect("termination finite-model Vampire fixture arguments")
}

fn proof_vampire(launch_log: &Path) -> VampireWorkerCommand {
    VampireWorkerCommand::new(support::fake_vampire())
        .with_extra_args([
            OsString::from("--fixture"),
            OsString::from("proof"),
            OsString::from("--launch-log"),
            launch_log.as_os_str().to_owned(),
        ])
        .unwrap()
}

async fn admit(
    admission: &FrameworkIIAdmissionContext,
    sources: &[&str],
    solver_admission: &SolverAdmission,
    cancellation: &CancellationToken,
) -> Vec<whiel_runner::ExtendedClause> {
    let sources = sources
        .iter()
        .map(|source| (*source).to_owned())
        .collect::<Vec<_>>();
    admission
        .admit_clauses(&sources, None, solver_admission, cancellation)
        .await
        .expect("live admission is not cancelled")
        .accepted()
        .expect("fixture clauses are accepted")
        .to_vec()
}

fn register_and_enqueue(
    houdini: &mut LeveledHoudiniState,
    clauses: &[whiel_runner::ExtendedClause],
) -> Vec<ClauseId> {
    let registered = houdini
        .catalog()
        .register_batch(
            0,
            clauses
                .iter()
                .cloned()
                .map(|clause| (clause, ExtendedClauseOrigin::Submitted)),
        )
        .unwrap();
    houdini.enqueue_registered(&registered).unwrap();
    registered.ids().to_vec()
}

async fn wait_for_marker(path: &Path) {
    let deadline = Instant::now() + Duration::from_secs(20);
    while !path.exists() {
        assert!(
            Instant::now() < deadline,
            "worker fault marker was not written"
        );
        tokio::time::sleep(Duration::from_millis(5)).await;
    }
}

const ROLES: [FrameworkIICheckRole; 2] = [
    FrameworkIICheckRole::Initialization,
    FrameworkIICheckRole::Maintenance,
];

// ------------------------------------------------------------
// Scripted Agent Providers
// ------------------------------------------------------------

#[derive(Clone, Debug)]
struct ObservedProviderRequest {
    push: AgentPush,
    bytes: Vec<u8>,
    digest: String,
    validation_ordinal: usize,
}

fn assert_fixed_ambient_agent_request(request: &Value) {
    assert_eq!(request["schema_version"], json!(4));
    assert_eq!(request["operation"], json!("proposer_observation"));
    assert!(request["binding"].get("prior_active_plan_digest").is_none());
    let encoded = serde_json::to_string(request).expect("provider request serializes");
    for retired in [
        "finite_validity_search_catalog",
        "active_selection_plan",
        "library_selections",
        "source_relations",
        "extended_schema",
    ] {
        assert!(!encoded.contains(retired), "request exposes {retired}");
    }
}

fn request_bound_response_binding(request_value: &Value, request: &AgentPush) -> Value {
    assert_fixed_ambient_agent_request(request_value);
    let request_binding = request_value["binding"]
        .as_object()
        .expect("provider request has an exact binding");
    let field = |name: &str| {
        request_binding
            .get(name)
            .cloned()
            .unwrap_or_else(|| panic!("provider request omitted binding field {name}"))
    };
    json!({
        "task_digest":field("task_digest"),
        "scope_digest":field("scope_digest"),
        "run_digest":field("run_digest"),
        "consultation_digest":field("consultation_digest"),
        "state_snapshot_digest":field("state_snapshot_digest"),
        "validation_manifest_digest":field("validation_manifest_digest"),
        "request_digest":request.digest(),
        "validation_ordinal":request.validation_ordinal(),
    })
}

fn clause_response(request: &AgentPush, clauses: &[&str]) -> Vec<u8> {
    let request_value: Value =
        serde_json::from_slice(request.bytes()).expect("provider receives valid request JSON");
    let response = json!({
        "kind":"candidate_clauses",
        "schema_version":4,
        "binding":request_bound_response_binding(&request_value, request),
        "clauses":clauses,
        "dropped":[],
    });
    serde_json::to_vec(&response).expect("provider response serializes")
}

/// Like [`clause_response`], but with an explicit `dropped` list carried
/// verbatim from a push's own `retry[*].drop_reference` (Pass 7.5c).
fn clause_response_with_drops(
    request: &AgentPush,
    clauses: &[&str],
    dropped: Vec<Value>,
) -> Vec<u8> {
    let request_value: Value =
        serde_json::from_slice(request.bytes()).expect("provider receives valid request JSON");
    let response = json!({
        "kind":"candidate_clauses",
        "schema_version":4,
        "binding":request_bound_response_binding(&request_value, request),
        "clauses":clauses,
        "dropped":dropped,
    });
    serde_json::to_vec(&response).expect("provider response serializes")
}

fn observe(log: &Mutex<Vec<ObservedProviderRequest>>, request: &AgentPush) {
    log.lock()
        .expect("provider request log is not poisoned")
        .push(ObservedProviderRequest {
            push: request.clone(),
            bytes: request.bytes().to_vec(),
            digest: request.digest().to_string(),
            validation_ordinal: request.validation_ordinal(),
        });
}

/// One provider that always returns the same exact clause list.
struct ClauseProvider {
    clauses: Vec<&'static str>,
    observed: Arc<Mutex<Vec<ObservedProviderRequest>>>,
}

impl AgentProvider for ClauseProvider {
    fn quiesce_request(&mut self) -> whiel_runner::proposer_api::ProposerCleanupFuture<'_> {
        Box::pin(async { Ok(()) })
    }
    fn shutdown(
        &mut self,
        _reason: whiel_runner::proposer_api::wire::ShutdownReason,
    ) -> whiel_runner::proposer_api::ProposerCleanupFuture<'_> {
        self.quiesce_request()
    }

    fn consult<'a>(
        &'a mut self,
        request: &'a AgentPush,
        _tools: &'a dyn AgentToolSurface,
        response: &'a mut AgentResponseWriter,
        _cancellation: AgentSourceCancellation,
    ) -> AgentSourceFuture<'a> {
        observe(&self.observed, request);
        let bytes = clause_response(request, &self.clauses);
        let _ = response.write_chunk(&bytes);
        Box::pin(async { AgentSourceOutcome::Response })
    }
}

/// A provider which calls the tool surface once before submitting its
/// clause, recording the exact tool response so the test can check it
/// against the push's own `state_revision` (Pass 7.5c).
struct ToolProbeProvider {
    clauses: Vec<&'static str>,
    observed: Arc<Mutex<Vec<ObservedProviderRequest>>>,
    tool_responses: Arc<Mutex<Vec<Value>>>,
}

impl AgentProvider for ToolProbeProvider {
    fn quiesce_request(&mut self) -> whiel_runner::proposer_api::ProposerCleanupFuture<'_> {
        Box::pin(async { Ok(()) })
    }
    fn shutdown(
        &mut self,
        _reason: whiel_runner::proposer_api::wire::ShutdownReason,
    ) -> whiel_runner::proposer_api::ProposerCleanupFuture<'_> {
        self.quiesce_request()
    }

    fn consult<'a>(
        &'a mut self,
        request: &'a AgentPush,
        tools: &'a dyn AgentToolSurface,
        response: &'a mut AgentResponseWriter,
        _cancellation: AgentSourceCancellation,
    ) -> AgentSourceFuture<'a> {
        observe(&self.observed, request);
        let bytes = clause_response(request, &self.clauses);
        Box::pin(async move {
            let outcome = tools
                .call("countermodel", json!({"attempt": 999_999_999_u64}))
                .await;
            self.tool_responses
                .lock()
                .unwrap()
                .push(serde_json::to_value(&outcome).expect("tool response serializes"));
            let skill = tools.call("get_skill", json!({"id":"fixture"})).await;
            self.tool_responses
                .lock()
                .unwrap()
                .push(serde_json::to_value(skill).unwrap());
            let _ = response.write_chunk(&bytes);
            AgentSourceOutcome::Response
        })
    }
}

/// Extract one accepted tool call's `result` payload, panicking with the
/// full response otherwise (a test assertion helper, not production code:
/// every call this provider makes is expected to succeed unless the test
/// itself is specifically checking for an error).
fn tool_result(response: &Value) -> Value {
    response
        .get("result")
        .unwrap_or_else(|| panic!("tool call unexpectedly failed: {response}"))
        .clone()
}

/// A scripted provider driving three consultation rounds against the real
/// worker. Round 0 proposes one prophecy clause whose only check is
/// inconclusive, so it ends the scan pending and the epoch's termination
/// check on the (still empty) Core is refuted with a real, Lean-validated
/// countermodel. Round 1 reads that countermodel through the `countermodel`
/// tool by the attempt the `postcondition_open` event names, exercises the
/// rest of the tool surface, and submits one fresh clause. Round 2 only
/// captures the following push so the test can inspect it.
struct VetoAndToolsProvider {
    round: usize,
    observed: Arc<Mutex<Vec<ObservedProviderRequest>>>,
    tool_responses: Arc<Mutex<Vec<Value>>>,
}

impl AgentProvider for VetoAndToolsProvider {
    fn quiesce_request(&mut self) -> whiel_runner::proposer_api::ProposerCleanupFuture<'_> {
        Box::pin(async { Ok(()) })
    }
    fn shutdown(
        &mut self,
        _reason: whiel_runner::proposer_api::wire::ShutdownReason,
    ) -> whiel_runner::proposer_api::ProposerCleanupFuture<'_> {
        self.quiesce_request()
    }

    fn consult<'a>(
        &'a mut self,
        request: &'a AgentPush,
        tools: &'a dyn AgentToolSurface,
        response: &'a mut AgentResponseWriter,
        _cancellation: AgentSourceCancellation,
    ) -> AgentSourceFuture<'a> {
        observe(&self.observed, request);
        let round = self.round;
        self.round += 1;
        let request_value: Value =
            serde_json::from_slice(request.bytes()).expect("provider receives valid request JSON");
        Box::pin(async move {
            match round {
                0 => {
                    assert_eq!(
                        request_value["feedback"]["latest"]["kind"],
                        json!("initial")
                    );
                    let bytes = clause_response(request, &[LEVEL_ONE_CLAUSE]);
                    let _ = response.write_chunk(&bytes);
                    AgentSourceOutcome::Response
                }
                1 => {
                    // The epoch's termination check was refuted; the event
                    // names the attempt whose countermodel the tool serves.
                    let latest = &request_value["feedback"]["latest"];
                    assert_eq!(latest["kind"], json!("postcondition_open"), "{latest}");
                    assert_eq!(
                        latest["postcondition_open"]["outcome"],
                        json!("refuted"),
                        "{latest}"
                    );
                    let attempt = latest["postcondition_open"]["attempt"]
                        .as_u64()
                        .expect("a refuted termination check names its attempt");

                    let pending = request_value["feedback"]["pending"]
                        .as_array()
                        .expect("round 1's push shows the pending list");
                    assert_eq!(
                        pending.len(),
                        1,
                        "the only proposed clause is still pending: {pending:?}"
                    );
                    let entry = &pending[0];
                    assert_eq!(entry["minimum_level"], json!(1));
                    assert_eq!(entry["current_level"], json!(1));
                    let drop_reference = entry["drop_reference"].clone();
                    assert!(!drop_reference.is_null(), "a pending clause is droppable");
                    let clause = entry["clause"].clone();

                    let record = |value: Value| {
                        self.tool_responses.lock().unwrap().push(value);
                    };

                    let unknown = tools.call("bogus_tool_name", json!({})).await;
                    record(serde_json::to_value(&unknown).unwrap());

                    // The termination refutation's own countermodel, served
                    // by the attempt the event named.
                    let countermodel = tools
                        .call("countermodel", json!({"attempt": attempt}))
                        .await;
                    record(serde_json::to_value(&countermodel).unwrap());

                    let history = tools
                        .call("history", json!({"clause": clause.clone()}))
                        .await;
                    record(serde_json::to_value(&history).unwrap());

                    let strongest = tools
                        .call("strongest_refutations", json!({"clause": clause}))
                        .await;
                    record(serde_json::to_value(&strongest).unwrap());

                    let ledger = tools.call("ledger", json!({})).await;
                    record(serde_json::to_value(&ledger).unwrap());

                    let validate = tools
                        .call(
                            "evaluate_clauses",
                            json!({"clauses": [LEVEL_ONE_CLAUSE], "instances": [
                                {"kind":"retained","attempt":attempt},
                                {"kind":"supplied","instance": supplied_api_instance(request)},
                                {"kind":"retained","attempt":attempt}
                            ]}),
                        )
                        .await;
                    record(serde_json::to_value(&validate).unwrap());

                    let skill = tools.call("get_skill", json!({"id": "nonexistent"})).await;
                    record(serde_json::to_value(&skill).unwrap());

                    // Drop the pending clause while proposing a fresh one:
                    // the drop moves it to dead-by-drop, out of `pending`.
                    let bytes = clause_response_with_drops(
                        request,
                        &[LEVEL_ZERO_CLAUSE],
                        vec![drop_reference],
                    );
                    let _ = response.write_chunk(&bytes);
                    AgentSourceOutcome::Response
                }
                _ => AgentSourceOutcome::SourceExhausted,
            }
        })
    }
}

#[derive(Clone)]
enum SearchFailureProviderMode {
    SourceExhausted,
    /// Submits `invalid` responses whose binding does not match, each of
    /// which is answered with a correction, then one acceptable response.
    /// Corrections are unlimited within a consultation, so the run never
    /// ends because of them.
    InvalidThenValid {
        invalid: usize,
        sent: Arc<AtomicUsize>,
    },
    NoResponse,
    TransportFailure,
    Stall(Arc<AtomicBool>),
    UnresolvedClauses,
}

#[derive(Default)]
struct SearchProviderLifecycle {
    idle_calls: AtomicUsize,
    dropped: AtomicBool,
    dropped_after_idle: AtomicBool,
}

struct SearchFailureProvider {
    mode: SearchFailureProviderMode,
    observed: Arc<Mutex<Vec<ObservedProviderRequest>>>,
    lifecycle: Option<Arc<SearchProviderLifecycle>>,
}

impl SearchFailureProvider {
    fn new(
        mode: SearchFailureProviderMode,
        observed: Arc<Mutex<Vec<ObservedProviderRequest>>>,
    ) -> Self {
        Self {
            mode,
            observed,
            lifecycle: None,
        }
    }

    fn with_lifecycle(mut self, lifecycle: Arc<SearchProviderLifecycle>) -> Self {
        self.lifecycle = Some(lifecycle);
        self
    }
}

impl Drop for SearchFailureProvider {
    fn drop(&mut self) {
        if let Some(lifecycle) = &self.lifecycle {
            lifecycle.dropped_after_idle.store(
                lifecycle.idle_calls.load(Ordering::SeqCst) > 0,
                Ordering::SeqCst,
            );
            lifecycle.dropped.store(true, Ordering::SeqCst);
        }
    }
}

impl AgentProvider for SearchFailureProvider {
    fn quiesce_request(&mut self) -> AgentSourceCleanupFuture<'_> {
        if let Some(lifecycle) = &self.lifecycle {
            lifecycle.idle_calls.fetch_add(1, Ordering::SeqCst);
        }
        Box::pin(async { Ok(()) })
    }
    fn shutdown(
        &mut self,
        _reason: whiel_runner::proposer_api::wire::ShutdownReason,
    ) -> AgentSourceCleanupFuture<'_> {
        self.quiesce_request()
    }

    fn consult<'a>(
        &'a mut self,
        request: &'a AgentPush,
        _tools: &'a dyn AgentToolSurface,
        response: &'a mut AgentResponseWriter,
        cancellation: AgentSourceCancellation,
    ) -> AgentSourceFuture<'a> {
        observe(&self.observed, request);
        match self.mode.clone() {
            SearchFailureProviderMode::SourceExhausted => {
                Box::pin(async { AgentSourceOutcome::SourceExhausted })
            }
            SearchFailureProviderMode::NoResponse => {
                Box::pin(async { AgentSourceOutcome::NoResponse })
            }
            SearchFailureProviderMode::TransportFailure => {
                response
                    .write_chunk(b"ignored partial transport bytes")
                    .unwrap();
                Box::pin(async { AgentSourceOutcome::TransportFailure })
            }
            SearchFailureProviderMode::Stall(cleaned) => Box::pin(async move {
                cancellation.cancelled().await;
                cleaned.store(true, Ordering::SeqCst);
                AgentSourceOutcome::NoResponse
            }),
            SearchFailureProviderMode::InvalidThenValid { invalid, sent } => {
                let ordinal = sent.fetch_add(1, Ordering::SeqCst);
                let mut candidate: Value =
                    serde_json::from_slice(&clause_response(request, &[LEVEL_ZERO_CLAUSE]))
                        .unwrap();
                if ordinal < invalid {
                    candidate["binding"]["task_digest"] = json!("0".repeat(64));
                }
                response
                    .write_chunk(&serde_json::to_vec(&candidate).unwrap())
                    .unwrap();
                Box::pin(async { AgentSourceOutcome::Response })
            }
            SearchFailureProviderMode::UnresolvedClauses => {
                let bytes = clause_response(request, &[LEVEL_ZERO_CLAUSE]);
                response.write_chunk(&bytes).unwrap();
                Box::pin(async { AgentSourceOutcome::Response })
            }
        }
    }
}

struct CancellationCleanupControl {
    request_started: AtomicBool,
    cleanup_started: AtomicBool,
    cleanup_complete: AtomicBool,
    request_started_notify: tokio::sync::Notify,
    cleanup_started_notify: tokio::sync::Notify,
    cleanup_release: tokio::sync::Notify,
    observed: Mutex<Vec<ObservedProviderRequest>>,
}

impl CancellationCleanupControl {
    fn new() -> Self {
        Self {
            request_started: AtomicBool::new(false),
            cleanup_started: AtomicBool::new(false),
            cleanup_complete: AtomicBool::new(false),
            request_started_notify: tokio::sync::Notify::new(),
            cleanup_started_notify: tokio::sync::Notify::new(),
            cleanup_release: tokio::sync::Notify::new(),
            observed: Mutex::new(Vec::new()),
        }
    }

    async fn wait_for_request_start(&self) {
        while !self.request_started.load(Ordering::SeqCst) {
            self.request_started_notify.notified().await;
        }
    }

    async fn wait_for_cleanup_start(&self) {
        while !self.cleanup_started.load(Ordering::SeqCst) {
            self.cleanup_started_notify.notified().await;
        }
    }
}

struct CleanupAwareProvider {
    request_ordinal: usize,
    control: Arc<CancellationCleanupControl>,
}

impl AgentProvider for CleanupAwareProvider {
    fn quiesce_request(&mut self) -> whiel_runner::proposer_api::ProposerCleanupFuture<'_> {
        Box::pin(async { Ok(()) })
    }
    fn shutdown(
        &mut self,
        _reason: whiel_runner::proposer_api::wire::ShutdownReason,
    ) -> whiel_runner::proposer_api::ProposerCleanupFuture<'_> {
        self.quiesce_request()
    }

    fn consult<'a>(
        &'a mut self,
        request: &'a AgentPush,
        _tools: &'a dyn AgentToolSurface,
        response: &'a mut AgentResponseWriter,
        cancellation: AgentSourceCancellation,
    ) -> AgentSourceFuture<'a> {
        observe(&self.control.observed, request);
        let request_ordinal = self.request_ordinal;
        self.request_ordinal += 1;
        if request_ordinal == 0 {
            self.control.request_started.store(true, Ordering::SeqCst);
            self.control.request_started_notify.notify_waiters();
            let control = Arc::clone(&self.control);
            return Box::pin(async move {
                cancellation.cancelled().await;
                control.cleanup_started.store(true, Ordering::SeqCst);
                control.cleanup_started_notify.notify_waiters();
                control.cleanup_release.notified().await;
                control.cleanup_complete.store(true, Ordering::SeqCst);
                AgentSourceOutcome::NoResponse
            });
        }
        let bytes = clause_response(request, &[LEVEL_ZERO_CLAUSE]);
        let _ = response.write_chunk(&bytes);
        Box::pin(async move { AgentSourceOutcome::Response })
    }
}

// ------------------------------------------------------------
// Admission, Restart, And Cancellation
// ------------------------------------------------------------

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn live_fixed_ambient_admission_is_task_bound_correctable_and_parallel_safe() {
    let solver_admission = agent_admission(2, 2);
    let cancellation = CancellationToken::new();
    let bound = bind(worker_pool(2), '1', None, &solver_admission, &cancellation).await;
    let (task, admission, solver, _houdini) = bound.into_parts();
    assert_eq!(admission.scope().task_identity(), task.identity());
    assert!(admission.scope().identity().is_object());
    assert_eq!(admission.scope().relations().len(), 5);
    assert_eq!(admission.scope().prophecy_bindings().len(), 2);

    let unknown = admission
        .admit_clauses(
            &["(op_zZ = ∅[1])".to_string()],
            None,
            &solver_admission,
            &cancellation,
        )
        .await
        .unwrap();
    let diagnostic = &unknown.correction().unwrap().diagnostics()[0];
    assert_eq!(diagnostic.code(), "clause_schema_error");
    assert_eq!(diagnostic.item_index(), Some(0));

    let lexical = admission
        .admit_clauses(
            &["E + E = E".to_string()],
            None,
            &solver_admission,
            &cancellation,
        )
        .await
        .unwrap();
    let diagnostic = &lexical.correction().unwrap().diagnostics()[0];
    assert_eq!(diagnostic.code(), "clause_lexical_error");
    assert_eq!(diagnostic.item_index(), Some(0));

    let (zero, one) = tokio::join!(
        admit(
            &admission,
            &[LEVEL_ZERO_CLAUSE, LEVEL_ZERO_CLAUSE],
            &solver_admission,
            &cancellation
        ),
        admit(
            &admission,
            &[LEVEL_ONE_CLAUSE],
            &solver_admission,
            &cancellation
        ),
    );
    let distinct = zero
        .iter()
        .map(|clause| clause.identity_sha256().to_owned())
        .collect::<BTreeSet<_>>();
    assert_eq!(distinct.len(), 1, "duplicate sources share one identity");
    assert_eq!(zero[0].minimum_level(), FrameworkIILevel::ZERO);
    assert_eq!(zero[0].scope(), admission.scope());
    assert_eq!(one.len(), 1);
    assert_eq!(one[0].minimum_level(), FrameworkIILevel::ONE);
    assert!(
        one[0]
            .relation_keys()
            .iter()
            .any(|key| key == PROPHECY_T_KEY),
        "the prophecy clause retains its opaque Lean key"
    );

    let (repeated_zero, repeated_one) = tokio::join!(
        admit(
            &admission,
            &[LEVEL_ZERO_CLAUSE],
            &solver_admission,
            &cancellation
        ),
        admit(
            &admission,
            &[LEVEL_ONE_CLAUSE],
            &solver_admission,
            &cancellation
        ),
    );
    assert_eq!(repeated_zero[0], zero[0]);
    assert_eq!(repeated_one, one);

    let canonical = zero[0].canonical_source().to_owned();
    assert!(!canonical.is_empty());
    let round_trip = admit(&admission, &[&canonical], &solver_admission, &cancellation).await;
    assert_eq!(round_trip[0], zero[0]);
    assert_eq!(round_trip[0].canonical_source(), canonical);

    solver.shutdown().await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn stateless_clause_admission_recovers_after_worker_exit() {
    let directory = support::TestDir::new("fixed_ambient_worker_restart");
    let solver_admission = agent_admission(2, 2);
    let cancellation = CancellationToken::new();
    let (pool, marker) = fault_pool(&directory, "fail_clause");
    let bound = bind(pool, '2', None, &solver_admission, &cancellation).await;
    let (_task, admission, solver, _houdini) = bound.into_parts();
    let clauses = vec![LEVEL_ZERO_CLAUSE.to_string()];

    assert!(
        admission
            .admit_clauses(&clauses, None, &solver_admission, &cancellation)
            .await
            .is_err()
    );
    assert!(marker.exists());
    let recovered = admit(
        &admission,
        &[LEVEL_ZERO_CLAUSE],
        &solver_admission,
        &cancellation,
    )
    .await;
    let repeated = admit(
        &admission,
        &[LEVEL_ZERO_CLAUSE],
        &solver_admission,
        &cancellation,
    )
    .await;
    assert_eq!(recovered, repeated);

    solver.shutdown().await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn active_stateless_cancellation_replaces_worker_without_identity_drift() {
    let directory = support::TestDir::new("fixed_ambient_active_cancellation");
    let solver_admission = agent_admission(2, 2);
    let cancellation = CancellationToken::new();
    let (pool, marker) = fault_pool(&directory, "stall_clause");
    let bound = bind(pool, '3', None, &solver_admission, &cancellation).await;
    let (_task, admission, solver, _houdini) = bound.into_parts();
    let expected_scope = admission.scope().clone();

    let request_admission = admission.clone();
    let request_solver_admission = solver_admission.clone();
    let request_cancellation = CancellationToken::new();
    let request_token = request_cancellation.clone();
    let request = tokio::spawn(async move {
        request_admission
            .admit_clauses(
                &[LEVEL_ZERO_CLAUSE.to_string()],
                None,
                &request_solver_admission,
                &request_token,
            )
            .await
    });
    wait_for_marker(&marker).await;
    request_cancellation.cancel();
    assert!(matches!(
        request.await.unwrap(),
        Err(FrameworkIIAdmissionError::Cancelled)
    ));

    let recovered = admit(
        &admission,
        &[LEVEL_ZERO_CLAUSE],
        &solver_admission,
        &CancellationToken::new(),
    )
    .await;
    assert_eq!(recovered[0].scope(), &expected_scope);
    assert_eq!(recovered[0].minimum_level(), FrameworkIILevel::ZERO);

    solver.shutdown().await.unwrap();
}

/// The ordinary check path's worker calls replay byte for byte after the
/// worker dies mid-request.
///
/// `differential` selects the configuration: `false` is the production
/// path, which since Pass 7.5d assembles its obligation from cached opaque
/// pieces and whose only worker calls here are `prepare_clause_pieces` and
/// `check_empty_counterexample` — the ops the fault proxy targets. `true`
/// is the configuration every other test in this suite runs under, kept so
/// the recovery is pinned there too.
async fn exact_obligation_response_replays_exactly_after_worker_death_with(
    differential: bool,
    catalog_digit: char,
    label: &str,
) {
    let directory = support::TestDir::new(label);
    let launch_log = directory.path().join("vampire-launches.log");
    let solver_admission = agent_admission(1, 1);
    let cancellation = CancellationToken::new();
    let (pool, marker) = fault_pool(&directory, "fail_after_prepare");
    let bound = bind(pool, catalog_digit, None, &solver_admission, &cancellation).await;
    let (task, admission, solver, mut houdini) = bound.into_parts();
    solver.set_assembly_differential(differential);
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();

    let clauses = admit(
        &admission,
        &[LEVEL_ONE_CLAUSE],
        &solver_admission,
        &cancellation,
    )
    .await;
    assert_eq!(clauses[0].minimum_level(), FrameworkIILevel::ONE);
    let external = register_and_enqueue(&mut houdini, &clauses)[0];

    let mut checker = solver
        .clone()
        .production_checker(proof_only_production_config(
            &artifacts,
            &solver_admission,
            proof_vampire(&launch_log),
            &cancellation,
        ));
    let first_outcome = stabilize_leveled_houdini(&mut houdini, &mut checker)
        .await
        .expect("worker failure is a typed stabilization stop");
    let LeveledStabilizationOutcome::Failure(worker_failure) = first_outcome else {
        panic!("worker failure must stop stabilization, got {first_outcome:?}")
    };
    assert_eq!(worker_failure.origin(), FailureOrigin::EncodingPreparation);
    assert_eq!(worker_failure.kind(), FailureKind::ProcessFailure);
    assert!(!worker_failure.retryable());
    assert_eq!(worker_failure.scope(), FailureScope::LaneLocal);
    assert!(worker_failure.artifact_references().is_empty());
    drop(checker);
    assert!(marker.exists());
    assert!(houdini.attempts().rows().is_empty());
    assert!(
        houdini
            .current_root(external, FrameworkIICheckRole::Initialization)
            .is_none()
    );
    assert!(!launch_log.exists());

    let mut checker = solver
        .clone()
        .production_checker(proof_only_production_config(
            &artifacts,
            &solver_admission,
            proof_vampire(&launch_log),
            &cancellation,
        ));
    assert!(matches!(
        stabilize_leveled_houdini(&mut houdini, &mut checker)
            .await
            .unwrap(),
        LeveledStabilizationOutcome::Stabilized(_)
    ));
    let replay = marker.with_extension("replayed");
    wait_for_marker(&replay).await;
    let mut before_death: Value = serde_json::from_slice(&fs::read(&marker).unwrap()).unwrap();
    let mut after_replacement: Value = serde_json::from_slice(&fs::read(&replay).unwrap()).unwrap();
    for response in [&before_death, &after_replacement] {
        assert_eq!(
            response["operation"].as_str(),
            Some("prepare_clause_pieces"),
            "the ordinary path's first worker call is the clause-piece fetch"
        );
        assert_eq!(response["status"], json!("ok"));
        assert_eq!(
            response["task_identity"]["canonical_id"],
            json!("Example0001")
        );
    }
    assert!(before_death["name_env_revision"].as_u64().unwrap() > 0);
    assert_eq!(
        before_death["name_env_revision"],
        after_replacement["name_env_revision"]
    );
    assert_eq!(
        before_death["request_name_env_revision"],
        after_replacement["request_name_env_revision"]
    );
    // The input's computed precondition has no EDB-only conjunct, so the
    // first clause-piece fetch in a run belongs to the proposed clause and
    // the replayed response names it by its canonical source.
    assert!(
        serde_json::to_string(&before_death["payload"])
            .unwrap()
            .contains(LEVEL_ONE_CLAUSE),
        "the clause-piece response retains the clause's canonical source"
    );
    before_death["request_id"] = json!(0);
    after_replacement["request_id"] = json!(0);
    assert_eq!(before_death, after_replacement);
    for role in ROLES {
        assert!(houdini.current_root(external, role).is_some());
    }

    drop(checker);
    solver.shutdown().await.unwrap();
    drop(solver);
    drop(admission);
    drop(artifacts);
    owner.settle().unwrap();
}

/// Pass 7.5d: the production path — the assembly differential off — is the
/// one that must survive a worker death, since it is the only one that runs
/// outside the test suites.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn exact_obligation_response_replays_exactly_after_worker_death() {
    exact_obligation_response_replays_exactly_after_worker_death_with(
        false,
        '4',
        "fixed_ambient_prepare_restart_replay",
    )
    .await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn exact_obligation_response_replays_exactly_after_worker_death_under_the_differential() {
    exact_obligation_response_replays_exactly_after_worker_death_with(
        true,
        'e',
        "fixed_ambient_prepare_restart_replay_differential",
    )
    .await;
}

/// Pass 7.7b: a worker request with more than 128 clauses is served, in one
/// round trip, on every clause-carrying operation.
///
/// The old `maxClauseBatchItems = 128` cap is gone from Lean and from Rust,
/// so `admit_clauses` takes all 130 sources at once and
/// `prepare_clause_pieces` takes all 130 clauses at once. Both counts are
/// exact: one admission call, and exactly one clause-piece round trip for a
/// set that the removed cap would have split into two.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_clause_batch_larger_than_the_removed_cap_is_served_in_one_request() {
    let solver_admission = agent_admission(1, 1);
    let cancellation = CancellationToken::new();
    let bound = bind(worker_pool(1), '5', None, &solver_admission, &cancellation).await;
    let (_task, admission, solver, _houdini) = bound.into_parts();

    // Distinct, admissible level-zero clauses over the fixture's own
    // relations, one per constant, so no two share a clause identity.
    // 130 > the removed 128-item cap.
    let count = 130usize;
    let sources = (0..count)
        .map(|k| format!("(σ[#0 = {k}] op_zE ⊆ op_zT)"))
        .collect::<Vec<_>>();
    let references = sources.iter().map(String::as_str).collect::<Vec<_>>();
    let clauses = admit(&admission, &references, &solver_admission, &cancellation).await;
    assert_eq!(
        clauses.len(),
        count,
        "one admit_clauses call admits all {count} clauses"
    );

    solver
        .prefetch_clause_pieces(&clauses, &solver_admission, &cancellation)
        .await
        .expect("an unbounded clause-piece set is fetched in one request");

    let stats = solver.piece_cache_stats();
    let (clause_pieces, _task_pieces, _support_sets) = solver.piece_cache_sizes();
    assert_eq!(
        clause_pieces,
        count * 4,
        "every clause contributes its four pieces"
    );
    assert_eq!(stats.clause_piece_misses as usize, clause_pieces);
    assert_eq!(
        stats.clause_piece_fetches, 1,
        "{count} clauses need exactly one unchunked request"
    );

    // A second call over the same clauses is fully cached, so it makes no
    // further round trip at all.
    solver
        .prefetch_clause_pieces(&clauses, &solver_admission, &cancellation)
        .await
        .unwrap();
    assert_eq!(solver.piece_cache_stats(), stats);

    solver.shutdown().await.unwrap();
    drop(admission);
}

// ------------------------------------------------------------
// Production Stabilization
// ------------------------------------------------------------

#[derive(Debug, PartialEq, Eq)]
struct StabilizedIdentity {
    scope: Value,
    snapshot: Value,
    levels: Vec<(String, u64)>,
}

async fn live_production_stabilization(
    vampire_processes: usize,
    workers: usize,
    digit: char,
) -> StabilizedIdentity {
    let directory = support::TestDir::new(&format!(
        "fixed_ambient_production_{vampire_processes}_{workers}"
    ));
    let launch_log = directory.path().join("vampire-launches.log");
    let solver_admission = agent_admission(vampire_processes, workers);
    let cancellation = CancellationToken::new();
    let bound = bind(
        worker_pool(workers),
        digit,
        None,
        &solver_admission,
        &cancellation,
    )
    .await;
    let (task, admission, solver, mut houdini) = bound.into_parts();
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();

    let clauses = admit(
        &admission,
        &[
            LEVEL_ZERO_CLAUSE,
            LEVEL_ONE_CLAUSE,
            SECOND_LEVEL_ZERO_CLAUSE,
        ],
        &solver_admission,
        &cancellation,
    )
    .await;
    assert_eq!(clauses.len(), 3);
    let ids = register_and_enqueue(&mut houdini, &clauses);

    let command = VampireWorkerCommand::new(support::fake_vampire())
        .with_extra_args([
            OsString::from("--fixture"),
            OsString::from("race-proof-fast"),
            OsString::from("--expect-start"),
            OsString::from("1"),
            OsString::from("--launch-log"),
            launch_log.as_os_str().to_owned(),
        ])
        .unwrap();
    let mut checker = solver.clone().production_checker(production_config(
        &artifacts,
        &solver_admission,
        FmbOptions::default(),
        command,
        &cancellation,
    ));
    let outcome = stabilize_leveled_houdini_with_system_clauses(&mut houdini, &mut checker)
        .await
        .unwrap();
    let LeveledStabilizationOutcome::Stabilized(core) = outcome else {
        panic!("live fixed-ambient stabilization did not close: {outcome:?}")
    };
    // The computed precondition of the input has no EDB-only conjunct, so
    // Lean reserves no protected row (nothing to install) and the Core is
    // exactly the proposal.
    assert!(!houdini.system_installation_pending().unwrap());
    assert!(houdini.system_clauses().is_empty());
    assert_eq!(core.snapshot().canonical_order().len(), 3);
    assert_eq!(ids.len(), 3);
    for clause in &ids {
        let source = houdini
            .catalog()
            .record(*clause)
            .unwrap()
            .formula()
            .canonical_source()
            .to_owned();
        let expected = if source == LEVEL_ONE_CLAUSE {
            FrameworkIILevel::ONE
        } else {
            assert!(source == LEVEL_ZERO_CLAUSE || source == SECOND_LEVEL_ZERO_CLAUSE);
            FrameworkIILevel::ZERO
        };
        assert_eq!(
            houdini.committed_levels().get(clause),
            Some(&expected),
            "{source}"
        );
    }
    // Committed clauses are never re-checked, so only some roots stay
    // current at the end of a scan; every retained one still carries its
    // exact runtime proof receipt.
    let mut retained_roots = 0_usize;
    for clause in &ids {
        for role in ROLES {
            let Some(root) = houdini.current_root(*clause, role) else {
                continue;
            };
            retained_roots += 1;
            let proof = root
                .proof_evidence()
                .runtime_proof()
                .expect("ordinary fixed-ambient roots carry runtime proof receipts");
            assert_eq!(proof.preparation_digest().len(), 64);
            assert_eq!(proof.semantic_vc_digest().len(), 64);
            let receipt = artifacts.resolve(proof.receipt_artifact()).unwrap();
            let payload: Value =
                serde_json::from_slice(&fs::read(receipt.path()).unwrap()).unwrap();
            assert_eq!(
                payload["fields"]["fixed_ambient_job"]["preparation_digest"].as_str(),
                Some(proof.preparation_digest())
            );
            assert!(payload["fields"].get("ordinary_job").is_none());
            assert!(
                payload["fields"]
                    .get("finite_validity_application")
                    .is_none()
            );
            assert!(payload["fields"].get("protected").is_none());
        }
    }
    assert!(retained_roots > 0);

    let launches_before = fs::read_to_string(&launch_log).unwrap().lines().count();
    assert!(launches_before >= 6, "launches: {launches_before}");
    let stats_before = solver.piece_cache_stats();
    let sizes_before = solver.piece_cache_sizes();
    assert!(matches!(
        stabilize_leveled_houdini_with_system_clauses(&mut houdini, &mut checker)
            .await
            .unwrap(),
        LeveledStabilizationOutcome::Stabilized(_)
    ));
    let launches_after = fs::read_to_string(&launch_log).unwrap().lines().count();
    assert_eq!(launches_after, launches_before);

    // Pass 7.5d: every cache miss renders one piece or one support block
    // through Lean exactly once, and nothing is evicted, so the miss counts
    // equal the number of distinct keys held. Three clauses contribute four
    // pieces each; the task contributes its five in one round trip.
    let stats = solver.piece_cache_stats();
    let (clause_pieces, task_pieces, support_sets) = solver.piece_cache_sizes();
    assert_eq!(
        stats, stats_before,
        "a settled run fetches no further pieces"
    );
    assert_eq!((clause_pieces, task_pieces, support_sets), sizes_before);
    assert_eq!(task_pieces, 5);
    assert_eq!(stats.task_piece_fetches, 1);
    assert_eq!(clause_pieces, 3 * 4);
    assert_eq!(stats.clause_piece_misses as usize, clause_pieces);
    assert_eq!(stats.support_misses as usize, support_sets);
    // Every clause and every task piece of this fixture is constant-free,
    // so all seven obligations share the one empty constant set.
    assert_eq!(support_sets, 1);
    assert!(stats.support_fetches >= stats.support_misses);
    assert!(
        stats.clause_piece_fetches >= 1 && stats.clause_piece_fetches <= 3,
        "clause pieces arrive in batches: {}",
        stats.clause_piece_fetches
    );

    let identity = StabilizedIdentity {
        scope: core.snapshot().scope().identity().clone(),
        snapshot: core.identity().clone(),
        levels: core
            .snapshot()
            .canonical_order()
            .iter()
            .map(|clause| {
                (
                    houdini
                        .catalog()
                        .record(*clause)
                        .unwrap()
                        .formula()
                        .canonical_source()
                        .to_owned(),
                    core.snapshot().level_of(*clause).unwrap().get(),
                )
            })
            .collect(),
    };
    drop(checker);
    solver.shutdown().await.unwrap();
    drop(solver);
    drop(admission);
    drop(artifacts);
    owner.settle().unwrap();
    identity
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn live_fixed_ambient_production_matches_in_serial_and_bounded_pool_modes() {
    let serial = live_production_stabilization(1, 1, '5').await;
    let pooled = live_production_stabilization(2, 3, '5').await;
    assert_eq!(serial, pooled);
    assert_eq!(serial.levels.len(), 3);
    assert!(serial.levels.iter().any(|(_, level)| *level == 0));
    assert!(serial.levels.iter().any(|(_, level)| *level == 1));
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn cancelled_fixed_ambient_preparation_publishes_nothing_and_worker_recovers() {
    let directory = support::TestDir::new("fixed_ambient_prepare_cancellation");
    let launch_log = directory.path().join("vampire-launches.log");
    let solver_admission = agent_admission(1, 1);
    let setup_cancellation = CancellationToken::new();
    let (pool, marker) = fault_pool(&directory, "stall_prepare");
    let bound = bind(pool, '6', None, &solver_admission, &setup_cancellation).await;
    let (task, admission, solver, mut houdini) = bound.into_parts();
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let clauses = admit(
        &admission,
        &[LEVEL_ZERO_CLAUSE],
        &solver_admission,
        &setup_cancellation,
    )
    .await;
    let external = register_and_enqueue(&mut houdini, &clauses)[0];
    // No protected row exists for this input, so the stalled worker call is
    // the proposed clause's initialization preparation.

    let cancellation = CancellationToken::new();
    let config = proof_only_production_config(
        &artifacts,
        &solver_admission,
        proof_vampire(&launch_log),
        &cancellation,
    );
    let task_solver = solver.clone();
    let stabilization = tokio::spawn(async move {
        let mut checker = task_solver.production_checker(config);
        let result = stabilize_leveled_houdini(&mut houdini, &mut checker).await;
        (houdini, result)
    });
    wait_for_marker(&marker).await;
    cancellation.cancel();
    let (mut houdini, result) = stabilization.await.unwrap();
    // A cancelled scan is a typed stop, not an outcome: the partition is
    // exactly as it was when the scan began.
    assert!(matches!(result, Err(FrameworkIIStateError::Cancelled)));
    assert!(houdini.attempts().rows().is_empty());
    assert!(houdini.pending_levels().contains_key(&external));
    assert!(!houdini.system_clauses_installed());
    assert!(houdini.committed_levels().is_empty());
    {
        let clause = external;
        assert!(
            houdini
                .current_root(clause, FrameworkIICheckRole::Initialization)
                .is_none()
        );
    }
    assert!(!launch_log.exists());

    let mut checker = solver
        .clone()
        .production_checker(proof_only_production_config(
            &artifacts,
            &solver_admission,
            proof_vampire(&launch_log),
            &CancellationToken::new(),
        ));
    assert!(matches!(
        stabilize_leveled_houdini(&mut houdini, &mut checker)
            .await
            .unwrap(),
        LeveledStabilizationOutcome::Stabilized(_)
    ));
    assert!(!houdini.system_installation_pending().unwrap());
    assert!(houdini.system_clauses().is_empty());
    {
        let clause = external;
        for role in ROLES {
            assert!(houdini.current_root(clause, role).is_some());
        }
    }

    drop(checker);
    solver.shutdown().await.unwrap();
    drop(solver);
    drop(admission);
    drop(artifacts);
    owner.settle().unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn live_fixed_ambient_casc_winner_selects_the_casc_certificate_profile() {
    let directory = support::TestDir::new("fixed_ambient_casc_receipt");
    let launch_log = directory.path().join("vampire-launches.log");
    let solver_admission = agent_admission(1, 1);
    let cancellation = CancellationToken::new();
    let bound = bind(worker_pool(1), '7', None, &solver_admission, &cancellation).await;
    let (task, admission, solver, mut houdini) = bound.into_parts();
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let clauses = admit(
        &admission,
        &[LEVEL_ZERO_CLAUSE],
        &solver_admission,
        &cancellation,
    )
    .await;
    let external = register_and_enqueue(&mut houdini, &clauses)[0];

    let command = VampireWorkerCommand::new(support::fake_vampire())
        .with_extra_args([
            OsString::from("--fixture"),
            OsString::from("ladder-unknown-casc-proof"),
            OsString::from("--launch-log"),
            launch_log.as_os_str().to_owned(),
        ])
        .unwrap()
        .with_proof_casc_share(ProofCascShare::CLI_DEFAULT)
        .unwrap();
    // A run that has explicitly enabled the CASC portfolio: this test's
    // subject is what the search does with a `casc_2025` winner, and since
    // the Milestone 7.5 review (finding 5) the portfolio is a run option
    // that is disabled by default, which would otherwise clear the CASC
    // share from every launch command of this run.
    let config =
        proof_only_production_config(&artifacts, &solver_admission, command, &cancellation);
    let retry_policy = config
        .retry_policy()
        .clone()
        .with_casc_portfolio(CascPortfolioPolicy::Enabled);
    let mut checker = solver
        .clone()
        .production_checker(config.with_retry_policy(retry_policy));
    assert!(matches!(
        stabilize_leveled_houdini(&mut houdini, &mut checker)
            .await
            .unwrap(),
        LeveledStabilizationOutcome::Stabilized(_)
    ));

    for role in ROLES {
        let receipt = houdini
            .current_root(external, role)
            .expect("the CASC-backed row has both final roots")
            .proof_evidence()
            .runtime_proof()
            .expect("the CASC winner constructs a runtime proof receipt");
        assert_eq!(receipt.winner(), ProofSearchProfile::Casc2025);
        assert_eq!(
            receipt.certification_profile().profile(),
            ProofSearchProfile::Casc2025
        );
        assert_eq!(
            receipt.certification_profile().profile_version(),
            "fixture-casc-2025-v1"
        );
        let arguments = receipt
            .runtime_invocation()
            .arguments()
            .iter()
            .map(AsRef::<str>::as_ref)
            .collect::<Vec<_>>();
        assert!(
            arguments
                .windows(2)
                .any(|pair| pair == ["--mode", "portfolio"])
        );
        assert!(
            arguments
                .windows(2)
                .any(|pair| pair == ["--schedule", "casc_2025"])
        );
    }
    assert_eq!(fs::read_to_string(&launch_log).unwrap().lines().count(), 4);

    drop(checker);
    solver.shutdown().await.unwrap();
    drop(solver);
    drop(admission);
    drop(artifacts);
    owner.settle().unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn live_fixed_ambient_finite_model_refutation_of_a_prophecy_free_clause_is_dead() {
    let directory = support::TestDir::new("fixed_ambient_validated_fmb_refutation");
    let solver_admission = agent_admission(1, 1);
    let cancellation = CancellationToken::new();
    let bound = bind(worker_pool(1), '8', None, &solver_admission, &cancellation).await;
    let (task, admission, solver, mut houdini) = bound.into_parts();
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let clauses = admit(&admission, &[EDB_CLAUSE], &solver_admission, &cancellation).await;
    assert_eq!(clauses[0].minimum_level(), FrameworkIILevel::ZERO);
    let external = register_and_enqueue(&mut houdini, &clauses)[0];

    let mut checker = solver.clone().production_checker(production_config(
        &artifacts,
        &solver_admission,
        FmbOptions::default(),
        refuting_model_vampire(directory.path()),
        &cancellation,
    ));
    let outcome = stabilize_leveled_houdini(&mut houdini, &mut checker)
        .await
        .unwrap();
    assert!(
        matches!(outcome, LeveledStabilizationOutcome::Stabilized(_)),
        "{outcome:?}\nrows={:#?}",
        houdini.attempts().rows()
    );
    // `EDB_CLAUSE` mentions no prophecy relation: Pass 7.5b's dead rule makes
    // this Lean-validated level-zero initialization refutation final rather
    // than a promotion candidate.
    assert!(houdini.dead().contains_key(&external));
    assert!(!houdini.committed_levels().contains_key(&external));
    assert!(houdini.pending_levels().is_empty());

    let (refuted_row, refutation) = houdini
        .attempts()
        .rows()
        .iter()
        .find_map(|row| {
            let LevelLedgerRow::Attempt(row) = row else {
                return None;
            };
            if row.request().clause() != external
                || row.request().level() != FrameworkIILevel::ZERO
                || row.request().role() != FrameworkIICheckRole::Initialization
            {
                return None;
            }
            let FrameworkIICheckOutcome::Refuted(evidence) = row.outcome() else {
                return None;
            };
            evidence
                .validated_refutation()
                .cloned()
                .map(|receipt| (row.row_ordinal(), receipt))
        })
        .expect("the level-zero finite model is retained as Lean-validated refutation authority");
    assert_eq!(refutation.source_artifact().kind(), ArtifactKind::Model);
    assert_eq!(
        refutation.validation_artifact().kind(),
        ArtifactKind::Witness
    );
    assert_eq!(refutation.receipt_artifact().kind(), ArtifactKind::Witness);
    assert_eq!(
        refutation.validation_identity()["kind"],
        json!("whiel_framework_ii_base_refutation_validation")
    );
    assert_eq!(
        refutation.validation_identity()["axioms_hold"].as_bool(),
        Some(true)
    );
    assert_eq!(
        refutation.validation_identity()["conjecture_holds"].as_bool(),
        Some(false)
    );
    assert_eq!(
        refutation.validation_identity()["validated_refutation"].as_bool(),
        Some(true)
    );
    assert_eq!(refutation.validation_digest().len(), 64);
    assert_eq!(refutation.refutation_digest().len(), 64);
    let receipt_artifact = artifacts.resolve(refutation.receipt_artifact()).unwrap();
    let receipt_payload: Value =
        serde_json::from_slice(&fs::read(receipt_artifact.path()).unwrap()).unwrap();
    assert_eq!(
        receipt_payload["fields"]["fixed_ambient_job"]["preparation_digest"].as_str(),
        Some(refutation.preparation_digest())
    );
    assert_eq!(
        receipt_payload["fields"]["validation_identity"]["interpretation_identity"]["kind"],
        json!("whiel_framework_ii_finite_interpretation")
    );

    let dead_reason = houdini
        .dead_reason(external)
        .expect("the prophecy-free clause is dead");
    assert_eq!(
        dead_reason,
        whiel_runner::FrameworkIIDeadReason::ProphecyFreeInitializationRefuted {
            attempt: refuted_row,
        }
    );
    for role in ROLES {
        assert!(houdini.current_root(external, role).is_none());
    }

    // A raw re-registration of the exact same identity never resurrects it:
    // the low-level catalog/state boundary silently keeps it dead (the
    // proposal boundary instead rejects a live resubmission with this exact
    // reason, exercised in the scripted `proposal_tests` suite).
    let resubmission = admit(&admission, &[EDB_CLAUSE], &solver_admission, &cancellation).await;
    assert_eq!(resubmission[0].identity(), clauses[0].identity());
    let next_ordinal = houdini.catalog().next_batch_ordinal().unwrap();
    let registered = houdini
        .catalog()
        .register_batch(
            next_ordinal,
            resubmission
                .iter()
                .cloned()
                .map(|clause| (clause, ExtendedClauseOrigin::Submitted)),
        )
        .unwrap();
    assert_eq!(registered.ids()[0], external);
    houdini.enqueue_registered(&registered).unwrap();
    assert!(houdini.is_dead(external));
    assert!(!houdini.pending_levels().contains_key(&external));
    assert_eq!(houdini.dead_reason(external), Some(dead_reason));

    drop(checker);
    solver.shutdown().await.unwrap();
    drop(solver);
    drop(admission);
    drop(artifacts);
    owner.settle().unwrap();
}

fn recording_fixture(
    task: &SynthesisTask,
    feedback: &whiel_runner::framework2::AgentFeedback,
    policy: &AgentConsultationPolicy,
) -> TranscriptRecorder {
    TranscriptRecorder::new(
        TranscriptHeader::new(
            "offline-fixed-ambient-fixture".into(),
            feedback.run_digest().into(),
            TranscriptPins {
                task_digest: feedback.task_digest().into(),
                source_digest: task.identity().source_digest().as_str().into(),
                scope_digest: feedback.scope_digest().into(),
                policy_digest: policy.digest().into(),
                // These pure fixture labels make no claim to production toolchain pins.
                runner_digest: "1".repeat(64),
                worker_digest: "2".repeat(64),
                lean_digest: "3".repeat(64),
                vampire_digest: "4".repeat(64),
                profile_digest: "5".repeat(64),
            },
        ),
        4 * 1024 * 1024,
    )
    .unwrap()
}

// This bounded selector is test configuration for the two substitution gates
// only. Opaque arguments are never interpreted or rewritten by B.
#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct AcceptanceProposerCommand {
    executable: String,
    arguments: Vec<String>,
}

fn parse_acceptance_proposer_command(
    bytes: &[u8],
) -> Result<whiel_runner::proposer_host::generic_process::GenericProcessConfig, &'static str> {
    const MAX_BYTES: usize = 16 * 1024;
    if bytes.is_empty() || bytes.len() > MAX_BYTES {
        return Err("acceptance command must contain at most 16384 bytes");
    }
    let command: AcceptanceProposerCommand =
        serde_json::from_slice(bytes).map_err(|_| "invalid acceptance command JSON")?;
    if command.executable.is_empty()
        || !Path::new(&command.executable).is_absolute()
        || command.executable.contains('\0')
        || command.arguments.len() > 128
        || command
            .arguments
            .iter()
            .any(|argument| argument.contains('\0'))
    {
        return Err("acceptance command requires an absolute executable and bounded NUL-free argv");
    }
    Ok(
        whiel_runner::proposer_host::generic_process::GenericProcessConfig::new(
            command.executable.into(),
            command.arguments.into_iter().map(OsString::from).collect(),
        ),
    )
}

fn independent_proposer_command(
    directory: &Path,
    mode: &str,
) -> whiel_runner::proposer_host::generic_process::GenericProcessConfig {
    let python = std::env::split_paths(&std::env::var_os("PATH").expect("PATH is set"))
        .map(|directory| directory.join("python3"))
        .find(|path| path.is_file())
        .expect("Python 3 is required for the independent standard-library fixture")
        .canonicalize()
        .unwrap();
    whiel_runner::proposer_host::generic_process::GenericProcessConfig::new(
        python,
        vec![
            "-I".into(),
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("tests/fixtures/generic_api_acceptance.py")
                .into_os_string(),
            "--trace".into(),
            directory.join("api-trace.jsonl").into_os_string(),
            "--mode".into(),
            mode.into(),
        ],
    )
}

fn acceptance_proposer_command(
    directory: &Path,
    mode: &str,
) -> whiel_runner::proposer_host::generic_process::GenericProcessConfig {
    assert!(matches!(mode, "full" | "historical"));
    match std::env::var_os("WHIEL_ACCEPTANCE_PROPOSER_COMMAND") {
        None => independent_proposer_command(directory, mode),
        Some(value) => {
            use std::os::unix::ffi::OsStrExt;
            parse_acceptance_proposer_command(value.as_bytes())
                .expect("invalid WHIEL_ACCEPTANCE_PROPOSER_COMMAND; no fallback is permitted")
        }
    }
}

#[test]
fn acceptance_proposer_command_is_strict_bounded_and_preserves_opaque_arguments() {
    let command = parse_acceptance_proposer_command(
        br#"{"executable":"/caller/endpoint","arguments":["","--help","$(touch nope)","a b"]}"#,
    )
    .unwrap();
    assert_eq!(command.executable, Path::new("/caller/endpoint"));
    assert_eq!(
        command.arguments,
        ["", "--help", "$(touch nope)", "a b"].map(OsString::from)
    );
    for invalid in [
        "",
        "null",
        "[]",
        "{}",
        r#"{"executable":"/x"}"#,
        r#"{"executable":"x","arguments":[]}"#,
        r#"{"executable":"","arguments":[]}"#,
        r#"{"executable":"/x","arguments":null}"#,
        r#"{"executable":"/x","arguments":[1]}"#,
        r#"{"executable":"/x","arguments":["\u0000"]}"#,
        r#"{"executable":"/x\u0000","arguments":[]}"#,
        r#"{"executable":"/x","arguments":[],"provider":"ignored"}"#,
        r#"{"executable":"/x","executable":"/y","arguments":[]}"#,
    ] {
        assert!(
            parse_acceptance_proposer_command(invalid.as_bytes()).is_err(),
            "{invalid}"
        );
    }
    assert!(parse_acceptance_proposer_command(&[b' '; 16385]).is_err());
    assert!(parse_acceptance_proposer_command(&[0xff]).is_err());
    assert!(
        parse_acceptance_proposer_command(
            &serde_json::to_vec(&json!({"executable":"/x","arguments":vec!["";129]})).unwrap()
        )
        .is_err()
    );
}

// Keep the endpoint available for explicit normal shutdown after Agent is
// consumed/dropped, without adding a test-only lifecycle method to the API.
struct BorrowedProposer<'a, P>(&'a mut P);

impl<P: AgentProvider> AgentProvider for BorrowedProposer<'_, P> {
    fn api_capabilities(&self) -> whiel_runner::proposer_api::ApiCapabilities {
        self.0.api_capabilities()
    }
    fn resource_failure(&self) -> Option<String> {
        self.0.resource_failure()
    }
    fn terminal_failure(&self) -> Option<whiel_runner::proposer_api::ProposerTerminalFailure> {
        self.0.terminal_failure()
    }
    fn consult<'a>(
        &'a mut self,
        push: &'a AgentPush,
        tools: &'a dyn AgentToolSurface,
        response: &'a mut AgentResponseWriter,
        cancellation: AgentSourceCancellation,
    ) -> AgentSourceFuture<'a> {
        self.0.consult(push, tools, response, cancellation)
    }
    fn quiesce_request(&mut self) -> AgentSourceCleanupFuture<'_> {
        self.0.quiesce_request()
    }
    fn shutdown(
        &mut self,
        reason: whiel_runner::proposer_api::wire::ShutdownReason,
    ) -> AgentSourceCleanupFuture<'_> {
        self.0.shutdown(reason)
    }
}

async fn catch_test_panic<F: std::future::Future>(future: F) -> std::thread::Result<F::Output> {
    let mut future = std::pin::pin!(future);
    std::future::poll_fn(|context| {
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            future.as_mut().poll(context)
        })) {
            Ok(std::task::Poll::Ready(value)) => std::task::Poll::Ready(Ok(value)),
            Ok(std::task::Poll::Pending) => std::task::Poll::Pending,
            Err(panic) => std::task::Poll::Ready(Err(panic)),
        }
    })
    .await
}

async fn finish_acceptance_proposer<T>(
    provider: &mut whiel_runner::proposer_host::generic_process::GenericProcessProposer,
    cleanup: &whiel_runner::proposer_host::generic_process::GenericProcessCleanup,
    result: std::thread::Result<T>,
) -> T {
    let shutdown = provider
        .shutdown(whiel_runner::proposer_api::wire::ShutdownReason::Complete)
        .await;
    if result.is_err() || shutdown.is_err() {
        cleanup
            .stop_and_join()
            .await
            .expect("failed-test endpoint fallback must join");
    }
    let value = match result {
        Ok(value) => value,
        Err(panic) => std::panic::resume_unwind(panic),
    };
    shutdown.expect("normal acceptance endpoint Shutdown/Closed must complete");
    assert!(provider.resource_failure().is_none());
    assert!(provider.terminal_failure().is_none());
    value
}

struct CanonicalAcceptanceTrace {
    observations: Vec<Value>,
    submissions: Vec<Value>,
    queries: Vec<Value>,
    outcomes: Vec<TranscriptOutcome>,
}

fn canonical_acceptance_trace(
    recorder: &TranscriptRecorder,
    artifacts: &ArtifactStore,
) -> CanonicalAcceptanceTrace {
    let recorded = recorder.finish(artifacts).unwrap();
    recorded.require_replayable().unwrap();
    let transcript = VerifiedTranscript::read(recorded.frames(), recorded.head()).unwrap();
    let mut pushes = BTreeMap::new();
    let mut responses = BTreeMap::<_, Vec<u8>>::new();
    let mut calls = BTreeMap::new();
    let mut queries = BTreeMap::new();
    let mut outcomes = Vec::new();
    for event in transcript.events() {
        match event {
            TranscriptEvent::Bytes {
                coordinates,
                stream: TranscriptStream::Push,
                bytes,
                ..
            } => {
                whiel_runner::framework2::replay_identity::decode_push(bytes).unwrap();
                assert!(
                    pushes
                        .insert(
                            *coordinates,
                            serde_json::from_slice::<Value>(bytes).unwrap()
                        )
                        .is_none()
                );
            }
            TranscriptEvent::Bytes {
                coordinates,
                stream: TranscriptStream::Response,
                bytes,
                accounting,
            } => {
                assert!(accounting.as_ref().unwrap().accepted);
                responses
                    .entry(*coordinates)
                    .or_default()
                    .extend_from_slice(bytes);
            }
            TranscriptEvent::ToolCall {
                coordinates,
                call_id,
                name,
                arguments,
            } => {
                assert!(
                    calls
                        .insert(*call_id, (*coordinates, name, arguments))
                        .is_none()
                );
            }
            TranscriptEvent::ToolResponse {
                coordinates,
                call_id,
                response,
            } => {
                let (called_at, name, arguments) =
                    calls.remove(call_id).expect("response has a recorded call");
                assert_eq!(called_at, *coordinates);
                serde_json::from_slice::<whiel_runner::proposer_api::query_results::ToolResponseV1>(response).unwrap();
                let reply: Value = serde_json::from_slice(response).unwrap();
                assert_eq!(reply["tool"], name.as_str());
                assert_eq!(
                    reply["state_revision"],
                    pushes[coordinates]["feedback"]["state_revision"]
                );
                assert!(queries.insert(*call_id, json!({
                    "coordinates":coordinates, "name":name,
                    "arguments":serde_json::from_slice::<Value>(arguments).unwrap(), "reply":reply,
                })).is_none());
            }
            TranscriptEvent::Outcome { outcome, .. } if *outcome != TranscriptOutcome::Received => {
                outcomes.push(*outcome);
            }
            _ => {}
        }
    }
    assert!(
        calls.is_empty(),
        "every canonical query must have a complete response"
    );
    assert_eq!(pushes.len(), responses.len());
    let observations = pushes.into_iter().map(|(coordinates, observation)| {
        json!({"coordinates":coordinates, "observation":observation})
    }).collect();
    let submissions = responses.into_iter().map(|(coordinates, bytes)| {
        json!({"coordinates":coordinates, "response":serde_json::from_slice::<Value>(&bytes).unwrap()})
    }).collect();
    CanonicalAcceptanceTrace {
        observations,
        submissions,
        queries: queries.into_values().collect(),
        outcomes,
    }
}

fn verify_recording(
    recorder: &TranscriptRecorder,
    artifacts: &ArtifactStore,
    observed: &Mutex<Vec<ObservedProviderRequest>>,
) -> VerifiedTranscript {
    let recorded = recorder.finish(artifacts).unwrap();
    let verified = VerifiedTranscript::read(recorded.frames(), recorded.head()).unwrap();
    recorded.require_replayable().unwrap_or_else(|error| {
        panic!(
            "recording is not replayable: {error:?}; owner failures: {:?}",
            verified
                .events()
                .iter()
                .filter_map(|event| {
                    if let TranscriptEvent::OwnerUnavailable {
                        coordinates,
                        reason,
                    } = event
                    {
                        Some((coordinates, reason))
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>()
        )
    });
    verify_recorded_owner_correspondence(&verified, observed, recorder);
    for event in verified.events() {
        match event {
            TranscriptEvent::Bytes {
                stream: TranscriptStream::Push,
                bytes,
                ..
            } => {
                whiel_runner::framework2::replay_identity::decode_push(bytes).unwrap();
            }
            TranscriptEvent::ToolResponse { response, .. } => {
                whiel_runner::framework2::replay_identity::decode_tool_response(response).unwrap();
            }
            _ => {}
        }
    }
    verified
}

// ------------------------------------------------------------
// Agent Consultation
// ------------------------------------------------------------

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn live_agent_clause_response_admits_without_publication() {
    let directory = support::TestDir::new("fixed_ambient_live_agent_clause_admission");
    let solver_admission = agent_admission(1, 1);
    let cancellation = CancellationToken::new();
    let bound = bind(worker_pool(1), '9', None, &solver_admission, &cancellation).await;
    let (task, admission, solver, houdini) = bound.into_parts();
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let catalog = houdini.catalog().clone();
    let feedback_state = PreCertificateAgentHoudiniState::new(
        Arc::clone(&task),
        &artifacts,
        &houdini,
        Duration::from_secs(30),
        AgentFeedbackPolicy::default(),
    )
    .unwrap();
    let feedback = feedback_state.feedback().clone();
    let revision_before = houdini.proposal_revision();
    let registration_before = catalog.next_batch_ordinal().unwrap();
    // Nothing is interned before consultation: the input reserves no
    // protected precondition row.
    assert_eq!(catalog.len().unwrap(), 0);

    let observed = Arc::new(Mutex::new(Vec::new()));
    let policy = AgentConsultationPolicy::default();
    let recorder = recording_fixture(&task, &feedback, &policy);
    let mut agent = RecordingProvider::agent(
        ClauseProvider {
            clauses: vec![LEVEL_ZERO_CLAUSE],
            observed: Arc::clone(&observed),
        },
        policy,
        recorder.clone(),
    );
    let validator = AgentResponseValidator::new(
        &task,
        &houdini,
        &admission,
        &solver,
        &solver_admission,
        &feedback_state,
        None,
    );
    let proposal = agent
        .get_houdini_proposal(&feedback, &validator, &cancellation)
        .await
        .expect("live Agent consultation is not cancelled");
    let HoudiniProposal::CandidateClauses(epoch) = proposal else {
        panic!("the live clause response did not produce an admitted epoch: {proposal:?}")
    };

    assert_eq!(epoch.context().proposal_revision(), revision_before);
    assert_eq!(
        epoch.context().expected_registration_ordinal(),
        registration_before
    );
    assert_eq!(epoch.clauses().len(), 1);
    assert_eq!(epoch.clauses()[0].canonical_source(), LEVEL_ZERO_CLAUSE);
    assert!(epoch.dropped().is_empty());
    assert_eq!(houdini.proposal_revision(), revision_before);
    assert!(houdini.core().snapshot().canonical_order().is_empty());
    assert!(houdini.pending_levels().is_empty());
    assert!(houdini.committed_levels().is_empty());
    assert_eq!(catalog.next_batch_ordinal().unwrap(), registration_before);
    assert_eq!(catalog.len().unwrap(), 0);
    assert!(catalog.find(&epoch.clauses()[0]).unwrap().is_none());
    assert_eq!(agent.attempt_history().len(), 1);
    assert_eq!(
        agent.attempt_history()[0].outcome(),
        AgentRequestAttemptOutcome::Accepted
    );
    assert_eq!(observed.lock().unwrap().len(), 1);

    let recording = verify_recording(&recorder, &artifacts, &observed);
    let pushes: Vec<_> = recording
        .events()
        .iter()
        .filter_map(|event| match event {
            TranscriptEvent::Bytes {
                stream: TranscriptStream::Push,
                bytes,
                coordinates,
                ..
            } => Some((bytes, coordinates)),
            _ => None,
        })
        .collect();
    assert_eq!(pushes.len(), 1);
    assert_eq!(pushes[0].0, &observed.lock().unwrap()[0].bytes);
    assert_eq!(
        (
            pushes[0].1.consultation,
            pushes[0].1.validation,
            pushes[0].1.transport
        ),
        (0, 0, 0)
    );
    assert!(recording.events().iter().any(|event| matches!(
        event,
        TranscriptEvent::Outcome {
            outcome: TranscriptOutcome::Accepted,
            ..
        }
    )));
    // Refuse even when only the final Accepted tap exceeds the recording
    // budget: validation must not release its otherwise admitted proposal.
    let maximum = serde_json::to_vec(recording.header()).unwrap().len()
        + recording
            .events()
            .iter()
            .filter(|event| {
                !matches!(
                    event,
                    TranscriptEvent::Outcome {
                        outcome: TranscriptOutcome::Accepted,
                        ..
                    }
                )
            })
            .map(|event| serde_json::to_vec(event).unwrap().len())
            .sum::<usize>();
    let limited_recorder = TranscriptRecorder::new(recording.header().clone(), maximum).unwrap();
    let mut limited_agent = RecordingProvider::agent(
        ClauseProvider {
            clauses: vec![LEVEL_ZERO_CLAUSE],
            observed: Arc::new(Mutex::new(Vec::new())),
        },
        AgentConsultationPolicy::default(),
        limited_recorder.clone(),
    );
    let rejected = limited_agent
        .get_houdini_proposal(&feedback, &validator, &cancellation)
        .await
        .unwrap();
    assert!(matches!(rejected, HoudiniProposal::Failure(_)));
    assert_eq!(
        limited_recorder.status(),
        Err(whiel_runner::framework2::TranscriptError::LimitExceeded)
    );
    assert_eq!(
        limited_agent.attempt_history()[0].outcome(),
        AgentRequestAttemptOutcome::RecordingFailure
    );
    assert_eq!(catalog.len().unwrap(), 0);
    drop(limited_agent);
    drop(epoch);
    drop(agent);
    drop(feedback_state);
    drop(houdini);
    solver.shutdown().await.unwrap();
    drop(solver);
    drop(admission);
    drop(artifacts);
    owner.settle().unwrap();
}

// The independent B fixture crosses the generic proposer process boundary.
// The ledger comes from the real dispatcher; Lean admits the returned clauses.
// This is an admission test, not a solver or certificate-success fixture.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn live_generic_api_reference_queries_real_ledger_and_admits_leveled_clauses() {
    use whiel_runner::proposer_api::query_results::ToolResponseV1;
    use whiel_runner::proposer_host::generic_process::GenericProcessProposer;

    let directory = support::TestDir::new("fixed_ambient_generic_admission");
    let solver_admission = agent_admission(1, 1);
    let cancellation = CancellationToken::new();
    let bound = bind(worker_pool(1), '6', None, &solver_admission, &cancellation).await;
    let (task, admission, solver, houdini) = bound.into_parts();
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let catalog = houdini.catalog().clone();
    let feedback_state = PreCertificateAgentHoudiniState::new(
        Arc::clone(&task),
        &artifacts,
        &houdini,
        Duration::from_secs(30),
        AgentFeedbackPolicy::default(),
    )
    .unwrap();
    let feedback = feedback_state.feedback().clone();
    let state_before = format!("{houdini:?}");
    let revision_before = houdini.proposal_revision();
    let registration_before = catalog.next_batch_ordinal().unwrap();
    assert_eq!(catalog.len().unwrap(), 0);

    let clauses = [CANONICAL_LEVEL_ZERO_CLAUSE, CANONICAL_LEVEL_ONE_CLAUSE];
    let mut provider = GenericProcessProposer::start(
        independent_proposer_command(directory.path(), "admission"),
        &AgentToolPolicy::all_enabled().enabled_names(),
        &cancellation,
    )
    .await
    .unwrap();
    let cleanup = provider.cleanup_handle();
    let policy = AgentConsultationPolicy::default();
    let recorder = recording_fixture(&task, &feedback, &policy);
    let result = catch_test_panic(async {
        let mut agent =
            RecordingProvider::agent(BorrowedProposer(&mut provider), policy, recorder.clone());
        let validator = AgentResponseValidator::new(
            &task,
            &houdini,
            &admission,
            &solver,
            &solver_admission,
            &feedback_state,
            None,
        );
        let proposal = agent
            .get_houdini_proposal(&feedback, &validator, &cancellation)
            .await
            .expect("the generic reference consultation is not cancelled");
        let HoudiniProposal::CandidateClauses(epoch) = proposal else {
            panic!("generic proposal {proposal:?}");
        };
        assert_eq!(epoch.clauses().len(), 2);
        for ((clause, source), level) in epoch
            .clauses()
            .iter()
            .zip(clauses)
            .zip([FrameworkIILevel::ZERO, FrameworkIILevel::ONE])
        {
            assert_eq!(clause.canonical_source(), source);
            assert_eq!(clause.minimum_level(), level);
            assert!(catalog.find(clause).unwrap().is_none());
        }
        assert!(epoch.dropped().is_empty());
        assert_eq!(epoch.context().proposal_revision(), revision_before);
        assert_eq!(
            epoch.context().expected_registration_ordinal(),
            registration_before
        );
        assert_eq!(format!("{houdini:?}"), state_before);
        assert_eq!(houdini.proposal_revision(), revision_before);
        assert!(houdini.core().snapshot().canonical_order().is_empty());
        assert!(houdini.pending_levels().is_empty());
        assert!(houdini.committed_levels().is_empty());
        assert_eq!(catalog.len().unwrap(), 0);
        assert_eq!(catalog.next_batch_ordinal().unwrap(), registration_before);
        assert_eq!(agent.attempt_history().len(), 1);
        assert_eq!(
            agent.attempt_history()[0].outcome(),
            AgentRequestAttemptOutcome::Accepted
        );

        // RecordingProvider observes the real dispatcher result, independently of
        // the reference client's wire trace or its own JSON-decoding assertions.
        let recorded = recorder.finish(&artifacts).unwrap();
        recorded.require_replayable().unwrap();
        let recording = VerifiedTranscript::read(recorded.frames(), recorded.head()).unwrap();
        let pushes = recording
            .events()
            .iter()
            .filter_map(|event| match event {
                TranscriptEvent::Bytes {
                    stream: TranscriptStream::Push,
                    bytes,
                    ..
                } => Some(bytes),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(pushes.len(), 1);
        let push: Value = serde_json::from_slice(pushes[0]).unwrap();
        whiel_runner::framework2::replay_identity::decode_push(pushes[0]).unwrap();
        let calls = recording
            .events()
            .iter()
            .filter_map(|event| match event {
                TranscriptEvent::ToolCall {
                    call_id,
                    name,
                    arguments,
                    ..
                } => Some((*call_id, name, arguments)),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(calls.len(), 1);
        assert_eq!(calls[0].1, "ledger");
        assert_eq!(
            serde_json::from_slice::<Value>(calls[0].2).unwrap(),
            json!({})
        );
        let responses = recording
            .events()
            .iter()
            .filter_map(|event| match event {
                TranscriptEvent::ToolResponse {
                    call_id, response, ..
                } => Some((*call_id, response)),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(responses.len(), 1);
        assert_eq!(responses[0].0, calls[0].0);
        let reply: ToolResponseV1 = serde_json::from_slice(responses[0].1).unwrap();
        let ToolResponseV1::Ledger(reply) = reply else {
            panic!("the actual ledger call returned an unexpected response: {reply:?}");
        };
        assert_eq!(
            reply.state_revision,
            push["feedback"]["state_revision"].as_u64().unwrap()
        );
        assert!(reply.result.items.is_empty());
        assert_eq!(reply.result.metadata.total_items, 0);
        assert_eq!(reply.result.metadata.first_index, 0);
        assert_eq!(reply.result.metadata.returned_items, 0);
        assert_eq!(reply.result.metadata.continuation, None);
        assert!(recording.events().iter().any(|event| matches!(
            event,
            TranscriptEvent::Outcome {
                outcome: TranscriptOutcome::Accepted,
                ..
            }
        )));

        drop(epoch);
        drop(agent);
    })
    .await;
    finish_acceptance_proposer(&mut provider, &cleanup, result).await;
    drop(feedback_state);
    drop(houdini);
    solver.shutdown().await.unwrap();
    drop(solver);
    drop(admission);
    drop(artifacts);
    owner.settle().unwrap();
}

// B consumes only generic outcomes and API resource accounting. Native prose,
// native process status and local transport accounting are tested by C.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn live_generic_outcomes_never_admit_prose_or_failed_responses() {
    for mode in [
        "no_response",
        "failure",
        "source_exhausted",
        "endpoint_exit",
        "api_flood",
    ] {
        use whiel_runner::proposer_host::generic_process::GenericProcessProposer;
        let directory = support::TestDir::new("generic_failed_admission");
        let budget = agent_admission(1, 1);
        let cancellation = CancellationToken::new();
        let (task, admission, solver, houdini) =
            bind(worker_pool(1), 'c', None, &budget, &cancellation)
                .await
                .into_parts();
        let (owner, artifacts) =
            new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
        let feedback = PreCertificateAgentHoudiniState::new(
            Arc::clone(&task),
            &artifacts,
            &houdini,
            Duration::from_secs(30),
            AgentFeedbackPolicy::default(),
        )
        .unwrap();
        let before = format!("{houdini:?}");
        let ordinal = houdini.catalog().next_batch_ordinal().unwrap();
        let mut config = independent_proposer_command(directory.path(), mode);
        if mode == "api_flood" {
            config.traffic_limits.messages = 12;
        }
        let mut provider = GenericProcessProposer::start(
            config,
            &AgentToolPolicy::all_enabled().enabled_names(),
            &cancellation,
        )
        .await
        .unwrap();
        let cleanup = provider.cleanup_handle();
        let policy = AgentConsultationPolicy::new(AgentConsultationLimits {
            max_transport_retries_per_request: 2,
            ..Default::default()
        })
        .unwrap();
        let result = catch_test_panic(async {
            let mut agent = Agent::new(BorrowedProposer(&mut provider), policy);
            let validator = AgentResponseValidator::new(
                &task, &houdini, &admission, &solver, &budget, &feedback, None,
            );
            let proposal = agent
                .get_houdini_proposal(feedback.feedback(), &validator, &cancellation)
                .await
                .unwrap();
            let HoudiniProposal::Failure(report) = proposal else {
                panic!("generic {mode} outcome admitted a proposal: {proposal:?}");
            };
            let attempts = agent.attempt_history();
            if mode == "api_flood" {
                assert_eq!(report.scope(), FailureScope::RunGlobal);
                assert!(format!("{report:?}").contains("resource_exhausted"));
                assert_eq!(
                    attempts.len(),
                    1,
                    "resource faults preclude transport retry"
                );
            } else if mode == "endpoint_exit" {
                assert_eq!(report.scope(), FailureScope::RunGlobal);
                assert!(
                    attempts.is_empty(),
                    "terminal endpoint failure precedes response admission"
                );
            } else {
                assert!(!attempts.is_empty());
            }
            let expected = match mode {
                "no_response" => AgentRequestAttemptOutcome::NoResponse,
                "failure" | "endpoint_exit" => AgentRequestAttemptOutcome::TransportFailure,
                "source_exhausted" | "api_flood" => AgentRequestAttemptOutcome::SourceExhausted,
                _ => unreachable!(),
            };
            assert!(attempts.iter().all(|attempt| attempt.outcome() == expected));
            assert_eq!(format!("{houdini:?}"), before);
            assert_eq!(houdini.catalog().len().unwrap(), 0);
            assert_eq!(houdini.catalog().next_batch_ordinal().unwrap(), ordinal);
            assert!(houdini.core().snapshot().canonical_order().is_empty());
            assert!(houdini.pending_levels().is_empty());
            assert!(houdini.committed_levels().is_empty());
            let mut certificates = Vec::new();
            collect_certificate_files(directory.path(), &mut certificates);
            assert!(
                certificates.iter().all(|path| {
                    !matches!(
                        path.file_name().and_then(|name| name.to_str()),
                        Some("Valid.lean" | "Invalid.lean")
                    )
                }),
                "failed proposal must publish no certificate"
            );
            assert!(!directory.path().join("published").exists());
        })
        .await;
        let shutdown = provider
            .shutdown(whiel_runner::proposer_api::wire::ShutdownReason::Failure)
            .await;
        cleanup
            .stop_and_join()
            .await
            .expect("failed outcome endpoint is joined");
        if let Err(panic) = result {
            std::panic::resume_unwind(panic);
        }
        shutdown.unwrap();
        assert_eq!(provider.resource_failure().is_some(), mode == "api_flood");
        assert_eq!(
            provider.terminal_failure().is_some(),
            mode == "endpoint_exit"
        );
        drop(provider);
        drop(feedback);
        solver.shutdown().await.unwrap();
        drop(solver);
        drop(admission);
        drop(artifacts);
        owner.settle().unwrap();
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn live_agent_source_cancellation_waits_for_cleanup_and_preserves_synchronization() {
    let directory = support::TestDir::new("fixed_ambient_live_agent_source_cleanup");
    let solver_admission = agent_admission(1, 1);
    let cancellation = CancellationToken::new();
    let bound = bind(worker_pool(1), 'a', None, &solver_admission, &cancellation).await;
    let (task, admission, solver, houdini) = bound.into_parts();
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let catalog = houdini.catalog().clone();
    let state = Arc::new(houdini);
    let mut feedback_state = PreCertificateAgentHoudiniState::new(
        Arc::clone(&task),
        &artifacts,
        &state,
        Duration::from_secs(30),
        AgentFeedbackPolicy::default(),
    )
    .unwrap();
    let first_feedback = feedback_state.feedback().clone();

    let control = Arc::new(CancellationCleanupControl::new());
    let policy = AgentConsultationPolicy::default();
    let recorder = recording_fixture(&task, &first_feedback, &policy);
    let mut agent = RecordingProvider::agent(
        CleanupAwareProvider {
            request_ordinal: 0,
            control: Arc::clone(&control),
        },
        policy,
        recorder.clone(),
    );
    let request_task = Arc::clone(&task);
    let request_state = Arc::clone(&state);
    let request_admission = admission.clone();
    let request_solver = solver.clone();
    let request_solver_admission = solver_admission.clone();
    let request_feedback = first_feedback.clone();
    let request_feedback_state = feedback_state.clone();
    let request_cancellation = CancellationToken::new();
    let request_token = request_cancellation.clone();
    let request = tokio::spawn(async move {
        let validator = AgentResponseValidator::new(
            &request_task,
            &request_state,
            &request_admission,
            &request_solver,
            &request_solver_admission,
            &request_feedback_state,
            None,
        );
        let outcome = agent
            .get_houdini_proposal(&request_feedback, &validator, &request_token)
            .await;
        (agent, outcome)
    });

    control.wait_for_request_start().await;
    request_cancellation.cancel();
    control.wait_for_cleanup_start().await;
    tokio::task::yield_now().await;
    assert!(!request.is_finished());
    assert!(!control.cleanup_complete.load(Ordering::SeqCst));
    control.cleanup_release.notify_one();
    let (mut agent, cancelled) = tokio::time::timeout(Duration::from_secs(10), request)
        .await
        .expect("Agent cancellation waits only for bounded source cleanup")
        .unwrap();
    assert!(
        cancelled.is_err(),
        "source cancellation remains out of band"
    );
    assert!(control.cleanup_complete.load(Ordering::SeqCst));
    assert_eq!(agent.attempt_history().len(), 1);
    assert_eq!(
        agent.attempt_history()[0].outcome(),
        AgentRequestAttemptOutcome::Cancelled
    );
    assert!(agent.attempt_history()[0].response_digest().is_none());

    let latest = AgentSearchFeedback::postcondition_open_inconclusive(
        &state,
        FrameworkIIInconclusiveReason::Cancelled,
    )
    .expect("an epoch's termination outcome binds to the exact state");
    let second_feedback = feedback_state
        .build_next_feedback(&state, &latest, Duration::from_secs(20))
        .unwrap()
        .clone();
    assert_ne!(
        first_feedback.consultation_digest(),
        second_feedback.consultation_digest()
    );
    let validator = AgentResponseValidator::new(
        &task,
        &state,
        &admission,
        &solver,
        &solver_admission,
        &feedback_state,
        None,
    );
    let proposal = agent
        .get_houdini_proposal(&second_feedback, &validator, &CancellationToken::new())
        .await
        .expect("the synchronized source remains usable");
    let HoudiniProposal::CandidateClauses(epoch) = proposal else {
        panic!("the live clause response did not produce an admitted epoch: {proposal:?}")
    };
    assert_eq!(epoch.clauses().len(), 1);
    assert_eq!(agent.attempt_history().len(), 2);
    assert_eq!(
        agent.attempt_history()[1].outcome(),
        AgentRequestAttemptOutcome::Accepted
    );
    assert_ne!(
        agent.attempt_history()[0].consultation_digest(),
        agent.attempt_history()[1].consultation_digest()
    );
    assert_ne!(
        agent.attempt_history()[0].request_digest(),
        agent.attempt_history()[1].request_digest()
    );
    {
        let observed = control.observed.lock().unwrap();
        assert_eq!(observed.len(), 2);
        assert_eq!(observed[0].validation_ordinal, 0);
        assert_eq!(observed[1].validation_ordinal, 0);
    }
    assert_eq!(state.proposal_revision(), 0);
    assert_eq!(catalog.len().unwrap(), 0);

    let recording = verify_recording(&recorder, &artifacts, &control.observed);
    assert!(recording.events().iter().any(|event| matches!(event, TranscriptEvent::Lifecycle { event: TranscriptLifecycle::RequestCancelled, coordinates } if coordinates.consultation == 0)));
    let joins = recording
        .events()
        .iter()
        .filter(|event| {
            matches!(
                event,
                TranscriptEvent::Lifecycle {
                    event: TranscriptLifecycle::CleanupJoined,
                    ..
                }
            )
        })
        .count();
    assert_eq!(joins, 2);
    drop(epoch);
    drop(agent);
    drop(feedback_state);
    drop(state);
    solver.shutdown().await.unwrap();
    drop(solver);
    drop(admission);
    drop(artifacts);
    owner.settle().unwrap();
}

// ------------------------------------------------------------
// Pre-Certificate Search
// ------------------------------------------------------------

/// Search budget the canaries give the real pinned Vampire.
///
/// The fake solver answers instantly; the real one has to prove the
/// fixture's own verification conditions, and the deterministic tests'
/// five-second baseline is not a claim about how long that takes.
const REAL_SOLVER_SEARCH_BUDGET: Duration = Duration::from_secs(60);

/// One `SearchFixture` taken apart for [`settle_search_outcome`].
struct SettlementParts {
    directory: support::TestDir,
    task: Arc<SynthesisTask>,
    admission: FrameworkIIAdmissionContext,
    solver_admission: SolverAdmission,
    resources: SettlementResources,
}

struct SearchFixture {
    directory: support::TestDir,
    task: Arc<SynthesisTask>,
    admission: FrameworkIIAdmissionContext,
    solver: FrameworkIISolverContext,
    houdini: Option<LeveledHoudiniState>,
    solver_admission: SolverAdmission,
    artifacts: ArtifactStore,
    owner: whiel_runner::ArtifactBackendOwner,
}

impl SearchFixture {
    async fn new(label: &str, digit: char, pool: FixedAmbientWorkerPoolConfig) -> Self {
        Self::for_task(label, PRODUCTION_TASK_ID, digit, pool).await
    }

    async fn for_task(
        label: &str,
        canonical_id: &str,
        digit: char,
        pool: FixedAmbientWorkerPoolConfig,
    ) -> Self {
        let directory = support::TestDir::new(label);
        // Two Vampire slots: a racing check takes both at once, and a single
        // slot would make the race run its lanes in turn — a different search
        // from the one a campaign runs.
        let solver_admission = agent_admission(2, 1);
        let bound = bind_task(
            canonical_id,
            pool,
            digit,
            None,
            &solver_admission,
            &CancellationToken::new(),
        )
        .await;
        let (task, admission, solver, houdini) = bound.into_parts();
        let (owner, artifacts) =
            new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
        Self {
            directory,
            task,
            admission,
            solver,
            houdini: Some(houdini),
            solver_admission,
            artifacts,
            owner,
        }
    }

    fn runtime(
        &self,
        fixture: &str,
        cancellation: &CancellationToken,
    ) -> PreCertificateAgentHoudiniRuntime<
        whiel_runner::FrameworkIIProductionChecker<FrameworkIISolverContext>,
    > {
        let command = VampireWorkerCommand::new(support::fake_vampire())
            .with_extra_args([OsString::from("--fixture"), OsString::from(fixture)])
            .unwrap();
        let checker = self
            .solver
            .clone()
            .production_checker(proof_only_production_config(
                &self.artifacts,
                &self.solver_admission,
                command,
                cancellation,
            ));
        PreCertificateAgentHoudiniRuntime::new(
            self.admission.clone(),
            self.solver.clone(),
            self.solver_admission.clone(),
            checker,
            self.artifacts.clone(),
            cancellation.clone(),
            AgentToolPolicy::default(),
        )
    }

    /// The run's checker over the **real pinned Vampire**, with a search
    /// budget large enough for it to close the fixture's own conditions.
    ///
    /// Pass 7.5g review, finding 4: `runtime` above stands a fake solver in
    /// for the whole checker, which is right for the tests whose subject is
    /// the search's control flow, and wrong for a canary whose claim is
    /// that leveled Houdini reached a *proved* termination check. The fake
    /// provider is the LLM side; the solver has to be real.
    ///
    /// Both lanes race, because a campaign races both: a canary that stands
    /// for the production path and searched only the proof lane would be
    /// gating a search nothing runs.
    fn real_solver_runtime(
        &self,
        pinned: &PinnedLeancheckVampire,
        cancellation: &CancellationToken,
    ) -> PreCertificateAgentHoudiniRuntime<
        whiel_runner::FrameworkIIProductionChecker<FrameworkIISolverContext>,
    > {
        let config = FrameworkIIProductionCheckConfig::new(
            self.artifacts.clone(),
            self.solver_admission.clone(),
            VampireSearchBudget::finite(REAL_SOLVER_SEARCH_BUDGET),
            FmbOptions::default(),
            VampireWorkerCommand::new(pinned.path()),
            cancellation.clone(),
            "pinned-leancheck-vampire",
            certification_profiles(),
        )
        .unwrap();
        let checker = self.solver.clone().production_checker(config);
        PreCertificateAgentHoudiniRuntime::new(
            self.admission.clone(),
            self.solver.clone(),
            self.solver_admission.clone(),
            checker,
            self.artifacts.clone(),
            cancellation.clone(),
            AgentToolPolicy::default(),
        )
    }

    /// Take the fixture apart into what a settlement needs: the run-owned
    /// authorities `settle_search_outcome` consumes, the two it only
    /// borrows, and the scratch directory the caller keeps alive across the
    /// call.
    fn into_settlement_parts(self) -> SettlementParts {
        let Self {
            directory,
            task,
            admission,
            solver,
            houdini,
            solver_admission,
            artifacts,
            owner,
        } = self;
        drop(houdini);
        drop(artifacts);
        SettlementParts {
            directory,
            task,
            admission,
            solver_admission: solver_admission.clone(),
            resources: SettlementResources {
                solver,
                artifacts: owner,
            },
        }
    }

    async fn settle(self) {
        let Self {
            directory,
            task,
            admission,
            solver,
            houdini,
            solver_admission,
            artifacts,
            owner,
        } = self;
        drop(houdini);
        solver.shutdown().await.unwrap();
        drop(solver);
        drop(admission);
        drop(solver_admission);
        drop(task);
        drop(artifacts);
        owner.settle().unwrap();
        drop(directory);
    }
}

struct LifecycleProbeProvider {
    terminal: Option<whiel_runner::proposer_api::ProposerTerminalFailure>,
    fail_request: bool,
    panic_request: bool,
    fail_shutdown: bool,
    events: Arc<Mutex<Vec<&'static str>>>,
    observed_budget: Arc<Mutex<Option<Option<u64>>>>,
}

impl AgentProvider for LifecycleProbeProvider {
    fn terminal_failure(&self) -> Option<whiel_runner::proposer_api::ProposerTerminalFailure> {
        self.terminal
    }
    fn consult<'a>(
        &'a mut self,
        push: &'a AgentPush,
        _queries: &'a dyn AgentToolSurface,
        response: &'a mut AgentResponseWriter,
        _cancellation: AgentSourceCancellation,
    ) -> AgentSourceFuture<'a> {
        Box::pin(async move {
            self.events.lock().unwrap().push("request");
            assert!(!self.panic_request, "intentional proposer polling panic");
            *self.observed_budget.lock().unwrap() =
                Some(push.remaining_request_budget_ns().unwrap());
            response
                .write_chunk(&clause_response(push, &[LEVEL_ZERO_CLAUSE]))
                .unwrap();
            AgentSourceOutcome::Response
        })
    }
    fn quiesce_request(&mut self) -> whiel_runner::proposer_api::ProposerCleanupFuture<'_> {
        Box::pin(async move {
            self.events.lock().unwrap().push("quiesce");
            if self.fail_request {
                Err(whiel_runner::proposer_api::ProposerCleanupError::Failed)
            } else {
                Ok(())
            }
        })
    }
    fn shutdown(
        &mut self,
        reason: whiel_runner::proposer_api::wire::ShutdownReason,
    ) -> whiel_runner::proposer_api::ProposerCleanupFuture<'_> {
        Box::pin(async move {
            self.events.lock().unwrap().push(match reason {
                whiel_runner::proposer_api::wire::ShutdownReason::Complete => "shutdown_complete",
                whiel_runner::proposer_api::wire::ShutdownReason::Failure => "shutdown_failure",
                whiel_runner::proposer_api::wire::ShutdownReason::Cancelled => "shutdown_cancelled",
            });
            if self.fail_shutdown {
                Err(whiel_runner::proposer_api::ProposerCleanupError::TimedOut)
            } else {
                Ok(())
            }
        })
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn live_proposer_cleanup_errors_block_success_and_deadline_is_controller_owned() {
    for (fail_request, fail_shutdown, local_limit) in [
        (false, false, None),
        (false, false, Some(Duration::from_secs(10))),
        (true, false, None),
        (false, true, None),
    ] {
        let mut fixture = SearchFixture::new("proposer_lifecycle", 'a', worker_pool(1)).await;
        let cancellation = CancellationToken::new();
        let runtime = fixture.runtime("proof", &cancellation);
        let events = Arc::new(Mutex::new(Vec::new()));
        let observed_budget = Arc::new(Mutex::new(None));
        let agent = Agent::with_default_policy(LifecycleProbeProvider {
            terminal: None,
            fail_request,
            panic_request: false,
            fail_shutdown,
            events: Arc::clone(&events),
            observed_budget: Arc::clone(&observed_budget),
        });
        let overall = Duration::from_secs(20);
        let search = PreCertificateAgentHoudiniSearch::new(
            Arc::clone(&fixture.task),
            agent,
            fixture.houdini.take().unwrap(),
            runtime,
            PreCertificateAgentHoudiniLimits::new(overall, local_limit, Some(4)),
            tokio::time::Instant::now() + overall,
            AgentFeedbackPolicy::default(),
        )
        .unwrap();
        let outcome = search.run().await;
        if fail_request || fail_shutdown {
            let PreCertificateAgentHoudiniOutcome::Failure(report) = &outcome else {
                panic!("cleanup failure must block a valid handoff: {outcome:?}");
            };
            assert_eq!(report.kind(), FailureKind::InfrastructureFailure);
            assert_eq!(report.scope(), FailureScope::RunGlobal);
            assert!(!report.retryable());
            assert_eq!(
                report.detail(),
                Some(if fail_request {
                    "proposer cleanup failed"
                } else {
                    "proposer cleanup timed out"
                })
            );
        } else {
            assert!(
                matches!(&outcome, PreCertificateAgentHoudiniOutcome::Valid(_)),
                "{outcome:?}"
            );
        }
        assert_eq!(
            *events.lock().unwrap(),
            vec![
                "request",
                "quiesce",
                if fail_request {
                    "shutdown_failure"
                } else {
                    "shutdown_complete"
                }
            ]
        );
        let observed = observed_budget.lock().unwrap().unwrap();
        match local_limit {
            None => assert_eq!(observed, None),
            Some(limit) => {
                assert!(observed.is_some_and(|n| n > 0 && u128::from(n) <= limit.as_nanos()))
            }
        }
        drop(outcome);
        fixture.settle().await;
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn live_proposer_polling_panic_quiesces_then_shuts_down_before_unwind() {
    let mut fixture = SearchFixture::new("proposer_panic_cleanup", 'a', worker_pool(1)).await;
    let cancellation = CancellationToken::new();
    let runtime = fixture.runtime("proof", &cancellation);
    let events = Arc::new(Mutex::new(Vec::new()));
    let agent = Agent::with_default_policy(LifecycleProbeProvider {
        terminal: None,
        fail_request: false,
        fail_shutdown: false,
        panic_request: true,
        events: Arc::clone(&events),
        observed_budget: Arc::new(Mutex::new(None)),
    });
    let search = PreCertificateAgentHoudiniSearch::new_with_joined_cleanup(
        Arc::clone(&fixture.task),
        agent,
        fixture.houdini.take().unwrap(),
        runtime,
        PreCertificateAgentHoudiniLimits::new(Duration::from_secs(20), None, Some(4)),
        tokio::time::Instant::now() + Duration::from_secs(20),
        AgentFeedbackPolicy::default(),
    )
    .await
    .unwrap();
    let error = tokio::spawn(search.run()).await.unwrap_err();
    assert!(error.is_panic());
    assert_eq!(
        *events.lock().unwrap(),
        vec!["request", "quiesce", "shutdown_failure"]
    );
    assert!(cancellation.is_cancelled());
    fixture.settle().await;
}

/// Only shutdown raises the resource fault; successful search work before it
/// cannot hide the final control packet's exhausted API allowance.
struct ShutdownResourceProvider(LifecycleProbeProvider);
impl AgentProvider for ShutdownResourceProvider {
    fn resource_failure(&self) -> Option<String> {
        self.0
            .events
            .lock()
            .unwrap()
            .iter()
            .any(|event| event.starts_with("shutdown_"))
            .then(|| "resource_exhausted: API message allowance at shutdown".to_string())
    }
    fn consult<'a>(
        &'a mut self,
        push: &'a AgentPush,
        queries: &'a dyn AgentToolSurface,
        response: &'a mut AgentResponseWriter,
        cancellation: AgentSourceCancellation,
    ) -> AgentSourceFuture<'a> {
        self.0.consult(push, queries, response, cancellation)
    }
    fn quiesce_request(&mut self) -> whiel_runner::proposer_api::ProposerCleanupFuture<'_> {
        self.0.quiesce_request()
    }
    fn shutdown(
        &mut self,
        reason: whiel_runner::proposer_api::wire::ShutdownReason,
    ) -> whiel_runner::proposer_api::ProposerCleanupFuture<'_> {
        self.0.shutdown(reason)
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn live_shutdown_resource_fault_blocks_success_but_real_cleanup_error_has_priority() {
    for fail_shutdown in [false, true] {
        let mut fixture = SearchFixture::new("shutdown_resource", 'a', worker_pool(1)).await;
        let cancellation = CancellationToken::new();
        let runtime = fixture.runtime("proof", &cancellation);
        let events = Arc::new(Mutex::new(Vec::new()));
        let agent = Agent::with_default_policy(ShutdownResourceProvider(LifecycleProbeProvider {
            terminal: None,
            fail_request: false,
            panic_request: false,
            fail_shutdown,
            events: Arc::clone(&events),
            observed_budget: Arc::new(Mutex::new(None)),
        }));
        let overall = Duration::from_secs(20);
        let search = PreCertificateAgentHoudiniSearch::new(
            Arc::clone(&fixture.task),
            agent,
            fixture.houdini.take().unwrap(),
            runtime,
            PreCertificateAgentHoudiniLimits::new(overall, None, Some(4)),
            tokio::time::Instant::now() + overall,
            AgentFeedbackPolicy::default(),
        )
        .unwrap();
        let outcome = search.run().await;
        let PreCertificateAgentHoudiniOutcome::Failure(report) = &outcome else {
            panic!("shutdown resource fault must block success: {outcome:?}");
        };
        assert_eq!(report.scope(), FailureScope::RunGlobal);
        assert!(!report.retryable());
        if fail_shutdown {
            assert_eq!(report.kind(), FailureKind::InfrastructureFailure);
            assert_eq!(report.detail(), Some("proposer cleanup timed out"));
        } else {
            assert_eq!(report.kind(), FailureKind::SourceExhausted);
            assert_eq!(
                report.detail(),
                Some("resource_exhausted: API message allowance at shutdown")
            );
        }
        assert_eq!(
            *events.lock().unwrap(),
            vec!["request", "quiesce", "shutdown_complete"]
        );
        drop(outcome);
        fixture.settle().await;
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn live_terminal_endpoint_fault_prevents_admission_and_reconsultation() {
    use whiel_runner::proposer_api::ProposerTerminalFailure;
    for terminal in [
        ProposerTerminalFailure::ProtocolViolation,
        ProposerTerminalFailure::EndpointExited,
        ProposerTerminalFailure::EndpointFailure,
    ] {
        let mut fixture = SearchFixture::new("terminal_endpoint", 'a', worker_pool(1)).await;
        let cancellation = CancellationToken::new();
        let runtime = fixture.runtime("proof", &cancellation);
        let events = Arc::new(Mutex::new(Vec::new()));
        let agent = Agent::with_default_policy(LifecycleProbeProvider {
            terminal: Some(terminal),
            fail_request: false,
            fail_shutdown: false,
            panic_request: false,
            events: Arc::clone(&events),
            observed_budget: Arc::new(Mutex::new(None)),
        });
        let search = PreCertificateAgentHoudiniSearch::new_with_joined_cleanup(
            Arc::clone(&fixture.task),
            agent,
            fixture.houdini.take().unwrap(),
            runtime,
            PreCertificateAgentHoudiniLimits::new(Duration::from_secs(20), None, Some(4)),
            tokio::time::Instant::now() + Duration::from_secs(20),
            AgentFeedbackPolicy::default(),
        )
        .await
        .unwrap();
        let outcome = search.run().await;
        let PreCertificateAgentHoudiniOutcome::Failure(report) = &outcome else {
            panic!("a terminal endpoint cannot yield a successful handoff: {outcome:?}");
        };
        assert_eq!(report.kind(), FailureKind::InfrastructureFailure);
        assert_eq!(report.scope(), FailureScope::RunGlobal);
        assert!(!report.retryable());
        assert_eq!(report.detail(), Some(terminal.to_string().as_str()));
        assert_eq!(
            *events.lock().unwrap(),
            vec!["request", "quiesce", "shutdown_failure"]
        );
        drop(outcome);
        fixture.settle().await;
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn live_started_proposer_is_joined_on_search_setup_failure() {
    for fail_shutdown in [false, true] {
        let mut fixture = SearchFixture::new("proposer_setup_cleanup", 'a', worker_pool(1)).await;
        let cancellation = CancellationToken::new();
        let runtime = fixture.runtime("proof", &cancellation);
        let events = Arc::new(Mutex::new(Vec::new()));
        let agent = Agent::with_default_policy(LifecycleProbeProvider {
            terminal: None,
            fail_request: false,
            panic_request: false,
            fail_shutdown,
            events: Arc::clone(&events),
            observed_budget: Arc::new(Mutex::new(None)),
        });
        let result = PreCertificateAgentHoudiniSearch::new_with_joined_cleanup(
            Arc::clone(&fixture.task),
            agent,
            fixture.houdini.take().unwrap(),
            runtime,
            PreCertificateAgentHoudiniLimits::new(Duration::from_secs(1), None, Some(4)),
            tokio::time::Instant::now() + Duration::from_secs(20),
            AgentFeedbackPolicy::default(),
        )
        .await;
        let Err(report) = result else {
            panic!("inconsistent run deadline must fail setup")
        };
        assert_eq!(report.kind(), FailureKind::InfrastructureFailure);
        assert_eq!(
            report.detail(),
            Some(if fail_shutdown {
                "proposer cleanup timed out"
            } else {
                "pre-certificate AgentHoudini deadline exceeds its overall limit"
            })
        );
        assert_eq!(*events.lock().unwrap(), vec!["shutdown_failure"]);
        fixture.settle().await;
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn live_pre_certificate_search_ends_valid_when_the_termination_check_proves() {
    let mut fixture = SearchFixture::new(
        "fixed_ambient_live_pre_certificate_handoff",
        'b',
        worker_pool(1),
    )
    .await;
    let cancellation = CancellationToken::new();
    let runtime = fixture.runtime("proof", &cancellation);
    let observed = Arc::new(Mutex::new(Vec::new()));
    let policy = AgentConsultationPolicy::default();
    let feedback = PreCertificateAgentHoudiniState::new(
        Arc::clone(&fixture.task),
        &fixture.artifacts,
        fixture.houdini.as_ref().unwrap(),
        Duration::from_secs(20),
        AgentFeedbackPolicy::default(),
    )
    .unwrap();
    let recorder = recording_fixture(&fixture.task, feedback.feedback(), &policy);
    drop(feedback);
    let agent = RecordingProvider::agent(
        ClauseProvider {
            clauses: vec![LEVEL_ZERO_CLAUSE],
            observed: Arc::clone(&observed),
        },
        policy,
        recorder.clone(),
    );
    let overall_limit = Duration::from_secs(20);
    let search = PreCertificateAgentHoudiniSearch::new(
        Arc::clone(&fixture.task),
        agent,
        fixture.houdini.take().unwrap(),
        runtime,
        PreCertificateAgentHoudiniLimits::new(overall_limit, None, Some(4)),
        tokio::time::Instant::now() + overall_limit,
        AgentFeedbackPolicy::default(),
    )
    .unwrap();

    // Every epoch ends with the termination check; this fixture proves it,
    // so the search returns Valid with the frozen Core after one epoch.
    // There is no pre-termination handoff any more.
    let outcome = search.run().await;
    let recording = verify_recording(&recorder, &fixture.artifacts, &observed);
    assert!(recording.final_state_projection().is_some());
    let PreCertificateAgentHoudiniOutcome::Valid(handoff) = outcome else {
        panic!("the proof fixture did not end the run valid: {outcome:?}")
    };
    let inspection = handoff.inspection().unwrap();
    assert_eq!(inspection.iteration(), 1);
    assert!(inspection.core_is_current());
    assert_eq!(inspection.termination_attempts_total(), 1);
    // Exactly the one proposed clause; the input reserves no system row.
    assert_eq!(inspection.catalog_len(), 1);
    assert_eq!(inspection.core().snapshot().canonical_order().len(), 1);
    assert_eq!(inspection.attempt_history().len(), 1);
    assert_eq!(
        inspection.attempt_history()[0].outcome(),
        AgentRequestAttemptOutcome::Accepted
    );
    assert_eq!(
        inspection.runtime().task_identity(),
        fixture.task.identity()
    );
    assert_eq!(
        inspection.runtime().encoding_context_id(),
        fixture.solver.encoding().context_id()
    );
    assert_eq!(
        inspection.runtime().artifact_backend_id(),
        fixture.artifacts.backend_id()
    );
    assert!(inspection.runtime().checker_matches_runtime());
    assert!(!inspection.runtime().cancellation_requested());
    assert!(!inspection.runtime().artifact_diagnostics().settled);
    {
        let observed = observed.lock().unwrap();
        assert_eq!(observed.len(), 1);
        let request: Value = serde_json::from_slice(&observed[0].bytes).unwrap();
        assert_eq!(request["feedback"]["iteration"], 1);
        assert_fixed_ambient_agent_request(&request);
    }
    drop(inspection);
    drop(handoff);
    fixture.settle().await;
}

/// Pass 7.5f, live: a proved termination check — and nothing else —
/// freezes the run's final Core, once. The frozen record is the Core's
/// clauses in canonical level order with their Lean-issued identities and
/// canonical sources, the task and scope identities, and one closed
/// profile label per job, read from the run's search provenance. A second
/// freeze is refused rather than producing a second record.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn live_a_proved_termination_check_freezes_the_final_core_exactly_once() {
    let mut fixture =
        SearchFixture::new("fixed_ambient_live_freeze_core", 'f', worker_pool(1)).await;
    let cancellation = CancellationToken::new();
    let runtime = fixture.runtime("proof", &cancellation);
    let observed = Arc::new(Mutex::new(Vec::new()));
    let agent = Agent::with_default_policy(ClauseProvider {
        clauses: vec![LEVEL_ZERO_CLAUSE],
        observed: Arc::clone(&observed),
    });
    let overall_limit = Duration::from_secs(20);
    let search = PreCertificateAgentHoudiniSearch::new(
        Arc::clone(&fixture.task),
        agent,
        fixture.houdini.take().unwrap(),
        runtime,
        PreCertificateAgentHoudiniLimits::new(overall_limit, None, Some(4)),
        tokio::time::Instant::now() + overall_limit,
        AgentFeedbackPolicy::default(),
    )
    .unwrap();

    let outcome = search.run().await;
    let PreCertificateAgentHoudiniOutcome::Valid(mut handoff) = outcome else {
        panic!("the proof fixture did not end the run valid: {outcome:?}")
    };
    let core_digest = handoff
        .inspection()
        .unwrap()
        .core()
        .core_digest()
        .to_string();
    let frozen = handoff
        .freeze_core()
        .expect("a proved termination check freezes its own Core");

    assert_eq!(frozen.core_size(), 1);
    // Exactly 2N+1 conditions: one initialization, one step, one
    // termination.
    assert_eq!(frozen.condition_count(), 3);
    assert_eq!(frozen.core_digest(), core_digest);
    assert_eq!(
        frozen.task_canonical_id(),
        fixture.task.identity().canonical_id()
    );
    assert_eq!(frozen.rows()[0].level(), 0);
    assert!(!frozen.rows()[0].canonical_source().is_empty());
    assert_eq!(frozen.rows()[0].identity_sha256().len(), 64);
    // The fake Vampire proves under the direct schedule, so every launched
    // condition's own winner — and the run's configured profile, for any
    // condition it closed without a launch — is `direct`.
    assert_eq!(
        frozen.rows()[0].initialization_profile(),
        ProofSearchProfile::Direct
    );
    assert_eq!(frozen.rows()[0].step_profile(), ProofSearchProfile::Direct);
    assert_eq!(frozen.termination_profile(), ProofSearchProfile::Direct);
    // The record round-trips through its own canonical payload, and the
    // payload carries no attempt id, ledger row, or runtime receipt.
    let decoded = FrozenLeveledCore::from_payload(&frozen.payload()).unwrap();
    assert_eq!(decoded, frozen);
    let payload = frozen.payload();
    let members = payload
        .as_object()
        .unwrap()
        .keys()
        .cloned()
        .collect::<Vec<_>>();
    for forbidden in ["attempt", "attempt_id", "receipt", "ledger", "library"] {
        assert!(
            !members.iter().any(|member| member.contains(forbidden)),
            "the frozen record must not carry {forbidden}: {members:?}"
        );
    }

    // Freeze-once.
    assert_eq!(handoff.freeze_core(), Err(CoreFreezeError::AlreadyFrozen));

    drop(handoff);
    fixture.settle().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn live_consultation_tool_call_is_stamped_with_the_pushs_state_revision() {
    let mut fixture = SearchFixture::new(
        "fixed_ambient_live_pre_certificate_tool_probe",
        '7',
        worker_pool(1),
    )
    .await;
    let cancellation = CancellationToken::new();
    let runtime = fixture.runtime("proof", &cancellation);
    let observed = Arc::new(Mutex::new(Vec::new()));
    let tool_responses = Arc::new(Mutex::new(Vec::new()));
    let record_policy = AgentConsultationPolicy::default();
    let record_feedback = PreCertificateAgentHoudiniState::new(
        Arc::clone(&fixture.task),
        &fixture.artifacts,
        fixture.houdini.as_ref().unwrap(),
        Duration::from_secs(30),
        AgentFeedbackPolicy::default(),
    )
    .unwrap();
    let recorder = recording_fixture(&fixture.task, record_feedback.feedback(), &record_policy);
    drop(record_feedback);
    let agent = RecordingProvider::agent(
        ToolProbeProvider {
            clauses: vec![LEVEL_ZERO_CLAUSE],
            observed: Arc::clone(&observed),
            tool_responses: Arc::clone(&tool_responses),
        },
        record_policy,
        recorder.clone(),
    );
    let overall_limit = Duration::from_secs(20);
    let search = PreCertificateAgentHoudiniSearch::new(
        Arc::clone(&fixture.task),
        agent,
        fixture.houdini.take().unwrap(),
        runtime,
        PreCertificateAgentHoudiniLimits::new(overall_limit, None, Some(4)),
        tokio::time::Instant::now() + overall_limit,
        AgentFeedbackPolicy::default(),
    )
    .unwrap();

    let outcome = search.run().await;
    assert!(
        matches!(&outcome, PreCertificateAgentHoudiniOutcome::Valid(_)),
        "{outcome:?}"
    );

    let pushed_revision = {
        let observed = observed.lock().unwrap();
        assert_eq!(observed.len(), 1);
        let request: Value = serde_json::from_slice(&observed[0].bytes).unwrap();
        request["feedback"]["state_revision"].clone()
    };

    {
        let tool_responses = tool_responses.lock().unwrap();
        assert_eq!(tool_responses.len(), 2);
        // The probed attempt never refuted anything in this run, so the real
        // `countermodel` body reports `no_refutation`; the response is still
        // stamped with the exact state revision the answered push carried.
        assert_eq!(tool_responses[0]["tool"], json!("countermodel"));
        assert_eq!(tool_responses[0]["error"]["code"], json!("no_refutation"));
        assert_eq!(tool_responses[0]["state_revision"], pushed_revision);
        // Skills no longer traverse the B dispatcher, even when the run allows all queries.
        assert_eq!(tool_responses[1]["tool"], "get_skill");
        assert_eq!(tool_responses[1]["error"]["code"], "unknown_tool");
        assert_eq!(tool_responses[1]["state_revision"], pushed_revision);
    }

    let recording = verify_recording(&recorder, &fixture.artifacts, &observed);
    let calls: Vec<_> = recording
        .events()
        .iter()
        .filter_map(|event| match event {
            TranscriptEvent::ToolCall { call_id, .. } => Some(*call_id),
            _ => None,
        })
        .collect();
    let responses: Vec<_> = recording
        .events()
        .iter()
        .filter_map(|event| match event {
            TranscriptEvent::ToolResponse { call_id, .. } => Some(*call_id),
            _ => None,
        })
        .collect();
    assert!(!calls.is_empty());
    assert_eq!(calls, responses);
    fixture.settle().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn live_pre_certificate_search_recovers_from_lane_local_checker_failure() {
    let directory = support::TestDir::new("fixed_ambient_checker_recovery_proxy");
    let (pool, marker) = fault_pool(&directory, "fail_after_prepare");
    let mut fixture = SearchFixture::new(
        "fixed_ambient_live_pre_certificate_checker_recovery",
        'c',
        pool,
    )
    .await;
    let cancellation = CancellationToken::new();
    let runtime = fixture.runtime("proof", &cancellation);
    let observed = Arc::new(Mutex::new(Vec::new()));
    let agent = Agent::with_default_policy(SearchFailureProvider::new(
        SearchFailureProviderMode::UnresolvedClauses,
        Arc::clone(&observed),
    ));
    let overall_limit = Duration::from_secs(20);
    let search = PreCertificateAgentHoudiniSearch::new(
        Arc::clone(&fixture.task),
        agent,
        fixture.houdini.take().unwrap(),
        runtime,
        PreCertificateAgentHoudiniLimits::new(overall_limit, None, Some(3)),
        tokio::time::Instant::now() + overall_limit,
        AgentFeedbackPolicy::default(),
    )
    .unwrap();

    let outcome = search.run().await;
    let PreCertificateAgentHoudiniOutcome::Valid(handoff) = outcome else {
        panic!(
            "the replacement encoding worker did not stabilize the preserved proposal: {outcome:?}"
        )
    };
    let inspection = handoff.inspection().unwrap();
    assert!(marker.exists());
    assert_eq!(inspection.iteration(), 2);
    assert_eq!(inspection.attempt_history().len(), 2);
    assert!(
        inspection
            .attempt_history()
            .iter()
            .all(|attempt| attempt.outcome() == AgentRequestAttemptOutcome::Accepted)
    );
    // Only the preserved proposal; the input reserves no system row.
    assert_eq!(inspection.catalog_len(), 1);
    drop(inspection);
    drop(handoff);

    {
        let observed = observed.lock().unwrap();
        assert_eq!(observed.len(), 2);
        let first: Value = serde_json::from_slice(&observed[0].bytes).unwrap();
        let recovery: Value = serde_json::from_slice(&observed[1].bytes).unwrap();
        assert_eq!(first["feedback"]["iteration"], 1);
        assert_eq!(recovery["feedback"]["iteration"], 2);
        assert_eq!(recovery["feedback"]["latest"]["kind"], "failure");
        assert_eq!(
            recovery["feedback"]["latest"]["failure"]["origin"],
            "encoding_preparation"
        );
        assert_eq!(
            recovery["feedback"]["latest"]["failure"]["kind"],
            "process_failure"
        );
        assert_eq!(
            recovery["feedback"]["latest"]["failure"]["scope"],
            "lane_local"
        );
        // Only the preserved proposal is tracked, and it is pending because
        // the failed installation published no staged placement: it never
        // enters the push's Core (Pass 7.5c never carries the deprecated
        // `summary` key at all).
        assert!(recovery["feedback"].get("summary").is_none());
        assert_eq!(recovery["feedback"]["core"], json!([]));
        assert!(
            recovery["feedback"]["state_revision"].as_u64().unwrap()
                > first["feedback"]["state_revision"].as_u64().unwrap()
        );
        assert_ne!(
            first["binding"]["state_snapshot_digest"],
            recovery["binding"]["state_snapshot_digest"]
        );
    }

    fixture.settle().await;
    drop(directory);
}

type LiveSearchLatestExpectation = (
    usize,
    &'static str,
    Option<(&'static str, &'static str, &'static str)>,
);

struct LiveSearchFailureCase {
    label: &'static str,
    mode: SearchFailureProviderMode,
    overall_limit: Duration,
    consultation_limit: Option<Duration>,
    iteration_limit: Option<u64>,
    expected_final_kind: FailureKind,
    expected_iterations: Vec<u64>,
    expected_validation_ordinals: Vec<usize>,
    latest_request: Option<LiveSearchLatestExpectation>,
    expect_run_cancellation: bool,
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn live_pre_certificate_search_failure_matrix_preserves_loop_accounting_and_cleanup() {
    let fixture = SearchFixture::new(
        "fixed_ambient_live_pre_certificate_failure_matrix",
        'd',
        worker_pool(1),
    )
    .await;
    let scope = fixture.admission.scope().clone();
    let local_cleaned = Arc::new(AtomicBool::new(false));
    let overall_cleaned = Arc::new(AtomicBool::new(false));
    let cases = vec![
        LiveSearchFailureCase {
            label: "source-exhausted",
            mode: SearchFailureProviderMode::SourceExhausted,
            overall_limit: Duration::from_secs(5),
            consultation_limit: None,
            iteration_limit: Some(2),
            expected_final_kind: FailureKind::IterationLimitExhausted,
            expected_iterations: vec![1, 2],
            expected_validation_ordinals: vec![0, 0],
            latest_request: Some((
                1,
                "failure",
                Some(("agent_consultation", "source_exhausted", "lane_local")),
            )),
            expect_run_cancellation: false,
        },
        // Corrections are unlimited within a consultation: four invalid
        // responses are corrected four times, and the fifth is accepted, all
        // inside iteration 1.
        LiveSearchFailureCase {
            label: "four-corrections",
            mode: SearchFailureProviderMode::InvalidThenValid {
                invalid: 4,
                sent: Arc::new(AtomicUsize::new(0)),
            },
            overall_limit: Duration::from_secs(20),
            consultation_limit: None,
            iteration_limit: Some(1),
            expected_final_kind: FailureKind::IterationLimitExhausted,
            expected_iterations: vec![1, 1, 1, 1, 1],
            expected_validation_ordinals: vec![0, 1, 2, 3, 4],
            latest_request: Some((4, "initial", None)),
            expect_run_cancellation: false,
        },
        LiveSearchFailureCase {
            label: "no-response",
            mode: SearchFailureProviderMode::NoResponse,
            overall_limit: Duration::from_secs(5),
            consultation_limit: None,
            iteration_limit: Some(2),
            expected_final_kind: FailureKind::IterationLimitExhausted,
            expected_iterations: vec![1, 2],
            expected_validation_ordinals: vec![0, 0],
            latest_request: Some((
                1,
                "failure",
                Some(("agent_consultation", "no_response", "lane_local")),
            )),
            expect_run_cancellation: false,
        },
        LiveSearchFailureCase {
            label: "transport-failure",
            mode: SearchFailureProviderMode::TransportFailure,
            overall_limit: Duration::from_secs(5),
            consultation_limit: None,
            iteration_limit: Some(2),
            expected_final_kind: FailureKind::IterationLimitExhausted,
            expected_iterations: vec![1, 2],
            expected_validation_ordinals: vec![0, 0],
            latest_request: Some((
                1,
                "failure",
                Some(("agent_consultation", "transport_failure", "lane_local")),
            )),
            expect_run_cancellation: false,
        },
        LiveSearchFailureCase {
            label: "zero-iteration",
            mode: SearchFailureProviderMode::SourceExhausted,
            overall_limit: Duration::from_secs(5),
            consultation_limit: None,
            iteration_limit: Some(0),
            expected_final_kind: FailureKind::IterationLimitExhausted,
            expected_iterations: Vec::new(),
            expected_validation_ordinals: Vec::new(),
            latest_request: None,
            expect_run_cancellation: false,
        },
        LiveSearchFailureCase {
            label: "zero-overall-time",
            mode: SearchFailureProviderMode::SourceExhausted,
            overall_limit: Duration::ZERO,
            consultation_limit: None,
            iteration_limit: Some(2),
            expected_final_kind: FailureKind::OverallTimeout,
            expected_iterations: Vec::new(),
            expected_validation_ordinals: Vec::new(),
            latest_request: None,
            expect_run_cancellation: true,
        },
        LiveSearchFailureCase {
            label: "local-timeout",
            mode: SearchFailureProviderMode::Stall(Arc::clone(&local_cleaned)),
            overall_limit: Duration::from_secs(2),
            consultation_limit: Some(Duration::from_millis(10)),
            iteration_limit: Some(2),
            expected_final_kind: FailureKind::IterationLimitExhausted,
            expected_iterations: vec![1, 2],
            expected_validation_ordinals: vec![0, 0],
            latest_request: Some((
                1,
                "failure",
                Some(("agent_consultation", "consultation_timeout", "lane_local")),
            )),
            expect_run_cancellation: false,
        },
        LiveSearchFailureCase {
            label: "equal-local-overall-timeout",
            mode: SearchFailureProviderMode::Stall(Arc::clone(&overall_cleaned)),
            // Leave time for the real worker and push construction before
            // testing the stalled session's equal-limit timeout precedence.
            overall_limit: Duration::from_secs(1),
            consultation_limit: Some(Duration::from_secs(1)),
            iteration_limit: Some(2),
            expected_final_kind: FailureKind::OverallTimeout,
            expected_iterations: vec![1],
            expected_validation_ordinals: vec![0],
            latest_request: None,
            expect_run_cancellation: true,
        },
        // Every consultation submits the same clause, and every epoch ends
        // with the termination check; this fixture never decides it, so the
        // run consults until its iteration limit and each later push states
        // that the postcondition is still open.
        LiveSearchFailureCase {
            label: "iteration-exhaustion",
            mode: SearchFailureProviderMode::UnresolvedClauses,
            overall_limit: Duration::from_secs(5),
            consultation_limit: None,
            iteration_limit: Some(2),
            expected_final_kind: FailureKind::IterationLimitExhausted,
            expected_iterations: vec![1, 2],
            expected_validation_ordinals: vec![0, 0],
            latest_request: Some((1, "postcondition_open", None)),
            expect_run_cancellation: false,
        },
    ];

    for (case_ordinal, case) in cases.into_iter().enumerate() {
        let cancellation = CancellationToken::new();
        let catalog = whiel_runner::LeveledClauseCatalog::new(
            scope.clone(),
            format!("{:064x}", case_ordinal + 1),
        )
        .unwrap();
        let houdini = LeveledHoudiniState::new(catalog).unwrap();
        let runtime = fixture.runtime("unknown", &cancellation);
        let observed = Arc::new(Mutex::new(Vec::new()));
        let zero_budget_lifecycle = matches!(case.label, "zero-iteration" | "zero-overall-time")
            .then(|| Arc::new(SearchProviderLifecycle::default()));
        let mut provider = SearchFailureProvider::new(case.mode, Arc::clone(&observed));
        if let Some(lifecycle) = &zero_budget_lifecycle {
            provider = provider.with_lifecycle(Arc::clone(lifecycle));
        }
        let agent = Agent::with_default_policy(provider);
        let absolute_deadline = tokio::time::Instant::now() + case.overall_limit;
        let search = PreCertificateAgentHoudiniSearch::new(
            Arc::clone(&fixture.task),
            agent,
            houdini,
            runtime,
            PreCertificateAgentHoudiniLimits::new(
                case.overall_limit,
                case.consultation_limit,
                case.iteration_limit,
            ),
            absolute_deadline,
            AgentFeedbackPolicy::default(),
        )
        .unwrap();

        let outcome = search.run().await;
        let PreCertificateAgentHoudiniOutcome::Failure(report) = outcome else {
            panic!("failure-matrix case {} returned {outcome:?}", case.label)
        };
        assert_eq!(
            report.kind(),
            case.expected_final_kind,
            "{} {report:?}",
            case.label
        );
        assert_eq!(report.origin(), FailureOrigin::RunControl, "{}", case.label);
        assert_eq!(report.scope(), FailureScope::RunGlobal, "{}", case.label);
        assert!(!report.retryable(), "{}", case.label);
        assert_eq!(
            cancellation.is_cancelled(),
            case.expect_run_cancellation,
            "{}",
            case.label
        );
        if let Some(lifecycle) = zero_budget_lifecycle {
            assert_eq!(
                lifecycle.idle_calls.load(Ordering::SeqCst),
                1,
                "{}",
                case.label
            );
            assert!(lifecycle.dropped.load(Ordering::SeqCst), "{}", case.label);
            assert!(
                lifecycle.dropped_after_idle.load(Ordering::SeqCst),
                "{}",
                case.label
            );
        }

        let observed = observed.lock().unwrap();
        let request_values = observed
            .iter()
            .map(|request| serde_json::from_slice::<Value>(&request.bytes).unwrap())
            .collect::<Vec<_>>();
        assert_eq!(
            request_values
                .iter()
                .map(|request| request["feedback"]["iteration"].as_u64().unwrap())
                .collect::<Vec<_>>(),
            case.expected_iterations,
            "{}",
            case.label
        );
        assert_eq!(
            observed
                .iter()
                .map(|request| request.validation_ordinal)
                .collect::<Vec<_>>(),
            case.expected_validation_ordinals,
            "{}",
            case.label
        );
        if let Some((index, latest_kind, failure)) = case.latest_request {
            let latest = &request_values[index]["feedback"]["latest"];
            assert_eq!(latest["kind"], latest_kind, "{}", case.label);
            if let Some((origin, kind, scope)) = failure {
                assert_eq!(latest["failure"]["origin"], origin, "{}", case.label);
                assert_eq!(latest["failure"]["kind"], kind, "{}", case.label);
                assert_eq!(latest["failure"]["scope"], scope, "{}", case.label);
            }
        }
        if case.label == "four-corrections" {
            // The first push carries no correction; each of the next four
            // carries the rejection of the response before it, and the
            // fifth response is accepted.
            assert!(request_values[0]["correction"].is_null());
            for (ordinal, push) in request_values[1..].iter().enumerate() {
                assert_eq!(
                    push["correction"]["binding"]["correction_ordinal"],
                    ordinal + 1
                );
                assert_eq!(
                    push["correction"]["diagnostics"][0]["code"],
                    "wrong_response_binding",
                );
            }
        }
    }

    assert!(local_cleaned.load(Ordering::SeqCst));
    assert!(overall_cleaned.load(Ordering::SeqCst));
    fixture.settle().await;
}

/// Milestone 7.5 review, finding 7. The push-size bound is a memory guard on
/// the document the *host* builds, so exceeding it is a run-global resource
/// fault that ends the run. Published to the proposer as a lane-local
/// consultation failure instead, the search would hold the next
/// consultation, build the same push from the same state, and re-enter the
/// same failure until the run deadline — a livelock.
///
/// The run here declares no consultation bound at all, so nothing but the
/// fault itself can stop it: before the fix this test ran until its overall
/// deadline and failed with `OverallTimeout`.
///
/// API 3.1.0 made the push far smaller by dropping the verifier's tutorial
/// prose, so the fixture states the guard's subject explicitly: a pending
/// frontier whose entries carry their clause text.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn an_oversize_push_is_a_run_global_resource_fault_not_a_livelock() {
    let fixture = SearchFixture::new(
        "fixed_ambient_oversize_push_resource_fault",
        'a',
        worker_pool(1),
    )
    .await;
    let scope = fixture.admission.scope().clone();
    let cancellation = CancellationToken::new();
    let catalog = whiel_runner::LeveledClauseCatalog::new(scope, format!("{:064x}", 1)).unwrap();
    let mut houdini = LeveledHoudiniState::new(catalog).unwrap();
    // The guard cannot be set below `MINIMUM_CORRECTION_BYTES`, and the
    // standing presentation alone is well under it, so the run starts with a
    // pending frontier: each entry carries its clause's own admitted source
    // and its drop authorization, and the first push of the run is over the
    // guard before a single round has run.
    let pending = admit(
        &fixture.admission,
        &[
            LEVEL_ZERO_CLAUSE,
            SECOND_LEVEL_ZERO_CLAUSE,
            CANONICAL_LEVEL_ZERO_CLAUSE,
            CANONICAL_LEVEL_ONE_CLAUSE,
            "(op_zT ⊆ yp_zT)",
            "(op_zS ⊆ yp_zS)",
        ],
        &fixture.solver_admission,
        &cancellation,
    )
    .await;
    register_and_enqueue(&mut houdini, &pending);
    let runtime = fixture.runtime("unknown", &cancellation);
    let observed = Arc::new(Mutex::new(Vec::new()));
    let policy = AgentConsultationPolicy::new(AgentConsultationLimits {
        max_request_bytes: 4 * 1024,
        max_correction_bytes: 4 * 1024,
        ..AgentConsultationLimits::default()
    })
    .unwrap();
    let agent = Agent::new(
        SearchFailureProvider::new(
            SearchFailureProviderMode::SourceExhausted,
            Arc::clone(&observed),
        ),
        policy,
    );
    let overall_limit = Duration::from_secs(20);
    let search = PreCertificateAgentHoudiniSearch::new(
        Arc::clone(&fixture.task),
        agent,
        houdini,
        runtime,
        PreCertificateAgentHoudiniLimits::new(overall_limit, None, None),
        tokio::time::Instant::now() + overall_limit,
        AgentFeedbackPolicy::default(),
    )
    .unwrap();

    let outcome = search.run().await;
    let PreCertificateAgentHoudiniOutcome::Failure(report) = outcome else {
        panic!("an oversize push ends the run: {outcome:?}")
    };
    assert_eq!(report.kind(), FailureKind::SourceExhausted, "{report:?}");
    assert_eq!(
        report.origin(),
        FailureOrigin::AgentConsultation,
        "{report:?}"
    );
    assert_eq!(report.scope(), FailureScope::RunGlobal, "{report:?}");
    assert!(!report.retryable(), "{report:?}");
    assert!(
        report
            .detail()
            .is_some_and(|detail| detail.contains("request-size memory guard")),
        "{report:?}"
    );
    assert!(
        observed.lock().unwrap().is_empty(),
        "a push refused by the memory guard never reaches the provider"
    );
    fixture.settle().await;
}

#[derive(Clone, Copy)]
enum SearchConstructorNegative {
    RemainingExceedsOverall,
    ZeroOverallWithFutureDeadline,
    MismatchedCheckerCancellation,
    DifferentAdmissionController,
    DifferentSolverContext,
    EnabledCompressCoreOnAgentPath,
    MismatchedToolPolicy,
}

impl SearchConstructorNegative {
    fn label(self) -> &'static str {
        match self {
            Self::RemainingExceedsOverall => "remaining-exceeds-overall",
            Self::ZeroOverallWithFutureDeadline => "zero-overall-future-deadline",
            Self::MismatchedCheckerCancellation => "mismatched-checker-cancellation",
            Self::DifferentAdmissionController => "different-admission-controller",
            Self::DifferentSolverContext => "different-solver-context",
            Self::EnabledCompressCoreOnAgentPath => "enabled-compress-core-on-agent-path",
            Self::MismatchedToolPolicy => "mismatched-tool-policy",
        }
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn live_pre_certificate_search_constructor_rejects_detached_runtime_authority() {
    let fixture = SearchFixture::new(
        "fixed_ambient_live_pre_certificate_constructor_negative",
        'e',
        worker_pool(1),
    )
    .await;
    let same_policy_other_admission = agent_admission(2, 1);
    assert_eq!(
        fixture.solver_admission.policy(),
        same_policy_other_admission.policy()
    );

    for (ordinal, case) in [
        SearchConstructorNegative::RemainingExceedsOverall,
        SearchConstructorNegative::ZeroOverallWithFutureDeadline,
        SearchConstructorNegative::MismatchedCheckerCancellation,
        SearchConstructorNegative::DifferentAdmissionController,
        SearchConstructorNegative::DifferentSolverContext,
        SearchConstructorNegative::EnabledCompressCoreOnAgentPath,
        SearchConstructorNegative::MismatchedToolPolicy,
    ]
    .into_iter()
    .enumerate()
    {
        let runtime_cancellation = CancellationToken::new();
        let checker_cancellation = if matches!(
            case,
            SearchConstructorNegative::MismatchedCheckerCancellation
        ) {
            CancellationToken::new()
        } else {
            runtime_cancellation.clone()
        };
        let runtime_admission = if matches!(
            case,
            SearchConstructorNegative::DifferentAdmissionController
        ) {
            same_policy_other_admission.clone()
        } else {
            fixture.solver_admission.clone()
        };
        let command = VampireWorkerCommand::new(support::fake_vampire())
            .with_extra_args([OsString::from("--fixture"), OsString::from("proof")])
            .unwrap();
        let checker_config = proof_only_production_config(
            &fixture.artifacts,
            &runtime_admission,
            command,
            &checker_cancellation,
        );
        let checker_solver = if matches!(case, SearchConstructorNegative::DifferentSolverContext) {
            FrameworkIISolverContext::from_admission(&fixture.admission)
        } else {
            fixture.solver.clone()
        };
        let checker = checker_solver.production_checker(checker_config);
        let runtime_tool_policy = if matches!(case, SearchConstructorNegative::MismatchedToolPolicy)
        {
            AgentToolPolicy::new([AgentTool::Ledger])
        } else {
            AgentToolPolicy::default()
        };
        let runtime = PreCertificateAgentHoudiniRuntime::new(
            fixture.admission.clone(),
            fixture.solver.clone(),
            runtime_admission,
            checker,
            fixture.artifacts.clone(),
            runtime_cancellation.clone(),
            runtime_tool_policy.clone(),
        );
        let catalog = whiel_runner::LeveledClauseCatalog::new(
            fixture.admission.scope().clone(),
            format!("{:064x}", ordinal + 20),
        )
        .unwrap();
        // The houdini side always carries the AgentHoudini default
        // (`compress_core: false`); only `EnabledCompressCoreOnAgentPath`
        // supplies a disagreeing side.
        let houdini_compress_core = matches!(
            case,
            SearchConstructorNegative::EnabledCompressCoreOnAgentPath
        );
        let houdini = LeveledHoudiniState::new_with_options(
            catalog,
            None,
            houdini_compress_core,
            BTreeSet::new(),
            BTreeSet::new(),
            AgentToolPolicy::default(),
        )
        .unwrap();
        let observed = Arc::new(Mutex::new(Vec::new()));
        let agent = Agent::with_default_policy(SearchFailureProvider::new(
            SearchFailureProviderMode::SourceExhausted,
            Arc::clone(&observed),
        ));
        let (overall_limit, deadline) = match case {
            SearchConstructorNegative::RemainingExceedsOverall => (
                Duration::from_secs(1),
                tokio::time::Instant::now() + Duration::from_secs(10),
            ),
            SearchConstructorNegative::ZeroOverallWithFutureDeadline => (
                Duration::ZERO,
                tokio::time::Instant::now() + Duration::from_secs(1),
            ),
            SearchConstructorNegative::MismatchedCheckerCancellation
            | SearchConstructorNegative::DifferentAdmissionController
            | SearchConstructorNegative::DifferentSolverContext
            | SearchConstructorNegative::EnabledCompressCoreOnAgentPath
            | SearchConstructorNegative::MismatchedToolPolicy => (
                Duration::from_secs(10),
                tokio::time::Instant::now() + Duration::from_secs(10),
            ),
        };
        let report = match PreCertificateAgentHoudiniSearch::new(
            Arc::clone(&fixture.task),
            agent,
            houdini,
            runtime,
            PreCertificateAgentHoudiniLimits::new(overall_limit, None, Some(1)),
            deadline,
            AgentFeedbackPolicy::default(),
        ) {
            Err(report) => report,
            Ok(_) => panic!("constructor accepted negative case {}", case.label()),
        };
        assert_eq!(
            report.origin(),
            FailureOrigin::RunControl,
            "{}",
            case.label()
        );
        assert_eq!(
            report.kind(),
            FailureKind::InfrastructureFailure,
            "{}",
            case.label()
        );
        assert_eq!(report.scope(), FailureScope::RunGlobal, "{}", case.label());
        assert!(!report.retryable(), "{}", case.label());
        assert!(observed.lock().unwrap().is_empty(), "{}", case.label());
        assert!(!runtime_cancellation.is_cancelled(), "{}", case.label());
    }

    fixture.settle().await;
}

// ------------------------------------------------------------
// Pass 7.5b: Live Semantic-Dictionary Subsumption
// ------------------------------------------------------------

/// A prophecy-free single-clause promotion fixture for the real Lean worker:
/// `direct[k]`/`fmb[k]` name the outcome of the `k`-th direct/finite-model
/// launch (`"prove"` reads the assembled query and cites every axiom it
/// declares, exactly like the checked-in `proof-citing-input-axioms` fake
/// mode; `"give-up"` answers `GaveUp`; `"model"` answers with a fixed,
/// Lean-validated one-element countermodel of `LEVEL_ZERO_CLAUSE`'s own
/// level-zero maintenance obligation in isolation, captured from a real
/// Vampire run against the real worker so leancheck accepts it). Every
/// invocation appends one line to `launch_log` regardless of mode, so its
/// line count is the exact real-launch total.
fn promoted_prophecy_free_vampire(directory: &Path, launch_log: &Path) -> VampireWorkerCommand {
    let script = directory.join("promoted-prophecy-free-vampire.py");
    let model_marker = directory.join("promoted-prophecy-free-vampire.model-used");
    fs::write(
        &script,
        r#"import fcntl
import sys
from pathlib import Path

log_path = Path(sys.argv[1])
marker_path = Path(sys.argv[2])
arguments = sys.argv[3:]
is_fmb = "--saturation_algorithm" in arguments
mode = "fmb" if is_fmb else "direct"

def real_axiom_names(tptp):
    # Every non-support axiom the generic TPTP assembler wrote
    # (`entailment::assembly::render_query`): `axiom_<index>`, never
    # `support_adom`/`support_distinct_<n>`. Distinguishes which exact
    # verification condition this call was asked to solve by its axiom
    # count alone, since every VC in this single-clause fixture has a
    # distinct count: Init_0 has 1 (`pre`), Maintenance_0 has 2
    # (`plain`, `guard`), Maintenance_1 has 3 (adds `not_theta_guard`).
    names = []
    for line in tptp.splitlines():
        marker = None
        for candidate in (", axiom,", ",axiom,"):
            if candidate in line:
                marker = candidate
                break
        if marker is None:
            continue
        prefix = line.split(marker)[0]
        paren = prefix.rfind("(")
        if paren == -1:
            continue
        name = prefix[paren + 1:].strip()
        if name.startswith("axiom_"):
            names.append(name)
    return names

def query_text():
    query_path = arguments[-1]
    try:
        with open(query_path, "r", encoding="utf-8") as handle:
            return handle.read()
    except OSError:
        return ""

def do_prove(contents):
    print("% SZS status Theorem for problem")
    print("% SZS output start Proof for problem")
    for index, name in enumerate(real_axiom_names(contents)):
        print(f"fof(fixture_cite_{index}, plain, ($false), file('problem.p', {name})).")
    print("1. $false [fixture]")
    print("% SZS output end Proof for problem")

def do_give_up():
    print("% SZS status GaveUp for problem")

def do_model():
    print("% TRYING [1]")
    print("% Finite Model Found!")
    print("% SZS status CounterSatisfiable for problem")
    print("% SZS output start FiniteModel for problem")
    print("tff('declare_$i1',type,'fmb_$i_1':$i).")
    print("tff('finite_domain_$i',axiom,")
    print("      ! [X:$i] : (")
    print("         X = 'fmb_$i_1'")
    print("      ) ).")
    for name, negate in [
        ("op_zE", False),
        ("op_zS", False),
        ("op_zT", True),
        ("yp_zS", False),
        ("yp_zT", False),
    ]:
        print()
        print(f"tff(declare_{name},type,{name}: ($i * $i) > $o).")
        sign = "~" if negate else ""
        print(f"tff(predicate_{name},axiom,")
        print(f"           {sign}{name}('fmb_$i_1','fmb_$i_1')")
        print()
        print(").")
    print("% SZS output end FiniteModel for problem")

contents = query_text()
axiom_count = len(real_axiom_names(contents))

marker_path.parent.mkdir(parents=True, exist_ok=True)
with marker_path.open("a+", encoding="utf-8") as marker:
    fcntl.flock(marker.fileno(), fcntl.LOCK_EX)
    marker.seek(0)
    model_already_used = marker.read().strip() == "used"
    step_is_model = is_fmb and axiom_count == 2 and not model_already_used
    if step_is_model:
        marker.seek(0)
        marker.truncate()
        marker.write("used")
        marker.flush()
    fcntl.flock(marker.fileno(), fcntl.LOCK_UN)

with log_path.open("a", encoding="utf-8") as log:
    log.write(f"{mode} axioms={axiom_count}\n")

if step_is_model:
    do_model()
elif is_fmb:
    # Every other finite-model call loses the race to a direct proof
    # (Init_0, Maintenance_1) or would otherwise duplicate the one
    # genuine refutation (never reached: `Init_1` must not launch at
    # all).
    do_give_up()
elif axiom_count == 2:
    # Maintenance_0's own direct call: give up so the concurrent
    # finite-model call's real countermodel is the one that decides
    # this check.
    do_give_up()
else:
    do_prove(contents)
"#,
    )
    .expect("write the promoted prophecy-free Vampire fixture");
    VampireWorkerCommand::new("python3")
        .with_extra_args([
            script.into_os_string(),
            launch_log.as_os_str().to_owned(),
            model_marker.into_os_string(),
        ])
        .expect("promoted prophecy-free Vampire fixture arguments")
}

/// Pass 7.5b deliverables 1 and 2, live: a prophecy-free clause
/// (`LEVEL_ZERO_CLAUSE`) proves its level-zero initialization, is genuinely
/// refuted at level-zero maintenance (a real, Lean-validated countermodel —
/// this is not the dead rule, since maintenance refutation always promotes),
/// and is promoted to level one. `Init_1`'s tagged premise set
/// (`{pre, not_theta_guard}`) contains `Init_0`'s cited set (`{pre}`, read
/// from the real worker's `axiom_tags` table against the real generated
/// TPTP names), so the controller must never launch it — root coverage at
/// level one is reached by proof-subsumption alone — while `Maintenance_1`
/// is a fresh, freshly launched proof that finally lets the clause commit.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn live_fixed_ambient_promoted_prophecy_free_clause_never_relaunches_initialization() {
    let directory = support::TestDir::new("fixed_ambient_promoted_prophecy_free");
    let launch_log = directory.path().join("vampire-launches.log");
    let solver_admission = agent_admission(1, 1);
    let cancellation = CancellationToken::new();
    let bound = bind(worker_pool(1), '3', None, &solver_admission, &cancellation).await;
    let (task, admission, solver, mut houdini) = bound.into_parts();
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();

    let clauses = admit(
        &admission,
        &[LEVEL_ZERO_CLAUSE],
        &solver_admission,
        &cancellation,
    )
    .await;
    assert!(!clauses[0].mentions_prophecy_relation());
    let clause_identity = clauses[0].identity_sha256().to_string();
    let clause = register_and_enqueue(&mut houdini, &clauses)[0];

    // Real-launch order: Init_0 (direct proves, fmb gives up), Maintenance_0
    // (direct gives up, fmb finds a real countermodel), [Init_1 must never
    // launch], Maintenance_1 (direct proves, fmb gives up). Each call
    // decides its own answer from its axiom count rather than launch
    // ordinal, since a race's losing branch does not always reach the
    // solver stand-in at all.
    let command = promoted_prophecy_free_vampire(directory.path(), &launch_log);
    let mut checker = solver.clone().production_checker(production_config(
        &artifacts,
        &solver_admission,
        FmbOptions::default(),
        command,
        &cancellation,
    ));

    let outcome = stabilize_leveled_houdini(&mut houdini, &mut checker)
        .await
        .unwrap();
    assert!(
        matches!(outcome, LeveledStabilizationOutcome::Stabilized(_)),
        "{outcome:?}\nrows={:#?}",
        houdini.attempts().rows()
    );
    assert_eq!(
        houdini.committed_levels().get(&clause),
        Some(&FrameworkIILevel::ONE)
    );
    assert!(houdini.dead().is_empty());
    assert!(houdini.pending_levels().is_empty());

    // Since Pass 7.5d Rust builds the `axiom_tags` table itself for every
    // preparation (and the assembly differential, on in this suite, checks
    // it against the worker's own), so a proof-subsumption hit no longer
    // depends on the worker binary carrying a table.
    assert!(checker.proof_subsumption_hits_total() >= 1);

    // Exactly three checks ever launch a real process pair (Init_0,
    // Maintenance_0, Maintenance_1); Init_1 never does.
    // A losing race branch is not always spawned far enough to log at all
    // (Init_0 and Maintenance_1 both prove immediately via `direct`, so
    // their concurrent `fmb` call routinely never reaches its own log
    // line), so the total is a loose sanity bound rather than an exact
    // count. The precise "Init_1 never launches" evidence is the count of
    // 2-axiom obligations asked: `Init_1` shares `Maintenance_0`'s exact
    // axiom count (`{pre, not_theta_guard}` vs `{plain, guard}`, both size
    // 2), so a stray `Init_1` launch would show up here as a second pair.
    let launch_log_text = fs::read_to_string(&launch_log).unwrap();
    let launches = launch_log_text.lines().count();
    assert!(
        (4..=6).contains(&launches),
        "launches: {launches}\n{launch_log_text}"
    );
    let two_axiom_launches = launch_log_text
        .lines()
        .filter(|line| line.contains("axioms=2"))
        .count();
    assert_eq!(
        two_axiom_launches, 2,
        "only Maintenance_0's direct-gives-up/fmb-model pair may ask a 2-axiom obligation; \
         a third would mean Init_1 launched\n{launch_log_text}"
    );

    let level_zero_init = houdini
        .attempts()
        .rows()
        .iter()
        .find_map(|row| {
            let LevelLedgerRow::Attempt(attempt) = row else {
                return None;
            };
            (attempt.request().clause() == clause
                && attempt.request().role() == FrameworkIICheckRole::Initialization
                && attempt.request().level() == FrameworkIILevel::ZERO)
                .then(|| attempt.clone())
        })
        .expect("Init_0 was checked");
    let FrameworkIICheckOutcome::Proved(level_zero_evidence) = level_zero_init.outcome() else {
        panic!("Init_0 must prove");
    };
    assert!(level_zero_evidence.semantic_reuse().is_none());
    let level_zero_receipt = level_zero_evidence
        .runtime_proof()
        .expect("Init_0 closes with a runtime proof receipt")
        .clone();

    let level_one_init = houdini
        .attempts()
        .rows()
        .iter()
        .find_map(|row| {
            let LevelLedgerRow::Attempt(attempt) = row else {
                return None;
            };
            (attempt.request().clause() == clause
                && attempt.request().role() == FrameworkIICheckRole::Initialization
                && attempt.request().level() == FrameworkIILevel::ONE)
                .then(|| attempt.clone())
        })
        .expect("Init_1 was checked (via the dictionary, never a launch)");
    let FrameworkIICheckOutcome::Proved(level_one_evidence) = level_one_init.outcome() else {
        panic!("Init_1 must be a Proved proof-subsumption hit");
    };
    let reuse = level_one_evidence
        .semantic_reuse()
        .expect("Init_1 is served by proof subsumption, not a fresh launch");
    assert_eq!(reuse.kind(), FrameworkIISemanticReuseKind::ProofSubsumption);
    assert_eq!(
        reuse.original_request_digest(),
        level_zero_init.request().request_digest(),
        "the reuse points back at Init_0's own attempt"
    );
    assert_eq!(
        level_one_evidence
            .runtime_proof()
            .expect("reuse carries the original runtime proof receipt through unchanged")
            .request_digest(),
        level_zero_receipt.request_digest(),
        "the reuse carries Init_0's own receipt through unchanged"
    );

    // Root coverage: Init_1's current root is the reused evidence. Since
    // Pass 7.5f the frozen job's profile label is read from the semantic
    // dictionary's proof-entry provenance for the condition, never off a
    // root, and both name the level-zero launch's own winner: the
    // condition `(Initialization, this clause)` was proved once, by that
    // launch, and the level-one request reused it.
    let root = houdini
        .current_root(clause, FrameworkIICheckRole::Initialization)
        .expect("a root exists at the committed level with reuse evidence");
    assert!(root.proof_evidence().semantic_reuse().is_some());
    assert_eq!(
        checker
            .search_profile_provenance(houdini.core().snapshot())
            .clause_profile(FrameworkIICheckRole::Initialization, &clause_identity),
        level_zero_receipt.winner(),
        "the frozen label of a dictionary-served condition is its original launch's winner"
    );

    drop(checker);
    solver.shutdown().await.unwrap();
    drop(solver);
    drop(admission);
    drop(artifacts);
    owner.settle().unwrap();
}

/// Committed clauses leave the check loop, live: once a level-zero clause
/// commits, a same-level sibling's arrival issues no check of any kind
/// against it — not a launch and not a dictionary answer — and its roots
/// stay exactly where they were. Certification re-proves the frozen Core's
/// 2N+1 conditions regardless.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn live_fixed_ambient_committed_clause_is_never_rechecked_for_a_new_sibling() {
    let directory = support::TestDir::new("fixed_ambient_proof_subsumption_sibling");
    let launch_log = directory.path().join("vampire-launches.log");
    let solver_admission = agent_admission(1, 1);
    let cancellation = CancellationToken::new();
    let bound = bind(worker_pool(1), '4', None, &solver_admission, &cancellation).await;
    let (task, admission, solver, mut houdini) = bound.into_parts();
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();

    let clauses = admit(
        &admission,
        &[LEVEL_ZERO_CLAUSE],
        &solver_admission,
        &cancellation,
    )
    .await;
    let clause_a = register_and_enqueue(&mut houdini, &clauses)[0];

    let command = VampireWorkerCommand::new(support::fake_vampire())
        .with_extra_args([
            OsString::from("--fixture"),
            OsString::from("proof-citing-input-axioms"),
            OsString::from("--launch-log"),
            launch_log.as_os_str().to_owned(),
        ])
        .unwrap();
    let mut checker = solver
        .clone()
        .production_checker(proof_only_production_config(
            &artifacts,
            &solver_admission,
            command,
            &cancellation,
        ));

    let outcome = stabilize_leveled_houdini_with_system_clauses(&mut houdini, &mut checker)
        .await
        .unwrap();
    assert!(matches!(
        outcome,
        LeveledStabilizationOutcome::Stabilized(_)
    ));
    assert_eq!(
        houdini.committed_levels().get(&clause_a),
        Some(&FrameworkIILevel::ZERO)
    );
    let launches_after_a = fs::read_to_string(&launch_log).unwrap().lines().count();
    assert_eq!(launches_after_a, 2, "Init_0(A) and Maintenance_0(A)");
    assert_eq!(checker.proof_subsumption_hits_total(), 0);

    let sibling = admit(
        &admission,
        &[SECOND_LEVEL_ZERO_CLAUSE],
        &solver_admission,
        &cancellation,
    )
    .await;
    let next_ordinal = houdini.catalog().next_batch_ordinal().unwrap();
    let registered = houdini
        .catalog()
        .register_batch(
            next_ordinal,
            sibling
                .iter()
                .cloned()
                .map(|clause| (clause, ExtendedClauseOrigin::Submitted)),
        )
        .unwrap();
    let clause_b = registered.ids()[0];
    houdini.enqueue_registered(&registered).unwrap();

    let outcome = stabilize_leveled_houdini_with_system_clauses(&mut houdini, &mut checker)
        .await
        .unwrap();
    assert!(matches!(
        outcome,
        LeveledStabilizationOutcome::Stabilized(_)
    ));
    assert_eq!(
        houdini.committed_levels().get(&clause_a),
        Some(&FrameworkIILevel::ZERO)
    );
    assert_eq!(
        houdini.committed_levels().get(&clause_b),
        Some(&FrameworkIILevel::ZERO)
    );

    let launches_after_b = fs::read_to_string(&launch_log).unwrap().lines().count();
    assert_eq!(
        launches_after_b,
        launches_after_a + 2,
        "only B's own two checks launch; A is committed and is never re-checked"
    );
    // Not one row of any kind names A after the first scan: a committed
    // clause receives no check, by dictionary or otherwise.
    let rows_naming_a_after = houdini
        .attempts()
        .rows()
        .iter()
        .filter(|row| match row {
            LevelLedgerRow::Attempt(attempt) => attempt.request().clause() == clause_a,
            LevelLedgerRow::Invalidation(_) => false,
        })
        .count();
    assert_eq!(rows_naming_a_after, 2, "only A's own first-scan two checks");
    // A publishes no replacement root either: a current root is published
    // only by a check issued against the already-published Core, and A is
    // never checked again.
    for role in ROLES {
        if let Some(root) = houdini.current_root(clause_a, role) {
            assert!(root.proof_evidence().semantic_reuse().is_none());
        }
    }

    drop(checker);
    solver.shutdown().await.unwrap();
    drop(solver);
    drop(admission);
    drop(artifacts);
    owner.settle().unwrap();
}

// ------------------------------------------------------------
// Pass 7.5c: Consultation-Session Tool Surface
// ------------------------------------------------------------

/// One live epoch end to end: a fresh clause's only check is inconclusive so
/// it ends the scan pending, the epoch's termination check on the resulting
/// Core is refuted with a real Lean-validated countermodel, the next push
/// names that attempt in its `postcondition_open` event, and the
/// `countermodel` tool serves it. The following epoch's fresh clause fails
/// too while the older clause's identical check is answered from the
/// semantic dictionary without a launch.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn live_epoch_refutes_the_termination_check_and_serves_its_countermodel() {
    retained_evaluation_sources(None).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn live_evaluation_reports_unretained_sources_without_fabricating_truth() {
    retained_evaluation_sources(Some(1)).await;
}

async fn retained_evaluation_sources(retention: Option<u64>) {
    let directory = support::TestDir::new("fixed_ambient_tool_round_veto");
    let solver_admission = agent_admission(1, 1);
    let cancellation = CancellationToken::new();
    let host_limits = HostLimits {
        countermodel_retention_tuples: retention,
        ..HostLimits::UNBOUNDED
    };
    let feedback_policy = AgentFeedbackPolicy::new(whiel_runner::framework2::AgentFeedbackLimits {
        host_limits,
        ..whiel_runner::framework2::AgentFeedbackLimits::default()
    })
    .unwrap();
    let bound = bind_fixed_ambient_framework_ii(
        fixture_descriptor(),
        worker_pool(1),
        "d".repeat(64),
        host_limits,
        false,
        AgentToolPolicy::default(),
        &solver_admission,
        &cancellation,
    )
    .await
    .unwrap();
    let (task, admission, solver, houdini) = bound.into_parts();
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let command = termination_refuting_vampire(directory.path());
    let checker = solver.clone().production_checker(
        production_config(
            &artifacts,
            &solver_admission,
            FmbOptions::default(),
            command,
            &cancellation,
        )
        .with_host_limits(host_limits),
    );
    let runtime = PreCertificateAgentHoudiniRuntime::new(
        admission.clone(),
        solver.clone(),
        solver_admission.clone(),
        checker,
        artifacts.clone(),
        cancellation.clone(),
        AgentToolPolicy::default(),
    );
    let observed = Arc::new(Mutex::new(Vec::new()));
    let tool_responses = Arc::new(Mutex::new(Vec::new()));
    let record_policy = AgentConsultationPolicy::default();
    let record_feedback = PreCertificateAgentHoudiniState::new(
        Arc::clone(&task),
        &artifacts,
        &houdini,
        Duration::from_secs(30),
        feedback_policy.clone(),
    )
    .unwrap();
    let recorder = recording_fixture(&task, record_feedback.feedback(), &record_policy);
    drop(record_feedback);
    let agent = RecordingProvider::agent(
        VetoAndToolsProvider {
            round: 0,
            observed: Arc::clone(&observed),
            tool_responses: Arc::clone(&tool_responses),
        },
        record_policy,
        recorder.clone(),
    );
    let overall_limit = Duration::from_secs(30);
    let search = PreCertificateAgentHoudiniSearch::new(
        Arc::clone(&task),
        agent,
        houdini,
        runtime,
        PreCertificateAgentHoudiniLimits::new(overall_limit, None, Some(8)),
        tokio::time::Instant::now() + overall_limit,
        feedback_policy.clone(),
    )
    .unwrap();

    let _outcome = search.run().await;

    {
        let observed = observed.lock().unwrap();
        assert!(
            observed.len() >= 3,
            "expected at least three consultation rounds, saw {}",
            observed.len()
        );
        let round2: Value = serde_json::from_slice(&observed[2].bytes).unwrap();
        let feedback = &round2["feedback"];
        assert!(feedback.get("retry").is_none());
        assert_eq!(feedback["core"], json!([]), "{round2}");
        // Only the fresh clause is pending: the older one was dropped, so
        // it is dead by drop and absent from `pending`.
        let pending = feedback["pending"].as_array().unwrap();
        assert_eq!(pending.len(), 1, "{round2}");
        // `last_round` reports the round's own submission as pending; the
        // drop target is not part of the submission.
        let last_round = feedback["last_round"].as_array().unwrap();
        assert_eq!(last_round.len(), 1, "{round2}");
        assert_eq!(
            last_round[0]["outcome"]["kind"],
            json!("pending"),
            "{round2}"
        );
        // The one pending clause is exactly the round's fresh submission,
        // which failed through level 0 and now rests at level 1; the
        // dropped clause is gone from both lists.
        assert_eq!(
            last_round[0]["clause"]["clause_id"], pending[0]["clause"]["clause_id"],
            "{round2}"
        );
        assert_eq!(pending[0]["minimum_level"], json!(0), "{round2}");
        assert_eq!(pending[0]["current_level"], json!(1), "{round2}");
        assert_eq!(
            feedback["latest"]["kind"],
            json!("postcondition_open"),
            "{round2}"
        );
    }

    {
        let responses = tool_responses.lock().unwrap();
        assert_eq!(responses.len(), 7);
        assert_eq!(responses[0]["error"]["code"], json!("unknown_tool"));

        // The termination refutation's countermodel, addressed by the
        // attempt the `postcondition_open` event named.
        let countermodel = tool_result(&responses[1]);
        if retention.is_some() {
            assert_eq!(countermodel["found_not_retained"]["value"], 1);
            assert!(
                countermodel["found_not_retained"]["tuple_count"]
                    .as_u64()
                    .unwrap()
                    > 1
            );
        } else {
            let relations = countermodel["model"]["relations"].as_array().unwrap();
            assert!(!relations.is_empty());
        }

        let history = tool_result(&responses[2]);
        assert_eq!(history["status"]["kind"], json!("pending"));
        assert_eq!(history["status"]["level"], json!(1));

        let strongest = tool_result(&responses[3]);
        assert!(strongest["refutations"].is_array());

        let ledger = tool_result(&responses[4]);
        assert!(!ledger["items"].as_array().unwrap().is_empty());

        let validate = tool_result(&responses[5]);
        let results = validate["results"].as_array().unwrap();
        assert_eq!(results.len(), 1);
        assert_eq!(results[0]["admitted"], json!(true));
        if retention.is_some() {
            assert_eq!(results[0]["holds"], json!([true]));
            assert_eq!(
                validate["instances"],
                json!([{"kind":"supplied","source_index":1}])
            );
            assert_eq!(validate["cost"], 1);
            let skipped = validate["skipped"].as_array().unwrap();
            assert_eq!(skipped.len(), 2);
            for (entry, source_index) in skipped.iter().zip([0, 2]) {
                assert_eq!(entry["reason"], "not_retained");
                assert_eq!(entry["source_index"], source_index);
                assert!(entry["attempt"].is_u64());
            }
        } else {
            assert_eq!(results[0]["holds"].as_array().unwrap().len(), 3);
            assert_eq!(results[0]["holds"][0], results[0]["holds"][2]);
            assert_eq!(results[0]["holds"][1], true);
            assert_eq!(validate["instances"][0]["kind"], "retained");
            assert_eq!(
                validate["instances"][1],
                json!({"kind":"supplied","source_index":1})
            );
            assert_eq!(validate["instances"][2]["kind"], "retained");
            assert_eq!(validate["cost"], 3);
        }

        assert_eq!(responses[6]["error"]["code"], json!("unknown_tool"));
    }

    let recording = verify_recording(&recorder, &artifacts, &observed);
    let calls: Vec<_> = recording
        .events()
        .iter()
        .filter_map(|event| match event {
            TranscriptEvent::ToolCall { call_id, .. } => Some(*call_id),
            _ => None,
        })
        .collect();
    let responses: Vec<_> = recording
        .events()
        .iter()
        .filter_map(|event| match event {
            TranscriptEvent::ToolResponse { call_id, .. } => Some(*call_id),
            _ => None,
        })
        .collect();
    assert!(!calls.is_empty());
    assert_eq!(calls, responses);
    solver.shutdown().await.unwrap();
    drop(solver);
    drop(admission);
    drop(artifacts);
    owner.settle().unwrap();
}

/// A proposer's private presentation choice is not B policy. Its local trace
/// may differ while B provides the same complete immutable observation.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn live_proposer_local_variants_receive_the_same_complete_observation() {
    async fn one_run(label: &str, mode: &'static str) -> (Value, String, Vec<&'static str>) {
        let directory = support::TestDir::new(label);
        let launch_log = directory.path().join("vampire-launches.log");
        let solver_admission = agent_admission(1, 1);
        let cancellation = CancellationToken::new();
        // Share the catalog instance; the private presentation choice never
        // enters B's request policy or observation.
        let bound = bind(worker_pool(1), 'f', None, &solver_admission, &cancellation).await;
        let (task, admission, solver, houdini) = bound.into_parts();
        let (owner, artifacts) =
            new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
        let checker = solver
            .clone()
            .production_checker(proof_only_production_config(
                &artifacts,
                &solver_admission,
                proof_vampire(&launch_log),
                &cancellation,
            ));
        let runtime = PreCertificateAgentHoudiniRuntime::new(
            admission.clone(),
            solver.clone(),
            solver_admission.clone(),
            checker,
            artifacts.clone(),
            cancellation.clone(),
            AgentToolPolicy::default(),
        );
        let observed = Arc::new(Mutex::new(Vec::new()));
        let sessions = Arc::new(Mutex::new(Vec::new()));
        let policy = AgentConsultationPolicy::new(AgentConsultationLimits::default()).unwrap();
        let policy_digest = policy.digest().to_string();
        let agent = Agent::new(
            LocalVariantProvider {
                mode,
                clauses: vec![LEVEL_ZERO_CLAUSE],
                observed: Arc::clone(&observed),
                sessions: Arc::clone(&sessions),
            },
            policy,
        );
        let overall_limit = Duration::from_secs(20);
        let search = PreCertificateAgentHoudiniSearch::new(
            Arc::clone(&task),
            agent,
            houdini,
            runtime,
            PreCertificateAgentHoudiniLimits::new(overall_limit, None, Some(1)),
            tokio::time::Instant::now() + overall_limit,
            AgentFeedbackPolicy::default(),
        )
        .unwrap();
        let _outcome = search.run().await;
        let push: Value = {
            let observed = observed.lock().unwrap();
            assert_eq!(observed.len(), 1);
            serde_json::from_slice(&observed[0].bytes).unwrap()
        };
        let recorded = sessions.lock().unwrap().clone();
        solver.shutdown().await.unwrap();
        drop(solver);
        drop(admission);
        drop(artifacts);
        owner.settle().unwrap();
        (push, policy_digest, recorded)
    }

    let (fresh_push, fresh_digest, fresh_sessions) =
        one_run("fixed_ambient_session_mode_fresh", "compact").await;
    let (continuous_push, continuous_digest, continuous_sessions) =
        one_run("fixed_ambient_session_mode_continuous", "verbose").await;

    // C's private choice is absent from B's policy.
    assert_eq!(fresh_digest, continuous_digest);
    assert_eq!(fresh_push["operation"], "proposer_observation");
    assert!(fresh_push.get("session_mode").is_none());
    assert_eq!(
        fresh_push["binding"]["policy_digest"].as_str(),
        Some(fresh_digest.as_str())
    );
    assert_eq!(
        continuous_push["binding"]["policy_digest"].as_str(),
        Some(continuous_digest.as_str())
    );

    // The pushed document itself is identical. Only the three wall-time
    // derived fields are normalized away: the remaining budget, and the
    // consultation and validation-manifest digests it feeds.
    let normalize = |push: &Value| {
        let mut feedback = push["feedback"].clone();
        let object = feedback.as_object_mut().unwrap();
        object.insert("remaining_search_budget_ns".to_string(), json!("<budget>"));
        let binding = object.get_mut("binding").unwrap().as_object_mut().unwrap();
        binding.insert("consultation_digest".to_string(), json!("<time>"));
        binding.insert("validation_manifest_digest".to_string(), json!("<time>"));
        feedback
    };
    assert_eq!(normalize(&fresh_push), normalize(&continuous_push));
    // Everything that does not depend on wall time is byte-identical,
    // including the run and state-snapshot digests and the presentation.
    assert_eq!(
        fresh_push["feedback"]["binding"]["run_digest"],
        continuous_push["feedback"]["binding"]["run_digest"]
    );
    assert_eq!(
        fresh_push["feedback"]["binding"]["state_snapshot_digest"],
        continuous_push["feedback"]["binding"]["state_snapshot_digest"]
    );
    assert_eq!(
        fresh_push["feedback"]["presentation"]["presentation_digest"],
        continuous_push["feedback"]["presentation"]["presentation_digest"]
    );

    assert_eq!(fresh_sessions, vec!["compact"]);
    assert_eq!(continuous_sessions, vec!["verbose"]);
}

/// Records a C-owned choice locally, then submits the same fixed proposal.
struct LocalVariantProvider {
    mode: &'static str,
    clauses: Vec<&'static str>,
    observed: Arc<Mutex<Vec<ObservedProviderRequest>>>,
    sessions: Arc<Mutex<Vec<&'static str>>>,
}

impl AgentProvider for LocalVariantProvider {
    fn quiesce_request(&mut self) -> whiel_runner::proposer_api::ProposerCleanupFuture<'_> {
        Box::pin(async { Ok(()) })
    }
    fn shutdown(
        &mut self,
        _reason: whiel_runner::proposer_api::wire::ShutdownReason,
    ) -> whiel_runner::proposer_api::ProposerCleanupFuture<'_> {
        self.quiesce_request()
    }

    fn consult<'a>(
        &'a mut self,
        request: &'a AgentPush,
        _tools: &'a dyn AgentToolSurface,
        response: &'a mut AgentResponseWriter,
        _cancellation: AgentSourceCancellation,
    ) -> AgentSourceFuture<'a> {
        self.sessions.lock().unwrap().push(self.mode);
        observe(&self.observed, request);
        let bytes = clause_response(request, &self.clauses);
        let _ = response.write_chunk(&bytes);
        Box::pin(async { AgentSourceOutcome::Response })
    }
}

/// A scripted provider that calls every tool once with bad, ineligible, or
/// oversized arguments (plus one call against a disabled tool and one
/// against an unrecognized name), recording each typed error, then submits
/// a single ordinary clause so the round completes normally.
struct BadArgumentsProvider {
    observed: Arc<Mutex<Vec<ObservedProviderRequest>>>,
    tool_responses: Arc<Mutex<Vec<Value>>>,
}

impl AgentProvider for BadArgumentsProvider {
    fn quiesce_request(&mut self) -> whiel_runner::proposer_api::ProposerCleanupFuture<'_> {
        Box::pin(async { Ok(()) })
    }
    fn shutdown(
        &mut self,
        _reason: whiel_runner::proposer_api::wire::ShutdownReason,
    ) -> whiel_runner::proposer_api::ProposerCleanupFuture<'_> {
        self.quiesce_request()
    }

    fn consult<'a>(
        &'a mut self,
        request: &'a AgentPush,
        tools: &'a dyn AgentToolSurface,
        response: &'a mut AgentResponseWriter,
        _cancellation: AgentSourceCancellation,
    ) -> AgentSourceFuture<'a> {
        observe(&self.observed, request);
        let bytes = clause_response(request, &[LEVEL_ZERO_CLAUSE]);
        // 129 drafts, one past the removed 128-clause cap: with no host
        // `evaluation_cost` limit set, this call is served, not refused.
        let large_clause_batch: Vec<String> =
            std::iter::repeat_n(String::from("(x)"), 129).collect();
        let bogus_clause = json!({
            "clause_id": 999_999_u64,
            "record_digest": "a".repeat(64),
            "formula_digest": "b".repeat(64),
        });
        Box::pin(async move {
            let calls: Vec<(&str, Value)> = vec![
                ("bogus_tool", json!({})),
                ("countermodel", json!({})),
                ("countermodel", json!({"attempt": "not-a-number"})),
                ("strongest_refutations", json!({})),
                ("strongest_refutations", json!({"clause": bogus_clause})),
                ("history", json!({"clause": {"clause_id": 0}})),
                ("history", json!({"clause": bogus_clause})),
                ("ledger", json!({"cursor": "not-a-number"})),
                ("validate_clauses", json!({})),
                ("validate_clauses", json!({"clauses": large_clause_batch})),
                (
                    "evaluate_clauses",
                    json!({"clauses": [], "instances": [{"kind":"retained","attempt":424_242_u64}]}),
                ),
                ("get_skill", json!({})),
            ];
            for (name, args) in calls {
                let outcome = tools.call(name, args).await;
                self.tool_responses
                    .lock()
                    .unwrap()
                    .push(serde_json::to_value(&outcome).unwrap());
            }
            let _ = response.write_chunk(&bytes);
            AgentSourceOutcome::Response
        })
    }
}

/// Every error code and argument-validation path `AgentToolDispatcher`
/// defines, plus a disabled tool rejected regardless of its arguments
/// (`ledger` is the one disabled tool this run's policy omits).
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn live_consultation_tool_surface_rejects_bad_arguments_and_a_disabled_tool() {
    let directory = support::TestDir::new("fixed_ambient_tool_surface_bad_arguments");
    let launch_log = directory.path().join("vampire-launches.log");
    let solver_admission = agent_admission(1, 1);
    let cancellation = CancellationToken::new();
    let tool_policy = AgentToolPolicy::new([
        AgentTool::Countermodel,
        AgentTool::StrongestRefutations,
        AgentTool::History,
        AgentTool::ValidateClauses,
        AgentTool::EvaluateClauses,
    ]);
    let bound = bind_fixed_ambient_framework_ii(
        fixture_descriptor(),
        worker_pool(1),
        "e".repeat(64),
        HostLimits::UNBOUNDED,
        false,
        tool_policy.clone(),
        &solver_admission,
        &cancellation,
    )
    .await
    .expect("bind the checked-in fixed-ambient fixture");
    let (task, admission, solver, houdini) = bound.into_parts();
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let checker = solver
        .clone()
        .production_checker(proof_only_production_config(
            &artifacts,
            &solver_admission,
            proof_vampire(&launch_log),
            &cancellation,
        ));
    let runtime = PreCertificateAgentHoudiniRuntime::new(
        admission.clone(),
        solver.clone(),
        solver_admission.clone(),
        checker,
        artifacts.clone(),
        cancellation.clone(),
        tool_policy,
    );
    let observed = Arc::new(Mutex::new(Vec::new()));
    let tool_responses = Arc::new(Mutex::new(Vec::new()));
    let record_policy = AgentConsultationPolicy::default();
    let record_feedback = PreCertificateAgentHoudiniState::new(
        Arc::clone(&task),
        &artifacts,
        &houdini,
        Duration::from_secs(30),
        AgentFeedbackPolicy::default(),
    )
    .unwrap();
    let recorder = recording_fixture(&task, record_feedback.feedback(), &record_policy);
    drop(record_feedback);
    let agent = RecordingProvider::agent(
        BadArgumentsProvider {
            observed: Arc::clone(&observed),
            tool_responses: Arc::clone(&tool_responses),
        },
        record_policy,
        recorder.clone(),
    );
    let overall_limit = Duration::from_secs(20);
    let search = PreCertificateAgentHoudiniSearch::new(
        Arc::clone(&task),
        agent,
        houdini,
        runtime,
        PreCertificateAgentHoudiniLimits::new(overall_limit, None, Some(4)),
        tokio::time::Instant::now() + overall_limit,
        AgentFeedbackPolicy::default(),
    )
    .unwrap();

    let outcome = search.run().await;
    assert!(
        matches!(&outcome, PreCertificateAgentHoudiniOutcome::Valid(_)),
        "{outcome:?}"
    );

    {
        let responses = tool_responses.lock().unwrap();
        // A call with no `error` object succeeded; record it as `ok` so the
        // pinned list says which calls are refused and which are served.
        let codes = responses
            .iter()
            .map(|response| {
                response["error"]["code"]
                    .as_str()
                    .unwrap_or("ok")
                    .to_string()
            })
            .collect::<Vec<_>>();
        assert_eq!(
            codes,
            vec![
                "unknown_tool",
                "invalid_arguments",
                "invalid_arguments",
                "invalid_arguments",
                "unknown_clause",
                "invalid_arguments",
                "unknown_clause",
                "tool_disabled",
                "invalid_arguments",
                // 129 drafts against zero models: no cap refuses it any more.
                "ok",
                "no_refutation",
                "unknown_tool",
            ],
            "{responses:#?}"
        );
    }

    let recording = verify_recording(&recorder, &artifacts, &observed);
    let calls: Vec<_> = recording
        .events()
        .iter()
        .filter_map(|event| match event {
            TranscriptEvent::ToolCall { call_id, .. } => Some(*call_id),
            _ => None,
        })
        .collect();
    let responses: Vec<_> = recording
        .events()
        .iter()
        .filter_map(|event| match event {
            TranscriptEvent::ToolResponse { call_id, .. } => Some(*call_id),
            _ => None,
        })
        .collect();
    assert!(!calls.is_empty());
    assert_eq!(calls, responses);
    solver.shutdown().await.unwrap();
    drop(solver);
    drop(admission);
    drop(artifacts);
    owner.settle().unwrap();
}

// ------------------------------------------------------------
// Pass 7.5d: Batched Dispatch Of A Sweep
// ------------------------------------------------------------

/// A Vampire stand-in for the single-failure drop.
///
/// Its answer is a pure function of the problem text, so both lanes of one
/// check agree and the run is reproducible however the batch's launches
/// interleave. It gives up on exactly one verification condition:
/// `SECOND_LEVEL_ZERO_CLAUSE`'s level-zero step condition, identified by
/// the four non-support axioms of a three-clause step cohort (three `plain`
/// plus `guard`; level-zero initialization carries one, and the restarted
/// two-clause sweep carries three) together with a conjecture that names
/// `S` and not `E` — the other two clauses' step conjectures both name `E`.
/// Every other check proves, citing only its problem's last axiom, which
/// for a step problem is `guard`: a cited set that survives the cohort
/// shrinking, so the restarted sweep is answerable from the dictionary.
/// Every call is logged with the query it was asked about.
fn drop_restart_vampire(directory: &Path, log: &Path) -> VampireWorkerCommand {
    let script = directory.join("drop-restart-vampire.py");
    fs::write(
        &script,
        r#"import fcntl
import os
import sys

log_path = sys.argv[1]
arguments = sys.argv[2:]
is_fmb = "--saturation_algorithm" in arguments
mode = "fmb" if is_fmb else "direct"
query_path = arguments[-1]
key = os.path.basename(query_path)

def real_axiom_names(tptp):
    names = []
    for line in tptp.splitlines():
        marker = None
        for candidate in (", axiom,", ",axiom,"):
            if candidate in line:
                marker = candidate
                break
        if marker is None:
            continue
        prefix = line.split(marker)[0]
        paren = prefix.rfind("(")
        if paren == -1:
            continue
        name = prefix[paren + 1:].strip()
        if name.startswith("axiom_"):
            names.append(name)
    return names

try:
    with open(query_path, "r", encoding="utf-8") as handle:
        contents = handle.read()
except OSError:
    contents = ""
names = real_axiom_names(contents)
goal = ""
capture = False
for line in contents.splitlines():
    if "conjecture" in line:
        capture = True
    if capture:
        goal += line
        if line.rstrip().endswith("."):
            capture = False
names_in_goal = {name for name in ("op_zE", "op_zS", "op_zT") if name in goal}
decision = (
    "giveup"
    if len(names) == 4 and names_in_goal == {"op_zS"}
    else "prove"
)

with open(log_path, "a", encoding="utf-8") as handle:
    fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
    handle.write(f"{mode} axioms={len(names)} decision={decision} key={key}\n")
    handle.flush()
    fcntl.flock(handle.fileno(), fcntl.LOCK_UN)

if decision == "giveup" or is_fmb:
    print("% SZS status GaveUp for problem")
else:
    print("% SZS status Theorem for problem")
    print("% SZS output start Proof for problem")
    if names:
        print(f"fof(fixture_cite, plain, ($false), file('problem.p', {names[-1]})).")
    print("1. $false [fixture]")
    print("% SZS output end Proof for problem")
"#,
    )
    .expect("write the drop/restart Vampire fixture");
    VampireWorkerCommand::new("python3")
        .with_extra_args([script.into_os_string(), log.as_os_str().to_owned()])
        .expect("drop/restart Vampire fixture arguments")
}

/// One level-zero maintenance sweep as the ledger recorded it: the
/// partition it was checked against, and per clause whether the outcome was
/// a launch or a dictionary answer.
#[derive(Clone, Debug, PartialEq, Eq)]
struct RecordedSweep {
    partition: String,
    launches: usize,
    reuses: usize,
    checks: usize,
}

fn recorded_level_zero_step_sweeps(houdini: &LeveledHoudiniState) -> Vec<RecordedSweep> {
    let mut sweeps: Vec<RecordedSweep> = Vec::new();
    for row in houdini.attempts().rows() {
        let LevelLedgerRow::Attempt(attempt) = row else {
            continue;
        };
        let request = attempt.request();
        if request.role() != FrameworkIICheckRole::Maintenance
            || request.level() != FrameworkIILevel::ZERO
        {
            continue;
        }
        let partition = request.snapshot().partition_digest().to_owned();
        let evidence = match attempt.outcome() {
            FrameworkIICheckOutcome::Proved(evidence)
            | FrameworkIICheckOutcome::Refuted(evidence) => evidence,
            FrameworkIICheckOutcome::Inconclusive { progress, .. } => progress,
        };
        let reused = evidence.semantic_reuse().is_some();
        match sweeps.last_mut() {
            Some(sweep) if sweep.partition == partition => {
                sweep.checks += 1;
                if reused {
                    sweep.reuses += 1;
                } else {
                    sweep.launches += 1;
                }
            }
            _ => sweeps.push(RecordedSweep {
                partition,
                launches: usize::from(!reused),
                reuses: usize::from(reused),
                checks: 1,
            }),
        }
    }
    sweeps
}

struct DropRestartRun {
    sweeps: Vec<RecordedSweep>,
    committed: Vec<(String, u64)>,
    /// The dictionary's keyed entries: `(kind, key, count)` per key. The
    /// keys are built from Lean-issued formula identities and the scope,
    /// never from the catalog digest, so two runs of this fixture under
    /// different catalog digits must produce the identical list.
    dictionary: Vec<(&'static str, String, usize)>,
    proof_subsumption_hits: u64,
    semantic_reuses: u64,
    batches: u64,
    concurrent_batches: u64,
    max_in_flight: usize,
    vampire_launches: usize,
}

async fn drop_restart_run(digit: char, concurrent: bool) -> DropRestartRun {
    let directory = support::TestDir::new(&format!("fixed_ambient_drop_restart_{digit}"));
    let launch_log = directory.path().join("vampire-launches.log");
    fs::write(&launch_log, "").unwrap();
    let solver_admission = agent_admission(3, 3);
    let cancellation = CancellationToken::new();
    let bound = bind(
        worker_pool(3),
        digit,
        Some(FrameworkIILevel::ONE),
        &solver_admission,
        &cancellation,
    )
    .await;
    let (task, admission, solver, mut houdini) = bound.into_parts();
    solver.set_concurrent_dispatch(concurrent);
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();

    let clauses = admit(
        &admission,
        &[LEVEL_ZERO_CLAUSE, SECOND_LEVEL_ZERO_CLAUSE, EDB_CLAUSE],
        &solver_admission,
        &cancellation,
    )
    .await;
    assert_eq!(clauses.len(), 3);
    register_and_enqueue(&mut houdini, &clauses);

    let mut checker = solver.clone().production_checker(production_config(
        &artifacts,
        &solver_admission,
        FmbOptions::default(),
        drop_restart_vampire(directory.path(), &launch_log),
        &cancellation,
    ));
    let outcome = stabilize_leveled_houdini(&mut houdini, &mut checker)
        .await
        .unwrap();
    assert!(
        matches!(outcome, LeveledStabilizationOutcome::Stabilized(_)),
        "the drop/restart fixture must stabilize: {outcome:?}"
    );

    let sweeps = recorded_level_zero_step_sweeps(&houdini);
    let committed = houdini
        .committed_levels()
        .iter()
        .map(|(clause, level)| {
            (
                houdini
                    .catalog()
                    .record(*clause)
                    .unwrap()
                    .formula()
                    .canonical_source()
                    .to_owned(),
                level.get(),
            )
        })
        .collect::<Vec<_>>();
    let run = DropRestartRun {
        sweeps,
        committed,
        dictionary: checker.dictionary_entry_summary(),
        proof_subsumption_hits: checker.proof_subsumption_hits_total(),
        semantic_reuses: checker.semantic_reuses_total(),
        batches: checker.batches_total(),
        concurrent_batches: checker.concurrent_batches_total(),
        max_in_flight: checker.max_in_flight_launches(),
        vampire_launches: fs::read_to_string(&launch_log).unwrap().lines().count(),
    };
    drop(checker);
    solver.shutdown().await.unwrap();
    drop(solver);
    drop(admission);
    drop(artifacts);
    owner.settle().unwrap();
    run
}

/// Pass 7.5d, deliverable 2 (and the Pass-7.5b test debt): the whole step
/// sweep of a level goes to the pools at once, the single-failure drop takes
/// the first failure in check order, and the sweep the drop restarts is
/// answered from the dictionary instead of relaunching.
///
/// The saving is isolated by counting both numbers on the same run: the
/// restarted sweep issues one check per surviving clause, and every one of
/// them closes as a proof-subsumption reuse, so it launches nothing. The
/// naive cost of the restart is the check count; the paid cost is the
/// launch count.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn live_single_failure_drop_restart_is_answered_from_the_dictionary() {
    let run = drop_restart_run('9', true).await;

    assert!(
        run.sweeps.len() >= 2,
        "the drop must restart the sweep: {:?}",
        run.sweeps
    );
    let first = &run.sweeps[0];
    let restarted = &run.sweeps[1];
    assert_eq!(
        first.checks, 3,
        "the whole sweep is dispatched as one batch: {first:?}"
    );
    assert_eq!(
        first.launches, 3,
        "nothing in the first sweep is a reuse: {first:?}"
    );
    assert_eq!(
        restarted.checks, 2,
        "the restarted sweep checks the survivors: {restarted:?}"
    );
    assert_eq!(
        restarted.launches, 0,
        "the restarted sweep launches nothing: {restarted:?}"
    );
    assert_eq!(
        restarted.reuses, restarted.checks,
        "every check of the restarted sweep is a dictionary answer: {restarted:?}"
    );
    assert!(run.proof_subsumption_hits >= 2);
    assert!(run.batches > 0);
}

/// Pass 7.5d abort criterion, live: running the batch's launches
/// concurrently must not change the Core, the drop, or the dictionary. The
/// same fixture goes through the concurrent dispatch and — with the
/// semantic adapter's shareable handle withheld — through the sequential
/// one the checker falls back to.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn live_concurrent_batch_dispatch_matches_sequential_dispatch() {
    let concurrent = drop_restart_run('a', true).await;
    let sequential = drop_restart_run('b', false).await;

    assert_eq!(concurrent.committed, sequential.committed);
    assert_eq!(
        concurrent
            .sweeps
            .iter()
            .map(|sweep| (sweep.checks, sweep.launches, sweep.reuses))
            .collect::<Vec<_>>(),
        sequential
            .sweeps
            .iter()
            .map(|sweep| (sweep.checks, sweep.launches, sweep.reuses))
            .collect::<Vec<_>>()
    );
    // The doc claims the dictionary is unchanged, so compare what it
    // holds — every key and the kind and count of entries under it — not
    // only how often it answered.
    assert_eq!(concurrent.dictionary, sequential.dictionary);
    assert!(
        !concurrent.dictionary.is_empty(),
        "the fixture must record dictionary entries for the comparison to mean anything"
    );
    assert_eq!(
        concurrent.proof_subsumption_hits,
        sequential.proof_subsumption_hits
    );
    assert_eq!(concurrent.semantic_reuses, sequential.semantic_reuses);
    assert_eq!(concurrent.batches, sequential.batches);

    // The two runs differ only in whether the batch's launches overlapped.
    // How many launches actually overlapped is a scheduling detail — with
    // three of them a worker thread can finish one before the next is even
    // spawned — so what is asserted here is that the concurrent path was
    // taken at all, and that withholding the shareable handle really did
    // fall back to the sequential one. The overlap itself is asserted where
    // it is not a coin flip: `framework2_preparation_stress`, whose sweep
    // has a hundred launches.
    assert!(concurrent.concurrent_batches > 0);
    assert!(concurrent.vampire_launches > 0);
    assert_eq!(sequential.concurrent_batches, 0);
    assert_eq!(sequential.max_in_flight, 0);
    println!(
        "live_concurrent_batch_dispatch: max_in_flight={} vampire_launches={} (sequential {})",
        concurrent.max_in_flight, concurrent.vampire_launches, sequential.vampire_launches
    );
}

// ------------------------------------------------------------
// Agent Counterexample Proposals (Pass 7.5e)
// ------------------------------------------------------------

/// One `candidate_counterexample` submission, bound to the exact push.
fn counterexample_response(request: &AgentPush, instance: &Value) -> Vec<u8> {
    let request_value: Value =
        serde_json::from_slice(request.bytes()).expect("provider receives valid request JSON");
    let response = json!({
        "kind":"candidate_counterexample",
        "schema_version":4,
        "binding":request_bound_response_binding(&request_value, request),
        "input":instance,
    });
    serde_json::to_vec(&response).expect("provider response serializes")
}

/// Submits one counterexample instance on the first consultation and the
/// given clause on every later one, so the run can be observed both across
/// the counterexample round and after it.
struct CounterexampleThenClauseProvider {
    instance: Value,
    clause: &'static str,
    observed: Arc<Mutex<Vec<ObservedProviderRequest>>>,
    consultations: Arc<AtomicUsize>,
}

impl AgentProvider for CounterexampleThenClauseProvider {
    fn quiesce_request(&mut self) -> whiel_runner::proposer_api::ProposerCleanupFuture<'_> {
        Box::pin(async { Ok(()) })
    }
    fn shutdown(
        &mut self,
        _reason: whiel_runner::proposer_api::wire::ShutdownReason,
    ) -> whiel_runner::proposer_api::ProposerCleanupFuture<'_> {
        self.quiesce_request()
    }

    fn consult<'a>(
        &'a mut self,
        request: &'a AgentPush,
        _tools: &'a dyn AgentToolSurface,
        response: &'a mut AgentResponseWriter,
        _cancellation: AgentSourceCancellation,
    ) -> AgentSourceFuture<'a> {
        observe(&self.observed, request);
        let ordinal = self.consultations.fetch_add(1, Ordering::SeqCst);
        let bytes = if ordinal == 0 {
            counterexample_response(request, &self.instance)
        } else {
            clause_response(request, &[self.clause])
        };
        let _ = response.write_chunk(&bytes);
        Box::pin(async { AgentSourceOutcome::Response })
    }
}

/// Run one counterexample round against the live Lean worker, followed by a
/// proving clause round, and return the pushes the provider saw plus the
/// handoff inspection.
async fn counterexample_round(
    label: &str,
    instance: Value,
    pool: FixedAmbientWorkerPoolConfig,
    counterexample_limit: Duration,
) -> (
    Vec<Value>,
    whiel_runner::PreCertificateAgentHoudiniInspection,
) {
    let mut fixture = SearchFixture::new(label, 'b', pool).await;
    let cancellation = CancellationToken::new();
    let runtime = fixture.runtime("proof", &cancellation);
    let observed = Arc::new(Mutex::new(Vec::new()));
    let agent = Agent::with_default_policy(CounterexampleThenClauseProvider {
        instance,
        clause: LEVEL_ZERO_CLAUSE,
        observed: Arc::clone(&observed),
        consultations: Arc::new(AtomicUsize::new(0)),
    });
    let overall_limit = Duration::from_secs(60);
    let search = PreCertificateAgentHoudiniSearch::new(
        Arc::clone(&fixture.task),
        agent,
        fixture.houdini.take().unwrap(),
        runtime,
        PreCertificateAgentHoudiniLimits::new_with_counterexample_limit(
            overall_limit,
            None,
            Some(4),
            counterexample_limit,
        ),
        tokio::time::Instant::now() + overall_limit,
        AgentFeedbackPolicy::default(),
    )
    .unwrap();

    let outcome = search.run().await;
    let PreCertificateAgentHoudiniOutcome::Valid(handoff) = outcome else {
        panic!("the clause round after a rejected counterexample must still prove: {outcome:?}")
    };
    let inspection = handoff.inspection().unwrap();
    let pushes = {
        let observed = observed.lock().unwrap();
        observed
            .iter()
            .map(|push| serde_json::from_slice::<Value>(&push.bytes).unwrap())
            .collect::<Vec<_>>()
    };
    drop(handoff);
    fixture.settle().await;
    (pushes, inspection)
}

/// A counterexample submission is answered by Lean, never by an epoch: no
/// clause is admitted, no termination check runs, and the next push carries
/// the `counterexample_rejected` event with Lean's own code and reason.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn live_counterexample_submission_is_rejected_without_running_an_epoch() {
    let (pushes, inspection) = counterexample_round(
        "fixed_ambient_counterexample_rejected",
        json!({"relations": []}),
        worker_pool(1),
        Duration::from_secs(30),
    )
    .await;

    assert_eq!(pushes.len(), 2);
    let latest = &pushes[1]["feedback"]["latest"];
    assert_eq!(latest["kind"], json!("counterexample_rejected"));
    let code = latest["counterexample_rejected"]["code"]
        .as_str()
        .expect("a rejection names its code")
        .to_string();
    assert!(
        whiel_runner::LEAN_COUNTEREXAMPLE_REJECTION_CODES.contains(&code.as_str()),
        "unexpected rejection code {code}"
    );
    assert!(
        !latest["counterexample_rejected"]["reason"]
            .as_str()
            .unwrap()
            .is_empty()
    );

    // Two consultations, but only the clause round ran an epoch: exactly one
    // termination check and exactly the one admitted clause.
    assert_eq!(inspection.iteration(), 2);
    assert_eq!(inspection.termination_attempts_total(), 1);
    assert_eq!(inspection.catalog_len(), 1);
    assert_eq!(inspection.core().snapshot().canonical_order().len(), 1);
}

/// Lean owns every rejection class, and instance size is not one of them
/// (Pass 7.7b): an unknown relation is refused with Lean's own
/// `unknown_relation`, and an instance far larger than the removed caps
/// earns the same code for the same reason — the relation name — never a
/// size rejection.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn live_counterexample_naming_an_unknown_relation_is_rejected_at_any_size() {
    let (pushes, _) = counterexample_round(
        "fixed_ambient_counterexample_unknown_relation",
        json!({"relations": [{"name": "definitely_not_a_relation", "rows": []}]}),
        worker_pool(1),
        Duration::from_secs(30),
    )
    .await;
    assert_eq!(
        pushes[1]["feedback"]["latest"]["counterexample_rejected"]["code"],
        json!("unknown_relation")
    );

    // 400 rows over 400 distinct values: well beyond the removed 256-row and
    // 64-value caps. The decoder reads it and rejects it on its relation
    // name alone.
    let rows = (0..400)
        .map(|index| json!([format!("num:{index}"), format!("num:{index}")]))
        .collect::<Vec<_>>();
    let (pushes, _) = counterexample_round(
        "fixed_ambient_counterexample_larger_than_the_removed_caps",
        json!({"relations": [{"name": "definitely_not_a_relation", "rows": rows}]}),
        worker_pool(1),
        Duration::from_secs(30),
    )
    .await;
    assert_eq!(
        pushes[1]["feedback"]["latest"]["counterexample_rejected"]["code"],
        json!("unknown_relation"),
        "instance size is no longer a rejection class"
    );
}

/// Rust never parses the instance: an arbitrary nested JSON object submitted
/// by the provider reaches the Lean worker's `validate_counterexample`
/// payload exactly as submitted.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn live_counterexample_instance_reaches_the_worker_untouched() {
    let directory = support::TestDir::new("fixed_ambient_counterexample_capture");
    let (pool, marker) = fault_pool(&directory, "capture_counterexample");
    let instance = json!({
        "relations": [{"name": "definitely_not_a_relation", "rows": [["num:1", "num:2"]]}],
        "unexpected": {"nested": [1, 2, {"deeper": null, "text": "opaque to Rust"}]},
        "zzz_last_key": [true, false],
    });
    let (pushes, _) = counterexample_round(
        "fixed_ambient_counterexample_capture_run",
        instance.clone(),
        pool,
        Duration::from_secs(30),
    )
    .await;
    assert_eq!(
        pushes[1]["feedback"]["latest"]["kind"],
        json!("counterexample_rejected")
    );

    let captured = fs::read(&marker).expect("the proxy recorded the counterexample request frame");
    let frame: Value = serde_json::from_slice(&captured).expect("the captured frame is JSON");
    assert_eq!(frame["operation"], json!("validate_counterexample"));
    assert_eq!(frame["payload"]["input"], instance);
    assert_eq!(
        serde_json::to_string(&frame["payload"]["input"]).unwrap(),
        serde_json::to_string(&instance).unwrap()
    );
    assert_eq!(
        frame["payload"].as_object().map(|payload| payload.len()),
        Some(1),
        "the request carries the instance and nothing else: no fuel bound"
    );
    drop(directory);
}

/// A worker that never answers the counterexample call is terminated by the
/// host's call-local limit and replaced by the pool: the submission becomes
/// an ordinary `timeout` rejection and the run continues to a proof.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn live_stalled_counterexample_validation_times_out_and_the_pool_recovers() {
    let directory = support::TestDir::new("fixed_ambient_counterexample_stall");
    let (pool, marker) = fault_pool(&directory, "stall_counterexample");
    let (pushes, inspection) = counterexample_round(
        "fixed_ambient_counterexample_stall_run",
        json!({"relations": []}),
        pool,
        Duration::from_millis(750),
    )
    .await;

    assert!(marker.exists(), "the stalling worker must publish its PID");
    assert_eq!(
        pushes[1]["feedback"]["latest"]["counterexample_rejected"]["code"],
        json!("timeout")
    );
    // The run itself was never cancelled: the replacement worker served the
    // clause round and its epoch proved the termination check.
    assert_eq!(inspection.iteration(), 2);
    assert_eq!(inspection.termination_attempts_total(), 1);
    assert!(!inspection.runtime().cancellation_requested());
    drop(directory);
}

// ------------------------------------------------------------
// Refutable Task: The Invalid Run (Pass 7.5e)
// ------------------------------------------------------------

/// The two-edge witness that refutes `Example0013`'s postcondition
/// `T ⊆ E`: the transitive closure of `{(0,1),(1,2)}` also contains
/// `(0,2)`, which `E` does not.
fn refutable_witness() -> Value {
    json!({
        "relations": [
            {"name": "p::E", "rows": [["num:0", "num:1"], ["num:1", "num:2"]]},
            {"name": "p::S", "rows": []},
            {"name": "p::T", "rows": []},
        ]
    })
}

/// An instance of `Example0013` whose halted run satisfies `T ⊆ E`, so Lean
/// rejects it with its own `postcondition_holds` code.
fn refutable_non_witness() -> Value {
    json!({
        "relations": [
            {"name": "p::E", "rows": [["num:0", "num:0"]]},
            {"name": "p::S", "rows": []},
            {"name": "p::T", "rows": []},
        ]
    })
}

/// Collect every file below `root`, recursively.
fn collect_certificate_files(root: &Path, into: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(root).expect("read the promoted certificate tree") {
        let path = entry.expect("read one certificate tree entry").path();
        if path.is_dir() {
            collect_certificate_files(&path, into);
        } else {
            into.push(path);
        }
    }
}

/// The staging root must be empty again once a build returns.
fn staging_is_empty(staging_root: &Path) -> bool {
    fs::read_dir(staging_root)
        .expect("read the staging root")
        .next()
        .is_none()
}

/// A counterexample instance larger than every cap Pass 7.7b removed: 71
/// distinct carrier values (removed cap: 64) and 300 rows in one relation,
/// 302 across the instance (removed caps: 256 per relation, 1024 in total).
///
/// The extra rows live in `p::S`, which `Example0013`'s command overwrites
/// on its first statement, so the instance is large without changing what
/// the transitive-closure loop computes: the size, not the closure, is what
/// this exercises. `p::E` is still the two-edge witness, so the halted run
/// still violates `T ⊆ E`.
/// Rows of `p::S` in the over-cap witness. Past the removed 1024-row total
/// and the removed 256-row per-relation cap, and chosen for the one relation
/// the input command's first statement overwrites, so these rows are never
/// composed by the program's relational algebra and the kernel check stays
/// inside the measured budget.
const OVERSIZED_WITNESS_ROWS: u64 = 1_100;

/// Distinct carrier values the over-cap witness carries.
///
/// `p::S` contributes `(2i+3, 2i+4)` for `i < OVERSIZED_WITNESS_ROWS`, whose
/// two columns together cover every integer from 3 to `2n+2` inclusive —
/// `2 * OVERSIZED_WITNESS_ROWS` values. `p::E` adds `0`, `1` and `2`.
const OVERSIZED_WITNESS_CARRIER_VALUES: u64 = 2 * OVERSIZED_WITNESS_ROWS + 3;

fn oversized_witness() -> Value {
    let wide_rows = (0..OVERSIZED_WITNESS_ROWS)
        .map(|index: u64| {
            json!([
                format!("num:{}", 2 * index + 3),
                format!("num:{}", 2 * index + 4)
            ])
        })
        .collect::<Vec<_>>();
    json!({
        "relations": [
            {"name": "p::E", "rows": [["num:0", "num:1"], ["num:1", "num:2"]]},
            {"name": "p::S", "rows": wide_rows},
            {"name": "p::T", "rows": []},
        ]
    })
}

/// Pass 7.7b: an instance larger than every removed cap is validated by the
/// live Lean worker *and certified*, and both calls are timed rather than
/// bounded.
///
/// The witness carries 1_100 rows in one relation — past the removed
/// 1024-row total, the removed 256-row per-relation cap, and the removed
/// 64-value carrier cap — in `p::S`, which the input command's first
/// statement overwrites. That is the point: the certificate build's cost is
/// the number of rows the program's own relational algebra *composes*, not
/// the instance's size, so a large non-composing relation certifies inside a
/// few seconds while the same count in `p::E` would exhaust the kernel's
/// memory. The certificate is built into the test's own staging directory
/// and never near the checked-in `Benchmark/Example0013/Certificate` tree,
/// which belongs to the two-edge witness.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn live_counterexample_larger_than_the_removed_caps_is_validated_and_timed() {
    let mut fixture = SearchFixture::for_task(
        "fixed_ambient_oversized_counterexample",
        REFUTABLE_TASK_ID,
        'f',
        worker_pool(1),
    )
    .await;
    let cancellation = CancellationToken::new();

    let instance = oversized_witness();
    let relations = instance["relations"].as_array().unwrap();
    let wide = relations[1]["rows"].as_array().unwrap().len();
    assert_eq!(
        wide,
        usize::try_from(OVERSIZED_WITNESS_ROWS).unwrap(),
        "the non-composing relation carries every over-cap row"
    );

    let started = std::time::Instant::now();
    let validation = fixture
        .solver
        .validate_counterexample(&instance, &fixture.solver_admission, &cancellation)
        .await
        .expect("no size bound refuses this instance");
    let validated_in = started.elapsed();

    let whiel_runner::CounterexampleValidation::Validated(validated) = validation else {
        panic!("the oversized instance still refutes the triple: {validation:?}")
    };
    // The record freezes the fuel the run actually consumed. The extra rows
    // are discarded by the command's first statement, so the run is the
    // same six steps the two-edge witness takes.
    assert_eq!(validated.fuel_consumed(), 6);
    println!(
        "validate_counterexample: {} rows in p::S, {} distinct carrier values, \
         elapsed {validated_in:?}, fuel consumed {}",
        OVERSIZED_WITNESS_ROWS,
        OVERSIZED_WITNESS_CARRIER_VALUES,
        validated.fuel_consumed()
    );
    drop(validated);

    // The same instance through the search, whose frozen record is what a
    // certificate is built from. `FrozenCounterexampleRecord` is only ever
    // minted by the search, so this is the one way to reach the build.
    let runtime = fixture.runtime("unknown", &cancellation);
    let agent = Agent::with_default_policy(CounterexampleThenClauseProvider {
        instance: oversized_witness(),
        clause: LEVEL_ZERO_CLAUSE,
        observed: Arc::new(Mutex::new(Vec::new())),
        consultations: Arc::new(AtomicUsize::new(0)),
    });
    let overall_limit = Duration::from_secs(180);
    let search = PreCertificateAgentHoudiniSearch::new(
        Arc::clone(&fixture.task),
        agent,
        fixture.houdini.take().unwrap(),
        runtime,
        PreCertificateAgentHoudiniLimits::new(overall_limit, None, Some(4)),
        tokio::time::Instant::now() + overall_limit,
        AgentFeedbackPolicy::default(),
    )
    .unwrap();
    let outcome = search.run().await;
    let PreCertificateAgentHoudiniOutcome::Invalid(record) = outcome else {
        panic!("the over-cap witness must end the run invalid: {outcome:?}")
    };
    assert_eq!(record.fuel_consumed(), 6);

    let repository_root = support::repository_root();
    let staging_root = fixture.directory.path().join("staging");
    fs::create_dir_all(&staging_root).unwrap();
    let destination = fixture.directory.path().join("OversizedCertificate");
    let started = std::time::Instant::now();
    let receipt = build_invalid_certificate(InvalidCertificateBuildRequest {
        solver: &fixture.solver,
        admission: &fixture.solver_admission,
        record: &record,
        repository_root,
        staging_root: staging_root.clone(),
        destination: destination.clone(),
        cancellation: &cancellation,
        hooks: CertificateBuildHooks::default(),
    })
    .await
    .expect("the over-cap counterexample builds its own Invalid certificate");
    let certified_in = started.elapsed();

    // Zero solver jobs, and the std3 axiom closure of the negated theorem —
    // the same closure the two-edge witness earns, at 1_100 rows.
    assert!(receipt.jobs.is_empty());
    let mut axioms = receipt.axioms.clone();
    axioms.sort();
    assert_eq!(axioms, vec!["Classical.choice", "Quot.sound", "propext"]);
    assert_eq!(receipt.destination, destination);
    assert!(staging_is_empty(&staging_root));
    assert_invalid_certificate_files(&destination);
    let emitted = fs::read(destination.join("Invalid.lean")).unwrap();
    assert!(!emitted.is_empty());
    // The checked-in certificate belongs to the two-edge witness and is
    // untouched: this build is a different instance entirely.
    let checked_in =
        fs::read(support::repository_root().join("Benchmark/Example0013/Certificate/Invalid.lean"))
            .unwrap();
    assert_ne!(emitted, checked_in);
    println!(
        "build_invalid_certificate: {} rows in p::S, elapsed {certified_in:?}, \
         {} bytes of Invalid.lean, axioms {axioms:?}",
        OVERSIZED_WITNESS_ROWS,
        emitted.len()
    );

    drop(record);
    fixture.settle().await;
}

/// Lean's own digest of the canonical witness instance, pinned by
/// `Whiel/Synthesis/Tests/FixedAmbientWorker.lean`.
const REFUTABLE_WITNESS_IDENTITY: &str =
    "7fb4ca7b93ec6f10c0e9d6ca87258086058ae9cb84c7349177125d50eb9ee64f";

fn assert_invalid_certificate_files(destination: &Path) {
    let mut files = Vec::new();
    collect_certificate_files(destination, &mut files);
    let mut relative: Vec<_> = files
        .iter()
        .map(|path| path.strip_prefix(destination).unwrap())
        .collect();
    relative.sort();
    assert_eq!(
        relative,
        vec![
            Path::new("Invalid.lean"),
            Path::new("certificate-build-settings.json")
        ]
    );
    let settings: Value = serde_json::from_slice(
        &fs::read(destination.join("certificate-build-settings.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(settings["kind"], "whiel_certificate_build_settings");
    assert_eq!(settings["version"], 1);
    assert_eq!(settings["solver_jobs"], 0);
    assert_eq!(settings["preparation_packaging_cpu_worker_limit"], 1);
}

// Preserve every byte of the existing certificate body while expecting
// the deliberately versioned emitter banner. The independent Lean worker
// test pins the actual v2 output digest; Benchmark remains unchanged.
fn expected_refutable_certificate_v2() -> Vec<u8> {
    let original = fs::read_to_string(
        support::repository_root().join("Benchmark/Example0013/Certificate/Invalid.lean"),
    )
    .unwrap();
    let old = "-- Generated by the Lean-owned fixed-ambient certificate emitter.\n";
    let body = original
        .strip_prefix(old)
        .expect("the checked-in legacy banner");
    format!("-- Generated by the Lean-owned fixed-ambient certificate-emitter-v2.\n{body}")
        .into_bytes()
}

/// The whole point of the refutable branch: the agent submits a genuine
/// counterexample on a registered fixed-ambient task, Lean validates it, the
/// run ends `Invalid` without running a single epoch, and the frozen record
/// alone builds a kernel-checked `Certificate/Invalid.lean` at the negated
/// input-schema type, preserving the checked-in body with its v2 banner.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn live_refutable_task_ends_invalid_and_builds_its_kernel_certificate() {
    let mut fixture = SearchFixture::for_task(
        "fixed_ambient_refutable_invalid",
        REFUTABLE_TASK_ID,
        'c',
        worker_pool(1),
    )
    .await;
    let cancellation = CancellationToken::new();
    // The checker never proves anything here: a run that ends `Invalid` must
    // do so without consulting the solver lane at all.
    let runtime = fixture.runtime("unknown", &cancellation);
    let observed = Arc::new(Mutex::new(Vec::new()));
    let policy = AgentConsultationPolicy::default();
    let feedback = PreCertificateAgentHoudiniState::new(
        Arc::clone(&fixture.task),
        &fixture.artifacts,
        fixture.houdini.as_ref().unwrap(),
        Duration::from_secs(20),
        AgentFeedbackPolicy::default(),
    )
    .unwrap();
    let recorder = recording_fixture(&fixture.task, feedback.feedback(), &policy);
    drop(feedback);
    let agent = RecordingProvider::agent(
        CounterexampleThenClauseProvider {
            instance: refutable_witness(),
            clause: LEVEL_ZERO_CLAUSE,
            observed: Arc::clone(&observed),
            consultations: Arc::new(AtomicUsize::new(0)),
        },
        policy,
        recorder.clone(),
    );
    let overall_limit = Duration::from_secs(120);
    let search = PreCertificateAgentHoudiniSearch::new(
        Arc::clone(&fixture.task),
        agent,
        fixture.houdini.take().unwrap(),
        runtime,
        PreCertificateAgentHoudiniLimits::new(overall_limit, None, Some(4)),
        tokio::time::Instant::now() + overall_limit,
        AgentFeedbackPolicy::default(),
    )
    .unwrap();

    let outcome = search.run().await;
    let recording = verify_recording(&recorder, &fixture.artifacts, &observed);
    assert!(recording.final_state_projection().is_some());
    let PreCertificateAgentHoudiniOutcome::Invalid(record) = outcome else {
        panic!("a validated counterexample must end the run invalid: {outcome:?}")
    };

    // The frozen record is Lean's, verbatim.
    assert_eq!(record.instance_identity(), REFUTABLE_WITNESS_IDENTITY);
    assert_eq!(record.fuel_consumed(), 6);
    assert_eq!(record.task_identity().canonical_id(), REFUTABLE_TASK_ID);
    assert_eq!(
        record.scope_identity_sha256(),
        fixture.solver.scope().identity_sha256()
    );

    // Exactly one consultation, and no epoch: nothing was admitted into the
    // catalog and no termination check ever ran.
    assert_eq!(observed.lock().unwrap().len(), 1);
    assert_eq!(
        fixture.solver.scope().task_identity().canonical_id(),
        REFUTABLE_TASK_ID
    );

    // The frozen record alone builds the certificate.
    let repository_root = support::repository_root();
    let staging_root = fixture.directory.path().join("staging");
    fs::create_dir_all(&staging_root).unwrap();
    let destination = fixture.directory.path().join("Certificate");
    let receipt = build_invalid_certificate(InvalidCertificateBuildRequest {
        solver: &fixture.solver,
        admission: &fixture.solver_admission,
        record: &record,
        repository_root: repository_root.clone(),
        staging_root: staging_root.clone(),
        destination: destination.clone(),
        cancellation: &cancellation,
        hooks: CertificateBuildHooks::default(),
    })
    .await
    .expect("the frozen counterexample builds its own Invalid certificate");

    // Zero solver jobs, and the std3 axiom closure of the negated theorem.
    assert!(receipt.jobs.is_empty());
    let mut axioms = receipt.axioms.clone();
    axioms.sort();
    assert_eq!(axioms, vec!["Classical.choice", "Quot.sound", "propext"]);
    assert_eq!(receipt.destination, destination);
    assert!(staging_is_empty(&staging_root));

    // The theorem body is byte-identical; only the emitter banner is v2.
    assert_invalid_certificate_files(&destination);
    let promoted = fs::read(destination.join("Invalid.lean")).unwrap();
    let checked_in = expected_refutable_certificate_v2();
    assert_eq!(
        promoted, checked_in,
        "the emitted Invalid.lean differs beyond the expected v2 banner"
    );

    drop(record);
    fixture.settle().await;
}

/// A submission Lean refuses is an ordinary round: the `postcondition_holds`
/// code reaches the next push, the run's state is untouched, and the clause
/// round that follows runs a real epoch on the same refutable task.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn live_refutable_task_rejects_a_non_witness_and_then_runs_an_epoch() {
    let mut fixture = SearchFixture::for_task(
        "fixed_ambient_refutable_rejected",
        REFUTABLE_TASK_ID,
        'd',
        worker_pool(1),
    )
    .await;
    let cancellation = CancellationToken::new();
    let runtime = fixture.runtime("unknown", &cancellation);
    let observed = Arc::new(Mutex::new(Vec::new()));
    let agent = Agent::with_default_policy(CounterexampleThenClauseProvider {
        instance: refutable_non_witness(),
        clause: LEVEL_ZERO_CLAUSE,
        observed: Arc::clone(&observed),
        consultations: Arc::new(AtomicUsize::new(0)),
    });
    let overall_limit = Duration::from_secs(120);
    let search = PreCertificateAgentHoudiniSearch::new(
        Arc::clone(&fixture.task),
        agent,
        fixture.houdini.take().unwrap(),
        runtime,
        PreCertificateAgentHoudiniLimits::new(overall_limit, None, Some(3)),
        tokio::time::Instant::now() + overall_limit,
        AgentFeedbackPolicy::default(),
    )
    .unwrap();

    // The checker never proves, so the run ends on its iteration limit —
    // which is the truthful outcome for a task whose postcondition is false.
    let outcome = search.run().await;
    let PreCertificateAgentHoudiniOutcome::Failure(report) = outcome else {
        panic!("the refutable clause round cannot prove: {outcome:?}")
    };
    assert_eq!(report.origin(), FailureOrigin::RunControl);

    let pushes = {
        let observed = observed.lock().unwrap();
        observed
            .iter()
            .map(|push| serde_json::from_slice::<Value>(&push.bytes).unwrap())
            .collect::<Vec<_>>()
    };
    assert_eq!(pushes.len(), 3);

    // Lean's own rejection code reached the second push, unchanged.
    let rejected = &pushes[1]["feedback"]["latest"];
    assert_eq!(rejected["kind"], json!("counterexample_rejected"));
    assert_eq!(
        rejected["counterexample_rejected"]["code"],
        json!("postcondition_holds")
    );

    // The clause round that followed ran a real epoch.
    assert_eq!(
        pushes[2]["feedback"]["latest"]["kind"],
        json!("postcondition_open")
    );

    fixture.settle().await;
}

// ------------------------------------------------------------
// Pass 7.5g: The Two Vertical Canaries And The Run Configuration
// ------------------------------------------------------------

/// The `Valid` canary, end to end: a deterministic in-process provider and
/// the real pinned Vampire, settled through the production function.
///
/// One run: a proposal from the fake provider, Lean admission, leveled
/// Houdini, and a termination check *proved by the real pinned Vampire* —
/// the fake provider stands in for the LLM, never for the solver — and then
/// [`settle_search_outcome`], the one production exit from the search,
/// which freezes the Core, re-proves every one of its `2N+1` conditions
/// with the same pinned binary, revalidates, publishes with one rename, and
/// shuts the run's resources down. The published theorem elaborates at the
/// exact raw `Input.lean` declaration type
/// `Whiel.HoareValid inputPre inputCmd inputPost` with an exactly-std3
/// axiom closure. Everything runs under the `direct` profile: this canary
/// fixes one search so a change of outcome is a change of the engine, and
/// there is deliberately no fallback between profiles.
///
/// It is a slow test by construction — the real solver runs the search
/// phase as well as the certification batch — and its wall time is recorded
/// in the pass record. Nothing here is stubbed to make it faster.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn live_valid_canary_publishes_the_certified_aggregate_at_the_exact_input_type() {
    let mut fixture = SearchFixture::new("fixed_ambient_valid_canary", '7', worker_pool(1)).await;
    // Search binds its own deadline; settlement needs a separate,
    // deadline-free external root for its certification allowance.
    let cancellation = CancellationToken::new();
    let external_cancellation = CancellationToken::new();
    let pinned = PinnedLeancheckVampire::from_lock(&support::repository_root())
        .expect("the repository-pinned leancheck Vampire resolves");
    // The solver is real: the search phase's own termination check is
    // proved by the pinned binary, not by a fixture that answers `proof`.
    let runtime = fixture.real_solver_runtime(&pinned, &cancellation);
    let observed = Arc::new(Mutex::new(Vec::new()));
    // The canary proposes the real checked-in Example0001 invariant, so the
    // conditions the search proves and the certification re-proves are
    // conditions that genuinely hold.
    let agent = Agent::with_default_policy(ClauseProvider {
        clauses: vec![CANONICAL_LEVEL_ZERO_CLAUSE, CANONICAL_LEVEL_ONE_CLAUSE],
        observed: Arc::clone(&observed),
    });
    let overall_limit = Duration::from_secs(900);
    let limits = PreCertificateAgentHoudiniLimits::new(overall_limit, None, Some(4));
    let search = PreCertificateAgentHoudiniSearch::new(
        Arc::clone(&fixture.task),
        agent,
        fixture.houdini.take().unwrap(),
        runtime,
        limits,
        tokio::time::Instant::now() + overall_limit,
        AgentFeedbackPolicy::default(),
    )
    .unwrap();

    let started = std::time::Instant::now();
    let outcome = search.run().await;
    assert!(
        matches!(&outcome, PreCertificateAgentHoudiniOutcome::Valid(_)),
        "the real pinned Vampire did not prove the termination check: {outcome:?}"
    );
    let search_elapsed = started.elapsed();

    let staging_root = fixture.directory.path().join("staging");
    let private_root = fixture.directory.path().join("private");
    let destination = fixture.directory.path().join("published/Certificate");
    fs::create_dir_all(&staging_root).unwrap();
    let SettlementParts {
        directory,
        task,
        admission,
        solver_admission,
        resources,
    } = fixture.into_settlement_parts();

    // The production settlement function, not a hand-assembled sequence:
    // certification, revalidation, atomic publication, solver shutdown and
    // artifact settlement all happen inside it.
    let settled = settle_search_outcome(
        outcome,
        SettlementPolicy {
            space_guard: None,
            admission: &admission,
            solver_admission: &solver_admission,
            pinned: &pinned,
            canonical_id: PRODUCTION_TASK_ID,
            input_namespace: "Whiel.Benchmark.Example0001",
            repository_root: support::repository_root(),
            staging_root,
            private_root: private_root.clone(),
            input_directory: directory.path().to_path_buf(),
            destination: destination.clone(),
            time_limit_seconds: 60,
            certification_limit: Duration::from_secs(900),
            concurrency: DEFAULT_CERTIFICATION_CONCURRENCY,
            fuel_policy: CounterexampleFuelPolicy::new(limits.counterexample_validation_limit())
                .unwrap(),
            // `--retention all`: this canary is also where evidence
            // retention is exercised against the real pinned Vampire (see
            // the assertions below and the fake-Vampire-based coverage in
            // `framework2_certificate.rs` for the refusal and drop cases).
            retention: Retention::All,
            external_cancellation: &external_cancellation,
            hooks: CertificateBuildHooks::default(),
        },
        resources,
    )
    .await
    .expect("the canary's run settles as a published Valid result");
    let SettledSearchOutcome::Valid(published) = settled else {
        panic!("a proved termination check settles as a published Valid result: {settled:?}")
    };

    assert_eq!(published.certificate(), destination);
    assert!(destination.join("Valid.lean").is_file());
    // P3/P4: the published tree never carries the solver-evidence subtree,
    // but does carry `timing.csv` at its own root — and, under
    // `Retention::All`, the evidence itself lands beside the run's other
    // payloads instead of being dropped.
    assert!(!destination.join("VampireArtifacts").exists());
    assert!(destination.join("timing.csv").is_file());
    let evidence_root = directory.path().join("CertificateEvidence");
    let non_empty = |path: &Path| fs::metadata(path).map(|metadata| metadata.len() > 0);
    for job in &published.receipt().jobs {
        let problem = evidence_root.join("jobs").join(&job.id).join("problem.p");
        assert!(
            non_empty(&problem).unwrap_or(false),
            "job {} evidence problem.p is kept, and not empty, under {evidence_root:?}",
            job.id
        );
        let leancheck = evidence_root
            .join("jobs")
            .join(&job.id)
            .join("leancheck.lean");
        assert!(
            non_empty(&leancheck).unwrap_or(false),
            "job {} evidence leancheck.lean is kept, and not empty, under {evidence_root:?}",
            job.id
        );
    }
    let mut axioms = published.revalidation().axioms.clone();
    axioms.sort();
    assert_eq!(axioms, vec!["Classical.choice", "Quot.sound", "propext"]);
    assert_eq!(
        published.receipt().certificate_module,
        "Benchmark.Example0001.Certificate.Valid"
    );
    // Exactly 2N+1 conditions for the two-clause Core, every one under the
    // `direct` label the freeze assigned it, with no fallback.
    assert_eq!(published.receipt().jobs.len(), 5);
    for job in &published.receipt().jobs {
        assert_eq!(job.profile.profile(), ProofSearchProfile::Direct);
    }
    assert_eq!(observed.lock().unwrap().len(), 1);
    // Pass 7.5g review, finding 7: the emptied `aggregate-<digest>`
    // directory does not survive the publication, so a later certification
    // of the same frozen Core is not refused by a leftover.
    assert!(
        private_root
            .read_dir()
            .map(|mut entries| entries.next().is_none())
            .unwrap_or(true),
        "the emptied private certification directory is removed: {private_root:?}"
    );
    // The frozen Core is published beside the tree, as the rows record that
    // regenerates the certificate, and it is the checked-in one.
    let record = published
        .certificate()
        .parent()
        .expect("the published tree has a parent")
        .join("Core.json");
    let written: Value = serde_json::from_str(
        &std::fs::read_to_string(&record).expect("Core.json is published beside the tree"),
    )
    .unwrap();
    let checked_in: Value = serde_json::from_str(
        &std::fs::read_to_string(
            support::repository_root().join("Benchmark/Example0001/Core.json"),
        )
        .unwrap(),
    )
    .unwrap();
    assert_eq!(
        written, checked_in,
        "the published Core differs from the checked-in rows"
    );

    // The rounds this certificate came out of survive it: the attempt
    // history is published from the search's own terminal path, with no
    // provider recording installed at all.
    let history = assert_settled_attempt_history(directory.path(), "valid");
    assert!(
        !history["ledger"].as_array().unwrap().is_empty(),
        "a proved Core records the checks that proved it: {history}"
    );

    eprintln!(
        "live_valid_canary: search phase {search_elapsed:.2?}, whole run {:.2?}",
        started.elapsed()
    );
    drop(task);
    drop(directory);
}

/// Exercise the complete public API through a selectable generic endpoint.
/// By default this is an independent standard-library non-LLM fixture.
/// It uses the same racing configuration a campaign runs. Both solver lanes
/// use the actual pinned Vampire; Lean validates the model and freshly
/// kernel-checks the certificate. No model-producing solver is faked.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn live_generic_api_full_model_flow_publishes_a_fresh_kernel_certificate() {
    use whiel_runner::proposer_host::generic_process::GenericProcessProposer;

    let mut fixture = SearchFixture::new("generic_api_full_model", 'c', worker_pool(1)).await;
    let proposer_directory = support::TestDir::new("standalone_generic_proposer");
    let cancellation = CancellationToken::new();
    let external_cancellation = CancellationToken::new();
    let pinned = PinnedLeancheckVampire::from_lock(&support::repository_root())
        .expect("the real repository-pinned leancheck Vampire resolves");
    let production = FrameworkIIProductionCheckConfig::new(
        fixture.artifacts.clone(),
        fixture.solver_admission.clone(),
        VampireSearchBudget::finite(REAL_SOLVER_SEARCH_BUDGET),
        FmbOptions::default(),
        VampireWorkerCommand::new(pinned.path()),
        cancellation.clone(),
        "pinned-leancheck-vampire",
        certification_profiles(),
    )
    .unwrap();
    assert!(production.fmb().is_some());
    let checker = fixture.solver.clone().production_checker(production);
    let tool_policy = AgentToolPolicy::all_enabled();
    let runtime = PreCertificateAgentHoudiniRuntime::new(
        fixture.admission.clone(),
        fixture.solver.clone(),
        fixture.solver_admission.clone(),
        checker,
        fixture.artifacts.clone(),
        cancellation.clone(),
        tool_policy.clone(),
    );
    let policy = AgentConsultationPolicy::default();
    let feedback = PreCertificateAgentHoudiniState::new(
        Arc::clone(&fixture.task),
        &fixture.artifacts,
        fixture.houdini.as_ref().unwrap(),
        Duration::from_secs(60),
        AgentFeedbackPolicy::default(),
    )
    .unwrap();
    let recorder = recording_fixture(&fixture.task, feedback.feedback(), &policy);
    drop(feedback);
    let provider = GenericProcessProposer::start(
        acceptance_proposer_command(proposer_directory.path(), "full"),
        &tool_policy.enabled_names(),
        &cancellation,
    )
    .await
    .expect("the external proposer completes generic API negotiation");
    let cleanup = provider.cleanup_handle();
    let overall_limit = Duration::from_secs(900);
    let limits = PreCertificateAgentHoudiniLimits::new(
        overall_limit,
        Some(Duration::from_secs(60)),
        Some(5),
    );
    let started = std::time::Instant::now();
    let result = catch_test_panic(async {
        let search = PreCertificateAgentHoudiniSearch::new_with_joined_cleanup(
            Arc::clone(&fixture.task),
            RecordingProvider::agent(provider, policy, recorder.clone()),
            fixture.houdini.take().unwrap(),
            runtime,
            limits,
            tokio::time::Instant::now() + overall_limit,
            AgentFeedbackPolicy::default(),
        )
        .await
        .unwrap();
        search.run().await
    })
    .await;
    // Search owns the successful handoff and explicitly completes normal
    // Proposer::shutdown before returning it. Retain an independent fallback
    // across panic paths without borrowing the provider out of that handoff.
    let outcome = match result {
        Ok(outcome) => outcome,
        Err(panic) => {
            cleanup
                .stop_and_join()
                .await
                .expect("failed full-flow endpoint must join");
            std::panic::resume_unwind(panic);
        }
    };
    let trace = canonical_acceptance_trace(&recorder, &fixture.artifacts);
    assert!(
        matches!(&outcome, PreCertificateAgentHoudiniOutcome::Valid(_)),
        "real FMB/Lean/API flow did not reach a valid Core: {outcome:?}"
    );

    let observations = &trace.observations;
    assert!(observations.len() >= 3);
    assert!(!observations[1]["observation"]["correction"].is_null());
    assert_eq!(
        observations[0]["observation"]["binding"]["state_snapshot_digest"],
        observations[1]["observation"]["binding"]["state_snapshot_digest"],
        "wrong-binding correction cannot mutate Houdini"
    );
    assert_ne!(
        observations[0]["coordinates"],
        observations[1]["coordinates"]
    );
    assert_eq!(
        trace.submissions[0]["response"]["binding"]["request_digest"],
        "0".repeat(64)
    );
    assert_eq!(
        trace
            .outcomes
            .iter()
            .filter(|outcome| **outcome == TranscriptOutcome::Correctable)
            .count(),
        1
    );
    assert_eq!(
        observations[1]["observation"]["binding"]["validation_ordinal"],
        1
    );
    assert_ne!(
        trace.submissions[0]["response"]["binding"]["request_digest"],
        trace.submissions[1]["response"]["binding"]["request_digest"]
    );
    let queries = &trace.queries;
    let names: BTreeSet<_> = queries
        .iter()
        .map(|event| event["name"].as_str().unwrap())
        .collect();
    assert_eq!(names, tool_policy.enabled_names().into_iter().collect());
    assert!(queries.iter().any(|event| {
        event["name"] == "history"
            && event["reply"]["result"]["attempts"]
                .as_array()
                .unwrap()
                .iter()
                .any(|row| row["result"]["outcome"]["kind"] == "refuted")
    }));
    assert!(queries.iter().any(|event| {
        event["name"] == "strongest_refutations"
            && !event["reply"]["result"]["refutations"]
                .as_array()
                .unwrap()
                .is_empty()
    }));
    assert!(
        queries.iter().any(|event| event["name"] == "countermodel"
            && event["reply"]["result"]["model"].is_object())
    );
    assert!(
        queries
            .iter()
            .any(|event| event["name"] == "evaluate_clauses"
                && event["arguments"]["instances"][0]["kind"] == "retained"
                && event["reply"]["result"]["results"][0]["holds"] == json!([false])),
        "the cached initialization countermodel actually falsifies the proposed E=empty clause"
    );
    assert!(queries.iter().any(|event| {
        event["name"] == "evaluate_clauses"
            && event["arguments"]["instances"][0]["kind"] == "supplied"
            && event["reply"]["result"]["results"]
                .as_array()
                .unwrap()
                .iter()
                .all(|row| row["admitted"] == true && row["holds"] == json!([true]))
    }));
    for observation in observations {
        let ledger: Vec<_> = queries
            .iter()
            .filter(|query| {
                query["coordinates"] == observation["coordinates"]
                    && query["name"] == "ledger"
                    && query["arguments"] == json!({})
            })
            .collect();
        assert!(
            ledger.len() >= 2,
            "each request brackets its queries with ledger reads"
        );
        assert_eq!(
            ledger.first().unwrap()["reply"],
            ledger.last().unwrap()["reply"],
            "semantic queries leave the ledger and revision unchanged"
        );
    }
    for query in queries
        .iter()
        .filter(|query| query["name"] == "evaluate_clauses")
    {
        let result = &query["reply"]["result"];
        assert_eq!(result["skipped"], json!([]));
        let source = &query["arguments"]["instances"][0];
        let expected = if source["kind"] == "retained" {
            json!([{"kind":"retained", "attempt":source["attempt"], "source_index":0}])
        } else {
            assert_eq!(source["kind"], "supplied");
            json!([{"kind":"supplied", "source_index":0}])
        };
        assert_eq!(result["instances"], expected);
        assert!(
            result["results"]
                .as_array()
                .unwrap()
                .iter()
                .all(|row| row["admitted"] == true)
        );
    }
    for (index, query) in queries.iter().enumerate() {
        let earlier: Vec<_> = queries[..index]
            .iter()
            .filter(|earlier| earlier["coordinates"] == query["coordinates"])
            .collect();
        if query["name"] == "history" {
            let clause = &query["arguments"]["clause"];
            assert!(
                earlier.iter().any(|earlier| earlier["name"] == "ledger"
                    && earlier["reply"]["result"]["items"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .any(|row| {
                            row.get("clause").or_else(|| row.get("target")) == Some(clause)
                        })),
                "history reference must come from the canonical ledger"
            );
        }
        if query["name"] == "countermodel" {
            let attempt = &query["arguments"]["attempt"];
            assert_eq!(query["reply"]["result"]["attempt"], *attempt);
            assert!(
                earlier.iter().any(|earlier| earlier["name"] == "history"
                    && earlier["reply"]["result"]["attempts"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .any(|row| {
                            row["result"]["attempt_id"] == *attempt
                                && row["result"]["outcome"]["kind"] == "refuted"
                        })),
                "saved model attempt must have been exposed by canonical history"
            );
        }
    }
    let search_elapsed = started.elapsed();

    let staging_root = fixture.directory.path().join("staging");
    let private_root = fixture.directory.path().join("private");
    let destination = fixture.directory.path().join("published/Certificate");
    assert!(
        !destination.exists(),
        "this gate must construct a fresh certificate"
    );
    fs::create_dir_all(&staging_root).unwrap();
    let SettlementParts {
        directory,
        task,
        admission,
        solver_admission,
        resources,
    } = fixture.into_settlement_parts();
    let settled = settle_search_outcome(
        outcome,
        SettlementPolicy {
            space_guard: None,
            admission: &admission,
            solver_admission: &solver_admission,
            pinned: &pinned,
            canonical_id: PRODUCTION_TASK_ID,
            input_namespace: "Whiel.Benchmark.Example0001",
            repository_root: support::repository_root(),
            staging_root,
            private_root,
            input_directory: directory.path().to_path_buf(),
            destination: destination.clone(),
            time_limit_seconds: 60,
            certification_limit: Duration::from_secs(900),
            concurrency: DEFAULT_CERTIFICATION_CONCURRENCY,
            fuel_policy: CounterexampleFuelPolicy::new(limits.counterexample_validation_limit())
                .unwrap(),
            // This run's own evidence is not this test's subject; drop it.
            retention: Retention::CertificateOnly,
            external_cancellation: &external_cancellation,
            hooks: CertificateBuildHooks::default(),
        },
        resources,
    )
    .await
    .expect("the real full-model API run certifies and settles");
    let SettledSearchOutcome::Valid(published) = settled else {
        panic!("the full-model API run must publish Valid: {settled:?}");
    };
    assert_eq!(published.certificate(), destination);
    assert!(destination.join("Valid.lean").is_file());
    // `Retention::CertificateOnly` (the default): no evidence directory is
    // kept anywhere under this run, not merely absent from the published
    // tree.
    assert!(!destination.join("VampireArtifacts").exists());
    assert!(!directory.path().join("CertificateEvidence").exists());
    let mut axioms = published.revalidation().axioms.clone();
    axioms.sort();
    assert_eq!(axioms, vec!["Classical.choice", "Quot.sound", "propext"]);
    assert_eq!(
        published.receipt().certificate_module,
        "Benchmark.Example0001.Certificate.Valid"
    );
    assert_eq!(published.receipt().jobs.len(), 5);
    assert!(
        published
            .receipt()
            .jobs
            .iter()
            .all(|job| job.profile.profile() == ProofSearchProfile::Direct)
    );
    let file_digest = |path: &Path| {
        let output = std::process::Command::new("shasum")
            .args(["-a", "256"])
            .arg(path)
            .output()
            .unwrap();
        assert!(output.status.success());
        String::from_utf8(output.stdout)
            .unwrap()
            .split_whitespace()
            .next()
            .unwrap()
            .to_owned()
    };
    eprintln!(
        "generic_api_fmb_receipt={}",
        json!({
            "fmb_enabled":true, "vampire_sha256":pinned.sha256(),
            "query_names":names, "requests":observations.len(),
            "canonical_queries":queries, "canonical_outcomes":trace.outcomes,
            "certificate_sha256":file_digest(&destination.join("Valid.lean")),
            "certificate_module":published.receipt().certificate_module, "certificate_jobs":published.receipt().jobs.len(),
            "axioms":axioms, "search_seconds":search_elapsed.as_secs_f64(), "total_seconds":started.elapsed().as_secs_f64(),
        })
    );
    // A certified run keeps both of its run records. Settlement freezes them
    // into the manifest it leaves behind, so the consultations this
    // certificate came out of stay readable beside the certificate itself.
    assert_settled_run_records(directory.path(), "valid");
    drop(task);
    drop(directory);
}

/// Assert that one settled run published both of its records under
/// `Retention::All`: the provider transcript's frames and the search's own
/// attempt history.
///
/// This is the shape every settlement leaves, whichever way the run ended;
/// the outcome label is the only part that differs.
fn assert_settled_run_records(artifact_root: &Path, outcome: &str) {
    let (run_root, manifest) = support::settled_run(artifact_root);
    let frames: Vec<Vec<u8>> = support::manifest_records(
        &manifest,
        "runtime_trace",
        &["root", CONSULTATION_RECORD_SCOPE],
    )
    .into_iter()
    .map(|record| support::retained_payload(&run_root, record))
    .collect();
    assert!(
        frames.len() >= 3,
        "a recorded run publishes a header, its events and a closure: {}",
        frames.len()
    );
    assert_eq!(support::transcript_record(&frames[0])["kind"], "header");
    assert_eq!(
        support::transcript_record(frames.last().unwrap())["kind"],
        "closed"
    );
    assert_settled_attempt_history(artifact_root, outcome);
}

/// Assert that one settled run published its attempt history, and return it.
///
/// The search publishes this from every terminal path, with or without a
/// provider recording, so a run with no transcript still keeps its rounds.
fn assert_settled_attempt_history(artifact_root: &Path, outcome: &str) -> Value {
    let (run_root, manifest) = support::settled_run(artifact_root);
    let records =
        support::manifest_records(&manifest, "runtime_trace", &["root", ATTEMPT_HISTORY_SCOPE]);
    assert_eq!(records.len(), 1, "one attempt history per run: {records:?}");
    let history: Value =
        serde_json::from_slice(&support::retained_payload(&run_root, records[0])).unwrap();
    assert_eq!(history["kind"], ATTEMPT_HISTORY_KIND);
    assert_eq!(history["version"], ATTEMPT_HISTORY_VERSION);
    assert_eq!(history["outcome"], outcome);
    assert!(history["ledger"].is_array());
    assert!(history["consultations"].is_array());
    history
}

/// The `Invalid` canary, end to end on a deterministic in-process provider.
///
/// One run: the provider submits an instance, Lean validates it against the
/// immutable input triple, the run ends `Invalid`, and
/// [`settle_search_outcome`] — the same production exit the `Valid` result
/// takes — binds the frozen record to the run's own fuel policy, writes
/// `Counterexample.json` beside the input, publishes the
/// `Certificate/Invalid.lean` tree revalidated at the exact negated input
/// type with an exactly-std3 audit, and shuts the run's resources down. The
/// durable record also rebuilds the same tree on its own, which is what the
/// certificate CLI's `--counterexample` mode does.
///
/// The two refusals that cannot happen inside one settled run — the forced
/// crash point between the two renames, and another result's record
/// standing beside the input — are exercised first, directly against
/// `publish_invalid`.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn live_invalid_canary_publishes_its_record_and_rebuilds_the_certificate_from_it() {
    // Two workers here and one in the `Valid` canary, so the publication
    // path is exercised at both pool sizes.
    let mut fixture = SearchFixture::for_task(
        "fixed_ambient_invalid_canary",
        REFUTABLE_TASK_ID,
        '8',
        worker_pool(2),
    )
    .await;
    // Search binds its own deadline; settlement needs a separate,
    // deadline-free external root for its certification allowance.
    let cancellation = CancellationToken::new();
    let external_cancellation = CancellationToken::new();
    // The checker never proves anything: a run that ends `Invalid` reaches
    // its result without consulting the solver lane at all.
    let runtime = fixture.runtime("unknown", &cancellation);
    let observed = Arc::new(Mutex::new(Vec::new()));
    let agent = Agent::with_default_policy(CounterexampleThenClauseProvider {
        instance: refutable_witness(),
        clause: LEVEL_ZERO_CLAUSE,
        observed: Arc::clone(&observed),
        consultations: Arc::new(AtomicUsize::new(0)),
    });
    let overall_limit = Duration::from_secs(120);
    // One authority for the call-local validation limit: the search applies
    // it, and the durable record states exactly it as its fuel policy.
    let limits = PreCertificateAgentHoudiniLimits::new(overall_limit, None, Some(4));
    let search = PreCertificateAgentHoudiniSearch::new(
        Arc::clone(&fixture.task),
        agent,
        fixture.houdini.take().unwrap(),
        runtime,
        limits,
        tokio::time::Instant::now() + overall_limit,
        AgentFeedbackPolicy::default(),
    )
    .unwrap();

    let outcome = search.run().await;
    let PreCertificateAgentHoudiniOutcome::Invalid(ref frozen) = outcome else {
        panic!("a validated counterexample must end the run invalid: {outcome:?}")
    };
    // The record's provenance is the consultation that submitted it.
    assert_eq!(
        frozen
            .consultation()
            .expect("a search-produced record names its consultation")
            .validation_ordinal(),
        0
    );

    let fuel_policy = CounterexampleFuelPolicy::new(limits.counterexample_validation_limit())
        .expect("the run's own validation limit is exactly representable");
    let durable = DurableCounterexampleRecord::new((**frozen).clone(), fuel_policy);
    let scope_identity = fixture.solver.scope().identity_sha256().to_string();
    let input_directory = fixture.directory.path().join("Example0013");
    fs::create_dir_all(&input_directory).unwrap();
    let staging_root = fixture.directory.path().join("staging");
    fs::create_dir_all(&staging_root).unwrap();
    let destination = input_directory.join("Certificate");
    let record_path = input_directory.join("Counterexample.json");

    // A malformed destination parent is now refused during early ownership
    // acquisition, before any certificate work or durable record write.
    fs::write(input_directory.join("blocked"), b"not a directory").unwrap();
    let early_refusal = publish_invalid(PublishInvalidRequest {
        space_guard: None,
        solver: &fixture.solver,
        admission: &fixture.solver_admission,
        record: &durable,
        input_namespace: "Whiel.Benchmark.Example0013",
        repository_root: support::repository_root(),
        staging_root: staging_root.clone(),
        input_directory: input_directory.clone(),
        destination: input_directory.join("blocked/Certificate"),
        external_cancellation: &external_cancellation,
        certification_limit: None,
        hooks: CertificateBuildHooks::default(),
    })
    .await
    .expect_err("a certificate that cannot be renamed into place is not published");
    assert!(
        matches!(&early_refusal, PublicationError::Io(_)),
        "{early_refusal}"
    );
    assert!(
        !record_path.exists(),
        "early ownership refusal writes no record"
    );
    assert_eq!(
        fs::read(input_directory.join("blocked")).unwrap(),
        b"not a directory"
    );
    assert!(staging_is_empty(&staging_root));

    // Inject a nonparticipating writer after the lease/existence checks.
    // The certificate is fully checked and its durable record is written,
    // then final publication refuses to replace this newly occupied leaf.
    // The surviving record alone still authorizes no certificate.
    let late_destination = input_directory.join("late/Certificate");
    let occupy_late = late_destination.clone();
    let interrupted = publish_invalid(PublishInvalidRequest {
        space_guard: None,
        solver: &fixture.solver,
        admission: &fixture.solver_admission,
        record: &durable,
        input_namespace: "Whiel.Benchmark.Example0013",
        repository_root: support::repository_root(),
        staging_root: staging_root.clone(),
        input_directory: input_directory.clone(),
        destination: late_destination.clone(),
        external_cancellation: &external_cancellation,
        certification_limit: None,
        hooks: CertificateBuildHooks {
            before_build: Some(Box::new(move |_| {
                fs::write(&occupy_late, b"late destination sentinel").unwrap();
            })),
            ..CertificateBuildHooks::default()
        },
    })
    .await
    .expect_err("a late occupied certificate destination is never replaced");
    assert!(
        matches!(&interrupted, PublicationError::DestinationExists(path) if path == &late_destination),
        "{interrupted}"
    );
    assert!(
        record_path.is_file(),
        "the durable record precedes the final certificate publication"
    );
    assert_eq!(
        fs::read(&late_destination).unwrap(),
        b"late destination sentinel"
    );
    assert!(!destination.exists(), "no certificate was published");
    assert!(
        staging_is_empty(&staging_root),
        "the unpublished tree is removed with its guard"
    );

    // Pass 7.5g review, finding 9: a byte-different record standing beside
    // the input is a content conflict — named as one, naming the instance
    // the standing record belongs to — not an occupied destination.
    let written = fs::read(&record_path).unwrap();
    let mut foreign: Value = serde_json::from_slice(&written).unwrap();
    foreign["instance_identity"] = json!("a".repeat(64));
    fs::write(&record_path, serde_json::to_vec_pretty(&foreign).unwrap()).unwrap();
    let conflict = publish_invalid(PublishInvalidRequest {
        space_guard: None,
        solver: &fixture.solver,
        admission: &fixture.solver_admission,
        record: &durable,
        input_namespace: "Whiel.Benchmark.Example0013",
        repository_root: support::repository_root(),
        staging_root: staging_root.clone(),
        input_directory: input_directory.clone(),
        destination: destination.clone(),
        external_cancellation: &external_cancellation,
        certification_limit: None,
        hooks: CertificateBuildHooks::default(),
    })
    .await
    .expect_err("one result never publishes over another result's record");
    assert!(
        matches!(&conflict, PublicationError::RecordConflict { path, existing }
            if path == &record_path && existing == &"a".repeat(64)),
        "{conflict}"
    );
    fs::write(&record_path, &written).unwrap();

    // The durable record alone rebuilds the same tree: read back from disk
    // and decoded strictly against this run's own task and scope. This is
    // what the certificate CLI's `--counterexample` mode does.
    let reread: Value = serde_json::from_slice(&written).unwrap();
    let rebuilt_record =
        DurableCounterexampleRecord::from_json(&reread, fixture.task.identity(), &scope_identity)
            .expect("the durable record decodes against its own run");
    assert_eq!(
        rebuilt_record.fuel_policy().validation_limit(),
        limits.counterexample_validation_limit(),
        "the record states the limit the validation actually ran under"
    );
    let rebuilt_directory = fixture.directory.path().join("Rebuilt");
    fs::create_dir_all(&rebuilt_directory).unwrap();
    let rebuilt = publish_invalid(PublishInvalidRequest {
        space_guard: None,
        solver: &fixture.solver,
        admission: &fixture.solver_admission,
        record: &rebuilt_record,
        input_namespace: "Whiel.Benchmark.Example0013",
        repository_root: support::repository_root(),
        staging_root: staging_root.clone(),
        input_directory: rebuilt_directory.clone(),
        destination: rebuilt_directory.join("Certificate"),
        external_cancellation: &external_cancellation,
        certification_limit: None,
        hooks: CertificateBuildHooks::default(),
    })
    .await
    .expect("the durable record rebuilds its own certificate");

    // Now the production path: the same terminal outcome, settled.
    let pinned = PinnedLeancheckVampire::from_lock(&support::repository_root())
        .expect("the repository-pinned leancheck Vampire resolves");
    let SettlementParts {
        directory,
        task,
        admission,
        solver_admission,
        resources,
    } = fixture.into_settlement_parts();
    let settled = settle_search_outcome(
        outcome,
        SettlementPolicy {
            space_guard: None,
            admission: &admission,
            solver_admission: &solver_admission,
            pinned: &pinned,
            canonical_id: REFUTABLE_TASK_ID,
            input_namespace: "Whiel.Benchmark.Example0013",
            repository_root: support::repository_root(),
            staging_root,
            private_root: directory.path().join("private"),
            input_directory: input_directory.clone(),
            destination: destination.clone(),
            time_limit_seconds: 60,
            certification_limit: Duration::from_secs(900),
            concurrency: DEFAULT_CERTIFICATION_CONCURRENCY,
            fuel_policy,
            // An `Invalid` result never had evidence to retain; the field
            // is read only on the `Valid` path.
            retention: Retention::CertificateOnly,
            external_cancellation: &external_cancellation,
            hooks: CertificateBuildHooks::default(),
        },
        resources,
    )
    .await
    .expect("a validated counterexample settles as a published Invalid result");
    let SettledSearchOutcome::Invalid(published) = settled else {
        panic!("a validated counterexample settles as a published Invalid result: {settled:?}")
    };

    // The record is beside the input. Every certificate body byte is
    // unchanged; the emitter banner is explicitly versioned.
    assert_eq!(published.record(), record_path);
    assert!(published.record().is_file());
    let promoted = fs::read(destination.join("Invalid.lean")).unwrap();
    let checked_in = expected_refutable_certificate_v2();
    assert_eq!(promoted, checked_in);
    // An `Invalid` result never had evidence to retain, `Retention` is read
    // only on the `Valid` path, and no evidence directory exists either way.
    assert!(!input_directory.join("CertificateEvidence").exists());
    let mut axioms = published.revalidation().axioms.clone();
    axioms.sort();
    assert_eq!(axioms, vec!["Classical.choice", "Quot.sound", "propext"]);
    assert!(published.receipt().jobs.is_empty(), "no solver ever ran");
    assert_eq!(
        fs::read(rebuilt.certificate().join("Invalid.lean")).unwrap(),
        promoted
    );
    assert_eq!(
        fs::read(rebuilt.record()).unwrap(),
        fs::read(published.record()).unwrap(),
        "the rebuilt record is the record it was rebuilt from"
    );

    drop(task);
    drop(directory);
}

/// How a resumed search's policy differs from the bound one.
#[derive(Clone, Copy)]
enum ResumeDrift {
    None,
    RetryLadder,
    PremiseRole,
}

/// The run policy is bound to the artifact store's run identity, and every
/// later entry into that run is checked against it.
///
/// The first search binds it and persists it into the run root, where a
/// manifest-driven reopen reads it back. An in-process resume — a second
/// search over the same artifact store — recomputes the policy from the
/// same live authorities and is refused when it has moved; the settled
/// manifest carries the same record. There is no cross-process search
/// resume in this milestone, so the reopen path is a read, not a resume.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn the_run_configuration_binds_the_run_identity_and_fails_a_drifted_resume() {
    let mut fixture =
        SearchFixture::new("fixed_ambient_run_configuration", '9', worker_pool(1)).await;
    let cancellation = CancellationToken::new();

    // Exactly the policy the fixture's authorities apply: a default
    // bound state sets no level bound
    // and no Core compression, every tool is enabled, and the store keeps
    // every payload.
    let probe = proof_only_production_config(
        &fixture.artifacts,
        &fixture.solver_admission,
        VampireWorkerCommand::new(support::fake_vampire())
            .with_extra_args([OsString::from("--fixture"), OsString::from("unknown")])
            .unwrap(),
        &cancellation,
    );
    let expected = RunConfiguration::new(
        false,
        None,
        Some(probe.retry_policy()),
        Some(probe.retry_premise_role()),
        &AgentToolPolicy::default(),
        fixture.artifacts.retention(),
    )
    .expect("every duration of the fixture's policy is exactly representable");
    assert_eq!(
        expected.retry_premise_role(),
        PremiseRole::NegatedConjecture,
        "the production default reaches the record"
    );

    let overall_limit = Duration::from_secs(20);
    let search = PreCertificateAgentHoudiniSearch::new(
        Arc::clone(&fixture.task),
        Agent::with_default_policy(ClauseProvider {
            clauses: vec![LEVEL_ZERO_CLAUSE],
            observed: Arc::new(Mutex::new(Vec::new())),
        }),
        fixture.houdini.take().unwrap(),
        fixture.runtime("unknown", &cancellation),
        PreCertificateAgentHoudiniLimits::new(overall_limit, None, Some(2)),
        tokio::time::Instant::now() + overall_limit,
        AgentFeedbackPolicy::default(),
    )
    .expect("the first search binds the run configuration");

    // Bound, and persisted into the run root where a reopen can read it.
    let bound = fixture
        .artifacts
        .run_configuration()
        .expect("the run is bound to a configuration");
    assert_eq!(bound, expected.to_json());
    let reopened = read_run_configuration(fixture.artifacts.run_root())
        .expect("the run root carries a readable configuration")
        .expect("a bound run has a configuration to reopen");
    assert_eq!(reopened, bound);
    assert_eq!(
        RunConfiguration::from_json(&reopened).expect("the reopened record decodes"),
        expected
    );

    let outcome = search.run().await;
    assert!(
        matches!(&outcome, PreCertificateAgentHoudiniOutcome::Failure(_)),
        "the unknown fixture cannot prove: {outcome:?}"
    );
    drop(outcome);

    // An in-process resume: a second search over the *same* artifact store.
    // Under the same policy it is accepted; under a moved one — a changed
    // solver retry allowance, or a changed retry premise role, each of
    // which decides which conditions a retry reaches — it is refused
    // before any work is done.
    // Every resume brings its own cancellation token: a token owns exactly
    // one absolute deadline, and the first search already bound this run's.
    let resume = |drift: ResumeDrift,
                  houdini: LeveledHoudiniState,
                  admission: &FrameworkIIAdmissionContext,
                  solver: &FrameworkIISolverContext,
                  solver_admission: &SolverAdmission| {
        let resumed = CancellationToken::new();
        let config = proof_only_production_config(
            &fixture.artifacts,
            solver_admission,
            VampireWorkerCommand::new(support::fake_vampire())
                .with_extra_args([OsString::from("--fixture"), OsString::from("unknown")])
                .unwrap(),
            &resumed,
        );
        let config = match drift {
            ResumeDrift::None => config,
            ResumeDrift::RetryLadder => config.with_retry_policy(
                whiel_runner::FrameworkIIRetryPolicy::new([Duration::from_secs(31)]).unwrap(),
            ),
            ResumeDrift::PremiseRole => config.with_retry_premise_role(PremiseRole::Axiom),
        };
        let checker = solver.clone().production_checker(config);
        let runtime = PreCertificateAgentHoudiniRuntime::new(
            admission.clone(),
            solver.clone(),
            solver_admission.clone(),
            checker,
            fixture.artifacts.clone(),
            resumed.clone(),
            AgentToolPolicy::default(),
        );
        PreCertificateAgentHoudiniSearch::new(
            Arc::clone(&fixture.task),
            Agent::new(
                ClauseProvider {
                    clauses: vec![LEVEL_ZERO_CLAUSE],
                    observed: Arc::new(Mutex::new(Vec::new())),
                },
                AgentConsultationPolicy::new(AgentConsultationLimits::default()).unwrap(),
            ),
            houdini,
            runtime,
            PreCertificateAgentHoudiniLimits::new(overall_limit, None, Some(2)),
            tokio::time::Instant::now() + overall_limit,
            AgentFeedbackPolicy::default(),
        )
    };

    let solver_admission = agent_admission(1, 1);
    let rebound = bind_task(
        PRODUCTION_TASK_ID,
        worker_pool(1),
        '9',
        None,
        &solver_admission,
        &cancellation,
    )
    .await;
    let (_task, admission, solver, houdini) = rebound.into_parts();

    let drifted = match resume(
        ResumeDrift::RetryLadder,
        houdini,
        &admission,
        &solver,
        &solver_admission,
    ) {
        Ok(_) => panic!("a resume under a changed retry policy must be refused"),
        Err(report) => report,
    };
    assert!(
        drifted
            .detail()
            .is_some_and(|detail| detail.contains("run configuration")),
        "{drifted:?}"
    );

    // The premise role is bound on the same footing: the same ladder under
    // the other rendering is a different search, not a resume of this one.
    let rebound = bind_task(
        PRODUCTION_TASK_ID,
        worker_pool(1),
        '9',
        None,
        &solver_admission,
        &cancellation,
    )
    .await;
    let (_task, role_admission, role_solver, houdini) = rebound.into_parts();
    let role_drifted = match resume(
        ResumeDrift::PremiseRole,
        houdini,
        &role_admission,
        &role_solver,
        &solver_admission,
    ) {
        Ok(_) => panic!("a resume under a changed retry premise role must be refused"),
        Err(report) => report,
    };
    assert!(
        role_drifted
            .detail()
            .is_some_and(|detail| detail.contains("run configuration")),
        "{role_drifted:?}"
    );
    role_solver.shutdown().await.unwrap();

    let rebound = bind_task(
        PRODUCTION_TASK_ID,
        worker_pool(1),
        '9',
        None,
        &solver_admission,
        &cancellation,
    )
    .await;
    let (_task, admission, second_solver, houdini) = rebound.into_parts();
    let accepted = resume(
        ResumeDrift::None,
        houdini,
        &admission,
        &second_solver,
        &solver_admission,
    )
    .expect("a resume under the same policy is accepted");
    drop(accepted);

    solver.shutdown().await.unwrap();
    second_solver.shutdown().await.unwrap();

    // Settled by hand rather than through `SearchFixture::settle`, so the
    // run root outlives settlement long enough to read its manifest.
    let SearchFixture {
        directory,
        task,
        admission: fixture_admission,
        solver: fixture_solver,
        houdini,
        solver_admission: fixture_solver_admission,
        artifacts,
        owner,
    } = fixture;
    let run_root = artifacts.run_root().to_path_buf();
    drop(houdini);
    fixture_solver.shutdown().await.unwrap();
    drop(fixture_solver);
    drop(fixture_admission);
    drop(fixture_solver_admission);
    drop(task);
    drop(artifacts);
    owner.settle().unwrap();

    // The settled manifest carries the same record.
    let manifest: Value =
        serde_json::from_slice(&fs::read(run_root.join("manifest.json")).unwrap()).unwrap();
    assert_eq!(manifest["run_configuration"], expected.to_json());
    drop(directory);
}

struct TerminalCorrectionProvider {
    oversized: bool,
    observed: Arc<Mutex<Vec<ObservedProviderRequest>>>,
}
impl AgentProvider for TerminalCorrectionProvider {
    fn consult<'a>(
        &'a mut self,
        push: &'a AgentPush,
        _tools: &'a dyn AgentToolSurface,
        response: &'a mut AgentResponseWriter,
        _cancellation: AgentSourceCancellation,
    ) -> AgentSourceFuture<'a> {
        observe(&self.observed, push);
        Box::pin(async move {
            if self.oversized {
                assert!(response.write_chunk(b"1234").is_ok());
                assert!(response.write_chunk(b"56789").is_err());
            } else {
                assert!(response.write_chunk(b"{malformed").is_ok());
            }
            AgentSourceOutcome::Response
        })
    }
    fn quiesce_request(&mut self) -> whiel_runner::proposer_api::ProposerCleanupFuture<'_> {
        Box::pin(async { Ok(()) })
    }
    fn shutdown(
        &mut self,
        _reason: whiel_runner::proposer_api::wire::ShutdownReason,
    ) -> whiel_runner::proposer_api::ProposerCleanupFuture<'_> {
        self.quiesce_request()
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn live_recording_captures_both_terminal_correction_sites_without_another_push() {
    let directory = support::TestDir::new("fixed_ambient_terminal_recorded_corrections");
    let solver_admission = agent_admission(1, 1);
    let cancellation = CancellationToken::new();
    let bound = bind(worker_pool(1), 'a', None, &solver_admission, &cancellation).await;
    let (task, admission, solver, houdini) = bound.into_parts();
    for oversized in [false, true] {
        let (owner, artifacts) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(directory.path().join(if oversized {
                "oversized"
            } else {
                "malformed"
            })),
        )
        .unwrap();
        let feedback_policy =
            AgentFeedbackPolicy::new(whiel_runner::framework2::AgentFeedbackLimits {
                host_limits: if oversized {
                    HostLimits {
                        reply_bytes: Some(8),
                        ..HostLimits::UNBOUNDED
                    }
                } else {
                    HostLimits::UNBOUNDED
                },
                ..Default::default()
            })
            .unwrap();
        let feedback_state = PreCertificateAgentHoudiniState::new(
            Arc::clone(&task),
            &artifacts,
            &houdini,
            Duration::from_secs(30),
            feedback_policy,
        )
        .unwrap();
        let feedback = feedback_state.feedback();
        let policy = AgentConsultationPolicy::new(AgentConsultationLimits {
            max_attempt_history_records: 1,
            max_transport_retries_per_request: 0,
            ..Default::default()
        })
        .unwrap();
        let recorder = recording_fixture(&task, feedback, &policy);
        let observed = Arc::new(Mutex::new(Vec::new()));
        let mut agent = RecordingProvider::agent(
            TerminalCorrectionProvider {
                oversized,
                observed: Arc::clone(&observed),
            },
            policy,
            recorder.clone(),
        );
        let validator = AgentResponseValidator::new(
            &task,
            &houdini,
            &admission,
            &solver,
            &solver_admission,
            &feedback_state,
            None,
        );
        let result = agent
            .get_houdini_proposal(feedback, &validator, &cancellation)
            .await
            .unwrap();
        assert!(matches!(result, HoudiniProposal::Failure(_)));
        let recording = verify_recording(&recorder, &artifacts, &observed);
        let pushes = recording
            .events()
            .iter()
            .filter(|event| {
                matches!(
                    event,
                    TranscriptEvent::Bytes {
                        stream: TranscriptStream::Push,
                        ..
                    }
                )
            })
            .count();
        let corrections: Vec<_> = recording
            .events()
            .iter()
            .filter_map(|event| match event {
                TranscriptEvent::Bytes {
                    stream: TranscriptStream::Correction,
                    bytes,
                    coordinates,
                    ..
                } => Some((bytes, coordinates)),
                _ => None,
            })
            .collect();
        assert_eq!(pushes, 1);
        assert_eq!(corrections.len(), 1);
        assert_eq!(
            (
                corrections[0].1.consultation,
                corrections[0].1.validation,
                corrections[0].1.transport
            ),
            (0, 0, 0)
        );
        let correction: Value = serde_json::from_slice(corrections[0].0).unwrap();
        assert_eq!(correction["binding"]["correction_ordinal"], 1);
        assert_eq!(
            agent.attempt_history()[0].outcome(),
            if oversized {
                AgentRequestAttemptOutcome::OversizedResponse
            } else {
                AgentRequestAttemptOutcome::Correctable
            }
        );
        drop(agent);
        drop(feedback_state);
        drop(artifacts);
        owner.settle().unwrap();
    }
    drop(houdini);
    solver.shutdown().await.unwrap();
    drop(solver);
    drop(admission);
}

fn verify_recorded_owner_correspondence(
    recording: &VerifiedTranscript,
    observed: &Mutex<Vec<ObservedProviderRequest>>,
    recorder: &TranscriptRecorder,
) {
    let observed = observed.lock().unwrap();
    let final_owner = recorder.final_state_owner();
    compare_fresh_recordings(
        recording,
        recording,
        &observed,
        &observed,
        final_owner.as_deref(),
    );
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn replay_correspondence_checks_fresh_native_routes_and_every_recorded_byte() {
    async fn run(
        label: &str,
        digit: char,
        command: VampireWorkerCommand,
    ) -> (
        VerifiedTranscript,
        Vec<ObservedProviderRequest>,
        Option<Arc<whiel_runner::framework2::ReplayFinalStateOwner>>,
    ) {
        let directory = support::TestDir::new(label);
        let solver_admission = agent_admission(1, 1);
        let cancellation = CancellationToken::new();
        let (task, admission, solver, houdini) = bind(
            worker_pool(1),
            digit,
            None,
            &solver_admission,
            &cancellation,
        )
        .await
        .into_parts();
        let (owner, artifacts) =
            new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
        let checker = solver.clone().production_checker(production_config(
            &artifacts,
            &solver_admission,
            FmbOptions::default(),
            command,
            &cancellation,
        ));
        let runtime = PreCertificateAgentHoudiniRuntime::new(
            admission.clone(),
            solver.clone(),
            solver_admission.clone(),
            checker,
            artifacts.clone(),
            cancellation.clone(),
            AgentToolPolicy::default(),
        );
        let observed = Arc::new(Mutex::new(Vec::new()));
        let policy = AgentConsultationPolicy::default();
        let feedback = PreCertificateAgentHoudiniState::new(
            Arc::clone(&task),
            &artifacts,
            &houdini,
            Duration::from_secs(30),
            AgentFeedbackPolicy::default(),
        )
        .unwrap();
        let recorder = recording_fixture(&task, feedback.feedback(), &policy);
        drop(feedback);
        let provider = VetoAndToolsProvider {
            round: 0,
            observed: Arc::clone(&observed),
            tool_responses: Arc::new(Mutex::new(Vec::new())),
        };
        let agent = RecordingProvider::agent(provider, policy, recorder.clone());
        let limit = Duration::from_secs(30);
        let search = PreCertificateAgentHoudiniSearch::new(
            Arc::clone(&task),
            agent,
            houdini,
            runtime,
            PreCertificateAgentHoudiniLimits::new(limit, None, Some(8)),
            tokio::time::Instant::now() + limit,
            AgentFeedbackPolicy::default(),
        )
        .unwrap();
        let _outcome = search.run().await;
        let recording = verify_recording(&recorder, &artifacts, &observed);
        let pushes = observed.lock().unwrap().clone();
        assert!(pushes.len() >= 3);
        solver.shutdown().await.unwrap();
        drop(solver);
        drop(admission);
        drop(artifacts);
        owner.settle().unwrap();
        (recording, pushes, recorder.final_state_owner())
    }
    let fixture = support::TestDir::new("replay_fresh_route_command");
    let command = termination_refuting_vampire(fixture.path());
    let (recorded, old_pushes, _) = run("replay_fresh_route_old", 'd', command.clone()).await;
    fs::write(fixture.path().join("termination-model-vampire.state"), b"").unwrap();
    let (live, live_pushes, final_owner) = run("replay_fresh_route_live", 'e', command).await;
    assert_ne!(old_pushes[0].digest, live_pushes[0].digest);
    assert_ne!(
        recorded.header().source_run_identity,
        live.header().source_run_identity
    );
    compare_fresh_recordings(
        &recorded,
        &live,
        &old_pushes,
        &live_pushes,
        final_owner.as_deref(),
    );
}

fn compare_fresh_recordings(
    recorded: &VerifiedTranscript,
    live: &VerifiedTranscript,
    old_pushes: &[ObservedProviderRequest],
    pushes: &[ObservedProviderRequest],
    final_owner: Option<&whiel_runner::framework2::ReplayFinalStateOwner>,
) {
    use whiel_runner::framework2::replay_audit::decode_comparison_log;
    use whiel_runner::framework2::{ReplayCorrespondenceV1, ReplayResponseChunk};
    let mut graph = ReplayCorrespondenceV1::new();
    let mut owner = None;
    let mut requests = None::<(
        whiel_runner::framework2::TranscriptCoordinates,
        String,
        String,
    )>;
    let mut chunks = (
        Vec::<ReplayResponseChunk>::new(),
        Vec::<ReplayResponseChunk>::new(),
    );
    let mut push_index = 0;
    let mut tool_count = 0;
    let flush =
        |graph: &mut ReplayCorrespondenceV1,
         requests: &Option<(
            whiel_runner::framework2::TranscriptCoordinates,
            String,
            String,
        )>,
         chunks: &mut (Vec<ReplayResponseChunk>, Vec<ReplayResponseChunk>)| {
            if !chunks.0.is_empty() {
                let (coordinates, old, live) = requests.as_ref().unwrap();
                graph
                    .compare_response_chunks(*coordinates, old, live, &chunks.0, &chunks.1)
                    .unwrap();
                chunks.0.clear();
                chunks.1.clear();
            }
        };
    assert_eq!(recorded.events().len(), live.events().len());
    for (old, current) in recorded.events().iter().zip(live.events()) {
        match (old, current) {
            (
                TranscriptEvent::FinalOwnerProjection { projection },
                TranscriptEvent::FinalOwnerProjection {
                    projection: live_projection,
                },
            ) => {
                flush(&mut graph, &requests, &mut chunks);
                let actual = final_owner
                    .expect("actual search completion retains its fresh comparison owner");
                assert_eq!(actual.projection(), live_projection.as_ref());
                let exact = serde_json::to_value(projection).unwrap();
                assert_eq!(exact["version"], 2);
                assert_eq!(
                    exact["request_policy"]["domain"],
                    "whiel-proposer-request-policy-v1"
                );
                assert_eq!(
                    exact["feedback_policy"]["domain"],
                    "whiel-proposer-feedback-policy-v1"
                );
                assert!(exact["request_policy"].get("session_mode").is_none());
                for (path, old) in [
                    ("/version", json!(1)),
                    (
                        "/request_policy/domain",
                        json!("whiel-agent-consultation-policy-v4"),
                    ),
                    (
                        "/feedback_policy/domain",
                        json!("whiel-agent-feedback-policy-v4"),
                    ),
                    ("/run_configuration/version", json!(2)),
                ] {
                    let mut stale = exact.clone();
                    if let Some(slot) = stale.pointer_mut(path) {
                        *slot = old;
                        assert!(
                            serde_json::from_value::<
                                whiel_runner::framework2::ReplayFinalStateProjection,
                            >(stale)
                            .is_err(),
                            "{path}"
                        );
                    }
                }
                let before = graph.comparison_log().ok().cloned();
                let mut changed = serde_json::to_value(projection).unwrap();
                match changed["outcome"]["kind"].as_str().unwrap() {
                    "valid" => changed["outcome"]["evidence_identity"] = json!("0".repeat(64)),
                    "invalid" => {
                        changed["outcome"]["fuel_consumed"] =
                            json!(changed["outcome"]["fuel_consumed"].as_u64().unwrap() + 1)
                    }
                    "failure" => {
                        changed["outcome"]["failure"]["retryable"] = json!(
                            !changed["outcome"]["failure"]["retryable"]
                                .as_bool()
                                .unwrap()
                        )
                    }
                    _ => unreachable!(),
                }
                let changed = serde_json::from_value(changed).unwrap();
                assert!(graph.compare_final_state(&changed, actual).is_err());
                assert_eq!(graph.comparison_log().ok().cloned(), before);
                graph.compare_final_state(projection, actual).unwrap();
                assert!(graph.compare_final_state(projection, actual).is_err());
                if push_index == 0 {
                    graph
                        .bind_headers(recorded.header(), live.header())
                        .unwrap();
                }
            }
            (TranscriptEvent::FinalOwnerUnavailable { reason }, _) => {
                panic!("actual final owner unavailable: {reason:?}")
            }
            (
                TranscriptEvent::OwnerProjection {
                    coordinates: a,
                    projection,
                    ..
                },
                TranscriptEvent::OwnerProjection { coordinates: b, .. },
            ) => {
                assert_eq!(a, b);
                flush(&mut graph, &requests, &mut chunks);
                let exact = serde_json::to_value(projection).unwrap();
                assert_eq!(exact["version"], 2);
                assert_eq!(exact["feedback"]["version"], 2);
                assert!(exact["request_policy"].get("session_mode").is_none());
                assert_eq!(
                    exact["feedback"]["session_digest"].as_str().unwrap().len(),
                    64
                );
                for (path, old) in [
                    ("/version", json!(1)),
                    ("/feedback/version", json!(1)),
                    (
                        "/request_policy/domain",
                        json!("whiel-agent-consultation-policy-v4"),
                    ),
                    (
                        "/feedback/policy/domain",
                        json!("whiel-agent-feedback-policy-v4"),
                    ),
                    ("/feedback/run_configuration/version", json!(2)),
                ] {
                    let mut stale = exact.clone();
                    if let Some(slot) = stale.pointer_mut(path) {
                        *slot = old;
                        assert!(serde_json::from_value::<whiel_runner::framework2::ReplayPushProjection>(stale).is_err(), "{path}");
                    }
                }
                let mut stale_names = exact.clone();
                let policy = stale_names
                    .as_object_mut()
                    .unwrap()
                    .remove("request_policy")
                    .unwrap();
                stale_names["agent_policy"] = policy;
                assert!(
                    serde_json::from_value::<whiel_runner::framework2::ReplayPushProjection>(
                        stale_names
                    )
                    .is_err()
                );
                owner = Some(projection.as_ref());
            }
            (TranscriptEvent::OwnerUnavailable { reason, .. }, _) => {
                panic!("actual wrapped fixture lost owner evidence: {reason:?}")
            }
            (
                TranscriptEvent::Bytes {
                    coordinates: a,
                    stream: TranscriptStream::Push,
                    bytes,
                    ..
                },
                TranscriptEvent::Bytes {
                    coordinates: b,
                    stream: TranscriptStream::Push,
                    bytes: live_bytes,
                    ..
                },
            ) => {
                assert_eq!(a, b);
                let actual = &pushes[push_index].push;
                assert_eq!(actual.bytes(), live_bytes);
                assert_eq!(old_pushes[push_index].bytes, *bytes);
                graph
                    .compare_push(*a, owner.take().unwrap(), bytes, actual)
                    .unwrap_or_else(|error| panic!("fresh owner push {push_index}: {error:?}"));
                if push_index == 0 {
                    graph
                        .bind_headers(recorded.header(), live.header())
                        .unwrap();
                }
                requests = Some((
                    *a,
                    old_pushes[push_index].digest.clone(),
                    actual.digest().to_owned(),
                ));
                push_index += 1;
            }
            (
                TranscriptEvent::Bytes {
                    coordinates: a,
                    stream: TranscriptStream::Response,
                    bytes,
                    accounting,
                    ..
                },
                TranscriptEvent::Bytes {
                    coordinates: b,
                    stream: TranscriptStream::Response,
                    bytes: live_bytes,
                    accounting: live_accounting,
                    ..
                },
            ) => {
                assert_eq!(a, b);
                assert_eq!(requests.as_ref().unwrap().0, *a);
                chunks.0.push(ReplayResponseChunk {
                    bytes: bytes.clone(),
                    accounting: accounting.clone().unwrap(),
                });
                chunks.1.push(ReplayResponseChunk {
                    bytes: live_bytes.clone(),
                    accounting: live_accounting.clone().unwrap(),
                });
            }
            (
                TranscriptEvent::Bytes {
                    coordinates: a,
                    stream: TranscriptStream::Correction,
                    bytes,
                    ..
                },
                TranscriptEvent::Bytes {
                    coordinates: b,
                    stream: TranscriptStream::Correction,
                    bytes: live_bytes,
                    ..
                },
            ) => {
                assert_eq!(a, b);
                flush(&mut graph, &requests, &mut chunks);
                graph.compare_correction(*a, bytes, live_bytes).unwrap();
            }
            (
                TranscriptEvent::ToolCall {
                    coordinates: a,
                    call_id: i,
                    name,
                    arguments,
                },
                TranscriptEvent::ToolCall {
                    coordinates: b,
                    call_id: j,
                    name: live_name,
                    arguments: live_arguments,
                },
            ) => {
                assert_eq!((a, i, name), (b, j, live_name));
                graph
                    .compare_tool_call(*a, *i, name, arguments, live_arguments)
                    .unwrap();
                tool_count += 1;
            }
            (
                TranscriptEvent::ToolResponse {
                    coordinates: a,
                    call_id: i,
                    response,
                },
                TranscriptEvent::ToolResponse {
                    coordinates: b,
                    call_id: j,
                    response: live_response,
                },
            ) => {
                assert_eq!((a, i), (b, j));
                graph
                    .compare_tool_response(*a, *i, response, live_response)
                    .unwrap();
            }
            _ => assert_eq!(
                old, current,
                "every other lifecycle/outcome/event remains exact"
            ),
        }
    }
    flush(&mut graph, &requests, &mut chunks);
    assert_eq!(push_index, pushes.len());
    assert!(push_index > 0 || final_owner.is_some());
    assert_eq!(push_index, old_pushes.len());
    let audit = graph.comparison_log().unwrap();
    assert!(graph.comparison_log_bytes(0).is_err());
    let bytes = graph.comparison_log_bytes(4 * 1024 * 1024).unwrap();
    assert_eq!(&decode_comparison_log(&bytes, bytes.len()).unwrap(), audit);
    assert!(!audit.identity_pairs.is_empty());
    eprintln!(
        "replay owner coverage: {push_index} pushes, {tool_count} tool calls, {} checked identity pairs, {} exact traffic comparisons",
        audit.identity_pairs.len(),
        audit.comparisons.len()
    );
}

// This provider depends only on the public proposer facade. It needs no MCP,
// native agent, skills, historical harness code, or engine checker handle.
struct SemanticApiProbe {
    exercise_bad_inputs: bool,
    replies: Arc<Mutex<Vec<(String, Value)>>>,
}

fn supplied_api_instance(request: &whiel_runner::proposer_api::ProposerPush) -> Value {
    let relations = request
        .observation()
        .feedback
        .presentation
        .ambient_schema
        .relations
        .iter()
        .map(|relation| {
            json!({"name": relation.key, "rows": if relation.key == "o:p::T" {
            vec![vec!["num:0"; relation.arity as usize]]
        } else { vec![] }})
        })
        .collect::<Vec<_>>();
    json!({"carrier_keys":["num:0"], "relations":relations})
}

impl whiel_runner::proposer_api::Proposer for SemanticApiProbe {
    fn quiesce_request(&mut self) -> whiel_runner::proposer_api::ProposerCleanupFuture<'_> {
        Box::pin(async { Ok(()) })
    }
    fn shutdown(
        &mut self,
        _reason: whiel_runner::proposer_api::wire::ShutdownReason,
    ) -> whiel_runner::proposer_api::ProposerCleanupFuture<'_> {
        self.quiesce_request()
    }

    fn consult<'a>(
        &'a mut self,
        request: &'a whiel_runner::proposer_api::ProposerPush,
        queries: &'a dyn whiel_runner::proposer_api::ProposerQueries,
        response: &'a mut whiel_runner::proposer_api::AgentResponseWriter,
        _cancellation: whiel_runner::proposer_api::AgentSourceCancellation,
    ) -> whiel_runner::proposer_api::AgentSourceFuture<'a> {
        Box::pin(async move {
            assert_eq!(
                request.negotiated_api().version,
                whiel_runner::proposer_api::API_VERSION
            );
            let canonical_before = request.bytes().to_vec();
            let instance = supplied_api_instance(request);
            let evaluate = |instance: Value| {
                json!({"clauses":[LEVEL_ZERO_CLAUSE, LEVEL_ONE_CLAUSE],
                "instances":[{"kind":"supplied","instance":instance}]})
            };
            let mut cases = vec![
                (
                    "validate",
                    "validate_clauses",
                    json!({"clauses":[LEVEL_ZERO_CLAUSE,"bad formula"]}),
                ),
                ("evaluate", "evaluate_clauses", evaluate(instance.clone())),
            ];
            if self.exercise_bad_inputs {
                let mut empty_tables = instance.clone();
                for relation in empty_tables["relations"].as_array_mut().unwrap() {
                    relation["rows"] = json!([]);
                }
                cases.push(("empty_tables", "evaluate_clauses", evaluate(empty_tables)));
                cases.push((
                    "duplicates",
                    "evaluate_clauses",
                    json!({"clauses":[LEVEL_ZERO_CLAUSE],
                    "instances":[{"kind":"supplied","instance":instance.clone()},
                                 {"kind":"supplied","instance":instance.clone()}]}),
                ));
                cases.push((
                    "all_retained",
                    "evaluate_clauses",
                    json!({"clauses":[LEVEL_ZERO_CLAUSE],"instances":"all_retained"}),
                ));
                cases.push((
                    "no_instances",
                    "evaluate_clauses",
                    json!({"clauses":[LEVEL_ZERO_CLAUSE],"instances":[]}),
                ));
                cases.push((
                    "missing_selection",
                    "evaluate_clauses",
                    json!({"clauses":[]}),
                ));
                cases.push((
                    "null_selection",
                    "evaluate_clauses",
                    json!({"clauses":[],"instances":null}),
                ));
                cases.push((
                    "old_validation",
                    "validate_clauses",
                    json!({"clauses":[],"instances":[]}),
                ));
                cases.push((
                    "unknown_retained",
                    "evaluate_clauses",
                    json!({"clauses":[],"instances":[{"kind":"retained","attempt":9999}]}),
                ));
                for invalid in [
                    "missing_relation",
                    "duplicate_relation",
                    "wrong_arity",
                    "bad_key",
                    "empty_carrier",
                    "missing_cell",
                    "duplicate_row",
                    "unknown_relation",
                ] {
                    let mut bad = instance.clone();
                    match invalid {
                        "missing_relation" => {
                            bad["relations"].as_array_mut().unwrap().pop();
                        }
                        "duplicate_relation" => {
                            let row = bad["relations"][0].clone();
                            bad["relations"].as_array_mut().unwrap().push(row);
                        }
                        "wrong_arity" => {
                            bad["relations"][0]["rows"] = json!([["num:0"]]);
                        }
                        "bad_key" => {
                            bad["carrier_keys"] = json!(["not a canonical key"]);
                        }
                        "empty_carrier" => {
                            bad["carrier_keys"] = json!([]);
                        }
                        "missing_cell" => {
                            bad["carrier_keys"] = json!(["num:1"]);
                        }
                        "duplicate_row" => {
                            bad["relations"][0]["rows"] =
                                json!([["num:0", "num:0"], ["num:0", "num:0"]]);
                        }
                        "unknown_relation" => {
                            bad["relations"][0]["name"] = json!("unknown");
                        }
                        _ => unreachable!(),
                    }
                    let mut args = evaluate(bad);
                    if invalid == "empty_carrier" {
                        args["clauses"] = json!([]);
                    }
                    cases.push((invalid, "evaluate_clauses", args));
                }
            }
            for (label, name, args) in cases {
                let reply = serde_json::to_value(queries.call(name, args).await).unwrap();
                // Every result is consumable by the public closed DTO schema.
                let _: whiel_runner::proposer_api::query_results::ToolResponseV1 =
                    serde_json::from_value(reply.clone()).unwrap();
                self.replies.lock().unwrap().push((label.into(), reply));
            }
            assert_eq!(request.bytes(), canonical_before);
            let bytes = serde_json::to_vec(&request.candidate_clauses_example().unwrap()).unwrap();
            response.write_chunk(&bytes).unwrap();
            whiel_runner::proposer_api::AgentSourceOutcome::Response
        })
    }
}

async fn semantic_api_probe(
    policy: AgentToolPolicy,
    evaluation_cost: Option<u64>,
    bad_inputs: bool,
) -> Vec<(String, Value)> {
    let directory = support::TestDir::new("public_semantic_api");
    let launch_log = directory.path().join("unwanted-vampire-launches");
    let admission_budget = agent_admission(1, 1);
    let cancellation = CancellationToken::new();
    let host_limits = HostLimits {
        evaluation_cost,
        ..HostLimits::UNBOUNDED
    };
    let bound = bind_fixed_ambient_framework_ii(
        fixture_descriptor(),
        worker_pool(1),
        "7".repeat(64),
        host_limits,
        false,
        policy,
        &admission_budget,
        &cancellation,
    )
    .await
    .unwrap();
    let (task, admission, solver, houdini) = bound.into_parts();
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let checker = solver
        .clone()
        .production_checker(proof_only_production_config(
            &artifacts,
            &admission_budget,
            proof_vampire(&launch_log),
            &cancellation,
        ));
    let feedback = PreCertificateAgentHoudiniState::new(
        Arc::clone(&task),
        &artifacts,
        &houdini,
        Duration::from_secs(30),
        AgentFeedbackPolicy::new(whiel_runner::framework2::AgentFeedbackLimits {
            host_limits,
            ..whiel_runner::framework2::AgentFeedbackLimits::default()
        })
        .unwrap(),
    )
    .unwrap();
    let before = format!("{houdini:?}");
    let catalog_ordinal = houdini.catalog().next_batch_ordinal().unwrap();
    let dictionary = checker.dictionary_entry_summary();
    let replies = Arc::new(Mutex::new(Vec::new()));
    let mut proposer = Agent::new(
        SemanticApiProbe {
            exercise_bad_inputs: bad_inputs,
            replies: Arc::clone(&replies),
        },
        AgentConsultationPolicy::default(),
    );
    let validator = AgentResponseValidator::new(
        &task,
        &houdini,
        &admission,
        &solver,
        &admission_budget,
        &feedback,
        Some(&checker),
    );
    let result = proposer
        .get_houdini_proposal(feedback.feedback(), &validator, &cancellation)
        .await
        .unwrap();
    assert!(
        matches!(result, HoudiniProposal::CandidateClauses(_)),
        "{result:?}"
    );
    assert_eq!(
        format!("{houdini:?}"),
        before,
        "queries must preserve every runtime state field"
    );
    assert_eq!(houdini.catalog().len().unwrap(), 0);
    assert_eq!(
        houdini.catalog().next_batch_ordinal().unwrap(),
        catalog_ordinal
    );
    assert_eq!(checker.dictionary_entry_summary(), dictionary);
    assert!(!launch_log.exists(), "semantic drafts never run Vampire");
    drop(proposer);
    solver.shutdown().await.unwrap();
    drop(checker);
    drop(solver);
    drop(admission);
    drop(feedback);
    drop(artifacts);
    owner.settle().unwrap();
    Arc::try_unwrap(replies).unwrap().into_inner().unwrap()
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn public_proposer_api_evaluates_supplied_instances_without_houdini_effects() {
    let replies = semantic_api_probe(AgentToolPolicy::default(), None, true).await;
    for (label, reply) in replies {
        match label.as_str() {
            "validate" => {
                assert_eq!(
                    reply["result"]["results"][0],
                    json!({"source":LEVEL_ZERO_CLAUSE,"admitted":true})
                );
                assert_eq!(reply["result"]["results"][1]["admitted"], false);
            }
            "evaluate" => {
                assert_eq!(
                    reply["result"]["results"][0]["holds"],
                    json!([false]),
                    "{reply}"
                );
                assert_eq!(reply["result"]["results"][1]["holds"], json!([true]));
                assert_eq!(
                    reply["result"]["instances"],
                    json!([{"kind":"supplied","source_index":0}])
                );
                assert_eq!(reply["result"]["cost"], 2);
            }
            "empty_tables" => {
                assert_eq!(reply["result"]["results"][0]["holds"], json!([true]));
            }
            "duplicates" => {
                assert_eq!(
                    reply["result"]["results"][0]["holds"],
                    json!([false, false])
                );
                assert_eq!(reply["result"]["instances"].as_array().unwrap().len(), 2);
            }
            "all_retained" | "no_instances" => {
                assert_eq!(reply["result"]["results"][0]["holds"], json!([]));
            }
            "missing_selection" | "null_selection" | "old_validation" => {
                assert_eq!(
                    reply["error"]["code"], "invalid_arguments",
                    "{label}: {reply}"
                );
            }
            "unknown_retained" => {
                assert_eq!(reply["error"]["code"], "no_refutation");
            }
            _ => {
                assert_eq!(
                    reply["error"]["code"], "invalid_instance",
                    "{label}: {reply}"
                );
            }
        }
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn public_proposer_api_has_independent_validation_evaluation_permissions_and_cost_limits() {
    for allowed in [AgentTool::ValidateClauses, AgentTool::EvaluateClauses] {
        let replies = semantic_api_probe(AgentToolPolicy::new([allowed]), None, false).await;
        for (label, reply) in replies {
            if (label == "validate") == (allowed == AgentTool::ValidateClauses) {
                assert!(reply.get("result").is_some(), "{reply}");
            } else {
                assert_eq!(reply["error"]["code"], "tool_disabled");
            }
        }
    }
    let replies = semantic_api_probe(AgentToolPolicy::default(), Some(1), false).await;
    assert!(replies[0].1.get("result").is_some());
    assert_eq!(replies[1].1["error"]["code"], "host_limit");
    assert_eq!(
        replies[1].1["error"]["host_limit"],
        json!({"limit":"evaluation_cost","value":1,"observed":2})
    );
}

// The proposer learns the old identity and attempt only from public ledger
// pagination. It has no manifest, checker, dictionary or Houdini handle.
struct HistoricalReferenceProbe {
    corrected: bool,
    found: Arc<Mutex<Option<Value>>>,
}

async fn public_query_result(
    queries: &dyn whiel_runner::proposer_api::ProposerQueries,
    name: &str,
    args: Value,
) -> Value {
    let reply = serde_json::to_value(queries.call(name, args).await).unwrap();
    serde_json::from_value::<whiel_runner::proposer_api::query_results::ToolResponseV1>(
        reply.clone(),
    )
    .unwrap();
    tool_result(&reply)
}

impl whiel_runner::proposer_api::Proposer for HistoricalReferenceProbe {
    fn quiesce_request(&mut self) -> whiel_runner::proposer_api::ProposerCleanupFuture<'_> {
        Box::pin(async { Ok(()) })
    }
    fn shutdown(
        &mut self,
        _reason: whiel_runner::proposer_api::wire::ShutdownReason,
    ) -> whiel_runner::proposer_api::ProposerCleanupFuture<'_> {
        self.quiesce_request()
    }

    fn consult<'a>(
        &'a mut self,
        push: &'a whiel_runner::proposer_api::ProposerPush,
        queries: &'a dyn whiel_runner::proposer_api::ProposerQueries,
        response: &'a mut whiel_runner::proposer_api::AgentResponseWriter,
        _cancellation: whiel_runner::proposer_api::AgentSourceCancellation,
    ) -> whiel_runner::proposer_api::AgentSourceFuture<'a> {
        Box::pin(async move {
            let mut submission = push.candidate_clauses_example().unwrap();
            if self.corrected {
                let correction = push.observation().correction.as_ref().unwrap();
                assert!(
                    correction
                        .diagnostics
                        .iter()
                        .any(|diagnostic| { diagnostic.code == "drop_target_not_eligible" })
                );
                assert_eq!(push.validation_ordinal(), 1);
                response
                    .write_chunk(&serde_json::to_vec(&submission).unwrap())
                    .unwrap();
                return whiel_runner::proposer_api::AgentSourceOutcome::Response;
            }
            self.corrected = true;
            let mut args = json!({});
            let mut pages = 0;
            let mut cursors = BTreeSet::new();
            let row = loop {
                let page = public_query_result(queries, "ledger", args).await;
                pages += 1;
                let items = page["items"].as_array().unwrap();
                assert_eq!(items.len(), 1, "the fixture must require pagination");
                if let Some(row) = items.iter().find(|row| {
                    row["kind"] == "attempt" && row["result"]["outcome"]["kind"] == "refuted"
                }) {
                    assert!(
                        pages > 1,
                        "the old refutation must be outside the initial page"
                    );
                    break row.clone();
                }
                let cursor = page["metadata"]["continuation"]
                    .as_str()
                    .unwrap()
                    .to_owned();
                assert!(
                    cursors.insert(cursor.clone()),
                    "ledger pagination must advance"
                );
                args = json!({"cursor":cursor});
            };
            let clause = row["clause"].clone();
            let attempt = row["result"]["attempt_id"].as_u64().unwrap();
            let observation = serde_json::to_value(&push.observation().feedback).unwrap();
            for list in ["core", "pending", "last_round"] {
                assert!(
                    observation[list]
                        .as_array()
                        .unwrap()
                        .iter()
                        .all(|entry| { entry["clause"] != clause }),
                    "historical clause unexpectedly visible in {list}"
                );
            }
            let history = public_query_result(queries, "history", json!({"clause":clause})).await;
            assert_eq!(history["clause"], clause);
            assert_eq!(history["status"]["kind"], "dead");
            assert_eq!(history["status"]["cause"], "refuted");
            assert!(history["current_level"].is_null());
            assert!(history["attempts"].as_array().unwrap().iter().any(|entry| {
                entry["clause"] == clause
                    && entry["result"]["attempt_id"] == attempt
                    && entry["result"]["outcome"]["kind"] == "refuted"
            }));
            let model =
                public_query_result(queries, "countermodel", json!({"attempt":attempt})).await;
            assert_eq!(model["attempt"], attempt);
            assert_eq!(model["clause"], clause);
            assert!(model.get("found_not_retained").is_none());
            assert!(!model["model"]["relations"].as_array().unwrap().is_empty());
            let evaluated = public_query_result(
                queries,
                "evaluate_clauses",
                json!({
                    "clauses":[EDB_CLAUSE],
                    "instances":[{"kind":"retained", "attempt":attempt}]
                }),
            )
            .await;
            assert_eq!(evaluated["results"][0]["admitted"], true);
            assert_eq!(evaluated["results"][0]["holds"], json!([false]));
            assert_eq!(
                evaluated["instances"],
                json!([
                    {"kind":"retained", "source_index":0, "attempt":attempt}
                ])
            );
            *self.found.lock().unwrap() = Some(clause.clone());
            // A readable reference confers no drop capability. Reusing it in
            // the proposal channel must earn a correction, never a state edit.
            submission["dropped"] = json!([{
                "clause":clause,
                "consultation_digest":submission["binding"]["consultation_digest"],
                "authorization_digest":"0".repeat(64)
            }]);
            response
                .write_chunk(&serde_json::to_vec(&submission).unwrap())
                .unwrap();
            whiel_runner::proposer_api::AgentSourceOutcome::Response
        })
    }
}

fn assert_historical_generic_trace(trace: &CanonicalAcceptanceTrace) -> Value {
    assert_eq!(trace.observations.len(), 2);
    let initial = &trace.observations[0]["observation"];
    let corrected = &trace.observations[1]["observation"];
    assert!(initial["correction"].is_null());
    assert_eq!(initial["binding"]["validation_ordinal"], 0);
    assert_eq!(corrected["binding"]["validation_ordinal"], 1);
    assert_eq!(
        corrected["binding"]["consultation_digest"],
        initial["binding"]["consultation_digest"]
    );
    assert!(
        corrected["correction"]["diagnostics"]
            .as_array()
            .unwrap()
            .iter()
            .any(|item| item["code"] == "drop_target_not_eligible")
    );
    let queries = &trace.queries;
    let page_count = queries
        .iter()
        .take_while(|query| query["name"] == "ledger")
        .count();
    assert!(page_count > 1 && page_count <= 128);
    let row = &queries[page_count - 1]["reply"]["result"]["items"][0];
    let clause = row["clause"].clone();
    let attempt = row["result"]["attempt_id"].as_u64().unwrap();
    for list in ["core", "pending", "last_round"] {
        assert!(
            initial["feedback"][list]
                .as_array()
                .unwrap()
                .iter()
                .all(|entry| entry["clause"] != clause)
        );
    }
    assert_eq!(queries.len(), page_count + 3);
    for query in queries {
        // Assert the complete canonical response, independently of the endpoint.
        serde_json::from_value::<whiel_runner::proposer_api::query_results::ToolResponseV1>(
            query["reply"].clone(),
        )
        .unwrap();
        assert_eq!(query["reply"]["tool"], query["name"]);
        assert_eq!(
            query["reply"]["state_revision"],
            queries[0]["reply"]["state_revision"]
        );
    }
    let mut cursors = BTreeSet::new();
    for index in 0..page_count {
        let page = &queries[index];
        assert_eq!(page["name"], "ledger");
        assert_eq!(
            page["arguments"],
            if index == 0 {
                json!({})
            } else {
                let cursor = queries[index - 1]["reply"]["result"]["metadata"]["continuation"]
                    .as_str()
                    .unwrap();
                assert!(cursors.insert(cursor));
                json!({"cursor":cursor})
            }
        );
        let items = page["reply"]["result"]["items"].as_array().unwrap();
        assert_eq!(items.len(), 1);
        if index + 1 == page_count {
            assert_eq!(items[0]["kind"], "attempt");
            assert_eq!(items[0]["clause"], clause);
            assert_eq!(items[0]["result"]["attempt_id"], attempt);
            assert_eq!(items[0]["result"]["outcome"]["kind"], "refuted");
        } else {
            assert!(items.iter().all(|row| {
                row["kind"] != "attempt" || row["result"]["outcome"]["kind"] != "refuted"
            }));
        }
    }
    let history = &queries[page_count];
    assert_eq!(history["name"], "history");
    assert_eq!(history["arguments"], json!({"clause":clause}));
    let history = tool_result(&history["reply"]);
    assert_eq!(history["clause"], clause);
    assert_eq!(history["status"]["kind"], "dead");
    assert_eq!(history["status"]["cause"], "refuted");
    assert!(history["current_level"].is_null());
    assert!(history["attempts"].as_array().unwrap().iter().any(|row| {
        row["clause"] == clause
            && row["result"]["attempt_id"] == attempt
            && row["result"]["outcome"]["kind"] == "refuted"
    }));
    let model = &queries[page_count + 1];
    assert_eq!(model["name"], "countermodel");
    assert_eq!(model["arguments"], json!({"attempt":attempt}));
    let model = tool_result(&model["reply"]);
    assert_eq!(model["clause"], clause);
    assert_eq!(model["attempt"], attempt);
    assert!(model.get("found_not_retained").is_none());
    assert!(!model["model"]["relations"].as_array().unwrap().is_empty());
    let evaluated = &queries[page_count + 2];
    assert_eq!(evaluated["name"], "evaluate_clauses");
    assert_eq!(
        evaluated["arguments"],
        json!({"clauses":[EDB_CLAUSE], "instances":[{"kind":"retained", "attempt":attempt}]})
    );
    let evaluated = tool_result(&evaluated["reply"]);
    assert_eq!(evaluated["results"][0]["admitted"], true);
    assert_eq!(evaluated["results"][0]["holds"], json!([false]));
    assert_eq!(
        evaluated["instances"],
        json!([{"kind":"retained", "source_index":0, "attempt":attempt}])
    );
    assert_eq!(evaluated["skipped"], json!([]));
    let submissions = &trace.submissions;
    assert_eq!(submissions.len(), 2);
    let first = &submissions[0]["response"];
    for (name, value) in initial["binding"]
        .as_object()
        .unwrap()
        .iter()
        .filter(|(name, _)| name.as_str() != "policy_digest")
    {
        assert_eq!(first["binding"][name], *value);
    }
    assert!(first["binding"].get("policy_digest").is_none());
    assert_eq!(
        first["binding"]["request_digest"].as_str().unwrap().len(),
        64
    );
    assert_ne!(first["binding"]["request_digest"], "0".repeat(64));
    assert_eq!(first["clauses"], json!([]));
    assert_eq!(
        first["dropped"],
        json!([{
            "clause":clause, "consultation_digest":initial["binding"]["consultation_digest"],
            "authorization_digest":"0".repeat(64)
        }])
    );
    let second = &submissions[1]["response"];
    for (name, value) in corrected["binding"]
        .as_object()
        .unwrap()
        .iter()
        .filter(|(name, _)| name.as_str() != "policy_digest")
    {
        assert_eq!(second["binding"][name], *value);
    }
    assert_ne!(
        first["binding"]["request_digest"],
        second["binding"]["request_digest"]
    );
    assert_eq!(
        initial["binding"]["state_snapshot_digest"],
        corrected["binding"]["state_snapshot_digest"]
    );
    assert_eq!(second["clauses"], json!([]));
    assert_eq!(second["dropped"], json!([]));
    assert_eq!(
        trace.outcomes,
        vec![TranscriptOutcome::Correctable, TranscriptOutcome::Accepted]
    );
    clause
}

async fn assert_historical_empty_proposal<P: AgentProvider>(
    provider: P,
    feedback_state: &PreCertificateAgentHoudiniState,
    validator: &AgentResponseValidator<'_>,
    cancellation: &CancellationToken,
) {
    let mut agent = Agent::with_default_policy(provider);
    let proposal = agent
        .get_houdini_proposal(feedback_state.feedback(), validator, cancellation)
        .await
        .unwrap();
    let HoudiniProposal::CandidateClauses(epoch) = proposal else {
        panic!("expected corrected empty proposal: {proposal:?}");
    };
    assert!(epoch.clauses().is_empty());
    assert!(epoch.dropped().is_empty());
    assert_eq!(
        agent
            .attempt_history()
            .iter()
            .map(|attempt| attempt.outcome())
            .collect::<Vec<_>>(),
        vec![
            AgentRequestAttemptOutcome::Correctable,
            AgentRequestAttemptOutcome::Accepted
        ]
    );
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn public_historical_ledger_references_reach_saved_models_without_drop_authority() {
    historical_ledger_references_case(false).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn generic_historical_ledger_references_reach_saved_models_without_drop_authority() {
    historical_ledger_references_case(true).await;
}

async fn historical_ledger_references_case(generic_process: bool) {
    let directory = support::TestDir::new(if generic_process {
        "generic_historical_references"
    } else {
        "public_historical_references"
    });
    let budget = agent_admission(1, 1);
    let cancellation = CancellationToken::new();
    let bound = bind(worker_pool(1), '6', None, &budget, &cancellation).await;
    let (task, admission, solver, mut houdini) = bound.into_parts();
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let clauses = admit(
        &admission,
        &[
            CANONICAL_LEVEL_ZERO_CLAUSE,
            EDB_CLAUSE,
            CANONICAL_LEVEL_ONE_CLAUSE,
        ],
        &budget,
        &cancellation,
    )
    .await;
    // Reserve a lower catalog identity, then enqueue it only after the old
    // refutation. It will occupy the first internal clause page, while its
    // newer checks push the old refutation off the first public ledger page.
    let register = |clause: &whiel_runner::ExtendedClause| {
        let catalog = houdini.catalog();
        catalog
            .register_batch(
                catalog.next_batch_ordinal().unwrap(),
                [(clause.clone(), ExtendedClauseOrigin::Submitted)],
            )
            .unwrap()
    };
    let earlier_identity = register(&clauses[0]);
    let old = register(&clauses[1]);
    let later_identity = register(&clauses[2]);
    let old_id = old.ids()[0];
    houdini.enqueue_registered(&old).unwrap();
    let mut checker = solver.clone().production_checker(production_config(
        &artifacts,
        &budget,
        FmbOptions::default(),
        refuting_model_vampire(directory.path()),
        &cancellation,
    ));
    stabilize_leveled_houdini(&mut houdini, &mut checker)
        .await
        .unwrap();
    assert!(houdini.is_dead(old_id));
    assert!(
        houdini.attempts().rows().iter().any(|row| {
            let LevelLedgerRow::Attempt(row) = row else {
                return false;
            };
            let FrameworkIICheckOutcome::Refuted(evidence) = row.outcome() else {
                return false;
            };
            row.request().clause() == old_id
                && evidence.validated_refutation().is_some_and(|receipt| {
                    receipt.validation_identity()["validated_refutation"] == true
                        && receipt.validation_identity()["axioms_hold"] == true
                        && receipt.validation_identity()["conjecture_holds"] == false
                })
        }),
        "fixture requires a real Lean-validated retained refutation"
    );
    houdini.enqueue_registered(&earlier_identity).unwrap();
    houdini.enqueue_registered(&later_identity).unwrap();
    stabilize_leveled_houdini(&mut houdini, &mut checker)
        .await
        .unwrap();
    assert!(houdini.is_dead(old_id));
    let feedback_state = PreCertificateAgentHoudiniState::new(
        Arc::clone(&task),
        &artifacts,
        &houdini,
        Duration::from_secs(30),
        AgentFeedbackPolicy::new(whiel_runner::framework2::AgentFeedbackLimits {
            clause_page_items: 1,
            ledger_page_items: 1,
            ..whiel_runner::framework2::AgentFeedbackLimits::default()
        })
        .unwrap(),
    )
    .unwrap();
    let initial_page = feedback_state.feedback().clauses().items();
    assert_eq!(initial_page.len(), 1);
    assert_eq!(
        initial_page[0].clause().clause_id(),
        earlier_identity.ids()[0]
    );
    assert!(
        initial_page
            .iter()
            .all(|entry| entry.clause().clause_id() != old_id)
    );
    let before = format!("{houdini:?}");
    let catalog_len = houdini.catalog().len().unwrap();
    let catalog_ordinal = houdini.catalog().next_batch_ordinal().unwrap();
    let dictionary = checker.dictionary_entry_summary();
    let validator = AgentResponseValidator::new(
        &task,
        &houdini,
        &admission,
        &solver,
        &budget,
        &feedback_state,
        Some(&checker),
    );
    let found = if generic_process {
        use whiel_runner::proposer_host::generic_process::GenericProcessProposer;
        let policy = AgentConsultationPolicy::default();
        let recorder = recording_fixture(&task, feedback_state.feedback(), &policy);
        let mut provider = GenericProcessProposer::start(
            acceptance_proposer_command(directory.path(), "historical"),
            &AgentToolPolicy::all_enabled().enabled_names(),
            &cancellation,
        )
        .await
        .unwrap();
        let cleanup = provider.cleanup_handle();
        let result = catch_test_panic(async {
            let mut agent =
                RecordingProvider::agent(BorrowedProposer(&mut provider), policy, recorder.clone());
            let proposal = agent
                .get_houdini_proposal(feedback_state.feedback(), &validator, &cancellation)
                .await
                .unwrap();
            let HoudiniProposal::CandidateClauses(epoch) = proposal else {
                panic!("expected corrected empty generic proposal: {proposal:?}");
            };
            assert!(epoch.clauses().is_empty());
            assert!(epoch.dropped().is_empty());
            assert_eq!(
                agent
                    .attempt_history()
                    .iter()
                    .map(|attempt| attempt.outcome())
                    .collect::<Vec<_>>(),
                vec![
                    AgentRequestAttemptOutcome::Correctable,
                    AgentRequestAttemptOutcome::Accepted
                ]
            );
        })
        .await;
        finish_acceptance_proposer(&mut provider, &cleanup, result).await;
        let trace = canonical_acceptance_trace(&recorder, &artifacts);
        let found = assert_historical_generic_trace(&trace);
        eprintln!(
            "generic_api_historical_receipt={}",
            json!({
                "model_producer":"synthetic", "real_lean_validation":true,
                "canonical_queries":trace.queries, "canonical_outcomes":trace.outcomes,
                "requests":trace.observations.len(), "discovered_clause":found,
            })
        );
        found
    } else {
        let found = Arc::new(Mutex::new(None));
        assert_historical_empty_proposal(
            HistoricalReferenceProbe {
                corrected: false,
                found: Arc::clone(&found),
            },
            &feedback_state,
            &validator,
            &cancellation,
        )
        .await;
        found.lock().unwrap().clone().unwrap()
    };
    assert_eq!(found["clause_id"], old_id.get());
    assert_eq!(
        format!("{houdini:?}"),
        before,
        "successful reads and rejected drop must not change Houdini state"
    );
    assert_eq!(houdini.catalog().len().unwrap(), catalog_len);
    assert_eq!(
        houdini.catalog().next_batch_ordinal().unwrap(),
        catalog_ordinal
    );
    assert_eq!(checker.dictionary_entry_summary(), dictionary);
    assert!(houdini.is_dead(old_id));
    solver.shutdown().await.unwrap();
    drop(checker);
    drop(solver);
    drop(admission);
    drop(feedback_state);
    drop(artifacts);
    owner.settle().unwrap();
}

// ------------------------------------------------------------
// Solver-Name Agreement
// ------------------------------------------------------------

/// Registered inputs whose symbols cover the naming convention's cases: a
/// string constant, auxiliary copies, prophecy copies, and the flag symbols
/// a two-loop input carries.
const NAME_AGREEMENT_TASK_IDS: [&str; 3] = ["Example0001", "Example5033", "Example4041"];

/// Every relation and constant of one registered input, named by Rust.
fn solver_name_bindings(descriptor: &Value) -> Vec<NameMapping> {
    let task = SynthesisTask::from_fixed_ambient_json(&descriptor["manifest"].to_string())
        .expect("the descriptor carries a fixed-ambient task manifest");
    TaskNameEnv::from_task(&task)
        .expect("every key of a registered input has a solver name")
        .all_mappings()
}

/// Offer one name-environment extension to a freshly started worker.
///
/// The framework-level suites reach this operation only through a bound
/// search, which extends the environment from Rust's own authoritative copy.
/// Agreement between the two namings is a property of the offered bindings
/// themselves, so this speaks the worker's protocol directly and can offer a
/// name Rust would never compute.
fn offer_name_bindings(
    descriptor: &Value,
    bindings: &[NameMapping],
) -> FixedAmbientWorkerResponseEnvelope {
    let manifest = &descriptor["manifest"];
    let identity = &descriptor["task_identity"];
    let field = |value: &Value, name: &str| {
        value[name]
            .as_str()
            .unwrap_or_else(|| panic!("the descriptor carries {name}"))
            .to_string()
    };
    let wire = |kind: NameMappingKind| {
        bindings
            .iter()
            .filter(|binding| binding.kind == kind)
            .map(|binding| json!({"key": binding.key, "name": binding.tptp_name}))
            .collect::<Vec<_>>()
    };
    let request = FixedAmbientWorkerRequestEnvelope {
        format_version: FIXED_AMBIENT_WORKER_FORMAT_VERSION,
        semantic_version: manifest["semantic_version"]
            .as_u64()
            .expect("semantic version"),
        encoding_version: manifest["encoding_version"]
            .as_u64()
            .expect("encoding version"),
        task_canonical_id: field(identity, "canonical_id"),
        task_module: field(identity, "module"),
        task_namespace: field(identity, "namespace"),
        task_source_sha256: field(identity, "source_sha256"),
        scope_identity: descriptor["scope_identity"].clone(),
        request_id: 1,
        name_env_revision: NameEnvRevision::INITIAL,
        operation: FixedAmbientWorkerOperation::ExtendNameEnv,
        payload: json!({
            "relations": wire(NameMappingKind::Relation),
            "constants": wire(NameMappingKind::Constant),
            "next_revision": 1,
        }),
    };

    let mut worker = Command::new(fixed_ambient_worker())
        .arg("worker")
        .current_dir(support::repository_root())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("start the fixed-ambient worker");
    write_frame(
        worker.stdin.as_mut().expect("worker stdin"),
        &request,
        MAX_ENCODING_FRAME_BYTES,
    )
    .expect("send one name-environment extension");
    let response = read_frame(
        worker.stdout.as_mut().expect("worker stdout"),
        MAX_ENCODING_FRAME_BYTES,
    )
    .expect("read the worker's answer");
    drop(worker.stdin.take());
    let _ = worker.wait();
    response
}

/// Lean accepts every name Rust computes for a registered input's symbols.
#[test]
fn the_worker_accepts_rust_solver_names_for_registered_inputs() {
    for canonical_id in NAME_AGREEMENT_TASK_IDS {
        let descriptor = manifest_for(canonical_id);
        let bindings = solver_name_bindings(&descriptor);
        assert!(
            bindings
                .iter()
                .any(|binding| binding.kind == NameMappingKind::Relation),
            "{canonical_id} declares relations"
        );
        let response = offer_name_bindings(&descriptor, &bindings);
        assert_eq!(
            response.status,
            WorkerResponseStatus::Ok,
            "{canonical_id} name bindings were refused: {error:?}",
            error = response.error
        );
    }

    // Example5033 and Example4041, examined again below, between them carry
    // the convention's cases, and these are the spellings the class fixes
    // for them.
    let example5033 = solver_name_bindings(&manifest_for("Example5033"));
    let name_of = |bindings: &[NameMapping], key: &str| {
        bindings
            .iter()
            .find(|binding| binding.key == key)
            .unwrap_or_else(|| panic!("the input declares {key}"))
            .tptp_name
            .clone()
    };
    assert_eq!(name_of(&example5033, "o:p::Edge"), "op_zEdge");
    assert_eq!(name_of(&example5033, "o:a::MPath"), "oa_zMPath");
    assert_eq!(name_of(&example5033, "y:p::Res"), "yp_zRes");
    assert_eq!(name_of(&example5033, "str:root"), "ksroot");

    let example4041 = solver_name_bindings(&manifest_for("Example4041"));
    assert_eq!(name_of(&example4041, "o:f::0"), "of_z0");
    assert_eq!(name_of(&example4041, "y:f::1"), "yf_z1");
}

/// A name that is not Lean's own name for the symbol is refused, even though
/// it is a legal identifier that collides with nothing in the environment.
#[test]
fn the_worker_refuses_a_binding_that_renames_a_symbol() {
    let descriptor = manifest_for("Example5033");
    let mut bindings = solver_name_bindings(&descriptor);
    let renamed = bindings
        .iter_mut()
        .find(|binding| binding.key == "o:p::Edge")
        .expect("Example5033 declares its edge relation");
    renamed.tptp_name = "op_zEdgeRenamed".to_string();

    let response = offer_name_bindings(&descriptor, &bindings);
    assert_eq!(response.status, WorkerResponseStatus::Error);
    let error = response.error.expect("a refusal carries its reason");
    assert_eq!(error.kind, "name_environment");
    assert!(
        error.message.contains("op_zEdge"),
        "the refusal names the symbol's own solver name: {message}",
        message = error.message
    );
}

/// The same refusal for a constant beside the relation case above.
#[test]
fn the_worker_refuses_a_binding_that_renames_a_constant() {
    let descriptor = manifest_for("Example5033");
    let mut bindings = solver_name_bindings(&descriptor);
    let renamed = bindings
        .iter_mut()
        .find(|binding| binding.key == "str:root")
        .expect("Example5033 declares its root constant");
    renamed.tptp_name = "ksrootRenamed".to_string();

    let response = offer_name_bindings(&descriptor, &bindings);
    assert_eq!(response.status, WorkerResponseStatus::Error);
    let error = response.error.expect("a refusal carries its reason");
    assert_eq!(error.kind, "name_environment");
    assert!(
        error.message.contains("ksroot"),
        "the refusal names the symbol's own solver name: {message}",
        message = error.message
    );
}

/// Every canonical id the fixed-ambient worker's registry answers `ids` with.
///
/// This is a one-shot subprocess call into the same compiled worker binary
/// `manifest_for` already uses, not a persistent worker session — naming a
/// task's keys is pure computation over its manifest JSON (see
/// `try_solver_name_bindings` below), so no `describe` round trip through a
/// worker's stdin/stdout is needed to reach them.
fn all_registered_task_ids() -> Vec<String> {
    let output = Command::new(fixed_ambient_worker())
        .arg("ids")
        .current_dir(support::repository_root())
        .output()
        .expect("list registered fixed-ambient canonical ids");
    assert!(
        output.status.success(),
        "listing registered fixed-ambient ids failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .map(str::to_string)
        .collect()
}

/// Every relation and constant of one registered input, named by Rust, or
/// the reason a key could not be named — the fallible twin of
/// `solver_name_bindings`, which panics on the same failure.
fn try_solver_name_bindings(descriptor: &Value) -> Result<Vec<NameMapping>, String> {
    let task = SynthesisTask::from_fixed_ambient_json(&descriptor["manifest"].to_string())
        .map_err(|error| error.to_string())?;
    TaskNameEnv::from_task(&task)
        .map(|env| env.all_mappings())
        .map_err(|error| error.to_string())
}

/// Every registered fixed-ambient input's symbol keys have a solver name.
///
/// `NAME_AGREEMENT_TASK_IDS` above only samples the naming convention's
/// cases; this instead sweeps every registered input so an unnameable key —
/// one Rust's naming grammar cannot parse — is found here, cheaply, before
/// the far more expensive certificate regeneration that would otherwise be
/// where it first surfaces. Each of the 86 registered inputs costs one
/// one-shot subprocess call (well under a second), so the whole sweep is a
/// few seconds and needs no `#[ignore]`. Run directly with:
/// `cargo test --test framework2_fixed_ambient \
///   every_registered_input_has_solver_names_for_all_its_keys -- \
///   --test-threads=3`
#[test]
fn every_registered_input_has_solver_names_for_all_its_keys() {
    let ids = all_registered_task_ids();
    assert!(!ids.is_empty(), "the registry lists at least one input");
    let mut failures = Vec::new();
    for canonical_id in &ids {
        let descriptor = manifest_for(canonical_id);
        if let Err(reason) = try_solver_name_bindings(&descriptor) {
            failures.push(format!("{canonical_id}: {reason}"));
        }
    }
    assert!(
        failures.is_empty(),
        "{failed} of {total} registered inputs have an unnameable key:\n{detail}",
        failed = failures.len(),
        total = ids.len(),
        detail = failures.join("\n")
    );
}

/// A certification that fails leaves the search's own records behind.
///
/// This is the whole point of recording at acceptance. Before it, the frozen
/// counterexample lived in memory and `Counterexample.json` was written only
/// once the invalidity certificate had built and revalidated, so a build
/// that failed — or ran out of its allowance — lost the result the search
/// had actually found. Here the build is forced to fail at its last step,
/// and both records are still on disk with no certificate beside them.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_failed_certification_still_leaves_the_records_written_at_acceptance() {
    let mut fixture = SearchFixture::for_task(
        "fixed_ambient_records_survive",
        REFUTABLE_TASK_ID,
        '9',
        worker_pool(1),
    )
    .await;
    let cancellation = CancellationToken::new();
    let external_cancellation = CancellationToken::new();
    let pinned = PinnedLeancheckVampire::from_lock(&support::repository_root())
        .expect("the repository-pinned leancheck Vampire resolves");
    let runtime = fixture.runtime("unknown", &cancellation);
    let agent = Agent::with_default_policy(CounterexampleThenClauseProvider {
        instance: refutable_witness(),
        clause: LEVEL_ZERO_CLAUSE,
        observed: Arc::new(Mutex::new(Vec::new())),
        consultations: Arc::new(AtomicUsize::new(0)),
    });
    let overall_limit = Duration::from_secs(120);
    let limits = PreCertificateAgentHoudiniLimits::new(overall_limit, None, Some(4));
    let search = PreCertificateAgentHoudiniSearch::new(
        Arc::clone(&fixture.task),
        agent,
        fixture.houdini.take().unwrap(),
        runtime,
        limits,
        tokio::time::Instant::now() + overall_limit,
        AgentFeedbackPolicy::default(),
    )
    .unwrap();
    let mut outcome = search.run().await;
    assert!(
        matches!(&outcome, PreCertificateAgentHoudiniOutcome::Invalid(_)),
        "a validated counterexample must end the run invalid: {outcome:?}"
    );

    let input_directory = fixture.directory.path().join("Example0013");
    fs::create_dir_all(&input_directory).unwrap();
    let staging_root = fixture.directory.path().join("staging");
    fs::create_dir_all(&staging_root).unwrap();
    let fuel_policy = CounterexampleFuelPolicy::new(limits.counterexample_validation_limit())
        .expect("the run's own validation limit is exactly representable");

    // The seam: records first, certification afterwards.
    let accepted = record_acceptance(
        &mut outcome,
        AcceptanceRecordRequest {
            input_directory: &input_directory,
            fuel_policy,
            search_elapsed: Duration::from_secs(1),
            search_limit: overall_limit,
        },
    )
    .expect("an accepted counterexample records")
    .expect("an invalid outcome has a record");
    assert_eq!(accepted.verdict(), AcceptedVerdict::Invalid);
    assert_eq!(
        accepted.verdict().uncertified_status(),
        "invalid_uncertified"
    );
    let record_path = input_directory.join("Counterexample.json");
    let envelope_path = input_directory.join("Accepted.json");
    assert!(record_path.is_file());
    assert!(envelope_path.is_file());
    let envelope: Value = serde_json::from_slice(&fs::read(&envelope_path).unwrap()).unwrap();
    assert_eq!(envelope["kind"], "whiel_search_acceptance");
    assert_eq!(envelope["version"], 1);
    assert_eq!(envelope["verdict"], "invalid");
    assert_eq!(envelope["record"], "Counterexample.json");
    assert_eq!(envelope["task_identity"]["canonical_id"], REFUTABLE_TASK_ID);
    assert!(
        envelope["core"].is_null(),
        "an invalid result freezes no Core"
    );
    assert_eq!(envelope["search"]["limit_seconds"], 120.0);
    let record_bytes = fs::read(&record_path).unwrap();

    // Force the publication to fail at its last step: a sentinel appears at
    // the destination after the existence check, so a fully built and
    // revalidated tree still cannot be renamed into place.
    let destination = input_directory.join("Certificate");
    let occupy = destination.clone();
    let SettlementParts {
        directory,
        task: _task,
        admission,
        solver_admission,
        resources,
    } = fixture.into_settlement_parts();
    let settled = settle_search_outcome(
        outcome,
        SettlementPolicy {
            space_guard: None,
            admission: &admission,
            solver_admission: &solver_admission,
            pinned: &pinned,
            canonical_id: REFUTABLE_TASK_ID,
            input_namespace: "Whiel.Benchmark.Example0013",
            repository_root: support::repository_root(),
            staging_root,
            private_root: directory.path().join("private"),
            input_directory: input_directory.clone(),
            destination: destination.clone(),
            time_limit_seconds: 60,
            certification_limit: Duration::from_secs(600),
            concurrency: DEFAULT_CERTIFICATION_CONCURRENCY,
            fuel_policy,
            retention: Retention::CertificateOnly,
            external_cancellation: &external_cancellation,
            hooks: CertificateBuildHooks {
                before_build: Some(Box::new(move |_| {
                    fs::write(&occupy, b"occupied before the rename").unwrap();
                })),
                ..CertificateBuildHooks::default()
            },
        },
        resources,
    )
    .await;
    assert!(
        settled.is_err(),
        "the forced conflict must fail the certification"
    );

    // The records the search wrote are exactly as they were, and nothing
    // was published beside them.
    assert_eq!(fs::read(&record_path).unwrap(), record_bytes);
    assert!(envelope_path.is_file());
    assert_eq!(
        fs::read(&destination).unwrap(),
        b"occupied before the rename"
    );
    assert!(!input_directory.join("CertificateEvidence").exists());
    drop(directory);
}

/// The equivalence canary: what the search accepts certifies by the rows
/// path, and an input that changed does not.
///
/// The inline canary above proves the in-process path; this one takes the
/// *same* real search to the *same* frozen Core, stops at acceptance as
/// `--certify never` does, and then hands the resulting run directory to the
/// real `campaign certify` command. Two things are pinned:
///
/// - a record whose input has changed is refused — `input_changed`, no tree,
///   and the record left untouched — which is checked first because it costs
///   only a worker manifest;
/// - the untouched record then certifies: the published tree is checked
///   against the real `Input.lean` by the build itself, `result.json` reads
///   `valid` with the axiom closure and the module the tree can be
///   revalidated with, and `Core.json` is byte-for-byte the record the
///   search wrote. That last equality is the guard against the two
///   certification paths drifting: the rows path re-admits, re-levels and
///   re-renders the record, and the bytes still match.
///
/// It is slow by construction — a real search followed by a real
/// certification — and nothing in it is stubbed.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn the_accepted_record_certifies_by_the_rows_path_and_a_changed_input_does_not() {
    let mut fixture =
        SearchFixture::new("fixed_ambient_deferred_canary", 'b', worker_pool(1)).await;
    let cancellation = CancellationToken::new();
    let pinned = PinnedLeancheckVampire::from_lock(&support::repository_root())
        .expect("the repository-pinned leancheck Vampire resolves");
    let runtime = fixture.real_solver_runtime(&pinned, &cancellation);
    let agent = Agent::with_default_policy(ClauseProvider {
        clauses: vec![CANONICAL_LEVEL_ZERO_CLAUSE, CANONICAL_LEVEL_ONE_CLAUSE],
        observed: Arc::new(Mutex::new(Vec::new())),
    });
    let overall_limit = Duration::from_secs(900);
    let limits = PreCertificateAgentHoudiniLimits::new(overall_limit, None, Some(4));
    let search = PreCertificateAgentHoudiniSearch::new(
        Arc::clone(&fixture.task),
        agent,
        fixture.houdini.take().unwrap(),
        runtime,
        limits,
        tokio::time::Instant::now() + overall_limit,
        AgentFeedbackPolicy::default(),
    )
    .unwrap();
    let mut outcome = search.run().await;
    assert!(
        matches!(&outcome, PreCertificateAgentHoudiniOutcome::Valid(_)),
        "the real pinned Vampire did not prove the termination check: {outcome:?}"
    );

    // A run directory exactly as `--certify never` leaves one.
    let run = fixture.directory.path().join("searched");
    let input_directory = run.join(PRODUCTION_TASK_ID);
    fs::create_dir_all(&input_directory).unwrap();
    let accepted = record_acceptance(
        &mut outcome,
        AcceptanceRecordRequest {
            input_directory: &input_directory,
            fuel_policy: CounterexampleFuelPolicy::new(limits.counterexample_validation_limit())
                .unwrap(),
            search_elapsed: Duration::from_secs(1),
            search_limit: overall_limit,
        },
    )
    .expect("an accepted Core records")
    .expect("a valid outcome has a record");
    assert_eq!(accepted.verdict(), AcceptedVerdict::Valid);
    let core_record = input_directory.join("Core.json");
    let accepted_bytes = fs::read(&core_record).unwrap();
    let envelope_path = input_directory.join("Accepted.json");
    let envelope: Value = serde_json::from_slice(&fs::read(&envelope_path).unwrap()).unwrap();
    assert_eq!(envelope["verdict"], "valid");
    assert_eq!(
        envelope["core"]["task_canonical_id"], PRODUCTION_TASK_ID,
        "a valid envelope carries the frozen payload"
    );
    let recorded_search_seconds = envelope["search"]["elapsed_seconds"].clone();
    fs::write(
        input_directory.join("result.json"),
        serde_json::to_vec_pretty(&json!({
            "input": PRODUCTION_TASK_ID,
            "schema_version": 3,
            "status": "valid_uncertified",
            // Named relative to the input's own directory, as a search
            // writes them: a run directory is certified wherever it is.
            "record": "Core.json",
            "accepted": "Accepted.json",
            "search_seconds": recorded_search_seconds,
        }))
        .unwrap(),
    )
    .unwrap();
    let write_summary = || {
        fs::write(
            run.join("summary.json"),
            serde_json::to_vec_pretty(&json!({
                "schema_version": 3,
                "interrupted": false,
                "all_certified": false,
                "all_accepted": true,
                "resource_failure": Value::Null,
                "selected_inputs": [PRODUCTION_TASK_ID],
                "unrun_inputs": [],
                "results": [],
            }))
            .unwrap(),
        )
        .unwrap();
    };
    write_summary();

    // The search's own resources stop here, exactly as the uncertified
    // settlement boundary releases them.
    let SettlementParts {
        directory,
        task: _task,
        admission: _admission,
        solver_admission: _solver_admission,
        resources,
    } = fixture.into_settlement_parts();
    release_without_certifying(outcome, resources)
        .await
        .expect("an uncertified run still settles");

    let certify = |run: &Path| {
        std::process::Command::new(env!("CARGO_BIN_EXE_whiel-symbolic"))
            .current_dir(support::repository_root())
            .args(["campaign", "certify", "--repo"])
            .arg(support::repository_root())
            .arg("--run")
            .arg(run)
            .args(["--jobs", "1"])
            .stdin(std::process::Stdio::null())
            .output()
            .unwrap()
    };

    // A record whose input is no longer this input is refused before any
    // build: nothing is published and the record is left alone.
    let mut tampered: Value = serde_json::from_slice(&fs::read(&envelope_path).unwrap()).unwrap();
    tampered["task_identity"]["source_sha256"] = json!("0".repeat(64));
    let genuine = fs::read(&envelope_path).unwrap();
    fs::write(
        &envelope_path,
        serde_json::to_vec_pretty(&tampered).unwrap(),
    )
    .unwrap();
    let refused = certify(&run);
    assert_eq!(refused.status.code(), Some(3), "{refused:?}");
    let refused_result: Value =
        serde_json::from_slice(&fs::read(input_directory.join("result.json")).unwrap()).unwrap();
    assert_eq!(refused_result["status"], "input_changed");
    assert!(
        !input_directory.join("Certificate").exists(),
        "a changed input publishes nothing"
    );
    assert_eq!(fs::read(&core_record).unwrap(), accepted_bytes);

    // Restored, the very same record certifies.
    fs::write(&envelope_path, &genuine).unwrap();
    fs::write(
        input_directory.join("result.json"),
        serde_json::to_vec_pretty(&json!({
            "input": PRODUCTION_TASK_ID,
            "schema_version": 3,
            "status": "valid_uncertified",
            "search_seconds": recorded_search_seconds,
        }))
        .unwrap(),
    )
    .unwrap();
    write_summary();
    let certified = certify(&run);
    assert_eq!(certified.status.code(), Some(0), "{certified:?}");
    let result: Value =
        serde_json::from_slice(&fs::read(input_directory.join("result.json")).unwrap()).unwrap();
    assert_eq!(result["status"], "valid");
    // Certification rewrites the verdict and leaves the search's own
    // measurement exactly as the run recorded it, equal to the envelope's.
    assert_eq!(result["search_seconds"], recorded_search_seconds);
    assert_eq!(
        result["search_seconds"],
        serde_json::from_slice::<Value>(&fs::read(&envelope_path).unwrap()).unwrap()["search"]["elapsed_seconds"]
    );
    assert!(input_directory.join("Certificate/Valid.lean").is_file());
    assert_eq!(
        result["certificate_module"],
        format!("Benchmark.{PRODUCTION_TASK_ID}.Certificate.Valid")
    );
    let axioms = result["axioms"]
        .as_array()
        .expect("a certified result names its axiom closure")
        .iter()
        .map(|axiom| axiom.as_str().unwrap().to_owned())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        axioms,
        ["Classical.choice", "Quot.sound", "propext"]
            .into_iter()
            .map(str::to_owned)
            .collect::<BTreeSet<_>>()
    );
    // The record the search wrote is the record the rows path built from,
    // unchanged: this is the guard against the two paths drifting.
    assert_eq!(fs::read(&core_record).unwrap(), accepted_bytes);
    let summary: Value =
        serde_json::from_slice(&fs::read(run.join("summary.json")).unwrap()).unwrap();
    assert_eq!(summary["all_certified"], true);
    assert_eq!(summary["all_accepted"], true);
    // The phase leaves no staging or lock behind.
    assert!(!input_directory.join("certify-staging").exists());
    assert!(!run.join(".certify-lock").exists());

    // Nothing the run recorded names this machine: every path the result
    // carries is relative to the input's own directory, which is what lets
    // the directory be certified somewhere else. A certified valid result
    // names its published tree; the acceptance-time `record`/`accepted` are
    // whatever the result it rewrote already held.
    assert!(result["certificate"].is_string());
    for field in ["record", "accepted", "certificate", "counterexample"] {
        let Some(value) = result[field].as_str() else {
            continue;
        };
        assert!(
            !Path::new(value).is_absolute() && !value.contains(std::path::MAIN_SEPARATOR),
            "{field} names a machine location: {value}"
        );
        assert!(
            input_directory.join(value).exists(),
            "{field} does not resolve"
        );
    }

    // The same directory, moved: every record it needs is inside it, so the
    // published tree revalidates from its new location without the search
    // being repeated.
    let moved = run
        .parent()
        .expect("the run directory has a parent")
        .join("elsewhere");
    copy_tree(&run, &moved).unwrap();
    fs::remove_dir_all(&run).unwrap();
    let elsewhere = certify(&moved);
    assert_eq!(elsewhere.status.code(), Some(0), "{elsewhere:?}");
    let moved_result: Value = serde_json::from_slice(
        &fs::read(moved.join(PRODUCTION_TASK_ID).join("result.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(moved_result["status"], "valid");
    assert_eq!(moved_result["certificate"], result["certificate"]);
    assert_eq!(
        moved_result["certificate_module"],
        result["certificate_module"]
    );
    assert_eq!(moved_result["search_seconds"], recorded_search_seconds);
    drop(directory);
}

/// Copy one directory tree onto a fresh path, so a run directory can be read
/// from somewhere other than where it was written.
fn copy_tree(from: &Path, to: &Path) -> std::io::Result<()> {
    fs::create_dir_all(to)?;
    for entry in fs::read_dir(from)? {
        let entry = entry?;
        let target = to.join(entry.file_name());
        if entry.file_type()?.is_dir() {
            copy_tree(&entry.path(), &target)?;
        } else {
            fs::copy(entry.path(), &target)?;
        }
    }
    Ok(())
}
