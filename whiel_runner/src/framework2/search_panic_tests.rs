//! Engine-poll unwind coverage with a real generic endpoint and Lean admission.

use super::*;
use crate::encoding::{FixedAmbientWorkerCommand, FixedAmbientWorkerPoolConfig};
use crate::framework2::catalog::FrameworkIIStateError;
use crate::framework2::ledger::FrameworkIICheckRequest;
use crate::framework2::production::{
    FrameworkIICountermodelInstance, FrameworkIIRefutationSummary, FrameworkIIRetainedCountermodel,
};
use crate::framework2::stabilization::{FrameworkIICheckExecution, sealed};
use crate::proposer_host::generic_process::{GenericProcessConfig, GenericProcessProposer};
use crate::runtime::create_general_solver_admission;
use std::fs;
use std::path::PathBuf;
use std::pin::Pin;
use std::process::Command;

struct PanickingChecker;
impl sealed::Sealed for PanickingChecker {}
impl FrameworkIIChecker for PanickingChecker {
    fn check<'a>(
        &'a mut self,
        _request: FrameworkIICheckRequest,
    ) -> Pin<
        Box<
            dyn Future<Output = Result<FrameworkIICheckExecution, FrameworkIIStateError>>
                + Send
                + 'a,
        >,
    > {
        // This is the verifier future, after the provider's request is closed;
        // it deliberately never returns proof or refutation evidence.
        Box::pin(async { panic!("intentional engine checker polling panic") })
    }
    fn matches_search_runtime(
        &self,
        _solver: &FrameworkIISolverContext,
        _artifacts: &ArtifactStore,
        _admission: &SolverAdmission,
        _cancellation: &CancellationToken,
    ) -> bool {
        true
    }
}
impl FrameworkIIQueryChecker for PanickingChecker {
    fn countermodel_of_attempt(
        &self,
        _attempt: crate::AttemptId,
    ) -> Option<&FrameworkIIRetainedCountermodel> {
        None
    }
    fn strongest_refutations(
        &self,
        _clause: &str,
        _cap: Option<usize>,
    ) -> Vec<FrameworkIIRefutationSummary> {
        Vec::new()
    }
    fn retained_countermodel_entries(
        &self,
    ) -> Box<dyn Iterator<Item = (u64, &FrameworkIICountermodelInstance)> + '_> {
        Box::new(std::iter::empty())
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn engine_poll_panic_joins_idle_endpoint_descendant_and_captures_before_unwind() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .to_owned();
    let build = Command::new("bash")
        .arg(repository.join("scripts/lake_build_watched.sh"))
        .arg("fixed_ambient_encoding_worker")
        .current_dir(&repository)
        .output()
        .unwrap();
    assert!(
        build.status.success(),
        "{}",
        String::from_utf8_lossy(&build.stderr)
    );
    let worker = repository.join(".lake/build/bin/fixed_ambient_encoding_worker");
    let manifest = Command::new(&worker)
        .args(["manifest", "Example0001"])
        .current_dir(&repository)
        .output()
        .unwrap();
    assert!(manifest.status.success());
    let descriptor = serde_json::from_slice(&manifest.stdout).unwrap();
    let cancellation = CancellationToken::new();
    let solver_admission =
        create_general_solver_admission(RuntimeResourcePolicy::agent_only(1, 1).unwrap()).unwrap();
    let bound = crate::framework2::bind_fixed_ambient_framework_ii(
        descriptor,
        FixedAmbientWorkerPoolConfig::new(FixedAmbientWorkerCommand::new(worker, &repository), 1)
            .unwrap(),
        "a".repeat(64),
        super::super::host_limits::HostLimits::UNBOUNDED,
        false,
        AgentToolPolicy::default(),
        &solver_admission,
        &cancellation,
    )
    .await
    .unwrap();
    let (task, admission, solver, houdini) = bound.into_parts();
    let directory = std::env::temp_dir().join(format!(
        "whiel_engine_panic_{}_{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    fs::create_dir(&directory).unwrap();
    let (owner, artifacts) = crate::artifact::new_artifact_store(
        &task,
        crate::artifact::ArtifactStoreConfig::new(&directory),
    )
    .unwrap();
    let trace = directory.join("api.jsonl");
    let identities = directory.join("processes.json");
    let wrapper = directory.join("endpoint.py");
    fs::write(&wrapper, r#"import json,os,runpy,signal,subprocess,sys,time
child = subprocess.Popen([sys.executable, '-c', 'import signal,time; signal.signal(signal.SIGTERM,signal.SIG_IGN); time.sleep(60)'], start_new_session=True)
with open(sys.argv[1], 'w') as output:
    json.dump({'endpoint':os.getpid(), 'descendant':child.pid},output)
# Keep both capture streams inherited by the detached child. Allow the existing
# process identity observer one ordinary interval before any request completes.
print('endpoint stdout capture',flush=True)
print('endpoint stderr capture',file=sys.stderr,flush=True)
time.sleep(.15)
fixture,trace=sys.argv[2:]
sys.argv=[fixture,'--trace',trace,'--mode','full']
runpy.run_path(fixture,run_name='__main__')
"#).unwrap();
    let python = std::env::split_paths(&std::env::var_os("PATH").unwrap())
        .map(|p| p.join("python3"))
        .find(|p| p.is_file())
        .unwrap()
        .canonicalize()
        .unwrap();
    let provider = GenericProcessProposer::start(
        GenericProcessConfig::new(
            python,
            vec![
                "-I".into(),
                wrapper.into_os_string(),
                identities.clone().into_os_string(),
                repository
                    .join("whiel_runner/tests/fixtures/generic_api_acceptance.py")
                    .into_os_string(),
                trace.clone().into_os_string(),
            ],
        ),
        &AgentToolPolicy::default().enabled_names(),
        &cancellation,
    )
    .await
    .unwrap();
    let scratch = provider.scratch_directory().to_owned();
    let runtime = PreCertificateAgentHoudiniRuntime::new(
        admission.clone(),
        solver.clone(),
        solver_admission.clone(),
        PanickingChecker,
        artifacts.clone(),
        cancellation.clone(),
        AgentToolPolicy::default(),
    );
    let search = PreCertificateAgentHoudiniSearch::new_with_joined_cleanup(
        task.clone(),
        Agent::with_default_policy(provider),
        houdini,
        runtime,
        PreCertificateAgentHoudiniLimits::new(Duration::from_secs(30), None, Some(4)),
        Instant::now() + Duration::from_secs(30),
        AgentFeedbackPolicy::default(),
    )
    .await
    .unwrap();
    let error = tokio::spawn(search.run()).await.unwrap_err();
    assert!(error.is_panic());
    let payload = error.into_panic();
    assert_eq!(
        payload.downcast_ref::<&str>().copied(),
        Some("intentional engine checker polling panic")
    );
    assert!(cancellation.is_cancelled());
    let processes: serde_json::Value =
        serde_json::from_slice(&fs::read(&identities).unwrap()).unwrap();
    for kind in ["endpoint", "descendant"] {
        let pid = processes[kind].as_u64().unwrap();
        let result = Command::new("/bin/ps")
            .args(["-o", "stat=", "-p", &pid.to_string()])
            .output()
            .unwrap();
        let state = String::from_utf8_lossy(&result.stdout);
        assert!(
            state.trim().is_empty() || state.trim().starts_with('Z'),
            "{kind} still live after unwind: {pid} {state}"
        );
    }
    // The child supervisor retains this directory until BOTH stdout/stderr
    // capture threads join. No extra wait or cleanup call may mask early unwind.
    assert!(
        !scratch.exists(),
        "endpoint/capture owner remains after unwind"
    );
    let events: Vec<serde_json::Value> = fs::read_to_string(&trace)
        .unwrap()
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect();
    assert_eq!(
        events
            .iter()
            .filter(|event| event["kind"] == "submission")
            .count(),
        2
    );
    assert_eq!(
        events.last().unwrap()["kind"],
        "closed",
        "idle endpoint received terminal shutdown after its request closed"
    );
    solver.shutdown().await.unwrap();
    drop((solver, admission, solver_admission, task, artifacts));
    owner.settle().unwrap();
    fs::remove_dir_all(directory).unwrap();
}
