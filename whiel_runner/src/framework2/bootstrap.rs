//! One explicit construction path for the fixed-ambient runtime.

use std::fmt;
use std::sync::Arc;

use serde_json::Value;

use crate::encoding::{
    FixedAmbientWorkerBinding, FixedAmbientWorkerPoolConfig, new_fixed_ambient_encoding_context,
};
use crate::failure::FailureReport;
use crate::runtime::{CancellationToken, SolverAdmission};
use crate::task::SynthesisTask;

use super::admission::{
    FixedAmbientTaskBootstrap, FrameworkIIAdmissionContext, FrameworkIIAdmissionError,
    build_framework_ii_admission,
};
use super::catalog::{FrameworkIIStateError, LeveledClauseCatalog};
use super::host_limits::HostLimits;
use super::solver::{FrameworkIISolverContext, FrameworkIISolverError};
use super::stabilization::LeveledHoudiniState;
use super::tools::AgentToolPolicy;
use super::types::FrameworkIILevel;

/// Coherent authorities created from one explicitly selected V5 descriptor.
pub struct BoundFixedAmbientFrameworkII {
    task: Arc<SynthesisTask>,
    admission: FrameworkIIAdmissionContext,
    solver: FrameworkIISolverContext,
    houdini: LeveledHoudiniState,
    host_limits: HostLimits,
}

impl BoundFixedAmbientFrameworkII {
    pub fn task(&self) -> &Arc<SynthesisTask> {
        &self.task
    }

    pub fn admission(&self) -> &FrameworkIIAdmissionContext {
        &self.admission
    }

    pub fn solver(&self) -> &FrameworkIISolverContext {
        &self.solver
    }

    pub fn houdini(&self) -> &LeveledHoudiniState {
        &self.houdini
    }

    /// The run's host limits, exactly as they were handed in.
    ///
    /// Every other authority of the run is built from this one value: the
    /// bound state's `max_level`, the feedback policy the search is given,
    /// and the production check configuration. `PreCertificateAgentHoudiniSearch::new`
    /// rejects a run whose authorities carry different limits.
    pub fn host_limits(&self) -> &HostLimits {
        &self.host_limits
    }

    pub fn into_parts(
        self,
    ) -> (
        Arc<SynthesisTask>,
        FrameworkIIAdmissionContext,
        FrameworkIISolverContext,
        LeveledHoudiniState,
    ) {
        (self.task, self.admission, self.solver, self.houdini)
    }
}

/// Bind an already bounded worker-manifest result to one live V5 worker pool.
///
/// Executing the one-shot `manifest` command remains the campaign dispatcher's
/// responsibility. This function starts only the persistent worker protocol,
/// rechecks `describe`, and constructs the empty classification-free catalog.
///
/// `host_limits` is the run's single source of every optional host limit
/// (Pass 7.7b). The controller state's level bound is *derived* from
/// `level_bound` here rather than passed separately, so the state cannot
/// enforce a bound the presentation does not state; the same value must then
/// reach the feedback policy and the production check configuration, which
/// `PreCertificateAgentHoudiniSearch::new` verifies.
#[allow(clippy::too_many_arguments)]
pub async fn bind_fixed_ambient_framework_ii(
    descriptor: Value,
    workers: FixedAmbientWorkerPoolConfig,
    catalog_instance_digest: impl Into<Arc<str>>,
    host_limits: HostLimits,
    compress_core: bool,
    tool_policy: AgentToolPolicy,
    solver_admission: &SolverAdmission,
    cancellation: &CancellationToken,
) -> Result<BoundFixedAmbientFrameworkII, FrameworkIIBindError> {
    let bootstrap = FixedAmbientTaskBootstrap::from_json(descriptor)?;
    let binding = FixedAmbientWorkerBinding::from_task(
        bootstrap.task(),
        bootstrap.scope().identity().clone(),
    )
    .map_err(FrameworkIIBindError::Binding)?;
    let encoding = new_fixed_ambient_encoding_context(
        binding,
        bootstrap
            .scope()
            .relations()
            .iter()
            .map(|relation| relation.key().clone()),
        bootstrap.task().solver_constants().iter().cloned(),
        workers,
    )?;

    let admission =
        match build_framework_ii_admission(&encoding, &bootstrap, solver_admission, cancellation)
            .await
        {
            Ok(admission) => admission,
            Err(error) => {
                let _ = encoding.shutdown().await;
                return Err(error.into());
            }
        };
    let catalog =
        match LeveledClauseCatalog::new(admission.scope().clone(), catalog_instance_digest) {
            Ok(catalog) => catalog,
            Err(error) => {
                let _ = encoding.shutdown().await;
                return Err(error.into());
            }
        };
    let solver = FrameworkIISolverContext::from_admission(&admission);
    // Lean's protected EDB-precondition rows are reserved before any external
    // registration so they receive the lowest catalog identities.
    if let Err(error) = solver
        .reserve_precondition_system_clauses(&catalog, solver_admission, cancellation)
        .await
    {
        let _ = encoding.shutdown().await;
        return Err(error.into());
    }
    let houdini = match LeveledHoudiniState::new_with_options(
        catalog,
        host_limits.level_bound.map(FrameworkIILevel::new),
        compress_core,
        std::collections::BTreeSet::new(),
        std::collections::BTreeSet::new(),
        tool_policy,
    ) {
        Ok(houdini) => houdini,
        Err(error) => {
            let _ = encoding.shutdown().await;
            return Err(error.into());
        }
    };
    Ok(BoundFixedAmbientFrameworkII {
        task: Arc::new(bootstrap.task().clone()),
        admission,
        solver,
        houdini,
        host_limits,
    })
}

#[derive(Clone, Debug)]
pub enum FrameworkIIBindError {
    Binding(&'static str),
    Admission(FrameworkIIAdmissionError),
    Solver(FrameworkIISolverError),
    Failure(FailureReport),
    State(FrameworkIIStateError),
}

impl From<FrameworkIISolverError> for FrameworkIIBindError {
    fn from(error: FrameworkIISolverError) -> Self {
        Self::Solver(error)
    }
}

impl From<FrameworkIIAdmissionError> for FrameworkIIBindError {
    fn from(error: FrameworkIIAdmissionError) -> Self {
        Self::Admission(error)
    }
}

impl From<FailureReport> for FrameworkIIBindError {
    fn from(error: FailureReport) -> Self {
        Self::Failure(error)
    }
}

impl From<FrameworkIIStateError> for FrameworkIIBindError {
    fn from(error: FrameworkIIStateError) -> Self {
        Self::State(error)
    }
}

impl fmt::Display for FrameworkIIBindError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Binding(detail) => write!(formatter, "fixed-ambient worker binding: {detail}"),
            Self::Admission(error) => error.fmt(formatter),
            Self::Solver(error) => error.fmt(formatter),
            Self::Failure(report) => write!(
                formatter,
                "fixed-ambient runtime: origin={:?} kind={:?} detail={}",
                report.origin(),
                report.kind(),
                report.detail().unwrap_or("none"),
            ),
            Self::State(error) => error.fmt(formatter),
        }
    }
}

impl std::error::Error for FrameworkIIBindError {}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;
    use std::path::{Path, PathBuf};
    use std::process::Command;

    use serde_json::{Value, json};

    use super::*;
    use crate::encoding::{FixedAmbientWorkerCommand, canonical_value_sha256};
    use crate::framework2::{
        AdmissionOutcome, ExtendedClauseOrigin, FrameworkIICheckEvidence, FrameworkIICheckOutcome,
        FrameworkIICheckRequest, FrameworkIICheckRole, LeveledStabilizationOutcome,
        SyncFrameworkIIChecker, stabilize_leveled_houdini_with_system_clauses,
    };
    use crate::runtime::{RuntimeResourcePolicy, create_general_solver_admission};

    #[derive(Debug, PartialEq, Eq)]
    struct LiveRunIdentity {
        scope: Value,
        snapshot: Value,
        rows: Vec<(u64, u64)>,
        jobs: Vec<Value>,
    }

    fn repository_root() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("whiel_runner lives below the repository root")
            .to_path_buf()
    }

    fn live_worker() -> Option<(PathBuf, PathBuf)> {
        let root = repository_root();
        let executable = root.join(".lake/build/bin/fixed_ambient_encoding_worker");
        executable.is_file().then_some((root, executable))
    }

    fn manifest(root: &Path, executable: &Path) -> Value {
        let output = Command::new(executable)
            .arg("manifest")
            .current_dir(root)
            .output()
            .expect("run the checked-in fixed-ambient fixture manifest");
        assert!(
            output.status.success(),
            "fixture manifest failed: {}",
            String::from_utf8_lossy(&output.stderr),
        );
        serde_json::from_slice(&output.stdout).expect("fixture manifest emits one JSON value")
    }

    async fn run_live(worker_count: usize) -> LiveRunIdentity {
        let Some((root, executable)) = live_worker() else {
            eprintln!("skipping live fixed-ambient test: build the Lean worker first");
            return LiveRunIdentity {
                scope: Value::Null,
                snapshot: Value::Null,
                rows: Vec::new(),
                jobs: Vec::new(),
            };
        };
        let descriptor = manifest(&root, &executable);
        let worker = FixedAmbientWorkerCommand::new(executable, &root);
        let pool = FixedAmbientWorkerPoolConfig::new(worker, worker_count).unwrap();
        let admission = create_general_solver_admission(
            RuntimeResourcePolicy::agent_only(worker_count.max(2), worker_count.max(2)).unwrap(),
        )
        .unwrap();
        let cancellation = CancellationToken::new();
        let bound = bind_fixed_ambient_framework_ii(
            descriptor,
            pool,
            "4".repeat(64),
            HostLimits::UNBOUNDED,
            false,
            AgentToolPolicy::default(),
            &admission,
            &cancellation,
        )
        .await
        .unwrap();
        assert_eq!(bound.task().identity().canonical_id(), "Example0001");
        let (task, clause_admission, solver, mut houdini) = bound.into_parts();
        // The input's computed precondition has no EDB-only conjunct, so Lean
        // reserves no protected row before external registration.
        let reserved = houdini.catalog().len().unwrap();
        assert_eq!(reserved, 0);
        assert!(!houdini.system_installation_pending().unwrap());

        let sources = [
            "(op_zT = ∅[2])".to_owned(),
            "(yp_zT = ∅[2])".to_owned(),
            "(op_zS = ∅[2])".to_owned(),
        ];
        let admitted = clause_admission
            .admit_clauses(&sources, None, &admission, &cancellation)
            .await
            .unwrap();
        let AdmissionOutcome::Accepted(clauses) = admitted else {
            panic!("the fixed fixture clauses must be accepted")
        };
        assert_eq!(clauses.len(), sources.len());
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
        let mut checker = SyncFrameworkIIChecker::new(|request: FrameworkIICheckRequest| {
            Ok(FrameworkIICheckOutcome::Proved(
                FrameworkIICheckEvidence::new(
                    request.request_digest(),
                    format!("live-scripted-proof:{}", request.request_digest()),
                )
                .unwrap(),
            ))
        });
        let LeveledStabilizationOutcome::Stabilized(core) =
            stabilize_leveled_houdini_with_system_clauses(&mut houdini, &mut checker)
                .await
                .unwrap()
        else {
            panic!("the all-proved fixture must stabilize")
        };
        // Root coverage is provenance only: a committed clause is never
        // re-checked, so a scan that commits at several levels ordinarily
        // ends with partial coverage. Certification re-proves every
        // condition of the frozen final Core regardless.
        assert!(!houdini.system_installation_pending().unwrap());
        assert!(houdini.system_clauses().is_empty());
        let expected_rows = sources.len();

        let rows = core
            .snapshot()
            .canonical_order()
            .iter()
            .map(|clause| {
                (
                    clause.get(),
                    core.snapshot().level_of(*clause).unwrap().get(),
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(rows.len(), expected_rows);
        assert!(rows.iter().any(|(_, level)| *level == 0));
        assert!(rows.iter().any(|(_, level)| *level == 1));

        // Committed clauses are never re-checked during search, so only some
        // roots are still current at the end of a scan. Certification
        // re-proves all 2N+1 conditions of the frozen Core regardless, so
        // the obligations are built from the Core snapshot directly.
        let mut requests = Vec::new();
        let mut ordinal = 0_u64;
        for clause in core.snapshot().canonical_order() {
            for role in [
                FrameworkIICheckRole::Initialization,
                FrameworkIICheckRole::Maintenance,
            ] {
                let level = core.snapshot().level_of(*clause).unwrap();
                requests.push(
                    super::super::ledger::FrameworkIICheckRequest::new(
                        ordinal,
                        *clause,
                        level,
                        role,
                        Arc::clone(core.snapshot()),
                        false,
                    )
                    .unwrap(),
                );
                ordinal += 1;
            }
        }
        assert_eq!(requests.len(), expected_rows * 2);

        let mut jobs = tokio::task::JoinSet::new();
        for request in requests {
            let solver = solver.clone();
            let admission = admission.clone();
            let cancellation = cancellation.clone();
            jobs.spawn(async move {
                solver
                    .build_obligation(&request, &admission, &cancellation)
                    .await
                    .map(|obligation| obligation.obligation_identity().clone())
            });
        }
        let mut identities = Vec::new();
        while let Some(result) = jobs.join_next().await {
            identities.push(result.unwrap().unwrap());
        }
        let termination = solver
            .build_termination_obligation(core.snapshot(), &admission, &cancellation)
            .await
            .unwrap();
        identities.push(termination.obligation_identity().clone());
        identities.sort_by_key(canonical_value_sha256);
        let distinct = identities
            .iter()
            .map(canonical_value_sha256)
            .collect::<BTreeSet<_>>();
        assert_eq!(identities.len(), expected_rows * 2 + 1);
        assert_eq!(distinct.len(), identities.len());
        assert_eq!(
            identities
                .iter()
                .filter(|identity| identity["selector"]["kind"] == json!("initialization"))
                .count(),
            expected_rows,
        );
        assert_eq!(
            identities
                .iter()
                .filter(|identity| identity["selector"]["kind"] == json!("maintenance"))
                .count(),
            expected_rows,
        );
        assert_eq!(
            identities
                .iter()
                .filter(|identity| identity["selector"]["kind"] == json!("termination"))
                .count(),
            1,
        );
        assert!(identities.iter().all(|identity| {
            identity["scope_identity"] == *core.snapshot().scope().identity()
                && identity["snapshot"] == core.snapshot().worker_identity()
        }));
        assert_eq!(task.identity(), core.snapshot().scope().task_identity());

        let outcome = LiveRunIdentity {
            scope: core.snapshot().scope().identity().clone(),
            snapshot: core.snapshot().worker_identity(),
            rows,
            jobs: identities,
        };
        solver.shutdown().await.unwrap();
        outcome
    }

    #[tokio::test(flavor = "multi_thread", worker_threads = 4)]
    async fn fixed_ambient_fixture_matches_in_serial_and_bounded_pool_modes() {
        let serial = run_live(1).await;
        let pooled = run_live(3).await;
        assert_eq!(serial, pooled);
    }
}

#[cfg(test)]
mod resume_tests {
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::process::Command;
    use std::sync::{Arc, Mutex};
    use std::time::Duration;

    use serde_json::{Value, json};

    use super::*;
    use crate::FailureKind;
    use crate::artifact::{ArtifactStoreConfig, new_artifact_store};
    use crate::encoding::FixedAmbientWorkerCommand;
    use crate::framework2::agent::AGENT_HOUDINI_PROTOCOL_VERSION;
    use crate::framework2::{
        Agent, AgentConsultationLimits, AgentConsultationPolicy, AgentFeedbackLimits,
        AgentFeedbackPolicy, AgentProvider, AgentPush, AgentResponseWriter,
        AgentSourceCancellation, AgentSourceFuture, AgentSourceOutcome, AgentToolSurface,
        FrameworkIICertificationProfiles, FrameworkIIProductionCheckConfig,
        LeancheckCertificationProfile, PreCertificateAgentHoudiniLimits,
        PreCertificateAgentHoudiniOutcome, PreCertificateAgentHoudiniRuntime,
        PreCertificateAgentHoudiniSearch, ProofSearchProfile, SolverInvocationIdentity,
    };
    use crate::runtime::{RuntimeResourcePolicy, create_general_solver_admission};
    use crate::vampire::{VampireSearchBudget, VampireWorkerCommand};

    struct TestDirectory(PathBuf);

    impl TestDirectory {
        fn new(label: &str) -> Self {
            let path = std::env::temp_dir().join(format!(
                "whiel_runner_{label}_{}_{}",
                std::process::id(),
                std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_nanos()
            ));
            fs::create_dir_all(&path).unwrap();
            Self(path)
        }

        fn path(&self) -> &Path {
            &self.0
        }
    }

    impl Drop for TestDirectory {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    fn repository_root() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("whiel_runner lives below the repository root")
            .to_path_buf()
    }

    fn live_worker() -> Option<(PathBuf, PathBuf)> {
        let root = repository_root();
        let executable = root.join(".lake/build/bin/fixed_ambient_encoding_worker");
        executable.is_file().then_some((root, executable))
    }

    fn manifest(root: &Path, executable: &Path) -> Value {
        let output = Command::new(executable)
            .arg("manifest")
            .current_dir(root)
            .output()
            .expect("run the checked-in fixed-ambient fixture manifest");
        assert!(output.status.success());
        serde_json::from_slice(&output.stdout).expect("fixture manifest emits one JSON value")
    }

    /// A proof-only Vampire stand-in that ignores its problem.
    fn proof_vampire(directory: &Path) -> VampireWorkerCommand {
        let script = directory.join("proof-vampire.py");
        fs::write(
            &script,
            "print('% SZS status Theorem for problem')\n\
             print('% SZS output start Proof for problem')\n\
             print('1. $false [fixture]')\n\
             print('% SZS output end Proof for problem')\n",
        )
        .unwrap();
        VampireWorkerCommand::new("python3")
            .with_extra_args([script.into_os_string()])
            .unwrap()
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

    /// Proposes one clause on the first consultation and nothing afterwards.
    ///
    /// Also records the run's session mode as the controller announces it,
    /// which is as much as a synchronous in-process provider can honour: it
    /// keeps no conversation of its own, so `Fresh` and `Continuous` differ
    /// for it only in what it is told.
    struct HandoffProvider {
        observed: Arc<Mutex<Vec<Value>>>,
    }

    impl AgentProvider for HandoffProvider {
        fn quiesce_request(&mut self) -> crate::proposer_api::ProposerCleanupFuture<'_> {
            Box::pin(async { Ok(()) })
        }
        fn shutdown(
            &mut self,
            _reason: crate::proposer_api::wire::ShutdownReason,
        ) -> crate::proposer_api::ProposerCleanupFuture<'_> {
            self.quiesce_request()
        }

        fn consult<'a>(
            &'a mut self,
            request: &'a AgentPush,
            _tools: &'a dyn AgentToolSurface,
            response: &'a mut AgentResponseWriter,
            _cancellation: AgentSourceCancellation,
        ) -> AgentSourceFuture<'a> {
            let request_value: Value = serde_json::from_slice(request.bytes()).unwrap();
            assert_eq!(
                request_value["schema_version"],
                json!(AGENT_HOUDINI_PROTOCOL_VERSION)
            );
            self.observed.lock().unwrap().push(request_value.clone());
            let binding = &request_value["binding"];
            let clauses = if request_value["feedback"]["iteration"] == json!(1) {
                assert_eq!(request_value["feedback"]["latest"]["kind"], "initial");
                vec!["(op_zT = ∅[2])"]
            } else {
                // Every later push states why the postcondition is still
                // open: the epoch's termination check was refuted or
                // inconclusive.
                assert_eq!(
                    request_value["feedback"]["latest"]["kind"],
                    "postcondition_open"
                );
                Vec::new()
            };
            let response_value = json!({
                "kind": "candidate_clauses",
                "schema_version": AGENT_HOUDINI_PROTOCOL_VERSION,
                "binding": {
                    "task_digest": binding["task_digest"],
                    "scope_digest": binding["scope_digest"],
                    "run_digest": binding["run_digest"],
                    "consultation_digest": binding["consultation_digest"],
                    "state_snapshot_digest": binding["state_snapshot_digest"],
                    "validation_manifest_digest": binding["validation_manifest_digest"],
                    "request_digest": request.digest(),
                    "validation_ordinal": request.validation_ordinal(),
                },
                "clauses": clauses,
                "dropped": [],
            });
            let _ = response.write_chunk(&serde_json::to_vec(&response_value).unwrap());
            Box::pin(async { AgentSourceOutcome::Response })
        }
    }

    #[tokio::test(flavor = "multi_thread", worker_threads = 4)]
    async fn live_continuous_run_reaches_the_termination_check_every_epoch() {
        let Some((root, executable)) = live_worker() else {
            eprintln!("skipping live fixed-ambient search test: build the Lean worker first");
            return;
        };
        let directory = TestDirectory::new("fixed_ambient_resume");
        let descriptor = manifest(&root, &executable);
        let worker = FixedAmbientWorkerCommand::new(executable, &root);
        let pool = FixedAmbientWorkerPoolConfig::new(worker, 1).unwrap();
        let solver_admission =
            create_general_solver_admission(RuntimeResourcePolicy::agent_only(1, 1).unwrap())
                .unwrap();
        let cancellation = CancellationToken::new();
        // Pass 7.7b: one source for the run's host limits. The same value
        // binds the controller state, configures the production checker,
        // and is declared to the proposer in the standing presentation.
        let host_limits = HostLimits {
            countermodel_retention_tuples: Some(2),
            ..HostLimits::UNBOUNDED
        };
        let feedback_policy = AgentFeedbackPolicy::new(AgentFeedbackLimits {
            host_limits,
            ..AgentFeedbackLimits::default()
        })
        .unwrap();
        let bound = bind_fixed_ambient_framework_ii(
            descriptor,
            pool,
            "5".repeat(64),
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

        // Proof lane only: `proof_vampire` answers one proof call and nothing
        // else, and this test's subject is the continuous run loop reaching its
        // termination check, not what a finite-model lane would find.
        let config = FrameworkIIProductionCheckConfig::new_proof_only_not_a_campaign_configuration(
            artifacts.clone(),
            solver_admission.clone(),
            VampireSearchBudget::finite(Duration::from_secs(5)),
            proof_vampire(directory.path()),
            cancellation.clone(),
            "fixture-vampire",
            certification_profiles(),
        )
        .unwrap()
        .with_host_limits(host_limits);
        // The checker truncates a validated countermodel at exactly the
        // limit the policy declares, and nowhere else.
        assert_eq!(config.countermodel_tuple_bound(), Some(2));
        let checker = solver.clone().production_checker(config);
        assert_eq!(
            crate::framework2::FrameworkIIChecker::host_limits(&checker),
            Some(&host_limits),
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
        let agent = Agent::new(
            HandoffProvider {
                observed: Arc::clone(&observed),
            },
            AgentConsultationPolicy::new(AgentConsultationLimits::default()).unwrap(),
        );
        let overall_limit = Duration::from_secs(30);
        let search = PreCertificateAgentHoudiniSearch::new(
            Arc::clone(&task),
            agent,
            houdini,
            runtime,
            PreCertificateAgentHoudiniLimits::new(overall_limit, None, Some(2)),
            tokio::time::Instant::now() + overall_limit,
            feedback_policy,
        )
        .unwrap();

        // Every epoch ends with the termination check, so the search either
        // ends Valid with the frozen Core or keeps consulting until its
        // iteration limit. There is no pre-termination handoff any more.
        let outcome = search.run().await;
        let termination_attempts = match &outcome {
            PreCertificateAgentHoudiniOutcome::Valid(handoff) => {
                let inspection = handoff.inspection().unwrap();
                assert!(inspection.core_is_current());
                inspection.termination_attempts_total()
            }
            PreCertificateAgentHoudiniOutcome::Failure(report) => {
                assert_eq!(report.kind(), FailureKind::IterationLimitExhausted);
                u64::try_from(observed.lock().unwrap().len()).unwrap()
            }
            PreCertificateAgentHoudiniOutcome::Invalid(record) => {
                panic!(
                    "a clause-only provider cannot end the run invalid: {}",
                    record.instance_identity()
                )
            }
        };
        assert!(
            termination_attempts >= 1,
            "an epoch must run its termination check"
        );

        {
            let observed = observed.lock().unwrap();
            assert!(!observed.is_empty());
            for (index, push) in observed.iter().enumerate() {
                let feedback = &push["feedback"];
                assert_eq!(
                    feedback["schema_version"],
                    json!(crate::proposer_api::version::AGENT_FEEDBACK_SCHEMA_VERSION)
                );
                assert_eq!(
                    feedback["presentation"]["schema_version"],
                    json!(crate::proposer_api::version::AGENT_PRESENTATION_SCHEMA_VERSION)
                );
                assert!(feedback.get("pending").unwrap().is_array());
                assert!(feedback.get("retry").is_none());
                assert_eq!(
                    feedback["iteration"],
                    json!(u64::try_from(index).unwrap() + 1)
                );
                // The one limit this run sets is the one the standing
                // presentation states, with the value the checker applies.
                assert_eq!(
                    feedback["presentation"]["host_limits"],
                    json!([{"limit": "countermodel_retention_tuples", "value": 2}]),
                );
            }
        }

        solver.shutdown().await.unwrap();
        drop(solver);
        drop(admission);
        drop(artifacts);
        owner.settle().unwrap();
    }
}
