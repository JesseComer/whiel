mod support;

use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

#[cfg(unix)]
use std::os::unix::fs::PermissionsExt;

use whiel_runner::artifact::MaintenanceHistoryCursor;
use whiel_runner::encoding::{
    EncodingWorkerCommand, EncodingWorkerPoolConfig, QfSolverSource, SolverBodySource,
    SolverEncodingContext, new_solver_encoding_context,
};
use whiel_runner::{
    ArtifactKind, ArtifactStore, ArtifactStoreConfig, CancellationToken, ClauseCatalog,
    ClauseFormula, ClauseId, ClauseSet, ConstantKey, CoverageLookup, CoverageMode, FailureScope,
    HoudiniState, InitializationInvocationOutcome, InitializationStatus, MaintenanceBlockOutcome,
    MaintenanceExecutionOutcome, MaintenancePolicy, MaintenancePreparationOutcome,
    MaintenanceResultClass, MaintenanceResultDisposition, MaintenanceTrackHint,
    MaintenanceTrackKind, RuntimeResourcePolicy, SolverAdmission, TelemetryConfig, TelemetryHandle,
    TelemetryLevel, TelemetrySession, TrackLayout, VampireWorkerCommand, VerificationParameters,
    create_general_solver_admission, new_artifact_store, prepare_maintenance,
    run_maintenance_block, run_maintenance_block_sequential, run_maintenance_blocks,
    run_maintenance_blocks_sequential,
};

// ------------------------------------------------------------
// Concurrent Maintenance Fixtures
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

fn gated_malformed_support_worker_config(
    gate: &Path,
    fault_marker: &Path,
) -> EncodingWorkerPoolConfig {
    let command = EncodingWorkerCommand::new(
        support::gated_malformed_support_encoding_worker(),
        support::repository_root(),
    )
    .arguments([
        support::example_encoding_worker().as_os_str().to_owned(),
        gate.as_os_str().to_owned(),
        fault_marker.as_os_str().to_owned(),
    ]);
    EncodingWorkerPoolConfig::new(command, 2).expect("positive worker count")
}

fn runtime_policy() -> RuntimeResourcePolicy {
    RuntimeResourcePolicy::agent_only(4, 2).unwrap()
}

fn admission(policy: RuntimeResourcePolicy) -> SolverAdmission {
    create_general_solver_admission(policy).unwrap()
}

fn formula(
    task: &whiel_runner::SynthesisTask,
    canonical: &str,
    source_id: &str,
    relations: &[&str],
) -> ClauseFormula {
    formula_with_constants(task, canonical, source_id, &[], relations)
}

fn formula_with_constants(
    task: &whiel_runner::SynthesisTask,
    canonical: &str,
    source_id: &str,
    constants: &[&str],
    relations: &[&str],
) -> ClauseFormula {
    let constants = constants
        .iter()
        .map(|key| ConstantKey::from_canonical(*key).unwrap())
        .collect::<Vec<_>>();
    let relations = relations
        .iter()
        .map(|key| {
            task.solver_relations()
                .iter()
                .find(|relation| relation.key().as_str() == *key)
                .expect("fixture relation")
                .key()
                .clone()
        })
        .collect::<Vec<_>>();
    let source = SolverBodySource::QuantifierFree(
        QfSolverSource::new(task, source_id, constants, relations).unwrap(),
    );
    ClauseFormula::from_trusted_lean_source(canonical, source).unwrap()
}

fn mixed_constant_wp(task: &whiel_runner::SynthesisTask, canonical: &str) -> ClauseFormula {
    formula_with_constants(
        task,
        canonical,
        "task.phase2c_qf_mixed_constants",
        &["num:10", "str:mixed", "bool:0", "num:2"],
        &[],
    )
}

fn vampire_command(fixture: &str, launch_log: Option<&Path>) -> VampireWorkerCommand {
    let mut arguments = vec![
        OsString::from("--fixture"),
        OsString::from(fixture),
        OsString::from("--expect-start"),
        OsString::from("1"),
    ];
    if let Some(path) = launch_log {
        arguments.push(OsString::from("--launch-log"));
        arguments.push(path.as_os_str().to_owned());
    }
    VampireWorkerCommand::new(support::fake_vampire())
        .with_extra_args(arguments)
        .unwrap()
}

#[cfg(unix)]
fn overlap_worker(root: &Path) -> VampireWorkerCommand {
    let executable = root.join("overlap-vampire.sh");
    let starts = root.join("proof-starts");
    std::fs::create_dir_all(&starts).unwrap();
    std::fs::write(
        &executable,
        r#"#!/bin/sh
mode=proof
start_dir=
while [ "$#" -gt 0 ]; do
  if [ "$1" = "--saturation_algorithm" ]; then mode=fmb; fi
  if [ "$1" = "--event-log" ]; then shift; start_dir=$1; fi
  shift
done
if [ "$mode" = "fmb" ]; then
  while :; do sleep 1; done
fi
# Use an atomic directory creation to elect one proof process as the barrier
# waiter. The other proof process publishes the release marker. This tests the
# same cross-track overlap without launching find/wc/tr subprocesses in a hot
# polling loop. The enclosing solver deadline remains the sole failure bound.
if mkdir "$start_dir/first-proof" 2>/dev/null; then
  while [ ! -e "$start_dir/second-proof" ]; do sleep 0.05; done
else
  : > "$start_dir/second-proof"
fi
printf '%s\n' '% SZS status Theorem for problem'
printf '%s\n' '% SZS output start Proof for problem'
printf '%s\n' '1. $false [overlap fixture]'
printf '%s\n' '% SZS output end Proof for problem'
"#,
    )
    .unwrap();
    let mut permissions = std::fs::metadata(&executable).unwrap().permissions();
    permissions.set_mode(0o755);
    std::fs::set_permissions(&executable, permissions).unwrap();
    VampireWorkerCommand::new(executable)
        .with_extra_args([OsString::from("--event-log"), starts.as_os_str().to_owned()])
        .unwrap()
}

#[cfg(unix)]
fn late_result_worker(root: &Path, late_outcome: &str) -> VampireWorkerCommand {
    let executable = root.join(format!("late-{late_outcome}-vampire.sh"));
    std::fs::write(
        &executable,
        r#"#!/bin/sh
mode=proof
late_outcome=
problem=
while [ "$#" -gt 0 ]; do
  case "$1" in
    --saturation_algorithm)
      shift
      if [ "$1" = "fmb" ]; then mode=fmb; fi
      ;;
    --late-outcome)
      shift
      late_outcome=$1
      ;;
    *) problem=$1 ;;
  esac
  shift
done
goal=$(grep '^fof(goal,' "$problem")
if [ "$goal" = 'fof(goal, conjecture, (($true))).' ]; then
  source=yes
else
  source=no
fi
hang() {
  while :; do sleep 1; done
}
unknown() {
  printf '%s\n' '% SZS status GaveUp for problem'
}
proof() {
  printf '%s\n' '% SZS status Theorem for problem'
  printf '%s\n' '% SZS output start Proof for problem'
  printf '%s\n' '1. $false [late-result fixture]'
  printf '%s\n' '% SZS output end Proof for problem'
}
model() {
  printf '%s\n' '% TRYING [1]'
  printf '%s\n' '% SZS status CounterSatisfiable for problem'
  printf '%s\n' '% SZS output start FiniteModel for problem'
  printf '%s\n' 'fof(fixture_model, fi_domain, ! [X] : X = d0).'
  printf '%s\n' '% SZS output end FiniteModel for problem'
}
if [ "$source" = yes ]; then
  # The source proof controls coverage publication. Its irrelevant FMB peer
  # must terminate independently; process-race cleanup has dedicated tests.
  if [ "$mode" = proof ]; then sleep 0.05; proof; else unknown; fi
  exit 0
fi
case "$late_outcome" in
  refuted)
    # The delayed model is the result under test. Its irrelevant proof peer
    # must terminate independently so host load cannot change Refuted to a
    # local timeout before the model is observed.
    if [ "$mode" = fmb ]; then sleep 0.4; model; else unknown; fi
    ;;
  timed_out) hang ;;
  failure)
    sleep 0.4
    printf '%s\n' '% SZS status GaveUp for problem'
    ;;
  *) exit 42 ;;
esac
"#,
    )
    .unwrap();
    let mut permissions = std::fs::metadata(&executable).unwrap().permissions();
    permissions.set_mode(0o755);
    std::fs::set_permissions(&executable, permissions).unwrap();
    VampireWorkerCommand::new(executable)
        .with_extra_args([
            OsString::from("--late-outcome"),
            OsString::from(late_outcome),
        ])
        .unwrap()
}

fn new_state(
    task: &whiel_runner::SynthesisTask,
    artifacts: &ArtifactStore,
    context: &SolverEncodingContext,
    search_limit: Duration,
    retries: Vec<Duration>,
) -> HoudiniState {
    let resources = runtime_policy();
    let verification = VerificationParameters::new(search_limit, resources)
        .unwrap()
        .with_bulk_maint_limit(Duration::ZERO)
        .with_maintenance_retry_increments(retries)
        .unwrap();
    let catalog = ClauseCatalog::new(task, context.clone(), artifacts).unwrap();
    HoudiniState::new(task, verification, admission(resources), catalog).unwrap()
}

async fn install_two_track_active(
    task: &whiel_runner::SynthesisTask,
    state: &mut HoudiniState,
    add_cross_track_support: bool,
) -> [ClauseId; 2] {
    let prepared = state
        .prepare_init_candidates(
            vec![
                formula(task, "phase3d.ordinary", "task.phase2c_qf_fixture", &[]),
                formula(
                    task,
                    "phase3d.w",
                    "catalog.clause.0",
                    &["rel:E:0", "rel:TBound:0"],
                ),
            ],
            &ClauseSet::new(),
            &CancellationToken::new(),
        )
        .await;
    assert!(matches!(
        prepared,
        InitializationInvocationOutcome::Complete
    ));
    let mut ids = state.init_candidates().iter().copied().collect::<Vec<_>>();
    ids.sort_unstable();
    let ids: [ClauseId; 2] = ids.try_into().expect("two distinct clauses");
    let evidence = state
        .catalog()
        .artifacts()
        .publish(
            ArtifactKind::InitializationCheck,
            b"phase3d InitProved".as_slice().into(),
        )
        .unwrap();
    for id in ids {
        state
            .catalog()
            .record_initialization(id, InitializationStatus::InitProved, evidence)
            .unwrap();
    }
    state
        .set_track_hint(
            ids[0],
            MaintenanceTrackHint::new(MaintenanceTrackKind::Ordinary, None),
        )
        .unwrap();
    state
        .set_track_hint(
            ids[1],
            MaintenanceTrackHint::new(MaintenanceTrackKind::WLayer, Some(7)),
        )
        .unwrap();
    if add_cross_track_support {
        state.insert_maint_support(ids[0], ids[1]).unwrap();
    }
    let log_history = state.maintenance_policy().log_maintenance_history();
    let strict_history = state.maintenance_policy().fail_on_history_log_error();
    state
        .set_maintenance_policy(
            MaintenancePolicy::new(
                CoverageMode::UseProducerClosed,
                TrackLayout::OrdinaryAndWTracks,
                CoverageLookup::IncomingEdges,
            )
            .with_history(log_history, strict_history),
        )
        .unwrap();
    let prepared = prepare_maintenance(task, state, &CancellationToken::new()).await;
    assert!(matches!(prepared, MaintenancePreparationOutcome::Complete));
    ids
}

async fn install_late_coverage_active(
    task: &whiel_runner::SynthesisTask,
    state: &mut HoudiniState,
) -> [ClauseId; 2] {
    install_late_coverage_active_with_target_wp(task, state, None).await
}

async fn install_late_coverage_active_with_target_wp(
    task: &whiel_runner::SynthesisTask,
    state: &mut HoudiniState,
    target_wp: Option<ClauseFormula>,
) -> [ClauseId; 2] {
    let prepared = state
        .prepare_init_candidates(
            vec![
                formula(task, "phase3d.late.source", "task.phase2c_qf_fixture", &[]),
                formula(
                    task,
                    "phase3d.late.target",
                    "catalog.clause.0",
                    &["rel:E:0", "rel:TBound:0"],
                ),
            ],
            &ClauseSet::new(),
            &CancellationToken::new(),
        )
        .await;
    assert!(matches!(
        prepared,
        InitializationInvocationOutcome::Complete
    ));
    let mut ids = state.init_candidates().iter().copied().collect::<Vec<_>>();
    ids.sort_unstable();
    let ids: [ClauseId; 2] = ids.try_into().expect("two late-result clauses");
    let [source, target] = ids;
    let evidence = state
        .catalog()
        .artifacts()
        .publish(
            ArtifactKind::InitializationCheck,
            b"phase3d InitProved".as_slice().into(),
        )
        .unwrap();
    for id in ids {
        state
            .catalog()
            .record_initialization(id, InitializationStatus::InitProved, evidence)
            .unwrap();
    }
    if let Some(target_wp) = target_wp {
        let admission = state.admission().clone();
        state
            .catalog()
            .prepare_supplied_maintenance_wp(
                &admission,
                target,
                target_wp,
                &CancellationToken::new(),
            )
            .await
            .unwrap();
    }
    state
        .set_track_hint(
            source,
            MaintenanceTrackHint::new(MaintenanceTrackKind::Ordinary, None),
        )
        .unwrap();
    state
        .set_track_hint(
            target,
            MaintenanceTrackHint::new(MaintenanceTrackKind::WLayer, Some(1)),
        )
        .unwrap();
    state.insert_maint_coverage(source, target).unwrap();
    let log_history = state.maintenance_policy().log_maintenance_history();
    let strict_history = state.maintenance_policy().fail_on_history_log_error();
    state
        .set_maintenance_policy(
            MaintenancePolicy::new(
                CoverageMode::UseProducerClosed,
                TrackLayout::OrdinaryAndWTracks,
                CoverageLookup::IncomingEdges,
            )
            .with_history(log_history, strict_history),
        )
        .unwrap();
    let prepared = prepare_maintenance(task, state, &CancellationToken::new()).await;
    assert!(matches!(prepared, MaintenancePreparationOutcome::Complete));
    ids
}

async fn install_same_track_coverage_cycle(
    task: &whiel_runner::SynthesisTask,
    state: &mut HoudiniState,
) -> [ClauseId; 2] {
    let prepared = state
        .prepare_init_candidates(
            vec![
                formula(task, "phase3e.cycle.left", "task.phase2c_qf_fixture", &[]),
                formula(
                    task,
                    "phase3e.cycle.right",
                    "catalog.clause.0",
                    &["rel:E:0", "rel:TBound:0"],
                ),
            ],
            &ClauseSet::new(),
            &CancellationToken::new(),
        )
        .await;
    assert!(matches!(
        prepared,
        InitializationInvocationOutcome::Complete
    ));
    let mut ids = state.init_candidates().iter().copied().collect::<Vec<_>>();
    ids.sort_unstable();
    let ids: [ClauseId; 2] = ids.try_into().expect("two cycle clauses");
    let evidence = state
        .catalog()
        .artifacts()
        .publish(
            ArtifactKind::InitializationCheck,
            b"phase3e InitProved".as_slice().into(),
        )
        .unwrap();
    for id in ids {
        state
            .catalog()
            .record_initialization(id, InitializationStatus::InitProved, evidence)
            .unwrap();
    }
    state.insert_maint_coverage(ids[0], ids[1]).unwrap();
    state.insert_maint_coverage(ids[1], ids[0]).unwrap();
    state
        .set_maintenance_policy(MaintenancePolicy::new(
            CoverageMode::UseProducerClosed,
            TrackLayout::SingleTrack,
            CoverageLookup::IncomingEdges,
        ))
        .unwrap();
    assert!(matches!(
        prepare_maintenance(task, state, &CancellationToken::new()).await,
        MaintenancePreparationOutcome::Complete
    ));
    ids
}

async fn install_cross_track_closed_coverage_scc(
    task: &whiel_runner::SynthesisTask,
    state: &mut HoudiniState,
) -> [ClauseId; 4] {
    let prepared = state
        .prepare_init_candidates(
            vec![
                formula(task, "phase3e.scc.a", "task.phase2c_qf_fixture", &[]),
                formula(
                    task,
                    "phase3e.scc.b",
                    "catalog.clause.0",
                    &["rel:E:0", "rel:TBound:0"],
                ),
                formula(
                    task,
                    "phase3e.scc.c",
                    "agent_naive.one_off",
                    &["rel:E:0", "rel:T:0", "rel:T:1"],
                ),
                formula(
                    task,
                    "phase3e.scc.d",
                    "catalog.clause.1",
                    &["rel:E:0", "rel:T:1", "rel:T:0"],
                ),
            ],
            &ClauseSet::new(),
            &CancellationToken::new(),
        )
        .await;
    assert!(matches!(
        prepared,
        InitializationInvocationOutcome::Complete
    ));
    let mut ids = state.init_candidates().iter().copied().collect::<Vec<_>>();
    ids.sort_unstable();
    let ids: [ClauseId; 4] = ids.try_into().expect("four SCC clauses");
    let evidence = state
        .catalog()
        .artifacts()
        .publish(
            ArtifactKind::InitializationCheck,
            b"phase3e InitProved".as_slice().into(),
        )
        .unwrap();
    for id in ids {
        state
            .catalog()
            .record_initialization(id, InitializationStatus::InitProved, evidence)
            .unwrap();
    }
    state
        .set_track_hint(
            ids[0],
            MaintenanceTrackHint::new(MaintenanceTrackKind::Ordinary, None),
        )
        .unwrap();
    state
        .set_track_hint(
            ids[2],
            MaintenanceTrackHint::new(MaintenanceTrackKind::Ordinary, None),
        )
        .unwrap();
    state
        .set_track_hint(
            ids[1],
            MaintenanceTrackHint::new(MaintenanceTrackKind::WLayer, Some(9)),
        )
        .unwrap();
    state
        .set_track_hint(
            ids[3],
            MaintenanceTrackHint::new(MaintenanceTrackKind::WLayer, Some(2)),
        )
        .unwrap();
    for source in ids {
        for target in ids {
            if source != target {
                state.insert_maint_coverage(source, target).unwrap();
            }
        }
    }
    state
        .set_maintenance_policy(MaintenancePolicy::new(
            CoverageMode::UseProducerClosed,
            TrackLayout::OrdinaryAndWTracks,
            CoverageLookup::IncomingEdges,
        ))
        .unwrap();
    assert!(matches!(
        prepare_maintenance(task, state, &CancellationToken::new()).await,
        MaintenancePreparationOutcome::Complete
    ));
    ids
}

async fn install_sparse_w_coverage_active(
    task: &whiel_runner::SynthesisTask,
    state: &mut HoudiniState,
) -> [ClauseId; 3] {
    assert!(matches!(
        state
            .prepare_init_candidates(
                vec![
                    formula(task, "phase3d.cover.source", "task.phase2c_qf_fixture", &[]),
                    formula(
                        task,
                        "phase3d.cover.w9",
                        "catalog.clause.0",
                        &["rel:E:0", "rel:TBound:0"],
                    ),
                    formula(
                        task,
                        "phase3d.cover.w2",
                        "agent_naive.one_off",
                        &["rel:E:0", "rel:T:0", "rel:T:1"],
                    ),
                ],
                &ClauseSet::new(),
                &CancellationToken::new(),
            )
            .await,
        InitializationInvocationOutcome::Complete
    ));
    let mut ids = state.init_candidates().iter().copied().collect::<Vec<_>>();
    ids.sort_unstable();
    let ids: [ClauseId; 3] = ids.try_into().expect("three registered clauses");
    let [source, w9, w2] = ids;
    let evidence = state
        .catalog()
        .artifacts()
        .publish(
            ArtifactKind::InitializationCheck,
            b"phase3d InitProved".as_slice().into(),
        )
        .unwrap();
    for id in ids {
        state
            .catalog()
            .record_initialization(id, InitializationStatus::InitProved, evidence)
            .unwrap();
    }
    state.insert_maint_support(source, source).unwrap();
    state.insert_maint_coverage(source, w2).unwrap();
    state
        .set_track_hint(
            source,
            MaintenanceTrackHint::new(MaintenanceTrackKind::Ordinary, None),
        )
        .unwrap();
    state
        .set_track_hint(
            w9,
            MaintenanceTrackHint::new(MaintenanceTrackKind::WLayer, Some(9)),
        )
        .unwrap();
    state
        .set_track_hint(
            w2,
            MaintenanceTrackHint::new(MaintenanceTrackKind::WLayer, Some(2)),
        )
        .unwrap();
    state
        .set_maintenance_policy(MaintenancePolicy::new(
            CoverageMode::UseProducerClosed,
            TrackLayout::OrdinaryAndWTracks,
            CoverageLookup::IncomingEdges,
        ))
        .unwrap();
    assert!(matches!(
        prepare_maintenance(task, state, &CancellationToken::new()).await,
        MaintenancePreparationOutcome::Complete
    ));
    ids
}

async fn shutdown(
    state: HoudiniState,
    context: SolverEncodingContext,
    artifacts: ArtifactStore,
    owner: whiel_runner::ArtifactBackendOwner,
) {
    context.shutdown().await.unwrap();
    drop(state);
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}

fn launch_count(path: &Path) -> usize {
    std::fs::read_to_string(path)
        .unwrap_or_default()
        .lines()
        .count()
}

fn history_run_root(artifacts: &ArtifactStore) -> PathBuf {
    let marker = artifacts
        .publish(
            ArtifactKind::RuntimeTrace,
            b"phase3d history marker".as_slice().into(),
        )
        .unwrap();
    artifacts
        .resolve(marker)
        .unwrap()
        .path()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf()
}

fn read_history(run_root: &Path) -> Vec<serde_json::Value> {
    fs::read_to_string(run_root.join("history/maintenance.jsonl"))
        .unwrap()
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect()
}

fn open_gate_after_proved_history(
    artifacts: ArtifactStore,
    source: ClauseId,
    request_marker: PathBuf,
    gate: PathBuf,
) -> std::thread::JoinHandle<()> {
    std::thread::spawn(move || {
        let deadline = Instant::now() + Duration::from_secs(60);
        let mut source_is_live = false;
        while Instant::now() < deadline {
            let page = artifacts
                .query_maintenance_history(source.get(), MaintenanceHistoryCursor::start(), 32)
                .unwrap();
            source_is_live |= page.records.iter().any(|record| {
                record["event"] == "maintenance_attempt" && record["outcome"] == "proved"
            });
            if source_is_live && request_marker.exists() {
                fs::write(&gate, b"source is live").expect("open support-failure gate");
                return;
            }
            std::thread::sleep(Duration::from_millis(5));
        }
        panic!("source proof and gated support request did not both become visible");
    })
}

async fn install_single_active(
    task: &whiel_runner::SynthesisTask,
    state: &mut HoudiniState,
) -> ClauseId {
    install_single_active_with_target_wp(task, state, None).await
}

async fn install_single_active_with_target_wp(
    task: &whiel_runner::SynthesisTask,
    state: &mut HoudiniState,
    target_wp: Option<ClauseFormula>,
) -> ClauseId {
    let prepared = state
        .prepare_init_candidates(
            vec![formula(
                task,
                "phase3d.single",
                "task.phase2c_qf_fixture",
                &[],
            )],
            &ClauseSet::new(),
            &CancellationToken::new(),
        )
        .await;
    assert!(matches!(
        prepared,
        InitializationInvocationOutcome::Complete
    ));
    let id = *state.init_candidates().iter().next().unwrap();
    let evidence = state
        .catalog()
        .artifacts()
        .publish(
            ArtifactKind::InitializationCheck,
            b"phase3d InitProved".as_slice().into(),
        )
        .unwrap();
    state
        .catalog()
        .record_initialization(id, InitializationStatus::InitProved, evidence)
        .unwrap();
    if let Some(target_wp) = target_wp {
        let admission = state.admission().clone();
        state
            .catalog()
            .prepare_supplied_maintenance_wp(&admission, id, target_wp, &CancellationToken::new())
            .await
            .unwrap();
    }
    let log_history = state.maintenance_policy().log_maintenance_history();
    let strict_history = state.maintenance_policy().fail_on_history_log_error();
    state
        .set_maintenance_policy(
            MaintenancePolicy::new(
                CoverageMode::UseProducerClosed,
                TrackLayout::SingleTrack,
                CoverageLookup::IncomingEdges,
            )
            .with_history(log_history, strict_history),
        )
        .unwrap();
    let prepared = prepare_maintenance(task, state, &CancellationToken::new()).await;
    assert!(matches!(prepared, MaintenancePreparationOutcome::Complete));
    id
}

// ------------------------------------------------------------
// Concurrent Tracks And Differential Semantics
// ------------------------------------------------------------

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn concurrent_tracks_match_the_sequential_oracle_on_stable_results() {
    let task = support::export_canonical_task();
    let sequential_root = support::TestDir::new("phase3d_differential_sequential");
    let concurrent_root = support::TestDir::new("phase3d_differential_concurrent");
    let (sequential_owner, sequential_artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(sequential_root.path().join("artifacts")),
    )
    .unwrap();
    let (concurrent_owner, concurrent_artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(concurrent_root.path().join("artifacts")),
    )
    .unwrap();
    let sequential_context =
        new_solver_encoding_context(&task, &sequential_artifacts, worker_config()).unwrap();
    let concurrent_context =
        new_solver_encoding_context(&task, &concurrent_artifacts, worker_config()).unwrap();
    let mut sequential = new_state(
        &task,
        &sequential_artifacts,
        &sequential_context,
        Duration::from_secs(60),
        Vec::new(),
    );
    let mut concurrent = new_state(
        &task,
        &concurrent_artifacts,
        &concurrent_context,
        Duration::from_secs(60),
        Vec::new(),
    );
    let sequential_ids = install_two_track_active(&task, &mut sequential, false).await;
    let concurrent_ids = install_two_track_active(&task, &mut concurrent, false).await;
    assert_eq!(sequential_ids, concurrent_ids);

    let sequential_result = run_maintenance_block_sequential(
        &task,
        &mut sequential,
        vampire_command("race-fmb-failure-proof", None),
        &CancellationToken::new(),
    )
    .await;
    let concurrent_result = run_maintenance_block(
        &task,
        &mut concurrent,
        vampire_command("race-fmb-failure-proof", None),
        &CancellationToken::new(),
    )
    .await;
    let MaintenanceExecutionOutcome::Complete(sequential_block) = sequential_result else {
        panic!("sequential oracle did not complete: {sequential_result:#?}");
    };
    let MaintenanceExecutionOutcome::Complete(concurrent_block) = concurrent_result else {
        panic!("concurrent block did not complete: {concurrent_result:#?}");
    };
    assert_eq!(sequential_block.outcome(), MaintenanceBlockOutcome::Stable);
    assert_eq!(concurrent_block.outcome(), sequential_block.outcome());
    assert_eq!(concurrent_block.candidate(), sequential_block.candidate());
    assert_eq!(concurrent_block.known_live(), sequential_block.known_live());
    assert_eq!(concurrent.active(), sequential.active());
    assert_eq!(concurrent.core(), sequential.core());
    let mut result_run_id = None;
    for id in concurrent_ids {
        let record = concurrent.catalog().record(id).unwrap();
        let latest = record
            .latest_maintenance()
            .expect("production maintenance retains one compact latest result");
        assert_eq!(latest.class(), MaintenanceResultClass::Proved);
        assert_eq!(latest.disposition(), MaintenanceResultDisposition::Applied);
        assert_eq!(latest.candidate_len(), 2);
        assert_eq!(
            latest.candidate_generation(),
            concurrent_block.generation().get()
        );
        match result_run_id {
            Some(run_id) => assert_eq!(latest.candidate_run_id(), run_id),
            None => result_run_id = Some(latest.candidate_run_id()),
        }
        assert_eq!(latest.evidence().kind(), ArtifactKind::RuntimeTrace);
        concurrent
            .artifacts()
            .resolve(latest.evidence())
            .expect("latest result references durable evidence");
    }

    shutdown(
        sequential,
        sequential_context,
        sequential_artifacts,
        sequential_owner,
    )
    .await;
    shutdown(
        concurrent,
        concurrent_context,
        concurrent_artifacts,
        concurrent_owner,
    )
    .await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn concurrent_refutation_matches_the_sequential_oracle_block_exactly() {
    let task = support::export_canonical_task();
    let sequential_root = support::TestDir::new("phase3d_refuted_sequential");
    let concurrent_root = support::TestDir::new("phase3d_refuted_concurrent");
    let (sequential_owner, sequential_artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(sequential_root.path().join("artifacts")),
    )
    .unwrap();
    let (concurrent_owner, concurrent_artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(concurrent_root.path().join("artifacts")),
    )
    .unwrap();
    let sequential_context =
        new_solver_encoding_context(&task, &sequential_artifacts, worker_config()).unwrap();
    let concurrent_context =
        new_solver_encoding_context(&task, &concurrent_artifacts, worker_config()).unwrap();
    let mut sequential = new_state(
        &task,
        &sequential_artifacts,
        &sequential_context,
        Duration::from_secs(60),
        Vec::new(),
    );
    let mut concurrent = new_state(
        &task,
        &concurrent_artifacts,
        &concurrent_context,
        Duration::from_secs(60),
        Vec::new(),
    );
    let sequential_id = install_single_active(&task, &mut sequential).await;
    let concurrent_id = install_single_active(&task, &mut concurrent).await;
    assert_eq!(sequential_id, concurrent_id);
    let sequential_telemetry = TelemetrySession::start(TelemetryConfig::new(
        sequential_root.path().join("telemetry"),
        TelemetryLevel::Aggregate,
    ));
    let concurrent_telemetry = TelemetrySession::start(TelemetryConfig::new(
        concurrent_root.path().join("telemetry"),
        TelemetryLevel::Aggregate,
    ));
    sequential.attach_telemetry(sequential_telemetry.handle());
    concurrent.attach_telemetry(concurrent_telemetry.handle());

    let sequential_result = run_maintenance_block_sequential(
        &task,
        &mut sequential,
        vampire_command("race-proof-failure-model", None),
        &CancellationToken::new(),
    )
    .await;
    let concurrent_result = run_maintenance_block(
        &task,
        &mut concurrent,
        vampire_command("race-proof-failure-model", None),
        &CancellationToken::new(),
    )
    .await;
    let MaintenanceExecutionOutcome::Complete(sequential_block) = sequential_result else {
        panic!("sequential oracle did not complete: {sequential_result:#?}");
    };
    let MaintenanceExecutionOutcome::Complete(concurrent_block) = concurrent_result else {
        panic!("concurrent block did not complete: {concurrent_result:#?}");
    };
    assert_eq!(
        concurrent_block.outcome(),
        MaintenanceBlockOutcome::Refuted(concurrent_id)
    );
    assert_eq!(concurrent_block.outcome(), sequential_block.outcome());
    assert_eq!(
        concurrent_block.entry_active(),
        sequential_block.entry_active()
    );
    assert_eq!(concurrent_block.candidate(), sequential_block.candidate());
    assert_eq!(concurrent_block.known_live(), sequential_block.known_live());
    for report in [sequential_telemetry.finish(), concurrent_telemetry.finish()] {
        assert_eq!(
            report
                .snapshot
                .counters
                .get("houdini.maintenance.proof_and_fmb_requests"),
            Some(&1)
        );
        assert_eq!(
            report
                .snapshot
                .dispositions
                .get("maintenance_query_refuted_applied"),
            Some(&1)
        );
        assert!(
            report
                .snapshot
                .duration_nanoseconds
                .get("houdini.maintenance.query_inclusive")
                .is_some_and(|duration| *duration > 0)
        );
    }

    shutdown(
        sequential,
        sequential_context,
        sequential_artifacts,
        sequential_owner,
    )
    .await;
    shutdown(
        concurrent,
        concurrent_context,
        concurrent_artifacts,
        concurrent_owner,
    )
    .await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn concurrent_multi_block_pruning_matches_the_sequential_oracle() {
    let task = support::export_canonical_task();
    let sequential_root = support::TestDir::new("phase3d_pruning_sequential");
    let concurrent_root = support::TestDir::new("phase3d_pruning_concurrent");
    let (sequential_owner, sequential_artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(sequential_root.path().join("artifacts")),
    )
    .unwrap();
    let (concurrent_owner, concurrent_artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(concurrent_root.path().join("artifacts")),
    )
    .unwrap();
    let sequential_context =
        new_solver_encoding_context(&task, &sequential_artifacts, worker_config()).unwrap();
    let concurrent_context =
        new_solver_encoding_context(&task, &concurrent_artifacts, worker_config()).unwrap();
    let mut sequential = new_state(
        &task,
        &sequential_artifacts,
        &sequential_context,
        Duration::from_secs(30),
        Vec::new(),
    );
    let mut concurrent = new_state(
        &task,
        &concurrent_artifacts,
        &concurrent_context,
        Duration::from_secs(30),
        Vec::new(),
    );
    let sequential_ids = install_two_track_active(&task, &mut sequential, false).await;
    let concurrent_ids = install_two_track_active(&task, &mut concurrent, false).await;
    assert_eq!(sequential_ids, concurrent_ids);

    let sequential_result = run_maintenance_blocks_sequential(
        &task,
        &mut sequential,
        vampire_command("race-proof-failure-model", None),
        &CancellationToken::new(),
    )
    .await;
    let concurrent_result = run_maintenance_blocks(
        &task,
        &mut concurrent,
        vampire_command("race-proof-failure-model", None),
        &CancellationToken::new(),
    )
    .await;
    assert!(matches!(
        sequential_result,
        MaintenanceExecutionOutcome::Complete(None)
    ));
    assert!(matches!(
        concurrent_result,
        MaintenanceExecutionOutcome::Complete(None)
    ));
    assert_eq!(concurrent.active(), sequential.active());
    assert_eq!(concurrent.core(), sequential.core());
    assert!(concurrent.active().is_empty());
    assert!(concurrent.core().is_empty());
    assert!(concurrent.maintenance_plan().is_none());
    assert!(sequential.maintenance_plan().is_none());
    for id in concurrent_ids {
        let sequential_record = sequential.catalog().record(id).unwrap();
        let concurrent_record = concurrent.catalog().record(id).unwrap();
        assert_eq!(
            concurrent_record.has_retry_candidate(),
            sequential_record.has_retry_candidate()
        );
        assert_eq!(
            concurrent_record.next_retry_tier(),
            sequential_record.next_retry_tier()
        );
        assert_eq!(
            concurrent_record.retry_exhausted(),
            sequential_record.retry_exhausted()
        );
    }

    shutdown(
        sequential,
        sequential_context,
        sequential_artifacts,
        sequential_owner,
    )
    .await;
    shutdown(
        concurrent,
        concurrent_context,
        concurrent_artifacts,
        concurrent_owner,
    )
    .await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn mixed_refutation_then_cross_track_coverage_matches_the_sequential_oracle() {
    let task = support::export_canonical_task();
    let sequential_root = support::TestDir::new("phase3d_mixed_sequential");
    let concurrent_root = support::TestDir::new("phase3d_mixed_concurrent");
    let sequential_log = sequential_root.path().join("launches");
    let concurrent_log = concurrent_root.path().join("launches");
    let (sequential_owner, sequential_artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(sequential_root.path().join("artifacts")),
    )
    .unwrap();
    let (concurrent_owner, concurrent_artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(concurrent_root.path().join("artifacts")),
    )
    .unwrap();
    let sequential_context =
        new_solver_encoding_context(&task, &sequential_artifacts, worker_config()).unwrap();
    let concurrent_context =
        new_solver_encoding_context(&task, &concurrent_artifacts, worker_config()).unwrap();
    let mut sequential = new_state(
        &task,
        &sequential_artifacts,
        &sequential_context,
        Duration::from_secs(30),
        Vec::new(),
    );
    let mut concurrent = new_state(
        &task,
        &concurrent_artifacts,
        &concurrent_context,
        Duration::from_secs(30),
        Vec::new(),
    );
    let [sequential_source, sequential_refuted, sequential_covered] =
        install_sparse_w_coverage_active(&task, &mut sequential).await;
    let concurrent_ids = install_sparse_w_coverage_active(&task, &mut concurrent).await;
    assert_eq!(
        [sequential_source, sequential_refuted, sequential_covered],
        concurrent_ids
    );

    let sequential_result = run_maintenance_blocks_sequential(
        &task,
        &mut sequential,
        vampire_command("race-proof-failure-model", Some(&sequential_log)),
        &CancellationToken::new(),
    )
    .await;
    let concurrent_result = run_maintenance_blocks(
        &task,
        &mut concurrent,
        vampire_command("race-proof-failure-model", Some(&concurrent_log)),
        &CancellationToken::new(),
    )
    .await;
    let MaintenanceExecutionOutcome::Complete(Some(sequential_block)) = sequential_result else {
        panic!("sequential mixed run did not reach a stable block: {sequential_result:#?}");
    };
    let MaintenanceExecutionOutcome::Complete(Some(concurrent_block)) = concurrent_result else {
        panic!("concurrent mixed run did not reach a stable block: {concurrent_result:#?}");
    };
    let survivors = ClauseSet::from([sequential_source, sequential_covered]);
    assert_eq!(sequential_block.outcome(), MaintenanceBlockOutcome::Stable);
    assert_eq!(concurrent_block.outcome(), MaintenanceBlockOutcome::Stable);
    assert_eq!(sequential.active(), &survivors);
    assert_eq!(concurrent.active(), &survivors);
    assert_eq!(sequential_block.entry_active(), &survivors);
    assert_eq!(concurrent_block.entry_active(), &survivors);
    assert_eq!(sequential_block.candidate(), &survivors);
    assert_eq!(concurrent_block.candidate(), &survivors);
    assert_eq!(sequential_block.known_live(), &survivors);
    assert_eq!(concurrent_block.known_live(), &survivors);
    assert!(!sequential.active().contains(&sequential_refuted));
    assert!(!concurrent.active().contains(&sequential_refuted));
    assert!(sequential.core().is_empty());
    assert!(concurrent.core().is_empty());
    assert_eq!(launch_count(&sequential_log), 2);
    assert_eq!(launch_count(&concurrent_log), 2);

    shutdown(
        sequential,
        sequential_context,
        sequential_artifacts,
        sequential_owner,
    )
    .await;
    shutdown(
        concurrent,
        concurrent_context,
        concurrent_artifacts,
        concurrent_owner,
    )
    .await;
}

#[cfg(unix)]
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn nonempty_tracks_reach_solver_work_concurrently() {
    let task = support::export_canonical_task();
    let root = support::TestDir::new("phase3d_track_overlap");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(root.path().join("artifacts")),
    )
    .unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_state(
        &task,
        &artifacts,
        &context,
        // This fixture checks track overlap, not solver timeout behavior.
        // Allow process-startup headroom after the preceding all-target gates.
        Duration::from_secs(30),
        Vec::new(),
    );
    install_two_track_active(&task, &mut state, false).await;

    // Each proof worker refuses to finish until both tracks have launched a
    // proof process. A serial track executor would therefore time out/fail.
    let outcome = run_maintenance_block(
        &task,
        &mut state,
        overlap_worker(root.path()),
        &CancellationToken::new(),
    )
    .await;
    let MaintenanceExecutionOutcome::Complete(block) = outcome else {
        panic!("two-track overlap fixture did not complete: {outcome:#?}");
    };
    assert_eq!(block.outcome(), MaintenanceBlockOutcome::Stable);

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn cross_track_support_skips_the_supported_track_without_serializing_tracks() {
    let task = support::export_canonical_task();
    let root = support::TestDir::new("phase3d_cross_track_support");
    let launch_log = root.path().join("launches");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(root.path().join("artifacts")),
    )
    .unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_state(
        &task,
        &artifacts,
        &context,
        Duration::from_secs(30),
        Vec::new(),
    );
    let ids = install_two_track_active(&task, &mut state, true).await;
    let disabled = TelemetryHandle::disabled();
    state.attach_telemetry(disabled.clone());

    let outcome = run_maintenance_block(
        &task,
        &mut state,
        vampire_command("race-fmb-failure-proof", Some(&launch_log)),
        &CancellationToken::new(),
    )
    .await;
    let MaintenanceExecutionOutcome::Complete(block) = outcome else {
        panic!("concurrent block did not complete: {outcome:#?}");
    };
    assert_eq!(block.outcome(), MaintenanceBlockOutcome::Stable);
    assert_eq!(block.known_live(), &ClauseSet::from(ids));
    assert_eq!(launch_count(&launch_log), 2, "only one Vampire race ran");
    let disabled_snapshot = disabled.snapshot();
    // Off mode retains only the fixed-size campaign progress projection. It
    // must not retain solver/support counters or other aggregate telemetry.
    assert_eq!(disabled_snapshot.counters.len(), 2);
    assert_eq!(disabled_snapshot.counters["inv.epochs"], 0);
    assert_eq!(disabled_snapshot.counters["catalog.registered_unique"], 0);
    assert_eq!(disabled_snapshot.dispositions.len(), 1);
    assert_eq!(disabled_snapshot.dispositions["core_admission"], 0);
    assert!(disabled_snapshot.duration_nanoseconds.is_empty());

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn sparse_w_track_observes_cross_track_coverage_online() {
    let task = support::export_canonical_task();
    let root = support::TestDir::new("phase3d_cross_track_coverage");
    let launch_log = root.path().join("launches");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(root.path().join("artifacts")),
    )
    .unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_state(
        &task,
        &artifacts,
        &context,
        Duration::from_secs(30),
        Vec::new(),
    );
    let [_source, _w9, w2] = install_sparse_w_coverage_active(&task, &mut state).await;
    let telemetry = TelemetrySession::start(TelemetryConfig::new(
        root.path().join("telemetry"),
        TelemetryLevel::Aggregate,
    ));
    state.attach_telemetry(telemetry.handle());
    // The ordinary source publishes immediately. The W(9)-like predecessor
    // performs one real query before the W(2)-like covered target is reached.

    let outcome = run_maintenance_block(
        &task,
        &mut state,
        vampire_command("race-fmb-failure-delayed-proof", Some(&launch_log)),
        &CancellationToken::new(),
    )
    .await;
    let MaintenanceExecutionOutcome::Complete(block) = outcome else {
        panic!("cross-track coverage block did not complete: {outcome:#?}");
    };
    assert_eq!(block.outcome(), MaintenanceBlockOutcome::Stable);
    assert!(block.known_live().contains(&w2));
    assert_eq!(launch_count(&launch_log), 2, "only W(9)-like query ran");
    let report = telemetry.finish();
    assert_eq!(
        report
            .snapshot
            .counters
            .get("houdini.maintenance.shortcuts.support"),
        Some(&1)
    );
    assert_eq!(
        report
            .snapshot
            .counters
            .get("houdini.maintenance.shortcuts.coverage"),
        Some(&1)
    );
    assert_eq!(
        report
            .snapshot
            .counters
            .get("houdini.maintenance.proof_and_fmb_requests"),
        Some(&1)
    );
    assert!(
        report
            .snapshot
            .counters
            .get("houdini.maintenance.lazy_coverage_lookup_requests")
            .is_some_and(|requests| *requests >= 1)
    );
    assert_eq!(
        report
            .snapshot
            .dispositions
            .get("maintenance_support_shortcut"),
        Some(&1)
    );
    assert_eq!(
        report
            .snapshot
            .dispositions
            .get("maintenance_coverage_shortcut"),
        Some(&1)
    );
    assert_eq!(
        report
            .snapshot
            .dispositions
            .get("maintenance_query_proved_applied"),
        Some(&1)
    );
    assert!(
        report
            .snapshot
            .duration_nanoseconds
            .get("houdini.maintenance.query_inclusive")
            .is_some_and(|duration| *duration > 0)
    );
    assert!(
        report
            .snapshot
            .duration_nanoseconds
            .get("houdini.maintenance.lazy_coverage_lookup_inclusive")
            .is_some_and(|duration| *duration > 0)
    );

    shutdown(state, context, artifacts, owner).await;
}

#[cfg(unix)]
async fn assert_late_nonproved_result_is_redundant(
    label: &str,
    late_outcome: &str,
    expected_history_outcome: &str,
    expected_disposition: &str,
) {
    let task = support::export_canonical_task();
    let root = support::TestDir::new(label);
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(root.path().join("artifacts")).maintenance_history(true, true),
    )
    .unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_state(
        &task,
        &artifacts,
        &context,
        Duration::from_secs(30),
        vec![Duration::from_secs(30)],
    );
    let [source, target] = install_late_coverage_active(&task, &mut state).await;

    let outcome = run_maintenance_block(
        &task,
        &mut state,
        late_result_worker(root.path(), late_outcome),
        &CancellationToken::new(),
    )
    .await;
    let MaintenanceExecutionOutcome::Complete(block) = outcome else {
        panic!("late {late_outcome} block did not complete: {outcome:#?}");
    };
    assert_eq!(block.outcome(), MaintenanceBlockOutcome::Stable);
    assert_eq!(block.known_live(), &ClauseSet::from([source, target]));
    assert!(state.maintenance_failure().is_none());
    let target_record = state.catalog().record(target).unwrap();
    assert!(!target_record.has_retry_candidate());
    assert_eq!(target_record.next_retry_tier(), 0);
    assert!(!target_record.retry_exhausted());

    let history = artifacts
        .query_maintenance_history(target.get(), MaintenanceHistoryCursor::start(), 32)
        .unwrap();
    let terminal = history
        .records
        .iter()
        .find(|record| {
            record["event"] == "maintenance_attempt"
                && record["outcome"] == expected_history_outcome
        })
        .unwrap_or_else(|| panic!("missing retained late {late_outcome} diagnostic: {history:#?}"));
    assert_eq!(terminal["disposition"], expected_disposition);
    assert!(
        !terminal["artifact_reference"].is_null(),
        "late result lost its required diagnostic artifact"
    );

    shutdown(state, context, artifacts, owner).await;
}

#[cfg(unix)]
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn late_refutation_becomes_live_after_concurrent_coverage_publication() {
    assert_late_nonproved_result_is_redundant(
        "phase3d_late_refuted",
        "refuted",
        "refuted",
        "conflicting",
    )
    .await;
}

#[cfg(unix)]
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn history_off_retains_compact_late_refutation_feedback() {
    let task = support::export_canonical_task();
    let root = support::TestDir::new("phase3e_history_off_late_refuted");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(root.path().join("artifacts")),
    )
    .unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_state(
        &task,
        &artifacts,
        &context,
        Duration::from_secs(30),
        vec![Duration::from_secs(30)],
    );
    let [source, target] = install_late_coverage_active(&task, &mut state).await;

    let outcome = run_maintenance_block(
        &task,
        &mut state,
        late_result_worker(root.path(), "refuted"),
        &CancellationToken::new(),
    )
    .await;
    let MaintenanceExecutionOutcome::Complete(block) = outcome else {
        panic!("history-off late-refutation block did not complete: {outcome:#?}");
    };
    assert_eq!(block.outcome(), MaintenanceBlockOutcome::Stable);
    assert_eq!(block.known_live(), &ClauseSet::from([source, target]));
    assert!(state.maintenance_failure().is_none());

    let record = state.catalog().record(target).unwrap();
    let latest = record
        .latest_maintenance()
        .expect("hot feedback must not depend on optional history");
    assert_eq!(latest.class(), MaintenanceResultClass::Refuted);
    assert_eq!(
        latest.disposition(),
        MaintenanceResultDisposition::Conflicting
    );
    assert_eq!(latest.candidate_len(), 2);
    assert_eq!(latest.candidate_generation(), block.generation().get());
    assert_eq!(latest.evidence().kind(), ArtifactKind::RuntimeTrace);
    state
        .artifacts()
        .resolve(latest.evidence())
        .expect("hot feedback retains durable evidence");
    assert!(!record.has_retry_candidate());
    assert_eq!(record.next_retry_tier(), 0);
    assert!(!record.retry_exhausted());
    assert_eq!(artifacts.diagnostics().history_records_constructed, 0);

    shutdown(state, context, artifacts, owner).await;
}

#[cfg(unix)]
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn late_timeout_becomes_live_after_concurrent_coverage_publication() {
    assert_late_nonproved_result_is_redundant(
        "phase3d_late_timeout",
        "timed_out",
        "timed_out",
        "redundant",
    )
    .await;
}

#[cfg(unix)]
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn late_lane_local_failure_becomes_live_after_concurrent_coverage_publication() {
    assert_late_nonproved_result_is_redundant(
        "phase3d_late_failure",
        "failure",
        "failure",
        "redundant",
    )
    .await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn same_track_coverage_cycle_does_not_wait_on_queued_work_or_bootstrap_liveness() {
    let task = support::export_canonical_task();
    let root = support::TestDir::new("phase3e_same_track_coverage_cycle");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(root.path().join("artifacts")),
    )
    .unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_state(
        &task,
        &artifacts,
        &context,
        Duration::from_secs(30),
        vec![Duration::from_secs(10)],
    );
    let ids = install_same_track_coverage_cycle(&task, &mut state).await;

    let outcome = tokio::time::timeout(
        Duration::from_secs(5),
        run_maintenance_block(
            &task,
            &mut state,
            vampire_command("race-dual-failure", None),
            &CancellationToken::new(),
        ),
    )
    .await
    .expect("a serial track must not wait for its own queued coverage source");
    let MaintenanceExecutionOutcome::Complete(block) = outcome else {
        panic!("same-track cycle did not complete: {outcome:#?}");
    };
    let failed = block
        .outcome()
        .target()
        .expect("a coverage cycle cannot bootstrap a live clause");
    assert!(ids.contains(&failed));
    assert!(block.known_live().is_empty());

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn cross_track_coverage_scc_has_an_acyclic_wait_relation() {
    let task = support::export_canonical_task();
    let root = support::TestDir::new("phase3e_cross_track_coverage_scc");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(root.path().join("artifacts")),
    )
    .unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_state(
        &task,
        &artifacts,
        &context,
        Duration::from_secs(10),
        vec![Duration::from_secs(10)],
    );
    let ids = install_cross_track_closed_coverage_scc(&task, &mut state).await;

    let outcome = tokio::time::timeout(
        Duration::from_secs(5),
        run_maintenance_block(
            &task,
            &mut state,
            vampire_command("race-dual-failure", None),
            &CancellationToken::new(),
        ),
    )
    .await
    .expect("a cross-track coverage SCC must not form a wait cycle");
    let MaintenanceExecutionOutcome::Complete(block) = outcome else {
        panic!("cross-track SCC did not complete: {outcome:#?}");
    };
    let failed = block
        .outcome()
        .target()
        .expect("coverage cycles cannot bootstrap live clauses");
    assert!(ids.contains(&failed));
    assert!(block.known_live().is_empty());

    shutdown(state, context, artifacts, owner).await;
}

// ------------------------------------------------------------
// Concurrent Assembly Failures
// ------------------------------------------------------------

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn lane_local_assembly_failure_selects_failed_without_retry_advancement() {
    let task = support::export_canonical_task();
    let root = support::TestDir::new("phase3d_lane_local_assembly_failure");
    let gate = root.path().join("release-support-failure");
    let request_marker = root.path().join("support-request");
    let launch_log = root.path().join("launches");
    fs::write(&gate, b"fail immediately").unwrap();
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(root.path().join("artifacts")).maintenance_history(true, true),
    )
    .unwrap();
    let context = new_solver_encoding_context(
        &task,
        &artifacts,
        gated_malformed_support_worker_config(&gate, &request_marker),
    )
    .unwrap();
    let mut state = new_state(
        &task,
        &artifacts,
        &context,
        Duration::from_secs(30),
        vec![Duration::from_secs(30)],
    );
    let target = install_single_active_with_target_wp(
        &task,
        &mut state,
        Some(mixed_constant_wp(&task, "phase3d.assembly_failure.wp")),
    )
    .await;
    let entry_active = state.active().clone();
    let entry_record = state.catalog().record(target).unwrap();
    assert!(!entry_record.has_retry_candidate());
    assert_eq!(entry_record.next_retry_tier(), 0);
    assert!(!entry_record.retry_exhausted());
    assert_eq!(entry_record.next_fmb_start_size(), None);

    let outcome = run_maintenance_block(
        &task,
        &mut state,
        vampire_command("race-fmb-failure-proof", Some(&launch_log)),
        &CancellationToken::new(),
    )
    .await;
    let MaintenanceExecutionOutcome::Complete(block) = outcome else {
        panic!("LaneLocal assembly failure did not produce a block result: {outcome:#?}");
    };
    assert_eq!(block.outcome(), MaintenanceBlockOutcome::Failed(target));
    assert_eq!(block.entry_active(), &entry_active);
    assert_eq!(block.candidate(), &entry_active);
    assert!(block.known_live().is_empty());
    assert_eq!(state.active(), &entry_active);
    assert!(state.core().is_empty());
    assert!(state.maintenance_failure().is_none());
    assert!(
        request_marker.exists(),
        "the selected support request did not run"
    );
    assert_eq!(launch_count(&launch_log), 0, "assembly launched Vampire");

    let record = state.catalog().record(target).unwrap();
    assert!(!record.has_retry_candidate());
    assert_eq!(record.next_retry_tier(), 0);
    assert!(!record.retry_exhausted());
    assert_eq!(record.next_fmb_start_size(), None);
    let history = artifacts
        .query_maintenance_history(target.get(), MaintenanceHistoryCursor::start(), 32)
        .unwrap();
    let assembly_failures = history
        .records
        .iter()
        .filter(|record| record["event"] == "maintenance_assembly_failure")
        .collect::<Vec<_>>();
    assert_eq!(assembly_failures.len(), 1);
    assert!(!assembly_failures[0]["artifact_reference"].is_null());
    assert!(
        history
            .records
            .iter()
            .all(|record| record["event"] != "maintenance_attempt"),
        "assembly-only failure allocated a solver attempt: {history:#?}"
    );

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn late_lane_local_assembly_failure_becomes_live_after_concurrent_coverage_publication() {
    let task = support::export_canonical_task();
    let root = support::TestDir::new("phase3d_late_lane_local_assembly_failure");
    let gate = root.path().join("release-support-failure");
    let request_marker = root.path().join("support-request");
    let launch_log = root.path().join("launches");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(root.path().join("artifacts")).maintenance_history(true, true),
    )
    .unwrap();
    let context = new_solver_encoding_context(
        &task,
        &artifacts,
        gated_malformed_support_worker_config(&gate, &request_marker),
    )
    .unwrap();
    let mut state = new_state(
        &task,
        &artifacts,
        &context,
        Duration::from_secs(60),
        vec![Duration::from_secs(30)],
    );
    let [source, target] = install_late_coverage_active_with_target_wp(
        &task,
        &mut state,
        Some(mixed_constant_wp(&task, "phase3d.late_assembly_failure.wp")),
    )
    .await;
    let observer = open_gate_after_proved_history(
        artifacts.clone(),
        source,
        request_marker.clone(),
        gate.clone(),
    );

    let outcome = tokio::time::timeout(
        Duration::from_secs(65),
        run_maintenance_block(
            &task,
            &mut state,
            vampire_command("race-fmb-failure-proof", Some(&launch_log)),
            &CancellationToken::new(),
        ),
    )
    .await
    .expect("gated assembly-failure block timed out");
    observer.join().expect("history observer failed");
    let MaintenanceExecutionOutcome::Complete(block) = outcome else {
        panic!("late LaneLocal assembly failure did not complete: {outcome:#?}");
    };
    assert_eq!(block.outcome(), MaintenanceBlockOutcome::Stable);
    assert_eq!(block.known_live(), &ClauseSet::from([source, target]));
    assert!(state.maintenance_failure().is_none());
    assert!(
        request_marker.exists(),
        "the gated support request did not run"
    );
    assert!(gate.exists(), "source proof did not release the failure");
    assert_eq!(
        launch_count(&launch_log),
        2,
        "the assembly-failing target reached Vampire"
    );

    let record = state.catalog().record(target).unwrap();
    assert!(!record.has_retry_candidate());
    assert_eq!(record.next_retry_tier(), 0);
    assert!(!record.retry_exhausted());
    assert_eq!(record.next_fmb_start_size(), None);
    let history = artifacts
        .query_maintenance_history(target.get(), MaintenanceHistoryCursor::start(), 32)
        .unwrap();
    assert!(
        history.records.iter().all(|record| {
            record["event"] != "maintenance_attempt"
                && record["event"] != "maintenance_assembly_failure"
        }),
        "the late shortcut retained work which was already redundant: {history:#?}"
    );

    shutdown(state, context, artifacts, owner).await;
}

// ------------------------------------------------------------
// Retry, Cancellation, And Optional History
// ------------------------------------------------------------

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn retry_exhaustion_launches_no_second_query_for_the_same_candidate() {
    let task = support::export_canonical_task();
    let root = support::TestDir::new("phase3d_retry_exhaustion");
    let launch_log = root.path().join("launches");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(root.path().join("artifacts")),
    )
    .unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_state(
        &task,
        &artifacts,
        &context,
        // Leave enough wall time for both fixture processes to launch even
        // when the full integration suite is scheduling other subprocesses.
        Duration::from_secs(1),
        Vec::new(),
    );
    let prepared = state
        .prepare_init_candidates(
            vec![formula(
                &task,
                "phase3d.timeout",
                "task.phase2c_qf_fixture",
                &[],
            )],
            &ClauseSet::new(),
            &CancellationToken::new(),
        )
        .await;
    assert!(matches!(
        prepared,
        InitializationInvocationOutcome::Complete
    ));
    let id = *state.init_candidates().iter().next().unwrap();
    let evidence = state
        .catalog()
        .artifacts()
        .publish(
            ArtifactKind::InitializationCheck,
            b"phase3d InitProved".as_slice().into(),
        )
        .unwrap();
    state
        .catalog()
        .record_initialization(id, InitializationStatus::InitProved, evidence)
        .unwrap();
    assert!(matches!(
        prepare_maintenance(&task, &mut state, &CancellationToken::new()).await,
        MaintenancePreparationOutcome::Complete
    ));

    let first = run_maintenance_block(
        &task,
        &mut state,
        vampire_command("race-timeout", Some(&launch_log)),
        &CancellationToken::new(),
    )
    .await;
    let MaintenanceExecutionOutcome::Complete(first) = first else {
        panic!("first timeout block did not complete: {first:#?}");
    };
    assert_eq!(first.outcome(), MaintenanceBlockOutcome::TimedOut(id));
    assert_eq!(launch_count(&launch_log), 2);

    let second = run_maintenance_block(
        &task,
        &mut state,
        vampire_command("race-timeout", Some(&launch_log)),
        &CancellationToken::new(),
    )
    .await;
    let MaintenanceExecutionOutcome::Complete(second) = second else {
        panic!("exhaustion block did not complete: {second:#?}");
    };
    assert_eq!(
        second.outcome(),
        MaintenanceBlockOutcome::RetryExhausted(id)
    );
    assert_eq!(
        launch_count(&launch_log),
        2,
        "retry exhaustion launched work"
    );

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn strict_history_indexes_attempt_transitions_by_clause() {
    let task = support::export_canonical_task();
    let root = support::TestDir::new("phase3d_attempt_history");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(root.path().join("artifacts")).maintenance_history(true, true),
    )
    .unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_state(
        &task,
        &artifacts,
        &context,
        Duration::from_secs(30),
        Vec::new(),
    );
    let ids = install_two_track_active(&task, &mut state, false).await;
    let outcome = run_maintenance_block(
        &task,
        &mut state,
        vampire_command("race-fmb-failure-proof", None),
        &CancellationToken::new(),
    )
    .await;
    assert!(matches!(outcome, MaintenanceExecutionOutcome::Complete(_)));

    for id in ids {
        let page = artifacts
            .query_maintenance_history(id.get(), MaintenanceHistoryCursor::start(), 32)
            .unwrap();
        let attempts = page
            .records
            .iter()
            .filter(|record| record["event"] == "maintenance_attempt")
            .collect::<Vec<_>>();
        assert_eq!(attempts.len(), 2, "pending and terminal transitions");
        assert!(attempts.iter().any(|record| record["outcome"].is_null()));
        assert!(attempts.iter().any(|record| record["outcome"] == "proved"));
        assert_eq!(attempts[0]["attempt_id"], attempts[1]["attempt_id"]);
    }

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn first_nonstable_track_result_cancels_and_joins_its_peer() {
    let task = support::export_canonical_task();
    let root = support::TestDir::new("phase3d_nonstable_join");
    let launch_log = root.path().join("launches");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(root.path().join("artifacts")),
    )
    .unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_state(
        &task,
        &artifacts,
        &context,
        Duration::from_secs(30),
        Vec::new(),
    );
    let ids = install_two_track_active(&task, &mut state, false).await;
    let entry_active = state.active().clone();

    let outcome = run_maintenance_block(
        &task,
        &mut state,
        vampire_command("race-model-win", Some(&launch_log)),
        &CancellationToken::new(),
    )
    .await;
    let MaintenanceExecutionOutcome::Complete(block) = outcome else {
        panic!("nonstable concurrent block did not complete: {outcome:#?}");
    };
    let MaintenanceBlockOutcome::Refuted(target) = block.outcome() else {
        panic!("expected one refuted target: {block:#?}");
    };
    assert!(ids.contains(&target));
    assert_eq!(
        state.active(),
        &entry_active,
        "block execution is immutable"
    );
    assert!(launch_count(&launch_log) >= 2);

    // Context shutdown succeeding immediately after return is the retained-
    // process ownership check: no canceled peer task or Vampire tree survives.
    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn run_global_query_assembly_failure_is_sticky_and_never_excludes() {
    let task = support::export_canonical_task();
    let root = support::TestDir::new("phase3d_run_global_assembly_failure");
    let launch_log = root.path().join("launches");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(root.path().join("artifacts")),
    )
    .unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_state(
        &task,
        &artifacts,
        &context,
        Duration::from_secs(30),
        Vec::new(),
    );
    install_two_track_active(&task, &mut state, false).await;
    let entry_active = state.active().clone();

    // Consuming the unique backend owner before the encoding context shuts
    // down is an intentional fault injection. Settlement fails closed and
    // leaves query publication unavailable, so assembly must report a
    // RunGlobal failure before either Vampire race can launch.
    let premature_settlement = owner.settle().unwrap_err();
    assert_eq!(premature_settlement.scope(), FailureScope::RunGlobal);
    let outcome = run_maintenance_block(
        &task,
        &mut state,
        vampire_command("race-proof-failure-model", Some(&launch_log)),
        &CancellationToken::new(),
    )
    .await;
    let MaintenanceExecutionOutcome::Failed(report) = outcome else {
        panic!("closed query backend did not fail maintenance: {outcome:#?}");
    };
    assert_eq!(report.scope(), FailureScope::RunGlobal);
    let retained = state
        .maintenance_failure()
        .expect("RunGlobal failure remains sticky in HoudiniState");
    assert_eq!(retained.scope(), report.scope());
    assert_eq!(retained.origin(), report.origin());
    assert_eq!(retained.kind(), report.kind());
    assert_eq!(state.active(), &entry_active);
    assert!(state.core().is_empty());
    assert_eq!(launch_count(&launch_log), 0);

    context.shutdown().await.unwrap();
    drop(state);
    drop(context);
    drop(artifacts);
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn caller_cancellation_stops_and_joins_all_track_process_trees() {
    let task = support::export_canonical_task();
    let root = support::TestDir::new("phase3d_cancel_join");
    let launch_log = root.path().join("launches");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(root.path().join("artifacts")),
    )
    .unwrap();
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_state(
        &task,
        &artifacts,
        &context,
        Duration::from_secs(30),
        Vec::new(),
    );
    install_two_track_active(&task, &mut state, false).await;
    let cancellation = CancellationToken::new();
    let trigger = cancellation.clone();
    let trigger_log = launch_log.clone();
    tokio::spawn(async move {
        let deadline = tokio::time::Instant::now() + Duration::from_secs(10);
        while launch_count(&trigger_log) < 2 && tokio::time::Instant::now() < deadline {
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
        trigger.cancel();
    });

    let started = std::time::Instant::now();
    let outcome = run_maintenance_block(
        &task,
        &mut state,
        vampire_command("race-timeout", Some(&launch_log)),
        &cancellation,
    )
    .await;
    assert!(matches!(outcome, MaintenanceExecutionOutcome::Cancelled));
    assert!(started.elapsed() < Duration::from_secs(5));
    assert!(state.maintenance_failure().is_none());
    assert!(launch_count(&launch_log) >= 2);

    shutdown(state, context, artifacts, owner).await;
}

// ------------------------------------------------------------
// Concurrent Generation Lifecycle
// ------------------------------------------------------------

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn strict_stable_history_opens_before_attempts_and_closes_once() {
    let task = support::export_canonical_task();
    let root = support::TestDir::new("phase3d_stable_lifecycle");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(root.path().join("artifacts")).maintenance_history(true, true),
    )
    .unwrap();
    let run_root = history_run_root(&artifacts);
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_state(
        &task,
        &artifacts,
        &context,
        Duration::from_secs(30),
        Vec::new(),
    );
    install_two_track_active(&task, &mut state, false).await;

    let outcome = run_maintenance_block(
        &task,
        &mut state,
        vampire_command("race-fmb-failure-proof", None),
        &CancellationToken::new(),
    )
    .await;
    let MaintenanceExecutionOutcome::Complete(block) = outcome else {
        panic!("stable concurrent generation did not complete: {outcome:#?}");
    };
    assert_eq!(block.outcome(), MaintenanceBlockOutcome::Stable);

    let records = read_history(&run_root);
    let open = records
        .iter()
        .position(|record| {
            record["event"] == "maintenance_generation_state" && record["state"] == "open"
        })
        .expect("generation Open record");
    let attempts = records
        .iter()
        .enumerate()
        .filter_map(|(index, record)| (record["event"] == "maintenance_attempt").then_some(index))
        .collect::<Vec<_>>();
    assert!(!attempts.is_empty());
    let closed = records
        .iter()
        .position(|record| {
            record["event"] == "maintenance_generation_state" && record["state"] == "closed"
        })
        .expect("generation Closed record");
    assert!(
        attempts
            .iter()
            .all(|attempt| open < *attempt && *attempt < closed)
    );

    let lifecycle = records
        .iter()
        .filter(|record| record["event"] == "maintenance_generation_state")
        .collect::<Vec<_>>();
    assert_eq!(lifecycle.len(), 2);
    assert!(lifecycle[0]["initial_core"].is_array());
    assert!(lifecycle[0]["initial_active"].is_array());
    assert!(lifecycle[0]["candidate"].is_array());
    assert!(lifecycle[0].get("baseline_generation").is_none());
    assert!(lifecycle[1].get("initial_core").is_none());
    assert!(lifecycle[1].get("initial_active").is_none());
    assert!(lifecycle[1].get("candidate").is_none());
    assert_eq!(lifecycle[1]["outcome"], "stable");
    assert_eq!(lifecycle[1]["exclusion_applied"], false);

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn cancellation_after_open_emits_canceled_without_mutating_retry_or_sets() {
    let task = support::export_canonical_task();
    let root = support::TestDir::new("phase3d_canceled_lifecycle");
    let launch_log = root.path().join("launches");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(root.path().join("artifacts")).maintenance_history(true, true),
    )
    .unwrap();
    let run_root = history_run_root(&artifacts);
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_state(
        &task,
        &artifacts,
        &context,
        Duration::from_secs(30),
        vec![Duration::from_secs(30)],
    );
    let ids = install_two_track_active(&task, &mut state, false).await;
    let entry_active = state.active().clone();
    let entry_core = state.core().clone();
    let entry_retry = ids.map(|id| {
        let record = state.catalog().record(id).unwrap();
        (
            record.has_retry_candidate(),
            record.retry_candidate_len(),
            record.next_retry_tier(),
            record.retry_exhausted(),
            record.next_fmb_start_size(),
        )
    });
    let cancellation = CancellationToken::new();
    let trigger = cancellation.clone();
    let trigger_log = launch_log.clone();
    tokio::spawn(async move {
        let deadline = tokio::time::Instant::now() + Duration::from_secs(10);
        while launch_count(&trigger_log) < 2 && tokio::time::Instant::now() < deadline {
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
        trigger.cancel();
    });

    let outcome = run_maintenance_block(
        &task,
        &mut state,
        vampire_command("race-timeout", Some(&launch_log)),
        &cancellation,
    )
    .await;
    assert!(matches!(outcome, MaintenanceExecutionOutcome::Cancelled));
    assert!(launch_count(&launch_log) >= 2);
    assert_eq!(state.active(), &entry_active);
    assert_eq!(state.core(), &entry_core);
    for (id, expected) in ids.into_iter().zip(entry_retry) {
        let record = state.catalog().record(id).unwrap();
        assert_eq!(
            (
                record.has_retry_candidate(),
                record.retry_candidate_len(),
                record.next_retry_tier(),
                record.retry_exhausted(),
                record.next_fmb_start_size(),
            ),
            expected
        );
    }

    let records = read_history(&run_root);
    let open = records
        .iter()
        .position(|record| {
            record["event"] == "maintenance_generation_state" && record["state"] == "open"
        })
        .expect("generation Open record");
    let canceled = records
        .iter()
        .position(|record| record["event"] == "maintenance_generation_canceled")
        .expect("distinct generation canceled record");
    assert!(open < canceled);
    assert!(!records.iter().any(|record| {
        record["event"] == "maintenance_generation_state"
            && matches!(
                record["state"].as_str(),
                Some("closed" | "aborted" | "abandoned")
            )
    }));

    // Successful shutdown is the retained-process ownership assertion.
    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn nonstable_blocks_log_close_then_exactly_one_exclusion_commit() {
    let task = support::export_canonical_task();
    let root = support::TestDir::new("phase3d_exclusion_lifecycle");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(root.path().join("artifacts")).maintenance_history(true, true),
    )
    .unwrap();
    let run_root = history_run_root(&artifacts);
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_state(
        &task,
        &artifacts,
        &context,
        Duration::from_secs(30),
        Vec::new(),
    );
    let target = install_single_active(&task, &mut state).await;
    let entry_active = state.active().clone();

    let outcome = run_maintenance_blocks(
        &task,
        &mut state,
        vampire_command("race-proof-failure-model", None),
        &CancellationToken::new(),
    )
    .await;
    assert!(matches!(
        outcome,
        MaintenanceExecutionOutcome::Complete(None)
    ));
    assert_eq!(entry_active, ClauseSet::from([target]));
    assert!(state.active().is_empty());
    assert!(state.core().is_empty());

    let records = read_history(&run_root);
    let lifecycle = records
        .iter()
        .filter(|record| {
            record["event"] == "maintenance_generation_state"
                || record["event"] == "maintenance_exclusion_applied"
        })
        .collect::<Vec<_>>();
    assert_eq!(lifecycle.len(), 4);
    assert_eq!(lifecycle[0]["state"], "open");
    assert_eq!(lifecycle[1]["state"], "closed");
    assert_eq!(lifecycle[1]["exclusion_applied"], false);
    assert_eq!(lifecycle[2]["state"], "closed");
    assert_eq!(lifecycle[2]["exclusion_applied"], true);
    assert_eq!(lifecycle[3]["event"], "maintenance_exclusion_applied");
    assert_eq!(lifecycle[3]["target"], target.get());
    assert!(lifecycle[0]["initial_core"].is_array());
    assert!(lifecycle[0]["initial_active"].is_array());
    assert!(lifecycle[0]["candidate"].is_array());
    assert!(lifecycle[1]["known_live"].is_array());
    assert!(lifecycle[2].get("known_live").is_none());
    assert!(lifecycle[0].get("baseline_generation").is_none());
    assert!(lifecycle[1..].iter().all(|record| {
        record.get("initial_core").is_none()
            && record.get("initial_active").is_none()
            && record.get("candidate").is_none()
    }));

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn shrinking_generations_share_one_strict_history_baseline() {
    let task = support::export_canonical_task();
    let root = support::TestDir::new("phase3d_shared_history_baseline");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(root.path().join("artifacts")).maintenance_history(true, true),
    )
    .unwrap();
    let run_root = history_run_root(&artifacts);
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_state(
        &task,
        &artifacts,
        &context,
        Duration::from_secs(30),
        Vec::new(),
    );
    let ids = install_two_track_active(&task, &mut state, false).await;
    let mut initial_active = ids.into_iter().map(ClauseId::get).collect::<Vec<_>>();
    initial_active.sort_unstable();

    let outcome = run_maintenance_blocks(
        &task,
        &mut state,
        vampire_command("race-proof-failure-model", None),
        &CancellationToken::new(),
    )
    .await;
    assert!(matches!(
        outcome,
        MaintenanceExecutionOutcome::Complete(None)
    ));
    assert!(state.active().is_empty());
    assert!(state.core().is_empty());

    let records = read_history(&run_root);
    let lifecycle = records
        .iter()
        .filter(|record| {
            record["event"] == "maintenance_generation_state"
                || record["event"] == "maintenance_exclusion_applied"
        })
        .collect::<Vec<_>>();
    let opens = lifecycle
        .iter()
        .filter(|record| record["state"] == "open")
        .copied()
        .collect::<Vec<_>>();
    assert!(opens.len() >= 2, "expected multiple shrinking generations");

    let baseline_generation = opens[0]["generation"].as_u64().unwrap();
    let expected_initial = serde_json::to_value(&initial_active).unwrap();
    assert_eq!(opens[0]["initial_core"], serde_json::json!([]));
    assert_eq!(opens[0]["initial_active"], expected_initial);
    assert_eq!(opens[0]["candidate"], expected_initial);
    assert!(opens[0].get("baseline_generation").is_none());
    for open in &opens[1..] {
        assert!(open.get("initial_core").is_none());
        assert!(open.get("initial_active").is_none());
        assert!(open.get("candidate").is_none());
        assert_eq!(open["baseline_generation"], baseline_generation);
    }
    assert_eq!(
        lifecycle
            .iter()
            .filter(|record| record.get("initial_core").is_some())
            .count(),
        1,
        "the shrinking run must emit exactly one full baseline"
    );
    let mut generations = std::collections::HashMap::<u64, usize>::new();
    for record in &lifecycle {
        if let (Some(generation), Some(_)) =
            (record["generation"].as_u64(), record.get("known_live"))
        {
            *generations.entry(generation).or_default() += 1;
        }
    }
    assert!(
        generations.values().all(|count| *count <= 1),
        "a generation serialized its final known-live snapshot more than once"
    );

    let exclusions = lifecycle
        .iter()
        .filter(|record| record["event"] == "maintenance_exclusion_applied")
        .copied()
        .collect::<Vec<_>>();
    assert_eq!(exclusions.len(), opens.len());
    let mut reconstructed_active = initial_active.clone();
    for (generation_index, (open, exclusion)) in opens.iter().zip(exclusions).enumerate() {
        let generation = open["generation"].as_u64().unwrap();
        let open_index = lifecycle
            .iter()
            .position(|record| std::ptr::eq(*record, *open))
            .unwrap();
        let closed_before_exclusion = lifecycle
            .iter()
            .position(|record| {
                record["generation"] == generation
                    && record["state"] == "closed"
                    && record["exclusion_applied"] == false
            })
            .unwrap();
        let closed_after_exclusion = lifecycle
            .iter()
            .position(|record| {
                record["generation"] == generation
                    && record["state"] == "closed"
                    && record["exclusion_applied"] == true
            })
            .unwrap();
        let exclusion_index = lifecycle
            .iter()
            .position(|record| std::ptr::eq(*record, exclusion))
            .unwrap();
        assert!(
            open_index < closed_before_exclusion
                && closed_before_exclusion < closed_after_exclusion
                && closed_after_exclusion < exclusion_index
        );
        if let Some(next_open) = opens.get(generation_index + 1) {
            let next_open_index = lifecycle
                .iter()
                .position(|record| std::ptr::eq(*record, *next_open))
                .unwrap();
            assert!(exclusion_index < next_open_index);
        }

        let target = exclusion["target"].as_u64().unwrap();
        let position = reconstructed_active
            .iter()
            .position(|clause| *clause == target)
            .expect("each ordered delta removes one currently active clause");
        reconstructed_active.remove(position);
    }
    assert!(reconstructed_active.is_empty());

    shutdown(state, context, artifacts, owner).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn history_off_keeps_optional_history_infrastructure_dormant() {
    let task = support::export_canonical_task();
    let root = support::TestDir::new("phase3d_history_off_lifecycle");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(root.path().join("artifacts")),
    )
    .unwrap();
    let run_root = history_run_root(&artifacts);
    let context = new_solver_encoding_context(&task, &artifacts, worker_config()).unwrap();
    let mut state = new_state(
        &task,
        &artifacts,
        &context,
        Duration::from_secs(30),
        Vec::new(),
    );
    install_single_active(&task, &mut state).await;
    let before = artifacts.diagnostics();
    assert!(!before.history_sink_initialized);
    assert_eq!(before.history_records_constructed, 0);
    assert!(!before.history_path_exists);

    let outcome = run_maintenance_block(
        &task,
        &mut state,
        vampire_command("race-fmb-failure-proof", None),
        &CancellationToken::new(),
    )
    .await;
    let MaintenanceExecutionOutcome::Complete(block) = outcome else {
        panic!("history-off stable block did not complete: {outcome:#?}");
    };
    assert_eq!(block.outcome(), MaintenanceBlockOutcome::Stable);
    let after = artifacts.diagnostics();
    assert!(!after.history_sink_initialized);
    assert_eq!(after.history_records_constructed, 0);
    assert_eq!(after.history_records_written, 0);
    assert_eq!(after.history_queue_depth, 0);
    assert_eq!(after.history_queue_high_water, 0);
    assert!(!after.history_path_exists);
    assert!(!run_root.join("history").exists());

    shutdown(state, context, artifacts, owner).await;
}
