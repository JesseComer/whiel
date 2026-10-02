mod support;

use std::collections::BTreeSet;

#[cfg(unix)]
use whiel_runner::encoding::{EncodingError, SolverBodySource};
use whiel_runner::encoding::{
    EncodingWorkerCommand, EncodingWorkerPoolConfig, ProposalRealization,
    new_solver_encoding_context,
};
use whiel_runner::{
    ArtifactStoreConfig, CancellationToken, InitializationInvocationOutcome, RuntimeResourcePolicy,
    TelemetryConfig, TelemetryLevel, TelemetrySession, VerificationParameters,
    create_general_solver_admission, create_symbolic_solver_admissions, new_artifact_store,
    new_symbolic_inv_state, prepare_ordinary_candidates, propose_symbolic_clauses,
};

// ------------------------------------------------------------
// Realization-Neutral Proposal Snapshots
// ------------------------------------------------------------

async fn first_two_waves(
    label: &str,
    realization: ProposalRealization,
) -> Vec<BTreeSet<(String, String)>> {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new(label);
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let admission =
        create_general_solver_admission(RuntimeResourcePolicy::agent_only(1, 1).unwrap()).unwrap();
    let workers = EncodingWorkerPoolConfig::new(
        EncodingWorkerCommand::new(
            support::example_encoding_worker(),
            support::repository_root(),
        ),
        2,
    )
    .unwrap()
    .proposal_realization(realization);
    let context = new_solver_encoding_context(&task, &artifacts, workers).unwrap();
    assert_eq!(context.proposal_realization(), realization);
    let cancellation = CancellationToken::new();
    let mut waves = Vec::new();
    for expected_stage in 0..2 {
        let batch = context
            .advance_reference_proposal(&admission, &cancellation)
            .await
            .unwrap();
        assert_eq!(batch.stage(), expected_stage);
        waves.push(
            batch
                .entries()
                .iter()
                .map(|entry| (entry.identity().to_string(), entry.display().to_string()))
                .collect::<BTreeSet<_>>(),
        );
    }

    context.shutdown().await.unwrap();
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
    waves
}

// ------------------------------------------------------------
// Production Selection And Immediate Reference Fallback
// ------------------------------------------------------------

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn fast_v1_matches_small_reference_wave_content_and_reference_remains_runnable() {
    let fast = first_two_waves("phase4e_fast_v1", ProposalRealization::FastV1).await;
    let reference = first_two_waves(
        "phase4e_reference_fallback",
        ProposalRealization::ReferenceV3,
    )
    .await;
    assert_eq!(fast, reference);
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn fast_v1_flows_through_symbolic_inv_proposal_catalog_and_telemetry() {
    use std::fs;
    use std::time::Duration;

    let task = support::export_canonical_task();
    let directory = support::TestDir::new("phase4e_fast_symbolic_inv_path");
    let (owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("artifacts")),
    )
    .unwrap();
    let resources = RuntimeResourcePolicy::symbolic(4, 2, 2).unwrap();
    let (inv, _cex) = create_symbolic_solver_admissions(resources).unwrap();
    let verification = VerificationParameters::new(Duration::from_secs(5), resources).unwrap();
    let workers = EncodingWorkerPoolConfig::new(
        EncodingWorkerCommand::new(
            support::example_encoding_worker(),
            support::repository_root(),
        ),
        2,
    )
    .unwrap()
    .proposal_realization(ProposalRealization::FastV1);
    let context = new_solver_encoding_context(&task, &artifacts, workers).unwrap();
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
    assert_eq!(state.proposal_progress().enumerator_version(), 1);
    assert_eq!(state.proposal_progress().last_stage(), Some(0));
    assert_eq!(state.proposal_progress().revision().get(), 1);
    assert!(!state.proposal().is_empty());
    assert!(matches!(
        prepare_ordinary_candidates(&mut state, &cancellation).await,
        InitializationInvocationOutcome::Complete
    ));
    assert_eq!(state.houdini().catalog().len(), state.proposal().len());
    for formula in state.proposal() {
        let id = state
            .houdini()
            .catalog()
            .find(formula)
            .unwrap()
            .expect("the fast proposal must be interned");
        assert!(
            state
                .houdini()
                .catalog()
                .record(id)
                .unwrap()
                .formula_body()
                .is_some()
        );
    }

    let report = telemetry.finish();
    assert_eq!(report.snapshot.waves.len(), 1);
    let wave = &report.snapshot.waves[0];
    assert_eq!(wave.stage, 0);
    assert_eq!(wave.emitted_formulas, state.proposal().len() as u64);
    assert_eq!(wave.registered_unique_formulas, wave.emitted_formulas);
    assert_eq!(wave.cumulative_catalog_size, wave.emitted_formulas);
    assert_eq!(wave.worker_stage_batch_evaluations, 1);
    assert!(wave.generator_work_units > 0);
    let events = fs::read_to_string(report.events_path.expect("detailed event path")).unwrap();
    let fast_wave = events
        .lines()
        .map(|line| serde_json::from_str::<serde_json::Value>(line).unwrap())
        .find(|event| event["kind"] == "reference_wave")
        .expect("one detailed fast-wave event");
    assert_eq!(
        fast_wave["payload"]["proposal_realization_id"],
        "lean-fast-v1"
    );
    assert_eq!(fast_wave["payload"]["proposal_realization_version"], 1);

    context.shutdown().await.unwrap();
    drop(state);
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}

// ------------------------------------------------------------
// Fast Worker Pagination And Replay
// ------------------------------------------------------------

#[cfg(unix)]
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn fast_v1_tiny_budget_pages_one_wave_without_restarting_the_worker() {
    use std::ffi::OsString;

    let task = support::export_canonical_task();
    let directory = support::TestDir::new("phase4e_fast_paged_worker_reuse");
    let state = directory.path().join("first-worker.state");
    let launches = directory.path().join("worker-launches.log");
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let admission =
        create_general_solver_admission(RuntimeResourcePolicy::agent_only(1, 1).unwrap()).unwrap();
    let worker = EncodingWorkerCommand::new(
        support::restartable_encoding_worker(),
        support::repository_root(),
    )
    .arguments([
        OsString::from(support::example_encoding_worker().as_os_str()),
        OsString::from(state.as_os_str()),
        OsString::from(launches.as_os_str()),
        OsString::from("count"),
    ]);
    let workers = EncodingWorkerPoolConfig::new(worker, 2)
        .unwrap()
        .max_frame_bytes(896)
        .unwrap()
        .proposal_realization(ProposalRealization::FastV1);
    let context = new_solver_encoding_context(&task, &artifacts, workers).unwrap();

    let batch = context
        .advance_reference_proposal(&admission, &CancellationToken::new())
        .await
        .unwrap();
    assert_eq!(batch.stage(), 0);
    assert_eq!(batch.revision().get(), 1);
    let events = std::fs::read_to_string(&launches).unwrap();
    let launch_count = events
        .lines()
        .filter(|event| event.starts_with("launch:"))
        .count();
    let page_count = events.lines().filter(|event| *event == "page").count();
    assert!(page_count > 1, "the tiny budget must force multiple pages");
    assert_eq!(batch.page_count(), page_count as u64);
    assert_eq!(
        launch_count, 1,
        "successful fast pages must retain one exact worker despite spare pool capacity"
    );

    context.shutdown().await.unwrap();
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}

#[cfg(unix)]
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn fast_v1_three_stages_keep_one_owner_while_ordinary_work_uses_spare_slot() {
    use std::ffi::OsString;

    let task = support::export_canonical_task();
    let directory = support::TestDir::new("phase4e_fast_cross_stage_affinity");
    let state = directory.path().join("first-worker.state");
    let events_path = directory.path().join("worker-events.log");
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let admission =
        create_general_solver_admission(RuntimeResourcePolicy::agent_only(1, 1).unwrap()).unwrap();
    let worker = EncodingWorkerCommand::new(
        support::restartable_encoding_worker(),
        support::repository_root(),
    )
    .arguments([
        OsString::from(support::example_encoding_worker().as_os_str()),
        OsString::from(state.as_os_str()),
        OsString::from(events_path.as_os_str()),
        OsString::from("synthetic_proposal_count"),
    ]);
    let workers = EncodingWorkerPoolConfig::new(worker, 2)
        .unwrap()
        .proposal_realization(ProposalRealization::FastV1);
    let context = new_solver_encoding_context(&task, &artifacts, workers).unwrap();

    for expected_stage in 0..3 {
        let batch = context
            .advance_reference_proposal(&admission, &CancellationToken::new())
            .await
            .unwrap();
        assert_eq!(batch.stage(), expected_stage);
        assert_eq!(batch.revision().get(), expected_stage + 1);
        assert!(batch.entries().is_empty());
        if expected_stage == 0 {
            let guard = context
                .prepare_loop_guard_body(&admission, &artifacts, &CancellationToken::new())
                .await
                .unwrap();
            assert!(!guard.tptp_body().is_empty());
        }
    }
    let events = std::fs::read_to_string(&events_path).unwrap();
    let launches = events
        .lines()
        .filter(|event| event.starts_with("launch:"))
        .map(|event| event.trim_start_matches("launch:"))
        .collect::<Vec<_>>();
    assert_eq!(
        launches.len(),
        2,
        "ordinary work should use the spare slot without stealing proposal ownership"
    );
    let owner_stages = events
        .lines()
        .filter(|event| event.starts_with(&format!("stage:{}:", launches[0])))
        .collect::<Vec<_>>();
    assert_eq!(
        owner_stages,
        [
            format!("stage:{}:0", launches[0]),
            format!("stage:{}:1", launches[0]),
            format!("stage:{}:2", launches[0]),
        ],
        "the preferred proposal child must advance without replay"
    );
    let spare_stages = events
        .lines()
        .filter(|event| event.starts_with(&format!("stage:{}:", launches[1])))
        .collect::<Vec<_>>();
    assert_eq!(
        spare_stages,
        [format!("stage:{}:0", launches[1])],
        "ordinary work may perform one bounded synchronization on its spare slot"
    );

    context.shutdown().await.unwrap();
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}

#[cfg(unix)]
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn fast_v1_replays_committed_frontier_after_worker_replacement() {
    use std::ffi::OsString;

    let expected =
        first_two_waves("phase4e_fast_restart_oracle", ProposalRealization::FastV1).await;
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("phase4e_fast_restart_frontier");
    let state = directory.path().join("first-worker.state");
    let marker = directory.path().join("failed-prepare.pid");
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let admission =
        create_general_solver_admission(RuntimeResourcePolicy::agent_only(1, 1).unwrap()).unwrap();
    let worker = EncodingWorkerCommand::new(
        support::restartable_encoding_worker(),
        support::repository_root(),
    )
    .arguments([
        OsString::from(support::example_encoding_worker().as_os_str()),
        OsString::from(state.as_os_str()),
        OsString::from(marker.as_os_str()),
        OsString::from("fail_first_prepare"),
    ]);
    let workers = EncodingWorkerPoolConfig::new(worker, 1)
        .unwrap()
        .proposal_realization(ProposalRealization::FastV1);
    let context = new_solver_encoding_context(&task, &artifacts, workers).unwrap();
    assert_eq!(context.proposal_realization(), ProposalRealization::FastV1);

    let first = context
        .advance_reference_proposal(&admission, &CancellationToken::new())
        .await
        .unwrap();
    let first_snapshot = first
        .entries()
        .iter()
        .map(|entry| (entry.identity().to_string(), entry.display().to_string()))
        .collect::<BTreeSet<_>>();
    assert_eq!(first.stage(), 0);
    assert_eq!(first.revision().get(), 1);
    assert_eq!(first_snapshot, expected[0]);

    // Kill the synchronized child on its next read-only request. Advancing
    // stage one must launch a replacement, replay the committed fast stage
    // zero pages, and continue from the reconstructed fast frontier.
    let old_source = SolverBodySource::QuantifierFree(first.entries()[0].source().clone());
    assert!(
        context
            .prepare_solver_bodies(
                &admission,
                &artifacts,
                vec![old_source.clone()],
                &CancellationToken::new(),
            )
            .await
            .is_err()
    );
    assert!(marker.exists());

    let second = context
        .advance_reference_proposal(&admission, &CancellationToken::new())
        .await
        .unwrap();
    let second_snapshot = second
        .entries()
        .iter()
        .map(|entry| (entry.identity().to_string(), entry.display().to_string()))
        .collect::<BTreeSet<_>>();
    assert_eq!(second.stage(), 1);
    assert_eq!(second.revision().get(), 2);
    assert_eq!(context.proposal_revision().get(), 2);
    assert_eq!(second_snapshot, expected[1]);
    assert!(first_snapshot.is_disjoint(&second_snapshot));
    assert!(
        second
            .entries()
            .iter()
            .all(|entry| entry.source().source_id().contains(":v1:s1:o"))
    );

    // The replacement learned the prior source bindings during replay.
    let old_body = context
        .prepare_solver_bodies(
            &admission,
            &artifacts,
            vec![old_source],
            &CancellationToken::new(),
        )
        .await
        .unwrap();
    assert_eq!(old_body.len(), 1);

    context.shutdown().await.unwrap();
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}

#[cfg(unix)]
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn cancelled_fast_v1_partial_wave_resumes_without_publishing_it_early() {
    use std::ffi::OsString;
    use std::time::Duration;

    let task = support::export_canonical_task();
    let directory = support::TestDir::new("phase4e_fast_cancel_mid_wave");
    let state = directory.path().join("first-worker.state");
    let marker = directory.path().join("second-page.pid");
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let admission =
        create_general_solver_admission(RuntimeResourcePolicy::agent_only(1, 1).unwrap()).unwrap();
    let worker = EncodingWorkerCommand::new(
        support::restartable_encoding_worker(),
        support::repository_root(),
    )
    .arguments([
        OsString::from(support::example_encoding_worker().as_os_str()),
        OsString::from(state.as_os_str()),
        OsString::from(marker.as_os_str()),
        OsString::from("stall_after_partial"),
    ]);
    let workers = EncodingWorkerPoolConfig::new(worker, 1)
        .unwrap()
        .max_frame_bytes(896)
        .unwrap()
        .proposal_realization(ProposalRealization::FastV1);
    let context = new_solver_encoding_context(&task, &artifacts, workers).unwrap();
    let cancellation = CancellationToken::new();
    let request = {
        let context = context.clone();
        let admission = admission.clone();
        let cancellation = cancellation.clone();
        tokio::spawn(async move {
            context
                .advance_reference_proposal(&admission, &cancellation)
                .await
        })
    };
    for _ in 0..500 {
        if marker.exists() {
            break;
        }
        tokio::time::sleep(Duration::from_millis(10)).await;
    }
    assert!(
        marker.exists(),
        "the fixture must stall after a private page"
    );
    let stalled_pid: i32 = std::fs::read_to_string(&marker).unwrap().parse().unwrap();
    assert_eq!(
        context.proposal_revision().get(),
        0,
        "a partial fast page must not publish a wave"
    );

    cancellation.cancel();
    assert!(matches!(
        request.await.unwrap(),
        Err(EncodingError::Cancelled)
    ));
    assert_process_gone(stalled_pid);
    assert_eq!(context.proposal_revision().get(), 0);

    let retry = tokio::time::timeout(
        Duration::from_secs(15),
        context.advance_reference_proposal(&admission, &CancellationToken::new()),
    )
    .await
    .expect("the replacement must resume the unpublished fast wave")
    .unwrap();
    assert_eq!(retry.stage(), 0);
    assert_eq!(retry.revision().get(), 1);
    assert!(!retry.entries().is_empty());
    assert!(
        retry
            .entries()
            .iter()
            .all(|entry| entry.source().source_id().contains(":v1:s0:o"))
    );

    context.shutdown().await.unwrap();
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}

#[cfg(unix)]
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn rejected_fast_v1_second_page_reaps_its_exact_worker_before_returning() {
    use std::ffi::OsString;

    let task = support::export_canonical_task();
    let directory = support::TestDir::new("phase4e_fast_reject_second_page");
    let state = directory.path().join("first-worker.state");
    let marker = directory.path().join("rejected-worker.pid");
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let admission =
        create_general_solver_admission(RuntimeResourcePolicy::agent_only(1, 1).unwrap()).unwrap();
    let worker = EncodingWorkerCommand::new(
        support::restartable_encoding_worker(),
        support::repository_root(),
    )
    .arguments([
        OsString::from(support::example_encoding_worker().as_os_str()),
        OsString::from(state.as_os_str()),
        OsString::from(marker.as_os_str()),
        OsString::from("reject_after_partial"),
    ]);
    let workers = EncodingWorkerPoolConfig::new(worker, 1)
        .unwrap()
        .max_frame_bytes(896)
        .unwrap()
        .proposal_realization(ProposalRealization::FastV1);
    let context = new_solver_encoding_context(&task, &artifacts, workers).unwrap();

    assert!(
        context
            .advance_reference_proposal(&admission, &CancellationToken::new())
            .await
            .is_err()
    );
    let rejected_pid: i32 = std::fs::read_to_string(&marker).unwrap().parse().unwrap();
    assert_process_gone(rejected_pid);
    assert_eq!(context.proposal_revision().get(), 0);

    let retry = context
        .advance_reference_proposal(&admission, &CancellationToken::new())
        .await
        .unwrap();
    assert_eq!(retry.stage(), 0);
    assert_eq!(retry.revision().get(), 1);

    context.shutdown().await.unwrap();
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}

#[cfg(unix)]
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn cancelled_next_page_admission_retires_the_pinned_worker_before_reuse() {
    use std::ffi::OsString;
    use std::time::Duration;

    let task = support::export_canonical_task();
    let directory = support::TestDir::new("phase4e_fast_cancel_next_page_admission");
    let state = directory.path().join("first-worker.state");
    let gates = directory.path().join("page-gates");
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let admission =
        create_general_solver_admission(RuntimeResourcePolicy::agent_only(1, 1).unwrap()).unwrap();
    let worker = EncodingWorkerCommand::new(
        support::restartable_encoding_worker(),
        support::repository_root(),
    )
    .arguments([
        OsString::from(support::example_encoding_worker().as_os_str()),
        OsString::from(state.as_os_str()),
        OsString::from(gates.as_os_str()),
        OsString::from("gate_first_partial"),
    ]);
    let workers = EncodingWorkerPoolConfig::new(worker, 1)
        .unwrap()
        .max_frame_bytes(896)
        .unwrap()
        .proposal_realization(ProposalRealization::FastV1);
    let context = new_solver_encoding_context(&task, &artifacts, workers).unwrap();
    let cancellation = CancellationToken::new();
    let registration = {
        let context = context.clone();
        let admission = admission.clone();
        let cancellation = cancellation.clone();
        tokio::spawn(async move {
            context
                .advance_reference_proposal(&admission, &cancellation)
                .await
        })
    };
    let first_page_ready = gates.join("first_page.ready");
    wait_for_path(&first_page_ready).await;
    let retained_pid: i32 = std::fs::read_to_string(&first_page_ready)
        .unwrap()
        .parse()
        .unwrap();

    // Queue a CPU holder while page one still owns the only CPU permit. FIFO
    // admission gives the holder the permit when that page is released, so
    // the pinned session must wait at the admission boundary for page two.
    let (holder_acquired_tx, holder_acquired_rx) = tokio::sync::oneshot::channel();
    let (holder_release_tx, holder_release_rx) = tokio::sync::oneshot::channel();
    let holder = {
        let admission = admission.clone();
        tokio::spawn(async move {
            let permit = admission
                .acquire_cpu_worker(&CancellationToken::new())
                .await
                .unwrap();
            holder_acquired_tx.send(()).unwrap();
            let _ = holder_release_rx.await;
            drop(permit);
        })
    };
    tokio::task::yield_now().await;
    std::fs::write(gates.join("first_page.release"), b"release").unwrap();
    tokio::time::timeout(Duration::from_secs(5), holder_acquired_rx)
        .await
        .expect("the queued CPU holder must run before page two")
        .unwrap();
    assert_eq!(context.proposal_revision().get(), 0);

    // A competing request queues for the same sole worker slot. Cancellation
    // of page-two admission must retire and reap the pinned process before a
    // replacement can use that capacity.
    let competing = {
        let context = context.clone();
        let admission = admission.clone();
        let artifacts = artifacts.clone();
        tokio::spawn(async move {
            context
                .prepare_loop_guard_body(&admission, &artifacts, &CancellationToken::new())
                .await
        })
    };
    tokio::task::yield_now().await;
    cancellation.cancel();
    holder_release_tx.send(()).unwrap();
    assert!(matches!(
        tokio::time::timeout(Duration::from_secs(10), registration)
            .await
            .expect("cancelled retained session must finish cleanup")
            .unwrap(),
        Err(EncodingError::Cancelled)
    ));
    assert_process_gone(retained_pid);
    holder.await.unwrap();
    let bodies = tokio::time::timeout(Duration::from_secs(10), competing)
        .await
        .expect("the worker slot must become reusable after retirement")
        .unwrap()
        .unwrap();
    assert!(!bodies.tptp_body().is_empty());
    wait_for_path(&gates.join("replacement.started")).await;
    assert!(
        !gates.join("replacement.overlap").exists(),
        "replacement capacity must not be published while the retired PID exists"
    );

    context.shutdown().await.unwrap();
    drop(context);
    drop(artifacts);
    owner.settle().unwrap();
}

#[cfg(unix)]
fn assert_process_gone(pid: i32) {
    assert_eq!(unsafe { libc::kill(pid, 0) }, -1);
    assert_eq!(
        std::io::Error::last_os_error().raw_os_error(),
        Some(libc::ESRCH),
        "the exact rejected worker must already be reaped"
    );
}

#[cfg(unix)]
async fn wait_for_path(path: &std::path::Path) {
    use std::time::Duration;

    for _ in 0..500 {
        if path.exists() {
            return;
        }
        tokio::time::sleep(Duration::from_millis(10)).await;
    }
    panic!("fixture marker was not written: {}", path.display());
}
