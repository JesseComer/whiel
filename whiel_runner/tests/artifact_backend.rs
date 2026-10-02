mod support;

use std::fs;
use std::io::Write;

use whiel_runner::artifact::{HistoryWorkerState, MaintenanceHistoryCursor};
use whiel_runner::{
    ArtifactKind, ArtifactStoreConfig, FailureKind, FailureOrigin, FailureScope, HistoryMode,
    ScopeTag, new_artifact_store,
};

#[test]
fn history_off_has_no_optional_infrastructure() {
    let directory = support::TestDir::new("history_off");
    let task = support::sample_task();
    let config = ArtifactStoreConfig::new(directory.path()).maintenance_history(false, true);
    let (owner, root) = new_artifact_store(&task, config).unwrap();

    let initial = root.diagnostics();
    assert_eq!(initial.history_mode, HistoryMode::Disabled);
    assert!(!initial.history_sink_initialized);
    assert_eq!(initial.history_records_constructed, 0);
    assert!(!initial.history_path_exists);

    let solver = root.scoped(ScopeTag::solver("proof"));
    let payload = vec![0x5a; 1024 * 1024].into_boxed_slice();
    let reference = solver.publish(ArtifactKind::Proof, payload).unwrap();
    let resolved_from_root = root.resolve(reference).unwrap();
    let resolved_from_sibling = root.scoped(ScopeTag::Inv).resolve(reference).unwrap();
    assert_eq!(resolved_from_root.path(), resolved_from_sibling.path());
    assert_eq!(resolved_from_root.byte_len(), 1024 * 1024);
    assert_eq!(
        fs::metadata(resolved_from_root.path()).unwrap().len(),
        1024 * 1024
    );

    let after_publish = root.diagnostics();
    assert_eq!(after_publish.required_payloads_published, 1);
    assert!(!after_publish.history_path_exists);
    assert_eq!(root.next_attempt_id().unwrap().get(), 0);
    assert_eq!(root.next_attempt_id().unwrap().get(), 1);

    let run_root = resolved_from_root
        .path()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf();
    fs::write(run_root.join("staging/incomplete.part"), b"partial").unwrap();
    owner.settle().unwrap();
    assert!(root.diagnostics().settled);
    let attempt_error = root.next_attempt_id().unwrap_err();
    assert_eq!(attempt_error.kind(), FailureKind::InfrastructureFailure);
    assert!(root.resolve(reference).is_ok());
    assert!(!run_root.join("staging").exists());
    assert!(!run_root.join("history").exists());
    let manifest = fs::read_to_string(run_root.join("manifest.json")).unwrap();
    assert!(manifest.contains("Example0012"));
    assert!(manifest.contains("artifact-00000000000000000000.bin"));
    assert_eq!(fs::read_dir(run_root.join("required")).unwrap().count(), 1);
    let error = root
        .publish(ArtifactKind::Proof, vec![1].into_boxed_slice())
        .unwrap_err();
    assert_eq!(error.kind(), FailureKind::PublicationFailure);
    assert!(!root.diagnostics().history_path_exists);
}

#[test]
fn backend_identity_prevents_cross_run_resolution() {
    let directory = support::TestDir::new("backend_identity");
    let task = support::sample_task();
    let (owner_a, store_a) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path().join("a"))).unwrap();
    let (owner_b, store_b) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path().join("b"))).unwrap();
    assert_ne!(store_a.backend_id(), store_b.backend_id());
    assert_eq!(store_a.task_identity(), store_b.task_identity());

    let reference = store_a
        .publish(ArtifactKind::Model, b"model".to_vec().into_boxed_slice())
        .unwrap();
    let error = store_b.resolve(reference).unwrap_err();
    assert_eq!(error.kind(), FailureKind::InfrastructureFailure);

    owner_a.settle().unwrap();
    owner_b.settle().unwrap();
}

#[test]
fn failed_manifest_freeze_is_not_reported_as_settled() {
    let directory = support::TestDir::new("settlement_failure");
    let task = support::sample_task();
    let (owner, store) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let reference = store
        .publish(ArtifactKind::Proof, b"proof".to_vec().into_boxed_slice())
        .unwrap();
    let resolved = store.resolve(reference).unwrap();
    let run_root = resolved.path().parent().unwrap().parent().unwrap();
    fs::create_dir(run_root.join("manifest.json")).unwrap();

    let error = owner.settle().unwrap_err();
    assert_eq!(error.origin(), FailureOrigin::ArtifactSettlement);
    assert_eq!(error.kind(), FailureKind::ManifestFailure);
    assert!(!error.retryable());
    assert_eq!(error.scope(), FailureScope::RunGlobal);
    assert!(!store.diagnostics().settled);
    assert!(store.diagnostics().settlement_failed);
}

#[test]
fn enabled_history_is_lazy_bounded_and_queryable_by_clause() {
    let directory = support::TestDir::new("history_index");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path())
            .maintenance_history(true, true)
            .maintenance_history_queue_capacity(8),
    )
    .unwrap();

    let initial = store.diagnostics();
    assert_eq!(initial.history_worker_state, HistoryWorkerState::Dormant);
    assert_eq!(initial.history_queue_capacity, 8);
    assert_eq!(initial.history_queue_depth, 0);
    assert_eq!(initial.history_queue_high_water, 0);
    assert!(!initial.history_path_exists);

    for sequence in 0..3_u64 {
        store
            .append_maintenance_history_value(
                serde_json::json!({"event":"attempt", "sequence":sequence}),
                if sequence == 1 {
                    &[7_u64][..]
                } else {
                    &[7_u64, 9][..]
                },
            )
            .unwrap();
    }

    let first = store
        .query_maintenance_history(7, MaintenanceHistoryCursor::start(), 2)
        .unwrap();
    assert_eq!(first.records.len(), 2);
    assert_eq!(first.records[0]["sequence"], 0);
    assert_eq!(first.records[1]["sequence"], 1);
    let cursor = first.next_cursor.expect("clause 7 has one more page");
    assert!(cursor.get() > 0);
    let second = store.query_maintenance_history(7, cursor, 2).unwrap();
    assert_eq!(second.records.len(), 1);
    assert_eq!(second.records[0]["sequence"], 2);
    assert!(second.next_cursor.is_none());

    let clause_nine = store
        .query_maintenance_history(9, MaintenanceHistoryCursor::start(), 256)
        .unwrap();
    assert_eq!(clause_nine.records.len(), 2);
    assert_eq!(clause_nine.records[0]["sequence"], 0);
    assert_eq!(clause_nine.records[1]["sequence"], 2);

    let diagnostics = store.diagnostics();
    assert_eq!(diagnostics.history_records_constructed, 3);
    assert_eq!(diagnostics.history_records_written, 3);
    assert!(diagnostics.history_queue_high_water <= 8);
    assert_eq!(diagnostics.history_queue_depth, 0);
    assert_eq!(
        diagnostics.history_worker_state,
        HistoryWorkerState::Running
    );

    let observer = store.clone();
    drop(store);
    owner.settle().unwrap();
    assert_eq!(
        observer.diagnostics().history_worker_state,
        HistoryWorkerState::Stopped
    );
}

#[test]
fn disabled_history_accepts_no_event_or_index_infrastructure() {
    let directory = support::TestDir::new("disabled_history_event");
    let task = support::sample_task();
    let (owner, store) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();

    store
        .append_maintenance_history_value(serde_json::json!({"event":"must_not_exist"}), &[17])
        .unwrap();
    let page = store
        .query_maintenance_history(17, MaintenanceHistoryCursor::start(), 10)
        .unwrap();
    assert!(page.records.is_empty());
    let diagnostics = store.diagnostics();
    assert_eq!(
        diagnostics.history_worker_state,
        HistoryWorkerState::Disabled
    );
    assert_eq!(diagnostics.history_queue_capacity, 0);
    assert_eq!(diagnostics.history_records_constructed, 0);
    assert!(!diagnostics.history_path_exists);

    owner.settle().unwrap();
}

#[test]
fn enabled_history_rejects_a_zero_sized_queue() {
    let directory = support::TestDir::new("zero_history_queue");
    let task = support::sample_task();
    let error = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path())
            .maintenance_history(true, true)
            .maintenance_history_queue_capacity(0),
    )
    .unwrap_err();
    assert_eq!(error.kind(), FailureKind::InfrastructureFailure);
}

#[test]
fn best_effort_history_disables_after_writer_failure() {
    let directory = support::TestDir::new("best_effort_history_failure");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path())
            .maintenance_history(true, false)
            .maintenance_history_queue_capacity(1),
    )
    .unwrap();
    let marker = store
        .publish(
            ArtifactKind::RuntimeTrace,
            b"required".to_vec().into_boxed_slice(),
        )
        .unwrap();
    let run_root = store
        .resolve(marker)
        .unwrap()
        .path()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf();
    fs::write(run_root.join("history"), b"not a directory").unwrap();

    store
        .append_maintenance_history_value(serde_json::json!({"event":"failure"}), &[23])
        .unwrap();
    assert!(
        store
            .query_maintenance_history(23, MaintenanceHistoryCursor::start(), 1)
            .unwrap()
            .records
            .is_empty()
    );
    let accepted = store.diagnostics().history_records_constructed;
    store
        .append_maintenance_history_value(serde_json::json!({"after":"disabled"}), &[23])
        .unwrap();
    assert_eq!(store.diagnostics().history_records_constructed, accepted);
    assert_eq!(
        store.diagnostics().history_worker_state,
        HistoryWorkerState::Failed
    );

    owner.settle().unwrap();
}

#[test]
fn strict_history_worker_failure_surfaces_at_query_and_final_settlement() {
    let directory = support::TestDir::new("history_worker_failure");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path()).maintenance_history(true, true),
    )
    .unwrap();
    let marker = store
        .publish(
            ArtifactKind::RuntimeTrace,
            b"required".to_vec().into_boxed_slice(),
        )
        .unwrap();
    let run_root = store
        .resolve(marker)
        .unwrap()
        .path()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf();
    fs::write(run_root.join("history"), b"not a directory").unwrap();

    store
        .append_maintenance_history_value(serde_json::json!({"event":"failure"}), &[1])
        .unwrap();
    let error = store
        .query_maintenance_history(1, MaintenanceHistoryCursor::start(), 1)
        .unwrap_err();
    assert_eq!(error.kind(), FailureKind::HistoryLogFailure);
    assert_eq!(
        store.diagnostics().history_worker_state,
        HistoryWorkerState::Failed
    );

    let settlement = owner.settle().unwrap_err();
    assert_eq!(settlement.kind(), FailureKind::HistoryLogFailure);
    assert!(run_root.join("manifest.json").is_file());
}

#[test]
fn strict_history_applies_backpressure_instead_of_failing_when_queue_is_full() {
    let directory = support::TestDir::new("strict_history_backpressure");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path())
            .maintenance_history(true, true)
            .maintenance_history_queue_capacity(1),
    )
    .unwrap();

    let threads: Vec<_> = (0..16_u64)
        .map(|sequence| {
            let store = store.clone();
            std::thread::spawn(move || {
                store.append_maintenance_history_value(
                    serde_json::json!({"event":"saturation", "sequence":sequence}),
                    &[41],
                )
            })
        })
        .collect();
    for thread in threads {
        thread.join().unwrap().unwrap();
    }

    let page = store
        .query_maintenance_history(41, MaintenanceHistoryCursor::start(), 32)
        .unwrap();
    assert_eq!(page.records.len(), 16);
    assert_eq!(store.diagnostics().history_queue_high_water, 1);
    owner.settle().unwrap();
}

#[test]
fn strict_backpressure_repeatedly_wakes_waiters_without_lost_notifications() {
    let directory = support::TestDir::new("strict_history_wakeup");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path())
            .maintenance_history(true, true)
            .maintenance_history_queue_capacity(1),
    )
    .unwrap();

    let (done_tx, done_rx) = std::sync::mpsc::channel();
    for producer in 0..8_u64 {
        let store = store.clone();
        let done_tx = done_tx.clone();
        std::thread::spawn(move || {
            for sequence in 0..64_u64 {
                let result = store.append_maintenance_history_value(
                    serde_json::json!({"event":"wakeup", "producer":producer, "sequence":sequence}),
                    &[77],
                );
                if result.is_err() {
                    break;
                }
            }
            done_tx.send(()).unwrap();
        });
    }
    drop(done_tx);
    for _ in 0..8 {
        done_rx
            .recv_timeout(std::time::Duration::from_secs(5))
            .expect("strict history producer lost a capacity wakeup");
    }
    let mut cursor = MaintenanceHistoryCursor::start();
    let mut total = 0;
    loop {
        let page = store.query_maintenance_history(77, cursor, 256).unwrap();
        total += page.records.len();
        match page.next_cursor {
            Some(next) => cursor = next,
            None => break,
        }
    }
    assert_eq!(total, 8 * 64);
    assert_eq!(store.diagnostics().history_queue_depth, 0);
    owner.settle().unwrap();
}

#[test]
fn history_record_cannot_override_scope_provenance() {
    let directory = support::TestDir::new("history_scope_collision");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path()).maintenance_history(true, true),
    )
    .unwrap();

    store
        .append_maintenance_history_value(
            serde_json::json!({"event":"collision", "scope":["forged"]}),
            &[5],
        )
        .unwrap();
    let error = store
        .query_maintenance_history(5, MaintenanceHistoryCursor::start(), 1)
        .unwrap_err();
    assert_eq!(error.kind(), FailureKind::HistoryLogFailure);
    assert!(owner.settle().is_err());
}

#[test]
fn history_query_propagates_non_not_found_index_errors() {
    let directory = support::TestDir::new("history_index_error");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path()).maintenance_history(true, true),
    )
    .unwrap();
    let marker = store
        .publish(
            ArtifactKind::RuntimeTrace,
            b"marker".to_vec().into_boxed_slice(),
        )
        .unwrap();
    let run_root = store
        .resolve(marker)
        .unwrap()
        .path()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf();
    store
        .append_maintenance_history_value(serde_json::json!({"event":"indexed"}), &[99])
        .unwrap();
    store
        .query_maintenance_history(99, MaintenanceHistoryCursor::start(), 1)
        .unwrap();
    let index = run_root.join("history/by-clause/clause-00000000000000000099.idx");
    fs::remove_file(&index).unwrap();
    fs::create_dir(&index).unwrap();

    let error = store
        .query_maintenance_history(99, MaintenanceHistoryCursor::start(), 1)
        .unwrap_err();
    assert_eq!(error.kind(), FailureKind::HistoryLogFailure);
    fs::remove_dir(index).unwrap();
    owner.settle().unwrap();
}

#[test]
fn concurrent_history_queries_never_observe_index_before_record_body() {
    let directory = support::TestDir::new("history_query_visibility");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path())
            .maintenance_history(true, true)
            .maintenance_history_queue_capacity(4),
    )
    .unwrap();
    let writer_store = store.clone();
    let writer = std::thread::spawn(move || {
        for sequence in 0..256_u64 {
            writer_store
                .append_maintenance_history_value(
                    serde_json::json!({"event":"visibility", "sequence":sequence}),
                    &[61],
                )
                .unwrap();
        }
    });

    while !writer.is_finished() {
        let page = store
            .query_maintenance_history(61, MaintenanceHistoryCursor::start(), 256)
            .unwrap();
        for record in page.records {
            assert_eq!(record["event"], "visibility");
            assert!(record["sequence"].is_u64());
        }
    }
    writer.join().unwrap();
    let page = store
        .query_maintenance_history(61, MaintenanceHistoryCursor::start(), 256)
        .unwrap();
    assert_eq!(page.records.len(), 256);
    owner.settle().unwrap();
}

#[test]
fn history_query_stops_before_an_indexed_body_outside_the_stable_prefix() {
    let directory = support::TestDir::new("history_query_stable_prefix");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path()).maintenance_history(true, true),
    )
    .unwrap();
    let marker = store
        .publish(
            ArtifactKind::RuntimeTrace,
            b"marker".to_vec().into_boxed_slice(),
        )
        .unwrap();
    let run_root = store
        .resolve(marker)
        .unwrap()
        .path()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf();
    store
        .append_maintenance_history_value(serde_json::json!({"event":"stable"}), &[83])
        .unwrap();
    let stable = store
        .query_maintenance_history(83, MaintenanceHistoryCursor::start(), 8)
        .unwrap();
    assert_eq!(stable.records.len(), 1);

    let main_len = fs::metadata(run_root.join("history/maintenance.jsonl"))
        .unwrap()
        .len();
    let mut index = fs::OpenOptions::new()
        .append(true)
        .open(run_root.join("history/by-clause/clause-00000000000000000083.idx"))
        .unwrap();
    writeln!(index, "{main_len} 128").unwrap();
    drop(index);

    let page = store
        .query_maintenance_history(83, MaintenanceHistoryCursor::start(), 8)
        .unwrap();
    assert_eq!(page.records.len(), 1);
    assert!(page.next_cursor.is_some());
    owner.settle().unwrap();
}
