mod support;

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use whiel_runner::{
    ArtifactKind, ArtifactStoreConfig, TimedChildOutcome, new_artifact_store, run_timed_child,
};

#[test]
fn timeout_joins_child_before_settlement() {
    let directory = support::TestDir::new("timeout_join");
    let task = support::sample_task();
    let (owner, store) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let observer = store.clone();
    let stopped = Arc::new(AtomicBool::new(false));
    let stopped_in_child = Arc::clone(&stopped);
    let published = Arc::new(Mutex::new(None));
    let published_in_child = Arc::clone(&published);

    let run = run_timed_child(
        owner,
        Duration::from_millis(20),
        move |cancellation, artifacts| {
            cancellation.wait_cancelled();
            let reference = artifacts
                .publish(
                    ArtifactKind::RuntimeTrace,
                    b"cleanup-complete".to_vec().into_boxed_slice(),
                )
                .unwrap();
            *published_in_child.lock().unwrap() = Some(reference);
            stopped_in_child.store(true, Ordering::Release);
        },
    );

    assert!(matches!(run.outcome, TimedChildOutcome::TimedOut));
    assert!(run.settlement.is_ok());
    assert!(stopped.load(Ordering::Acquire));
    let reference = published.lock().unwrap().expect("child published cleanup");
    assert!(observer.resolve(reference).is_ok());
    assert!(observer.diagnostics().settled);
    assert!(
        observer
            .publish(
                ArtifactKind::RuntimeTrace,
                b"too-late".to_vec().into_boxed_slice(),
            )
            .is_err()
    );
}

#[test]
fn completion_and_panic_both_settle_after_join() {
    let directory = support::TestDir::new("completion_panic");
    let task = support::sample_task();
    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("complete")),
    )
    .unwrap();
    let observer = store.clone();
    let completed = run_timed_child(
        owner,
        Duration::from_secs(1),
        |_cancellation, _artifacts| 17_u64,
    );
    assert!(matches!(
        completed.outcome,
        TimedChildOutcome::Completed(17)
    ));
    assert!(completed.settlement.is_ok());
    assert!(observer.diagnostics().settled);

    let (owner, store) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(directory.path().join("panic")),
    )
    .unwrap();
    let observer = store.clone();
    let panicked = run_timed_child(
        owner,
        Duration::from_secs(1),
        |_cancellation, _artifacts| -> () { panic!("intentional child panic") },
    );
    match panicked.outcome {
        TimedChildOutcome::Panicked(report) => {
            assert!(report.detail().contains("intentional child panic"));
        }
        other => panic!("expected panic outcome, got {other:?}"),
    }
    assert!(panicked.settlement.is_ok());
    assert!(observer.diagnostics().settled);
}

#[test]
fn timeout_remains_authoritative_when_cleanup_panics() {
    let directory = support::TestDir::new("timeout_cleanup_panic");
    let task = support::sample_task();
    let (owner, store) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();

    let run = run_timed_child(
        owner,
        Duration::from_millis(20),
        |cancellation, _artifacts| {
            cancellation.wait_cancelled();
            panic!("cleanup panic after timeout");
        },
    );

    assert!(matches!(run.outcome, TimedChildOutcome::TimedOut));
    assert!(run.settlement.is_ok());
    assert!(store.diagnostics().settled);
}
