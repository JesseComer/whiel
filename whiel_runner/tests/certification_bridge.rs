mod support;

use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use serde_json::json;
use whiel_runner::{
    CancellationToken, CertificationBridgeCommand, CertificationBridgeError, CertificationOutcome,
    CertifiedClassification, InvalidityCertificationLimits, ValidityCertificationLimits,
};

static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

struct RepositoryDirectory(PathBuf);

impl RepositoryDirectory {
    fn new(label: &str) -> Self {
        let sequence = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = support::repository_root().join(format!(
            "whiel_runner/target/certification-{label}-{}-{nanos}-{sequence}",
            std::process::id()
        ));
        fs::create_dir_all(&path).unwrap();
        // Canonicalize so path equality survives symlinked
        // build directories.
        let path = path.canonicalize().unwrap();
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

fn validity_limits(bridge: Option<Duration>) -> ValidityCertificationLimits {
    ValidityCertificationLimits {
        final_search: Some(Duration::from_secs(30)),
        lean: Some(Duration::from_secs(40)),
        max_heartbeats: 1_000_000,
        bridge,
    }
}

#[test]
fn validity_request_is_sorted_and_published_certificate_is_hash_checked() {
    let directory = RepositoryDirectory::new("valid");
    let solution = directory.path().join("solution");
    let outcome = command("success")
        .certify_valid(
            &support::sample_task(),
            ["clause-b", "clause-a"],
            directory.path().join("work"),
            &solution,
            validity_limits(Some(Duration::from_secs(5))),
            &CancellationToken::new(),
        )
        .unwrap();

    let CertificationOutcome::Certified(bundle) = outcome else {
        panic!("fixture success must certify");
    };
    assert_eq!(bundle.classification, CertifiedClassification::Valid);
    assert!(bundle.witness.is_none());
    assert_eq!(bundle.bundle, solution);
    assert_eq!(bundle.certificate, solution.join("Certificate.lean"));
    assert!(
        bundle
            .certificate_sha256
            .chars()
            .all(|value| value.is_ascii_hexdigit())
    );
}

#[test]
fn bridge_failure_is_typed_and_does_not_publish() {
    let directory = RepositoryDirectory::new("failed");
    let solution = directory.path().join("solution");
    let outcome = command("failed")
        .certify_valid(
            &support::sample_task(),
            ["clause"],
            directory.path().join("work"),
            &solution,
            validity_limits(Some(Duration::from_secs(5))),
            &CancellationToken::new(),
        )
        .unwrap();

    let CertificationOutcome::Failed(failure) = outcome else {
        panic!("fixture failure must remain non-certified");
    };
    assert_eq!(failure.kind, "certificate_rejected");
    assert!(!solution.exists());
}

#[test]
fn malformed_failure_publication_is_removed_before_return() {
    let directory = RepositoryDirectory::new("failed-publication");
    let solution = directory.path().join("solution");
    let result = command("failed_with_bundle").certify_valid(
        &support::sample_task(),
        ["clause"],
        directory.path().join("work"),
        &solution,
        validity_limits(Some(Duration::from_secs(5))),
        &CancellationToken::new(),
    );

    assert!(matches!(
        result,
        Err(CertificationBridgeError::MalformedResponse(_))
    ));
    assert!(!solution.exists());
}

#[test]
fn certified_response_with_owned_staging_left_behind_fails_closed() {
    let directory = RepositoryDirectory::new("leftover-staging");
    let solution = directory.path().join("solution");
    let result = command("leftover_stage").certify_valid(
        &support::sample_task(),
        ["clause"],
        directory.path().join("work"),
        &solution,
        validity_limits(Some(Duration::from_secs(5))),
        &CancellationToken::new(),
    );

    assert!(matches!(
        result,
        Err(CertificationBridgeError::MalformedResponse(_))
    ));
    assert!(!solution.exists());
    assert!(
        !fs::read_dir(directory.path())
            .unwrap()
            .filter_map(Result::ok)
            .any(|entry| entry.file_name().to_string_lossy().contains(".stage-"))
    );
}

#[test]
fn response_for_another_task_and_forged_digest_fail_closed() {
    for (label, mode) in [("identity", "mismatched_identity"), ("hash", "bad_hash")] {
        let directory = RepositoryDirectory::new(label);
        let result = command(mode).certify_valid(
            &support::sample_task(),
            ["clause"],
            directory.path().join("work"),
            directory.path().join("solution"),
            validity_limits(Some(Duration::from_secs(5))),
            &CancellationToken::new(),
        );
        assert!(matches!(
            result,
            Err(CertificationBridgeError::MalformedResponse(_))
        ));
    }
}

#[test]
fn invalidity_uses_the_same_typed_authority_boundary() {
    let directory = RepositoryDirectory::new("invalid");
    let solution = directory.path().join("solution");
    let outcome = command("success")
        .certify_invalid(
            &support::sample_task(),
            json!({"R": []}),
            100,
            directory.path().join("work"),
            &solution,
            InvalidityCertificationLimits {
                runtime: Duration::from_secs(30),
                lean: Some(Duration::from_secs(40)),
                max_heartbeats: 1_000_000,
                bridge: Some(Duration::from_secs(5)),
            },
            &CancellationToken::new(),
        )
        .unwrap();
    let CertificationOutcome::Certified(bundle) = outcome else {
        panic!("invalidity fixture must certify");
    };
    assert_eq!(bundle.classification, CertifiedClassification::Invalid);
    let witness = bundle
        .witness
        .expect("invalid certification retains Witness");
    assert!(witness.path.is_file());
    assert_eq!(witness.sha256.len(), 64);
}

#[test]
fn invalidity_rejects_missing_forged_or_mismatched_witness_artifacts() {
    for mode in ["missing_witness", "bad_witness_hash", "wrong_witness_input"] {
        let directory = RepositoryDirectory::new(mode);
        let solution = directory.path().join("solution");
        let result = command(mode).certify_invalid(
            &support::sample_task(),
            json!({"R": []}),
            100,
            directory.path().join("work"),
            &solution,
            InvalidityCertificationLimits {
                runtime: Duration::from_secs(30),
                lean: Some(Duration::from_secs(40)),
                max_heartbeats: 1_000_000,
                bridge: Some(Duration::from_secs(5)),
            },
            &CancellationToken::new(),
        );
        assert!(matches!(
            result,
            Err(CertificationBridgeError::MalformedResponse(_))
        ));
        assert!(!solution.exists());
    }
}

#[test]
fn outer_timeout_stops_the_one_shot_bridge() {
    let directory = RepositoryDirectory::new("timeout");
    let result = command("sleep").certify_valid(
        &support::sample_task(),
        ["clause"],
        directory.path().join("work"),
        directory.path().join("solution"),
        validity_limits(Some(Duration::from_millis(25))),
        &CancellationToken::new(),
    );
    assert_eq!(result.unwrap_err(), CertificationBridgeError::TimedOut);
}

#[test]
fn no_final_specific_limit_is_transported_as_none() {
    let directory = RepositoryDirectory::new("no-final-limit");
    let outcome = command("expect_no_limits")
        .certify_valid(
            &support::sample_task(),
            ["clause"],
            directory.path().join("work"),
            directory.path().join("solution"),
            ValidityCertificationLimits {
                final_search: None,
                lean: None,
                max_heartbeats: 1_000_000,
                bridge: Some(Duration::from_secs(5)),
            },
            &CancellationToken::new(),
        )
        .unwrap();
    assert!(matches!(outcome, CertificationOutcome::Certified(_)));
}

#[test]
fn invalidity_rejection_is_distinct_from_failure() {
    let directory = RepositoryDirectory::new("rejected");
    let outcome = command("rejected")
        .certify_invalid(
            &support::sample_task(),
            json!({"R": []}),
            100,
            directory.path().join("work"),
            directory.path().join("solution"),
            InvalidityCertificationLimits {
                runtime: Duration::from_secs(30),
                lean: None,
                max_heartbeats: 1_000_000,
                bridge: Some(Duration::from_secs(5)),
            },
            &CancellationToken::new(),
        )
        .unwrap();
    let CertificationOutcome::Rejected(rejection) = outcome else {
        panic!("complete negative source check must be Rejected");
    };
    assert_eq!(rejection.kind, "postTrue");
}

#[test]
fn malformed_failure_metadata_fails_closed() {
    let directory = RepositoryDirectory::new("malformed-metadata");
    let result = command("malformed_failure_metadata").certify_valid(
        &support::sample_task(),
        ["clause"],
        directory.path().join("work"),
        directory.path().join("solution"),
        validity_limits(Some(Duration::from_secs(5))),
        &CancellationToken::new(),
    );
    assert!(matches!(
        result,
        Err(CertificationBridgeError::MalformedResponse(_))
    ));
}

#[test]
fn certificate_and_witness_symlinks_fail_closed() {
    for mode in ["symlink_certificate", "symlink_bundle"] {
        let directory = RepositoryDirectory::new(mode);
        let result = command(mode).certify_valid(
            &support::sample_task(),
            ["clause"],
            directory.path().join("work"),
            directory.path().join("solution"),
            validity_limits(Some(Duration::from_secs(5))),
            &CancellationToken::new(),
        );
        assert!(matches!(
            result,
            Err(CertificationBridgeError::MalformedResponse(_))
        ));
    }
    for mode in ["symlink_witness", "wrong_witness_name"] {
        let directory = RepositoryDirectory::new(mode);
        let result = command(mode).certify_invalid(
            &support::sample_task(),
            json!({"R": []}),
            100,
            directory.path().join("work"),
            directory.path().join("solution"),
            InvalidityCertificationLimits {
                runtime: Duration::from_secs(30),
                lean: Some(Duration::from_secs(40)),
                max_heartbeats: 1_000_000,
                bridge: Some(Duration::from_secs(5)),
            },
            &CancellationToken::new(),
        );
        assert!(matches!(
            result,
            Err(CertificationBridgeError::MalformedResponse(_))
        ));
    }
}

#[test]
fn blocking_stdin_transport_obeys_the_outer_timeout() {
    let directory = RepositoryDirectory::new("blocked-stdin");
    let large_clause = "x".repeat(8 * 1024 * 1024);
    let started = Instant::now();
    let result = command("stall_before_stdin").certify_valid(
        &support::sample_task(),
        [large_clause],
        directory.path().join("work"),
        directory.path().join("solution"),
        validity_limits(Some(Duration::from_millis(50))),
        &CancellationToken::new(),
    );
    assert_eq!(result.unwrap_err(), CertificationBridgeError::TimedOut);
    assert!(started.elapsed() < Duration::from_secs(3));
}

#[test]
fn blocking_stdin_transport_obeys_cancellation() {
    let directory = RepositoryDirectory::new("cancelled-stdin");
    let large_clause = "x".repeat(8 * 1024 * 1024);
    let cancellation = CancellationToken::new();
    let canceller = cancellation.clone();
    let cancellation_thread = thread::spawn(move || {
        thread::sleep(Duration::from_millis(50));
        canceller.cancel();
    });
    let started = Instant::now();
    let result = command("stall_before_stdin").certify_valid(
        &support::sample_task(),
        [large_clause],
        directory.path().join("work"),
        directory.path().join("solution"),
        validity_limits(None),
        &cancellation,
    );
    cancellation_thread.join().unwrap();
    assert_eq!(result.unwrap_err(), CertificationBridgeError::Cancelled);
    assert!(started.elapsed() < Duration::from_secs(3));
}

#[test]
fn output_lease_rejects_a_concurrent_owner_and_preserves_foreign_staging() {
    let directory = RepositoryDirectory::new("output-lease");
    let first_root = directory.path().to_path_buf();
    let first = thread::spawn(move || {
        command("hold_output_lease").certify_valid(
            &support::sample_task(),
            ["clause"],
            first_root.join("work"),
            first_root.join("solution"),
            validity_limits(Some(Duration::from_millis(500))),
            &CancellationToken::new(),
        )
    });
    let marker = directory.path().join("work/lease-held");
    let deadline = Instant::now() + Duration::from_secs(2);
    while !marker.exists() && Instant::now() < deadline {
        thread::sleep(Duration::from_millis(5));
    }
    assert!(
        marker.exists(),
        "first bridge did not acquire its output lease"
    );
    let second = command("success").certify_valid(
        &support::sample_task(),
        ["clause"],
        directory.path().join("other-work"),
        directory.path().join("solution"),
        validity_limits(Some(Duration::from_secs(5))),
        &CancellationToken::new(),
    );
    assert!(matches!(
        second,
        Err(CertificationBridgeError::InvalidRequest(_))
    ));
    assert_eq!(
        first.join().unwrap().unwrap_err(),
        CertificationBridgeError::TimedOut
    );

    let foreign_root = RepositoryDirectory::new("foreign-stage");
    let solution = foreign_root.path().join("solution");
    let outcome = command("foreign_stage")
        .certify_valid(
            &support::sample_task(),
            ["clause"],
            foreign_root.path().join("work"),
            &solution,
            validity_limits(Some(Duration::from_secs(5))),
            &CancellationToken::new(),
        )
        .unwrap();
    assert!(matches!(outcome, CertificationOutcome::Failed(_)));
    assert!(PathBuf::from(format!("{}.stage-{}", solution.display(), "f".repeat(64))).exists());
}

#[cfg(unix)]
#[test]
fn outer_timeout_kills_a_nested_child_in_the_owned_process_group() {
    let directory = RepositoryDirectory::new("nested-child");
    let pid_file = directory.path().join("work/nested-child.pid");
    let result = command("nested_child").certify_valid(
        &support::sample_task(),
        ["clause"],
        directory.path().join("work"),
        directory.path().join("solution"),
        validity_limits(Some(Duration::from_millis(150))),
        &CancellationToken::new(),
    );
    assert_eq!(result.unwrap_err(), CertificationBridgeError::TimedOut);
    let pid: i32 = fs::read_to_string(pid_file).unwrap().parse().unwrap();
    let deadline = Instant::now() + Duration::from_secs(2);
    loop {
        let alive = unsafe { libc::kill(pid, 0) } == 0;
        if !alive {
            break;
        }
        assert!(
            Instant::now() < deadline,
            "nested child survived timeout cleanup"
        );
        thread::sleep(Duration::from_millis(10));
    }
}
