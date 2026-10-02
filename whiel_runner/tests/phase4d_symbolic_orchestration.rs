mod support;

use std::ffi::OsString;
use std::fs;
use std::time::Duration;

use whiel_runner::encoding::{EncodingWorkerCommand, EncodingWorkerPoolConfig};
use whiel_runner::{
    CertificationBridgeCommand, CertificationRuntime, FailureKind, RuntimeResourcePolicy,
    SymbolicHoudiniPolicy, SymbolicHoudiniRuntime, SynthesisResult, VampireWorkerCommand,
    VerificationParameters, symbolic_houdini,
};

/// The synchronous entry owns the artifact authority outside its lane deadline
/// and does not return until a launched Lean worker tree is gone and the
/// manifest is settled.
#[cfg(unix)]
#[test]
fn overall_timeout_joins_runtime_work_before_artifact_settlement() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("phase4d_symbolic_timeout_cleanup");
    let artifact_root = directory.path().join("artifacts");
    let worker_marker = directory.path().join("encoding-worker.pid");
    let child_marker = directory.path().join("encoding-worker-child.pid");
    let repository = support::repository_root();
    let encoding_workers = EncodingWorkerPoolConfig::new(
        EncodingWorkerCommand::new(support::stalling_encoding_worker(), &repository).arguments([
            worker_marker.clone().into_os_string(),
            child_marker.clone().into_os_string(),
        ]),
        2,
    )
    .expect("positive worker count");
    let vampire = VampireWorkerCommand::new(support::fake_vampire())
        .with_extra_args([
            OsString::from("--fixture"),
            OsString::from("race-proof-fast"),
            OsString::from("--expect-start"),
            OsString::from("1"),
        ])
        .expect("valid fake Vampire command");
    let certification = CertificationRuntime::new(
        CertificationBridgeCommand::new("python3", &repository).with_arguments([
            repository
                .join("whiel_runner/tests/fixtures/fake_certification_bridge.py")
                .into_os_string(),
            "success".into(),
        ]),
        directory.path().join("certification-work"),
        directory.path().join("solution"),
    );
    let runtime =
        SymbolicHoudiniRuntime::new(&artifact_root, encoding_workers, vampire, certification);
    let resources = RuntimeResourcePolicy::symbolic(4, 2, 2).expect("symbolic resources");
    let verification =
        VerificationParameters::new(Duration::from_secs(1), resources).expect("verification");

    let result = symbolic_houdini(
        &task,
        Duration::from_millis(500),
        verification,
        SymbolicHoudiniPolicy::default(),
        false,
        true,
        runtime,
    );
    let SynthesisResult::Failure(report) = result else {
        panic!("the overall deadline must make no logical claim")
    };
    assert_eq!(report.kind(), FailureKind::OverallTimeout);
    let run_roots = fs::read_dir(&artifact_root)
        .expect("artifact root")
        .map(|entry| entry.expect("artifact run entry").path())
        .collect::<Vec<_>>();
    assert_eq!(run_roots.len(), 1);
    assert!(run_roots[0].join("manifest.json").is_file());
    assert!(!run_roots[0].join("manifest.json.part").exists());

    let worker_pid = read_pid(
        &worker_marker,
        "the encoding worker must launch before timeout",
    );
    let child_pid = read_pid(
        &child_marker,
        "the encoding worker descendant must launch before timeout",
    );
    assert_process_gone(worker_pid);
    assert_process_gone(child_pid);
}

/// The same entry boundary also retains Vampire proof/FMB cleanup after the
/// lane futures are cancelled. The manifest cannot freeze while either
/// blocking solver worker still owns its admitted process tree.
#[cfg(unix)]
#[test]
fn overall_timeout_reaps_live_vampire_pair_before_manifest_settlement() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("phase4d_symbolic_vampire_cleanup");
    let artifact_root = directory.path().join("artifacts");
    let proof_pid_path = directory.path().join("vampire-proof.pid");
    let fmb_pid_path = directory.path().join("vampire-fmb.pid");
    let repository = support::repository_root();
    let encoding_workers = EncodingWorkerPoolConfig::new(
        EncodingWorkerCommand::new(support::example_encoding_worker(), &repository),
        2,
    )
    .expect("positive worker count");
    let vampire = VampireWorkerCommand::new(support::fake_vampire())
        .with_extra_args([
            OsString::from("--fixture"),
            OsString::from("race-timeout"),
            OsString::from("--expect-start"),
            OsString::from("1"),
            OsString::from("--proof-pid"),
            proof_pid_path.clone().into_os_string(),
            OsString::from("--fmb-pid"),
            fmb_pid_path.clone().into_os_string(),
        ])
        .expect("valid fake Vampire command");
    let certification = CertificationRuntime::new(
        CertificationBridgeCommand::new("python3", &repository).with_arguments([
            repository
                .join("whiel_runner/tests/fixtures/fake_certification_bridge.py")
                .into_os_string(),
            "success".into(),
        ]),
        directory.path().join("certification-work"),
        directory.path().join("solution"),
    );
    let runtime =
        SymbolicHoudiniRuntime::new(&artifact_root, encoding_workers, vampire, certification);
    let resources = RuntimeResourcePolicy::symbolic(4, 2, 2).expect("symbolic resources");
    let verification =
        VerificationParameters::new(Duration::from_secs(30), resources).expect("verification");

    let result = symbolic_houdini(
        &task,
        Duration::from_secs(3),
        verification,
        SymbolicHoudiniPolicy::default(),
        false,
        true,
        runtime,
    );
    let SynthesisResult::Failure(report) = result else {
        panic!("the overall deadline must make no logical claim")
    };
    assert_eq!(report.kind(), FailureKind::OverallTimeout);

    let proof_pid = read_pid(&proof_pid_path, "a live proof worker must launch");
    let fmb_pid = read_pid(&fmb_pid_path, "a live FMB worker must launch");
    assert_ne!(proof_pid, fmb_pid);
    assert_process_gone(proof_pid);
    assert_process_gone(fmb_pid);

    let run_roots = fs::read_dir(&artifact_root)
        .expect("artifact root")
        .map(|entry| entry.expect("artifact run entry").path())
        .collect::<Vec<_>>();
    assert_eq!(run_roots.len(), 1);
    assert!(run_roots[0].join("manifest.json").is_file());
    assert!(!run_roots[0].join("manifest.json.part").exists());
}

#[cfg(unix)]
fn read_pid(path: &std::path::Path, message: &str) -> i32 {
    fs::read_to_string(path)
        .unwrap_or_else(|_| panic!("{message}"))
        .trim()
        .parse()
        .expect("PID marker must contain an integer")
}

#[cfg(unix)]
fn assert_process_gone(pid: i32) {
    for _ in 0..500 {
        if unsafe { libc::kill(pid, 0) } == -1 {
            return;
        }
        std::thread::sleep(Duration::from_millis(10));
    }
    panic!("process {pid} remained live after Symbolic-Houdini returned");
}

#[cfg(unix)]
struct CertificationScratch(std::path::PathBuf);

#[cfg(unix)]
impl CertificationScratch {
    fn new(label: &str) -> Self {
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = support::repository_root().join(format!(
            "whiel_runner/target/certification-{label}-{}-{nanos}",
            std::process::id()
        ));
        fs::create_dir_all(&path).unwrap();
        Self(path)
    }

    fn path(&self) -> &std::path::Path {
        &self.0
    }
}

#[cfg(unix)]
impl Drop for CertificationScratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[cfg(unix)]
fn find_file_under(root: &std::path::Path, name: &str) -> Option<std::path::PathBuf> {
    let entries = fs::read_dir(root).ok()?;
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            if let Some(found) = find_file_under(&path, name) {
                return Some(found);
            }
        } else if path.file_name().is_some_and(|file| file == name) {
            return Some(path);
        }
    }
    None
}

/// A deterministic certificate rejection ends the run as a typed terminal
/// failure. The INV lane must not dissolve the report into an inconclusive
/// outcome that leaves the CEX lane burning the remaining deadline, and the
/// non-retryable rejection must reach the certification authority exactly
/// once.
#[cfg(unix)]
#[test]
fn deterministic_certificate_rejection_is_a_terminal_typed_failure() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("phase4d_certification_rejection");
    let scratch = CertificationScratch::new("rejection");
    let artifact_root = directory.path().join("artifacts");
    let work_directory = scratch.path().join("certification-work");
    let repository = support::repository_root();
    let encoding_workers = EncodingWorkerPoolConfig::new(
        EncodingWorkerCommand::new(support::example_encoding_worker(), &repository),
        2,
    )
    .expect("positive worker count");
    let vampire = VampireWorkerCommand::new(support::fake_vampire())
        .with_extra_args([
            OsString::from("--fixture"),
            OsString::from("race-proof-fast"),
            OsString::from("--expect-start"),
            OsString::from("1"),
        ])
        .expect("valid fake Vampire command");
    let certification = CertificationRuntime::new(
        CertificationBridgeCommand::new("python3", &repository).with_arguments([
            repository
                .join("whiel_runner/tests/fixtures/fake_certification_bridge.py")
                .into_os_string(),
            "failed".into(),
        ]),
        work_directory.clone(),
        scratch.path().join("solution"),
    );
    let runtime =
        SymbolicHoudiniRuntime::new(&artifact_root, encoding_workers, vampire, certification);
    let resources = RuntimeResourcePolicy::symbolic(4, 2, 2).expect("symbolic resources");
    let verification =
        VerificationParameters::new(Duration::from_secs(5), resources).expect("verification");

    let started = std::time::Instant::now();
    let result = symbolic_houdini(
        &task,
        Duration::from_secs(120),
        verification,
        SymbolicHoudiniPolicy::default(),
        false,
        true,
        runtime,
    );
    let elapsed = started.elapsed();
    let SynthesisResult::Failure(report) = result else {
        panic!("a rejected certificate must be a terminal failure, got {result:?}")
    };
    assert_eq!(
        report.kind(),
        FailureKind::CertificateRejected,
        "unexpected failure report: {report:?}"
    );
    // A burned deadline shows as the full 120 seconds. The bound sits well
    // below that and well above what a loaded machine needs to reach the
    // rejection, so it separates the two without timing the machine.
    assert!(
        elapsed < Duration::from_secs(100),
        "certification rejection must not burn the overall deadline; took {elapsed:?}"
    );
    let invocations = find_file_under(scratch.path(), "fixture-failed-invocations.log")
        .and_then(|path| fs::read_to_string(path).ok())
        .expect("the certification authority must be consulted");
    assert_eq!(
        invocations.lines().count(),
        1,
        "a deterministic rejection must not be repeated"
    );
}

/// A transient certification failure earns exactly one same-core retry, and
/// a successful retry still publishes the valid result.
#[cfg(unix)]
#[test]
fn transient_certification_failure_retries_once_then_certifies() {
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("phase4d_certification_retry");
    let scratch = CertificationScratch::new("retry");
    let artifact_root = directory.path().join("artifacts");
    let work_directory = scratch.path().join("certification-work");
    let repository = support::repository_root();
    let encoding_workers = EncodingWorkerPoolConfig::new(
        EncodingWorkerCommand::new(support::example_encoding_worker(), &repository),
        2,
    )
    .expect("positive worker count");
    let vampire = VampireWorkerCommand::new(support::fake_vampire())
        .with_extra_args([
            OsString::from("--fixture"),
            OsString::from("race-proof-fast"),
            OsString::from("--expect-start"),
            OsString::from("1"),
        ])
        .expect("valid fake Vampire command");
    let certification = CertificationRuntime::new(
        CertificationBridgeCommand::new("python3", &repository).with_arguments([
            repository
                .join("whiel_runner/tests/fixtures/fake_certification_bridge.py")
                .into_os_string(),
            "transient_then_success".into(),
        ]),
        work_directory.clone(),
        scratch.path().join("solution"),
    );
    let runtime =
        SymbolicHoudiniRuntime::new(&artifact_root, encoding_workers, vampire, certification);
    let resources = RuntimeResourcePolicy::symbolic(4, 2, 2).expect("symbolic resources");
    let verification =
        VerificationParameters::new(Duration::from_secs(5), resources).expect("verification");

    let result = symbolic_houdini(
        &task,
        Duration::from_secs(120),
        verification,
        SymbolicHoudiniPolicy::default(),
        false,
        true,
        runtime,
    );
    let SynthesisResult::Valid(_) = result else {
        panic!("a transient failure must earn one retry and certify, got {result:?}")
    };
    assert!(
        find_file_under(scratch.path(), "fixture-retry-observed").is_some(),
        "the first transient attempt must reach the authority"
    );
}
