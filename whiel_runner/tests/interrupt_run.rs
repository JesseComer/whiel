mod support;

use std::ffi::OsString;
use std::fs;
use std::thread;
use std::time::{Duration, Instant};

use whiel_runner::encoding::{EncodingWorkerCommand, EncodingWorkerPoolConfig};
use whiel_runner::runtime::interrupt;
use whiel_runner::{
    CertificationBridgeCommand, CertificationRuntime, FailureKind, RuntimeResourcePolicy,
    SymbolicHoudiniPolicy, SymbolicHoudiniRuntime, SynthesisResult, VampireWorkerCommand,
    VerificationParameters, symbolic_houdini,
};

/*
  The interrupt flag is process-global, so this end-to-end test owns a
  dedicated test binary: a simulated interrupt here can never leak into
  another integration run.
*/

/// An operator interrupt behaves as an externally imposed earlier
/// deadline: both lanes cancel, the owned worker tree is reaped, the
/// manifest settles, and the result is a typed run-global interrupt
/// failure — well before the configured overall limit.
#[cfg(unix)]
#[test]
fn interrupt_cancels_lanes_and_settles_artifacts() {
    interrupt::clear();
    let task = support::export_canonical_task();
    let directory = support::TestDir::new("interrupt_run_cleanup");
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

    let trigger = thread::spawn(|| {
        thread::sleep(Duration::from_millis(1500));
        interrupt::simulate(libc::SIGINT);
    });
    let started = Instant::now();
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
    trigger.join().expect("interrupt trigger thread");
    interrupt::clear();

    let SynthesisResult::Failure(report) = result else {
        panic!("an interrupt must make no logical claim")
    };
    assert_eq!(report.kind(), FailureKind::Interrupted);
    assert!(!report.retryable());
    assert!(
        elapsed < Duration::from_secs(60),
        "interrupt did not preempt the 120s overall limit: {elapsed:?}"
    );

    let run_roots = fs::read_dir(&artifact_root)
        .expect("artifact root")
        .map(|entry| entry.expect("artifact run entry").path())
        .collect::<Vec<_>>();
    assert_eq!(run_roots.len(), 1);
    assert!(run_roots[0].join("manifest.json").is_file());
    assert!(!run_roots[0].join("manifest.json.part").exists());

    let worker_pid = read_pid(
        &worker_marker,
        "the encoding worker must launch before the interrupt",
    );
    let child_pid = read_pid(
        &child_marker,
        "the encoding worker descendant must launch before the interrupt",
    );
    assert_process_gone(worker_pid);
    assert_process_gone(child_pid);
}

fn read_pid(path: &std::path::Path, message: &str) -> i32 {
    let text = fs::read_to_string(path).expect(message);
    text.trim().parse::<i32>().expect("pid file content")
}

fn assert_process_gone(pid: i32) {
    let deadline = Instant::now() + Duration::from_secs(10);
    loop {
        let alive = unsafe { libc::kill(pid, 0) } == 0;
        if !alive {
            return;
        }
        assert!(Instant::now() < deadline, "process {pid} survived cleanup");
        thread::sleep(Duration::from_millis(20));
    }
}
