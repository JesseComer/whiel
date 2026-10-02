//! Subprocess and deadline regressions for proof candidate selection.

use super::*;

#[cfg(unix)]
fn fake_cadical(root: &Path, body: &str) -> PathBuf {
    use std::os::unix::fs::PermissionsExt;
    let executable = root.join("fake-cadical");
    std::fs::write(&executable, format!("#!/bin/sh\n{body}\n")).unwrap();
    std::fs::set_permissions(&executable, std::fs::Permissions::from_mode(0o700)).unwrap();
    executable
}

#[cfg(unix)]
#[tokio::test]
async fn managed_sat_overlaps_and_keeps_each_invocations_own_files() {
    let root = OwnedDirectory::fresh(&std::env::temp_dir(), "whiel-sat-files").unwrap();
    let executable = fake_cadical(
        root.path(),
        concat!(
            "[ \"$3\" = '--fixture' ] || exit 2\n",
            "[ \"$LANG\" = C ] && [ \"$LC_ALL\" = C ] || exit 3\n",
            "cnf=$1; proof=$2; touch started\n",
            "attempt=0\n",
            "while [ \"$(find .. -name started -type f | wc -l)\" -lt 2 ]; do\n",
            "  attempt=$((attempt + 1)); [ $attempt -lt 100 ] || exit 4\n",
            "  sleep 0.01\n",
            "done\n",
            "cat \"$cnf\" > \"$proof\"\nexit 20"
        ),
    );
    let cancellation = CancellationToken::new();
    let arguments = vec!["--fixture".into()];
    let root_path = root.path().join("attempts");
    let (first, second) = tokio::join!(
        solve_cnf_with_cadical(
            &executable,
            &arguments,
            &root_path,
            "same-step",
            "first",
            Duration::from_secs(3),
            &cancellation
        ),
        solve_cnf_with_cadical(
            &executable,
            &arguments,
            &root_path,
            "same-step",
            "second",
            Duration::from_secs(3),
            &cancellation
        ),
    );
    assert_eq!(first.unwrap(), "first");
    assert_eq!(second.unwrap(), "second");
    assert_eq!(std::fs::read_dir(root_path).unwrap().count(), 2);
}

#[cfg(unix)]
#[tokio::test]
async fn managed_sat_rejects_sat_and_missing_trace() {
    let root = OwnedDirectory::fresh(&std::env::temp_dir(), "whiel-sat-reject").unwrap();
    let cancellation = CancellationToken::new();
    for (body, expected) in [
        ("echo trace > \"$2\"; exit 10", "SAT; no refutation"),
        ("exit 20", "LRAT"),
    ] {
        let executable = fake_cadical(root.path(), body);
        let error = solve_cnf_with_cadical(
            &executable,
            &[],
            root.path(),
            "reject",
            "p cnf 0 0\n",
            Duration::from_secs(2),
            &cancellation,
        )
        .await
        .unwrap_err();
        assert!(error.to_string().contains(expected), "{error}");
    }
}

#[cfg(unix)]
async fn managed_sat_stop_joins_tree(cancel: bool, leader_exits: bool) {
    let root = OwnedDirectory::fresh(&std::env::temp_dir(), "whiel-sat-stop").unwrap();
    let executable = fake_cadical(
        root.path(),
        &format!(
            "sleep 30 &\necho $! > \"$(dirname \"$2\")/child.pid\"\n{}",
            if leader_exits {
                "sleep 0.1; exit 2"
            } else {
                "wait"
            }
        ),
    );
    let attempts = root.path().join("attempts");
    let observed = attempts.clone();
    let cancellation = CancellationToken::new();
    let token = cancellation.clone();
    let observer = tokio::spawn(async move {
        for _ in 0..300 {
            if let Ok(entries) = std::fs::read_dir(&observed) {
                for entry in entries.flatten() {
                    if let Ok(text) = std::fs::read_to_string(entry.path().join("child.pid")) {
                        // The producer may have created but not yet written it.
                        let Ok(pid) = text.trim().parse::<u32>() else {
                            continue;
                        };
                        let registry =
                            crate::runtime::process_tree::ProcessRegistry::new(std::process::id())
                                .unwrap();
                        if cancel {
                            token.cancel();
                        }
                        return (pid, registry);
                    }
                }
            }
            tokio::time::sleep(Duration::from_millis(5)).await;
        }
        panic!("SAT fixture never launched");
    });
    let error = solve_cnf_with_cadical(
        &executable,
        &[],
        &attempts,
        "stop",
        "p cnf 0 0\n",
        Duration::from_millis(300),
        &cancellation,
    )
    .await
    .unwrap_err();
    if cancel {
        assert!(matches!(error, CertificateBuildError::Cancelled));
    } else if !leader_exits {
        assert!(error.to_string().contains("solver limit"), "{error}");
        assert!(!cancellation.is_cancelled());
    } else {
        assert!(error.to_string().contains("exited with Some(2)"), "{error}");
    }
    let (pid, registry) = observer.await.unwrap();
    assert!(
        !registry
            .live_matching_descendants()
            .iter()
            .any(|child| child.identity.pid == pid)
    );
}

#[cfg(unix)]
#[tokio::test]
async fn managed_sat_timeout_joins_children_on_current_thread_runtime() {
    managed_sat_stop_joins_tree(false, false).await;
}

#[cfg(unix)]
#[tokio::test]
async fn managed_sat_cancellation_joins_children_on_current_thread_runtime() {
    managed_sat_stop_joins_tree(true, false).await;
}

#[cfg(unix)]
#[tokio::test]
async fn managed_sat_failed_leader_joins_children_and_inherited_pipes() {
    managed_sat_stop_joins_tree(false, true).await;
}

#[test]
fn certificate_job_settings_are_explicit_positive_and_default_to_request() {
    let two = NonZeroUsize::new(2).unwrap();
    assert_eq!(
        resolve_solver_jobs(Err(std::env::VarError::NotPresent), two).unwrap(),
        two
    );
    assert_eq!(resolve_solver_jobs(Ok("3".into()), two).unwrap().get(), 3);
    for invalid in [
        "0",
        "",
        "-1",
        "1.5",
        "two",
        "999999999999999999999999999999",
    ] {
        assert!(
            resolve_solver_jobs(Ok(invalid.into()), two).is_err(),
            "{invalid}"
        );
    }
}

#[tokio::test]
async fn certificate_jobs_with_one_permit_remain_fail_fast() {
    use std::sync::atomic::{AtomicUsize, Ordering};
    let entered = Arc::new(AtomicUsize::new(0));
    let futures = (0..4).map(|_| {
        let entered = Arc::clone(&entered);
        async move {
            entered.fetch_add(1, Ordering::SeqCst);
            Err::<(), _>(CertificateBuildError::Io("failure".into()))
        }
    });
    assert!(
        run_certificate_jobs(
            futures,
            NonZeroUsize::new(1).unwrap(),
            &CancellationToken::new()
        )
        .await
        .is_err()
    );
    assert_eq!(entered.load(Ordering::SeqCst), 1);
}

#[tokio::test]
async fn certificate_jobs_overlap_within_bound_and_keep_bundle_order() {
    use std::sync::atomic::{AtomicUsize, Ordering};
    let active = Arc::new(AtomicUsize::new(0));
    let peak = Arc::new(AtomicUsize::new(0));
    let barrier = Arc::new(tokio::sync::Barrier::new(2));
    let futures = (0..6).map(|index| {
        let active = Arc::clone(&active);
        let peak = Arc::clone(&peak);
        let barrier = Arc::clone(&barrier);
        async move {
            let current = active.fetch_add(1, Ordering::SeqCst) + 1;
            peak.fetch_max(current, Ordering::SeqCst);
            assert!(current <= 2);
            barrier.wait().await;
            if index % 2 == 0 {
                tokio::time::sleep(Duration::from_millis(10)).await;
            }
            active.fetch_sub(1, Ordering::SeqCst);
            Ok(index)
        }
    });
    let result = tokio::time::timeout(
        Duration::from_secs(3),
        run_certificate_jobs(
            futures,
            NonZeroUsize::new(2).unwrap(),
            &CancellationToken::new(),
        ),
    )
    .await
    .unwrap()
    .unwrap();
    assert_eq!(result, (0..6).collect::<Vec<_>>());
    assert_eq!(peak.load(Ordering::SeqCst), 2);
    assert_eq!(active.load(Ordering::SeqCst), 0);
}

#[tokio::test]
async fn certificate_jobs_join_failures_and_choose_lowest_bundle_index() {
    use std::sync::atomic::{AtomicUsize, Ordering};
    let completed = Arc::new(AtomicUsize::new(0));
    let futures = (0..4).map(|index| {
        let completed = Arc::clone(&completed);
        async move {
            tokio::time::sleep(Duration::from_millis((4 - index) * 2)).await;
            completed.fetch_add(1, Ordering::SeqCst);
            Err::<(), _>(CertificateBuildError::Io(format!("failure {index}")))
        }
    });
    let error = run_certificate_jobs(
        futures,
        NonZeroUsize::new(2).unwrap(),
        &CancellationToken::new(),
    )
    .await
    .unwrap_err();
    assert!(matches!(error, CertificateBuildError::Io(message) if message == "failure 0"));
    assert_eq!(completed.load(Ordering::SeqCst), 4);
}

#[tokio::test]
async fn certificate_job_cancellation_joins_active_and_skips_queued_work() {
    use std::sync::atomic::{AtomicUsize, Ordering};
    let cancellation = CancellationToken::new();
    let started = Arc::new(AtomicUsize::new(0));
    let finished = Arc::new(AtomicUsize::new(0));
    let futures = (0..6).map(|_| {
        let cancellation = cancellation.clone();
        let started = Arc::clone(&started);
        let finished = Arc::clone(&finished);
        async move {
            if started.fetch_add(1, Ordering::SeqCst) == 1 {
                cancellation.cancel();
            }
            cancellation.cancelled().await;
            finished.fetch_add(1, Ordering::SeqCst);
            Err::<(), _>(CertificateBuildError::Cancelled)
        }
    });
    assert!(matches!(
        run_certificate_jobs(futures, NonZeroUsize::new(2).unwrap(), &cancellation).await,
        Err(CertificateBuildError::Cancelled)
    ));
    assert_eq!(started.load(Ordering::SeqCst), 2);
    assert_eq!(finished.load(Ordering::SeqCst), 2);
}

#[cfg(unix)]
#[tokio::test]
async fn compiler_cancellation_stops_grandchildren() {
    let directory = OwnedDirectory::fresh(&std::env::temp_dir(), "whiel-compiler-tree").unwrap();
    let marker = directory.path().join("child");
    let mut command = Command::new("/bin/sh");
    command
        .args(["-c", "sleep 30 & echo $! > \"$1\"; wait", "compiler"])
        .arg(&marker);
    let cancellation = CancellationToken::new();
    let cancel = cancellation.clone();
    let observed = marker.clone();
    let observer = tokio::spawn(async move {
        for _ in 0..500 {
            if observed.exists() {
                let pid: u32 = std::fs::read_to_string(&observed)
                    .unwrap()
                    .trim()
                    .parse()
                    .unwrap();
                let registry =
                    crate::runtime::process_tree::ProcessRegistry::new(std::process::id()).unwrap();
                cancel.cancel();
                return (pid, registry);
            }
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
        panic!("compiler grandchild did not start");
    });
    assert!(matches!(
        run_supervised(command, &cancellation).await,
        Err(CertificateBuildError::Cancelled)
    ));
    let (pid, registry) = observer.await.unwrap();
    assert!(
        !registry
            .live_matching_descendants()
            .iter()
            .any(|p| p.identity.pid == pid)
    );
}

// Run explicitly under the repository memory watchdog. This exercises real
// Lake rather than a mock which could hide search-path/cache mistakes.
#[tokio::test]
#[ignore = "live Lean build; requires watched execution"]
async fn lake_build_is_fresh_and_checks_unreachable_modules() {
    let root = OwnedDirectory::fresh(&std::env::temp_dir(), "whiel-lake-test").unwrap();
    let repo = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();
    let cancellation = CancellationToken::new();
    let lean = lake_env_which_lean(repo, &cancellation).await.unwrap();
    let base = lake_env_lean_path(repo, &cancellation).await.unwrap();
    let prefix = "Benchmark.Example0001.Certificate";
    let first = format!("{prefix}.First");
    let second = format!("{prefix}.Second");
    let independent = format!("{prefix}.Independent");
    let source = root.path().join("src");
    let output = root.path().join("olean");
    let relative = "Benchmark/Example0001/Certificate";
    write_staged(
        &source,
        &format!("{relative}/First.lean"),
        b"def certifiedValue : Nat := 42\n",
    )
    .await
    .unwrap();
    write_staged(
        &source,
        &format!("{relative}/Independent.lean"),
        b"def unrelatedValue : Nat := 7\n",
    )
    .await
    .unwrap();
    write_staged(
        &source,
        &format!("{relative}/Second.lean"),
        format!("import {first}\nexample : certifiedValue = 42 := rfl\n").as_bytes(),
    )
    .await
    .unwrap();
    let shadow = shadowed_lean_path(&base, &root.path().join("shadow"), "Example0001").unwrap();
    let path = format!("{}:{shadow}", output.display());
    compile_with_lake(
        &lean,
        &path,
        &source,
        &output,
        prefix,
        &[first.clone(), second.clone(), independent.clone()],
        &cancellation,
    )
    .await
    .unwrap();
    assert!(output.join(relative).join("Second.olean").is_file());
    let independent_output = output.join(relative).join("Independent.olean");
    let independent_modified = std::fs::metadata(&independent_output)
        .unwrap()
        .modified()
        .unwrap();

    // An unreachable staged module is still a required target.
    write_staged(
        &source,
        &format!("{relative}/Unused.lean"),
        b"example : False := by trivial\n",
    )
    .await
    .unwrap();
    assert!(
        compile_with_lake(
            &lean,
            &path,
            &source,
            &output,
            prefix,
            &[first.clone(), second.clone(), format!("{prefix}.Unused")],
            &cancellation
        )
        .await
        .is_err()
    );

    // A fresh workspace must not import a missing own module from the
    // successful first build, even if that build is a dependency path.
    let other = OwnedDirectory::fresh(&std::env::temp_dir(), "whiel-lake-fresh-test").unwrap();
    let other_source = other.path().join("src");
    let other_output = other.path().join("olean");
    write_staged(
        &other_source,
        &format!("{relative}/Second.lean"),
        format!("import {first}\nexample : certifiedValue = 42 := rfl\n").as_bytes(),
    )
    .await
    .unwrap();
    let shadow = shadowed_lean_path(&path, &other.path().join("shadow"), "Example0001").unwrap();
    let path = format!("{}:{shadow}", other_output.display());
    assert!(
        compile_with_lake(
            &lean,
            &path,
            &other_source,
            &other_output,
            prefix,
            std::slice::from_ref(&second),
            &cancellation
        )
        .await
        .is_err()
    );
    // A selected fallback changes source. Lake must invalidate a dependent
    // whose old proof no longer typechecks, even in the same build tree.
    write_staged(
        &source,
        &format!("{relative}/First.lean"),
        b"def certifiedValue : Nat := 43\n",
    )
    .await
    .unwrap();
    let path = format!("{}:{base}", output.display());
    assert!(
        compile_with_lake(
            &lean,
            &path,
            &source,
            &output,
            prefix,
            &[first, second, independent],
            &cancellation
        )
        .await
        .is_err()
    );
    assert_eq!(
        std::fs::metadata(independent_output)
            .unwrap()
            .modified()
            .unwrap(),
        independent_modified
    );
}

#[tokio::test]
async fn candidate_budget_covers_work_and_cleanup() {
    let local = CancellationToken::new();
    let cancellation = CancellationToken::new();
    let phase = std::sync::atomic::AtomicUsize::new(0);
    let work = async {
        // Preparation and native waiting share one candidate deadline.
        tokio::time::sleep(Duration::from_millis(100)).await;
        phase.store(1, std::sync::atomic::Ordering::SeqCst);
        tokio::select! {
            _ = local.cancelled() => Err(CertificateBuildError::Cancelled),
            _ = tokio::time::sleep(Duration::from_millis(450)) => Ok(()),
        }
    };
    let error = run_candidate_with_budget(
        work,
        &local,
        &cancellation,
        Duration::from_millis(500),
        "Candidate",
    )
    .await
    .unwrap_err();
    assert!(
        matches!(error, CertificateBuildError::Build { diagnostics, .. }
        if diagnostics.contains("budget"))
    );
    assert_eq!(phase.load(std::sync::atomic::Ordering::SeqCst), 1);
    assert!(local.is_cancelled());
    assert!(!cancellation.is_cancelled());
}

#[cfg(unix)]
async fn candidate_process_stops_and_is_reaped(cancel: bool) {
    let scratch = std::env::temp_dir().join(format!(
        "whiel-candidate-cleanup-{}-{}",
        std::process::id(),
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir_all(&scratch).unwrap();
    let pid_path = scratch.join("pid");
    let mut command = Command::new("/bin/sh");
    // exec preserves the PID: there is exactly one child to reap.
    command.args(["-c", "echo $$ > \"$1\"; exec sleep 30", "candidate"]);
    command.arg(&pid_path);
    let cancellation = CancellationToken::new();
    let canceller = cancellation.clone();
    let observed_path = pid_path.clone();
    let observer = tokio::spawn(async move {
        for _ in 0..500 {
            if observed_path.exists() {
                if cancel {
                    canceller.cancel();
                }
                return;
            }
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
        panic!("supervised candidate did not start");
    });
    let local = CancellationToken::new();
    let error = run_candidate_with_budget(
        run_supervised(command, &local),
        &local,
        &cancellation,
        Duration::from_secs(2),
        "Candidate",
    )
    .await
    .unwrap_err();
    observer.await.unwrap();
    if cancel {
        assert!(matches!(error, CertificateBuildError::Cancelled));
    } else {
        assert!(
            matches!(error, CertificateBuildError::Build { diagnostics, .. }
            if diagnostics.contains("budget"))
        );
    }
    let pid: i32 = std::fs::read_to_string(pid_path)
        .unwrap()
        .trim()
        .parse()
        .unwrap();
    // A reaped process is gone, not a still-running child or zombie.
    assert_eq!(unsafe { libc::kill(pid, 0) }, -1);
    assert_eq!(io::Error::last_os_error().raw_os_error(), Some(libc::ESRCH));
    std::fs::remove_dir_all(scratch).unwrap();
}

#[cfg(unix)]
#[tokio::test]
async fn candidate_timeout_reaps_the_child() {
    candidate_process_stops_and_is_reaped(false).await;
}

#[cfg(unix)]
#[tokio::test]
async fn candidate_cancellation_remains_cancellation_and_reaps_the_child() {
    candidate_process_stops_and_is_reaped(true).await;
}

#[tokio::test]
async fn cancellation_joins_a_capture_whose_pipe_is_still_open() {
    let (reader, _writer) = tokio::io::duplex(64);
    let task = tokio::spawn(read_to_end_capped(reader));
    let cancellation = CancellationToken::new();
    cancellation.cancel();
    assert!(matches!(
        join_supervised_capture(task, &cancellation, "stdout").await,
        Err(CertificateBuildError::Cancelled)
    ));
}
