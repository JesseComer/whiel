//! Generic CLI selection/records: no C installation or native agent. Only the
//! final interruption and retention modules run a real campaign, each with a
//! Lean worker child.

mod support;

use whiel_runner::campaign_cli::{
    CampaignProvider, CampaignRunConfig, parse_campaign_run_arguments,
};
use whiel_runner::cli::{CliAction, parse_cli_args};

fn parse(arguments: &[&str]) -> Result<CampaignRunConfig, String> {
    parse_campaign_run_arguments(
        &arguments
            .iter()
            .map(|value| (*value).to_owned())
            .collect::<Vec<_>>(),
    )
}

#[test]
fn generic_selection_keeps_opaque_arguments_and_no_native_configuration() {
    let configuration = parse(&[
        "--input",
        "1",
        "--proposer-arg",
        "--endpoint",
        "--proposer-executable",
        "custom proposer",
        "--proposer-arg",
        "a b",
        "--proposer-arg=--help",
        "--proposer-arg",
        "",
        "--proposer-arg",
        "$(must-not-run);*",
        "--api-traffic-bytes",
        "3210",
        "--api-messages",
        "12",
    ])
    .unwrap();
    assert_eq!(configuration.provider, CampaignProvider::Generic);
    let selection = configuration.proposer.unwrap();
    assert_eq!(selection.executable.to_str(), Some("custom proposer"));
    assert_eq!(
        selection.arguments,
        ["--endpoint", "a b", "--help", "", "$(must-not-run);*"]
    );
    assert_eq!(configuration.resource_limits.api_traffic_bytes, 3210);
    assert_eq!(configuration.resource_limits.api_messages, 12);

    let configuration = parse(&["--all", "--no-proposer"]).unwrap();
    assert_eq!(configuration.provider, CampaignProvider::None);
    assert!(configuration.proposer.is_none());
}

#[test]
fn endpoint_selection_is_required_without_an_implicit_default() {
    for arguments in [
        vec!["--all"],
        vec!["--input", "1"],
        vec!["--all", "--api-messages", "5"],
    ] {
        assert_eq!(
            parse(&arguments).unwrap_err(),
            "select --proposer-executable PATH or --no-proposer"
        );
    }
    for retired in [
        "--provider",
        "--model",
        "--reasoning-effort",
        "--claude-cli",
        "--bridge",
        "--isolation",
        "--provider-traffic-bytes",
        "--provider-messages",
        "--session-mode",
    ] {
        let error = parse(&["--all", retired, "private-value"]).unwrap_err();
        assert!(error.contains("unknown campaign option"));
        assert!(!error.contains("private-value"));
        assert!(!whiel_runner::campaign_cli::CAMPAIGN_USAGE.contains(retired));
    }
}

#[test]
fn help_inside_proposer_arguments_is_not_verifier_help() {
    for value in ["--help", "-h", "--proposer-arg", ""] {
        let action = parse_cli_args([
            "campaign",
            "run",
            "--all",
            "--proposer-executable",
            "endpoint",
            "--proposer-arg",
            value,
        ])
        .unwrap();
        let CliAction::CampaignRun(Ok(configuration)) = action else {
            panic!("opaque argument became help")
        };
        assert_eq!(configuration.proposer.unwrap().arguments, [value]);
    }
    assert!(matches!(
        parse_cli_args([
            "campaign",
            "run",
            "--all",
            "--proposer-executable",
            "endpoint",
            "--proposer-arg=--help",
        ])
        .unwrap(),
        CliAction::CampaignRun(Ok(_))
    ));
    assert!(matches!(
        parse_cli_args([
            "campaign",
            "run",
            "--all",
            "--proposer-executable",
            "endpoint",
            "--proposer-arg",
            "--help",
            "--help",
        ])
        .unwrap(),
        CliAction::CampaignHelp
    ));
}

#[test]
fn retired_native_options_are_refused_in_either_order() {
    for legacy in [
        vec!["--provider", "codex"],
        vec!["--provider", "none"],
        vec!["--model", "private-value"],
        vec!["--reasoning-effort", "private-value"],
        vec!["--claude-cli", "private-value"],
        vec!["--bridge", "private-value"],
        vec!["--isolation", "local"],
        vec!["--provider-traffic-bytes", "10"],
        vec!["--provider-messages", "10"],
        vec!["--session-mode", "fresh"],
    ] {
        for generic in [
            vec!["--proposer-executable", "endpoint"],
            vec!["--no-proposer"],
        ] {
            for reverse in [false, true] {
                let mut arguments = vec!["--all"];
                for options in if reverse {
                    [&legacy, &generic]
                } else {
                    [&generic, &legacy]
                } {
                    arguments.extend(options.iter().copied());
                }
                let error = parse(&arguments).unwrap_err();
                assert!(!error.contains("private-value"));
            }
        }
    }
    assert!(parse(&["--all", "--api-messages", "10"]).is_err());
}

#[test]
fn malformed_or_conflicting_endpoint_selection_fails_without_echoing_arguments() {
    for extra in [
        vec!["--proposer-executable", ""],
        vec!["--proposer-executable", "private\0value"],
        vec!["--proposer-arg", "private-value"],
        vec!["--proposer-arg=private-value"],
        vec!["--proposer-executable", "endpoint", "--proposer-arg"],
        vec![
            "--proposer-executable",
            "endpoint",
            "--proposer-arg",
            "private\0value",
        ],
        vec![
            "--proposer-executable",
            "endpoint",
            "--proposer-arg=private\0value",
        ],
        vec!["--proposer-executable", "endpoint", "--no-proposer"],
        vec!["--no-proposer", "--no-proposer"],
        vec![
            "--proposer-executable",
            "one",
            "--proposer-executable",
            "two",
        ],
        vec!["--no-proposer", "--api-messages", "0"],
        vec!["--no-proposer", "--api-traffic-bytes", "0"],
    ] {
        let mut arguments = vec!["--all"];
        arguments.extend(extra);
        let error = parse(&arguments).unwrap_err();
        assert!(!error.contains("private-value") && !error.contains("private\0value"));
    }
}

#[cfg(unix)]
mod executable {
    use serde_json::Value;
    use std::collections::BTreeSet;
    use std::fs;
    use std::os::unix::fs::PermissionsExt;
    use std::path::{Path, PathBuf};
    use std::process::{Command, Output, Stdio};
    use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

    struct Fixture {
        root: PathBuf,
        repository: PathBuf,
        destination: PathBuf,
        endpoint: PathBuf,
    }

    impl Fixture {
        fn new() -> Self {
            let root = std::env::temp_dir().join(format!(
                "whiel-generic-cli-{}-{}",
                std::process::id(),
                SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .unwrap()
                    .as_nanos()
            ));
            let repository = root.join("repo");
            fs::create_dir_all(repository.join("Benchmark/Example0001")).unwrap();
            fs::write(repository.join("Whiel.lean"), "-- inventory fixture only\n").unwrap();
            fs::write(
                repository.join("Benchmark/Example0001/Input.lean"),
                "-- not checked or built\n",
            )
            .unwrap();
            let endpoint = repository.join("custom endpoint");
            fs::write(
                &endpoint,
                "#!/bin/sh\nprintf started > \"$0.started\"\nexit 94\n",
            )
            .unwrap();
            fs::set_permissions(&endpoint, fs::Permissions::from_mode(0o755)).unwrap();
            Self {
                destination: root.join("output/campaign"),
                root,
                repository,
                endpoint,
            }
        }

        fn run(&self, arguments: &[&str]) -> Output {
            // No interpreter, model, source helper, worker or solver is needed:
            // the absent toolchain pin fails before a proposer is started.
            let mut child = Command::new(env!("CARGO_BIN_EXE_whiel-symbolic"))
                .current_dir(&self.repository)
                .args([
                    "campaign",
                    "run",
                    "--input",
                    "1",
                    "--minimum-free-bytes",
                    "1",
                ])
                .args(arguments)
                .arg("--destination")
                .arg(&self.destination)
                .env("PATH", self.root.join("no-executables"))
                .stdin(Stdio::null())
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .spawn()
                .unwrap();
            let deadline = Instant::now() + Duration::from_secs(10);
            while child.try_wait().unwrap().is_none() {
                if Instant::now() >= deadline {
                    let _ = child.kill();
                    panic!(
                        "generic CLI fixture timed out: {:?}",
                        child.wait_with_output().unwrap()
                    );
                }
                std::thread::sleep(Duration::from_millis(10));
            }
            child.wait_with_output().unwrap()
        }

        fn read(&self, name: &str) -> Value {
            serde_json::from_slice(&fs::read(self.destination.join(name)).unwrap()).unwrap()
        }
    }

    impl Drop for Fixture {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.root);
        }
    }

    fn keys(value: &Value, expected: &[&str]) {
        assert_eq!(
            value
                .as_object()
                .unwrap()
                .keys()
                .map(String::as_str)
                .collect::<BTreeSet<_>>(),
            expected.iter().copied().collect()
        );
    }

    #[test]
    fn generic_output_is_schema_three_without_agent_installation_or_native_fields() {
        for disabled in [false, true] {
            let fixture = Fixture::new();
            let arguments = if disabled {
                vec!["--no-proposer"]
            } else {
                vec![
                    "--proposer-executable",
                    "custom endpoint",
                    "--proposer-arg",
                    "--help",
                    "--proposer-arg",
                    "two words",
                    "--proposer-arg",
                    "",
                ]
            };
            let output = fixture.run(&arguments);
            assert_eq!(output.status.code(), Some(3), "{output:?}");
            assert!(!fixture.repository.join("agent_houdini").exists());
            assert!(!fixture.repository.join("custom endpoint.started").exists());
            let settings = fixture.read("campaign-settings.json");
            keys(
                &settings,
                &["schema_version", "inputs", "controls", "proposer"],
            );
            assert_eq!(settings["schema_version"], 3);
            if disabled {
                assert!(settings["proposer"].is_null());
            } else {
                keys(&settings["proposer"], &["executable", "arguments"]);
                // An executable inside the repository is recorded relative to
                // its root, so the settings a copied run directory carries
                // name no machine location.
                assert!(fixture.endpoint.is_absolute());
                assert_eq!(settings["proposer"]["executable"], "custom endpoint");
                assert_eq!(
                    settings["proposer"]["arguments"],
                    serde_json::json!(["--help", "two words", ""])
                );
            }
            let resources = fixture.read("resource-limits.json");
            keys(&resources, &["schema_version", "limits"]);
            assert_eq!(resources["schema_version"], 2);
            keys(
                &resources["limits"],
                &[
                    "api_traffic_bytes",
                    "api_messages",
                    "artifact_bytes",
                    "artifact_files",
                    "workspace_bytes",
                    "workspace_files",
                    "minimum_free_bytes",
                    "workspace_entries",
                    "workspace_directories",
                ],
            );
            assert_eq!(settings["controls"]["resource_limits"], resources["limits"]);
            let result = fixture.read("Example0001/result.json");
            keys(
                &result,
                &[
                    "schema_version",
                    "input",
                    "status",
                    "detail",
                    "campaign_controls",
                    "proposer",
                ],
            );
            assert_eq!(result["schema_version"], 3);
            assert_eq!(result["status"], "failed");
            // This fixture has no toolchain pin, so the search loop is never
            // entered. The key is absent rather than zero: a zero would read
            // as a search that returned instantly.
            assert!(
                result.get("search_seconds").is_none(),
                "a search that never started reports no duration: {result}"
            );
            assert_eq!(result["proposer"], settings["proposer"]);
            let summary = fixture.read("summary.json");
            keys(
                &summary,
                &[
                    "schema_version",
                    "interrupted",
                    "all_certified",
                    // Two questions, not one: whether every input's search
                    // reached a verdict, and whether every verdict was
                    // certified. A run that only searched answers the first
                    // yes and the second no.
                    "all_accepted",
                    "resource_failure",
                    "selected_inputs",
                    "unrun_inputs",
                    "campaign_controls",
                    "results",
                ],
            );
            assert_eq!(summary["schema_version"], 3);
            assert_eq!(summary["results"][0], result);
            assert_eq!(summary["all_certified"], false);
            assert_eq!(summary["all_accepted"], false);
            // The mode a run was made under is recorded beside its budgets,
            // so a run directory says how it is to be read.
            assert_eq!(settings["controls"]["certify"], "inline");
        }
    }

    /// An endpoint or argument outside the repository is not a portable path:
    /// the executable is named by its bare file name (still meaningful on
    /// another machine, such as a python interpreter or a provider CLI), and
    /// any other out-of-repository argument is replaced by a placeholder,
    /// with the flag that named it left exactly as the caller wrote it.
    #[test]
    fn an_out_of_repository_endpoint_and_argument_are_recorded_without_their_machine_path() {
        let fixture = Fixture::new();
        let outside_endpoint = fixture.root.join("outside endpoint");
        fs::write(
            &outside_endpoint,
            "#!/bin/sh\nprintf started > \"$0.started\"\nexit 94\n",
        )
        .unwrap();
        fs::set_permissions(&outside_endpoint, fs::Permissions::from_mode(0o755)).unwrap();
        let scratch = fixture.root.join("scratch-parent");
        fs::create_dir_all(&scratch).unwrap();
        assert!(outside_endpoint.is_absolute());
        assert!(!outside_endpoint.starts_with(&fixture.repository));
        let output = fixture.run(&[
            "--proposer-executable",
            outside_endpoint.to_str().unwrap(),
            "--proposer-arg",
            "--agent-scratch-parent",
            "--proposer-arg",
            scratch.to_str().unwrap(),
        ]);
        assert_eq!(output.status.code(), Some(3), "{output:?}");
        let settings = fixture.read("campaign-settings.json");
        assert_eq!(
            settings["proposer"]["executable"],
            outside_endpoint.file_name().unwrap().to_str().unwrap()
        );
        assert_eq!(
            settings["proposer"]["arguments"],
            serde_json::json!(["--agent-scratch-parent", "<outside-repository>"])
        );
        let result = fixture.read("Example0001/result.json");
        assert_eq!(result["proposer"], settings["proposer"]);
    }

    /// A relative argument that walks back out of the repository with `..`
    /// is exactly as much an outside path as the same location spelled
    /// absolute, and must not be recorded verbatim just because it happens
    /// to be relative.
    #[test]
    fn a_relative_argument_that_escapes_the_repository_is_redacted() {
        let fixture = Fixture::new();
        let scratch = fixture.root.join("scratch-parent");
        fs::create_dir_all(&scratch).unwrap();
        let output = fixture.run(&[
            "--proposer-executable",
            fixture.endpoint.to_str().unwrap(),
            "--proposer-arg",
            "--agent-scratch-parent",
            "--proposer-arg",
            "../scratch-parent",
        ]);
        assert_eq!(output.status.code(), Some(3), "{output:?}");
        let settings = fixture.read("campaign-settings.json");
        assert_eq!(
            settings["proposer"]["arguments"],
            serde_json::json!(["--agent-scratch-parent", "<outside-repository>"])
        );
    }

    /// An outside-repository argument is redacted the same way regardless of
    /// whether it happens to name something executable on this machine: only
    /// the executable at position 0 of the command is ever named, so the
    /// same spec records identically whether or not the argument's target
    /// exists here, or on any other machine that runs it.
    #[test]
    fn an_outside_repository_argument_is_redacted_even_when_it_names_an_executable() {
        let fixture = Fixture::new();
        let outside_executable_argument = fixture.root.join("looks-like-a-provider-cli");
        fs::write(&outside_executable_argument, "#!/bin/sh\nexit 0\n").unwrap();
        fs::set_permissions(
            &outside_executable_argument,
            fs::Permissions::from_mode(0o755),
        )
        .unwrap();
        let output = fixture.run(&[
            "--proposer-executable",
            fixture.endpoint.to_str().unwrap(),
            "--proposer-arg",
            "--agent-cli",
            "--proposer-arg",
            outside_executable_argument.to_str().unwrap(),
        ]);
        assert_eq!(output.status.code(), Some(3), "{output:?}");
        let settings = fixture.read("campaign-settings.json");
        assert_eq!(
            settings["proposer"]["arguments"],
            serde_json::json!(["--agent-cli", "<outside-repository>"])
        );
    }

    /// Ordinary arguments — flags, numbers, model names — and any
    /// in-repository relative path are left exactly as the caller wrote
    /// them: only a path that actually resolves outside the repository is
    /// ever touched.
    #[test]
    fn ordinary_and_in_repository_relative_arguments_are_left_exactly_as_given() {
        let fixture = Fixture::new();
        fs::write(fixture.repository.join("config.json"), "{}\n").unwrap();
        let output = fixture.run(&[
            "--proposer-executable",
            fixture.endpoint.to_str().unwrap(),
            "--proposer-arg",
            "--model",
            "--proposer-arg",
            "example-model",
            "--proposer-arg",
            "--temperature",
            "--proposer-arg",
            "0.7",
            "--proposer-arg",
            "config.json",
            "--proposer-arg",
            "./config.json",
        ]);
        assert_eq!(output.status.code(), Some(3), "{output:?}");
        let settings = fixture.read("campaign-settings.json");
        assert_eq!(
            settings["proposer"]["arguments"],
            serde_json::json!([
                "--model",
                "example-model",
                "--temperature",
                "0.7",
                "config.json",
                "./config.json",
            ])
        );
    }

    /// A campaign that names no CASC option at all runs the portfolio, and
    /// its own settings file says so — the default is a property of the
    /// command, not of a flag a caller remembered to pass. `off` is
    /// recorded as the direct-only run it is, with no split it never
    /// performed, and a share that such a run would not apply is refused
    /// rather than silently ignored.
    #[test]
    fn the_recorded_default_of_a_bare_campaign_is_the_casc_portfolio() {
        let fixture = Fixture::new();
        fixture.run(&["--no-proposer"]);
        let settings = fixture.read("campaign-settings.json");
        // Everything a reader has to match before two runs' results mean
        // anything against each other, pinned as a set so a later member
        // cannot be added to one record and forgotten in the other.
        keys(
            &settings["controls"],
            &[
                "search_limit_seconds",
                "certification_limit_seconds",
                "consultation_limit_seconds",
                "transport_retries",
                "certificate_solver_limit_seconds",
                "counterexample_validation_limit_seconds",
                "iteration_limit",
                "workers",
                "budgets",
                "certify",
                "casc_portfolio",
                "proof_casc_share",
                "proof_casc_retry_share",
                "retry_allowance_seconds",
                "premise_role_retries",
                "resource_limits",
            ],
        );
        assert_eq!(settings["controls"]["casc_portfolio"], "enabled");
        assert_eq!(settings["controls"]["proof_casc_share"], "0.25");
        assert_eq!(settings["controls"]["proof_casc_retry_share"], "0.75");
        // The ladder a run without the flag actually applies, never null.
        assert_eq!(
            settings["controls"]["retry_allowance_seconds"],
            serde_json::json!([30.0, 90.0, 240.0])
        );
        // The role a retry launch renders its premises under.
        assert_eq!(
            settings["controls"]["premise_role_retries"],
            "negated_conjecture"
        );
        // Every started input repeats the settings verbatim.
        let result = fixture.read("Example0001/result.json");
        assert_eq!(result["campaign_controls"], settings["controls"]);

        let off = Fixture::new();
        off.run(&["--no-proposer", "--casc-portfolio", "off"]);
        let settings = off.read("campaign-settings.json");
        assert_eq!(settings["controls"]["casc_portfolio"], "disabled");
        assert_eq!(settings["controls"]["proof_casc_share"], "0");
        assert_eq!(settings["controls"]["proof_casc_retry_share"], "0");

        // A run that names its own ladder records that one instead: two
        // runs whose launches have different allowances are not comparable,
        // and now their settings say so.
        let ladder = Fixture::new();
        ladder.run(&[
            "--no-proposer",
            "--retry-allowance",
            "5",
            "--retry-allowance",
            "12.5",
        ]);
        assert_eq!(
            ladder.read("campaign-settings.json")["controls"]["retry_allowance_seconds"],
            serde_json::json!([5.0, 12.5])
        );

        // The ablation value is reachable, and records itself.
        let axiom_tagged = Fixture::new();
        axiom_tagged.run(&["--no-proposer", "--retry-premise-role", "axiom"]);
        assert_eq!(
            axiom_tagged.read("campaign-settings.json")["controls"]["premise_role_retries"],
            "axiom"
        );

        let refused = Fixture::new();
        let output = refused.run(&[
            "--no-proposer",
            "--casc-portfolio",
            "off",
            "--proof-casc-share",
            "0.25",
        ]);
        assert_eq!(output.status.code(), Some(2), "{output:?}");
    }

    /// The uncertified modes stop at acceptance: nothing is certified, the
    /// summary says so twice over, and the exit code is its own value.
    #[test]
    fn the_uncertified_modes_are_recorded_and_exit_with_their_own_code() {
        for mode in ["deferred", "never"] {
            let fixture = Fixture::new();
            // The fixture repository has no toolchain pin, so the search
            // never starts; what is pinned here is the mode's own record and
            // that a failed input is still a failure in every mode.
            let output = fixture.run(&["--no-proposer", "--certify", mode]);
            assert_eq!(output.status.code(), Some(3), "{output:?}");
            let settings = fixture.read("campaign-settings.json");
            assert_eq!(settings["controls"]["certify"], mode);
            let summary = fixture.read("summary.json");
            assert_eq!(summary["all_certified"], false);
            assert_eq!(summary["all_accepted"], false);
            assert!(!fixture.destination.join("Example0001/Certificate").exists());
            assert!(
                !fixture
                    .destination
                    .join("Example0001/CertificateEvidence")
                    .exists()
            );
        }
        let fixture = Fixture::new();
        let output = fixture.run(&["--no-proposer", "--certify", "sometimes"]);
        assert_eq!(output.status.code(), Some(2), "{output:?}");
    }

    /// A run directory is untrusted input: an empty `Certificate/` beside a
    /// hand-written `"status": "valid"` is never read as certified.
    ///
    /// This is the shape a tampered or half-written directory takes, and it
    /// is also the cheapest way to state the rule: the tree names no
    /// certificate module, so nothing can revalidate it, so the claim does
    /// not stand. The run reports `certification_unchecked` and does not
    /// remove the tree. It exits 3, not 0 and not 4: the input is still
    /// accepted, but no later certification can resolve a tree that cannot be
    /// checked, so this is a failure of the run rather than work merely
    /// outstanding.
    #[test]
    fn an_unverifiable_certificate_tree_is_never_read_as_certified() {
        let fixture = Fixture::new();
        let run = fixture.root.join("searched");
        fs::create_dir_all(run.join("Example0001")).unwrap();
        fs::create_dir_all(run.join("Example0001/Certificate")).unwrap();
        fs::write(
            run.join("Example0001/Accepted.json"),
            serde_json::to_vec_pretty(&serde_json::json!({
                "kind": "whiel_search_acceptance",
                "version": 1,
                "verdict": "valid",
                "record": "Core.json",
                "task_identity": {"canonical_id": "Example0001"},
                "search": {"elapsed_seconds": 1.0, "limit_seconds": 600.0},
                "core": serde_json::Value::Null,
            }))
            .unwrap(),
        )
        .unwrap();
        fs::write(
            run.join("Example0001/result.json"),
            br#"{"input":"Example0001","status":"valid"}"#,
        )
        .unwrap();
        fs::write(
            run.join("summary.json"),
            serde_json::to_vec_pretty(&serde_json::json!({
                "schema_version": 3,
                "interrupted": false,
                "all_certified": false,
                "all_accepted": true,
                "resource_failure": serde_json::Value::Null,
                "selected_inputs": ["Example0001"],
                "unrun_inputs": [],
                "results": [],
            }))
            .unwrap(),
        )
        .unwrap();
        let certify = |run: &Path| {
            Command::new(env!("CARGO_BIN_EXE_whiel-symbolic"))
                .current_dir(&fixture.repository)
                .args(["campaign", "certify", "--run"])
                .arg(run)
                .env("PATH", fixture.root.join("no-executables"))
                .stdin(Stdio::null())
                .output()
                .unwrap()
        };
        let output = certify(&run);
        assert_eq!(output.status.code(), Some(3), "{output:?}");
        let summary: Value =
            serde_json::from_slice(&fs::read(run.join("summary.json")).unwrap()).unwrap();
        assert_eq!(summary["all_certified"], false);
        // The input was accepted — its envelope is right there — and that
        // stays true however little can be said about the tree beside it.
        assert_eq!(summary["all_accepted"], true);
        assert_eq!(summary["results"][0]["status"], "certification_unchecked");
        assert!(
            run.join("Example0001/Certificate").is_dir(),
            "a published tree is never removed to make room"
        );
        // Repeating it says the same thing: the decision is made from the
        // records, so a resumed certify is the same certify.
        let again = certify(&run);
        assert_eq!(again.status.code(), Some(3), "{again:?}");
        let repeated: Value =
            serde_json::from_slice(&fs::read(run.join("summary.json")).unwrap()).unwrap();
        // The verdict repeats exactly; only the refusal's own wording moves
        // on, because the second pass reads back the status the first wrote.
        assert_eq!(repeated["all_certified"], summary["all_certified"]);
        assert_eq!(repeated["all_accepted"], summary["all_accepted"]);
        assert_eq!(
            repeated["results"][0]["status"],
            summary["results"][0]["status"]
        );

        // A second command on the same directory is refused by name rather
        // than racing the first one's staging and summary.
        let lock = run.join(".certify-lock");
        fs::create_dir(&lock).unwrap();
        let contended = certify(&run);
        assert_eq!(contended.status.code(), Some(2), "{contended:?}");
        assert!(
            String::from_utf8_lossy(&contended.stderr).contains("another certification"),
            "{contended:?}"
        );
        fs::remove_dir(&lock).unwrap();

        // A directory with no run summary is an argument failure, not a
        // silent success over nothing.
        let empty = fixture.root.join("not-a-run");
        fs::create_dir_all(&empty).unwrap();
        assert_eq!(certify(&empty).status.code(), Some(2));
    }

    /// `--workers N` is N concurrent checks, and every budget derived from it
    /// is recorded with the run so two runs are comparable from their settings.
    #[test]
    fn every_derived_concurrency_budget_is_recorded_with_the_run() {
        let cores = whiel_runner::campaign_cli::host_parallelism();
        let lanes = whiel_runner::campaign_cli::CAMPAIGN_CHECK_LANES;
        for requested in ["1", "3", "64"] {
            let fixture = Fixture::new();
            let output = fixture.run(&["--no-proposer", "--workers", requested]);
            assert_eq!(output.status.code(), Some(3), "{output:?}");
            let controls = fixture.read("campaign-settings.json")["controls"].clone();
            let checks: usize = requested.parse().unwrap();
            // The Python harness renders `workers`, so it stays beside the
            // derived record rather than being replaced by it.
            assert_eq!(controls["workers"], checks);
            let budgets = &controls["budgets"];
            keys(
                budgets,
                &[
                    "host_parallelism",
                    "host_memory_bytes",
                    "vampire_memory_limit_mb",
                    "vampire_planned_footprint_mb",
                    "memory_estimate_checks",
                    "exceeds_memory_estimate",
                    "exceeds_host_parallelism",
                    "checks",
                    "lanes",
                    "finite_model_lane",
                    "vampire_processes",
                    "lean_workers",
                    "lean_worker_threads",
                    "lean_round_trip_timeout_seconds",
                    "cpu_permits",
                    "runtime_worker_threads",
                    "certification_jobs",
                ],
            );
            assert_eq!(budgets["checks"], checks);
            assert_eq!(budgets["lanes"], lanes);
            assert_eq!(
                budgets["finite_model_lane"],
                whiel_runner::campaign_cli::CAMPAIGN_FINITE_MODEL_LANE
            );
            // A check takes every lane's slot atomically, so N concurrent
            // checks need N x lanes processes; with one check the race must
            // still get both slots rather than running the lanes in turn.
            assert_eq!(budgets["vampire_processes"], checks * lanes);
            assert!(budgets["vampire_processes"].as_u64().unwrap() >= lanes as u64);
            assert_eq!(budgets["lean_workers"], checks.min(4));
            assert_eq!(budgets["lean_worker_threads"], 1);
            assert_eq!(budgets["certification_jobs"], checks);
            assert_eq!(budgets["host_parallelism"], cores);
            assert_eq!(budgets["cpu_permits"], cores);
            assert_eq!(budgets["runtime_worker_threads"], cores.max(2));
            // An explicit count is honoured whatever memory or the core count
            // allow; exceeding either is reported, never enforced.
            assert_eq!(
                budgets["exceeds_memory_estimate"].as_bool().unwrap(),
                budgets["memory_estimate_checks"]
                    .as_u64()
                    .is_some_and(|estimate| checks as u64 > estimate)
            );
            assert_eq!(
                budgets["exceeds_host_parallelism"].as_bool().unwrap(),
                (checks * lanes) as u64 > cores as u64
            );
        }
        // Without `--workers` the default is half the cores, at least one and
        // at most four, whatever memory is estimated to hold.
        let fixture = Fixture::new();
        assert_eq!(fixture.run(&["--no-proposer"]).status.code(), Some(3),);
        let budgets = fixture.read("campaign-settings.json")["controls"]["budgets"].clone();
        let expected = (cores / 2).clamp(1, 4);
        assert_eq!(budgets["checks"], expected);
        assert_eq!(
            budgets["exceeds_memory_estimate"].as_bool().unwrap(),
            budgets["memory_estimate_checks"]
                .as_u64()
                .is_some_and(|estimate| expected as u64 > estimate)
        );
        assert_eq!(
            budgets["exceeds_host_parallelism"].as_bool().unwrap(),
            (expected * lanes) as u64 > cores as u64
        );
        assert_eq!(budgets["checks"], budgets["certification_jobs"]);
    }

    #[test]
    fn missing_or_retired_selection_fails_before_output_and_help_starts_nothing() {
        for arguments in [
            vec![],
            vec!["--provider", "none"],
            vec!["--provider", "codex"],
        ] {
            let fixture = Fixture::new();
            let output = fixture.run(&arguments);
            assert_eq!(output.status.code(), Some(2), "{output:?}");
            assert!(!fixture.destination.exists());
            assert!(!fixture.repository.join("custom endpoint.started").exists());
        }
        let fixture = Fixture::new();
        let output = fixture.run(&["--help"]);
        assert_eq!(output.status.code(), Some(0), "{output:?}");
        assert!(!fixture.destination.exists());
        assert!(!fixture.repository.join("custom endpoint.started").exists());
    }

    #[test]
    fn invalid_generic_executable_is_status_two_before_output() {
        for selection in ["missing", ".", "not executable"] {
            let fixture = Fixture::new();
            fs::write(fixture.repository.join("not executable"), "data").unwrap();
            let output = fixture.run(&["--proposer-executable", selection]);
            assert_eq!(output.status.code(), Some(2), "{output:?}");
            assert!(!fixture.destination.exists());
        }
    }
}

/// Real interrupted campaign run at the generic selector. This is the process
/// level of the restored 130 classification: a signal to the CLI alone, a live
/// endpoint tree and a Lean worker, joined cleanup and no partial publication.
#[cfg(unix)]
mod interruption {
    use serde_json::Value;
    use std::collections::BTreeSet;
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::process::{Child, Command, Stdio};
    use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

    fn pid_gone(pid: i32) -> bool {
        (unsafe { libc::kill(pid, 0) }) == -1
            && std::io::Error::last_os_error().raw_os_error() == Some(libc::ESRCH)
    }

    fn assert_gone(pid: i32, label: &str) {
        let deadline = Instant::now() + Duration::from_secs(10);
        while !pid_gone(pid) {
            assert!(
                Instant::now() < deadline,
                "{label} {pid} survived the campaign's joined cleanup"
            );
            std::thread::sleep(Duration::from_millis(20));
        }
    }

    /// Every live descendant of the CLI, so the endpoint's own children and the
    /// worker/Lean tree are covered without a private supervision handle.
    fn descendants(root: i32) -> BTreeSet<i32> {
        let listing = Command::new("ps").args(["-Ao", "pid=,ppid="]).output();
        let listing = String::from_utf8(listing.expect("process listing").stdout).unwrap();
        let mut parents = Vec::new();
        for line in listing.lines() {
            let mut fields = line.split_whitespace();
            if let (Some(pid), Some(parent)) = (fields.next(), fields.next())
                && let (Ok(pid), Ok(parent)) = (pid.parse::<i32>(), parent.parse::<i32>())
            {
                parents.push((pid, parent));
            }
        }
        let mut tree = BTreeSet::from([root]);
        // The listing is ordered by pid, so repeat until no new child appears.
        loop {
            let mut grew = false;
            for (pid, parent) in &parents {
                if tree.contains(parent) && tree.insert(*pid) {
                    grew = true;
                }
            }
            if !grew {
                break;
            }
        }
        tree.remove(&root);
        tree
    }

    struct CampaignProcess {
        child: Option<Child>,
        root: PathBuf,
        destination: PathBuf,
        trace: PathBuf,
        stderr: PathBuf,
    }

    impl CampaignProcess {
        fn start(repository: &Path) -> Self {
            let python = Command::new("python3")
                .args(["-I", "-c", "import sys; print(sys.executable)"])
                .output()
                .unwrap();
            assert!(python.status.success());
            let python = PathBuf::from(String::from_utf8(python.stdout).unwrap().trim());
            let root = std::env::temp_dir().join(format!(
                "whiel-campaign-interrupt-{}-{}",
                std::process::id(),
                SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .unwrap()
                    .as_nanos()
            ));
            fs::create_dir(&root).unwrap();
            let worker = repository.join(".lake/build/bin/fixed_ambient_encoding_worker");
            assert!(
                worker.is_file(),
                "build {} before this gate",
                worker.display()
            );
            let mut process = Self {
                destination: root.join("campaign"),
                trace: root.join("trace.jsonl"),
                stderr: root.join("stderr.log"),
                child: None,
                root,
            };
            // Captures go to files: a leaked descendant holding an inherited
            // pipe must never make this test's own wait block. The signal is
            // delivered to one pid, so no watchdog wrapper sits in between;
            // the gate's own watchdog already bounds this whole process tree.
            let child = Command::new(env!("CARGO_BIN_EXE_whiel-symbolic"))
                .args(["campaign", "run"])
                .arg("--repo")
                .arg(repository)
                .args([
                    "--input",
                    "Example0001",
                    "--iteration-limit",
                    "1",
                    "--consultation-limit",
                    "300",
                    "--search-limit",
                    "600",
                ])
                .arg("--destination")
                .arg(&process.destination)
                .arg("--worker")
                .arg(&worker)
                .arg("--proposer-executable")
                .arg(&python)
                .args(["--proposer-arg", "-I", "--proposer-arg"])
                .arg(repository.join("whiel_runner/tests/fixtures/generic_campaign_exhausted.py"))
                .arg("--proposer-arg")
                .arg(&process.trace)
                .args(["--proposer-arg", "0", "--proposer-arg", "idle"])
                .env("LEAN_NUM_THREADS", "1")
                .current_dir(repository)
                .stdin(Stdio::null())
                .stdout(fs::File::create(process.root.join("stdout.log")).unwrap())
                .stderr(fs::File::create(&process.stderr).unwrap())
                .spawn()
                .unwrap();
            process.child = Some(child);
            process
        }

        fn pid(&self) -> i32 {
            i32::try_from(self.child.as_ref().unwrap().id()).unwrap()
        }

        fn events(&self) -> Vec<Value> {
            fs::read_to_string(&self.trace)
                .unwrap_or_default()
                .lines()
                .filter_map(|line| serde_json::from_str(line).ok())
                .collect()
        }

        /// The endpoint is connected, holds B's request and has its own child.
        fn wait_for_idle_consultation(&mut self) -> (i32, i32) {
            let deadline = Instant::now() + Duration::from_secs(300);
            loop {
                let events = self.events();
                let pid = |kind: &str, field: &str| {
                    events
                        .iter()
                        .find(|event| event["kind"] == kind)
                        .and_then(|event| event[field].as_i64())
                        .map(|pid| i32::try_from(pid).unwrap())
                };
                if let (Some(endpoint), Some(child)) = (pid("idle", "pid"), pid("idle", "child")) {
                    return (endpoint, child);
                }
                assert!(
                    self.child.as_mut().unwrap().try_wait().unwrap().is_none(),
                    "the campaign exited before its endpoint held a consultation: {}",
                    fs::read_to_string(&self.stderr).unwrap_or_default()
                );
                assert!(
                    Instant::now() < deadline,
                    "the endpoint never reached an idle consultation"
                );
                std::thread::sleep(Duration::from_millis(100));
            }
        }

        /// Positive pid only: neither the endpoint tree nor this test's own
        /// process group may receive the signal. B must propagate cancellation.
        fn interrupt_cli_only(&self) {
            assert!(self.pid() > 1);
            assert_eq!(unsafe { libc::kill(self.pid(), libc::SIGINT) }, 0);
        }

        fn wait(&mut self, timeout: Duration) -> std::process::ExitStatus {
            let deadline = Instant::now() + timeout;
            loop {
                if let Some(status) = self.child.as_mut().unwrap().try_wait().unwrap() {
                    self.child.take();
                    return status;
                }
                assert!(
                    Instant::now() < deadline,
                    "the interrupted campaign exceeded the test deadline: {}",
                    fs::read_to_string(&self.stderr).unwrap_or_default()
                );
                std::thread::sleep(Duration::from_millis(20));
            }
        }

        fn read(&self, name: &str) -> Value {
            serde_json::from_slice(&fs::read(self.destination.join(name)).unwrap()).unwrap()
        }
    }

    // Test-owned cleanup also covers assertion failures; only recorded fixture
    // pids and the CLI's own tree are eligible, never a process-group kill.
    impl Drop for CampaignProcess {
        fn drop(&mut self) {
            if let Some(child) = self.child.as_mut() {
                let tree = descendants(i32::try_from(child.id()).unwrap());
                let _ = child.kill();
                let _ = child.wait();
                for pid in tree {
                    unsafe { libc::kill(pid, libc::SIGKILL) };
                }
            }
            for event in self.events() {
                for field in ["pid", "child"] {
                    if let Some(pid) = event[field]
                        .as_i64()
                        .and_then(|pid| i32::try_from(pid).ok())
                        && pid > 1
                        && !pid_gone(pid)
                    {
                        unsafe { libc::kill(pid, libc::SIGKILL) };
                    }
                }
            }
            let _ = fs::remove_dir_all(&self.root);
        }
    }

    fn certificates(directory: &Path) -> Vec<PathBuf> {
        let mut found = Vec::new();
        let Ok(entries) = fs::read_dir(directory) else {
            return found;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                found.extend(certificates(&path));
            } else if path.file_name().is_some_and(|name| name == "Valid.lean") {
                found.push(path);
            }
        }
        found
    }

    #[test]
    fn campaign_run_sigint_exits_130_after_joined_cleanup() {
        let repository = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();
        let mut campaign = CampaignProcess::start(repository);
        let (endpoint, endpoint_child) = campaign.wait_for_idle_consultation();
        let tree = descendants(campaign.pid());
        assert!(tree.contains(&endpoint), "endpoint is not the CLI's child");
        assert!(tree.len() > 1, "no worker child was running: {tree:?}");
        campaign.interrupt_cli_only();
        let status = campaign.wait(Duration::from_secs(60));

        assert_eq!(status.code(), Some(130), "{status:?}");
        assert_gone(endpoint, "the generic endpoint");
        assert_gone(endpoint_child, "the endpoint's child");
        for pid in tree {
            assert_gone(pid, "a campaign descendant");
        }

        let summary = campaign.read("summary.json");
        assert_eq!(summary["schema_version"], 3);
        assert_eq!(summary["interrupted"], true);
        assert_eq!(summary["all_certified"], false);
        assert!(summary["resource_failure"].is_null());
        let result = campaign.read("Example0001/result.json");
        assert_eq!(summary["results"][0], result);
        assert_eq!(result["status"], "interrupted");
        assert!(
            !campaign
                .destination
                .join("Example0001/Certificate")
                .exists(),
            "an interrupted run published a certificate"
        );
        assert!(certificates(&campaign.destination).is_empty());
    }
}

/// What a real campaign run keeps of its own consultations, per retention.
///
/// Both runs here are the same run: the same input, the same fixture
/// proposer holding one consultation open until the search deadline, and the
/// same `search_timeout` settlement. Only `--retention` differs, so what each
/// one leaves behind is attributable to that option alone.
#[cfg(unix)]
mod retention {
    use serde_json::Value;
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::process::{Child, Command, Stdio};
    use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

    use whiel_runner::framework2::{
        ATTEMPT_HISTORY_KIND, ATTEMPT_HISTORY_SCOPE, ATTEMPT_HISTORY_VERSION,
        CONSULTATION_RECORD_SCOPE,
    };

    use crate::support;

    /// The search's own bound. The deadline is armed after the Lean worker
    /// and admission are up, so this is time the endpoint spends holding the
    /// consultation, not bootstrap time.
    const SEARCH_LIMIT_SECONDS: &str = "45";

    struct Campaign {
        child: Option<Child>,
        root: PathBuf,
        destination: PathBuf,
        trace: PathBuf,
        stderr: PathBuf,
    }

    impl Campaign {
        /// Run one campaign to its own settlement and return it.
        fn settle(repository: &Path, extra: &[&str]) -> Self {
            let python = Command::new("python3")
                .args(["-I", "-c", "import sys; print(sys.executable)"])
                .output()
                .unwrap();
            assert!(python.status.success());
            let python = PathBuf::from(String::from_utf8(python.stdout).unwrap().trim());
            let worker = repository.join(".lake/build/bin/fixed_ambient_encoding_worker");
            assert!(
                worker.is_file(),
                "build {} before this gate",
                worker.display()
            );
            let root = std::env::temp_dir().join(format!(
                "whiel-campaign-retention-{}-{}",
                std::process::id(),
                SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .unwrap()
                    .as_nanos()
            ));
            fs::create_dir(&root).unwrap();
            let mut campaign = Self {
                destination: root.join("campaign"),
                trace: root.join("trace.jsonl"),
                stderr: root.join("stderr.log"),
                child: None,
                root,
            };
            // Captures go to files so a leaked descendant holding an
            // inherited pipe can never make this test's own wait block.
            let child = Command::new(env!("CARGO_BIN_EXE_whiel-symbolic"))
                .args(["campaign", "run"])
                .arg("--repo")
                .arg(repository)
                .args([
                    "--input",
                    "Example0001",
                    "--consultation-limit",
                    "300",
                    "--search-limit",
                    SEARCH_LIMIT_SECONDS,
                ])
                .args(extra)
                .arg("--destination")
                .arg(&campaign.destination)
                .arg("--worker")
                .arg(&worker)
                .arg("--proposer-executable")
                .arg(&python)
                .args(["--proposer-arg", "-I", "--proposer-arg"])
                .arg(repository.join("whiel_runner/tests/fixtures/generic_campaign_exhausted.py"))
                .arg("--proposer-arg")
                .arg(&campaign.trace)
                .args(["--proposer-arg", "0", "--proposer-arg", "idle"])
                .env("LEAN_NUM_THREADS", "1")
                .current_dir(repository)
                .stdin(Stdio::null())
                .stdout(fs::File::create(campaign.root.join("stdout.log")).unwrap())
                .stderr(fs::File::create(&campaign.stderr).unwrap())
                .spawn()
                .unwrap();
            campaign.child = Some(child);
            campaign.wait(Duration::from_secs(900));
            campaign
        }

        fn wait(&mut self, timeout: Duration) {
            let deadline = Instant::now() + timeout;
            loop {
                if self.child.as_mut().unwrap().try_wait().unwrap().is_some() {
                    self.child.take();
                    return;
                }
                assert!(
                    Instant::now() < deadline,
                    "the campaign exceeded the test deadline: {}",
                    fs::read_to_string(&self.stderr).unwrap_or_default()
                );
                std::thread::sleep(Duration::from_millis(50));
            }
        }

        fn result(&self) -> Value {
            let path = self.destination.join("Example0001/result.json");
            serde_json::from_slice(&fs::read(&path).unwrap_or_else(|error| {
                panic!(
                    "read {}: {error}; stderr:\n{}",
                    path.display(),
                    fs::read_to_string(&self.stderr).unwrap_or_default()
                )
            }))
            .unwrap()
        }

        fn artifact_root(&self) -> PathBuf {
            self.destination.join("Example0001/artifacts")
        }
    }

    // Test-owned cleanup also covers assertion failures. Only the fixture's
    // own recorded pids and the CLI's own child are eligible.
    impl Drop for Campaign {
        fn drop(&mut self) {
            if let Some(child) = self.child.as_mut() {
                let _ = child.kill();
                let _ = child.wait();
            }
            for line in fs::read_to_string(&self.trace).unwrap_or_default().lines() {
                let Ok(event) = serde_json::from_str::<Value>(line) else {
                    continue;
                };
                for field in ["pid", "child"] {
                    if let Some(pid) = event[field]
                        .as_i64()
                        .and_then(|pid| i32::try_from(pid).ok())
                        && pid > 1
                    {
                        unsafe { libc::kill(pid, libc::SIGKILL) };
                    }
                }
            }
            let _ = fs::remove_dir_all(&self.root);
        }
    }

    #[test]
    fn retention_all_publishes_every_consultation_and_the_attempt_history() {
        let repository = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();
        let campaign = Campaign::settle(repository, &["--retention", "all"]);
        let result = campaign.result();
        assert_eq!(result["status"], "search_timeout", "{result}");
        assert!(
            !campaign
                .destination
                .join("Example0001/Certificate")
                .exists(),
            "a timed-out run published a certificate"
        );

        // The run reports what it sealed, and the sealed frames are on disk.
        let frames_reported = result["consultation_records"]["frames"]
            .as_u64()
            .unwrap_or_else(|| panic!("a retained run reports its records: {result}"));
        assert!(frames_reported >= 3, "{result}");
        let head = result["consultation_records"]["head"].as_str().unwrap();
        assert_eq!(head.len(), 64, "{result}");
        // The report names what to read: the manifest kind and scope that
        // select exactly this chain, and the record ids of its frames.
        assert_eq!(result["consultation_records"]["kind"], "runtime_trace");
        assert_eq!(
            result["consultation_records"]["scope"],
            serde_json::json!(["root", CONSULTATION_RECORD_SCOPE])
        );
        let reported_ids = result["consultation_records"]["artifact_ids"]
            .as_array()
            .unwrap_or_else(|| panic!("a retained run names its record ids: {result}"))
            .clone();
        assert_eq!(reported_ids.len() as u64, frames_reported);

        let (run_root, manifest) = support::settled_run(&campaign.artifact_root());
        let records = support::manifest_records(
            &manifest,
            "runtime_trace",
            &["root", CONSULTATION_RECORD_SCOPE],
        );
        assert_eq!(
            records
                .iter()
                .map(|record| record["id"].clone())
                .collect::<Vec<_>>(),
            reported_ids,
            "the reported ids are the manifest records in chain order"
        );
        let frames: Vec<Vec<u8>> = records
            .into_iter()
            .map(|record| support::retained_payload(&run_root, record))
            .collect();
        assert_eq!(frames.len() as u64, frames_reported);
        assert_eq!(support::transcript_record(&frames[0])["kind"], "header");
        assert_eq!(
            support::transcript_record(frames.last().unwrap())["kind"],
            "closed"
        );
        // The recorded traffic is this run's, not a fixture's: the header
        // carries the run's own identity pins.
        let header = support::transcript_record(&frames[0]);
        for pin in [
            "task_digest",
            "source_digest",
            "scope_digest",
            "policy_digest",
            "runner_digest",
            "worker_digest",
            "lean_digest",
            "vampire_digest",
            "profile_digest",
        ] {
            let value = header["header"]["pins"][pin].as_str().unwrap();
            assert_eq!(value.len(), 64, "{pin} is not a digest: {value}");
        }
        // One consultation was started and held open until the deadline, so
        // the frames carry that request, its push and how it ended.
        let records: Vec<Value> = frames
            .iter()
            .map(|frame| support::transcript_record(frame))
            .collect();
        let lifecycle = |event: &str| {
            records.iter().any(|record| {
                record["event"]["kind"] == "lifecycle" && record["event"]["event"] == event
            })
        };
        assert!(lifecycle("request_started"), "{records:?}");
        assert!(lifecycle("request_cancelled"), "{records:?}");
        assert!(
            records
                .iter()
                .any(|record| record["event"]["kind"] == "bytes"
                    && record["event"]["stream"] == "push"),
            "the consultation's push was not recorded: {records:?}"
        );
        assert!(
            records
                .iter()
                .any(|record| record["event"]["kind"] == "final_owner_projection"),
            "the run's final state was not recorded: {records:?}"
        );
        assert_eq!(
            records.last().unwrap()["ineligible"],
            serde_json::json!([]),
            "a production recording is replayable as published: {records:?}"
        );

        // The attempt history is the search's own record, published from the
        // failure path the settlement never reaches.
        let history =
            support::manifest_records(&manifest, "runtime_trace", &["root", ATTEMPT_HISTORY_SCOPE]);
        assert_eq!(history.len(), 1, "{history:?}");
        // The run also reports where its attempt history went, so a refused
        // record would be visible in the run's own output.
        assert_eq!(result["attempt_history"]["kind"], "runtime_trace");
        assert_eq!(
            result["attempt_history"]["scope"],
            serde_json::json!(["root", ATTEMPT_HISTORY_SCOPE])
        );
        assert_eq!(result["attempt_history"]["artifact_id"], history[0]["id"]);
        let history: Value =
            serde_json::from_slice(&support::retained_payload(&run_root, history[0])).unwrap();
        assert_eq!(history["kind"], ATTEMPT_HISTORY_KIND);
        assert_eq!(history["version"], ATTEMPT_HISTORY_VERSION);
        assert_eq!(history["outcome"], "failure");
        assert_eq!(history["failure"]["kind"], "OverallTimeout");
        assert_eq!(history["canonical_id"], "Example0001");
        assert_eq!(history["iteration"], 1);
        // A run the deadline ended before any epoch has both lists empty and
        // still publishes them: the record states what the run did, and this
        // run got no further than holding one consultation open.
        assert_eq!(history["ledger"], serde_json::json!([]));
        assert_eq!(history["consultations"], serde_json::json!([]));
    }

    #[test]
    fn the_default_retention_publishes_no_consultation_records() {
        let repository = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();
        let campaign = Campaign::settle(repository, &[]);
        let result = campaign.result();
        assert_eq!(result["status"], "search_timeout", "{result}");
        assert!(
            result["consultation_records"].is_null(),
            "a default run reported records it does not keep: {result}"
        );
        assert!(
            result["attempt_history"].is_null(),
            "a default run reported a history it does not publish: {result}"
        );

        let (_, manifest) = support::settled_run(&campaign.artifact_root());
        assert!(
            support::manifest_records(
                &manifest,
                "runtime_trace",
                &["root", CONSULTATION_RECORD_SCOPE]
            )
            .is_empty(),
            "the default retention recorded provider traffic"
        );
        assert!(
            support::manifest_records(&manifest, "runtime_trace", &["root", ATTEMPT_HISTORY_SCOPE])
                .is_empty(),
            "the default retention published an attempt history"
        );
    }
}

/// Deferred certification, end to end, for both verdicts.
///
/// One `campaign run --certify never` over a valid and an invalid input
/// records each accepted answer and stops there; `campaign certify --run`
/// then builds and publishes both certificates from those records alone.
/// The invalid half is the one this covers that nothing else does: its
/// publication runs inside the deferred command's own certification phase,
/// which is a different arrangement from the inline settlement's.
///
/// The answers are replayed from the repository's own records, so no model
/// and no proof search of substance is involved; what runs is the verifier.
#[cfg(unix)]
mod deferred_certification {
    use serde_json::Value;
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::process::{Command, Output, Stdio};
    use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

    /// The two cheapest inputs of each verdict: what is being measured is
    /// the deferred certification, not the search in front of it.
    const VALID_INPUT: &str = "Example2007";
    const INVALID_INPUT: &str = "Example0013";

    struct Scratch {
        root: PathBuf,
    }

    impl Scratch {
        fn new() -> Self {
            let root = std::env::temp_dir().join(format!(
                "whiel-deferred-certify-{}-{}",
                std::process::id(),
                SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .unwrap()
                    .as_nanos()
            ));
            fs::create_dir(&root).unwrap();
            Self { root }
        }
    }

    impl Drop for Scratch {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.root);
        }
    }

    /// Run one command to completion, or fail the test with its own log.
    fn finished(mut command: Command, label: &str, log: &Path, timeout: Duration) -> Output {
        let mut child = command
            .stdin(Stdio::null())
            .stdout(fs::File::create(log).unwrap())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        let deadline = Instant::now() + timeout;
        while child.try_wait().unwrap().is_none() {
            if Instant::now() >= deadline {
                let _ = child.kill();
                let _ = child.wait();
                panic!(
                    "{label} exceeded the test deadline:\n{}",
                    fs::read_to_string(log).unwrap_or_default()
                );
            }
            std::thread::sleep(Duration::from_millis(50));
        }
        child.wait_with_output().unwrap()
    }

    fn read(path: &Path) -> Value {
        serde_json::from_slice(&fs::read(path).unwrap()).unwrap()
    }

    fn result(destination: &Path, input: &str) -> Value {
        read(&destination.join(input).join("result.json"))
    }

    #[test]
    fn a_never_certified_run_is_certified_afterwards_for_both_verdicts() {
        let repository = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();
        let worker = repository.join(".lake/build/bin/fixed_ambient_encoding_worker");
        assert!(
            worker.is_file(),
            "build {} before this gate",
            worker.display()
        );
        let python = Command::new("python3")
            .args(["-I", "-c", "import sys; print(sys.executable)"])
            .output()
            .unwrap();
        assert!(python.status.success());
        let python = PathBuf::from(String::from_utf8(python.stdout).unwrap().trim());
        let benchmark_record = fs::read(
            repository
                .join("Benchmark")
                .join(INVALID_INPUT)
                .join("Counterexample.json"),
        )
        .expect("the invalid input's recorded answer is what gets replayed");
        let scratch = Scratch::new();
        let destination = scratch.root.join("campaign");

        let mut run = Command::new(env!("CARGO_BIN_EXE_whiel-symbolic"));
        run.args(["campaign", "run"])
            .arg("--repo")
            .arg(repository)
            .args([
                "--input",
                VALID_INPUT,
                "--input",
                INVALID_INPUT,
                "--certify",
                "never",
                "--search-limit",
                "300",
                "--workers",
                "2",
            ])
            .arg("--destination")
            .arg(&destination)
            .arg("--worker")
            .arg(&worker)
            .arg("--proposer-executable")
            .arg(&python)
            .args(["--proposer-arg", "-I", "--proposer-arg"])
            .arg(repository.join("whiel_runner/tests/fixtures/generic_campaign_replay.py"))
            .arg("--proposer-arg")
            .arg(repository)
            .env("LEAN_NUM_THREADS", "1")
            .current_dir(repository);
        let searched = finished(
            run,
            "campaign run",
            &scratch.root.join("run.log"),
            Duration::from_secs(900),
        );
        // Every input accepted, none certified: the run's own exit code for
        // work it deliberately left outstanding.
        assert_eq!(searched.status.code(), Some(4), "{searched:?}");
        let summary = read(&destination.join("summary.json"));
        assert_eq!(summary["all_accepted"], true, "{summary}");
        assert_eq!(summary["all_certified"], false, "{summary}");
        for (input, status) in [
            (VALID_INPUT, "valid_uncertified"),
            (INVALID_INPUT, "invalid_uncertified"),
        ] {
            assert_eq!(result(&destination, input)["status"], status);
            assert!(
                !destination.join(input).join("Certificate").exists(),
                "{input} was certified by a run that was told not to"
            );
        }
        assert!(
            destination
                .join(INVALID_INPUT)
                .join("Counterexample.json")
                .is_file(),
            "the accepted invalid answer left no record to certify from"
        );

        // The deferred command, on the records alone. Before the nested
        // certification phase was resolved, the invalid input failed here
        // while the valid one passed.
        let certify = |label: &str, log: &str| {
            let mut command = Command::new(env!("CARGO_BIN_EXE_whiel-symbolic"));
            command
                .args(["campaign", "certify", "--run"])
                .arg(&destination)
                .arg("--repo")
                .arg(repository)
                .arg("--worker")
                .arg(&worker)
                .args(["--jobs", "1"])
                .env("LEAN_NUM_THREADS", "1")
                .current_dir(repository);
            finished(
                command,
                label,
                &scratch.root.join(log),
                Duration::from_secs(1800),
            )
        };
        let certified = certify("campaign certify", "certify.log");
        assert_eq!(
            certified.status.code(),
            Some(0),
            "{certified:?}\n{}",
            fs::read_to_string(scratch.root.join("certify.log")).unwrap_or_default()
        );
        let summary = read(&destination.join("summary.json"));
        assert_eq!(summary["all_certified"], true, "{summary}");
        for (input, status) in [(VALID_INPUT, "valid"), (INVALID_INPUT, "invalid")] {
            let result = result(&destination, input);
            assert_eq!(result["status"], status, "{result}");
            assert_eq!(result["certificate"], "Certificate", "{result}");
            assert!(
                destination.join(input).join("Certificate").is_dir(),
                "{input} reported a certificate it did not publish"
            );
        }
        // A certification writes beside the run's own records and nowhere
        // else: the benchmark input it read is left exactly as it stands.
        assert_eq!(
            fs::read(
                repository
                    .join("Benchmark")
                    .join(INVALID_INPUT)
                    .join("Counterexample.json")
            )
            .unwrap(),
            benchmark_record,
            "the certification wrote into the checked-in benchmark tree"
        );

        // A second certify is the same certify: every input is already
        // certified, each standing tree is revalidated rather than trusted,
        // and nothing is rebuilt or replaced.
        let published = fs::read_to_string(
            destination
                .join(INVALID_INPUT)
                .join("Certificate/Invalid.lean"),
        )
        .expect("the invalid certificate names its own module");
        let again = certify("repeated campaign certify", "certify-again.log");
        assert_eq!(again.status.code(), Some(0), "{again:?}");
        let repeated = read(&destination.join("summary.json"));
        assert_eq!(repeated["all_certified"], true, "{repeated}");
        for (input, status) in [(VALID_INPUT, "valid"), (INVALID_INPUT, "invalid")] {
            assert_eq!(result(&destination, input)["status"], status);
        }
        assert_eq!(
            fs::read_to_string(
                destination
                    .join(INVALID_INPUT)
                    .join("Certificate/Invalid.lean")
            )
            .unwrap(),
            published,
            "a standing certificate was rebuilt rather than re-checked"
        );
    }
}
