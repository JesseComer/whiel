//! Current-input discovery and verifier control parsing with an explicit endpoint.
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use whiel_runner::PremiseRole;
use whiel_runner::artifact::Retention;
use whiel_runner::campaign_cli::{CampaignProvider, discover_inputs, parse_campaign_run_arguments};
use whiel_runner::cli::{CliAction, parse_cli_args};
use whiel_runner::framework2::{CascPortfolioPolicy, FrameworkIIRetryPolicy};
use whiel_runner::vampire::{ProofCascPolicy, ProofCascShare};

fn parse(arguments: &[&str]) -> Result<whiel_runner::campaign_cli::CampaignRunConfig, String> {
    parse_campaign_run_arguments(
        &std::iter::once("--no-proposer")
            .chain(arguments.iter().copied())
            .map(str::to_owned)
            .collect::<Vec<_>>(),
    )
}

#[test]
fn explicit_no_proposer_preserves_unbounded_and_independently_timed_controls() {
    let config = parse(&["--input", "Example0001"]).unwrap();
    assert_eq!(config.inputs, ["Example0001"]);
    assert!(!config.all_inputs);
    assert_eq!(config.provider, CampaignProvider::None);
    assert!(config.host_limits.in_force().is_empty());
    assert_eq!(config.retention, Retention::CertificateOnly);
    assert_eq!(config.casc_portfolio, CascPortfolioPolicy::Enabled);
    assert_eq!(config.proof_casc_policy, ProofCascPolicy::CLI_DEFAULT);
    assert_eq!(
        config.search_limits.overall_limit(),
        Duration::from_secs(600)
    );
    assert_eq!(config.certification_limit, Duration::from_secs(600));
    assert_eq!(config.certificate_solver_limit_seconds, 60);
    assert_eq!(config.search_limits.consultation_limit(), None);
    assert_eq!(
        config
            .consultation_policy
            .limits()
            .max_transport_retries_per_request,
        0
    );
    assert!(config.retry_policy_override.is_none());
    let policy =
        FrameworkIIRetryPolicy::new([Duration::from_secs(7), Duration::from_secs(19)]).unwrap();
    // The authority's own ladder, under the run's portfolio policy: the
    // campaign resolves one from the other and changes nothing else.
    assert_eq!(
        config.resolve_retry_policy(&policy),
        policy
            .clone()
            .with_casc_portfolio(CascPortfolioPolicy::Enabled)
    );
    let off = parse(&["--input", "Example0001", "--casc-portfolio", "off"]).unwrap();
    assert_eq!(off.resolve_retry_policy(&policy), policy);
}

#[test]
fn numeric_selectors_and_independent_consultation_controls_parse() {
    let config = parse(&[
        "--input",
        "0001, 13",
        "--consultation-limit",
        "0.125",
        "--transport-retries",
        "8",
        "--certificate-solver-limit",
        "17",
    ])
    .unwrap();
    assert_eq!(config.inputs, ["0001", "13"]);
    assert_eq!(
        config.search_limits.consultation_limit(),
        Some(Duration::from_millis(125))
    );
    assert_eq!(
        config
            .consultation_policy
            .limits()
            .max_transport_retries_per_request,
        8
    );
    assert_eq!(config.certificate_solver_limit_seconds, 17);
    assert_eq!(
        config.search_limits.overall_limit(),
        Duration::from_secs(600)
    );
    assert_eq!(config.certification_limit, Duration::from_secs(600));
    assert!(parse(&["--input", "1", "--transport-retries", "0"]).is_ok());
    for (flag, value) in [
        ("--consultation-limit", "0"),
        ("--consultation-limit", "NaN"),
        ("--transport-retries", "9"),
        ("--transport-retries", "1.5"),
        ("--certificate-solver-limit", "0"),
        ("--certificate-solver-limit", "1.5"),
        ("--certificate-solver-limit", "NaN"),
        ("--certificate-solver-limit", "18446744073709551616"),
    ] {
        assert!(
            parse(&["--input", "1", flag, value]).is_err(),
            "accepted {flag} {value}"
        );
    }
    for flag in [
        "--consultation-limit",
        "--transport-retries",
        "--certificate-solver-limit",
    ] {
        assert!(parse(&["--input", "1", flag, "1", flag, "2"]).is_err());
    }
    for selector in ["", "1/2", "../1", "１２", "+1", "1,,2"] {
        assert!(parse(&["--input", selector]).is_err());
    }
}

#[test]
fn single_subset_repeated_inputs_and_all_have_explicit_selection() {
    assert!(parse(&["--all"]).unwrap().all_inputs);
    assert_eq!(
        parse(&[
            "--input",
            "Example0001,Example0002",
            "--input",
            "Example0003"
        ])
        .unwrap()
        .inputs,
        ["Example0001", "Example0002", "Example0003"]
    );
    for args in [
        vec![],
        vec!["--all", "--input", "Example0001"],
        vec!["--input", "Example0001,Example0001"],
        vec!["--input", "Example0001,"],
        vec!["--input", "../Legacy"],
        vec!["--input", "Example0001/Input.lean"],
    ] {
        assert!(parse(&args).is_err(), "accepted {args:?}");
    }
}

#[test]
fn tools_and_phase_limits_remain_separate() {
    let config = parse(&[
        "--all",
        "--no-tools",
        "--search-limit",
        "0.125",
        "--certification-limit",
        "2.5",
        "--workers",
        "2",
        "--iteration-limit",
        "3",
    ])
    .unwrap();
    assert_eq!(config.provider, CampaignProvider::None);
    assert!(config.tool_policy.enabled().is_empty());
    assert_eq!(
        config.search_limits.overall_limit(),
        Duration::from_millis(125)
    );
    assert_eq!(config.certification_limit, Duration::from_millis(2500));
    assert_eq!(config.search_limits.iteration_limit(), Some(3));
}

#[test]
fn deferred_and_secret_bearing_options_are_refused_without_echo() {
    for extra in [
        vec!["--provider", "replay:old.json"],
        vec!["--provider", "process:arbitrary"],
        vec!["--session-mode", "continuous"],
        vec!["--session-mode", "fresh"],
        vec!["--compress-core"],
        vec!["--provider-key", "private-token"],
        vec!["--provider-arg", "private-token"],
        vec!["--input-directory", "Legacy"],
        vec!["--profile", "direct"],
    ] {
        let args: Vec<_> = ["--input", "Example0001"]
            .into_iter()
            .chain(extra)
            .collect();
        let error = parse(&args).unwrap_err();
        assert!(!error.contains("private-token"));
    }
}

/// The portfolio is the campaign default, `off` restores a direct-only
/// run, and the two shares are exact decimals the run records verbatim.
#[test]
fn the_casc_portfolio_is_the_default_and_its_shares_are_exact() {
    let on = parse(&["--input", "Example0001", "--casc-portfolio", "on"]).unwrap();
    assert_eq!(on.casc_portfolio, CascPortfolioPolicy::Enabled);
    assert_eq!(on.proof_casc_policy, ProofCascPolicy::CLI_DEFAULT);

    let off = parse(&["--input", "Example0001", "--casc-portfolio", "off"]).unwrap();
    assert_eq!(off.casc_portfolio, CascPortfolioPolicy::Disabled);
    // A disabled run records the split it performed, which is none at all.
    assert_eq!(off.proof_casc_policy, ProofCascPolicy::DISABLED);
    assert!(off.proof_casc_policy.is_disabled());

    let shares = parse(&[
        "--input",
        "Example0001",
        "--proof-casc-share",
        "0.5",
        "--proof-casc-retry-share",
        "0.875",
    ])
    .unwrap();
    assert_eq!(
        shares.proof_casc_policy,
        ProofCascPolicy::new(
            "0.5".parse::<ProofCascShare>().unwrap(),
            "0.875".parse::<ProofCascShare>().unwrap(),
        )
        .unwrap()
    );
    assert_eq!(shares.proof_casc_policy.initial_share().to_string(), "0.5");
    assert_eq!(
        shares.proof_casc_policy.retry_added_share().to_string(),
        "0.875"
    );

    // A lone initial share applies to the retry-added time as well, exactly
    // as the legacy command defined it.
    let uniform = parse(&["--input", "Example0001", "--proof-casc-share", "1"]).unwrap();
    assert_eq!(uniform.proof_casc_policy, ProofCascPolicy::ONLY);
}

/// A retry launch re-tags its premises by default, and the old rendering
/// stays reachable for an ablation.
#[test]
fn retries_are_goal_tagged_by_default_and_the_old_rendering_is_reachable() {
    assert_eq!(
        parse(&["--input", "Example0001"])
            .unwrap()
            .retry_premise_role,
        PremiseRole::NegatedConjecture
    );
    for (value, expected) in [
        ("axiom", PremiseRole::Axiom),
        ("negated_conjecture", PremiseRole::NegatedConjecture),
    ] {
        assert_eq!(
            parse(&["--input", "Example0001", "--retry-premise-role", value])
                .unwrap()
                .retry_premise_role,
            expected
        );
    }
}

/// Every share the solver layer cannot state exactly, every share a
/// disabled run would not apply, and every inconsistent pair is refused
/// rather than recorded.
#[test]
fn out_of_range_inert_and_inconsistent_casc_shares_are_refused() {
    for extra in [
        vec!["--proof-casc-share", "1.5"],
        vec!["--proof-casc-share", "2"],
        vec!["--proof-casc-share", "0.1234567"],
        vec!["--proof-casc-share", "half"],
        vec!["--proof-casc-share", ""],
        vec!["--proof-casc-retry-share", "1.000001"],
        // 0 initial disables the whole chain, so a nonzero retry share is
        // a contradiction; 1 initial selects it for the whole chain.
        vec![
            "--proof-casc-share",
            "0",
            "--proof-casc-retry-share",
            "0.75",
        ],
        vec!["--proof-casc-share", "1", "--proof-casc-retry-share", "0.5"],
        // Inert under a disabled portfolio.
        vec!["--casc-portfolio", "off", "--proof-casc-share", "0.25"],
        vec![
            "--casc-portfolio",
            "off",
            "--proof-casc-retry-share",
            "0.75",
        ],
        vec!["--casc-portfolio", "yes"],
        vec!["--casc-portfolio", "on", "--casc-portfolio", "off"],
    ] {
        let args: Vec<_> = ["--input", "Example0001"]
            .into_iter()
            .chain(extra.iter().copied())
            .collect();
        assert!(parse(&args).is_err(), "{extra:?} was accepted");
    }
}

#[test]
fn invalid_duration_count_duplicate_and_tool_policy_are_refused() {
    for extra in [
        vec!["--search-limit", "0"],
        vec!["--certification-limit", "NaN"],
        vec!["--workers", "0"],
        vec!["--iteration-limit", "0"],
        vec!["--retry-allowance", "2", "--retry-allowance", "1"],
        vec!["--retry-premise-role", "conjecture"],
        vec![
            "--retry-premise-role",
            "axiom",
            "--retry-premise-role",
            "negated_conjecture",
        ],
        vec!["--tools", "ledger,ledger"],
        vec!["--no-tools", "--tools", "history"],
        vec!["--isolation", "unknown"],
        vec!["--all", "--all"],
    ] {
        let args: Vec<_> = ["--input", "Example0001"]
            .into_iter()
            .chain(extra)
            .collect();
        assert!(parse(&args).is_err());
    }
}

#[test]
fn campaign_help_and_old_task_grammar_remain_distinct() {
    assert!(matches!(
        parse_cli_args(["campaign", "run", "--help"]).unwrap(),
        CliAction::CampaignHelp
    ));
    assert!(matches!(
        parse_cli_args(["campaign", "run", "--all", "--no-proposer"]).unwrap(),
        CliAction::CampaignRun(Ok(_))
    ));
    assert!(matches!(
        parse_cli_args(["task", "Example0001"]).unwrap(),
        CliAction::Run(_)
    ));
    assert!(!whiel_runner::campaign_cli::CAMPAIGN_USAGE.contains("scaffold"));
}

#[test]
fn discovery_reads_only_immediate_current_input_directories_and_rejects_links() {
    let temporary = std::env::temp_dir().join(format!(
        "whiel-campaign-inventory-{}-{}",
        std::process::id(),
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    let root = temporary.join("repo");
    for directory in [
        "Benchmark/Example0002",
        "Benchmark/Example0001",
        "Benchmark/Legacy/Nested",
        "Benchmark/Missing",
    ] {
        std::fs::create_dir_all(root.join(directory)).unwrap();
    }
    for file in [
        "Benchmark/Example0002/Input.lean",
        "Benchmark/Example0001/Input.lean",
        "Benchmark/Legacy/Nested/Input.lean",
    ] {
        std::fs::write(root.join(file), "synthetic inventory only").unwrap();
    }
    assert_eq!(
        discover_inputs(&root.canonicalize().unwrap()).unwrap(),
        ["Example0001", "Example0002"]
    );
    #[cfg(unix)]
    {
        std::fs::remove_file(root.join("Benchmark/Example0002/Input.lean")).unwrap();
        std::os::unix::fs::symlink(
            root.join("Benchmark/Example0001/Input.lean"),
            root.join("Benchmark/Example0002/Input.lean"),
        )
        .unwrap();
        assert!(discover_inputs(&root.canonicalize().unwrap()).is_err());
    }
    std::fs::remove_dir_all(temporary).unwrap();
}

#[test]
fn transport_resource_defaults_and_overrides_are_explicit() {
    let default = parse(&["--all"]).unwrap();
    assert_eq!(default.resource_limits.api_traffic_bytes, 1_073_741_824);
    assert_eq!(default.resource_limits.api_messages, 16_384);
    let override_ = parse(&[
        "--all",
        "--api-traffic-bytes",
        "1234",
        "--api-messages",
        "9",
    ])
    .unwrap();
    assert_eq!(override_.resource_limits.api_traffic_bytes, 1234);
    assert_eq!(override_.resource_limits.api_messages, 9);
    for flag in ["--api-traffic-bytes", "--api-messages"] {
        for invalid in ["0", "-1", "18446744073709551616"] {
            assert!(parse(&["--all", flag, invalid]).is_err());
        }
    }
}

#[test]
fn artifact_resource_allowances_have_explicit_defaults_and_positive_overrides() {
    let defaults = parse(&["--input", "Example0001"]).unwrap().resource_limits;
    assert_eq!(defaults.artifact_bytes, 4 * 1024 * 1024 * 1024);
    assert_eq!(defaults.artifact_files, 50_000);
    let limits = parse(&[
        "--input",
        "Example0001",
        "--artifact-bytes",
        "64",
        "--artifact-files",
        "2",
    ])
    .unwrap()
    .resource_limits;
    assert_eq!((limits.artifact_bytes, limits.artifact_files), (64, 2));
    for flag in ["--artifact-bytes", "--artifact-files"] {
        for value in ["0", "-1", "18446744073709551616"] {
            assert!(parse(&["--input", "Example0001", flag, value]).is_err());
        }
    }
}

#[test]
fn workspace_resource_defaults_units_and_positive_overrides_are_explicit() {
    let defaults = parse(&["--input", "Example0001"]).unwrap().resource_limits;
    assert_eq!(
        (
            defaults.workspace_bytes,
            defaults.workspace_files,
            defaults.minimum_free_bytes,
            defaults.workspace_entries,
            defaults.workspace_directories
        ),
        (8589934592, 100000, 2147483648, 200000, 25000)
    );
    for flag in [
        "--workspace-bytes",
        "--workspace-files",
        "--minimum-free-bytes",
        "--workspace-entries",
        "--workspace-directories",
    ] {
        assert!(parse(&["--input", "Example0001", flag, "1"]).is_ok());
        for value in ["0", "-1", "18446744073709551616"] {
            assert!(parse(&["--input", "Example0001", flag, value]).is_err());
        }
    }
}

/// A retained campaign accumulates every earlier input's ledger and
/// consultation records against one campaign-wide count, so `--retention all`
/// raises the four workspace limits by itself when the caller gave none of
/// its own; an explicit flag still wins for the limit it names, and
/// `--minimum-free-bytes` never changes, since a full disk should stop the
/// run whatever else it retains.
#[test]
fn retention_all_raises_workspace_defaults_unless_told_otherwise() {
    let retained = parse(&["--input", "Example0001", "--retention", "all"])
        .unwrap()
        .resource_limits;
    assert_eq!(
        (
            retained.workspace_bytes,
            retained.workspace_files,
            retained.minimum_free_bytes,
            retained.workspace_entries,
            retained.workspace_directories
        ),
        (68719476736, 1000000, 2147483648, 2000000, 250000)
    );
    let overridden = parse(&[
        "--input",
        "Example0001",
        "--retention",
        "all",
        "--workspace-bytes",
        "1",
        "--workspace-directories",
        "9",
    ])
    .unwrap()
    .resource_limits;
    // An explicit flag wins for its own limit only; the other two raised
    // limits still take the retained default.
    assert_eq!(overridden.workspace_bytes, 1);
    assert_eq!(overridden.workspace_directories, 9);
    assert_eq!(overridden.workspace_files, 1000000);
    assert_eq!(overridden.workspace_entries, 2000000);
    // The default retention keeps the ordinary, smaller defaults.
    let unretained = parse(&["--input", "Example0001"]).unwrap().resource_limits;
    assert_eq!(unretained.workspace_bytes, 8589934592);
    assert_eq!(unretained.workspace_files, 100000);
    assert_eq!(unretained.workspace_entries, 200000);
    assert_eq!(unretained.workspace_directories, 25000);
}
