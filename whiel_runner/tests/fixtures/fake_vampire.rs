use std::env;
use std::fs::{self, OpenOptions};
use std::io::{self, Write};
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::thread;
use std::time::Duration;

#[cfg(unix)]
unsafe extern "C" {
    fn kill(pid: i32, signal: i32) -> i32;
    fn setsid() -> i32;
    fn signal(signal: i32, handler: usize) -> usize;
}

/*
  Deterministic stand-in for Vampire process and protocol tests.
  Each fixture validates the worker-owned arguments it depends on
  before emitting protocol output or constructing a process tree.
*/

// ------------------------------------------------------------
// Fixture Dispatch
// ------------------------------------------------------------

fn main() {
    let arguments = env::args_os().collect::<Vec<_>>();
    record_launch(&arguments);
    record_serial_stage(&arguments);
    let mode = value(&arguments, "--fixture").expect("--fixture mode is required");
    match mode.to_string_lossy().as_ref() {
        "proof" => proof(&arguments, false),
        "large-proof" => proof(&arguments, true),
        "proof-citing-input-axioms" => proof_citing_input_axioms(&arguments),
        "model" => model(&arguments),
        "source-model" => source_model(&arguments),
        "fmb-unknown" => fmb_unknown(&arguments),
        "hang-fmb-frontier" => hang_fmb_frontier(&arguments),
        "race-proof-win" => by_vampire_mode(&arguments, hang_fmb_frontier, delayed_proof),
        "race-fmb-failure-delayed-proof" => by_vampire_mode(&arguments, fmb_unknown, delayed_proof),
        "race-proof-fast" => by_vampire_mode(&arguments, hang_fmb_frontier, proof_small),
        "race-proof-barrier" => by_vampire_mode(&arguments, hang_fmb_frontier, barrier_proof),
        "race-model-win" => by_vampire_mode(&arguments, delayed_model, hang_proof),
        "race-source-model-win" => by_vampire_mode(&arguments, source_model, hang_proof),
        "race-proof-failure-model" => by_vampire_mode(&arguments, model, unknown),
        "race-fmb-failure-proof" => by_vampire_mode(&arguments, fmb_unknown, proof_small),
        "race-dual-failure" => by_vampire_mode(&arguments, fmb_unknown, unknown),
        "race-proof-failure-fmb-hang" => by_vampire_mode(&arguments, hang_fmb_frontier, unknown),
        "race-timeout" => by_vampire_mode(&arguments, hang_fmb_frontier, hang_proof),
        "race-timeout-advanced-frontier" => {
            by_vampire_mode(&arguments, hang_fmb_advanced_frontier, hang_proof)
        }
        "ladder-normal-proof" => ladder_normal_proof(&arguments),
        "ladder-cutoff-casc-proof" => ladder_cutoff_casc_proof(&arguments),
        "ladder-unknown-casc-proof" => ladder_unknown_casc_proof(&arguments),
        "ladder-unknown-casc-hang" => ladder_unknown_casc_hang(&arguments),
        "ladder-casc-argv" => ladder_casc_argv(&arguments),
        "ladder-both-proof-stages-unknown" => ladder_both_proof_stages_unknown(&arguments),
        "ladder-direct-process-failure" => ladder_direct_process_failure(&arguments),
        "ladder-malformed-no-casc" => ladder_malformed_no_casc(&arguments),
        "ladder-fmb-survives-switch" => ladder_fmb_survives_switch(&arguments),
        "ladder-both-proof-stages-hang" => ladder_both_proof_stages_hang(&arguments),
        "ladder-casc-only" => ladder_casc_only(&arguments),
        "race-first-pair-proof-then-hang" => first_pair_proof_then_hang(&arguments),
        "race-first-three-pairs-proof-then-hang" => first_three_pairs_proof_then_hang(&arguments),
        "race-first-pair-hang-then-delayed-proof" => first_pair_hang_then_delayed_proof(&arguments),
        "race-first-pair-hang-retry-delayed-then-proof" => {
            first_pair_hang_retry_delayed_then_proof(&arguments)
        }
        "race-first-pair-gamma-model-then-proof" => first_pair_gamma_model_then_proof(&arguments),
        "hang-proof" => hang_proof(&arguments),
        "unknown" => println!("% SZS status GaveUp for problem"),
        "proof-with-frontier" => {
            println!("% TRYING [11]");
            println!("% SZS status GaveUp for problem");
        }
        "malformed-proof" => {
            println!("% SZS status Theorem for problem");
            println!("% SZS output start Proof for problem");
            println!("incomplete proof");
        }
        "invalid-utf8-proof" => invalid_utf8_proof(),
        "nonzero" => std::process::exit(17),
        "self-time-limit" => self_resource_limit(&arguments, "Time limit"),
        "self-memory-limit" => self_resource_limit(&arguments, "Memory limit"),
        "nonzero-without-diagnostic" => {
            println!("% SZS status GaveUp for problem");
            std::process::exit(1);
        }
        // The pinned portfolio's own shapes: it echoes each child
        // strategy's termination, then reports for itself — an SZS status,
        // which no child prints — or dies without reporting at all.
        "casc-children-then-own-timeout" => casc_children(&arguments, CascEnd::OwnTimeout),
        "casc-children-then-crash" => casc_children(&arguments, CascEnd::Crash),
        "casc-children-then-proof" => casc_children(&arguments, CascEnd::Proof),
        "self-time-limit-malformed" => {
            println!("% SZS output start Proof for problem");
            println!("truncated");
            println!("% Termination reason: Time limit");
            std::process::exit(1);
        }
        "hang-tree" => hang_tree(&arguments, false),
        "hang-escape-tree" => hang_tree(&arguments, true),
        "exit-with-child" => exit_with_child(&arguments, false),
        "exit-with-escape-child" => exit_with_child(&arguments, true),
        "child-hang" => child_hang(&arguments),
        "flood-forever" => flood_forever(&arguments),
        other => panic!("unknown fixture mode {other}"),
    }
}

// ------------------------------------------------------------
// Protocol Output Fixtures
// ------------------------------------------------------------

fn proof(arguments: &[std::ffi::OsString], large: bool) {
    require_argument(arguments, "--proof", "tptp");
    require_argument(arguments, "--output_axiom_names", "on");
    println!("% SZS status Theorem for problem");
    println!("% SZS output start Proof for problem");
    if large {
        let payload = vec![b'x'; 2 * 1024 * 1024];
        io::stdout().write_all(&payload).unwrap();
        io::stdout().write_all(b"\n").unwrap();
        for _ in 0..512 {
            io::stderr().write_all(b"large stderr block\n").unwrap();
        }
    } else {
        println!("1. $false [fixture]");
    }
    println!("% SZS output end Proof for problem");
}

/// Pass 7.5b: a realistic proof fixture for exercising cited-premise
/// extraction end to end against a real Lean-generated TPTP query. Rather
/// than a canned proof, it reads its own assembled query file (the last
/// CLI argument, exactly as `proof.invocation().arguments().last()`
/// expects) and cites every `<name>` it finds in an `fof(<name>, axiom,`
/// or `tff(<name>, axiom,` declaration via a `file('problem.p', <name>)`
/// annotation — the same shape Vampire's own `--output_axiom_names on`
/// proofs use. It never interprets the surrounding formula, only the
/// literal `, axiom,` marker and the name token immediately before it.
fn proof_citing_input_axioms(arguments: &[std::ffi::OsString]) {
    require_argument(arguments, "--output_axiom_names", "on");
    println!("% SZS status Theorem for problem");
    println!("% SZS output start Proof for problem");
    if let Some(query_path) = arguments.last()
        && let Ok(contents) = fs::read_to_string(query_path)
    {
        for (ordinal, name) in cited_axiom_names(&contents).into_iter().enumerate() {
            println!("fof(fixture_cite_{ordinal}, plain, ($false), file('problem.p', {name})).");
        }
    }
    println!("1. $false [fixture]");
    println!("% SZS output end Proof for problem");
}

/// Strict lexical scan for every declared axiom name in a TPTP file: a
/// `, axiom,` marker preceded by `<role>(<name>` on the same line. Never
/// parses the formula itself.
fn cited_axiom_names(tptp: &str) -> Vec<String> {
    let mut names = Vec::new();
    for line in tptp.lines() {
        let Some(marker) = line.find(", axiom,").or_else(|| line.find(",axiom,")) else {
            continue;
        };
        let prefix = &line[..marker];
        let Some(open_paren) = prefix.rfind('(') else {
            continue;
        };
        let name = prefix[open_paren + 1..].trim();
        if !name.is_empty() {
            names.push(name.to_string());
        }
    }
    names
}

fn proof_small(arguments: &[std::ffi::OsString]) {
    proof(arguments, false);
}

fn delayed_proof(arguments: &[std::ffi::OsString]) {
    thread::sleep(Duration::from_millis(100));
    proof_small(arguments);
}

fn unknown(_: &[std::ffi::OsString]) {
    println!("% SZS status GaveUp for problem");
}

/// The pinned solver stopping itself at a limit it was given: it prints the
/// termination reason and exits nonzero. Both proof stages and the
/// finite-model lane behave this way.
fn self_resource_limit(arguments: &[std::ffi::OsString], reason: &str) -> ! {
    if is_casc(arguments) {
        require_casc_contract(arguments);
    }
    // The launch states the limit, so a stage that reports stopping at one
    // must have been given one.
    assert!(
        value(arguments, "--time_limit").is_some(),
        "every stage is told the limit it runs under"
    );
    println!("% Termination reason: {reason}");
    println!("% Time elapsed: 0.0100 s");
    std::process::exit(1);
}

enum CascEnd {
    OwnTimeout,
    Crash,
    Proof,
}

/// A portfolio launch: several child strategies each report their own time
/// limit, and then the parent either reports for itself or does not.
fn casc_children(arguments: &[std::ffi::OsString], end: CascEnd) -> ! {
    require_casc_contract(arguments);
    for _ in 0..14 {
        println!("% Time limit reached! ");
        println!("% Termination reason: Time limit");
        println!("% Time elapsed: 0.1000 s");
    }
    match end {
        CascEnd::OwnTimeout => {
            println!("% Proof not found in time 1.957 s");
            println!("% SZS status Timeout for problem");
            std::process::exit(1);
        }
        // Nothing of the parent's own: a segmentation fault or an
        // out-of-memory kill prints no report at all.
        CascEnd::Crash => std::process::exit(134),
        CascEnd::Proof => {
            println!("% SZS status Theorem for problem");
            println!("% SZS output start Proof for problem");
            println!("1. $false [fixture]");
            println!("% SZS output end Proof for problem");
            std::process::exit(0);
        }
    }
}

fn model(arguments: &[std::ffi::OsString]) {
    require_argument(arguments, "--saturation_algorithm", "fmb");
    require_argument(arguments, "--fmb_enumeration_strategy", "contour");
    require_argument(arguments, "--proof", "tptp");
    let expected = value(arguments, "--expect-start").expect("--expect-start is required");
    let actual = value(arguments, "--fmb_start_size").expect("--fmb_start_size is required");
    assert_eq!(actual, expected);
    println!("% TRYING [3]");
    println!("% TRYING [{actual}]", actual = actual.to_string_lossy());
    println!("% SZS status CounterSatisfiable for problem");
    println!("% SZS output start FiniteModel for problem");
    println!("fof(fixture_model, fi_domain, ! [X] : X = d0).");
    println!("% SZS output end FiniteModel for problem");
}

fn delayed_model(arguments: &[std::ffi::OsString]) {
    thread::sleep(Duration::from_millis(100));
    model(arguments);
}

fn source_model(arguments: &[std::ffi::OsString]) {
    require_argument(arguments, "--saturation_algorithm", "fmb");
    require_argument(arguments, "--fmb_enumeration_strategy", "contour");
    require_argument(arguments, "--proof", "tptp");
    let expected = value(arguments, "--expect-start").expect("--expect-start is required");
    let actual = value(arguments, "--fmb_start_size").expect("--fmb_start_size is required");
    assert_eq!(actual, expected);
    println!("% TRYING [{actual}]", actual = actual.to_string_lossy());
    println!("% SZS status CounterSatisfiable for problem");
    println!("% SZS output start FiniteModel for problem");
    println!("tff('declare_$i1',type,'fmb_$i_1':$i).");
    println!("tff('finite_domain_$i',axiom,! [X:$i] : X = 'fmb_$i_1').");
    for relation in ["r_0zE", "r_0zT", "r_1zT", "r_0zTBound"] {
        println!("tff(declare_{relation},type,{relation}:($i*$i)>$o).");
        println!("tff(predicate_{relation},axiom,~{relation}('fmb_$i_1','fmb_$i_1')).");
    }
    println!("% SZS output end FiniteModel for problem");
}

fn framework_ii_model(arguments: &[std::ffi::OsString]) {
    require_argument(arguments, "--saturation_algorithm", "fmb");
    require_argument(arguments, "--fmb_enumeration_strategy", "contour");
    require_argument(arguments, "--proof", "tptp");
    let expected = value(arguments, "--expect-start").expect("--expect-start is required");
    let actual = value(arguments, "--fmb_start_size").expect("--fmb_start_size is required");
    assert_eq!(actual, expected);

    let problem = arguments
        .last()
        .expect("the problem path is the final argument");
    let query = fs::read_to_string(problem).expect("read fixed-ambient query");
    let relations = query
        .split(|character: char| !(character.is_ascii_alphanumeric() || character == '_'))
        .filter(|token| is_fixed_ambient_relation_name(token))
        .map(str::to_string)
        .collect::<std::collections::BTreeSet<_>>();
    assert!(
        relations.contains("yp_zT"),
        "the Gamma-plus query must mention the prophecy copy of T"
    );

    println!("% TRYING [{actual}]", actual = actual.to_string_lossy());
    println!("% SZS status CounterSatisfiable for problem");
    println!("% SZS output start FiniteModel for problem");
    println!("tff('declare_$i1',type,'fmb_$i_1':$i).");
    println!("tff('finite_domain_$i',axiom,! [X:$i] : X = 'fmb_$i_1').");
    for relation in relations {
        println!("tff(declare_{relation},type,{relation}:($i*$i)>$o).");
        let negation = if relation == "yp_zT" { "" } else { "~" };
        println!("tff(predicate_{relation},axiom,{negation}{relation}('fmb_$i_1','fmb_$i_1')).");
    }
    println!("% SZS output end FiniteModel for problem");
}

/// One fixed-ambient relation name: the copy tag, the family tag and `_`.
///
/// The solver names of a fixed-ambient problem are its relations' clause
/// sources, so a relation is recognised by that opening rather than by a
/// prefix the renderer used to add. A constant's name opens with `k` and
/// never matches.
fn is_fixed_ambient_relation_name(token: &str) -> bool {
    let mut characters = token.chars();
    let (Some(copy), Some(family), Some('_')) =
        (characters.next(), characters.next(), characters.next())
    else {
        return false;
    };
    matches!(copy, 'o' | 'y') && matches!(family, 'p' | 'a' | 'f')
}

fn hang_fmb_frontier(arguments: &[std::ffi::OsString]) {
    require_argument(arguments, "--saturation_algorithm", "fmb");
    require_argument(arguments, "--fmb_enumeration_strategy", "contour");
    require_argument(arguments, "--proof", "tptp");
    let expected = value(arguments, "--expect-start").expect("--expect-start is required");
    let actual = value(arguments, "--fmb_start_size").expect("--fmb_start_size is required");
    assert_eq!(actual, expected);
    println!("% TRYING [{actual}]", actual = actual.to_string_lossy());
    io::stdout().flush().unwrap();
    ignore_term();
    write_preferred_pid(arguments, "--fmb-pid", std::process::id());
    loop {
        thread::sleep(Duration::from_secs(1));
    }
}

fn hang_fmb_advanced_frontier(arguments: &[std::ffi::OsString]) {
    require_argument(arguments, "--saturation_algorithm", "fmb");
    require_argument(arguments, "--fmb_enumeration_strategy", "contour");
    require_argument(arguments, "--proof", "tptp");
    let expected = value(arguments, "--expect-start").expect("--expect-start is required");
    let actual = value(arguments, "--fmb_start_size").expect("--fmb_start_size is required");
    assert_eq!(actual, expected);
    println!("% TRYING [13]");
    io::stdout().flush().unwrap();
    ignore_term();
    write_preferred_pid(arguments, "--fmb-pid", std::process::id());
    loop {
        thread::sleep(Duration::from_secs(1));
    }
}

fn hang_proof(arguments: &[std::ffi::OsString]) {
    require_argument(arguments, "--proof", "tptp");
    ignore_term();
    write_preferred_pid(arguments, "--proof-pid", std::process::id());
    loop {
        thread::sleep(Duration::from_secs(1));
    }
}

fn fmb_unknown(arguments: &[std::ffi::OsString]) {
    require_argument(arguments, "--saturation_algorithm", "fmb");
    require_argument(arguments, "--fmb_enumeration_strategy", "contour");
    require_argument(arguments, "--proof", "tptp");
    let expected = value(arguments, "--expect-start").expect("--expect-start is required");
    let actual = value(arguments, "--fmb_start_size").expect("--fmb_start_size is required");
    assert_eq!(actual, expected);
    println!("% TRYING [13]");
    println!("% SZS status GaveUp for problem");
}

fn first_pair_proof_then_hang(arguments: &[std::ffi::OsString]) {
    let launch_log = value(arguments, "--launch-log").expect("--launch-log is required");
    let launch_count = fs::read_to_string(launch_log).unwrap().lines().count();
    if launch_count <= 2 {
        by_vampire_mode(arguments, hang_fmb_frontier, proof_small);
    } else {
        by_vampire_mode(arguments, hang_fmb_frontier, hang_proof);
    }
}

fn first_three_pairs_proof_then_hang(arguments: &[std::ffi::OsString]) {
    let launch_log = value(arguments, "--launch-log").expect("--launch-log is required");
    let launch_count = fs::read_to_string(launch_log).unwrap().lines().count();
    if launch_count <= 6 {
        by_vampire_mode(arguments, hang_fmb_frontier, proof_small);
    } else {
        by_vampire_mode(arguments, hang_fmb_frontier, hang_proof);
    }
}

fn first_pair_hang_then_delayed_proof(arguments: &[std::ffi::OsString]) {
    let launch_log = value(arguments, "--launch-log").expect("--launch-log is required");
    let launch_count = fs::read_to_string(launch_log).unwrap().lines().count();
    if launch_count <= 2 {
        by_vampire_mode(arguments, hang_fmb_frontier, hang_proof);
    } else {
        by_vampire_mode(arguments, hang_fmb_frontier, delayed_retry_proof);
    }
}

fn first_pair_hang_retry_delayed_then_proof(arguments: &[std::ffi::OsString]) {
    let launch_log = value(arguments, "--launch-log").expect("--launch-log is required");
    let launch_count = fs::read_to_string(launch_log).unwrap().lines().count();
    if launch_count <= 2 {
        by_vampire_mode(arguments, hang_fmb_frontier, hang_proof);
    } else if launch_count <= 4 {
        by_vampire_mode(arguments, hang_fmb_frontier, delayed_retry_proof);
    } else {
        by_vampire_mode(arguments, hang_fmb_frontier, proof_small);
    }
}

fn first_pair_gamma_model_then_proof(arguments: &[std::ffi::OsString]) {
    let launch_log = value(arguments, "--launch-log").expect("--launch-log is required");
    let launch_count = fs::read_to_string(launch_log).unwrap().lines().count();
    if launch_count <= 2 {
        by_vampire_mode(arguments, framework_ii_model, unknown);
    } else {
        by_vampire_mode(arguments, hang_fmb_frontier, proof_small);
    }
}

fn delayed_retry_proof(arguments: &[std::ffi::OsString]) {
    thread::sleep(Duration::from_millis(600));
    proof_small(arguments);
}

fn ladder_normal_proof(arguments: &[std::ffi::OsString]) {
    if is_casc(arguments) {
        panic!("CASC must not start after a direct proof")
    }
    by_vampire_mode(arguments, hang_fmb_frontier, proof_small);
}

fn ladder_cutoff_casc_proof(arguments: &[std::ffi::OsString]) {
    if value(arguments, "--saturation_algorithm").is_some() {
        hang_fmb_frontier(arguments);
    } else if is_casc(arguments) {
        require_casc_contract(arguments);
        assert_prior_pid_reaped(arguments, "--normal-proof-pid");
        proof_small(arguments);
    } else {
        hang_ladder_proof(arguments);
    }
}

/// Record the portfolio stage's own argv, under a direct stage whose
/// duration and teardown cost the caller chooses: `--direct-hang` makes the
/// direct child ignore SIGTERM so it has to be killed at its prefix cutoff,
/// and `--direct-delay-ms` makes it give up that many milliseconds in.
/// Neither may reach the recorded argv.
fn ladder_casc_argv(arguments: &[std::ffi::OsString]) {
    if value(arguments, "--saturation_algorithm").is_some() {
        hang_fmb_frontier(arguments);
    } else if is_casc(arguments) {
        require_casc_contract(arguments);
        record_worker_argv(arguments);
        proof_small(arguments);
    } else if value(arguments, "--direct-hang").is_some() {
        hang_ladder_proof(arguments);
    } else {
        if let Some(delay) = value(arguments, "--direct-delay-ms") {
            thread::sleep(Duration::from_millis(
                delay
                    .to_string_lossy()
                    .parse()
                    .expect("--direct-delay-ms takes whole milliseconds"),
            ));
        }
        unknown(arguments);
    }
}

/// Append this launch's runner-owned argv — everything from
/// `--memory_limit`, which every launch states, up to but not including the
/// problem path — to the file `--casc-argv-log` names. The caller's own
/// fixture arguments precede it and are deliberately left out.
fn record_worker_argv(arguments: &[std::ffi::OsString]) {
    let Some(path) = value(arguments, "--casc-argv-log") else {
        return;
    };
    let start = arguments
        .iter()
        .position(|argument| argument == "--memory_limit")
        .expect("every launch states the memory it runs under");
    let owned = arguments[start..arguments.len() - 1]
        .iter()
        .map(|argument| argument.to_string_lossy().into_owned())
        .collect::<Vec<_>>()
        .join("\u{1f}");
    writeln!(
        OpenOptions::new()
            .create(true)
            .append(true)
            .open(path)
            .unwrap(),
        "{owned}"
    )
    .unwrap();
}

fn ladder_unknown_casc_hang(arguments: &[std::ffi::OsString]) {
    if value(arguments, "--saturation_algorithm").is_some() {
        hang_fmb_frontier(arguments);
    } else if is_casc(arguments) {
        require_casc_contract(arguments);
        hang_ladder_proof(arguments);
    } else {
        unknown(arguments);
    }
}

fn ladder_both_proof_stages_unknown(arguments: &[std::ffi::OsString]) {
    if is_casc(arguments) {
        require_casc_contract(arguments);
    }
    unknown(arguments);
}

fn ladder_direct_process_failure(arguments: &[std::ffi::OsString]) {
    if is_casc(arguments) {
        panic!("CASC must not start after a direct process failure")
    }
    std::process::exit(17);
}

fn ladder_unknown_casc_proof(arguments: &[std::ffi::OsString]) {
    if value(arguments, "--saturation_algorithm").is_some() {
        hang_fmb_frontier(arguments);
    } else if is_casc(arguments) {
        require_casc_contract(arguments);
        thread::sleep(Duration::from_millis(900));
        proof_small(arguments);
    } else {
        unknown(arguments);
    }
}

fn ladder_malformed_no_casc(arguments: &[std::ffi::OsString]) {
    if value(arguments, "--saturation_algorithm").is_some() {
        hang_fmb_frontier(arguments);
    } else if is_casc(arguments) {
        panic!("CASC must not start after malformed direct output")
    } else {
        println!("% SZS status Theorem for problem");
        println!("% SZS output start Proof for problem");
        println!("incomplete proof");
    }
}

fn ladder_fmb_survives_switch(arguments: &[std::ffi::OsString]) {
    if value(arguments, "--saturation_algorithm").is_some() {
        let casc_pid = value(arguments, "--casc-proof-pid")
            .map(PathBuf::from)
            .expect("the FMB handoff fixture requires --casc-proof-pid");
        while !casc_pid.is_file() {
            thread::sleep(Duration::from_millis(10));
        }
        thread::sleep(Duration::from_millis(100));
        model(arguments);
    } else {
        if is_casc(arguments) {
            require_casc_contract(arguments);
        }
        hang_ladder_proof(arguments);
    }
}

fn ladder_both_proof_stages_hang(arguments: &[std::ffi::OsString]) {
    if value(arguments, "--saturation_algorithm").is_some() {
        hang_fmb_frontier(arguments);
    } else {
        if is_casc(arguments) {
            require_casc_contract(arguments);
        }
        hang_ladder_proof(arguments);
    }
}

fn ladder_casc_only(arguments: &[std::ffi::OsString]) {
    if value(arguments, "--saturation_algorithm").is_some() {
        hang_fmb_frontier(arguments);
    } else if is_casc(arguments) {
        require_casc_contract(arguments);
        proof_small(arguments);
    } else {
        panic!("direct proof search must not start in CASC-only mode")
    }
}

fn hang_ladder_proof(arguments: &[std::ffi::OsString]) {
    require_argument(arguments, "--proof", "tptp");
    ignore_term();
    let option = if is_casc(arguments) {
        "--casc-proof-pid"
    } else {
        "--normal-proof-pid"
    };
    write_preferred_pid(arguments, option, std::process::id());
    loop {
        thread::sleep(Duration::from_secs(1));
    }
}

fn is_casc(arguments: &[std::ffi::OsString]) -> bool {
    value(arguments, "--mode").as_deref() == Some(std::ffi::OsStr::new("portfolio"))
}

fn require_casc_contract(arguments: &[std::ffi::OsString]) {
    require_argument(arguments, "--mode", "portfolio");
    require_argument(arguments, "--schedule", "casc_2025");
    require_argument(arguments, "--cores", "1");
    require_argument(arguments, "--random_seed", "1");
    require_argument(arguments, "--randomize_seed_for_portfolio_workers", "off");
    require_argument(arguments, "--shuffle_on_schedule_repeats", "off");
    require_argument(arguments, "--avatar", "on");
    require_argument(arguments, "--proof", "tptp");
    require_argument(arguments, "--output_axiom_names", "on");
    let time_limit = value(arguments, "--time_limit").expect("CASC time limit is required");
    assert!(
        time_limit.to_string_lossy().ends_with('d'),
        "CASC time limit must use exact deciseconds"
    );
    if let Some(expected) = value(arguments, "--expect-casc-limit") {
        assert_eq!(time_limit, expected);
    }
    let actual_deciseconds = parse_deciseconds(&time_limit);
    if let Some(maximum) = value(arguments, "--max-casc-limit") {
        assert!(actual_deciseconds <= parse_deciseconds(&maximum));
    }
    if let Some(minimum) = value(arguments, "--min-casc-limit") {
        assert!(actual_deciseconds >= parse_deciseconds(&minimum));
    }
}

fn parse_deciseconds(value: &std::ffi::OsStr) -> u64 {
    value
        .to_string_lossy()
        .strip_suffix('d')
        .expect("a CASC limit must end in d")
        .parse()
        .expect("a CASC limit must contain whole deciseconds")
}

fn assert_prior_pid_reaped(arguments: &[std::ffi::OsString], option: &str) {
    let Some(path) = value(arguments, option) else {
        return;
    };
    let pid = fs::read_to_string(path)
        .expect("the prior proof stage must publish its PID before CASC")
        .trim()
        .parse::<i32>()
        .expect("the prior proof PID must be an integer");
    #[cfg(unix)]
    assert_ne!(
        unsafe { kill(pid, 0) },
        0,
        "the direct proof process still existed when CASC launched",
    );
}

fn invalid_utf8_proof() {
    let mut stdout = io::stdout().lock();
    stdout
        .write_all(b"% SZS status Theorem for problem\n")
        .unwrap();
    stdout
        .write_all(b"% SZS output start Proof for problem\n")
        .unwrap();
    stdout.write_all(b"proof-\xff\n").unwrap();
    stdout
        .write_all(b"% SZS output end Proof for problem\n")
        .unwrap();
}

// ------------------------------------------------------------
// Process Tree And Pipe Fixtures
// ------------------------------------------------------------

fn hang_tree(arguments: &[std::ffi::OsString], escape: bool) {
    ignore_term();
    write_pid(arguments, "--leader-pid", std::process::id());
    let executable = env::current_exe().unwrap();
    let mut child = Command::new(executable);
    child.arg("--fixture").arg("child-hang");
    if escape {
        child.arg("--escape").arg("yes");
    }
    if let Some(path) = value(arguments, "--child-pid") {
        child.arg("--child-pid").arg(path);
    }
    child.spawn().unwrap();
    loop {
        thread::sleep(Duration::from_secs(1));
    }
}

fn exit_with_child(arguments: &[std::ffi::OsString], escape: bool) {
    let executable = env::current_exe().unwrap();
    let mut child = Command::new(executable);
    child
        .arg("--fixture")
        .arg("child-hang")
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit());
    if let Some(path) = value(arguments, "--child-pid") {
        child.arg("--child-pid").arg(path);
    }
    if escape {
        child.arg("--escape").arg("yes");
    }
    child.spawn().unwrap();
    thread::sleep(Duration::from_millis(100));
    proof(arguments, false);
}

fn child_hang(arguments: &[std::ffi::OsString]) {
    #[cfg(unix)]
    if value(arguments, "--escape").as_deref() == Some(std::ffi::OsStr::new("yes")) {
        let result = unsafe { setsid() };
        assert!(result >= 0, "setsid failed: {}", io::Error::last_os_error());
    }
    ignore_term();
    write_pid(arguments, "--child-pid", std::process::id());
    loop {
        thread::sleep(Duration::from_secs(1));
    }
}

fn flood_forever(arguments: &[std::ffi::OsString]) {
    ignore_term();
    write_pid(arguments, "--leader-pid", std::process::id());
    let block = vec![b'z'; 64 * 1024];
    loop {
        io::stdout().write_all(&block).unwrap();
        io::stderr().write_all(&block).unwrap();
    }
}

// ------------------------------------------------------------
// Fixture Argument Helpers
// ------------------------------------------------------------

/// A proof lane that will not answer until the run has the expected number of
/// proof-lane processes alive at once.
///
/// This turns "the run reached its configured concurrency" from something a
/// test hopes to observe into something the fixture forces: with a barrier of
/// `N`, no check can complete until `N` checks are simultaneously in flight, so
/// a run that cannot reach `N` never sees its high-water mark reach `N`. The
/// wait is bounded, so a run that has genuinely lost its concurrency fails an
/// assertion rather than hanging.
///
/// Occupancy is counted with one file per live process in `--barrier-dir`,
/// created on entry and removed on exit.
fn barrier_proof(arguments: &[std::ffi::OsString]) {
    let directory = PathBuf::from(
        value(arguments, "--barrier-dir").expect("--barrier-dir is required for the barrier lane"),
    );
    let width: usize = value(arguments, "--barrier-width")
        .expect("--barrier-width is required for the barrier lane")
        .to_string_lossy()
        .parse()
        .expect("--barrier-width is a positive integer");
    fs::create_dir_all(&directory).expect("create the barrier directory");
    let occupant = directory.join(format!("{}", std::process::id()));
    fs::write(&occupant, b"").expect("register at the barrier");
    // Bounded well under the run's own search allowance, so a run that cannot
    // reach the width still answers and fails on the concurrency assertion
    // rather than on a solver timeout.
    let deadline = std::time::Instant::now() + Duration::from_millis(2000);
    while std::time::Instant::now() < deadline {
        let live = fs::read_dir(&directory)
            .map(|entries| entries.flatten().count())
            .unwrap_or(0);
        if live >= width {
            break;
        }
        thread::sleep(Duration::from_millis(5));
    }
    let _ = fs::remove_file(&occupant);
    proof_small(arguments);
}

fn by_vampire_mode(
    arguments: &[std::ffi::OsString],
    fmb: fn(&[std::ffi::OsString]),
    proof: fn(&[std::ffi::OsString]),
) {
    if value(arguments, "--saturation_algorithm").as_deref() == Some(std::ffi::OsStr::new("fmb")) {
        fmb(arguments);
    } else {
        proof(arguments);
    }
}

fn record_launch(arguments: &[std::ffi::OsString]) {
    let Some(path) = value(arguments, "--launch-log") else {
        return;
    };
    writeln!(
        OpenOptions::new()
            .create(true)
            .append(true)
            .open(path)
            .unwrap(),
        "{}",
        std::process::id()
    )
    .unwrap();
}

fn record_serial_stage(arguments: &[std::ffi::OsString]) {
    let Some(path) = value(arguments, "--serial-order-log") else {
        return;
    };
    let stage = if value(arguments, "--saturation_algorithm").as_deref()
        == Some(std::ffi::OsStr::new("fmb"))
    {
        "fmb"
    } else if is_casc(arguments) {
        "casc"
    } else {
        "direct"
    };
    writeln!(
        OpenOptions::new()
            .create(true)
            .append(true)
            .open(path)
            .unwrap(),
        "{stage}"
    )
    .unwrap();
}

fn ignore_term() {
    #[cfg(unix)]
    unsafe {
        const SIGTERM: i32 = 15;
        const SIG_IGN: usize = 1;
        signal(SIGTERM, SIG_IGN);
    }
}

fn write_pid(arguments: &[std::ffi::OsString], option: &str, pid: u32) {
    if let Some(path) = value(arguments, option) {
        fs::write(PathBuf::from(path), pid.to_string()).unwrap();
    }
}

fn write_preferred_pid(arguments: &[std::ffi::OsString], option: &str, pid: u32) {
    if value(arguments, option).is_some() {
        write_pid(arguments, option, pid);
    } else {
        write_pid(arguments, "--leader-pid", pid);
    }
}

fn require_argument(arguments: &[std::ffi::OsString], option: &str, expected: &str) {
    assert_eq!(
        value(arguments, option).as_deref(),
        Some(std::ffi::OsStr::new(expected))
    );
}

fn value(arguments: &[std::ffi::OsString], option: &str) -> Option<std::ffi::OsString> {
    arguments
        .windows(2)
        .find(|pair| pair[0] == option)
        .map(|pair| pair[1].clone())
}
