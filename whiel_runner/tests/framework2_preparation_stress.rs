//! Live obligation-preparation stress measurement.
//!
//! Drives the real `Example0001` fixed-ambient worker with a synthetic
//! slice — a Core of committed level-zero clauses plus a much larger batch
//! of candidate clauses — and reports the split between obligation
//! preparation time and solver time, together with the worker round trips
//! the run's opaque-piece cache actually made.
//!
//! The two pool sizes are compared like with like: the same lane policy, and
//! the same rule turning a check budget into a Vampire budget, so `N` means N
//! concurrent checks at either size. What this file asserts is structural —
//! the two runs issued the same checks, none came back inconclusive, and each
//! run reached exactly the number of simultaneous checks its budgets
//! configured. Timing is reported, never asserted: wall time on a shared
//! machine is not a property of the code under test. The numbers it prints
//! and writes to `target/preparation-stress.json` are evidence for the
//! implementation manifest, not thresholds.
//!
//! Requires the Lean toolchain: `fixed_ambient_worker()` below builds
//! `fixed_ambient_encoding_worker` via `lake build` on first use, exactly
//! like `tests/framework2_fixed_ambient.rs` (whose fixture-binding and
//! command helpers this file copies rather than sharing, since integration
//! test binaries do not share a `tests/` module tree).

mod support;

use std::collections::BTreeSet;
use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::{Arc, OnceLock};
use std::time::{Duration, Instant};

use serde_json::{Value, json};

use whiel_runner::encoding::{FixedAmbientWorkerCommand, FixedAmbientWorkerPoolConfig};
use whiel_runner::{
    AgentToolPolicy, ArtifactStoreConfig, ExtendedClauseOrigin, FmbOptions,
    FrameworkIICertificationProfiles, FrameworkIICheckEvidence, FrameworkIICheckOutcome,
    FrameworkIILevel, FrameworkIIProductionCheckConfig, HostLimits, LeancheckCertificationProfile,
    LevelLedgerRow, LeveledHoudiniState, LeveledStabilizationOutcome, ProofSearchProfile,
    RuntimeResourcePolicy, SolverAdmission, SolverInvocationIdentity, VampireSearchBudget,
    VampireWorkerCommand, bind_fixed_ambient_framework_ii, create_general_solver_admission,
    new_artifact_store, stabilize_leveled_houdini,
};

// ------------------------------------------------------------
// Fixture Sources And Worker Commands (copied from framework2_fixed_ambient.rs)
// ------------------------------------------------------------

static FIXED_AMBIENT_WORKER: OnceLock<PathBuf> = OnceLock::new();
static FIXTURE_DESCRIPTOR: OnceLock<Value> = OnceLock::new();

fn fixed_ambient_worker() -> &'static Path {
    FIXED_AMBIENT_WORKER
        .get_or_init(|| {
            let repository = support::repository_root();
            let build = Command::new("lake")
                .args(["build", "fixed_ambient_encoding_worker"])
                .current_dir(&repository)
                .output()
                .expect("build fixed-ambient encoding worker");
            assert!(
                build.status.success(),
                "Lean fixed-ambient worker build failed\nstdout:\n{}\nstderr:\n{}",
                String::from_utf8_lossy(&build.stdout),
                String::from_utf8_lossy(&build.stderr)
            );
            repository.join(".lake/build/bin/fixed_ambient_encoding_worker")
        })
        .as_path()
}

fn fixture_descriptor() -> Value {
    FIXTURE_DESCRIPTOR
        .get_or_init(|| {
            let output = Command::new(fixed_ambient_worker())
                .arg("manifest")
                .current_dir(support::repository_root())
                .output()
                .expect("run the fixed-ambient fixture manifest");
            assert!(
                output.status.success(),
                "fixture manifest failed: {}",
                String::from_utf8_lossy(&output.stderr)
            );
            serde_json::from_slice(&output.stdout).expect("fixture manifest emits one JSON value")
        })
        .clone()
}

fn worker_pool(workers: usize) -> FixedAmbientWorkerPoolConfig {
    FixedAmbientWorkerPoolConfig::new(
        FixedAmbientWorkerCommand::new(fixed_ambient_worker(), support::repository_root()),
        workers,
    )
    .expect("positive worker count")
}

/// Solver lanes one check of this scenario occupies at once. The finite-model
/// lane is enabled below, so a check races two lanes and the race takes both
/// Vampire slots atomically. Deriving the Vampire budget as `checks × lanes`
/// is what makes `checks = 1` and `checks = 4` the same workload at different
/// widths rather than two different workloads.
const STRESS_CHECK_LANES: usize = 2;

fn agent_admission(checks: usize) -> SolverAdmission {
    create_general_solver_admission(
        RuntimeResourcePolicy::agent_only(checks * STRESS_CHECK_LANES, checks).unwrap(),
    )
    .unwrap()
}

async fn bind(
    pool: FixedAmbientWorkerPoolConfig,
    catalog_digit: char,
    max_level: Option<FrameworkIILevel>,
    differential: bool,
    admission: &SolverAdmission,
    cancellation: &whiel_runner::CancellationToken,
) -> whiel_runner::BoundFixedAmbientFrameworkII {
    let bound = bind_fixed_ambient_framework_ii(
        fixture_descriptor(),
        pool,
        catalog_digit.to_string().repeat(64),
        // The run's host limits are its single source; this suite declares
        // only the level bound it wants and leaves every other limit unset.
        HostLimits {
            level_bound: max_level.map(FrameworkIILevel::get),
            ..HostLimits::UNBOUNDED
        },
        false,
        AgentToolPolicy::default(),
        admission,
        cancellation,
    )
    .await
    .expect("bind the checked-in fixed-ambient fixture");
    assert_eq!(bound.task().identity().canonical_id(), "Example0001");
    // Pass 7.5d: every live suite runs the differential safety net, so a
    // controller-assembled problem that differs from the worker's own
    // `prepare_exact_obligation` output fails the run. This measurement
    // also runs the same scenario with it off, because the differential
    // doubles the worker traffic of every check and so hides the
    // production-relevant preparation cost.
    bound.solver().set_assembly_differential(differential);
    bound
}

fn certification_profiles() -> FrameworkIICertificationProfiles {
    let invocation = |profile: &str| {
        SolverInvocationIdentity::from_parts(
            Arc::from("vampire"),
            Arc::from("fixture-leancheck"),
            Arc::from("/fixture/pinned-vampire"),
            Arc::from("a".repeat(64)),
            Arc::from(std::env::consts::OS),
            Arc::from(std::env::consts::ARCH),
            vec![Arc::from(profile)],
        )
        .unwrap()
    };
    let profile = |kind, name: &str| {
        LeancheckCertificationProfile::new(
            kind,
            format!("fixture-{name}-v1"),
            invocation(name),
            None,
            "b".repeat(64),
            "c".repeat(64),
            "d".repeat(64),
            "e".repeat(64),
            "f".repeat(64),
        )
        .unwrap()
    };
    FrameworkIICertificationProfiles::new(
        profile(ProofSearchProfile::Direct, "direct"),
        profile(ProofSearchProfile::Casc2025, "casc-2025"),
    )
    .unwrap()
}

fn production_config(
    artifacts: &whiel_runner::ArtifactStore,
    admission: &SolverAdmission,
    fmb: FmbOptions,
    command: VampireWorkerCommand,
    cancellation: &whiel_runner::CancellationToken,
) -> FrameworkIIProductionCheckConfig {
    FrameworkIIProductionCheckConfig::new(
        artifacts.clone(),
        admission.clone(),
        VampireSearchBudget::finite(Duration::from_secs(5)),
        fmb,
        command,
        cancellation.clone(),
        "fixture-vampire",
        certification_profiles(),
    )
    .unwrap()
}

/// The `race-proof-fast` fake Vampire: a hanging finite-model lane races a
/// fast, small direct proof, so the solver time this check spends is a
/// known small constant dominated by process spawn, not by real search.
fn race_proof_fast_vampire() -> VampireWorkerCommand {
    VampireWorkerCommand::new(support::fake_vampire())
        .with_extra_args([
            OsString::from("--fixture"),
            OsString::from("race-proof-fast"),
        ])
        .unwrap()
}

/// The same race, with a proof lane that will not answer until `width` proof
/// lanes are alive at once. It makes concurrency a property the run must
/// exhibit rather than one the test hopes to catch: with `width` equal to the
/// configured checks, the high-water mark can only reach the budget if the run
/// really does run that many checks at the same time.
fn race_proof_barrier_vampire(directory: &Path, width: usize) -> VampireWorkerCommand {
    VampireWorkerCommand::new(support::fake_vampire())
        .with_extra_args([
            OsString::from("--fixture"),
            OsString::from("race-proof-barrier"),
            OsString::from("--barrier-dir"),
            directory.as_os_str().to_owned(),
            OsString::from("--barrier-width"),
            OsString::from(width.to_string()),
        ])
        .unwrap()
}

/// The Lean-owned admission surface has no item cap (Pass 7.7b), so the
/// whole `CORE_SIZE + CANDIDATE_SIZE`-clause synthetic slice is admitted in
/// one batch however large it is.
async fn admit(
    admission: &whiel_runner::FrameworkIIAdmissionContext,
    sources: &[String],
    solver_admission: &SolverAdmission,
    cancellation: &whiel_runner::CancellationToken,
) -> Vec<whiel_runner::ExtendedClause> {
    let outcome = admission
        .admit_clauses(sources, None, solver_admission, cancellation)
        .await
        .expect("live admission is not cancelled");
    if let Some(correction) = outcome.correction() {
        for diagnostic in correction.diagnostics() {
            eprintln!(
                "REJECTED[{:?}] code={} message={} source={:?}",
                diagnostic.item_index(),
                diagnostic.code(),
                diagnostic.message(),
                diagnostic.item_index().and_then(|index| sources.get(index)),
            );
        }
    }
    outcome
        .accepted()
        .expect("every generated clause is admissible")
        .to_vec()
}

fn register_and_enqueue(
    houdini: &mut LeveledHoudiniState,
    clauses: &[whiel_runner::ExtendedClause],
) {
    // Distinct from `tests/framework2_fixed_ambient.rs`'s copy of this
    // helper, which hardcodes batch ordinal `0`: this stress run registers
    // two batches (Core, then candidates) against the same catalog, so the
    // ordinal must advance.
    let batch_ordinal = houdini.catalog().next_batch_ordinal().unwrap();
    let registered = houdini
        .catalog()
        .register_batch(
            batch_ordinal,
            clauses
                .iter()
                .cloned()
                .map(|clause| (clause, ExtendedClauseOrigin::Submitted)),
        )
        .unwrap();
    houdini.enqueue_registered(&registered).unwrap();
}

// ------------------------------------------------------------
// Synthetic Admissible Clause Generation
// ------------------------------------------------------------
//
// Every clause below is over the fixed-ambient `Example0001` schema's three
// level-zero relations `op_zE`, `op_zT`, `op_zS` (arity 2 each, confirmed by
// the checked-in fixtures in `tests/framework2_fixed_ambient.rs`), combined
// with the admission surface's selection (`σ`), projection (`π`), and union
// (`∪`) operators. Every clause reduces to a comparison between relational
// expressions built only from these operators, which evaluate to the empty
// relation for any argument in the domain-empty finite-model instance, so
// every one of them is expected to be initialization-provable regardless of
// its exact constant `k`.

const CORE_SIZE: usize = 50;
// Reduced from the originally planned 300 candidates (with CORE_SIZE held at
// the spec's 50-clause floor): each check's worker round trip carries the
// full current committed-clause snapshot, so per-check preparation time
// grows with the committed count and total run time grows worse than
// linearly in the candidate count. Empirically, 300 candidates did not
// finish within several minutes and even 150 took ~6.75 minutes across both
// pool sizes; 100 candidates completes both pool-size runs in well under 5
// minutes (~4.3 minutes total) while still exercising the same worker-round
// trip/preparation-time/solver-time measurement this test exists to check.
const CANDIDATE_SIZE: usize = 100;
const SELECTION_TOTAL: usize = 110;
const UNION_TOTAL: usize = 20;
const PROJECTION_TOTAL: usize = 20;

fn selection_clause(k: usize) -> String {
    format!("(σ[#0 = {k}] op_zE ⊆ op_zT)")
}

fn union_clause(k: usize) -> String {
    format!("((op_zE ∪ (σ[#0 = {k}] op_zT)) ⊆ op_zS)")
}

fn projection_clause(k: usize) -> String {
    format!("((π[0,1] (σ[#1 = {k}] op_zE)) ⊆ (π[0,1] op_zT))")
}

/// Build the Core (`CORE_SIZE` committed level-zero clauses) and the
/// candidate batch (`CANDIDATE_SIZE` further clauses), all syntactically
/// distinct from each other and from the Core.
fn build_clause_set() -> (Vec<String>, Vec<String>) {
    let selection = (0..SELECTION_TOTAL)
        .map(selection_clause)
        .collect::<Vec<_>>();
    let union = (0..UNION_TOTAL).map(union_clause).collect::<Vec<_>>();
    let projection = (0..PROJECTION_TOTAL)
        .map(projection_clause)
        .collect::<Vec<_>>();

    let core = selection[..CORE_SIZE].to_vec();
    let mut candidates = selection[CORE_SIZE..].to_vec();
    candidates.extend(union);
    candidates.extend(projection);
    assert_eq!(core.len(), CORE_SIZE);
    assert_eq!(candidates.len(), CANDIDATE_SIZE);
    (core, candidates)
}

fn evidence_of(outcome: &FrameworkIICheckOutcome) -> &FrameworkIICheckEvidence {
    match outcome {
        FrameworkIICheckOutcome::Proved(evidence) | FrameworkIICheckOutcome::Refuted(evidence) => {
            evidence
        }
        FrameworkIICheckOutcome::Inconclusive { progress, .. } => progress,
    }
}

fn mean_and_p95(mut samples: Vec<Duration>) -> (Duration, Duration) {
    if samples.is_empty() {
        return (Duration::ZERO, Duration::ZERO);
    }
    let total: Duration = samples.iter().sum();
    let mean = total / u32::try_from(samples.len()).unwrap_or(1);
    samples.sort_unstable();
    let rank = ((samples.len() as f64) * 0.95).ceil() as usize;
    let index = rank.saturating_sub(1).min(samples.len() - 1);
    (mean, samples[index])
}

// ------------------------------------------------------------
// Stress Run
// ------------------------------------------------------------

struct StressRun {
    pool_workers: usize,
    /// Checks the run was configured to have in flight at once.
    configured_checks: usize,
    /// The most it ever did have, read off the run's own admission.
    observed_checks: usize,
    differential: bool,
    checks_issued: usize,
    dictionary_hits: u64,
    preparation_time_total: Duration,
    solver_time_total: Duration,
    /// Checks that prepared an obligation of their own, rather than being
    /// answered from the dictionary or closed by a protected theorem.
    preparations_total: u64,
    /// Worker round trips the run's opaque-piece cache actually made over
    /// the candidate batch: clause, task and support fetches together. Most
    /// preparations make none of these.
    worker_round_trips_total: u64,
    wall_time: Duration,
    preparation_time_mean: Duration,
    preparation_time_p95: Duration,
    /// Pass 7.5d: sweeps dispatched as one batch, and the largest number of
    /// launches the run ever had in flight at one instant. `max_in_flight`
    /// of one would mean batching bought no overlap at all.
    batches: u64,
    concurrent_batches: u64,
    max_in_flight: usize,
    epochs: u64,
    proved: usize,
    refuted: usize,
    inconclusive: usize,
}

impl StressRun {
    fn wall_per_epoch(&self) -> Duration {
        self.wall_time / u32::try_from(self.epochs.max(1)).unwrap_or(1)
    }

    fn wall_per_check(&self) -> Duration {
        self.wall_time / u32::try_from(self.checks_issued.max(1)).unwrap_or(1)
    }
}

async fn run_stress(pool_workers: usize, catalog_digit: char, differential: bool) -> StressRun {
    run_stress_with(pool_workers, catalog_digit, differential, None).await
}

async fn run_stress_with(
    pool_workers: usize,
    catalog_digit: char,
    differential: bool,
    barrier: Option<PathBuf>,
) -> StressRun {
    let solver_admission = agent_admission(pool_workers);
    let cancellation = whiel_runner::CancellationToken::new();
    let bound = bind(
        worker_pool(pool_workers),
        catalog_digit,
        None,
        differential,
        &solver_admission,
        &cancellation,
    )
    .await;
    let (task, admission, solver, mut houdini) = bound.into_parts();
    let directory = support::TestDir::new(&format!("preparation-stress-{catalog_digit}"));
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();

    let (core_sources, candidate_sources) = build_clause_set();
    let mut all_sources = core_sources.clone();
    all_sources.extend(candidate_sources.clone());
    assert_eq!(
        all_sources.iter().collect::<BTreeSet<_>>().len(),
        all_sources.len(),
        "every generated clause must be syntactically distinct"
    );

    let accepted = admit(&admission, &all_sources, &solver_admission, &cancellation).await;
    assert_eq!(
        accepted.len(),
        all_sources.len(),
        "every generated clause must admit"
    );
    let (core_accepted, candidate_accepted) = accepted.split_at(CORE_SIZE);

    let prover = match &barrier {
        Some(directory) => race_proof_barrier_vampire(directory, pool_workers),
        None => race_proof_fast_vampire(),
    };
    let mut checker = solver.clone().production_checker(production_config(
        &artifacts,
        &solver_admission,
        FmbOptions::default(),
        prover,
        &cancellation,
    ));

    register_and_enqueue(&mut houdini, core_accepted);
    let core_outcome = stabilize_leveled_houdini(&mut houdini, &mut checker)
        .await
        .unwrap();
    assert!(
        matches!(core_outcome, LeveledStabilizationOutcome::Stabilized(_)),
        "the Core batch must stabilize, got {core_outcome:?}"
    );
    assert!(
        houdini.committed_levels().len() >= CORE_SIZE,
        "the Core batch must commit at least {CORE_SIZE} clauses, got {}",
        houdini.committed_levels().len()
    );

    let base_rows = houdini.attempts().rows().len();
    let base_preparation_total = houdini.preparation_time_total();
    let base_solver_total = houdini.solver_time_total();
    let base_preparations = houdini.preparations_total();
    let base_round_trips = solver.piece_cache_stats().worker_round_trips();
    let base_semantic_reuses = checker.semantic_reuses_total();

    register_and_enqueue(&mut houdini, candidate_accepted);
    let wall_started = Instant::now();
    let candidate_outcome = stabilize_leveled_houdini(&mut houdini, &mut checker)
        .await
        .unwrap();
    let wall_time = wall_started.elapsed();
    assert!(
        matches!(
            candidate_outcome,
            LeveledStabilizationOutcome::Stabilized(_)
        ),
        "the candidate batch must stabilize, got {candidate_outcome:?}"
    );

    let preparation_time_total = houdini.preparation_time_total() - base_preparation_total;
    let solver_time_total = houdini.solver_time_total() - base_solver_total;
    let preparations_total = houdini.preparations_total() - base_preparations;
    let worker_round_trips_total =
        solver.piece_cache_stats().worker_round_trips() - base_round_trips;
    let dictionary_hits = checker.semantic_reuses_total() - base_semantic_reuses;

    let candidate_rows = houdini.attempts().rows().get(base_rows..).unwrap_or(&[]);
    let checks_issued = candidate_rows
        .iter()
        .filter(|row| matches!(row, LevelLedgerRow::Attempt(_)))
        .count();
    let preparation_samples = candidate_rows
        .iter()
        .filter_map(|row| match row {
            LevelLedgerRow::Attempt(attempt) => Some(evidence_of(attempt.outcome())),
            LevelLedgerRow::Invalidation(_) => None,
        })
        .filter_map(FrameworkIICheckEvidence::preparation_time)
        .collect::<Vec<_>>();
    let (preparation_time_mean, preparation_time_p95) = mean_and_p95(preparation_samples);
    let mut proved = 0;
    let mut refuted = 0;
    let mut inconclusive = 0;
    for row in candidate_rows {
        if let LevelLedgerRow::Attempt(attempt) = row {
            match attempt.outcome() {
                FrameworkIICheckOutcome::Proved(_) => proved += 1,
                FrameworkIICheckOutcome::Refuted(_) => refuted += 1,
                FrameworkIICheckOutcome::Inconclusive { reason, .. } => {
                    inconclusive += 1;
                    // Diagnostic only. This scenario expects every check to
                    // prove; an inconclusive one means the machine was busy
                    // enough for a solver launch to time out, which drops
                    // its clause and restarts the sweep, so the run is no
                    // longer the same workload as its pool-size peer.
                    if inconclusive <= 5 {
                        eprintln!(
                            "framework2_preparation_stress: inconclusive pool={pool_workers} \
                             differential={differential} reason={reason:?} role={:?} level={}",
                            attempt.request().role(),
                            attempt.request().level().get()
                        );
                    }
                }
            }
        }
    }
    let batches = checker.batches_total();
    let concurrent_batches = checker.concurrent_batches_total();
    let max_in_flight = checker.max_in_flight_launches();
    // The candidate batch is one epoch of this measurement: one call to
    // `stabilize_leveled_houdini`.
    let epochs = 1;

    let observed_checks = solver_admission.max_simultaneous_solver_grants();

    solver.shutdown().await.unwrap();
    owner.settle().unwrap();

    StressRun {
        pool_workers,
        configured_checks: pool_workers,
        observed_checks,
        differential,
        checks_issued,
        dictionary_hits,
        preparation_time_total,
        solver_time_total,
        preparations_total,
        worker_round_trips_total,
        wall_time,
        preparation_time_mean,
        preparation_time_p95,
        batches,
        concurrent_batches,
        max_in_flight,
        epochs,
        proved,
        refuted,
        inconclusive,
    }
}

fn as_ms(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1000.0
}

/// `--workers N` runs N checks at once, proved rather than observed.
///
/// The prover will not answer until N proof lanes are alive at the same
/// instant, so a run that cannot reach N concurrent checks cannot reach a
/// high-water mark of N either. That makes the assertion structural at every
/// pool size, including the regression this milestone exists to prevent — a
/// four-check budget that behaves like a one-check budget, which here fails
/// rather than merely measuring the same wall time.
#[tokio::test(flavor = "multi_thread", worker_threads = 8)]
async fn concurrency_reaches_the_configured_budget_at_every_pool_size() {
    let barrier_root = support::TestDir::new("preparation-stress-barrier");
    for (checks, digit) in [(1usize, '1'), (2, '2'), (4, '3')] {
        let directory = barrier_root.path().join(format!("width-{checks}"));
        std::fs::create_dir_all(&directory).unwrap();
        let run = run_stress_with(checks, digit, false, Some(directory)).await;
        assert_eq!(
            run.inconclusive, 0,
            "the barrier answers well inside the search allowance (checks={checks})"
        );
        assert_eq!(
            run.observed_checks, checks,
            "a budget of {checks} concurrent checks must be reached and never \
             exceeded: observed={}",
            run.observed_checks
        );
        println!(
            "framework2_preparation_stress: barrier checks={checks} \
             observed={} issued={} wall_per_check_ms={:.2}",
            run.observed_checks,
            run.checks_issued,
            as_ms(run.wall_per_check()),
        );
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn preparation_time_stress_across_worker_pool_sizes() {
    // The suite requires the differential safety net, so the measurement it
    // gates on runs with it on. It also runs with it off, because the
    // differential asks the worker to re-prepare every obligation the
    // controller assembled — roughly doubling this scenario's worker
    // traffic — and the production path never does that.
    let single = run_stress(1, '7', true).await;
    let pooled = run_stress(4, '8', true).await;
    let single_production = run_stress(1, 'c', false).await;
    let pooled_production = run_stress(4, 'd', false).await;

    for run in [&single, &pooled, &single_production, &pooled_production] {
        assert!(
            run.checks_issued > 0,
            "the candidate batch must issue checks"
        );
        assert!(
            run.preparations_total > 0,
            "the candidate batch must perform fresh obligation preparations"
        );
        assert!(
            run.worker_round_trips_total > 0,
            "the candidate clauses are new, so their pieces must be fetched"
        );
        assert!(
            run.preparation_time_total > Duration::ZERO,
            "measured preparation time must be positive"
        );
        assert!(
            run.batches > 0,
            "every sweep of a level reaches the checker as one batch"
        );
        println!(
            "framework2_preparation_stress: pool={} differential={} core={CORE_SIZE} \
             candidates={CANDIDATE_SIZE} checks_issued={} dictionary_hits={} \
             preparation_total_ms={:.1} solver_total_ms={:.1} preparations={} \
             worker_round_trips={} wall_ms={:.1} wall_per_epoch_ms={:.1} \
             wall_per_check_ms={:.2} \
             preparation_mean_ms={:.2} preparation_p95_ms={:.2} batches={} \
             concurrent_batches={} max_in_flight={} configured_checks={} \
             observed_checks={} proved={} refuted={} inconclusive={}",
            run.pool_workers,
            run.differential,
            run.checks_issued,
            run.dictionary_hits,
            as_ms(run.preparation_time_total),
            as_ms(run.solver_time_total),
            run.preparations_total,
            run.worker_round_trips_total,
            as_ms(run.wall_time),
            as_ms(run.wall_per_epoch()),
            as_ms(run.wall_per_check()),
            as_ms(run.preparation_time_mean),
            as_ms(run.preparation_time_p95),
            run.batches,
            run.concurrent_batches,
            run.max_in_flight,
            run.configured_checks,
            run.observed_checks,
            run.proved,
            run.refuted,
            run.inconclusive,
        );
    }

    // What this gate asserts is structural, and it is asserted for every run
    // rather than only when the machine happened to cooperate.
    //
    // 1. Overlap. A sweep dispatches its launches as one batch, so a batch
    //    with more than one launch must have more than one in flight.
    //
    // 2. The budget. A run configured for N concurrent checks must actually
    //    reach N: the observed maximum is read off the run's own admission,
    //    where one check holds one solver lease for its whole solver work. A
    //    run that never reached its budget was gated by something other than
    //    the budget, which is exactly the defect this gate exists to catch.
    //
    // 3. Equal work. The two pool sizes run the same lane policy and derive
    //    their Vampire budget by the same rule, so they must issue the same
    //    checks, and none may come back inconclusive — an inconclusive launch
    //    drops its clause and restarts the sweep, which would silently make
    //    the two runs different workloads.
    for run in [&single, &pooled, &single_production, &pooled_production] {
        assert!(
            run.concurrent_batches > 0,
            "every sweep of this scenario has more than one launch to dispatch"
        );
        assert!(
            run.max_in_flight > 1,
            "a batch must overlap its launches (pool={} differential={}): {}",
            run.pool_workers,
            run.differential,
            run.max_in_flight
        );
        // The bound always holds. That the run *reaches* the bound is a
        // property of how fast the stand-in answers relative to dispatch, so it
        // is proved deterministically by
        // `concurrency_reaches_the_configured_budget_at_every_pool_size` with a
        // barrier prover, and only reported here.
        assert!(
            run.observed_checks <= run.configured_checks,
            "a run may never exceed the simultaneous checks it configured \
             (pool={} differential={}): observed={} configured={}",
            run.pool_workers,
            run.differential,
            run.observed_checks,
            run.configured_checks
        );
        assert_eq!(
            run.inconclusive, 0,
            "every check of this scenario proves (pool={} differential={}); an \
             inconclusive launch drops its clause and restarts the sweep",
            run.pool_workers, run.differential
        );
    }
    let mut pool_comparisons = Vec::new();
    for (single, pooled) in [(&single, &pooled), (&single_production, &pooled_production)] {
        assert_eq!(
            single.checks_issued, pooled.checks_issued,
            "the two pool sizes must issue the same checks (differential={})",
            pooled.differential
        );
        // Timing is reported, not asserted. Wall time per check is the fair
        // comparison between the two widths, but on a shared machine it is a
        // property of the load, not of the code, so the ratio is recorded as
        // evidence and left to a reader.
        let ratio = single.wall_per_check().as_secs_f64() / pooled.wall_per_check().as_secs_f64();
        println!(
            "framework2_preparation_stress: pool comparison (differential={}): \
             checks1={:.2}ms checks4={:.2}ms ratio={ratio:.2}",
            pooled.differential,
            as_ms(single.wall_per_check()),
            as_ms(pooled.wall_per_check()),
        );
        pool_comparisons.push(json!({
            "assembly_differential": pooled.differential,
            "pool_comparison": "reported",
            "pool1_wall_time_per_check_ms": as_ms(single.wall_per_check()),
            "pool4_wall_time_per_check_ms": as_ms(pooled.wall_per_check()),
            "wall_time_per_check_ratio": ratio,
        }));
    }

    let runs = [&single, &pooled, &single_production, &pooled_production]
        .into_iter()
        .map(|run| {
            json!({
                "pool_workers": run.pool_workers,
                "assembly_differential": run.differential,
                "checks_issued": run.checks_issued,
                "dictionary_hits": run.dictionary_hits,
                "preparation_time_total_ms": as_ms(run.preparation_time_total),
                "solver_time_total_ms": as_ms(run.solver_time_total),
                "preparations_total": run.preparations_total,
                "worker_round_trips_total": run.worker_round_trips_total,
                "wall_time_ms": as_ms(run.wall_time),
                "wall_time_per_epoch_ms": as_ms(run.wall_per_epoch()),
                "wall_time_per_check_ms": as_ms(run.wall_per_check()),
                "preparation_time_mean_ms": as_ms(run.preparation_time_mean),
                "preparation_time_p95_ms": as_ms(run.preparation_time_p95),
                "batches": run.batches,
                "concurrent_batches": run.concurrent_batches,
                "max_in_flight_launches": run.max_in_flight,
                "configured_simultaneous_checks": run.configured_checks,
                "observed_simultaneous_checks": run.observed_checks,
                "epochs": run.epochs,
                "proved": run.proved,
                "refuted": run.refuted,
                "inconclusive": run.inconclusive,
            })
        })
        .collect::<Vec<_>>();
    let report = json!({
        "core_size": CORE_SIZE,
        "candidate_size": CANDIDATE_SIZE,
        "runs": runs,
        "pool_comparisons": pool_comparisons,
    });
    let output_path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/preparation-stress.json");
    std::fs::create_dir_all(output_path.parent().unwrap()).unwrap();
    std::fs::write(&output_path, serde_json::to_string_pretty(&report).unwrap()).unwrap();
    assert!(output_path.exists());
}
