mod support;

use std::collections::BTreeMap;
use std::path::PathBuf;
use std::time::{Duration, Instant};

use whiel_runner::encoding::{
    EncodingWorkerCommand, EncodingWorkerPoolConfig, SolverEncodingContext,
    new_solver_encoding_context,
};
use whiel_runner::{
    ArtifactBackendOwner, ArtifactKind, ArtifactStore, ArtifactStoreConfig, CancellationToken,
    ClauseCatalog, ClauseFormula, ClauseSet, CoverageLookup, CoverageMode, HoudiniState,
    InitializationInvocationOutcome, InitializationStatus, MaintenanceBlockOutcome,
    MaintenanceExecutionOutcome, MaintenancePreparationOutcome, RuntimeResourcePolicy,
    SolverAdmission, TrackLayout, VampireWorkerCommand, VerificationParameters, expand_core,
    new_artifact_store, new_symbolic_inv_state, prepare_maintenance, propose_symbolic_clauses,
    run_maintenance_block,
};

// ------------------------------------------------------------
// Benchmark Policy And Measurements
// ------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum ShortcutMode {
    None,
    Coverage,
    Support,
    Both,
}

impl ShortcutMode {
    const ALL: [Self; 4] = [Self::None, Self::Coverage, Self::Support, Self::Both];

    fn label(self) -> &'static str {
        match self {
            Self::None => "none",
            Self::Coverage => "coverage",
            Self::Support => "support",
            Self::Both => "both",
        }
    }

    fn coverage_lookup(self) -> CoverageLookup {
        match self {
            Self::None | Self::Support => CoverageLookup::IncomingEdges,
            Self::Coverage | Self::Both => CoverageLookup::LiteralSubsetThenIncoming,
        }
    }

    fn installs_support(self) -> bool {
        matches!(self, Self::Support | Self::Both)
    }

    fn expected_queries(self) -> usize {
        match self {
            Self::None => 2,
            Self::Coverage | Self::Support | Self::Both => 1,
        }
    }
}

#[derive(Clone, Debug)]
struct Sample {
    shortcut_setup: Duration,
    plan_preparation: Duration,
    block_execution: Duration,
    queried_targets: usize,
    core: Vec<String>,
}

impl Sample {
    fn total(&self) -> Duration {
        self.shortcut_setup + self.plan_preparation + self.block_execution
    }
}

#[derive(Clone, Copy, Debug)]
struct Distribution {
    minimum: f64,
    first_quartile: f64,
    median: f64,
    third_quartile: f64,
    maximum: f64,
}

fn milliseconds(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1_000.0
}

fn percentile(values: &[f64], fraction: f64) -> f64 {
    assert!(!values.is_empty());
    let mut ordered = values.to_vec();
    ordered.sort_by(f64::total_cmp);
    let rank = fraction * (ordered.len() - 1) as f64;
    let lower = rank.floor() as usize;
    let upper = rank.ceil() as usize;
    if lower == upper {
        ordered[lower]
    } else {
        let weight = rank - lower as f64;
        ordered[lower] * (1.0 - weight) + ordered[upper] * weight
    }
}

fn distribution(values: &[f64]) -> Distribution {
    Distribution {
        minimum: percentile(values, 0.0),
        first_quartile: percentile(values, 0.25),
        median: percentile(values, 0.5),
        third_quartile: percentile(values, 0.75),
        maximum: percentile(values, 1.0),
    }
}

fn print_distribution(mode: ShortcutMode, metric: &str, values: &[f64]) {
    let summary = distribution(values);
    println!(
        "BENCH_SUMMARY mode={} metric={} min_ms={:.3} q1_ms={:.3} median_ms={:.3} q3_ms={:.3} max_ms={:.3}",
        mode.label(),
        metric,
        summary.minimum,
        summary.first_quartile,
        summary.median,
        summary.third_quartile,
        summary.maximum,
    );
}

fn print_paired_summary(baseline: &[Sample], mode: ShortcutMode, samples: &[Sample]) {
    assert_eq!(baseline.len(), samples.len());
    let saved = baseline
        .iter()
        .zip(samples)
        .map(|(off, shortcut)| milliseconds(off.total()) - milliseconds(shortcut.total()))
        .collect::<Vec<_>>();
    let ratios = baseline
        .iter()
        .zip(samples)
        .map(|(off, shortcut)| off.total().as_secs_f64() / shortcut.total().as_secs_f64())
        .collect::<Vec<_>>();
    let wins = baseline
        .iter()
        .zip(samples)
        .filter(|(off, shortcut)| shortcut.total() < off.total())
        .count();
    let saved = distribution(&saved);
    let ratios = distribution(&ratios);
    println!(
        "BENCH_PAIRED mode={} pairs={} wins={} median_saved_ms={:.3} q1_saved_ms={:.3} q3_saved_ms={:.3} median_speedup={:.3} q1_speedup={:.3} q3_speedup={:.3}",
        mode.label(),
        samples.len(),
        wins,
        saved.median,
        saved.first_quartile,
        saved.third_quartile,
        ratios.median,
        ratios.first_quartile,
        ratios.third_quartile,
    );
}

fn configured_count(variable: &str, default: usize) -> usize {
    std::env::var(variable)
        .ok()
        .and_then(|value| value.parse::<usize>().ok())
        .filter(|value| *value > 0)
        .unwrap_or(default)
}

fn is_structural_atom(value: &serde_json::Value) -> bool {
    let Some(parts) = value.as_array() else {
        return false;
    };
    match parts.as_slice() {
        [tag, _, _] => tag
            .as_str()
            .is_some_and(|tag| matches!(tag, "eq" | "subset")),
        [tag, _] => tag.as_str().is_some_and(|tag| {
            matches!(
                tag,
                "eq_empty_right" | "eq_empty_left" | "subset_empty_right" | "subset_empty_left"
            )
        }),
        _ => false,
    }
}

fn assert_benchmark_formula_shapes(formulas: &[ClauseFormula; 2]) {
    let false_identity: serde_json::Value =
        serde_json::from_str(formulas[0].identity()).expect("structural false identity");
    assert_eq!(false_identity, serde_json::json!(["false"]));
    assert!(formulas[0].source().source_id().contains(":v3:s0:o0"));

    let singleton_identity: serde_json::Value =
        serde_json::from_str(formulas[1].identity()).expect("structural singleton identity");
    let is_singleton = is_structural_atom(&singleton_identity)
        || singleton_identity
            .as_array()
            .is_some_and(|parts| matches!(parts.as_slice(), [tag, atom] if tag == "not" && is_structural_atom(atom)));
    assert!(
        is_singleton,
        "stage-one benchmark target must be exactly one structural literal: {singleton_identity}"
    );
    assert!(formulas[1].source().source_id().contains(":v3:s1:o"));
}

// ------------------------------------------------------------
// Shared Real-Vampire Harness
// ------------------------------------------------------------

struct BenchmarkHarness {
    _directory: support::TestDir,
    task: whiel_runner::SynthesisTask,
    owner: ArtifactBackendOwner,
    artifacts: ArtifactStore,
    admission: SolverAdmission,
    verification: VerificationParameters,
    vampire: VampireWorkerCommand,
}

impl BenchmarkHarness {
    async fn new() -> Self {
        let executable = std::env::var_os("VAMPIRE_BIN")
            .map(PathBuf::from)
            .unwrap_or_else(|| PathBuf::from("/opt/vampire/build/vampire"));
        assert!(
            executable.is_file(),
            "set VAMPIRE_BIN to the real Vampire executable; missing {}",
            executable.display()
        );

        let directory = support::TestDir::new("phase4a_shortcut_benchmark");
        let task = support::export_canonical_task();
        let (owner, artifacts) = new_artifact_store(
            &task,
            ArtifactStoreConfig::new(directory.path().join("artifacts")),
        )
        .expect("create benchmark ArtifactStore");
        let resources = RuntimeResourcePolicy::symbolic(4, 2, 2).expect("valid symbolic policy");
        let (admission, _cex) =
            whiel_runner::create_symbolic_solver_admissions(resources).expect("INV admission");
        let verification = VerificationParameters::new(Duration::from_secs(30), resources)
            .expect("positive search limit")
            .with_bulk_init_limit(Duration::ZERO)
            .with_bulk_maint_limit(Duration::ZERO)
            .with_maintenance_retry_increments(Vec::new())
            .expect("empty retry schedule");
        Self {
            _directory: directory,
            task,
            owner,
            artifacts,
            admission,
            verification,
            vampire: VampireWorkerCommand::new(executable),
        }
    }

    async fn sample(&self, mode: ShortcutMode) -> Sample {
        // Entailment proofs are intentionally cached within one encoding
        // context in production. Give every measured sample a fresh context
        // so it must launch real Vampire rather than reuse a prior proof.
        let worker_config = EncodingWorkerPoolConfig::new(
            EncodingWorkerCommand::new(
                support::example_encoding_worker(),
                support::repository_root(),
            ),
            2,
        )
        .expect("positive worker count");
        let context = new_solver_encoding_context(&self.task, &self.artifacts, worker_config)
            .expect("create sample encoding context");
        let cancellation = CancellationToken::new();

        // Enumerate outside the timed region. The resulting clauses are exact
        // Lean-owned stage-0 false and stage-1 singleton formulas.
        let mut seed = new_symbolic_inv_state(
            &self.task,
            context.clone(),
            &self.artifacts,
            self.verification.clone(),
            self.admission.clone(),
            false,
            false,
        )
        .expect("create proposal seed");
        propose_symbolic_clauses(&mut seed, &cancellation)
            .await
            .expect("enumerate stage zero");
        propose_symbolic_clauses(&mut seed, &cancellation)
            .await
            .expect("enumerate stage one");
        assert!(seed.proposal().len() >= 2);
        let formulas = [seed.proposal()[0].clone(), seed.proposal()[1].clone()];
        assert_ne!(formulas[0].identity(), formulas[1].identity());
        assert_benchmark_formula_shapes(&formulas);
        drop(seed);

        // Warm only formula, WP, guard, and support encodings. Do not run a
        // maintenance query here: the context's proof cache must remain empty.
        let mut warm_state = self.prepare_unmeasured_state(&context, &formulas).await;
        assert!(matches!(
            prepare_maintenance(&self.task, &mut warm_state, &cancellation).await,
            MaintenancePreparationOutcome::Complete
        ));
        context
            .prepare_loop_guard_body(&self.admission, &self.artifacts, &cancellation)
            .await
            .expect("warm loop-guard body");
        context
            .prepare_support_block(
                &self.admission,
                &self.artifacts,
                std::iter::empty(),
                &cancellation,
            )
            .await
            .expect("warm schema support block");
        drop(warm_state);

        let catalog = ClauseCatalog::new(&self.task, context.clone(), &self.artifacts)
            .expect("fresh benchmark Catalog");
        let mut state = HoudiniState::new(
            &self.task,
            self.verification.clone(),
            self.admission.clone(),
            catalog,
        )
        .expect("fresh benchmark Houdini state");
        // Initialization is deliberately supplied, not measured. This test
        // isolates the maintenance cost of sound support/coverage shortcuts.
        assert!(matches!(
            state
                .prepare_init_candidates(
                    formulas.iter().cloned(),
                    &ClauseSet::new(),
                    &cancellation,
                )
                .await,
            InitializationInvocationOutcome::Complete
        ));
        let false_id = state
            .catalog()
            .find(&formulas[0])
            .expect("lookup false clause")
            .expect("false clause was registered");
        let target_id = state
            .catalog()
            .find(&formulas[1])
            .expect("lookup singleton clause")
            .expect("singleton clause was registered");
        let candidate = ClauseSet::from([false_id, target_id]);
        state
            .retain_init_candidates(candidate.clone())
            .expect("retain exact benchmark Candidate");
        let evidence = state
            .catalog()
            .artifacts()
            .publish(
                ArtifactKind::InitializationCheck,
                b"Phase 4A maintenance-only wall-clock benchmark"
                    .as_slice()
                    .into(),
            )
            .expect("publish synthetic initialization evidence");
        for clause in &candidate {
            state
                .catalog()
                .record_initialization(*clause, InitializationStatus::InitProved, evidence)
                .expect("record benchmark InitProved");
        }

        let setup_started = Instant::now();
        state
            .set_maintenance_schedule_policy(
                CoverageMode::UseProducerClosed,
                TrackLayout::SingleTrack,
                mode.coverage_lookup(),
            )
            .expect("select benchmark maintenance policy");
        if mode.installs_support() {
            // MaintSupport_∅(false, target) is sound: Step({false}, target)
            // holds vacuously. The relation therefore adds no solver query.
            state
                .insert_maint_support(false_id, target_id)
                .expect("install sound benchmark MaintSupport");
        }
        let shortcut_setup = setup_started.elapsed();

        let preparation_started = Instant::now();
        let preparation = prepare_maintenance(&self.task, &mut state, &cancellation).await;
        let plan_preparation = preparation_started.elapsed();
        assert!(matches!(
            preparation,
            MaintenancePreparationOutcome::Complete
        ));
        assert!(state.maintenance_failure().is_none());

        let execution_started = Instant::now();
        let outcome =
            run_maintenance_block(&self.task, &mut state, self.vampire.clone(), &cancellation)
                .await;
        let block_execution = execution_started.elapsed();
        let MaintenanceExecutionOutcome::Complete(block) = outcome else {
            panic!("real-Vampire benchmark block did not complete: {outcome:#?}");
        };
        assert_eq!(block.outcome(), MaintenanceBlockOutcome::Stable);
        assert_eq!(block.known_live(), &candidate);

        let queried_targets = candidate
            .iter()
            .filter(|clause| {
                state
                    .catalog()
                    .record(**clause)
                    .expect("benchmark ClauseRecord")
                    .latest_maintenance()
                    .is_some()
            })
            .count();
        assert_eq!(queried_targets, mode.expected_queries());

        expand_core(&mut state, &block).expect("expand benchmark Core");
        let mut core = state
            .core()
            .iter()
            .map(|clause| {
                state
                    .catalog()
                    .record(*clause)
                    .expect("benchmark Core record")
                    .formula()
                    .identity()
                    .to_owned()
            })
            .collect::<Vec<_>>();
        core.sort();
        assert_eq!(core.len(), 2);

        let sample = Sample {
            shortcut_setup,
            plan_preparation,
            block_execution,
            queried_targets,
            core,
        };
        drop(state);
        context
            .shutdown()
            .await
            .expect("stop sample encoding workers");
        drop(context);
        sample
    }

    async fn prepare_unmeasured_state(
        &self,
        context: &SolverEncodingContext,
        formulas: &[ClauseFormula; 2],
    ) -> HoudiniState {
        let catalog = ClauseCatalog::new(&self.task, context.clone(), &self.artifacts)
            .expect("fresh warmup Catalog");
        let mut state = HoudiniState::new(
            &self.task,
            self.verification.clone(),
            self.admission.clone(),
            catalog,
        )
        .expect("fresh warmup Houdini state");
        let cancellation = CancellationToken::new();
        assert!(matches!(
            state
                .prepare_init_candidates(
                    formulas.iter().cloned(),
                    &ClauseSet::new(),
                    &cancellation,
                )
                .await,
            InitializationInvocationOutcome::Complete
        ));
        let candidates = state.init_candidates().clone();
        let evidence = state
            .catalog()
            .artifacts()
            .publish(
                ArtifactKind::InitializationCheck,
                b"Phase 4A benchmark encoding warmup".as_slice().into(),
            )
            .expect("publish warmup initialization evidence");
        for clause in &candidates {
            state
                .catalog()
                .record_initialization(*clause, InitializationStatus::InitProved, evidence)
                .expect("record warmup InitProved");
        }
        state
    }

    async fn shutdown(self) {
        drop(self.artifacts);
        self.owner.settle().expect("settle benchmark artifacts");
    }
}

// ------------------------------------------------------------
// Repeated Paired Benchmark
// ------------------------------------------------------------

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
#[ignore = "requires real Vampire and measures wall-clock performance"]
async fn real_vampire_coverage_and_support_wall_clock() {
    let rounds = configured_count("WHIEL_BENCH_ROUNDS", 12);
    let warmups = configured_count("WHIEL_BENCH_WARMUPS", 2);
    let harness = BenchmarkHarness::new().await;

    // Fill Lean formula/WP/support caches and warm the Vampire executable and
    // filesystem before collecting steady-state samples.
    for _ in 0..warmups {
        for mode in ShortcutMode::ALL {
            let _ = harness.sample(mode).await;
        }
    }

    let mut samples = BTreeMap::<ShortcutMode, Vec<Sample>>::new();
    for round in 0..rounds {
        let mut order = ShortcutMode::ALL;
        if round % 2 == 1 {
            order.reverse();
        }
        for mode in order {
            let sample = harness.sample(mode).await;
            println!(
                "BENCH_SAMPLE round={} mode={} setup_ms={:.3} prepare_ms={:.3} execute_ms={:.3} total_ms={:.3} queried_targets={}",
                round,
                mode.label(),
                milliseconds(sample.shortcut_setup),
                milliseconds(sample.plan_preparation),
                milliseconds(sample.block_execution),
                milliseconds(sample.total()),
                sample.queried_targets,
            );
            samples.entry(mode).or_default().push(sample);
        }
    }

    let baseline = samples.get(&ShortcutMode::None).expect("baseline samples");
    let expected_core = &baseline[0].core;
    for mode in ShortcutMode::ALL {
        let mode_samples = samples.get(&mode).expect("complete mode samples");
        assert_eq!(mode_samples.len(), rounds);
        assert!(
            mode_samples
                .iter()
                .all(|sample| &sample.core == expected_core)
        );
        print_distribution(
            mode,
            "setup",
            &mode_samples
                .iter()
                .map(|sample| milliseconds(sample.shortcut_setup))
                .collect::<Vec<_>>(),
        );
        print_distribution(
            mode,
            "prepare",
            &mode_samples
                .iter()
                .map(|sample| milliseconds(sample.plan_preparation))
                .collect::<Vec<_>>(),
        );
        print_distribution(
            mode,
            "execute",
            &mode_samples
                .iter()
                .map(|sample| milliseconds(sample.block_execution))
                .collect::<Vec<_>>(),
        );
        print_distribution(
            mode,
            "total",
            &mode_samples
                .iter()
                .map(|sample| milliseconds(sample.total()))
                .collect::<Vec<_>>(),
        );
        if mode != ShortcutMode::None {
            print_paired_summary(baseline, mode, mode_samples);
        }
    }

    harness.shutdown().await;
}
