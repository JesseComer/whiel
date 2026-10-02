//! Live durable coverage for `evaluate_clauses` (fixed-ambient worker
//! protocol 6, `FixedAmbientWorkerOperation::EvaluateClauses`).
//!
//! Every test binds the checked-in `Example0001` fixture through the Lean
//! `fixed_ambient_encoding_worker` executable, exactly like
//! `tests/framework2_fixed_ambient.rs` and `tests/framework2_certificate.rs`
//! (whose fixture-binding and command helpers this file copies rather than
//! sharing, since integration test binaries do not share a `tests/` module
//! tree). `evaluate_clauses` needs no admitted Core: it admits and
//! evaluates clause sources directly against caller-supplied finite
//! instances, so these tests never stabilize a Houdini state.

mod support;

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

use serde_json::Value;

use whiel_runner::encoding::{FixedAmbientWorkerCommand, FixedAmbientWorkerPoolConfig};
use whiel_runner::framework2::{ClauseEvaluationResult, EvaluationInstance, EvaluationRelation};
use whiel_runner::{
    AgentToolPolicy, CancellationToken, HostLimits, RuntimeResourcePolicy, SolverAdmission,
    bind_fixed_ambient_framework_ii, create_general_solver_admission,
};

// ------------------------------------------------------------
// Fixture Sources And Worker Commands (copied from
// tests/framework2_fixed_ambient.rs / tests/framework2_certificate.rs)
// ------------------------------------------------------------

/// Prophecy-free clause over the input's `T` row.
const ORDINARY_CLAUSE: &str = "(op_zT = \u{2205}[2])";
/// A clause mentioning the prophecy copy of `T`.
const LEVEL_ONE_CLAUSE: &str = "(yp_zT = \u{2205}[2])";

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

fn agent_admission(vampire_processes: usize, workers: usize) -> SolverAdmission {
    create_general_solver_admission(
        RuntimeResourcePolicy::agent_only(vampire_processes, workers).unwrap(),
    )
    .unwrap()
}

/// Every ambient relation of Example0001, each with a caller-supplied row
/// set: `o:p::E`, `o:p::S`, `o:p::T`, `y:p::S`, `y:p::T` (all arity 2).
/// `decodeInstance` requires a complete instance over the schema, so every
/// relation must be present even when its rows are empty.
fn interpretation(rows_for: impl Fn(&str) -> Vec<Value>) -> EvaluationInstance {
    let keys = ["o:p::E", "o:p::S", "o:p::T", "y:p::S", "y:p::T"];
    let relations = keys
        .iter()
        .map(|key| EvaluationRelation::new(*key, rows_for(key)))
        .collect();
    EvaluationInstance::new(vec!["num:1".to_string()], relations)
}

/// One edge in `E` and one edge in the prophecy copy of `T` (`T∞`), with
/// the plain `T` row itself left empty: this differentiates `ORDINARY_CLAUSE`
/// (over plain `T`, so it holds here exactly as it does on the fully empty
/// instance) from `LEVEL_ONE_CLAUSE` (over `T∞`, so it fails here but holds
/// on the fully empty instance).
fn edb_and_prophecy_interpretation() -> EvaluationInstance {
    interpretation(|key| {
        if key == "o:p::E" || key == "y:p::T" {
            vec![serde_json::json!(["num:1", "num:1"])]
        } else {
            Vec::new()
        }
    })
}

/// Every relation empty.
fn satisfying_interpretation() -> EvaluationInstance {
    interpretation(|_| Vec::new())
}

// ------------------------------------------------------------
// Live Direct Clause Evaluation
// ------------------------------------------------------------

/// Truth table over two clauses (`ORDINARY_CLAUSE` is prophecy-free, over
/// plain `T`; `LEVEL_ONE_CLAUSE` mentions the prophecy copy `T∞`) and two
/// instances (`edb_and_prophecy_interpretation`, with `T∞` populated and
/// plain `T` empty, and `satisfying_interpretation`, with every relation
/// empty). Plain `T` is empty on both instances, so `ORDINARY_CLAUSE`
/// holds throughout; `T∞` is populated only on the first, so
/// `LEVEL_ONE_CLAUSE` fails there and holds on the second.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn evaluate_clauses_reports_the_expected_truth_table() {
    let solver_admission = agent_admission(1, 1);
    let cancellation = CancellationToken::new();
    let bound = bind_fixed_ambient_framework_ii(
        fixture_descriptor(),
        worker_pool(1),
        '1'.to_string().repeat(64),
        HostLimits::UNBOUNDED,
        false,
        AgentToolPolicy::default(),
        &solver_admission,
        &cancellation,
    )
    .await
    .expect("bind the checked-in fixed-ambient fixture");
    // Pass 7.5d: every live suite runs the differential safety net.
    bound.solver().set_assembly_differential(true);
    let (_task, _admission, solver, _houdini) = bound.into_parts();

    let instances = [
        edb_and_prophecy_interpretation(),
        satisfying_interpretation(),
    ];
    let clauses = [ORDINARY_CLAUSE.to_string(), LEVEL_ONE_CLAUSE.to_string()];
    let evaluation = solver
        .evaluate_clauses(&clauses, &instances, &solver_admission, &cancellation)
        .await
        .expect("live evaluation of two admissible clauses is not cancelled");

    assert_eq!(evaluation.instances, 2);
    assert_eq!(evaluation.cost, 4);
    assert_eq!(evaluation.results.len(), 2);

    match &evaluation.results[0] {
        ClauseEvaluationResult::Evaluated { source, holds, .. } => {
            assert_eq!(source, ORDINARY_CLAUSE);
            assert_eq!(holds, &[true, true]);
        }
        other => panic!("expected the ordinary clause to evaluate, got {other:?}"),
    }
    match &evaluation.results[1] {
        ClauseEvaluationResult::Evaluated { source, holds, .. } => {
            assert_eq!(source, LEVEL_ONE_CLAUSE);
            assert_eq!(holds, &[false, true]);
        }
        other => panic!("expected the level-one clause to evaluate, got {other:?}"),
    }

    solver.shutdown().await.unwrap();
}

/// A non-admissible clause source yields a per-clause correctable entry;
/// the admissible clause alongside it still evaluates, mirroring
/// `mixedEvaluationDispatch`.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn evaluate_clauses_reports_a_correctable_entry_for_a_non_admissible_source() {
    let solver_admission = agent_admission(1, 1);
    let cancellation = CancellationToken::new();
    let bound = bind_fixed_ambient_framework_ii(
        fixture_descriptor(),
        worker_pool(1),
        '2'.to_string().repeat(64),
        HostLimits::UNBOUNDED,
        false,
        AgentToolPolicy::default(),
        &solver_admission,
        &cancellation,
    )
    .await
    .expect("bind the checked-in fixed-ambient fixture");
    // Pass 7.5d: every live suite runs the differential safety net.
    bound.solver().set_assembly_differential(true);
    let (_task, _admission, solver, _houdini) = bound.into_parts();

    let instances = [satisfying_interpretation()];
    let clauses = [ORDINARY_CLAUSE.to_string(), "not a clause".to_string()];
    let evaluation = solver
        .evaluate_clauses(&clauses, &instances, &solver_admission, &cancellation)
        .await
        .expect("a mixed admissible/correctable batch is not cancelled");

    assert_eq!(evaluation.results.len(), 2);
    match &evaluation.results[0] {
        ClauseEvaluationResult::Evaluated { holds, .. } => assert_eq!(holds, &[true]),
        other => panic!("expected the ordinary clause to evaluate, got {other:?}"),
    }
    match &evaluation.results[1] {
        ClauseEvaluationResult::Correctable { source, diagnostic } => {
            assert_eq!(source, "not a clause");
            assert!(!diagnostic.code().is_empty());
        }
        other => panic!("expected a correctable diagnostic, got {other:?}"),
    }

    solver.shutdown().await.unwrap();
}

/// Pass 7.7b: a batch larger than the removed 128/64/4096 caps is evaluated,
/// end to end, by the live Lean worker.
///
/// The old `MAX_EVALUATION_CLAUSES`, `MAX_EVALUATION_INSTANCES` and
/// `MAX_EVALUATION_COST` are gone from Rust and from
/// `FixedAmbientWorker.lean`. This asks for 130 drafts against 65 models —
/// beyond the removed per-axis caps and, at a cost of 8450, beyond the
/// removed 4096 product cap — and requires the exact result shape back.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn evaluate_clauses_serves_a_batch_beyond_the_removed_caps() {
    let solver_admission = agent_admission(1, 1);
    let cancellation = CancellationToken::new();
    let bound = bind_fixed_ambient_framework_ii(
        fixture_descriptor(),
        worker_pool(1),
        '3'.to_string().repeat(64),
        HostLimits::UNBOUNDED,
        false,
        AgentToolPolicy::default(),
        &solver_admission,
        &cancellation,
    )
    .await
    .expect("bind the checked-in fixed-ambient fixture");
    // Pass 7.5d: every live suite runs the differential safety net.
    bound.solver().set_assembly_differential(true);
    let (_task, _admission, solver, _houdini) = bound.into_parts();

    let clauses = vec![ORDINARY_CLAUSE.to_string(); 130];
    let instances = vec![satisfying_interpretation(); 65];
    let evaluation = solver
        .evaluate_clauses(&clauses, &instances, &solver_admission, &cancellation)
        .await
        .expect("no clause, instance, or cost bound refuses this batch");
    assert_eq!(evaluation.results.len(), 130);
    assert_eq!(evaluation.instances, 65);
    assert_eq!(evaluation.cost, 130 * 65);
    for result in evaluation.results {
        match result {
            ClauseEvaluationResult::Evaluated { holds, .. } => {
                assert_eq!(holds.len(), 65);
            }
            other => panic!("every draft is admissible, got {other:?}"),
        }
    }

    solver.shutdown().await.unwrap();
}
