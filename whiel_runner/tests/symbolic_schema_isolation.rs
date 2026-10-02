mod support;

use std::time::Duration;

use whiel_runner::encoding::{EncodingWorkerCommand, EncodingWorkerPoolConfig};
use whiel_runner::{
    CertificationBridgeCommand, CertificationRuntime, FailureKind, FailureOrigin,
    RuntimeResourcePolicy, SymbolicHoudiniPolicy, SymbolicHoudiniRuntime, SynthesisResult,
    SynthesisTask, VampireWorkerCommand, VerificationParameters, symbolic_houdini,
};

fn fixed_ambient_task() -> SynthesisTask {
    let mut manifest =
        serde_json::from_str::<serde_json::Value>(support::export_canonical_task_json())
            .expect("canonical task export");
    manifest["format_version"] = 4.into();
    let preproc = "Whiel.Benchmark.Example0012.inputPreproc";
    manifest["schema"]["expression"] = format!("{preproc}.prophecySchema").into();
    manifest["preprocessed"]["pre"]["expression"] =
        format!("{preproc}.liftedLoop.preAssert").into();
    manifest["preprocessed"]["command"]["expression"] = format!("{preproc}.liftedLoop.cmd").into();
    manifest["preprocessed"]["post"]["expression"] =
        format!("{preproc}.liftedLoop.postAssert").into();
    manifest["solver"]["preprocessed_pre"]["expression"] =
        format!("{preproc}.liftedLoop.preAssert").into();
    manifest["solver"]["preprocessed_pre"]["no_bound_expression"] =
        format!("{preproc}.liftedLoop.preAssert_noBound").into();
    manifest["solver"]["preprocessed_post"]["expression"] =
        format!("{preproc}.liftedLoop.postAssert").into();
    manifest["solver"]["preprocessed_post"]["no_bound_expression"] =
        format!("{preproc}.liftedLoop.postAssert_noBound").into();
    SynthesisTask::from_fixed_ambient_json(&serde_json::to_string(&manifest).expect("task JSON"))
        .expect("fixed-ambient task")
}

fn unavailable_runtime(directory: &support::TestDir) -> SymbolicHoudiniRuntime {
    let repository = support::repository_root();
    let unavailable = directory.path().join("must-not-run");
    let encoding_workers =
        EncodingWorkerPoolConfig::new(EncodingWorkerCommand::new(&unavailable, &repository), 1)
            .expect("positive worker count");
    let certification = CertificationRuntime::new(
        CertificationBridgeCommand::new(&unavailable, &repository),
        directory.path().join("certification-work"),
        directory.path().join("solution"),
    );
    SymbolicHoudiniRuntime::new(
        directory.path().join("artifacts"),
        encoding_workers,
        VampireWorkerCommand::new(unavailable),
        certification,
    )
}

fn verification() -> VerificationParameters {
    VerificationParameters::new(
        Duration::from_secs(1),
        RuntimeResourcePolicy::default_symbolic(),
    )
    .expect("valid symbolic resources")
}

#[test]
fn fixed_ambient_task_is_rejected_before_runtime_creation() {
    let task = fixed_ambient_task();
    let directory = support::TestDir::new("symbolic_fixed_ambient_isolation");
    let artifact_root = directory.path().join("artifacts");

    let result = symbolic_houdini(
        &task,
        Duration::from_secs(1),
        verification(),
        SymbolicHoudiniPolicy::default(),
        false,
        true,
        unavailable_runtime(&directory),
    );

    let SynthesisResult::Failure(report) = result else {
        panic!("fixed-ambient task must fail closed")
    };
    assert_eq!(report.origin(), FailureOrigin::RunControl);
    assert_eq!(report.kind(), FailureKind::InfrastructureFailure);
    assert_eq!(
        report.detail(),
        Some("Symbolic-Houdini accepts only legacy-program tasks")
    );
    assert!(
        !artifact_root.exists(),
        "schema rejection must precede artifact and worker creation"
    );
}

#[test]
fn legacy_program_task_passes_the_symbolic_schema_gate() {
    let task = support::sample_task();
    let directory = support::TestDir::new("symbolic_legacy_schema_gate");

    let result = symbolic_houdini(
        &task,
        Duration::from_secs(1),
        verification(),
        SymbolicHoudiniPolicy::default(),
        false,
        true,
        unavailable_runtime(&directory),
    );

    let SynthesisResult::Failure(report) = result else {
        panic!("unavailable worker must fail the legacy run")
    };
    // The unavailable worker surfaces through the symbolic race, not the
    // run-control schema gate that rejects fixed-ambient tasks.
    assert_ne!(report.origin(), FailureOrigin::RunControl);
    assert_ne!(
        report.detail(),
        Some("Symbolic-Houdini accepts only legacy-program tasks"),
        "legacy task must pass the schema gate and reach worker preparation"
    );
}
