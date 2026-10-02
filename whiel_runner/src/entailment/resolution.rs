//! Resolution of untrusted entailment counterexamples.

use std::fs;

use serde_json::json;

use crate::artifact::{ArtifactKind, ArtifactStore, ScopeTag};
use crate::failure::{FailureKind, FailureOrigin, FailureReport, FailureScope};
use crate::task::SynthesisTask;

use super::check::EntailmentCounterexample;
use super::model::{DecodedInstance, InstanceValue, ModelDecodeError, decode_vampire_model};

// ------------------------------------------------------------
// Counterexample Resolution
// ------------------------------------------------------------

/// Resolve one model or already decoded empty counterexample.
pub fn resolve_entailment_counterexample(
    task: &SynthesisTask,
    artifacts: &ArtifactStore,
    counterexample: &EntailmentCounterexample,
) -> Result<DecodedInstance, FailureReport> {
    if artifacts.task_identity() != task.identity() {
        return Err(model_failure(
            FailureKind::InfrastructureFailure,
            false,
            FailureScope::RunGlobal,
            "counterexample resolution uses another task backend",
            Vec::new(),
        ));
    }
    if let Some(input) = counterexample.empty_input() {
        let evidence = counterexample
            .empty_evidence()
            .expect("every empty counterexample retains its worker evidence");
        if input.task_identity() != task.identity()
            || evidence.backend_id() != artifacts.backend_id()
        {
            return Err(model_failure(
                FailureKind::MalformedResult,
                false,
                FailureScope::LaneLocal,
                "empty counterexample belongs to another task or run backend",
                vec![evidence],
            ));
        }
        return Ok(input.clone());
    }

    let model = counterexample
        .model()
        .expect("every nonempty counterexample contains a model");
    let context = counterexample
        .context()
        .expect("every model counterexample retains its context");
    if context.task_identity() != task.identity()
        || model.problem_identity() != counterexample.entailment_identity()
        || model.output().backend_id() != artifacts.backend_id()
    {
        return Err(model_failure(
            FailureKind::MalformedResult,
            false,
            FailureScope::RunGlobal,
            "model evidence differs from its task, entailment, or backend",
            vec![model.output()],
        ));
    }

    let decoded = counterexample
        .decoded_model()
        .expect("every model counterexample retains its decoded-result cache");
    let mut decoded = decoded.lock().map_err(|_| {
        model_failure(
            FailureKind::InfrastructureFailure,
            false,
            FailureScope::RunGlobal,
            "decoded-model cache lock was poisoned",
            vec![model.output()],
        )
    })?;
    if let Some(input) = decoded.as_ref() {
        return Ok(input.clone());
    }

    let resolved = artifacts.resolve(model.output()).map_err(|report| {
        model_failure(
            FailureKind::InfrastructureFailure,
            true,
            report.scope(),
            format!(
                "resolve retained Vampire model: {}",
                report.detail().unwrap_or("artifact backend failure")
            ),
            vec![model.output()],
        )
    })?;
    let bytes = fs::read(resolved.path()).map_err(|error| {
        model_failure(
            FailureKind::ProcessFailure,
            true,
            FailureScope::LaneLocal,
            format!("read retained Vampire model: {error}"),
            vec![model.output()],
        )
    })?;
    let stdout = String::from_utf8(bytes).map_err(|error| {
        model_failure(
            FailureKind::MalformedResult,
            false,
            FailureScope::LaneLocal,
            format!("Vampire model output is not UTF-8: {error}"),
            vec![model.output()],
        )
    })?;
    let names = context.name_env();
    let input = match decode_vampire_model(task, &names, &stdout) {
        Ok(input) => input,
        Err(error) => {
            let report = decode_failure(error, model.output());
            publish_decode_failure(artifacts, &report)?;
            return Err(report);
        }
    };
    publish_decoded_instance(
        artifacts,
        counterexample.entailment_identity(),
        model.output(),
        &input,
    )?;
    /*
      The decoded instance is the only consumer of this model text, and it
      has now been published in its own right. Under certificate-only
      retention the raw model is spent, so discard it here — on the success
      path only. A failed decode returns above with the model still on disk,
      which is exactly when someone needs to read what Vampire emitted.
    */
    artifacts.discard(model.output())?;
    *decoded = Some(input.clone());
    Ok(input)
}

// ------------------------------------------------------------
// Resolution Artifacts
// ------------------------------------------------------------

fn publish_decoded_instance(
    artifacts: &ArtifactStore,
    entailment_identity: &str,
    model: crate::artifact::ArtifactRef,
    input: &DecodedInstance,
) -> Result<(), FailureReport> {
    let relations = input
        .relations()
        .iter()
        .map(|(relation, table)| {
            json!({
                "relation_key": relation.as_str(),
                "arity": table.arity(),
                "true_tuples": table.true_tuples().iter().map(|tuple| {
                    tuple.iter().map(|value| match value {
                        InstanceValue::Constant(key) => json!({
                            "kind": "constant",
                            "key": key.as_str(),
                        }),
                        InstanceValue::Fresh(index) => json!({
                            "kind": "fresh",
                            "index": index,
                        }),
                    }).collect::<Vec<_>>()
                }).collect::<Vec<_>>(),
            })
        })
        .collect::<Vec<_>>();
    let payload = json!({
        "kind": "decoded_entailment_counterexample",
        "entailment_identity": entailment_identity,
        "model_artifact_backend": model.backend_id().to_string(),
        "relations": relations,
    });
    artifacts
        .scoped(ScopeTag::named("model-decoding"))
        .publish(
            ArtifactKind::Witness,
            payload.to_string().into_bytes().into_boxed_slice(),
        )
        .map(|_| ())
}

fn publish_decode_failure(
    artifacts: &ArtifactStore,
    report: &FailureReport,
) -> Result<(), FailureReport> {
    let payload = json!({
        "kind": "model_decode_failure",
        "origin": format!("{:?}", report.origin()),
        "failure_kind": format!("{:?}", report.kind()),
        "detail": report.detail(),
    });
    artifacts
        .scoped(ScopeTag::named("model-decoding"))
        .publish(
            ArtifactKind::FailureDiagnostic,
            payload.to_string().into_bytes().into_boxed_slice(),
        )
        .map(|_| ())
}

// ------------------------------------------------------------
// Typed Decode Failures
// ------------------------------------------------------------

fn decode_failure(error: ModelDecodeError, model: crate::artifact::ArtifactRef) -> FailureReport {
    let kind = match error {
        ModelDecodeError::Syntax(_) => FailureKind::UnsupportedCheck,
        _ => FailureKind::MalformedResult,
    };
    model_failure(
        kind,
        false,
        FailureScope::LaneLocal,
        error.to_string(),
        vec![model],
    )
}

fn model_failure(
    kind: FailureKind,
    retryable: bool,
    scope: FailureScope,
    detail: impl Into<String>,
    artifacts: Vec<crate::artifact::ArtifactRef>,
) -> FailureReport {
    FailureReport::try_new(
        FailureOrigin::ModelDecoding,
        kind,
        retryable,
        scope,
        Some(detail.into()),
        artifacts,
    )
    .expect("model decoding uses a permitted failure kind")
}
