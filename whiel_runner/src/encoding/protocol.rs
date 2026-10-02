//! Bounded length-framed protocol for the persistent Lean worker.

use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::task::{SynthesisTask, TaskIdentity, TaskSchemaKind};

use super::names::{NameEnvRevision, NameMapping};
use super::proposal::ProposalRevision;

pub const WORKER_FORMAT_VERSION: u64 = 13;
/// Independent protocol version for the fixed-ambient worker.
pub const FIXED_AMBIENT_WORKER_FORMAT_VERSION: u64 = 11;
pub const MAX_ENCODING_FRAME_BYTES: usize = 64 * 1024 * 1024;

/// Explicit marker that a task came through the fixed-ambient bootstrap path.
#[derive(Clone, Debug)]
pub struct FixedAmbientWorkerBinding {
    task: TaskIdentity,
    scope_identity: Value,
}

impl FixedAmbientWorkerBinding {
    pub fn from_task(task: &SynthesisTask, scope_identity: Value) -> Result<Self, &'static str> {
        if task.schema_kind() != TaskSchemaKind::FixedAmbient {
            return Err("fixed-ambient worker binding requires an explicitly loaded V5 task");
        }
        Ok(Self {
            task: task.identity().clone(),
            scope_identity,
        })
    }

    #[cfg(test)]
    pub(crate) fn for_test(task: TaskIdentity, scope_identity: Value) -> Self {
        Self {
            task,
            scope_identity,
        }
    }

    pub fn task_identity(&self) -> &TaskIdentity {
        &self.task
    }

    pub fn scope_identity(&self) -> &Value {
        &self.scope_identity
    }
}

/// Closed operation set accepted by the fixed-ambient worker.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum FixedAmbientWorkerOperation {
    Ping,
    Describe,
    ExtendNameEnv,
    AdmitClauses,
    EvaluateClauses,
    PrepareComponent,
    PrepareTaskPieces,
    PrepareClausePieces,
    PrepareSupportBlock,
    /// Lean still serves this operation, but since Pass 7.5d the production
    /// path never issues it: an obligation identity is assembled locally
    /// from the cached opaque pieces. The only Rust callers left are this
    /// crate's own tests.
    BuildExactObligation,
    PrepareExactObligation,
    CheckEmptyCounterexample,
    ValidateRefutation,
    /// Decode, precondition-check, and fuel-evaluate one agent-proposed
    /// counterexample instance over the input schema. The instance itself is
    /// opaque to Rust: it is passed through untouched and Lean answers either
    /// a canonical validated instance or a typed rejection code.
    ValidateCounterexample,
    ExtractPreconditionClauses,
    ConfirmPreconditionRow,
    EmitCertificate,
    /// Render `Certificate/Invalid.lean` over the raw input triple from one
    /// frozen counterexample instance and its frozen fuel. The emitted
    /// bundle carries no proof jobs at all.
    EmitInvalidCertificate,
    PackageProof,
    Shutdown,
}

/// Exact task identity echoed by every fixed-ambient response.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FixedAmbientWorkerTaskIdentity {
    pub canonical_id: String,
    pub module: String,
    pub namespace: String,
    pub source_sha256: String,
}

/// Strict V5 request envelope. The scope is opaque to Rust and compared whole.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FixedAmbientWorkerRequestEnvelope {
    pub format_version: u64,
    pub semantic_version: u64,
    pub encoding_version: u64,
    pub task_canonical_id: String,
    pub task_module: String,
    pub task_namespace: String,
    pub task_source_sha256: String,
    pub scope_identity: Value,
    pub request_id: u64,
    pub name_env_revision: NameEnvRevision,
    pub operation: FixedAmbientWorkerOperation,
    pub payload: Value,
}

/// Strict V5 response envelope. V4's context and proposal fields are invalid.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FixedAmbientWorkerResponseEnvelope {
    pub format_version: u64,
    pub semantic_version: u64,
    pub encoding_version: u64,
    /// The identity the worker answered under, or `null` on an error frame
    /// the worker could not bind to a registered task at all: it resolved no
    /// entry, so it has no identity of its own to echo and must not name
    /// another task's. `scope_identity` is `null` on exactly those frames.
    /// `deserialize_with` keeps the field itself required: an `Option` field
    /// is otherwise satisfied by a missing key, and a response that simply
    /// omits its identity is a malformed frame rather than an unbound one.
    #[serde(deserialize_with = "required_option")]
    pub task_identity: Option<FixedAmbientWorkerTaskIdentity>,
    pub scope_identity: Value,
    pub request_id: u64,
    pub request_name_env_revision: NameEnvRevision,
    pub name_env_revision: NameEnvRevision,
    pub operation: FixedAmbientWorkerOperation,
    pub status: WorkerResponseStatus,
    #[serde(default)]
    pub payload: Value,
    #[serde(default)]
    pub error: Option<FixedAmbientWorkerResponseError>,
}

/// Deserialize an `Option` field that must still be present. Serde treats a
/// plain `Option` field as satisfied by a missing key; routing it through
/// `deserialize_with` restores the requirement that the key appear, with
/// `null` as the only way to reach `None`.
fn required_option<'de, D, T>(deserializer: D) -> Result<Option<T>, D::Error>
where
    D: serde::Deserializer<'de>,
    T: Deserialize<'de>,
{
    Option::<T>::deserialize(deserializer)
}

/// Exact error object carried by a fixed-ambient response envelope.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FixedAmbientWorkerResponseError {
    pub kind: String,
    pub message: String,
}

/// Exact key/name pair used only by the fixed-ambient protocol.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct FixedAmbientNameBinding {
    pub(crate) key: String,
    pub(crate) name: String,
}

impl From<&NameMapping> for FixedAmbientNameBinding {
    fn from(mapping: &NameMapping) -> Self {
        Self {
            key: mapping.key.clone(),
            name: mapping.tptp_name.clone(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum WorkerOperation {
    Ping,
    ExtendNameEnv,
    RegisterReferenceProposal,
    EnsureWLayer,
    PrepareBodies,
    PrepareMaintenanceWps,
    PrepareSupport,
    CheckEmptyCounterexample,
    Shutdown,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct WorkerRequestEnvelope {
    pub format_version: u64,
    pub semantic_version: u64,
    pub encoding_version: u64,
    pub task_canonical_id: String,
    pub task_module: String,
    pub task_namespace: String,
    pub task_source_sha256: String,
    pub request_id: u64,
    pub context_id: String,
    pub name_env_revision: NameEnvRevision,
    pub proposal_revision: ProposalRevision,
    pub operation: WorkerOperation,
    pub payload: Value,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct WorkerResponseEnvelope {
    pub format_version: u64,
    pub semantic_version: u64,
    pub encoding_version: u64,
    pub task_canonical_id: String,
    pub task_module: String,
    pub task_namespace: String,
    pub task_source_sha256: String,
    pub request_id: u64,
    pub context_id: String,
    pub operation: WorkerOperation,
    pub request_name_env_revision: NameEnvRevision,
    pub name_env_revision: NameEnvRevision,
    pub request_proposal_revision: ProposalRevision,
    pub proposal_revision: ProposalRevision,
    pub status: WorkerResponseStatus,
    #[serde(default)]
    pub payload: Value,
    #[serde(default)]
    pub error: Option<WorkerResponseError>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WorkerResponseError {
    pub kind: String,
    pub message: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct NameBinding {
    pub(crate) key: String,
    pub(crate) name: String,
}

impl From<&NameMapping> for NameBinding {
    fn from(mapping: &NameMapping) -> Self {
        Self {
            key: mapping.key.clone(),
            name: mapping.tptp_name.clone(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum WorkerResponseStatus {
    Ok,
    Error,
}

pub(crate) use crate::framing::{read_frame, write_frame};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn frame_round_trip_uses_big_endian_length() {
        let request = WorkerRequestEnvelope {
            format_version: WORKER_FORMAT_VERSION,
            semantic_version: 3,
            encoding_version: 5,
            task_canonical_id: "Task".to_string(),
            task_module: "Task.Module".to_string(),
            task_namespace: "Task.Namespace".to_string(),
            task_source_sha256: "0".repeat(64),
            request_id: 7,
            context_id: "context".to_string(),
            name_env_revision: NameEnvRevision::INITIAL,
            proposal_revision: ProposalRevision::INITIAL,
            operation: WorkerOperation::Ping,
            payload: Value::Null,
        };
        let mut bytes = Vec::new();
        write_frame(&mut bytes, &request, MAX_ENCODING_FRAME_BYTES).unwrap();
        let length = u32::from_be_bytes(bytes[..4].try_into().unwrap()) as usize;
        assert_eq!(length, bytes.len() - 4);
        let decoded: WorkerRequestEnvelope =
            read_frame(&mut bytes.as_slice(), MAX_ENCODING_FRAME_BYTES).unwrap();
        assert_eq!(decoded.request_id, request.request_id);
        assert_eq!(decoded.operation, WorkerOperation::Ping);
    }

    #[test]
    fn rejects_zero_and_oversized_frames_before_allocation() {
        assert!(read_frame::<Value>(&mut [0_u8; 4].as_slice(), 8).is_err());
        assert!(read_frame::<Value>(&mut [0, 0, 0, 9].as_slice(), 8).is_err());
    }

    fn fixed_ambient_request() -> FixedAmbientWorkerRequestEnvelope {
        FixedAmbientWorkerRequestEnvelope {
            format_version: FIXED_AMBIENT_WORKER_FORMAT_VERSION,
            semantic_version: 1,
            encoding_version: 1,
            task_canonical_id: "Example0001".to_string(),
            task_module: "Benchmark.Example0001.Input".to_string(),
            task_namespace: "Whiel.Benchmark.Example0001".to_string(),
            task_source_sha256: "a".repeat(64),
            scope_identity: serde_json::json!({"kind":"fixed"}),
            request_id: 9,
            name_env_revision: NameEnvRevision::INITIAL,
            operation: FixedAmbientWorkerOperation::BuildExactObligation,
            payload: serde_json::json!({"selector":{"kind":"termination"},"snapshot":{"rows":[]}}),
        }
    }

    #[test]
    fn fixed_ambient_envelope_is_independent_and_strict() {
        let request = fixed_ambient_request();
        let value = serde_json::to_value(&request).unwrap();
        assert_eq!(
            value["operation"],
            serde_json::json!("build_exact_obligation")
        );
        assert!(value.get("context_id").is_none());
        assert!(value.get("proposal_revision").is_none());

        let mut extra = value.clone();
        extra["context_id"] = serde_json::json!("legacy");
        assert!(serde_json::from_value::<FixedAmbientWorkerRequestEnvelope>(extra).is_err());
        assert!(serde_json::from_value::<WorkerRequestEnvelope>(value).is_err());
    }

    #[test]
    fn fixed_ambient_response_rejects_v4_shape() {
        let legacy = serde_json::json!({
            "format_version": WORKER_FORMAT_VERSION,
            "semantic_version": 1,
            "encoding_version": 1,
            "task_canonical_id": "Example0001",
            "task_module": "Benchmark.Example0001.Input",
            "task_namespace": "Whiel.Benchmark.Example0001",
            "task_source_sha256": "a".repeat(64),
            "request_id": 9,
            "context_id": "legacy",
            "name_env_revision": 0,
            "proposal_revision": 0,
            "operation": "ping",
            "status": "ok",
            "payload": {}
        });
        assert!(serde_json::from_value::<FixedAmbientWorkerResponseEnvelope>(legacy).is_err());

        let mut response = serde_json::json!({
            "format_version": FIXED_AMBIENT_WORKER_FORMAT_VERSION,
            "semantic_version": 1,
            "encoding_version": 1,
            "task_identity": {
                "canonical_id": "Example0001",
                "module": "Benchmark.Example0001.Input",
                "namespace": "Whiel.Benchmark.Example0001",
                "source_sha256": "a".repeat(64)
            },
            "scope_identity": {"kind":"fixed"},
            "request_id": 9,
            "request_name_env_revision": 0,
            "name_env_revision": 0,
            "operation": "ping",
            "status": "ok",
            "payload": {"ready":true}
        });
        assert!(
            serde_json::from_value::<FixedAmbientWorkerResponseEnvelope>(response.clone()).is_ok()
        );
        assert!(serde_json::from_value::<WorkerResponseEnvelope>(response.clone()).is_err());
        response["format_version"] = serde_json::json!(WORKER_FORMAT_VERSION);
        let decoded: FixedAmbientWorkerResponseEnvelope = serde_json::from_value(response).unwrap();
        assert_ne!(decoded.format_version, FIXED_AMBIENT_WORKER_FORMAT_VERSION);

        let mut extra_error_field = serde_json::json!({
            "format_version": FIXED_AMBIENT_WORKER_FORMAT_VERSION,
            "semantic_version": 1,
            "encoding_version": 1,
            "task_identity": {
                "canonical_id": "Example0001",
                "module": "Benchmark.Example0001.Input",
                "namespace": "Whiel.Benchmark.Example0001",
                "source_sha256": "a".repeat(64)
            },
            "scope_identity": {"kind":"fixed"},
            "request_id": 9,
            "request_name_env_revision": 0,
            "name_env_revision": 0,
            "operation": "ping",
            "status": "error",
            "payload": null,
            "error": {"kind":"invalid_envelope", "message":"bad", "legacy":true}
        });
        assert!(
            serde_json::from_value::<FixedAmbientWorkerResponseEnvelope>(extra_error_field.clone())
                .is_err()
        );
        extra_error_field["error"]
            .as_object_mut()
            .unwrap()
            .remove("legacy");
        assert!(
            serde_json::from_value::<FixedAmbientWorkerResponseEnvelope>(extra_error_field.clone())
                .is_ok()
        );

        // An error frame the worker bound to no registered task echoes null
        // for both identities and still decodes; the field must be present.
        let mut unbound = extra_error_field;
        unbound["task_identity"] = serde_json::Value::Null;
        unbound["scope_identity"] = serde_json::Value::Null;
        let decoded: FixedAmbientWorkerResponseEnvelope =
            serde_json::from_value(unbound.clone()).unwrap();
        assert!(decoded.task_identity.is_none());
        assert!(decoded.scope_identity.is_null());
        unbound.as_object_mut().unwrap().remove("task_identity");
        assert!(serde_json::from_value::<FixedAmbientWorkerResponseEnvelope>(unbound).is_err());
    }

    #[test]
    fn fixed_ambient_binding_rejects_a_legacy_loaded_task() {
        let task = super::super::names::sample_task_for_encoding_tests();
        assert!(
            FixedAmbientWorkerBinding::from_task(&task, serde_json::json!({"kind":"fixed"}))
                .is_err()
        );
    }

    #[test]
    fn fixed_ambient_operation_names_are_stable() {
        for (operation, expected) in [
            (FixedAmbientWorkerOperation::Ping, "\"ping\""),
            (FixedAmbientWorkerOperation::Describe, "\"describe\""),
            (
                FixedAmbientWorkerOperation::ExtendNameEnv,
                "\"extend_name_env\"",
            ),
            (
                FixedAmbientWorkerOperation::AdmitClauses,
                "\"admit_clauses\"",
            ),
            (
                FixedAmbientWorkerOperation::EvaluateClauses,
                "\"evaluate_clauses\"",
            ),
            (
                FixedAmbientWorkerOperation::PrepareComponent,
                "\"prepare_component\"",
            ),
            (
                FixedAmbientWorkerOperation::PrepareTaskPieces,
                "\"prepare_task_pieces\"",
            ),
            (
                FixedAmbientWorkerOperation::PrepareClausePieces,
                "\"prepare_clause_pieces\"",
            ),
            (
                FixedAmbientWorkerOperation::PrepareSupportBlock,
                "\"prepare_support_block\"",
            ),
            (
                FixedAmbientWorkerOperation::BuildExactObligation,
                "\"build_exact_obligation\"",
            ),
            (
                FixedAmbientWorkerOperation::PrepareExactObligation,
                "\"prepare_exact_obligation\"",
            ),
            (
                FixedAmbientWorkerOperation::CheckEmptyCounterexample,
                "\"check_empty_counterexample\"",
            ),
            (
                FixedAmbientWorkerOperation::ValidateRefutation,
                "\"validate_refutation\"",
            ),
            (
                FixedAmbientWorkerOperation::ValidateCounterexample,
                "\"validate_counterexample\"",
            ),
            (
                FixedAmbientWorkerOperation::ExtractPreconditionClauses,
                "\"extract_precondition_clauses\"",
            ),
            (
                FixedAmbientWorkerOperation::ConfirmPreconditionRow,
                "\"confirm_precondition_row\"",
            ),
            (
                FixedAmbientWorkerOperation::EmitCertificate,
                "\"emit_certificate\"",
            ),
            (
                FixedAmbientWorkerOperation::EmitInvalidCertificate,
                "\"emit_invalid_certificate\"",
            ),
            (
                FixedAmbientWorkerOperation::PackageProof,
                "\"package_proof\"",
            ),
            (FixedAmbientWorkerOperation::Shutdown, "\"shutdown\""),
        ] {
            assert_eq!(serde_json::to_string(&operation).unwrap(), expected);
        }
    }

    #[test]
    fn retired_framework_ii_v4_operations_fail_closed() {
        for retired in [
            "describe_framework_ii_scope",
            "admit_framework_ii_clauses",
            "admit_source_instance",
            "prepare_framework_ii_component",
            "prepare_framework_ii_support",
            "build_framework_ii_prophecy_context",
            "build_framework_ii_obligation",
            "collapse_framework_ii_core",
            "extract_framework_ii_precondition_clauses",
            "validate_framework_ii_refutation",
            "prepare_framework_ii_entailment",
            "check_framework_ii_empty_counterexample",
        ] {
            assert!(serde_json::from_value::<WorkerOperation>(serde_json::json!(retired)).is_err());
        }
    }

    #[test]
    fn retired_finite_validity_operations_fail_closed() {
        for retired in [
            "describe_finite_validity_registry",
            "admit_finite_validity_selections",
            "apply_finite_validity_uses",
        ] {
            let request = serde_json::json!({
                "format_version": WORKER_FORMAT_VERSION,
                "semantic_version": 3,
                "encoding_version": 5,
                "task_canonical_id": "Task",
                "task_module": "Task.Module",
                "task_namespace": "Task.Namespace",
                "task_source_sha256": "0".repeat(64),
                "request_id": 7,
                "context_id": "context",
                "name_env_revision": NameEnvRevision::INITIAL,
                "proposal_revision": ProposalRevision::INITIAL,
                "operation": retired,
                "payload": null,
            });
            assert!(serde_json::from_value::<WorkerRequestEnvelope>(request).is_err());
        }
    }
}
