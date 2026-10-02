//! State-bound final certification for Houdini and source instances.
//!
//! This module is the production guard around the low-level legacy bridge.
//! It derives validity input from the exact current Core, keeps bridge work
//! owned by the run artifact backend, and imports every terminal certificate,
//! Witness, and diagnostic into that backend before returning.

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

use serde_json::{Value, json};

use crate::artifact::{
    ArtifactKind, ArtifactRef, ArtifactStore, BackendId, OwnedWorkRegistration, ScopeTag,
};
use crate::certification::{
    CertificationBridgeCommand, CertificationBridgeError, CertificationFailure,
    CertificationOutcome, CertifiedClassification, InvalidityCertificationLimits,
    ValidityCertificationLimits,
};
use crate::entailment::assembly::Sha256;
use crate::entailment::{DecodedInstance, InstanceValue};
use crate::failure::{FailureKind, FailureOrigin, FailureReport, FailureScope};
use crate::runtime::CancellationToken;
use crate::task::{SynthesisTask, TaskIdentity};

use super::{
    HoudiniState, InitializationStatus, LastTermStatus, SearchFeedback, VerificationParameters,
};

const DEFAULT_MAX_HEARTBEATS: u64 = 400_000_000;
const DEFAULT_INVALIDITY_FUEL: u64 = 1_000;

// ------------------------------------------------------------
// Runtime Configuration And Typed Input
// ------------------------------------------------------------

/// Process paths and nonlogical limits needed by the legacy authority.
#[derive(Clone, Debug)]
pub struct CertificationRuntime {
    command: CertificationBridgeCommand,
    work_directory: PathBuf,
    solution_directory: PathBuf,
    max_heartbeats: u64,
    invalidity_fuel: u64,
    /// Exact transient failures which already consumed their one retry permit.
    invalidity_retries: Arc<Mutex<HashSet<InvalidityRetryKey>>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct InvalidityRetryKey {
    backend: BackendId,
    task: TaskIdentity,
    input_sha256: String,
    stage: String,
    search_limit: std::time::Duration,
    final_certification_limit: Option<std::time::Duration>,
    max_heartbeats: u64,
    invalidity_fuel: u64,
}

#[derive(Clone, Debug)]
struct InvalidityRetryObservation {
    stage: String,
    deterministic: bool,
}

impl CertificationRuntime {
    pub fn new(
        command: CertificationBridgeCommand,
        work_directory: impl Into<PathBuf>,
        solution_directory: impl Into<PathBuf>,
    ) -> Self {
        Self {
            command,
            work_directory: work_directory.into(),
            solution_directory: solution_directory.into(),
            max_heartbeats: DEFAULT_MAX_HEARTBEATS,
            invalidity_fuel: DEFAULT_INVALIDITY_FUEL,
            invalidity_retries: Arc::new(Mutex::new(HashSet::new())),
        }
    }

    pub fn with_max_heartbeats(mut self, max_heartbeats: u64) -> Result<Self, &'static str> {
        if max_heartbeats == 0 {
            return Err("max_heartbeats must be positive");
        }
        self.max_heartbeats = max_heartbeats;
        Ok(self)
    }

    pub fn with_invalidity_fuel(mut self, fuel: u64) -> Result<Self, &'static str> {
        if fuel == 0 {
            return Err("invalidity fuel must be positive");
        }
        self.invalidity_fuel = fuel;
        Ok(self)
    }

    /// Give the INV lane exclusive bridge work and solution locations.
    ///
    /// The legacy bridge takes an exclusive lease on its solution directory.
    /// Symbolic lanes therefore cannot safely certify concurrently against one
    /// shared path, even though the remaining runtime configuration is shared.
    pub(crate) fn for_symbolic_inv_lane(&self) -> Self {
        self.with_path_scope("symbolic-inv")
    }

    /// Give the CEX lane exclusive bridge work and solution locations.
    pub(crate) fn for_symbolic_cex_lane(&self) -> Self {
        self.with_path_scope("symbolic-cex")
    }

    fn with_path_scope(&self, component: &str) -> Self {
        let mut scoped = self.clone();
        scoped.work_directory = self.work_directory.join(component);
        scoped.solution_directory = self.solution_directory.join(component);
        scoped
    }

    fn classify_invalidity_retry(
        &self,
        task: &SynthesisTask,
        verification: &VerificationParameters,
        artifacts: &ArtifactStore,
        input: &CertificationInstance,
        observation: InvalidityRetryObservation,
        report: FailureReport,
    ) -> FailureReport {
        // Retry policy belongs to the authority boundary. Callers receive one
        // already-final classification and cannot accidentally loop forever.
        let kind = report.kind();
        let transient = matches!(
            kind,
            FailureKind::CheckTimeout
                | FailureKind::ProcessFailure
                | FailureKind::InfrastructureFailure
                | FailureKind::PublicationFailure
        );
        let retryable =
            if transient && !observation.deterministic && report.scope() == FailureScope::LaneLocal
            {
                match self.claim_invalidity_retry(InvalidityRetryKey {
                    backend: artifacts.backend_id(),
                    task: task.identity().clone(),
                    input_sha256: canonical_value_sha256(input.as_json()),
                    stage: observation.stage,
                    search_limit: verification.search_limit(),
                    final_certification_limit: verification.final_certification_limit(),
                    max_heartbeats: self.max_heartbeats,
                    invalidity_fuel: self.invalidity_fuel,
                }) {
                    Ok(retryable) => retryable,
                    Err(()) => {
                        return certification_failure(
                            FailureOrigin::InvalidityCertification,
                            FailureKind::InfrastructureFailure,
                            false,
                            FailureScope::RunGlobal,
                            "invalidity-certification retry tracker is poisoned",
                            report.artifact_references().to_vec(),
                        );
                    }
                }
            } else {
                false
            };
        certification_failure(
            FailureOrigin::InvalidityCertification,
            kind,
            retryable,
            report.scope(),
            report.detail().unwrap_or("invalidity certification failed"),
            report.artifact_references().to_vec(),
        )
    }

    fn claim_invalidity_retry(&self, key: InvalidityRetryKey) -> Result<bool, ()> {
        self.invalidity_retries
            .lock()
            .map(|mut retries| retries.insert(key))
            .map_err(|_| ())
    }
}

fn canonical_value_sha256(value: &Value) -> String {
    let canonical = canonical_value_bytes(value);
    let mut digest = Sha256::new();
    digest.update(&canonical);
    digest.finalize_hex()
}

fn canonical_value_bytes(value: &Value) -> Vec<u8> {
    fn sorted(value: &Value) -> Value {
        match value {
            Value::Object(entries) => {
                let mut keys = entries.keys().collect::<Vec<_>>();
                keys.sort_unstable();
                Value::Object(
                    keys.into_iter()
                        .map(|key| (key.clone(), sorted(&entries[key])))
                        .collect(),
                )
            }
            Value::Array(values) => Value::Array(values.iter().map(sorted).collect()),
            _ => value.clone(),
        }
    }

    serde_json::to_vec(&sorted(value))
        .expect("a validated certification Instance is JSON-serializable")
}

#[derive(Clone, Debug)]
struct CertificationProvenance {
    task_identity: Value,
    logical_input: Value,
}

impl CertificationProvenance {
    fn validity(task: &SynthesisTask, canonical_core: &[String]) -> Self {
        let encoded =
            serde_json::to_vec(canonical_core).expect("a canonical Core is JSON-serializable");
        let mut digest = Sha256::new();
        digest.update(&encoded);
        Self {
            task_identity: task_identity_value(task.identity()),
            logical_input: json!({
                "core_encoding": "sorted-canonical-formula-json-v1",
                "core_sha256": digest.finalize_hex(),
                "core_member_count": canonical_core.len(),
                "core_byte_len": encoded.len(),
            }),
        }
    }

    fn invalidity(task: &SynthesisTask, input: &Value) -> Self {
        let canonical = canonical_value_bytes(input);
        let mut digest = Sha256::new();
        digest.update(&canonical);
        Self {
            task_identity: task_identity_value(task.identity()),
            logical_input: json!({
                "input_encoding": "canonical-json-v1",
                "input_sha256": digest.finalize_hex(),
                "input_byte_len": canonical.len(),
            }),
        }
    }

    fn record_fields(&self, details: Value, evidence: &[ArtifactRef]) -> Value {
        json!({
            "task_identity": self.task_identity,
            "logical_input": self.logical_input,
            "details": details,
            "evidence": evidence.iter().copied().map(artifact_reference_value).collect::<Vec<_>>(),
        })
    }
}

fn task_identity_value(identity: &TaskIdentity) -> Value {
    json!({
        "canonical_id": identity.canonical_id(),
        "module": identity.module(),
        "namespace": identity.namespace(),
        "source_sha256": identity.source_digest().as_str(),
        "semantic_version": identity.semantic_version(),
        "encoding_version": identity.encoding_version(),
    })
}

fn artifact_reference_value(reference: ArtifactRef) -> Value {
    json!({
        "backend_id": reference.backend_id().to_string(),
        "local_id": reference.local_id(),
        "kind": reference.kind(),
    })
}

/// One schema-complete, task-bound source Instance accepted by the authority.
#[derive(Clone, Debug)]
pub struct CertificationInstance {
    task: TaskIdentity,
    value: Value,
}

impl CertificationInstance {
    /// Validate the legacy JSON Instance representation once at the boundary.
    pub fn from_json(
        task: &SynthesisTask,
        value: Value,
    ) -> Result<Self, CertificationInstanceError> {
        validate_instance(task, &value)?;
        Ok(Self {
            task: task.identity().clone(),
            value,
        })
    }

    /// Convert one exact decoded solver model to the legacy source-Instance
    /// representation without weakening the certification boundary.
    ///
    /// Task constants retain their exact concrete values. Unnamed model
    /// elements receive deterministic string values which are injective and
    /// disjoint from every task constant, including isolated constants which
    /// occur in no relation tuple. The result still passes through
    /// [`CertificationInstance::from_json`], so this conversion cannot bypass
    /// schema-completeness or tuple-shape validation.
    pub fn from_decoded(
        task: &SynthesisTask,
        input: &DecodedInstance,
    ) -> Result<Self, CertificationInstanceError> {
        if input.task_identity() != task.identity() {
            return Err(CertificationInstanceError(
                "decoded Instance belongs to another task".to_string(),
            ));
        }

        let fresh_values = fresh_certification_values(task, input);
        let task_constants = task.solver_constants().iter().collect::<BTreeSet<_>>();
        let mut value = serde_json::Map::new();
        for schema_relation in task.solver_relations() {
            let relation = input.relation(schema_relation.key()).ok_or_else(|| {
                CertificationInstanceError(format!(
                    "decoded Instance omits relation {:?}",
                    schema_relation.key().as_str()
                ))
            })?;
            if relation.arity() != schema_relation.arity() {
                return Err(CertificationInstanceError(format!(
                    "decoded relation {:?} has arity {}, expected {}",
                    schema_relation.key().as_str(),
                    relation.arity(),
                    schema_relation.arity()
                )));
            }
            let rows = relation
                .true_tuples()
                .iter()
                .map(|tuple| {
                    tuple
                        .iter()
                        .map(|cell| match cell {
                            InstanceValue::Constant(key) => {
                                if !task_constants.contains(key) {
                                    return Err(CertificationInstanceError(format!(
                                        "decoded Instance uses foreign constant {:?}",
                                        key.as_str()
                                    )));
                                }
                                concrete_constant_json(key.as_str())
                            }
                            InstanceValue::Fresh(index) => fresh_values
                                .get(index)
                                .cloned()
                                .map(Value::String)
                                .ok_or_else(|| {
                                    CertificationInstanceError(format!(
                                        "decoded Instance has no value for fresh element {index}"
                                    ))
                                }),
                        })
                        .collect::<Result<Vec<_>, _>>()
                        .map(Value::Array)
                })
                .collect::<Result<Vec<_>, _>>()?;
            value.insert(
                relation_display_name(schema_relation.key().as_str())?,
                Value::Array(rows),
            );
        }
        if input.relations().len() != task.solver_relations().len() {
            return Err(CertificationInstanceError(
                "decoded Instance relation set differs from task.schema".to_string(),
            ));
        }
        Self::from_json(task, Value::Object(value))
    }

    pub fn task_identity(&self) -> &TaskIdentity {
        &self.task
    }

    pub fn as_json(&self) -> &Value {
        &self.value
    }
}

fn fresh_certification_values(
    task: &SynthesisTask,
    input: &DecodedInstance,
) -> BTreeMap<u64, String> {
    let mut occupied = task
        .solver_constants()
        .iter()
        .filter_map(|key| key.as_str().strip_prefix("str:").map(str::to_owned))
        .collect::<BTreeSet<_>>();
    let indices = input
        .relations()
        .values()
        .flat_map(|relation| relation.true_tuples())
        .flat_map(|tuple| tuple.iter())
        .filter_map(|value| match value {
            InstanceValue::Fresh(index) => Some(*index),
            InstanceValue::Constant(_) => None,
        })
        .collect::<BTreeSet<_>>();
    indices
        .into_iter()
        .map(|index| {
            let mut value = format!("__whiel_fmb_fresh_{index}");
            while occupied.contains(&value) {
                value.push('_');
            }
            occupied.insert(value.clone());
            (index, value)
        })
        .collect()
}

fn concrete_constant_json(key: &str) -> Result<Value, CertificationInstanceError> {
    if let Some(number) = key.strip_prefix("num:") {
        let value = serde_json::from_str::<Value>(number).map_err(|error| {
            CertificationInstanceError(format!("decode concrete numeric constant {key:?}: {error}"))
        })?;
        if value
            .as_number()
            .is_some_and(is_nonnegative_integral_number)
        {
            return Ok(value);
        }
    } else if let Some(string) = key.strip_prefix("str:") {
        return Ok(Value::String(string.to_string()));
    } else if key == "bool:0" {
        return Ok(Value::Bool(false));
    } else if key == "bool:1" {
        return Ok(Value::Bool(true));
    }
    Err(CertificationInstanceError(format!(
        "malformed concrete constant key {key:?}"
    )))
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertificationInstanceError(String);

impl fmt::Display for CertificationInstanceError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0)
    }
}

impl std::error::Error for CertificationInstanceError {}

// ------------------------------------------------------------
// Terminal Wrapper Results
// ------------------------------------------------------------

#[derive(Clone, Debug)]
pub struct CertifiedValidity {
    /// Stable retained certificate; no bridge-owned path crosses this boundary.
    pub certificate: ArtifactRef,
    /// Required authority-acceptance record which preceded certificate import.
    pub record: ArtifactRef,
    /// Exact sorted Core syntax supplied to the unchanged certificate bridge.
    pub invariant: Vec<String>,
}

#[derive(Clone, Debug)]
pub struct CertifiedInvalidity {
    /// Stable retained certificate; no bridge-owned path crosses this boundary.
    pub certificate: ArtifactRef,
    /// Stable retained Witness for the exact task and source Instance.
    pub witness: ArtifactRef,
    /// Required authority-acceptance record which preceded certificate import.
    pub record: ArtifactRef,
    /// Exact source Instance supplied to the unchanged certificate bridge.
    pub counterexample: Value,
    /// Symbolic W index which produced this Instance, when applicable.
    pub source_w_index: Option<u64>,
}

#[derive(Clone, Debug)]
pub enum ValidityCertificationOutcome {
    Certified(CertifiedValidity),
    Failure(FailureReport),
    Cancelled,
}

#[derive(Clone, Debug)]
pub enum InvalidityCertificationOutcome {
    Certified(CertifiedInvalidity),
    Rejected(SearchFeedback),
    Failure(FailureReport),
    Cancelled,
}

// ------------------------------------------------------------
// State-Bound Certification
// ------------------------------------------------------------

/// Certify only the exact current, initialized Core whose Term status is Proved.
pub async fn certify_valid(
    task: &SynthesisTask,
    state: &mut HoudiniState,
    runtime: &CertificationRuntime,
    cancellation: &CancellationToken,
) -> ValidityCertificationOutcome {
    if cancellation.is_cancelled() {
        return ValidityCertificationOutcome::Cancelled;
    }
    let core = match exact_certifiable_core(task, state) {
        Ok(core) => core,
        Err(report) => return ValidityCertificationOutcome::Failure(report),
    };
    let provenance = CertificationProvenance::validity(task, &core);
    let exact_core = state.core.clone();
    let task = task.clone();
    let verification = state.verification.clone();
    let runtime = runtime.clone();
    let artifacts = state
        .artifacts
        .scoped(ScopeTag::verification_stage("validity-certification"));
    let worker_artifacts = artifacts.clone();

    let invoked = run_owned_blocking(&artifacts, cancellation, move |worker_cancellation| {
        let invariant = core.clone();
        let outcome = runtime.command.certify_valid(
            &task,
            core,
            &runtime.work_directory,
            &runtime.solution_directory,
            ValidityCertificationLimits {
                final_search: verification.final_certification_limit(),
                lean: verification.final_certification_limit(),
                max_heartbeats: runtime.max_heartbeats,
                bridge: None,
            },
            &worker_cancellation,
        );
        import_validity_outcome(&worker_artifacts, &provenance, invariant, outcome)
    })
    .await;

    let imported = match invoked {
        OwnedBlockingOutcome::Complete(imported) => imported,
        OwnedBlockingOutcome::Cancelled => return ValidityCertificationOutcome::Cancelled,
        OwnedBlockingOutcome::Panicked(detail) => {
            return ValidityCertificationOutcome::Failure(certification_failure(
                FailureOrigin::ValidityCertification,
                FailureKind::InfrastructureFailure,
                false,
                FailureScope::RunGlobal,
                detail,
                Vec::new(),
            ));
        }
    };
    match imported {
        ImportedValidity::Certified(certified) => {
            if !matches!(state.last_term_status, LastTermStatus::Proved)
                || state.core.as_ref() != exact_core.as_ref()
            {
                return ValidityCertificationOutcome::Failure(certification_failure(
                    FailureOrigin::ValidityCertification,
                    FailureKind::InfrastructureFailure,
                    false,
                    FailureScope::RunGlobal,
                    "Houdini Core changed during final validity certification",
                    vec![certified.certificate, certified.record],
                ));
            }
            ValidityCertificationOutcome::Certified(certified)
        }
        ImportedValidity::Failure(report) => ValidityCertificationOutcome::Failure(report),
        ImportedValidity::Cancelled => ValidityCertificationOutcome::Cancelled,
    }
}

/// Check and certify one typed source Instance without trusting caller JSON.
pub async fn certify_invalid(
    task: &SynthesisTask,
    verification: &VerificationParameters,
    artifacts: &ArtifactStore,
    input: &CertificationInstance,
    runtime: &CertificationRuntime,
    cancellation: &CancellationToken,
) -> InvalidityCertificationOutcome {
    certify_invalid_controlled(task, verification, artifacts, input, runtime, cancellation).await
}

/// Certify invalidity while honoring the run owner's bound stop authority at
/// every artifact-publication boundary.
///
/// The public wrapper preserves the established API. Pre-certificate search
/// calls this crate-visible form to make the bound absolute deadline visible
/// inside the blocking import worker even before its async supervisor polls.
pub(crate) async fn certify_invalid_controlled(
    task: &SynthesisTask,
    verification: &VerificationParameters,
    artifacts: &ArtifactStore,
    input: &CertificationInstance,
    runtime: &CertificationRuntime,
    cancellation: &CancellationToken,
) -> InvalidityCertificationOutcome {
    if cancellation.should_stop() {
        return InvalidityCertificationOutcome::Cancelled;
    }
    if artifacts.task_identity() != task.identity() || input.task_identity() != task.identity() {
        return InvalidityCertificationOutcome::Failure(certification_failure(
            FailureOrigin::InvalidityCertification,
            FailureKind::InfrastructureFailure,
            false,
            FailureScope::RunGlobal,
            "invalidity certification inputs belong to different tasks",
            Vec::new(),
        ));
    }
    let worker_task = task.clone();
    let worker_verification = verification.clone();
    let worker_input = input.value.clone();
    let worker_provenance = CertificationProvenance::invalidity(task, &worker_input);
    let worker_runtime = runtime.clone();
    let scoped_artifacts =
        artifacts.scoped(ScopeTag::verification_stage("invalidity-certification"));
    let worker_artifacts = scoped_artifacts.clone();
    let publication_control = cancellation.clone();

    let invoked = run_owned_blocking(
        &scoped_artifacts,
        cancellation,
        move |worker_cancellation| {
            if publication_control.should_stop() {
                return (
                    ImportedInvalidity::Cancelled,
                    InvalidityRetryObservation {
                        stage: "cancelled_before_authority".to_string(),
                        deterministic: false,
                    },
                );
            }
            let certified_input = worker_input.clone();
            let outcome = worker_runtime.command.certify_invalid(
                &worker_task,
                worker_input,
                worker_runtime.invalidity_fuel,
                &worker_runtime.work_directory,
                &worker_runtime.solution_directory,
                InvalidityCertificationLimits {
                    runtime: worker_verification.search_limit(),
                    lean: worker_verification.final_certification_limit(),
                    max_heartbeats: worker_runtime.max_heartbeats,
                    bridge: None,
                },
                &worker_cancellation,
            );
            let authority_completed = matches!(
                &outcome,
                Ok(CertificationOutcome::Certified(_) | CertificationOutcome::Rejected(_))
            );
            let mut retry_observation = invalidity_retry_observation(&outcome);
            let imported = import_invalidity_outcome(
                &worker_artifacts,
                &worker_task,
                &worker_provenance,
                certified_input,
                outcome,
                &publication_control,
            );
            if authority_completed && matches!(&imported, ImportedInvalidity::Failure(_)) {
                retry_observation = InvalidityRetryObservation {
                    stage: "artifact_import".to_string(),
                    deterministic: false,
                };
            }
            (imported, retry_observation)
        },
    )
    .await;

    if cancellation.should_stop() {
        return InvalidityCertificationOutcome::Cancelled;
    }

    match invoked {
        OwnedBlockingOutcome::Complete((ImportedInvalidity::Certified(certified), _)) => {
            InvalidityCertificationOutcome::Certified(certified)
        }
        OwnedBlockingOutcome::Complete((ImportedInvalidity::Rejected(feedback), _)) => {
            InvalidityCertificationOutcome::Rejected(feedback)
        }
        OwnedBlockingOutcome::Complete((ImportedInvalidity::Failure(report), observation)) => {
            InvalidityCertificationOutcome::Failure(runtime.classify_invalidity_retry(
                task,
                verification,
                artifacts,
                input,
                observation,
                report,
            ))
        }
        OwnedBlockingOutcome::Complete((ImportedInvalidity::Cancelled, _))
        | OwnedBlockingOutcome::Cancelled => InvalidityCertificationOutcome::Cancelled,
        OwnedBlockingOutcome::Panicked(detail) => {
            InvalidityCertificationOutcome::Failure(certification_failure(
                FailureOrigin::InvalidityCertification,
                FailureKind::InfrastructureFailure,
                false,
                FailureScope::RunGlobal,
                detail,
                Vec::new(),
            ))
        }
    }
}

// ------------------------------------------------------------
// Exact Guard And Artifact Import
// ------------------------------------------------------------

fn exact_certifiable_core(
    task: &SynthesisTask,
    state: &HoudiniState,
) -> Result<Vec<String>, FailureReport> {
    if state.catalog.task_identity() != task.identity()
        || state.artifacts.task_identity() != task.identity()
        || state.admission.policy() != state.verification.resources()
        || !matches!(state.last_term_status, LastTermStatus::Proved)
        || !state.active.is_empty()
        || state.maintenance_plan.is_some()
        || state.maintenance_failure.is_some()
    {
        return Err(certification_failure(
            FailureOrigin::ValidityCertification,
            FailureKind::InfrastructureFailure,
            false,
            FailureScope::RunGlobal,
            "validity certification requires one stopped, coherent Houdini state with Proved Term",
            Vec::new(),
        ));
    }
    let mut ids = state.core.iter().copied().collect::<Vec<_>>();
    ids.sort_unstable();
    let mut core = ids
        .into_iter()
        .map(|id| {
            let record = state.catalog.record(id).map_err(|report| {
                certification_failure(
                    FailureOrigin::ValidityCertification,
                    FailureKind::InfrastructureFailure,
                    false,
                    FailureScope::RunGlobal,
                    report.detail().unwrap_or("Core record lookup failed"),
                    report.artifact_references().to_vec(),
                )
            })?;
            if record.initialization() != InitializationStatus::InitProved {
                return Err(certification_failure(
                    FailureOrigin::ValidityCertification,
                    FailureKind::InfrastructureFailure,
                    false,
                    FailureScope::RunGlobal,
                    format!("Core clause {} lacks initialization proof", id.get()),
                    record.initialization_evidence().into_iter().collect(),
                ));
            }
            Ok(record.formula().certificate_formula().to_owned())
        })
        .collect::<Result<Vec<_>, _>>()?;
    // This exact formula-sorted vector is both hashed as provenance and sent
    // to the low-level authority. Its defensive sort is therefore idempotent.
    core.sort_unstable();
    Ok(core)
}

enum ImportedValidity {
    Certified(CertifiedValidity),
    Failure(FailureReport),
    Cancelled,
}

enum ImportedInvalidity {
    Certified(CertifiedInvalidity),
    Rejected(SearchFeedback),
    Failure(FailureReport),
    Cancelled,
}

fn invalidity_retry_observation(
    outcome: &Result<CertificationOutcome, CertificationBridgeError>,
) -> InvalidityRetryObservation {
    match outcome {
        Ok(CertificationOutcome::Failed(failure)) => InvalidityRetryObservation {
            stage: failure.phase.clone(),
            deterministic: failure_is_deterministic(failure),
        },
        Err(error) => InvalidityRetryObservation {
            stage: "certification_bridge".to_string(),
            deterministic: matches!(
                error,
                CertificationBridgeError::InvalidRequest(_)
                    | CertificationBridgeError::ProcessFailed { .. }
                    | CertificationBridgeError::MalformedResponse(_)
                    | CertificationBridgeError::Cleanup(_)
            ),
        },
        Ok(CertificationOutcome::Certified(_)) | Ok(CertificationOutcome::Rejected(_)) => {
            InvalidityRetryObservation {
                stage: "completed".to_string(),
                deterministic: true,
            }
        }
    }
}

fn failure_is_deterministic(failure: &CertificationFailure) -> bool {
    match failure.kind.as_str() {
        "check_timeout" | "timeout" => false,
        "inconclusive" => failure.process_status.as_deref() != Some("timeout"),
        "process_failure"
        | "vampire_failure"
        | "infrastructure_failure"
        | "publication_failure" => failure
            .process_status
            .as_deref()
            .is_some_and(|status| matches!(status, "completed" | "nonzero_exit")),
        _ => true,
    }
}

fn import_validity_outcome(
    artifacts: &ArtifactStore,
    provenance: &CertificationProvenance,
    invariant: Vec<String>,
    outcome: Result<CertificationOutcome, CertificationBridgeError>,
) -> ImportedValidity {
    match outcome {
        Ok(CertificationOutcome::Certified(bundle)) => {
            if bundle.classification != CertifiedClassification::Valid || bundle.witness.is_some() {
                return ImportedValidity::Failure(report_bridge_error(
                    artifacts,
                    provenance,
                    FailureOrigin::ValidityCertification,
                    CertificationBridgeError::MalformedResponse(
                        "validity authority returned the wrong classification".to_string(),
                    ),
                    None,
                ));
            }
            let record = match publish_record(
                artifacts,
                "validity_authority_accepted",
                provenance.record_fields(
                    json!({"certificate_sha256": bundle.certificate_sha256}),
                    &[],
                ),
                None,
            ) {
                Ok(reference) => reference,
                Err(report) => {
                    return ImportedValidity::Failure(remap_publication(
                        report,
                        FailureOrigin::ValidityCertification,
                    ));
                }
            };
            let certificate = match import_file(
                artifacts,
                ArtifactKind::Certificate,
                &bundle.certificate,
                &bundle.certificate_sha256,
                FailureOrigin::ValidityCertification,
                None,
            ) {
                Ok(reference) => reference,
                Err(report) => {
                    return ImportedValidity::Failure(certification_failure(
                        FailureOrigin::ValidityCertification,
                        FailureKind::PublicationFailure,
                        true,
                        report.scope(),
                        report
                            .detail()
                            .unwrap_or("import certified validity certificate"),
                        vec![record],
                    ));
                }
            };
            ImportedValidity::Certified(CertifiedValidity {
                certificate,
                record,
                invariant,
            })
        }
        Ok(CertificationOutcome::Failed(failure)) => {
            ImportedValidity::Failure(report_authority_failure(
                artifacts,
                provenance,
                FailureOrigin::ValidityCertification,
                failure,
                None,
            ))
        }
        Ok(CertificationOutcome::Rejected(rejection)) => {
            ImportedValidity::Failure(report_bridge_error(
                artifacts,
                provenance,
                FailureOrigin::ValidityCertification,
                CertificationBridgeError::MalformedResponse(format!(
                    "validity authority returned rejection {}: {}",
                    rejection.kind, rejection.message
                )),
                None,
            ))
        }
        Err(CertificationBridgeError::Cancelled) => ImportedValidity::Cancelled,
        Err(error) => ImportedValidity::Failure(report_bridge_error(
            artifacts,
            provenance,
            FailureOrigin::ValidityCertification,
            error,
            None,
        )),
    }
}

fn import_invalidity_outcome(
    artifacts: &ArtifactStore,
    task: &SynthesisTask,
    provenance: &CertificationProvenance,
    counterexample: Value,
    outcome: Result<CertificationOutcome, CertificationBridgeError>,
    cancellation: &CancellationToken,
) -> ImportedInvalidity {
    if cancellation.should_stop() {
        return ImportedInvalidity::Cancelled;
    }
    match outcome {
        Ok(CertificationOutcome::Certified(bundle)) => {
            let Some(witness) = bundle.witness.as_ref() else {
                return invalidity_failure_or_cancelled(
                    cancellation,
                    report_bridge_error(
                        artifacts,
                        provenance,
                        FailureOrigin::InvalidityCertification,
                        CertificationBridgeError::MalformedResponse(
                            "invalidity authority omitted its Witness".to_string(),
                        ),
                        Some(cancellation),
                    ),
                );
            };
            if bundle.classification != CertifiedClassification::Invalid {
                return invalidity_failure_or_cancelled(
                    cancellation,
                    report_bridge_error(
                        artifacts,
                        provenance,
                        FailureOrigin::InvalidityCertification,
                        CertificationBridgeError::MalformedResponse(
                            "invalidity authority returned the wrong classification".to_string(),
                        ),
                        Some(cancellation),
                    ),
                );
            }
            let witness = match import_file(
                artifacts,
                ArtifactKind::Witness,
                &witness.path,
                &witness.sha256,
                FailureOrigin::InvalidityCertification,
                Some(cancellation),
            ) {
                Ok(reference) => reference,
                Err(report) => {
                    return invalidity_failure_or_cancelled(
                        cancellation,
                        certification_failure(
                            FailureOrigin::InvalidityCertification,
                            FailureKind::PublicationFailure,
                            true,
                            report.scope(),
                            report
                                .detail()
                                .unwrap_or("import certified invalidity Witness"),
                            Vec::new(),
                        ),
                    );
                }
            };
            let record = match publish_record(
                artifacts,
                "invalidity_authority_accepted",
                provenance.record_fields(
                    json!({
                        "certificate_sha256": bundle.certificate_sha256,
                        "witness_sha256": bundle.witness.as_ref().map(|item| item.sha256.as_str()),
                    }),
                    &[witness],
                ),
                Some(cancellation),
            ) {
                Ok(reference) => reference,
                Err(report) => {
                    return invalidity_failure_or_cancelled(
                        cancellation,
                        remap_publication_with_prior(
                            report,
                            FailureOrigin::InvalidityCertification,
                            vec![witness],
                        ),
                    );
                }
            };
            // Import the certificate last. No fallible publication follows a
            // successful certificate import on this Rust-side boundary.
            let certificate = match import_file(
                artifacts,
                ArtifactKind::Certificate,
                &bundle.certificate,
                &bundle.certificate_sha256,
                FailureOrigin::InvalidityCertification,
                Some(cancellation),
            ) {
                Ok(reference) => reference,
                Err(report) => {
                    return invalidity_failure_or_cancelled(
                        cancellation,
                        certification_failure(
                            FailureOrigin::InvalidityCertification,
                            FailureKind::PublicationFailure,
                            true,
                            report.scope(),
                            report
                                .detail()
                                .unwrap_or("import certified invalidity certificate"),
                            vec![witness, record],
                        ),
                    );
                }
            };
            if cancellation.should_stop() {
                return ImportedInvalidity::Cancelled;
            }
            ImportedInvalidity::Certified(CertifiedInvalidity {
                certificate,
                witness,
                record,
                counterexample,
                source_w_index: None,
            })
        }
        Ok(CertificationOutcome::Rejected(rejection)) => {
            if cancellation.should_stop() {
                return ImportedInvalidity::Cancelled;
            }
            let attempt = match artifacts.next_attempt_id() {
                Ok(attempt) => attempt,
                Err(report) => {
                    return invalidity_failure_or_cancelled(
                        cancellation,
                        remap_publication(report, FailureOrigin::InvalidityCertification),
                    );
                }
            };
            if cancellation.should_stop() {
                return ImportedInvalidity::Cancelled;
            }
            let attempt_store = artifacts.scoped(ScopeTag::Attempt(attempt));
            let record = match publish_record(
                &attempt_store,
                "rejected_invalidity_candidate",
                provenance.record_fields(
                    json!({"kind": rejection.kind, "message": rejection.message}),
                    &[],
                ),
                Some(cancellation),
            ) {
                Ok(reference) => reference,
                Err(report) => {
                    return invalidity_failure_or_cancelled(
                        cancellation,
                        remap_publication(report, FailureOrigin::InvalidityCertification),
                    );
                }
            };
            if cancellation.should_stop() {
                return ImportedInvalidity::Cancelled;
            }
            ImportedInvalidity::Rejected(
                SearchFeedback::new(task.identity().clone(), artifacts.backend_id(), attempt)
                    .with_artifact_references(vec![record]),
            )
        }
        Ok(CertificationOutcome::Failed(failure)) => invalidity_failure_or_cancelled(
            cancellation,
            report_authority_failure(
                artifacts,
                provenance,
                FailureOrigin::InvalidityCertification,
                failure,
                Some(cancellation),
            ),
        ),
        Err(CertificationBridgeError::Cancelled) => ImportedInvalidity::Cancelled,
        Err(error) => invalidity_failure_or_cancelled(
            cancellation,
            report_bridge_error(
                artifacts,
                provenance,
                FailureOrigin::InvalidityCertification,
                error,
                Some(cancellation),
            ),
        ),
    }
}

fn invalidity_failure_or_cancelled(
    cancellation: &CancellationToken,
    report: FailureReport,
) -> ImportedInvalidity {
    if cancellation.should_stop() {
        ImportedInvalidity::Cancelled
    } else {
        ImportedInvalidity::Failure(report)
    }
}

fn import_file(
    artifacts: &ArtifactStore,
    kind: ArtifactKind,
    path: &Path,
    expected_sha256: &str,
    origin: FailureOrigin,
    cancellation: Option<&CancellationToken>,
) -> Result<ArtifactRef, FailureReport> {
    ensure_publication_allowed(cancellation)?;
    let payload = read_verified_artifact(path, expected_sha256, origin)?;
    ensure_publication_allowed(cancellation)?;
    artifacts.publish(kind, payload.into_boxed_slice())
}

fn read_verified_artifact(
    path: &Path,
    expected_sha256: &str,
    origin: FailureOrigin,
) -> Result<Vec<u8>, FailureReport> {
    let payload = fs::read(path).map_err(|error| {
        certification_failure(
            origin,
            FailureKind::PublicationFailure,
            true,
            FailureScope::LaneLocal,
            format!("read certification artifact {}: {error}", path.display()),
            Vec::new(),
        )
    })?;
    let mut digest = Sha256::new();
    digest.update(&payload);
    if !digest.finalize_hex().eq_ignore_ascii_case(expected_sha256) {
        return Err(certification_failure(
            origin,
            FailureKind::PublicationFailure,
            true,
            FailureScope::LaneLocal,
            format!(
                "certification artifact changed before import: {}",
                path.display()
            ),
            Vec::new(),
        ));
    }
    Ok(payload)
}

fn publish_record(
    artifacts: &ArtifactStore,
    status: &str,
    fields: Value,
    cancellation: Option<&CancellationToken>,
) -> Result<ArtifactRef, FailureReport> {
    ensure_publication_allowed(cancellation)?;
    let payload = serde_json::to_vec(&json!({
        "format_version": 1,
        "status": status,
        "fields": fields,
    }))
    .map_err(|error| {
        FailureReport::artifact(
            FailureKind::InfrastructureFailure,
            FailureScope::RunGlobal,
            format!("encode required certification record: {error}"),
        )
    })?;
    ensure_publication_allowed(cancellation)?;
    artifacts.publish(ArtifactKind::AcceptanceRecord, payload.into_boxed_slice())
}

fn ensure_publication_allowed(
    cancellation: Option<&CancellationToken>,
) -> Result<(), FailureReport> {
    if cancellation.is_some_and(CancellationToken::should_stop) {
        Err(FailureReport::artifact(
            FailureKind::PublicationFailure,
            FailureScope::LaneLocal,
            "certification artifact publication stopped by run control",
        ))
    } else {
        Ok(())
    }
}

fn report_authority_failure(
    artifacts: &ArtifactStore,
    provenance: &CertificationProvenance,
    origin: FailureOrigin,
    failure: CertificationFailure,
    cancellation: Option<&CancellationToken>,
) -> FailureReport {
    let mut references = Vec::new();
    if let Some(witness) = failure.witness.as_ref() {
        match import_file(
            artifacts,
            ArtifactKind::Witness,
            &witness.path,
            &witness.sha256,
            origin,
            cancellation,
        ) {
            Ok(reference) => references.push(reference),
            Err(report) => return remap_publication(report, origin),
        }
    }
    if let Some(diagnostic) = failure.diagnostic.as_ref() {
        match import_file(
            artifacts,
            ArtifactKind::FailureDiagnostic,
            &diagnostic.path,
            &diagnostic.sha256,
            origin,
            cancellation,
        ) {
            Ok(reference) => references.push(reference),
            Err(report) => {
                return certification_failure(
                    origin,
                    FailureKind::PublicationFailure,
                    true,
                    report.scope(),
                    report.detail().unwrap_or("import certification diagnostic"),
                    references,
                );
            }
        }
    }
    match publish_record(
        artifacts,
        "certification_failure",
        provenance.record_fields(
            json!({
                "kind": failure.kind,
                "phase": failure.phase,
                "message": failure.message,
                "elapsed_sec": failure.elapsed_sec,
                "process_status": failure.process_status,
                "returncode": failure.returncode,
                "stdout_sha256": failure.stdout_sha256,
                "stderr_sha256": failure.stderr_sha256,
            }),
            &references,
        ),
        cancellation,
    ) {
        Ok(reference) => references.push(reference),
        Err(report) => {
            return certification_failure(
                origin,
                FailureKind::PublicationFailure,
                true,
                report.scope(),
                report
                    .detail()
                    .unwrap_or("publish certification failure record"),
                references,
            );
        }
    }
    let kind = authority_failure_kind(origin, &failure);
    certification_failure(
        origin,
        kind,
        retryable(kind),
        FailureScope::LaneLocal,
        format!("{}: {}", failure.phase, failure.message),
        references,
    )
}

fn report_bridge_error(
    artifacts: &ArtifactStore,
    provenance: &CertificationProvenance,
    origin: FailureOrigin,
    error: CertificationBridgeError,
    cancellation: Option<&CancellationToken>,
) -> FailureReport {
    let kind = match error {
        CertificationBridgeError::TimedOut => FailureKind::CheckTimeout,
        CertificationBridgeError::Launch(_)
        | CertificationBridgeError::Transport(_)
        | CertificationBridgeError::ProcessFailed { .. } => FailureKind::ProcessFailure,
        CertificationBridgeError::MalformedResponse(_)
            if origin == FailureOrigin::InvalidityCertification =>
        {
            FailureKind::MalformedResult
        }
        CertificationBridgeError::InvalidRequest(_)
        | CertificationBridgeError::MalformedResponse(_)
        | CertificationBridgeError::Cleanup(_)
        | CertificationBridgeError::Cancelled => FailureKind::InfrastructureFailure,
    };
    let detail = error.to_string();
    let mut references = Vec::new();
    if let Ok(reference) = publish_record(
        artifacts,
        "certification_bridge_failure",
        provenance.record_fields(json!({"detail": detail}), &[]),
        cancellation,
    ) {
        references.push(reference);
    }
    certification_failure(
        origin,
        kind,
        retryable(kind),
        if matches!(error, CertificationBridgeError::Cleanup(_)) {
            FailureScope::RunGlobal
        } else {
            FailureScope::LaneLocal
        },
        detail,
        references,
    )
}

fn authority_failure_kind(origin: FailureOrigin, failure: &CertificationFailure) -> FailureKind {
    match failure.kind.as_str() {
        "unsupported_check" if origin == FailureOrigin::InvalidityCertification => {
            FailureKind::UnsupportedCheck
        }
        "fuel_exhausted" if origin == FailureOrigin::InvalidityCertification => {
            FailureKind::FuelExhausted
        }
        "malformed_result" if origin == FailureOrigin::InvalidityCertification => {
            FailureKind::MalformedResult
        }
        "certificate_construction_failure" => FailureKind::CertificateConstructionFailure,
        "certificate_rejected"
            if failure.phase.to_ascii_lowercase().contains("typecheck")
                || failure.message.to_ascii_lowercase().contains("typecheck") =>
        {
            FailureKind::CertificateTypecheckFailure
        }
        "certificate_rejected" | "certification_failed" | "not_counterexample" | "refuted" => {
            FailureKind::CertificateRejected
        }
        "certificate_typecheck_failure" => FailureKind::CertificateTypecheckFailure,
        "manifest_failure" => FailureKind::ManifestFailure,
        "publication_failure" => FailureKind::PublicationFailure,
        "check_timeout" | "timeout" => FailureKind::CheckTimeout,
        "inconclusive" if failure.process_status.as_deref() == Some("timeout") => {
            FailureKind::CheckTimeout
        }
        "process_failure" | "vampire_failure" => FailureKind::ProcessFailure,
        _ => FailureKind::InfrastructureFailure,
    }
}

fn retryable(kind: FailureKind) -> bool {
    matches!(
        kind,
        FailureKind::CheckTimeout
            | FailureKind::ProcessFailure
            | FailureKind::InfrastructureFailure
            | FailureKind::PublicationFailure
    )
}

fn remap_publication(report: FailureReport, origin: FailureOrigin) -> FailureReport {
    certification_failure(
        origin,
        FailureKind::PublicationFailure,
        true,
        report.scope(),
        report
            .detail()
            .unwrap_or("certification artifact publication failed"),
        report.artifact_references().to_vec(),
    )
}

fn remap_publication_with_prior(
    report: FailureReport,
    origin: FailureOrigin,
    mut prior: Vec<ArtifactRef>,
) -> FailureReport {
    for reference in report.artifact_references() {
        if !prior.contains(reference) {
            prior.push(*reference);
        }
    }
    certification_failure(
        origin,
        FailureKind::PublicationFailure,
        true,
        report.scope(),
        report
            .detail()
            .unwrap_or("certification artifact publication failed"),
        prior,
    )
}

fn certification_failure(
    origin: FailureOrigin,
    kind: FailureKind,
    retryable: bool,
    scope: FailureScope,
    detail: impl Into<String>,
    references: Vec<ArtifactRef>,
) -> FailureReport {
    FailureReport::try_new(
        origin,
        kind,
        retryable,
        scope,
        Some(detail.into()),
        references,
    )
    .expect("certification wrappers use permitted failure classifications")
}

// ------------------------------------------------------------
// Backend-Owned Blocking Work
// ------------------------------------------------------------

enum OwnedBlockingOutcome<T> {
    Complete(T),
    Cancelled,
    Panicked(String),
}

async fn run_owned_blocking<T, F>(
    artifacts: &ArtifactStore,
    caller_cancellation: &CancellationToken,
    work: F,
) -> OwnedBlockingOutcome<T>
where
    T: Send + 'static,
    F: FnOnce(CancellationToken) -> T + Send + 'static,
{
    let registration = match artifacts.register_owned_work() {
        Ok(registration) => registration,
        Err(report) => {
            return OwnedBlockingOutcome::Panicked(format!(
                "register certification-owned work: {report:?}"
            ));
        }
    };
    let worker_cancellation = CancellationToken::new();
    let mut cancellation_guard = CancellationOnDrop(Some(worker_cancellation.clone()));
    let mut worker = tokio::task::spawn_blocking(move || {
        let _completion = OwnedWorkCompletion(Some(registration));
        work(worker_cancellation)
    });
    let result = tokio::select! {
        result = &mut worker => result,
        _ = caller_cancellation.cancelled() => {
            cancellation_guard.cancel();
            let _ = worker.await;
            return OwnedBlockingOutcome::Cancelled;
        }
    };
    cancellation_guard.disarm();
    match result {
        Ok(value) => OwnedBlockingOutcome::Complete(value),
        Err(error) => {
            OwnedBlockingOutcome::Panicked(format!("certification blocking worker failed: {error}"))
        }
    }
}

struct OwnedWorkCompletion(Option<OwnedWorkRegistration>);

impl Drop for OwnedWorkCompletion {
    fn drop(&mut self) {
        if let Some(registration) = self.0.take() {
            registration.discharge();
        }
    }
}

struct CancellationOnDrop(Option<CancellationToken>);

impl CancellationOnDrop {
    fn cancel(&mut self) {
        if let Some(cancellation) = self.0.take() {
            cancellation.cancel();
        }
    }

    fn disarm(&mut self) {
        self.0 = None;
    }
}

impl Drop for CancellationOnDrop {
    fn drop(&mut self) {
        self.cancel();
    }
}

// ------------------------------------------------------------
// Source Instance Validation
// ------------------------------------------------------------

fn validate_instance(
    task: &SynthesisTask,
    value: &Value,
) -> Result<(), CertificationInstanceError> {
    let object = value.as_object().ok_or_else(|| {
        CertificationInstanceError("source Instance must be a JSON object".to_string())
    })?;
    let schema = task
        .solver_relations()
        .iter()
        .map(|relation| {
            relation_display_name(relation.key().as_str()).map(|name| (name, relation.arity()))
        })
        .collect::<Result<BTreeMap<_, _>, _>>()?;
    if object.keys().collect::<BTreeSet<_>>() != schema.keys().collect::<BTreeSet<_>>() {
        return Err(CertificationInstanceError(
            "source Instance relation set differs from task.schema".to_string(),
        ));
    }
    for (name, arity) in schema {
        let rows = object[&name].as_array().ok_or_else(|| {
            CertificationInstanceError(format!("relation {name} must be a tuple list"))
        })?;
        let mut seen = BTreeSet::new();
        for row in rows {
            let cells = row.as_array().ok_or_else(|| {
                CertificationInstanceError(format!("relation {name} contains a non-tuple"))
            })?;
            if u64::try_from(cells.len()).ok() != Some(arity)
                || cells.iter().any(|cell| {
                    !(cell.is_string()
                        || cell.is_boolean()
                        || cell.as_number().is_some_and(is_nonnegative_integral_number))
                })
            {
                return Err(CertificationInstanceError(format!(
                    "relation {name} contains an ill-typed tuple"
                )));
            }
            let key = serde_json::to_string(cells).map_err(|error| {
                CertificationInstanceError(format!("encode relation tuple: {error}"))
            })?;
            if !seen.insert(key) {
                return Err(CertificationInstanceError(format!(
                    "relation {name} contains a duplicate tuple"
                )));
            }
        }
    }
    Ok(())
}

fn is_nonnegative_integral_number(number: &serde_json::Number) -> bool {
    let text = number.to_string();
    !text.is_empty() && text.bytes().all(|byte| byte.is_ascii_digit())
}

fn relation_display_name(key: &str) -> Result<String, CertificationInstanceError> {
    let rest = key
        .strip_prefix("rel:")
        .ok_or_else(|| CertificationInstanceError(format!("malformed relation key {key:?}")))?;
    let (base, index) = rest
        .rsplit_once(':')
        .ok_or_else(|| CertificationInstanceError(format!("malformed relation key {key:?}")))?;
    let index = index
        .parse::<u64>()
        .map_err(|_| CertificationInstanceError(format!("malformed relation key {key:?}")))?;
    if index == 0 {
        Ok(base.to_string())
    } else {
        let display_index = index.checked_add(1).ok_or_else(|| {
            CertificationInstanceError("relation display index overflow".to_string())
        })?;
        Ok(format!("{base}_{display_index}"))
    }
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicU64, Ordering};

    use super::*;

    static NEXT_TEST_FILE: AtomicU64 = AtomicU64::new(0);

    fn certification_test_task() -> SynthesisTask {
        SynthesisTask::from_json(
            r#"{
              "format_version":3,"semantic_version":1,"encoding_version":1,
              "identity":{"canonical_id":"CertificationTest","module":"Whiel.Test.CertificationTest","namespace":"Whiel.Test.CertificationTest","source_sha256":"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"},
              "schema":{"expression":"Whiel.Test.CertificationTest.programSchema","display":"{R}"},
              "original":{"pre":{"expression":"Whiel.Test.CertificationTest.inputPre","display":"true"},"command":{"expression":"Whiel.Test.CertificationTest.inputCmd","display":"SKIP"},"post":{"expression":"Whiel.Test.CertificationTest.inputPost","display":"true"}},
              "preprocessed":{"pre":{"expression":"Whiel.Test.CertificationTest.inputPreproc.loopPre","display":"true"},"command":{"expression":"Whiel.Test.CertificationTest.inputPreproc.loopCmd","display":"SKIP"},"post":{"expression":"Whiel.Test.CertificationTest.inputPreproc.loopPost","display":"true"}},
              "preprocessing_evidence":{"expression":"Whiel.Test.CertificationTest.inputPreproc"},
              "solver":{"schema_relations":[{"key":"rel:R:0","arity":1}],"task_constants":[],"preprocessed_pre":{"source_id":"task.preprocessed_pre","expression":"Whiel.Test.CertificationTest.inputPreproc.loopPre","no_bound_expression":"Whiel.Test.CertificationTest.inputPreproc.loopPre_noBound","constants":[],"relations":[]},"preprocessed_post":{"source_id":"task.preprocessed_post","expression":"Whiel.Test.CertificationTest.inputPreproc.loopPost","no_bound_expression":"Whiel.Test.CertificationTest.inputPreproc.loopPost_noBound","constants":[],"relations":[]},"loop_guard":{"source_id":"task.loop_guard","constants":[],"relations":[]},"negated_loop_guard":{"source_id":"task.negated_loop_guard","constants":[],"relations":[]}}
            }"#,
        )
        .unwrap()
    }

    #[test]
    fn symbolic_lanes_receive_disjoint_certification_paths() {
        let runtime = CertificationRuntime::new(
            CertificationBridgeCommand::new("python3", "."),
            "certification-work",
            "solution",
        );
        let inv = runtime.for_symbolic_inv_lane();
        let cex = runtime.for_symbolic_cex_lane();

        assert_eq!(
            inv.work_directory,
            PathBuf::from("certification-work/symbolic-inv")
        );
        assert_eq!(
            cex.work_directory,
            PathBuf::from("certification-work/symbolic-cex")
        );
        assert_eq!(
            inv.solution_directory,
            PathBuf::from("solution/symbolic-inv")
        );
        assert_eq!(
            cex.solution_directory,
            PathBuf::from("solution/symbolic-cex")
        );
        assert_ne!(inv.work_directory, cex.work_directory);
        assert_ne!(inv.solution_directory, cex.solution_directory);
    }

    #[test]
    fn concrete_number_boundary_accepts_exact_naturals_only() {
        for accepted in ["0", "184467440737095516160000"] {
            let value: Value = serde_json::from_str(accepted).unwrap();
            assert!(
                value
                    .as_number()
                    .is_some_and(is_nonnegative_integral_number),
                "{accepted}"
            );
        }
        for rejected in ["-1", "1.5", "1e2"] {
            let value: Value = serde_json::from_str(rejected).unwrap();
            assert!(
                !value
                    .as_number()
                    .is_some_and(is_nonnegative_integral_number),
                "{rejected}"
            );
        }
    }

    #[test]
    fn artifact_import_rechecks_the_validated_digest_after_a_path_change() {
        let sequence = NEXT_TEST_FILE.fetch_add(1, Ordering::Relaxed);
        let directory = std::env::temp_dir().join(format!(
            "whiel-certification-import-{}-{sequence}",
            std::process::id()
        ));
        fs::create_dir_all(&directory).unwrap();
        let path = directory.join("certificate");
        fs::write(&path, b"accepted bytes").unwrap();
        let mut expected = Sha256::new();
        expected.update(b"accepted bytes");
        let expected = expected.finalize_hex();

        fs::write(&path, b"changed bytes").unwrap();
        let report = read_verified_artifact(&path, &expected, FailureOrigin::ValidityCertification)
            .unwrap_err();

        assert_eq!(report.origin(), FailureOrigin::ValidityCertification);
        assert_eq!(report.kind(), FailureKind::PublicationFailure);
        assert!(report.detail().unwrap().contains("changed before import"));
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn invalidity_import_after_bound_deadline_publishes_no_authority_artifacts() {
        let sequence = NEXT_TEST_FILE.fetch_add(1, Ordering::Relaxed);
        let directory = std::env::temp_dir().join(format!(
            "whiel-invalidity-deadline-import-{}-{sequence}",
            std::process::id()
        ));
        fs::create_dir_all(&directory).unwrap();

        let witness_path = directory.join("witness.json");
        let certificate_path = directory.join("certificate.lean");
        let witness_payload = br#"{"accepted":true}"#;
        let certificate_payload = b"theorem accepted : True := by trivial\n";
        fs::write(&witness_path, witness_payload).unwrap();
        fs::write(&certificate_path, certificate_payload).unwrap();
        let mut witness_digest = Sha256::new();
        witness_digest.update(witness_payload);
        let mut certificate_digest = Sha256::new();
        certificate_digest.update(certificate_payload);

        let task = certification_test_task();
        let (owner, artifacts) = crate::artifact::new_artifact_store(
            &task,
            crate::artifact::ArtifactStoreConfig::new(directory.join("artifacts")),
        )
        .unwrap();
        let before = artifacts.diagnostics();
        let counterexample = json!({"P_2": [], "R": []});
        let provenance = CertificationProvenance::invalidity(&task, &counterexample);
        let cancellation = CancellationToken::new();
        let deadline = tokio::time::Instant::now() + std::time::Duration::from_millis(5);
        assert!(cancellation.bind_absolute_deadline(deadline));

        // Model a blocking authority call which began while the run was live
        // and returned an importable bundle only after the bound deadline.
        while !cancellation.deadline_elapsed() {
            std::thread::yield_now();
        }
        let imported = import_invalidity_outcome(
            &artifacts,
            &task,
            &provenance,
            counterexample,
            Ok(CertificationOutcome::Certified(
                crate::certification::CertifiedBundle {
                    classification: CertifiedClassification::Invalid,
                    bundle: directory.join("bundle"),
                    certificate: certificate_path,
                    certificate_sha256: certificate_digest.finalize_hex(),
                    witness: Some(crate::certification::WitnessArtifactRef {
                        path: witness_path,
                        sha256: witness_digest.finalize_hex(),
                    }),
                },
            )),
            &cancellation,
        );

        assert!(matches!(imported, ImportedInvalidity::Cancelled));
        let after = artifacts.diagnostics();
        assert_eq!(
            after.required_payloads_published,
            before.required_payloads_published
        );
        assert_eq!(
            after.required_payload_files_created,
            before.required_payload_files_created
        );
        owner.settle().unwrap();
        fs::remove_dir_all(directory).unwrap();
    }
}
