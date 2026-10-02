//! Strict public observation DTOs. Owned values confer no engine authority.

use serde::{Deserialize, Serialize};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(transparent)]
pub struct PhysicalAttemptId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(transparent)]
pub struct LedgerRowOrdinal(pub u64);

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FeedbackBindingV1 {
    pub task_digest: String,
    pub scope_digest: String,
    pub run_digest: String,
    pub consultation_digest: String,
    pub state_snapshot_digest: String,
    pub validation_manifest_digest: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PushBindingV1 {
    pub task_digest: String,
    pub scope_digest: String,
    pub run_digest: String,
    pub consultation_digest: String,
    pub state_snapshot_digest: String,
    pub validation_manifest_digest: String,
    pub validation_ordinal: u64,
    pub policy_digest: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ResponseBindingV1 {
    pub task_digest: String,
    pub scope_digest: String,
    pub run_digest: String,
    pub consultation_digest: String,
    pub state_snapshot_digest: String,
    pub validation_manifest_digest: String,
    pub request_digest: String,
    pub validation_ordinal: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ClauseV1 {
    pub clause_id: u64,
    pub record_digest: String,
    pub formula_digest: String,
    /// The exact parseable clause source the verifier admitted, null only
    /// where that text is unsafe to present.
    #[serde(deserialize_with = "nullable")]
    pub canonical_source: Option<String>,
    /// The record's display spelling of the same clause, under the same rule.
    #[serde(deserialize_with = "nullable")]
    pub display: Option<String>,
}

/// A clause named as an authorization token rather than shown: the three
/// identity fields, without the record's text. A drop reference sits in the
/// same push entry as the clause it authorizes, which already carries that
/// clause's source, so it does not repeat it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ClauseReferenceV1 {
    pub clause_id: u64,
    pub record_digest: String,
    pub formula_digest: String,
}

/// A clause as a caller names it in a query argument. The digests are the
/// identity; the record's text is optional, so a reference copied whole out of
/// the push and one built from the digests alone are both exact arguments and
/// both recorded as they were sent.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ClauseArgumentV1 {
    pub clause_id: u64,
    pub record_digest: String,
    pub formula_digest: String,
    #[serde(default, skip_serializing_if = "PresenceV1::is_absent")]
    pub canonical_source: PresenceV1<String>,
    #[serde(default, skip_serializing_if = "PresenceV1::is_absent")]
    pub display: PresenceV1<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DropV1 {
    pub clause: ClauseReferenceV1,
    pub consultation_digest: String,
    pub authorization_digest: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum OriginV1 {
    Submitted,
    Symbolic,
    EdbPreconditionSystem,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RoleV1 {
    Initialization,
    Maintenance,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ProfileV1 {
    Direct,
    #[serde(rename = "casc_2025")]
    Casc2025,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum InconclusiveReasonV1 {
    TimedOut,
    SolverUnknown,
    PeerFailed,
    UnvalidatedRefutation,
    Cancelled,
    Suspended,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum InvalidationReasonV1 {
    AntecedentClauseDeleted,
    AntecedentClausePromoted,
    AntecedentClauseExcluded,
    SnapshotChanged,
    SystemClausesInstalled,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", deny_unknown_fields, rename_all = "snake_case")]
pub enum DeadReasonV1 {
    ProphecyFreeInitializationRefuted { attempt: LedgerRowOrdinal },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "cause", deny_unknown_fields, rename_all = "snake_case")]
pub enum DeathV1 {
    Dropped {},
    Refuted { reason: DeadReasonV1 },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum StatusV1 {
    Committed {
        level: u64,
    },
    Pending {
        level: u64,
    },
    Dead {
        cause: DeathCauseV1,
        #[serde(skip_serializing_if = "Option::is_none")]
        reason: Option<DeadReasonV1>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum DeathCauseV1 {
    Dropped,
    Refuted,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CoreV1 {
    pub clause: ClauseV1,
    pub source: OriginV1,
    pub level: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PendingV1 {
    pub clause: ClauseV1,
    pub source: OriginV1,
    pub minimum_level: u64,
    pub current_level: u64,
    #[serde(deserialize_with = "nullable")]
    pub drop_reference: Option<DropV1>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LastV1 {
    pub clause: ClauseV1,
    pub source: OriginV1,
    pub outcome: StatusV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TruncationV1 {
    pub list: String,
    pub shown: u64,
    pub total: u64,
    #[serde(deserialize_with = "host_limit_name")]
    pub limit: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RefusalV1 {
    #[serde(deserialize_with = "host_limit_name")]
    pub limit: String,
    pub value: u64,
    pub observed: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TripleV1 {
    pub precondition: String,
    pub command: String,
    pub postcondition: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TaskV1 {
    pub canonical_id: String,
    pub task_digest: String,
    pub semantic_version: u64,
    pub encoding_version: u64,
    pub schema: String,
    pub original: TripleV1,
    pub preprocessed: TripleV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RelationV1 {
    pub key: String,
    pub arity: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProphecyV1 {
    pub program_relation: String,
    pub prophecy_relation: String,
    pub arity: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AmbientV1 {
    pub scope_digest: String,
    pub relations: Vec<RelationV1>,
    pub prophecy_map: Vec<ProphecyV1>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HostLimitV1 {
    #[serde(deserialize_with = "host_limit_name")]
    pub limit: String,
    pub value: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ResourcePresentationV1 {
    pub api_packet_bytes: u64,
    #[serde(deserialize_with = "nullable")]
    pub configured: Option<ResourceLimitsV1>,
}

/// The standing presentation: the run's data, and no explanatory prose. The
/// contract's rules live in the report and are enforced by the controller;
/// stating them to an agent is the proposer's own work.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PresentationV1 {
    pub schema_version: u64,
    pub task: TaskV1,
    pub ambient_schema: AmbientV1,
    pub host_limits: Vec<HostLimitV1>,
    pub resource_limits: ResourcePresentationV1,
    pub presentation_digest: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum FailureScopeV1 {
    LaneLocal,
    RunGlobal,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum FailureOriginV1 {
    RunControl,
    ArtifactSettlement,
    AgentConsultation,
    ResponseValidation,
    EncodingPreparation,
    InitializationExecution,
    VampireProofSearch,
    VampireFiniteModelBuilding,
    VampireRace,
    SymbolicRace,
    ModelDecoding,
    TerminationCheck,
    MaintenanceExecution,
    MaintenanceHistory,
    ValidityCertification,
    InvalidityCertification,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum FailureKindV1 {
    OverallTimeout,
    Interrupted,
    ConsultationTimeout,
    IterationLimitExhausted,
    SourceExhausted,
    CorrectionExhausted,
    NoResponse,
    TransportFailure,
    ValidationInfrastructureFailure,
    UnsupportedCheck,
    FuelExhausted,
    CheckTimeout,
    SolverUnknown,
    MalformedResult,
    ProcessFailure,
    InfrastructureFailure,
    ConcurrentWorkerFailures,
    CertificateConstructionFailure,
    CertificateRejected,
    CertificateTypecheckFailure,
    ManifestFailure,
    PublicationFailure,
    HistoryLogFailure,
    StateInvariantViolation,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ArtifactRoleV1 {
    Proof,
    Model,
    EmptyCheck,
    RouteReceipt,
    ValidationReceipt,
    ProgressReceipt,
    FailureDiagnostic,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ArtifactKindV1 {
    Query,
    Proof,
    Model,
    EmptyInstanceCheck,
    InitializationCheck,
    Certificate,
    AcceptanceRecord,
    Witness,
    FailureDiagnostic,
    RuntimeTrace,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ArtifactV1 {
    pub stable_id: String,
    pub role: ArtifactRoleV1,
    pub kind: ArtifactKindV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FailureV1 {
    pub origin: FailureOriginV1,
    pub kind: FailureKindV1,
    pub retryable: bool,
    pub scope: FailureScopeV1,
    pub has_withheld_detail: bool,
    pub artifacts: Vec<ArtifactV1>,
    pub withheld_artifacts: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "outcome", deny_unknown_fields, rename_all = "snake_case")]
pub enum PostconditionOpenV1 {
    Refuted {
        #[serde(deserialize_with = "nullable")]
        attempt: Option<PhysicalAttemptId>,
    },
    Inconclusive {
        reason: InconclusiveReasonV1,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CounterexampleRejectedV1 {
    pub code: String,
    pub reason: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", deny_unknown_fields, rename_all = "snake_case")]
pub enum LatestV1 {
    Initial {},
    PostconditionOpen {
        postcondition_open: PostconditionOpenV1,
    },
    Failure {
        failure: FailureV1,
    },
    CounterexampleRejected {
        counterexample_rejected: CounterexampleRejectedV1,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FeedbackV1 {
    pub schema_version: u64,
    pub binding: FeedbackBindingV1,
    pub iteration: u64,
    #[serde(deserialize_with = "decimal_nanos")]
    pub remaining_search_budget_ns: String,
    pub presentation: PresentationV1,
    pub core: Vec<CoreV1>,
    pub last_round: Vec<LastV1>,
    pub pending: Vec<PendingV1>,
    pub latest: LatestV1,
    pub tools: Vec<ToolV1>,
    pub state_revision: u64,
    #[serde(
        default,
        deserialize_with = "present",
        skip_serializing_if = "Option::is_none"
    )]
    pub truncated: Option<TruncationV1>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CorrectionBindingV1 {
    pub consultation_digest: String,
    pub rejected_response_digest: String,
    pub correction_ordinal: u64,
}

/// The keys a diagnostic can name at its `path`: those the submission left
/// out, those it added, and those whose value differs from the one the
/// controller issued. Each list is in key order.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DiagnosticDetailsV1 {
    pub missing: Vec<String>,
    pub unexpected: Vec<String>,
    pub changed: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CorrectionDiagnosticV1 {
    pub code: String,
    pub message: String,
    #[serde(deserialize_with = "nullable")]
    pub item_index: Option<u64>,
    #[serde(deserialize_with = "nullable")]
    pub path: Option<String>,
    /// Where inside the named clause the fault is, when the diagnostic can
    /// locate it. Additive and absent on every diagnostic that cannot, so a
    /// consumer that does not read it is unaffected.
    #[serde(
        default,
        deserialize_with = "present",
        skip_serializing_if = "Option::is_none"
    )]
    pub offset: Option<u64>,
    #[serde(
        default,
        deserialize_with = "present",
        skip_serializing_if = "Option::is_none"
    )]
    pub host_limit: Option<RefusalV1>,
    #[serde(
        default,
        deserialize_with = "present",
        skip_serializing_if = "Option::is_none"
    )]
    pub details: Option<DiagnosticDetailsV1>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CorrectionV1 {
    pub schema_version: u64,
    pub binding: CorrectionBindingV1,
    pub diagnostics: Vec<CorrectionDiagnosticV1>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum PushOperationV1 {
    ProposerObservation,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PushV1 {
    pub schema_version: u64,
    pub operation: PushOperationV1,
    pub binding: PushBindingV1,
    pub feedback: FeedbackV1,
    #[serde(deserialize_with = "nullable")]
    pub correction: Option<CorrectionV1>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ToolV1 {
    Countermodel,
    StrongestRefutations,
    History,
    Ledger,
    ValidateClauses,
    EvaluateClauses,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ResourceLimitsV1 {
    pub api_traffic_bytes: u64,
    pub api_messages: u64,
    pub artifact_bytes: u64,
    pub artifact_files: u64,
    pub workspace_bytes: u64,
    pub workspace_files: u64,
    pub minimum_free_bytes: u64,
    pub workspace_entries: u64,
    pub workspace_directories: u64,
}
// Optional tool arguments accept both omission and null. Preserve that exact
// distinction; unlike a required nullable property, neither may stand for the
// other in recorded input. Invalid argument bytes stay outside these DTOs.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub enum PresenceV1<T> {
    #[default]
    Absent,
    Null,
    Value(T),
}

impl<T> PresenceV1<T> {
    pub fn is_absent(&self) -> bool {
        matches!(self, Self::Absent)
    }
}

impl<T: Serialize> Serialize for PresenceV1<T> {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self {
            Self::Value(value) => value.serialize(serializer),
            Self::Null => serializer.serialize_none(),
            Self::Absent => Err(serde::ser::Error::custom("an absent field must be omitted")),
        }
    }
}

impl<'de, T: Deserialize<'de>> Deserialize<'de> for PresenceV1<T> {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Ok(match Option::<T>::deserialize(deserializer)? {
            Some(value) => Self::Value(value),
            None => Self::Null,
        })
    }
}

fn nullable<'de, D, T>(deserializer: D) -> Result<Option<T>, D::Error>
where
    D: serde::Deserializer<'de>,
    T: Deserialize<'de>,
{
    Option::<T>::deserialize(deserializer)
}

fn present<'de, D, T>(deserializer: D) -> Result<Option<T>, D::Error>
where
    D: serde::Deserializer<'de>,
    T: Deserialize<'de>,
{
    T::deserialize(deserializer).map(Some)
}

fn host_limit_name<'de, D: serde::Deserializer<'de>>(deserializer: D) -> Result<String, D::Error> {
    let name = String::deserialize(deserializer)?;
    if HOST_LIMIT_NAMES.contains(&name.as_str()) {
        Ok(name)
    } else {
        Err(serde::de::Error::custom("unknown host limit name"))
    }
}

fn decimal_nanos<'de, D: serde::Deserializer<'de>>(deserializer: D) -> Result<String, D::Error> {
    let value = String::deserialize(deserializer)?;
    match value.parse::<u128>() {
        Ok(nanos) if nanos.to_string() == value => Ok(value),
        _ => Err(serde::de::Error::custom(
            "nanoseconds must be a canonical unsigned decimal string",
        )),
    }
}

impl<'de> Deserialize<'de> for StatusV1 {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        #[derive(Deserialize)]
        #[serde(tag = "kind", deny_unknown_fields, rename_all = "snake_case")]
        enum Wire {
            Committed {
                level: u64,
            },
            Pending {
                level: u64,
            },
            Dead {
                cause: DeathCauseV1,
                #[serde(default)]
                reason: PresenceV1<DeadReasonV1>,
            },
        }
        match Wire::deserialize(deserializer)? {
            Wire::Committed { level } => Ok(Self::Committed { level }),
            Wire::Pending { level } => Ok(Self::Pending { level }),
            Wire::Dead {
                cause: DeathCauseV1::Dropped,
                reason: PresenceV1::Absent,
            } => Ok(Self::Dead {
                cause: DeathCauseV1::Dropped,
                reason: None,
            }),
            Wire::Dead {
                cause: DeathCauseV1::Refuted,
                reason: PresenceV1::Value(reason),
            } => Ok(Self::Dead {
                cause: DeathCauseV1::Refuted,
                reason: Some(reason),
            }),
            Wire::Dead { .. } => Err(serde::de::Error::custom(
                "dead/dropped must omit reason; dead/refuted requires a non-null reason",
            )),
        }
    }
}

/// One host limit's stable wire name.
pub type HostLimitName = &'static str;

/// Every limit's wire name, in the order the presentation lists them.
pub const HOST_LIMIT_NAMES: [HostLimitName; 10] = [
    "catalog_size",
    "clause_text_bytes",
    "countermodel_retention_tuples",
    "drop_references",
    "evaluation_cost",
    "level_bound",
    "proposal_size",
    "pushed_core",
    "reply_bytes",
    "strongest_refutations",
];
