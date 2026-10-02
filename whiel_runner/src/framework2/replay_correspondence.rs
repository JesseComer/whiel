//! Checked owner inputs for the exhaustive V1 correspondence categories.
//! Durable projections are data. Only fresh owner checks establish a pair.

use super::catalog::task_identity_fields;
use super::production::*;
use super::replay_audit::*;
use super::replay_identity::{LedgerRowOrdinal, PhysicalAttemptId, ReplayDivergence};
use super::replay_production_compare::{ReplayProductionBindings, ReplayProductionIdentity};
use super::replay_wire_compare::{ReplayWireBindings, ReplayWireIdentity};
use super::transcript::{TranscriptCoordinates, TranscriptHeader};
use super::{
    ExtendedClauseOrigin, FixedAmbientTaskScope, FrameworkIIComponentMetadata,
    LeveledCandidateSnapshot, LeveledClauseCatalog, LeveledClauseRecord,
};
use crate::encoding::canonical_value_sha256;
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ReplayCaptureError {
    UnsupportedSchema,
    SemanticRedaction,
    OwnerInvariant,
    LimitExceeded,
}
impl From<ReplayProductionError> for ReplayCaptureError {
    fn from(e: ReplayProductionError) -> Self {
        match e {
            ReplayProductionError::PrivateDetailRedacted => Self::SemanticRedaction,
            _ => Self::OwnerInvariant,
        }
    }
}
pub(super) fn decode_owner<T: serde::de::DeserializeOwned>(
    value: &Value,
) -> Result<T, ReplayCaptureError> {
    serde_json::from_value(value.clone()).map_err(|_| ReplayCaptureError::UnsupportedSchema)
}

fn nullable<'de, D, T>(d: D) -> Result<Option<T>, D::Error>
where
    D: serde::Deserializer<'de>,
    T: Deserialize<'de>,
{
    Option::<T>::deserialize(d)
}
fn present<'de, D, T>(d: D) -> Result<Option<T>, D::Error>
where
    D: serde::Deserializer<'de>,
    T: Deserialize<'de>,
{
    T::deserialize(d).map(Some)
}
pub(super) fn checked_projection<T: Serialize>(projection: T) -> Result<T, ReplayCaptureError> {
    let bytes =
        serde_json::to_vec(&projection).map_err(|_| ReplayCaptureError::UnsupportedSchema)?;
    if super::Redaction::changes(&bytes) {
        Err(ReplayCaptureError::SemanticRedaction)
    } else {
        Ok(projection)
    }
}
fn same<T: PartialEq>(left: &T, right: &T, path: &str) -> Result<(), ReplayDivergence> {
    if left == right {
        Ok(())
    } else {
        Err(ReplayDivergence {
            path: path.into(),
            reason: "semantic value differs".into(),
        })
    }
}
fn invariant(ok: bool) -> Result<(), ReplayCaptureError> {
    if ok {
        Ok(())
    } else {
        Err(ReplayCaptureError::OwnerInvariant)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayTaskIdentity {
    pub canonical_id: String,
    pub module: String,
    pub namespace: String,
    pub source_sha256: ReplaySha256,
    pub semantic_version: u64,
    pub encoding_version: u64,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(super) enum ReplayComponentRole {
    Precondition,
    Guard,
    NegatedThetaGuard,
    NegatedGuard,
    Postcondition,
    Clause,
    ThetaClause,
    MaintenanceWp,
    CollapsedClause,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(super) enum ReplayComponentTag {
    #[serde(rename = "whiel_framework_ii_fixed_ambient_component")]
    V1,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayComponentIdentity {
    kind: ReplayComponentTag,
    version: ReplayVersion<1>,
    scope_identity: ReplayScopeIdentity,
    role: ReplayComponentRole,
    result_formula_identity: ReplayQfIdentity,
    source_id: String,
    #[serde(
        default,
        deserialize_with = "present",
        skip_serializing_if = "Option::is_none"
    )]
    base_clause_identity: Option<ReplayClauseIdentity>,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayComponent {
    role: ReplayComponentRole,
    identity: ReplayComponentIdentity,
    digest: ReplaySha256,
    formula_identity: ReplayQfIdentity,
    formula_digest: ReplaySha256,
    canonical_source: String,
    source_id: String,
    display: String,
    relation_keys: Vec<String>,
    constant_keys: Vec<String>,
    semantic_theorem: String,
}
impl ReplayComponent {
    fn capture(component: &FrameworkIIComponentMetadata) -> Result<Self, ReplayCaptureError> {
        let formula = component.formula();
        let projection = Self {
            role: decode_owner(&json!(component.role().as_str()))?,
            identity: decode_owner(component.identity())?,
            digest: decode_owner(&json!(component.digest()))?,
            formula_identity: decode_owner(formula.identity())?,
            formula_digest: decode_owner(&json!(formula.identity_sha256()))?,
            canonical_source: formula.canonical_source().into(),
            source_id: formula.source_id().into(),
            display: formula.display().into(),
            relation_keys: formula
                .relation_keys()
                .iter()
                .map(|k| k.as_str().to_owned())
                .collect(),
            constant_keys: formula
                .constant_keys()
                .iter()
                .map(|k| k.as_str().to_owned())
                .collect(),
            semantic_theorem: formula.semantic_theorem().into(),
        };
        projection.verify()?;
        checked_projection(projection)
    }
    fn verify(&self) -> Result<(), ReplayCaptureError> {
        invariant(
            self.digest.0 == canonical_value_sha256(&json!(self.identity))
                && self.formula_digest.0 == canonical_value_sha256(&json!(self.formula_identity))
                && self.identity.role == self.role
                && self.identity.source_id == self.source_id
                && self.identity.result_formula_identity == self.formula_identity,
        )
    }
    fn bundle_fields(&self) -> Value {
        json!({"role":self.role,"identity":self.identity,"digest":self.digest,
        "formula_identity":self.formula_identity,"canonical_source":self.canonical_source,"source_id":self.source_id})
    }
}
fn component_bundle_digest(domain: &str, components: &[ReplayComponent]) -> String {
    canonical_value_sha256(
        &json!({"domain":domain,"components":components.iter().map(ReplayComponent::bundle_fields).collect::<Vec<_>>() }),
    )
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayScopeProjection {
    pub task: ReplayTaskIdentity,
    pub identity: ReplayScopeIdentity,
    pub digest: ReplaySha256,
    pub components: Vec<ReplayComponent>,
    pub components_digest: ReplaySha256,
}
impl ReplayScopeProjection {
    pub(super) fn capture(scope: &FixedAmbientTaskScope) -> Result<Self, ReplayCaptureError> {
        let projection = Self {
            task: decode_owner(&task_identity_fields(scope))?,
            identity: decode_owner(scope.identity())?,
            digest: decode_owner(&json!(scope.identity_sha256()))?,
            components: scope
                .components()
                .components()
                .iter()
                .map(ReplayComponent::capture)
                .collect::<Result<_, _>>()?,
            components_digest: decode_owner(&json!(scope.components().digest()))?,
        };
        projection.verify()?;
        checked_projection(projection)
    }
    fn verify(&self) -> Result<(), ReplayCaptureError> {
        invariant(canonical_value_sha256(&json!(self.identity)) == self.digest.0)?;
        invariant(
            self.identity.task_canonical_id == self.task.canonical_id
                && self.identity.task_module == self.task.module
                && self.identity.task_namespace == self.task.namespace
                && self.identity.task_source_sha256 == self.task.source_sha256
                && self.identity.semantic_version == self.task.semantic_version
                && self.identity.encoding_version == self.task.encoding_version,
        )?;
        invariant(
            self.components.iter().map(|c| &c.role).eq([
                ReplayComponentRole::Precondition,
                ReplayComponentRole::Guard,
                ReplayComponentRole::NegatedThetaGuard,
                ReplayComponentRole::NegatedGuard,
                ReplayComponentRole::Postcondition,
            ]
            .iter()),
        )?;
        for c in &self.components {
            c.verify()?;
            invariant(
                c.identity.scope_identity == self.identity
                    && c.identity.base_clause_identity.is_none(),
            )?;
        }
        invariant(
            component_bundle_digest(
                "whiel-framework-ii-fixed-ambient-task-components-v1",
                &self.components,
            ) == self.components_digest.0,
        )
    }
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub(super) enum ReplayRecordOrigin {
    Submitted {},
    Symbolic {},
    EdbPreconditionSystem {
        conjunct_ordinal: u64,
        route_digest: ReplaySha256,
    },
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayRecordProjection {
    pub id: u64,
    pub protected: bool,
    pub formula: ReplayClauseIdentity,
    pub formula_digest: ReplaySha256,
    pub canonical_source: String,
    pub display: String,
    pub formula_order_key: String,
    pub relation_keys: Vec<String>,
    pub origin: ReplayRecordOrigin,
    pub minimum_level: u64,
    pub mentions_prophecy: bool,
    pub components: Vec<ReplayComponent>,
    pub components_digest: ReplaySha256,
    pub record_digest: ReplaySha256,
}
impl ReplayRecordProjection {
    pub(super) fn capture(record: &LeveledClauseRecord) -> Result<Self, ReplayCaptureError> {
        let formula = record.formula();
        checked_projection(Self {
            id: record.id().get(),
            protected: record.is_protected(),
            formula: decode_owner(formula.identity())?,
            formula_digest: decode_owner(&json!(formula.identity_sha256()))?,
            canonical_source: formula.canonical_source().into(),
            display: formula.display().into(),
            formula_order_key: record.registration_order_key().into(),
            relation_keys: formula.relation_keys().to_vec(),
            origin: match record.origin() {
                ExtendedClauseOrigin::Submitted => ReplayRecordOrigin::Submitted {},
                ExtendedClauseOrigin::Symbolic => ReplayRecordOrigin::Symbolic {},
                ExtendedClauseOrigin::EdbPreconditionSystem {
                    conjunct_ordinal,
                    route_digest,
                } => ReplayRecordOrigin::EdbPreconditionSystem {
                    conjunct_ordinal: *conjunct_ordinal,
                    route_digest: decode_owner(&json!(route_digest.as_ref()))?,
                },
            },
            minimum_level: record.minimum_level().get(),
            mentions_prophecy: record.mentions_prophecy_relation(),
            components: record
                .components()
                .components()
                .iter()
                .map(ReplayComponent::capture)
                .collect::<Result<_, _>>()?,
            components_digest: decode_owner(&json!(record.components().digest()))?,
            record_digest: decode_owner(&json!(record.record_digest()))?,
        })
    }
    fn derive_digest(&self, scope: &ReplayScopeProjection, run: &str) -> String {
        canonical_value_sha256(
            &json!({"domain":"whiel-framework-ii-fixed-ambient-clause-record-v2","protected":self.protected,
            "task":scope.task,"scope":scope.identity,"task_components_digest":scope.components_digest,"catalog_instance_digest":run,
            "id":self.id,"formula":self.formula,"canonical_source":self.canonical_source,"components_digest":self.components_digest,
            "formula_order_key":self.formula_order_key,"relation_keys":self.relation_keys,"origin":self.origin,"minimum_level":self.minimum_level}),
        )
    }
    fn verify(&self, scope: &ReplayScopeProjection, run: &str) -> Result<(), ReplayCaptureError> {
        invariant(
            self.formula_digest.0 == canonical_value_sha256(&json!(self.formula))
                && self.record_digest.0 == self.derive_digest(scope, run)
                && self.protected
                    == matches!(
                        self.origin,
                        ReplayRecordOrigin::EdbPreconditionSystem { .. }
                    ),
        )?;
        invariant(
            self.components.iter().map(|c| &c.role).eq([
                ReplayComponentRole::Clause,
                ReplayComponentRole::ThetaClause,
                ReplayComponentRole::MaintenanceWp,
                ReplayComponentRole::CollapsedClause,
            ]
            .iter()),
        )?;
        for c in &self.components {
            c.verify()?;
            invariant(
                c.identity.scope_identity == scope.identity
                    && c.identity.base_clause_identity.as_ref() == Some(&self.formula),
            )?;
        }
        invariant(
            component_bundle_digest(
                "whiel-framework-ii-fixed-ambient-clause-components-v1",
                &self.components,
            ) == self.components_digest.0,
        )
    }
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayCatalogProjection {
    pub scope: ReplayScopeProjection,
    pub instance_digest: ReplaySha256,
    pub registration_ordinal: u64,
    pub records: Vec<ReplayRecordProjection>,
}
impl ReplayCatalogProjection {
    pub(super) fn capture(catalog: &LeveledClauseCatalog) -> Result<Self, ReplayCaptureError> {
        let (registration_ordinal, records) = catalog
            .record_snapshot()
            .map_err(|_| ReplayCaptureError::OwnerInvariant)?;
        let projection = Self {
            scope: ReplayScopeProjection::capture(catalog.scope())?,
            instance_digest: decode_owner(&json!(catalog.instance_digest()))?,
            registration_ordinal,
            records: records
                .iter()
                .map(ReplayRecordProjection::capture)
                .collect::<Result<_, _>>()?,
        };
        projection.verify()?;
        checked_projection(projection)
    }
    fn verify(&self) -> Result<(), ReplayCaptureError> {
        self.scope.verify()?;
        for (ordinal, record) in self.records.iter().enumerate() {
            invariant(record.id == ordinal as u64)?;
            record.verify(&self.scope, &self.instance_digest.0)?;
        }
        Ok(())
    }
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayPartitionMember {
    pub id: u64,
    pub record_digest: ReplaySha256,
    pub level: u64,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayPartitionProjection {
    pub scope: ReplayScopeProjection,
    pub catalog_instance_digest: ReplaySha256,
    #[serde(deserialize_with = "nullable")]
    pub max_level: Option<u64>,
    pub records: Vec<ReplayPartitionMember>,
    pub canonical_order: Vec<u64>,
    #[serde(deserialize_with = "nullable")]
    pub greatest_occupied_level: Option<u64>,
    pub partition_digest: ReplaySha256,
    pub worker_identity: ReplaySnapshotIdentity,
}
impl ReplayPartitionProjection {
    pub(super) fn capture(snapshot: &LeveledCandidateSnapshot) -> Result<Self, ReplayCaptureError> {
        let projection = Self {
            scope: ReplayScopeProjection::capture(snapshot.scope())?,
            catalog_instance_digest: decode_owner(&json!(snapshot.catalog_instance_digest()))?,
            max_level: snapshot.max_level().map(|x| x.get()),
            records: snapshot
                .records()
                .iter()
                .map(|(id, r)| {
                    Ok(ReplayPartitionMember {
                        id: id.get(),
                        record_digest: decode_owner(&json!(r.record_digest()))?,
                        level: snapshot
                            .level_of(*id)
                            .ok_or(ReplayCaptureError::OwnerInvariant)?
                            .get(),
                    })
                })
                .collect::<Result<_, ReplayCaptureError>>()?,
            canonical_order: snapshot
                .canonical_order()
                .iter()
                .map(|id| id.get())
                .collect(),
            greatest_occupied_level: snapshot.greatest_occupied_level().map(|x| x.get()),
            partition_digest: decode_owner(&json!(snapshot.partition_digest()))?,
            worker_identity: decode_owner(&snapshot.worker_identity())?,
        };
        invariant(projection.partition_digest.0 == projection.derive_digest())?;
        checked_projection(projection)
    }
    fn derive_digest(&self) -> String {
        canonical_value_sha256(
            &json!({"domain":"whiel-framework-ii-fixed-ambient-partition-v1","task":self.scope.task,"scope":self.scope.identity,"catalog_instance_digest":self.catalog_instance_digest,"max_level":self.max_level,"records":self.records,"canonical_order":self.canonical_order,"greatest_occupied_level":self.greatest_occupied_level}),
        )
    }
    fn verify(&self, catalog: &ReplayCatalogProjection) -> Result<(), ReplayCaptureError> {
        self.scope.verify()?;
        invariant(
            self.scope == catalog.scope
                && self.catalog_instance_digest == catalog.instance_digest
                && self.partition_digest.0 == self.derive_digest(),
        )?;
        let ids = self.records.iter().map(|r| r.id).collect::<BTreeSet<_>>();
        invariant(
            ids.len() == self.records.len() && self.records.windows(2).all(|w| w[0].id < w[1].id),
        )?;
        let mut expected_order = Vec::new();
        for member in &self.records {
            let record = catalog
                .records
                .get(member.id as usize)
                .ok_or(ReplayCaptureError::OwnerInvariant)?;
            invariant(
                record.id == member.id
                    && record.record_digest == member.record_digest
                    && member.level >= record.minimum_level
                    && self.max_level.is_none_or(|max| member.level <= max),
            )?;
            expected_order.push((member.level, record.formula_order_key.as_str(), member.id));
        }
        expected_order.sort();
        invariant(
            expected_order
                .iter()
                .map(|r| r.2)
                .eq(self.canonical_order.iter().copied()),
        )?;
        invariant(self.greatest_occupied_level == self.records.iter().map(|r| r.level).max())?;
        let expected_worker = json!({"kind":"whiel_fixed_ambient_snapshot","version":1,"rows":self.canonical_order.iter().map(|id|{let record=&catalog.records[*id as usize];let level=self.records.iter().find(|r|r.id==*id).unwrap().level;json!({"canonical_source":record.canonical_source,"clause_id":id,"identity":record.formula,"level":level})}).collect::<Vec<_>>()});
        invariant(json!(self.worker_identity) == expected_worker)
    }
}

// A separate bijection exists for each declared constructor category. No
// public insertion or generic text substitution is available.
#[derive(Clone)]
struct CheckedBijection<T: Ord + Clone> {
    forward: BTreeMap<T, T>,
    reverse: BTreeMap<T, T>,
}
impl<T: Ord + Clone> Default for CheckedBijection<T> {
    fn default() -> Self {
        Self {
            forward: BTreeMap::new(),
            reverse: BTreeMap::new(),
        }
    }
}
impl<T: Ord + Clone> CheckedBijection<T> {
    fn bind(&mut self, old: T, live: T, path: &str) -> Result<(), ReplayDivergence> {
        if self.forward.get(&old).is_some_and(|v| v != &live)
            || self.reverse.get(&live).is_some_and(|v| v != &old)
        {
            return Err(ReplayDivergence {
                path: path.into(),
                reason: "conflicting checked identity bijection".into(),
            });
        }
        self.forward.insert(old.clone(), live.clone());
        self.reverse.insert(live, old);
        Ok(())
    }
    fn mapped(&self, old: &T, path: &str) -> Result<&T, ReplayDivergence> {
        self.forward.get(old).ok_or_else(|| ReplayDivergence {
            path: path.into(),
            reason: "reference has no checked owner correspondence".into(),
        })
    }
}
#[derive(Clone)]
struct ReplayTrafficBinding {
    old_request: String,
    live_request: String,
    old_consultation: String,
    live_consultation: String,
    state_revision: u64,
}
#[derive(Clone, PartialEq, Eq)]
struct ReplayRunPair {
    old_run: String,
    live_run: String,
    task: String,
    source: String,
    scope: String,
    request_policy: String,
    feedback_policy: String,
}
#[derive(Clone, Default)]
pub struct ReplayCorrespondenceV1 {
    audit: ReplayComparisonLogV2,
    finalized: bool,
    run_pair: Option<ReplayRunPair>,
    coordinates: BTreeMap<TranscriptCoordinates, ReplayTrafficBinding>,
    tool_calls: BTreeMap<(TranscriptCoordinates, u64), String>,
    completed_tools: BTreeSet<(TranscriptCoordinates, u64)>,
    catalogs: CheckedBijection<String>,
    records: CheckedBijection<String>,
    partitions: CheckedBijection<String>,
    physical_attempts: CheckedBijection<PhysicalAttemptId>,
    production: BTreeMap<ReplayProductionIdentity, CheckedBijection<String>>,
    host: BTreeMap<ReplayHostIdentity, CheckedBijection<String>>,
    wire: BTreeMap<ReplayWireIdentity, CheckedBijection<String>>,
    artifacts: CheckedBijection<(String, u64)>,
    refutation_attempts: BTreeSet<PhysicalAttemptId>,
    push_bindings: BTreeMap<String, super::replay_identity::ResponseBindingV1>,
}
impl ReplayCorrespondenceV1 {
    pub fn new() -> Self {
        Self::default()
    }
    pub(super) fn compare_catalog(
        &mut self,
        old: &ReplayCatalogProjection,
        live: &ReplayCatalogProjection,
    ) -> Result<(), ReplayDivergence> {
        old.verify().map_err(|_| ReplayDivergence {
            path: "catalog.recorded".into(),
            reason: "owner constructor verification failed".into(),
        })?;
        live.verify().map_err(|_| ReplayDivergence {
            path: "catalog.live".into(),
            reason: "owner constructor verification failed".into(),
        })?;
        same(&old.scope, &live.scope, "catalog.scope")?;
        same(
            &old.registration_ordinal,
            &live.registration_ordinal,
            "catalog.registration_ordinal",
        )?;
        same(
            &old.records.len(),
            &live.records.len(),
            "catalog.records.length",
        )?;
        for (a, b) in old.records.iter().zip(&live.records) {
            let mut expected = a.clone();
            expected.record_digest = b.record_digest.clone();
            same(&expected, b, "catalog.records.semantic")?;
            self.records.bind(
                a.record_digest.0.clone(),
                b.record_digest.0.clone(),
                "catalog.record_digest",
            )?;
        }
        self.catalogs.bind(
            old.instance_digest.0.clone(),
            live.instance_digest.0.clone(),
            "catalog.instance",
        )
    }
    pub(super) fn compare_partition(
        &mut self,
        old: &ReplayPartitionProjection,
        live: &ReplayPartitionProjection,
        old_catalog: &ReplayCatalogProjection,
        live_catalog: &ReplayCatalogProjection,
    ) -> Result<(), ReplayDivergence> {
        old.verify(old_catalog).map_err(|_| ReplayDivergence {
            path: "partition.recorded".into(),
            reason: "owner constructor verification failed".into(),
        })?;
        live.verify(live_catalog).map_err(|_| ReplayDivergence {
            path: "partition.live".into(),
            reason: "owner constructor verification failed".into(),
        })?;
        same(
            self.catalogs
                .mapped(&old.catalog_instance_digest.0, "partition.catalog")?,
            &live.catalog_instance_digest.0,
            "partition.catalog",
        )?;
        same(&old.scope, &live.scope, "partition.scope")?;
        same(&old.max_level, &live.max_level, "partition.max_level")?;
        same(
            &old.canonical_order,
            &live.canonical_order,
            "partition.canonical_order",
        )?;
        same(
            &old.greatest_occupied_level,
            &live.greatest_occupied_level,
            "partition.greatest_occupied_level",
        )?;
        same(
            &old.worker_identity,
            &live.worker_identity,
            "partition.worker_identity",
        )?;
        same(
            &old.records.len(),
            &live.records.len(),
            "partition.records.length",
        )?;
        for (a, b) in old.records.iter().zip(&live.records) {
            same(&a.id, &b.id, "partition.record.id")?;
            same(&a.level, &b.level, "partition.record.level")?;
            same(
                self.records
                    .mapped(&a.record_digest.0, "partition.record.digest")?,
                &b.record_digest.0,
                "partition.record.digest",
            )?;
        }
        self.partitions.bind(
            old.partition_digest.0.clone(),
            live.partition_digest.0.clone(),
            "partition.digest",
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayCheckRequestProjection {
    pub row_ordinal: LedgerRowOrdinal,
    pub clause: u64,
    pub level: u64,
    pub role: super::replay_identity::RoleV1,
    pub launch_suppressed: bool,
    pub snapshot: ReplayPartitionProjection,
    pub identity: ReplayClauseRequestIdentity,
    pub request_digest: ReplaySha256,
}
impl ReplayCheckRequestProjection {
    fn capture(request: &super::FrameworkIICheckRequest) -> Result<Self, ReplayCaptureError> {
        invariant(request.has_current_identity())?;
        checked_projection(Self {
            row_ordinal: LedgerRowOrdinal(request.attempt_ordinal()),
            clause: request.clause().get(),
            level: request.level().get(),
            role: match request.role() {
                super::FrameworkIICheckRole::Initialization => {
                    super::replay_identity::RoleV1::Initialization
                }
                super::FrameworkIICheckRole::Maintenance => {
                    super::replay_identity::RoleV1::Maintenance
                }
            },
            launch_suppressed: request.launch_suppressed(),
            snapshot: ReplayPartitionProjection::capture(request.snapshot())?,
            identity: decode_owner(request.identity())?,
            request_digest: decode_owner(&json!(request.request_digest()))?,
        })
    }
    fn verify(&self, catalog: &ReplayCatalogProjection) -> Result<(), ReplayCaptureError> {
        self.snapshot.verify(catalog)?;
        let kind = match self.role {
            super::replay_identity::RoleV1::Initialization => "initialization",
            super::replay_identity::RoleV1::Maintenance => "maintenance",
        };
        let expected = json!({"kind":"whiel_framework_ii_fixed_ambient_check_request","version":1,"attempt_ordinal":self.row_ordinal.0,"scope_identity":self.snapshot.scope.identity,"snapshot_identity":self.snapshot.worker_identity,"selector":{"kind":kind,"clause_id":self.clause}});
        invariant(
            json!(self.identity) == expected
                && canonical_value_sha256(&expected) == self.request_digest.0
                && self
                    .snapshot
                    .records
                    .iter()
                    .any(|r| r.id == self.clause && r.level == self.level),
        )
    }
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayEvidenceTiming {
    #[serde(deserialize_with = "nullable")]
    pub solver_time_ns: Option<String>,
    #[serde(deserialize_with = "nullable")]
    pub preparation_time_ns: Option<String>,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub(super) enum ReplayEvidenceAuthority {
    Production {
        projection: Box<ReplayProductionProjection>,
        preparation: Box<ReplayPreparedProjection>,
        artifacts: Vec<ReplayArtifactAssociation>,
    },
    LaunchSuppressed {},
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayEvidenceProjection {
    pub request_digest: ReplaySha256,
    pub identity: ReplaySha256,
    pub authority: ReplayEvidenceAuthority,
    #[serde(deserialize_with = "nullable")]
    pub reuse: Option<ReplayProductionProjection>,
    pub timing: ReplayEvidenceTiming,
}
#[derive(Clone)]
pub(super) struct ReplayEvidenceOwner {
    native: super::FrameworkIICheckEvidence,
    pub projection: ReplayEvidenceProjection,
}
impl ReplayEvidenceOwner {
    fn capture(evidence: &super::FrameworkIICheckEvidence) -> Result<Self, ReplayCaptureError> {
        fn capture_projection(
            capture: &ReplayProductionCapture,
        ) -> Result<ReplayProductionProjection, ReplayCaptureError> {
            match capture {
                ReplayProductionCapture::Replayable(p) => Ok((**p).clone()),
                ReplayProductionCapture::NonReplayable(e) => Err(e.clone().into()),
            }
        }
        macro_rules! route {
            ($owner:expr) => {{
                let owner = $owner;
                let projection = capture_projection(owner.replay_projection())?;
                owner.verify_replay_projection(&projection)?;
                ReplayEvidenceAuthority::Production {
                    projection: Box::new(projection),
                    preparation: Box::new(
                        owner
                            .replay_preparation()
                            .map_err(|e| ReplayCaptureError::from(e.clone()))?
                            .clone(),
                    ),
                    artifacts: owner.replay_artifact_associations()?,
                }
            }};
        }
        let authority = if let Some(r) = evidence.runtime_proof() {
            route!(r)
        } else if let Some(r) = evidence.protected_theorem_selection() {
            route!(r)
        } else if let Some(r) = evidence.validated_refutation() {
            route!(r)
        } else if let Some(r) = evidence.progress() {
            route!(r)
        } else if evidence.is_launch_suppressed() {
            ReplayEvidenceAuthority::LaunchSuppressed {}
        } else {
            return Err(ReplayCaptureError::UnsupportedSchema);
        };
        let reuse = evidence
            .semantic_reuse()
            .map(|r| {
                let p = capture_projection(r.replay_projection())?;
                r.verify_replay_projection(&p)?;
                Ok::<_, ReplayCaptureError>(p)
            })
            .transpose()?;
        let projection = checked_projection(ReplayEvidenceProjection {
            request_digest: decode_owner(&json!(evidence.request_digest()))?,
            identity: decode_owner(&json!(evidence.identity()))?,
            authority,
            reuse,
            timing: ReplayEvidenceTiming {
                solver_time_ns: evidence.solver_time().map(|d| d.as_nanos().to_string()),
                preparation_time_ns: evidence
                    .preparation_time()
                    .map(|d| d.as_nanos().to_string()),
            },
        })?;
        let owner = Self {
            native: evidence.clone(),
            projection,
        };
        owner.verify_recorded(&owner.projection)?;
        Ok(owner)
    }
    fn verify_recorded(
        &self,
        recorded: &ReplayEvidenceProjection,
    ) -> Result<(), ReplayCaptureError> {
        match &recorded.authority {
            ReplayEvidenceAuthority::LaunchSuppressed {} => {
                invariant(
                    self.native.is_launch_suppressed()
                        && recorded.reuse.is_none()
                        && recorded.identity.0
                            == canonical_value_sha256(
                                &json!({"kind":"whiel_framework_ii_launch_suppressed_check","version":1,"request_digest":recorded.request_digest}),
                            ),
                )?;
            }
            ReplayEvidenceAuthority::Production {
                projection,
                preparation,
                artifacts,
            } => {
                preparation.verify()?;
                projection.verify_preparation(preparation)?;
                macro_rules! verify {
                    ($owner:expr) => {{
                        $owner
                            .ok_or(ReplayCaptureError::OwnerInvariant)?
                            .verify_replay_projection(projection)?;
                    }};
                }
                match projection.as_ref() {
                    ReplayProductionProjection::RuntimeProof { .. } => {
                        verify!(self.native.runtime_proof())
                    }
                    ReplayProductionProjection::Protected { .. } => {
                        verify!(self.native.protected_theorem_selection())
                    }
                    ReplayProductionProjection::ValidatedRefutation { .. } => {
                        verify!(self.native.validated_refutation())
                    }
                    ReplayProductionProjection::Progress { .. } => verify!(self.native.progress()),
                    ReplayProductionProjection::SemanticReuse { .. } => {
                        return Err(ReplayCaptureError::OwnerInvariant);
                    }
                }
                invariant(!artifacts.is_empty())?;
            }
        }
        if let Some(reuse) = &recorded.reuse {
            self.native
                .semantic_reuse()
                .ok_or(ReplayCaptureError::OwnerInvariant)?
                .verify_replay_projection(reuse)?;
            invariant(recorded.identity == *production_digest(reuse))?;
        } else {
            invariant(self.native.semantic_reuse().is_none())?;
            if let ReplayEvidenceAuthority::Production { projection, .. } = &recorded.authority {
                invariant(recorded.identity == *production_digest(projection))?;
            }
        }
        Ok(())
    }
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub(super) enum ReplayOutcomeProjection {
    Proved {
        evidence: ReplayEvidenceProjection,
    },
    Refuted {
        evidence: ReplayEvidenceProjection,
    },
    Inconclusive {
        reason: super::replay_identity::InconclusiveReasonV1,
        evidence: ReplayEvidenceProjection,
    },
}
impl ReplayOutcomeProjection {
    fn evidence(&self) -> &ReplayEvidenceProjection {
        match self {
            Self::Proved { evidence }
            | Self::Refuted { evidence }
            | Self::Inconclusive { evidence, .. } => evidence,
        }
    }
    fn identity_fields(&self) -> Value {
        let evidence = self.evidence();
        match self {
            Self::Proved { .. } => {
                json!({"kind":"proved","request_digest":evidence.request_digest,"evidence":evidence.identity})
            }
            Self::Refuted { .. } => {
                json!({"kind":"refuted","request_digest":evidence.request_digest,"evidence":evidence.identity})
            }
            Self::Inconclusive { reason, .. } => {
                json!({"kind":"inconclusive","reason":reason,"request_digest":evidence.request_digest,"progress":evidence.identity})
            }
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub(super) enum ReplayLedgerRowProjection {
    Attempt {
        row_ordinal: LedgerRowOrdinal,
        request: Box<ReplayCheckRequestProjection>,
        outcome: Box<ReplayOutcomeProjection>,
        #[serde(deserialize_with = "nullable")]
        previous_digest: Option<ReplaySha256>,
        row_digest: ReplaySha256,
    },
    Invalidation {
        row_ordinal: LedgerRowOrdinal,
        invalidated_attempt: LedgerRowOrdinal,
        target: u64,
        #[serde(deserialize_with = "nullable")]
        cause: Option<u64>,
        reason: super::replay_identity::InvalidationReasonV1,
        #[serde(deserialize_with = "nullable")]
        previous_digest: Option<ReplaySha256>,
        row_digest: ReplaySha256,
    },
}
impl ReplayLedgerRowProjection {
    fn ordinal(&self) -> LedgerRowOrdinal {
        match self {
            Self::Attempt { row_ordinal, .. } | Self::Invalidation { row_ordinal, .. } => {
                *row_ordinal
            }
        }
    }
    fn digest(&self) -> &ReplaySha256 {
        match self {
            Self::Attempt { row_digest, .. } | Self::Invalidation { row_digest, .. } => row_digest,
        }
    }
    fn previous(&self) -> Option<&ReplaySha256> {
        match self {
            Self::Attempt {
                previous_digest, ..
            }
            | Self::Invalidation {
                previous_digest, ..
            } => previous_digest.as_ref(),
        }
    }
    fn derive_digest(&self) -> String {
        let fields = match self {
            Self::Attempt {
                row_ordinal,
                request,
                outcome,
                previous_digest,
                ..
            } => {
                json!({"domain":"whiel-framework-ii-attempt-row-v3","row_ordinal":row_ordinal.0,"request_digest":request.request_digest,"outcome":outcome.identity_fields(),"previous_digest":previous_digest})
            }
            Self::Invalidation {
                row_ordinal,
                invalidated_attempt,
                target,
                cause,
                reason,
                previous_digest,
                ..
            } => {
                json!({"domain":"whiel-framework-ii-invalidation-row-v2","row_ordinal":row_ordinal.0,"invalidated_attempt":invalidated_attempt.0,"target":target,"cause":cause,"reason":reason,"previous_digest":previous_digest})
            }
        };
        canonical_value_sha256(&fields)
    }
}
#[derive(Clone)]
pub(super) struct ReplayLedgerOwner {
    pub rows: Vec<ReplayLedgerRowProjection>,
    evidence: BTreeMap<LedgerRowOrdinal, ReplayEvidenceOwner>,
}
impl ReplayLedgerOwner {
    fn capture(ledger: &super::LevelAttemptLedger) -> Result<Self, ReplayCaptureError> {
        ledger
            .validate_lineage()
            .map_err(|_| ReplayCaptureError::OwnerInvariant)?;
        let mut rows = Vec::new();
        let mut evidence = BTreeMap::new();
        for row in ledger.rows() {
            let ordinal = LedgerRowOrdinal(row.row_ordinal());
            let projection = match row {
                super::LevelLedgerRow::Attempt(row) => {
                    let owner = ReplayEvidenceOwner::capture(row.outcome().evidence())?;
                    let projected = owner.projection.clone();
                    let outcome = match row.outcome() {
                        super::FrameworkIICheckOutcome::Proved(_) => {
                            ReplayOutcomeProjection::Proved {
                                evidence: projected,
                            }
                        }
                        super::FrameworkIICheckOutcome::Refuted(_) => {
                            ReplayOutcomeProjection::Refuted {
                                evidence: projected,
                            }
                        }
                        super::FrameworkIICheckOutcome::Inconclusive { reason, .. } => {
                            ReplayOutcomeProjection::Inconclusive {
                                reason: decode_owner(&json!(reason.identity_name()))?,
                                evidence: projected,
                            }
                        }
                    };
                    invariant(outcome.identity_fields() == row.outcome().identity_fields())?;
                    evidence.insert(LedgerRowOrdinal(row.row_ordinal()), owner);
                    ReplayLedgerRowProjection::Attempt {
                        row_ordinal: LedgerRowOrdinal(row.row_ordinal()),
                        request: Box::new(ReplayCheckRequestProjection::capture(row.request())?),
                        outcome: Box::new(outcome),
                        previous_digest: row
                            .previous_digest()
                            .map(|d| decode_owner(&json!(d)))
                            .transpose()?,
                        row_digest: decode_owner(&json!(row.row_digest()))?,
                    }
                }
                super::LevelLedgerRow::Invalidation(row) => {
                    ReplayLedgerRowProjection::Invalidation {
                        row_ordinal: ordinal,
                        invalidated_attempt: LedgerRowOrdinal(row.invalidated_attempt()),
                        target: row.target().get(),
                        cause: row.cause().map(|c| c.get()),
                        reason: decode_owner(&json!(row.reason().identity_name()))?,
                        previous_digest: row
                            .previous_digest()
                            .map(|d| decode_owner(&json!(d)))
                            .transpose()?,
                        row_digest: decode_owner(&json!(row.row_digest()))?,
                    }
                }
            };
            invariant(projection.derive_digest() == projection.digest().0)?;
            rows.push(projection);
        }
        Ok(Self { rows, evidence })
    }
    fn verify_recorded(
        &self,
        rows: &[ReplayLedgerRowProjection],
        catalog: &ReplayCatalogProjection,
    ) -> Result<(), ReplayCaptureError> {
        let mut invalidated = BTreeSet::new();
        for (i, row) in rows.iter().enumerate() {
            invariant(
                row.ordinal().0 == i as u64
                    && row.previous() == i.checked_sub(1).map(|p| rows[p].digest())
                    && row.digest().0 == row.derive_digest(),
            )?;
            match row {
                ReplayLedgerRowProjection::Attempt {
                    request, outcome, ..
                } => {
                    invariant(
                        request.row_ordinal == row.ordinal()
                            && request.request_digest == outcome.evidence().request_digest,
                    )?;
                    request.verify(catalog)?;
                    self.evidence
                        .get(&row.ordinal())
                        .ok_or(ReplayCaptureError::OwnerInvariant)?
                        .verify_recorded(outcome.evidence())?;
                }
                ReplayLedgerRowProjection::Invalidation {
                    invalidated_attempt,
                    target,
                    ..
                } => {
                    invariant(
                        invalidated.insert(*invalidated_attempt)
                            && invalidated_attempt.0 < row.ordinal().0,
                    )?;
                    let Some(ReplayLedgerRowProjection::Attempt { request, .. }) =
                        rows.get(invalidated_attempt.0 as usize)
                    else {
                        return Err(ReplayCaptureError::OwnerInvariant);
                    };
                    invariant(request.clause == *target)?;
                }
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayCurrentRootProjection {
    pub clause: u64,
    pub role: super::replay_identity::RoleV1,
    pub attempt_row: LedgerRowOrdinal,
    pub request_digest: ReplaySha256,
    pub partition_digest: ReplaySha256,
    pub evidence: ReplayEvidenceProjection,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayDeadEntry {
    pub clause: u64,
    pub cause: super::replay_identity::DeathV1,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayStateProjection {
    pub catalog: ReplayCatalogProjection,
    pub proposal_revision: u64,
    pub core: ReplayPartitionProjection,
    pub core_digest: ReplaySha256,
    pub committed: Vec<(u64, u64)>,
    pub pending: Vec<(u64, u64)>,
    pub dead: Vec<ReplayDeadEntry>,
    pub roots: Vec<ReplayCurrentRootProjection>,
    pub missing_roots: Vec<(u64, super::replay_identity::RoleV1)>,
    pub ledger: Vec<ReplayLedgerRowProjection>,
    pub state_snapshot_digest: ReplaySha256,
    pub termination_attempts_total: u64,
    pub terminations: Vec<ReplayTerminationProjection>,
}
#[derive(Clone)]
pub(super) struct ReplayStateOwner {
    pub projection: ReplayStateProjection,
    pub ledger: ReplayLedgerOwner,
    terminations: Vec<ReplayTerminationOwner>,
}
impl ReplayStateOwner {
    pub(super) fn capture(
        state: &super::LeveledHoudiniState,
        expected_digest: &str,
    ) -> Result<Self, ReplayCaptureError> {
        // This owner method validates private extraneous keys and exact native
        // evidence against noninvalidated ledger rows before any enumeration.
        let coverage = state
            .root_coverage()
            .map_err(|_| ReplayCaptureError::OwnerInvariant)?;
        let catalog = ReplayCatalogProjection::capture(state.catalog())?;
        let ledger = ReplayLedgerOwner::capture(state.attempts())?;
        let terminations = state
            .replay_termination_observations()
            .iter()
            .map(ReplayTerminationOwner::capture)
            .collect::<Result<Vec<_>, _>>()?;
        let mut roots = Vec::new();
        for record in &catalog.records {
            for role in [
                super::FrameworkIICheckRole::Initialization,
                super::FrameworkIICheckRole::Maintenance,
            ] {
                if let Some(root) = state.current_root(
                    crate::houdini::ClauseId::from_catalog_ordinal(record.id),
                    role,
                ) {
                    roots.push(ReplayCurrentRootProjection {
                        clause: record.id,
                        role: decode_owner(&json!(role.identity_name()))?,
                        attempt_row: LedgerRowOrdinal(root.attempt_row()),
                        request_digest: decode_owner(&json!(root.request_digest()))?,
                        partition_digest: decode_owner(&json!(root.partition_digest()))?,
                        evidence: ReplayEvidenceOwner::capture(root.proof_evidence())?.projection,
                    });
                }
            }
        }
        let projection = ReplayStateProjection {
            termination_attempts_total: state.termination_attempts_total(),
            terminations: terminations.iter().map(|o| o.projection.clone()).collect(),
            catalog,
            proposal_revision: state.proposal_revision(),
            core: ReplayPartitionProjection::capture(state.core().snapshot())?,
            core_digest: decode_owner(&json!(state.core().core_digest()))?,
            committed: state
                .committed_levels()
                .iter()
                .map(|(id, level)| (id.get(), level.get()))
                .collect(),
            pending: state
                .pending_levels()
                .iter()
                .map(|(id, level)| (id.get(), level.get()))
                .collect(),
            dead: state
                .dead()
                .iter()
                .map(|(id, cause)| {
                    Ok(ReplayDeadEntry {
                        clause: id.get(),
                        cause: match cause {
                            super::FrameworkIIDeadCause::Dropped => {
                                super::replay_identity::DeathV1::Dropped {}
                            }
                            super::FrameworkIIDeadCause::Refuted(reason) => {
                                super::replay_identity::DeathV1::Refuted {
                                    reason: decode_owner(&reason.identity_fields())?,
                                }
                            }
                        },
                    })
                })
                .collect::<Result<_, ReplayCaptureError>>()?,
            roots,
            missing_roots: coverage
                .missing()
                .iter()
                .map(|(id, role)| Ok((id.get(), decode_owner(&json!(role.identity_name()))?)))
                .collect::<Result<_, ReplayCaptureError>>()?,
            ledger: ledger.rows.clone(),
            state_snapshot_digest: decode_owner(&json!(expected_digest))?,
        };
        let owner = Self {
            projection: checked_projection(projection)?,
            ledger,
            terminations,
        };
        owner.verify_recorded(&owner.projection)?;
        Ok(owner)
    }
    fn verify_recorded(
        &self,
        projection: &ReplayStateProjection,
    ) -> Result<(), ReplayCaptureError> {
        projection.verify_structure()?;
        self.ledger
            .verify_recorded(&projection.ledger, &projection.catalog)?;
        invariant(
            projection.termination_attempts_total == projection.terminations.len() as u64
                && projection.terminations.len() == self.terminations.len(),
        )?;
        for (index, (owner, recorded)) in self
            .terminations
            .iter()
            .zip(&projection.terminations)
            .enumerate()
        {
            invariant(recorded.ordinal == index as u64 + 1)?;
            owner.verify_recorded(recorded, &projection.catalog)?;
        }
        Ok(())
    }
}
impl ReplayStateProjection {
    fn derive_digest(&self) -> String {
        let dead = self
            .dead
            .iter()
            .map(|entry| match &entry.cause {
                super::replay_identity::DeathV1::Dropped {} => json!([entry.clause, "dropped"]),
                super::replay_identity::DeathV1::Refuted { reason } => {
                    json!([entry.clause, "refuted", reason])
                }
            })
            .collect::<Vec<_>>();
        let roots=self.roots.iter().map(|r|json!({"clause":r.clause,"role":r.role,"attempt_row":r.attempt_row,"request_digest":r.request_digest,"partition_digest":r.partition_digest})).collect::<Vec<_>>();
        canonical_value_sha256(
            &json!({"domain":"whiel-agent-feedback-state-snapshot-v3","task":self.catalog.scope.task,"scope_digest":self.catalog.scope.digest,
            "run_digest":self.catalog.instance_digest,"proposal_revision":self.proposal_revision,"registration_ordinal":self.catalog.registration_ordinal,
            "record_digests":self.catalog.records.iter().map(|r|&r.record_digest).collect::<Vec<_>>(),"core_partition_digest":self.core.partition_digest,
            "committed":self.committed,"pending":self.pending,"dead":dead,"current_roots":roots,"ledger_rows":self.ledger.len(),"ledger_head":self.ledger.last().map(ReplayLedgerRowProjection::digest)}),
        )
    }
    fn verify_structure(&self) -> Result<(), ReplayCaptureError> {
        self.catalog.verify()?;
        self.core.verify(&self.catalog)?;
        invariant(
            self.state_snapshot_digest.0 == self.derive_digest()
                && self.core_digest.0
                    == canonical_value_sha256(
                        &json!({"kind":"whiel_framework_ii_fixed_ambient_core","version":1,"scope_identity":self.catalog.scope.identity,"snapshot_identity":self.core.worker_identity}),
                    ),
        )?;
        invariant(
            self.committed
                .iter()
                .copied()
                .eq(self.core.records.iter().map(|r| (r.id, r.level))),
        )?;
        for values in [&self.committed, &self.pending] {
            invariant(values.windows(2).all(|w| w[0].0 < w[1].0))?;
        }
        invariant(self.dead.windows(2).all(|w| w[0].clause < w[1].clause))?;
        let mut partitioned = BTreeSet::new();
        for (id, level) in self.committed.iter().chain(&self.pending) {
            let r = self
                .catalog
                .records
                .get(*id as usize)
                .ok_or(ReplayCaptureError::OwnerInvariant)?;
            invariant(
                partitioned.insert(*id)
                    && r.minimum_level <= *level
                    && self.core.max_level.is_none_or(|m| *level <= m),
            )?;
        }
        for entry in &self.dead {
            invariant(
                partitioned.insert(entry.clause)
                    && self.catalog.records.get(entry.clause as usize).is_some(),
            )?;
            if let super::replay_identity::DeathV1::Refuted {
                reason:
                    super::replay_identity::DeadReasonV1::ProphecyFreeInitializationRefuted { attempt },
            } = &entry.cause
            {
                let Some(ReplayLedgerRowProjection::Attempt {
                    request, outcome, ..
                }) = self.ledger.get(attempt.0 as usize)
                else {
                    return Err(ReplayCaptureError::OwnerInvariant);
                };
                invariant(
                    request.clause == entry.clause
                        && request.level == 0
                        && matches!(request.role, super::replay_identity::RoleV1::Initialization)
                        && matches!(outcome.as_ref(), ReplayOutcomeProjection::Refuted { .. })
                        && !self.catalog.records[entry.clause as usize].mentions_prophecy,
                )?;
            }
        }
        let invalidated = self
            .ledger
            .iter()
            .filter_map(|r| {
                if let ReplayLedgerRowProjection::Invalidation {
                    invalidated_attempt,
                    ..
                } = r
                {
                    Some(*invalidated_attempt)
                } else {
                    None
                }
            })
            .collect::<BTreeSet<_>>();
        let mut root_keys = BTreeSet::new();
        for root in &self.roots {
            let role = match root.role {
                super::replay_identity::RoleV1::Initialization => 0u8,
                super::replay_identity::RoleV1::Maintenance => 1,
            };
            invariant(
                root_keys.insert((root.clause, role))
                    && !invalidated.contains(&root.attempt_row)
                    && root.partition_digest == self.core.partition_digest,
            )?;
            let Some(ReplayLedgerRowProjection::Attempt {
                request, outcome, ..
            }) = self.ledger.get(root.attempt_row.0 as usize)
            else {
                return Err(ReplayCaptureError::OwnerInvariant);
            };
            invariant(
                request.clause == root.clause
                    && request.role == root.role
                    && request.snapshot == self.core
                    && request.request_digest == root.request_digest
                    && matches!(outcome.as_ref(), ReplayOutcomeProjection::Proved { .. })
                    && outcome.evidence() == &root.evidence,
            )?;
        }
        let mut missing = Vec::new();
        for id in &self.core.canonical_order {
            for (role, kind) in [
                (0u8, super::replay_identity::RoleV1::Initialization),
                (1u8, super::replay_identity::RoleV1::Maintenance),
            ] {
                if !root_keys.contains(&(*id, role)) {
                    missing.push((*id, kind));
                }
            }
        }
        invariant(missing == self.missing_roots)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayHostLimits {
    #[serde(deserialize_with = "nullable")]
    pub catalog_size: Option<u64>,
    #[serde(deserialize_with = "nullable")]
    pub clause_text_bytes: Option<u64>,
    #[serde(deserialize_with = "nullable")]
    pub countermodel_retention_tuples: Option<u64>,
    #[serde(deserialize_with = "nullable")]
    pub drop_references: Option<u64>,
    #[serde(deserialize_with = "nullable")]
    pub evaluation_cost: Option<u64>,
    #[serde(deserialize_with = "nullable")]
    pub level_bound: Option<u64>,
    #[serde(deserialize_with = "nullable")]
    pub proposal_size: Option<u64>,
    #[serde(deserialize_with = "nullable")]
    pub pushed_core: Option<u64>,
    #[serde(deserialize_with = "nullable")]
    pub reply_bytes: Option<u64>,
    #[serde(deserialize_with = "nullable")]
    pub strongest_refutations: Option<u64>,
}
impl ReplayHostLimits {
    fn native(&self) -> super::HostLimits {
        super::HostLimits {
            catalog_size: self.catalog_size,
            clause_text_bytes: self.clause_text_bytes,
            countermodel_retention_tuples: self.countermodel_retention_tuples,
            drop_references: self.drop_references,
            evaluation_cost: self.evaluation_cost,
            level_bound: self.level_bound,
            proposal_size: self.proposal_size,
            pushed_core: self.pushed_core,
            reply_bytes: self.reply_bytes,
            strongest_refutations: self.strongest_refutations,
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(super) enum ReplayPolicyDomain {
    #[serde(rename = "whiel-proposer-feedback-policy-v1")]
    V1,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayPolicyFields {
    pub domain: ReplayPolicyDomain,
    pub max_shared_presentation_bytes: usize,
    pub max_private_manifest_bytes: usize,
    pub max_feedback_bytes: usize,
    pub max_page_bytes: usize,
    pub clause_page_items: usize,
    pub ledger_page_items: usize,
    pub max_artifact_references: usize,
    pub host_limits: ReplayHostLimits,
    pub resource_limits: Option<super::resource_limits::CampaignResourceLimits>,
}
impl ReplayPolicyFields {
    fn verify(&self, digest: &ReplaySha256) -> Result<(), ReplayCaptureError> {
        let policy = super::AgentFeedbackPolicy::new(super::AgentFeedbackLimits {
            max_shared_presentation_bytes: self.max_shared_presentation_bytes,
            max_private_manifest_bytes: self.max_private_manifest_bytes,
            max_feedback_bytes: self.max_feedback_bytes,
            max_page_bytes: self.max_page_bytes,
            clause_page_items: self.clause_page_items,
            ledger_page_items: self.ledger_page_items,
            max_artifact_references: self.max_artifact_references,
            host_limits: self.host_limits.native(),
            resource_limits: self.resource_limits.clone(),
        })
        .map_err(|_| ReplayCaptureError::OwnerInvariant)?;
        invariant(policy.digest() == digest.0)
    }
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayLatestArtifact {
    pub backend_matches_only: bool,
    pub local_id: u64,
    pub kind: super::replay_identity::ArtifactKindV1,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum ReplayLatestIdentity {
    Initial {},
    PostconditionOpen {
        #[serde(flatten)]
        outcome: super::replay_identity::PostconditionOpenV1,
    },
    Failure {
        origin: super::replay_identity::FailureOriginV1,
        failure_kind: super::replay_identity::FailureKindV1,
        retryable: bool,
        scope: super::replay_identity::FailureScopeV1,
        detail_digest: Option<ReplaySha256>,
        artifacts: Vec<ReplayLatestArtifact>,
    },
    CounterexampleRejected {
        code: String,
        reason: String,
    },
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayPendingEligibility {
    pub clause_id: u64,
    pub record_digest: ReplaySha256,
    pub level: u64,
    pub drop_eligible: bool,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayShownDrop {
    pub authorization_digest: ReplaySha256,
    pub clause_id: u64,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayManifestArtifact {
    pub stable_id: ReplaySha256,
    pub local_id: u64,
    pub kind: super::replay_identity::ArtifactKindV1,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(super) enum ReplayManifestDomain {
    #[serde(rename = "whiel-agent-feedback-private-validation-manifest-v2")]
    V2,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayManifestFields {
    pub domain: ReplayManifestDomain,
    pub task: ReplayTaskIdentity,
    pub scope_digest: ReplaySha256,
    pub run_digest: ReplaySha256,
    pub session_digest: ReplaySha256,
    pub consultation_digest: ReplaySha256,
    pub policy_digest: ReplaySha256,
    pub proposal_revision: u64,
    pub registration_ordinal: u64,
    pub state_snapshot_digest: ReplaySha256,
    pub core_partition_digest: ReplaySha256,
    pub pending: Vec<ReplayPendingEligibility>,
    pub shown_clauses: Vec<super::replay_identity::ClauseV1>,
    pub shown_drops: Vec<ReplayShownDrop>,
    pub artifact_references: Vec<ReplayManifestArtifact>,
    pub core_clause_ids: Vec<u64>,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayEligibilityProjection {
    pub visible_records: Vec<u64>,
    pub proposal_revision: u64,
    pub expected_registration_ordinal: u64,
    pub core: ReplayPartitionProjection,
    pub drop_eligible_records: Vec<u64>,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayConsultationInputs {
    pub iteration: u64,
    pub remaining_search_budget_ns: String,
    pub clause_page_start: usize,
    pub ledger_page_end: usize,
    pub previous_round_proposed: Vec<u64>,
    pub reconciled_host_limits: ReplayHostLimits,
}
/// Sanitized constructor inputs. This value carries no controller authority;
/// acceptance always requires a fresh immutable owner and checked correspondence.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReplayOwnerProjection {
    version: ReplayVersion<2>,
    state: ReplayStateProjection,
    routes: Vec<ReplayRouteProjection>,
    stable_artifacts: Vec<ReplayStableArtifactProjection>,
    cursors: Vec<ReplayCursorProjection>,
    backend: ReplayBackendIdentity,
    #[serde(deserialize_with = "nullable")]
    run_configuration: Option<ReplayRunConfiguration>,
    policy: ReplayPolicyFields,
    policy_digest: ReplaySha256,
    session_digest: ReplaySha256,
    latest: ReplayLatestIdentity,
    latest_artifacts: Vec<ReplayArtifactIdentity>,
    latest_digest: ReplaySha256,
    eligibility: ReplayEligibilityProjection,
    consultation: ReplayConsultationInputs,
    manifest: ReplayManifestFields,
    manifest_digest: ReplaySha256,
}
#[derive(Clone)]
pub(super) struct ReplayFeedbackOwner {
    pub projection: ReplayOwnerProjection,
    pub state: ReplayStateOwner,
}
impl ReplayFeedbackOwner {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn capture(
        state: ReplayStateOwner,
        routes: Vec<ReplayRouteProjection>,
        stable_artifacts: Vec<ReplayStableArtifactProjection>,
        cursors: Vec<ReplayCursorProjection>,
        backend: ReplayBackendIdentity,
        run_configuration: Option<ReplayRunConfiguration>,
        policy: ReplayPolicyFields,
        policy_digest: ReplaySha256,
        session_digest: ReplaySha256,
        latest: ReplayLatestIdentity,
        latest_artifacts: Vec<ReplayArtifactIdentity>,
        latest_digest: ReplaySha256,
        eligibility: ReplayEligibilityProjection,
        consultation: ReplayConsultationInputs,
        manifest: ReplayManifestFields,
        manifest_digest: ReplaySha256,
    ) -> Result<Self, ReplayCaptureError> {
        let projection = checked_projection(ReplayOwnerProjection {
            version: ReplayVersion,
            state: state.projection.clone(),
            routes,
            stable_artifacts,
            cursors,
            backend,
            run_configuration,
            policy,
            policy_digest,
            session_digest,
            latest,
            latest_artifacts,
            latest_digest,
            eligibility,
            consultation,
            manifest,
            manifest_digest,
        })?;
        let owner = Self { projection, state };
        owner.verify_recorded(&owner.projection)?;
        Ok(owner)
    }
    fn verify_recorded(&self, p: &ReplayOwnerProjection) -> Result<(), ReplayCaptureError> {
        self.state.verify_recorded(&p.state)?;
        p.verify_structure()
    }
}
impl ReplayOwnerProjection {
    fn verify_structure(&self) -> Result<(), ReplayCaptureError> {
        self.policy.verify(&self.policy_digest)?;
        if let Some(configuration) = &self.run_configuration {
            configuration.verify()?;
        }
        invariant(
            self.session_digest.0
                == canonical_value_sha256(
                    &json!({"domain":"whiel-agent-feedback-session-v2","artifact_backend":self.backend.as_str()}),
                ),
        )?;
        invariant(self.latest_digest.0 == canonical_value_sha256(&json!(self.latest)))?;
        match &self.latest {
            ReplayLatestIdentity::Failure { artifacts, .. } => {
                invariant(artifacts.len() == self.latest_artifacts.len())?;
                for (a, b) in artifacts.iter().zip(&self.latest_artifacts) {
                    invariant(
                        a.backend_matches_only
                            && a.local_id == b.local_id
                            && serde_json::to_value(&a.kind).ok()
                                == Some(json!(replay_artifact_wire_name(&b.kind))),
                    )?;
                }
            }
            _ => invariant(self.latest_artifacts.is_empty())?,
        }
        let state = &self.state;
        let e = &self.eligibility;
        let m = &self.manifest;
        let c = &self.consultation;
        invariant(
            e.core == state.core
                && e.proposal_revision == state.proposal_revision
                && e.expected_registration_ordinal == state.catalog.registration_ordinal,
        )?;
        let visible = state
            .committed
            .iter()
            .chain(&state.pending)
            .map(|(id, _)| *id)
            .chain(state.dead.iter().map(|d| d.clause))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        invariant(e.visible_records == visible && m.pending.len() == state.pending.len())?;
        for (entry, (id, level)) in m.pending.iter().zip(&state.pending) {
            let record = state
                .catalog
                .records
                .get(*id as usize)
                .ok_or(ReplayCaptureError::OwnerInvariant)?;
            invariant(
                entry.clause_id == *id
                    && entry.level == *level
                    && entry.record_digest == record.record_digest
                    && entry.drop_eligible == e.drop_eligible_records.contains(id),
            )?;
        }
        invariant(
            e.drop_eligible_records.windows(2).all(|w| w[0] < w[1])
                && e.drop_eligible_records.iter().all(|id| {
                    state.pending.iter().any(|(pending, _)| pending == id)
                        && !state.catalog.records[*id as usize].protected
                }),
        )?;
        let nanos = c
            .remaining_search_budget_ns
            .parse::<u128>()
            .map_err(|_| ReplayCaptureError::OwnerInvariant)?;
        invariant(
            nanos.to_string() == c.remaining_search_budget_ns
                && c.iteration > 0
                && c.clause_page_start <= visible.len()
                && c.ledger_page_end <= state.ledger.len(),
        )?;
        invariant(
            m.consultation_digest.0
                == canonical_value_sha256(
                    &json!({"domain":"whiel-agent-consultation-v2","task_digest":canonical_value_sha256(&json!(state.catalog.scope.task)),"scope_digest":state.catalog.scope.digest,"run_digest":state.catalog.instance_digest,"iteration":c.iteration,"state_snapshot_digest":state.state_snapshot_digest,"latest_digest":self.latest_digest,"session_digest":self.session_digest,"remaining_search_budget_ns":c.remaining_search_budget_ns,"clause_page_start":c.clause_page_start,"ledger_page_end":c.ledger_page_end,"policy_digest":self.policy_digest}),
                ),
        )?;
        invariant(
            m.task == state.catalog.scope.task
                && m.scope_digest == state.catalog.scope.digest
                && m.run_digest == state.catalog.instance_digest
                && m.session_digest == self.session_digest
                && m.policy_digest == self.policy_digest
                && m.proposal_revision == state.proposal_revision
                && m.registration_ordinal == state.catalog.registration_ordinal
                && m.state_snapshot_digest == state.state_snapshot_digest
                && m.core_partition_digest == state.core.partition_digest,
        )?;
        invariant(self.manifest_digest.0 == canonical_value_sha256(&json!(m)))?;
        invariant(
            m.shown_clauses
                .windows(2)
                .all(|w| w[0].clause_id < w[1].clause_id)
                && m.shown_drops
                    .windows(2)
                    .all(|w| w[0].authorization_digest.0 < w[1].authorization_digest.0)
                && m.artifact_references
                    .windows(2)
                    .all(|w| w[0].stable_id.0 < w[1].stable_id.0)
                && m.core_clause_ids.windows(2).all(|w| w[0] < w[1]),
        )?;
        for clause in &m.shown_clauses {
            let r = state
                .catalog
                .records
                .get(clause.clause_id as usize)
                .ok_or(ReplayCaptureError::OwnerInvariant)?;
            invariant(
                clause.record_digest == r.record_digest.0
                    && clause.formula_digest == r.formula_digest.0,
            )?;
        }
        for drop in &m.shown_drops {
            let r = state
                .catalog
                .records
                .get(drop.clause_id as usize)
                .ok_or(ReplayCaptureError::OwnerInvariant)?;
            invariant(
                e.drop_eligible_records.contains(&drop.clause_id)
                    && drop.authorization_digest.0
                        == canonical_value_sha256(
                            &json!({"domain":"whiel-agent-shown-drop-v1","consultation_digest":m.consultation_digest,"proposal_revision":state.proposal_revision,"registration_ordinal":state.catalog.registration_ordinal,"record_digest":r.record_digest,"clause_id":drop.clause_id}),
                        ),
            )?;
        }
        invariant(
            m.core_clause_ids
                .iter()
                .all(|id| state.core.canonical_order.contains(id)),
        )?;
        invariant(
            self.stable_artifacts
                .windows(2)
                .all(|w| w[0].stable_id.0 < w[1].stable_id.0),
        )?;
        for reference in &self.stable_artifacts {
            invariant(
                reference.artifact.backend == self.backend
                    && reference.stable_id.0
                        == canonical_value_sha256(
                            &json!({"domain":"whiel-agent-artifact-reference-v1","run_digest":m.run_digest,"session_digest":self.session_digest,"local_id":reference.artifact.local_id,"artifact_kind":replay_artifact_wire_name(&reference.artifact.kind),"role":reference.role}),
                        ),
            )?;
        }
        for reference in &m.artifact_references {
            let all = self
                .stable_artifacts
                .iter()
                .find(|r| r.stable_id == reference.stable_id)
                .ok_or(ReplayCaptureError::OwnerInvariant)?;
            invariant(
                all.artifact.local_id == reference.local_id
                    && json!(reference.kind)
                        == json!(replay_artifact_wire_name(&all.artifact.kind)),
            )?;
        }
        for cursor in &self.cursors {
            invariant(
                cursor.source_consultation_digest == m.consultation_digest
                    && cursor.state_snapshot_digest == state.state_snapshot_digest
                    && cursor.token_digest.0
                        == canonical_value_sha256(
                            &json!({"domain":"whiel-agent-feedback-cursor-v2","category":cursor.category,"offset":cursor.offset,"source_consultation_digest":cursor.source_consultation_digest,"state_snapshot_digest":cursor.state_snapshot_digest,"policy_digest":self.policy_digest}),
                        ),
            )?;
        }
        invariant(
            self.consultation.reconciled_host_limits.native()
                == self
                    .policy
                    .host_limits
                    .native()
                    .with_level_bound(state.core.max_level)
                    .map_err(|_| ReplayCaptureError::OwnerInvariant)?,
        )?;
        let rows = state
            .ledger
            .iter()
            .filter(|r| matches!(r, ReplayLedgerRowProjection::Attempt { .. }))
            .collect::<Vec<_>>();
        invariant(rows.len() == self.routes.len())?;
        for (row, route) in rows.iter().zip(&self.routes) {
            invariant(
                row.ordinal() == route.row_ordinal
                    && route.route_digest.0 == canonical_value_sha256(&json!(route.route)),
            )?;
        }
        Ok(())
    }
}

fn replay_artifact_wire_name(kind: &ReplayArtifactKind) -> &'static str {
    match kind {
        ReplayArtifactKind::Query => "query",
        ReplayArtifactKind::Proof => "proof",
        ReplayArtifactKind::Model => "model",
        ReplayArtifactKind::EmptyInstanceCheck => "empty_instance_check",
        ReplayArtifactKind::InitializationCheck => "initialization_check",
        ReplayArtifactKind::Certificate => "certificate",
        ReplayArtifactKind::AcceptanceRecord => "acceptance_record",
        ReplayArtifactKind::Witness => "witness",
        ReplayArtifactKind::FailureDiagnostic => "failure_diagnostic",
        ReplayArtifactKind::RuntimeTrace => "runtime_trace",
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(super) enum ReplayRunConfigurationKind {
    #[serde(rename = "whiel_framework_ii_run_configuration")]
    V2,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(super) enum ReplayRetention {
    All,
    CertificateOnly,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(super) enum ReplayCascPortfolio {
    Disabled,
    Enabled,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(super) enum ReplayPremiseRole {
    Axiom,
    NegatedConjecture,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayRetryPolicy {
    baseline_nanos: u64,
    allowance_nanos: Vec<u64>,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayRunConfiguration {
    kind: ReplayRunConfigurationKind,
    version: ReplayVersion<4>,
    compress_core: bool,
    #[serde(deserialize_with = "nullable")]
    level_bound: Option<u64>,
    retry_policy: ReplayRetryPolicy,
    casc_portfolio: ReplayCascPortfolio,
    retry_premise_role: ReplayPremiseRole,
    tools: Vec<super::replay_identity::ToolV1>,
    retention: ReplayRetention,
}
impl ReplayRunConfiguration {
    pub(super) fn capture(value: Value) -> Result<Self, ReplayCaptureError> {
        let native = super::publication::RunConfiguration::from_json(&value)
            .map_err(|_| ReplayCaptureError::UnsupportedSchema)?;
        invariant(native.to_json() == value)?;
        checked_projection(decode_owner::<Self>(&value)?)
    }
    fn verify(&self) -> Result<(), ReplayCaptureError> {
        Self::capture(json!(self)).map(|_| ())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub(super) enum ReplayStateError {
    WrongScope {},
    InvalidCatalogInstanceDigest {},
    WrongCatalog {},
    UnexpectedRegistrationBatch {
        expected: u64,
        found: u64,
    },
    RegistrationBatchIdentityExhausted {},
    ConflictingFormulaMetadata {},
    ClauseIdentityExhausted {},
    ClauseLimitExceeded {
        found: usize,
        limit: usize,
    },
    UnknownClause {
        clause: u64,
    },
    CatalogPoisoned {},
    InvalidPlacement {
        detail: String,
    },
    InvalidEvidence {
        detail: String,
    },
    Cancelled {},
    CheckerFailure {
        detail_digest: ReplaySha256,
    },
    InvalidSystemRouteDigest {},
    NonSystemReservation {},
    PropheticSystemClause {},
    ConflictingSystemOrigins {},
    SystemReservationAlreadyClosed {},
    SystemOriginOutsideReservation {},
    DeadClauseRejected {
        clause: u64,
        reason: super::replay_identity::DeadReasonV1,
    },
    LevelBoundExceeded {
        #[serde(deserialize_with = "nullable")]
        clause: Option<u64>,
        minimum_level: u64,
        max_level: u64,
    },
    EdgeInputRequiresSymbolicMigration {
        field: String,
    },
}
impl ReplayStateError {
    fn capture(error: &super::FrameworkIIStateError) -> Result<Self, ReplayCaptureError> {
        use super::FrameworkIIStateError as E;
        checked_projection(match error {
            E::WrongScope => Self::WrongScope {},
            E::InvalidCatalogInstanceDigest => Self::InvalidCatalogInstanceDigest {},
            E::WrongCatalog => Self::WrongCatalog {},
            E::UnexpectedRegistrationBatch { expected, found } => {
                Self::UnexpectedRegistrationBatch {
                    expected: *expected,
                    found: *found,
                }
            }
            E::RegistrationBatchIdentityExhausted => Self::RegistrationBatchIdentityExhausted {},
            E::ConflictingFormulaMetadata => Self::ConflictingFormulaMetadata {},
            E::ClauseIdentityExhausted => Self::ClauseIdentityExhausted {},
            E::ClauseLimitExceeded { found, limit } => Self::ClauseLimitExceeded {
                found: *found,
                limit: *limit,
            },
            E::UnknownClause(clause) => Self::UnknownClause { clause: *clause },
            E::CatalogPoisoned => Self::CatalogPoisoned {},
            E::InvalidPlacement(detail) => Self::InvalidPlacement {
                detail: (*detail).into(),
            },
            E::InvalidEvidence(detail) => Self::InvalidEvidence {
                detail: (*detail).into(),
            },
            E::Cancelled => Self::Cancelled {},
            E::CheckerFailure(detail) => {
                if super::Redaction::changes(detail.as_bytes()) {
                    return Err(ReplayCaptureError::SemanticRedaction);
                }
                Self::CheckerFailure {
                    detail_digest: decode_owner(&json!(canonical_value_sha256(&json!(
                        detail.as_ref()
                    ))))?,
                }
            }
            E::InvalidSystemRouteDigest => Self::InvalidSystemRouteDigest {},
            E::NonSystemReservation => Self::NonSystemReservation {},
            E::PropheticSystemClause => Self::PropheticSystemClause {},
            E::ConflictingSystemOrigins => Self::ConflictingSystemOrigins {},
            E::SystemReservationAlreadyClosed => Self::SystemReservationAlreadyClosed {},
            E::SystemOriginOutsideReservation => Self::SystemOriginOutsideReservation {},
            E::DeadClauseRejected { clause, reason } => Self::DeadClauseRejected {
                clause: clause.get(),
                reason: decode_owner(&reason.identity_fields())?,
            },
            E::LevelBoundExceeded {
                clause,
                minimum_level,
                max_level,
            } => Self::LevelBoundExceeded {
                clause: clause.map(|id| id.get()),
                minimum_level: *minimum_level,
                max_level: *max_level,
            },
            E::EdgeInputRequiresSymbolicMigration(field) => {
                Self::EdgeInputRequiresSymbolicMigration {
                    field: (*field).into(),
                }
            }
        })
    }
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub(super) enum ReplayTerminationResult {
    Applied {
        outcome: Box<ReplayOutcomeProjection>,
    },
    Failure {
        failure: ReplayPrivateFailure,
    },
    StateError {
        error: ReplayStateError,
    },
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayTerminationProjection {
    pub ordinal: u64,
    pub core: ReplayPartitionProjection,
    pub result: ReplayTerminationResult,
}
#[derive(Clone)]
struct ReplayTerminationOwner {
    projection: ReplayTerminationProjection,
    observation: super::stabilization::ReplayTerminationObservation,
    evidence: Option<ReplayEvidenceOwner>,
}
fn private_failure_projection(
    report: &crate::failure::FailureReport,
) -> Result<ReplayPrivateFailure, ReplayCaptureError> {
    ReplayPrivateFailure::capture(report).map_err(|e| match e {
        ReplayPrivateFailureError::Redacted => ReplayCaptureError::SemanticRedaction,
        ReplayPrivateFailureError::Unsupported => ReplayCaptureError::UnsupportedSchema,
    })
}
impl ReplayTerminationOwner {
    fn capture(
        observation: &super::stabilization::ReplayTerminationObservation,
    ) -> Result<Self, ReplayCaptureError> {
        let (result, evidence) = match &observation.result {
            Ok(super::FrameworkIICheckExecution::Applied(outcome)) => {
                let evidence = ReplayEvidenceOwner::capture(outcome.evidence())?;
                let projected = evidence.projection.clone();
                let outcome = match outcome {
                    super::FrameworkIICheckOutcome::Proved(_) => ReplayOutcomeProjection::Proved {
                        evidence: projected,
                    },
                    super::FrameworkIICheckOutcome::Refuted(_) => {
                        ReplayOutcomeProjection::Refuted {
                            evidence: projected,
                        }
                    }
                    super::FrameworkIICheckOutcome::Inconclusive { reason, .. } => {
                        ReplayOutcomeProjection::Inconclusive {
                            reason: decode_owner(&json!(reason.identity_name()))?,
                            evidence: projected,
                        }
                    }
                };
                (
                    ReplayTerminationResult::Applied {
                        outcome: Box::new(outcome),
                    },
                    Some(evidence),
                )
            }
            Ok(super::FrameworkIICheckExecution::Failure(report)) => (
                ReplayTerminationResult::Failure {
                    failure: private_failure_projection(report)?,
                },
                None,
            ),
            Err(error) => (
                ReplayTerminationResult::StateError {
                    error: ReplayStateError::capture(error)?,
                },
                None,
            ),
        };
        Ok(Self {
            projection: ReplayTerminationProjection {
                ordinal: observation.ordinal,
                core: ReplayPartitionProjection::capture(&observation.core)?,
                result,
            },
            observation: observation.clone(),
            evidence,
        })
    }
    fn verify_recorded(
        &self,
        p: &ReplayTerminationProjection,
        catalog: &ReplayCatalogProjection,
    ) -> Result<(), ReplayCaptureError> {
        p.core.verify(catalog)?;
        invariant(p.ordinal == self.observation.ordinal)?;
        match (&p.result, &self.observation.result) {
            (
                ReplayTerminationResult::Applied { outcome },
                Ok(super::FrameworkIICheckExecution::Applied(_)),
            ) => {
                let evidence = self
                    .evidence
                    .as_ref()
                    .ok_or(ReplayCaptureError::OwnerInvariant)?;
                evidence.verify_recorded(outcome.evidence())?;
                invariant(
                    outcome.evidence().request_digest.0
                        == canonical_value_sha256(
                            &json!({"kind":"whiel_framework_ii_termination_request","version":1,"scope_identity":p.core.scope.identity,"snapshot":p.core.worker_identity}),
                        ),
                )
            }
            (
                ReplayTerminationResult::Failure { failure },
                Ok(super::FrameworkIICheckExecution::Failure(report)),
            ) => {
                // This path has no remappable outer constructor. Exact private
                // detail commitment and typed metadata are compared by the graph.
                let native = private_failure_projection(report)?;
                invariant(failure.detail_digest == native.detail_digest)
            }
            (ReplayTerminationResult::StateError { error }, Err(native)) => {
                invariant(error == &ReplayStateError::capture(native)?)
            }
            _ => Err(ReplayCaptureError::OwnerInvariant),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayStableArtifactProjection {
    pub stable_id: ReplaySha256,
    pub role: super::replay_identity::ArtifactRoleV1,
    pub artifact: ReplayArtifactIdentity,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayRouteProjection {
    pub row_ordinal: LedgerRowOrdinal,
    pub route: super::replay_identity::RouteV1,
    pub route_digest: ReplaySha256,
}

fn production_digest(p: &ReplayProductionProjection) -> &ReplaySha256 {
    match p {
        ReplayProductionProjection::RuntimeProof {
            original_digest, ..
        }
        | ReplayProductionProjection::Protected {
            original_digest, ..
        }
        | ReplayProductionProjection::Progress {
            original_digest, ..
        }
        | ReplayProductionProjection::ValidatedRefutation {
            original_digest, ..
        }
        | ReplayProductionProjection::SemanticReuse {
            original_digest, ..
        } => original_digest,
    }
}
fn owner_divergence(path: &str) -> ReplayDivergence {
    ReplayDivergence {
        path: path.into(),
        reason: "fresh owner constructor verification failed".into(),
    }
}
impl ReplayProductionBindings for ReplayCorrespondenceV1 {
    fn bind_identity(
        &mut self,
        kind: ReplayProductionIdentity,
        old: &str,
        live: &str,
        path: &str,
    ) -> Result<(), ReplayDivergence> {
        self.production
            .entry(kind)
            .or_default()
            .bind(old.into(), live.into(), path)
    }
    fn require_identity(
        &self,
        kind: ReplayProductionIdentity,
        old: &str,
        live: &str,
        path: &str,
    ) -> Result<(), ReplayDivergence> {
        let map = self.production.get(&kind).ok_or_else(|| ReplayDivergence {
            path: path.into(),
            reason: "reference has no checked owner correspondence".into(),
        })?;
        same(map.mapped(&old.to_owned(), path)?, &live.to_owned(), path)
    }
    fn bind_artifact(
        &mut self,
        old: &ReplayArtifactIdentity,
        live: &ReplayArtifactIdentity,
        path: &str,
    ) -> Result<(), ReplayDivergence> {
        self.require_identity(
            ReplayProductionIdentity::Backend,
            old.backend.as_str(),
            live.backend.as_str(),
            path,
        )?;
        same(&old.kind, &live.kind, path)?;
        self.artifacts.bind(
            (old.backend.as_str().into(), old.local_id),
            (live.backend.as_str().into(), live.local_id),
            path,
        )
    }
    fn bind_attempt(
        &mut self,
        old: PhysicalAttemptId,
        live: PhysicalAttemptId,
        path: &str,
    ) -> Result<(), ReplayDivergence> {
        self.physical_attempts.bind(old, live, path)
    }
}
impl ReplayWireBindings for ReplayCorrespondenceV1 {
    fn map_identity(
        &self,
        kind: ReplayWireIdentity,
        old: &str,
    ) -> Result<String, ReplayDivergence> {
        let path = format!("wire/{kind:?}");
        self.wire
            .get(&kind)
            .ok_or_else(|| owner_divergence(&path))?
            .mapped(&old.to_owned(), &path)
            .cloned()
    }
    fn map_attempt(&self, old: PhysicalAttemptId) -> Result<PhysicalAttemptId, ReplayDivergence> {
        self.physical_attempts
            .mapped(&old, "wire/physical_attempt")
            .copied()
    }
    fn map_refutation_attempt(
        &self,
        old: PhysicalAttemptId,
    ) -> Result<PhysicalAttemptId, ReplayDivergence> {
        if !self.refutation_attempts.contains(&old) {
            return Err(owner_divergence("wire/refutation_attempt"));
        }
        self.map_attempt(old)
    }
}
impl ReplayCorrespondenceV1 {
    fn bind_wire(
        &mut self,
        kind: ReplayWireIdentity,
        old: &str,
        live: &str,
    ) -> Result<(), ReplayDivergence> {
        self.wire
            .entry(kind)
            .or_default()
            .bind(old.into(), live.into(), &format!("wire/{kind:?}"))
    }
    fn request_pair(&mut self, old: &str, live: &str) -> Result<(), ReplayDivergence> {
        self.bind_identity(ReplayProductionIdentity::CheckRequest, old, live, "request")?;
        self.bind_wire(ReplayWireIdentity::CheckRequest, old, live)
    }
    fn partition_pair(
        &mut self,
        old: &ReplayPartitionProjection,
        live: &ReplayPartitionProjection,
        old_catalog: &ReplayCatalogProjection,
        live_catalog: &ReplayCatalogProjection,
    ) -> Result<(), ReplayDivergence> {
        self.compare_partition(old, live, old_catalog, live_catalog)?;
        self.bind_identity(
            ReplayProductionIdentity::Partition,
            &old.partition_digest.0,
            &live.partition_digest.0,
            "partition",
        )?;
        self.bind_wire(
            ReplayWireIdentity::Partition,
            &old.partition_digest.0,
            &live.partition_digest.0,
        )
    }
    fn compare_failure(
        &mut self,
        old: &ReplayPrivateFailure,
        live: &ReplayPrivateFailure,
        path: &str,
    ) -> Result<(), ReplayDivergence> {
        same(&old.artifacts.len(), &live.artifacts.len(), path)?;
        for (a, b) in old.artifacts.iter().zip(&live.artifacts) {
            self.bind_artifact(a, b, path)?;
        }
        let mut expected = old.clone();
        expected.artifacts = live.artifacts.clone();
        same(&expected, live, path)
    }
    fn compare_evidence(
        &mut self,
        old: &ReplayEvidenceProjection,
        live: &ReplayEvidenceProjection,
    ) -> Result<(), ReplayDivergence> {
        self.require_identity(
            ReplayProductionIdentity::CheckRequest,
            &old.request_digest.0,
            &live.request_digest.0,
            "evidence/request",
        )?;
        for (a, b) in [
            (&old.timing.solver_time_ns, &live.timing.solver_time_ns),
            (
                &old.timing.preparation_time_ns,
                &live.timing.preparation_time_ns,
            ),
        ] {
            same(&a.is_some(), &b.is_some(), "evidence/timing_presence")?;
            for v in [a, b].into_iter().flatten() {
                let nanos = v
                    .parse::<u128>()
                    .map_err(|_| owner_divergence("evidence/timing"))?;
                same(&nanos.to_string(), v, "evidence/timing")?;
            }
        }
        match (&old.authority, &live.authority) {
            (
                ReplayEvidenceAuthority::LaunchSuppressed {},
                ReplayEvidenceAuthority::LaunchSuppressed {},
            ) => {}
            (
                ReplayEvidenceAuthority::Production {
                    projection: a,
                    preparation: ap,
                    artifacts: aa,
                },
                ReplayEvidenceAuthority::Production {
                    projection: b,
                    preparation: bp,
                    artifacts: ba,
                },
            ) => {
                super::replay_production_compare::compare_preparation(ap, bp, self)?;
                super::replay_production_compare::compare_production(a, b, aa, ba, self)?;
                self.bind_wire(
                    ReplayWireIdentity::EvidenceReceipt,
                    &production_digest(a).0,
                    &production_digest(b).0,
                )?;
                if let (
                    ReplayProductionProjection::ValidatedRefutation { fields: a, .. },
                    ReplayProductionProjection::ValidatedRefutation { fields: b, .. },
                ) = (a.as_ref(), b.as_ref())
                {
                    self.require_identity(
                        ReplayProductionIdentity::ProductionReceipt,
                        &production_digest(old_raw(old)?).0,
                        &production_digest(old_raw(live)?).0,
                        "refutation/receipt",
                    )?;
                    self.bind_attempt(a.attempt, b.attempt, "refutation/attempt")?;
                    self.refutation_attempts.insert(a.attempt);
                }
            }
            _ => return Err(owner_divergence("evidence/authority_kind")),
        }
        match (&old.reuse, &live.reuse) {
            (None, None) => {}
            (Some(a), Some(b)) => {
                super::replay_production_compare::compare_production(a, b, &[], &[], self)?
            }
            _ => return Err(owner_divergence("evidence/reuse_presence")),
        }
        self.bind_identity(
            ReplayProductionIdentity::EvidenceIdentity,
            &old.identity.0,
            &live.identity.0,
            "evidence/identity",
        )
    }
    fn compare_outcome(
        &mut self,
        old: &ReplayOutcomeProjection,
        live: &ReplayOutcomeProjection,
    ) -> Result<(), ReplayDivergence> {
        match (old, live) {
            (ReplayOutcomeProjection::Proved { .. }, ReplayOutcomeProjection::Proved { .. })
            | (ReplayOutcomeProjection::Refuted { .. }, ReplayOutcomeProjection::Refuted { .. }) => {
            }
            (
                ReplayOutcomeProjection::Inconclusive { reason: a, .. },
                ReplayOutcomeProjection::Inconclusive { reason: b, .. },
            ) => same(a, b, "outcome/reason")?,
            _ => return Err(owner_divergence("outcome/kind")),
        }
        self.compare_evidence(old.evidence(), live.evidence())
    }
    fn compare_state(
        &mut self,
        old: &ReplayStateProjection,
        live: &ReplayStateProjection,
    ) -> Result<(), ReplayDivergence> {
        self.compare_catalog(&old.catalog, &live.catalog)?;
        self.bind_identity(
            ReplayProductionIdentity::Catalog,
            &old.catalog.instance_digest.0,
            &live.catalog.instance_digest.0,
            "catalog",
        )?;
        self.bind_wire(
            ReplayWireIdentity::Run,
            &old.catalog.instance_digest.0,
            &live.catalog.instance_digest.0,
        )?;
        for (a, b) in old.catalog.records.iter().zip(&live.catalog.records) {
            self.bind_wire(
                ReplayWireIdentity::CatalogRecord,
                &a.record_digest.0,
                &b.record_digest.0,
            )?;
        }
        self.partition_pair(&old.core, &live.core, &old.catalog, &live.catalog)?;
        same(&old.core_digest, &live.core_digest, "state/core_digest")?;
        same(
            &old.proposal_revision,
            &live.proposal_revision,
            "state/proposal_revision",
        )?;
        same(&old.committed, &live.committed, "state/committed")?;
        same(&old.pending, &live.pending, "state/pending")?;
        same(&old.dead, &live.dead, "state/dead")?;
        same(
            &old.missing_roots,
            &live.missing_roots,
            "state/missing_roots",
        )?;
        same(&old.ledger.len(), &live.ledger.len(), "ledger/length")?;
        same(
            &old.termination_attempts_total,
            &live.termination_attempts_total,
            "termination/count",
        )?;
        same(
            &old.terminations.len(),
            &live.terminations.len(),
            "termination/length",
        )?;
        let mut outcomes = Vec::new();
        for (a, b) in old.ledger.iter().zip(&live.ledger) {
            same(&a.ordinal(), &b.ordinal(), "ledger/ordinal")?;
            match (a, b) {
                (
                    ReplayLedgerRowProjection::Attempt {
                        request: a,
                        outcome: ao,
                        ..
                    },
                    ReplayLedgerRowProjection::Attempt {
                        request: b,
                        outcome: bo,
                        ..
                    },
                ) => {
                    self.partition_pair(&a.snapshot, &b.snapshot, &old.catalog, &live.catalog)?;
                    let mut normalized = (**a).clone();
                    normalized.snapshot = b.snapshot.clone();
                    normalized.request_digest = b.request_digest.clone();
                    same(&normalized, b.as_ref(), "ledger/request")?;
                    self.request_pair(&a.request_digest.0, &b.request_digest.0)?;
                    outcomes.push((ao.as_ref(), bo.as_ref()));
                }
                (
                    ReplayLedgerRowProjection::Invalidation {
                        invalidated_attempt: a,
                        target: at,
                        cause: ac,
                        reason: ar,
                        ..
                    },
                    ReplayLedgerRowProjection::Invalidation {
                        invalidated_attempt: b,
                        target: bt,
                        cause: bc,
                        reason: br,
                        ..
                    },
                ) => {
                    same(a, b, "ledger/invalidated_ordinal")?;
                    same(at, bt, "ledger/invalidation_target")?;
                    same(ac, bc, "ledger/invalidation_cause")?;
                    same(ar, br, "ledger/invalidation_reason")?;
                }
                _ => return Err(owner_divergence("ledger/kind")),
            }
        }
        for (a, b) in old.terminations.iter().zip(&live.terminations) {
            same(&a.ordinal, &b.ordinal, "termination/ordinal")?;
            self.partition_pair(&a.core, &b.core, &old.catalog, &live.catalog)?;
            match (&a.result, &b.result) {
                (
                    ReplayTerminationResult::Applied { outcome: a },
                    ReplayTerminationResult::Applied { outcome: b },
                ) => {
                    self.request_pair(
                        &a.evidence().request_digest.0,
                        &b.evidence().request_digest.0,
                    )?;
                    outcomes.push((a.as_ref(), b.as_ref()));
                }
                (
                    ReplayTerminationResult::Failure { failure: a },
                    ReplayTerminationResult::Failure { failure: b },
                ) => self.compare_failure(a, b, "termination/failure")?,
                (
                    ReplayTerminationResult::StateError { error: a },
                    ReplayTerminationResult::StateError { error: b },
                ) => same(a, b, "termination/error")?,
                _ => return Err(owner_divergence("termination/result_kind")),
            }
        }
        // Ledger and termination histories interleave. An original checked
        // evidence may precede a reuse in either history; process only complete
        // dependency-satisfied pairs, transactionally, until every pair closes.
        while !outcomes.is_empty() {
            let mut pending = Vec::new();
            let mut last_error = None;
            let before = outcomes.len();
            for (a, b) in outcomes {
                let mut candidate = self.clone();
                match candidate.compare_outcome(a, b) {
                    Ok(()) => *self = candidate,
                    Err(error) => {
                        last_error = Some(error);
                        pending.push((a, b));
                    }
                }
            }
            if pending.len() == before {
                return Err(last_error.unwrap_or_else(|| owner_divergence("evidence/dependencies")));
            }
            outcomes = pending;
        }
        for (a, b) in old.ledger.iter().zip(&live.ledger) {
            self.bind_wire(ReplayWireIdentity::LedgerRow, &a.digest().0, &b.digest().0)?;
        }
        same(&old.roots.len(), &live.roots.len(), "roots/length")?;
        for (a, b) in old.roots.iter().zip(&live.roots) {
            same(&a.clause, &b.clause, "roots/clause")?;
            same(&a.role, &b.role, "roots/role")?;
            same(&a.attempt_row, &b.attempt_row, "roots/ledger_ordinal")?;
            self.require_identity(
                ReplayProductionIdentity::CheckRequest,
                &a.request_digest.0,
                &b.request_digest.0,
                "roots/request",
            )?;
            self.require_identity(
                ReplayProductionIdentity::Partition,
                &a.partition_digest.0,
                &b.partition_digest.0,
                "roots/partition",
            )?;
            self.require_identity(
                ReplayProductionIdentity::EvidenceIdentity,
                &a.evidence.identity.0,
                &b.evidence.identity.0,
                "roots/evidence",
            )?;
        }
        self.bind_wire(
            ReplayWireIdentity::StateSnapshot,
            &old.state_snapshot_digest.0,
            &live.state_snapshot_digest.0,
        )
    }
}
fn old_raw(e: &ReplayEvidenceProjection) -> Result<&ReplayProductionProjection, ReplayDivergence> {
    match &e.authority {
        ReplayEvidenceAuthority::Production { projection, .. } => Ok(projection),
        _ => Err(owner_divergence("evidence/production")),
    }
}

impl ReplayCorrespondenceV1 {
    fn compare_feedback(
        &mut self,
        old: &ReplayOwnerProjection,
        owner: &ReplayFeedbackOwner,
    ) -> Result<(), ReplayDivergence> {
        owner
            .verify_recorded(old)
            .map_err(|_| owner_divergence("feedback/recorded"))?;
        owner
            .verify_recorded(&owner.projection)
            .map_err(|_| owner_divergence("feedback/live"))?;
        let live = &owner.projection;
        same(&old.policy, &live.policy, "feedback/policy")?;
        same(
            &old.policy_digest,
            &live.policy_digest,
            "feedback/policy_digest",
        )?;
        same(
            &old.run_configuration,
            &live.run_configuration,
            "feedback/run_configuration",
        )?;
        self.bind_identity(
            ReplayProductionIdentity::Backend,
            old.backend.as_str(),
            live.backend.as_str(),
            "feedback/backend",
        )?;
        self.host
            .entry(ReplayHostIdentity::FeedbackSession)
            .or_default()
            .bind(
                old.session_digest.0.clone(),
                live.session_digest.0.clone(),
                "feedback/session",
            )?;
        self.compare_state(&old.state, &live.state)?;
        let mut eligibility = old.eligibility.clone();
        eligibility.core = live.eligibility.core.clone();
        same(&eligibility, &live.eligibility, "feedback/eligibility")?;
        let mut consultation = old.consultation.clone();
        consultation.remaining_search_budget_ns =
            live.consultation.remaining_search_budget_ns.clone();
        same(
            &consultation,
            &live.consultation,
            "feedback/consultation_inputs",
        )?;
        same(
            &old.latest_artifacts.len(),
            &live.latest_artifacts.len(),
            "feedback/latest_artifacts",
        )?;
        for (a, b) in old.latest_artifacts.iter().zip(&live.latest_artifacts) {
            self.bind_artifact(a, b, "feedback/latest_artifacts")?;
        }
        let mut latest = old.latest.clone();
        match (&mut latest, &live.latest) {
            (
                ReplayLatestIdentity::Failure { artifacts: a, .. },
                ReplayLatestIdentity::Failure { artifacts: b, .. },
            ) => {
                same(&a.len(), &b.len(), "latest/artifacts")?;
                for (a, b) in a.iter_mut().zip(b) {
                    a.local_id = b.local_id;
                }
            }
            (
                ReplayLatestIdentity::PostconditionOpen {
                    outcome: super::replay_identity::PostconditionOpenV1::Refuted { attempt: a },
                },
                ReplayLatestIdentity::PostconditionOpen {
                    outcome: super::replay_identity::PostconditionOpenV1::Refuted { attempt: b },
                },
            ) => {
                match (a.as_ref(), b) {
                    (None, None) => {}
                    (Some(a), Some(b)) => same(
                        &self.map_refutation_attempt(*a)?,
                        b,
                        "latest/refutation_attempt",
                    )?,
                    _ => return Err(owner_divergence("latest/attempt_presence")),
                }
                *a = *b;
            }
            _ => {}
        }
        same(&latest, &live.latest, "feedback/latest")?;
        self.host
            .entry(ReplayHostIdentity::LatestEvent)
            .or_default()
            .bind(
                old.latest_digest.0.clone(),
                live.latest_digest.0.clone(),
                "feedback/latest_digest",
            )?;
        self.bind_wire(
            ReplayWireIdentity::Consultation,
            &old.manifest.consultation_digest.0,
            &live.manifest.consultation_digest.0,
        )?;
        // Stable artifact hashes sort independently in each run. Match the
        // complete owner artifact+role pair, then verify both native hashes.
        same(
            &old.stable_artifacts.len(),
            &live.stable_artifacts.len(),
            "feedback/stable_artifacts_length",
        )?;
        let mut used = BTreeSet::new();
        for a in &old.stable_artifacts {
            let mapped = self.artifacts.mapped(
                &(a.artifact.backend.as_str().into(), a.artifact.local_id),
                "feedback/stable_artifact",
            )?;
            let (index, b) = live
                .stable_artifacts
                .iter()
                .enumerate()
                .find(|(_, b)| {
                    b.artifact.backend.as_str() == mapped.0
                        && b.artifact.local_id == mapped.1
                        && b.role == a.role
                })
                .ok_or_else(|| owner_divergence("feedback/stable_artifact_role"))?;
            if !used.insert(index) {
                return Err(owner_divergence("feedback/stable_artifact_duplicate"));
            }
            same(
                &a.artifact.kind,
                &b.artifact.kind,
                "feedback/stable_artifact_kind",
            )?;
            self.bind_wire(
                ReplayWireIdentity::ArtifactReference,
                &a.stable_id.0,
                &b.stable_id.0,
            )?;
        }
        same(
            &old.routes.len(),
            &live.routes.len(),
            "feedback/routes_length",
        )?;
        for (a, b) in old.routes.iter().zip(&live.routes) {
            same(&a.row_ordinal, &b.row_ordinal, "feedback/route_row")?;
            super::replay_wire_compare::compare_route(&a.route, &b.route, self)?;
            self.bind_wire(
                ReplayWireIdentity::RouteDisplay,
                &a.route_digest.0,
                &b.route_digest.0,
            )?;
        }
        let mut manifest = old.manifest.clone();
        manifest.run_digest = live.manifest.run_digest.clone();
        manifest.session_digest = live.manifest.session_digest.clone();
        manifest.consultation_digest = live.manifest.consultation_digest.clone();
        manifest.state_snapshot_digest = live.manifest.state_snapshot_digest.clone();
        manifest.core_partition_digest = live.manifest.core_partition_digest.clone();
        for entry in &mut manifest.pending {
            entry.record_digest = ReplaySha256::parse(
                &self.map_identity(ReplayWireIdentity::CatalogRecord, &entry.record_digest.0)?,
            )
            .map_err(|_| owner_divergence("manifest/pending_record"))?;
        }
        for clause in &mut manifest.shown_clauses {
            clause.record_digest =
                self.map_identity(ReplayWireIdentity::CatalogRecord, &clause.record_digest)?;
        }
        same(
            &manifest.shown_drops.len(),
            &live.manifest.shown_drops.len(),
            "manifest/drop_length",
        )?;
        for drop in &mut manifest.shown_drops {
            let paired = live
                .manifest
                .shown_drops
                .iter()
                .find(|d| d.clause_id == drop.clause_id)
                .ok_or_else(|| owner_divergence("manifest/drop_clause"))?;
            self.bind_wire(
                ReplayWireIdentity::DropAuthorization,
                &drop.authorization_digest.0,
                &paired.authorization_digest.0,
            )?;
            drop.authorization_digest = paired.authorization_digest.clone();
        }
        manifest
            .shown_drops
            .sort_by(|a, b| a.authorization_digest.0.cmp(&b.authorization_digest.0));
        for reference in &mut manifest.artifact_references {
            reference.stable_id = ReplaySha256::parse(&self.map_identity(
                ReplayWireIdentity::ArtifactReference,
                &reference.stable_id.0,
            )?)
            .map_err(|_| owner_divergence("manifest/artifact"))?;
            reference.local_id = self
                .artifacts
                .mapped(
                    &(old.backend.as_str().into(), reference.local_id),
                    "manifest/artifact_local",
                )?
                .1;
        }
        manifest
            .artifact_references
            .sort_by(|a, b| a.stable_id.0.cmp(&b.stable_id.0));
        same(&manifest, &live.manifest, "feedback/manifest")?;
        self.bind_wire(
            ReplayWireIdentity::ValidationManifest,
            &old.manifest_digest.0,
            &live.manifest_digest.0,
        )?;
        same(
            &old.cursors.len(),
            &live.cursors.len(),
            "feedback/cursors_length",
        )?;
        for (a, b) in old.cursors.iter().zip(&live.cursors) {
            same(&a.category, &b.category, "cursor/category")?;
            same(&a.offset, &b.offset, "cursor/offset")?;
            same(
                &self.map_identity(
                    ReplayWireIdentity::Consultation,
                    &a.source_consultation_digest.0,
                )?,
                &b.source_consultation_digest.0,
                "cursor/source_consultation",
            )?;
            same(
                &self.map_identity(
                    ReplayWireIdentity::StateSnapshot,
                    &a.state_snapshot_digest.0,
                )?,
                &b.state_snapshot_digest.0,
                "cursor/state",
            )?;
            self.bind_wire(
                ReplayWireIdentity::Cursor,
                &a.token_digest.0,
                &b.token_digest.0,
            )?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(super) enum ReplayRequestPolicyDomain {
    #[serde(rename = "whiel-proposer-request-policy-v1")]
    V1,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayRequestPolicyFields {
    domain: ReplayRequestPolicyDomain,
    max_request_bytes: usize,
    max_correction_diagnostics: usize,
    max_correction_bytes: usize,
    max_attempt_history_records: usize,
    max_transport_retries_per_request: usize,
    #[serde(deserialize_with = "nullable")]
    max_consultations: Option<usize>,
}
impl ReplayRequestPolicyFields {
    fn capture(policy: &super::AgentConsultationPolicy) -> Self {
        let limits = policy.limits();
        Self {
            domain: ReplayRequestPolicyDomain::V1,
            max_request_bytes: limits.max_request_bytes,
            max_correction_diagnostics: limits.max_correction_diagnostics,
            max_correction_bytes: limits.max_correction_bytes,
            max_attempt_history_records: limits.max_attempt_history_records,
            max_transport_retries_per_request: limits.max_transport_retries_per_request,
            max_consultations: limits.max_consultations,
        }
    }
    fn verify(&self, digest: &ReplaySha256) -> Result<(), ReplayCaptureError> {
        let native = super::AgentConsultationPolicy::new(super::AgentConsultationLimits {
            max_request_bytes: self.max_request_bytes,
            max_correction_diagnostics: self.max_correction_diagnostics,
            max_correction_bytes: self.max_correction_bytes,
            max_attempt_history_records: self.max_attempt_history_records,
            max_transport_retries_per_request: self.max_transport_retries_per_request,
            max_consultations: self.max_consultations,
        })
        .map_err(|_| ReplayCaptureError::OwnerInvariant)?;
        invariant(native.digest() == digest.0 && digest.0 == canonical_value_sha256(&json!(self)))
    }
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReplayPushProjection {
    version: ReplayVersion<2>,
    feedback: ReplayOwnerProjection,
    request_policy: ReplayRequestPolicyFields,
    request_policy_digest: ReplaySha256,
    push_digest: ReplaySha256,
}
fn exact_bytes_sha256(bytes: &[u8]) -> String {
    crate::encoding::bytes_sha256(bytes)
}
impl ReplayPushProjection {
    pub(super) fn capture_bounded(
        push: &super::AgentPush,
        maximum: usize,
    ) -> Result<Self, ReplayCaptureError> {
        #[derive(Serialize)]
        struct View<'a> {
            version: ReplayVersion<2>,
            feedback: &'a ReplayOwnerProjection,
            request_policy: ReplayRequestPolicyFields,
            request_policy_digest: &'a str,
            push_digest: &'a str,
        }
        let feedback = push.replay_feedback()?.replay_owner()?;
        let view = View {
            version: ReplayVersion,
            feedback: &feedback.projection,
            request_policy: ReplayRequestPolicyFields::capture(push.replay_policy()),
            request_policy_digest: push.replay_policy().digest(),
            push_digest: push.digest(),
        };
        super::transcript::encoded_size(&view, maximum)
            .map_err(|_| ReplayCaptureError::LimitExceeded)?;
        Self::capture(push)
    }
    pub(super) fn capture(push: &super::AgentPush) -> Result<Self, ReplayCaptureError> {
        let owner = push.replay_feedback()?.replay_owner()?;
        checked_projection(Self {
            version: ReplayVersion,
            feedback: owner.projection.clone(),
            request_policy: ReplayRequestPolicyFields::capture(push.replay_policy()),
            request_policy_digest: decode_owner(&json!(push.replay_policy().digest()))?,
            push_digest: decode_owner(&json!(push.digest()))?,
        })
    }
    pub(super) fn verify_push(
        &self,
        bytes: &[u8],
    ) -> Result<super::replay_identity::PushV1, ReplayDivergence> {
        self.request_policy
            .verify(&self.request_policy_digest)
            .map_err(|_| owner_divergence("push/request_policy"))?;
        same(
            &self.push_digest.0,
            &exact_bytes_sha256(bytes),
            "push/bytes_digest",
        )?;
        let push = super::replay_identity::decode_push(bytes)?;
        let binding = &push.binding;
        let state = &self.feedback.state;
        same(
            &binding.task_digest,
            &canonical_value_sha256(&json!(state.catalog.scope.task)),
            "push/task",
        )?;
        same(
            &binding.scope_digest,
            &state.catalog.scope.digest.0,
            "push/scope",
        )?;
        same(
            &binding.run_digest,
            &state.catalog.instance_digest.0,
            "push/run",
        )?;
        same(
            &binding.consultation_digest,
            &self.feedback.manifest.consultation_digest.0,
            "push/consultation",
        )?;
        same(
            &binding.state_snapshot_digest,
            &state.state_snapshot_digest.0,
            "push/state_snapshot",
        )?;
        same(
            &binding.validation_manifest_digest,
            &self.feedback.manifest_digest.0,
            "push/manifest",
        )?;
        same(
            &binding.policy_digest,
            &self.request_policy_digest.0,
            "push/policy",
        )?;
        same(
            &push.feedback.iteration,
            &self.feedback.consultation.iteration,
            "push/iteration",
        )?;
        same(
            &push.feedback.remaining_search_budget_ns,
            &self.feedback.consultation.remaining_search_budget_ns,
            "push/remaining",
        )?;
        let p = &push.feedback.presentation;
        let presentation_fields = json!({"schema_version":p.schema_version,"task":p.task,"ambient_schema":p.ambient_schema,"host_limits":p.host_limits,"resource_limits":p.resource_limits});
        same(
            &p.presentation_digest,
            &canonical_value_sha256(&presentation_fields),
            "push/presentation_digest",
        )?;
        Ok(push)
    }
}
impl ReplayCorrespondenceV1 {
    /// Validate the entire recorded owner graph and exact live push, then
    /// atomically admit its identity bijections. A failure changes no mapping.
    pub fn compare_push(
        &mut self,
        coordinates: TranscriptCoordinates,
        recorded: &ReplayPushProjection,
        recorded_bytes: &[u8],
        live: &super::AgentPush,
    ) -> Result<(), ReplayDivergence> {
        if self.finalized {
            return Err(owner_divergence("push/after_final_state"));
        }
        replay_safe_bytes(recorded_bytes)?;
        replay_safe_bytes(live.bytes())?;
        let current = ReplayPushProjection::capture(live)
            .map_err(|_| owner_divergence("push/live_capture"))?;
        let source_push = recorded.verify_push(recorded_bytes)?;
        current.verify_push(live.bytes())?;
        same(
            &recorded.request_policy,
            &current.request_policy,
            "push/request_policy",
        )?;
        same(
            &coordinates.validation,
            &(live.validation_ordinal() as u64),
            "push/coordinates/validation",
        )?;
        if self.coordinates.contains_key(&coordinates) {
            return Err(owner_divergence("push/duplicate_coordinates"));
        }
        let mut candidate = self.clone();
        candidate.bind_run_pair(recorded, &current)?;
        candidate.compare_feedback(
            &recorded.feedback,
            live.replay_feedback()
                .map_err(|_| owner_divergence("push/live_feedback"))?
                .replay_owner()
                .map_err(|_| owner_divergence("push/live_owner"))?,
        )?;
        let timing =
            super::replay_wire_compare::compare_push(recorded_bytes, live.bytes(), &candidate)?;
        candidate.bind_wire(
            ReplayWireIdentity::PushRequest,
            &recorded.push_digest.0,
            &current.push_digest.0,
        )?;
        let traffic_binding = ReplayTrafficBinding {
            old_request: recorded.push_digest.0.clone(),
            live_request: current.push_digest.0.clone(),
            old_consultation: source_push.binding.consultation_digest.clone(),
            live_consultation: current.feedback.manifest.consultation_digest.0.clone(),
            state_revision: source_push.feedback.state_revision,
        };
        candidate.push_bindings.insert(
            recorded.push_digest.0.clone(),
            super::replay_identity::ResponseBindingV1 {
                task_digest: source_push.binding.task_digest,
                scope_digest: source_push.binding.scope_digest,
                run_digest: source_push.binding.run_digest,
                consultation_digest: source_push.binding.consultation_digest,
                state_snapshot_digest: source_push.binding.state_snapshot_digest,
                validation_manifest_digest: source_push.binding.validation_manifest_digest,
                request_digest: recorded.push_digest.0.clone(),
                validation_ordinal: source_push.binding.validation_ordinal,
            },
        );
        let old_owner = audit_digest(canonical_value_sha256(&json!(recorded)))?;
        let live_owner = audit_digest(canonical_value_sha256(&json!(current)))?;
        candidate.append_new_pairs(self, &old_owner, &live_owner)?;
        candidate
            .audit
            .comparisons
            .push(ReplayComparisonRecord::Push {
                coordinates,
                old_bytes_sha256: audit_digest(recorded.push_digest.0.clone())?,
                live_bytes_sha256: audit_digest(current.push_digest.0.clone())?,
                old_owner_projection_sha256: old_owner,
                live_owner_projection_sha256: live_owner,
                semantic_core_digest: audit_digest(recorded.feedback.state.core_digest.0.clone())?,
                owner_timing: owner_timing_observations(
                    &recorded.feedback.state,
                    &current.feedback.state,
                ),
                old_ledger_chain_digest: audit_digest(canonical_value_sha256(&json!(
                    recorded.feedback.state.ledger
                )))?,
                live_ledger_chain_digest: audit_digest(canonical_value_sha256(&json!(
                    current.feedback.state.ledger
                )))?,
                timing,
            });
        candidate.coordinates.insert(coordinates, traffic_binding);
        *self = candidate;
        Ok(())
    }
}

impl ReplayCorrespondenceV1 {
    pub fn compare_tool_response(
        &mut self,
        coordinates: TranscriptCoordinates,
        call_id: u64,
        recorded: &[u8],
        live: &[u8],
    ) -> Result<Vec<super::replay_wire_compare::ReplayTimingDifference>, ReplayDivergence> {
        replay_safe_bytes(recorded)?;
        replay_safe_bytes(live)?;
        self.require_coordinates(coordinates)?;
        let name = self
            .tool_calls
            .get(&(coordinates, call_id))
            .ok_or_else(|| owner_divergence("tool_response/missing_call"))?;
        if self.completed_tools.contains(&(coordinates, call_id)) {
            return Err(owner_divergence("tool_response/duplicate"));
        }
        let binding = self
            .coordinates
            .get(&coordinates)
            .expect("checked coordinates");
        for bytes in [recorded, live] {
            let value = super::replay_identity::decode_tool_response(bytes)?;
            let (tool, revision) = tool_response_stamp(&value);
            same(&tool, name, "tool_response/name")?;
            same(
                &revision,
                &binding.state_revision,
                "tool_response/state_revision",
            )?;
        }
        let timing = super::replay_wire_compare::compare_tool_response(recorded, live, self)?;
        self.completed_tools.insert((coordinates, call_id));
        self.audit
            .comparisons
            .push(ReplayComparisonRecord::ToolResponse {
                coordinates,
                call_id,
                old_bytes_sha256: audit_digest(exact_bytes_sha256(recorded))?,
                live_bytes_sha256: audit_digest(exact_bytes_sha256(live))?,
                timing: timing.clone(),
            });
        Ok(timing)
    }
    pub fn compare_correction(
        &mut self,
        coordinates: TranscriptCoordinates,
        recorded: &[u8],
        live: &[u8],
    ) -> Result<Vec<super::replay_wire_compare::ReplayTimingDifference>, ReplayDivergence> {
        replay_safe_bytes(recorded)?;
        replay_safe_bytes(live)?;
        self.require_coordinates(coordinates)?;
        let binding = self
            .coordinates
            .get(&coordinates)
            .expect("checked coordinates");
        for (bytes, consultation) in [
            (recorded, &binding.old_consultation),
            (live, &binding.live_consultation),
        ] {
            let correction: super::replay_identity::CorrectionV1 =
                super::replay_identity::decode_wire(bytes)?;
            same(
                &correction.binding.consultation_digest,
                consultation,
                "correction/traffic_consultation",
            )?;
            same(
                &correction.binding.correction_ordinal,
                &coordinates
                    .validation
                    .checked_add(1)
                    .ok_or_else(|| owner_divergence("correction/ordinal_overflow"))?,
                "correction/traffic_ordinal",
            )?;
        }
        let timing = super::replay_wire_compare::compare_correction(recorded, live, self)?;
        self.audit
            .comparisons
            .push(ReplayComparisonRecord::Correction {
                coordinates,
                old_bytes_sha256: audit_digest(exact_bytes_sha256(recorded))?,
                live_bytes_sha256: audit_digest(exact_bytes_sha256(live))?,
                timing: timing.clone(),
            });
        Ok(timing)
    }
    pub fn response_rebinding(
        &self,
        recorded: &[u8],
    ) -> super::replay_wire_compare::ReplayWireRebinding {
        let mut plan = super::replay_wire_compare::rebind_response(recorded, self);
        if plan.parsed {
            return plan;
        }
        let Some(binding) = super::agent::replay_unsupported_counterexample_binding(recorded)
        else {
            return plan;
        };
        if self.push_bindings.get(&binding.request_digest) != Some(&binding) {
            return plan;
        }
        let mut replacements = Vec::new();
        for (kind, field, value) in [
            (ReplayWireIdentity::Run, "run_digest", &binding.run_digest),
            (
                ReplayWireIdentity::Consultation,
                "consultation_digest",
                &binding.consultation_digest,
            ),
            (
                ReplayWireIdentity::StateSnapshot,
                "state_snapshot_digest",
                &binding.state_snapshot_digest,
            ),
            (
                ReplayWireIdentity::ValidationManifest,
                "validation_manifest_digest",
                &binding.validation_manifest_digest,
            ),
            (
                ReplayWireIdentity::PushRequest,
                "request_digest",
                &binding.request_digest,
            ),
        ] {
            let Ok(live) = self.map_identity(kind, value) else {
                return plan;
            };
            if &live != value {
                replacements.push(
                    super::replay_wire_compare::ReplayWireReplacement::Identity {
                        path: format!("/binding/{field}"),
                        identity: kind,
                        old: value.clone(),
                        live,
                    },
                );
            }
        }
        plan.parsed = true;
        plan.replacements = replacements;
        plan
    }
    pub fn tool_argument_rebinding(
        &self,
        tool: &str,
        recorded: &[u8],
    ) -> super::replay_wire_compare::ReplayWireRebinding {
        super::replay_wire_compare::rebind_tool_arguments(tool, recorded, self)
    }
    /// Apply only a plan produced from this correspondence. Malformed or
    /// intentionally invalid inputs remain byte-for-byte unchanged.
    pub fn rebind_response_bytes(&self, recorded: &[u8]) -> Result<Vec<u8>, ReplayDivergence> {
        apply_rebinding(recorded, &self.response_rebinding(recorded))
    }
    pub fn rebind_tool_argument_bytes(
        &self,
        tool: &str,
        recorded: &[u8],
    ) -> Result<Vec<u8>, ReplayDivergence> {
        apply_rebinding(recorded, &self.tool_argument_rebinding(tool, recorded))
    }
}
fn apply_rebinding(
    bytes: &[u8],
    plan: &super::replay_wire_compare::ReplayWireRebinding,
) -> Result<Vec<u8>, ReplayDivergence> {
    use super::replay_wire_compare::ReplayWireReplacement as R;
    if !plan.parsed || plan.replacements.is_empty() {
        return Ok(bytes.to_vec());
    }
    let spans = json_scalar_spans(bytes)?;
    let mut edits = Vec::new();
    let mut seen = BTreeSet::new();
    for replacement in &plan.replacements {
        let (path, old, live) = match replacement {
            R::Identity {
                path, old, live, ..
            } => (path, json!(old), json!(live)),
            R::PhysicalAttempt { path, old, live } => (path, json!(old.0), json!(live.0)),
        };
        if !seen.insert(path) {
            return Err(owner_divergence("rebind/duplicate_path"));
        }
        let (start, end) = *spans.get(path).ok_or_else(|| owner_divergence(path))?;
        let actual: Value =
            serde_json::from_slice(&bytes[start..end]).map_err(|_| owner_divergence(path))?;
        same(&actual, &old, path)?;
        let encoded = match (&old, &live) {
            (Value::String(old), Value::String(live))
                if old.len() == 64
                    && live.len() == 64
                    && old
                        .bytes()
                        .chain(live.bytes())
                        .all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase()) =>
            {
                preserve_hash_token(&bytes[start..end], live)?
            }
            _ => serde_json::to_vec(&live).map_err(|_| owner_divergence(path))?,
        };
        edits.push((start, end, encoded));
    }
    edits.sort_by_key(|edit| edit.0);
    let mut result = Vec::with_capacity(bytes.len());
    let mut cursor = 0;
    for (start, end, replacement) in edits {
        if start < cursor {
            return Err(owner_divergence("rebind/overlap"));
        }
        result.extend_from_slice(&bytes[cursor..start]);
        result.extend(replacement);
        cursor = end;
    }
    result.extend_from_slice(&bytes[cursor..]);
    Ok(result)
}
fn json_scalar_spans(bytes: &[u8]) -> Result<BTreeMap<String, (usize, usize)>, ReplayDivergence> {
    struct Reader<'a> {
        bytes: &'a [u8],
        position: usize,
        spans: BTreeMap<String, (usize, usize)>,
    }
    impl Reader<'_> {
        fn whitespace(&mut self) {
            while self
                .bytes
                .get(self.position)
                .is_some_and(u8::is_ascii_whitespace)
            {
                self.position += 1;
            }
        }
        fn byte(&mut self, wanted: u8) -> Result<(), ReplayDivergence> {
            self.whitespace();
            if self.bytes.get(self.position) != Some(&wanted) {
                return Err(owner_divergence("rebind/json_token"));
            }
            self.position += 1;
            Ok(())
        }
        fn string(&mut self) -> Result<(usize, usize), ReplayDivergence> {
            let start = self.position;
            self.byte(b'"')?;
            while let Some(byte) = self.bytes.get(self.position) {
                self.position += 1;
                match byte {
                    b'"' => return Ok((start, self.position)),
                    b'\\' => {
                        if self.position >= self.bytes.len() {
                            break;
                        }
                        self.position += 1;
                    }
                    _ => {}
                }
            }
            Err(owner_divergence("rebind/json_string"))
        }
        fn value(&mut self, path: String, depth: usize) -> Result<(), ReplayDivergence> {
            if depth > 128 {
                return Err(owner_divergence("rebind/json_depth"));
            }
            self.whitespace();
            let start = self.position;
            match self.bytes.get(self.position) {
                Some(b'{') => {
                    self.position += 1;
                    self.whitespace();
                    if self.bytes.get(self.position) == Some(&b'}') {
                        self.position += 1;
                        return Ok(());
                    }
                    loop {
                        self.whitespace();
                        let (a, b) = self.string()?;
                        let key: String = serde_json::from_slice(&self.bytes[a..b])
                            .map_err(|_| owner_divergence("rebind/json_key"))?;
                        self.byte(b':')?;
                        self.value(
                            format!("{}/{}", path, key.replace('~', "~0").replace('/', "~1")),
                            depth + 1,
                        )?;
                        self.whitespace();
                        match self.bytes.get(self.position) {
                            Some(b',') => self.position += 1,
                            Some(b'}') => {
                                self.position += 1;
                                break;
                            }
                            _ => return Err(owner_divergence("rebind/json_object")),
                        }
                    }
                }
                Some(b'[') => {
                    self.position += 1;
                    self.whitespace();
                    if self.bytes.get(self.position) == Some(&b']') {
                        self.position += 1;
                        return Ok(());
                    }
                    let mut index = 0;
                    loop {
                        self.value(format!("{path}/{index}"), depth + 1)?;
                        index += 1;
                        self.whitespace();
                        match self.bytes.get(self.position) {
                            Some(b',') => self.position += 1,
                            Some(b']') => {
                                self.position += 1;
                                break;
                            }
                            _ => return Err(owner_divergence("rebind/json_array")),
                        }
                    }
                }
                Some(b'"') => {
                    self.string()?;
                    if self.spans.insert(path, (start, self.position)).is_some() {
                        return Err(owner_divergence("rebind/duplicate_scalar"));
                    }
                }
                Some(_) => {
                    while self.bytes.get(self.position).is_some_and(|b| {
                        !b.is_ascii_whitespace() && !matches!(b, b',' | b']' | b'}')
                    }) {
                        self.position += 1;
                    }
                    if start == self.position {
                        return Err(owner_divergence("rebind/json_scalar"));
                    }
                    if self.spans.insert(path, (start, self.position)).is_some() {
                        return Err(owner_divergence("rebind/duplicate_scalar"));
                    }
                }
                None => return Err(owner_divergence("rebind/json_eof")),
            }
            Ok(())
        }
    }
    let mut reader = Reader {
        bytes,
        position: 0,
        spans: BTreeMap::new(),
    };
    reader.value(String::new(), 0)?;
    reader.whitespace();
    if reader.position != bytes.len() {
        return Err(owner_divergence("rebind/json_trailing"));
    }
    Ok(reader.spans)
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReplayResponseChunk {
    pub bytes: Vec<u8>,
    pub accounting: super::ResponseChunkAccounting,
}
fn retained_response(
    chunks: &[ReplayResponseChunk],
) -> Result<(Vec<u8>, Vec<u8>, bool), ReplayDivergence> {
    let mut all = Vec::new();
    let mut retained = Vec::new();
    let mut maximum = None;
    let mut exceeded = false;
    let mut observed = 0usize;
    for (index, chunk) in chunks.iter().enumerate() {
        let count = &chunk.accounting;
        if index == 0 {
            maximum = count.maximum_bytes
        } else {
            same(&maximum, &count.maximum_bytes, "response/maximum")?;
        }
        all.extend_from_slice(&chunk.bytes);
        observed = observed.saturating_add(chunk.bytes.len());
        let accepted = match maximum {
            None => {
                retained.extend_from_slice(&chunk.bytes);
                true
            }
            Some(maximum) if !exceeded => {
                let remaining = maximum.saturating_sub(retained.len());
                retained.extend_from_slice(&chunk.bytes[..chunk.bytes.len().min(remaining)]);
                exceeded = chunk.bytes.len() > remaining;
                !exceeded
            }
            Some(_) => false,
        };
        same(&accepted, &count.accepted, "response/chunk_acceptance")?;
        same(&observed, &count.observed_bytes, "response/observed_bytes")?;
        same(
            &retained.len(),
            &count.retained_bytes,
            "response/retained_bytes",
        )?;
    }
    Ok((all, retained, exceeded))
}
impl ReplayCorrespondenceV1 {
    pub fn compare_response_chunks(
        &mut self,
        coordinates: TranscriptCoordinates,
        recorded_request: &str,
        live_request: &str,
        recorded: &[ReplayResponseChunk],
        live: &[ReplayResponseChunk],
    ) -> Result<(), ReplayDivergence> {
        self.require_coordinates(coordinates)?;
        let binding = self
            .coordinates
            .get(&coordinates)
            .expect("checked coordinates");
        same(
            &binding.old_request,
            &recorded_request.to_owned(),
            "response/coordinates/recorded_request",
        )?;
        same(
            &binding.live_request,
            &live_request.to_owned(),
            "response/coordinates/live_request",
        )?;
        same(
            &self.map_identity(ReplayWireIdentity::PushRequest, recorded_request)?,
            &live_request.to_owned(),
            "response/request",
        )?;
        same(&recorded.len(), &live.len(), "response/chunks_length")?;
        for (a, b) in recorded.iter().zip(live) {
            same(&a.bytes.len(), &b.bytes.len(), "response/chunk_boundary")?;
            same(&a.accounting, &b.accounting, "response/chunk_accounting")?;
        }
        let (old_all, old_retained, old_exceeded) = retained_response(recorded)?;
        let (live_all, live_retained, live_exceeded) = retained_response(live)?;
        replay_safe_bytes(&old_all)?;
        replay_safe_bytes(&live_all)?;
        same(&old_exceeded, &live_exceeded, "response/oversized")?;
        same(
            &self.rebind_response_bytes(&old_all)?,
            &live_all,
            "response/exact_rebound_bytes",
        )?;
        let mut candidate = self.clone();
        candidate.bind_wire(
            ReplayWireIdentity::Response,
            &exact_bytes_sha256(&old_retained),
            &exact_bytes_sha256(&live_retained),
        )?;
        if old_exceeded {
            let old_count = &recorded
                .last()
                .ok_or_else(|| owner_divergence("response/missing_chunk"))?
                .accounting;
            let live_count = &live
                .last()
                .ok_or_else(|| owner_divergence("response/missing_chunk"))?
                .accounting;
            let digest = |request: &str, count: &super::ResponseChunkAccounting, prefix: &[u8]| {
                canonical_value_sha256(
                    &json!({"domain":"whiel-oversized-agent-response-v1","request_digest":request,"maximum_bytes":count.maximum_bytes,"observed_bytes_at_least":count.observed_bytes,"bounded_prefix_digest":exact_bytes_sha256(prefix)}),
                )
            };
            candidate.bind_wire(
                ReplayWireIdentity::Response,
                &digest(recorded_request, old_count, &old_retained),
                &digest(live_request, live_count, &live_retained),
            )?;
        }
        let old_chain = audit_digest(canonical_value_sha256(&json!(recorded)))?;
        let live_chain = audit_digest(canonical_value_sha256(&json!(live)))?;
        candidate.append_new_pairs(self, &old_chain, &live_chain)?;
        candidate
            .audit
            .comparisons
            .push(ReplayComparisonRecord::ResponseChunks {
                coordinates,
                old_complete_bytes_sha256: audit_digest(exact_bytes_sha256(&old_all))?,
                live_complete_bytes_sha256: audit_digest(exact_bytes_sha256(&live_all))?,
                old_chunk_chain_sha256: old_chain,
                live_chunk_chain_sha256: live_chain,
            });
        *self = candidate;
        Ok(())
    }
}

fn preserve_hash_token(token: &[u8], replacement: &str) -> Result<Vec<u8>, ReplayDivergence> {
    let mut output = Vec::with_capacity(token.len());
    output.push(b'"');
    let mut at = 1;
    for next in replacement.bytes() {
        match token.get(at) {
            Some(b'\\') if token.get(at + 1) == Some(&b'u') => {
                if at + 6 > token.len() {
                    return Err(owner_divergence("rebind/hash_escape"));
                }
                output.extend_from_slice(format!("\\u{:04x}", next).as_bytes());
                at += 6;
            }
            Some(_) => {
                output.push(next);
                at += 1;
            }
            None => return Err(owner_divergence("rebind/hash_length")),
        }
    }
    if token.get(at) != Some(&b'"') || at + 1 != token.len() {
        return Err(owner_divergence("rebind/hash_length"));
    }
    output.push(b'"');
    Ok(output)
}

#[cfg(test)]
mod correspondence_tests {
    use super::*;
    fn binding() -> super::super::replay_identity::ResponseBindingV1 {
        super::super::replay_identity::ResponseBindingV1 {
            task_digest: "a".repeat(64),
            scope_digest: "b".repeat(64),
            run_digest: "c".repeat(64),
            consultation_digest: "d".repeat(64),
            state_snapshot_digest: "e".repeat(64),
            validation_manifest_digest: "f".repeat(64),
            request_digest: "1".repeat(64),
            validation_ordinal: 0,
        }
    }
    fn bindings() -> ReplayCorrespondenceV1 {
        let mut graph = ReplayCorrespondenceV1::new();
        let binding = binding();
        graph.coordinates.insert(
            TranscriptCoordinates {
                consultation: 0,
                validation: 0,
                transport: 0,
            },
            ReplayTrafficBinding {
                old_request: "1".repeat(64),
                live_request: "6".repeat(64),
                old_consultation: binding.consultation_digest.clone(),
                live_consultation: "3".repeat(64),
                state_revision: 0,
            },
        );
        for (kind, old, new) in [
            (ReplayWireIdentity::Run, &binding.run_digest, '2'),
            (
                ReplayWireIdentity::Consultation,
                &binding.consultation_digest,
                '3',
            ),
            (
                ReplayWireIdentity::StateSnapshot,
                &binding.state_snapshot_digest,
                '4',
            ),
            (
                ReplayWireIdentity::ValidationManifest,
                &binding.validation_manifest_digest,
                '5',
            ),
            (
                ReplayWireIdentity::PushRequest,
                &binding.request_digest,
                '6',
            ),
        ] {
            graph
                .bind_wire(kind, old, &new.to_string().repeat(64))
                .unwrap();
        }
        graph
            .push_bindings
            .insert(binding.request_digest.clone(), binding);
        graph
    }
    fn coordinates() -> TranscriptCoordinates {
        TranscriptCoordinates {
            consultation: 0,
            validation: 0,
            transport: 0,
        }
    }
    #[test]
    fn tool_traffic_requires_its_checked_coordinate_call_name_and_revision() {
        let mut graph = bindings();
        let c = coordinates();
        let error=serde_json::to_vec(&json!({"tool":"unknown_tool","state_revision":0,"error":{"code":"unknown_tool","message":"exact"}})).unwrap();
        assert!(graph.compare_tool_response(c, 0, &error, &error).is_err());
        assert!(graph.audit.comparisons.is_empty());
        let bad = TranscriptCoordinates { transport: 1, ..c };
        assert!(
            graph
                .compare_tool_call(bad, 0, "unknown_tool", b"{bad", b"{bad")
                .is_err()
        );
        graph
            .compare_tool_call(c, 0, "unknown_tool", b"{bad", b"{bad")
            .unwrap();
        assert!(
            graph
                .compare_tool_call(c, 0, "unknown_tool", b"{bad", b"{bad")
                .is_err()
        );
        let changed=serde_json::to_vec(&json!({"tool":"unknown_tool","state_revision":1,"error":{"code":"unknown_tool","message":"exact"}})).unwrap();
        assert!(
            graph
                .compare_tool_response(c, 0, &changed, &changed)
                .is_err()
        );
        assert_eq!(graph.audit.comparisons.len(), 1);
        graph.compare_tool_response(c, 0, &error, &error).unwrap();
        assert_eq!(graph.audit.comparisons.len(), 2);
        assert!(graph.compare_tool_response(c, 0, &error, &error).is_err());
    }
    #[test]
    fn raw_semantic_secret_never_creates_a_comparison_digest() {
        let mut graph = bindings();
        let c = coordinates();
        let secret = b"{\"key\":\"sk-sensitive-token\"}";
        assert!(
            graph
                .compare_tool_call(c, 0, "unknown_tool", secret, secret)
                .is_err()
        );
        assert!(graph.audit.comparisons.is_empty());
        let chunks = [
            ReplayResponseChunk {
                bytes: secret[..10].to_vec(),
                accounting: super::super::ResponseChunkAccounting {
                    accepted: true,
                    maximum_bytes: None,
                    observed_bytes: 10,
                    retained_bytes: 10,
                },
            },
            ReplayResponseChunk {
                bytes: secret[10..].to_vec(),
                accounting: super::super::ResponseChunkAccounting {
                    accepted: true,
                    maximum_bytes: None,
                    observed_bytes: secret.len(),
                    retained_bytes: secret.len(),
                },
            },
        ];
        assert!(
            graph
                .compare_response_chunks(c, &"1".repeat(64), &"6".repeat(64), &chunks, &chunks)
                .is_err()
        );
        assert!(graph.audit.comparisons.is_empty());
        assert!(!graph.wire.contains_key(&ReplayWireIdentity::Response));
    }
    #[test]
    fn comparison_log_requires_owner_bound_headers_and_keeps_them_fixed() {
        let mut graph = bindings();
        assert!(graph.comparison_log().is_err());
        let pins = super::super::TranscriptPins {
            task_digest: "a".repeat(64),
            source_digest: "b".repeat(64),
            scope_digest: "c".repeat(64),
            policy_digest: "d".repeat(64),
            runner_digest: "e".repeat(64),
            worker_digest: "f".repeat(64),
            lean_digest: "1".repeat(64),
            vampire_digest: "2".repeat(64),
            profile_digest: "3".repeat(64),
        };
        let old = TranscriptHeader::new("offline".into(), "4".repeat(64), pins.clone());
        let live = TranscriptHeader::new("offline".into(), "5".repeat(64), pins);
        assert!(graph.bind_headers(&old, &live).is_err());
        graph.run_pair = Some(ReplayRunPair {
            old_run: old.source_run_identity.clone(),
            live_run: live.source_run_identity.clone(),
            task: old.pins.task_digest.clone(),
            source: old.pins.source_digest.clone(),
            scope: old.pins.scope_digest.clone(),
            request_policy: old.pins.policy_digest.clone(),
            feedback_policy: "6".repeat(64),
        });
        let mut wrong = old.clone();
        wrong.pins.source_digest = "7".repeat(64);
        let mut wrong_live = live.clone();
        wrong_live.pins.source_digest = "7".repeat(64);
        assert!(graph.bind_headers(&wrong, &wrong_live).is_err());
        assert!(graph.comparison_log().is_err());
        graph.bind_headers(&old, &live).unwrap();
        let before = graph.comparison_log().unwrap().clone();
        let mut changed = live.clone();
        changed.pins.runner_digest = "8".repeat(64);
        assert!(graph.bind_headers(&old, &changed).is_err());
        assert_eq!(graph.comparison_log().unwrap(), &before);
    }
    #[test]
    fn unsupported_counterexample_input_retains_every_raw_byte_outside_valid_binding() {
        let graph = bindings();
        for input in [
            "null",
            "{\"relations\":false}",
            "{\"relations\":[{\"name\":\"R\",\"rows\":[[1]]}]}",
            "{\"relations\":[],\"unknown\":{\"deep\":[false,null,3]}}",
        ] {
            let raw = format!(
                " {{ \"kind\" : \"candidate_counterexample\", \"schema_version\":4, \"binding\":{}, \"input\" : {input} }} ",
                serde_json::to_string(&binding()).unwrap()
            );
            let plan = graph.response_rebinding(raw.as_bytes());
            assert!(plan.parsed);
            assert_eq!(plan.replacements.len(), 5);
            let rebound =
                String::from_utf8(graph.rebind_response_bytes(raw.as_bytes()).unwrap()).unwrap();
            assert!(rebound.ends_with(&format!("\"input\" : {input} }} ")));
            assert!(rebound.starts_with(" { \"kind\" :"));
            let mut wrong: Value = serde_json::from_str(&raw).unwrap();
            wrong["binding"]["task_digest"] = json!("0".repeat(64));
            let wrong = serde_json::to_vec(&wrong).unwrap();
            assert!(!graph.response_rebinding(&wrong).parsed);
            assert_eq!(graph.rebind_response_bytes(&wrong).unwrap(), wrong);
        }
    }
    /// A counterexample the envelope admitted with the clause variant's two
    /// members left empty rebinds like any other counterexample; one carrying
    /// clause content the envelope refused stays exact, unparsed bytes.
    #[test]
    fn an_empty_clause_member_beside_a_counterexample_rebinds_like_a_plain_one() {
        let graph = bindings();
        let response = |members: &str| {
            format!(
                "{{\"kind\":\"candidate_counterexample\",\"schema_version\":4,\"binding\":{}{members},\"input\":{{\"relations\":[]}}}}",
                serde_json::to_string(&binding()).unwrap()
            )
        };
        let plain = graph.response_rebinding(response("").as_bytes());
        assert!(plain.parsed);
        for members in [
            ",\"clauses\":[]",
            ",\"dropped\":[]",
            ",\"clauses\":[],\"dropped\":[]",
        ] {
            let raw = response(members);
            let plan = graph.response_rebinding(raw.as_bytes());
            assert!(plan.parsed);
            assert_eq!(plan.replacements.len(), plain.replacements.len());
            let rebound =
                String::from_utf8(graph.rebind_response_bytes(raw.as_bytes()).unwrap()).unwrap();
            assert!(rebound.contains(members.trim_start_matches(',')));
        }
        let carried = response(",\"clauses\":[\"formula\"]");
        assert!(!graph.response_rebinding(carried.as_bytes()).parsed);
        assert_eq!(
            graph.rebind_response_bytes(carried.as_bytes()).unwrap(),
            carried.as_bytes()
        );
    }

    #[test]
    fn unknown_outer_duplicate_and_malformed_negative_envelopes_remain_exact() {
        let graph = bindings();
        for raw in [b"{malformed".to_vec(),format!("{{\"kind\":\"candidate_counterexample\",\"schema_version\":4,\"binding\":{},\"input\":null,\"extra\":true}}",serde_json::to_string(&binding()).unwrap()).into_bytes(),b"{\"kind\":1,\"kind\":2}".to_vec()]{assert!(!graph.response_rebinding(&raw).parsed);assert_eq!(graph.rebind_response_bytes(&raw).unwrap(),raw);}
    }
    #[test]
    fn rebinding_preserves_escaped_hash_width_and_other_scalars() {
        use super::super::replay_wire_compare::{ReplayWireRebinding, ReplayWireReplacement};
        let old = "a".repeat(64);
        let live = "b".repeat(64);
        let raw = format!(
            "{{ \"x\":\"{}\", \"untouched\" : [ 3.00, \"a\" ] }}",
            "\\u0061".repeat(64)
        );
        let plan = ReplayWireRebinding {
            parsed: true,
            replacements: vec![ReplayWireReplacement::Identity {
                path: "/x".into(),
                identity: ReplayWireIdentity::Run,
                old,
                live,
            }],
        };
        let rebound = apply_rebinding(raw.as_bytes(), &plan).unwrap();
        assert_eq!(raw.len(), rebound.len());
        assert_eq!(
            String::from_utf8(rebound).unwrap(),
            raw.replace("\\u0061", "\\u0062")
        );
    }
    #[test]
    fn response_chunks_rederive_ordinary_and_oversized_digests_and_refuse_boundary_changes() {
        let mut graph = bindings();
        let chunks = vec![
            ReplayResponseChunk {
                bytes: b"1234".to_vec(),
                accounting: super::super::ResponseChunkAccounting {
                    accepted: true,
                    maximum_bytes: Some(5),
                    observed_bytes: 4,
                    retained_bytes: 4,
                },
            },
            ReplayResponseChunk {
                bytes: b"5678".to_vec(),
                accounting: super::super::ResponseChunkAccounting {
                    accepted: false,
                    maximum_bytes: Some(5),
                    observed_bytes: 8,
                    retained_bytes: 5,
                },
            },
        ];
        graph
            .compare_response_chunks(
                TranscriptCoordinates {
                    consultation: 0,
                    validation: 0,
                    transport: 0,
                },
                &"1".repeat(64),
                &"6".repeat(64),
                &chunks,
                &chunks,
            )
            .unwrap();
        assert_eq!(
            graph
                .map_identity(ReplayWireIdentity::Response, &exact_bytes_sha256(b"12345"))
                .unwrap(),
            exact_bytes_sha256(b"12345")
        );
        let mut wrong = chunks.clone();
        wrong[0].accounting.retained_bytes = 3;
        assert!(
            graph
                .compare_response_chunks(
                    TranscriptCoordinates {
                        consultation: 0,
                        validation: 0,
                        transport: 0
                    },
                    &"1".repeat(64),
                    &"6".repeat(64),
                    &chunks,
                    &wrong
                )
                .is_err()
        );
        let mut wrong = chunks.clone();
        wrong[0].bytes.push(b'5');
        wrong[1].bytes.remove(0);
        assert!(
            graph
                .compare_response_chunks(
                    TranscriptCoordinates {
                        consultation: 0,
                        validation: 0,
                        transport: 0
                    },
                    &"1".repeat(64),
                    &"6".repeat(64),
                    &chunks,
                    &wrong
                )
                .is_err()
        );
    }
    #[test]
    fn latest_identity_has_closed_nested_negative_inventory() {
        for value in [
            json!({"kind":"postcondition_open","outcome":"refuted","attempt":3}),
            json!({"kind":"postcondition_open","outcome":"inconclusive","reason":"timed_out"}),
        ] {
            let parsed: ReplayLatestIdentity = decode_owner(&value).unwrap();
            assert_eq!(json!(parsed), value);
            let mut unknown = value;
            unknown["extra"] = json!(true);
            assert!(decode_owner::<ReplayLatestIdentity>(&unknown).is_err());
        }
    }
}

impl<'de> Deserialize<'de> for ReplayLatestIdentity {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        use super::replay_identity::{PostconditionOpenV1, PresenceV1};
        #[derive(Deserialize)]
        #[serde(rename_all = "snake_case")]
        enum Outcome {
            Refuted,
            Inconclusive,
        }
        #[derive(Deserialize)]
        #[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
        enum Wire {
            Initial {},
            PostconditionOpen {
                outcome: Outcome,
                #[serde(default)]
                attempt: PresenceV1<PhysicalAttemptId>,
                #[serde(default)]
                reason: PresenceV1<super::replay_identity::InconclusiveReasonV1>,
            },
            Failure {
                origin: super::replay_identity::FailureOriginV1,
                failure_kind: super::replay_identity::FailureKindV1,
                retryable: bool,
                scope: super::replay_identity::FailureScopeV1,
                #[serde(deserialize_with = "nullable")]
                detail_digest: Option<ReplaySha256>,
                artifacts: Vec<ReplayLatestArtifact>,
            },
            CounterexampleRejected {
                code: String,
                reason: String,
            },
        }
        match Wire::deserialize(d)? {
            Wire::Initial {} => Ok(Self::Initial {}),
            Wire::PostconditionOpen {
                outcome: Outcome::Refuted,
                attempt,
                reason: PresenceV1::Absent,
            } => {
                let attempt = match attempt {
                    PresenceV1::Null => None,
                    PresenceV1::Value(v) => Some(v),
                    PresenceV1::Absent => {
                        return Err(serde::de::Error::custom("missing required attempt"));
                    }
                };
                Ok(Self::PostconditionOpen {
                    outcome: PostconditionOpenV1::Refuted { attempt },
                })
            }
            Wire::PostconditionOpen {
                outcome: Outcome::Inconclusive,
                attempt: PresenceV1::Absent,
                reason: PresenceV1::Value(reason),
            } => Ok(Self::PostconditionOpen {
                outcome: PostconditionOpenV1::Inconclusive { reason },
            }),
            Wire::PostconditionOpen { .. } => Err(serde::de::Error::custom(
                "inconsistent postcondition outcome fields",
            )),
            Wire::Failure {
                origin,
                failure_kind,
                retryable,
                scope,
                detail_digest,
                artifacts,
            } => Ok(Self::Failure {
                origin,
                failure_kind,
                retryable,
                scope,
                detail_digest,
                artifacts,
            }),
            Wire::CounterexampleRejected { code, reason } => {
                Ok(Self::CounterexampleRejected { code, reason })
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(super) enum ReplayPageCategory {
    Clauses,
    Ledger,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ReplayCursorProjection {
    pub category: ReplayPageCategory,
    pub offset: usize,
    pub token_digest: ReplaySha256,
    pub source_consultation_digest: ReplaySha256,
    pub state_snapshot_digest: ReplaySha256,
}

fn audit_digest(value: String) -> Result<ReplayAuditDigest, ReplayDivergence> {
    ReplayAuditDigest::new(value)
}
impl ReplayCorrespondenceV1 {
    fn bind_run_pair(
        &mut self,
        old: &ReplayPushProjection,
        live: &ReplayPushProjection,
    ) -> Result<(), ReplayDivergence> {
        let scope = &old.feedback.state.catalog.scope;
        let pair = ReplayRunPair {
            old_run: old.feedback.state.catalog.instance_digest.0.clone(),
            live_run: live.feedback.state.catalog.instance_digest.0.clone(),
            task: canonical_value_sha256(&json!(scope.task)),
            source: scope.task.source_sha256.0.clone(),
            scope: scope.digest.0.clone(),
            request_policy: old.request_policy_digest.0.clone(),
            feedback_policy: old.feedback.policy_digest.0.clone(),
        };
        if let Some(existing) = &self.run_pair
            && existing != &pair
        {
            return Err(owner_divergence("run/changed_owner_or_policy"));
        }
        self.run_pair = Some(pair);
        Ok(())
    }
    fn require_coordinates(
        &self,
        coordinates: TranscriptCoordinates,
    ) -> Result<(), ReplayDivergence> {
        if !self.finalized && self.coordinates.contains_key(&coordinates) {
            Ok(())
        } else {
            Err(owner_divergence("traffic/coordinates_without_checked_push"))
        }
    }
    /// Bind compatible pinned headers to the task, policy and fresh catalog
    /// owners already verified at the first actual traffic point.
    pub fn bind_headers(
        &mut self,
        old: &TranscriptHeader,
        live: &TranscriptHeader,
    ) -> Result<(), ReplayDivergence> {
        for header in [old, live] {
            replay_safe_bytes(
                &serde_json::to_vec(header)
                    .map_err(|_| owner_divergence("headers/serialization"))?,
            )?;
        }
        let pair = compare_headers(old, live)?;
        let run = self
            .run_pair
            .as_ref()
            .ok_or_else(|| owner_divergence("headers/missing_actual_owner"))?;
        for (header, identity) in [(old, &run.old_run), (live, &run.live_run)] {
            same(&header.source_run_identity, identity, "headers/owner_run")?;
            for (actual, expected, path) in [
                (&header.pins.task_digest, &run.task, "task"),
                (&header.pins.source_digest, &run.source, "source"),
                (&header.pins.scope_digest, &run.scope, "scope"),
                (&header.pins.policy_digest, &run.request_policy, "policy"),
            ] {
                same(actual, expected, &format!("headers/owner_{path}"))?;
            }
        }
        if let Some(previous) = &self.audit.headers {
            same(previous, &pair, "headers/rebinding")?;
        }
        self.audit.headers = Some(pair);
        Ok(())
    }
    /// Return inert comparison evidence only after actual owners and compatible
    /// pinned headers have both been checked. No mapping can be imported here.
    pub fn comparison_log(&self) -> Result<&ReplayComparisonLogV2, ReplayDivergence> {
        if self.audit.headers.is_none() {
            return Err(owner_divergence("audit/missing_checked_headers"));
        }
        self.audit.validate()?;
        Ok(&self.audit)
    }
    pub fn comparison_log_bytes(&self, maximum_bytes: usize) -> Result<Vec<u8>, ReplayDivergence> {
        let log = self.comparison_log()?;
        super::transcript::encoded_size(log, maximum_bytes)
            .map_err(|_| owner_divergence("audit/byte_limit"))?;
        serde_json::to_vec(log).map_err(|_| owner_divergence("audit/serialization"))
    }
    fn append_new_pairs(
        &mut self,
        before: &Self,
        old_input: &ReplayAuditDigest,
        live_input: &ReplayAuditDigest,
    ) -> Result<(), ReplayDivergence> {
        let mut pairs = Vec::new();
        let mut add = |identity, constructor| {
            pairs.push(ReplayIdentityPair {
                identity,
                derivation: ReplayDerivation {
                    constructor,
                    old_owner_projection_sha256: old_input.clone(),
                    live_owner_projection_sha256: live_input.clone(),
                },
            })
        };
        for (old, live) in &self.catalogs.forward {
            if !before.catalogs.forward.contains_key(old) {
                add(
                    ReplayIdentityPairValue::Catalog {
                        old: audit_digest(old.clone())?,
                        live: audit_digest(live.clone())?,
                    },
                    ReplayDerivationConstructor::CatalogSnapshot {},
                );
            }
        }
        for (old, live) in &self.records.forward {
            if !before.records.forward.contains_key(old) {
                add(
                    ReplayIdentityPairValue::ClauseRecord {
                        old: audit_digest(old.clone())?,
                        live: audit_digest(live.clone())?,
                    },
                    ReplayDerivationConstructor::ClauseRecord {},
                );
            }
        }
        for (old, live) in &self.partitions.forward {
            if !before.partitions.forward.contains_key(old) {
                add(
                    ReplayIdentityPairValue::Partition {
                        old: audit_digest(old.clone())?,
                        live: audit_digest(live.clone())?,
                    },
                    ReplayDerivationConstructor::PartitionSnapshot {},
                );
            }
        }
        for (old, live) in &self.physical_attempts.forward {
            if !before.physical_attempts.forward.contains_key(old) {
                add(
                    ReplayIdentityPairValue::PhysicalAttempt {
                        old: old.0,
                        live: live.0,
                    },
                    ReplayDerivationConstructor::PhysicalAttemptLink {},
                );
            }
        }
        for ((old_backend, old_local), (live_backend, live_local)) in &self.artifacts.forward {
            if !before
                .artifacts
                .forward
                .contains_key(&(old_backend.clone(), *old_local))
            {
                add(
                    ReplayIdentityPairValue::Artifact {
                        old_backend: old_backend.clone(),
                        old_local: *old_local,
                        live_backend: live_backend.clone(),
                        live_local: *live_local,
                    },
                    ReplayDerivationConstructor::ArtifactAllocation {},
                );
            }
        }
        for (kind, mapping) in &self.host {
            for (old, live) in &mapping.forward {
                if !before
                    .host
                    .get(kind)
                    .is_some_and(|m| m.forward.contains_key(old))
                {
                    add(
                        ReplayIdentityPairValue::Host {
                            category: *kind,
                            old: audit_digest(old.clone())?,
                            live: audit_digest(live.clone())?,
                        },
                        ReplayDerivationConstructor::HostOwner { category: *kind },
                    );
                }
            }
        }
        for (kind, mapping) in &self.production {
            let category = audit_production_kind(*kind);
            for (old, live) in &mapping.forward {
                if !before
                    .production
                    .get(kind)
                    .is_some_and(|map| map.forward.contains_key(old))
                {
                    add(
                        ReplayIdentityPairValue::Production {
                            category,
                            old: old.clone(),
                            live: live.clone(),
                        },
                        ReplayDerivationConstructor::ProductionOwner { category },
                    );
                }
            }
        }
        for (kind, mapping) in &self.wire {
            for (old, live) in &mapping.forward {
                if !before
                    .wire
                    .get(kind)
                    .is_some_and(|map| map.forward.contains_key(old))
                {
                    add(
                        ReplayIdentityPairValue::Wire {
                            category: *kind,
                            old: old.clone(),
                            live: live.clone(),
                        },
                        ReplayDerivationConstructor::WireOwner { category: *kind },
                    );
                }
            }
        }
        self.audit.identity_pairs.extend(pairs);
        Ok(())
    }
}
fn audit_production_kind(kind: ReplayProductionIdentity) -> ReplayAuditProductionIdentity {
    use ReplayAuditProductionIdentity as A;
    use ReplayProductionIdentity as P;
    match kind {
        P::Catalog => A::Catalog,
        P::Partition => A::Partition,
        P::CheckRequest => A::CheckRequest,
        P::Backend => A::Backend,
        P::ArtifactBackendDigest => A::ArtifactBackendDigest,
        P::ContextAllocation => A::ContextAllocation,
        P::PreparedBody => A::PreparedBody,
        P::SupportBlock => A::SupportBlock,
        P::Entailment => A::Entailment,
        P::Preparation => A::Preparation,
        P::Job => A::Job,
        P::Terminal => A::Terminal,
        P::ProductionReceipt => A::ProductionReceipt,
        P::SemanticReuse => A::SemanticReuse,
        P::EvidenceIdentity => A::EvidenceIdentity,
        P::RouteDisplay => A::RouteDisplay,
    }
}
impl ReplayCorrespondenceV1 {
    pub fn compare_tool_call(
        &mut self,
        coordinates: TranscriptCoordinates,
        call_id: u64,
        name: &str,
        recorded: &[u8],
        live: &[u8],
    ) -> Result<(), ReplayDivergence> {
        replay_safe_bytes(recorded)?;
        replay_safe_bytes(live)?;
        replay_safe_bytes(name.as_bytes())?;
        self.require_coordinates(coordinates)?;
        if self.tool_calls.contains_key(&(coordinates, call_id)) {
            return Err(owner_divergence("tool_call/duplicate"));
        }
        same(
            &self.rebind_tool_argument_bytes(name, recorded)?,
            &live.to_vec(),
            "tool_call/exact_rebound_arguments",
        )?;
        self.audit
            .comparisons
            .push(ReplayComparisonRecord::ToolCall {
                coordinates,
                call_id,
                name: name.into(),
                old_bytes_sha256: audit_digest(exact_bytes_sha256(recorded))?,
                live_bytes_sha256: audit_digest(exact_bytes_sha256(live))?,
            });
        self.tool_calls.insert((coordinates, call_id), name.into());
        Ok(())
    }
}
fn tool_response_stamp(value: &super::replay_identity::ToolResponseV1) -> (String, u64) {
    use super::replay_identity::ToolResponseV1 as R;
    match value {
        R::Error(e) => (e.tool.clone(), e.state_revision),
        R::Countermodel(e) => ("countermodel".into(), e.state_revision),
        R::StrongestRefutations(e) => ("strongest_refutations".into(), e.state_revision),
        R::History(e) => ("history".into(), e.state_revision),
        R::Ledger(e) => ("ledger".into(), e.state_revision),
        R::ValidateClauses(e) => ("validate_clauses".into(), e.state_revision),
        R::EvaluateClauses(e) => ("evaluate_clauses".into(), e.state_revision),
    }
}

fn owner_timing_observations(
    old: &ReplayStateProjection,
    live: &ReplayStateProjection,
) -> Vec<ReplayOwnerTiming> {
    let mut observed = Vec::new();
    let mut add =
        |owner: ReplayTimingOwner, a: &ReplayEvidenceProjection, b: &ReplayEvidenceProjection| {
            for (slot, old_ns, live_ns) in [
                (
                    ReplayOwnerTimingSlot::Solver,
                    &a.timing.solver_time_ns,
                    &b.timing.solver_time_ns,
                ),
                (
                    ReplayOwnerTimingSlot::Preparation,
                    &a.timing.preparation_time_ns,
                    &b.timing.preparation_time_ns,
                ),
            ] {
                observed.push(ReplayOwnerTiming {
                    owner: owner.clone(),
                    slot,
                    old_ns: old_ns.clone(),
                    live_ns: live_ns.clone(),
                });
            }
        };
    for (a, b) in old.ledger.iter().zip(&live.ledger) {
        if let (
            ReplayLedgerRowProjection::Attempt {
                row_ordinal,
                outcome: a,
                ..
            },
            ReplayLedgerRowProjection::Attempt { outcome: b, .. },
        ) = (a, b)
        {
            add(
                ReplayTimingOwner::Ledger {
                    row_ordinal: row_ordinal.0,
                },
                a.evidence(),
                b.evidence(),
            );
        }
    }
    for (a, b) in old.terminations.iter().zip(&live.terminations) {
        if let (
            ReplayTerminationResult::Applied { outcome: a_result },
            ReplayTerminationResult::Applied { outcome: b_result },
        ) = (&a.result, &b.result)
        {
            add(
                ReplayTimingOwner::Termination {
                    check_ordinal: a.ordinal,
                },
                a_result.evidence(),
                b_result.evidence(),
            );
        }
    }
    observed
}

fn replay_safe_bytes(bytes: &[u8]) -> Result<(), ReplayDivergence> {
    if super::Redaction::changes(bytes) {
        Err(owner_divergence("traffic/semantic_redaction"))
    } else {
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub(super) enum ReplayFinalOutcome {
    Valid {
        core_digest: ReplaySha256,
        request_digest: ReplaySha256,
        evidence_identity: ReplaySha256,
    },
    Invalid {
        instance: super::replay_identity::ProgramInstanceV1,
        instance_digest: ReplaySha256,
        fuel_consumed: u64,
    },
    Failure {
        failure: ReplayPrivateFailure,
    },
}
impl ReplayFinalOutcome {
    pub(super) fn valid(
        proof: &super::FrameworkIITerminationProof,
    ) -> Result<Self, ReplayCaptureError> {
        Ok(Self::Valid {
            core_digest: decode_owner(&json!(proof.core_digest()))?,
            request_digest: decode_owner(&json!(proof.request_digest()))?,
            evidence_identity: decode_owner(&json!(proof.evidence_identity()))?,
        })
    }
    pub(super) fn invalid(
        record: &super::FrozenCounterexampleRecord,
    ) -> Result<Self, ReplayCaptureError> {
        checked_projection(Self::Invalid {
            instance: decode_owner(record.instance())?,
            instance_digest: decode_owner(&json!(record.instance_identity()))?,
            fuel_consumed: record.fuel_consumed(),
        })
    }
    pub(super) fn failure(
        report: &crate::failure::FailureReport,
    ) -> Result<Self, ReplayCaptureError> {
        Ok(Self::Failure {
            failure: private_failure_projection(report)?,
        })
    }
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReplayFinalStateProjection {
    version: ReplayVersion<2>,
    state: ReplayStateProjection,
    backend: ReplayBackendIdentity,
    #[serde(deserialize_with = "nullable")]
    run_configuration: Option<ReplayRunConfiguration>,
    feedback_policy: ReplayPolicyFields,
    feedback_policy_digest: ReplaySha256,
    request_policy: ReplayRequestPolicyFields,
    request_policy_digest: ReplaySha256,
    outcome: ReplayFinalOutcome,
}
#[derive(Clone)]
pub struct ReplayFinalStateOwner {
    projection: ReplayFinalStateProjection,
    state: ReplayStateOwner,
}
impl ReplayFinalStateOwner {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn capture(
        state: ReplayStateOwner,
        backend: ReplayBackendIdentity,
        run_configuration: Option<ReplayRunConfiguration>,
        feedback_policy: ReplayPolicyFields,
        feedback_policy_digest: ReplaySha256,
        request_policy: &super::AgentConsultationPolicy,
        outcome: ReplayFinalOutcome,
    ) -> Result<Self, ReplayCaptureError> {
        let projection = checked_projection(ReplayFinalStateProjection {
            version: ReplayVersion,
            state: state.projection.clone(),
            backend,
            run_configuration,
            feedback_policy,
            feedback_policy_digest,
            request_policy: ReplayRequestPolicyFields::capture(request_policy),
            request_policy_digest: decode_owner(&json!(request_policy.digest()))?,
            outcome,
        })?;
        let owner = Self { projection, state };
        owner.verify_recorded(&owner.projection)?;
        Ok(owner)
    }
    pub fn projection(&self) -> &ReplayFinalStateProjection {
        &self.projection
    }
    fn verify_recorded(&self, p: &ReplayFinalStateProjection) -> Result<(), ReplayCaptureError> {
        self.state.verify_recorded(&p.state)?;
        p.request_policy.verify(&p.request_policy_digest)?;
        p.feedback_policy.verify(&p.feedback_policy_digest)?;
        if let Some(configuration) = &p.run_configuration {
            configuration.verify()?;
        }
        match &p.outcome {
            ReplayFinalOutcome::Valid {
                core_digest,
                request_digest,
                evidence_identity,
            } => {
                invariant(core_digest == &p.state.core_digest)?;
                let last = p
                    .state
                    .terminations
                    .last()
                    .ok_or(ReplayCaptureError::OwnerInvariant)?;
                match &last.result {
                    ReplayTerminationResult::Applied { outcome } => match outcome.as_ref() {
                        ReplayOutcomeProjection::Proved { evidence } => invariant(
                            &evidence.request_digest == request_digest
                                && &evidence.identity == evidence_identity
                                && last.core == p.state.core,
                        )?,
                        _ => return Err(ReplayCaptureError::OwnerInvariant),
                    },
                    _ => return Err(ReplayCaptureError::OwnerInvariant),
                }
            }
            ReplayFinalOutcome::Invalid {
                instance,
                instance_digest,
                ..
            } => invariant(canonical_value_sha256(&json!(instance)) == instance_digest.0)?,
            ReplayFinalOutcome::Failure { .. } => {}
        }
        Ok(())
    }
}
impl ReplayCorrespondenceV1 {
    pub fn compare_final_state(
        &mut self,
        recorded: &ReplayFinalStateProjection,
        live: &ReplayFinalStateOwner,
    ) -> Result<(), ReplayDivergence> {
        if self.finalized {
            return Err(owner_divergence("final_state/duplicate"));
        }
        live.verify_recorded(recorded)
            .map_err(|_| owner_divergence("final_state/recorded_owner"))?;
        live.verify_recorded(&live.projection)
            .map_err(|_| owner_divergence("final_state/live_owner"))?;
        let current = &live.projection;
        let scope = &recorded.state.catalog.scope;
        let run = ReplayRunPair {
            old_run: recorded.state.catalog.instance_digest.0.clone(),
            live_run: current.state.catalog.instance_digest.0.clone(),
            task: canonical_value_sha256(&json!(scope.task)),
            source: scope.task.source_sha256.0.clone(),
            scope: scope.digest.0.clone(),
            request_policy: recorded.request_policy_digest.0.clone(),
            feedback_policy: recorded.feedback_policy_digest.0.clone(),
        };
        if self
            .run_pair
            .as_ref()
            .is_some_and(|expected| expected != &run)
        {
            return Err(owner_divergence("final_state/run"));
        }
        same(
            &recorded.request_policy,
            &current.request_policy,
            "final_state/request_policy",
        )?;
        same(
            &recorded.feedback_policy,
            &current.feedback_policy,
            "final_state/feedback_policy",
        )?;
        same(
            &recorded.run_configuration,
            &current.run_configuration,
            "final_state/run_configuration",
        )?;
        let mut candidate = self.clone();
        candidate.run_pair = Some(run);
        candidate.bind_identity(
            ReplayProductionIdentity::Backend,
            recorded.backend.as_str(),
            current.backend.as_str(),
            "final_state/backend",
        )?;
        candidate.compare_state(&recorded.state, &current.state)?;
        match (&recorded.outcome, &current.outcome) {
            (
                ReplayFinalOutcome::Valid {
                    core_digest: a,
                    request_digest: ar,
                    evidence_identity: ae,
                },
                ReplayFinalOutcome::Valid {
                    core_digest: b,
                    request_digest: br,
                    evidence_identity: be,
                },
            ) => {
                same(a, b, "final_state/core")?;
                candidate.require_identity(
                    ReplayProductionIdentity::CheckRequest,
                    &ar.0,
                    &br.0,
                    "final_state/termination_request",
                )?;
                candidate.require_identity(
                    ReplayProductionIdentity::EvidenceIdentity,
                    &ae.0,
                    &be.0,
                    "final_state/termination_evidence",
                )?;
            }
            (
                ReplayFinalOutcome::Failure { failure: a },
                ReplayFinalOutcome::Failure { failure: b },
            ) => candidate.compare_failure(a, b, "final_state/failure")?,
            _ => same(&recorded.outcome, &current.outcome, "final_state/outcome")?,
        }
        let old_owner = audit_digest(canonical_value_sha256(&json!(recorded)))?;
        let live_owner = audit_digest(canonical_value_sha256(&json!(current)))?;
        candidate.append_new_pairs(self, &old_owner, &live_owner)?;
        candidate
            .audit
            .comparisons
            .push(ReplayComparisonRecord::FinalState {
                old_owner_projection_sha256: old_owner,
                live_owner_projection_sha256: live_owner,
                semantic_core_digest: audit_digest(recorded.state.core_digest.0.clone())?,
                old_ledger_chain_digest: audit_digest(canonical_value_sha256(&json!(
                    recorded.state.ledger
                )))?,
                live_ledger_chain_digest: audit_digest(canonical_value_sha256(&json!(
                    current.state.ledger
                )))?,
                owner_timing: owner_timing_observations(&recorded.state, &current.state),
            });
        candidate.finalized = true;
        *self = candidate;
        Ok(())
    }
}
