//! Immutable fixed-ambient partitions and Lean-request handles.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::sync::Arc;

use serde_json::{Value, json};

use crate::encoding::canonical_value_sha256;
use crate::houdini::ClauseId;

use super::catalog::{
    FrameworkIIStateError, LeveledClauseCatalog, LeveledClauseRecord, task_identity_fields,
};
use super::types::{FixedAmbientTaskScope, FrameworkIILevel};

// ------------------------------------------------------------
// Immutable Candidate Partitions
// ------------------------------------------------------------

/// One complete immutable candidate partition for an exact check.
#[derive(Clone)]
pub struct LeveledCandidateSnapshot {
    scope: FixedAmbientTaskScope,
    /// The run's optional level bound. Absent by default: the scan's halting
    /// rule, not a bound, is what ends a stabilization scan.
    max_level: Option<FrameworkIILevel>,
    catalog_instance_digest: Arc<str>,
    records: Arc<BTreeMap<ClauseId, LeveledClauseRecord>>,
    level_of: Arc<BTreeMap<ClauseId, FrameworkIILevel>>,
    canonical_order: Arc<[ClauseId]>,
    greatest_occupied_level: Option<FrameworkIILevel>,
    partition_digest: Arc<str>,
}

impl LeveledCandidateSnapshot {
    pub(crate) fn build(
        catalog: &LeveledClauseCatalog,
        max_level: Option<FrameworkIILevel>,
        level_of: BTreeMap<ClauseId, FrameworkIILevel>,
    ) -> Result<Self, FrameworkIIStateError> {
        if max_level.is_some_and(|bound| bound < FrameworkIILevel::ONE) {
            return Err(FrameworkIIStateError::InvalidPlacement(
                "a fixed-ambient level bound must be at least one",
            ));
        }
        let mut records = BTreeMap::new();
        for (id, level) in &level_of {
            if max_level.is_some_and(|bound| *level > bound) {
                return Err(FrameworkIIStateError::InvalidPlacement(
                    "a clause exceeds the run's level bound",
                ));
            }
            let record = catalog.record(*id)?;
            if *level < record.minimum_level() {
                return Err(FrameworkIIStateError::InvalidPlacement(
                    "a clause is below its Lean-owned minimum level",
                ));
            }
            records.insert(*id, record);
        }

        // Canonical order is (level, registration order, id). The controller
        // applies the contract's fresh-first check order on top of this,
        // which is why the tie-break here stays exactly as Lean issued it.
        let mut canonical_order = level_of.keys().copied().collect::<Vec<_>>();
        canonical_order.sort_by(|left, right| {
            let left_record = records
                .get(left)
                .expect("every placed clause has an immutable record");
            let right_record = records
                .get(right)
                .expect("every placed clause has an immutable record");
            (level_of[left], left_record.registration_order_key(), *left).cmp(&(
                level_of[right],
                right_record.registration_order_key(),
                *right,
            ))
        });
        // BTreeMap value order is ClauseId order, not level order.
        let greatest_occupied_level = level_of.values().copied().max();
        let partition_digest = partition_digest(
            catalog,
            max_level,
            &records,
            &level_of,
            &canonical_order,
            greatest_occupied_level,
        );
        Ok(Self {
            scope: catalog.scope().clone(),
            max_level,
            catalog_instance_digest: Arc::from(catalog.instance_digest()),
            records: Arc::new(records),
            level_of: Arc::new(level_of),
            canonical_order: canonical_order.into(),
            greatest_occupied_level,
            partition_digest,
        })
    }

    pub fn scope(&self) -> &FixedAmbientTaskScope {
        &self.scope
    }

    /// The run's optional level bound, absent unless a host set one.
    pub fn max_level(&self) -> Option<FrameworkIILevel> {
        self.max_level
    }

    pub fn catalog_instance_digest(&self) -> &str {
        &self.catalog_instance_digest
    }

    pub fn records(&self) -> &BTreeMap<ClauseId, LeveledClauseRecord> {
        &self.records
    }

    pub fn members(&self) -> BTreeSet<ClauseId> {
        self.records.keys().copied().collect()
    }

    pub fn contains(&self, clause: ClauseId) -> bool {
        self.records.contains_key(&clause)
    }

    pub fn level_of(&self, clause: ClauseId) -> Option<FrameworkIILevel> {
        self.level_of.get(&clause).copied()
    }

    pub fn canonical_order(&self) -> &[ClauseId] {
        &self.canonical_order
    }

    pub fn greatest_occupied_level(&self) -> Option<FrameworkIILevel> {
        self.greatest_occupied_level
    }

    pub fn partition_digest(&self) -> &str {
        &self.partition_digest
    }

    pub fn same_partition(&self, other: &Self) -> bool {
        // The digest is only a quick rejection key.  Exact root reuse compares
        // every immutable logical field retained by the snapshots.
        self.partition_digest == other.partition_digest
            && self.scope == other.scope
            && self.max_level == other.max_level
            && self.catalog_instance_digest == other.catalog_instance_digest
            && self.records == other.records
            && self.level_of == other.level_of
            && self.canonical_order == other.canonical_order
            && self.greatest_occupied_level == other.greatest_occupied_level
    }

    /// Materialize rows accepted by the fixed-ambient Lean worker.
    pub(crate) fn worker_payload(&self) -> Value {
        json!({"rows": self.worker_rows()})
    }

    /// Return the exact V5 snapshot identity reconstructed by Lean.
    pub(crate) fn worker_identity(&self) -> Value {
        json!({
            "kind": "whiel_fixed_ambient_snapshot",
            "version": 1,
            "rows": self.worker_rows(),
        })
    }

    fn worker_rows(&self) -> Vec<Value> {
        self.canonical_order
            .iter()
            .map(|clause| {
                let record = &self.records[clause];
                let level = self.level_of[clause];
                json!({
                    "canonical_source": record.formula().canonical_source(),
                    "clause_id": clause.get(),
                    "identity": record.formula().identity(),
                    "level": level.get(),
                })
            })
            .collect::<Vec<_>>()
    }

    #[cfg(test)]
    pub(super) fn set_partition_digest_for_collision_test(&mut self, digest: Arc<str>) {
        self.partition_digest = digest;
    }
}

impl fmt::Debug for LeveledCandidateSnapshot {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("LeveledCandidateSnapshot")
            .field("scope", &self.scope)
            .field("max_level", &self.max_level)
            .field("catalog_instance_digest", &self.catalog_instance_digest)
            .field("members", &self.canonical_order)
            .field("partition_digest", &self.partition_digest)
            .finish_non_exhaustive()
    }
}

/// Exact immutable handle for one stabilized fixed-ambient core.
#[derive(Clone, Debug)]
pub struct LeveledCoreHandle {
    snapshot: Arc<LeveledCandidateSnapshot>,
    identity: Arc<Value>,
    core_digest: Arc<str>,
}

impl LeveledCoreHandle {
    pub fn build(snapshot: Arc<LeveledCandidateSnapshot>) -> Result<Self, FrameworkIIStateError> {
        let identity = json!({
            "kind": "whiel_framework_ii_fixed_ambient_core",
            "version": 1,
            "scope_identity": snapshot.scope().identity(),
            "snapshot_identity": snapshot.worker_identity(),
        });
        let core_digest: Arc<str> = Arc::from(canonical_value_sha256(&identity));
        Ok(Self {
            snapshot,
            identity: Arc::new(identity),
            core_digest,
        })
    }

    pub fn snapshot(&self) -> &Arc<LeveledCandidateSnapshot> {
        &self.snapshot
    }

    /// Complete fixed-ambient core identity retained across handoff/resume.
    pub fn identity(&self) -> &Value {
        &self.identity
    }

    pub fn core_digest(&self) -> &str {
        &self.core_digest
    }
}

fn partition_digest(
    catalog: &LeveledClauseCatalog,
    max_level: Option<FrameworkIILevel>,
    records: &BTreeMap<ClauseId, LeveledClauseRecord>,
    level_of: &BTreeMap<ClauseId, FrameworkIILevel>,
    canonical_order: &[ClauseId],
    greatest_occupied_level: Option<FrameworkIILevel>,
) -> Arc<str> {
    let payload = json!({
        "domain": "whiel-framework-ii-fixed-ambient-partition-v1",
        "task": task_identity_fields(catalog.scope()),
        "scope": catalog.scope().identity(),
        "catalog_instance_digest": catalog.instance_digest(),
        "max_level": max_level.map(FrameworkIILevel::get),
        "records": records
            .iter()
            .map(|(id, record)| {
                json!({
                    "id": id.get(),
                    "record_digest": record.record_digest(),
                    "level": level_of[id].get(),
                })
            })
            .collect::<Vec<_>>(),
        "canonical_order": canonical_order
            .iter()
            .map(|clause| clause.get())
            .collect::<Vec<_>>(),
        "greatest_occupied_level": greatest_occupied_level.map(FrameworkIILevel::get),
    });
    Arc::from(canonical_value_sha256(&payload))
}
