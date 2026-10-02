//! The frozen final Core: one immutable, ordered, leveled record.
//!
//! `houdini.tex` Section 2: a run whose termination check is *proved*
//! freezes the Core it was proved on, and certification re-proves all
//! `2N+1` conditions of that frozen record. This module owns the freeze
//! and nothing else.
//!
//! [`FrozenLeveledCore::freeze`] takes a [`LeveledCoreHandle`], the
//! [`FrameworkIITerminationProof`] of *that* Core, and the run's
//! [`SearchProfileProvenance`], and produces an immutable ordered record:
//! the Core's clauses in canonical level order with their Lean-issued
//! identities and canonical sources, the task and scope identities, and one
//! closed profile label per job. It rejects a refutation, an inconclusive
//! or otherwise non-proved termination state, and a proof of a different
//! Core.
//!
//! The record has a canonical payload
//! ([`FrozenLeveledCore::payload`]) with a strict decoder
//! ([`FrozenLeveledCore::from_payload`]). The decoder is the certification
//! path's own re-admission boundary: it is where a payload carrying a
//! finite-validity-library surface, an unknown member, a duplicate row, a
//! row whose level drops below its predecessor's, a missing digested member
//! or freeze digest, or a stale task is refused. It checks levels, not the
//! whole canonical order, because the record carries no registration order
//! key; certification rebuilds the snapshot from the catalog and catches
//! every finer reordering there. Nothing here writes a file; durable
//! publication is Pass 7.5g's.

use std::collections::BTreeSet;
use std::fmt;
use std::sync::Arc;

use serde_json::{Value, json};

use crate::encoding::canonical_value_sha256;

use super::catalog::task_identity_fields;
use super::certificate_profiles::SearchProfileProvenance;
#[cfg(test)]
use super::ledger::FrameworkIICheckOutcome;
use super::ledger::{FrameworkIICheckEvidence, FrameworkIICheckRole};
use super::production::{CascPortfolioPolicy, ProofSearchProfile};
use super::snapshot::LeveledCoreHandle;
use super::types::FixedAmbientTaskScope;

/// The payload tag of one frozen Core record.
pub const FROZEN_CORE_KIND: &str = "whiel_framework_ii_frozen_core";

/// The payload version of one frozen Core record.
///
/// Bumped whenever the payload's members change. A host that decodes an
/// unknown kind or version fails closed rather than guessing.
pub const FROZEN_CORE_VERSION: u64 = 1;

/// Member names a frozen Core payload may never carry, whatever else it
/// holds: the dormant finite-validity library's surface.
///
/// The checked finite-validity library is research code with no place on
/// the certification path (TODO.md, standing implementation guardrails), so
/// a frozen record that names a library catalog, tool, selection,
/// application, use list, augmented job, or fresh-symbol witness is refused
/// outright instead of being decoded and silently ignored. Strict decoding
/// already refuses every unknown member; this list makes the library case
/// its own named refusal so the reason is legible.
const LIBRARY_MEMBER_MARKERS: [&str; 4] = ["library", "augmented", "fresh_symbol", "use_list"];

// ------------------------------------------------------------
// Termination Proof
// ------------------------------------------------------------

/// Proof that one exact Core's termination check was *proved*.
///
/// Constructed only from a proved [`FrameworkIICheckOutcome`] together with
/// the Core it was run on, and carrying that Core's digest, so it cannot
/// authorize the freeze of any other Core. A refutation and an inconclusive
/// outcome are refused here, before any freeze exists.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FrameworkIITerminationProof {
    core_digest: Arc<str>,
    request_digest: Arc<str>,
    evidence_identity: Arc<str>,
}

impl FrameworkIITerminationProof {
    /// Bind the evidence of a *proved* termination check to the Core it was
    /// checked on.
    ///
    /// The only constructor on the live path, and it takes the proved
    /// evidence itself rather than an outcome, so a refutation and an
    /// inconclusive outcome cannot reach it at all: there is no runtime
    /// branch left to get wrong.
    pub(crate) fn proved(core: &LeveledCoreHandle, evidence: &FrameworkIICheckEvidence) -> Self {
        Self {
            core_digest: Arc::from(core.core_digest()),
            request_digest: Arc::from(evidence.request_digest()),
            evidence_identity: Arc::from(evidence.identity()),
        }
    }

    /// The total mapping from one termination outcome to a proof, or to the
    /// refusal that outcome earns.
    ///
    /// Test-only: the live path matches `Proved` structurally and calls
    /// [`Self::proved`]. This pins the other two outcomes' refusals.
    #[cfg(test)]
    pub(crate) fn from_outcome(
        core: &LeveledCoreHandle,
        outcome: &FrameworkIICheckOutcome,
    ) -> Result<Self, CoreFreezeError> {
        match outcome {
            FrameworkIICheckOutcome::Proved(evidence) => Ok(Self::proved(core, evidence)),
            FrameworkIICheckOutcome::Refuted(_) => Err(CoreFreezeError::TerminationRefuted),
            FrameworkIICheckOutcome::Inconclusive { .. } => {
                Err(CoreFreezeError::TerminationNotProved)
            }
        }
    }

    /// The digest of the Core this proof closes, and only that Core.
    pub fn core_digest(&self) -> &str {
        &self.core_digest
    }

    pub fn request_digest(&self) -> &str {
        &self.request_digest
    }

    pub fn evidence_identity(&self) -> &str {
        &self.evidence_identity
    }
}

// ------------------------------------------------------------
// Frozen Rows
// ------------------------------------------------------------

/// One frozen Core clause, with the closed profile label of each of its two
/// conditions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FrozenCoreRow {
    clause_id: u64,
    level: u64,
    identity_sha256: Arc<str>,
    canonical_source: Arc<str>,
    initialization_profile: ProofSearchProfile,
    step_profile: ProofSearchProfile,
}

impl FrozenCoreRow {
    /// The Lean-issued clause identity this row was interned under.
    pub fn clause_id(&self) -> u64 {
        self.clause_id
    }

    /// The level the search committed this clause at. Frozen: nothing
    /// relabels it after the freeze.
    pub fn level(&self) -> u64 {
        self.level
    }

    /// The Lean-issued content digest of the clause's own formula.
    pub fn identity_sha256(&self) -> &str {
        &self.identity_sha256
    }

    /// The clause's canonical Lean source, as re-admitted at certification.
    pub fn canonical_source(&self) -> &str {
        &self.canonical_source
    }

    /// The closed label of this clause's initialization condition.
    pub fn initialization_profile(&self) -> ProofSearchProfile {
        self.initialization_profile
    }

    /// The closed label of this clause's step condition. (The wire roles,
    /// the Lean obligation module, and the ledger still say `maintenance`;
    /// the gate-7 cleanup pass renames them with a worker protocol bump.)
    pub fn step_profile(&self) -> ProofSearchProfile {
        self.step_profile
    }

    fn payload(&self) -> Value {
        json!({
            "clause_id": self.clause_id,
            "level": self.level,
            "identity_sha256": self.identity_sha256.as_ref(),
            "canonical_source": self.canonical_source.as_ref(),
            "initialization_profile": profile_name(self.initialization_profile),
            "step_profile": profile_name(self.step_profile),
        })
    }
}

// ------------------------------------------------------------
// The Frozen Core
// ------------------------------------------------------------

/// One immutable ordered leveled Core, frozen on a proved termination
/// check.
///
/// The rows are in the snapshot's canonical order — `(level, registration
/// order, id)`, exactly as Lean issued it — which is the order the Lean
/// emitter numbers its jobs in, so job ordinal `k` is row `k`'s
/// initialization, ordinal `N + k` is row `k`'s step, and ordinal `2N` is
/// the termination check.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FrozenLeveledCore {
    task_canonical_id: Arc<str>,
    task_namespace: Arc<str>,
    task_identity: Arc<Value>,
    scope_identity: Arc<Value>,
    scope_identity_sha256: Arc<str>,
    core_digest: Arc<str>,
    partition_digest: Arc<str>,
    /// The run's optional level bound, as the frozen snapshot was built
    /// under it. Absent unless a host set one. It is part of the frozen
    /// partition's own identity, so certification rebuilds the snapshot
    /// under exactly this bound and never under a different one.
    max_level: Option<u64>,
    snapshot_identity: Arc<Value>,
    rows: Arc<[FrozenCoreRow]>,
    termination_profile: ProofSearchProfile,
    termination_request_digest: Arc<str>,
    termination_evidence_identity: Arc<str>,
    freeze_digest: Arc<str>,
}

impl FrozenLeveledCore {
    /// Freeze `core` on the strength of `termination`, labelling every job
    /// from `provenance`, under a run whose CASC portfolio policy is
    /// [`CascPortfolioPolicy::Disabled`]. A run that may escalate into the
    /// portfolio names its policy through [`Self::freeze_under`].
    pub fn freeze(
        core: &LeveledCoreHandle,
        scope: &FixedAmbientTaskScope,
        termination: &FrameworkIITerminationProof,
        provenance: &SearchProfileProvenance,
    ) -> Result<Self, CoreFreezeError> {
        Self::freeze_under(
            core,
            scope,
            termination,
            provenance,
            CascPortfolioPolicy::Disabled,
        )
    }

    /// Freeze `core` under an explicit [`CascPortfolioPolicy`].
    ///
    /// Fails closed if the proof does not belong to this exact Core, if a
    /// row is missing its level or record, or if the Core carries a clause
    /// the snapshot does not place.
    ///
    /// It also fails closed —
    /// [`CoreFreezeError::CascProfileWhileCascDisabled`] — on a Core that
    /// carries a `casc_2025` label under a run whose CASC portfolio is
    /// disabled. No launch of such a run can produce that label, so a Core
    /// carrying one contradicts the configuration it was proved under and
    /// nothing downstream can say which of the two is right. Refusing at
    /// the freeze makes that early, explicit, and attributable to the label
    /// rather than to a mismatched job many steps later.
    pub fn freeze_under(
        core: &LeveledCoreHandle,
        scope: &FixedAmbientTaskScope,
        termination: &FrameworkIITerminationProof,
        provenance: &SearchProfileProvenance,
        casc_portfolio: CascPortfolioPolicy,
    ) -> Result<Self, CoreFreezeError> {
        if termination.core_digest() != core.core_digest() {
            return Err(CoreFreezeError::TerminationProofIsForAnotherCore {
                proved: termination.core_digest().to_string(),
                core: core.core_digest().to_string(),
            });
        }
        let snapshot = core.snapshot();
        if snapshot.scope() != scope {
            return Err(CoreFreezeError::TaskIdentityMismatch);
        }
        let mut rows = Vec::with_capacity(snapshot.canonical_order().len());
        for clause in snapshot.canonical_order() {
            let record = snapshot
                .records()
                .get(clause)
                .ok_or(CoreFreezeError::UnplacedClause(clause.get()))?;
            let level = snapshot
                .level_of(*clause)
                .ok_or(CoreFreezeError::UnplacedClause(clause.get()))?;
            let identity = record.formula().identity_sha256();
            rows.push(FrozenCoreRow {
                clause_id: clause.get(),
                level: level.get(),
                identity_sha256: Arc::from(identity),
                canonical_source: Arc::from(record.formula().canonical_source()),
                initialization_profile: provenance
                    .clause_profile(FrameworkIICheckRole::Initialization, identity),
                step_profile: provenance
                    .clause_profile(FrameworkIICheckRole::Maintenance, identity),
            });
        }
        if !casc_portfolio.is_enabled() {
            for row in &rows {
                for (role, profile) in [
                    ("initialization", row.initialization_profile),
                    ("step", row.step_profile),
                ] {
                    if profile == ProofSearchProfile::Casc2025 {
                        return Err(CoreFreezeError::CascProfileWhileCascDisabled {
                            job: role.to_string(),
                            clause_id: Some(row.clause_id),
                        });
                    }
                }
            }
            if provenance.termination_profile() == ProofSearchProfile::Casc2025 {
                return Err(CoreFreezeError::CascProfileWhileCascDisabled {
                    job: "termination".to_string(),
                    clause_id: None,
                });
            }
        }
        Self::assemble(
            Arc::from(scope.task_identity().canonical_id()),
            Arc::from(scope.task_identity().namespace()),
            task_identity_fields(scope),
            snapshot.scope().identity().clone(),
            Arc::from(snapshot.scope().identity_sha256()),
            Arc::from(core.core_digest()),
            Arc::from(snapshot.partition_digest()),
            snapshot
                .max_level()
                .map(super::types::FrameworkIILevel::get),
            core.identity()
                .get("snapshot_identity")
                .cloned()
                .ok_or(CoreFreezeError::MissingSnapshotIdentity)?,
            rows,
            provenance.termination_profile(),
            Arc::from(termination.request_digest()),
            Arc::from(termination.evidence_identity()),
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn assemble(
        task_canonical_id: Arc<str>,
        task_namespace: Arc<str>,
        task_identity: Value,
        scope_identity: Value,
        scope_identity_sha256: Arc<str>,
        core_digest: Arc<str>,
        partition_digest: Arc<str>,
        max_level: Option<u64>,
        snapshot_identity: Value,
        rows: Vec<FrozenCoreRow>,
        termination_profile: ProofSearchProfile,
        termination_request_digest: Arc<str>,
        termination_evidence_identity: Arc<str>,
    ) -> Result<Self, CoreFreezeError> {
        let mut seen_ids = BTreeSet::new();
        let mut seen_identities = BTreeSet::new();
        let mut previous_level: Option<u64> = None;
        for row in &rows {
            if !seen_ids.insert(row.clause_id) {
                return Err(CoreFreezeError::DuplicateRow(row.clause_id));
            }
            if !seen_identities.insert(row.identity_sha256.clone()) {
                return Err(CoreFreezeError::DuplicateRow(row.clause_id));
            }
            if row.canonical_source.is_empty() || row.identity_sha256.len() != 64 {
                return Err(CoreFreezeError::MalformedRow(row.clause_id));
            }
            // Canonical order is `(level, registration order key, id)`, and
            // the record carries no order key, so *levels* are the only part
            // of it a record can be checked against on its own: ids are
            // monotone across registration batches but the order key is not,
            // so two same-level clauses registered in different batches
            // legitimately appear with their ids descending. Certification
            // catches every finer reordering by rebuilding the snapshot from
            // the catalog and comparing its canonical order against the
            // frozen one (`aggregate.rs`, `OrderDrift`).
            if previous_level.is_some_and(|previous| row.level < previous) {
                return Err(CoreFreezeError::RowsOutOfCanonicalOrder);
            }
            previous_level = Some(row.level);
        }
        let mut frozen = Self {
            task_canonical_id,
            task_namespace,
            task_identity: Arc::new(task_identity),
            scope_identity: Arc::new(scope_identity),
            scope_identity_sha256,
            core_digest,
            partition_digest,
            max_level,
            snapshot_identity: Arc::new(snapshot_identity),
            rows: rows.into(),
            termination_profile,
            termination_request_digest,
            termination_evidence_identity,
            freeze_digest: Arc::from(""),
        };
        frozen.freeze_digest = Arc::from(canonical_value_sha256(&frozen.identity_fields()));
        Ok(frozen)
    }

    /// The number of frozen clauses, `N`.
    pub fn core_size(&self) -> usize {
        self.rows.len()
    }

    /// The exact number of conditions certification must re-prove: `2N+1`.
    pub fn condition_count(&self) -> usize {
        self.rows.len() * 2 + 1
    }

    pub fn rows(&self) -> &[FrozenCoreRow] {
        &self.rows
    }

    /// The run's canonical task identity fields, exactly as
    /// `task_identity_fields` renders them for the live scope.
    pub fn task_identity(&self) -> &Value {
        &self.task_identity
    }

    pub fn task_canonical_id(&self) -> &str {
        &self.task_canonical_id
    }

    pub fn task_namespace(&self) -> &str {
        &self.task_namespace
    }

    pub fn scope_identity(&self) -> &Value {
        &self.scope_identity
    }

    pub fn scope_identity_sha256(&self) -> &str {
        &self.scope_identity_sha256
    }

    pub fn core_digest(&self) -> &str {
        &self.core_digest
    }

    pub fn partition_digest(&self) -> &str {
        &self.partition_digest
    }

    /// The run's optional level bound, as the frozen snapshot was built
    /// under it.
    pub fn max_level(&self) -> Option<u64> {
        self.max_level
    }

    /// The V5 snapshot identity Lean reconstructs for this Core, as the
    /// emitted bundle must echo it back.
    pub fn snapshot_identity(&self) -> &Value {
        &self.snapshot_identity
    }

    /// The closed label of the single termination condition.
    pub fn termination_profile(&self) -> ProofSearchProfile {
        self.termination_profile
    }

    pub fn freeze_digest(&self) -> &str {
        &self.freeze_digest
    }

    /// The canonical sources of every frozen clause, in canonical order:
    /// exactly what certification re-admits.
    pub fn canonical_sources(&self) -> Vec<String> {
        self.rows
            .iter()
            .map(|row| row.canonical_source.to_string())
            .collect()
    }

    /// The closed profile label of the job at `role`, for the clause the
    /// job names.
    ///
    /// `role` is the certificate job's own role string, as Lean emits it.
    /// An unrecognized role, or a clause condition naming a clause outside
    /// this frozen record, fails closed: there is no fallback profile.
    pub fn job_profile(
        &self,
        role: &str,
        clause_id: Option<u64>,
    ) -> Result<ProofSearchProfile, CoreFreezeError> {
        if role == "termination" {
            if clause_id.is_some() {
                return Err(CoreFreezeError::TerminationJobNamesAClause);
            }
            return Ok(self.termination_profile);
        }
        let clause_id =
            clause_id.ok_or_else(|| CoreFreezeError::JobHasNoClause(role.to_string()))?;
        let row = self
            .rows
            .iter()
            .find(|row| row.clause_id == clause_id)
            .ok_or(CoreFreezeError::JobNamesAnUnfrozenClause(clause_id))?;
        match role {
            "initialization" => Ok(row.initialization_profile),
            "maintenance" => Ok(row.step_profile),
            other => Err(CoreFreezeError::UnrecognizedRole(other.to_string())),
        }
    }

    /// Every member the freeze digest covers: the whole payload but the
    /// digest itself.
    ///
    /// The scope and snapshot identities are in here rather than beside the
    /// digest: they are what the emitted certificate bundle must echo back,
    /// so a record whose identities were swapped after the freeze must fail
    /// the digest check like any other tampering.
    fn identity_fields(&self) -> Value {
        json!({
            "kind": FROZEN_CORE_KIND,
            "version": FROZEN_CORE_VERSION,
            "task_canonical_id": self.task_canonical_id.as_ref(),
            "task_namespace": self.task_namespace.as_ref(),
            "task_identity": (*self.task_identity).clone(),
            "scope_identity": (*self.scope_identity).clone(),
            "scope_identity_sha256": self.scope_identity_sha256.as_ref(),
            "core_digest": self.core_digest.as_ref(),
            "partition_digest": self.partition_digest.as_ref(),
            "max_level": self.max_level,
            "snapshot_identity": (*self.snapshot_identity).clone(),
            "rows": self.rows.iter().map(FrozenCoreRow::payload).collect::<Vec<_>>(),
            "termination_profile": profile_name(self.termination_profile),
            "termination_request_digest": self.termination_request_digest.as_ref(),
            "termination_evidence_identity": self.termination_evidence_identity.as_ref(),
        })
    }

    /// The canonical payload of this frozen record.
    ///
    /// Everything a certification needs to re-admit the input and clauses
    /// and to label every job, and nothing else: no runtime receipt, no
    /// attempt id, no ledger row, and no library surface. A runtime receipt
    /// may justify the search transition and the operational profile
    /// choice, but never becomes certificate proof, so none rides along
    /// here.
    pub fn payload(&self) -> Value {
        let mut payload = self.identity_fields();
        payload
            .as_object_mut()
            .expect("the frozen Core identity is a JSON object")
            .insert(
                "freeze_digest".to_string(),
                Value::from(self.freeze_digest.as_ref()),
            );
        payload
    }

    /// Recompute and install the freeze digest of a hand-built payload.
    ///
    /// A freeze digest is a content digest, not a secret: anyone holding a
    /// record can recompute it, and its whole job is to refuse a record that
    /// was truncated or edited in transit. This is that computation, named
    /// once, so a fixture that deliberately forges a record stays
    /// digest-consistent and every "missing or disagreeing digest" refusal
    /// is left to the tests that target it.
    #[cfg(feature = "test-hooks")]
    pub fn signed_payload(payload: &Value) -> Value {
        let mut object = payload.as_object().cloned().unwrap_or_default();
        object.remove("freeze_digest");
        let digest = canonical_value_sha256(&Value::Object(object.clone()));
        object.insert("freeze_digest".to_string(), Value::from(digest));
        Value::Object(object)
    }

    /// Decode one frozen Core payload, failing closed.
    ///
    /// Refuses an unknown kind or version, any unknown member (a
    /// library-bearing record among them, by its own named refusal), a
    /// duplicate or out-of-order row, a payload missing any digested member,
    /// and a payload whose recomputed freeze digest is absent or disagrees
    /// with the one it carries. A record with no digest is refused rather
    /// than accepted unchecked: an undigested record is exactly the shape a
    /// truncated or hand-edited one takes.
    pub fn from_payload(payload: &Value) -> Result<Self, CoreFreezeError> {
        let object = payload
            .as_object()
            .ok_or(CoreFreezeError::MalformedPayload("not a JSON object"))?;
        const MEMBERS: [&str; 15] = [
            "kind",
            "version",
            "task_canonical_id",
            "task_namespace",
            "task_identity",
            "scope_identity",
            "scope_identity_sha256",
            "core_digest",
            "partition_digest",
            "max_level",
            "snapshot_identity",
            "rows",
            "termination_profile",
            "termination_request_digest",
            "termination_evidence_identity",
            // `freeze_digest` is handled separately below.
        ];
        for key in object.keys() {
            if LIBRARY_MEMBER_MARKERS
                .iter()
                .any(|marker| key.contains(marker))
            {
                return Err(CoreFreezeError::LibraryBearingRecord(key.clone()));
            }
            if key != "freeze_digest" && !MEMBERS.contains(&key.as_str()) {
                return Err(CoreFreezeError::UnknownMember(key.clone()));
            }
        }
        if object.get("kind").and_then(Value::as_str) != Some(FROZEN_CORE_KIND)
            || object.get("version").and_then(Value::as_u64) != Some(FROZEN_CORE_VERSION)
        {
            return Err(CoreFreezeError::MalformedPayload(
                "retired or unsupported frozen-core kind/version",
            ));
        }
        let text = |key: &str| -> Result<Arc<str>, CoreFreezeError> {
            object
                .get(key)
                .and_then(Value::as_str)
                .map(Arc::from)
                .ok_or(CoreFreezeError::MalformedPayload("missing text member"))
        };
        let rows_value = object
            .get("rows")
            .and_then(Value::as_array)
            .ok_or(CoreFreezeError::MalformedPayload("missing rows"))?;
        let mut rows = Vec::with_capacity(rows_value.len());
        for row in rows_value {
            rows.push(decode_row(row)?);
        }
        let carried_digest = object
            .get("freeze_digest")
            .and_then(Value::as_str)
            .ok_or(CoreFreezeError::MalformedPayload("missing freeze digest"))?;
        let frozen =
            Self::assemble(
                text("task_canonical_id")?,
                text("task_namespace")?,
                object
                    .get("task_identity")
                    .cloned()
                    .ok_or(CoreFreezeError::MalformedPayload("missing task identity"))?,
                object
                    .get("scope_identity")
                    .cloned()
                    .ok_or(CoreFreezeError::MalformedPayload("missing scope identity"))?,
                text("scope_identity_sha256")?,
                text("core_digest")?,
                text("partition_digest")?,
                match object.get("max_level") {
                    None | Some(Value::Null) => None,
                    Some(value) => Some(
                        value
                            .as_u64()
                            .ok_or(CoreFreezeError::MalformedPayload("malformed level bound"))?,
                    ),
                },
                object.get("snapshot_identity").cloned().ok_or(
                    CoreFreezeError::MalformedPayload("missing snapshot identity"),
                )?,
                rows,
                decode_profile(object.get("termination_profile"))?,
                text("termination_request_digest")?,
                text("termination_evidence_identity")?,
            )?;
        if carried_digest != frozen.freeze_digest.as_ref() {
            return Err(CoreFreezeError::FreezeDigestMismatch);
        }
        Ok(frozen)
    }
}

fn decode_row(value: &Value) -> Result<FrozenCoreRow, CoreFreezeError> {
    let object = value
        .as_object()
        .ok_or(CoreFreezeError::MalformedPayload("a row is not an object"))?;
    const ROW_MEMBERS: [&str; 6] = [
        "clause_id",
        "level",
        "identity_sha256",
        "canonical_source",
        "initialization_profile",
        "step_profile",
    ];
    for key in object.keys() {
        if LIBRARY_MEMBER_MARKERS
            .iter()
            .any(|marker| key.contains(marker))
        {
            return Err(CoreFreezeError::LibraryBearingRecord(key.clone()));
        }
        if !ROW_MEMBERS.contains(&key.as_str()) {
            return Err(CoreFreezeError::UnknownMember(key.clone()));
        }
    }
    Ok(FrozenCoreRow {
        clause_id: object
            .get("clause_id")
            .and_then(Value::as_u64)
            .ok_or(CoreFreezeError::MalformedPayload("a row has no clause id"))?,
        level: object
            .get("level")
            .and_then(Value::as_u64)
            .ok_or(CoreFreezeError::MalformedPayload("a row has no level"))?,
        identity_sha256: object
            .get("identity_sha256")
            .and_then(Value::as_str)
            .map(Arc::from)
            .ok_or(CoreFreezeError::MalformedPayload("a row has no identity"))?,
        canonical_source: object
            .get("canonical_source")
            .and_then(Value::as_str)
            .map(Arc::from)
            .ok_or(CoreFreezeError::MalformedPayload("a row has no source"))?,
        initialization_profile: decode_profile(object.get("initialization_profile"))?,
        step_profile: decode_profile(object.get("step_profile"))?,
    })
}

fn decode_profile(value: Option<&Value>) -> Result<ProofSearchProfile, CoreFreezeError> {
    match value.and_then(Value::as_str) {
        Some("direct") => Ok(ProofSearchProfile::Direct),
        Some("casc_2025") => Ok(ProofSearchProfile::Casc2025),
        _ => Err(CoreFreezeError::MalformedPayload("unknown profile label")),
    }
}

pub(crate) fn profile_name(profile: ProofSearchProfile) -> &'static str {
    match profile {
        ProofSearchProfile::Direct => "direct",
        ProofSearchProfile::Casc2025 => "casc_2025",
    }
}

// ------------------------------------------------------------
// Errors
// ------------------------------------------------------------

/// Why a Core could not be frozen, or a frozen record could not be read.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CoreFreezeError {
    /// The epoch's termination check was refuted: no Core is frozen.
    TerminationRefuted,
    /// The epoch's termination check was inconclusive or otherwise not
    /// proved: no Core is frozen.
    TerminationNotProved,
    /// The termination proof closes a different Core than the one offered.
    TerminationProofIsForAnotherCore { proved: String, core: String },
    /// This run already froze its Core. A freeze happens once.
    AlreadyFrozen,
    /// The Core's scope names a different task than the run's.
    TaskIdentityMismatch,
    /// A clause of the Core has no record or no level in its own snapshot.
    UnplacedClause(u64),
    /// One row repeats a clause id or a clause identity.
    DuplicateRow(u64),
    /// One row carries an empty source or a malformed identity.
    MalformedRow(u64),
    /// The rows' levels are not nondecreasing, so the record is not in
    /// canonical order.
    RowsOutOfCanonicalOrder,
    /// The Core's own identity carries no snapshot identity to freeze.
    MissingSnapshotIdentity,
    /// The payload names a finite-validity-library member.
    LibraryBearingRecord(String),
    /// The payload carries a member this record shape does not define.
    UnknownMember(String),
    /// The payload is structurally malformed.
    MalformedPayload(&'static str),
    /// The payload's carried freeze digest disagrees with its content.
    FreezeDigestMismatch,
    /// A certificate job names a role this record does not define.
    UnrecognizedRole(String),
    /// A clause job carries no clause id.
    JobHasNoClause(String),
    /// The termination job names a clause.
    TerminationJobNamesAClause,
    /// A certificate job names a clause outside the frozen Core.
    JobNamesAnUnfrozenClause(u64),
    /// The Core carries a `casc_2025` label under a run whose CASC
    /// portfolio is disabled, so the labelled job could never be certified.
    ///
    /// `job` names the labelled condition (`initialization`, `step`, or
    /// `termination`) and `clause_id` the Core row it belongs to, absent for
    /// the termination job.
    CascProfileWhileCascDisabled { job: String, clause_id: Option<u64> },
}

impl fmt::Display for CoreFreezeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TerminationRefuted => write!(
                formatter,
                "a refuted termination check never freezes a Core"
            ),
            Self::TerminationNotProved => write!(
                formatter,
                "a Core is frozen only on a proved termination check"
            ),
            Self::TerminationProofIsForAnotherCore { proved, core } => write!(
                formatter,
                "the termination proof closes Core {proved} and cannot freeze Core {core}"
            ),
            Self::AlreadyFrozen => write!(formatter, "this run already froze its Core"),
            Self::TaskIdentityMismatch => write!(
                formatter,
                "the Core's scope names a different task than the run"
            ),
            Self::UnplacedClause(clause) => write!(
                formatter,
                "clause {clause} has no record or level in its own Core snapshot"
            ),
            Self::DuplicateRow(clause) => {
                write!(formatter, "the frozen Core repeats clause {clause}")
            }
            Self::MalformedRow(clause) => write!(
                formatter,
                "clause {clause}'s frozen row carries no source or a malformed identity"
            ),
            Self::RowsOutOfCanonicalOrder => write!(
                formatter,
                "the frozen Core's rows are not in canonical level order"
            ),
            Self::MissingSnapshotIdentity => write!(
                formatter,
                "the Core's own identity carries no snapshot identity to freeze"
            ),
            Self::LibraryBearingRecord(member) => write!(
                formatter,
                "a frozen Core record may not carry the finite-validity-library member {member:?}"
            ),
            Self::UnknownMember(member) => write!(
                formatter,
                "a frozen Core record carries the unknown member {member:?}"
            ),
            Self::MalformedPayload(reason) => {
                write!(formatter, "malformed frozen Core record: {reason}")
            }
            Self::FreezeDigestMismatch => write!(
                formatter,
                "a frozen Core record's freeze digest disagrees with its content"
            ),
            Self::UnrecognizedRole(role) => write!(
                formatter,
                "a certificate job carries the unrecognized role {role:?}"
            ),
            Self::JobHasNoClause(role) => write!(
                formatter,
                "a certificate job with role {role:?} carries no clause id"
            ),
            Self::TerminationJobNamesAClause => write!(
                formatter,
                "the termination certificate job may not name a clause"
            ),
            Self::JobNamesAnUnfrozenClause(clause) => write!(
                formatter,
                "a certificate job names clause {clause}, which the frozen Core does not carry"
            ),
            Self::CascProfileWhileCascDisabled { job, clause_id } => match clause_id {
                Some(clause) => write!(
                    formatter,
                    "the {job} condition of clause {clause} is labelled casc_2025, but this run's \
                     CASC portfolio is disabled and no launch of it could have produced that \
                     label; freeze it under a run whose CASC portfolio is enabled, or re-run the \
                     condition under the direct profile"
                ),
                None => write!(
                    formatter,
                    "the {job} condition is labelled casc_2025, but this run's CASC portfolio is \
                     disabled and no launch of it could have produced that label; freeze it \
                     under a run whose CASC portfolio is enabled, or re-run the condition under \
                     the direct profile"
                ),
            },
        }
    }
}

impl std::error::Error for CoreFreezeError {}
