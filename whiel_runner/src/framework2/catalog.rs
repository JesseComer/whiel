//! Deterministic, classification-free fixed-ambient clause catalog.

use std::collections::{BTreeMap, HashMap};
use std::fmt;
use std::sync::{Arc, Mutex, MutexGuard};

use serde_json::json;

use crate::encoding::canonical_value_sha256;
use crate::houdini::ClauseId;

use super::components::FrameworkIIClauseComponents;
use super::ledger::FrameworkIIDeadReason;
use super::types::{ExtendedClause, FixedAmbientTaskScope, FrameworkIILevel};

// ------------------------------------------------------------
// Immutable Clause Records
// ------------------------------------------------------------

/// Audited origin of one fixed-ambient clause.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ExtendedClauseOrigin {
    /// Clause text supplied by an external consultation.
    Submitted,
    /// Clause produced by the later Symbolic-Houdini frontend.
    Symbolic,
    /// Protected EDB-only top-level precondition conjunct issued by Lean.
    EdbPreconditionSystem {
        conjunct_ordinal: u64,
        route_digest: Arc<str>,
    },
}

impl ExtendedClauseOrigin {
    pub fn edb_precondition_system(
        conjunct_ordinal: u64,
        route_digest: impl Into<Arc<str>>,
    ) -> Result<Self, FrameworkIIStateError> {
        let route_digest = route_digest.into();
        if !is_sha256(&route_digest) {
            return Err(FrameworkIIStateError::InvalidSystemRouteDigest);
        }
        Ok(Self::EdbPreconditionSystem {
            conjunct_ordinal,
            route_digest,
        })
    }

    pub fn is_protected(&self) -> bool {
        matches!(self, Self::EdbPreconditionSystem { .. })
    }

    fn registration_rank(&self) -> u8 {
        match self {
            Self::EdbPreconditionSystem { .. } => 0,
            Self::Submitted => 1,
            Self::Symbolic => 2,
        }
    }

    fn identity_fields(&self) -> serde_json::Value {
        match self {
            Self::Submitted => json!({"kind": "submitted"}),
            Self::Symbolic => json!({"kind": "symbolic"}),
            Self::EdbPreconditionSystem {
                conjunct_ordinal,
                route_digest,
            } => json!({
                "kind": "edb_precondition_system",
                "conjunct_ordinal": conjunct_ordinal,
                "route_digest": route_digest.as_ref(),
            }),
        }
    }
}

/// One immutable entry in a fixed-ambient clause catalog.
#[derive(Clone)]
pub struct LeveledClauseRecord {
    id: ClauseId,
    formula: ExtendedClause,
    origin: ExtendedClauseOrigin,
    minimum_level: FrameworkIILevel,
    protected: bool,
    record_digest: Arc<str>,
}

impl PartialEq for LeveledClauseRecord {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
            && self.formula.semantic_metadata_matches(&other.formula)
            && self.origin == other.origin
            && self.minimum_level == other.minimum_level
            && self.protected == other.protected
            && self.record_digest == other.record_digest
    }
}

impl Eq for LeveledClauseRecord {}

impl LeveledClauseRecord {
    pub fn id(&self) -> ClauseId {
        self.id
    }

    pub fn formula(&self) -> &ExtendedClause {
        &self.formula
    }

    /// Return the immutable Lean component authority admitted with the clause.
    pub fn components(&self) -> &FrameworkIIClauseComponents {
        self.formula.components()
    }

    pub fn origin(&self) -> &ExtendedClauseOrigin {
        &self.origin
    }

    pub fn minimum_level(&self) -> FrameworkIILevel {
        self.minimum_level
    }

    /// Whether the admitted formula mentions a prophecy relation. See
    /// [`ExtendedClause::mentions_prophecy_relation`].
    pub fn mentions_prophecy_relation(&self) -> bool {
        self.formula.mentions_prophecy_relation()
    }

    /// Whether Houdini may never drop this Lean-issued system row.
    pub fn is_protected(&self) -> bool {
        self.protected
    }

    pub fn record_digest(&self) -> &str {
        &self.record_digest
    }

    pub(super) fn registration_order_key(&self) -> &str {
        self.formula.registration_order_key()
    }

    pub(super) fn identity_intern_key(&self) -> &str {
        self.formula.identity_intern_key()
    }
}

impl fmt::Debug for LeveledClauseRecord {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("LeveledClauseRecord")
            .field("id", &self.id.get())
            .field("formula", &self.formula)
            .field("origin", &self.origin)
            .field("minimum_level", &self.minimum_level)
            .field("protected", &self.protected)
            .field("record_digest", &self.record_digest)
            .finish()
    }
}

// ------------------------------------------------------------
// Serialized Catalog Registration
// ------------------------------------------------------------

#[derive(Clone)]
pub struct LeveledClauseCatalog {
    inner: Arc<CatalogInner>,
}

struct CatalogInner {
    instance_digest: Arc<str>,
    scope: FixedAmbientTaskScope,
    data: Mutex<CatalogData>,
}

#[derive(Default)]
struct CatalogData {
    by_formula: HashMap<Arc<str>, ClauseId>,
    records: Vec<LeveledClauseRecord>,
    record_limit: Option<usize>,
    next_batch_ordinal: u64,
    reserved_system: Vec<ClauseId>,
    system_reservation_closed: bool,
}

/// Result of one atomic, canonically ordered registration batch.
#[derive(Clone)]
pub struct RegisteredLeveledClauses {
    catalog: LeveledClauseCatalog,
    ids: Arc<[ClauseId]>,
    newly_allocated: Arc<[ClauseId]>,
    records: Arc<[LeveledClauseRecord]>,
}

impl RegisteredLeveledClauses {
    pub fn ids(&self) -> &[ClauseId] {
        &self.ids
    }

    pub fn newly_allocated(&self) -> &[ClauseId] {
        &self.newly_allocated
    }

    pub(super) fn records(&self) -> &[LeveledClauseRecord] {
        &self.records
    }

    pub(super) fn belongs_to(&self, catalog: &LeveledClauseCatalog) -> bool {
        self.catalog == *catalog
    }
}

impl fmt::Debug for RegisteredLeveledClauses {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("RegisteredLeveledClauses")
            .field("catalog_instance_digest", &self.catalog.instance_digest())
            .field("ids", &self.ids)
            .field("newly_allocated", &self.newly_allocated)
            .finish()
    }
}

impl PartialEq for RegisteredLeveledClauses {
    fn eq(&self, other: &Self) -> bool {
        self.catalog == other.catalog
            && self.ids == other.ids
            && self.newly_allocated == other.newly_allocated
            && self.records == other.records
    }
}

impl Eq for RegisteredLeveledClauses {}

impl LeveledClauseCatalog {
    /// Construct the catalog for one durable run identity.
    ///
    /// The supplied digest must be stable across process restart.  Pointer
    /// identity remains available through `Eq`, but never enters a durable
    /// record or snapshot digest.
    pub fn new(
        scope: FixedAmbientTaskScope,
        instance_digest: impl Into<Arc<str>>,
    ) -> Result<Self, FrameworkIIStateError> {
        let instance_digest = instance_digest.into();
        if !is_sha256(&instance_digest) {
            return Err(FrameworkIIStateError::InvalidCatalogInstanceDigest);
        }
        Ok(Self {
            inner: Arc::new(CatalogInner {
                instance_digest,
                scope,
                data: Mutex::new(CatalogData::default()),
            }),
        })
    }

    pub fn instance_digest(&self) -> &str {
        &self.inner.instance_digest
    }

    pub fn scope(&self) -> &FixedAmbientTaskScope {
        &self.inner.scope
    }

    pub fn len(&self) -> Result<usize, FrameworkIIStateError> {
        Ok(self.lock_data()?.records.len())
    }

    /// The protected precondition rows Lean reserved, in catalog order. A
    /// Core rebuilt from recorded rows places them at level zero itself:
    /// they are never among the recorded rows, since the input installs them.
    pub fn reserved_system_ids(&self) -> Result<Vec<ClauseId>, FrameworkIIStateError> {
        Ok(self.lock_data()?.reserved_system.clone())
    }

    pub fn is_empty(&self) -> Result<bool, FrameworkIIStateError> {
        Ok(self.len()? == 0)
    }

    pub fn next_batch_ordinal(&self) -> Result<u64, FrameworkIIStateError> {
        Ok(self.lock_data()?.next_batch_ordinal)
    }

    /// Whether the Lean-issued protected system rows have been reserved.
    pub fn system_origins_reserved(&self) -> Result<bool, FrameworkIIStateError> {
        Ok(self.lock_data()?.system_reservation_closed)
    }

    /// Reserve every Lean-issued protected EDB-precondition row before any
    /// external registration.
    ///
    /// Protected records are interned immediately in source-conjunct order and
    /// receive the lowest catalog IDs, but they enter no control snapshot
    /// until installation. A later external proposal that repeats one receives
    /// the existing protected ID.
    pub fn reserve_system_clauses(
        &self,
        clauses: impl IntoIterator<Item = (ExtendedClause, ExtendedClauseOrigin)>,
    ) -> Result<RegisteredLeveledClauses, FrameworkIIStateError> {
        let mut pending = BTreeMap::<u64, (Arc<str>, ExtendedClause, ExtendedClauseOrigin)>::new();
        let mut seen = HashMap::<Arc<str>, u64>::new();
        let mut prior_ordinal = None;
        for (formula, origin) in clauses {
            self.require_formula_scope(&formula)?;
            let ExtendedClauseOrigin::EdbPreconditionSystem {
                conjunct_ordinal, ..
            } = &origin
            else {
                return Err(FrameworkIIStateError::NonSystemReservation);
            };
            if formula.minimum_level() != FrameworkIILevel::ZERO {
                return Err(FrameworkIIStateError::PropheticSystemClause);
            }
            // Lean emits rows in strict source order; the catalog enforces it
            // so the earliest-conjunct policy below cannot be subverted.
            if prior_ordinal.is_some_and(|prior| *conjunct_ordinal <= prior) {
                return Err(FrameworkIIStateError::ConflictingSystemOrigins);
            }
            prior_ordinal = Some(*conjunct_ordinal);
            let key: Arc<str> = Arc::from(formula.identity_intern_key());
            if let Some(existing) = seen.get(&key) {
                // Lean emits rows in strict source order; a repeated formula
                // keeps its earliest conjunct.
                let (_, existing_formula, _) = &pending[existing];
                if !existing_formula.semantic_metadata_matches(&formula) {
                    return Err(FrameworkIIStateError::ConflictingFormulaMetadata);
                }
                continue;
            }
            if pending.contains_key(conjunct_ordinal) {
                return Err(FrameworkIIStateError::ConflictingSystemOrigins);
            }
            seen.insert(Arc::clone(&key), *conjunct_ordinal);
            pending.insert(*conjunct_ordinal, (key, formula, origin));
        }
        let ordered = pending.into_values().collect::<Vec<_>>();

        let mut data = self.lock_data()?;
        if !data.records.is_empty() || data.system_reservation_closed {
            return Err(FrameworkIIStateError::SystemReservationAlreadyClosed);
        }
        let registered = self.register_unique_locked(&mut data, ordered)?;
        data.reserved_system = registered.ids().to_vec();
        data.system_reservation_closed = true;
        Ok(registered)
    }

    /// Return the reserved protected rows in canonical installation order.
    pub(super) fn reserved_system_clauses(
        &self,
    ) -> Result<RegisteredLeveledClauses, FrameworkIIStateError> {
        let data = self.lock_data()?;
        let records = data
            .reserved_system
            .iter()
            .map(|id| {
                let index = usize::try_from(id.get())
                    .map_err(|_| FrameworkIIStateError::UnknownClause(id.get()))?;
                data.records
                    .get(index)
                    .cloned()
                    .ok_or(FrameworkIIStateError::UnknownClause(id.get()))
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(RegisteredLeveledClauses {
            catalog: self.clone(),
            ids: data.reserved_system.clone().into(),
            newly_allocated: Arc::from([]),
            records: records.into(),
        })
    }

    /// Capture one complete immutable record table and its publication
    /// ordinal under the catalog lock.
    pub(super) fn record_snapshot(
        &self,
    ) -> Result<(u64, Arc<[LeveledClauseRecord]>), FrameworkIIStateError> {
        let data = self.lock_data()?;
        Ok((data.next_batch_ordinal, data.records.clone().into()))
    }

    /// Check one prospective external batch against the exact current catalog
    /// cap without allocating an ID or publishing any state.
    pub(super) fn preflight_submitted_batch(
        &self,
        clauses: &[ExtendedClause],
    ) -> Result<(), FrameworkIIStateError> {
        let mut unique = BTreeMap::<Arc<str>, ExtendedClause>::new();
        for formula in clauses {
            self.require_formula_scope(formula)?;
            let key: Arc<str> = Arc::from(formula.identity_intern_key());
            if let Some(existing) = unique.get(&key)
                && !existing.semantic_metadata_matches(formula)
            {
                return Err(FrameworkIIStateError::ConflictingFormulaMetadata);
            }
            unique.insert(key, formula.clone());
        }

        let data = self.lock_data()?;
        let mut ordered = unique
            .into_iter()
            .map(|(key, formula)| (key, formula, ExtendedClauseOrigin::Submitted))
            .collect::<Vec<_>>();
        sort_registration_batch(&mut ordered);
        self.validate_unique_locked(&data, &ordered)
    }

    /// Pin the run-wide clause bound before an external consultation can
    /// publish another batch.
    ///
    /// `None` is the default and means no bound: the catalog holds whatever
    /// the run admits. A bound is set only when the run's optional
    /// `catalog_size` host limit is set, and a batch beyond it is refused
    /// with `host_limit`, never as a defect of the proposal.
    pub(super) fn install_record_limit(
        &self,
        limit: Option<usize>,
    ) -> Result<(), FrameworkIIStateError> {
        let Some(limit) = limit else {
            return Ok(());
        };
        let mut data = self.lock_data()?;
        if data.records.len() > limit {
            return Err(FrameworkIIStateError::ClauseLimitExceeded {
                found: data.records.len(),
                limit,
            });
        }
        match data.record_limit {
            Some(existing) if existing != limit => Err(FrameworkIIStateError::InvalidEvidence(
                "the fixed-ambient catalog already has another clause limit",
            )),
            Some(_) => Ok(()),
            None => {
                data.record_limit = Some(limit);
                Ok(())
            }
        }
    }

    /// Intern one complete, authority-ordered batch.
    ///
    /// The caller assigns monotonically increasing ordinals before concurrent
    /// admission work begins.  Completion out of order fails atomically; the
    /// later batch can be retried after every preceding ordinal publishes.
    pub fn register_batch(
        &self,
        batch_ordinal: u64,
        clauses: impl IntoIterator<Item = (ExtendedClause, ExtendedClauseOrigin)>,
    ) -> Result<RegisteredLeveledClauses, FrameworkIIStateError> {
        self.register_batch_transaction(batch_ordinal, clauses, || Ok(()), |_| ())
    }

    /// Register one batch while holding the catalog publication lock through
    /// an infallible owner-state checkpoint. This prevents another catalog
    /// batch from becoming visible between ID allocation and control install.
    pub(super) fn register_batch_transaction(
        &self,
        batch_ordinal: u64,
        clauses: impl IntoIterator<Item = (ExtendedClause, ExtendedClauseOrigin)>,
        authorize: impl FnOnce() -> Result<(), FrameworkIIStateError>,
        publish: impl FnOnce(&RegisteredLeveledClauses),
    ) -> Result<RegisteredLeveledClauses, FrameworkIIStateError> {
        let mut unique = BTreeMap::<Arc<str>, (ExtendedClause, ExtendedClauseOrigin)>::new();
        for (formula, origin) in clauses {
            self.require_formula_scope(&formula)?;
            if origin.is_protected() {
                return Err(FrameworkIIStateError::SystemOriginOutsideReservation);
            }
            let key: Arc<str> = Arc::from(formula.identity_intern_key());
            match unique.get(&key) {
                Some((existing_formula, existing_origin)) => {
                    if !existing_formula.semantic_metadata_matches(&formula) {
                        return Err(FrameworkIIStateError::ConflictingFormulaMetadata);
                    }
                    let selected = preferred_origin(existing_origin, &origin)?;
                    if selected == &origin {
                        unique.insert(key, (formula, origin));
                    }
                }
                None => {
                    unique.insert(key, (formula, origin));
                }
            }
        }

        let mut data = self.lock_data()?;
        if batch_ordinal != data.next_batch_ordinal {
            return Err(FrameworkIIStateError::UnexpectedRegistrationBatch {
                expected: data.next_batch_ordinal,
                found: batch_ordinal,
            });
        }
        let next_batch_ordinal = batch_ordinal
            .checked_add(1)
            .ok_or(FrameworkIIStateError::RegistrationBatchIdentityExhausted)?;
        let mut ordered = unique
            .into_iter()
            .map(|(identity, (formula, origin))| (identity, formula, origin))
            .collect::<Vec<_>>();
        sort_registration_batch(&mut ordered);
        // The authorization check is the fallible linearization gate. Once it
        // succeeds, catalog registration plus the owner checkpoint below are
        // one non-awaiting publication under this lock.
        authorize()?;
        let registered = self.register_unique_locked(&mut data, ordered)?;
        data.next_batch_ordinal = next_batch_ordinal;
        publish(&registered);
        Ok(registered)
    }

    pub fn record(&self, id: ClauseId) -> Result<LeveledClauseRecord, FrameworkIIStateError> {
        let index = usize::try_from(id.get())
            .map_err(|_| FrameworkIIStateError::UnknownClause(id.get()))?;
        self.lock_data()?
            .records
            .get(index)
            .cloned()
            .ok_or(FrameworkIIStateError::UnknownClause(id.get()))
    }

    pub fn find(
        &self,
        formula: &ExtendedClause,
    ) -> Result<Option<ClauseId>, FrameworkIIStateError> {
        if formula.scope() != self.scope() {
            return Ok(None);
        }
        Ok(self
            .lock_data()?
            .by_formula
            .get(formula.identity_intern_key())
            .copied())
    }

    fn register_unique_locked(
        &self,
        data: &mut CatalogData,
        unique: Vec<(Arc<str>, ExtendedClause, ExtendedClauseOrigin)>,
    ) -> Result<RegisteredLeveledClauses, FrameworkIIStateError> {
        // Validate the entire ordered batch before publishing its first row.
        // This keeps registration atomic even when a later item is invalid.
        self.validate_unique_locked(data, &unique)?;

        let mut ids = Vec::with_capacity(unique.len());
        let mut newly_allocated = Vec::new();
        for (key, formula, origin) in unique {
            if let Some(id) = data.by_formula.get(&key).copied() {
                ids.push(id);
                continue;
            }

            let ordinal = u64::try_from(data.records.len())
                .expect("the complete registration batch was capacity-checked");
            let id = ClauseId::from_catalog_ordinal(ordinal);
            let minimum_level = formula.minimum_level();
            let protected = origin.is_protected();
            let record_digest =
                record_digest(self.instance_digest(), id, &formula, &origin, protected);
            let record = LeveledClauseRecord {
                id,
                formula,
                origin,
                minimum_level,
                protected,
                record_digest,
            };
            data.by_formula.insert(Arc::clone(&key), id);
            data.records.push(record);
            ids.push(id);
            newly_allocated.push(id);
        }
        let records = ids
            .iter()
            .map(|id| {
                let index = usize::try_from(id.get())
                    .expect("a newly registered ClauseId fits the catalog index space");
                data.records[index].clone()
            })
            .collect::<Vec<_>>();
        Ok(RegisteredLeveledClauses {
            catalog: self.clone(),
            ids: ids.into(),
            newly_allocated: newly_allocated.into(),
            records: records.into(),
        })
    }

    fn validate_unique_locked(
        &self,
        data: &CatalogData,
        unique: &[(Arc<str>, ExtendedClause, ExtendedClauseOrigin)],
    ) -> Result<(), FrameworkIIStateError> {
        let mut new_count = 0_usize;
        for (key, formula, _origin) in unique {
            if let Some(id) = data.by_formula.get(key).copied() {
                let index = usize::try_from(id.get())
                    .map_err(|_| FrameworkIIStateError::UnknownClause(id.get()))?;
                let record = data
                    .records
                    .get(index)
                    .ok_or(FrameworkIIStateError::UnknownClause(id.get()))?;
                if !record.formula.semantic_metadata_matches(formula) {
                    return Err(FrameworkIIStateError::ConflictingFormulaMetadata);
                }
                continue;
            }
            new_count = new_count
                .checked_add(1)
                .ok_or(FrameworkIIStateError::ClauseIdentityExhausted)?;
        }
        let final_len = data
            .records
            .len()
            .checked_add(new_count)
            .ok_or(FrameworkIIStateError::ClauseIdentityExhausted)?;
        if let Some(limit) = data.record_limit
            && final_len > limit
        {
            return Err(FrameworkIIStateError::ClauseLimitExceeded {
                found: final_len,
                limit,
            });
        }
        u64::try_from(final_len).map_err(|_| FrameworkIIStateError::ClauseIdentityExhausted)?;
        Ok(())
    }

    fn require_formula_scope(&self, formula: &ExtendedClause) -> Result<(), FrameworkIIStateError> {
        if formula.scope() != self.scope() {
            Err(FrameworkIIStateError::WrongScope)
        } else {
            Ok(())
        }
    }

    fn lock_data(&self) -> Result<MutexGuard<'_, CatalogData>, FrameworkIIStateError> {
        self.inner
            .data
            .lock()
            .map_err(|_| FrameworkIIStateError::CatalogPoisoned)
    }
}

impl fmt::Debug for LeveledClauseCatalog {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("LeveledClauseCatalog")
            .field("instance_digest", &self.instance_digest())
            .field("scope", &self.scope())
            .field("record_count", &self.len())
            .finish_non_exhaustive()
    }
}

impl PartialEq for LeveledClauseCatalog {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.inner, &other.inner)
    }
}

impl Eq for LeveledClauseCatalog {}

// ------------------------------------------------------------
// Typed State Errors
// ------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FrameworkIIStateError {
    WrongScope,
    InvalidCatalogInstanceDigest,
    WrongCatalog,
    UnexpectedRegistrationBatch {
        expected: u64,
        found: u64,
    },
    RegistrationBatchIdentityExhausted,
    ConflictingFormulaMetadata,
    ClauseIdentityExhausted,
    ClauseLimitExceeded {
        found: usize,
        limit: usize,
    },
    UnknownClause(u64),
    CatalogPoisoned,
    InvalidPlacement(&'static str),
    InvalidEvidence(&'static str),
    Cancelled,
    CheckerFailure(Arc<str>),
    InvalidSystemRouteDigest,
    NonSystemReservation,
    PropheticSystemClause,
    ConflictingSystemOrigins,
    SystemReservationAlreadyClosed,
    SystemOriginOutsideReservation,
    /// A proposal interned an identity the run has already classified `dead`
    /// (Pass 7.5b): a prophecy-free clause with a Lean-validated finite
    /// refutation of its level-zero initialization. Dead clauses never
    /// revive; a later resubmission is rejected with the original reason.
    DeadClauseRejected {
        clause: ClauseId,
        reason: FrameworkIIDeadReason,
    },
    /// A proposal or registration named a clause whose Lean-owned minimum
    /// level exceeds the run's optional level bound. Such a clause is
    /// rejected at admission rather than placed: Lean assigns the minimum
    /// level and knows no bound, and the controller never places a clause
    /// above one.
    LevelBoundExceeded {
        /// Absent when the rejected clause was never interned, which is the
        /// ordinary case: the bound is checked before registration.
        clause: Option<ClauseId>,
        minimum_level: u64,
        max_level: u64,
    },
    /// `maintenance_support_edges`/`maintenance_coverage_edges` accept only
    /// the empty relation in this pass (Pass 7.5b deliverable 4): the
    /// shared core's construction exposes the interface early, but
    /// consuming a nonempty edge relation requires the deferred symbolic
    /// migration that gives the legacy SymbolicHoudini's maintenance-support
    /// edges a typed home here. Names the rejected field.
    EdgeInputRequiresSymbolicMigration(&'static str),
}

impl fmt::Display for FrameworkIIStateError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::WrongScope => formatter.write_str("fixed-ambient value belongs to another scope"),
            Self::InvalidCatalogInstanceDigest => {
                formatter.write_str("fixed-ambient catalog identity is not lowercase SHA-256")
            }
            Self::WrongCatalog => {
                formatter.write_str("fixed-ambient value belongs to another catalog instance")
            }
            Self::UnexpectedRegistrationBatch { expected, found } => write!(
                formatter,
                "fixed-ambient registration batch {found} arrived before expected batch {expected}"
            ),
            Self::RegistrationBatchIdentityExhausted => {
                formatter.write_str("fixed-ambient registration batch identity space is exhausted")
            }
            Self::ConflictingFormulaMetadata => formatter.write_str(
                "one fixed-ambient identity has conflicting Lean-owned semantic metadata",
            ),
            Self::ClauseIdentityExhausted => {
                formatter.write_str("fixed-ambient clause identity space is exhausted")
            }
            Self::ClauseLimitExceeded { found, limit } => write!(
                formatter,
                "fixed-ambient catalog would contain {found} clauses; limit is {limit}",
            ),
            Self::UnknownClause(id) => write!(formatter, "unknown fixed-ambient clause {id}"),
            Self::CatalogPoisoned => formatter.write_str("fixed-ambient catalog lock was poisoned"),
            Self::InvalidPlacement(detail) => write!(formatter, "invalid placement: {detail}"),
            Self::InvalidEvidence(detail) => write!(formatter, "invalid evidence: {detail}"),
            Self::Cancelled => formatter.write_str("fixed-ambient check was cancelled"),
            Self::CheckerFailure(detail) => {
                write!(formatter, "fixed-ambient checker failed: {detail}")
            }
            Self::InvalidSystemRouteDigest => {
                formatter.write_str("fixed-ambient system route digest is not lowercase SHA-256")
            }
            Self::NonSystemReservation => {
                formatter.write_str("fixed-ambient system reservation received an ordinary origin")
            }
            Self::PropheticSystemClause => {
                formatter.write_str("fixed-ambient system clause is not a level-zero clause")
            }
            Self::ConflictingSystemOrigins => {
                formatter.write_str("fixed-ambient system rows repeat a source conjunct ordinal")
            }
            Self::SystemReservationAlreadyClosed => formatter.write_str(
                "fixed-ambient system reservation must precede every other registration",
            ),
            Self::SystemOriginOutsideReservation => formatter.write_str(
                "fixed-ambient protected origins may enter only through system reservation",
            ),
            Self::DeadClauseRejected { clause, reason } => write!(
                formatter,
                "fixed-ambient clause {clause} is dead and cannot be resubmitted: {reason}",
                clause = clause.get(),
            ),
            Self::LevelBoundExceeded {
                clause,
                minimum_level,
                max_level,
            } => write!(
                formatter,
                "fixed-ambient clause {} has minimum level {minimum_level}, above the run's level bound {max_level}",
                clause.map_or_else(|| "(unregistered)".to_string(), |id| id.get().to_string())
            ),
            Self::EdgeInputRequiresSymbolicMigration(field) => write!(
                formatter,
                "fixed-ambient {field} requires the deferred symbolic-Houdini edge migration"
            ),
        }
    }
}

impl std::error::Error for FrameworkIIStateError {}

fn preferred_origin<'a>(
    left: &'a ExtendedClauseOrigin,
    right: &'a ExtendedClauseOrigin,
) -> Result<&'a ExtendedClauseOrigin, FrameworkIIStateError> {
    Ok(
        if (left.registration_rank(), left) <= (right.registration_rank(), right) {
            left
        } else {
            right
        },
    )
}

fn sort_registration_batch(batch: &mut [(Arc<str>, ExtendedClause, ExtendedClauseOrigin)]) {
    batch.sort_by(|left, right| {
        (left.1.registration_order_key(), left.0.as_ref(), &left.2).cmp(&(
            right.1.registration_order_key(),
            right.0.as_ref(),
            &right.2,
        ))
    });
}

fn record_digest(
    catalog_instance_digest: &str,
    id: ClauseId,
    formula: &ExtendedClause,
    origin: &ExtendedClauseOrigin,
    protected: bool,
) -> Arc<str> {
    let payload = json!({
        "domain": "whiel-framework-ii-fixed-ambient-clause-record-v2",
        "protected": protected,
        "task": task_identity_fields(formula.scope()),
        "scope": formula.scope().identity(),
        "task_components_digest": formula.scope().components().digest(),
        "catalog_instance_digest": catalog_instance_digest,
        "id": id.get(),
        "formula": formula.identity(),
        "canonical_source": formula.canonical_source(),
        "components_digest": formula.components().digest(),
        "formula_order_key": formula.registration_order_key(),
        "relation_keys": formula.relation_keys(),
        "origin": origin.identity_fields(),
        "minimum_level": formula.minimum_level().get(),
    });
    Arc::from(canonical_value_sha256(&payload))
}

pub(super) fn task_identity_fields(scope: &FixedAmbientTaskScope) -> serde_json::Value {
    task_identity_fields_of(scope.task_identity())
}

/// The canonical task identity fields, rendered in exactly one place.
///
/// Three copies of this object used to exist: the snapshot identity's, the
/// replay digest's, and the acceptance envelope's. They must agree member for
/// member — a frozen Core's payload carries this object, and a deferred
/// certification compares the live binding's against it — so a seventh field
/// added to one copy and not the others would report every input as changed
/// while nothing had changed. There is one renderer instead.
pub fn task_identity_fields_of(task: &crate::task::TaskIdentity) -> serde_json::Value {
    json!({
        "canonical_id": task.canonical_id(),
        "module": task.module(),
        "namespace": task.namespace(),
        "source_sha256": task.source_digest().as_str(),
        "semantic_version": task.semantic_version(),
        "encoding_version": task.encoding_version(),
    })
}

fn is_sha256(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}
