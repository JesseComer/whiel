//! Opaque formula pieces and controller-side obligation assembly (Pass 7.5d).
//!
//! Lean computes every syntactic object once. For each admitted clause it
//! renders the four immutable pieces `clause`, `theta_clause`,
//! `maintenance_wp`, and `collapsed_clause`; for the task it renders the
//! five fixed pieces `precondition`, `guard`, `negated_theta_guard`,
//! `negated_guard`, and `postcondition`; and for one exact constant set it
//! renders one support block. This module caches those rendered bodies for
//! the run, keyed by `(clause identity digest, role)`, by role, and by the
//! sorted constant-key list respectively, and splices them into the axiom
//! list `Whiel/Synthesis/FrameworkII/FixedAmbient/Obligations.lean` builds
//! for a selector.
//!
//! Rust never forms a conjunction and never interprets a formula string: it
//! orders and concatenates opaque bodies, and every formula identity it
//! reports is the Lean-issued `result_formula_identity` admitted with the
//! component. `reports/houdini/houdini.tex` Section 4.4 ("Problem assembly
//! is the controller's", Table 1, Algorithm `Check`) is the contract.

use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

use serde::Deserialize;
use serde_json::{Value, json};

use crate::encoding::{
    FixedAmbientEncodingContext, FixedAmbientPreparedBodyData, FixedAmbientPreparedSupportData,
    FixedAmbientWorkerOperation, MAX_ENCODING_FRAME_BYTES, PreparedBodyRef, SupportBlockRef,
};
use crate::runtime::{CancellationToken, SolverAdmission};
use crate::task::ConstantKey;

use super::components::{FrameworkIIComponentMetadata, FrameworkIIComponentRole};
use super::premise::FrameworkIIPremiseTag;
use super::snapshot::LeveledCandidateSnapshot;
use super::types::{ExtendedClause, FixedAmbientTaskScope};

/// The four clause-scoped pieces, in the order Lean emits them.
pub(super) const CLAUSE_PIECE_ROLES: [FrameworkIIComponentRole; 4] = [
    FrameworkIIComponentRole::Clause,
    FrameworkIIComponentRole::ThetaClause,
    FrameworkIIComponentRole::MaintenanceWp,
    FrameworkIIComponentRole::CollapsedClause,
];

/// The five task-scoped pieces, in the order Lean emits them.
pub(super) const TASK_PIECE_ROLES: [FrameworkIIComponentRole; 5] = [
    FrameworkIIComponentRole::Precondition,
    FrameworkIIComponentRole::Guard,
    FrameworkIIComponentRole::NegatedThetaGuard,
    FrameworkIIComponentRole::NegatedGuard,
    FrameworkIIComponentRole::Postcondition,
];

// ------------------------------------------------------------
// One Cached Piece
// ------------------------------------------------------------

/// One Lean-rendered piece: its opaque TPTP body plus the complete
/// Lean-issued formula identity admitted with the component it renders.
#[derive(Clone, Debug)]
pub(super) struct FrameworkIIPiece {
    role: FrameworkIIComponentRole,
    formula_identity: Arc<Value>,
    body: PreparedBodyRef,
}

impl FrameworkIIPiece {
    pub(super) fn role(&self) -> FrameworkIIComponentRole {
        self.role
    }

    pub(super) fn formula_identity(&self) -> &Value {
        &self.formula_identity
    }

    pub(super) fn body(&self) -> &PreparedBodyRef {
        &self.body
    }
}

// ------------------------------------------------------------
// Run-Scoped Piece Cache
// ------------------------------------------------------------

/// Cache-miss counters for one run's piece cache. Every miss inserts
/// exactly one entry and nothing is ever evicted, so each counter equals
/// the number of distinct keys the run needed.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct FrameworkIIPieceCacheStats {
    /// Distinct `(clause identity digest, role)` pieces rendered by Lean.
    pub clause_piece_misses: u64,
    /// `prepare_clause_pieces` worker round trips (one per request frame
    /// the missing set occupies — normally one).
    pub clause_piece_fetches: u64,
    /// `prepare_task_pieces` worker round trips (at most one per run).
    pub task_piece_fetches: u64,
    /// Distinct constant sets for which a support block was rendered.
    pub support_misses: u64,
    /// `prepare_support_block` worker round trips.
    pub support_fetches: u64,
}

impl FrameworkIIPieceCacheStats {
    /// Every worker round trip the run's piece cache made: the clause,
    /// task and support fetches together.
    ///
    /// This is the real worker traffic of obligation preparation. A
    /// controller's preparation count (`LeveledHoudiniState`'s
    /// `preparations_total`) counts *checks that prepared*, most of which
    /// splice their problem out of this cache without contacting the worker
    /// at all.
    pub fn worker_round_trips(&self) -> u64 {
        self.clause_piece_fetches
            .saturating_add(self.task_piece_fetches)
            .saturating_add(self.support_fetches)
    }
}

#[derive(Default)]
struct PieceCacheState {
    clause_pieces: BTreeMap<(Arc<str>, FrameworkIIComponentRole), FrameworkIIPiece>,
    task_pieces: BTreeMap<FrameworkIIComponentRole, FrameworkIIPiece>,
    support: BTreeMap<Arc<str>, SupportBlockRef>,
    stats: FrameworkIIPieceCacheStats,
}

/// The run-scoped store of Lean-rendered pieces and support blocks.
#[derive(Clone, Default)]
pub(super) struct FrameworkIIPieceCache {
    state: Arc<Mutex<PieceCacheState>>,
    /// Serializes the one task-piece fetch, so concurrent preparations at
    /// the start of a run make exactly one round trip for the five fixed
    /// pieces rather than one each.
    task_fetch: Arc<tokio::sync::Mutex<()>>,
}

impl FrameworkIIPieceCache {
    pub(super) fn stats(&self) -> FrameworkIIPieceCacheStats {
        self.lock().stats
    }

    /// The number of distinct cached keys, for the miss-count invariant.
    pub(super) fn sizes(&self) -> (usize, usize, usize) {
        let state = self.lock();
        (
            state.clause_pieces.len(),
            state.task_pieces.len(),
            state.support.len(),
        )
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, PieceCacheState> {
        self.state
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
    }

    fn cached_task_piece(&self, role: FrameworkIIComponentRole) -> Option<FrameworkIIPiece> {
        self.lock().task_pieces.get(&role).cloned()
    }

    fn cached_clause_piece(
        &self,
        identity_digest: &str,
        role: FrameworkIIComponentRole,
    ) -> Option<FrameworkIIPiece> {
        self.lock()
            .clause_pieces
            .get(&(Arc::from(identity_digest), role))
            .cloned()
    }

    fn cached_support(&self, key: &str) -> Option<SupportBlockRef> {
        self.lock().support.get(key).cloned()
    }

    fn task_pieces_present(&self) -> bool {
        let state = self.lock();
        TASK_PIECE_ROLES
            .iter()
            .all(|role| state.task_pieces.contains_key(role))
    }

    /// Render and cache every task piece unless the run already has them.
    pub(super) async fn ensure_task_pieces(
        &self,
        encoding: &FixedAmbientEncodingContext,
        scope: &FixedAmbientTaskScope,
        admission: &SolverAdmission,
        cancellation: &CancellationToken,
    ) -> Result<(), PieceError> {
        if self.task_pieces_present() {
            return Ok(());
        }
        let _serialized = self.task_fetch.lock().await;
        if self.task_pieces_present() {
            return Ok(());
        }
        let response = encoding
            .execute(
                admission,
                cancellation,
                FixedAmbientWorkerOperation::PrepareTaskPieces,
                json!({}),
            )
            .await
            .map_err(PieceError::Encoding)?;
        let revision = response.name_env_revision;
        let wire: WireTaskPieces = decode(response.payload, "fixed-ambient task pieces")?;
        let expected = scope.components().components().iter().collect::<Vec<_>>();
        let pieces = adopt_pieces(
            encoding,
            wire.pieces,
            &TASK_PIECE_ROLES,
            &expected,
            revision,
        )?;
        let mut state = self.lock();
        state.stats.task_piece_fetches = state.stats.task_piece_fetches.saturating_add(1);
        for piece in pieces {
            state.task_pieces.insert(piece.role(), piece);
        }
        Ok(())
    }

    /// Render and cache every missing piece of `clauses`.
    ///
    /// There is no item cap on `prepare_clause_pieces`, so the missing set
    /// is not cut by count: a fresh solver context over a Core of any size
    /// (a resumed run, or the first termination request of a large Core)
    /// gets every piece it needs, normally in a single round trip counted
    /// in [`FrameworkIIPieceCacheStats::clause_piece_fetches`].
    ///
    /// The one bound is the transport's: a request must fit in one
    /// [`MAX_ENCODING_FRAME_BYTES`] frame. A missing set whose payload
    /// would not fit is therefore split into consecutive requests that do,
    /// rather than being sent as one oversized frame that the worker would
    /// refuse — a very large missing set costs more round trips, never a
    /// failed run.
    pub(super) async fn ensure_clause_pieces(
        &self,
        encoding: &FixedAmbientEncodingContext,
        clauses: &[ExtendedClause],
        admission: &SolverAdmission,
        cancellation: &CancellationToken,
    ) -> Result<(), PieceError> {
        let missing = distinct_clauses(clauses.to_vec())
            .into_iter()
            .filter(|clause| {
                CLAUSE_PIECE_ROLES.iter().any(|role| {
                    self.cached_clause_piece(clause.identity_sha256(), *role)
                        .is_none()
                })
            })
            .collect::<Vec<_>>();
        for batch in clause_request_batches(&missing) {
            self.fetch_clause_pieces(encoding, batch, admission, cancellation)
                .await?;
        }
        Ok(())
    }

    /// One `prepare_clause_pieces` round trip over every missing clause.
    async fn fetch_clause_pieces(
        &self,
        encoding: &FixedAmbientEncodingContext,
        missing: &[ExtendedClause],
        admission: &SolverAdmission,
        cancellation: &CancellationToken,
    ) -> Result<(), PieceError> {
        if missing.is_empty() {
            return Ok(());
        }
        let payload = json!({
            "clauses": missing
                .iter()
                .map(|clause| json!({
                    "canonical_source": clause.canonical_source(),
                    "identity": clause.identity(),
                }))
                .collect::<Vec<_>>(),
        });
        let response = encoding
            .execute(
                admission,
                cancellation,
                FixedAmbientWorkerOperation::PrepareClausePieces,
                payload,
            )
            .await
            .map_err(PieceError::Encoding)?;
        let revision = response.name_env_revision;
        let wire: WireClausePieces = decode(response.payload, "fixed-ambient clause pieces")?;
        if wire.clauses.len() != missing.len() {
            return Err(PieceError::Invalid(
                "fixed-ambient clause-piece response changed its clause count",
            ));
        }
        let mut adopted = Vec::with_capacity(missing.len() * CLAUSE_PIECE_ROLES.len());
        for (row, clause) in wire.clauses.into_iter().zip(missing) {
            if &row.identity != clause.identity()
                || row.canonical_source != clause.canonical_source()
            {
                return Err(PieceError::Invalid(
                    "fixed-ambient clause-piece response named another clause",
                ));
            }
            let expected = clause.components().components().iter().collect::<Vec<_>>();
            let pieces = adopt_pieces(
                encoding,
                row.pieces,
                &CLAUSE_PIECE_ROLES,
                &expected,
                revision,
            )?;
            let digest: Arc<str> = Arc::from(clause.identity_sha256());
            for piece in pieces {
                adopted.push(((Arc::clone(&digest), piece.role()), piece));
            }
        }
        let mut state = self.lock();
        state.stats.clause_piece_fetches = state.stats.clause_piece_fetches.saturating_add(1);
        for (key, piece) in adopted {
            if state.clause_pieces.insert(key, piece).is_none() {
                state.stats.clause_piece_misses = state.stats.clause_piece_misses.saturating_add(1);
            }
        }
        Ok(())
    }

    /// Render and cache the support block of one exact constant set.
    pub(super) async fn support_block(
        &self,
        encoding: &FixedAmbientEncodingContext,
        constants: &[ConstantKey],
        admission: &SolverAdmission,
        cancellation: &CancellationToken,
    ) -> Result<SupportBlockRef, PieceError> {
        let key = support_cache_key(constants);
        if let Some(cached) = self.cached_support(&key) {
            return Ok(cached);
        }
        let response = encoding
            .execute(
                admission,
                cancellation,
                FixedAmbientWorkerOperation::PrepareSupportBlock,
                json!({
                    "constant_keys": constants
                        .iter()
                        .map(ConstantKey::as_str)
                        .collect::<Vec<_>>(),
                }),
            )
            .await
            .map_err(PieceError::Encoding)?;
        let revision = response.name_env_revision;
        let wire: FixedAmbientPreparedSupportData =
            decode(response.payload, "fixed-ambient support block")?;
        let support = encoding
            .adopt_support(wire, revision)
            .map_err(PieceError::Encoding)?;
        if support.constant_keys() != constants {
            return Err(PieceError::Invalid(
                "fixed-ambient support block covers another constant set",
            ));
        }
        let mut state = self.lock();
        state.stats.support_fetches = state.stats.support_fetches.saturating_add(1);
        if let Some(existing) = state.support.get(key.as_str()) {
            return Ok(existing.clone());
        }
        state.stats.support_misses = state.stats.support_misses.saturating_add(1);
        state.support.insert(Arc::from(key), support.clone());
        Ok(support)
    }

    /// Look one cached piece up, failing closed when it was never fetched.
    pub(super) fn piece_for(
        &self,
        slot: &FrameworkIIPieceSlot,
    ) -> Result<FrameworkIIPiece, PieceError> {
        let piece = match &slot.clause {
            None => self.cached_task_piece(slot.role),
            Some(digest) => self.cached_clause_piece(digest, slot.role),
        };
        piece.ok_or(PieceError::Invalid(
            "a fixed-ambient obligation names a piece that was never rendered",
        ))
    }
}

/// The sorted constant-key list, length-framed so no two distinct sets
/// share a key.
fn support_cache_key(constants: &[ConstantKey]) -> String {
    let mut key = String::new();
    for constant in constants {
        key.push_str(&constant.as_str().len().to_string());
        key.push(':');
        key.push_str(constant.as_str());
    }
    key
}

fn adopt_pieces(
    encoding: &FixedAmbientEncodingContext,
    wire: Vec<WirePiece>,
    roles: &[FrameworkIIComponentRole],
    expected: &[&FrameworkIIComponentMetadata],
    revision: crate::encoding::NameEnvRevision,
) -> Result<Vec<FrameworkIIPiece>, PieceError> {
    if wire.len() != roles.len() || expected.len() != roles.len() {
        return Err(PieceError::Invalid(
            "a fixed-ambient piece bundle has the wrong cardinality",
        ));
    }
    let mut pieces = Vec::with_capacity(wire.len());
    for ((row, role), component) in wire.into_iter().zip(roles).zip(expected) {
        if row.role != role.as_str() || component.role() != *role {
            return Err(PieceError::Invalid(
                "a fixed-ambient piece bundle is not in Lean's component order",
            ));
        }
        // Rust holds the component authority from admission; a piece is
        // only a rendering of it. Both the source identity and the complete
        // formula identity must agree before the body is adopted.
        if &row.formula_identity != component.formula().identity()
            || row.body.source_id != component.formula().source_id()
        {
            return Err(PieceError::Invalid(
                "a fixed-ambient piece disagrees with its admitted component",
            ));
        }
        let body = encoding
            .adopt_body(row.body, revision)
            .map_err(PieceError::Encoding)?;
        pieces.push(FrameworkIIPiece {
            role: *role,
            formula_identity: Arc::new(row.formula_identity),
            body,
        });
    }
    Ok(pieces)
}

// ------------------------------------------------------------
// Splice Recipes
// ------------------------------------------------------------

/// One position in an assembled obligation: which piece fills it, and — for
/// an axiom — the tag Lean assigns the axiom it becomes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct FrameworkIIPieceSlot {
    pub(super) role: FrameworkIIComponentRole,
    /// `None` for a task piece; the clause identity digest otherwise.
    pub(super) clause: Option<Arc<str>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct FrameworkIISpliceRecipe {
    pub(super) axioms: Vec<(FrameworkIIPieceSlot, FrameworkIIPremiseTag)>,
    pub(super) conjecture: FrameworkIIPieceSlot,
    /// Every distinct clause the recipe needs a piece of, in snapshot order.
    pub(super) clauses: Vec<ExtendedClause>,
}

fn task_slot(role: FrameworkIIComponentRole) -> FrameworkIIPieceSlot {
    FrameworkIIPieceSlot { role, clause: None }
}

fn clause_slot(role: FrameworkIIComponentRole, digest: &str) -> FrameworkIIPieceSlot {
    FrameworkIIPieceSlot {
        role,
        clause: Some(Arc::from(digest)),
    }
}

/// The exact axiom order `Obligations.lean` emits for one selector.
///
/// - `initVC`: `pre :: premises`, conjecture the plain clause.
/// - `maintenanceVC`: `formulas (upTo level) ++ guard :: premises`,
///   conjecture `wp(body, d)`.
/// - `premises`: `[]` at level zero, else
///   `not (theta guard) :: below.map theta`.
/// - `terminationVC`: `not guard :: collapsedPremises`, conjecture `post`.
///
/// `snapshot.canonical_order()` is `(level, registration order, id)`, the
/// same list Lean reconstructs as `Snapshot.rows`, so the `below`/`upTo`
/// filters here are the same filters over the same list.
pub(super) fn splice_recipe(
    snapshot: &LeveledCandidateSnapshot,
    selector: super::solver::FrameworkIISelector,
) -> Result<FrameworkIISpliceRecipe, PieceError> {
    use super::solver::FrameworkIISelector as Selector;
    let mut axioms = Vec::new();
    let mut clauses = Vec::new();
    let conjecture = match selector {
        Selector::Initialization(clause) | Selector::Maintenance(clause) => {
            let record = snapshot.records().get(&clause).ok_or(PieceError::Invalid(
                "a fixed-ambient obligation names a clause outside its snapshot",
            ))?;
            let level = snapshot.level_of(clause).ok_or(PieceError::Invalid(
                "a fixed-ambient obligation names an unplaced clause",
            ))?;
            let digest: Arc<str> = Arc::from(record.formula().identity_sha256());
            if matches!(selector, Selector::Maintenance(_)) {
                for row in snapshot.canonical_order() {
                    let row_level = snapshot.level_of(*row).ok_or(PieceError::Invalid(
                        "the canonical order lists an unplaced clause",
                    ))?;
                    if row_level > level {
                        continue;
                    }
                    let row_record = snapshot.records().get(row).ok_or(PieceError::Invalid(
                        "the canonical order lists a clause without a record",
                    ))?;
                    let row_digest = row_record.formula().identity_sha256();
                    clauses.push(row_record.formula().clone());
                    axioms.push((
                        clause_slot(FrameworkIIComponentRole::Clause, row_digest),
                        FrameworkIIPremiseTag::Plain(Arc::from(row_digest)),
                    ));
                }
                axioms.push((
                    task_slot(FrameworkIIComponentRole::Guard),
                    FrameworkIIPremiseTag::Guard,
                ));
            } else {
                axioms.push((
                    task_slot(FrameworkIIComponentRole::Precondition),
                    FrameworkIIPremiseTag::Pre,
                ));
            }
            if level.get() > 0 {
                axioms.push((
                    task_slot(FrameworkIIComponentRole::NegatedThetaGuard),
                    FrameworkIIPremiseTag::NotThetaGuard,
                ));
                for row in snapshot.canonical_order() {
                    let row_level = snapshot.level_of(*row).ok_or(PieceError::Invalid(
                        "the canonical order lists an unplaced clause",
                    ))?;
                    if row_level >= level {
                        continue;
                    }
                    let row_record = snapshot.records().get(row).ok_or(PieceError::Invalid(
                        "the canonical order lists a clause without a record",
                    ))?;
                    let row_digest = row_record.formula().identity_sha256();
                    clauses.push(row_record.formula().clone());
                    axioms.push((
                        clause_slot(FrameworkIIComponentRole::ThetaClause, row_digest),
                        FrameworkIIPremiseTag::Theta(Arc::from(row_digest)),
                    ));
                }
            }
            clauses.push(record.formula().clone());
            match selector {
                Selector::Initialization(_) => {
                    clause_slot(FrameworkIIComponentRole::Clause, &digest)
                }
                _ => clause_slot(FrameworkIIComponentRole::MaintenanceWp, &digest),
            }
        }
        Selector::Termination => {
            axioms.push((
                task_slot(FrameworkIIComponentRole::NegatedGuard),
                FrameworkIIPremiseTag::NotGuard,
            ));
            for row in snapshot.canonical_order() {
                let row_record = snapshot.records().get(row).ok_or(PieceError::Invalid(
                    "the canonical order lists a clause without a record",
                ))?;
                let row_digest = row_record.formula().identity_sha256();
                clauses.push(row_record.formula().clone());
                axioms.push((
                    clause_slot(FrameworkIIComponentRole::CollapsedClause, row_digest),
                    FrameworkIIPremiseTag::Collapsed(Arc::from(row_digest)),
                ));
            }
            task_slot(FrameworkIIComponentRole::Postcondition)
        }
    };
    Ok(FrameworkIISpliceRecipe {
        axioms,
        conjecture,
        clauses: distinct_clauses(clauses),
    })
}

/// The sorted, deduplicated union of the pieces' exact constant keys.
///
/// This is the set `QFEntailment.constants` denotes for the assembled
/// obligation — every constant of every axiom together with the
/// conjecture's — and the set the support block must cover.
/// `assemble_fixed_ambient_entailment_with_support` recomputes the same
/// union from the same bodies and rejects a block over any other set.
pub(super) fn constant_union<'a>(
    sets: impl IntoIterator<Item = &'a [ConstantKey]>,
) -> Vec<ConstantKey> {
    let mut union = std::collections::BTreeSet::new();
    for set in sets {
        union.extend(set.iter().cloned());
    }
    union.into_iter().collect()
}

/// Bytes of one `prepare_clause_pieces` request frame reserved for the
/// envelope the worker protocol wraps the payload in — the operation name,
/// the task and scope identities, the source digest, and the JSON
/// scaffolding around the clause array. Generous on purpose: overshooting
/// costs one extra round trip on an enormous missing set, while
/// undershooting would produce a frame the worker refuses.
const CLAUSE_REQUEST_ENVELOPE_RESERVE: usize = 64 * 1024;

/// Split `missing` into consecutive batches whose request payloads each fit
/// inside one [`MAX_ENCODING_FRAME_BYTES`] transport frame.
///
/// The transport frame is the only bound on a piece request: there is no
/// item cap on either side. Batching by measured bytes rather than by a
/// fixed count means a missing set of any size is served — a set that does
/// not fit costs additional round trips instead of failing closed — while a
/// missing set of ordinary size is still exactly one request.
///
/// A single clause whose own payload exceeds a whole frame is left in a
/// batch of one: it cannot be split further, and the worker's own frame
/// check is what reports it.
fn clause_request_batches(missing: &[ExtendedClause]) -> Vec<&[ExtendedClause]> {
    let sizes = missing.iter().map(clause_request_bytes).collect::<Vec<_>>();
    let budget = MAX_ENCODING_FRAME_BYTES.saturating_sub(CLAUSE_REQUEST_ENVELOPE_RESERVE);
    batch_ranges(&sizes, budget)
        .into_iter()
        .map(|range| &missing[range])
        .collect()
}

/// Consecutive index ranges covering `sizes`, each summing to at most
/// `budget` except where one item alone exceeds it and so stands alone.
fn batch_ranges(sizes: &[usize], budget: usize) -> Vec<std::ops::Range<usize>> {
    if sizes.is_empty() {
        return Vec::new();
    }
    let mut batches = Vec::new();
    let mut start = 0;
    let mut used = 0usize;
    for (index, size) in sizes.iter().enumerate() {
        if index > start && used.saturating_add(*size) > budget {
            batches.push(start..index);
            start = index;
            used = 0;
        }
        used = used.saturating_add(*size);
    }
    batches.push(start..sizes.len());
    batches
}

/// Bytes one clause occupies in a `prepare_clause_pieces` payload.
fn clause_request_bytes(clause: &ExtendedClause) -> usize {
    // The two fields the payload carries, plus the object punctuation
    // around them. `identity` is measured as Lean's own serialization of
    // it, which is what the request actually sends.
    clause.canonical_source().len()
        + clause.identity().to_string().len()
        + "{\"canonical_source\":,\"identity\":},".len()
}

/// Keep the first occurrence of each Lean-issued clause identity, in order.
fn distinct_clauses(clauses: Vec<ExtendedClause>) -> Vec<ExtendedClause> {
    let mut seen = std::collections::BTreeSet::new();
    clauses
        .into_iter()
        .filter(|clause| seen.insert(Arc::<str>::from(clause.identity_sha256())))
        .collect()
}

// ------------------------------------------------------------
// Strict Wire Shapes
// ------------------------------------------------------------

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WireTaskPieces {
    pieces: Vec<WirePiece>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WireClausePieces {
    clauses: Vec<WireClausePieceRow>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WireClausePieceRow {
    identity: Value,
    canonical_source: String,
    pieces: Vec<WirePiece>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WirePiece {
    role: String,
    formula_identity: Value,
    body: FixedAmbientPreparedBodyData,
}

fn decode<T: for<'de> Deserialize<'de>>(value: Value, label: &str) -> Result<T, PieceError> {
    serde_json::from_value(value)
        .map_err(|error| PieceError::Decode(format!("decode {label}: {error}")))
}

#[derive(Clone, Debug)]
pub(super) enum PieceError {
    Encoding(crate::encoding::EncodingError),
    Decode(String),
    Invalid(&'static str),
}

#[cfg(test)]
mod tests {
    use super::*;

    fn keys(values: &[&str]) -> Vec<ConstantKey> {
        values
            .iter()
            .map(|value| ConstantKey::from_canonical((*value).to_owned()).unwrap())
            .collect()
    }

    #[test]
    fn the_constant_union_is_sorted_and_deduplicated() {
        let first = keys(&["str:c", "str:a"]);
        let second = keys(&["str:a", "str:b"]);
        assert_eq!(
            constant_union([first.as_slice(), second.as_slice()]),
            keys(&["str:a", "str:b", "str:c"])
        );
        assert!(constant_union(std::iter::empty()).is_empty());
        assert_eq!(
            constant_union([first.as_slice()]),
            keys(&["str:a", "str:c"])
        );
    }

    /// Pass 7.7b, item 15: the piece request is chunked by transport frame
    /// bytes, not by an item count, so a missing set of any size is served.
    #[test]
    fn piece_requests_are_batched_by_frame_bytes() {
        // Nothing missing is no round trip at all.
        assert!(batch_ranges(&[], 100).is_empty());
        // An ordinary missing set is exactly one request.
        assert_eq!(batch_ranges(&[10, 20, 30], 100), vec![0..3]);
        assert_eq!(batch_ranges(&[50, 50], 100), vec![0..2]);
        // Beyond the budget the set is split rather than refused.
        assert_eq!(batch_ranges(&[50, 51], 100), vec![0..1, 1..2]);
        assert_eq!(batch_ranges(&[40, 40, 40, 40], 100), vec![0..2, 2..4]);
        // One item larger than a whole frame stands alone; it cannot be
        // split further, and the worker's own frame check reports it.
        assert_eq!(batch_ranges(&[10, 500, 10], 100), vec![0..1, 1..2, 2..3]);
        // Every clause appears exactly once, in order, whatever the split.
        let sizes = (1..=40).collect::<Vec<usize>>();
        let batches = batch_ranges(&sizes, 60);
        assert!(batches.len() > 1);
        let covered = batches
            .iter()
            .flat_map(|range| range.clone())
            .collect::<Vec<_>>();
        assert_eq!(covered, (0..sizes.len()).collect::<Vec<_>>());
    }

    #[test]
    fn the_support_cache_key_separates_adjacent_constant_lists() {
        assert_ne!(
            support_cache_key(&keys(&["str:ab", "str:c"])),
            support_cache_key(&keys(&["str:a", "str:bc"]))
        );
        assert_eq!(
            support_cache_key(&keys(&["str:a"])),
            support_cache_key(&keys(&["str:a"]))
        );
        assert_ne!(
            support_cache_key(&keys(&[])),
            support_cache_key(&keys(&["str:a"]))
        );
    }
}
