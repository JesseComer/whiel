//! Append-only fixed-ambient placement and invalidation evidence.
//!
//! # Row ordinals and attempt ids are different identifiers
//!
//! A row's `row_ordinal` is the controller's own: requests reserve
//! consecutive ordinals in check order before a batch is dispatched, and
//! the recording pass appends in that same order, so a rerun of one
//! deterministic fixture produces the same ordinals and the same row-digest
//! chain whatever the dispatch does.
//!
//! An `AttemptId` (`ArtifactStore::begin_entailment_attempt`) is not. It is
//! allocated when a launch first needs an artifact scope, and since Pass
//! 7.5d a batch's launches run concurrently, so the ids of one sweep are
//! handed out in completion order rather than check order and a rerun may
//! permute them. Nothing durable keys on an attempt id as a reproducible
//! name: it addresses a retained countermodel *within one run* (the agent
//! reads the id off the very feedback push that announces the refutation,
//! and the `countermodel` tool answers by that id), and it is one digested
//! field of a per-attempt receipt, whose digest is likewise run-local. The
//! Core, its certificate inputs and the emitted certificate carry no
//! attempt id at all. Anything that needs a reproducible name for a check
//! must use the row ordinal.

use std::collections::BTreeSet;
use std::fmt;
use std::sync::Arc;
use std::time::Duration;

use serde_json::{Value, json};

use crate::encoding::canonical_value_sha256;
use crate::houdini::ClauseId;

use super::catalog::FrameworkIIStateError;
use super::production::{
    FrameworkIIEntailmentProgress, ProtectedTheoremSelectionReceipt, RuntimeProofReceipt,
    SemanticReuseEvidence, ValidatedFiniteRefutation,
};
use super::snapshot::LeveledCandidateSnapshot;
use super::types::FrameworkIILevel;

// ------------------------------------------------------------
// Checker Requests And Outcomes
// ------------------------------------------------------------

const FRAMEWORK_II_LAUNCH_SUPPRESSED_IDENTITY_VERSION: u64 = 1;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum FrameworkIICheckRole {
    Initialization,
    Maintenance,
}

impl FrameworkIICheckRole {
    pub(super) fn identity_name(self) -> &'static str {
        match self {
            Self::Initialization => "initialization",
            Self::Maintenance => "maintenance",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum FrameworkIIInconclusiveReason {
    TimedOut,
    SolverUnknown,
    PeerFailed,
    UnvalidatedRefutation,
    Cancelled,
    /// The controller had already suspended this clause for the epoch, so
    /// the check was answered from the semantic dictionary alone and no
    /// solver was launched.
    Suspended,
}

impl FrameworkIIInconclusiveReason {
    pub(super) fn identity_name(self) -> &'static str {
        match self {
            Self::TimedOut => "timed_out",
            Self::SolverUnknown => "solver_unknown",
            Self::PeerFailed => "peer_failed",
            Self::UnvalidatedRefutation => "unvalidated_refutation",
            Self::Cancelled => "cancelled",
            Self::Suspended => "suspended",
        }
    }

    /// Whether an inconclusive launch under this reason consumes one of the
    /// key's retry allowances and is recorded as a dictionary entry.
    ///
    /// A cancelled launch and a launch stopped by a peer's failure say
    /// nothing about the obligation — the solver never reported on it — so
    /// they leave the key exactly as they found it. Only a solver timeout,
    /// an unknown result and a model the validator could not accept are
    /// evidence that this key is hard.
    pub(crate) fn consumes_retry_allowance(self) -> bool {
        match self {
            Self::TimedOut | Self::SolverUnknown | Self::UnvalidatedRefutation => true,
            Self::PeerFailed | Self::Cancelled | Self::Suspended => false,
        }
    }
}

/// Exact reason a catalog clause was moved to the terminal `dead` partition.
///
/// A clause dead by refutation never revives, never becomes drop-eligible,
/// and a later proposal that interns the same identity is rejected with this
/// reason rather than re-entering `pending`. A clause dead by a proposer
/// drop carries no reason and is revived by its own exact resubmission.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FrameworkIIDeadReason {
    /// A clause whose admitted formula mentions no prophecy relation received
    /// a Lean-validated finite refutation of its level-zero initialization
    /// obligation. `attempt` names the ledger attempt row that carries the
    /// validated refutation.
    ProphecyFreeInitializationRefuted { attempt: u64 },
}

impl FrameworkIIDeadReason {
    pub(super) fn identity_name(self) -> &'static str {
        match self {
            Self::ProphecyFreeInitializationRefuted { .. } => {
                "prophecy_free_initialization_refuted"
            }
        }
    }

    pub(crate) fn identity_fields(self) -> serde_json::Value {
        match self {
            Self::ProphecyFreeInitializationRefuted { attempt } => json!({
                "kind": self.identity_name(),
                "attempt": attempt,
            }),
        }
    }
}

impl fmt::Display for FrameworkIIDeadReason {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ProphecyFreeInitializationRefuted { attempt } => write!(
                formatter,
                "prophecy-free clause received a Lean-validated level-zero \
                 initialization refutation (ledger attempt {attempt})"
            ),
        }
    }
}

#[derive(Clone, Debug)]
enum FrameworkIICheckAuthority {
    RuntimeProof(Arc<RuntimeProofReceipt>),
    ProtectedTheoremSelection(Arc<ProtectedTheoremSelectionReceipt>),
    ValidatedRefutation(Arc<ValidatedFiniteRefutation>),
    Progress(Arc<FrameworkIIEntailmentProgress>),
    /// The controller suspended this clause for the rest of the epoch, so
    /// the check was answered from the semantic dictionary alone and no
    /// solver ran. There is no solver receipt to carry: the row's
    /// provenance is the suspension itself.
    LaunchSuppressed,
    #[cfg(test)]
    Scripted,
}

/// Complete typed evidence supplied to the runtime placement controller.
///
/// A semantic-key reuse (see [`Self::from_semantic_reuse`]) shares this same
/// `authority` — the identical `Arc` the original attempt published, never a
/// fabricated copy — so every existing consumer (root-profile selection,
/// certificate packaging, Agent feedback) keeps reading real search-phase
/// authority through `runtime_proof`/`protected_theorem_selection`/
/// `validated_refutation` unchanged. `reuse` carries only the additional
/// audit pointer back to the original attempt; it never grants authority by
/// itself.
#[derive(Clone, Debug)]
pub struct FrameworkIICheckEvidence {
    request_digest: Arc<str>,
    identity: Arc<str>,
    authority: FrameworkIICheckAuthority,
    reuse: Option<Arc<SemanticReuseEvidence>>,
    solver_time: Option<Duration>,
    /// Measured wall time of the obligation preparation this evidence's
    /// check performed. Attached only through
    /// [`Self::with_preparation_time`] after construction, so every
    /// existing authority constructor keeps its original signature and
    /// defaults to `None` unless a caller opts in.
    preparation_time: Option<Duration>,
}

impl FrameworkIICheckEvidence {
    /// `solver_time` is the measured wall time of the Vampire invocation this
    /// receipt closed. Absent for a row that never launched a solver.
    pub(crate) fn from_runtime_proof(
        receipt: RuntimeProofReceipt,
        solver_time: Option<Duration>,
    ) -> Self {
        Self {
            request_digest: Arc::from(receipt.request_digest()),
            identity: Arc::from(receipt.receipt_digest()),
            authority: FrameworkIICheckAuthority::RuntimeProof(Arc::new(receipt)),
            reuse: None,
            solver_time,
            preparation_time: None,
        }
    }

    /// A protected system row closes by reviewed Lean theorem selection, never
    /// by a solver launch, so its solver time is always absent.
    pub(crate) fn from_protected_theorem_selection(
        selection: ProtectedTheoremSelectionReceipt,
    ) -> Self {
        Self {
            request_digest: Arc::from(selection.request_digest()),
            identity: Arc::from(selection.selection_digest()),
            authority: FrameworkIICheckAuthority::ProtectedTheoremSelection(Arc::new(selection)),
            reuse: None,
            solver_time: None,
            preparation_time: None,
        }
    }

    /// `solver_time` is the measured wall time of the Vampire invocation this
    /// refutation closed. Absent for a row that never launched a solver.
    pub(crate) fn from_validated_refutation(
        refutation: ValidatedFiniteRefutation,
        solver_time: Option<Duration>,
    ) -> Self {
        Self {
            request_digest: Arc::from(refutation.request_digest()),
            identity: Arc::from(refutation.refutation_digest()),
            authority: FrameworkIICheckAuthority::ValidatedRefutation(Arc::new(refutation)),
            reuse: None,
            solver_time,
            preparation_time: None,
        }
    }

    /// `solver_time` is the measured wall time of the Vampire invocation that
    /// produced this progress record. Absent for a row that never launched a
    /// solver.
    pub(crate) fn from_progress(
        progress: FrameworkIIEntailmentProgress,
        solver_time: Option<Duration>,
    ) -> Self {
        Self {
            request_digest: Arc::from(progress.request_digest()),
            identity: Arc::from(progress.progress_digest()),
            authority: FrameworkIICheckAuthority::Progress(Arc::new(progress)),
            reuse: None,
            solver_time,
            preparation_time: None,
        }
    }

    /// The row of a check the controller had already suspended for this
    /// epoch: the semantic dictionary held no answer for it and no solver
    /// was launched, so there is no receipt and no timing to attribute.
    /// `houdini.tex` Section 4.4 still records one ledger row per check,
    /// and this evidence is that row's provenance.
    pub(crate) fn launch_suppressed(request_digest: &str) -> Result<Self, FrameworkIIStateError> {
        if !is_sha256(request_digest) {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "check evidence is not bound to a lowercase SHA-256 request",
            ));
        }
        let identity = canonical_value_sha256(&json!({
            "kind": "whiel_framework_ii_launch_suppressed_check",
            "version": FRAMEWORK_II_LAUNCH_SUPPRESSED_IDENTITY_VERSION,
            "request_digest": request_digest,
        }));
        Ok(Self {
            request_digest: Arc::from(request_digest),
            identity: Arc::from(identity),
            authority: FrameworkIICheckAuthority::LaunchSuppressed,
            reuse: None,
            solver_time: None,
            preparation_time: None,
        })
    }

    /// Attach the measured wall time of the obligation preparation this
    /// evidence's check performed. Chainable so the authority constructors
    /// above keep their original signature.
    /// Deliberately never called for [`Self::from_protected_theorem_selection`]
    /// or [`Self::from_semantic_reuse`], which never launch a fresh worker
    /// preparation for this row, so both stay `None`.
    pub(crate) fn with_preparation_time(mut self, preparation_time: Option<Duration>) -> Self {
        self.preparation_time = preparation_time;
        self
    }

    /// Bind a semantic-key reuse to this request without fabricating a new
    /// receipt: `authority` is the exact `Arc` `original` already carries
    /// (a runtime proof receipt, a protected-theorem selection, or a
    /// validated refutation — never [`FrameworkIICheckAuthority::Progress`],
    /// since inconclusive outcomes are never reused), so every downstream
    /// reader of `runtime_proof`/`protected_theorem_selection`/
    /// `validated_refutation` sees the real original authority unchanged.
    /// `request_digest` and `identity` are rebound to this reusing request
    /// and to the reuse's own audit identity; `reuse` records the pointer
    /// back to the original attempt.
    /// A semantic-key reuse never re-attributes solver time to the reusing
    /// row: this run's earlier attempt already accounted for it.
    pub(crate) fn from_semantic_reuse(
        original: &FrameworkIICheckEvidence,
        reuse: SemanticReuseEvidence,
    ) -> Self {
        Self {
            request_digest: reuse.request_digest_arc(),
            identity: reuse.identity_arc(),
            authority: original.authority.clone(),
            reuse: Some(Arc::new(reuse)),
            solver_time: None,
            preparation_time: None,
        }
    }

    /// Unit-test scaffolding cannot cross the production authority boundary.
    #[cfg(test)]
    pub(crate) fn new(
        request_digest: impl Into<Arc<str>>,
        identity: impl Into<Arc<str>>,
    ) -> Result<Self, FrameworkIIStateError> {
        let request_digest = request_digest.into();
        if !is_sha256(&request_digest) {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "check evidence is not bound to a lowercase SHA-256 request",
            ));
        }
        let identity = identity.into();
        if identity.is_empty() || identity.len() > 4096 {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "a check-evidence identity must be nonempty and bounded",
            ));
        }
        Ok(Self {
            request_digest,
            identity,
            authority: FrameworkIICheckAuthority::Scripted,
            reuse: None,
            solver_time: None,
            preparation_time: None,
        })
    }

    pub fn request_digest(&self) -> &str {
        &self.request_digest
    }

    pub fn identity(&self) -> &str {
        &self.identity
    }

    pub fn runtime_proof(&self) -> Option<&Arc<RuntimeProofReceipt>> {
        match &self.authority {
            FrameworkIICheckAuthority::RuntimeProof(receipt) => Some(receipt),
            _ => None,
        }
    }

    pub fn protected_theorem_selection(&self) -> Option<&Arc<ProtectedTheoremSelectionReceipt>> {
        match &self.authority {
            FrameworkIICheckAuthority::ProtectedTheoremSelection(selection) => Some(selection),
            _ => None,
        }
    }

    pub fn validated_refutation(&self) -> Option<&Arc<ValidatedFiniteRefutation>> {
        match &self.authority {
            FrameworkIICheckAuthority::ValidatedRefutation(refutation) => Some(refutation),
            _ => None,
        }
    }

    /// True for the row of a check the controller suspended for its epoch:
    /// no solver ran, so there is no receipt behind it, only the
    /// suspension.
    pub fn is_launch_suppressed(&self) -> bool {
        matches!(self.authority, FrameworkIICheckAuthority::LaunchSuppressed)
    }

    pub fn progress(&self) -> Option<&Arc<FrameworkIIEntailmentProgress>> {
        match &self.authority {
            FrameworkIICheckAuthority::Progress(progress) => Some(progress),
            _ => None,
        }
    }

    /// Measured wall time of the Vampire invocation this evidence closed.
    ///
    /// Absent for a theorem-closed row (protected system clause) and for a
    /// dictionary/semantic-key reuse row, both of which never launch a
    /// solver.
    pub fn solver_time(&self) -> Option<Duration> {
        self.solver_time
    }

    /// Measured wall time of the obligation preparation this evidence's
    /// check performed: the semantic adapter's `prepare` call in
    /// `production.rs`, which splices the problem out of the run's
    /// opaque-piece cache and contacts the worker only for the pieces that
    /// cache misses on. A preparation is therefore not a worker round trip;
    /// the round-trip counts live in
    /// `FrameworkIISolverContext::piece_cache_stats`.
    ///
    /// Absent for a theorem-closed row (protected system clause) and for a
    /// dictionary/semantic-key reuse row, neither of which prepares an
    /// obligation for this check, mirroring [`Self::solver_time`].
    pub fn preparation_time(&self) -> Option<Duration> {
        self.preparation_time
    }

    /// The reuse reference, when this evidence closed without a fresh
    /// worker preparation or solver launch because an earlier attempt in
    /// this run already resolved the same semantic verification condition.
    /// `runtime_proof`/`protected_theorem_selection`/`validated_refutation`
    /// still return the real original authority regardless of this.
    pub fn semantic_reuse(&self) -> Option<&Arc<SemanticReuseEvidence>> {
        self.reuse.as_ref()
    }

    fn closes_runtime_check(&self) -> bool {
        match &self.authority {
            FrameworkIICheckAuthority::RuntimeProof(_)
            | FrameworkIICheckAuthority::ProtectedTheoremSelection(_) => true,
            #[cfg(test)]
            FrameworkIICheckAuthority::Scripted => true,
            _ => false,
        }
    }

    fn is_refutation_authority(&self) -> bool {
        match &self.authority {
            FrameworkIICheckAuthority::ValidatedRefutation(_) => true,
            #[cfg(test)]
            FrameworkIICheckAuthority::Scripted => true,
            _ => false,
        }
    }

    fn is_progress_authority(&self, reason: FrameworkIIInconclusiveReason) -> bool {
        match &self.authority {
            FrameworkIICheckAuthority::LaunchSuppressed => {
                reason == FrameworkIIInconclusiveReason::Suspended
            }
            FrameworkIICheckAuthority::Progress(progress) => progress.reason() == reason,
            #[cfg(test)]
            FrameworkIICheckAuthority::Scripted => true,
            _ => false,
        }
    }
}

impl PartialEq for FrameworkIICheckEvidence {
    fn eq(&self, other: &Self) -> bool {
        self.request_digest == other.request_digest && self.identity == other.identity
    }
}

impl Eq for FrameworkIICheckEvidence {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FrameworkIICheckOutcome {
    Proved(FrameworkIICheckEvidence),
    Refuted(FrameworkIICheckEvidence),
    Inconclusive {
        reason: FrameworkIIInconclusiveReason,
        progress: FrameworkIICheckEvidence,
    },
}

impl FrameworkIICheckOutcome {
    pub(super) fn is_bound_to(&self, request_digest: &str) -> bool {
        match self {
            Self::Proved(evidence) | Self::Refuted(evidence) => {
                evidence.request_digest() == request_digest
            }
            Self::Inconclusive { progress, .. } => progress.request_digest() == request_digest,
        }
    }

    /// The one [`FrameworkIICheckEvidence`] this outcome carries, regardless
    /// of which terminal variant closed the check.
    pub(super) fn evidence(&self) -> &FrameworkIICheckEvidence {
        match self {
            Self::Proved(evidence) | Self::Refuted(evidence) => evidence,
            Self::Inconclusive { progress, .. } => progress,
        }
    }

    pub(super) fn identity_fields(&self) -> serde_json::Value {
        match self {
            Self::Proved(evidence) => json!({
                "kind": "proved",
                "request_digest": evidence.request_digest(),
                "evidence": evidence.identity(),
            }),
            Self::Refuted(evidence) => json!({
                "kind": "refuted",
                "request_digest": evidence.request_digest(),
                "evidence": evidence.identity(),
            }),
            Self::Inconclusive { reason, progress } => json!({
                "kind": "inconclusive",
                "reason": reason.identity_name(),
                "request_digest": progress.request_digest(),
                "progress": progress.identity(),
            }),
        }
    }

    fn has_typed_authority(&self) -> bool {
        match self {
            Self::Proved(evidence) => evidence.closes_runtime_check(),
            Self::Refuted(evidence) => evidence.is_refutation_authority(),
            Self::Inconclusive { reason, progress } => progress.is_progress_authority(*reason),
        }
    }
}

/// One exact snapshot-bound request issued by the control algorithm.
#[derive(Clone, Debug)]
pub struct FrameworkIICheckRequest {
    attempt_ordinal: u64,
    clause: ClauseId,
    level: FrameworkIILevel,
    role: FrameworkIICheckRole,
    snapshot: Arc<LeveledCandidateSnapshot>,
    identity: Arc<Value>,
    request_digest: Arc<str>,
    /// Purely an execution instruction to the production checker: this
    /// clause is already suspended for the epoch, so the check is answered
    /// from the semantic dictionary alone and, failing that, inconclusive
    /// without a solver launch. Never part of the request's logical
    /// identity, since a suppressed and an ordinary request denote the
    /// exact same verification condition.
    launch_suppressed: bool,
}

impl FrameworkIICheckRequest {
    /// Construct one check request.
    ///
    /// An ordinary request (`launch_suppressed` false) is served through
    /// the semantic dictionary and launched when the dictionary has no
    /// answer. A request for a clause the controller has already suspended
    /// for this epoch (`launch_suppressed` true) is still served through
    /// the dictionary, but when the dictionary has no answer the checker
    /// returns [`FrameworkIIInconclusiveReason::Suspended`] without a
    /// launch, without consuming a retry allowance and without recording a
    /// dictionary entry.
    pub(super) fn new(
        attempt_ordinal: u64,
        clause: ClauseId,
        level: FrameworkIILevel,
        role: FrameworkIICheckRole,
        snapshot: Arc<LeveledCandidateSnapshot>,
        launch_suppressed: bool,
    ) -> Result<Self, FrameworkIIStateError> {
        if snapshot.level_of(clause) != Some(level) {
            return Err(FrameworkIIStateError::InvalidPlacement(
                "a check target is absent or assigned to another level",
            ));
        }
        let identity = request_identity(attempt_ordinal, &snapshot, role, clause);
        let request_digest = Arc::from(canonical_value_sha256(&identity));
        Ok(Self {
            attempt_ordinal,
            clause,
            level,
            role,
            snapshot,
            identity: Arc::new(identity),
            request_digest,
            launch_suppressed,
        })
    }

    /// True when the controller had already suspended this clause for the
    /// epoch: the checker consults its dictionary as usual but never starts
    /// a solver for this request.
    pub(crate) fn launch_suppressed(&self) -> bool {
        self.launch_suppressed
    }

    pub fn attempt_ordinal(&self) -> u64 {
        self.attempt_ordinal
    }

    pub fn clause(&self) -> ClauseId {
        self.clause
    }

    pub fn level(&self) -> FrameworkIILevel {
        self.level
    }

    pub fn role(&self) -> FrameworkIICheckRole {
        self.role
    }

    pub fn snapshot(&self) -> &Arc<LeveledCandidateSnapshot> {
        &self.snapshot
    }

    /// Full fixed-ambient request identity. The digest is only an index over
    /// this Lean-owned snapshot and exact-obligation selector.
    pub fn identity(&self) -> &Value {
        &self.identity
    }

    pub(crate) fn worker_selector(&self) -> Value {
        worker_selector(self.role, self.clause)
    }

    pub fn request_digest(&self) -> &str {
        &self.request_digest
    }

    pub(super) fn has_current_identity(&self) -> bool {
        let identity =
            request_identity(self.attempt_ordinal, &self.snapshot, self.role, self.clause);
        identity == *self.identity
            && canonical_value_sha256(&identity) == self.request_digest.as_ref()
    }

    #[cfg(test)]
    pub(super) fn replace_request_digest_for_legacy_test(
        &mut self,
        request_digest: impl Into<Arc<str>>,
    ) {
        self.request_digest = request_digest.into();
    }
}

// ------------------------------------------------------------
// Hash-Linked Attempt History
// ------------------------------------------------------------

#[derive(Clone, Debug)]
pub struct LevelAttemptRecord {
    row_ordinal: u64,
    request: FrameworkIICheckRequest,
    outcome: FrameworkIICheckOutcome,
    previous_digest: Option<Arc<str>>,
    row_digest: Arc<str>,
}

impl LevelAttemptRecord {
    pub fn row_ordinal(&self) -> u64 {
        self.row_ordinal
    }

    pub fn request(&self) -> &FrameworkIICheckRequest {
        &self.request
    }

    pub fn outcome(&self) -> &FrameworkIICheckOutcome {
        &self.outcome
    }

    pub fn previous_digest(&self) -> Option<&str> {
        self.previous_digest.as_deref()
    }

    pub fn row_digest(&self) -> &str {
        &self.row_digest
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FrameworkIIInvalidationReason {
    AntecedentClauseDeleted,
    /// The antecedent clause survived its refutation — it mentions a
    /// prophecy relation, or it was committed at some earlier point — and
    /// was promoted past the level whose initialization refuted it. It is
    /// still a live candidate, so the dependent root falls only because the
    /// promoted clause left that level's cohort.
    AntecedentClausePromoted,
    /// The antecedent clause was excluded from this level's step cohort by
    /// its own maintenance refutation. Like a promotion this deletes
    /// nothing; the cohort the dependent root was checked against simply
    /// shrank.
    AntecedentClauseExcluded,
    SnapshotChanged,
    SystemClausesInstalled,
}

impl FrameworkIIInvalidationReason {
    pub(super) fn identity_name(self) -> &'static str {
        match self {
            Self::AntecedentClauseDeleted => "antecedent_clause_deleted",
            Self::AntecedentClausePromoted => "antecedent_clause_promoted",
            Self::AntecedentClauseExcluded => "antecedent_clause_excluded",
            Self::SnapshotChanged => "snapshot_changed",
            Self::SystemClausesInstalled => "system_clauses_installed",
        }
    }
}

#[derive(Clone, Debug)]
pub struct LevelInvalidationRecord {
    row_ordinal: u64,
    invalidated_attempt: u64,
    target: ClauseId,
    cause: Option<ClauseId>,
    reason: FrameworkIIInvalidationReason,
    previous_digest: Option<Arc<str>>,
    row_digest: Arc<str>,
}

impl LevelInvalidationRecord {
    pub fn invalidated_attempt(&self) -> u64 {
        self.invalidated_attempt
    }

    pub fn target(&self) -> ClauseId {
        self.target
    }

    pub fn cause(&self) -> Option<ClauseId> {
        self.cause
    }

    pub fn reason(&self) -> FrameworkIIInvalidationReason {
        self.reason
    }

    pub fn previous_digest(&self) -> Option<&str> {
        self.previous_digest.as_deref()
    }

    pub fn row_digest(&self) -> &str {
        &self.row_digest
    }
}

#[derive(Clone, Debug)]
pub enum LevelLedgerRow {
    Attempt(Box<LevelAttemptRecord>),
    Invalidation(LevelInvalidationRecord),
}

impl LevelLedgerRow {
    pub fn row_ordinal(&self) -> u64 {
        match self {
            Self::Attempt(row) => row.row_ordinal,
            Self::Invalidation(row) => row.row_ordinal,
        }
    }

    pub fn row_digest(&self) -> &str {
        match self {
            Self::Attempt(row) => &row.row_digest,
            Self::Invalidation(row) => &row.row_digest,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct LevelAttemptLedger {
    rows: Vec<LevelLedgerRow>,
    invalidated_attempts: BTreeSet<u64>,
}

impl LevelAttemptLedger {
    pub fn next_ordinal(&self) -> Result<u64, FrameworkIIStateError> {
        u64::try_from(self.rows.len()).map_err(|_| {
            FrameworkIIStateError::InvalidEvidence("the attempt ledger exhausted its row space")
        })
    }

    pub fn rows(&self) -> &[LevelLedgerRow] {
        &self.rows
    }

    pub fn attempt(&self, ordinal: u64) -> Option<&LevelAttemptRecord> {
        self.rows
            .get(usize::try_from(ordinal).ok()?)
            .and_then(|row| match row {
                LevelLedgerRow::Attempt(attempt) => Some(attempt.as_ref()),
                LevelLedgerRow::Invalidation(_) => None,
            })
    }

    pub fn is_invalidated(&self, attempt: u64) -> bool {
        self.invalidated_attempts.contains(&attempt)
    }

    #[cfg(test)]
    pub(super) fn rewrite_attempt_digest_as_legacy_v2_for_test(
        &mut self,
        ordinal: u64,
    ) -> Result<(), FrameworkIIStateError> {
        let Some(LevelLedgerRow::Attempt(attempt)) =
            self.rows.get_mut(usize::try_from(ordinal).map_err(|_| {
                FrameworkIIStateError::InvalidEvidence("test attempt ordinal is unrepresentable")
            })?)
        else {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "test row is not an attempt",
            ));
        };
        attempt.row_digest = Arc::from(canonical_value_sha256(&json!({
            "domain": "whiel-framework-ii-attempt-row-v2",
            "row_ordinal": attempt.row_ordinal,
            "request_digest": attempt.request.request_digest(),
            "outcome": attempt.outcome.identity_fields(),
            "previous_digest": attempt.previous_digest.as_deref(),
        })));
        Ok(())
    }

    pub(super) fn append_attempt(
        &mut self,
        request: FrameworkIICheckRequest,
        outcome: FrameworkIICheckOutcome,
    ) -> Result<u64, FrameworkIIStateError> {
        let row_ordinal = self.next_ordinal()?;
        if request.attempt_ordinal() != row_ordinal {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "a check result does not match the next ledger ordinal",
            ));
        }
        if !request.has_current_identity() {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "a check result carries a legacy or detached fixed-ambient request identity",
            ));
        }
        if !outcome.has_typed_authority() {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "a fixed-ambient outcome does not carry authority of the required kind",
            ));
        }
        let previous_digest = self
            .rows
            .last()
            .map(|row| Arc::<str>::from(row.row_digest()));
        let payload = json!({
            "domain": "whiel-framework-ii-attempt-row-v3",
            "row_ordinal": row_ordinal,
            "request_digest": request.request_digest(),
            "outcome": outcome.identity_fields(),
            "previous_digest": previous_digest.as_deref(),
        });
        let row_digest = Arc::from(canonical_value_sha256(&payload));
        self.rows
            .push(LevelLedgerRow::Attempt(Box::new(LevelAttemptRecord {
                row_ordinal,
                request,
                outcome,
                previous_digest,
                row_digest,
            })));
        Ok(row_ordinal)
    }

    pub(super) fn append_invalidation(
        &mut self,
        invalidated_attempt: u64,
        target: ClauseId,
        cause: Option<ClauseId>,
        reason: FrameworkIIInvalidationReason,
    ) -> Result<(), FrameworkIIStateError> {
        if self.attempt(invalidated_attempt).is_none() {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "an invalidation names a non-attempt row",
            ));
        }
        if !self.invalidated_attempts.insert(invalidated_attempt) {
            return Ok(());
        }
        let row_ordinal = self.next_ordinal()?;
        let previous_digest = self
            .rows
            .last()
            .map(|row| Arc::<str>::from(row.row_digest()));
        let payload = json!({
            "domain": "whiel-framework-ii-invalidation-row-v2",
            "row_ordinal": row_ordinal,
            "invalidated_attempt": invalidated_attempt,
            "target": target.get(),
            "cause": cause.map(ClauseId::get),
            "reason": reason.identity_name(),
            "previous_digest": previous_digest.as_deref(),
        });
        let row_digest = Arc::from(canonical_value_sha256(&payload));
        self.rows
            .push(LevelLedgerRow::Invalidation(LevelInvalidationRecord {
                row_ordinal,
                invalidated_attempt,
                target,
                cause,
                reason,
                previous_digest,
                row_digest,
            }));
        Ok(())
    }

    /// Merge only the exact append-only history produced from a private clone
    /// of this ledger. Placement and current-root publication remain the
    /// caller's separate responsibility.
    pub(super) fn merge_exact_extension(
        &mut self,
        staged: &Self,
    ) -> Result<bool, FrameworkIIStateError> {
        self.validate_lineage()?;
        staged.validate_lineage()?;
        if staged.rows.len() < self.rows.len()
            || !self
                .rows
                .iter()
                .zip(&staged.rows)
                .all(|(published, candidate)| same_ledger_row(published, candidate))
        {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "staged attempt history is not an exact extension of the published ledger",
            ));
        }
        if staged.rows.len() == self.rows.len() {
            return Ok(false);
        }

        self.rows.extend_from_slice(&staged.rows[self.rows.len()..]);
        self.invalidated_attempts = staged.invalidated_attempts.clone();
        Ok(true)
    }

    pub(super) fn validate_lineage(&self) -> Result<(), FrameworkIIStateError> {
        let mut invalidated_attempts = BTreeSet::new();
        for (index, row) in self.rows.iter().enumerate() {
            let ordinal = u64::try_from(index).map_err(|_| {
                FrameworkIIStateError::InvalidEvidence("the attempt ledger exhausted its row space")
            })?;
            if row.row_ordinal() != ordinal
                || row_previous_digest(row)
                    != index
                        .checked_sub(1)
                        .map(|previous| self.rows[previous].row_digest())
            {
                return Err(FrameworkIIStateError::InvalidEvidence(
                    "the attempt ledger has broken ordinal or hash-chain lineage",
                ));
            }

            let expected_digest = match row {
                LevelLedgerRow::Attempt(attempt) => {
                    if attempt.request.attempt_ordinal() != ordinal
                        || !attempt.request.has_current_identity()
                        || !attempt.outcome.has_typed_authority()
                        || !attempt
                            .outcome
                            .is_bound_to(attempt.request.request_digest())
                    {
                        return Err(FrameworkIIStateError::InvalidEvidence(
                            "an attempt row has detached request or evidence authority",
                        ));
                    }
                    canonical_value_sha256(&json!({
                        "domain": "whiel-framework-ii-attempt-row-v3",
                        "row_ordinal": ordinal,
                        "request_digest": attempt.request.request_digest(),
                        "outcome": attempt.outcome.identity_fields(),
                        "previous_digest": attempt.previous_digest.as_deref(),
                    }))
                }
                LevelLedgerRow::Invalidation(invalidation) => {
                    let invalidated_index = usize::try_from(invalidation.invalidated_attempt)
                        .map_err(|_| {
                            FrameworkIIStateError::InvalidEvidence(
                                "an invalidation names an unrepresentable attempt row",
                            )
                        })?;
                    let Some(LevelLedgerRow::Attempt(attempt)) = self.rows.get(invalidated_index)
                    else {
                        return Err(FrameworkIIStateError::InvalidEvidence(
                            "an invalidation names a non-attempt row",
                        ));
                    };
                    if invalidated_index >= index
                        || attempt.request.clause() != invalidation.target
                        || !invalidated_attempts.insert(invalidation.invalidated_attempt)
                    {
                        return Err(FrameworkIIStateError::InvalidEvidence(
                            "an invalidation is duplicated, forward, or target-detached",
                        ));
                    }
                    canonical_value_sha256(&json!({
                        "domain": "whiel-framework-ii-invalidation-row-v2",
                        "row_ordinal": ordinal,
                        "invalidated_attempt": invalidation.invalidated_attempt,
                        "target": invalidation.target.get(),
                        "cause": invalidation.cause.map(ClauseId::get),
                        "reason": invalidation.reason.identity_name(),
                        "previous_digest": invalidation.previous_digest.as_deref(),
                    }))
                }
            };
            if expected_digest != row.row_digest() {
                return Err(FrameworkIIStateError::InvalidEvidence(
                    "an attempt-ledger row digest is detached from its exact contents",
                ));
            }
        }
        if invalidated_attempts != self.invalidated_attempts {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "the attempt ledger's invalidation index disagrees with its rows",
            ));
        }
        Ok(())
    }
}

fn row_previous_digest(row: &LevelLedgerRow) -> Option<&str> {
    match row {
        LevelLedgerRow::Attempt(attempt) => attempt.previous_digest.as_deref(),
        LevelLedgerRow::Invalidation(invalidation) => invalidation.previous_digest.as_deref(),
    }
}

fn same_ledger_row(left: &LevelLedgerRow, right: &LevelLedgerRow) -> bool {
    match (left, right) {
        (LevelLedgerRow::Attempt(left), LevelLedgerRow::Attempt(right)) => {
            left.row_ordinal == right.row_ordinal
                && same_request(&left.request, &right.request)
                && same_outcome(&left.outcome, &right.outcome)
                && left.previous_digest == right.previous_digest
                && left.row_digest == right.row_digest
        }
        (LevelLedgerRow::Invalidation(left), LevelLedgerRow::Invalidation(right)) => {
            left.row_ordinal == right.row_ordinal
                && left.invalidated_attempt == right.invalidated_attempt
                && left.target == right.target
                && left.cause == right.cause
                && left.reason == right.reason
                && left.previous_digest == right.previous_digest
                && left.row_digest == right.row_digest
        }
        _ => false,
    }
}

fn same_request(left: &FrameworkIICheckRequest, right: &FrameworkIICheckRequest) -> bool {
    left.attempt_ordinal == right.attempt_ordinal
        && left.clause == right.clause
        && left.level == right.level
        && left.role == right.role
        && left.snapshot.same_partition(&right.snapshot)
        && left.identity == right.identity
        && left.request_digest == right.request_digest
}

fn request_identity(
    attempt_ordinal: u64,
    snapshot: &LeveledCandidateSnapshot,
    role: FrameworkIICheckRole,
    clause: ClauseId,
) -> Value {
    json!({
        "kind": "whiel_framework_ii_fixed_ambient_check_request",
        "version": 1,
        "attempt_ordinal": attempt_ordinal,
        "scope_identity": snapshot.scope().identity(),
        "snapshot_identity": snapshot.worker_identity(),
        "selector": worker_selector(role, clause),
    })
}

fn worker_selector(role: FrameworkIICheckRole, clause: ClauseId) -> Value {
    json!({
        "kind": role.identity_name(),
        "clause_id": clause.get(),
    })
}

fn same_outcome(left: &FrameworkIICheckOutcome, right: &FrameworkIICheckOutcome) -> bool {
    match (left, right) {
        (FrameworkIICheckOutcome::Proved(left), FrameworkIICheckOutcome::Proved(right))
        | (FrameworkIICheckOutcome::Refuted(left), FrameworkIICheckOutcome::Refuted(right)) => {
            same_evidence(left, right)
        }
        (
            FrameworkIICheckOutcome::Inconclusive {
                reason: left_reason,
                progress: left,
            },
            FrameworkIICheckOutcome::Inconclusive {
                reason: right_reason,
                progress: right,
            },
        ) => left_reason == right_reason && same_evidence(left, right),
        _ => false,
    }
}

fn same_evidence(left: &FrameworkIICheckEvidence, right: &FrameworkIICheckEvidence) -> bool {
    if left.request_digest != right.request_digest || left.identity != right.identity {
        return false;
    }
    match (&left.authority, &right.authority) {
        (
            FrameworkIICheckAuthority::RuntimeProof(left),
            FrameworkIICheckAuthority::RuntimeProof(right),
        ) => Arc::ptr_eq(left, right),
        (
            FrameworkIICheckAuthority::ProtectedTheoremSelection(left),
            FrameworkIICheckAuthority::ProtectedTheoremSelection(right),
        ) => Arc::ptr_eq(left, right),
        (
            FrameworkIICheckAuthority::ValidatedRefutation(left),
            FrameworkIICheckAuthority::ValidatedRefutation(right),
        ) => Arc::ptr_eq(left, right),
        (FrameworkIICheckAuthority::Progress(left), FrameworkIICheckAuthority::Progress(right)) => {
            Arc::ptr_eq(left, right)
        }
        #[cfg(test)]
        (FrameworkIICheckAuthority::Scripted, FrameworkIICheckAuthority::Scripted) => true,
        _ => false,
    }
}

impl fmt::Display for FrameworkIICheckRole {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.identity_name())
    }
}

fn is_sha256(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}
