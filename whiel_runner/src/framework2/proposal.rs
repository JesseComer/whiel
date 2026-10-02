//! Transactional, provider-neutral fixed-ambient proposal epochs.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::failure::{FailureKind, FailureReport, FailureScope};
use crate::houdini::ClauseId;
use crate::runtime::CancellationToken;

use super::catalog::{
    ExtendedClauseOrigin, FrameworkIIStateError, LeveledClauseCatalog, LeveledClauseRecord,
};
use super::freeze::FrameworkIITerminationProof;
use super::ledger::{FrameworkIICheckOutcome, FrameworkIIInconclusiveReason};
use super::snapshot::{LeveledCandidateSnapshot, LeveledCoreHandle};
use super::stabilization::{
    FrameworkIICheckExecution, FrameworkIIChecker, LeveledHoudiniState,
    LeveledStabilizationOutcome, stabilize_leveled_houdini,
    stabilize_leveled_houdini_under_control,
};
use super::types::ExtendedClause;

// ------------------------------------------------------------
// Exact Proposal Context And Payload
// ------------------------------------------------------------

/// One immutable authorization snapshot for the next proposal epoch.
///
/// Digests remain useful links, but are never the equality authority here.
/// The context retains the exact catalog owner, Core snapshot, and full
/// drop-eligible records.
#[derive(Clone, Debug)]
pub struct FrameworkIIProposalContext {
    catalog: LeveledClauseCatalog,
    proposal_revision: u64,
    expected_registration_ordinal: u64,
    core_snapshot: Arc<LeveledCandidateSnapshot>,
    drop_eligible_records: Arc<[LeveledClauseRecord]>,
}

impl FrameworkIIProposalContext {
    pub fn proposal_revision(&self) -> u64 {
        self.proposal_revision
    }

    pub fn expected_registration_ordinal(&self) -> u64 {
        self.expected_registration_ordinal
    }

    pub fn core_snapshot(&self) -> &Arc<LeveledCandidateSnapshot> {
        &self.core_snapshot
    }

    pub fn drop_eligible_records(&self) -> &[LeveledClauseRecord] {
        &self.drop_eligible_records
    }

    /// Bind one shown eligible record to this exact context and catalog.
    pub fn drop_token(&self, clause: ClauseId) -> Option<FrameworkIIProposalDrop> {
        self.drop_eligible_records
            .iter()
            .find(|record| record.id() == clause)
            .cloned()
            .map(|record| FrameworkIIProposalDrop {
                catalog: self.catalog.clone(),
                proposal_revision: self.proposal_revision,
                expected_registration_ordinal: self.expected_registration_ordinal,
                record,
            })
    }

    pub(super) fn matches_state(
        &self,
        state: &LeveledHoudiniState,
    ) -> Result<bool, FrameworkIIStateError> {
        Ok(self.catalog == *state.catalog()
            && self.proposal_revision == state.proposal_revision()
            && self.expected_registration_ordinal == state.catalog().next_batch_ordinal()?
            && self.core_snapshot.same_partition(state.core().snapshot())
            && self.drop_eligible_records.as_ref() == state.drop_eligible_records()?.as_slice())
    }
}

/// Exact context-bound authority to drop one shown pending candidate.
///
/// Bare numeric ClauseIds are deliberately insufficient because independent
/// catalogs may allocate the same ordinal to different clauses.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FrameworkIIProposalDrop {
    catalog: LeveledClauseCatalog,
    proposal_revision: u64,
    expected_registration_ordinal: u64,
    record: LeveledClauseRecord,
}

impl FrameworkIIProposalDrop {
    pub fn id(&self) -> ClauseId {
        self.record.id()
    }

    pub fn record(&self) -> &LeveledClauseRecord {
        &self.record
    }

    fn matches_context(&self, context: &FrameworkIIProposalContext) -> bool {
        self.catalog == context.catalog
            && self.proposal_revision == context.proposal_revision
            && self.expected_registration_ordinal == context.expected_registration_ordinal
            && context
                .drop_eligible_records
                .iter()
                .any(|record| record == &self.record)
    }
}

impl LeveledHoudiniState {
    /// Capture the exact, single-use context for the next proposal.
    pub fn proposal_context(&self) -> Result<FrameworkIIProposalContext, FrameworkIIStateError> {
        Ok(FrameworkIIProposalContext {
            catalog: self.catalog().clone(),
            proposal_revision: self.proposal_revision(),
            expected_registration_ordinal: self.catalog().next_batch_ordinal()?,
            core_snapshot: Arc::clone(self.core().snapshot()),
            drop_eligible_records: self.drop_eligible_records()?.into(),
        })
    }
}

/// One completely admitted clause proposal.
#[derive(Clone, Debug)]
pub struct FrameworkIIProposalEpoch {
    context: FrameworkIIProposalContext,
    clauses: Arc<[ExtendedClause]>,
    dropped: Arc<[FrameworkIIProposalDrop]>,
}

impl FrameworkIIProposalEpoch {
    pub fn new(
        context: FrameworkIIProposalContext,
        clauses: impl IntoIterator<Item = ExtendedClause>,
        dropped: impl IntoIterator<Item = FrameworkIIProposalDrop>,
    ) -> Result<Self, FrameworkIIStateError> {
        let clauses = clauses.into_iter().collect::<Vec<_>>();
        if clauses
            .iter()
            .any(|clause| clause.scope() != context.catalog.scope())
        {
            return Err(FrameworkIIStateError::WrongScope);
        }
        let mut seen = BTreeMap::<Arc<str>, &ExtendedClause>::new();
        for clause in &clauses {
            let key: Arc<str> = Arc::from(clause.identity_intern_key());
            if let Some(prior) = seen.insert(key, clause)
                && !prior.semantic_metadata_matches(clause)
            {
                return Err(FrameworkIIStateError::ConflictingFormulaMetadata);
            }
        }

        let mut dropped = dropped.into_iter().collect::<Vec<_>>();
        dropped.sort_unstable_by_key(FrameworkIIProposalDrop::id);
        if dropped.windows(2).any(|pair| pair[0].id() == pair[1].id()) {
            return Err(FrameworkIIStateError::InvalidPlacement(
                "a proposal repeats one drop identity",
            ));
        }
        Ok(Self {
            context,
            clauses: clauses.into(),
            dropped: dropped.into(),
        })
    }

    pub fn context(&self) -> &FrameworkIIProposalContext {
        &self.context
    }

    pub fn clauses(&self) -> &[ExtendedClause] {
        &self.clauses
    }

    pub fn dropped(&self) -> &[FrameworkIIProposalDrop] {
        &self.dropped
    }
}

// ------------------------------------------------------------
// Epoch Outcome
// ------------------------------------------------------------

/// What one epoch returns: the outcome of the termination check on the Core
/// the epoch's scan produced.
///
/// A proof ends the run with the frozen Core. A Lean-validated refutation is
/// the normal outcome of an epoch and is reported to the proposer with its
/// countermodel; an inconclusive check is reported as such and relaunched on
/// a later epoch. `Failure` is a run-global infrastructure fault (a worker or
/// solver process, never a solver verdict): the partition is as it was when
/// the epoch began.
#[derive(Clone, Debug)]
pub enum FrameworkIIEpochOutcome {
    /// The termination check on this epoch's Core was proved. The handle
    /// is that exact Core and `termination` is the proof of *that* Core,
    /// which is the only thing that can freeze it (Pass 7.5f).
    Proved {
        core: LeveledCoreHandle,
        termination: FrameworkIITerminationProof,
    },
    /// `attempt` names the checker's own attempt identifier for the
    /// refutation — the id its Lean-validated countermodel is retained
    /// under and the `countermodel` tool serves. A dictionary reuse names
    /// the original launching attempt, which is where the countermodel
    /// lives. `None` only when the checker published no validated
    /// refutation receipt (deterministic unit-test adapters), in which case
    /// no countermodel is addressable.
    Refuted {
        attempt: Option<u64>,
    },
    Inconclusive {
        reason: FrameworkIIInconclusiveReason,
    },
    /// The run's own cancellation token stopped this epoch. Nothing was
    /// learned about the postcondition, so this is not a
    /// `postcondition_open` event: the search stops here.
    Cancelled,
    Failure(FailureReport),
}

/// One epoch's outcome together with the identities its proposal submitted.
#[derive(Clone, Debug)]
pub struct FrameworkIIEpochResult {
    outcome: FrameworkIIEpochOutcome,
    submitted: Arc<[ClauseId]>,
}

impl FrameworkIIEpochResult {
    pub fn outcome(&self) -> &FrameworkIIEpochOutcome {
        &self.outcome
    }

    pub fn into_outcome(self) -> FrameworkIIEpochOutcome {
        self.outcome
    }

    /// The exact ClauseIds this epoch registered from its submission
    /// (freshly admitted clauses plus repeated ones), in ascending order.
    pub fn submitted(&self) -> &[ClauseId] {
        &self.submitted
    }

    /// The submitted identities this epoch produced a per-clause outcome
    /// for, in ascending order — what the next push may report as its
    /// `last_round`.
    ///
    /// Empty for a `Failure`. Every path that returns `Failure` rolls the
    /// epoch back onto the partition it began with, so the batch has no
    /// committed, dead, or pending outcome of its own, and
    /// `agent_houdini.tex` gives `last_round` exactly those three outcomes
    /// and no fourth. What the next push says about a rolled-back round is
    /// its `failure` event, after which the search continues (the report's
    /// "Search termination" paragraph); reporting the batch anyway would
    /// describe the epoch's start as though the epoch had applied.
    pub fn round_outcomes(&self) -> &[ClauseId] {
        if matches!(self.outcome, FrameworkIIEpochOutcome::Failure(_)) {
            &[]
        } else {
            &self.submitted
        }
    }
}

// ------------------------------------------------------------
// Transactional Epoch Coordinator
// ------------------------------------------------------------

/// Run one epoch: apply the drops, intern the batch, return every pending
/// clause to its minimum level, clear the epoch's suspension set, run one
/// bottom-up scan, then run the termination check on the resulting Core and
/// return its outcome.
///
/// A proposal may be empty, may repeat clauses, or may consist of drops
/// alone; the controller does not police the proposer's use of epochs, and an
/// epoch that changes no initialization premise is served level for level by
/// the checker's semantic dictionary.
///
/// The epoch is **atomic against infrastructure faults** (`houdini.tex`
/// Algorithm 1): an epoch that returns `Failure` leaves the partition as it
/// was when the epoch began. Proposal installation is still published as a
/// checkpoint before solver work — the catalog batch and the state half go in
/// together, so the two never disagree — but a failing epoch is rolled back
/// onto the partition it began with
/// ([`LeveledHoudiniState::rollback_epoch`]), so its drops, its freshly
/// admitted clauses, its levels, its `Fresh` marks and its `Susp` set are all
/// undone and the next push reports the partition as of the epoch's start.
/// Only the catalog's content-addressed records and the ledger's rows
/// survive, as provenance; an exact resubmission re-admits a rolled-back
/// clause identically and it is fresh again. A cancellation is not an
/// infrastructure fault and keeps its own rule below.
///
/// This holds of *every* path that returns `Failure`, not only of a failing
/// scan: a fault in activating or publishing the epoch's work takes the
/// same rollback ([`rolled_back_epoch_failure`]), and the two faults before
/// the checkpoint is published have no epoch to undo. So a `Failure` result
/// carries no per-clause outcome for its batch at all
/// ([`FrameworkIIEpochResult::round_outcomes`]).
///
/// A rollback rather than a deferred checkpoint because the checkpoint is one
/// in-process owner, not a separate durable write: the catalog transaction
/// publishes the state half inside its own lock, so there is no window in
/// which a partial epoch could be observed and nothing for a rollback marker
/// to guard. Deferring the state half until stabilization succeeded would
/// instead open that window, leaving the catalog holding a batch the
/// partition does not know about for the whole of the epoch's solver work.
pub async fn run_framework_ii_proposal_epoch<C: FrameworkIIChecker + ?Sized>(
    state: &mut LeveledHoudiniState,
    checker: &mut C,
    proposal: FrameworkIIProposalEpoch,
) -> Result<FrameworkIIEpochResult, FrameworkIIStateError> {
    run_framework_ii_proposal_epoch_inner(state, checker, proposal, None).await
}

/// Search-owned proposal entry whose publications share the run deadline.
pub(super) async fn run_framework_ii_proposal_epoch_under_control<
    C: FrameworkIIChecker + ?Sized,
>(
    state: &mut LeveledHoudiniState,
    checker: &mut C,
    proposal: FrameworkIIProposalEpoch,
    control: &CancellationToken,
) -> Result<FrameworkIIEpochResult, FrameworkIIStateError> {
    tokio::task::yield_now().await;
    run_framework_ii_proposal_epoch_inner(state, checker, proposal, Some(control)).await
}

async fn run_framework_ii_proposal_epoch_inner<C: FrameworkIIChecker + ?Sized>(
    state: &mut LeveledHoudiniState,
    checker: &mut C,
    proposal: FrameworkIIProposalEpoch,
    control: Option<&CancellationToken>,
) -> Result<FrameworkIIEpochResult, FrameworkIIStateError> {
    require_control_open(control)?;
    preflight_proposal(state, &proposal)?;
    require_control_open(control)?;
    // One epoch, one launch per semantic key: the checker's per-epoch
    // launched-key set is cleared exactly here, at the epoch's start,
    // before any check. Compression's re-stabilization does not reopen an
    // epoch; it belongs to the epoch that triggered it.
    checker.begin_epoch();

    // The partition this epoch is about to change, retained so that an
    // infrastructure fault can put it back exactly (`houdini.tex`
    // Algorithm 1). Taken before the drops are applied and before the batch
    // is interned, so it is the epoch's start in the contract's sense.
    let epoch_start = state.epoch_rollback_point();

    let dropped = proposal
        .dropped
        .iter()
        .map(FrameworkIIProposalDrop::id)
        .collect::<BTreeSet<_>>();
    let checkpoint = match state.prepare_proposal_checkpoint(&dropped) {
        Ok(checkpoint) => checkpoint,
        Err(error) => return Ok(epoch_failure(state_failure(error), Arc::from([]))),
    };

    let catalog = state.catalog().clone();
    let registered = match catalog.register_batch_transaction(
        proposal.context.expected_registration_ordinal,
        proposal
            .clauses
            .iter()
            .cloned()
            .map(|clause| (clause, ExtendedClauseOrigin::Submitted)),
        || require_control_open(control),
        |registered| state.publish_proposal_checkpoint(checkpoint, registered),
    ) {
        Ok(registered) => registered,
        Err(error) => return Ok(epoch_failure(state_failure(error), Arc::from([]))),
    };
    let submitted: Arc<[ClauseId]> = registered
        .ids()
        .iter()
        .copied()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();

    // The checkpoint is published by now, so a fault between it and the
    // scan has an epoch to undo: it takes the same rollback as a failing
    // scan, since it too returns `Failure`.
    let mut work = match state.activate_proposal_work() {
        Ok(work) => work,
        Err(error) => return rolled_back_epoch_failure(state, epoch_start, error, submitted),
    };

    let stabilization = match control {
        Some(control) => stabilize_leveled_houdini_under_control(&mut work, checker, control).await,
        None => stabilize_leveled_houdini(&mut work, checker).await,
    };
    require_control_open(control)?;
    match stabilization {
        Ok(LeveledStabilizationOutcome::Stabilized(_)) => {
            require_control_open(control)?;
            // Publishing the stabilized work consumes it, so a fault here
            // has no staged owner left to roll back from; the rollback runs
            // against the published checkpoint, which is what the epoch
            // installed and what has to go away.
            match state.publish_advanced_proposal_work(work) {
                Ok(true) => {}
                Ok(false) => {
                    return rolled_back_epoch_failure(
                        state,
                        epoch_start,
                        FrameworkIIStateError::InvalidEvidence(
                            "stabilized proposal work did not advance its durable checkpoint",
                        ),
                        submitted,
                    );
                }
                Err(error) => {
                    return rolled_back_epoch_failure(state, epoch_start, error, submitted);
                }
            }
            let outcome = run_termination_check(state, checker, control).await?;
            // The termination check is part of the epoch, so an
            // infrastructure fault in it aborts the epoch and takes the same
            // rollback: the partition goes back to the epoch's start even
            // though the scan itself had already stabilized.
            if matches!(outcome, FrameworkIIEpochOutcome::Failure(_)) {
                let published = state.epoch_rollback_point();
                state.rollback_epoch(epoch_start, published)?;
            }
            Ok(FrameworkIIEpochResult { outcome, submitted })
        }
        Ok(LeveledStabilizationOutcome::Failure(report)) => {
            require_control_open(control)?;
            state.rollback_epoch(epoch_start, work)?;
            Ok(epoch_failure(report, submitted))
        }
        Err(FrameworkIIStateError::Cancelled) => {
            require_control_open(control)?;
            preserve_advanced_work(state, work)?;
            Ok(FrameworkIIEpochResult {
                outcome: FrameworkIIEpochOutcome::Cancelled,
                submitted,
            })
        }
        // A typed state error aborts the epoch exactly as an infrastructure
        // fault does, and it too returns `Failure` to the proposer, so it
        // takes the same rollback: an epoch never ends half applied.
        Err(error) => {
            require_control_open(control)?;
            state.rollback_epoch(epoch_start, work)?;
            Ok(epoch_failure(state_failure(error), submitted))
        }
    }
}

/// Run the termination check on the epoch's Core, as an ordinary request.
///
/// Nothing about the pending clauses gates this check: it runs after every
/// epoch, and an epoch that did not change the Core's clause set is answered
/// from the checker's dictionary without a launch.
async fn run_termination_check<C: FrameworkIIChecker + ?Sized>(
    state: &mut LeveledHoudiniState,
    checker: &mut C,
    control: Option<&CancellationToken>,
) -> Result<FrameworkIIEpochOutcome, FrameworkIIStateError> {
    let core = Arc::clone(state.core().snapshot());
    state.count_termination_attempt();
    let completed = checker.check_termination(Arc::clone(&core)).await;
    state.record_replay_termination(core, &completed);
    let execution = match completed {
        Ok(execution) => execution,
        Err(FrameworkIIStateError::Cancelled) => {
            return Ok(FrameworkIIEpochOutcome::Cancelled);
        }
        Err(error) => return Ok(FrameworkIIEpochOutcome::Failure(state_failure(error))),
    };
    if control.is_some_and(CancellationToken::should_stop) {
        return Ok(FrameworkIIEpochOutcome::Cancelled);
    }
    Ok(match execution {
        FrameworkIICheckExecution::Failure(report) => FrameworkIIEpochOutcome::Failure(report),
        FrameworkIICheckExecution::Applied(FrameworkIICheckOutcome::Proved(evidence)) => {
            // The proof is built from the proved evidence itself, so this
            // arm has no failure to report: a refutation or an inconclusive
            // outcome takes one of the arms below and never reaches here.
            let core = state.core().clone();
            let termination = FrameworkIITerminationProof::proved(&core, &evidence);
            FrameworkIIEpochOutcome::Proved { core, termination }
        }
        FrameworkIICheckExecution::Applied(FrameworkIICheckOutcome::Refuted(evidence)) => {
            // The countermodel is retained by the checker under the
            // launching attempt's identifier; a reuse carries the original
            // attempt's receipt, which is exactly where it lives.
            FrameworkIIEpochOutcome::Refuted {
                attempt: evidence
                    .validated_refutation()
                    .map(|refutation| refutation.attempt().get()),
            }
        }
        // A cancelled termination check learned nothing about the
        // postcondition either, so it stops the search rather than
        // reporting the postcondition still open.
        FrameworkIICheckExecution::Applied(FrameworkIICheckOutcome::Inconclusive {
            reason: FrameworkIIInconclusiveReason::Cancelled,
            ..
        }) => FrameworkIIEpochOutcome::Cancelled,
        FrameworkIICheckExecution::Applied(FrameworkIICheckOutcome::Inconclusive {
            reason,
            ..
        }) => FrameworkIIEpochOutcome::Inconclusive { reason },
    })
}

/// Roll one epoch back onto the partition it began with and report the
/// typed fault that aborted it.
///
/// The route for the two faults that have no staged owner to abandon —
/// activating the work and publishing it — so that *every* path returning
/// `Failure` leaves the partition as it was when the epoch began. Both are
/// run-global invariant violations rather than ordinary infrastructure
/// faults, so what this changes is only the state the run records; the
/// contract's atomicity claim then holds without an exception.
///
/// Neither call site is reachable from a well-formed run — activating the
/// work fails only for a pending clause the catalog does not hold, and
/// publishing it reports "did not advance" only for a scan that published
/// no transition, which every successful scan does — so this route is
/// tested directly rather than through an epoch that provokes one of them.
pub(super) fn rolled_back_epoch_failure(
    state: &mut LeveledHoudiniState,
    epoch_start: LeveledHoudiniState,
    error: FrameworkIIStateError,
    submitted: Arc<[ClauseId]>,
) -> Result<FrameworkIIEpochResult, FrameworkIIStateError> {
    let published = state.epoch_rollback_point();
    state.rollback_epoch(epoch_start, published)?;
    Ok(epoch_failure(state_failure(error), submitted))
}

fn epoch_failure(report: FailureReport, submitted: Arc<[ClauseId]>) -> FrameworkIIEpochResult {
    FrameworkIIEpochResult {
        outcome: FrameworkIIEpochOutcome::Failure(report),
        submitted,
    }
}

fn require_control_open(control: Option<&CancellationToken>) -> Result<(), FrameworkIIStateError> {
    if control.is_some_and(CancellationToken::should_stop) {
        Err(FrameworkIIStateError::Cancelled)
    } else {
        Ok(())
    }
}

fn preflight_proposal(
    state: &LeveledHoudiniState,
    proposal: &FrameworkIIProposalEpoch,
) -> Result<(), FrameworkIIStateError> {
    if !proposal.context.matches_state(state)? {
        return Err(FrameworkIIStateError::InvalidEvidence(
            "a proposal context is stale, cross-task, or structurally mismatched",
        ));
    }
    let eligible = proposal
        .context
        .drop_eligible_records
        .iter()
        .map(LeveledClauseRecord::id)
        .collect::<BTreeSet<_>>();
    let dropped = proposal
        .dropped
        .iter()
        .map(FrameworkIIProposalDrop::id)
        .collect::<BTreeSet<_>>();
    if proposal.dropped.len() != dropped.len() {
        return Err(FrameworkIIStateError::InvalidPlacement(
            "a proposal repeats one drop identity",
        ));
    }
    for drop in proposal.dropped.iter() {
        if !drop.matches_context(&proposal.context) {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "a proposal drop token belongs to another catalog or proposal context",
            ));
        }
        let Some(expected) = proposal
            .context
            .drop_eligible_records
            .iter()
            .find(|record| record.id() == drop.id())
        else {
            return Err(FrameworkIIStateError::InvalidPlacement(
                "a proposal drop is stale, settled, or otherwise ineligible",
            ));
        };
        let current = state.catalog().record(drop.id())?;
        if expected != drop.record() || &current != drop.record() || !eligible.contains(&drop.id())
        {
            return Err(FrameworkIIStateError::InvalidEvidence(
                "a proposal drop token does not retain the exact eligible catalog record",
            ));
        }
    }

    for clause in proposal.clauses.iter() {
        if clause.scope() != state.catalog().scope() {
            return Err(FrameworkIIStateError::WrongScope);
        }
        // A clause whose Lean-owned minimum level exceeds the run's optional
        // level bound is rejected at admission, never parked: Lean assigns
        // the minimum level and knows no bound.
        if state.exceeds_level_bound(clause.minimum_level()) {
            return Err(FrameworkIIStateError::LevelBoundExceeded {
                clause: state.catalog().find(clause)?,
                minimum_level: clause.minimum_level().get(),
                max_level: state
                    .max_level()
                    .map(super::types::FrameworkIILevel::get)
                    .unwrap_or_default(),
            });
        }
        if let Some(existing) = state.catalog().find(clause)? {
            let record = state.catalog().record(existing)?;
            if !record.formula().semantic_metadata_matches(clause) {
                return Err(FrameworkIIStateError::ConflictingFormulaMetadata);
            }
            if dropped.contains(&existing) {
                return Err(FrameworkIIStateError::InvalidPlacement(
                    "one proposal both drops and submits the same exact formula",
                ));
            }
            // A clause dead by refutation never revives: a resubmission is
            // rejected fail-closed here with its exact reason. A clause dead
            // by drop is revived by exactly this resubmission instead.
            if let Some(reason) = state.dead_reason(existing) {
                return Err(FrameworkIIStateError::DeadClauseRejected {
                    clause: existing,
                    reason,
                });
            }
        }
    }
    Ok(())
}

fn preserve_advanced_work(
    state: &mut LeveledHoudiniState,
    work: LeveledHoudiniState,
) -> Result<(), FrameworkIIStateError> {
    state.publish_advanced_proposal_work(work).map(|_| ())
}

fn state_failure(error: FrameworkIIStateError) -> FailureReport {
    FailureReport::encoding_preparation(
        FailureKind::InfrastructureFailure,
        FailureScope::RunGlobal,
        error.to_string(),
    )
}
