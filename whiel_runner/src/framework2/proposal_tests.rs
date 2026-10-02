use std::collections::{BTreeSet, VecDeque};
use std::future::Future;
use std::pin::Pin;
use std::sync::{Arc, Mutex};

use serde_json::{Value, json};

use super::proposal::{
    FrameworkIIEpochOutcome, FrameworkIIEpochResult, FrameworkIIProposalDrop,
    FrameworkIIProposalEpoch, rolled_back_epoch_failure, run_framework_ii_proposal_epoch,
    run_framework_ii_proposal_epoch_under_control,
};
use super::types::FrameworkIIRelation;
use super::*;
use crate::failure::{FailureKind, FailureOrigin, FailureReport, FailureScope};
use crate::houdini::ClauseId;
use crate::runtime::CancellationToken;
use crate::task::SynthesisTask;

fn proposal_test_task() -> SynthesisTask {
    SynthesisTask::from_json(
        r#"{
          "format_version":3,
          "semantic_version":1,
          "encoding_version":1,
          "identity":{
            "canonical_id":"FrameworkIIProposalTest",
            "module":"Whiel.Test.FrameworkIIProposalTest",
            "namespace":"Whiel.Test.FrameworkIIProposalTest",
            "source_sha256":"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
          },
          "schema":{"expression":"Whiel.Test.FrameworkIIProposalTest.programSchema","display":"{R}"},
          "original":{
            "pre":{"expression":"Whiel.Test.FrameworkIIProposalTest.inputPre","display":"true"},
            "command":{"expression":"Whiel.Test.FrameworkIIProposalTest.inputCmd","display":"SKIP"},
            "post":{"expression":"Whiel.Test.FrameworkIIProposalTest.inputPost","display":"true"}
          },
          "preprocessed":{
            "pre":{"expression":"Whiel.Test.FrameworkIIProposalTest.inputPreproc.loopPre","display":"true"},
            "command":{"expression":"Whiel.Test.FrameworkIIProposalTest.inputPreproc.loopCmd","display":"SKIP"},
            "post":{"expression":"Whiel.Test.FrameworkIIProposalTest.inputPreproc.loopPost","display":"true"}
          },
          "preprocessing_evidence":{"expression":"Whiel.Test.FrameworkIIProposalTest.inputPreproc"},
          "solver":{
            "schema_relations":[{"key":"rel:R:0","arity":1}],
            "task_constants":[],
            "preprocessed_pre":{
              "source_id":"task.preprocessed_pre",
              "expression":"Whiel.Test.FrameworkIIProposalTest.inputPreproc.loopPre",
              "no_bound_expression":"Whiel.Test.FrameworkIIProposalTest.inputPreproc.loopPre_noBound",
              "constants":[],"relations":[]
            },
            "preprocessed_post":{
              "source_id":"task.preprocessed_post",
              "expression":"Whiel.Test.FrameworkIIProposalTest.inputPreproc.loopPost",
              "no_bound_expression":"Whiel.Test.FrameworkIIProposalTest.inputPreproc.loopPost_noBound",
              "constants":[],"relations":[]
            },
            "loop_guard":{"source_id":"task.loop_guard","constants":[],"relations":[]},
            "negated_loop_guard":{"source_id":"task.negated_loop_guard","constants":[],"relations":[]}
          }
        }"#,
    )
    .unwrap()
}

fn proposal_scope(marker: &str) -> FixedAmbientTaskScope {
    let task = proposal_test_task();
    let source = FrameworkIIRelation::new(
        task.solver_relations()[0].key().clone(),
        task.solver_relations()[0].arity(),
    );
    FixedAmbientTaskScope::new(
        task.identity().clone(),
        json!(["framework-ii-proposal-test-scope", marker]),
        json!([]),
        vec![source.clone()],
        vec![source],
        Vec::new(),
    )
}

/// Prophecy-bearing by default, so a scripted initialization refutation
/// promotes the clause rather than killing it. Use
/// [`proposal_clause_prophecy_free`] for a clause exercising the death
/// rule.
fn proposal_clause(
    scope: &FixedAmbientTaskScope,
    identity: &str,
    order_key: &str,
    minimum_level: FrameworkIILevel,
) -> ExtendedClause {
    proposal_clause_with_prophecy(scope, identity, order_key, minimum_level, true)
}

/// A clause whose admitted formula mentions no prophecy relation: while it
/// has never been committed, a Lean-validated initialization refutation at
/// any level makes it dead instead of promoting it.
fn proposal_clause_prophecy_free(
    scope: &FixedAmbientTaskScope,
    identity: &str,
    order_key: &str,
    minimum_level: FrameworkIILevel,
) -> ExtendedClause {
    proposal_clause_with_prophecy(scope, identity, order_key, minimum_level, false)
}

fn proposal_clause_with_prophecy(
    scope: &FixedAmbientTaskScope,
    identity: &str,
    order_key: &str,
    minimum_level: FrameworkIILevel,
    mentions_prophecy: bool,
) -> ExtendedClause {
    let formula_identity = json!(["proposal-clause", order_key, identity]);
    ExtendedClause::new(
        scope.clone(),
        formula_identity.clone(),
        serde_json::to_string(&formula_identity).unwrap(),
        identity.to_string(),
        vec!["rel:R:0".to_string()],
        mentions_prophecy,
        minimum_level,
    )
}

fn proposal_catalog(scope: &FixedAmbientTaskScope, marker: char) -> LeveledClauseCatalog {
    LeveledClauseCatalog::new(scope.clone(), marker.to_string().repeat(64)).unwrap()
}

fn proposal_proved(request: &FrameworkIICheckRequest) -> FrameworkIICheckOutcome {
    FrameworkIICheckOutcome::Proved(
        FrameworkIICheckEvidence::new(
            request.request_digest(),
            format!("proposal-proof:{}", request.request_digest()),
        )
        .unwrap(),
    )
}

fn proposal_refuted(request: &FrameworkIICheckRequest) -> FrameworkIICheckOutcome {
    FrameworkIICheckOutcome::Refuted(
        FrameworkIICheckEvidence::new(
            request.request_digest(),
            format!("proposal-refutation:{}", request.request_digest()),
        )
        .unwrap(),
    )
}

fn proposal_inconclusive(
    request: &FrameworkIICheckRequest,
    reason: FrameworkIIInconclusiveReason,
) -> FrameworkIICheckOutcome {
    FrameworkIICheckOutcome::Inconclusive {
        reason,
        progress: FrameworkIICheckEvidence::new(
            request.request_digest(),
            format!("proposal-progress:{}", request.request_digest()),
        )
        .unwrap(),
    }
}

fn proposal_failure() -> FailureReport {
    FailureReport::try_new(
        FailureOrigin::EncodingPreparation,
        FailureKind::InfrastructureFailure,
        true,
        FailureScope::RunGlobal,
        Some("typed proposal-epoch failure".to_string()),
        Vec::new(),
    )
    .unwrap()
}

/// The scripted termination checks of one fake checker: what every
/// `check_termination` call saw, and what it answers next.
#[derive(Default)]
struct TerminationScript {
    core_snapshots: Vec<Arc<LeveledCandidateSnapshot>>,
    steps: VecDeque<ProposalScriptStep>,
}

impl TerminationScript {
    fn calls(&self) -> usize {
        self.core_snapshots.len()
    }
}

struct ProposalExecutionChecker<F> {
    checker: F,
    /// The termination check answers `Refuted` unless a test scripts
    /// otherwise, which is the ordinary outcome of an epoch.
    termination: Arc<Mutex<TerminationScript>>,
}

impl<F> ProposalExecutionChecker<F> {
    fn new(checker: F) -> Self {
        Self {
            checker,
            termination: Arc::new(Mutex::new(TerminationScript::default())),
        }
    }

    fn termination(&self) -> Arc<Mutex<TerminationScript>> {
        Arc::clone(&self.termination)
    }
}

fn termination_evidence() -> FrameworkIICheckEvidence {
    FrameworkIICheckEvidence::new("c".repeat(64), "proposal-termination").unwrap()
}

fn termination_execution(
    step: ProposalScriptStep,
) -> Result<FrameworkIICheckExecution, FrameworkIIStateError> {
    Ok(match step {
        ProposalScriptStep::Proved => FrameworkIICheckExecution::Applied(
            FrameworkIICheckOutcome::Proved(termination_evidence()),
        ),
        ProposalScriptStep::Refuted => FrameworkIICheckExecution::Applied(
            FrameworkIICheckOutcome::Refuted(termination_evidence()),
        ),
        ProposalScriptStep::Inconclusive(reason) => {
            FrameworkIICheckExecution::Applied(FrameworkIICheckOutcome::Inconclusive {
                reason,
                progress: termination_evidence(),
            })
        }
        ProposalScriptStep::Failure(report) => FrameworkIICheckExecution::Failure(report),
        ProposalScriptStep::Cancelled => return Err(FrameworkIIStateError::Cancelled),
    })
}

impl<F> super::stabilization::sealed::Sealed for ProposalExecutionChecker<F> {}

impl<F> FrameworkIIChecker for ProposalExecutionChecker<F>
where
    F: FnMut(FrameworkIICheckRequest) -> Result<FrameworkIICheckExecution, FrameworkIIStateError>
        + Send,
{
    fn check<'a>(
        &'a mut self,
        request: FrameworkIICheckRequest,
    ) -> Pin<
        Box<
            dyn Future<Output = Result<FrameworkIICheckExecution, FrameworkIIStateError>>
                + Send
                + 'a,
        >,
    > {
        Box::pin(std::future::ready((self.checker)(request)))
    }

    fn check_termination<'a>(
        &'a mut self,
        core: Arc<LeveledCandidateSnapshot>,
    ) -> Pin<
        Box<
            dyn Future<Output = Result<FrameworkIICheckExecution, FrameworkIIStateError>>
                + Send
                + 'a,
        >,
    > {
        let step = {
            let mut script = self.termination.lock().unwrap();
            script.core_snapshots.push(core);
            script.steps.pop_front()
        };
        Box::pin(std::future::ready(termination_execution(
            step.unwrap_or(ProposalScriptStep::Refuted),
        )))
    }
}

#[derive(Clone, Debug)]
enum ProposalScriptStep {
    Proved,
    Refuted,
    Inconclusive(FrameworkIIInconclusiveReason),
    Failure(FailureReport),
    Cancelled,
}

type ProposalCheckClosure = Box<
    dyn FnMut(FrameworkIICheckRequest) -> Result<FrameworkIICheckExecution, FrameworkIIStateError>
        + Send,
>;

fn scripted_checker(
    steps: impl IntoIterator<Item = ProposalScriptStep>,
) -> (
    ProposalExecutionChecker<ProposalCheckClosure>,
    Arc<Mutex<Vec<FrameworkIICheckRequest>>>,
) {
    let mut steps = steps.into_iter().collect::<VecDeque<_>>();
    let requests = Arc::new(Mutex::new(Vec::new()));
    let captured = Arc::clone(&requests);
    let checker: ProposalCheckClosure = Box::new(move |request: FrameworkIICheckRequest| {
        captured.lock().unwrap().push(request.clone());
        // Model the production checker: a clause the controller already
        // suspended this epoch is still checked, but with no dictionary
        // behind this fake there is nothing to answer it with and no
        // launch is permitted, so it consumes no script step.
        if request.launch_suppressed() {
            return Ok(FrameworkIICheckExecution::Applied(proposal_inconclusive(
                &request,
                FrameworkIIInconclusiveReason::Suspended,
            )));
        }
        match steps.pop_front().unwrap_or(ProposalScriptStep::Proved) {
            ProposalScriptStep::Proved => Ok(FrameworkIICheckExecution::Applied(proposal_proved(
                &request,
            ))),
            ProposalScriptStep::Refuted => Ok(FrameworkIICheckExecution::Applied(
                proposal_refuted(&request),
            )),
            ProposalScriptStep::Inconclusive(reason) => Ok(FrameworkIICheckExecution::Applied(
                proposal_inconclusive(&request, reason),
            )),
            ProposalScriptStep::Failure(report) => Ok(FrameworkIICheckExecution::Failure(report)),
            ProposalScriptStep::Cancelled => Err(FrameworkIIStateError::Cancelled),
        }
    });
    (ProposalExecutionChecker::new(checker), requests)
}

fn registered_submitted(
    catalog: &LeveledClauseCatalog,
    batch_ordinal: u64,
    clauses: impl IntoIterator<Item = ExtendedClause>,
) -> RegisteredLeveledClauses {
    catalog
        .register_batch(
            batch_ordinal,
            clauses
                .into_iter()
                .map(|clause| (clause, ExtendedClauseOrigin::Submitted)),
        )
        .unwrap()
}

fn current_root_rows(state: &LeveledHoudiniState) -> Vec<(ClauseId, FrameworkIICheckRole, u64)> {
    let mut roots = Vec::new();
    for clause in state.committed_levels().keys().copied() {
        for role in [
            FrameworkIICheckRole::Initialization,
            FrameworkIICheckRole::Maintenance,
        ] {
            if let Some(root) = state.current_root(clause, role) {
                roots.push((clause, role, root.attempt_row()));
            }
        }
    }
    roots
}

fn attempt_row_digests(state: &LeveledHoudiniState) -> Vec<String> {
    state
        .attempts()
        .rows()
        .iter()
        .map(|row| row.row_digest().to_string())
        .collect()
}

fn committed_members(state: &LeveledHoudiniState) -> BTreeSet<ClauseId> {
    state.committed_levels().keys().copied().collect()
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ProposalStateFingerprint {
    catalog_instance_digest: String,
    catalog_scope_identity: Value,
    catalog_records: Vec<LeveledClauseRecord>,
    catalog_len: usize,
    next_batch_ordinal: u64,
    proposal_revision: u64,
    core_digest: String,
    partition_digest: String,
    committed: Vec<(ClauseId, FrameworkIILevel)>,
    pending: Vec<(ClauseId, FrameworkIILevel)>,
    dead: Vec<(ClauseId, FrameworkIIDeadCause)>,
    ledger_rows: Vec<String>,
    current_roots: Vec<(ClauseId, FrameworkIICheckRole, u64)>,
}

impl ProposalStateFingerprint {
    fn capture(state: &LeveledHoudiniState) -> Self {
        let catalog_len = state.catalog().len().unwrap();
        Self {
            catalog_instance_digest: state.catalog().instance_digest().to_string(),
            catalog_scope_identity: state.catalog().scope().identity().clone(),
            catalog_records: (0..catalog_len)
                .map(|ordinal| {
                    state
                        .catalog()
                        .record(ClauseId::from_catalog_ordinal(ordinal as u64))
                        .unwrap()
                })
                .collect(),
            catalog_len,
            next_batch_ordinal: state.catalog().next_batch_ordinal().unwrap(),
            proposal_revision: state.proposal_revision(),
            core_digest: state.core().core_digest().to_string(),
            partition_digest: state.core().snapshot().partition_digest().to_string(),
            committed: state
                .committed_levels()
                .iter()
                .map(|(clause, level)| (*clause, *level))
                .collect(),
            pending: state
                .pending_levels()
                .iter()
                .map(|(clause, level)| (*clause, *level))
                .collect(),
            dead: state
                .dead()
                .iter()
                .map(|(clause, cause)| (*clause, *cause))
                .collect(),
            ledger_rows: attempt_row_digests(state),
            current_roots: current_root_rows(state),
        }
    }
}

async fn run_proposal<C: FrameworkIIChecker + ?Sized>(
    state: &mut LeveledHoudiniState,
    checker: &mut C,
    clauses: impl IntoIterator<Item = ExtendedClause>,
    dropped: impl IntoIterator<Item = FrameworkIIProposalDrop>,
) -> Result<FrameworkIIEpochResult, FrameworkIIStateError> {
    let proposal = FrameworkIIProposalEpoch::new(state.proposal_context()?, clauses, dropped)?;
    run_framework_ii_proposal_epoch(state, checker, proposal).await
}

/// Assert that an epoch ran its scan and reported the termination check's
/// refutation, which is the ordinary outcome of an epoch.
fn assert_postcondition_open(result: &FrameworkIIEpochResult) {
    assert!(
        matches!(result.outcome(), FrameworkIIEpochOutcome::Refuted { .. }),
        "expected a refuted termination check: {:?}",
        result.outcome()
    );
}

#[tokio::test]
async fn proposal_epoch_registers_deduplicates_and_honors_minimum_levels() {
    let scope = proposal_scope("registration");
    let catalog = proposal_catalog(&scope, '1');
    let alpha = proposal_clause(&scope, "alpha", "01-alpha", FrameworkIILevel::ZERO);
    let beta = proposal_clause(&scope, "beta", "02-beta", FrameworkIILevel::ZERO);
    let higher = proposal_clause(&scope, "higher", "03-higher", FrameworkIILevel::ONE);
    let mut state = LeveledHoudiniState::new(catalog).unwrap();
    let (mut checker, requests) = scripted_checker([]);

    let outcome = run_proposal(
        &mut state,
        &mut checker,
        [beta.clone(), higher.clone(), alpha.clone()],
        [],
    )
    .await
    .unwrap();
    assert_postcondition_open(&outcome);

    let alpha_id = state.catalog().find(&alpha).unwrap().unwrap();
    let beta_id = state.catalog().find(&beta).unwrap().unwrap();
    let higher_id = state.catalog().find(&higher).unwrap().unwrap();
    assert_eq!([alpha_id.get(), beta_id.get(), higher_id.get()], [0, 1, 2]);
    assert_eq!(
        state.committed_levels().get(&alpha_id),
        Some(&FrameworkIILevel::ZERO)
    );
    assert_eq!(
        state.committed_levels().get(&beta_id),
        Some(&FrameworkIILevel::ZERO)
    );
    assert_eq!(
        state.committed_levels().get(&higher_id),
        Some(&FrameworkIILevel::ONE)
    );
    assert!(
        state
            .proposal_context()
            .unwrap()
            .drop_token(alpha_id)
            .is_none(),
        "committed Core members never produce drop authority"
    );
    assert!(
        requests
            .lock()
            .unwrap()
            .iter()
            .filter(|request| request.clause() == higher_id)
            .all(|request| request.level() == FrameworkIILevel::ONE)
    );

    let stable_ledger = attempt_row_digests(&state);
    let (mut duplicate_checker, duplicate_requests) = scripted_checker([]);
    let duplicate_outcome = run_proposal(&mut state, &mut duplicate_checker, [alpha.clone()], [])
        .await
        .unwrap();
    assert_postcondition_open(&duplicate_outcome);
    assert_eq!(state.catalog().find(&alpha).unwrap(), Some(alpha_id));
    assert_eq!(state.catalog().len().unwrap(), 3);
    assert_eq!(state.catalog().next_batch_ordinal().unwrap(), 2);
    assert_eq!(
        attempt_row_digests(&state),
        stable_ledger,
        "a repeated proposal issues no check and appends no ledger row"
    );
    assert!(duplicate_requests.lock().unwrap().is_empty());
}

#[tokio::test]
async fn controlled_proposal_epoch_rejects_expired_run_before_any_checkpoint() {
    let scope = proposal_scope("expired-control");
    let catalog = proposal_catalog(&scope, 'd');
    let alpha = proposal_clause(&scope, "alpha", "alpha", FrameworkIILevel::ZERO);
    let mut state = LeveledHoudiniState::new(catalog).unwrap();
    let before = ProposalStateFingerprint::capture(&state);
    let proposal =
        FrameworkIIProposalEpoch::new(state.proposal_context().unwrap(), [alpha], []).unwrap();
    let (mut checker, requests) = scripted_checker([]);
    let control = CancellationToken::new();
    let deadline = tokio::time::Instant::now();
    assert!(control.bind_absolute_deadline(deadline));

    assert_eq!(
        run_framework_ii_proposal_epoch_under_control(
            &mut state,
            &mut checker,
            proposal,
            &control,
        )
        .await
        .unwrap_err(),
        FrameworkIIStateError::Cancelled
    );
    assert!(control.should_stop());
    assert!(!control.is_cancelled());
    assert_eq!(ProposalStateFingerprint::capture(&state), before);
    assert!(requests.lock().unwrap().is_empty());
}

#[tokio::test]
async fn finite_refutation_promotes_without_becoming_a_permanent_rejection() {
    let scope = proposal_scope("finite-refutation");
    let catalog = proposal_catalog(&scope, '0');
    let alpha = proposal_clause(&scope, "alpha", "alpha", FrameworkIILevel::ZERO);
    let mut state = LeveledHoudiniState::new(catalog).unwrap();
    let (mut checker, requests) = scripted_checker([
        ProposalScriptStep::Refuted,
        ProposalScriptStep::Proved,
        ProposalScriptStep::Proved,
    ]);

    assert_postcondition_open(
        &run_proposal(&mut state, &mut checker, [alpha.clone()], [])
            .await
            .unwrap(),
    );

    let alpha_id = state.catalog().find(&alpha).unwrap().unwrap();
    assert_eq!(
        state.committed_levels().get(&alpha_id),
        Some(&FrameworkIILevel::ONE)
    );
    {
        let requests = requests.lock().unwrap();
        assert_eq!(requests.len(), 3);
        assert_eq!(requests[0].level(), FrameworkIILevel::ZERO);
        assert!(matches!(
            state.attempts().attempt(0).unwrap().outcome(),
            FrameworkIICheckOutcome::Refuted(_)
        ));
        assert_eq!(requests[1].level(), FrameworkIILevel::ONE);
        assert_eq!(requests[2].level(), FrameworkIILevel::ONE);
    }
}

#[tokio::test]
async fn invalid_stale_cross_catalog_and_ambiguous_proposals_are_mutation_free() {
    let scope = proposal_scope("negative-matrix");

    // Merely registered pending work is already drop eligible.
    let pending_catalog = proposal_catalog(&scope, '4');
    let pending_clause = proposal_clause(
        &scope,
        "fresh-pending",
        "fresh-pending",
        FrameworkIILevel::ZERO,
    );
    let pending_batch = registered_submitted(&pending_catalog, 0, [pending_clause.clone()]);
    let pending_id = pending_batch.ids()[0];
    let mut pending_state = LeveledHoudiniState::new(pending_catalog).unwrap();
    pending_state.enqueue_registered(&pending_batch).unwrap();
    assert_eq!(
        pending_state
            .proposal_context()
            .unwrap()
            .drop_eligible_records()
            .iter()
            .map(LeveledClauseRecord::id)
            .collect::<Vec<_>>(),
        vec![pending_id]
    );
    let pending_before = ProposalStateFingerprint::capture(&pending_state);
    assert!(
        pending_state
            .proposal_context()
            .unwrap()
            .drop_token(pending_id)
            .is_some(),
        "Pass 7.5c: freshly pending work is already drop-eligible"
    );
    assert_eq!(
        ProposalStateFingerprint::capture(&pending_state),
        pending_before
    );

    // A context is single-revision authority. Advance the state normally,
    // then prove the retained context cannot register even an empty batch.
    let stale_context = pending_state.proposal_context().unwrap();
    let (mut resolving_checker, _) = scripted_checker([]);
    assert_postcondition_open(
        &run_proposal(&mut pending_state, &mut resolving_checker, [], [])
            .await
            .unwrap(),
    );
    let stale_proposal = FrameworkIIProposalEpoch::new(stale_context, [], []).unwrap();
    let stale_before = ProposalStateFingerprint::capture(&pending_state);
    let (mut stale_checker, stale_requests) = scripted_checker([]);
    assert!(matches!(
        run_framework_ii_proposal_epoch(&mut pending_state, &mut stale_checker, stale_proposal)
            .await,
        Err(FrameworkIIStateError::InvalidEvidence(_))
    ));
    assert_eq!(
        ProposalStateFingerprint::capture(&pending_state),
        stale_before
    );
    assert!(stale_requests.lock().unwrap().is_empty());

    // An exact foreign drop token is never authority over the local record at
    // the same dense numeric ClauseId, even under the same scope.
    let left_catalog = proposal_catalog(&scope, '5');
    let right_catalog = proposal_catalog(&scope, '6');
    let mut left_state = LeveledHoudiniState::new(left_catalog).unwrap();
    let mut right_state = LeveledHoudiniState::new(right_catalog).unwrap();
    let left_clause = proposal_clause(&scope, "local", "local", FrameworkIILevel::ZERO);
    let right_clause = proposal_clause(&scope, "foreign", "foreign", FrameworkIILevel::ZERO);
    let (mut left_timeout, _) = scripted_checker([ProposalScriptStep::Inconclusive(
        FrameworkIIInconclusiveReason::TimedOut,
    )]);
    assert!(matches!(
        run_proposal(
            &mut left_state,
            &mut left_timeout,
            [left_clause.clone()],
            [],
        )
        .await
        .unwrap()
        .outcome(),
        FrameworkIIEpochOutcome::Refuted { .. }
    ));
    let (mut right_timeout, _) = scripted_checker([ProposalScriptStep::Inconclusive(
        FrameworkIIInconclusiveReason::TimedOut,
    )]);
    assert!(matches!(
        run_proposal(
            &mut right_state,
            &mut right_timeout,
            [right_clause.clone()],
            [],
        )
        .await
        .unwrap()
        .outcome(),
        FrameworkIIEpochOutcome::Refuted { .. }
    ));
    let left_id = left_state.catalog().find(&left_clause).unwrap().unwrap();
    let right_id = right_state.catalog().find(&right_clause).unwrap().unwrap();
    assert_eq!(
        left_id, right_id,
        "the catalogs deliberately reuse ordinal zero"
    );
    let foreign_drop = right_state
        .proposal_context()
        .unwrap()
        .drop_token(right_id)
        .unwrap();
    let foreign_proposal =
        FrameworkIIProposalEpoch::new(left_state.proposal_context().unwrap(), [], [foreign_drop])
            .unwrap();
    let left_before = ProposalStateFingerprint::capture(&left_state);
    let (mut foreign_checker, foreign_requests) = scripted_checker([]);
    assert!(matches!(
        run_framework_ii_proposal_epoch(&mut left_state, &mut foreign_checker, foreign_proposal)
            .await,
        Err(FrameworkIIStateError::InvalidEvidence(_))
    ));
    assert_eq!(ProposalStateFingerprint::capture(&left_state), left_before);
    assert!(foreign_requests.lock().unwrap().is_empty());

    // Cross-scope clauses fail while constructing the immutable proposal,
    // before the catalog or control revision can move.
    let foreign_scope = proposal_scope("foreign-scope");
    let foreign_clause =
        proposal_clause(&foreign_scope, "foreign", "foreign", FrameworkIILevel::ZERO);
    let constructor_before = ProposalStateFingerprint::capture(&left_state);
    assert_eq!(
        FrameworkIIProposalEpoch::new(
            left_state.proposal_context().unwrap(),
            [foreign_clause],
            [],
        )
        .unwrap_err(),
        FrameworkIIStateError::WrongScope
    );
    assert_eq!(
        ProposalStateFingerprint::capture(&left_state),
        constructor_before
    );

    // One eligible formula cannot be both dropped and resubmitted in the
    // same proposal, and an unknown identity fails before registration.
    let overlap_catalog = proposal_catalog(&scope, '7');
    let overlap_clause = proposal_clause(&scope, "overlap", "overlap", FrameworkIILevel::ZERO);
    let mut overlap_state = LeveledHoudiniState::new(overlap_catalog).unwrap();
    let (mut overlap_timeout, _) = scripted_checker([ProposalScriptStep::Inconclusive(
        FrameworkIIInconclusiveReason::TimedOut,
    )]);
    assert!(matches!(
        run_proposal(
            &mut overlap_state,
            &mut overlap_timeout,
            [overlap_clause.clone()],
            [],
        )
        .await
        .unwrap()
        .outcome(),
        FrameworkIIEpochOutcome::Refuted { .. }
    ));
    let overlap_id = overlap_state
        .catalog()
        .find(&overlap_clause)
        .unwrap()
        .unwrap();
    let overlap_before = ProposalStateFingerprint::capture(&overlap_state);
    let overlap_context = overlap_state.proposal_context().unwrap();
    let overlap_drop = overlap_context.drop_token(overlap_id).unwrap();
    let overlap_proposal =
        FrameworkIIProposalEpoch::new(overlap_context, [overlap_clause], [overlap_drop]).unwrap();
    let (mut overlap_checker, overlap_requests) = scripted_checker([]);
    assert!(matches!(
        run_framework_ii_proposal_epoch(&mut overlap_state, &mut overlap_checker, overlap_proposal)
            .await,
        Err(FrameworkIIStateError::InvalidPlacement(_))
    ));
    assert_eq!(
        ProposalStateFingerprint::capture(&overlap_state),
        overlap_before
    );
    assert!(overlap_requests.lock().unwrap().is_empty());

    let stale_drop = overlap_state
        .proposal_context()
        .unwrap()
        .drop_token(overlap_id)
        .unwrap();
    let (mut retry_timeout, _) = scripted_checker([ProposalScriptStep::Inconclusive(
        FrameworkIIInconclusiveReason::TimedOut,
    )]);
    assert!(matches!(
        run_proposal(&mut overlap_state, &mut retry_timeout, [], [],)
            .await
            .unwrap()
            .outcome(),
        FrameworkIIEpochOutcome::Refuted { .. }
    ));
    let stale_drop_proposal =
        FrameworkIIProposalEpoch::new(overlap_state.proposal_context().unwrap(), [], [stale_drop])
            .unwrap();
    let stale_drop_before = ProposalStateFingerprint::capture(&overlap_state);
    let (mut stale_drop_checker, stale_drop_requests) = scripted_checker([]);
    assert!(matches!(
        run_framework_ii_proposal_epoch(
            &mut overlap_state,
            &mut stale_drop_checker,
            stale_drop_proposal,
        )
        .await,
        Err(FrameworkIIStateError::InvalidEvidence(_))
    ));
    assert_eq!(
        ProposalStateFingerprint::capture(&overlap_state),
        stale_drop_before
    );
    assert!(stale_drop_requests.lock().unwrap().is_empty());

    let unknown_before = ProposalStateFingerprint::capture(&overlap_state);
    assert!(
        overlap_state
            .proposal_context()
            .unwrap()
            .drop_token(ClauseId::from_catalog_ordinal(999))
            .is_none(),
        "unknown dense identities cannot produce drop authority"
    );
    assert_eq!(
        ProposalStateFingerprint::capture(&overlap_state),
        unknown_before
    );
}

#[tokio::test]
async fn proposal_revision_exhaustion_fails_before_catalog_registration() {
    let scope = proposal_scope("revision-exhaustion");
    let catalog = proposal_catalog(&scope, '1');
    let alpha = proposal_clause(&scope, "alpha", "alpha", FrameworkIILevel::ZERO);
    let mut state = LeveledHoudiniState::new(catalog).unwrap();
    state.set_proposal_revision_for_test(u64::MAX);
    let before = ProposalStateFingerprint::capture(&state);
    let proposal =
        FrameworkIIProposalEpoch::new(state.proposal_context().unwrap(), [alpha], []).unwrap();
    let (mut checker, requests) = scripted_checker([]);

    let FrameworkIIEpochOutcome::Failure(report) =
        run_framework_ii_proposal_epoch(&mut state, &mut checker, proposal)
            .await
            .unwrap()
            .into_outcome()
    else {
        panic!("revision exhaustion must remain a typed pre-registration failure")
    };
    assert_eq!(report.origin(), FailureOrigin::EncodingPreparation);
    assert_eq!(report.kind(), FailureKind::InfrastructureFailure);
    assert_eq!(report.scope(), FailureScope::RunGlobal);
    assert!(
        report
            .detail()
            .is_some_and(|detail| detail.contains("revision space is exhausted"))
    );
    assert_eq!(ProposalStateFingerprint::capture(&state), before);
    assert!(requests.lock().unwrap().is_empty());
}

// ------------------------------------------------------------
// Two-Phase Levels And The Dead Partition
// ------------------------------------------------------------

#[tokio::test]
async fn phase1_initialization_is_issued_once_and_excludes_phase1_refuted_clauses_from_phase2() {
    // One initialization query per pending clause of the level: the
    // initialization premises are fixed for the whole level, so no clause's
    // outcome ever restarts the pass.
    let scope = proposal_scope("phase1-once");
    let catalog = proposal_catalog(&scope, 'a');
    let b = proposal_clause(&scope, "b", "02-b", FrameworkIILevel::ZERO);
    let c = proposal_clause(&scope, "c", "03-c", FrameworkIILevel::ZERO);
    let registered = registered_submitted(&catalog, 0, [b.clone(), c.clone()]);
    let mut state = LeveledHoudiniState::new(catalog).unwrap();
    state.enqueue_registered(&registered).unwrap();
    let b_id = state.catalog().find(&b).unwrap().unwrap();
    let c_id = state.catalog().find(&c).unwrap().unwrap();

    let log: Arc<Mutex<Vec<(ClauseId, FrameworkIILevel, FrameworkIICheckRole)>>> =
        Arc::new(Mutex::new(Vec::new()));
    let captured = Arc::clone(&log);
    let mut checker = ProposalExecutionChecker::new(move |request: FrameworkIICheckRequest| {
        captured
            .lock()
            .unwrap()
            .push((request.clause(), request.level(), request.role()));
        Ok(FrameworkIICheckExecution::Applied(proposal_proved(
            &request,
        )))
    });

    let outcome = stabilize_leveled_houdini(&mut state, &mut checker)
        .await
        .unwrap();
    assert!(matches!(
        outcome,
        LeveledStabilizationOutcome::Stabilized(_)
    ));

    let calls = log.lock().unwrap().clone();
    for (clause, role) in [
        (b_id, FrameworkIICheckRole::Initialization),
        (b_id, FrameworkIICheckRole::Maintenance),
        (c_id, FrameworkIICheckRole::Initialization),
        (c_id, FrameworkIICheckRole::Maintenance),
    ] {
        assert_eq!(
            calls
                .iter()
                .filter(|entry| **entry == (clause, FrameworkIILevel::ZERO, role))
                .count(),
            1,
            "expected exactly one {role} launch for clause {}",
            clause.get(),
        );
    }
    assert_eq!(
        state.committed_levels().get(&b_id),
        Some(&FrameworkIILevel::ZERO)
    );
    assert_eq!(
        state.committed_levels().get(&c_id),
        Some(&FrameworkIILevel::ZERO)
    );
}

#[tokio::test]
async fn a_phase1_refuted_clause_never_receives_a_maintenance_check_at_that_level() {
    let scope = proposal_scope("phase1-refuted-excluded");
    let catalog = proposal_catalog(&scope, 'b');
    // Prophecy-bearing so it promotes rather than dying, keeping the
    // assertion focused purely on Phase 1/Phase 2 exclusion.
    let a = proposal_clause(&scope, "a", "01-a", FrameworkIILevel::ZERO);
    let b = proposal_clause(&scope, "b", "02-b", FrameworkIILevel::ZERO);
    let registered = registered_submitted(&catalog, 0, [a.clone(), b.clone()]);
    let mut state = LeveledHoudiniState::new(catalog).unwrap();
    state.enqueue_registered(&registered).unwrap();
    let a_id = state.catalog().find(&a).unwrap().unwrap();
    let b_id = state.catalog().find(&b).unwrap().unwrap();

    let log: Arc<Mutex<Vec<(ClauseId, FrameworkIILevel, FrameworkIICheckRole)>>> =
        Arc::new(Mutex::new(Vec::new()));
    let captured = Arc::clone(&log);
    let mut checker = ProposalExecutionChecker::new(move |request: FrameworkIICheckRequest| {
        captured
            .lock()
            .unwrap()
            .push((request.clause(), request.level(), request.role()));
        let outcome = if request.clause() == a_id
            && request.level() == FrameworkIILevel::ZERO
            && request.role() == FrameworkIICheckRole::Initialization
        {
            proposal_refuted(&request)
        } else {
            proposal_proved(&request)
        };
        Ok(FrameworkIICheckExecution::Applied(outcome))
    });

    let outcome = stabilize_leveled_houdini(&mut state, &mut checker)
        .await
        .unwrap();
    assert!(matches!(
        outcome,
        LeveledStabilizationOutcome::Stabilized(_)
    ));

    let calls = log.lock().unwrap().clone();
    // `a` failed Phase 1 at level zero: it never enters the Phase-2
    // maintenance hypothesis set at that level, at any point in the run.
    assert!(
        !calls.iter().any(|(clause, level, role)| *clause == a_id
            && *level == FrameworkIILevel::ZERO
            && *role == FrameworkIICheckRole::Maintenance),
        "a Phase-1-refuted clause must never receive a level-zero maintenance check"
    );
    assert_eq!(
        state.committed_levels().get(&a_id),
        Some(&FrameworkIILevel::ONE)
    );
    assert_eq!(
        state.committed_levels().get(&b_id),
        Some(&FrameworkIILevel::ZERO)
    );
}

#[tokio::test]
async fn prophecy_bearing_level_zero_initialization_refutation_still_promotes() {
    let scope = proposal_scope("prophecy-bearing-promotes");
    let catalog = proposal_catalog(&scope, 'b');
    let bearing = proposal_clause(&scope, "bearing", "01-bearing", FrameworkIILevel::ZERO);
    let mut state = LeveledHoudiniState::new(catalog).unwrap();
    let (mut checker, _) = scripted_checker([ProposalScriptStep::Refuted]);

    let outcome = run_proposal(&mut state, &mut checker, [bearing.clone()], [])
        .await
        .unwrap();
    assert_postcondition_open(&outcome);

    let bearing_id = state.catalog().find(&bearing).unwrap().unwrap();
    assert!(state.dead().is_empty());
    assert_eq!(
        state.committed_levels().get(&bearing_id),
        Some(&FrameworkIILevel::ONE)
    );
}

#[tokio::test]
async fn prophecy_free_level_zero_initialization_refutation_is_dead_and_duplicate_is_rejected() {
    let scope = proposal_scope("dead-basic");
    let catalog = proposal_catalog(&scope, 'd');
    let x = proposal_clause_prophecy_free(&scope, "x", "01-x", FrameworkIILevel::ZERO);
    let mut state = LeveledHoudiniState::new(catalog).unwrap();
    let (mut checker, _) = scripted_checker([ProposalScriptStep::Refuted]);

    let outcome = run_proposal(&mut state, &mut checker, [x.clone()], [])
        .await
        .unwrap();
    assert_postcondition_open(&outcome);

    let x_id = state.catalog().find(&x).unwrap().unwrap();
    assert!(state.is_dead(x_id));
    assert!(state.pending_levels().is_empty());
    assert!(!state.committed_levels().contains_key(&x_id));
    let reason = state
        .dead_reason(x_id)
        .expect("the prophecy-free clause is dead");
    let FrameworkIIDeadReason::ProphecyFreeInitializationRefuted { attempt } = reason;
    assert_eq!(attempt, 0);
    assert!(
        state
            .drop_eligible_records()
            .unwrap()
            .iter()
            .all(|record| record.id() != x_id),
        "a dead clause is never drop-eligible"
    );

    // A later proposal resubmitting the exact same formula is rejected with
    // the original reason, not silently re-enqueued as pending.
    let (mut checker2, _) = scripted_checker([]);
    let rejected = run_proposal(&mut state, &mut checker2, [x.clone()], [])
        .await
        .unwrap_err();
    assert_eq!(
        rejected,
        FrameworkIIStateError::DeadClauseRejected {
            clause: x_id,
            reason,
        }
    );
    assert!(state.is_dead(x_id));
    assert!(state.pending_levels().is_empty());

    // A wholly unrelated fresh clause never revives a clause dead by
    // refutation.
    let y = proposal_clause(&scope, "y", "02-y", FrameworkIILevel::ZERO);
    let (mut checker3, _) = scripted_checker([]);
    let outcome = run_proposal(&mut state, &mut checker3, [y.clone()], [])
        .await
        .unwrap();
    assert_postcondition_open(&outcome);
    assert!(state.is_dead(x_id));
    assert!(!state.pending_levels().contains_key(&x_id));
}

// ------------------------------------------------------------
// The Epoch: Reset, Termination, Drops, And Check Order
// ------------------------------------------------------------

/// A checker whose clause checks are decided per request and whose
/// termination checks are scripted separately.
fn decided_checker(
    log: Arc<Mutex<Vec<FrameworkIICheckRequest>>>,
    mut decide: impl FnMut(&FrameworkIICheckRequest) -> FrameworkIICheckOutcome + Send + 'static,
) -> ProposalExecutionChecker<ProposalCheckClosure> {
    let checker: ProposalCheckClosure = Box::new(move |request: FrameworkIICheckRequest| {
        log.lock().unwrap().push(request.clone());
        Ok(FrameworkIICheckExecution::Applied(decide(&request)))
    });
    ProposalExecutionChecker::new(checker)
}

#[tokio::test]
async fn an_epoch_returns_the_termination_checks_outcome_on_the_epochs_core() {
    let scope = proposal_scope("termination-outcome");
    let catalog = proposal_catalog(&scope, '1');
    let alpha = proposal_clause(&scope, "alpha", "01-alpha", FrameworkIILevel::ZERO);
    let mut state = LeveledHoudiniState::new(catalog).unwrap();
    let (mut checker, _) = scripted_checker([]);
    let termination = checker.termination();
    termination
        .lock()
        .unwrap()
        .steps
        .push_back(ProposalScriptStep::Proved);

    let result = run_proposal(&mut state, &mut checker, [alpha.clone()], [])
        .await
        .unwrap();
    let alpha_id = state.catalog().find(&alpha).unwrap().unwrap();
    assert_eq!(result.submitted(), &[alpha_id]);
    let FrameworkIIEpochOutcome::Proved { core, .. } = result.into_outcome() else {
        panic!("a proved termination check ends the run with the frozen Core")
    };
    assert_eq!(core.snapshot().members(), BTreeSet::from([alpha_id]));

    let script = termination.lock().unwrap();
    assert_eq!(script.calls(), 1);
    assert_eq!(
        script.core_snapshots[0].members(),
        BTreeSet::from([alpha_id]),
        "the termination check sees a snapshot of the committed clauses only"
    );
    assert_eq!(state.termination_attempts_total(), 1);
}

#[tokio::test]
async fn the_termination_check_runs_after_empty_repeated_and_drops_only_proposals() {
    let scope = proposal_scope("termination-every-epoch");
    let catalog = proposal_catalog(&scope, '2');
    let alpha = proposal_clause(&scope, "alpha", "01-alpha", FrameworkIILevel::ZERO);
    let beta = proposal_clause(&scope, "beta", "02-beta", FrameworkIILevel::ZERO);
    let mut state = LeveledHoudiniState::new(catalog).unwrap();

    let log = Arc::new(Mutex::new(Vec::new()));
    let beta_identity = beta.identity().clone();
    let mut checker = decided_checker(Arc::clone(&log), move |request| {
        let is_beta = request
            .snapshot()
            .records()
            .get(&request.clause())
            .is_some_and(|record| record.formula().identity() == &beta_identity);
        if is_beta && request.role() == FrameworkIICheckRole::Maintenance {
            proposal_refuted(request)
        } else {
            proposal_proved(request)
        }
    });
    let termination = checker.termination();

    assert_postcondition_open(
        &run_proposal(&mut state, &mut checker, [alpha.clone(), beta.clone()], [])
            .await
            .unwrap(),
    );
    let alpha_id = state.catalog().find(&alpha).unwrap().unwrap();
    let beta_id = state.catalog().find(&beta).unwrap().unwrap();
    assert_eq!(
        state.committed_levels().get(&alpha_id),
        Some(&FrameworkIILevel::ZERO)
    );
    assert!(state.pending_levels().contains_key(&beta_id));

    // An empty proposal.
    assert_postcondition_open(
        &run_proposal(&mut state, &mut checker, [], [])
            .await
            .unwrap(),
    );
    // A repeated proposal.
    assert_postcondition_open(
        &run_proposal(&mut state, &mut checker, [alpha.clone()], [])
            .await
            .unwrap(),
    );
    // A drops-only proposal.
    let beta_drop = state
        .proposal_context()
        .unwrap()
        .drop_token(beta_id)
        .expect("a pending clause is drop eligible");
    assert_postcondition_open(
        &run_proposal(&mut state, &mut checker, [], [beta_drop])
            .await
            .unwrap(),
    );

    let script = termination.lock().unwrap();
    assert_eq!(
        script.calls(),
        4,
        "every epoch runs the termination check, whatever the proposal contained"
    );
    assert!(
        script
            .core_snapshots
            .iter()
            .all(|core| core.members() == BTreeSet::from([alpha_id])),
        "the termination check always ranges over the committed clauses only"
    );
    assert_eq!(state.termination_attempts_total(), 4);
}

#[tokio::test]
async fn every_pending_clause_returns_to_its_minimum_level_each_epoch() {
    let scope = proposal_scope("epoch-reset");
    let catalog = proposal_catalog(&scope, '3');
    let stuck = proposal_clause(&scope, "stuck", "01-stuck", FrameworkIILevel::ZERO);
    let mut state = LeveledHoudiniState::new(catalog).unwrap();

    let log = Arc::new(Mutex::new(Vec::new()));
    let mut checker = decided_checker(Arc::clone(&log), |request| {
        if request.role() == FrameworkIICheckRole::Initialization {
            proposal_proved(request)
        } else {
            proposal_refuted(request)
        }
    });
    assert_postcondition_open(
        &run_proposal(&mut state, &mut checker, [stuck.clone()], [])
            .await
            .unwrap(),
    );
    let stuck_id = state.catalog().find(&stuck).unwrap().unwrap();
    assert_eq!(
        state.pending_levels().get(&stuck_id),
        Some(&FrameworkIILevel::ONE)
    );

    log.lock().unwrap().clear();
    assert_postcondition_open(
        &run_proposal(&mut state, &mut checker, [], [])
            .await
            .unwrap(),
    );
    assert_eq!(
        log.lock().unwrap().first().map(|request| request.level()),
        Some(FrameworkIILevel::ZERO),
        "an epoch retries every pending clause from its minimum level"
    );
    assert_eq!(
        state.pending_levels().get(&stuck_id),
        Some(&FrameworkIILevel::ONE)
    );
}

#[tokio::test]
async fn a_drop_kills_a_pending_clause_and_only_an_exact_resubmission_revives_it() {
    let scope = proposal_scope("drop-revive");
    let catalog = proposal_catalog(&scope, '4');
    let victim = proposal_clause(&scope, "victim", "01-victim", FrameworkIILevel::ZERO);
    let other = proposal_clause(&scope, "other", "02-other", FrameworkIILevel::ZERO);
    let mut state = LeveledHoudiniState::new(catalog).unwrap();

    let log = Arc::new(Mutex::new(Vec::new()));
    let mut checker = decided_checker(Arc::clone(&log), |request| {
        if request.role() == FrameworkIICheckRole::Initialization {
            proposal_proved(request)
        } else {
            proposal_refuted(request)
        }
    });
    assert_postcondition_open(
        &run_proposal(&mut state, &mut checker, [victim.clone()], [])
            .await
            .unwrap(),
    );
    let victim_id = state.catalog().find(&victim).unwrap().unwrap();

    let drop_token = state
        .proposal_context()
        .unwrap()
        .drop_token(victim_id)
        .expect("a pending clause is drop eligible");
    assert_postcondition_open(
        &run_proposal(&mut state, &mut checker, [], [drop_token])
            .await
            .unwrap(),
    );
    assert_eq!(
        state.dead_cause(victim_id),
        Some(FrameworkIIDeadCause::Dropped)
    );
    assert!(state.is_dropped(victim_id));
    assert!(!state.pending_levels().contains_key(&victim_id));
    assert!(state.dead_reason(victim_id).is_none());
    assert!(
        state
            .proposal_context()
            .unwrap()
            .drop_token(victim_id)
            .is_none(),
        "a dead clause is never drop eligible"
    );

    // Another epoch, and an unrelated novel clause, never revive it.
    log.lock().unwrap().clear();
    assert_postcondition_open(
        &run_proposal(&mut state, &mut checker, [other.clone()], [])
            .await
            .unwrap(),
    );
    assert!(state.is_dropped(victim_id));
    assert!(
        log.lock()
            .unwrap()
            .iter()
            .all(|request| request.clause() != victim_id),
        "a dead clause receives no check"
    );

    // Its exact resubmission revives it, pending at its minimum level.
    log.lock().unwrap().clear();
    assert_postcondition_open(
        &run_proposal(&mut state, &mut checker, [victim.clone()], [])
            .await
            .unwrap(),
    );
    assert!(!state.is_dead(victim_id));
    assert_eq!(
        log.lock()
            .unwrap()
            .iter()
            .find(|request| request.clause() == victim_id)
            .map(FrameworkIICheckRequest::level),
        Some(FrameworkIILevel::ZERO),
        "a revived clause re-enters at its Lean-owned minimum level"
    );
}

#[tokio::test]
async fn an_epochs_fresh_clauses_are_checked_before_the_rest_of_their_level() {
    let scope = proposal_scope("fresh-first");
    let catalog = proposal_catalog(&scope, '5');
    // Canonical order is (level, registration order, identifier), so `old`
    // precedes `fresh` there; only the fresh-first rule can reverse them.
    let old = proposal_clause(&scope, "old", "01-old", FrameworkIILevel::ZERO);
    let fresh = proposal_clause(&scope, "fresh", "02-fresh", FrameworkIILevel::ZERO);
    let mut state = LeveledHoudiniState::new(catalog).unwrap();

    let log = Arc::new(Mutex::new(Vec::new()));
    let mut checker = decided_checker(Arc::clone(&log), |request| {
        if request.role() == FrameworkIICheckRole::Initialization {
            proposal_proved(request)
        } else {
            proposal_refuted(request)
        }
    });
    assert_postcondition_open(
        &run_proposal(&mut state, &mut checker, [old.clone()], [])
            .await
            .unwrap(),
    );
    let old_id = state.catalog().find(&old).unwrap().unwrap();

    log.lock().unwrap().clear();
    assert_postcondition_open(
        &run_proposal(&mut state, &mut checker, [fresh.clone()], [])
            .await
            .unwrap(),
    );
    let fresh_id = state.catalog().find(&fresh).unwrap().unwrap();
    assert!(state.fresh_clauses().contains(&fresh_id));
    assert!(!state.fresh_clauses().contains(&old_id));
    let log = log.lock().unwrap();
    assert_eq!(
        log.first().map(FrameworkIICheckRequest::clause),
        Some(fresh_id),
        "the epoch's fresh clause is checked before the older clause of its level"
    );
    assert_eq!(log[0].level(), FrameworkIILevel::ZERO);
}

#[tokio::test]
async fn a_proposal_above_the_level_bound_is_rejected_at_admission() {
    let scope = proposal_scope("proposal-level-bound");
    let catalog = proposal_catalog(&scope, '6');
    let above = proposal_clause(&scope, "above", "01-above", FrameworkIILevel::new(2));
    let mut state =
        LeveledHoudiniState::new_with_max_level(catalog, Some(FrameworkIILevel::ONE)).unwrap();
    let before = ProposalStateFingerprint::capture(&state);
    let (mut checker, requests) = scripted_checker([]);
    assert_eq!(
        run_proposal(&mut state, &mut checker, [above], [])
            .await
            .unwrap_err(),
        FrameworkIIStateError::LevelBoundExceeded {
            clause: None,
            minimum_level: 2,
            max_level: 1,
        }
    );
    assert_eq!(ProposalStateFingerprint::capture(&state), before);
    assert!(requests.lock().unwrap().is_empty());
    assert_eq!(state.termination_attempts_total(), 0);
}

#[tokio::test]
async fn an_infrastructure_failure_leaves_the_partition_at_the_epochs_start() {
    let scope = proposal_scope("epoch-failure");
    let catalog = proposal_catalog(&scope, '7');
    let alpha = proposal_clause(&scope, "alpha", "01-alpha", FrameworkIILevel::ZERO);
    let beta = proposal_clause(&scope, "beta", "02-beta", FrameworkIILevel::ZERO);
    let mut state = LeveledHoudiniState::new(catalog).unwrap();
    let (mut initial_checker, _) = scripted_checker([]);
    assert_postcondition_open(
        &run_proposal(&mut state, &mut initial_checker, [alpha.clone()], [])
            .await
            .unwrap(),
    );
    let alpha_id = state.catalog().find(&alpha).unwrap().unwrap();
    let core_before = committed_members(&state);
    let history_before = attempt_row_digests(&state);
    let pending_before = state.pending_levels().clone();
    let terminations_before = state.termination_attempts_total();

    let expected = proposal_failure();
    // The epoch completes one check before the infrastructure fault, so the
    // abandoned work carries a real ledger row to merge.
    let (mut checker, _) = scripted_checker([
        ProposalScriptStep::Proved,
        ProposalScriptStep::Failure(expected.clone()),
    ]);
    let FrameworkIIEpochOutcome::Failure(actual) =
        run_proposal(&mut state, &mut checker, [beta.clone()], [])
            .await
            .unwrap()
            .into_outcome()
    else {
        panic!("an infrastructure fault stays a typed run-global failure")
    };
    assert_eq!(actual.detail(), expected.detail());
    assert_eq!(actual.kind(), expected.kind());

    // Milestone 7.5 review, finding 2: the epoch is atomic. `beta` was
    // interned in the catalog, so its identity is findable, but the rolled
    // back partition holds it in neither `Core` nor `Pend` — it is fresh
    // again for an exact resubmission.
    let beta_id = state.catalog().find(&beta).unwrap().unwrap();
    assert_eq!(committed_members(&state), core_before);
    assert_eq!(committed_members(&state), BTreeSet::from([alpha_id]));
    assert_eq!(
        state.pending_levels().get(&beta_id),
        None,
        "an epoch that failed never admitted its batch to the pending partition"
    );
    assert!(
        !state.is_dead(beta_id),
        "a rolled-back fresh clause is not dead either; it is simply unknown to the partition"
    );
    assert_eq!(
        &attempt_row_digests(&state)[..history_before.len()],
        history_before.as_slice(),
        "append-only history is never rewritten"
    );
    assert_eq!(
        state.termination_attempts_total(),
        terminations_before,
        "a failed epoch runs no termination check"
    );
    // The epoch reset every pending clause to its minimum level on its
    // private work copy; a failure publishes none of that, only the
    // append-only history.
    assert_eq!(
        state.pending_levels(),
        &pending_before,
        "an infrastructure failure leaves the pending levels as the epoch found them"
    );
    assert!(
        attempt_row_digests(&state).len() > history_before.len(),
        "the abandoned epoch's attempt rows are still merged into the history"
    );
}

/// Milestone 7.5 review, finding 2. `houdini.tex` Algorithm 1: an epoch that
/// returns `Failure` leaves "the partition as it was when the epoch began",
/// which covers the drops it applied as much as the levels it moved. A
/// dropped clause therefore comes back to `Pend` at the level it held.
#[tokio::test]
async fn an_infrastructure_failure_restores_the_clauses_the_epoch_dropped() {
    let scope = proposal_scope("epoch-failure-drop-rollback");
    let catalog = proposal_catalog(&scope, '7');
    let alpha = proposal_clause(&scope, "alpha", "01-alpha", FrameworkIILevel::ZERO);
    let beta = proposal_clause(&scope, "beta", "02-beta", FrameworkIILevel::ZERO);
    let mut state = LeveledHoudiniState::new(catalog).unwrap();
    // One epoch that leaves both clauses pending: each initialization is
    // proved and each step check refuted, so neither enters the Core and
    // both stay drop eligible. `beta` is what the failing epoch's scan then
    // has to check, so that its fault happens after the drop was applied.
    let log = Arc::new(Mutex::new(Vec::new()));
    let mut initial_checker = decided_checker(Arc::clone(&log), |request| {
        if request.role() == FrameworkIICheckRole::Initialization {
            proposal_proved(request)
        } else {
            proposal_refuted(request)
        }
    });
    let _ = run_proposal(
        &mut state,
        &mut initial_checker,
        [alpha.clone(), beta.clone()],
        [],
    )
    .await
    .unwrap();
    let alpha_id = state.catalog().find(&alpha).unwrap().unwrap();
    let pending_before = state.pending_levels().clone();
    let dead_before = state.dead().clone();
    assert!(
        pending_before.contains_key(&alpha_id),
        "this fixture needs a pending, drop-eligible clause"
    );

    let context = state.proposal_context().unwrap();
    let drop_token = context
        .drop_token(alpha_id)
        .expect("a pending clause is drop eligible");
    let proposal = FrameworkIIProposalEpoch::new(context, [], [drop_token]).unwrap();
    let expected = proposal_failure();
    let (mut checker, _) = scripted_checker([ProposalScriptStep::Failure(expected.clone())]);
    let FrameworkIIEpochOutcome::Failure(actual) =
        run_framework_ii_proposal_epoch(&mut state, &mut checker, proposal)
            .await
            .unwrap()
            .into_outcome()
    else {
        panic!("an infrastructure fault stays a typed run-global failure")
    };
    assert_eq!(actual.detail(), expected.detail());

    assert_eq!(
        state.pending_levels(),
        &pending_before,
        "a failed epoch's drops go back to pending at the level they held"
    );
    assert_eq!(
        state.dead(),
        &dead_before,
        "a failed epoch's drops leave no dead row behind"
    );
    assert!(!state.is_dropped(alpha_id));
}

/// Milestone 7.5 review, finding 2, the remaining two Failure paths. A
/// fault in activating or publishing the epoch's work returns `Failure`
/// like any other, so it takes the same rollback; neither has a staged
/// owner left to abandon, so both roll the *published* checkpoint back onto
/// the epoch's start through `rolled_back_epoch_failure`. Both are
/// invariant violations no well-formed run reaches, so the route is driven
/// here directly, against a state an epoch really moved.
#[tokio::test]
async fn a_publication_fault_rolls_the_published_epoch_back_to_its_start() {
    let scope = proposal_scope("epoch-publication-fault");
    let catalog = proposal_catalog(&scope, '9');
    let alpha = proposal_clause(&scope, "alpha", "01-alpha", FrameworkIILevel::ZERO);
    let beta = proposal_clause(&scope, "beta", "02-beta", FrameworkIILevel::ZERO);
    let mut state = LeveledHoudiniState::new(catalog).unwrap();
    let (mut initial_checker, _) = scripted_checker([]);
    let _ = run_proposal(&mut state, &mut initial_checker, [alpha.clone()], [])
        .await
        .unwrap();
    let pending_before = state.pending_levels().clone();
    let committed_before = state.committed_levels().clone();
    let revision_before = state.proposal_revision();

    // A second epoch that really applies: `beta` is interned and placed,
    // and the partition moves.
    let epoch_start = state.epoch_rollback_point();
    let (mut checker, _) = scripted_checker([]);
    let _ = run_proposal(&mut state, &mut checker, [beta.clone()], [])
        .await
        .unwrap();
    let beta_id = state.catalog().find(&beta).unwrap().unwrap();
    assert_ne!(
        state.committed_levels(),
        &committed_before,
        "this fixture needs an epoch that really changed the partition"
    );

    let result = rolled_back_epoch_failure(
        &mut state,
        epoch_start,
        FrameworkIIStateError::InvalidEvidence(
            "stabilized proposal work did not advance its durable checkpoint",
        ),
        Arc::from([beta_id]),
    )
    .unwrap();

    assert!(matches!(
        result.outcome(),
        FrameworkIIEpochOutcome::Failure(_)
    ));
    assert_eq!(result.submitted(), &[beta_id]);
    assert!(
        result.round_outcomes().is_empty(),
        "a rolled-back epoch reports no per-clause outcome for its batch"
    );
    assert_eq!(
        state.committed_levels(),
        &committed_before,
        "the partition is the one the epoch began with"
    );
    assert_eq!(state.pending_levels(), &pending_before);
    assert!(!state.pending_levels().contains_key(&beta_id));
    assert!(!state.is_dead(beta_id));
    assert!(
        state.proposal_revision() > revision_before,
        "a rollback is itself a published transition, so the revision advances"
    );
    assert!(
        state.catalog().find(&beta).unwrap().is_some(),
        "the catalog keeps the rolled-back record as provenance"
    );
    assert!(
        !attempt_row_digests(&state).is_empty(),
        "the ledger keeps the checks the epoch really ran"
    );
}

/// Milestone 7.5 review, finding 2, the epoch after. A rolled-back epoch
/// leaves nothing of its own in check order: the next epoch's `Fresh` set is
/// computed against the restored partition, so a clause the failed epoch
/// admitted is fresh again when it is resubmitted exactly.
#[tokio::test]
async fn the_epoch_after_a_failure_treats_the_rolled_back_batch_as_fresh() {
    let scope = proposal_scope("epoch-failure-check-order");
    let catalog = proposal_catalog(&scope, '7');
    let alpha = proposal_clause(&scope, "alpha", "01-alpha", FrameworkIILevel::ZERO);
    let beta = proposal_clause(&scope, "beta", "02-beta", FrameworkIILevel::ZERO);
    let mut state = LeveledHoudiniState::new(catalog).unwrap();
    let (mut initial_checker, _) = scripted_checker([]);
    let _ = run_proposal(&mut state, &mut initial_checker, [alpha.clone()], [])
        .await
        .unwrap();

    let expected = proposal_failure();
    let (mut failing, _) = scripted_checker([ProposalScriptStep::Failure(expected)]);
    let _ = run_proposal(&mut state, &mut failing, [beta.clone()], [])
        .await
        .unwrap();

    // The exact resubmission re-admits the same content-addressed identity,
    // and it is fresh: the failed epoch's admission was rolled back.
    let (mut checker, requests) = scripted_checker([]);
    let _ = run_proposal(&mut state, &mut checker, [beta.clone()], [])
        .await
        .unwrap();
    let beta_id = state.catalog().find(&beta).unwrap().unwrap();
    let log = requests.lock().unwrap().clone();
    assert!(
        !log.is_empty(),
        "the resubmitted clause is checked in the following epoch"
    );
    assert_eq!(
        log[0].clause(),
        beta_id,
        "a rolled-back clause is fresh again, so it leads its level's check order"
    );
}

/// `houdini.tex` Section 4.2: the termination check runs once per epoch,
/// after the epoch's scan — never before the first consultation has
/// produced a proposal.
#[tokio::test]
async fn the_termination_check_runs_once_per_epoch_and_never_before_the_first() {
    let scope = proposal_scope("termination-timing");
    let catalog = proposal_catalog(&scope, 'c');
    let alpha = proposal_clause(&scope, "alpha", "01-alpha", FrameworkIILevel::ZERO);
    let mut state = LeveledHoudiniState::new(catalog).unwrap();
    assert_eq!(
        state.termination_attempts_total(),
        0,
        "no termination check runs before the first consultation's epoch"
    );

    let (mut checker, _) = scripted_checker([]);
    assert_postcondition_open(
        &run_proposal(&mut state, &mut checker, [alpha.clone()], [])
            .await
            .unwrap(),
    );
    assert_eq!(state.termination_attempts_total(), 1);

    let beta = proposal_clause(&scope, "beta", "02-beta", FrameworkIILevel::ZERO);
    assert_postcondition_open(
        &run_proposal(&mut state, &mut checker, [beta], [])
            .await
            .unwrap(),
    );
    assert_eq!(
        state.termination_attempts_total(),
        2,
        "one termination check per epoch, and only after its scan"
    );
}

#[tokio::test]
async fn a_cancelled_check_ends_the_epoch_cancelled() {
    let scope = proposal_scope("epoch-cancelled");
    let catalog = proposal_catalog(&scope, '8');
    let alpha = proposal_clause(&scope, "alpha", "01-alpha", FrameworkIILevel::ZERO);
    let mut state = LeveledHoudiniState::new(catalog).unwrap();
    let (mut checker, requests) = scripted_checker([ProposalScriptStep::Cancelled]);

    let outcome = run_proposal(&mut state, &mut checker, [alpha.clone()], [])
        .await
        .unwrap()
        .into_outcome();
    assert!(
        matches!(outcome, FrameworkIIEpochOutcome::Cancelled),
        "a cancelled epoch is not a postcondition-open report: {outcome:?}"
    );
    assert_eq!(requests.lock().unwrap().len(), 1);
    assert!(state.committed_levels().is_empty());
    assert_eq!(state.termination_attempts_total(), 0);
}
