use std::collections::BTreeSet;
use std::future::Future;
use std::path::PathBuf;
use std::pin::Pin;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Duration;

use serde_json::{Value, json};

use super::feedback::{
    AGENT_COUNTEREXAMPLE_REJECTED_KIND, legacy_v2_state_snapshot_digest_for_test,
};
use super::stabilization::FrameworkIICheckExecution;
use super::types::{FrameworkIIProphecyBinding, FrameworkIIRelation};
use super::*;
use crate::artifact::{ArtifactKind, ArtifactStore, ArtifactStoreConfig, new_artifact_store};
use crate::failure::{FailureKind, FailureOrigin, FailureReport, FailureScope};
use crate::houdini::ClauseId;
use crate::task::{RelationKey, SynthesisTask};

static NEXT_FEEDBACK_DIRECTORY: AtomicU64 = AtomicU64::new(0);

fn feedback_task(prose: &str) -> SynthesisTask {
    let source = r#"{
      "format_version":3,
      "semantic_version":1,
      "encoding_version":1,
      "identity":{
        "canonical_id":"FrameworkIIFeedbackTest",
        "module":"Whiel.Test.FrameworkIIFeedbackTest",
        "namespace":"Whiel.Test.FrameworkIIFeedbackTest",
        "source_sha256":"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
      },
      "schema":{"expression":"Whiel.Test.FrameworkIIFeedbackTest.programSchema","display":"SCHEMA_PROSE"},
      "original":{
        "pre":{"expression":"Whiel.Test.FrameworkIIFeedbackTest.inputPre","display":"ORIGINAL_PRE_PROSE"},
        "command":{"expression":"Whiel.Test.FrameworkIIFeedbackTest.inputCmd","display":"ORIGINAL_COMMAND_PROSE"},
        "post":{"expression":"Whiel.Test.FrameworkIIFeedbackTest.inputPost","display":"ORIGINAL_POST_PROSE"}
      },
      "preprocessed":{
        "pre":{"expression":"Whiel.Test.FrameworkIIFeedbackTest.inputPreproc.loopPre","display":"PREPROCESSED_PRE_PROSE"},
        "command":{"expression":"Whiel.Test.FrameworkIIFeedbackTest.inputPreproc.loopCmd","display":"PREPROCESSED_COMMAND_PROSE"},
        "post":{"expression":"Whiel.Test.FrameworkIIFeedbackTest.inputPreproc.loopPost","display":"PREPROCESSED_POST_PROSE"}
      },
      "preprocessing_evidence":{"expression":"Whiel.Test.FrameworkIIFeedbackTest.inputPreproc"},
      "solver":{
        "schema_relations":[{"key":"rel:R:0","arity":1}],
        "task_constants":[],
        "preprocessed_pre":{
          "source_id":"task.preprocessed_pre",
          "expression":"Whiel.Test.FrameworkIIFeedbackTest.inputPreproc.loopPre",
          "no_bound_expression":"Whiel.Test.FrameworkIIFeedbackTest.inputPreproc.loopPre_noBound",
          "constants":[],"relations":[]
        },
        "preprocessed_post":{
          "source_id":"task.preprocessed_post",
          "expression":"Whiel.Test.FrameworkIIFeedbackTest.inputPreproc.loopPost",
          "no_bound_expression":"Whiel.Test.FrameworkIIFeedbackTest.inputPreproc.loopPost_noBound",
          "constants":[],"relations":[]
        },
        "loop_guard":{"source_id":"task.loop_guard","constants":[],"relations":[]},
        "negated_loop_guard":{"source_id":"task.negated_loop_guard","constants":[],"relations":[]}
      }
    }"#;
    let source = [
        ("SCHEMA_PROSE", format!("schema {prose}")),
        ("ORIGINAL_PRE_PROSE", format!("original pre {prose}")),
        (
            "ORIGINAL_COMMAND_PROSE",
            format!("original command {prose}"),
        ),
        ("ORIGINAL_POST_PROSE", format!("original post {prose}")),
        (
            "PREPROCESSED_PRE_PROSE",
            format!("preprocessed pre {prose}"),
        ),
        (
            "PREPROCESSED_COMMAND_PROSE",
            format!("preprocessed command {prose}"),
        ),
        (
            "PREPROCESSED_POST_PROSE",
            format!("preprocessed post {prose}"),
        ),
    ]
    .into_iter()
    .fold(source.to_string(), |source, (placeholder, value)| {
        source.replace(placeholder, &value)
    });
    SynthesisTask::from_json(&source).unwrap()
}

fn feedback_scope(task: &SynthesisTask) -> FixedAmbientTaskScope {
    let source = FrameworkIIRelation::new(
        task.solver_relations()[0].key().clone(),
        task.solver_relations()[0].arity(),
    );
    let prophecy_key = RelationKey::from_canonical("rel:P:0").unwrap();
    let prophecy = FrameworkIIRelation::new(prophecy_key.clone(), 1);
    let binding = FrameworkIIProphecyBinding::new(source.key().clone(), prophecy_key, 1);
    FixedAmbientTaskScope::new(
        task.identity().clone(),
        json!(["framework-ii-feedback-scope", ["rel:R:0", "rel:P:0"]]),
        json!({"private": "SECRET_SCOPE_PRESENTATION"}),
        vec![source.clone()],
        vec![source, prophecy],
        vec![binding],
    )
}

fn feedback_clause(scope: &FixedAmbientTaskScope, ordinal: u64) -> ExtendedClause {
    feedback_clause_with_display(scope, ordinal, format!("clause display {ordinal}"))
}

fn feedback_clause_with_display(
    scope: &FixedAmbientTaskScope,
    ordinal: u64,
    display: String,
) -> ExtendedClause {
    let identity = json!(["feedback-clause", ordinal]);
    ExtendedClause::new(
        scope.clone(),
        identity.clone(),
        format!("{ordinal:04}"),
        display,
        vec!["rel:R:0".to_string()],
        // Prophecy-bearing: these fixtures exercise a level-zero refutation
        // that is expected to promote (exhaust at `max_level == ZERO`), not
        // the Pass 7.5b dead-clause rule for prophecy-free clauses.
        true,
        FrameworkIILevel::ZERO,
    )
}

fn feedback_catalog(scope: &FixedAmbientTaskScope, marker: char) -> LeveledClauseCatalog {
    LeveledClauseCatalog::new(scope.clone(), marker.to_string().repeat(64)).unwrap()
}

struct InconclusiveChecker;

/// The ordinary outcome of an epoch: the Core does not yet close the
/// postcondition, so the termination check is refuted.
fn refuted_termination() -> FrameworkIICheckExecution {
    FrameworkIICheckExecution::Applied(FrameworkIICheckOutcome::Refuted(
        FrameworkIICheckEvidence::new("c".repeat(64), "feedback-termination").unwrap(),
    ))
}

impl super::stabilization::sealed::Sealed for InconclusiveChecker {}

impl FrameworkIIChecker for InconclusiveChecker {
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
        let outcome = FrameworkIICheckOutcome::Inconclusive {
            reason: FrameworkIIInconclusiveReason::TimedOut,
            progress: FrameworkIICheckEvidence::new(
                request.request_digest(),
                format!("feedback-progress:{}", request.request_digest()),
            )
            .unwrap(),
        };
        Box::pin(std::future::ready(Ok(FrameworkIICheckExecution::Applied(
            outcome,
        ))))
    }

    fn check_termination<'a>(
        &'a mut self,
        _core: Arc<LeveledCandidateSnapshot>,
    ) -> Pin<
        Box<
            dyn Future<Output = Result<FrameworkIICheckExecution, FrameworkIIStateError>>
                + Send
                + 'a,
        >,
    > {
        Box::pin(std::future::ready(Ok(refuted_termination())))
    }
}

#[derive(Clone, Copy)]
enum ConclusiveOutcome {
    Proved,
    Refuted,
}

struct ConclusiveChecker(ConclusiveOutcome);

impl super::stabilization::sealed::Sealed for ConclusiveChecker {}

impl FrameworkIIChecker for ConclusiveChecker {
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
        let evidence = FrameworkIICheckEvidence::new(
            request.request_digest(),
            format!("feedback-route:{}", request.request_digest()),
        )
        .unwrap();
        let outcome = match self.0 {
            ConclusiveOutcome::Proved => FrameworkIICheckOutcome::Proved(evidence),
            ConclusiveOutcome::Refuted => FrameworkIICheckOutcome::Refuted(evidence),
        };
        Box::pin(std::future::ready(Ok(FrameworkIICheckExecution::Applied(
            outcome,
        ))))
    }

    fn check_termination<'a>(
        &'a mut self,
        _core: Arc<LeveledCandidateSnapshot>,
    ) -> Pin<
        Box<
            dyn Future<Output = Result<FrameworkIICheckExecution, FrameworkIIStateError>>
                + Send
                + 'a,
        >,
    > {
        Box::pin(std::future::ready(Ok(refuted_termination())))
    }
}

#[derive(Clone, Copy)]
enum RealRouteKind {
    RuntimeProof,
    ValidatedRefutation,
    RetryProgress,
}

struct RealRouteChecker {
    route: RealRouteKind,
    artifacts: ArtifactStore,
}

impl super::stabilization::sealed::Sealed for RealRouteChecker {}

impl FrameworkIIChecker for RealRouteChecker {
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
        let outcome = match self.route {
            RealRouteKind::RuntimeProof => {
                let receipt = RuntimeProofReceipt::feedback_test_fixture(
                    &request,
                    &self.artifacts,
                    ProofSearchProfile::Direct,
                );
                FrameworkIICheckOutcome::Proved(FrameworkIICheckEvidence::from_runtime_proof(
                    receipt,
                    Some(Duration::from_nanos(4_242)),
                ))
            }
            RealRouteKind::ValidatedRefutation => {
                let receipt =
                    ValidatedFiniteRefutation::feedback_test_fixture(&request, &self.artifacts);
                FrameworkIICheckOutcome::Refuted(
                    FrameworkIICheckEvidence::from_validated_refutation(
                        receipt,
                        Some(Duration::from_nanos(9_009)),
                    ),
                )
            }
            RealRouteKind::RetryProgress => {
                let diagnostic = self
                    .artifacts
                    .publish(
                        ArtifactKind::FailureDiagnostic,
                        b"SECRET_ROUTE_PEER_PAYLOAD".to_vec().into_boxed_slice(),
                    )
                    .unwrap();
                let peer_failure = diagnostic_failure(diagnostic, "SECRET_ROUTE_PEER_DETAIL");
                let progress = FrameworkIIEntailmentProgress::feedback_test_fixture(
                    &request,
                    &self.artifacts,
                    FrameworkIIInconclusiveReason::TimedOut,
                    Some(peer_failure),
                );
                FrameworkIICheckOutcome::Inconclusive {
                    reason: FrameworkIIInconclusiveReason::TimedOut,
                    progress: FrameworkIICheckEvidence::from_progress(
                        progress,
                        Some(Duration::from_nanos(1_001)),
                    ),
                }
            }
        };
        Box::pin(std::future::ready(Ok(FrameworkIICheckExecution::Applied(
            outcome,
        ))))
    }

    fn check_termination<'a>(
        &'a mut self,
        _core: Arc<LeveledCandidateSnapshot>,
    ) -> Pin<
        Box<
            dyn Future<Output = Result<FrameworkIICheckExecution, FrameworkIIStateError>>
                + Send
                + 'a,
        >,
    > {
        Box::pin(std::future::ready(Ok(refuted_termination())))
    }
}

/// Every clause stays pending: each check is inconclusive, which is a
/// failure at its level, so the scan ends with the clauses pending.
async fn pending_fixture(
    marker: char,
    clause_count: u64,
) -> (Arc<SynthesisTask>, LeveledHoudiniState) {
    let task = Arc::new(feedback_task("alpha"));
    let scope = feedback_scope(&task);
    let clauses = (0..clause_count)
        .map(|ordinal| feedback_clause(&scope, ordinal))
        .collect::<Vec<_>>();
    let catalog = feedback_catalog(&scope, marker);
    let mut state = LeveledHoudiniState::new(catalog).unwrap();
    let proposal =
        FrameworkIIProposalEpoch::new(state.proposal_context().unwrap(), clauses, []).unwrap();
    let outcome = run_framework_ii_proposal_epoch(&mut state, &mut InconclusiveChecker, proposal)
        .await
        .unwrap();
    assert!(matches!(
        outcome.outcome(),
        FrameworkIIEpochOutcome::Refuted { .. }
    ));
    assert_eq!(
        state.pending_levels().len(),
        usize::try_from(clause_count).unwrap()
    );
    (task, state)
}

async fn conclusive_fixture(
    marker: char,
    outcome: ConclusiveOutcome,
) -> (Arc<SynthesisTask>, LeveledHoudiniState) {
    let task = Arc::new(feedback_task("conclusive"));
    let scope = feedback_scope(&task);
    let clause = feedback_clause(&scope, 0);
    let catalog = feedback_catalog(&scope, marker);
    let mut state = LeveledHoudiniState::new(catalog).unwrap();
    let proposal =
        FrameworkIIProposalEpoch::new(state.proposal_context().unwrap(), [clause], []).unwrap();
    run_framework_ii_proposal_epoch(&mut state, &mut ConclusiveChecker(outcome), proposal)
        .await
        .unwrap();
    (task, state)
}

fn real_route_fixture(
    marker: char,
    label: &str,
) -> (
    Arc<SynthesisTask>,
    LeveledHoudiniState,
    FrameworkIIProposalEpoch,
) {
    let task = Arc::new(feedback_task(label));
    let scope = feedback_scope(&task);
    let clause = feedback_clause(&scope, 0);
    let catalog = feedback_catalog(&scope, marker);
    let state = LeveledHoudiniState::new(catalog).unwrap();
    let proposal =
        FrameworkIIProposalEpoch::new(state.proposal_context().unwrap(), [clause], []).unwrap();
    (task, state, proposal)
}

fn feedback_directory(label: &str) -> PathBuf {
    std::env::temp_dir().join(format!(
        "whiel_framework2_feedback_{label}_{}_{}",
        std::process::id(),
        NEXT_FEEDBACK_DIRECTORY.fetch_add(1, Ordering::Relaxed),
    ))
}

fn paging_policy(items: usize) -> AgentFeedbackPolicy {
    let limits = AgentFeedbackLimits {
        clause_page_items: items,
        ledger_page_items: items,
        ..AgentFeedbackLimits::default()
    };
    AgentFeedbackPolicy::new(limits).unwrap()
}

fn minimum_page_policy() -> AgentFeedbackPolicy {
    let limits = AgentFeedbackLimits {
        max_page_bytes: 4 * 1024,
        ..AgentFeedbackLimits::default()
    };
    AgentFeedbackPolicy::new(limits).unwrap()
}

/// A page budget chosen so the oldest row of the page does not fit with its
/// evidence route but does fit without it: the fitter's summarized form is
/// what this exercises, and a budget that is merely small stops the page one
/// row earlier instead. Rows are fixed-size — digests, not free text — so the
/// window is deterministic.
fn summarizing_page_policy(max_page_bytes: usize) -> AgentFeedbackPolicy {
    AgentFeedbackPolicy::new(AgentFeedbackLimits {
        max_page_bytes,
        ..AgentFeedbackLimits::default()
    })
    .unwrap()
}

fn diagnostic_failure(reference: crate::artifact::ArtifactRef, detail: &str) -> FailureReport {
    FailureReport::try_new(
        FailureOrigin::AgentConsultation,
        FailureKind::TransportFailure,
        true,
        FailureScope::LaneLocal,
        Some(detail.to_string()),
        vec![reference],
    )
    .unwrap()
}

fn stable_ids(value: &Value) -> Vec<String> {
    fn visit(value: &Value, output: &mut Vec<String>) {
        match value {
            Value::Object(fields) => {
                if let Some(stable_id) = fields.get("stable_id").and_then(Value::as_str) {
                    output.push(stable_id.to_string());
                }
                for child in fields.values() {
                    visit(child, output);
                }
            }
            Value::Array(rows) => {
                for child in rows {
                    visit(child, output);
                }
            }
            _ => {}
        }
    }

    let mut output = Vec::new();
    visit(value, &mut output);
    output
}

fn assert_no_retired_controller_keys(value: &Value) {
    const RETIRED: &[&str] = &[
        "active_plan",
        "active_plan_digest",
        "compatibility_plan",
        "finite_validity_application",
        "library_rejection",
        "library_use_digests",
        "selection_list",
        "selection_list_digest",
        "selection_list_identity",
        // Pass 7.5c-2 removed these from the controller and the wire.
        "retry",
        "exhausted",
        "unresolved",
        "unresolved_reason",
        "explicitly_dropped",
        "explicitly_dropped_clauses",
        "reconsideration",
    ];

    fn visit(value: &Value) {
        match value {
            Value::Object(fields) => {
                for (key, nested) in fields {
                    assert!(
                        !RETIRED.contains(&key.as_str()),
                        "feedback emitted retired controller key {key}",
                    );
                    visit(nested);
                }
            }
            Value::Array(items) => items.iter().for_each(visit),
            _ => {}
        }
    }

    visit(value);
}

#[tokio::test]
async fn initial_feedback_is_sanitized_and_has_no_library_surface() {
    let (task, state) = pending_fixture('a', 3).await;
    let raw_root = feedback_directory("sanitized");
    let (_owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(&raw_root)).unwrap();
    let policy = AgentFeedbackPolicy::default();
    let session = PreCertificateAgentHoudiniState::new(
        Arc::clone(&task),
        &artifacts,
        &state,
        Duration::from_secs(17),
        policy,
    )
    .unwrap();
    let feedback = session.feedback();

    assert!(matches!(feedback.latest(), AgentLatestFeedback::Initial));
    assert_eq!(feedback.iteration(), 1);
    assert_eq!(feedback.remaining_search_budget(), Duration::from_secs(17));
    assert!(feedback.encoded_bytes() <= session.policy().limits().max_feedback_bytes);

    let wire = feedback.to_json_value();
    assert_no_retired_controller_keys(&wire);
    assert_eq!(wire["schema_version"], 10);
    assert_eq!(wire["presentation"]["schema_version"], 16);
    let encoded = feedback.to_json_string().unwrap();
    for forbidden in [
        "Whiel.Test.FrameworkIIFeedbackTest.inputPreproc",
        "SECRET_SCOPE_PRESENTATION",
        "SECRET_TEMPLATE_SENTENCE",
        "SECRET_SEMANTIC_THEOREM",
        "preprocessing_evidence",
        "semantic_theorem_identity",
        "frozen_evidence",
        "termination_result",
        "certificate_bundle",
        "finite_validity_search_catalog",
        "active_selection_plan",
        "active_plan_digest",
        "registry_digest",
        "selected_entries",
        "realized_uses",
        "finite_validity_rejected",
    ] {
        assert!(!encoded.contains(forbidden), "leaked {forbidden}");
    }
    assert!(!encoded.contains(raw_root.to_string_lossy().as_ref()));
    assert_eq!(
        feedback.presentation().prophecy_map().len(),
        state.catalog().scope().prophecy_bindings().len(),
    );
}

#[tokio::test]
async fn legacy_v2_feedback_snapshot_has_no_current_authority() {
    let (task, state) = pending_fixture('2', 2).await;
    let (_owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(feedback_directory("legacy-v2-state-snapshot")),
    )
    .unwrap();
    let session = PreCertificateAgentHoudiniState::new(
        Arc::clone(&task),
        &artifacts,
        &state,
        Duration::from_secs(17),
        AgentFeedbackPolicy::default(),
    )
    .unwrap();
    let (registration_ordinal, records) = state.catalog().record_snapshot().unwrap();
    let legacy_digest =
        legacy_v2_state_snapshot_digest_for_test(&state, registration_ordinal, records.as_ref())
            .unwrap();

    assert_ne!(legacy_digest, session.feedback().state_snapshot_digest());
}

#[tokio::test]
async fn current_consultation_refresh_rebinds_time_without_advancing_or_repaging() {
    let (task, mut state) = pending_fixture('a', 3).await;
    let (_owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(feedback_directory("current-refresh")),
    )
    .unwrap();
    let mut session = PreCertificateAgentHoudiniState::new(
        Arc::clone(&task),
        &artifacts,
        &state,
        Duration::from_secs(9),
        paging_policy(1),
    )
    .unwrap();
    let before_iteration = session.feedback().iteration();
    let before_consultation = session.feedback().consultation_digest().to_string();
    let before_manifest = session.feedback().validation_manifest_digest().to_string();
    let before_state = session.feedback().state_snapshot_digest().to_string();
    let before_clause_page = session.feedback().clauses().metadata().first_index();
    let before_ledger_page = session.feedback().ledger().metadata().first_index();
    let stale_drop = session.feedback().clauses().items()[0]
        .drop_reference()
        .unwrap()
        .clone();

    let refreshed = session
        .refresh_current_feedback(&state, Duration::from_secs(4))
        .unwrap();
    assert_eq!(refreshed.iteration(), before_iteration);
    assert_eq!(refreshed.remaining_search_budget(), Duration::from_secs(4));
    assert_eq!(refreshed.state_snapshot_digest(), before_state);
    assert_ne!(refreshed.consultation_digest(), before_consultation);
    assert_ne!(refreshed.validation_manifest_digest(), before_manifest);
    assert_eq!(
        refreshed.clauses().metadata().first_index(),
        before_clause_page,
    );
    assert_eq!(
        refreshed.ledger().metadata().first_index(),
        before_ledger_page,
    );
    assert!(!refreshed.authorizes_shown_drop(&stale_drop));
    let current_drop = refreshed.clauses().items()[0]
        .drop_reference()
        .expect("the refreshed page reissues its exact drop authority");
    assert!(refreshed.authorizes_shown_drop(current_drop));

    let proposal =
        FrameworkIIProposalEpoch::new(state.proposal_context().unwrap(), [], []).unwrap();
    run_framework_ii_proposal_epoch(&mut state, &mut InconclusiveChecker, proposal)
        .await
        .unwrap();
    let last_good = session.feedback().to_json_value();
    assert!(matches!(
        session.refresh_current_feedback(&state, Duration::from_secs(3)),
        Err(AgentFeedbackError::StaleLatestFeedback),
    ));
    assert_eq!(session.feedback().to_json_value(), last_good);
}

/// The four pinned event kinds of the contract: `initial`,
/// `postcondition_open` (refuted, naming the attempt whose countermodel the
/// `countermodel` tool serves, or inconclusive with its reason), `failure`,
/// and `counterexample_rejected`. `unresolved`, `cancelled`, and
/// `verification_rejected` are gone.
#[tokio::test]
async fn every_latest_event_kind_is_pinned() {
    let (task, state) = pending_fixture('b', 1).await;
    let root = feedback_directory("event-kinds");
    let (_owner, artifacts) = new_artifact_store(&task, ArtifactStoreConfig::new(&root)).unwrap();
    let mut session = PreCertificateAgentHoudiniState::new(
        Arc::clone(&task),
        &artifacts,
        &state,
        Duration::from_secs(5),
        AgentFeedbackPolicy::default(),
    )
    .unwrap();
    assert_eq!(
        session.feedback().push_value(&[], 0)["latest"]["kind"],
        json!("initial")
    );
    assert!(matches!(
        session.feedback().latest(),
        AgentLatestFeedback::Initial
    ));

    let refuted = AgentSearchFeedback::postcondition_open_refuted(&state, Some(41)).unwrap();
    let wire = session
        .build_next_feedback(&state, &refuted, Duration::from_secs(4))
        .unwrap()
        .push_value(&[], 0);
    assert_eq!(wire["latest"]["kind"], json!("postcondition_open"));
    assert_eq!(
        wire["latest"]["postcondition_open"],
        json!({"outcome": "refuted", "attempt": 41})
    );

    let inconclusive = AgentSearchFeedback::postcondition_open_inconclusive(
        &state,
        FrameworkIIInconclusiveReason::TimedOut,
    )
    .unwrap();
    let wire = session
        .build_next_feedback(&state, &inconclusive, Duration::from_secs(3))
        .unwrap()
        .push_value(&[], 0);
    assert_eq!(wire["latest"]["kind"], json!("postcondition_open"));
    assert_eq!(
        wire["latest"]["postcondition_open"],
        json!({"outcome": "inconclusive", "reason": "timed_out"})
    );

    let failure = AgentSearchFeedback::failure(&state, checker_failure()).unwrap();
    let wire = session
        .build_next_feedback(&state, &failure, Duration::from_secs(2))
        .unwrap()
        .push_value(&[], 0);
    assert_eq!(wire["latest"]["kind"], json!("failure"));

    // A rejected counterexample submission leaves the state alone: the event
    // carries Lean's own code and reason, and `last_round`/`pending` are
    // exactly what the previous epoch left.
    let rejected = AgentSearchFeedback::counterexample_rejected(
        &state,
        "postcondition_holds",
        "the command halts in a state satisfying the postcondition",
    )
    .unwrap();
    let wire = session
        .build_next_feedback(&state, &rejected, Duration::from_secs(1))
        .unwrap()
        .push_value(&[], 0);
    assert_eq!(wire["latest"]["kind"], json!("counterexample_rejected"));
    assert_eq!(
        wire["latest"]["counterexample_rejected"],
        json!({
            "code": "postcondition_holds",
            "reason": "the command halts in a state satisfying the postcondition",
        })
    );
    assert!(matches!(
        session.feedback().latest(),
        AgentLatestFeedback::CounterexampleRejected { .. }
    ));
    assert_eq!(
        AGENT_COUNTEREXAMPLE_REJECTED_KIND,
        "counterexample_rejected"
    );

    let encoded = wire.to_string();
    for retired in ["unresolved", "cancelled", "verification_rejected"] {
        assert!(!encoded.contains(retired), "leaked retired event {retired}");
    }
}

#[tokio::test]
async fn pages_are_deterministic_bounded_and_authorize_only_shown_drops() {
    let (task, state) = pending_fixture('b', 3).await;
    let (_owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(feedback_directory("pages"))).unwrap();
    let policy = paging_policy(1);
    let mut left = PreCertificateAgentHoudiniState::new(
        Arc::clone(&task),
        &artifacts,
        &state,
        Duration::from_secs(11),
        policy.clone(),
    )
    .unwrap();
    let mut right = PreCertificateAgentHoudiniState::new(
        Arc::clone(&task),
        &artifacts,
        &state,
        Duration::from_secs(11),
        policy.clone(),
    )
    .unwrap();
    let mut ledger_session = PreCertificateAgentHoudiniState::new(
        Arc::clone(&task),
        &artifacts,
        &state,
        Duration::from_secs(11),
        policy.clone(),
    )
    .unwrap();
    let mut automatic = PreCertificateAgentHoudiniState::new(
        Arc::clone(&task),
        &artifacts,
        &state,
        Duration::from_secs(11),
        policy,
    )
    .unwrap();
    assert_eq!(
        left.feedback().to_json_value(),
        right.feedback().to_json_value()
    );

    let first_presentation = Arc::clone(left.feedback().presentation());
    let first_page = left.feedback().clauses();
    let first_manifest = left.feedback().validation_manifest().clone();
    assert_eq!(first_page.metadata().total_items(), 3);
    assert_eq!(first_page.metadata().first_index(), 0);
    assert_eq!(first_page.metadata().returned_items(), 1);
    assert_eq!(first_page.items()[0].clause().clause_id().get(), 0);
    assert_eq!(first_page.items()[0].display(), Some("clause display 0"));
    let first_identity = first_page.items()[0].clause().clone();
    let first_record = first_manifest
        .resolve_shown_clause(&first_identity)
        .expect("the exact shown clause resolves in its private manifest");
    assert_eq!(first_record.id(), first_identity.clause_id());
    assert_eq!(
        first_record,
        &state.catalog().record(first_identity.clause_id()).unwrap(),
    );
    let retry_records = first_manifest.pending_records().collect::<Vec<_>>();
    assert_eq!(retry_records.len(), 3);
    for (record, drop_eligible) in retry_records {
        assert!(drop_eligible);
        assert_eq!(record, &state.catalog().record(record.id()).unwrap());
    }
    let first_drop = first_page.items()[0]
        .drop_reference()
        .expect("the unresolved first clause is drop-eligible")
        .clone();
    assert!(left.feedback().authorizes_shown_drop(&first_drop));
    assert_eq!(left.feedback().private_pending_clause_count(), 3);
    let left_cursor = first_page
        .metadata()
        .continuation()
        .expect("three clauses require another page")
        .clone();
    let right_cursor = right
        .feedback()
        .clauses()
        .metadata()
        .continuation()
        .unwrap()
        .clone();
    assert_eq!(left_cursor.offset(), 1);
    assert_eq!(left_cursor.token_digest(), right_cursor.token_digest());

    let latest = AgentSearchFeedback::postcondition_open_refuted(&state, Some(7)).unwrap();
    let ledger_cursor = ledger_session
        .feedback()
        .ledger()
        .metadata()
        .continuation()
        .expect("six attempt rows require another page")
        .clone();
    assert_eq!(ledger_cursor.category(), AgentFeedbackPageCategory::Ledger);
    assert_eq!(ledger_cursor.offset(), 5);
    let clause_page_limit = left.policy().limits().clause_page_items;
    let ledger_page_limit = left.policy().limits().ledger_page_items;
    let left_next = left
        .build_next_feedback_from_cursor(&state, &latest, Duration::from_secs(10), &left_cursor)
        .unwrap();
    let right_next = right
        .build_next_feedback_from_cursor(&state, &latest, Duration::from_secs(10), &right_cursor)
        .unwrap();
    assert_eq!(left_next.to_json_value(), right_next.to_json_value());
    assert_eq!(left_next.clauses().metadata().first_index(), 1);
    assert_eq!(left_next.clauses().metadata().returned_items(), 1);
    assert_eq!(left_next.clauses().items()[0].clause().clause_id().get(), 1);
    let second_identity = left_next.clauses().items()[0].clause().clone();
    // The paged `clauses` window advances, but the push shows every pending
    // clause in `pending`, so both identities remain referenceable by a tool
    // in either consultation.
    assert!(
        first_manifest
            .resolve_shown_clause(&second_identity)
            .is_some()
    );
    assert!(
        left_next
            .validation_manifest()
            .resolve_shown_clause(&first_identity)
            .is_some()
    );
    assert!(
        left_next
            .clauses()
            .items()
            .iter()
            .all(|item| item.clause() != &first_identity)
    );
    assert!(
        left_next
            .validation_manifest()
            .resolve_shown_clause(&second_identity)
            .is_some()
    );
    assert_eq!(
        left_next.clauses().items()[0].display(),
        Some("clause display 1"),
    );
    let second_drop = left_next.clauses().items()[0]
        .drop_reference()
        .expect("the newly shown unresolved clause is drop-eligible");
    assert_ne!(
        second_drop.clause().clause_id(),
        first_drop.clause().clause_id(),
    );
    assert!(left_next.authorizes_shown_drop(second_drop));
    assert!(!left_next.authorizes_shown_drop(&first_drop));
    // Every pending clause's own drop reference is reissued each round.
    let reissued_first_drop = left_next
        .drop_references()
        .find(|reference| reference.clause().clause_id() == first_drop.clause().clause_id())
        .expect("every pending clause carries a drop reference in the push");
    assert!(left_next.authorizes_shown_drop(reissued_first_drop));
    assert_eq!(left_next.private_pending_clause_count(), 3);
    assert!(Arc::ptr_eq(&first_presentation, left_next.presentation()));
    assert!(left_next.clauses().metadata().returned_items() <= clause_page_limit,);
    assert!(left_next.ledger().metadata().returned_items() <= ledger_page_limit,);

    let ledger_next = ledger_session
        .build_next_feedback_from_cursor(&state, &latest, Duration::from_secs(10), &ledger_cursor)
        .unwrap();
    // Three clauses, each inconclusive at level 0 and then checked again at
    // level 1 with its launch suppressed: six attempt rows.
    assert_eq!(ledger_next.ledger().metadata().total_items(), 6);
    assert_eq!(ledger_next.ledger().metadata().first_index(), 4);
    assert_eq!(ledger_next.ledger().metadata().returned_items(), 1);

    let automatic_next = automatic
        .build_next_feedback(&state, &latest, Duration::from_secs(10))
        .unwrap();
    assert_eq!(automatic_next.clauses().metadata().first_index(), 1);
    assert_eq!(automatic_next.ledger().metadata().first_index(), 4);
}

#[tokio::test]
async fn minimum_page_cap_bounds_actual_clause_and_ledger_wire_objects() {
    let (task, state) = pending_fixture('1', 3).await;
    let (_owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(feedback_directory("minimum-page")),
    )
    .unwrap();
    let policy = minimum_page_policy();
    let page_limit = policy.limits().max_page_bytes;
    let session = PreCertificateAgentHoudiniState::new(
        task,
        &artifacts,
        &state,
        Duration::from_secs(6),
        policy,
    )
    .unwrap();
    let wire = session.feedback().to_json_value();
    let clause_bytes = serde_json::to_vec(&wire["clauses"]).unwrap().len();
    let ledger_bytes = serde_json::to_vec(&wire["ledger"]).unwrap().len();
    assert!(
        clause_bytes <= page_limit,
        "clause page used {clause_bytes}"
    );
    assert!(
        ledger_bytes <= page_limit,
        "ledger page used {ledger_bytes}"
    );
    assert!(session.feedback().clauses().metadata().returned_items() > 0);
    assert!(session.feedback().ledger().metadata().returned_items() > 0);
}

#[tokio::test]
async fn presentation_prose_and_history_mode_do_not_change_semantic_identity() {
    let first_task = Arc::new(feedback_task("first prose"));
    let second_task = Arc::new(feedback_task("second prose"));
    assert_eq!(first_task.identity(), second_task.identity());
    let scope = feedback_scope(&first_task);
    let catalog = feedback_catalog(&scope, 'c');
    let first_state = LeveledHoudiniState::new(catalog.clone()).unwrap();
    let second_state = LeveledHoudiniState::new(catalog).unwrap();
    let (_first_owner, first_artifacts) = new_artifact_store(
        &first_task,
        ArtifactStoreConfig::new(feedback_directory("history-disabled")),
    )
    .unwrap();
    let (_history_owner, history_artifacts) = new_artifact_store(
        &first_task,
        ArtifactStoreConfig::new(feedback_directory("history-enabled"))
            .maintenance_history(true, false),
    )
    .unwrap();
    let first = PreCertificateAgentHoudiniState::new(
        Arc::clone(&first_task),
        &first_artifacts,
        &first_state,
        Duration::from_secs(9),
        AgentFeedbackPolicy::default(),
    )
    .unwrap();
    let with_history = PreCertificateAgentHoudiniState::new(
        Arc::clone(&first_task),
        &history_artifacts,
        &first_state,
        Duration::from_secs(9),
        AgentFeedbackPolicy::default(),
    )
    .unwrap();
    let second = PreCertificateAgentHoudiniState::new(
        Arc::clone(&second_task),
        &first_artifacts,
        &second_state,
        Duration::from_secs(9),
        AgentFeedbackPolicy::default(),
    )
    .unwrap();

    assert_ne!(
        first.feedback().presentation().presentation_digest(),
        second.feedback().presentation().presentation_digest(),
    );
    assert_eq!(
        first.feedback().task_digest(),
        second.feedback().task_digest()
    );
    assert_eq!(
        first.feedback().scope_digest(),
        second.feedback().scope_digest()
    );
    assert_eq!(
        first.feedback().run_digest(),
        second.feedback().run_digest()
    );
    assert_eq!(
        first.feedback().state_snapshot_digest(),
        second.feedback().state_snapshot_digest(),
    );
    assert_eq!(
        first.feedback().consultation_digest(),
        second.feedback().consultation_digest(),
    );
    assert_eq!(
        first.feedback().validation_manifest_digest(),
        second.feedback().validation_manifest_digest(),
    );
    assert_ne!(
        first.feedback().to_json_value(),
        second.feedback().to_json_value()
    );

    let without_history = first.feedback().to_json_value();
    let with_history = with_history.feedback().to_json_value();
    for field in ["presentation", "latest", "summary", "clauses", "ledger"] {
        assert_eq!(without_history[field], with_history[field]);
    }
    assert_ne!(
        without_history["binding"]["consultation_digest"],
        with_history["binding"]["consultation_digest"],
    );
    assert_ne!(
        without_history["binding"]["validation_manifest_digest"],
        with_history["binding"]["validation_manifest_digest"],
    );
}

#[tokio::test]
async fn session_budget_and_backend_bind_drops_artifacts_and_debug_output() {
    let (task, state) = pending_fixture('2', 3).await;
    let shared_root = feedback_directory("shared-backend");
    let foreign_root = feedback_directory("foreign-backend");
    let (_shared_owner, shared_artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(&shared_root)).unwrap();
    let (_foreign_owner, foreign_artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(&foreign_root)).unwrap();
    let policy = paging_policy(1);
    let mut left = PreCertificateAgentHoudiniState::new(
        Arc::clone(&task),
        &shared_artifacts,
        &state,
        Duration::from_secs(5),
        policy.clone(),
    )
    .unwrap();
    let mut twin = PreCertificateAgentHoudiniState::new(
        Arc::clone(&task),
        &shared_artifacts,
        &state,
        Duration::from_secs(5),
        policy.clone(),
    )
    .unwrap();
    let foreign = PreCertificateAgentHoudiniState::new(
        Arc::clone(&task),
        &foreign_artifacts,
        &state,
        Duration::from_secs(5),
        policy.clone(),
    )
    .unwrap();
    let budget_variant = PreCertificateAgentHoudiniState::new(
        Arc::clone(&task),
        &shared_artifacts,
        &state,
        Duration::from_secs(6),
        policy,
    )
    .unwrap();

    assert_eq!(
        left.feedback().to_json_value(),
        twin.feedback().to_json_value()
    );
    let left_drop = left.feedback().clauses().items()[0]
        .drop_reference()
        .unwrap()
        .clone();
    let foreign_drop = foreign.feedback().clauses().items()[0]
        .drop_reference()
        .unwrap()
        .clone();
    let budget_drop = budget_variant.feedback().clauses().items()[0]
        .drop_reference()
        .unwrap()
        .clone();
    assert_ne!(
        left.feedback().consultation_digest(),
        foreign.feedback().consultation_digest(),
    );
    assert_ne!(
        left_drop.authorization_digest(),
        foreign_drop.authorization_digest()
    );
    assert!(!left.feedback().authorizes_shown_drop(&foreign_drop));
    assert!(!foreign.feedback().authorizes_shown_drop(&left_drop));
    assert_ne!(
        left.feedback().consultation_digest(),
        budget_variant.feedback().consultation_digest(),
    );
    assert_ne!(
        left_drop.authorization_digest(),
        budget_drop.authorization_digest()
    );
    assert!(!left.feedback().authorizes_shown_drop(&budget_drop));

    let shared_reference = shared_artifacts
        .publish(
            ArtifactKind::FailureDiagnostic,
            b"SECRET_DIAGNOSTIC_PAYLOAD".to_vec().into_boxed_slice(),
        )
        .unwrap();
    let foreign_reference = foreign_artifacts
        .publish(
            ArtifactKind::FailureDiagnostic,
            b"SECRET_DIAGNOSTIC_PAYLOAD".to_vec().into_boxed_slice(),
        )
        .unwrap();
    let shared_latest = AgentSearchFeedback::failure(
        &state,
        diagnostic_failure(shared_reference, "SECRET_FAILURE_DETAIL"),
    )
    .unwrap();
    let foreign_latest = AgentSearchFeedback::failure(
        &state,
        diagnostic_failure(foreign_reference, "SECRET_FAILURE_DETAIL"),
    )
    .unwrap();
    assert!(matches!(
        left.build_next_feedback(&state, &foreign_latest, Duration::from_secs(4)),
        Err(AgentFeedbackError::ForeignArtifactReference),
    ));
    let debug = format!(
        "{left:?} {:?} {:?} {shared_latest:?}",
        left.feedback(),
        left.feedback().clauses().metadata().continuation().unwrap(),
    );
    for forbidden in [
        "SECRET_FAILURE_DETAIL",
        "SECRET_DIAGNOSTIC_PAYLOAD",
        "SECRET_SEMANTIC_THEOREM",
        "test_lean_checked_binding",
        shared_root.to_string_lossy().as_ref(),
        foreign_root.to_string_lossy().as_ref(),
    ] {
        assert!(!debug.contains(forbidden), "Debug leaked {forbidden}");
    }

    let left_next = left
        .build_next_feedback(&state, &shared_latest, Duration::from_secs(4))
        .unwrap()
        .to_json_value();
    let twin_next = twin
        .build_next_feedback(&state, &shared_latest, Duration::from_secs(4))
        .unwrap()
        .to_json_value();
    let mut foreign = foreign;
    let foreign_next = foreign
        .build_next_feedback(&state, &foreign_latest, Duration::from_secs(4))
        .unwrap()
        .to_json_value();
    assert_eq!(left_next, twin_next);
    let shared_stable_id = left_next["latest"]["failure"]["artifacts"][0]["stable_id"]
        .as_str()
        .unwrap();
    let foreign_stable_id = foreign_next["latest"]["failure"]["artifacts"][0]["stable_id"]
        .as_str()
        .unwrap();
    assert_ne!(shared_stable_id, foreign_stable_id);
    let encoded = serde_json::to_string(&[left_next, foreign_next]).unwrap();
    assert!(!encoded.contains("SECRET_FAILURE_DETAIL"));
    assert!(!encoded.contains("SECRET_DIAGNOSTIC_PAYLOAD"));
    assert!(!encoded.contains(shared_root.to_string_lossy().as_ref()));
    assert!(!encoded.contains(foreign_root.to_string_lossy().as_ref()));
}

/// Milestone 7.5 review, finding 8. There is no hard-coded bound on display
/// text any more: a large clause display and a large task text are both
/// presented in full. The memory a push may occupy is bounded by the
/// push-size guard, whose failure is a run-global resource fault, and a run
/// that wants a stated bound on submitted clause text declares the optional
/// `clause_text_bytes` host limit. What still shortens a *page* is the page
/// fitter, which carries an item as its `summarized` form and says so.
#[tokio::test]
async fn a_large_clause_display_and_a_large_task_text_are_presented_in_full() {
    let task = Arc::new(feedback_task("oversized"));
    let scope = feedback_scope(&task);
    let large = format!("LARGE_CLAUSE_{}", "x".repeat(64 * 1024));
    let clause = feedback_clause_with_display(&scope, 0, large.clone());
    let catalog = feedback_catalog(&scope, '3');
    let mut state = LeveledHoudiniState::new(catalog).unwrap();
    let proposal =
        FrameworkIIProposalEpoch::new(state.proposal_context().unwrap(), [clause.clone()], [])
            .unwrap();
    run_framework_ii_proposal_epoch(&mut state, &mut InconclusiveChecker, proposal)
        .await
        .unwrap();
    let (_owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(feedback_directory("oversized-display")),
    )
    .unwrap();
    let session = PreCertificateAgentHoudiniState::new(
        task,
        &artifacts,
        &state,
        Duration::from_secs(3),
        AgentFeedbackPolicy::default(),
    )
    .unwrap();
    let item = &session.feedback().clauses().items()[0];
    assert_eq!(item.clause().formula_digest(), clause.identity_sha256());
    assert_eq!(
        item.display().map(|display| display.to_string()),
        Some(large.clone()),
        "a large clause display is presented in full, never truncated or dropped"
    );
    assert!(
        session
            .feedback()
            .to_json_string()
            .unwrap()
            .contains(&large)
    );

    // The task's own display strings go through the same check, which is a
    // safety check and no longer a size one: a megabyte of task text is
    // accepted, and a control character is still refused.
    let huge_task_text = "T".repeat(1024 * 1024);
    assert!(super::feedback::validate_presentation_text(&huge_task_text).is_ok());
    assert!(super::feedback::validate_presentation_text("line\nand\ttab").is_ok());
    assert!(super::feedback::validate_presentation_text("").is_err());
    assert!(super::feedback::validate_presentation_text("bell\u{7}").is_err());
}

#[tokio::test]
async fn stale_and_cross_run_feedback_authority_is_rejected() {
    let (task, first_state) = pending_fixture('d', 3).await;
    let (_, second_state) = pending_fixture('e', 3).await;
    let (_owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(feedback_directory("stale"))).unwrap();
    let policy = paging_policy(1);
    let mut first = PreCertificateAgentHoudiniState::new(
        Arc::clone(&task),
        &artifacts,
        &first_state,
        Duration::from_secs(8),
        policy.clone(),
    )
    .unwrap();
    let mut peer = PreCertificateAgentHoudiniState::new(
        Arc::clone(&task),
        &artifacts,
        &first_state,
        Duration::from_secs(8),
        policy,
    )
    .unwrap();
    let cursor = first
        .feedback()
        .clauses()
        .metadata()
        .continuation()
        .unwrap()
        .clone();
    let latest = AgentSearchFeedback::postcondition_open_refuted(&first_state, Some(7)).unwrap();

    assert!(matches!(
        peer.build_next_feedback_from_cursor(
            &first_state,
            &latest,
            Duration::from_secs(7),
            &cursor,
        ),
        Err(AgentFeedbackError::StaleCursor),
    ));
    assert!(matches!(
        first.build_next_feedback(&second_state, &latest, Duration::from_secs(7),),
        Err(AgentFeedbackError::WrongRun),
    ));

    let (_second_owner, second_artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(feedback_directory("cross-run")),
    )
    .unwrap();
    let mut second = PreCertificateAgentHoudiniState::new(
        task,
        &second_artifacts,
        &second_state,
        Duration::from_secs(8),
        paging_policy(1),
    )
    .unwrap();
    assert!(matches!(
        second.build_next_feedback(&second_state, &latest, Duration::from_secs(7),),
        Err(AgentFeedbackError::StaleLatestFeedback),
    ));
}

#[tokio::test]
async fn ledger_feedback_preserves_outcomes_routes_and_row_chain() {
    let (proved_task, proved_state) = conclusive_fixture('4', ConclusiveOutcome::Proved).await;
    let (refuted_task, refuted_state) = conclusive_fixture('5', ConclusiveOutcome::Refuted).await;
    let (_proved_owner, proved_artifacts) = new_artifact_store(
        &proved_task,
        ArtifactStoreConfig::new(feedback_directory("proved-ledger")),
    )
    .unwrap();
    let (_refuted_owner, refuted_artifacts) = new_artifact_store(
        &refuted_task,
        ArtifactStoreConfig::new(feedback_directory("refuted-ledger")),
    )
    .unwrap();
    let proved = PreCertificateAgentHoudiniState::new(
        proved_task,
        &proved_artifacts,
        &proved_state,
        Duration::from_secs(2),
        AgentFeedbackPolicy::default(),
    )
    .unwrap();
    let refuted = PreCertificateAgentHoudiniState::new(
        refuted_task,
        &refuted_artifacts,
        &refuted_state,
        Duration::from_secs(2),
        AgentFeedbackPolicy::default(),
    )
    .unwrap();

    let proved_wire = proved.feedback().to_json_value();
    let proved_rows = proved_wire["ledger"]["items"].as_array().unwrap();
    assert_eq!(proved_rows.len(), 2);
    assert_eq!(proved_wire["summary"]["proved_attempts"], 2);
    assert_eq!(proved_wire["summary"]["current_roots"], 2);
    assert_eq!(
        proved_wire["clauses"]["items"][0]["status"],
        json!({"kind": "committed", "level": 0}),
    );
    assert_eq!(proved_rows[0]["result"]["outcome"]["kind"], "proved");
    assert_eq!(proved_rows[1]["result"]["outcome"]["kind"], "proved");
    assert_eq!(proved_rows[0]["result"]["route"]["kind"], "test_scaffold");
    assert_eq!(proved_rows[1]["result"]["route"]["kind"], "test_scaffold");
    assert_eq!(proved_rows[0]["solver_time_nanos"], Value::Null);
    assert_eq!(proved_rows[1]["solver_time_nanos"], Value::Null);
    assert!(proved_rows[0].get("selected_entry_count").is_none());
    assert!(proved_rows[0].get("selected_entries").is_none());
    assert_eq!(proved_rows[0]["previous_row_digest"], Value::Null);
    assert_eq!(
        proved_rows[1]["previous_row_digest"],
        proved_rows[0]["row_digest"],
    );

    // A refuted clause that mentions a prophecy relation is promoted, not
    // killed: it is checked once at level 0 and once at level 1, then ends
    // the scan pending at 1.
    let refuted_wire = refuted.feedback().to_json_value();
    let refuted_rows = refuted_wire["ledger"]["items"].as_array().unwrap();
    assert_eq!(refuted_rows.len(), 2);
    assert_eq!(refuted_wire["summary"]["refuted_attempts"], 2);
    assert_eq!(refuted_wire["summary"]["pending_clauses"], 1);
    assert_eq!(refuted_wire["summary"]["dead_clauses"], 0);
    assert_eq!(refuted_rows[0]["result"]["outcome"]["kind"], "refuted",);
    assert_eq!(refuted_rows[0]["result"]["route"]["kind"], "test_scaffold",);
    assert_eq!(refuted_rows[0]["level"], 0);
    assert_eq!(refuted_rows[1]["level"], 1);
    assert_eq!(refuted_rows[0]["solver_time_nanos"], Value::Null);
    assert!(refuted_rows[0].get("selected_entry_count").is_none());
    assert_eq!(refuted_rows[0]["previous_row_digest"], Value::Null);
}

#[tokio::test]
async fn real_routes_are_typed_sanitized_and_hide_library_state() {
    let cases = [
        (
            '6',
            "runtime-route",
            RealRouteKind::RuntimeProof,
            "runtime_proof",
            "proved",
            2_usize,
            3_usize,
        ),
        (
            '8',
            "refutation-route",
            RealRouteKind::ValidatedRefutation,
            "validated_refutation",
            "refuted",
            // Refuted at level 0, promoted, refuted again at level 1.
            2,
            3,
        ),
        (
            '9',
            "progress-route",
            RealRouteKind::RetryProgress,
            "retry_progress",
            "inconclusive",
            // Inconclusive at level 0, promoted, checked again at level 1
            // with its launch suppressed — a suspended check still records
            // its ledger row.
            2,
            2,
        ),
    ];

    for (
        marker,
        label,
        route_kind,
        expected_route,
        expected_outcome,
        expected_rows,
        artifacts_per_row,
    ) in cases
    {
        let (task, mut state, proposal) = real_route_fixture(marker, label);
        let root = feedback_directory(label);
        let (_owner, artifacts) =
            new_artifact_store(&task, ArtifactStoreConfig::new(&root)).unwrap();
        let outcome = run_framework_ii_proposal_epoch(
            &mut state,
            &mut RealRouteChecker {
                route: route_kind,
                artifacts: artifacts.clone(),
            },
            proposal,
        )
        .await
        .unwrap();
        if matches!(route_kind, RealRouteKind::RetryProgress) {
            assert!(matches!(
                outcome.outcome(),
                FrameworkIIEpochOutcome::Refuted { .. }
            ));
        }
        let session = PreCertificateAgentHoudiniState::new(
            task,
            &artifacts,
            &state,
            Duration::from_secs(4),
            AgentFeedbackPolicy::default(),
        )
        .unwrap();
        let wire = session.feedback().to_json_value();
        let rows = wire["ledger"]["items"].as_array().unwrap();
        assert_eq!(rows.len(), expected_rows, "route {expected_route}");
        let expected_solver_time_nanos = match route_kind {
            RealRouteKind::RuntimeProof => 4_242,
            RealRouteKind::ValidatedRefutation => 9_009,
            RealRouteKind::RetryProgress => 1_001,
        };
        for row in rows {
            assert_eq!(row["result"]["outcome"]["kind"], expected_outcome,);
            let route = &row["result"]["route"];
            assert_eq!(route["kind"], expected_route);
            assert!(route.get("realized_uses").is_none());
            assert!(route.get("selection_digest").is_none());
            assert_eq!(stable_ids(route).len(), artifacts_per_row);
            assert_eq!(row["solver_time_nanos"], expected_solver_time_nanos);
        }
        if matches!(route_kind, RealRouteKind::RetryProgress) {
            let peer = &rows[0]["result"]["route"]["peer_failure"];
            assert_eq!(peer["has_withheld_detail"], true);
            assert_eq!(peer["artifacts"][0]["kind"], "failure_diagnostic");
        }
        let all_ids = stable_ids(&wire["ledger"]);
        let unique_ids = all_ids.iter().collect::<std::collections::BTreeSet<_>>();
        assert_eq!(all_ids.len(), unique_ids.len());
        let encoded = serde_json::to_string(&wire).unwrap();
        for forbidden in [
            "SECRET_TEST_INVOCATION_ARGUMENT",
            "SECRET_ROUTE_PEER_DETAIL",
            "SECRET_ROUTE_PEER_PAYLOAD",
            "hidden feedback terminal",
            "hidden feedback progress terminal",
            "hidden feedback refutation terminal",
            "runtime_trace",
            root.to_string_lossy().as_ref(),
        ] {
            assert!(
                !encoded.contains(forbidden),
                "route {expected_route} leaked {forbidden}",
            );
        }
    }
}

/// A dropped clause is dead by drop, not a partition of its own: the wire
/// shows `dead` with cause `dropped`, and it is absent from `pending`.
#[tokio::test]
async fn a_dropped_clause_is_dead_by_drop_and_leaves_the_pending_list() {
    let (drop_task, mut drop_state) = pending_fixture('b', 1).await;
    let context = drop_state.proposal_context().unwrap();
    let clause = context.drop_eligible_records()[0].id();
    let drop_token = context.drop_token(clause).unwrap();
    let drop_proposal = FrameworkIIProposalEpoch::new(context, [], [drop_token]).unwrap();
    run_framework_ii_proposal_epoch(&mut drop_state, &mut InconclusiveChecker, drop_proposal)
        .await
        .unwrap();
    assert!(drop_state.is_dropped(clause));
    assert!(!drop_state.pending_levels().contains_key(&clause));
    let (_drop_owner, drop_artifacts) = new_artifact_store(
        &drop_task,
        ArtifactStoreConfig::new(feedback_directory("explicit-drop")),
    )
    .unwrap();
    let dropped = PreCertificateAgentHoudiniState::new(
        drop_task,
        &drop_artifacts,
        &drop_state,
        Duration::from_secs(1),
        AgentFeedbackPolicy::default(),
    )
    .unwrap();
    let status = &dropped.feedback().to_json_value()["clauses"]["items"][0]["status"];
    assert_eq!(status["kind"], "dead");
    assert_eq!(status["cause"], "dropped");
    let push = dropped.feedback().push_value(&[], 0);
    assert_eq!(push["pending"].as_array().unwrap().len(), 0);
}

#[tokio::test]
async fn automatic_paging_survives_state_revision_changes() {
    let (task, mut state) = pending_fixture('d', 3).await;
    let (_owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(feedback_directory("revision-paging")),
    )
    .unwrap();
    let mut session = PreCertificateAgentHoudiniState::new(
        task,
        &artifacts,
        &state,
        Duration::from_secs(3),
        paging_policy(1),
    )
    .unwrap();
    assert_eq!(session.feedback().clauses().metadata().first_index(), 0);
    let revision = state.proposal_revision();
    let proposal =
        FrameworkIIProposalEpoch::new(state.proposal_context().unwrap(), [], []).unwrap();
    run_framework_ii_proposal_epoch(&mut state, &mut InconclusiveChecker, proposal)
        .await
        .unwrap();
    assert!(state.proposal_revision() > revision);
    let latest = AgentSearchFeedback::postcondition_open_refuted(&state, Some(7)).unwrap();
    let next = session
        .build_next_feedback(&state, &latest, Duration::from_secs(2))
        .unwrap();
    assert_eq!(next.clauses().metadata().first_index(), 1);
    // Three clauses, each inconclusive at level 0 and then checked again at
    // level 1 with its launch suppressed: six attempt rows, so the second
    // one-row ledger page starts at index four.
    assert_eq!(next.ledger().metadata().first_index(), 4);
}

#[tokio::test]
async fn summarized_routes_keep_compact_identity_and_authorize_no_hidden_artifact() {
    let task = Arc::new(feedback_task("summarized-route"));
    let scope = feedback_scope(&task);
    let clauses = (0..32)
        .map(|ordinal| feedback_clause(&scope, ordinal))
        .collect::<Vec<_>>();
    let catalog = feedback_catalog(&scope, 'f');
    let mut state = LeveledHoudiniState::new(catalog).unwrap();
    let proposal =
        FrameworkIIProposalEpoch::new(state.proposal_context().unwrap(), clauses, []).unwrap();
    let (_owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(feedback_directory("summarized-route")),
    )
    .unwrap();
    run_framework_ii_proposal_epoch(
        &mut state,
        &mut RealRouteChecker {
            route: RealRouteKind::RuntimeProof,
            artifacts: artifacts.clone(),
        },
        proposal,
    )
    .await
    .unwrap();

    let wide = PreCertificateAgentHoudiniState::new(
        Arc::clone(&task),
        &artifacts,
        &state,
        Duration::from_secs(2),
        AgentFeedbackPolicy::default(),
    )
    .unwrap();
    let first_reference = wide
        .feedback()
        .ledger()
        .items()
        .iter()
        .find_map(|row| match row {
            AgentLedgerFeedback::Attempt { outcome, .. } => match outcome.route() {
                Some(AgentEvidenceRoute::RuntimeProof { artifacts, .. }) => {
                    Some(artifacts[0].clone())
                }
                _ => None,
            },
            AgentLedgerFeedback::Invalidation { .. } => None,
        })
        .expect("the wide page keeps at least one detailed runtime route");

    let compact = PreCertificateAgentHoudiniState::new(
        task,
        &artifacts,
        &state,
        Duration::from_secs(2),
        summarizing_page_policy(4_608),
    )
    .unwrap();
    let compact_wire = compact.feedback().to_json_value();
    let row = &compact_wire["ledger"]["items"][0];
    assert_eq!(row["result"]["route"], Value::Null);
    assert_eq!(row["result"]["route_kind"], "runtime_proof");
    assert!(row["result"].get("realized_use_count").is_none());
    assert!(row["result"].get("realized_use_list_digest").is_none());
    assert!(row.get("selections_summarized").is_none());
    assert!(
        !compact
            .feedback()
            .issued_artifact_reference(&first_reference)
    );
    assert!(
        !compact_wire
            .to_string()
            .contains(first_reference.stable_id())
    );
    assert!(
        serde_json::to_vec(&compact_wire["ledger"]).unwrap().len()
            <= compact.policy().limits().max_page_bytes,
    );
}

#[tokio::test]
async fn policy_and_run_caps_fail_closed() {
    let invalid = AgentFeedbackLimits {
        clause_page_items: 0,
        ..AgentFeedbackLimits::default()
    };
    assert!(matches!(
        AgentFeedbackPolicy::new(invalid),
        Err(AgentFeedbackError::InvalidPolicy(_)),
    ));

    let (task, state) = pending_fixture('f', 3).await;
    let (_owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(feedback_directory("caps"))).unwrap();
    let limits = AgentFeedbackLimits {
        host_limits: HostLimits {
            catalog_size: Some(2),
            ..HostLimits::UNBOUNDED
        },
        clause_page_items: 2,
        ..AgentFeedbackLimits::default()
    };
    let policy = AgentFeedbackPolicy::new(limits).unwrap();
    assert!(matches!(
        PreCertificateAgentHoudiniState::new(
            task,
            &artifacts,
            &state,
            Duration::from_secs(1),
            policy,
        ),
        Err(AgentFeedbackError::TrackedClauseLimit { found: 3, limit: 2 }),
    ));
}

// ------------------------------------------------------------
// Pass 7.5c: `AgentFeedback::push_value`
// ------------------------------------------------------------

fn feedback_clause_prophecy_free(scope: &FixedAmbientTaskScope, ordinal: u64) -> ExtendedClause {
    let identity = json!(["feedback-clause-prophecy-free", ordinal]);
    ExtendedClause::new(
        scope.clone(),
        identity.clone(),
        format!("pf-{ordinal:04}"),
        format!("prophecy-free clause display {ordinal}"),
        vec!["rel:R:0".to_string()],
        false,
        FrameworkIILevel::ZERO,
    )
}

fn checker_failure() -> FailureReport {
    FailureReport::try_new(
        FailureOrigin::AgentConsultation,
        FailureKind::TransportFailure,
        true,
        FailureScope::LaneLocal,
        None,
        Vec::new(),
    )
    .unwrap()
}

/// Records ordinary checked progress before a later scan failure. Rollback
/// must preserve the resulting ledger provenance while restoring partitions.
struct FailingChecker {
    progress: RealRouteChecker,
}

impl super::stabilization::sealed::Sealed for FailingChecker {}

impl FrameworkIIChecker for FailingChecker {
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
        if request.clause().get() == 1 && request.level() == FrameworkIILevel::ONE {
            Box::pin(std::future::ready(Ok(FrameworkIICheckExecution::Failure(
                checker_failure(),
            ))))
        } else {
            self.progress.check(request)
        }
    }

    fn check_termination<'a>(
        &'a mut self,
        _core: Arc<LeveledCandidateSnapshot>,
    ) -> Pin<
        Box<
            dyn Future<Output = Result<FrameworkIICheckExecution, FrameworkIIStateError>>
                + Send
                + 'a,
        >,
    > {
        Box::pin(std::future::ready(Ok(refuted_termination())))
    }
}

/// Refutes exactly the first check it receives, then proves every check
/// after that — mirroring the checked
/// `prophecy_bearing_level_zero_initialization_refutation_still_promotes`
/// scripted sequence in `proposal_tests.rs`, so a single prophecy-bearing
/// clause promotes from level zero and then commits at level one.
struct PromoteThenProveChecker {
    used: bool,
}

impl super::stabilization::sealed::Sealed for PromoteThenProveChecker {}

impl FrameworkIIChecker for PromoteThenProveChecker {
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
        let evidence = FrameworkIICheckEvidence::new(
            request.request_digest(),
            format!("feedback-promote:{}", request.request_digest()),
        )
        .unwrap();
        let outcome = if self.used {
            FrameworkIICheckOutcome::Proved(evidence)
        } else {
            self.used = true;
            FrameworkIICheckOutcome::Refuted(evidence)
        };
        Box::pin(std::future::ready(Ok(FrameworkIICheckExecution::Applied(
            outcome,
        ))))
    }

    fn check_termination<'a>(
        &'a mut self,
        _core: Arc<LeveledCandidateSnapshot>,
    ) -> Pin<
        Box<
            dyn Future<Output = Result<FrameworkIICheckExecution, FrameworkIIStateError>>
                + Send
                + 'a,
        >,
    > {
        Box::pin(std::future::ready(Ok(refuted_termination())))
    }
}

struct PreparationTimeChecker;

impl super::stabilization::sealed::Sealed for PreparationTimeChecker {}

impl FrameworkIIChecker for PreparationTimeChecker {
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
        let evidence = FrameworkIICheckEvidence::new(
            request.request_digest(),
            format!("feedback-prep:{}", request.request_digest()),
        )
        .unwrap()
        .with_preparation_time(Some(Duration::from_nanos(4_444)));
        Box::pin(std::future::ready(Ok(FrameworkIICheckExecution::Applied(
            FrameworkIICheckOutcome::Proved(evidence),
        ))))
    }

    fn check_termination<'a>(
        &'a mut self,
        _core: Arc<LeveledCandidateSnapshot>,
    ) -> Pin<
        Box<
            dyn Future<Output = Result<FrameworkIICheckExecution, FrameworkIIStateError>>
                + Send
                + 'a,
        >,
    > {
        Box::pin(std::future::ready(Ok(refuted_termination())))
    }
}

async fn dead_clause_fixture(marker: char) -> (Arc<SynthesisTask>, LeveledHoudiniState, ClauseId) {
    let task = Arc::new(feedback_task("dead"));
    let scope = feedback_scope(&task);
    let clause = feedback_clause_prophecy_free(&scope, 0);
    let catalog = feedback_catalog(&scope, marker);
    let mut state = LeveledHoudiniState::new(catalog).unwrap();
    let proposal =
        FrameworkIIProposalEpoch::new(state.proposal_context().unwrap(), [clause.clone()], [])
            .unwrap();
    run_framework_ii_proposal_epoch(
        &mut state,
        &mut ConclusiveChecker(ConclusiveOutcome::Refuted),
        proposal,
    )
    .await
    .unwrap();
    let clause_id = state.catalog().find(&clause).unwrap().unwrap();
    assert!(state.is_dead(clause_id));
    (task, state, clause_id)
}

async fn pending_last_round_fixture(
    marker: char,
) -> (
    Arc<SynthesisTask>,
    LeveledHoudiniState,
    ClauseId,
    FrameworkIILevel,
) {
    let task = Arc::new(feedback_task("pending"));
    let scope = feedback_scope(&task);
    let clause = feedback_clause(&scope, 0);
    let catalog = feedback_catalog(&scope, marker);
    let mut state = LeveledHoudiniState::new(catalog).unwrap();
    let proposal =
        FrameworkIIProposalEpoch::new(state.proposal_context().unwrap(), [clause.clone()], [])
            .unwrap();
    // An inconclusive scan, not a failed epoch: an epoch that ends in an
    // infrastructure fault is rolled back whole (Milestone 7.5 review,
    // finding 2), so it leaves nothing pending to report. That case is
    // `push_after_a_rolled_back_epoch_shows_neither_outcome_nor_clause`
    // below, where the whole batch is absent rather than pending.
    let outcome = run_framework_ii_proposal_epoch(&mut state, &mut InconclusiveChecker, proposal)
        .await
        .unwrap();
    assert!(matches!(
        outcome.outcome(),
        FrameworkIIEpochOutcome::Refuted { .. } | FrameworkIIEpochOutcome::Inconclusive { .. }
    ));
    let clause_id = state.catalog().find(&clause).unwrap().unwrap();
    let level = *state
        .pending_levels()
        .get(&clause_id)
        .expect("an inconclusive clause stays pending");
    (task, state, clause_id, level)
}

/// Two independently committed clauses at different levels in the same
/// state, so the push's `core` ordering (ascending level, then canonical
/// order) is distinguishable from mere registration order: `zero_level`
/// registers second but must still appear first.
async fn two_level_core_fixture(
    marker: char,
) -> (Arc<SynthesisTask>, LeveledHoudiniState, ClauseId, ClauseId) {
    let task = Arc::new(feedback_task("two-level"));
    let scope = feedback_scope(&task);
    let catalog = feedback_catalog(&scope, marker);
    let mut state = LeveledHoudiniState::new(catalog).unwrap();

    let promoted = feedback_clause(&scope, 0);
    let proposal_a =
        FrameworkIIProposalEpoch::new(state.proposal_context().unwrap(), [promoted.clone()], [])
            .unwrap();
    run_framework_ii_proposal_epoch(
        &mut state,
        &mut PromoteThenProveChecker { used: false },
        proposal_a,
    )
    .await
    .unwrap();
    let promoted_id = state.catalog().find(&promoted).unwrap().unwrap();
    assert_eq!(
        state.committed_levels().get(&promoted_id),
        Some(&FrameworkIILevel::ONE)
    );

    let zero_level = feedback_clause(&scope, 1);
    let proposal_b =
        FrameworkIIProposalEpoch::new(state.proposal_context().unwrap(), [zero_level.clone()], [])
            .unwrap();
    run_framework_ii_proposal_epoch(
        &mut state,
        &mut ConclusiveChecker(ConclusiveOutcome::Proved),
        proposal_b,
    )
    .await
    .unwrap();
    let zero_level_id = state.catalog().find(&zero_level).unwrap().unwrap();
    assert_eq!(
        state.committed_levels().get(&zero_level_id),
        Some(&FrameworkIILevel::ZERO)
    );

    (task, state, promoted_id, zero_level_id)
}

fn push_key_set(push: &Value) -> BTreeSet<String> {
    push.as_object()
        .unwrap()
        .keys()
        .cloned()
        .collect::<BTreeSet<_>>()
}

#[tokio::test]
async fn push_value_pins_the_exact_key_set_and_omits_retired_pages() {
    let (task, state) = pending_fixture('0', 2).await;
    let (_owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(feedback_directory("push-keys")),
    )
    .unwrap();
    let session = PreCertificateAgentHoudiniState::new(
        Arc::clone(&task),
        &artifacts,
        &state,
        Duration::from_secs(5),
        AgentFeedbackPolicy::default(),
    )
    .unwrap();
    let push = session.feedback().push_value(&["submit", "history"], 42);

    let expected: BTreeSet<String> = [
        "schema_version",
        "binding",
        "iteration",
        "remaining_search_budget_ns",
        "presentation",
        "core",
        "last_round",
        "pending",
        "latest",
        "tools",
        "state_revision",
    ]
    .into_iter()
    .map(str::to_string)
    .collect();
    assert_eq!(push_key_set(&push), expected);
    assert!(push.get("summary").is_none());
    assert!(push.get("clauses").is_none());
    assert!(push.get("ledger").is_none());
    assert!(push.get("correction").is_none());
    assert!(push.get("truncated").is_none());

    let binding = push["binding"].as_object().unwrap();
    for key in [
        "task_digest",
        "scope_digest",
        "run_digest",
        "consultation_digest",
        "state_snapshot_digest",
        "validation_manifest_digest",
    ] {
        assert!(binding.contains_key(key), "missing binding key {key}");
    }
    assert_eq!(binding.len(), 6);

    assert_eq!(push["schema_version"], 10);
    assert_eq!(push["state_revision"], 42);
    assert_eq!(push["tools"], json!(["submit", "history"]));
    assert_eq!(push["core"], json!([]));
    assert_eq!(push["last_round"], json!([]));
    // Both clauses ended the scan pending at level 1, from minimum level 0.
    let pending = push["pending"].as_array().unwrap();
    assert_eq!(pending.len(), 2);
    assert!(
        pending
            .iter()
            .all(|entry| entry["minimum_level"] == 0 && entry["current_level"] == 1)
    );
}

#[tokio::test]
async fn push_core_orders_ascending_level_then_canonical_and_caps_with_marker() {
    let (task, state, level_one_id, level_zero_id) = two_level_core_fixture('c').await;
    let (_owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(feedback_directory("push-core-order")),
    )
    .unwrap();
    let session = PreCertificateAgentHoudiniState::new(
        Arc::clone(&task),
        &artifacts,
        &state,
        Duration::from_secs(5),
        AgentFeedbackPolicy::default(),
    )
    .unwrap();
    let push = session.feedback().push_value(&[], 1);
    let core = push["core"].as_array().unwrap();
    assert_eq!(core.len(), 2);
    assert_eq!(core[0]["clause"]["clause_id"], level_zero_id.get());
    assert_eq!(core[0]["level"], 0);
    assert_eq!(core[0]["source"], "submitted");
    assert_eq!(core[1]["clause"]["clause_id"], level_one_id.get());
    assert_eq!(core[1]["level"], 1);
    assert!(push.get("truncated").is_none());

    let capped_limits = AgentFeedbackLimits {
        host_limits: HostLimits {
            pushed_core: Some(1),
            ..HostLimits::UNBOUNDED
        },
        ..AgentFeedbackLimits::default()
    };
    let capped_session = PreCertificateAgentHoudiniState::new(
        task,
        &artifacts,
        &state,
        Duration::from_secs(5),
        AgentFeedbackPolicy::new(capped_limits).unwrap(),
    )
    .unwrap();
    let capped_push = capped_session.feedback().push_value(&[], 1);
    let capped_core = capped_push["core"].as_array().unwrap();
    assert_eq!(capped_core.len(), 1);
    assert_eq!(capped_core[0]["clause"]["clause_id"], level_zero_id.get());
    assert_eq!(
        capped_push["truncated"],
        json!({"list": "core", "shown": 1, "total": 2, "limit": "pushed_core"}),
    );
}

#[tokio::test]
async fn push_last_round_reports_committed_and_dead_outcomes() {
    let (committed_task, committed_state) =
        conclusive_fixture('1', ConclusiveOutcome::Proved).await;
    let committed_id = committed_state
        .committed_levels()
        .keys()
        .next()
        .copied()
        .unwrap();
    let (_owner, committed_artifacts) = new_artifact_store(
        &committed_task,
        ArtifactStoreConfig::new(feedback_directory("push-last-round-committed")),
    )
    .unwrap();
    let mut committed_session = PreCertificateAgentHoudiniState::new(
        committed_task,
        &committed_artifacts,
        &committed_state,
        Duration::from_secs(5),
        AgentFeedbackPolicy::default(),
    )
    .unwrap();
    committed_session.record_round_proposals([committed_id]);
    assert_eq!(
        committed_session.previous_round_proposals(),
        &[committed_id]
    );
    committed_session
        .refresh_current_feedback(&committed_state, Duration::from_secs(5))
        .unwrap();
    let push = committed_session.feedback().push_value(&[], 1);
    let last_round = push["last_round"].as_array().unwrap();
    assert_eq!(last_round.len(), 1);
    assert_eq!(last_round[0]["clause"]["clause_id"], committed_id.get());
    assert_eq!(last_round[0]["source"], "submitted");
    assert_eq!(
        last_round[0]["outcome"],
        json!({"kind": "committed", "level": 0}),
    );

    let (dead_task, dead_state, dead_id) = dead_clause_fixture('d').await;
    let (_dead_owner, dead_artifacts) = new_artifact_store(
        &dead_task,
        ArtifactStoreConfig::new(feedback_directory("push-last-round-dead")),
    )
    .unwrap();
    let mut dead_session = PreCertificateAgentHoudiniState::new(
        dead_task,
        &dead_artifacts,
        &dead_state,
        Duration::from_secs(5),
        AgentFeedbackPolicy::default(),
    )
    .unwrap();
    dead_session.record_round_proposals([dead_id]);
    dead_session
        .refresh_current_feedback(&dead_state, Duration::from_secs(5))
        .unwrap();
    let dead_push = dead_session.feedback().push_value(&[], 1);
    let dead_last_round = dead_push["last_round"].as_array().unwrap();
    assert_eq!(dead_last_round.len(), 1);
    assert_eq!(dead_last_round[0]["clause"]["clause_id"], dead_id.get());
    assert_eq!(dead_last_round[0]["outcome"]["kind"], "dead");
    assert_eq!(
        dead_last_round[0]["outcome"]["reason"]["kind"],
        "prophecy_free_initialization_refuted",
    );
}

/// The third `last_round` outcome: dead with cause `dropped`.
#[tokio::test]
async fn push_last_round_reports_the_dropped_death_outcome() {
    let (task, mut state) = pending_fixture('e', 1).await;
    let context = state.proposal_context().unwrap();
    let clause_id = context.drop_eligible_records()[0].id();
    let drop_token = context.drop_token(clause_id).unwrap();
    let proposal = FrameworkIIProposalEpoch::new(context, [], [drop_token]).unwrap();
    run_framework_ii_proposal_epoch(&mut state, &mut InconclusiveChecker, proposal)
        .await
        .unwrap();
    assert!(state.is_dropped(clause_id));

    let (_owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(feedback_directory("push-last-round-dropped")),
    )
    .unwrap();
    let mut session = PreCertificateAgentHoudiniState::new(
        task,
        &artifacts,
        &state,
        Duration::from_secs(5),
        AgentFeedbackPolicy::default(),
    )
    .unwrap();
    session.record_round_proposals([clause_id]);
    session
        .refresh_current_feedback(&state, Duration::from_secs(5))
        .unwrap();
    let push = session.feedback().push_value(&[], 1);
    let last_round = push["last_round"].as_array().unwrap();
    assert_eq!(last_round.len(), 1);
    assert_eq!(
        last_round[0]["outcome"],
        json!({"kind": "dead", "cause": "dropped"}),
    );
}

#[tokio::test]
async fn push_last_round_reports_pending_outcome_for_untouched_proposal() {
    let (task, state, clause_id, level) = pending_last_round_fixture('3').await;
    let (_owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(feedback_directory("push-last-round-pending")),
    )
    .unwrap();
    let mut session = PreCertificateAgentHoudiniState::new(
        task,
        &artifacts,
        &state,
        Duration::from_secs(5),
        AgentFeedbackPolicy::default(),
    )
    .unwrap();
    session.record_round_proposals([clause_id]);
    session
        .refresh_current_feedback(&state, Duration::from_secs(5))
        .unwrap();
    let push = session.feedback().push_value(&[], 1);
    let last_round = push["last_round"].as_array().unwrap();
    assert_eq!(last_round.len(), 1);
    assert_eq!(
        last_round[0]["outcome"],
        json!({"kind": "pending", "level": level.get()}),
    );
}

/// Milestone 7.5 review, finding 2, the push after. `agent_houdini.tex`
/// gives `last_round` exactly three outcomes — committed at a level, dead
/// with a reason, pending having failed through a level — and every one of
/// them presupposes an epoch that applied. A rolled-back epoch applied
/// nothing, so the round reports no outcome at all and its `failure` event
/// is what the push says about it; the batch it interned survives in the
/// catalog as provenance, holds no partition, and is therefore not shown as
/// a clause either (the retired `inactive` status).
#[tokio::test]
async fn push_after_a_rolled_back_epoch_shows_neither_outcome_nor_clause() {
    let task = Arc::new(feedback_task("rolled-back"));
    let scope = feedback_scope(&task);
    let kept = feedback_clause(&scope, 0);
    let rolled_back = feedback_clause(&scope, 1);
    let catalog = feedback_catalog(&scope, '8');
    let mut state = LeveledHoudiniState::new(catalog).unwrap();

    // One applied epoch first, so the push has a pending clause of its own
    // and the assertions below distinguish "nothing is reported" from
    // "nothing exists".
    let applied =
        FrameworkIIProposalEpoch::new(state.proposal_context().unwrap(), [kept.clone()], [])
            .unwrap();
    let applied = run_framework_ii_proposal_epoch(&mut state, &mut InconclusiveChecker, applied)
        .await
        .unwrap();
    let kept_id = state.catalog().find(&kept).unwrap().unwrap();
    let kept_level = *state.pending_levels().get(&kept_id).unwrap();
    assert_eq!(applied.round_outcomes(), &[kept_id]);

    let (_owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(feedback_directory("push-rolled-back")),
    )
    .unwrap();
    let mut session = PreCertificateAgentHoudiniState::new(
        Arc::clone(&task),
        &artifacts,
        &state,
        Duration::from_secs(5),
        AgentFeedbackPolicy::default(),
    )
    .unwrap();
    session.record_round_proposals(applied.round_outcomes().iter().copied());

    let failing =
        FrameworkIIProposalEpoch::new(state.proposal_context().unwrap(), [rolled_back.clone()], [])
            .unwrap();
    let mut failing_checker = FailingChecker {
        progress: RealRouteChecker {
            route: RealRouteKind::RetryProgress,
            artifacts: artifacts.clone(),
        },
    };
    let result = run_framework_ii_proposal_epoch(&mut state, &mut failing_checker, failing)
        .await
        .unwrap();
    let rolled_back_id = state.catalog().find(&rolled_back).unwrap().unwrap();
    assert!(matches!(
        result.outcome(),
        FrameworkIIEpochOutcome::Failure(_)
    ));
    assert_eq!(
        result.submitted(),
        &[rolled_back_id],
        "the batch was interned before the epoch failed, and its record survives"
    );
    assert!(
        result.round_outcomes().is_empty(),
        "a rolled-back epoch produced no per-clause outcome to report"
    );
    assert!(!state.committed_levels().contains_key(&rolled_back_id));
    assert!(!state.pending_levels().contains_key(&rolled_back_id));
    assert!(!state.is_dead(rolled_back_id));

    // Exactly what the search does with the round: record its outcomes,
    // which are none, and push the failure event.
    session.record_round_proposals(result.round_outcomes().iter().copied());
    let failure = AgentSearchFeedback::failure(&state, checker_failure()).unwrap();
    let push = session
        .build_next_feedback(&state, &failure, Duration::from_secs(4))
        .unwrap()
        .push_value(&[], 1);

    assert_eq!(push["latest"]["kind"], json!("failure"));
    assert_eq!(
        push["last_round"],
        json!([]),
        "a rolled-back round reports no clause outcome, not a fallback one"
    );
    let pending = push["pending"].as_array().unwrap();
    assert_eq!(pending.len(), 1, "the epoch-start partition, and only it");
    assert_eq!(pending[0]["clause"]["clause_id"], kept_id.get());
    assert_eq!(pending[0]["current_level"], kept_level.get());
    assert_eq!(push["core"], json!([]));

    // The clause page shows the partition, not the catalog.
    let wire = session.feedback().to_json_value();
    assert_eq!(wire["clauses"]["metadata"]["total_items"], 1);
    let shown = wire["clauses"]["items"]
        .as_array()
        .unwrap()
        .iter()
        .map(|item| item["clause"]["clause_id"].as_u64().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(shown, vec![kept_id.get()]);
    assert!(
        !session
            .feedback()
            .to_json_string()
            .unwrap()
            .contains("inactive"),
        "the contract defines three clause statuses and no fourth"
    );
    assert_eq!(
        wire["summary"]["tracked_clauses"], 2,
        "the catalog keeps the rolled-back record as provenance"
    );

    // Ledger references remain readable even when rollback removes a clause
    // from every current partition; queries retain no new semantic facts.
    let state_before = format!("{state:?}");
    let ledger = super::tools::read_ledger(&state, &session, json!({})).unwrap();
    let clause = ledger["items"]
        .as_array()
        .unwrap()
        .iter()
        .find_map(|row| {
            (row["clause"]["clause_id"] == rolled_back_id.get()).then(|| row["clause"].clone())
        })
        .expect("rollback retains its check row");
    let history = super::tools::read_history(
        session.feedback(),
        &state,
        &session,
        json!({"clause": clause}),
    )
    .unwrap();
    assert_eq!(history["clause"], clause);
    assert!(history["status"].is_null());
    assert!(history["current_level"].is_null());
    assert_eq!(history["minimum_level"], rolled_back.minimum_level().get());
    assert!(!history["attempts"].as_array().unwrap().is_empty());
    let typed: crate::proposer_api::query_results::HistoryV1 =
        serde_json::from_value(history).unwrap();
    assert!(typed.status.is_none());
    assert_eq!(format!("{state:?}"), state_before);
}

/// The push carries `pending`, never `retry`: every pending clause by
/// identity and source, with its minimum level and the level it failed
/// through in the last scan.
#[tokio::test]
async fn push_pending_lists_every_pending_clause_with_both_levels() {
    // A refuted clause that mentions a prophecy relation is promoted, not
    // killed, and ends the scan pending at level 1 with minimum level 0.
    let (task, state) = conclusive_fixture('4', ConclusiveOutcome::Refuted).await;
    let pending_id = state.pending_levels().keys().next().copied().unwrap();
    assert_eq!(
        state.pending_levels().get(&pending_id),
        Some(&FrameworkIILevel::ONE)
    );
    let (_owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(feedback_directory("push-pending")),
    )
    .unwrap();
    let session = PreCertificateAgentHoudiniState::new(
        task,
        &artifacts,
        &state,
        Duration::from_secs(5),
        AgentFeedbackPolicy::default(),
    )
    .unwrap();
    let push = session.feedback().push_value(&[], 1);
    assert!(push.get("retry").is_none());
    let pending = push["pending"].as_array().unwrap();
    assert_eq!(pending.len(), 1);
    assert_eq!(pending[0]["clause"]["clause_id"], pending_id.get());
    assert_eq!(pending[0]["source"], "submitted");
    assert_eq!(pending[0]["minimum_level"], 0);
    assert_eq!(pending[0]["current_level"], 1);
    assert!(!pending[0]["drop_reference"].is_null());

    // A state with nothing pending pushes an empty list.
    let (proved_task, proved_state) = conclusive_fixture('5', ConclusiveOutcome::Proved).await;
    assert!(proved_state.pending_levels().is_empty());
    let (_proved_owner, proved_artifacts) = new_artifact_store(
        &proved_task,
        ArtifactStoreConfig::new(feedback_directory("push-pending-empty")),
    )
    .unwrap();
    let proved_session = PreCertificateAgentHoudiniState::new(
        proved_task,
        &proved_artifacts,
        &proved_state,
        Duration::from_secs(5),
        AgentFeedbackPolicy::default(),
    )
    .unwrap();
    assert_eq!(
        proved_session.feedback().push_value(&[], 1)["pending"],
        json!([])
    );
}

/// The standing presentation is pinned, with and without a level bound: the
/// run's own data — task, schema, prophecy map, host limits with their values
/// and the resource allowances — and not one sentence of explanation. Every
/// tutorial field API 3.0 shipped is gone; the rules they worded are the
/// contract report's and the proposer's to state.
#[tokio::test]
async fn push_presentation_is_pinned_with_and_without_a_level_bound() {
    let (task, state) = pending_fixture('6', 1).await;
    let (_owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(feedback_directory("push-presentation")),
    )
    .unwrap();
    let session = PreCertificateAgentHoudiniState::new(
        Arc::clone(&task),
        &artifacts,
        &state,
        Duration::from_secs(5),
        AgentFeedbackPolicy::default(),
    )
    .unwrap();
    let push = session.feedback().push_value(&[], 1);
    let presentation = &push["presentation"];
    assert_eq!(presentation["schema_version"], 16);
    assert_eq!(
        presentation
            .as_object()
            .unwrap()
            .keys()
            .map(String::as_str)
            .collect::<Vec<_>>(),
        [
            "ambient_schema",
            "host_limits",
            "presentation_digest",
            "resource_limits",
            "schema_version",
            "task",
        ],
        "the presentation carries the run's data and no explanatory prose"
    );
    // The resource allowances are values, not a paragraph about accounting.
    assert_eq!(
        presentation["resource_limits"],
        json!({"api_packet_bytes": 67_108_864, "configured": null}),
    );
    // A run that sets no host limit — the default — lists none.
    assert_eq!(presentation["host_limits"], json!([]));
    let encoded = presentation.to_string();
    for retired in [
        "clause_grammar",
        "system_clauses",
        "prophecy_semantics",
        "checks",
        "pending_retry",
        "host_limits_note",
        "death_rules",
        "proposal_kinds",
        "level_bound\":",
        "reconsideration",
        "initialization_rule",
        "exhaust",
        "maintenance check",
        "OnNovelClause",
        "ExplicitOnly",
    ] {
        assert!(!encoded.contains(retired), "presentation kept {retired}");
    }

    // A run that sets a bound states it, with the submission-time rule.
    let bounded_catalog = feedback_catalog(&feedback_scope(&task), '8');
    let bounded_state =
        LeveledHoudiniState::new_with_max_level(bounded_catalog, Some(FrameworkIILevel::ONE))
            .unwrap();
    let (_bounded_owner, bounded_artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(feedback_directory("push-presentation-bounded")),
    )
    .unwrap();
    let listed_task = Arc::clone(&task);
    let bounded_session = PreCertificateAgentHoudiniState::new(
        task,
        &bounded_artifacts,
        &bounded_state,
        Duration::from_secs(5),
        AgentFeedbackPolicy::default(),
    )
    .unwrap();
    // The state's own bound is folded into the listed limits, by name and
    // value, with no per-limit code and no separate paragraph.
    assert_eq!(
        bounded_session.feedback().push_value(&[], 1)["presentation"]["host_limits"],
        json!([{"limit": "level_bound", "value": 1}]),
    );
    assert_eq!(
        bounded_session.host_limits().level_bound,
        Some(1),
        "the push enforces exactly the limit the presentation states"
    );

    // A policy that names other limits lists those too, alongside the
    // state's bound, in the fixed order.
    let listed_state = LeveledHoudiniState::new_with_max_level(
        feedback_catalog(&bounded_state.catalog().scope().clone(), '9'),
        Some(FrameworkIILevel::ONE),
    )
    .unwrap();
    let (_listed_owner, listed_artifacts) = new_artifact_store(
        &listed_task,
        ArtifactStoreConfig::new(feedback_directory("push-presentation-listed")),
    )
    .unwrap();
    let listed_session = PreCertificateAgentHoudiniState::new(
        listed_task,
        &listed_artifacts,
        &listed_state,
        Duration::from_secs(5),
        AgentFeedbackPolicy::new(AgentFeedbackLimits {
            host_limits: HostLimits {
                proposal_size: Some(16),
                reply_bytes: Some(4_096),
                ..HostLimits::UNBOUNDED
            },
            ..AgentFeedbackLimits::default()
        })
        .unwrap(),
    )
    .unwrap();
    assert_eq!(
        listed_session.feedback().push_value(&[], 1)["presentation"]["host_limits"],
        json!([
            {"limit": "level_bound", "value": 1},
            {"limit": "proposal_size", "value": 16},
            {"limit": "reply_bytes", "value": 4_096},
        ]),
    );
}

#[tokio::test]
async fn ledger_preparation_time_nanos_reflects_obligation_preparation() {
    let task = Arc::new(feedback_task("prep"));
    let scope = feedback_scope(&task);
    let clause = feedback_clause(&scope, 0);
    let catalog = feedback_catalog(&scope, '7');
    let mut state = LeveledHoudiniState::new(catalog).unwrap();
    let proposal =
        FrameworkIIProposalEpoch::new(state.proposal_context().unwrap(), [clause], []).unwrap();
    run_framework_ii_proposal_epoch(&mut state, &mut PreparationTimeChecker, proposal)
        .await
        .unwrap();
    let (_owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(feedback_directory("ledger-preparation-time")),
    )
    .unwrap();
    let session = PreCertificateAgentHoudiniState::new(
        task,
        &artifacts,
        &state,
        Duration::from_secs(5),
        AgentFeedbackPolicy::default(),
    )
    .unwrap();
    let wire = session.feedback().to_json_value();
    let rows = wire["ledger"]["items"].as_array().unwrap();
    assert!(!rows.is_empty());
    assert_eq!(rows[0]["preparation_time_nanos"], 4_444);
    assert_eq!(rows[0]["solver_time_nanos"], Value::Null);
}

/// Milestone 7.7 review: per-clause history is complete. The `ledger`
/// page size is not a bound on the `history` tool, so a clause with more
/// attempt rows than one ledger page still has every row served, oldest
/// first and in ledger order.
#[tokio::test(flavor = "current_thread")]
async fn clause_history_is_complete_past_the_ledger_page_size() {
    let (task, state) = pending_fixture('e', 1).await;
    let (_owner, artifacts) = new_artifact_store(
        &task,
        ArtifactStoreConfig::new(feedback_directory("history-complete")),
    )
    .unwrap();
    let session = PreCertificateAgentHoudiniState::new(
        Arc::clone(&task),
        &artifacts,
        &state,
        Duration::from_secs(5),
        paging_policy(1),
    )
    .unwrap();
    let clause = ClauseId::test(0);
    let expected = state
        .attempts()
        .rows()
        .iter()
        .filter_map(|row| match row {
            LevelLedgerRow::Attempt(attempt) if attempt.request().clause() == clause => {
                Some(row.row_digest())
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(
        expected.len() > session.policy().limits().ledger_page_items,
        "the fixture must exceed one ledger page: {} rows",
        expected.len()
    );
    let history = session.clause_history_tool(&state, clause).unwrap();
    assert_eq!(history.len(), expected.len(), "every attempt row is served");
    for (served, digest) in history.iter().zip(expected.iter()) {
        assert_eq!(
            served.wire_value()["row_digest"],
            json!(digest),
            "rows are served in ledger order"
        );
    }
}
