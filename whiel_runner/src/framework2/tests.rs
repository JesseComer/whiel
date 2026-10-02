use std::collections::{BTreeMap, BTreeSet};
use std::sync::{Arc, Mutex};

use serde_json::{Value, json};

use super::*;
use crate::encoding::{FIXED_AMBIENT_WORKER_FORMAT_VERSION, canonical_value_sha256};
use crate::houdini::ClauseId;
use crate::runtime::CancellationToken;
use crate::task::{RelationKey, SynthesisTask, TaskSchemaKind};

pub(super) fn fixed_ambient_task() -> SynthesisTask {
    SynthesisTask::from_fixed_ambient_json(
        r#"{
          "format_version":4,
          "semantic_version":1,
          "encoding_version":1,
          "identity":{
            "canonical_id":"FrameworkIIFixedAmbientControlTest",
            "module":"Whiel.Test.FrameworkIIFixedAmbientControlTest",
            "namespace":"Whiel.Test.FrameworkIIFixedAmbientControlTest",
            "source_sha256":"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
          },
          "schema":{"expression":"Whiel.Test.FrameworkIIFixedAmbientControlTest.inputPreproc.prophecySchema","display":"{R, R^infinity}"},
          "original":{
            "pre":{"expression":"Whiel.Test.FrameworkIIFixedAmbientControlTest.inputPre","display":"true"},
            "command":{"expression":"Whiel.Test.FrameworkIIFixedAmbientControlTest.inputCmd","display":"SKIP"},
            "post":{"expression":"Whiel.Test.FrameworkIIFixedAmbientControlTest.inputPost","display":"true"}
          },
          "preprocessed":{
            "pre":{"expression":"Whiel.Test.FrameworkIIFixedAmbientControlTest.inputPreproc.liftedLoop.preAssert","display":"true"},
            "command":{"expression":"Whiel.Test.FrameworkIIFixedAmbientControlTest.inputPreproc.liftedLoop.cmd","display":"SKIP"},
            "post":{"expression":"Whiel.Test.FrameworkIIFixedAmbientControlTest.inputPreproc.liftedLoop.postAssert","display":"true"}
          },
          "preprocessing_evidence":{"expression":"Whiel.Test.FrameworkIIFixedAmbientControlTest.inputPreproc"},
          "solver":{
            "schema_relations":[{"key":"o:p::R","arity":1},{"key":"y:p::R","arity":1}],
            "task_constants":[],
            "preprocessed_pre":{"source_id":"task.preprocessed_pre","expression":"Whiel.Test.FrameworkIIFixedAmbientControlTest.inputPreproc.liftedLoop.preAssert","no_bound_expression":"Whiel.Test.FrameworkIIFixedAmbientControlTest.inputPreproc.liftedLoop.preAssert_noBound","constants":[],"relations":[]},
            "preprocessed_post":{"source_id":"task.preprocessed_post","expression":"Whiel.Test.FrameworkIIFixedAmbientControlTest.inputPreproc.liftedLoop.postAssert","no_bound_expression":"Whiel.Test.FrameworkIIFixedAmbientControlTest.inputPreproc.liftedLoop.postAssert_noBound","constants":[],"relations":[]},
            "loop_guard":{"source_id":"task.loop_guard","constants":[],"relations":[]},
            "negated_loop_guard":{"source_id":"task.negated_loop_guard","constants":[],"relations":[]}
          }
        }"#,
    )
    .unwrap()
}

fn fixed_ambient_scope(marker: &str) -> FixedAmbientTaskScope {
    let task = fixed_ambient_task();
    let relations = task
        .solver_relations()
        .iter()
        .map(|relation| FrameworkIIRelation::new(relation.key().clone(), relation.arity()))
        .collect::<Vec<_>>();
    let binding = FrameworkIIProphecyBinding::new(
        RelationKey::from_lean_scope("o:p::R").unwrap(),
        RelationKey::from_lean_scope("y:p::R").unwrap(),
        1,
    );
    FixedAmbientTaskScope::new(
        task.identity().clone(),
        json!({
            "kind":"whiel_framework_ii_fixed_ambient_scope",
            "version":1,
            "marker":marker,
            "relations":["o:p::R", "y:p::R"],
        }),
        Value::Null,
        Vec::new(),
        relations,
        vec![binding],
    )
}

fn clause(
    scope: &FixedAmbientTaskScope,
    name: &str,
    order_key: &str,
    relation_key: &str,
    minimum_level: FrameworkIILevel,
) -> ExtendedClause {
    let identity = json!({
        "kind":"whiel_framework_ii_fixed_ambient_clause",
        "version":1,
        "scope_identity":scope.identity(),
        "formula":{"atom":name},
    });
    ExtendedClause::new(
        scope.clone(),
        identity,
        order_key.to_owned(),
        format!("({name} = empty[1])"),
        vec![relation_key.to_owned()],
        relation_key.starts_with("y:"),
        minimum_level,
    )
}

fn catalog(scope: &FixedAmbientTaskScope, marker: char) -> LeveledClauseCatalog {
    LeveledClauseCatalog::new(scope.clone(), marker.to_string().repeat(64)).unwrap()
}

fn proved(request: &FrameworkIICheckRequest) -> FrameworkIICheckOutcome {
    FrameworkIICheckOutcome::Proved(
        FrameworkIICheckEvidence::new(
            request.request_digest(),
            format!("proof:{}", request.request_digest()),
        )
        .unwrap(),
    )
}

fn refuted(request: &FrameworkIICheckRequest) -> FrameworkIICheckOutcome {
    FrameworkIICheckOutcome::Refuted(
        FrameworkIICheckEvidence::new(
            request.request_digest(),
            format!("refutation:{}", request.request_digest()),
        )
        .unwrap(),
    )
}

fn inconclusive(
    request: &FrameworkIICheckRequest,
    reason: FrameworkIIInconclusiveReason,
) -> FrameworkIICheckOutcome {
    FrameworkIICheckOutcome::Inconclusive {
        reason,
        progress: FrameworkIICheckEvidence::new(
            request.request_digest(),
            format!("progress:{}", request.request_digest()),
        )
        .unwrap(),
    }
}

#[test]
fn fixed_ambient_version_family_and_loader_are_explicit() {
    assert_eq!(FIXED_AMBIENT_WORKER_FORMAT_VERSION, 11);
    assert_eq!(FRAMEWORK_II_RUNTIME_CACHE_IDENTITY_VERSION, 9);
    assert_eq!(
        fixed_ambient_task().schema_kind(),
        TaskSchemaKind::FixedAmbient
    );

    let legacy = r#"{
      "format_version":3,"semantic_version":1,"encoding_version":1,
      "identity":{"canonical_id":"X","module":"X","namespace":"X","source_sha256":"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"},
      "schema":{"expression":"X.programSchema","display":"{}"},
      "original":{"pre":{"expression":"X.inputPre","display":"true"},"command":{"expression":"X.inputCmd","display":"SKIP"},"post":{"expression":"X.inputPost","display":"true"}},
      "preprocessed":{"pre":{"expression":"X.inputPreproc.loopPre","display":"true"},"command":{"expression":"X.inputPreproc.loopCmd","display":"SKIP"},"post":{"expression":"X.inputPreproc.loopPost","display":"true"}},
      "preprocessing_evidence":{"expression":"X.inputPreproc"},
      "solver":{"schema_relations":[],"task_constants":[],"preprocessed_pre":{"source_id":"task.preprocessed_pre","expression":"X.inputPreproc.loopPre","no_bound_expression":"X.inputPreproc.loopPre_noBound","constants":[],"relations":[]},"preprocessed_post":{"source_id":"task.preprocessed_post","expression":"X.inputPreproc.loopPost","no_bound_expression":"X.inputPreproc.loopPost_noBound","constants":[],"relations":[]},"loop_guard":{"source_id":"task.loop_guard","constants":[],"relations":[]},"negated_loop_guard":{"source_id":"task.negated_loop_guard","constants":[],"relations":[]}}
    }"#;
    assert!(SynthesisTask::from_fixed_ambient_json(legacy).is_err());
}

#[test]
fn catalog_registration_is_deterministic_opaque_and_atomic() {
    let scope = fixed_ambient_scope("catalog");
    let alpha = clause(
        &scope,
        "alpha",
        "02-alpha",
        "y:p::R",
        FrameworkIILevel::ZERO,
    );
    let beta = clause(&scope, "beta", "01-beta", "o:p::R", FrameworkIILevel::ONE);

    let left = catalog(&scope, 'b');
    let registered = left
        .register_batch(
            0,
            [
                (alpha.clone(), ExtendedClauseOrigin::Submitted),
                (beta.clone(), ExtendedClauseOrigin::Symbolic),
            ],
        )
        .unwrap();
    assert_eq!(
        registered
            .ids()
            .iter()
            .map(|id| id.get())
            .collect::<Vec<_>>(),
        [0, 1]
    );
    assert_eq!(left.find(&beta).unwrap().unwrap().get(), 0);
    assert_eq!(left.find(&alpha).unwrap().unwrap().get(), 1);
    assert_eq!(
        left.record(registered.ids()[0])
            .unwrap()
            .formula()
            .relation_keys(),
        &["o:p::R"]
    );

    let right = catalog(&scope, 'b');
    right
        .register_batch(
            0,
            [
                (beta.clone(), ExtendedClauseOrigin::Symbolic),
                (alpha.clone(), ExtendedClauseOrigin::Submitted),
            ],
        )
        .unwrap();
    for formula in [&alpha, &beta] {
        let left_record = left.record(left.find(formula).unwrap().unwrap()).unwrap();
        let right_record = right.record(right.find(formula).unwrap().unwrap()).unwrap();
        assert_eq!(left_record.id(), right_record.id());
        assert_eq!(left_record.record_digest(), right_record.record_digest());
    }

    let drifted = clause(&scope, "alpha", "02-alpha", "y:p::R", FrameworkIILevel::ONE);
    assert_eq!(
        left.register_batch(1, [(drifted, ExtendedClauseOrigin::Submitted)])
            .unwrap_err(),
        FrameworkIIStateError::ConflictingFormulaMetadata,
    );
    assert_eq!(left.len().unwrap(), 2);
    assert_eq!(left.next_batch_ordinal().unwrap(), 1);

    let foreign_scope = fixed_ambient_scope("foreign");
    let foreign = clause(
        &foreign_scope,
        "foreign",
        "03-foreign",
        "o:p::R",
        FrameworkIILevel::ZERO,
    );
    assert_eq!(
        left.register_batch(1, [(foreign, ExtendedClauseOrigin::Submitted)])
            .unwrap_err(),
        FrameworkIIStateError::WrongScope,
    );
}

#[test]
fn snapshot_and_request_retain_full_v5_identity_in_lean_order() {
    let scope = fixed_ambient_scope("snapshot");
    let first = clause(
        &scope,
        "first",
        "same-order",
        "o:p::R",
        FrameworkIILevel::ZERO,
    );
    let second = clause(
        &scope,
        "second",
        "same-order",
        "y:p::R",
        FrameworkIILevel::ZERO,
    );
    let catalog = catalog(&scope, 'c');
    let registered = catalog
        .register_batch(
            0,
            [
                (second.clone(), ExtendedClauseOrigin::Submitted),
                (first.clone(), ExtendedClauseOrigin::Submitted),
            ],
        )
        .unwrap();
    let first_id = catalog.find(&first).unwrap().unwrap();
    let second_id = catalog.find(&second).unwrap().unwrap();
    let snapshot = Arc::new(
        LeveledCandidateSnapshot::build(
            &catalog,
            Some(FrameworkIILevel::ONE),
            BTreeMap::from([
                (first_id, FrameworkIILevel::ONE),
                (second_id, FrameworkIILevel::ZERO),
            ]),
        )
        .unwrap(),
    );
    assert_eq!(registered.newly_allocated().len(), 2);
    assert_eq!(snapshot.canonical_order(), &[second_id, first_id]);
    assert_eq!(
        snapshot.worker_identity(),
        json!({
            "kind":"whiel_fixed_ambient_snapshot","version":1,
            "rows":[
                {"canonical_source":second.canonical_source(),"clause_id":second_id.get(),"identity":second.identity(),"level":0},
                {"canonical_source":first.canonical_source(),"clause_id":first_id.get(),"identity":first.identity(),"level":1}
            ]
        }),
    );

    let request = FrameworkIICheckRequest::new(
        0,
        second_id,
        FrameworkIILevel::ZERO,
        FrameworkIICheckRole::Maintenance,
        Arc::clone(&snapshot),
        false,
    )
    .unwrap();
    assert_eq!(
        request.identity()["kind"],
        "whiel_framework_ii_fixed_ambient_check_request"
    );
    assert_eq!(request.identity()["version"], 1);
    assert_eq!(request.identity()["scope_identity"], *scope.identity());
    assert_eq!(
        request.identity()["snapshot_identity"],
        snapshot.worker_identity()
    );
    assert_eq!(
        request.identity()["selector"],
        json!({"kind":"maintenance","clause_id":second_id.get()})
    );
    assert_ne!(
        request.identity(),
        &json!({"domain":"whiel-framework-ii-check-request-v3"})
    );
}

#[test]
fn snapshot_reuse_checks_full_records_even_under_digest_collision() {
    let scope = fixed_ambient_scope("collision");
    let catalog = catalog(&scope, 'd');
    let first = clause(&scope, "first", "01", "o:p::R", FrameworkIILevel::ZERO);
    let second = clause(&scope, "second", "02", "y:p::R", FrameworkIILevel::ZERO);
    let registered = catalog
        .register_batch(
            0,
            [
                (first, ExtendedClauseOrigin::Submitted),
                (second, ExtendedClauseOrigin::Submitted),
            ],
        )
        .unwrap();
    let first_snapshot = LeveledCandidateSnapshot::build(
        &catalog,
        None,
        BTreeMap::from([(registered.ids()[0], FrameworkIILevel::ZERO)]),
    )
    .unwrap();
    let mut second_snapshot = LeveledCandidateSnapshot::build(
        &catalog,
        None,
        BTreeMap::from([(registered.ids()[1], FrameworkIILevel::ZERO)]),
    )
    .unwrap();
    second_snapshot
        .set_partition_digest_for_collision_test(Arc::from(first_snapshot.partition_digest()));
    assert_eq!(
        first_snapshot.partition_digest(),
        second_snapshot.partition_digest()
    );
    assert!(!first_snapshot.same_partition(&second_snapshot));
}

// ------------------------------------------------------------
// Opaque Piece Splicing (Pass 7.5d)
// ------------------------------------------------------------

/// A two-row snapshot: `zero` at level zero, `one` at level one, in
/// canonical order.
fn splice_fixture() -> (
    FixedAmbientTaskScope,
    Arc<LeveledCandidateSnapshot>,
    ClauseId,
    ClauseId,
    ExtendedClause,
    ExtendedClause,
) {
    let scope = fixed_ambient_scope("splice");
    let catalog = catalog(&scope, '9');
    let zero = clause(&scope, "zero", "01-zero", "o:p::R", FrameworkIILevel::ZERO);
    let one = clause(&scope, "one", "02-one", "y:p::R", FrameworkIILevel::ONE);
    let registered = catalog
        .register_batch(
            0,
            [
                (zero.clone(), ExtendedClauseOrigin::Submitted),
                (one.clone(), ExtendedClauseOrigin::Submitted),
            ],
        )
        .unwrap();
    let zero_id = catalog.find(&zero).unwrap().unwrap();
    let one_id = catalog.find(&one).unwrap().unwrap();
    assert_eq!(registered.ids().len(), 2);
    let snapshot = Arc::new(
        LeveledCandidateSnapshot::build(
            &catalog,
            None,
            BTreeMap::from([
                (zero_id, FrameworkIILevel::ZERO),
                (one_id, FrameworkIILevel::ONE),
            ]),
        )
        .unwrap(),
    );
    assert_eq!(snapshot.canonical_order(), &[zero_id, one_id]);
    (scope, snapshot, zero_id, one_id, zero, one)
}

/// One splice slot as `(role, clause identity digest)`.
type SplicedSlot = (FrameworkIIComponentRole, Option<String>);

/// A recipe read back as `(axiom slots, axiom tags, conjecture slot)`.
type SplicedRecipe = (
    Vec<SplicedSlot>,
    Vec<super::premise::FrameworkIIPremiseTag>,
    SplicedSlot,
);

fn spliced(
    snapshot: &LeveledCandidateSnapshot,
    selector: super::solver::FrameworkIISelector,
) -> SplicedRecipe {
    let recipe = super::pieces::splice_recipe(snapshot, selector).unwrap();
    let slot = |slot: &super::pieces::FrameworkIIPieceSlot| {
        (
            slot.role,
            slot.clause.as_ref().map(|digest| digest.to_string()),
        )
    };
    (
        recipe.axioms.iter().map(|(s, _)| slot(s)).collect(),
        recipe.axioms.iter().map(|(_, tag)| tag.clone()).collect(),
        slot(&recipe.conjecture),
    )
}

#[test]
fn splice_recipes_follow_leans_axiom_order_for_every_selector() {
    use super::components::FrameworkIIComponentRole as Role;
    use super::solver::FrameworkIISelector as Selector;
    let (_scope, snapshot, zero_id, one_id, zero, one) = splice_fixture();
    let zero_digest = Some(zero.identity_sha256().to_owned());
    let one_digest = Some(one.identity_sha256().to_owned());

    // `initVC`: `pre :: premises`, and level zero has no premises.
    let (axioms, _, conjecture) = spliced(&snapshot, Selector::Initialization(zero_id));
    assert_eq!(axioms, vec![(Role::Precondition, None)]);
    assert_eq!(conjecture, (Role::Clause, zero_digest.clone()));

    // Level one adds `not (theta guard)` and theta of each strictly lower
    // row, in snapshot order.
    let (axioms, _, conjecture) = spliced(&snapshot, Selector::Initialization(one_id));
    assert_eq!(
        axioms,
        vec![
            (Role::Precondition, None),
            (Role::NegatedThetaGuard, None),
            (Role::ThetaClause, zero_digest.clone()),
        ]
    );
    assert_eq!(conjecture, (Role::Clause, one_digest.clone()));

    // `maintenanceVC`: `formulas (upTo level) ++ guard :: premises`.
    let (axioms, _, conjecture) = spliced(&snapshot, Selector::Maintenance(zero_id));
    assert_eq!(
        axioms,
        vec![(Role::Clause, zero_digest.clone()), (Role::Guard, None)]
    );
    assert_eq!(conjecture, (Role::MaintenanceWp, zero_digest.clone()));

    let (axioms, _, conjecture) = spliced(&snapshot, Selector::Maintenance(one_id));
    assert_eq!(
        axioms,
        vec![
            (Role::Clause, zero_digest.clone()),
            (Role::Clause, one_digest.clone()),
            (Role::Guard, None),
            (Role::NegatedThetaGuard, None),
            (Role::ThetaClause, zero_digest.clone()),
        ]
    );
    assert_eq!(conjecture, (Role::MaintenanceWp, one_digest.clone()));

    // `terminationVC`: `not guard :: collapsedPremises`, over every row.
    let (axioms, _, conjecture) = spliced(&snapshot, Selector::Termination);
    assert_eq!(
        axioms,
        vec![
            (Role::NegatedGuard, None),
            (Role::CollapsedClause, zero_digest.clone()),
            (Role::CollapsedClause, one_digest.clone()),
        ]
    );
    assert_eq!(conjecture, (Role::Postcondition, None));

    // Every recipe names each clause it needs pieces of exactly once.
    for selector in [
        Selector::Initialization(zero_id),
        Selector::Initialization(one_id),
        Selector::Maintenance(zero_id),
        Selector::Maintenance(one_id),
        Selector::Termination,
    ] {
        let recipe = super::pieces::splice_recipe(&snapshot, selector).unwrap();
        let digests = recipe
            .clauses
            .iter()
            .map(|clause| clause.identity_sha256().to_owned())
            .collect::<Vec<_>>();
        assert_eq!(
            digests.iter().collect::<BTreeSet<_>>().len(),
            digests.len(),
            "{selector:?}"
        );
        for (slot, _) in &recipe.axioms {
            if let Some(digest) = &slot.clause {
                assert!(digests.iter().any(|held| held == digest.as_ref()));
            }
        }
        if let Some(digest) = &recipe.conjecture.clause {
            assert!(digests.iter().any(|held| held == digest.as_ref()));
        }
    }
}

/// The recipe's tags and [`super::premise::tagged_premise_set`] are two
/// independent computations of the same tagged premise set; the assembled
/// `axiom_tags` table would otherwise be able to drift from the semantic
/// dictionary's key.
#[test]
fn spliced_axiom_tags_agree_with_the_independently_computed_premise_set() {
    use super::premise::{
        FrameworkIIPremiseTag, tagged_premise_set, termination_tagged_premise_set,
    };
    use super::solver::FrameworkIISelector as Selector;
    let (_scope, snapshot, zero_id, one_id, _zero, _one) = splice_fixture();
    for (clause, level, role) in [
        (
            zero_id,
            FrameworkIILevel::ZERO,
            FrameworkIICheckRole::Initialization,
        ),
        (
            zero_id,
            FrameworkIILevel::ZERO,
            FrameworkIICheckRole::Maintenance,
        ),
        (
            one_id,
            FrameworkIILevel::ONE,
            FrameworkIICheckRole::Initialization,
        ),
        (
            one_id,
            FrameworkIILevel::ONE,
            FrameworkIICheckRole::Maintenance,
        ),
    ] {
        let request =
            FrameworkIICheckRequest::new(0, clause, level, role, Arc::clone(&snapshot), false)
                .unwrap();
        let selector = match role {
            FrameworkIICheckRole::Initialization => Selector::Initialization(clause),
            FrameworkIICheckRole::Maintenance => Selector::Maintenance(clause),
        };
        let (_, tags, _) = spliced(&snapshot, selector);
        assert_eq!(
            tags.iter()
                .cloned()
                .collect::<BTreeSet<FrameworkIIPremiseTag>>(),
            tagged_premise_set(&request),
            "{role:?} at level {}",
            level.get()
        );
    }
    let (_, tags, _) = spliced(&snapshot, Selector::Termination);
    assert_eq!(
        tags.into_iter()
            .collect::<BTreeSet<FrameworkIIPremiseTag>>(),
        termination_tagged_premise_set(&snapshot)
    );
}

/// The assembled table is keyed by the short positional names
/// `entailment::assembly::render_query` writes, exactly as
/// `decode_axiom_tag_table` keys Lean's own table.
#[test]
fn the_assembled_axiom_tag_table_uses_render_querys_short_names() {
    use super::premise::{FrameworkIIAxiomTagTable, FrameworkIIPremiseTag};
    use super::solver::FrameworkIISelector as Selector;
    let (_scope, snapshot, _zero_id, one_id, zero, _one) = splice_fixture();
    let (_, tags, _) = spliced(&snapshot, Selector::Maintenance(one_id));
    let mut entries = tags
        .iter()
        .enumerate()
        .map(|(index, tag)| (Arc::from(format!("axiom_{index}")), tag.clone()))
        .collect::<Vec<(Arc<str>, _)>>();
    entries.push((Arc::from("support_adom"), FrameworkIIPremiseTag::Support));
    entries.push((
        Arc::from("support_distinct_0"),
        FrameworkIIPremiseTag::Support,
    ));
    let table = FrameworkIIAxiomTagTable::from_entries(entries).unwrap();
    assert_eq!(
        table.get("axiom_0"),
        Some(&FrameworkIIPremiseTag::Plain(Arc::from(
            zero.identity_sha256()
        )))
    );
    assert_eq!(table.get("axiom_2"), Some(&FrameworkIIPremiseTag::Guard));
    assert_eq!(
        table.get("support_distinct_0"),
        Some(&FrameworkIIPremiseTag::Support)
    );
    assert_eq!(table.get("axiom_5"), None);
    // `support` never enters the tagged premise set the dictionary keys on.
    assert_eq!(
        table.issued_tagged_premise_set(),
        tags.into_iter().collect::<BTreeSet<_>>()
    );
}

#[test]
fn core_identity_is_complete_and_stable_across_handoff_clone() {
    let scope = fixed_ambient_scope("handoff");
    let catalog = catalog(&scope, 'e');
    let candidate = clause(&scope, "candidate", "01", "o:p::R", FrameworkIILevel::ZERO);
    let registered = catalog
        .register_batch(0, [(candidate, ExtendedClauseOrigin::Submitted)])
        .unwrap();
    let snapshot = Arc::new(
        LeveledCandidateSnapshot::build(
            &catalog,
            None,
            BTreeMap::from([(registered.ids()[0], FrameworkIILevel::ZERO)]),
        )
        .unwrap(),
    );
    let core = LeveledCoreHandle::build(Arc::clone(&snapshot)).unwrap();
    let handed_off = core.clone();
    assert_eq!(handed_off.identity(), core.identity());
    assert_eq!(handed_off.core_digest(), core.core_digest());
    assert_eq!(canonical_value_sha256(core.identity()), core.core_digest());
    assert_eq!(core.identity()["scope_identity"], *scope.identity());
    assert_eq!(
        core.identity()["snapshot_identity"],
        snapshot.worker_identity()
    );
}

#[test]
fn ledger_rejects_legacy_request_and_row_authority() {
    let scope = fixed_ambient_scope("ledger");
    let catalog = catalog(&scope, 'f');
    let candidate = clause(&scope, "candidate", "01", "o:p::R", FrameworkIILevel::ZERO);
    let registered = catalog
        .register_batch(0, [(candidate, ExtendedClauseOrigin::Submitted)])
        .unwrap();
    let snapshot = Arc::new(
        LeveledCandidateSnapshot::build(
            &catalog,
            None,
            BTreeMap::from([(registered.ids()[0], FrameworkIILevel::ZERO)]),
        )
        .unwrap(),
    );
    let request = FrameworkIICheckRequest::new(
        0,
        registered.ids()[0],
        FrameworkIILevel::ZERO,
        FrameworkIICheckRole::Initialization,
        snapshot,
        false,
    )
    .unwrap();
    let mut detached = request.clone();
    detached.replace_request_digest_for_legacy_test("0".repeat(64));
    let mut ledger = LevelAttemptLedger::default();
    assert_eq!(
        ledger
            .append_attempt(detached, proved(&request))
            .unwrap_err(),
        FrameworkIIStateError::InvalidEvidence(
            "a check result carries a legacy or detached fixed-ambient request identity"
        ),
    );
    ledger
        .append_attempt(request.clone(), proved(&request))
        .unwrap();
    let mut legacy = ledger.clone();
    legacy
        .rewrite_attempt_digest_as_legacy_v2_for_test(0)
        .unwrap();
    assert!(ledger.merge_exact_extension(&legacy).is_err());
}

#[tokio::test]
async fn houdini_schedules_only_from_lean_minimum_levels() {
    let scope = fixed_ambient_scope("opaque-levels");
    let catalog = catalog(&scope, '1');
    // Deliberately invert the spelling intuition. Rust must obey only the Lean number.
    let prophecy_spelling = clause(
        &scope,
        "prophecy-spelling",
        "01",
        "y:p::R",
        FrameworkIILevel::ZERO,
    );
    let program_spelling = clause(
        &scope,
        "program-spelling",
        "02",
        "o:p::R",
        FrameworkIILevel::ONE,
    );
    let registered = catalog
        .register_batch(
            0,
            [
                (program_spelling.clone(), ExtendedClauseOrigin::Submitted),
                (prophecy_spelling.clone(), ExtendedClauseOrigin::Submitted),
            ],
        )
        .unwrap();
    let prophecy_id = catalog.find(&prophecy_spelling).unwrap().unwrap();
    let program_id = catalog.find(&program_spelling).unwrap().unwrap();
    let mut state = LeveledHoudiniState::new(catalog).unwrap();
    state.enqueue_registered(&registered).unwrap();
    let seen = Arc::new(Mutex::new(Vec::new()));
    let captured = Arc::clone(&seen);
    let mut checker = SyncFrameworkIIChecker::new(move |request: FrameworkIICheckRequest| {
        captured
            .lock()
            .unwrap()
            .push((request.clause(), request.level()));
        Ok(proved(&request))
    });
    let outcome = stabilize_leveled_houdini(&mut state, &mut checker)
        .await
        .unwrap();
    assert!(matches!(
        outcome,
        LeveledStabilizationOutcome::Stabilized(_)
    ));
    assert_eq!(
        state.committed_levels().get(&prophecy_id),
        Some(&FrameworkIILevel::ZERO)
    );
    assert_eq!(
        state.committed_levels().get(&program_id),
        Some(&FrameworkIILevel::ONE)
    );
    assert!(seen.lock().unwrap().iter().all(|(id, level)| {
        (*id == prophecy_id && *level == FrameworkIILevel::ZERO)
            || (*id == program_id && *level == FrameworkIILevel::ONE)
    }));
}

#[tokio::test]
async fn failed_level_is_retried_at_its_successor_without_symbol_classification() {
    let scope = fixed_ambient_scope("promotion");
    let catalog = catalog(&scope, '2');
    let candidate = clause(&scope, "candidate", "01", "o:p::R", FrameworkIILevel::ZERO);
    let registered = catalog
        .register_batch(0, [(candidate, ExtendedClauseOrigin::Submitted)])
        .unwrap();
    let candidate_id = registered.ids()[0];
    let mut state = LeveledHoudiniState::new(catalog).unwrap();
    state.enqueue_registered(&registered).unwrap();
    let first_maintenance = Arc::new(Mutex::new(true));
    let captured = Arc::clone(&first_maintenance);
    let mut checker = SyncFrameworkIIChecker::new(move |request: FrameworkIICheckRequest| {
        let mut first = captured.lock().unwrap();
        if *first
            && request.level() == FrameworkIILevel::ZERO
            && request.role() == FrameworkIICheckRole::Maintenance
        {
            *first = false;
            Ok(refuted(&request))
        } else {
            Ok(proved(&request))
        }
    });
    let outcome = stabilize_leveled_houdini(&mut state, &mut checker)
        .await
        .unwrap();
    assert!(matches!(
        outcome,
        LeveledStabilizationOutcome::Stabilized(_)
    ));
    assert_eq!(
        state.committed_levels().get(&candidate_id),
        Some(&FrameworkIILevel::ONE)
    );
}

#[tokio::test]
async fn cancelled_control_publishes_no_houdini_transition() {
    let scope = fixed_ambient_scope("cancelled");
    let catalog = catalog(&scope, '3');
    let candidate = clause(&scope, "candidate", "01", "o:p::R", FrameworkIILevel::ZERO);
    let registered = catalog
        .register_batch(0, [(candidate, ExtendedClauseOrigin::Submitted)])
        .unwrap();
    let mut state = LeveledHoudiniState::new(catalog).unwrap();
    state.enqueue_registered(&registered).unwrap();
    let revision = state.proposal_revision();
    let control = CancellationToken::new();
    control.cancel();
    let mut checker =
        SyncFrameworkIIChecker::new(|request: FrameworkIICheckRequest| Ok(proved(&request)));
    assert_eq!(
        super::stabilization::stabilize_leveled_houdini_under_control(
            &mut state,
            &mut checker,
            &control
        )
        .await
        .unwrap_err(),
        FrameworkIIStateError::Cancelled,
    );
    assert_eq!(state.proposal_revision(), revision);
    assert!(state.committed_levels().is_empty());
}

#[tokio::test(flavor = "current_thread")]
async fn protected_system_rows_are_reserved_first_installed_atomically_and_never_dropped() {
    let scope = fixed_ambient_scope("protected");
    let catalog = catalog(&scope, 'e');
    let system = clause(&scope, "system", "0000", "o:p::R", FrameworkIILevel::ZERO);
    let route_digest = "9".repeat(64);
    let origin = ExtendedClauseOrigin::edb_precondition_system(2, route_digest.clone()).unwrap();
    assert!(ExtendedClauseOrigin::edb_precondition_system(2, "short").is_err());

    // External batches cannot mint protected origins.
    assert_eq!(
        catalog
            .register_batch(0, [(system.clone(), origin.clone())])
            .unwrap_err(),
        FrameworkIIStateError::SystemOriginOutsideReservation
    );
    // Reservation rejects ordinary origins and prophecy-level rows.
    assert_eq!(
        catalog
            .reserve_system_clauses([(system.clone(), ExtendedClauseOrigin::Submitted)])
            .unwrap_err(),
        FrameworkIIStateError::NonSystemReservation
    );
    let prophetic = clause(&scope, "prophetic", "0001", "y:p::R", FrameworkIILevel::ONE);
    assert_eq!(
        catalog
            .reserve_system_clauses([(prophetic, origin.clone())])
            .unwrap_err(),
        FrameworkIIStateError::PropheticSystemClause
    );
    let reserved = catalog
        .reserve_system_clauses([(system.clone(), origin.clone())])
        .unwrap();
    assert_eq!(reserved.ids().len(), 1);
    let record = catalog.record(reserved.ids()[0]).unwrap();
    assert!(record.is_protected());
    assert_eq!(record.origin(), &origin);
    assert!(catalog.system_origins_reserved().unwrap());
    assert_eq!(
        catalog
            .reserve_system_clauses([(system.clone(), origin.clone())])
            .unwrap_err(),
        FrameworkIIStateError::SystemReservationAlreadyClosed
    );

    // A later external proposal of the same formula keeps the protected id.
    let ordinary = clause(&scope, "ordinary", "0002", "o:p::R", FrameworkIILevel::ZERO);
    let registered = catalog
        .register_batch(
            0,
            [
                (system.clone(), ExtendedClauseOrigin::Submitted),
                (ordinary.clone(), ExtendedClauseOrigin::Submitted),
            ],
        )
        .unwrap();
    assert_eq!(registered.ids()[0], reserved.ids()[0]);
    assert!(catalog.record(registered.ids()[0]).unwrap().is_protected());
    assert!(!catalog.record(registered.ids()[1]).unwrap().is_protected());

    let mut state = LeveledHoudiniState::new(catalog.clone()).unwrap();
    assert!(state.system_installation_pending().unwrap());
    state.enqueue_registered(&registered).unwrap();
    let mut checker =
        SyncFrameworkIIChecker::new(|request: FrameworkIICheckRequest| Ok(proved(&request)));
    let outcome = stabilize_leveled_houdini_with_system_clauses(&mut state, &mut checker)
        .await
        .unwrap();
    let LeveledStabilizationOutcome::Stabilized(core) = outcome else {
        panic!("all-proved system and ordinary rows stabilize: {outcome:?}")
    };
    assert!(state.system_clauses_installed());
    assert_eq!(state.system_clauses().len(), 1);
    assert!(!state.system_installation_pending().unwrap());
    assert_eq!(core.snapshot().canonical_order().len(), 2);
    assert_eq!(
        state.committed_levels().get(&reserved.ids()[0]),
        Some(&FrameworkIILevel::ZERO)
    );

    // The protected row can never be dropped and a refutation of it is invalid evidence.
    let protected_id = reserved.ids()[0];
    let dropped = [protected_id].into_iter().collect::<BTreeSet<_>>();
    match state.prepare_proposal_checkpoint(&dropped) {
        Err(FrameworkIIStateError::InvalidPlacement(_)) => {}
        Err(other) => panic!("unexpected drop rejection: {other:?}"),
        Ok(_) => panic!("a protected row must never be droppable"),
    }
}

/// The acceptance envelope's task identity is the frozen payload's own.
///
/// `campaign certify` compares the live binding's identity, rendered by
/// `task_identity_record`, against the object the envelope lifted out of
/// `FrozenLeveledCore::payload()`, which `task_identity_fields` rendered.
/// Two renderers that drifted by a single member would report every
/// unchanged input as `input_changed` — a status whose documented meaning is
/// that the declarations differ. One renderer, pinned here.
#[test]
fn one_renderer_produces_the_task_identity_the_envelope_is_checked_against() {
    let scope = fixed_ambient_scope("identity-renderer");
    assert_eq!(
        super::acceptance::task_identity_record(scope.task_identity()),
        super::catalog::task_identity_fields(&scope)
    );
    let members = super::catalog::task_identity_fields(&scope);
    let mut keys = members
        .as_object()
        .unwrap()
        .keys()
        .map(String::as_str)
        .collect::<Vec<_>>();
    keys.sort_unstable();
    assert_eq!(
        keys,
        [
            "canonical_id",
            "encoding_version",
            "module",
            "namespace",
            "semantic_version",
            "source_sha256"
        ]
    );
}

/// The record written at acceptance is the record the certificate build
/// writes, byte for byte.
///
/// Publication refuses a `Core.json` on disk that differs from the one it
/// would write, so a run whose acceptance record differed by so much as a
/// row would fail at its very last step after all the certification work.
/// One renderer is what makes that impossible, and a snapshot carrying a
/// protected precondition row is the case where two renderers would most
/// easily disagree: those rows are installed from the input again on every
/// re-admission and so are never part of the record.
#[tokio::test(flavor = "current_thread")]
async fn the_accepted_core_record_is_the_one_the_certificate_build_writes() {
    let scope = fixed_ambient_scope("accepted-core-record");
    let catalog = catalog(&scope, '3');
    let system = clause(&scope, "system", "0000", "o:p::R", FrameworkIILevel::ZERO);
    let origin = ExtendedClauseOrigin::edb_precondition_system(2, "7".repeat(64)).unwrap();
    let reserved = catalog
        .reserve_system_clauses([(system.clone(), origin)])
        .unwrap();
    let ordinary = clause(&scope, "ordinary", "0002", "o:p::R", FrameworkIILevel::ZERO);
    let registered = catalog
        .register_batch(
            0,
            [
                (system, ExtendedClauseOrigin::Submitted),
                (ordinary.clone(), ExtendedClauseOrigin::Submitted),
            ],
        )
        .unwrap();
    let mut state = LeveledHoudiniState::new(catalog.clone()).unwrap();
    state.enqueue_registered(&registered).unwrap();
    let mut checker =
        SyncFrameworkIIChecker::new(|request: FrameworkIICheckRequest| Ok(proved(&request)));
    let outcome = stabilize_leveled_houdini_with_system_clauses(&mut state, &mut checker)
        .await
        .unwrap();
    let LeveledStabilizationOutcome::Stabilized(core) = outcome else {
        panic!("all-proved rows stabilize: {outcome:?}")
    };
    let snapshot = core.snapshot();
    assert_eq!(snapshot.canonical_order().len(), 2);
    assert!(
        snapshot
            .records()
            .get(&reserved.ids()[0])
            .unwrap()
            .is_protected()
    );

    let rendered = String::from_utf8(super::acceptance::accepted_core_record_bytes(snapshot))
        .expect("the Core record is UTF-8");
    let value: serde_json::Value = serde_json::from_str(&rendered).unwrap();
    assert_eq!(value["kind"], super::certificate::CORE_ROWS_KIND);
    assert_eq!(value["version"], super::certificate::CORE_ROWS_VERSION);
    let rows = value["rows"].as_array().unwrap();
    assert_eq!(
        rows.len(),
        1,
        "the protected precondition row belongs to the input, not to the record: {rendered}"
    );
    assert_eq!(rows[0]["source"], ordinary.canonical_source());
    assert_eq!(rows[0]["level"], 0);

    // The acceptance path and the build path write the same bytes because
    // they call the same function over the same snapshot; writing both here
    // is what keeps that a checked fact rather than a convention.
    let root = std::env::temp_dir().join(format!(
        "whiel-accepted-core-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir_all(root.join("built")).unwrap();
    super::certificate::write_core_record(&root.join("built/Certificate"), snapshot)
        .await
        .unwrap();
    assert_eq!(
        rendered.as_bytes(),
        std::fs::read(root.join("built/Core.json")).unwrap()
    );
    std::fs::remove_dir_all(&root).unwrap();
}

#[tokio::test(flavor = "current_thread")]
async fn a_refutation_of_a_protected_row_is_invalid_evidence() {
    let scope = fixed_ambient_scope("protected-refuted");
    let catalog = catalog(&scope, 'f');
    let system = clause(&scope, "system", "0000", "o:p::R", FrameworkIILevel::ZERO);
    let origin = ExtendedClauseOrigin::edb_precondition_system(0, "8".repeat(64)).unwrap();
    let reserved = catalog.reserve_system_clauses([(system, origin)]).unwrap();
    let protected_id = reserved.ids()[0];
    let mut state = LeveledHoudiniState::new(catalog).unwrap();
    let mut checker = SyncFrameworkIIChecker::new(move |request: FrameworkIICheckRequest| {
        Ok(if request.clause() == protected_id {
            refuted(&request)
        } else {
            proved(&request)
        })
    });
    assert!(matches!(
        stabilize_leveled_houdini_with_system_clauses(&mut state, &mut checker).await,
        Err(FrameworkIIStateError::InvalidEvidence(_))
    ));
    assert!(!state.system_clauses_installed());
    assert!(state.committed_levels().is_empty());
    assert!(state.attempts().rows().is_empty());
}

#[test]
fn system_reservation_enforces_source_order_and_keeps_the_earliest_conjunct() {
    let scope = fixed_ambient_scope("protected-order");
    let first = clause(&scope, "first", "0000", "o:p::R", FrameworkIILevel::ZERO);
    let second = clause(&scope, "second", "0001", "o:p::R", FrameworkIILevel::ZERO);
    let origin = |ordinal: u64| {
        ExtendedClauseOrigin::edb_precondition_system(ordinal, "7".repeat(64)).unwrap()
    };

    let unordered = catalog(&scope, 'a');
    assert_eq!(
        unordered
            .reserve_system_clauses([(first.clone(), origin(3)), (second.clone(), origin(1))])
            .unwrap_err(),
        FrameworkIIStateError::ConflictingSystemOrigins
    );

    let repeated = catalog(&scope, 'b');
    let reserved = repeated
        .reserve_system_clauses([
            (first.clone(), origin(0)),
            (first.clone(), origin(4)),
            (second.clone(), origin(5)),
        ])
        .unwrap();
    assert_eq!(reserved.ids().len(), 2);
    let record = repeated.record(reserved.ids()[0]).unwrap();
    assert!(matches!(
        record.origin(),
        ExtendedClauseOrigin::EdbPreconditionSystem {
            conjunct_ordinal: 0,
            ..
        }
    ));
    assert_eq!(repeated.len().unwrap(), 2);
}

#[tokio::test]
async fn compress_core_default_is_disabled_and_new_with_options_rejects_nonempty_edges() {
    let scope = fixed_ambient_scope("compress_core_defaults");
    let default_catalog = catalog(&scope, 'd');
    let state = LeveledHoudiniState::new(default_catalog).unwrap();
    assert!(!state.compress_core());
    assert_eq!(state.compress_core_moves_total(), 0);
    assert_eq!(state.compress_core_attempts_total(), 0);

    let edge_scope = fixed_ambient_scope("compress_core_edges");
    let edge_catalog = catalog(&edge_scope, 'e');
    let some_clause = clause(
        &edge_scope,
        "edge-endpoint",
        "00",
        "o:p::R",
        FrameworkIILevel::ZERO,
    );
    edge_catalog
        .register_batch(0, [(some_clause, ExtendedClauseOrigin::Submitted)])
        .unwrap();
    let dummy_edge = (ClauseId::test(1), ClauseId::test(1));
    assert_eq!(
        LeveledHoudiniState::new_with_options(
            edge_catalog.clone(),
            None,
            false,
            BTreeSet::from([dummy_edge]),
            BTreeSet::new(),
            AgentToolPolicy::default(),
        )
        .unwrap_err(),
        FrameworkIIStateError::EdgeInputRequiresSymbolicMigration("maintenance_support_edges")
    );
    assert_eq!(
        LeveledHoudiniState::new_with_options(
            edge_catalog,
            None,
            false,
            BTreeSet::new(),
            BTreeSet::from([dummy_edge]),
            AgentToolPolicy::default(),
        )
        .unwrap_err(),
        FrameworkIIStateError::EdgeInputRequiresSymbolicMigration("maintenance_coverage_edges")
    );
}

// ------------------------------------------------------------
// The Halting Rule And The Optional Level Bound
// ------------------------------------------------------------

/// Records every request one scan issued, in order.
fn recording_checker(
    log: Arc<Mutex<Vec<(ClauseId, FrameworkIICheckRole, FrameworkIILevel)>>>,
    mut decide: impl FnMut(&FrameworkIICheckRequest) -> FrameworkIICheckOutcome + Send,
) -> SyncFrameworkIIChecker<
    impl FnMut(FrameworkIICheckRequest) -> Result<FrameworkIICheckOutcome, FrameworkIIStateError> + Send,
> {
    SyncFrameworkIIChecker::new(move |request: FrameworkIICheckRequest| {
        log.lock()
            .unwrap()
            .push((request.clause(), request.role(), request.level()));
        Ok(decide(&request))
    })
}

#[tokio::test]
async fn a_scan_halts_at_the_first_level_above_zero_whose_core_is_empty() {
    // Level 0 never halts, so levels 0 and 1 always run; level 1 has no Core
    // clause and nothing sits above it, so level 2 would replay level 1
    // verbatim and the scan ends with the failure pending at level 1.
    let scope = fixed_ambient_scope("halting");
    let catalog = catalog(&scope, 'a');
    let stuck = clause(&scope, "stuck", "01", "o:p::R", FrameworkIILevel::ZERO);
    let registered = catalog
        .register_batch(0, [(stuck, ExtendedClauseOrigin::Submitted)])
        .unwrap();
    let stuck_id = registered.ids()[0];
    let mut state = LeveledHoudiniState::new(catalog).unwrap();
    assert!(state.max_level().is_none());
    state.enqueue_registered(&registered).unwrap();

    let log = Arc::new(Mutex::new(Vec::new()));
    let mut checker = recording_checker(Arc::clone(&log), |request| {
        if request.role() == FrameworkIICheckRole::Initialization {
            proved(request)
        } else {
            refuted(request)
        }
    });
    let outcome = stabilize_leveled_houdini(&mut state, &mut checker)
        .await
        .unwrap();
    assert!(matches!(
        outcome,
        LeveledStabilizationOutcome::Stabilized(_)
    ));

    let levels = log
        .lock()
        .unwrap()
        .iter()
        .map(|(_, _, level)| *level)
        .collect::<BTreeSet<_>>();
    assert_eq!(
        levels,
        BTreeSet::from([FrameworkIILevel::ZERO, FrameworkIILevel::ONE]),
        "an unbounded scan runs levels 0 and 1 and then halts instead of climbing"
    );
    assert_eq!(
        state.pending_levels().get(&stuck_id),
        Some(&FrameworkIILevel::ONE),
        "the level-1 failure stays pending at level 1"
    );
    assert!(state.committed_levels().is_empty());
}

#[tokio::test]
async fn a_scan_continues_past_a_level_an_earlier_epochs_core_clause_occupies() {
    // `anchor` commits at level 1 in the first scan. In the second scan the
    // Core still holds level 1, so the halting test does not fire there and
    // `stuck` is promoted to level 2, where it does fire.
    let scope = fixed_ambient_scope("halting-continues");
    let catalog = catalog(&scope, 'b');
    let anchor = clause(&scope, "anchor", "01", "o:p::R", FrameworkIILevel::ZERO);
    let first_batch = catalog
        .register_batch(0, [(anchor, ExtendedClauseOrigin::Submitted)])
        .unwrap();
    let anchor_id = first_batch.ids()[0];
    let mut state = LeveledHoudiniState::new(catalog).unwrap();
    state.enqueue_registered(&first_batch).unwrap();

    let mut anchor_checker =
        SyncFrameworkIIChecker::new(move |request: FrameworkIICheckRequest| {
            Ok(
                if request.role() == FrameworkIICheckRole::Maintenance
                    && request.level() == FrameworkIILevel::ZERO
                {
                    refuted(&request)
                } else {
                    proved(&request)
                },
            )
        });
    stabilize_leveled_houdini(&mut state, &mut anchor_checker)
        .await
        .unwrap();
    assert_eq!(
        state.committed_levels().get(&anchor_id),
        Some(&FrameworkIILevel::ONE)
    );

    let stuck = clause(&scope, "stuck", "02", "o:p::R", FrameworkIILevel::ZERO);
    let second_batch = state
        .catalog()
        .register_batch(1, [(stuck, ExtendedClauseOrigin::Submitted)])
        .unwrap();
    let stuck_id = second_batch.ids()[0];
    state.enqueue_registered(&second_batch).unwrap();

    let log = Arc::new(Mutex::new(Vec::new()));
    let mut checker = recording_checker(Arc::clone(&log), |request| {
        if request.role() == FrameworkIICheckRole::Initialization {
            proved(request)
        } else {
            refuted(request)
        }
    });
    stabilize_leveled_houdini(&mut state, &mut checker)
        .await
        .unwrap();

    let log = log.lock().unwrap();
    assert!(
        log.iter().all(|(clause, ..)| *clause == stuck_id),
        "a committed clause receives no check of any kind"
    );
    let levels = log
        .iter()
        .map(|(_, _, level)| *level)
        .collect::<BTreeSet<_>>();
    assert_eq!(
        levels,
        BTreeSet::from([
            FrameworkIILevel::ZERO,
            FrameworkIILevel::ONE,
            FrameworkIILevel::new(2)
        ]),
        "the Core clause at level 1 keeps the scan going into level 2"
    );
    assert_eq!(
        state.pending_levels().get(&stuck_id),
        Some(&FrameworkIILevel::new(2))
    );
}

#[tokio::test]
async fn a_clause_whose_minimum_level_exceeds_the_bound_is_rejected_at_admission() {
    let scope = fixed_ambient_scope("level-bound");
    let catalog = catalog(&scope, '2');
    let above = clause(&scope, "above", "01", "o:p::R", FrameworkIILevel::new(2));
    let registered = catalog
        .register_batch(0, [(above, ExtendedClauseOrigin::Submitted)])
        .unwrap();
    let mut state =
        LeveledHoudiniState::new_with_max_level(catalog, Some(FrameworkIILevel::ONE)).unwrap();
    assert_eq!(
        state.enqueue_registered(&registered).unwrap_err(),
        FrameworkIIStateError::LevelBoundExceeded {
            clause: Some(registered.ids()[0]),
            minimum_level: 2,
            max_level: 1,
        },
        "a clause above the bound is rejected at admission, never parked"
    );
    assert!(state.pending_levels().is_empty());

    // A bound must be at least one: levels 0 and 1 always run.
    let zero_bound_catalog = LeveledClauseCatalog::new(scope.clone(), "3".repeat(64)).unwrap();
    assert_eq!(
        LeveledHoudiniState::new_with_max_level(zero_bound_catalog, Some(FrameworkIILevel::ZERO))
            .unwrap_err(),
        FrameworkIIStateError::InvalidPlacement("a fixed-ambient level bound must be at least one")
    );
}

#[tokio::test]
async fn no_clause_is_promoted_above_the_level_bound() {
    // `anchor` commits at level 1, so the halting test does not end the scan
    // there and the bound is what stops `stuck`'s promotion.
    let scope = fixed_ambient_scope("level-bound-promotion");
    let catalog = catalog(&scope, '4');
    let anchor = clause(&scope, "anchor", "01", "o:p::R", FrameworkIILevel::ZERO);
    let stuck = clause(&scope, "stuck", "02", "o:p::R", FrameworkIILevel::ZERO);
    let registered = catalog
        .register_batch(
            0,
            [
                (anchor.clone(), ExtendedClauseOrigin::Submitted),
                (stuck.clone(), ExtendedClauseOrigin::Submitted),
            ],
        )
        .unwrap();
    let anchor_id = catalog.find(&anchor).unwrap().unwrap();
    let stuck_id = catalog.find(&stuck).unwrap().unwrap();
    let mut state =
        LeveledHoudiniState::new_with_max_level(catalog, Some(FrameworkIILevel::ONE)).unwrap();
    state.enqueue_registered(&registered).unwrap();

    let log = Arc::new(Mutex::new(Vec::new()));
    let mut checker = recording_checker(Arc::clone(&log), move |request| {
        if request.role() == FrameworkIICheckRole::Initialization {
            return proved(request);
        }
        if request.clause() == stuck_id || request.level() == FrameworkIILevel::ZERO {
            refuted(request)
        } else {
            proved(request)
        }
    });
    stabilize_leveled_houdini(&mut state, &mut checker)
        .await
        .unwrap();

    assert_eq!(
        state.committed_levels().get(&anchor_id),
        Some(&FrameworkIILevel::ONE)
    );
    assert_eq!(
        state.pending_levels().get(&stuck_id),
        Some(&FrameworkIILevel::ONE),
        "a failure at the bound stays pending there"
    );
    assert_eq!(state.max_level_stops_total(), 1);
    assert!(
        log.lock()
            .unwrap()
            .iter()
            .all(|(_, _, level)| *level <= FrameworkIILevel::ONE),
        "no check is ever issued above the bound"
    );
}

// ------------------------------------------------------------
// Death, Suspension, And Core Compression
// ------------------------------------------------------------

#[tokio::test]
async fn a_never_committed_prophecy_free_clause_refuted_above_level_zero_is_dead() {
    // The countermodel, restricted to the ordinary relations, refutes the
    // level-zero initialization, so an
    // initialization refutation at any level is the level-zero verdict.
    let scope = fixed_ambient_scope("death-above-zero");
    let catalog = catalog(&scope, '5');
    let victim = clause(&scope, "victim", "01", "o:p::R", FrameworkIILevel::ZERO);
    let registered = catalog
        .register_batch(0, [(victim, ExtendedClauseOrigin::Submitted)])
        .unwrap();
    let victim_id = registered.ids()[0];
    let mut state = LeveledHoudiniState::new(catalog).unwrap();
    state.enqueue_registered(&registered).unwrap();

    let mut checker = SyncFrameworkIIChecker::new(move |request: FrameworkIICheckRequest| {
        Ok(match (request.role(), request.level()) {
            // Level zero: initialization holds, the step condition fails, so
            // the clause is promoted rather than killed.
            (FrameworkIICheckRole::Initialization, FrameworkIILevel::ZERO) => proved(&request),
            (FrameworkIICheckRole::Maintenance, FrameworkIILevel::ZERO) => refuted(&request),
            // Level one: the initialization is refuted, which is final.
            (FrameworkIICheckRole::Initialization, _) => refuted(&request),
            (FrameworkIICheckRole::Maintenance, _) => proved(&request),
        })
    });
    stabilize_leveled_houdini(&mut state, &mut checker)
        .await
        .unwrap();

    assert!(state.is_dead(victim_id));
    assert!(matches!(
        state.dead_cause(victim_id),
        Some(FrameworkIIDeadCause::Refuted(
            FrameworkIIDeadReason::ProphecyFreeInitializationRefuted { .. }
        ))
    ));
    assert!(!state.dead_cause(victim_id).unwrap().is_revivable());
    assert!(state.pending_levels().is_empty());
}

#[tokio::test]
async fn a_prophecy_bearing_clause_refuted_at_initialization_is_promoted_not_killed() {
    let scope = fixed_ambient_scope("prophecy-promotes");
    let catalog = catalog(&scope, '6');
    let candidate = clause(&scope, "candidate", "01", "y:p::R", FrameworkIILevel::ZERO);
    let registered = catalog
        .register_batch(0, [(candidate, ExtendedClauseOrigin::Submitted)])
        .unwrap();
    let candidate_id = registered.ids()[0];
    let mut state = LeveledHoudiniState::new(catalog).unwrap();
    state.enqueue_registered(&registered).unwrap();

    let mut checker = SyncFrameworkIIChecker::new(move |request: FrameworkIICheckRequest| {
        Ok(
            if request.role() == FrameworkIICheckRole::Initialization
                && request.level() == FrameworkIILevel::ZERO
            {
                refuted(&request)
            } else {
                proved(&request)
            },
        )
    });
    stabilize_leveled_houdini(&mut state, &mut checker)
        .await
        .unwrap();
    assert!(!state.is_dead(candidate_id));
    assert_eq!(
        state.committed_levels().get(&candidate_id),
        Some(&FrameworkIILevel::ONE)
    );
}

#[tokio::test]
async fn an_inconclusive_launch_suspends_every_further_check_of_that_clause() {
    // One stuck clause costs one *launch* per epoch. The level-zero
    // initialization launch comes back inconclusive; every remaining check
    // of that clause this epoch still reaches the checker, and is still
    // written to the ledger, but carries the instruction that no solver may
    // be started for it.
    let scope = fixed_ambient_scope("suspension");
    let catalog = catalog(&scope, '7');
    let stuck = clause(&scope, "stuck", "01", "o:p::R", FrameworkIILevel::ZERO);
    let registered = catalog
        .register_batch(0, [(stuck, ExtendedClauseOrigin::Submitted)])
        .unwrap();
    let stuck_id = registered.ids()[0];
    let mut state = LeveledHoudiniState::new(catalog).unwrap();
    state.enqueue_registered(&registered).unwrap();

    let log = Arc::new(Mutex::new(Vec::new()));
    let launches = Arc::new(Mutex::new(0u32));
    let counted = Arc::clone(&launches);
    let mut checker = recording_checker(Arc::clone(&log), move |request| {
        if request.launch_suppressed() {
            // What the production checker returns for a suspended clause
            // its semantic dictionary cannot answer: inconclusive, no
            // launch.
            return inconclusive(request, FrameworkIIInconclusiveReason::Suspended);
        }
        *counted.lock().unwrap() += 1;
        inconclusive(request, FrameworkIIInconclusiveReason::TimedOut)
    });
    stabilize_leveled_houdini(&mut state, &mut checker)
        .await
        .unwrap();

    assert_eq!(
        log.lock().unwrap().as_slice(),
        &[
            (
                stuck_id,
                FrameworkIICheckRole::Initialization,
                FrameworkIILevel::ZERO
            ),
            (
                stuck_id,
                FrameworkIICheckRole::Initialization,
                FrameworkIILevel::ONE
            ),
        ],
        "the suspended clause is still checked at level one, from the dictionary"
    );
    assert_eq!(
        *launches.lock().unwrap(),
        1,
        "the suspended clause is never launched again this epoch"
    );
    assert!(state.suspended_clauses().contains(&stuck_id));
    assert_eq!(
        state.pending_levels().get(&stuck_id),
        Some(&FrameworkIILevel::ONE),
        "an inconclusive outcome is a failure at its level, so the clause is promoted"
    );
    assert_eq!(
        state.attempts().rows().len(),
        2,
        "Check(q) records one ledger row per check, suspended or not"
    );
}

#[tokio::test]
async fn a_suspended_clause_refuted_from_the_dictionary_still_dies_without_a_launch() {
    // Suspension suppresses the launch, never the lookup: a never-committed
    // prophecy-free clause whose level-zero initialization was inconclusive
    // is still killed by a level-one refutation the checker serves from its
    // semantic dictionary, and no second solver runs.
    let scope = fixed_ambient_scope("suspension-death");
    let catalog = catalog(&scope, 'd');
    let doomed = clause(&scope, "doomed", "01", "o:p::R", FrameworkIILevel::ZERO);
    let registered = catalog
        .register_batch(0, [(doomed, ExtendedClauseOrigin::Submitted)])
        .unwrap();
    let doomed_id = registered.ids()[0];
    let mut state = LeveledHoudiniState::new(catalog).unwrap();
    state.enqueue_registered(&registered).unwrap();

    let launches = Arc::new(Mutex::new(0u32));
    let counted = Arc::clone(&launches);
    let mut checker = SyncFrameworkIIChecker::new(move |request: FrameworkIICheckRequest| {
        if request.launch_suppressed() {
            // A refutation entry matched: the dictionary answers a
            // suspended clause exactly as it answers any other.
            return Ok(refuted(&request));
        }
        *counted.lock().unwrap() += 1;
        Ok(inconclusive(
            &request,
            FrameworkIIInconclusiveReason::TimedOut,
        ))
    });
    stabilize_leveled_houdini(&mut state, &mut checker)
        .await
        .unwrap();

    assert_eq!(
        *launches.lock().unwrap(),
        1,
        "only the level-zero initialization launched a solver"
    );
    assert!(state.suspended_clauses().contains(&doomed_id));
    assert!(
        matches!(
            state.dead_cause(doomed_id),
            Some(FrameworkIIDeadCause::Refuted(
                FrameworkIIDeadReason::ProphecyFreeInitializationRefuted { .. }
            ))
        ),
        "a dictionary refutation kills a never-committed prophecy-free clause"
    );
    assert!(state.pending_levels().get(&doomed_id).is_none());
}

#[tokio::test]
async fn compress_core_restabilizes_from_minimum_levels_with_no_clause_ending_higher() {
    // `high` needs `low` as a same-level hypothesis to hold at level zero.
    // It first commits at level one without `low`; once `low` commits,
    // compression returns the whole Core to its minimum levels and `high`
    // re-converges at level zero.
    let scope = fixed_ambient_scope("compression");
    let catalog = catalog(&scope, '8');
    let high = clause(&scope, "high", "02", "y:p::R", FrameworkIILevel::ZERO);
    let first_batch = catalog
        .register_batch(0, [(high.clone(), ExtendedClauseOrigin::Submitted)])
        .unwrap();
    let high_id = catalog.find(&high).unwrap().unwrap();
    let mut state = LeveledHoudiniState::new_with_options(
        catalog,
        None,
        true,
        BTreeSet::new(),
        BTreeSet::new(),
        AgentToolPolicy::default(),
    )
    .unwrap();
    assert!(state.compress_core());
    state.enqueue_registered(&first_batch).unwrap();

    let low_slot: Arc<Mutex<Option<ClauseId>>> = Arc::new(Mutex::new(None));
    let checker_low = Arc::clone(&low_slot);
    let mut checker = SyncFrameworkIIChecker::new(move |request: FrameworkIICheckRequest| {
        if request.role() == FrameworkIICheckRole::Initialization || request.clause() != high_id {
            return Ok(proved(&request));
        }
        let low_present = checker_low
            .lock()
            .unwrap()
            .is_some_and(|low| request.snapshot().contains(low));
        Ok(
            if request.level() == FrameworkIILevel::ZERO && !low_present {
                refuted(&request)
            } else {
                proved(&request)
            },
        )
    });

    stabilize_leveled_houdini(&mut state, &mut checker)
        .await
        .unwrap();
    assert_eq!(
        state.committed_levels().get(&high_id),
        Some(&FrameworkIILevel::ONE)
    );
    assert_eq!(state.compress_core_attempts_total(), 1);
    assert_eq!(state.compress_core_moves_total(), 0);

    let low = clause(&scope, "low", "01", "y:p::R", FrameworkIILevel::ZERO);
    let second_batch = state
        .catalog()
        .register_batch(1, [(low.clone(), ExtendedClauseOrigin::Submitted)])
        .unwrap();
    let low_id = state.catalog().find(&low).unwrap().unwrap();
    *low_slot.lock().unwrap() = Some(low_id);
    state.enqueue_registered(&second_batch).unwrap();

    stabilize_leveled_houdini(&mut state, &mut checker)
        .await
        .unwrap();
    assert_eq!(
        state.committed_levels().get(&low_id),
        Some(&FrameworkIILevel::ZERO)
    );
    assert_eq!(
        state.committed_levels().get(&high_id),
        Some(&FrameworkIILevel::ZERO),
        "compression re-converges `high` at its minimum level"
    );
    assert_eq!(state.compress_core_attempts_total(), 2);
    assert_eq!(state.compress_core_moves_total(), 1);
}

/// Pass 7.5c-2 verification bullet: compression returns the Core to its
/// minimum levels, but a protected precondition row is never returned to
/// pending and is never rechecked — its two conditions closed through a
/// reviewed Lean theorem, not through the search.
#[tokio::test(flavor = "current_thread")]
async fn compression_never_resets_or_rechecks_a_protected_row() {
    let scope = fixed_ambient_scope("compression-protected");
    let catalog = catalog(&scope, 'c');
    let system = clause(&scope, "system", "0000", "o:p::R", FrameworkIILevel::ZERO);
    let origin = ExtendedClauseOrigin::edb_precondition_system(0, "7".repeat(64)).unwrap();
    let reserved = catalog.reserve_system_clauses([(system, origin)]).unwrap();
    let protected_id = reserved.ids()[0];
    let ordinary = clause(&scope, "ordinary", "0002", "o:p::R", FrameworkIILevel::ZERO);
    let registered = catalog
        .register_batch(0, [(ordinary.clone(), ExtendedClauseOrigin::Submitted)])
        .unwrap();
    let ordinary_id = registered.ids()[0];
    let mut state = LeveledHoudiniState::new_with_options(
        catalog,
        None,
        true,
        BTreeSet::new(),
        BTreeSet::new(),
        AgentToolPolicy::default(),
    )
    .unwrap();
    assert!(state.compress_core());
    state.enqueue_registered(&registered).unwrap();

    let installed = Arc::new(Mutex::new(false));
    let after_install = Arc::clone(&installed);
    let protected_checks_after_install = Arc::new(Mutex::new(0u32));
    let counted = Arc::clone(&protected_checks_after_install);
    let mut checker = SyncFrameworkIIChecker::new(move |request: FrameworkIICheckRequest| {
        if request.clause() == protected_id && *after_install.lock().unwrap() {
            *counted.lock().unwrap() += 1;
        }
        Ok(proved(&request))
    });
    let outcome = stabilize_leveled_houdini_with_system_clauses(&mut state, &mut checker)
        .await
        .unwrap();
    assert!(matches!(
        outcome,
        LeveledStabilizationOutcome::Stabilized(_)
    ));
    assert!(state.system_clauses_installed());
    assert_eq!(
        state.committed_levels().get(&protected_id),
        Some(&FrameworkIILevel::ZERO)
    );
    assert_eq!(
        state.committed_levels().get(&ordinary_id),
        Some(&FrameworkIILevel::ZERO)
    );
    *installed.lock().unwrap() = true;

    // A second clause makes the Core dirty again, so compression runs a
    // fresh re-stabilization over it.
    let extra = clause(&scope, "extra", "0003", "o:p::R", FrameworkIILevel::ZERO);
    let second_batch = state
        .catalog()
        .register_batch(1, [(extra, ExtendedClauseOrigin::Submitted)])
        .unwrap();
    state.enqueue_registered(&second_batch).unwrap();
    let attempts_before = state.compress_core_attempts_total();
    stabilize_leveled_houdini(&mut state, &mut checker)
        .await
        .unwrap();
    assert!(state.compress_core_attempts_total() > attempts_before);
    assert_eq!(
        state.committed_levels().get(&protected_id),
        Some(&FrameworkIILevel::ZERO),
        "compression never returns a protected row to pending"
    );
    assert!(state.pending_levels().get(&protected_id).is_none());
    assert_eq!(
        *protected_checks_after_install.lock().unwrap(),
        0,
        "an installed protected row is never rechecked"
    );
}

#[tokio::test]
async fn a_formerly_committed_clause_refuted_under_compression_is_promoted_not_killed() {
    // The death rule applies only to clauses that were never committed; a
    // Core clause whose initialization is refuted at a level below its old
    // one is promoted, and compression never removes it from the Core.
    let scope = fixed_ambient_scope("compression-death");
    let catalog = catalog(&scope, '9');
    let survivor = clause(&scope, "survivor", "01", "o:p::R", FrameworkIILevel::ZERO);
    let registered = catalog
        .register_batch(0, [(survivor, ExtendedClauseOrigin::Submitted)])
        .unwrap();
    let survivor_id = registered.ids()[0];
    let mut state = LeveledHoudiniState::new_with_options(
        catalog,
        None,
        true,
        BTreeSet::new(),
        BTreeSet::new(),
        AgentToolPolicy::default(),
    )
    .unwrap();
    state.enqueue_registered(&registered).unwrap();

    let level_zero_initializations = Arc::new(Mutex::new(0u32));
    let counted = Arc::clone(&level_zero_initializations);
    let mut checker = SyncFrameworkIIChecker::new(move |request: FrameworkIICheckRequest| {
        if request.level() != FrameworkIILevel::ZERO {
            return Ok(proved(&request));
        }
        match request.role() {
            FrameworkIICheckRole::Initialization => {
                let mut seen = counted.lock().unwrap();
                *seen += 1;
                // The first scan proves the level-zero initialization and
                // fails the step condition, so the clause commits at level
                // one; compression then meets a refutation at level zero.
                Ok(if *seen == 1 {
                    proved(&request)
                } else {
                    refuted(&request)
                })
            }
            FrameworkIICheckRole::Maintenance => Ok(refuted(&request)),
        }
    });
    stabilize_leveled_houdini(&mut state, &mut checker)
        .await
        .unwrap();

    assert!(
        !state.is_dead(survivor_id),
        "no clause dies under compression"
    );
    assert_eq!(
        state.committed_levels().get(&survivor_id),
        Some(&FrameworkIILevel::ONE),
        "the formerly committed clause is promoted back to its old level"
    );
    assert!(*level_zero_initializations.lock().unwrap() >= 2);
}

/// Pass 7.5d abort criterion: batching must not change which clause the
/// single-failure drop removes.
///
/// The fixture is order-sensitive on purpose. `bravo`'s step check always
/// fails; `charlie`'s fails only while `bravo` is still in the hypothesis
/// cohort. The contract's drop takes the *first* failure in check order, so
/// the sweep must drop `bravo`, and `charlie` must then prove against the
/// shrunken cohort: `Q' = {bravo}`. A dispatch that dropped the last
/// failure it saw, or the one whose outcome arrived first, would return
/// `{charlie}` or `{bravo, charlie}` instead.
async fn single_failure_drop_under(
    dispatch: FrameworkIISweepDispatch,
) -> (
    BTreeSet<ClauseId>,
    BTreeSet<ClauseId>,
    BTreeMap<ClauseId, FrameworkIILevel>,
    Vec<(ClauseId, FrameworkIICheckRole)>,
    ClauseId,
) {
    let scope = fixed_ambient_scope("batched-drop");
    let catalog = catalog(&scope, 'd');
    let names = ["alpha", "bravo", "charlie", "delta"];
    let clauses = names
        .iter()
        .enumerate()
        .map(|(index, name)| {
            clause(
                &scope,
                name,
                &format!("{:02}", index + 1),
                "o:p::R",
                FrameworkIILevel::ZERO,
            )
        })
        .collect::<Vec<_>>();
    let registered = catalog
        .register_batch(
            0,
            clauses
                .iter()
                .cloned()
                .map(|clause| (clause, ExtendedClauseOrigin::Submitted)),
        )
        .unwrap();
    let ids = registered.ids().to_vec();
    let (bravo, charlie) = (ids[1], ids[2]);
    let mut state = LeveledHoudiniState::new(catalog).unwrap();
    state.set_sweep_dispatch(dispatch);
    state.enqueue_registered(&registered).unwrap();

    let log = Arc::new(Mutex::new(Vec::new()));
    let captured = Arc::clone(&log);
    let mut checker = SyncFrameworkIIChecker::new(move |request: FrameworkIICheckRequest| {
        captured
            .lock()
            .unwrap()
            .push((request.clause(), request.role()));
        if request.role() == FrameworkIICheckRole::Maintenance
            && (request.clause() == bravo
                || (request.clause() == charlie && request.snapshot().contains(bravo)))
        {
            Ok(inconclusive(
                &request,
                FrameworkIIInconclusiveReason::TimedOut,
            ))
        } else {
            Ok(proved(&request))
        }
    });

    let initialization = match super::stabilization::init_pruning(
        &mut state,
        &mut checker,
        FrameworkIILevel::ZERO,
        None,
    )
    .await
    .unwrap()
    {
        super::stabilization::PhaseOutcome::Completed(failed) => failed,
        outcome => panic!("initialization must complete: {outcome:?}"),
    };
    let excluded = match super::stabilization::step_pruning(
        &mut state,
        &mut checker,
        FrameworkIILevel::ZERO,
        &initialization,
        None,
    )
    .await
    .unwrap()
    {
        super::stabilization::PhaseOutcome::Completed(excluded) => excluded,
        outcome => panic!("the step fixed point must complete: {outcome:?}"),
    };
    let requests = log.lock().unwrap().clone();
    (
        initialization,
        excluded,
        state.pending_levels().clone(),
        requests,
        bravo,
    )
}

#[tokio::test]
async fn batched_dispatch_drops_the_same_clause_as_sequential_dispatch() {
    let (batched_q, batched_excluded, batched_pending, batched_requests, batched_bravo) =
        single_failure_drop_under(FrameworkIISweepDispatch::Batched).await;
    let (
        sequential_q,
        sequential_excluded,
        sequential_pending,
        sequential_requests,
        sequential_bravo,
    ) = single_failure_drop_under(FrameworkIISweepDispatch::Sequential).await;

    assert!(
        batched_q.is_empty(),
        "no initialization failed: {batched_q:?}"
    );
    assert_eq!(batched_q, sequential_q);
    assert_eq!(batched_excluded, sequential_excluded);
    assert_eq!(batched_pending, sequential_pending);
    assert_eq!(
        batched_excluded,
        BTreeSet::from([batched_bravo]),
        "exactly the first failure in check order is dropped"
    );
    assert_eq!(sequential_excluded, BTreeSet::from([sequential_bravo]));

    // The dispatches differ in exactly the way the contract says they
    // should: a batched sweep collects the outcomes after the drop instead
    // of never asking for them.
    let maintenance = |requests: &[(ClauseId, FrameworkIICheckRole)]| {
        requests
            .iter()
            .filter(|(_, role)| *role == FrameworkIICheckRole::Maintenance)
            .count()
    };
    assert!(
        maintenance(&batched_requests) > maintenance(&sequential_requests),
        "batched={} sequential={}",
        maintenance(&batched_requests),
        maintenance(&sequential_requests)
    );
}

/// The `emit_invalid_certificate` request carries exactly the frozen
/// instance, the frozen fuel, and the Lean-issued instance identity, and
/// nothing else about the run. The instance is passed back unmodified as a
/// JSON value: Rust never rewrites or re-canonicalizes it.
#[test]
fn the_invalid_certificate_request_carries_only_the_frozen_instance_and_fuel() {
    let instance = json!({
        "relations": [
            {"name": "p::E", "rows": [["num:0", "num:1"], ["num:1", "num:2"]]},
            {"name": "p::S", "rows": []},
            {"name": "p::T", "rows": []}
        ],
        "unexpected": {"nested": [1, {"deeper": null}]}
    });
    let validated = super::counterexample::ValidatedCounterexample::for_test(
        instance.clone(),
        &"c".repeat(64),
        6,
    );
    let record = super::counterexample::FrozenCounterexampleRecord::freeze(
        validated,
        fixed_ambient_task().identity().clone(),
        "d".repeat(64),
        super::counterexample::CounterexampleProvenance::Consultation(Box::new(
            super::agent::AgentConsultationBinding::for_test(&"e".repeat(64), 3),
        )),
    );

    let payload = super::certificate_ops::invalid_certificate_payload(&record);
    assert_eq!(
        payload,
        json!({
            "instance": instance,
            "fuel": 6,
            "instance_identity": "c".repeat(64),
        })
    );
    assert_eq!(
        serde_json::to_string(&payload["instance"]).unwrap(),
        serde_json::to_string(&instance).unwrap()
    );
    // There is no bound to freeze: the record carries only the fuel the run
    // actually consumed, and that is what the emitter receives.
    assert_eq!(record.fuel_consumed(), 6);
    assert_eq!(
        record
            .consultation()
            .expect("a consulted record")
            .validation_ordinal(),
        3
    );
    assert_eq!(record.scope_identity_sha256(), "d".repeat(64));
}

// ------------------------------------------------------------
// Pass 7.5f: Freezing The Final Core
// ------------------------------------------------------------

/// A frozen-record fixture: `levels` places one clause per entry at the
/// given level, in the order given. Returns the catalog (so a caller can
/// re-derive the same snapshot), the Core handle, and the scope.
fn frozen_core_fixture(
    marker: char,
    levels: &[(&str, u64)],
) -> (
    FixedAmbientTaskScope,
    LeveledClauseCatalog,
    LeveledCoreHandle,
) {
    let scope = fixed_ambient_scope("freeze");
    let catalog = catalog(&scope, marker);
    let clauses = levels
        .iter()
        .enumerate()
        .map(|(index, (name, level))| {
            (
                clause(
                    &scope,
                    name,
                    &format!("{index:02}"),
                    if *level == 0 { "o:p::R" } else { "y:p::R" },
                    FrameworkIILevel::new(*level),
                ),
                ExtendedClauseOrigin::Submitted,
            )
        })
        .collect::<Vec<_>>();
    let registered = catalog.register_batch(0, clauses).unwrap();
    let level_of = registered
        .ids()
        .iter()
        .copied()
        .map(|id| {
            let level = catalog.record(id).unwrap().minimum_level();
            (id, level)
        })
        .collect::<BTreeMap<_, _>>();
    let snapshot = Arc::new(LeveledCandidateSnapshot::build(&catalog, None, level_of).unwrap());
    let core = LeveledCoreHandle::build(snapshot).unwrap();
    (scope, catalog, core)
}

/// A proved termination outcome over `core`'s own request digest.
fn termination_proof(core: &LeveledCoreHandle) -> FrameworkIITerminationProof {
    let evidence =
        FrameworkIICheckEvidence::new("a".repeat(64), format!("proof:{}", core.core_digest()))
            .unwrap();
    FrameworkIITerminationProof::from_outcome(core, &FrameworkIICheckOutcome::Proved(evidence))
        .unwrap()
}

#[test]
fn freezing_a_level_zero_core_records_its_rows_and_its_exact_condition_count() {
    let (scope, _catalog, core) = frozen_core_fixture('1', &[("alpha", 0)]);
    let provenance = SearchProfileProvenance::configured_only(ProofSearchProfile::Direct);
    let frozen =
        FrozenLeveledCore::freeze(&core, &scope, &termination_proof(&core), &provenance).unwrap();

    assert_eq!(frozen.core_size(), 1);
    // One initialization, one step, one termination.
    assert_eq!(frozen.condition_count(), 3);
    assert_eq!(frozen.rows()[0].level(), 0);
    assert_eq!(
        frozen.task_canonical_id(),
        scope.task_identity().canonical_id()
    );
    assert_eq!(frozen.scope_identity_sha256(), scope.identity_sha256());
    assert_eq!(frozen.core_digest(), core.core_digest());
    assert_eq!(
        frozen.partition_digest(),
        core.snapshot().partition_digest()
    );
    assert_eq!(frozen.canonical_sources().len(), 1);
    assert_eq!(
        frozen.snapshot_identity(),
        &core.snapshot().worker_identity()
    );
}

#[test]
fn a_multilevel_core_freezes_in_canonical_level_order() {
    let (scope, _catalog, core) =
        frozen_core_fixture('2', &[("high", 1), ("low", 0), ("higher", 1)]);
    let frozen = FrozenLeveledCore::freeze(
        &core,
        &scope,
        &termination_proof(&core),
        &SearchProfileProvenance::configured_only(ProofSearchProfile::Direct),
    )
    .unwrap();

    assert_eq!(frozen.core_size(), 3);
    assert_eq!(frozen.condition_count(), 7);
    let observed = frozen
        .rows()
        .iter()
        .map(FrozenCoreRow::level)
        .collect::<Vec<_>>();
    assert_eq!(observed, vec![0, 1, 1]);
    let ids = frozen
        .rows()
        .iter()
        .map(FrozenCoreRow::clause_id)
        .collect::<Vec<_>>();
    let rebuilt = core
        .snapshot()
        .canonical_order()
        .iter()
        .map(|clause| clause.get())
        .collect::<Vec<_>>();
    assert_eq!(ids, rebuilt);
}

/// Canonical order is `(level, registration order key, id)`, and clause ids
/// are monotone across registration batches while order keys are not. Two
/// clauses registered in different batches at one level can therefore be
/// canonically ordered with their ids *descending*, and such a Core freezes
/// and round-trips like any other: the record carries no order key, so the
/// only part of canonical order it can be checked against on its own is
/// the levels.
#[test]
fn two_registration_batches_may_reverse_the_id_order_at_one_level() {
    let scope = fixed_ambient_scope("freeze");
    let catalog = catalog(&scope, 'b');
    // The later batch's key sorts *before* the earlier batch's.
    let first = catalog
        .register_batch(
            0,
            [(
                clause(&scope, "zulu", "zz", "o:p::R", FrameworkIILevel::ZERO),
                ExtendedClauseOrigin::Submitted,
            )],
        )
        .unwrap();
    let second = catalog
        .register_batch(
            1,
            [(
                clause(&scope, "alpha", "aa", "o:p::R", FrameworkIILevel::ZERO),
                ExtendedClauseOrigin::Submitted,
            )],
        )
        .unwrap();
    let earlier = first.ids()[0];
    let later = second.ids()[0];
    assert!(earlier < later, "ids are monotone across batches");

    let level_of = [earlier, later]
        .into_iter()
        .map(|id| (id, FrameworkIILevel::ZERO))
        .collect::<BTreeMap<_, _>>();
    let snapshot = Arc::new(LeveledCandidateSnapshot::build(&catalog, None, level_of).unwrap());
    let core = LeveledCoreHandle::build(snapshot).unwrap();
    assert_eq!(
        core.snapshot().canonical_order(),
        [later, earlier],
        "the later batch's order key puts its higher id first"
    );

    let frozen = FrozenLeveledCore::freeze(
        &core,
        &scope,
        &termination_proof(&core),
        &SearchProfileProvenance::configured_only(ProofSearchProfile::Direct),
    )
    .expect("a Core whose canonical order reverses two ids at one level freezes");
    assert_eq!(
        frozen
            .rows()
            .iter()
            .map(FrozenCoreRow::clause_id)
            .collect::<Vec<_>>(),
        vec![later.get(), earlier.get()]
    );
    assert_eq!(
        frozen
            .rows()
            .iter()
            .map(FrozenCoreRow::level)
            .collect::<Vec<_>>(),
        vec![0, 0]
    );
    // And the record it writes is decodable: the decoder checks levels, not
    // ids, so it does not reject the record the freeze just built.
    let decoded = FrozenLeveledCore::from_payload(&frozen.payload()).unwrap();
    assert_eq!(decoded, frozen);
}

#[test]
fn a_refuted_or_inconclusive_termination_check_never_freezes_a_core() {
    let (_scope, _catalog, core) = frozen_core_fixture('3', &[("alpha", 0)]);
    let refutation = FrameworkIICheckOutcome::Refuted(
        FrameworkIICheckEvidence::new("b".repeat(64), "refutation").unwrap(),
    );
    assert_eq!(
        FrameworkIITerminationProof::from_outcome(&core, &refutation),
        Err(CoreFreezeError::TerminationRefuted)
    );
    let open = FrameworkIICheckOutcome::Inconclusive {
        reason: FrameworkIIInconclusiveReason::TimedOut,
        progress: FrameworkIICheckEvidence::new("c".repeat(64), "progress").unwrap(),
    };
    assert_eq!(
        FrameworkIITerminationProof::from_outcome(&core, &open),
        Err(CoreFreezeError::TerminationNotProved)
    );
}

#[test]
fn a_termination_proof_of_one_core_cannot_freeze_another() {
    let (scope, _catalog, first) = frozen_core_fixture('4', &[("alpha", 0)]);
    let (_scope, _catalog, second) = frozen_core_fixture('5', &[("beta", 0)]);
    let error = FrozenLeveledCore::freeze(
        &second,
        &scope,
        &termination_proof(&first),
        &SearchProfileProvenance::configured_only(ProofSearchProfile::Direct),
    )
    .unwrap_err();
    assert!(matches!(
        error,
        CoreFreezeError::TerminationProofIsForAnotherCore { .. }
    ));
}

#[test]
fn every_job_takes_its_own_provenance_label_and_never_a_fallback() {
    let (scope, _catalog, core) = frozen_core_fixture('6', &[("alpha", 0), ("beta", 1)]);
    let rows = core.snapshot().canonical_order().to_vec();
    let first = core.snapshot().records()[&rows[0]]
        .formula()
        .identity_sha256()
        .to_string();
    // A mixed-profile run: the first clause's step condition was won by
    // CASC, the termination condition too; every other condition was closed
    // without a launch and takes the configured profile.
    let provenance = SearchProfileProvenance::from_dictionary_winners(
        ProofSearchProfile::Direct,
        [
            (
                super::certificate_profiles::tagged_conjecture_key(
                    FrameworkIICheckRole::Maintenance,
                    &first,
                ),
                ProofSearchProfile::Casc2025,
            ),
            (
                super::certificate_profiles::termination_conjecture_key(),
                ProofSearchProfile::Casc2025,
            ),
        ],
    );
    // Under a run whose CASC portfolio is enabled: this fixture is about the
    // label plumbing, and a run with the portfolio disabled refuses a
    // `casc_2025` label outright (Milestone 7.5 review, finding 5, pinned by
    // `a_casc_label_is_refused_at_the_freeze_when_the_casc_portfolio_is_disabled`).
    let frozen = FrozenLeveledCore::freeze_under(
        &core,
        &scope,
        &termination_proof(&core),
        &provenance,
        CascPortfolioPolicy::Enabled,
    )
    .unwrap();

    assert_eq!(
        frozen.rows()[0].initialization_profile(),
        ProofSearchProfile::Direct
    );
    assert_eq!(
        frozen.rows()[0].step_profile(),
        ProofSearchProfile::Casc2025
    );
    assert_eq!(
        frozen.rows()[1].initialization_profile(),
        ProofSearchProfile::Direct
    );
    assert_eq!(frozen.rows()[1].step_profile(), ProofSearchProfile::Direct);
    assert_eq!(frozen.termination_profile(), ProofSearchProfile::Casc2025);

    // The same labels are what a certificate job resolves to.
    let zero = frozen.rows()[0].clause_id();
    assert_eq!(
        frozen.job_profile("initialization", Some(zero)).unwrap(),
        ProofSearchProfile::Direct
    );
    assert_eq!(
        frozen.job_profile("maintenance", Some(zero)).unwrap(),
        ProofSearchProfile::Casc2025
    );
    assert_eq!(
        frozen.job_profile("termination", None).unwrap(),
        ProofSearchProfile::Casc2025
    );
    // No fallback exists for a job the frozen record does not describe.
    assert!(matches!(
        frozen.job_profile("initialization", Some(9999)),
        Err(CoreFreezeError::JobNamesAnUnfrozenClause(9999))
    ));
    assert!(matches!(
        frozen.job_profile("initialization", None),
        Err(CoreFreezeError::JobHasNoClause(_))
    ));
    assert!(matches!(
        frozen.job_profile("termination", Some(zero)),
        Err(CoreFreezeError::TerminationJobNamesAClause)
    ));
    assert!(matches!(
        frozen.job_profile("elsewhere", Some(zero)),
        Err(CoreFreezeError::UnrecognizedRole(_))
    ));
}

/// A protected precondition row is a Core clause like any other: its two
/// conditions are frozen and counted, even though the search closed them by
/// reviewed Lean theorem selection and never launched a solver for them.
/// A theorem-closed condition records no winner, so both of its labels are
/// the run's configured search profile.
#[test]
fn a_protected_rows_two_conditions_are_frozen_like_any_other() {
    let scope = fixed_ambient_scope("freeze");
    let catalog = catalog(&scope, '7');
    let protected = clause(&scope, "protected", "00", "o:p::R", FrameworkIILevel::ZERO);
    let reserved = catalog
        .reserve_system_clauses([(
            protected,
            ExtendedClauseOrigin::edb_precondition_system(0, "d".repeat(64)).unwrap(),
        )])
        .unwrap();
    let ordinary = clause(&scope, "ordinary", "01", "o:p::R", FrameworkIILevel::ZERO);
    let registered = catalog
        .register_batch(0, [(ordinary, ExtendedClauseOrigin::Submitted)])
        .unwrap();
    let protected_id = reserved.ids()[0].get();
    let level_of = reserved
        .ids()
        .iter()
        .chain(registered.ids())
        .copied()
        .map(|id| (id, FrameworkIILevel::ZERO))
        .collect::<BTreeMap<_, _>>();
    let snapshot = Arc::new(LeveledCandidateSnapshot::build(&catalog, None, level_of).unwrap());
    let core = LeveledCoreHandle::build(snapshot).unwrap();

    // A `casc_2025`-configured run, so the portfolio is enabled: this
    // fixture is about counting and labelling a protected row's two frozen
    // conditions, not about the portfolio policy.
    let frozen = FrozenLeveledCore::freeze_under(
        &core,
        &scope,
        &termination_proof(&core),
        &SearchProfileProvenance::configured_only(ProofSearchProfile::Casc2025),
        CascPortfolioPolicy::Enabled,
    )
    .unwrap();
    assert_eq!(frozen.core_size(), 2);
    assert_eq!(frozen.condition_count(), 5);
    let protected_row = frozen
        .rows()
        .iter()
        .find(|row| row.clause_id() == protected_id)
        .expect("the protected row is frozen alongside the ordinary one");
    assert_eq!(
        protected_row.initialization_profile(),
        ProofSearchProfile::Casc2025
    );
    assert_eq!(protected_row.step_profile(), ProofSearchProfile::Casc2025);
}

/// No launch of a run whose CASC portfolio is disabled can produce a
/// `casc_2025` label, so a Core carrying one contradicts its own run: the
/// freeze refuses it with a named error rather than carrying the
/// contradiction into certification. The same Core freezes under a run
/// whose portfolio is enabled.
#[test]
fn a_casc_label_is_refused_at_the_freeze_when_the_casc_portfolio_is_disabled() {
    let (scope, _catalog, core) = frozen_core_fixture('9', &[("alpha", 0), ("beta", 1)]);

    // A `casc_2025` clause condition.
    let identity = core.snapshot().records().values().next().unwrap();
    let clause_key = super::certificate_profiles::tagged_conjecture_key(
        FrameworkIICheckRole::Initialization,
        identity.formula().identity_sha256(),
    );
    let clause_labelled = SearchProfileProvenance::from_dictionary_winners(
        ProofSearchProfile::Direct,
        [(clause_key, ProofSearchProfile::Casc2025)],
    );
    let error =
        FrozenLeveledCore::freeze(&core, &scope, &termination_proof(&core), &clause_labelled)
            .expect_err("a casc_2025 clause label is refused while the portfolio is disabled");
    let CoreFreezeError::CascProfileWhileCascDisabled { job, clause_id } = &error else {
        panic!("{error}")
    };
    assert_eq!(job, "initialization");
    assert!(clause_id.is_some());
    let message = error.to_string();
    assert!(message.contains("casc_2025"), "{message}");
    assert!(
        message.contains("no launch of it could have produced that label"),
        "{message}"
    );

    // The termination job is refused the same way, and names no clause.
    let termination_labelled = SearchProfileProvenance::from_dictionary_winners(
        ProofSearchProfile::Direct,
        [(
            super::certificate_profiles::termination_conjecture_key(),
            ProofSearchProfile::Casc2025,
        )],
    );
    let error = FrozenLeveledCore::freeze(
        &core,
        &scope,
        &termination_proof(&core),
        &termination_labelled,
    )
    .expect_err("a casc_2025 termination label is refused too");
    assert_eq!(
        error,
        CoreFreezeError::CascProfileWhileCascDisabled {
            job: "termination".to_string(),
            clause_id: None,
        }
    );

    // Enabled, the same Core freezes and keeps its label.
    let frozen = FrozenLeveledCore::freeze_under(
        &core,
        &scope,
        &termination_proof(&core),
        &clause_labelled,
        CascPortfolioPolicy::Enabled,
    )
    .expect("a run whose CASC portfolio is enabled freezes the same Core");
    assert!(
        frozen
            .rows()
            .iter()
            .any(|row| row.initialization_profile() == ProofSearchProfile::Casc2025)
    );

    // An all-direct Core freezes under either policy.
    let direct = SearchProfileProvenance::configured_only(ProofSearchProfile::Direct);
    assert!(
        FrozenLeveledCore::freeze(&core, &scope, &termination_proof(&core), &direct).is_ok(),
        "a direct-only Core is unaffected by the portfolio policy"
    );
}

/// A deferred certification rebuilds from the acceptance envelope's frozen
/// Core payload, and the labels it reads there have to be the labels the
/// freeze wrote — otherwise a condition the portfolio proved would be
/// re-proved under the direct profile, which is in general out of reach
/// inside a certificate job's allowance. This pins the renderer and the
/// reader to each other.
#[test]
fn a_portfolio_label_survives_the_frozen_payload_into_a_rebuild() {
    let (scope, _catalog, core) = frozen_core_fixture('a', &[("alpha", 0), ("beta", 1)]);
    let snapshot = core.snapshot();
    let mut identities = snapshot.records().values();
    let first = identities.next().unwrap().formula();
    let clause_labelled = SearchProfileProvenance::from_dictionary_winners(
        ProofSearchProfile::Direct,
        [
            (
                super::certificate_profiles::tagged_conjecture_key(
                    FrameworkIICheckRole::Maintenance,
                    first.identity_sha256(),
                ),
                ProofSearchProfile::Casc2025,
            ),
            (
                super::certificate_profiles::termination_conjecture_key(),
                ProofSearchProfile::Casc2025,
            ),
        ],
    );
    let frozen = FrozenLeveledCore::freeze_under(
        &core,
        &scope,
        &termination_proof(&core),
        &clause_labelled,
        CascPortfolioPolicy::Enabled,
    )
    .unwrap();

    let recorded =
        crate::certificate_cli::RecordedCoreProfiles::from_frozen_payload(&frozen.payload())
            .expect("the acceptance envelope's Core payload carries every label");
    assert_eq!(recorded.termination(), ProofSearchProfile::Casc2025);
    for row in frozen.rows() {
        assert_eq!(
            recorded.clause_labels(row.canonical_source()),
            Some((row.initialization_profile(), row.step_profile())),
            "clause {} lost its labels on the way through the record",
            row.clause_id()
        );
    }
    assert!(
        frozen
            .rows()
            .iter()
            .any(|row| row.step_profile() == ProofSearchProfile::Casc2025),
        "the fixture exercises a portfolio-won condition"
    );

    // A payload missing its labels is refused, never rebuilt under a
    // guessed profile.
    let mut stripped = frozen.payload();
    stripped["rows"][0]
        .as_object_mut()
        .unwrap()
        .remove("step_profile");
    assert!(crate::certificate_cli::RecordedCoreProfiles::from_frozen_payload(&stripped).is_err());
}

#[test]
fn a_frozen_record_round_trips_through_its_canonical_payload() {
    let (scope, _catalog, core) = frozen_core_fixture('8', &[("alpha", 0), ("beta", 1)]);
    let frozen = FrozenLeveledCore::freeze(
        &core,
        &scope,
        &termination_proof(&core),
        &SearchProfileProvenance::configured_only(ProofSearchProfile::Direct),
    )
    .unwrap();
    let decoded = FrozenLeveledCore::from_payload(&frozen.payload()).unwrap();
    assert_eq!(decoded, frozen);
    assert_eq!(decoded.freeze_digest(), frozen.freeze_digest());
    assert_eq!(frozen.payload()["kind"], json!(FROZEN_CORE_KIND));
    assert_eq!(frozen.payload()["version"], json!(FROZEN_CORE_VERSION));
}

/// Every digested member is required, the freeze digest among them.
///
/// A record with no digest is refused rather than accepted unchecked: an
/// undigested record is exactly the shape a truncated or hand-edited one
/// takes. The scope and snapshot identities are digested members too, so a
/// record that dropped either is refused before anything reads it.
#[test]
fn a_record_missing_its_digest_or_an_identity_is_refused() {
    let (scope, _catalog, core) = frozen_core_fixture('c', &[("alpha", 0)]);
    let frozen = FrozenLeveledCore::freeze(
        &core,
        &scope,
        &termination_proof(&core),
        &SearchProfileProvenance::configured_only(ProofSearchProfile::Direct),
    )
    .unwrap();
    for member in ["freeze_digest", "scope_identity", "snapshot_identity"] {
        let mut payload = frozen.payload();
        payload.as_object_mut().unwrap().remove(member);
        assert!(
            matches!(
                FrozenLeveledCore::from_payload(&payload),
                Err(CoreFreezeError::MalformedPayload(_))
            ),
            "a record without {member} must be refused"
        );
    }
    // Both identities are inside the digest, so swapping either one out
    // without re-signing is caught as tampering rather than accepted.
    let mut payload = frozen.payload();
    payload["snapshot_identity"] = json!({"kind": "another snapshot"});
    assert_eq!(
        FrozenLeveledCore::from_payload(&payload),
        Err(CoreFreezeError::FreezeDigestMismatch)
    );
    let mut payload = frozen.payload();
    payload["scope_identity"] = json!({"kind": "another scope"});
    assert_eq!(
        FrozenLeveledCore::from_payload(&payload),
        Err(CoreFreezeError::FreezeDigestMismatch)
    );
}

#[test]
fn a_library_bearing_frozen_record_is_refused_by_name() {
    let (scope, _catalog, core) = frozen_core_fixture('9', &[("alpha", 0)]);
    let frozen = FrozenLeveledCore::freeze(
        &core,
        &scope,
        &termination_proof(&core),
        &SearchProfileProvenance::configured_only(ProofSearchProfile::Direct),
    )
    .unwrap();
    for member in [
        "library_selections",
        "library_use_digests",
        "augmented_jobs",
        "fresh_symbol_witness",
        "use_list",
    ] {
        let mut payload = frozen.payload();
        payload
            .as_object_mut()
            .unwrap()
            .insert(member.to_string(), json!([]));
        assert!(
            matches!(
                FrozenLeveledCore::from_payload(&payload),
                Err(CoreFreezeError::LibraryBearingRecord(_))
            ),
            "member {member} must be refused as library-bearing"
        );
    }
    // A row-level library member is refused the same way.
    let mut payload = frozen.payload();
    payload["rows"][0]
        .as_object_mut()
        .unwrap()
        .insert("library_entry".to_string(), json!("epsilon_max"));
    assert!(matches!(
        FrozenLeveledCore::from_payload(&payload),
        Err(CoreFreezeError::LibraryBearingRecord(_))
    ));
    // Any other unknown member is refused too, just not by that name.
    let mut payload = frozen.payload();
    payload
        .as_object_mut()
        .unwrap()
        .insert("attempt_id".to_string(), json!(7));
    assert!(matches!(
        FrozenLeveledCore::from_payload(&payload),
        Err(CoreFreezeError::UnknownMember(_))
    ));
}

#[test]
fn a_reordered_duplicated_or_tampered_frozen_record_is_refused() {
    let (scope, _catalog, core) =
        frozen_core_fixture('a', &[("alpha", 0), ("beta", 1), ("gamma", 1)]);
    let frozen = FrozenLeveledCore::freeze(
        &core,
        &scope,
        &termination_proof(&core),
        &SearchProfileProvenance::configured_only(ProofSearchProfile::Direct),
    )
    .unwrap();

    let mut reordered = frozen.payload();
    let rows = reordered["rows"].as_array_mut().unwrap();
    rows.swap(0, 2);
    assert_eq!(
        FrozenLeveledCore::from_payload(&reordered),
        Err(CoreFreezeError::RowsOutOfCanonicalOrder)
    );

    let mut duplicated = frozen.payload();
    let rows = duplicated["rows"].as_array_mut().unwrap();
    let first = rows[0].clone();
    rows.insert(1, first);
    assert!(matches!(
        FrozenLeveledCore::from_payload(&duplicated),
        Err(CoreFreezeError::DuplicateRow(_))
    ));

    // Relabelling the last row keeps the record in canonical order, so the
    // refusal is the content check rather than the order check.
    let mut relabelled = frozen.payload();
    relabelled["rows"][2]["level"] = json!(9);
    assert_eq!(
        FrozenLeveledCore::from_payload(&relabelled),
        Err(CoreFreezeError::FreezeDigestMismatch)
    );

    let mut reprofiled = frozen.payload();
    reprofiled["rows"][0]["initialization_profile"] = json!("casc_2025");
    assert_eq!(
        FrozenLeveledCore::from_payload(&reprofiled),
        Err(CoreFreezeError::FreezeDigestMismatch)
    );

    let mut retired = frozen.payload();
    retired["version"] = json!(FROZEN_CORE_VERSION + 1);
    assert!(matches!(
        FrozenLeveledCore::from_payload(&retired),
        Err(CoreFreezeError::MalformedPayload(_))
    ));
}
