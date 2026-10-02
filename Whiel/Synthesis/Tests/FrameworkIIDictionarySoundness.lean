-- Author: Jesse Comer
import
  Whiel.Synthesis.FrameworkII.FixedAmbient.DictionarySoundness
import Whiel.Tests.FixedAmbientProphecy

/-
  Witnesses for the two non-theorems behind the semantic
  dictionary's one-directional rules.

  The converse of cross-role reuse fails: a proof of
  `wp(body, c)` is not a proof of `c`, so a step entry never
  answers an initialization request. The empty-instance
  verdict does not transfer from a request to the subset of
  premises a proof cited, so every proof hit repeats the
  empty-instance check on the new obligation.
-/

------------------------------------------------------------
-- The Converse Cross-Role Direction Fails
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Tests
namespace FrameworkIIDictionarySoundness

open Concrete
open Whiel.Tests.FixedAmbientProphecyCanary

/- A state whose `R` row is nonempty. -/
def rNonempty : Instance Data ambientSchema :=
  Instance.update
    (Instance.empty ambientSchema)
    ordinaryR
    {Vector.singleton (Data.num 0)}

/- The canary body empties `R`: `wp(body, R = ∅)` holds. -/
theorem wp_valid_from_nothing :
    QFEntailment.Valid (D := Data) (Γ := ambientSchema)
      ⟨[], QFAssertExpr.wpLoopFree loopBody (by decide)
        ordinaryREmpty⟩ := by
  intro state _
  rw [QFAssertExpr.wpLoopFree_eval_iff]
  intro final hStep
  exact (ordinaryREmpty_eval_iff final).mpr
    (loopBody_outputs_empty hStep).1

/- `R = ∅` itself does not hold from no premises. -/
theorem clause_not_valid_from_nothing :
    ¬ QFEntailment.Valid (D := Data) (Γ := ambientSchema)
      ⟨[], ordinaryREmpty⟩ := by
  intro hValid
  have hEmpty :=
    (ordinaryREmpty_eval_iff rNonempty).mp
      (hValid rNonempty (by
        intro premise hPremise
        simp at hPremise))
  rw [rNonempty, Instance.update_lookup_eq] at hEmpty
  exact Finset.singleton_ne_empty _ hEmpty

/-
  Lemma "Cross-role reuse" (ii): the step conjecture does
  not imply the initialization conjecture, by the
  contract's own witness: `body` assigns `R := ∅` and `c`
  is `R = ∅`.
-/
theorem cross_role_converse_fails :
    ¬ (QFEntailment.Valid (D := Data) (Γ := ambientSchema)
        ⟨[], QFAssertExpr.wpLoopFree loopBody (by decide)
          ordinaryREmpty⟩ →
      QFEntailment.Valid (D := Data) (Γ := ambientSchema)
        ⟨[], ordinaryREmpty⟩) :=
  fun h => clause_not_valid_from_nothing
    (h wp_valid_from_nothing)

end FrameworkIIDictionarySoundness
end Tests
end Synthesis
end Whiel

------------------------------------------------------------
-- The Empty-Instance Verdict Does Not Transfer
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Tests
namespace FrameworkIIDictionarySoundness

open Concrete
open Whiel.Tests.FixedAmbientProphecyCanary

/- A schema with exactly one unary relation. -/
def oneSchema : UnnamedSchema WhielNames where
  syms := {ordinaryRName}
  arity := fun _ => 1

def oneR : oneSchema.syms :=
  ⟨ordinaryRName, by simp [oneSchema]⟩

/- The one symbol of the one-relation schema. -/
theorem eq_oneR (relation : oneSchema.syms) :
    relation = oneR := by
  apply Subtype.ext
  have hMem : relation.1 ∈ ({ordinaryRName} : Finset _) :=
    relation.2
  exact Finset.mem_singleton.mp hMem

def rEmptyOne : QFAssertExpr Data oneSchema :=
  .eq (RAExpr.rel oneR) (RAExpr.empty 1)

/- `R ≠ ∅`, the one formula of the witness. -/
def rNonemptyOne : QFAssertExpr Data oneSchema :=
  .not rEmptyOne

private theorem eval_empty_one
    (state : Instance Data oneSchema) :
    (RAExpr.empty 1).eval state = ∅ := by
  simp [RAExpr.eval, RAExpr.empty, RawRAExpr.eval?]

private theorem eval_rel_one
    (state : Instance Data oneSchema) :
    (RAExpr.rel oneR).eval state = state oneR := by
  have hSpec :=
    RAExpr.raw_eval?_eq_eval
      (RAExpr.rel oneR :
        RAExpr Data oneSchema (oneSchema.arity oneR))
      state
  have hRaw :
      (RAExpr.rel oneR :
        RAExpr Data oneSchema
          (oneSchema.arity oneR)).expr.eval?
          (Γ := oneSchema) state =
        some ⟨oneSchema.arity oneR, state oneR⟩ := by
    simp [RAExpr.rel, RawRAExpr.eval?,
      Instance.relation?, oneR.2]
  rw [hRaw] at hSpec
  exact (eq_of_heq
    (Sigma.mk.inj (Option.some.inj hSpec)).2).symm

theorem rNonemptyOne_eval_iff
    (state : Instance Data oneSchema) :
    rNonemptyOne.eval state ↔ state oneR ≠ ∅ := by
  change ¬ ((RAExpr.rel oneR).eval state =
      (RAExpr.empty 1).eval state) ↔ _
  rw [eval_rel_one, eval_empty_one]
  exact Iff.rfl

/- In the one-relation schema, adom-empty means `R = ∅`. -/
theorem adomEmpty_iff
    (state : Instance Data oneSchema) :
    state.AdomEmpty ↔ state oneR = ∅ := by
  constructor
  · intro hAdom
    exact Instance.relation_eq_empty_of_adomEmpty
      state hAdom oneR (by decide)
  · intro hEmpty
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro value hValue
    rcases (Instance.in_Adom_iff_in_Relation
      state).mp hValue with ⟨relation, tuple, hTuple, _⟩
    have hRel := eq_oneR relation
    subst hRel
    rw [hEmpty] at hTuple
    simp at hTuple

/-
  The refuted-looking request `R ≠ ∅ ⊨ R ≠ ∅` is valid, and
  its empty half holds. A solver proves its conjecture over
  nonempty domains citing nothing: in a one-relation
  schema every nonempty active domain makes `R` nonempty.
-/
theorem original_request_valid :
    QFEntailment.ValidOnEmpty (D := Data) (Γ := oneSchema)
      ⟨[rNonemptyOne], rNonemptyOne⟩ :=
  fun _ _ hAxioms =>
    hAxioms rNonemptyOne (List.mem_cons.mpr (Or.inl rfl))

theorem cited_set_validOnNonempty :
    QFEntailment.ValidOnNonempty
      (D := Data) (Γ := oneSchema) ⟨[], rNonemptyOne⟩ := by
  intro state hAdom _
  rw [rNonemptyOne_eval_iff]
  intro hEmpty
  exact hAdom ((adomEmpty_iff state).mpr hEmpty)

/- The cited subset fails at the empty instance. -/
theorem cited_set_not_validOnEmpty :
    ¬ QFEntailment.ValidOnEmpty
      (D := Data) (Γ := oneSchema) ⟨[], rNonemptyOne⟩ := by
  intro hValid
  have hConj :=
    hValid (Instance.empty oneSchema)
      (Instance.empty_adomEmpty oneSchema)
      (by
        intro premise hPremise
        simp at hPremise)
  rw [rNonemptyOne_eval_iff] at hConj
  exact hConj rfl

/-
  The empty-instance verdict of the original request does
  not transfer to the cited subset, although the nonempty
  half does; so a proof hit must check the empty instance
  on the new obligation, never inherit it from the entry.
-/
theorem empty_verdict_does_not_transfer :
    QFEntailment.ValidOnEmpty (D := Data) (Γ := oneSchema)
        ⟨[rNonemptyOne], rNonemptyOne⟩ ∧
      QFEntailment.ValidOnNonempty
        (D := Data) (Γ := oneSchema) ⟨[], rNonemptyOne⟩ ∧
      ¬ QFEntailment.ValidOnEmpty
        (D := Data) (Γ := oneSchema) ⟨[], rNonemptyOne⟩ :=
  ⟨original_request_valid, cited_set_validOnNonempty,
    cited_set_not_validOnEmpty⟩

end FrameworkIIDictionarySoundness
end Tests
end Synthesis
end Whiel
