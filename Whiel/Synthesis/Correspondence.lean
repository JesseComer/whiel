-- Author: Jesse Comer
import Whiel.Synthesis.Queries

/-
  Correspondence between readable clause lists and the
  class-agnostic semantic specification.

  This file is the refinement boundary for later optimized
  representations. It proves both list materialization and
  every QF obligation adapter extensionally correct.
-/

------------------------------------------------------------
-- Clause Materialization Correctness
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace ClauseObligation

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}
variable {inputPre inputPost : AssertExpr D Γ}
variable {inputCmd : Cmd D Γ}

/- List materialization denotes its finite clause set. -/
@[simp] theorem materialize_eval_iff_denote
    (clauses : List (Clause D Γ))
    (I : Instance D Γ) :
    (materialize clauses).eval I ↔
      Candidate.denote clauses.toFinset I := by
  simp [materialize, Candidate.denote]

/- Materialization and denotation are equivalent. -/
theorem materialize_equiv_denote
    (clauses : List (Clause D Γ)) :
    Assertion.equiv (materialize clauses).eval
      (Candidate.denote clauses.toFinset) := by
  constructor
  · intro I hMaterialized
    exact
      (materialize_eval_iff_denote
        clauses I).mp hMaterialized
  · intro I hDenotation
    exact
      (materialize_eval_iff_denote
        clauses I).mpr hDenotation

/- Equal finite sets give equivalent materializations. -/
theorem materialize_equiv_of_toFinset_eq
    {left right : List (Clause D Γ)}
    (hSets : left.toFinset = right.toFinset) :
    QFAssertExpr.equiv
      (materialize left) (materialize right) := by
  constructor
  · intro I hLeft
    apply
      (materialize_eval_iff_denote right I).mpr
    rw [← hSets]
    exact
      (materialize_eval_iff_denote
        left I).mp hLeft
  · intro I hRight
    apply
      (materialize_eval_iff_denote left I).mpr
    rw [hSets]
    exact
      (materialize_eval_iff_denote
        right I).mp hRight

end ClauseObligation

end Synthesis

end Whiel

------------------------------------------------------------
-- Clause Query Correctness
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace ClauseObligation

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}
variable {inputPre inputPost : AssertExpr D Γ}
variable {inputCmd : Cmd D Γ}

/- Clause-init validity is semantic initialization. -/
theorem init_valid_iff
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (target : Clause D P.outSchema) :
    (init P target).Valid ↔
      Assertion.Init P target.eval := by
  simpa [init, Assertion.Init] using
    QFInvariantObligation.init_valid_iff
      P.loopPre P.loopPre_noBound target


/- Candidate-init validity is semantic initialization. -/
theorem initCandidate_valid_iff
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (candidate : List (Clause D P.outSchema)) :
    (initCandidate P candidate).Valid ↔
      Assertion.Init P
        (Candidate.denote candidate.toFinset) := by
  calc
    (initCandidate P candidate).Valid ↔
        Assertion.Init P
          (materialize candidate).eval := by
      simpa [initCandidate, Assertion.Init] using
        QFInvariantObligation.init_valid_iff
          P.loopPre P.loopPre_noBound
          (materialize candidate)
    _ ↔
        Assertion.Init P
          (Candidate.denote candidate.toFinset) :=
      Assertion.init_congr P
        (materialize_equiv_denote candidate)

/- Clause-step validity is semantic target maintenance. -/
theorem step_valid_iff
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (candidate : List (Clause D P.outSchema))
    (target : Clause D P.outSchema) :
    (step P candidate target).Valid ↔
      Assertion.Step P
        (Candidate.denote candidate.toFinset)
        target.eval := by
  calc
    (step P candidate target).Valid ↔
        Assertion.Step P
          (materialize candidate).eval
          target.eval := by
      simpa [step, Assertion.Step] using
        QFInvariantObligation.step_valid_iff
          (materialize candidate) target P.loopGuard
          P.loopBody P.loopBody_loopFree
    _ ↔
        Assertion.Step P
          (Candidate.denote candidate.toFinset)
          target.eval :=
      Assertion.step_congr P
        (materialize_equiv_denote candidate)
        ⟨fun _ hTarget => hTarget,
         fun _ hTarget => hTarget⟩

/- Candidate-maint validity is semantic maintenance. -/
theorem maintCandidate_valid_iff
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (candidate : List (Clause D P.outSchema)) :
    (maintCandidate P candidate).Valid ↔
      Assertion.Maint P
        (Candidate.denote candidate.toFinset) := by
  calc
    (maintCandidate P candidate).Valid ↔
        Assertion.Maint P
          (materialize candidate).eval := by
      simpa [maintCandidate, Assertion.Maint,
        Assertion.Step] using
        QFInvariantObligation.step_valid_iff
          (materialize candidate)
          (materialize candidate)
          P.loopGuard P.loopBody
          P.loopBody_loopFree
    _ ↔
        Assertion.Maint P
          (Candidate.denote candidate.toFinset) :=
      Assertion.maint_congr P
        (materialize_equiv_denote candidate)

/- Candidate-term validity is semantic termination. -/
theorem termCandidate_valid_iff
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (candidate : List (Clause D P.outSchema)) :
    (termCandidate P candidate).Valid ↔
      Assertion.Term P
        (Candidate.denote candidate.toFinset) := by
  calc
    (termCandidate P candidate).Valid ↔
        Assertion.Term P
          (materialize candidate).eval := by
      simpa [termCandidate, Assertion.Term] using
        QFInvariantObligation.term_valid_iff
          (materialize candidate)
          P.loopPost P.loopPost_noBound
          P.loopGuard
    _ ↔
        Assertion.Term P
          (Candidate.denote candidate.toFinset) :=
      Assertion.term_congr P
        (materialize_equiv_denote candidate)

end ClauseObligation

end Synthesis

end Whiel
