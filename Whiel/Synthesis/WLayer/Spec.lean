-- Author: Jesse Comer
import Whiel.Synthesis.Spec

/-
  Logical specification of exact weakest-precondition
  layers.

  A layer is a QF formula indexed by a natural number. The
  index is also its compact class-specific representation.

  Main declarations:
    * `formula`, `clauseClass`, `Slice`, and `upTo`
    * `candidateUpTo`
    * `formula_succ_step`
    * `loop_counterExample_of_not_formula`
    * `counterExample_input_of_not_formula`
    * `term_iff_entails_zero`
    * `isSufficientFor_of_isInductiveFor_of_mem_zero`
    * `candidateUpTo_isSufficientFor`
    * `entails_formula_of_isSufficientFor`
-/

------------------------------------------------------------
-- Layer Formulas and Finite Slices
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace WLayer

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}
variable {inputPre inputPost : AssertExpr D Γ}
variable {inputCmd : Cmd D Γ}

/- The normalized loop postcondition as a QF formula. -/
def loopPostQF
    (P : Hoare.Preproc inputPre inputCmd inputPost) :
    Clause D P.outSchema :=
  P.loopPost.toQFOfNoBound P.loopPost_noBound

/- The QF loop-post view has the trusted meaning. -/
@[simp] theorem loopPostQF_eval_iff
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (I : Instance D P.outSchema) :
    (loopPostQF P).eval I ↔
      P.loopPost.eval I :=
  AssertExpr.toQFOfNoBound_eval_iff
    P.loopPost P.loopPost_noBound I

/- Exact finite weakest-precondition layers. -/
def formula
    (P : Hoare.Preproc inputPre inputCmd inputPost) :
    Nat → Clause D P.outSchema
| 0 =>
    QFAssertExpr.or P.loopGuard
      (loopPostQF P)
| n + 1 =>
    QFAssertExpr.implies P.loopGuard
      (QFAssertExpr.wpLoopFree P.loopBody
        P.loopBody_loopFree (formula P n))

@[simp] theorem formula_zero
    (P : Hoare.Preproc inputPre inputCmd inputPost) :
    formula P 0 =
      QFAssertExpr.or P.loopGuard
        (loopPostQF P) :=
  rfl

@[simp] theorem formula_succ
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (n : Nat) :
    formula P (n + 1) =
      QFAssertExpr.implies P.loopGuard
        (QFAssertExpr.wpLoopFree P.loopBody
          P.loopBody_loopFree (formula P n)) :=
  rfl

@[simp] theorem formula_zero_eval_iff
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (I : Instance D P.outSchema) :
    (formula P 0).eval I ↔
      P.loopGuard.eval I ∨
        P.loopPost.eval I := by
  simp

@[simp] theorem formula_succ_eval_iff
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (n : Nat)
    (I : Instance D P.outSchema) :
    (formula P (n + 1)).eval I ↔
      ¬P.loopGuard.eval I ∨
        Hoare.wp P.loopBody
          (formula P n).eval I := by
  rw [formula_succ, Guard.eval_implies_iff]
  exact
    or_congr Iff.rfl
      (QFAssertExpr.wpLoopFree_eval_iff
        P.loopBody P.loopBody_loopFree
        (formula P n) I)

/-
  Failure of W(n) is an exact finite loop
  counterexample from the same loop-head instance.
-/
theorem loop_counterExample_of_not_formula
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (n : Nat)
    (I : Instance D P.outSchema)
    (hLoopPre : P.loopPre.eval I)
    (hNotFormula : ¬(formula P n).eval I) :
    ∃ J, Hoare.counterExample
      P.loopPre P.loopCmd P.loopPost I J := by
  have hRun :
      ∀ (m : Nat) (K : Instance D P.outSchema),
        ¬(formula P m).eval K →
          ∃ J, Cmd.BigStep P.loopCmd K J ∧
            ¬P.loopPost.eval J := by
    intro m
    induction m with
    | zero =>
        intro K hNotZero
        have hNotGuard : ¬P.loopGuard.eval K := by
          intro hGuard
          apply hNotZero
          exact (formula_zero_eval_iff P K).2 (Or.inl hGuard)
        have hNotPost : ¬P.loopPost.eval K := by
          intro hPost
          apply hNotZero
          exact (formula_zero_eval_iff P K).2 (Or.inr hPost)
        exact
          ⟨K, Cmd.BigStep.while_false hNotGuard, hNotPost⟩
    | succ m ih =>
        intro K hNotSuccessor
        have hGuard : P.loopGuard.eval K := by
          by_contra hNotGuard
          apply hNotSuccessor
          exact
            (formula_succ_eval_iff P m K).2
              (Or.inl hNotGuard)
        have hNotWP :
            ¬Hoare.wp P.loopBody (formula P m).eval K := by
          intro hWP
          apply hNotSuccessor
          exact
            (formula_succ_eval_iff P m K).2
              (Or.inr hWP)
        rcases
            Cmd.BigStep.exists_of_loopFree
              P.loopBody P.loopBody_loopFree K with
          ⟨L, hBodyStep⟩
        have hNotPredecessor : ¬(formula P m).eval L := by
          intro hPredecessor
          apply hNotWP
          intro L' hOtherBodyStep
          have hEq :=
            Cmd.BigStep.deterministic
              hBodyStep hOtherBodyStep
          rw [← hEq]
          exact hPredecessor
        rcases ih L hNotPredecessor with
          ⟨J, hLoopStep, hNotPost⟩
        exact
          ⟨J,
            Cmd.BigStep.while_true
              hGuard hBodyStep hLoopStep,
            hNotPost⟩
  rcases hRun n I hNotFormula with
    ⟨J, hLoopStep, hNotPost⟩
  exact ⟨J, hLoopPre, hLoopStep, hNotPost⟩

/-
  A loop-head model that initializes and falsifies W(n)
  reconstructs a source counterexample, starting at that
  model's projection to the input schema. The projection is
  the identity exactly when the transformation drew no flag.
-/
theorem counterExample_input_of_not_formula
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (n : Nat)
    (I : Instance D P.outSchema)
    (hLoopPre : P.loopPre.eval I)
    (hNotFormula : ¬(formula P n).eval I) :
    ∃ J,
      Hoare.counterExample inputPre inputCmd inputPost
        (Preprocess.project P.outExtends I) J := by
  rcases
      loop_counterExample_of_not_formula
        P n I hLoopPre hNotFormula with
    ⟨J, hLoopCounterExample⟩
  exact
    P.counterExample_input_of_loop_counterExample I J
      hLoopCounterExample

/- All exact-WP layer formulas for one problem. -/
def clauseClass
    (P : Hoare.Preproc inputPre inputCmd inputPost) :
    ClauseClass D P.outSchema :=
  Set.range (formula P)

/- A finite slice of the W-layer class for one problem. -/
abbrev Slice
    (P : Hoare.Preproc inputPre inputCmd inputPost) :=
  (clauseClass P).Slice

@[simp] theorem formula_mem_clauseClass
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (n : Nat) :
    formula P n ∈ clauseClass P :=
  ⟨n, rfl⟩

@[simp] theorem mem_clauseClass_iff
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (clause : Clause D P.outSchema) :
    clause ∈ clauseClass P ↔
      ∃ n, formula P n = clause :=
  Iff.rfl

/- The inclusive layer-index parameter. -/
structure Parameters where
  maxWIndex : Nat
deriving DecidableEq, Repr

/- The inclusive finite layer slice. -/
def upTo
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (maxWIndex : Nat) :
    Slice P where
  clauses :=
    formula P '' {n | n ≤ maxWIndex}
  finite :=
    (Set.finite_le_nat maxWIndex).image
      (formula P)
  subset_class := by
    rintro clause ⟨n, _, rfl⟩
    exact formula_mem_clauseClass P n

/- The inclusive W prefix as a candidate. -/
def candidateUpTo
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (maxWIndex : Nat) :
    Candidate D P.outSchema :=
  (Finset.range (maxWIndex + 1)).image (formula P)

@[simp] theorem mem_upTo_iff
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (maxWIndex : Nat)
    (clause : Clause D P.outSchema) :
    clause ∈ (upTo P maxWIndex).clauses ↔
      ∃ n ≤ maxWIndex,
        formula P n = clause := by
  simp [upTo]

@[simp] theorem mem_candidateUpTo_iff
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (maxWIndex : Nat)
    (clause : Clause D P.outSchema) :
    clause ∈ candidateUpTo P maxWIndex ↔
      ∃ n ≤ maxWIndex,
        formula P n = clause := by
  simp [candidateUpTo, Nat.lt_succ_iff]

theorem upTo_subset_clauseClass
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (maxWIndex : Nat) :
    ∀ clause ∈ (upTo P maxWIndex).clauses,
      clause ∈ clauseClass P :=
  (upTo P maxWIndex).subset_class

theorem formula_mem_upTo
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    {n maxWIndex : Nat}
    (hBound : n ≤ maxWIndex) :
    formula P n ∈
      (upTo P maxWIndex).clauses :=
  (mem_upTo_iff P maxWIndex
    (formula P n)).mpr
      ⟨n, hBound, rfl⟩

theorem mem_clauseClass_iff_exists_mem_upTo
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (clause : Clause D P.outSchema) :
    clause ∈ clauseClass P ↔
      ∃ maxWIndex,
        clause ∈
          (upTo P maxWIndex).clauses := by
  constructor
  · rintro ⟨n, rfl⟩
    exact
      ⟨n, formula_mem_upTo P
        (Nat.le_refl n)⟩
  · rintro ⟨maxWIndex, hMember⟩
    rcases
        (mem_upTo_iff
          P maxWIndex clause).mp hMember with
      ⟨n, _, rfl⟩
    exact formula_mem_clauseClass P n

end WLayer

end Synthesis

end Whiel

------------------------------------------------------------
-- Layer-Specific Semantic Laws
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace WLayer

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}
variable {inputPre inputPost : AssertExpr D Γ}
variable {inputCmd : Cmd D Γ}

/- A successor layer discharges its predecessor's step. -/
theorem formula_succ_step
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (n : Nat) :
    Assertion.Step P
      (formula P (n + 1)).eval
      (formula P n).eval := by
  intro I hGuarded
  rcases hGuarded with
    ⟨hSuccessor, hGuard⟩
  rcases hSuccessor with hNotGuard | hWp
  · exact False.elim (hNotGuard hGuard)
  · exact
      (QFAssertExpr.wpLoopFree_eval_iff
        P.loopBody P.loopBody_loopFree
        (formula P n) I).mp hWp

/- Term is exactly entailment of the zero layer. -/
theorem term_iff_entails_zero
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (assertion : Assertion D P.outSchema) :
    assertion.Term P ↔
      assertion.entails (formula P 0).eval := by
  constructor
  · intro hTerm I hAssertion
    by_cases hGuard : P.loopGuard.eval I
    · exact Or.inl hGuard
    · apply Or.inr
      exact
        (loopPostQF_eval_iff P I).mpr
          (hTerm I ⟨hAssertion, hGuard⟩)
  · intro hEntails I hExit
    rcases hExit with
      ⟨hAssertion, hNotGuard⟩
    rcases hEntails I hAssertion with
      hGuard | hPost
    · exact False.elim (hNotGuard hGuard)
    · exact
        (loopPostQF_eval_iff P I).mp hPost

/- An inductive candidate containing W(0) is sufficient. -/
theorem isSufficientFor_of_isInductiveFor_of_mem_zero
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (clauses : Candidate D P.outSchema)
    (hInductive : clauses.IsInductiveFor P)
    (hZero : formula P 0 ∈ clauses) :
    clauses.IsSufficientFor P := by
  refine ⟨hInductive, ?_⟩
  exact
    (term_iff_entails_zero P clauses.denote).2
      (Candidate.denote_entails_of_mem hZero)

/-
  Initialization plus top maintenance suffices for a W
  prefix.
-/
theorem candidateUpTo_isSufficientFor
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (maxWIndex : Nat)
    (hInit :
      ∀ n ≤ maxWIndex,
        Assertion.Init P (formula P n).eval)
    (hTopMaint :
      (candidateUpTo P maxWIndex).denote.Step P
        (formula P maxWIndex).eval) :
    (candidateUpTo P maxWIndex).IsSufficientFor P := by
  apply
    isSufficientFor_of_isInductiveFor_of_mem_zero
      P _ ?_ ?_
  · constructor
    · apply
        (Candidate.init_denote_iff P
          (candidateUpTo P maxWIndex)).2
      intro clause hClause
      rcases
          (mem_candidateUpTo_iff
            P maxWIndex clause).1 hClause with
        ⟨n, hBound, rfl⟩
      exact hInit n hBound
    · apply
        (Candidate.maint_denote_iff P
          (candidateUpTo P maxWIndex)).2
      intro clause hClause
      rcases
          (mem_candidateUpTo_iff
            P maxWIndex clause).1 hClause with
        ⟨n, hBound, rfl⟩
      rcases Nat.lt_or_eq_of_le hBound with hLt | rfl
      · intro I hGuarded
        apply formula_succ_step P n I
        exact
          ⟨hGuarded.1 _
              ((mem_candidateUpTo_iff
                P maxWIndex
                (formula P (n + 1))).2
                  ⟨n + 1,
                    Nat.succ_le_of_lt hLt,
                    rfl⟩),
            hGuarded.2⟩
      · exact hTopMaint
  · exact
      (mem_candidateUpTo_iff
        P maxWIndex (formula P 0)).2
          ⟨0, Nat.zero_le maxWIndex, rfl⟩

/- Every sufficient assertion entails every W layer. -/
theorem entails_formula_of_isSufficientFor
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (assertion : Assertion D P.outSchema)
    (hSufficient :
      assertion.IsSufficientFor P)
    (n : Nat) :
    assertion.entails (formula P n).eval := by
  induction n with
  | zero =>
      exact
        (term_iff_entails_zero
          P assertion).mp hSufficient.2
  | succ n ih =>
      intro I hAssertion
      by_cases hGuard : P.loopGuard.eval I
      · apply Or.inr
        have hWpAssertion :=
          hSufficient.1.2 I
            ⟨hAssertion, hGuard⟩
        have hWpLayer :=
          (Hoare.wp_mono P.loopBody ih)
            I hWpAssertion
        exact
          (QFAssertExpr.wpLoopFree_eval_iff
            P.loopBody P.loopBody_loopFree
            (formula P n) I).mpr hWpLayer
      · exact Or.inl hGuard

end WLayer

end Synthesis

end Whiel
