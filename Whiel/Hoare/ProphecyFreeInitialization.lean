-- Author: Jesse Comer
import Whiel.Hoare.FixedAmbientProphecy

/-
  Initialization finality for prophecy-free clauses.

  A clause whose truth depends only on the program frame is
  decided by its initialization condition on every halting
  input: when every level below the candidate level
  discharges its initialization and maintenance obligations
  and the candidate initialization is valid, the clause
  holds at every input satisfying the precondition from
  which the loop halts. A prophecy-free clause refuted at
  level zero is therefore admissible at a higher level only
  through inputs from which the loop diverges.

  Key definitions and theorems:
  `ProphecyFree`, `levelsBelow`,
  `prophecyBelow_levelsBelow_iff`,
  `initValid_of_initZeroValid`,
  `prophecyFree_holds_on_halting_of_vcs`,
  `prophecyFree_holds_on_halting_of_initValid`.
-/

------------------------------------------------------------
-- Prophecy-Free Assertions
------------------------------------------------------------

namespace Whiel

namespace Hoare

namespace FixedAmbientProphecy

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Gamma : UnnamedSchema A}

/-
  An assertion is prophecy-free when it reads only the
  program frame: agreement on the program symbols already
  decides it.
-/
def ProphecyFree
    (programSymbols : Finset A)
    (formula : Assertion D Gamma) : Prop :=
  forall left right : Instance D Gamma,
    Instance.agreeOn programSymbols left right ->
      (formula left ↔ formula right)

/- A guard over program symbols is prophecy-free. -/
theorem prophecyFree_of_symbols_subset
    {programSymbols : Finset A}
    (formula : Guard D Gamma)
    (hSymbols : formula.symbols ⊆ programSymbols) :
    ProphecyFree (D := D) (Gamma := Gamma)
      programSymbols formula.eval := by
  intro left right hAgree
  exact Guard.eval_reduct_property formula
    (Instance.agreeOn_of_subset hSymbols hAgree)

end FixedAmbientProphecy

end Hoare

end Whiel

------------------------------------------------------------
-- Truncated Level Families
------------------------------------------------------------

namespace Whiel

namespace Hoare

namespace FixedAmbientProphecy

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Gamma : UnnamedSchema A}
variable {programSymbols assigned : Finset A}

/- Initialization survives truncation above its level. -/
theorem initObligation_levelsBelow
    (prophecy : Collapse (D := D) (Gamma := Gamma)
      programSymbols assigned)
    (guard : Guard D Gamma)
    (levels : Nat -> List (Assertion D Gamma))
    (pre : Assertion D Gamma)
    {bound level : Nat}
    (hLevel : level ≤ bound)
    (formula : Assertion D Gamma)
    (hInit :
      InitObligation prophecy guard levels pre
        level formula) :
    InitObligation prophecy guard
      (levelsBelow levels bound) pre level formula := by
  intro state hPre hBelow
  exact hInit state hPre
    ((prophecyBelow_levelsBelow_iff prophecy guard levels
      hLevel state).mp hBelow)

/-
  The reduct lemma: a level-zero initialization is already
  an initialization at every level, because the terminal
  premises only grow.
-/
theorem initValid_of_initZeroValid
    (prophecy : Collapse (D := D) (Gamma := Gamma)
      programSymbols assigned)
    (guard : Guard D Gamma)
    (levels : Nat -> List (Assertion D Gamma))
    (pre : Assertion D Gamma)
    (level : Nat)
    (formula : Assertion D Gamma)
    (hZero :
      InitObligation prophecy guard levels pre 0 formula) :
    InitObligation prophecy guard levels pre
      level formula := by
  intro state hPre _hBelow
  exact hZero state hPre
    (prophecyBelow_zero prophecy guard levels state)

end FixedAmbientProphecy

end Hoare

end Whiel

------------------------------------------------------------
-- Initialization Finality on Halting Inputs
------------------------------------------------------------

namespace Whiel

namespace Hoare

namespace FixedAmbientProphecy

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Gamma : UnnamedSchema A}

/-
  Initialization finality. If every level of the family
  discharges its initialization and maintenance
  obligations, one prophecy-free clause is initialized at
  one candidate level, and the precondition is
  prophecy-free, then the clause holds at every input from
  which the raw loop halts.
-/
theorem prophecyFree_holds_on_halting_of_vcs
    (programSymbols : Finset A)
    {guard : Guard D Gamma}
    {body : Cmd D Gamma}
    (prophecy : Collapse (D := D) (Gamma := Gamma)
      programSymbols body.assignedSymbols)
    (levels : Nat -> List (Assertion D Gamma))
    (pre clause : Assertion D Gamma)
    (level : Nat)
    (hGuardSymbols : guard.symbols ⊆ programSymbols)
    (hBodySymbols : body.symbols ⊆ programSymbols)
    (hPreFree : ProphecyFree programSymbols pre)
    (hClauseFree : ProphecyFree programSymbols clause)
    (hInit : forall lower,
      ∀ formula ∈ levels lower,
        InitObligation prophecy guard levels pre
          lower formula)
    (hStep : forall lower,
      ∀ formula ∈ levels lower,
        StepObligation guard body prophecy levels
          lower formula)
    (hClauseInit :
      InitObligation prophecy guard levels pre
        level clause)
    {initial final : Instance D Gamma}
    (hPre : pre initial)
    (hRun :
      Cmd.BigStep (.while guard body) initial final) :
    clause initial := by
  let exitState : Instance D Gamma :=
    prophecy.exitLift final
  let expanded : Instance D Gamma :=
    overlay programSymbols initial exitState
  have hAgreeInitial :
      Instance.agreeOn programSymbols initial expanded :=
    agreeOn_overlay programSymbols initial exitState
  have hPreExpanded : pre expanded :=
    (hPreFree initial expanded hAgreeInitial).mp hPre
  have hLoopSymbols :
      (Cmd.while guard body).symbols ⊆
        programSymbols := by
    intro name hName
    rcases Finset.mem_union.mp hName with
      hGuard | hBody
    · exact hGuardSymbols hGuard
    · exact hBodySymbols hBody
  rcases hRun.frame hLoopSymbols hAgreeInitial with
    ⟨expandedFinal, hExpandedRun, hAgreeFinal⟩
  have hNotAssignedLoop :
      forall relation : Gamma.syms,
        relation.1 ∉ body.assignedSymbols ->
          relation.1 ∉
            (Cmd.while guard body).assignedSymbols := by
    intro _relation hNotAssigned
    exact hNotAssigned
  have hFinalEq : expandedFinal = exitState := by
    apply Instance.ext
    intro relation
    by_cases hProgram : relation.1 ∈ programSymbols
    · exact (hAgreeFinal relation hProgram).symm.trans
        (prophecy.exitLift_agreeOn final relation
          hProgram)
    · have hNotAssigned :
          relation.1 ∉
            (Cmd.while guard body).assignedSymbols := by
        intro hAssigned
        have hSymbol : relation.1 ∈
            (Cmd.while guard body).symbols :=
          Cmd.assignedSymbols_subset_symbols
            (.while guard body) hAssigned
        exact hProgram (hLoopSymbols hSymbol)
      calc
        expandedFinal relation = expanded relation :=
          hExpandedRun.no_update_preservation relation
            hNotAssigned
        _ = exitState relation :=
          overlay_eq_right_of_not_mem
            programSymbols initial exitState relation
              hProgram
  subst expandedFinal
  have hLadder :=
    ladderInv_inductive prophecy levels hInit hStep
  have hEnd :=
    hLadder expanded exitState hPreExpanded hExpandedRun
  have hFixed :
      prophecy.collapse exitState = exitState :=
    prophecy.collapse_exitLift final
  have hAll : holdsAt levels exitState :=
    holdsAt_of_ladderInv prophecy guard levels
      hFixed hEnd.2 hEnd.1
  have hCollapseExpanded :
      prophecy.collapse expanded = exitState := by
    have hAgree : forall relation : Gamma.syms,
        relation.1 ∉ body.assignedSymbols ->
          expanded relation = exitState relation := by
      intro relation hNotAssigned
      by_cases hProgram : relation.1 ∈ programSymbols
      · calc
          expanded relation = initial relation :=
            (hAgreeInitial relation hProgram).symm
          _ = final relation :=
            (hRun.no_update_preservation relation
              (hNotAssignedLoop relation
                hNotAssigned)).symm
          _ = exitState relation :=
            prophecy.exitLift_agreeOn final relation
              hProgram
      · exact overlay_eq_right_of_not_mem
          programSymbols initial exitState relation
            hProgram
    calc
      prophecy.collapse expanded =
          prophecy.collapse exitState :=
        prophecy.collapse_congr expanded exitState
          hAgree
      _ = exitState := hFixed
  have hBelowExpanded :
      prophecyBelow prophecy guard levels level
        expanded := by
    refine ⟨?_, ?_⟩
    · intro _hPositive
      rw [hCollapseExpanded]
      exact hEnd.2
    · intro lower _hLower formula hFormula
      rw [hCollapseExpanded]
      exact hAll lower formula hFormula
  have hClauseExpanded : clause expanded :=
    hClauseInit expanded hPreExpanded hBelowExpanded
  exact (hClauseFree initial expanded hAgreeInitial).mpr
    hClauseExpanded

/-
  The same statement with the obligations required only
  below the candidate level. The maintenance hypotheses are
  stated over the truncated family, which is exactly what
  the level-prefix maintenance conditions of the levels
  below the candidate level establish.
-/
theorem prophecyFree_holds_on_halting_of_initValid
    (programSymbols : Finset A)
    {guard : Guard D Gamma}
    {body : Cmd D Gamma}
    (prophecy : Collapse (D := D) (Gamma := Gamma)
      programSymbols body.assignedSymbols)
    (levels : Nat -> List (Assertion D Gamma))
    (pre clause : Assertion D Gamma)
    (level : Nat)
    (hGuardSymbols : guard.symbols ⊆ programSymbols)
    (hBodySymbols : body.symbols ⊆ programSymbols)
    (hPreFree : ProphecyFree programSymbols pre)
    (hClauseFree : ProphecyFree programSymbols clause)
    (hInit : forall lower, lower < level ->
      ∀ formula ∈ levels lower,
        InitObligation prophecy guard levels pre
          lower formula)
    (hStep : forall lower, lower < level ->
      ∀ formula ∈ levels lower,
        StepObligation guard body prophecy
          (levelsBelow levels level) lower formula)
    (hClauseInit :
      InitObligation prophecy guard levels pre
        level clause)
    {initial final : Instance D Gamma}
    (hPre : pre initial)
    (hRun :
      Cmd.BigStep (.while guard body) initial final) :
    clause initial := by
  refine prophecyFree_holds_on_halting_of_vcs
    programSymbols prophecy (levelsBelow levels level)
    pre clause level hGuardSymbols hBodySymbols
    hPreFree hClauseFree ?_ ?_ ?_ hPre hRun
  · intro lower formula hFormula
    by_cases hLower : lower < level
    · rw [levelsBelow_of_lt levels hLower] at hFormula
      exact initObligation_levelsBelow prophecy guard
        levels pre (Nat.le_of_lt hLower) formula
        (hInit lower hLower formula hFormula)
    · rw [levelsBelow_of_le levels
        (Nat.le_of_not_lt hLower)] at hFormula
      exact absurd hFormula (List.not_mem_nil)
  · intro lower formula hFormula
    by_cases hLower : lower < level
    · rw [levelsBelow_of_lt levels hLower] at hFormula
      exact hStep lower hLower formula hFormula
    · rw [levelsBelow_of_le levels
        (Nat.le_of_not_lt hLower)] at hFormula
      exact absurd hFormula (List.not_mem_nil)
  · exact initObligation_levelsBelow prophecy guard
      levels pre (Nat.le_refl level) clause hClauseInit

end FixedAmbientProphecy

end Hoare

end Whiel
