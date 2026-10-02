-- Author: Jesse Comer
import Whiel.Synthesis.FrameworkII.FixedAmbient.Obligations

/-
  Protected EDB-only precondition rows over the fixed
  ambient schema.

  A top-level conjunct of the preprocessed loop precondition
  that mentions no relation assigned by the loop body is a
  level-zero Framework-II clause whose two verification
  conditions are closed without a solver: the precondition
  itself carries initialization, and the body cannot change
  the conjunct's relations, so it is maintained.

  Key definitions include:
    * `EdbPrecondition.extract`
    * `EdbPrecondition.leveledClause`

  Correctness is proven by:
    * `EdbPrecondition.initVC_valid`
    * `EdbPrecondition.maintenanceVC_valid`

  Intervening definitions and lemmas are construction,
  helper, or proof support.
-/

------------------------------------------------------------
-- Top-Level Conjunct Extraction
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FixedAmbient
namespace EdbPrecondition

open Concrete

variable {D : Type} [Domain D]
variable {Gamma : UnnamedSchema WhielNames}

/- Flatten only top-level conjunctions, preserving order. -/
def topConjuncts :
    QFAssertExpr D Gamma -> List (QFAssertExpr D Gamma)
| .«true» => []
| .and left right => topConjuncts left ++ topConjuncts right
| formula => [formula]

/- Top-level conjunction extraction is complete. -/
theorem eval_iff_all_topConjuncts
    (formula : QFAssertExpr D Gamma)
    (I : Instance D Gamma) :
    formula.eval I ↔
      ∀ conjunct ∈ topConjuncts formula,
        conjunct.eval I := by
  induction formula with
  | «true» => simp [topConjuncts]
  | «false» => simp [topConjuncts]
  | eq => simp [topConjuncts]
  | subset => simp [topConjuncts]
  | and left right ihLeft ihRight =>
      constructor
      · intro hBoth conjunct hMember
        rcases List.mem_append.mp hMember with
          hLeft | hRight
        · exact ihLeft.mp hBoth.1 conjunct hLeft
        · exact ihRight.mp hBoth.2 conjunct hRight
      · intro hAll
        exact ⟨
          ihLeft.mpr (fun conjunct hMember =>
            hAll conjunct (List.mem_append_left _ hMember)),
          ihRight.mpr (fun conjunct hMember =>
            hAll conjunct
              (List.mem_append_right _ hMember))⟩
  | or => simp [topConjuncts]
  | not => simp [topConjuncts]

/- One extracted conjunct follows from the precondition. -/
theorem eval_of_mem_topConjuncts
    (formula conjunct : QFAssertExpr D Gamma)
    (hMember : conjunct ∈ topConjuncts formula)
    (I : Instance D Gamma)
    (hFormula : formula.eval I) :
    conjunct.eval I :=
  (eval_iff_all_topConjuncts formula I).mp
    hFormula conjunct hMember

end EdbPrecondition
end FixedAmbient
end FrameworkII
end Synthesis
end Whiel

------------------------------------------------------------
-- EDB-Only Rows
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FixedAmbient
namespace EdbPrecondition

open Concrete

variable {D : Type} [Domain D]
variable {Gamma : UnnamedSchema WhielNames}

/- EDB-only formulas mention no assigned row. -/
def IsEdbOnly
    (body : Cmd D Gamma)
    (formula : QFAssertExpr D Gamma) : Prop :=
  formula.symbols ∩ body.assignedSymbols = ∅

instance
    (body : Cmd D Gamma)
    (formula : QFAssertExpr D Gamma) :
    Decidable (IsEdbOnly body formula) := by
  unfold IsEdbOnly
  infer_instance

/- Stable source ordinal attached before EDB filtering. -/
structure Row where
  ordinal : Nat
  formula : QFAssertExpr D Gamma

private def withOrdinalsFrom :
    Nat -> List (QFAssertExpr D Gamma) ->
      List (Row (D := D) (Gamma := Gamma))
| _, [] => []
| ordinal, formula :: formulas =>
    { ordinal, formula } ::
      withOrdinalsFrom (ordinal + 1) formulas

private theorem formula_mem_of_mem_withOrdinalsFrom
    (ordinal : Nat)
    (formulas : List (QFAssertExpr D Gamma))
    (row : Row (D := D) (Gamma := Gamma))
    (hRow : row ∈ withOrdinalsFrom ordinal formulas) :
    row.formula ∈ formulas := by
  induction formulas generalizing ordinal row with
  | nil => simp [withOrdinalsFrom] at hRow
  | cons formula formulas ih =>
      simp only [withOrdinalsFrom, List.mem_cons] at hRow
      rcases hRow with hHead | hTail
      · subst row
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem formula
          (ih (ordinal + 1) row hTail)

/- Exact protected basis in source conjunction order. -/
def extract
    (body : Cmd D Gamma)
    (pre : QFAssertExpr D Gamma) :
    List (Row (D := D) (Gamma := Gamma)) :=
  (withOrdinalsFrom 0 (topConjuncts pre)).filter fun row =>
    decide (IsEdbOnly body row.formula)

/- An extracted row is one original top-level conjunct. -/
theorem row_formula_mem
    (body : Cmd D Gamma)
    (pre : QFAssertExpr D Gamma)
    (row : Row (D := D) (Gamma := Gamma))
    (hRow : row ∈ extract body pre) :
    row.formula ∈ topConjuncts pre := by
  unfold extract at hRow
  have hWith := (List.mem_filter.mp hRow).1
  exact formula_mem_of_mem_withOrdinalsFrom
    0 (topConjuncts pre) row hWith

/- Every extracted row is checked EDB-only. -/
theorem row_isEdbOnly
    (body : Cmd D Gamma)
    (pre : QFAssertExpr D Gamma)
    (row : Row (D := D) (Gamma := Gamma))
    (hRow : row ∈ extract body pre) :
    IsEdbOnly body row.formula := by
  exact of_decide_eq_true (List.mem_filter.mp hRow).2

/- EDB-only truth survives one execution of the body. -/
theorem eval_preserved
    {body : Cmd D Gamma}
    (formula : QFAssertExpr D Gamma)
    (hEdb : IsEdbOnly body formula)
    {I J : Instance D Gamma}
    (hStep : body.BigStep I J)
    (hFormula : formula.eval I) :
    formula.eval J := by
  apply (Guard.eval_reduct_property formula
    (I := I) (J := J) ?_).mp hFormula
  intro X hSymbol
  symm
  apply hStep.no_update_preservation X
  intro hAssigned
  have hBoth : X.1 ∈
      formula.symbols ∩ body.assignedSymbols :=
    Finset.mem_inter.mpr ⟨hSymbol, hAssigned⟩
  rw [hEdb] at hBoth
  exact Finset.notMem_empty X.1 hBoth

end EdbPrecondition
end FixedAmbient
end FrameworkII
end Synthesis
end Whiel

------------------------------------------------------------
-- Closed Verification Routes
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FixedAmbient
namespace EdbPrecondition

open Concrete

variable {D : Type} [Domain D]
variable {Gamma : UnnamedSchema WhielNames}

/- Canonical level-zero clause of one extracted row. -/
def leveledClause
    (row : Row (D := D) (Gamma := Gamma)) :
    LeveledClause D Gamma :=
  ⟨row.formula, 0⟩

/- The precondition itself closes initialization. -/
theorem initVC_valid
    {body : Cmd D Gamma}
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard pre : QFAssertExpr D Gamma)
    (row : Row (D := D) (Gamma := Gamma))
    (hRow : row ∈ extract body pre) :
    (family.initVC task guard pre
      (leveledClause row)).Valid := by
  intro I hAxioms
  have hPre : pre.eval I :=
    hAxioms pre (by simp [LeveledFamily.initVC])
  exact eval_of_mem_topConjuncts pre row.formula
    (row_formula_mem body pre row hRow) I hPre

/- The unchanged EDB rows close maintenance. -/
theorem maintenanceVC_valid
    {body : Cmd D Gamma}
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard : Guard D Gamma)
    (hBody : body.LoopFree)
    (row : Row (D := D) (Gamma := Gamma))
    (pre : QFAssertExpr D Gamma)
    (hRow : row ∈ extract body pre)
    (hInstalled : leveledClause row ∈ family.clauses) :
    (family.maintenanceVC task guard hBody
      (leveledClause row)).Valid := by
  intro I hAxioms
  apply (QFAssertExpr.wpLoopFree_eval_iff body hBody
    (leveledClause row).formula I).mpr
  intro J hStep
  apply eval_preserved row.formula
    (row_isEdbOnly body pre row hRow) hStep
  apply hAxioms (leveledClause row).formula
  simp only [LeveledFamily.maintenanceVC,
    List.mem_append]
  apply Or.inl
  apply List.mem_map.mpr
  refine ⟨leveledClause row, ?_, rfl⟩
  apply List.mem_filter.mpr
  refine ⟨hInstalled, ?_⟩
  rfl

end EdbPrecondition
end FixedAmbient
end FrameworkII
end Synthesis
end Whiel
