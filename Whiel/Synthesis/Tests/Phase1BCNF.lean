-- Author: Jesse Comer
import Whiel.Synthesis.DisjunctiveClause.CNF
import Whiel.Synthesis.DisjunctiveClause.Reference

/-
  Focused checks for finite-CNF conversion and the canonical
  reference-parameter schedule.
-/

namespace Whiel

namespace Synthesis

namespace Tests

namespace Phase1BCNFTests

open DisjunctiveClause

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

------------------------------------------------------------
-- Basic Conversion Shapes
------------------------------------------------------------

example :
    CNF.clauses
        (QFAssertExpr.«true» : QFAssertExpr D Γ) =
      [] := by
  rfl

example :
    CNF.clauses
        (QFAssertExpr.«false» : QFAssertExpr D Γ) =
      [[]] := by
  rfl

example
    {n : Nat}
    (left right : RAExpr D Γ n) :
    CNF.clauses (QFAssertExpr.eq left right) =
      [[CNF.equalityLiteral .positive left right]] := by
  simp [CNF.clauses, CNF.ofFormula]

example
    {n : Nat}
    (left right : RAExpr D Γ n) :
    CNF.clauses
        (QFAssertExpr.not
          (QFAssertExpr.eq left right)) =
      [[CNF.equalityLiteral .negative left right]] := by
  simp [CNF.clauses, CNF.ofFormula,
    CNF.Polarity.flip]

------------------------------------------------------------
-- Semantic Conversion Contract
------------------------------------------------------------

example
    (left middle right : QFAssertExpr D Γ)
    (I : Instance D Γ) :
    (CNF.formula
      (CNF.clauses
        (QFAssertExpr.or
          (QFAssertExpr.and left middle)
          (QFAssertExpr.not right)))).eval I ↔
      ((left.eval I ∧ middle.eval I) ∨
        ¬ right.eval I) := by
  exact
    (QFAssertExpr.equiv_iff_eval_iff _ _).mp
      (CNF.formula_equiv
        (QFAssertExpr.or
          (QFAssertExpr.and left middle)
          (QFAssertExpr.not right))) I

example
    (input : QFAssertExpr D Γ)
    {clause : DisjunctiveClause.LiteralList D Γ}
    (hMember : clause ∈ CNF.clauses input) :
    clause.IsNormalized :=
  CNF.clauses_normalized input hMember

example
    (input : QFAssertExpr D Γ)
    {clause : DisjunctiveClause.LiteralList D Γ}
    (hMember : clause ∈ CNF.clauses input) :
    clause.formula ∈
      (DisjunctiveClause.clauseClass :
        ClauseClass D Γ) :=
  CNF.formula_mem_clauseClass input hMember

example
    (input : QFAssertExpr D Γ)
    {clause : DisjunctiveClause.LiteralList D Γ}
    (hMember : clause ∈ CNF.clauses input) :
    CNF.LiteralList.UsesOnly clause input :=
  CNF.clauses_useOnlyInput input hMember

example
    (input : QFAssertExpr D Γ)
    {clause : Clause D Γ}
    (hMember : clause ∈ CNF.candidate input) :
    clause.symbols ⊆ input.symbols ∧
      clause.constants ⊆ input.constants :=
  CNF.candidate_member_support input hMember

example
    (input : QFAssertExpr D Γ) :
    Assertion.equiv
      (CNF.candidate input).denote input.eval :=
  CNF.candidate_denote_equiv input

------------------------------------------------------------
-- Canonical Reference Parameters
------------------------------------------------------------

example
    (stage : Nat) :
    (referenceParameters (stage + 1)).Dominates
      (referenceParameters stage) :=
  referenceParameters_mono (Nat.le_succ stage)

example :
    ParameterSchedule.IsCofinal referenceParameters :=
  referenceParameters_isCofinal

end Phase1BCNFTests

end Tests

end Synthesis

end Whiel
