-- Author: Jesse Comer
import Whiel.Synthesis.DisjunctiveClause.Spec
import Whiel.Synthesis.Spec

/-
  Auditable semantic rules for literal-subset coverage.

  Runtime code may construct the corresponding metadata
  without transporting one proof object per edge. The edge
  orientation is always the stronger source clause to the
  weaker target clause.

  Main declarations:
    * `LiteralList.formula_entails_of_subset`
    * `LiteralList.initCoverage_of_subset`
    * `LiteralList.maintCoverage_of_subset`
-/

------------------------------------------------------------
-- Literal-Subset Entailment
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

namespace LiteralList

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}

/- A disjunction entails every disjunction that extends it. -/
theorem formula_entails_of_subset
    {source target : LiteralList D Γ}
    (hSubset : source ⊆ target) :
    QFAssertExpr.entails source.formula target.formula := by
  intro I hSource
  rw [formula_eval_iff] at hSource ⊢
  rcases hSource with
    ⟨literal, hLiteral, hEval⟩
  exact ⟨literal, hSubset hLiteral, hEval⟩

/- Literal-subset entailment transfers initialization. -/
theorem initCoverage_of_subset
    {inputPre inputPost : AssertExpr D Γ}
    {inputCmd : Cmd D Γ}
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    {source target : LiteralList D P.outSchema}
    (hSubset : source ⊆ target)
    (hInit : Whiel.Assertion.Init P source.formula.eval) :
    Whiel.Assertion.Init P target.formula.eval := by
  intro I hPre
  exact
    formula_entails_of_subset hSubset I
      (hInit I hPre)

/-
  Literal-subset entailment transfers a maintenance result
  under any fixed antecedent. This is stronger than the
  runtime MaintCoverage condition over Candidate extensions.
-/
theorem maintCoverage_of_subset
    {inputPre inputPost : AssertExpr D Γ}
    {inputCmd : Cmd D Γ}
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    {source target : LiteralList D P.outSchema}
    (hSubset : source ⊆ target)
    (antecedent : Assertion D P.outSchema)
    (hStep : Whiel.Assertion.Step P antecedent
      source.formula.eval) :
    Whiel.Assertion.Step P antecedent
      target.formula.eval := by
  intro I hGuarded J hBody
  exact
    formula_entails_of_subset hSubset J
      (hStep I hGuarded J hBody)

end LiteralList

end DisjunctiveClause

end Synthesis

end Whiel
