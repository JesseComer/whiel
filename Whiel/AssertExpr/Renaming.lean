-- Author: Jesse Comer
import Whiel.AssertExpr.Substitution

/-
  Relation-symbol renaming for Whiel assertions.

  Key definitions include:
    * `Whiel.QFAssertExpr.rename`

  Correctness is inherited from substitution by:
    * `Whiel.QFAssertExpr.rename_eval`
-/

------------------------------------------------------------
-- Quantifier-Free Assertion Renaming
------------------------------------------------------------

namespace Whiel

namespace QFAssertExpr

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Rename one same-arity relation symbol to another. -/
def rename
    (φ : QFAssertExpr D Γ)
    (X Y : Γ.syms)
    (hAr : Γ.arity X = Γ.arity Y) :
    QFAssertExpr D Γ :=
  φ.subst X (RAExpr.relAs X Y hAr)

/- Renaming is vacuous when the source symbol is absent. -/
theorem rename_vacuous
    (φ : QFAssertExpr D Γ)
    (X Y : Γ.syms)
    (hAr : Γ.arity X = Γ.arity Y)
    (hFresh : X.1 ∉ φ.symbols) :
    φ.rename X Y hAr = φ :=
  subst_vacuous X (RAExpr.relAs X Y hAr) φ hFresh

/- Renaming has the substitution/update semantics. -/
theorem rename_eval
    (I : Instance D Γ)
    (φ : QFAssertExpr D Γ)
    (X Y : Γ.syms)
    (hAr : Γ.arity X = Γ.arity Y) :
    (φ.rename X Y hAr).eval I ↔
      φ.eval
        (Instance.update I X
          ((RAExpr.relAs X Y hAr).eval I)) := by
  exact subst_eval I X (RAExpr.relAs X Y hAr) φ

end QFAssertExpr

end Whiel
