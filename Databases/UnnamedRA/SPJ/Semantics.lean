-- Author: Jesse Comer
import Databases.UnnamedRA.SPJ.Syntax
import Databases.UnnamedRA.SPJU.Semantics

/-
  This file proves monotonicity of SPJ unnamed
  relational algebra expressions.

  Key theorems include:
    * `SPJExpr.eval_monotone`

  Intervening definitions and lemmas are construction,
  helper, or proof support.
-/

------------------------------------------------------------
-- Monotonicity Properties
------------------------------------------------------------

namespace SPJExpr

variable {A D : Type} [Domain D]
variable {_ : RelationNames A}
variable {Γ : UnnamedSchema A}

/-
  Typed `SPJ` expressions are monotone under pointwise
  instance inclusion.
-/
theorem eval_monotone
    {n : Nat}
    (e : SPJExpr D Γ n)
    {I J : Instance D Γ}
    (hSub : Instance.Subset I J) :
    e.1.eval I ⊆ e.1.eval J := by
  exact SPJUExpr.eval_monotone
    (e := e.toSPJU) (I := I) (J := J) hSub

end SPJExpr
