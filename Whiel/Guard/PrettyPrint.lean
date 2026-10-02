-- Author: Jesse Comer
import Whiel.Guard.Semantics
import Databases.UnnamedRA.PrettyPrint

/-
  Pretty-printers for Whiel guards.

  Key declarations:
    * `Whiel.Guard.pretty`
    * `Whiel.Guard.display`
    * `Whiel.Guard.displayEvalBase`
-/

------------------------------------------------------------
-- Guard Pretty-Printing
------------------------------------------------------------

namespace Whiel

namespace Guard

variable {A D : Type} [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Render a Whiel guard. -/
def pretty : Guard D Γ → String
| .«true» => "true"
| .«false» => "false"
| .eq e₁ e₂ => "(" ++ e₁.pretty ++ " = " ++ e₂.pretty ++ ")"
| .subset e₁ e₂ =>
    "(" ++ e₁.pretty ++ " ⊆ " ++ e₂.pretty ++ ")"
| .and φ ψ =>
    "(" ++ φ.pretty ++ " ∧ " ++ ψ.pretty ++ ")"
| .or φ ψ =>
    "(" ++ φ.pretty ++ " ∨ " ++ ψ.pretty ++ ")"
| .not φ =>
    "(¬(" ++ φ.pretty ++ "))"

/- Render a guard directly in `#eval`. -/
def display (φ : Guard D Γ) : DBTPretty.Display :=
  DBTPretty.display φ.pretty

/- Render same-schema guard satisfaction. -/
def displayEvalBase
    (φ : Guard D Γ)
    (I : Instance D Γ) : DBTPretty.Display :=
  DBTPretty.display (toString (decide (φ.eval I)))

end Guard

end Whiel
