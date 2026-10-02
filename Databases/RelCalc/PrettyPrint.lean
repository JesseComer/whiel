-- Author: Jesse Comer
import Databases.Core.PrettyPrint
import Databases.RelCalc.AdomSemantics

/-
  Pretty-printers and display helpers for relational
  calculus syntax and active-domain satisfaction.

  Key declarations include:
    * `RelTerm.pretty`
    * `RelCalc.Formula.pretty`
    * `RelCalc.Query.pretty`
    * `RelCalc.Formula.displayAdomSat`
    * `RelCalc.Query.display`
-/

-- Formula Pretty-Printing
------------------------------------------------------------

namespace RelCalc

namespace Formula

variable {A D : Type} [RelationNames A] [Domain D]
variable [DBLib.Notation.PrettyLiteral D]
variable {Γ : UnnamedSchema A}

/- Render a relational-calculus formula. -/
def pretty : Formula D Γ → String
| .top => "⊤"
| .bot => "⊥"
| .eq t₁ t₂ => t₁.pretty ++ " = " ++ t₂.pretty
| .rel a => a.pretty
| .and φ ψ =>
    "(" ++ φ.pretty ++ " ∧ " ++ ψ.pretty ++ ")"
| .or φ ψ =>
    "(" ++ φ.pretty ++ " ∨ " ++ ψ.pretty ++ ")"
| .not φ =>
    "¬" ++ φ.pretty
| .imp φ ψ =>
    "(" ++ φ.pretty ++ " → " ++ ψ.pretty ++ ")"
| .iff φ ψ =>
    "(" ++ φ.pretty ++ " ↔ " ++ ψ.pretty ++ ")"
| .forall_ x φ =>
    "∀ " ++ DBTPretty.varName x ++ ". " ++ φ.pretty
| .exists_ x φ =>
    "∃ " ++ DBTPretty.varName x ++ ". " ++ φ.pretty

/- Render a formula directly in `#eval` output. -/
def display (φ : Formula D Γ) : DBTPretty.Display :=
  DBTPretty.display φ.pretty

/- Display active-domain satisfaction in an instance. -/
def displayAdomSat
    (φ : Formula D Γ)
    (I : Instance D Γ)
    (σ : Assign D) : DBTPretty.Display :=
  DBTPretty.display (toString (decide (φ.AdomSat I σ)))

end Formula

end RelCalc

------------------------------------------------------------
-- Query Pretty-Printing
------------------------------------------------------------

namespace RelCalc

namespace Query

variable {A D : Type} [RelationNames A] [Domain D]
variable [DBLib.Notation.PrettyLiteral D]
variable {Γ : UnnamedSchema A} {n : Nat}

/- Render a query output-variable vector. -/
def prettyVars (xs : List Var) : String :=
  match xs with
  | [] => "()"
  | [x] => DBTPretty.varName x
  | xs =>
      "(" ++ DBTPretty.joinSep ", "
        (xs.map DBTPretty.varName) ++ ")"

/- Render a relational-calculus query. -/
def pretty (q : Query D Γ n) : String :=
  "{" ++ prettyVars q.vars.toList ++
    " | " ++ q.form.pretty ++ "}"

/- Render a query directly in `#eval` output. -/
def display (q : Query D Γ n) : DBTPretty.Display :=
  DBTPretty.display q.pretty

end Query

end RelCalc
