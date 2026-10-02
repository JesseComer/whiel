-- Author: Jesse Comer
import Databases.Core.PrettyPrint
import Databases.UnnamedRA.Syntax

/-
  Pretty-printers for unnamed relational algebra syntax.

  Key declarations include:
    * `Sel.pretty`
    * `RawRAExpr.pretty`
    * `RAExpr.pretty`
    * `RAExpr.display`
-/

------------------------------------------------------------
-- Selection Pretty-Printing
------------------------------------------------------------

namespace Sel

variable {D : Type} [Domain D]
variable [DBLib.Notation.PrettyLiteral D]

/- Render a selection condition as compact surface text. -/
def pretty : Sel D → String
| .eqIdx i j =>
    "#" ++ toString i ++ " = #" ++ toString j
| .eqConst i c =>
    "#" ++ toString i ++ " = " ++
      DBLib.Notation.prettyLiteral c
| .and φ ψ =>
    "(" ++ φ.pretty ++ " ∧ " ++ ψ.pretty ++ ")"
| .or φ ψ =>
    "(" ++ φ.pretty ++ " ∨ " ++ ψ.pretty ++ ")"
| .not φ =>
    "¬(" ++ φ.pretty ++ ")"

/- Render a selection condition directly in `#eval`. -/
def display (φ : Sel D) : DBTPretty.Display :=
  DBTPretty.display φ.pretty

end Sel

------------------------------------------------------------
-- RA Pretty-Printing
------------------------------------------------------------

namespace RawRAExpr

variable {A D : Type} [RelationNames A] [Domain D]
variable [DBLib.Notation.PrettyLiteral D]

/- Render a raw RA expression as compact surface text. -/
def pretty : RawRAExpr A D → String
| .top => "⊤"
| .empty n => "∅[" ++ toString n ++ "]"
| .rel X => spellName X
| .single d => "{" ++ DBLib.Notation.prettyLiteral d ++ "}"
| .select φ e => "σ[" ++ φ.pretty ++ "] (" ++ e.pretty ++ ")"
| .proj idxs e =>
    "π[" ++ DBTPretty.joinSep "," (idxs.map toString) ++
      "] (" ++ e.pretty ++ ")"
| .prod e₁ e₂ =>
    "(" ++ e₁.pretty ++ " × " ++ e₂.pretty ++ ")"
| .union e₁ e₂ =>
    "(" ++ e₁.pretty ++ " ∪ " ++ e₂.pretty ++ ")"
| .diff e₁ e₂ =>
    "(" ++ e₁.pretty ++ " ∖ " ++ e₂.pretty ++ ")"

/- Render a raw RA expression directly in `#eval`. -/
def display (e : RawRAExpr A D) : DBTPretty.Display :=
  DBTPretty.display e.pretty

end RawRAExpr

namespace RAExpr

variable {A D : Type} [RelationNames A] [Domain D]
variable [DBLib.Notation.PrettyLiteral D]
variable {Γ : UnnamedSchema A} {n : Nat}

/- Render a well-formed RA expression. -/
def pretty (e : RAExpr D Γ n) : String :=
  e.expr.pretty

/- Render a well-formed RA expression in `#eval`. -/
def display (e : RAExpr D Γ n) : DBTPretty.Display :=
  DBTPretty.display e.pretty

end RAExpr
