-- Author: Jesse Comer
import Whiel.AssertExpr.Syntax
import Whiel.Guard.PrettyPrint

/-
  Pretty-printers for Whiel assertions.

  Key declarations include:
    * `Whiel.QFAssertExpr.pretty`
    * `Whiel.AssertExpr.pretty`
    * `Whiel.AssertExpr.display`
-/

namespace Whiel

namespace QFAssertExpr

variable {A D : Type} [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Render a quantifier-free assertion. -/
abbrev pretty (φ : QFAssertExpr D Γ) : String :=
  Guard.pretty φ

/- Render a quantifier-free assertion in `#eval`. -/
abbrev display (φ : QFAssertExpr D Γ) :
    DBTPretty.Display :=
  Guard.display φ

end QFAssertExpr

namespace AssertExpr

variable {A D : Type} [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Render a full assertion. -/
def pretty (φ : AssertExpr D Γ) : String :=
  let body := φ.formula.pretty
  if φ.boundSymbols = ∅ then
    body
  else
    "∃ " ++
      DBTPretty.finset spellName φ.boundSymbols ++
      ". " ++ body

/- Render a full assertion directly in `#eval`. -/
def display (φ : AssertExpr D Γ) : DBTPretty.Display :=
  DBTPretty.display φ.pretty

end AssertExpr

end Whiel
