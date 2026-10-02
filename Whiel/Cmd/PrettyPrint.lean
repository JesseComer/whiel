-- Author: Jesse Comer
import Whiel.Cmd.Syntax
import Whiel.AssertExpr.PrettyPrint

/-
  Pretty-printers for Whiel commands and programs.

  Relation names render through the carrier's `Spelling`
  instance, so a printed command is the notation's own text
  for it wherever the carrier has a notation.

  Key declarations include:
    * `Whiel.Cmd.pretty`
    * `Whiel.Program.pretty`
    * `Whiel.Program.display`
-/

namespace Whiel

namespace Cmd

variable {A D : Type} [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Render a Whiel command. -/
def pretty : Cmd D Γ → String
| .skip => "SKIP"
| .assign X e =>
    spellName X.1 ++ " := " ++ e.pretty
| .seq C₁ C₂ =>
    C₁.pretty ++ ";\n" ++ C₂.pretty
| .ite G C₁ C₂ =>
    "IF " ++ G.pretty ++ " THEN\n" ++
      C₁.pretty ++ "\nELSE\n" ++ C₂.pretty ++ "\nEND"
| .«while» G C =>
    "WHILE " ++ G.pretty ++ " DO\n" ++
      C.pretty ++ "\nEND"

/- Render a command directly in `#eval`. -/
def display (C : Cmd D Γ) : DBTPretty.Display :=
  DBTPretty.display C.pretty

end Cmd

namespace Program

variable {A D : Type} [RelationNames A] [Domain D]
variable {Δ Λ : UnnamedSchema A}

/- Render the command body of a Whiel program. -/
def pretty (P : Program D Δ Λ) : String :=
  "input " ++ Δ.pretty ++
    "; output " ++ Λ.pretty ++
    "; exec " ++ P.execSchema.pretty ++
    "\n" ++ P.cmd.pretty

/- Render a program directly in `#eval`. -/
def display (P : Program D Δ Λ) : DBTPretty.Display :=
  DBTPretty.display P.pretty

end Program

end Whiel
