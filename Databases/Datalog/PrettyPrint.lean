-- Author: Jesse Comer
import Databases.Core.PrettyPrint
import Databases.Datalog.Syntax

/-
  Pretty-printers for Datalog syntax.

  Key declarations include:
    * `RelTerm.pretty`
    * `RelAtom.pretty`
    * `Datalog.Atom.pretty`
    * `Datalog.Rule.pretty`
    * `Datalog.Program.pretty`
    * `Datalog.Program.display`
-/

namespace Datalog

namespace Atom

variable {A D : Type} [RelationNames A] [Domain D]
variable [DBLib.Notation.PrettyLiteral D]
variable {Γ : UnnamedSchema A}

/- Render a Datalog atom. -/
def pretty : Atom D Γ → String
| .rel a => a.pretty
| .eq lhs rhs => lhs.pretty ++ " = " ++ rhs.pretty

/- Render a Datalog atom directly in `#eval`. -/
def display (b : Atom D Γ) : DBTPretty.Display :=
  DBTPretty.display b.pretty

end Atom

namespace Rule

variable {A D : Type} [RelationNames A] [Domain D]
variable [DBLib.Notation.PrettyLiteral D]
variable {Γ : UnnamedSchema A}

/- Render a Datalog rule. -/
def pretty (r : Rule D Γ) : String :=
  let head := r.head.pretty
  match r.body with
  | [] => head ++ " :-;"
  | body =>
      head ++ " :- " ++
        DBTPretty.joinSep ", "
          (body.map Atom.pretty) ++ ";"

/- Render a Datalog rule directly in `#eval`. -/
def display (r : Rule D Γ) : DBTPretty.Display :=
  DBTPretty.display r.pretty

end Rule

namespace Program

variable {A D : Type} [RelationNames A] [Domain D]
variable [DBLib.Notation.PrettyLiteral D]
variable {Γ : UnnamedSchema A}

/- Render a Datalog program. -/
def pretty (P : Program D Γ) : String :=
  DBTPretty.joinSep "\n" (P.rules.map Rule.pretty)

/- Render a Datalog program directly in `#eval`. -/
def display (P : Program D Γ) : DBTPretty.Display :=
  DBTPretty.display P.pretty

end Program

namespace Query

variable {A D : Type} [RelationNames A] [Domain D]
variable [DBLib.Notation.PrettyLiteral D]
variable {Γ : UnnamedSchema A} {n : Nat}

/- Render a Datalog query head. -/
def pretty (q : Query D Γ n) : String :=
  reprStr q.output.val.1 ++ " (arity: " ++ toString n ++ ")"

/- Render a Datalog query directly in `#eval`. -/
def display (q : Query D Γ n) : DBTPretty.Display :=
  DBTPretty.display q.pretty

end Query

end Datalog
