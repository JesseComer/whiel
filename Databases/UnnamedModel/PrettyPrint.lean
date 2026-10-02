-- Author: Jesse Comer
import Databases.Core.PrettyPrint
import Databases.UnnamedModel.Instance

/-
  Pretty-printers for unnamed database instances.

  Key declarations include:
    * `Instance.display`
    * `Instance.displayAdom`
-/

------------------------------------------------------------
-- Instance Pretty-Printing
------------------------------------------------------------

namespace Instance

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable [DBLib.Notation.PrettyLiteral D]
variable {Γ : UnnamedSchema A}

/- Render an unnamed instance relation-by-relation. -/
def pretty (I : Instance D Γ) : String :=
  DBTPretty.finset
    (fun X : Γ.syms =>
      reprStr X.1 ++ " ↦ " ++ (I X).pretty)
    Γ.syms.attach

/- Render an instance directly in `#eval` output. -/
def display (I : Instance D Γ) : DBTPretty.Display :=
  DBTPretty.display I.pretty

/- Render the active domain of an instance. -/
def prettyAdom (I : Instance D Γ) : String :=
  DBTPretty.finset DBLib.Notation.prettyLiteral I.Adom

/- Render the active domain directly in `#eval` output. -/
def displayAdom (I : Instance D Γ) :
    DBTPretty.Display :=
  DBTPretty.display I.prettyAdom

end Instance
