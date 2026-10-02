-- Author: Jesse Comer
import Databases.Core.PrettyPrint
import Databases.FinStruct.Basic

/-
  Pretty-printers for finite first-order structures.

  Key declarations include:
    * `FinStruct.display`
    * `FinStruct.displayCarrier`
    * `FinStruct.displayRelations`
    * `FinStruct.displayFunctions`
-/

------------------------------------------------------------
-- Finite Structure Pretty-Printing
------------------------------------------------------------

namespace FinStruct

variable {A F D : Type}
variable [RelationNames A]
variable [FunctionNames F]
variable [Domain D]
variable [DBLib.Notation.PrettyLiteral D]
variable [DBLib.Notation.PrettyLiteral F]
variable {Sig : Signature A F}

/- Render the finite structure carrier. -/
def prettyCarrier (M : FinStruct D Sig) : String :=
  DBTPretty.finset DBLib.Notation.prettyLiteral M.carrier

/- Render one relation interpretation. -/
def prettyRelation
    (M : FinStruct D Sig)
    (X : Signature.Rel Sig) : String :=
  reprStr X.1 ++ " ↦ " ++ (M.rels X).pretty

/- Render all relation interpretations. -/
def prettyRelations (M : FinStruct D Sig) : String :=
  DBTPretty.finset
    (fun X : Signature.Rel Sig => M.prettyRelation X)
    Sig.syms.attach

/- Render one function-table entry. -/
def prettyFunctionEntry
    (M : FinStruct D Sig)
    (f : Signature.Fun Sig)
    (args : Tuple D (Sig.funArity f)) : String :=
  Tuple.prettyFromKey args.prettyKey ++
    " ↦ " ++ DBLib.Notation.prettyLiteral
      (M.funcs f args)

/- Render one function interpretation as a finite graph. -/
def prettyFunction
    (M : FinStruct D Sig)
    (f : Signature.Fun Sig) : String :=
  DBLib.Notation.prettyLiteral f.1 ++ " ↦ " ++
    DBTPretty.finset
      (fun args : Tuple D (Sig.funArity f) =>
        M.prettyFunctionEntry f args)
      (Tuple.allOver M.carrier (Sig.funArity f))

/- Render all function interpretations. -/
def prettyFunctions (M : FinStruct D Sig) : String :=
  DBTPretty.finset
    (fun f : Signature.Fun Sig => M.prettyFunction f)
    Sig.funs.attach

/- Render carrier, relations, and functions. -/
def pretty (M : FinStruct D Sig) : String :=
  "carrier " ++ M.prettyCarrier ++
    "; relations " ++ M.prettyRelations ++
    "; functions " ++ M.prettyFunctions

/- Render a finite structure directly in `#eval` output. -/
def display (M : FinStruct D Sig) : DBTPretty.Display :=
  DBTPretty.display M.pretty

/- Render the carrier directly in `#eval` output. -/
def displayCarrier (M : FinStruct D Sig) :
    DBTPretty.Display :=
  DBTPretty.display M.prettyCarrier

/- Render relations directly in `#eval` output. -/
def displayRelations (M : FinStruct D Sig) :
    DBTPretty.Display :=
  DBTPretty.display M.prettyRelations

/- Render functions directly in `#eval` output. -/
def displayFunctions (M : FinStruct D Sig) :
    DBTPretty.Display :=
  DBTPretty.display M.prettyFunctions

end FinStruct
