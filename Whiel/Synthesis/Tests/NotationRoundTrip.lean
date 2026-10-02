-- Author: Jesse Comer
import Whiel.Concrete.Notation
import Whiel.Synthesis.Spec

/-
  Regression pins for the concrete guard notation and its
  pretty-printer.

  A certificate embeds `Guard.pretty` output and re-reads it
  with `qfAssert!`. These tests pin the two facts that keep
  that transition faithful:

    * connective precedence in the guard category matches
      the selection category (`¬` binds tighter than `∨`,
      `∧` binds tighter than `∨`); and
    * the exact printed form of representative formulas
      re-parses to the original formula.

  A precedence or printer regression fails these `decide`
  proofs at compile time.
-/

open Whiel.Concrete

set_option linter.hashCommand false

namespace Whiel
namespace Synthesis
namespace Tests
namespace NotationRoundTrip

def Γ : UnnamedSchema IndexAlphaName :=
  whielSch![ {R, R_2} (arity: 1), _ (arity: 0) ]

def eqAtom : QFAssertExpr Data Γ :=
  qfAssert![ (R = R_2) ]

def subsetAtom : QFAssertExpr Data Γ :=
  qfAssert![ (R ⊆ R_2) ]

def emptyAtom : QFAssertExpr Data Γ :=
  qfAssert![ (R = ∅) ]

def notEqAtom : QFAssertExpr Data Γ :=
  qfAssert![ ¬((R = R_2)) ]

def eqAndSubset : QFAssertExpr Data Γ :=
  qfAssert![ (R = R_2) ∧ (R ⊆ R_2) ]

def eqOrSubset : QFAssertExpr Data Γ :=
  qfAssert![ (R = R_2) ∨ (R ⊆ R_2) ]

------------------------------------------------------------
-- Connective Precedence
------------------------------------------------------------

def notOrFormula : QFAssertExpr Data Γ :=
  qfAssert![ ¬((R = R_2)) ∨ (R ⊆ R_2) ]

def andOrFormula : QFAssertExpr Data Γ :=
  qfAssert![ (R = R_2) ∧ (R ⊆ R_2) ∨ (R = ∅) ]

def negatedOrFormula : QFAssertExpr Data Γ :=
  qfAssert![ ¬((R = R_2) ∨ (R ⊆ R_2)) ]

/- `¬` binds tighter than `∨`. -/
example :
    notOrFormula =
      QFAssertExpr.or notEqAtom subsetAtom := by
  decide

/- `∧` binds tighter than `∨`. -/
example :
    andOrFormula =
      QFAssertExpr.or eqAndSubset emptyAtom := by
  decide

/- Parenthesized negation still covers the disjunction. -/
example :
    negatedOrFormula = QFAssertExpr.not eqOrSubset := by
  decide

------------------------------------------------------------
-- Printed-Form Round Trip
------------------------------------------------------------

/-
  Each `reparsed*` definition spells its formula exactly as
  `Guard.pretty` prints it, checked by the string equations
  below.
-/

def reparsedNotOr : QFAssertExpr Data Γ :=
  qfAssert![ ((¬((R = R_2))) ∨ (R ⊆ R_2)) ]

def reparsedAndOr : QFAssertExpr Data Γ :=
  qfAssert![ (((R = R_2) ∧ (R ⊆ R_2)) ∨ (R = ∅[1])) ]

def reparsedNegatedOr : QFAssertExpr Data Γ :=
  qfAssert![ (¬(((R = R_2) ∨ (R ⊆ R_2)))) ]

/-
  Printer spelling pins. The printer is untrusted runtime
  assistance, so these use compiled evaluation rather than
  kernel `decide`; a drifting spelling still fails the
  build.
-/
#eval show IO Unit from do
  unless notOrFormula.pretty =
      "((¬((R = R_2))) ∨ (R ⊆ R_2))" do
    throw (IO.userError "notOrFormula printer drift")

example : reparsedNotOr = notOrFormula := by decide

#eval show IO Unit from do
  unless andOrFormula.pretty =
      "(((R = R_2) ∧ (R ⊆ R_2)) ∨ (R = ∅[1]))" do
    throw (IO.userError "andOrFormula printer drift")

example : reparsedAndOr = andOrFormula := by decide

#eval show IO Unit from do
  unless negatedOrFormula.pretty =
      "(¬(((R = R_2) ∨ (R ⊆ R_2))))" do
    throw (IO.userError "negatedOrFormula printer drift")

example : reparsedNegatedOr = negatedOrFormula := by
  decide

end NotationRoundTrip
end Tests
end Synthesis
end Whiel
