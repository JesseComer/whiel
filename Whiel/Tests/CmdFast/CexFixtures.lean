-- Author: Jesse Comer
import Whiel.Eval.CounterExample.Fast
import Whiel.Concrete.Notation
import Databases.UnnamedModel.Notation

/-
  Small executable examples for the fast counterexample
  checker.  These cover the main `CheckResult` cases and are
  kept out of the evaluator module itself.
-/

------------------------------------------------------------
-- Counterexample Checker Examples
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace CmdFast

namespace CexFixtures

open Whiel.Concrete

def EName : IndexAlphaName :=
  IndexAlphaName.baseString "E"

def TName : IndexAlphaName :=
  IndexAlphaName.baseString "T"

def schema : UnnamedSchema IndexAlphaName :=
  whielSch![
    {E, T} (arity: 1),
    _ (arity: 0)
  ]

def input : Instance Data schema :=
  inst![schema |
    EName := finrel![tuple!["a"]];
    TName := finrel![]
  ]

def copyCmd : Cmd Data schema :=
  whielCmd![
    { ExecSchema: schema }
    { T := E }
  ]

def truePre : AssertExpr Data schema :=
  assert![true]

def falsePre : AssertExpr Data schema :=
  assert![E = ∅]

def badPost : AssertExpr Data schema :=
  assert![T = ∅]

def goodPost : AssertExpr Data schema :=
  assert![T = E]

def boundExtra : Finset IndexAlphaName :=
  whielSyms!{T_2}

def boundPre : AssertExpr Data schema :=
  Whiel.Concrete.Notation.ofFormula
    (D := Data)
    (Γ := schema)
    boundExtra
    (guard![T_2 = E] :
      QFAssertExpr Data
        (Whiel.Concrete.Notation.extendSchema
          schema boundExtra))

def divergentCmd : Cmd Data schema :=
  whielCmd![
    { ExecSchema: schema }
    { WHILE true DO SKIP END }
  ]

def confirmedCounterexample :
    Whiel.CexFast.CheckResult Data schema :=
  Whiel.CexFast.checkCounterexample
    8 truePre copyCmd badPost input

def preconditionFalse :
    Whiel.CexFast.CheckResult Data schema :=
  Whiel.CexFast.checkCounterexample
    8 falsePre copyCmd badPost input

def postconditionTrue :
    Whiel.CexFast.CheckResult Data schema :=
  Whiel.CexFast.checkCounterexample
    8 truePre copyCmd goodPost input

def unsupported :
    Whiel.CexFast.CheckResult Data schema :=
  Whiel.CexFast.checkCounterexample
    8 boundPre copyCmd badPost input

def divergentOutOfFuel :
    Whiel.CexFast.CheckResult Data schema :=
  Whiel.CexFast.checkCounterexample
    3 truePre divergentCmd goodPost input

-- #eval confirmedCounterexample.display
-- #eval preconditionFalse.display
-- #eval postconditionTrue.display
-- #eval unsupported.display
-- #eval divergentOutOfFuel.display

/-
  Evaluating a non-fuelled partial interpreter on this
  command would diverge:

    WHILE true DO SKIP END

  The fast checker reports `outOfFuel` instead.
-/

end CexFixtures

end CmdFast

end Tests

end Whiel
