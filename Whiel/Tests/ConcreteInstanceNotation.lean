-- Author: Jesse Comer
import Whiel.Concrete.Notation

/-
  Semantic checks for concrete instance notation. Large
  elaboration cases live in the dedicated stress runner.
-/

------------------------------------------------------------
-- Mixed Concrete Data
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace ConcreteInstanceNotation

open Concrete

def schema : UnnamedSchema IndexAlphaName :=
  whielSch![
  {Natural} (arity: 1),
  {Text} (arity: 1),
  {Flag} (arity: 1),
  {Pair} (arity: 2),
  {Empty} (arity: 3),
  {Nullary} (arity: 0),
  _ (arity: 0)
  ]

def computedValue : Data :=
  .num 17

def testInstance : Instance Data schema :=
  inst![schema |
    Natural := [[0], [1], [2], [3]];
    Text := [["alpha"], ["comma,semicolon;safe"]];
    Flag := [[Bool.true], [Bool.false]];
    Pair := [[computedValue, "value"], [3, "three"]];
    Empty := [];
    Nullary := [[]]
  ]

def naturalSymbol : schema.syms :=
  UnnamedSchema.sym schema
    (IndexAlphaName.baseString "Natural")

def textSymbol : schema.syms :=
  UnnamedSchema.sym schema
    (IndexAlphaName.baseString "Text")

def flagSymbol : schema.syms :=
  UnnamedSchema.sym schema
    (IndexAlphaName.baseString "Flag")

def pairSymbol : schema.syms :=
  UnnamedSchema.sym schema
    (IndexAlphaName.baseString "Pair")

def emptySymbol : schema.syms :=
  UnnamedSchema.sym schema
    (IndexAlphaName.baseString "Empty")

def nullarySymbol : schema.syms :=
  UnnamedSchema.sym schema
    (IndexAlphaName.baseString "Nullary")

set_option linter.style.nativeDecide false in
example : (testInstance naturalSymbol).card = 4 := by
  native_decide

set_option linter.style.nativeDecide false in
example : (testInstance textSymbol).card = 2 := by
  native_decide

set_option linter.style.nativeDecide false in
example : (testInstance flagSymbol).card = 2 := by
  native_decide

set_option linter.style.nativeDecide false in
example : (testInstance pairSymbol).card = 2 := by
  native_decide

set_option linter.style.nativeDecide false in
example : (testInstance emptySymbol).card = 0 := by
  native_decide

set_option linter.style.nativeDecide false in
example : (testInstance nullarySymbol).card = 1 := by
  native_decide

end ConcreteInstanceNotation

end Tests

end Whiel

------------------------------------------------------------
-- Kernel Reduction of Natural Literals
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace ConcreteInstanceNotation

open Concrete Concrete.Notation

/-
  Invalidity certificates kernel-reduce through the numeric
  fast path; these pins keep the decoder structural. All of
  them were stuck on `Acc.rec` under the previous
  `String.splitOn`-based decoder.
-/

example :
    encodedNaturalRelation 2 "0,1;2,3" =
      relationFromRows 2
        [[Data.num 0, Data.num 1],
         [Data.num 2, Data.num 3]] := by
  decide +kernel

example :
    encodedNaturalRelation 2 "12,345" =
      relationFromRows 2
        [[Data.num 12, Data.num 345]] := by
  decide +kernel

/- Malformed rows drop, as with the previous decoder. -/
example :
    encodedNaturalRelation 2 "0,1;x,y;2,3" =
      relationFromRows 2
        [[Data.num 0, Data.num 1],
         [Data.num 2, Data.num 3]] := by
  decide +kernel

example :
    encodedNaturalRelation 0 "" =
      relationFromRows 0 [[]] := by
  decide +kernel

/- End to end through the `inst!` macro's fast path. -/
example : (testInstance naturalSymbol).card = 4 := by
  decide +kernel

end ConcreteInstanceNotation

end Tests

end Whiel
