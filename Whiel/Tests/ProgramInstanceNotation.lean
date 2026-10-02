-- Author: Jesse Comer
import Whiel.Eval.CounterExample.InstanceNotation

/-
  Pins for the `programInst!` instance notation over the
  `ProgramNames` carrier.

  Three things are checked. The notation spells every shape
  a frozen counterexample record can carry: an explicitly
  empty relation, a relation the entries omit, a nullary
  relation, a program symbol, an auxiliary symbol, a flag,
  and each domain constant the records use. Its value is the
  `ProgramInstance.ofKeyedRows` instance over the same keyed
  rows, so every equality below is closed by `rfl` and the
  canonical keys the notation computes are pinned against
  `ProgramNames.encode`. And it kernel-reduces: the cardinal
  checks run under `decide +kernel`, which is the reduction
  an invalidity certificate's `certifyKernel` performs.

  The three frozen shapes rebuilt below are the checked-in
  counterexamples of `Example0013`, `Example4002` and
  `Example4037`. Their schemas are restated here rather than
  imported: these are pins on the notation, not on the
  corpus.
-/

open Whiel.Concrete

set_option linter.hashCommand false

------------------------------------------------------------
-- Every Shape the Notation Must Spell
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace ProgramInstanceNotation

open Concrete

/-
  A program symbol, an omitted program symbol, a nullary
  program symbol, an auxiliary symbol, a snapshot index and
  a flag.
-/
def mixedSchema : UnnamedSchema ProgramNames :=
  programSch![
    E (arity: 2),
    Omitted (arity: 2),
    Nullary (arity: 0),
    Text (arity: 1),
    Flags (arity: 1),
    S_aux (arity: 2),
    S_2 (arity: 1),
    flag_0_0 (arity: 0)
  ]

/-
  `Omitted` is named by the schema and by neither instance:
  a relation the entries do not mention is empty.
-/
def mixed : Instance Data mixedSchema :=
  programInst![mixedSchema |
    E := [[0, 1], [1, 2]];
    Nullary := [[]];
    Text := [["alpha"], ["comma,semicolon;safe"]];
    Flags := [[true], [false]];
    S_aux := [];
    S_2 := [[7]];
    flag_0_0 := [[]] ]

def mixedRows : ProgramInstance.KeyedRows :=
  [ ("p::E", [[Data.num 0, Data.num 1],
      [Data.num 1, Data.num 2]]),
    ("p::Nullary", [[]]),
    ("p::Text", [[Data.str "alpha"],
      [Data.str "comma,semicolon;safe"]]),
    ("p::Flags", [[Data.bool true], [Data.bool false]]),
    ("a::S", []),
    ("p:ss:S", [[Data.num 7]]),
    ("f::0", [[]]) ]

/- The notation is the keyed-row instance, not a copy. -/
example :
    mixed =
      ProgramInstance.ofKeyedRows mixedSchema mixedRows :=
  rfl

/-
  The keys above are the canonical codec's, so the pin is a
  pin on `ProgramNames.encode` and not on a respelling.
-/
#guard
  ProgramNames.encode
    (.programSymbol ⟨"E", by decide⟩ 0) == "p::E"

#guard
  ProgramNames.encode
    (.auxiliarySymbol ⟨"S", by decide⟩ 0) == "a::S"

#guard
  ProgramNames.encode
    (.programSymbol ⟨"S", by decide⟩ 2) == "p:ss:S"

#guard ProgramNames.encode (.flagSymbol 0 0) == "f::0"

def edge : mixedSchema.syms :=
  UnnamedSchema.sym mixedSchema
    (.programSymbol ⟨"E", by decide⟩ 0)

def omitted : mixedSchema.syms :=
  UnnamedSchema.sym mixedSchema
    (.programSymbol ⟨"Omitted", by decide⟩ 0)

def nullary : mixedSchema.syms :=
  UnnamedSchema.sym mixedSchema
    (.programSymbol ⟨"Nullary", by decide⟩ 0)

def text : mixedSchema.syms :=
  UnnamedSchema.sym mixedSchema
    (.programSymbol ⟨"Text", by decide⟩ 0)

def flags : mixedSchema.syms :=
  UnnamedSchema.sym mixedSchema
    (.programSymbol ⟨"Flags", by decide⟩ 0)

def snapshot : mixedSchema.syms :=
  UnnamedSchema.sym mixedSchema
    (.auxiliarySymbol ⟨"S", by decide⟩ 0)

def indexed : mixedSchema.syms :=
  UnnamedSchema.sym mixedSchema
    (.programSymbol ⟨"S", by decide⟩ 2)

def flagged : mixedSchema.syms :=
  UnnamedSchema.sym mixedSchema (.flagSymbol 0 0)

/-
  The notation kernel-reduces: these are the reductions
  `certifyKernel` performs on an emitted instance.
-/
example : (mixed edge).card = 2 := by decide +kernel

example : (mixed omitted).card = 0 := by decide +kernel

example : (mixed nullary).card = 1 := by decide +kernel

example : (mixed text).card = 2 := by decide +kernel

example : (mixed flags).card = 2 := by decide +kernel

example : (mixed snapshot).card = 0 := by decide +kernel

example : (mixed indexed).card = 1 := by decide +kernel

example : (mixed flagged).card = 1 := by decide +kernel

/- A schema whose every relation the notation omits. -/
def bareSchema : UnnamedSchema ProgramNames :=
  programSch![ E (arity: 2) ]

def bare : Instance Data bareSchema :=
  programInst![bareSchema]

example :
    bare = ProgramInstance.ofKeyedRows bareSchema [] :=
  rfl

end ProgramInstanceNotation

end Tests

end Whiel

------------------------------------------------------------
-- The Frozen Counterexample Shapes
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace ProgramInstanceNotation

open Concrete

/- `Example0013`: three binary program relations. -/
def schema0013 : UnnamedSchema ProgramNames :=
  programSch![ {E, T, S} (arity: 2) ]

def instance0013 : Instance Data schema0013 :=
  programInst![schema0013 |
    E := [[0, 1], [1, 2]];
    S := [];
    T := [] ]

example :
    instance0013 =
      ProgramInstance.ofKeyedRows schema0013
        [ ("p::E", [[Data.num 0, Data.num 1],
            [Data.num 1, Data.num 2]]),
          ("p::S", []),
          ("p::T", []) ] :=
  rfl

/- `Example4002`: auxiliary snapshots beside the inputs. -/
def schema4002 : UnnamedSchema ProgramNames :=
  programSch![
    {E, T, TUp} (arity: 2),
    V (arity: 1),
    {T_aux, TUp_aux} (arity: 2)
  ]

def instance4002 : Instance Data schema4002 :=
  programInst![schema4002 |
    T_aux := [];
    TUp_aux := [];
    E := [[0, 1]];
    T := [];
    TUp := [];
    V := [] ]

example :
    instance4002 =
      ProgramInstance.ofKeyedRows schema4002
        [ ("a::T", []),
          ("a::TUp", []),
          ("p::E", [[Data.num 0, Data.num 1]]),
          ("p::T", []),
          ("p::TUp", []),
          ("p::V", []) ] :=
  rfl

/- `Example4037`: strings and a ternary relation. -/
def schema4037 : UnnamedSchema ProgramNames :=
  programSch![
    F (arity: 3),
    {Q, QUp, T, Vb} (arity: 2),
    {Va, Vc} (arity: 1),
    {Q_aux, QUp_aux, T_aux} (arity: 2)
  ]

def instance4037 : Instance Data schema4037 :=
  programInst![schema4037 |
    Q_aux := [];
    QUp_aux := [];
    T_aux := [];
    F := [["b", "x", "d"], ["x", "y", "d"]];
    Q := [];
    QUp := [];
    T := [];
    Va := [];
    Vb := [["x", "d"]];
    Vc := [] ]

example :
    instance4037 =
      ProgramInstance.ofKeyedRows schema4037
        [ ("a::Q", []),
          ("a::QUp", []),
          ("a::T", []),
          ("p::F", [[Data.str "b", Data.str "x",
              Data.str "d"],
            [Data.str "x", Data.str "y", Data.str "d"]]),
          ("p::Q", []),
          ("p::QUp", []),
          ("p::T", []),
          ("p::Va", []),
          ("p::Vb", [[Data.str "x", Data.str "d"]]),
          ("p::Vc", []) ] :=
  rfl

end ProgramInstanceNotation

end Tests

end Whiel

------------------------------------------------------------
-- Rejections
------------------------------------------------------------

namespace Whiel

namespace Tests

namespace ProgramInstanceNotation

open Concrete

/-
  A name the schema does not carry is refused rather than
  silently ignored, which is what `ofKeyedRows` does with an
  unrecognized key.
-/
/--
error: unknown relation 'Z': the schema has no such symbol
-/
#guard_msgs in
def unknownRelation : Instance Data schema0013 :=
  programInst![schema0013 | Z := []]

/- A relation absent at a positive index is refused too. -/
/--
error: unknown relation 'E_3': the schema has no such symbol
-/
#guard_msgs in
def unknownIndex : Instance Data schema0013 :=
  programInst![schema0013 | E_3 := []]

/- A row of the wrong width is refused, never dropped. -/
/--
error: relation 'E' has arity 2 in the schema, but a row of the notation has 3 cells
-/
#guard_msgs in
def wrongArity : Instance Data schema0013 :=
  programInst![schema0013 | E := [[0, 1, 2]]]

/- Rows of one relation must agree with each other. -/
/--
error: relation 'E' has arity 2 in the schema, but a row of the notation has 1 cells
-/
#guard_msgs in
def raggedRows : Instance Data schema0013 :=
  programInst![schema0013 | E := [[0, 1], [2]]]

/- Only the first of two entries would be read. -/
/--
error: relation 'E' is named twice
-/
#guard_msgs in
def repeatedRelation : Instance Data schema0013 :=
  programInst![schema0013 | E := []; E := [[0, 1]]]

/- The shared program-name reader's spellings still bind. -/
/--
error: index zero is spelled without a suffix; write 'E' instead of 'E_0'
-/
#guard_msgs in
def rejectedZeroIndex : Instance Data schema0013 :=
  programInst![schema0013 | E_0 := []]

/--
error: expected an alphabetical relation name, got 'E1'
-/
#guard_msgs in
def rejectedBase : Instance Data schema0013 :=
  programInst![schema0013 | E1 := []]

end ProgramInstanceNotation

end Tests

end Whiel
