-- Author: Jesse Comer
import Whiel.Concrete.Notation
import Whiel.Cmd.Rewrites.FramedLoop

/-
  Pins for the `ProgramNames` surface notation:
  `programSch!`, `programAssert!`, `programQF!`, and
  `programCmd!`.

  A plain identifier `R` is `ProgramNames.programSymbol R 0`
  and an identifier `T_aux` is
  `ProgramNames.auxiliarySymbol T 0`. A positive canonical
  decimal suffix selects the snapshot index: `R_2` is
  `programSymbol R 2` and `T_aux_2` is
  `auxiliarySymbol T 2`. Index zero has no suffix spelling,
  so `R_0` is rejected, as are leading zeros and any
  non-alphabetical base. The notation does not enforce the
  raw index-zero discipline of input files; that is decided
  by `Hoare.preprocess` on the schema. Names bound by `∃`
  must be auxiliary names; they inherit arity from the
  program symbol with the same base.

  A block command may be followed directly by the rest of
  the sequence: `END C := ∅` and `END; C := ∅` elaborate to
  the same term.
-/

open Whiel.Concrete

set_option linter.hashCommand false

namespace Whiel
namespace Tests
namespace ProgramNotation

------------------------------------------------------------
-- Schema
------------------------------------------------------------

def r : ProgramNames :=
  .programSymbol ⟨"R", by decide⟩ 0

def u : ProgramNames :=
  .programSymbol ⟨"U", by decide⟩ 0

def tAux : ProgramNames :=
  .auxiliarySymbol ⟨"T", by decide⟩ 0

def rAux : ProgramNames :=
  .auxiliarySymbol ⟨"R", by decide⟩ 0

/- Two unary program symbols and one binary auxiliary. -/
def programSchema : UnnamedSchema ProgramNames :=
  programSch![ {R, U} (arity: 1), T_aux (arity: 2) ]

/- The same schema built from the constructors by hand. -/
def expectedSchema : UnnamedSchema ProgramNames where
  syms := {r, u, tAux}
  arity := fun X => if X.1 = tAux then 2 else 1

#guard programSchema.syms = expectedSchema.syms
#guard [r, u, tAux, rAux].all fun X =>
  programSchema.arity? X == expectedSchema.arity? X
#guard programSchema.arity? r = some 1
#guard programSchema.arity? tAux = some 2
#guard programSchema.arity? rAux = none

/- The `_ (arity: n)` fallback is available as well. -/
def fallbackSchema : UnnamedSchema ProgramNames :=
  programSch![ R (arity: 1), _ (arity: 3) ]

#guard fallbackSchema.arity? r = some 1
#guard fallbackSchema.arity? u = none

------------------------------------------------------------
-- Positive Indices
------------------------------------------------------------

def rTwo : ProgramNames :=
  .programSymbol ⟨"R", by decide⟩ 2

def uTwelve : ProgramNames :=
  .programSymbol ⟨"U", by decide⟩ 12

def tAuxThree : ProgramNames :=
  .auxiliarySymbol ⟨"T", by decide⟩ 3

/- `R_2`, `U_12`, and `T_aux_3` name snapshot indices. -/
def indexedSchema : UnnamedSchema ProgramNames :=
  programSch![
    {R, R_2, U_12} (arity: 1), {T_aux, T_aux_3} (arity: 2) ]

#guard indexedSchema.syms =
  ({r, rTwo, uTwelve, tAux, tAuxThree} :
    Finset ProgramNames)
#guard indexedSchema.arity? rTwo = some 1
#guard indexedSchema.arity? uTwelve = some 1
#guard indexedSchema.arity? tAuxThree = some 2
#guard indexedSchema.arity? u = none

def indexedGuard : QFAssertExpr Data indexedSchema :=
  programQF![ (R_2 ⊆ R) ∧ (T_aux_3 = (U_12 × R_2)) ]

#guard indexedGuard.toRaw =
  RawGuard.and
    (.subset (.rel rTwo) (.rel r))
    (.eq (.rel tAuxThree) (.prod (.rel uTwelve) (.rel rTwo)))

def indexedCmd : Cmd Data indexedSchema :=
  programCmd![
    { ExecSchema: indexedSchema }
    { R_2 := R; T_aux_3 := U_12 × R_2 }
  ]

/- Bound auxiliaries may carry a positive index as well. -/
def indexedBound : AssertExpr Data programSchema :=
  programAssert![ ∃ R_aux_2 . (R_aux_2 ⊆ R) ]

#guard indexedBound.fullSchema.arity?
  (.auxiliarySymbol ⟨"R", by decide⟩ 2) = some 1

------------------------------------------------------------
-- Assertions and Guards
------------------------------------------------------------

def inputPre : AssertExpr Data programSchema :=
  programAssert![ (R ⊆ U) ∨ (U = ∅) ]

def inputPost : AssertExpr Data programSchema :=
  programAssert![ (R ⊆ U) ∧ (T_aux = (U × U)) ]

/- `R_aux` inherits arity `1` from `R`. -/
def boundPre : AssertExpr Data programSchema :=
  programAssert![
    ∃ {R_aux} . (R_aux ⊆ R) ∧ (U = R_aux) ]

def boundPreSingle : AssertExpr Data programSchema :=
  programAssert![ ∃ R_aux . (R_aux ⊆ R) ]

#guard boundPre.fullSchema.arity? rAux = some 1

def loopGuard : QFAssertExpr Data programSchema :=
  programQF![ T_aux ≠ (U × U) ]

------------------------------------------------------------
-- Commands
------------------------------------------------------------

def inputCmd : Cmd Data programSchema :=
  programCmd![
    { ExecSchema: programSchema }
    {
      T_aux := ∅;
      U := R;
      WHILE T_aux ≠ (U × U) DO
        T_aux := U × U;
        U := U ∪ (π[0] (σ[#0 = #1] T_aux))
      END
    }
  ]

#guard inputCmd.framedLoopParts?.isSome

def inlineSchemaCmd : Cmd Data programSchema :=
  programCmd![
    { ExecSchema: {R, U} (arity: 1), T_aux (arity: 2) }
    { U := R; T_aux := R × U }
  ]

------------------------------------------------------------
-- Block Commands Without a Trailing Semicolon
------------------------------------------------------------

def loopThenAssignSemicolon : Cmd Data programSchema :=
  programCmd![
    { ExecSchema: programSchema }
    {
      WHILE T_aux ≠ (U × U) DO
        T_aux := U × U
      END;
      U := ∅
    }
  ]

def loopThenAssign : Cmd Data programSchema :=
  programCmd![
    { ExecSchema: programSchema }
    {
      WHILE T_aux ≠ (U × U) DO
        T_aux := U × U
      END
      U := ∅
    }
  ]

example : loopThenAssign = loopThenAssignSemicolon :=
  rfl

/- The continuation nests to the right, as `;` does. -/
def loopThenTwoSemicolons : Cmd Data programSchema :=
  programCmd![
    { ExecSchema: programSchema }
    {
      T_aux := ∅;
      WHILE T_aux ≠ (U × U) DO
        T_aux := U × U
      END;
      U := ∅;
      T_aux := R × U
    }
  ]

def loopThenTwo : Cmd Data programSchema :=
  programCmd![
    { ExecSchema: programSchema }
    {
      T_aux := ∅;
      WHILE T_aux ≠ (U × U) DO
        T_aux := U × U
      END
      U := ∅;
      T_aux := R × U
    }
  ]

example : loopThenTwo = loopThenTwoSemicolons :=
  rfl

def branchThenLoopSemicolon : Cmd Data programSchema :=
  programCmd![
    { ExecSchema: programSchema }
    {
      IF R = ∅ THEN U := ∅ ELSE U := R END;
      WHILE T_aux ≠ (U × U) DO
        T_aux := U × U
      END;
      SKIP
    }
  ]

def branchThenLoop : Cmd Data programSchema :=
  programCmd![
    { ExecSchema: programSchema }
    {
      IF R = ∅ THEN U := ∅ ELSE U := R END
      WHILE T_aux ≠ (U × U) DO
        T_aux := U × U
      END
      SKIP
    }
  ]

example : branchThenLoop = branchThenLoopSemicolon :=
  rfl

def lowercaseBlocksSemicolon : Cmd Data programSchema :=
  programCmd![
    { ExecSchema: programSchema }
    {
      if R = ∅ then U := ∅ else U := R end;
      while T_aux ≠ (U × U) do
        T_aux := U × U
      end;
      skip
    }
  ]

def lowercaseBlocks : Cmd Data programSchema :=
  programCmd![
    { ExecSchema: programSchema }
    {
      if R = ∅ then U := ∅ else U := R end
      while T_aux ≠ (U × U) do
        T_aux := U × U
      end
      skip
    }
  ]

example : lowercaseBlocks = lowercaseBlocksSemicolon :=
  rfl

/- Inside a branch, the juxtaposition stays in the branch. -/
def nestedContinuationSemicolon : Cmd Data programSchema :=
  programCmd![
    { ExecSchema: programSchema }
    {
      IF R = ∅ THEN
        WHILE T_aux ≠ (U × U) DO T_aux := U × U END;
        U := ∅
      ELSE
        U := R
      END
    }
  ]

def nestedContinuation : Cmd Data programSchema :=
  programCmd![
    { ExecSchema: programSchema }
    {
      IF R = ∅ THEN
        WHILE T_aux ≠ (U × U) DO T_aux := U × U END
        U := ∅
      ELSE
        U := R
      END
    }
  ]

example : nestedContinuation = nestedContinuationSemicolon :=
  rfl

------------------------------------------------------------
-- Rejected Identifiers
------------------------------------------------------------

/--
error: index zero is spelled without a suffix; write 'R' instead of 'R_0'
-/
#guard_msgs in
def rejectedZero : UnnamedSchema ProgramNames :=
  programSch![ R_0 (arity: 1) ]

/--
error: index zero is spelled without a suffix; write 'T_aux' instead of 'T_aux_0'
-/
#guard_msgs in
def rejectedAuxiliaryZero : UnnamedSchema ProgramNames :=
  programSch![ T_aux_0 (arity: 2) ]

/--
error: index suffix of 'R_02' must be a canonical decimal numeral without leading zeros
-/
#guard_msgs in
def rejectedLeadingZero : UnnamedSchema ProgramNames :=
  programSch![ R_02 (arity: 1) ]

/--
error: expected an alphabetical relation name, got 'R1'
-/
#guard_msgs in
def rejectedBase : UnnamedSchema ProgramNames :=
  programSch![ R1 (arity: 1) ]

/--
error: expected relation name X, X_n, or auxiliary name X_aux, X_aux_n, got 'R_foo'
-/
#guard_msgs in
def rejectedSuffix : UnnamedSchema ProgramNames :=
  programSch![ R_foo (arity: 1) ]

/- A positive index outside the schema fails membership. -/
/--
error: unknown relation or non-computable relation arity
-/
#guard_msgs in
def rejectedIndexedCmd : QFAssertExpr Data programSchema :=
  programQF![ U_2 = ∅ ]

/--
error: bound program-name relations must be auxiliary names such as 'R_aux'
-/
#guard_msgs in
def rejectedBound : AssertExpr Data programSchema :=
  programAssert![ ∃ {R} . (R = ∅) ]

------------------------------------------------------------
-- Name Spelling
------------------------------------------------------------

/-
  `ProgramNames.spell` is the one surface spelling of a
  relation, and the notation reads exactly it back. Every
  printer in the library renders a name through it, so
  these pins are what makes a printed program a program
  `programSch!`, `programAssert!` and `programCmd!` accept.

  A flag is the single name outside that round trip.
  `⟨flag id index⟩` is an explicit display-only marker that
  no notation reads back: a relation identifier is one Lean
  identifier over alphabetical characters and `_`, and this
  form carries brackets and spaces, so a preprocessed
  program carrying flags is visibly display-only rather
  than silently spelled as a name that would read back as a
  different one. Certificates never contain flags, and
  `FixedAmbient.ClauseNotation` fails closed on one. Pass
  7.8e owns choosing a notation-parsable flag spelling
  shared by `spell`, `ClauseNotation` and `programSch!`.
-/

def tThree : ProgramNames :=
  .programSymbol ⟨"T", by decide⟩ 3

def tBase : ProgramNames :=
  .programSymbol ⟨"T", by decide⟩ 0

#guard ProgramNames.spell tBase == "T"

#guard ProgramNames.spell tThree == "T_3"

#guard ProgramNames.spell tAux == "T_aux"

#guard ProgramNames.spell tAuxThree == "T_aux_3"

#guard ProgramNames.spell (.flagSymbol 2 1) ==
  "flag_2_1"

#guard ProgramNames.spell (.flagSymbol 0 0) ==
  "flag_0_0"

#guard WhielNames.spell (.ordinary tAux) == "T_aux"

#guard WhielNames.spell (.prophecy tAux) == "T_aux∞"

/- The notation reads those four spellings back. -/
def spelledSchema : UnnamedSchema ProgramNames :=
  programSch![ {T_3, T_aux_3, T_aux, T} (arity: 2) ]

#guard spelledSchema.syms =
  ({tThree, tAuxThree, tAux, tBase} : Finset ProgramNames)

#guard [tBase, tThree, tAux, tAuxThree].all fun X =>
  spelledSchema.arity? X == some 2

end ProgramNotation
end Tests
end Whiel
