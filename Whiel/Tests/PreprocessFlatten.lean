-- Author: Jesse Comer
import Whiel.Preprocess.Flatten
import Whiel.Concrete.Notation

/-
  Kernel-checked pins for the loop flattening of the
  generic preprocessor.

  Three small programs over `ProgramNames` exercise the
  three cases of `Whiel.Preprocess.flattenWhile`: a source
  body that carries a loop, a loop-free source body, and the
  idempotent nesting of a loop inside a loop on the same
  guard term. Every constructed unfolding is compared
  against a hand-written expected raw command by
  `decide +kernel`, so the transformation is checked to
  reduce by evaluation on concrete inputs.
-/

open Whiel.Concrete

set_option linter.hashCommand false

namespace Whiel

namespace Tests

namespace PreprocessFlatten

open Whiel.Preprocess

------------------------------------------------------------
-- Schema, Flag, And The Inner Framed Loop
------------------------------------------------------------

/- Five unary program relations. -/
def base : UnnamedSchema ProgramNames :=
  programSch![ {R, T, U, V, W} (arity: 1) ]

/- The one flag identifier the flattening draws. -/
def drawn : List Nat := [0]

/- The flag extension the flattening works over. -/
def ext : UnnamedSchema ProgramNames :=
  flagExt base drawn

def hExt : ext.extensionOf base :=
  flagExt_extensionOf base drawn

def inner : FlagSym ext :=
  flagSymOf base drawn 0 (by decide) (by decide)

/- On a raw input schema the flag supply starts at zero. -/
#guard flagSeed base == 0

/- The outer loop's guard. -/
def srcGuard : Guard Data base :=
  programQF![ T ≠ ∅ ]

/- The framed loop of the source body. -/
def loopBody : Framed Data base where
  init := programCmd![ { ExecSchema: base } { U := ∅ } ]
  guard := programQF![ R ≠ ∅ ]
  body := programCmd![ { ExecSchema: base } { R := ∅ } ]
  close := programCmd![ { ExecSchema: base } { W := U } ]

/- A loop-free source body. -/
def straightBody : Cmd Data base :=
  programCmd![ { ExecSchema: base } { R := ∅ } ]

#guard decide (LoopFree straightBody)

#guard ! decide (LoopFree loopBody.unfold)

------------------------------------------------------------
-- Raw Syntax For The Expected Commands
------------------------------------------------------------

/- Raw syntax for a base-schema command. -/
def rawOf (C : Cmd Data base) : RawCmd ProgramNames Data :=
  C.toRaw

/- Raw syntax for a base-schema guard. -/
def rawG (G : Guard Data base) :
    RawGuard ProgramNames Data :=
  G.toRaw

/- Raise the flag with the given identifier. -/
def rawRaise (i : Nat) : RawCmd ProgramNames Data :=
  .assign (flagName i) .top

/- Lower the flag with the given identifier. -/
def rawLower (i : Nat) : RawCmd ProgramNames Data :=
  .assign (flagName i) (.empty 0)

/-
  Test the flag with the given identifier: the note's
  Definition "Flag" guard, the flag against the nullary
  singleton.
-/
def rawTest (i : Nat) : RawGuard ProgramNames Data :=
  .eq (.rel (flagName i)) .top

------------------------------------------------------------
-- The Source Body Carries A Loop
------------------------------------------------------------

/-
  The expected unfolding of the general flattening,
  written as the note's Definition "Flatten" prescribes:
  the prefix lowers the flag, the guard is the disjunction,
  the body is the two-phase inner loop, and the suffix is
  empty.
-/
def expectedGeneralRaw : RawCmd ProgramNames Data :=
  .seq (rawLower 0)
    (.seq
      (.«while»
        (.or (rawTest 0) (rawG srcGuard))
        (.ite (rawTest 0)
          (.ite (rawG programQF![ R ≠ ∅ ])
            (rawOf
              programCmd![
                { ExecSchema: base } { R := ∅ } ])
            (.seq (rawLower 0)
              (rawOf
                programCmd![
                  { ExecSchema: base } { W := U } ])))
          (.seq
            (rawOf
              programCmd![
                { ExecSchema: base } { U := ∅ } ])
            (rawRaise 0))))
      .skip)

theorem generalCase_toRaw :
    (flattenWhile hExt inner srcGuard loopBody
        false false).unfold.toRaw =
      expectedGeneralRaw := by
  decide +kernel

theorem generalCase_equivMod :
    EquivMod hExt
      (.«while» srcGuard loopBody.unfold)
      (flattenWhile hExt inner srcGuard loopBody
        false false).unfold :=
  flattenWhile_equivMod hExt inner (by decide) srcGuard
    loopBody false false
    (fun h => by cases h)
    (fun h => by cases h)

theorem generalCase_flag_down
    {s t : Instance Data ext}
    (hRun :
      Cmd.BigStep
        (flattenGeneral hExt inner srcGuard
          loopBody).unfold s t) :
    ¬ inner.Up t :=
  flattenGeneral_flag_down hExt inner (by decide) srcGuard
    loopBody hRun

------------------------------------------------------------
-- A Loop-Free Source Body
------------------------------------------------------------

/-
  A loop whose source body is loop-free is already a framed
  loop, and no flag is drawn.
-/
def expectedLoopFreeRaw : RawCmd ProgramNames Data :=
  .seq .skip
    (.seq
      (.«while» (rawG srcGuard) (rawOf straightBody))
      .skip)

theorem loopFreeCase_toRaw :
    (flattenWhile hExt inner srcGuard
        (Framed.base straightBody)
        false true).unfold.toRaw =
      expectedLoopFreeRaw := by
  decide +kernel

theorem loopFreeCase_equivMod :
    EquivMod hExt
      (.«while» srcGuard (Framed.base straightBody).unfold)
      (flattenWhile hExt inner srcGuard
        (Framed.base straightBody) false true).unfold :=
  flattenWhile_equivMod hExt inner (by decide) srcGuard
    (Framed.base straightBody) false true
    (fun h => by cases h)
    (fun _ => Framed.isBase_base straightBody)

------------------------------------------------------------
-- Idempotent Nesting
------------------------------------------------------------

/-
  The framed loop of `while T ≠ ∅ do R := ∅ end`, the shape
  the idempotent clause receives from the recursion.
-/
def idemLoop : Framed Data base :=
  flattenLoopFree srcGuard straightBody

/-
  Lemma "Idempotent nesting" on this corpus: an outer loop
  on the same guard term adds nothing.
-/
theorem idem_bigStepEquiv :
    Cmd.BigStepEquiv
      (.«while» srcGuard idemLoop.unfold)
      idemLoop.unfold := by
  have hUnfold :
      Cmd.BigStepEquiv idemLoop.unfold
        (.«while» srcGuard straightBody) :=
    (flattenLoopFree_bigStepEquiv srcGuard
      straightBody).symm
  refine
    Cmd.BigStepEquiv.trans
      (Cmd.BigStepEquiv.trans
        (bigStepEquiv_while srcGuard hUnfold) ?_)
      hUnfold.symm
  exact while_idem_bigStepEquiv srcGuard straightBody

/- The idempotent clause returns its input, retagged. -/
theorem idemCase_toRaw :
    (flattenWhile hExt inner srcGuard idemLoop
        true false).unfold.toRaw =
      rawOf idemLoop.unfold := by
  decide +kernel

theorem idemCase_equivMod :
    EquivMod hExt
      (.«while» srcGuard idemLoop.unfold)
      (flattenWhile hExt inner srcGuard idemLoop
        true false).unfold :=
  flattenWhile_equivMod hExt inner (by decide) srcGuard
    idemLoop true false
    (fun _ => idem_bigStepEquiv)
    (fun h => by cases h)

------------------------------------------------------------
-- Reduction Of The Transformation
------------------------------------------------------------

/-
  Each case of the dispatcher reduces to its operation by
  `rfl`, on concrete inputs and with no proof obligation.
-/
theorem flattenWhile_reduces_general :
    flattenWhile hExt inner srcGuard loopBody false false =
      flattenGeneral hExt inner srcGuard loopBody :=
  rfl

theorem flattenWhile_reduces_loopFree :
    flattenWhile hExt inner srcGuard
        (Framed.base straightBody) false true =
      (flattenLoopFree srcGuard
        (Framed.base straightBody).close).retagOn hExt :=
  rfl

theorem flattenWhile_reduces_idem :
    flattenWhile hExt inner srcGuard idemLoop true false =
      (flattenIdem idemLoop).retagOn hExt :=
  rfl

/- Every case keeps the loop-free components loop-free. -/
theorem flattenWhile_parts_general :
    (flattenWhile hExt inner srcGuard loopBody
      false false).LoopFreeParts :=
  flattenWhile_loopFreeParts hExt inner srcGuard loopBody
    false false (by decide)

theorem flattenWhile_parts_loopFree :
    (flattenWhile hExt inner srcGuard
      (Framed.base straightBody)
      false true).LoopFreeParts :=
  flattenWhile_loopFreeParts hExt inner srcGuard
    (Framed.base straightBody) false true (by decide)

theorem flattenWhile_parts_idem :
    (flattenWhile hExt inner srcGuard idemLoop
      true false).LoopFreeParts :=
  flattenWhile_loopFreeParts hExt inner srcGuard idemLoop
    true false (by decide)

/- The flattened unfolding has exactly one loop. -/
#guard loops
  (flattenWhile hExt inner srcGuard loopBody
    false false).unfold == 1

#guard loops
  (flattenWhile hExt inner srcGuard
    (Framed.base straightBody) false true).unfold == 1

#guard loops
  (flattenWhile hExt inner srcGuard idemLoop
    true false).unfold == 1

end PreprocessFlatten

end Tests

end Whiel
