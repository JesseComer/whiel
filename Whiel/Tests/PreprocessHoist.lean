-- Author: Jesse Comer
import Whiel.Preprocess.Hoist
import Whiel.Concrete.Notation

/-
  Kernel-checked pins for the conditional hoist of the
  generic preprocessor.

  Four small programs over `ProgramNames` exercise the four
  cases of `Whiel.Preprocess.hoistIte`: both branches with a
  loop, a loop-free else-branch, a loop-free then-branch,
  and the flag-free case where neither branch has a loop.
  Every constructed unfolding is compared against a
  hand-written expected raw command by `decide +kernel`, so
  the transformation is checked to reduce by evaluation on
  concrete inputs.
-/

open Whiel.Concrete

set_option linter.hashCommand false

namespace Whiel

namespace Tests

namespace PreprocessHoist

open Whiel.Preprocess

------------------------------------------------------------
-- Schema, Flag, And Framed Loops
------------------------------------------------------------

/- Five unary program relations. -/
def base : UnnamedSchema ProgramNames :=
  programSch![ {R, T, U, V, W} (arity: 1) ]

/- The one flag identifier the hoist draws. -/
def flagIds : List Nat := [0]

/- The flag extension the hoist works over. -/
def ext : UnnamedSchema ProgramNames :=
  flagExt base flagIds

def hExt : ext.extensionOf base :=
  flagExt_extensionOf base flagIds

def f : FlagSym ext :=
  flagSymOf base flagIds 0 (by decide) (by decide)

/- On a raw input schema the flag supply starts at zero. -/
#guard flagSeed base == 0

/- The source guard of the conditional. -/
def srcGuard : Guard Data base :=
  programQF![ T ≠ ∅ ]

/- A framed loop over `R` and `U`, the then-branch. -/
def loopOne : Framed Data base where
  init := programCmd![ { ExecSchema: base } { U := ∅ } ]
  guard := programQF![ R ≠ ∅ ]
  body := programCmd![ { ExecSchema: base } { R := ∅ } ]
  close := programCmd![ { ExecSchema: base } { U := R } ]

/- A framed loop over `V` and `W`, the else-branch. -/
def loopTwo : Framed Data base where
  init := programCmd![ { ExecSchema: base } { W := ∅ } ]
  guard := programQF![ V ≠ ∅ ]
  body := programCmd![ { ExecSchema: base } { V := ∅ } ]
  close := programCmd![ { ExecSchema: base } { W := V } ]

/- A loop-free then-branch source. -/
def straightThen : Cmd Data base :=
  programCmd![ { ExecSchema: base } { V := R } ]

/- A loop-free else-branch source. -/
def straightElse : Cmd Data base :=
  programCmd![ { ExecSchema: base } { W := R } ]

/- The loop-free sources really are loop-free. -/
#guard decide (LoopFree straightThen)

#guard decide (LoopFree straightElse)

#guard ! decide (LoopFree loopOne.unfold)

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
-- Both Branches Contain A Loop
------------------------------------------------------------

/-
  The expected unfolding of the general hoist, written out
  as the note's Definition "Hoist" prescribes.
-/
def expectedGeneralRaw : RawCmd ProgramNames Data :=
  .seq
    (.ite (rawG srcGuard)
      (.seq
        (rawOf
          programCmd![ { ExecSchema: base } { U := ∅ } ])
        (rawRaise 0))
      (.seq
        (rawOf
          programCmd![ { ExecSchema: base } { W := ∅ } ])
        (rawLower 0)))
    (.seq
      (.«while»
        (.or
          (.and (rawTest 0)
            (rawG programQF![ R ≠ ∅ ]))
          (.and (.not (rawTest 0))
            (rawG programQF![ V ≠ ∅ ])))
        (.ite (rawTest 0)
          (rawOf
            programCmd![
              { ExecSchema: base } { R := ∅ } ])
          (rawOf
            programCmd![
              { ExecSchema: base } { V := ∅ } ])))
      (.ite (rawTest 0)
        (rawOf
          programCmd![ { ExecSchema: base } { U := R } ])
        (rawOf
          programCmd![ { ExecSchema: base } { W := V } ])))

theorem generalCase_toRaw :
    (hoistIte hExt f srcGuard loopOne loopTwo
        false false).unfold.toRaw =
      expectedGeneralRaw := by
  decide +kernel

theorem generalCase_equivMod :
    EquivMod hExt
      (.ite srcGuard loopOne.unfold loopTwo.unfold)
      (hoistIte hExt f srcGuard loopOne loopTwo
        false false).unfold :=
  hoistIte_equivMod hExt f (by decide) srcGuard loopOne
    loopTwo false false
    (fun h => by cases h)
    (fun h => by cases h)

theorem generalCase_records_branch
    {s t : Instance Data ext}
    (hRun :
      Cmd.BigStep
        (hoistIte hExt f srcGuard loopOne loopTwo
          false false).unfold s t) :
    (f.Up t ↔ srcGuard.eval (project hExt s)) :=
  hoistIte_flag_records_branch hExt f (by decide) srcGuard
    loopOne loopTwo false false rfl
    (fun h => by cases h)
    (fun h => by cases h)
    hRun

------------------------------------------------------------
-- A Loop-Free Else-Branch
------------------------------------------------------------

/-
  The loop-free else-branch goes to the suffix under the
  flag; the prefix keeps both branches.
-/
def expectedThenLoopRaw : RawCmd ProgramNames Data :=
  .seq
    (.ite (rawG srcGuard)
      (.seq
        (rawOf
          programCmd![ { ExecSchema: base } { U := ∅ } ])
        (rawRaise 0))
      (.seq .skip (rawLower 0)))
    (.seq
      (.«while»
        (.and (rawTest 0) (rawG programQF![ R ≠ ∅ ]))
        (rawOf
          programCmd![ { ExecSchema: base } { R := ∅ } ]))
      (.ite (rawTest 0)
        (rawOf
          programCmd![ { ExecSchema: base } { U := R } ])
        (rawOf straightElse)))

theorem thenLoopCase_toRaw :
    (hoistIte hExt f srcGuard loopOne
        (Framed.base straightElse)
        false true).unfold.toRaw =
      expectedThenLoopRaw := by
  decide +kernel

theorem thenLoopCase_equivMod :
    EquivMod hExt
      (.ite srcGuard loopOne.unfold
        (Framed.base straightElse).unfold)
      (hoistIte hExt f srcGuard loopOne
        (Framed.base straightElse) false true).unfold :=
  hoistIte_equivMod hExt f (by decide) srcGuard loopOne
    (Framed.base straightElse) false true
    (fun h => by cases h)
    (fun _ => Framed.isBase_base straightElse)

theorem thenLoopCase_records_branch
    {s t : Instance Data ext}
    (hRun :
      Cmd.BigStep
        (hoistIte hExt f srcGuard loopOne
          (Framed.base straightElse)
          false true).unfold s t) :
    (f.Up t ↔ srcGuard.eval (project hExt s)) :=
  hoistIte_flag_records_branch hExt f (by decide) srcGuard
    loopOne (Framed.base straightElse) false true rfl
    (fun h => by cases h)
    (fun _ => Framed.isBase_base straightElse)
    hRun

------------------------------------------------------------
-- A Loop-Free Then-Branch
------------------------------------------------------------

/- The mirror case, with the flag read the other way. -/
def expectedElseLoopRaw : RawCmd ProgramNames Data :=
  .seq
    (.ite (rawG srcGuard)
      (.seq .skip (rawRaise 0))
      (.seq
        (rawOf
          programCmd![ { ExecSchema: base } { W := ∅ } ])
        (rawLower 0)))
    (.seq
      (.«while»
        (.and (.not (rawTest 0))
          (rawG programQF![ V ≠ ∅ ]))
        (rawOf
          programCmd![ { ExecSchema: base } { V := ∅ } ]))
      (.ite (rawTest 0)
        (rawOf straightThen)
        (rawOf
          programCmd![ { ExecSchema: base } { W := V } ])))

theorem elseLoopCase_toRaw :
    (hoistIte hExt f srcGuard
        (Framed.base straightThen) loopTwo
        true false).unfold.toRaw =
      expectedElseLoopRaw := by
  decide +kernel

theorem elseLoopCase_equivMod :
    EquivMod hExt
      (.ite srcGuard (Framed.base straightThen).unfold
        loopTwo.unfold)
      (hoistIte hExt f srcGuard
        (Framed.base straightThen) loopTwo
        true false).unfold :=
  hoistIte_equivMod hExt f (by decide) srcGuard
    (Framed.base straightThen) loopTwo true false
    (fun _ => Framed.isBase_base straightThen)
    (fun h => by cases h)

theorem elseLoopCase_records_branch
    {s t : Instance Data ext}
    (hRun :
      Cmd.BigStep
        (hoistIte hExt f srcGuard
          (Framed.base straightThen) loopTwo
          true false).unfold s t) :
    (f.Up t ↔ srcGuard.eval (project hExt s)) :=
  hoistIte_flag_records_branch hExt f (by decide) srcGuard
    (Framed.base straightThen) loopTwo true false rfl
    (fun _ => Framed.isBase_base straightThen)
    (fun h => by cases h)
    hRun

------------------------------------------------------------
-- The Flag-Free Case
------------------------------------------------------------

/-
  With neither branch carrying a loop the conditional is
  its own base framed loop, and no flag is drawn.
-/
def expectedFlagFreeRaw : RawCmd ProgramNames Data :=
  .seq .skip
    (.seq (.«while» .«false» .skip)
      (.ite (rawG srcGuard)
        (rawOf straightThen)
        (rawOf straightElse)))

theorem flagFreeCase_toRaw :
    (hoistIte hExt f srcGuard
        (Framed.base straightThen)
        (Framed.base straightElse)
        true true).unfold.toRaw =
      expectedFlagFreeRaw := by
  decide +kernel

theorem flagFreeCase_equivMod :
    EquivMod hExt
      (.ite srcGuard (Framed.base straightThen).unfold
        (Framed.base straightElse).unfold)
      (hoistIte hExt f srcGuard
        (Framed.base straightThen)
        (Framed.base straightElse) true true).unfold :=
  hoistIte_equivMod hExt f (by decide) srcGuard
    (Framed.base straightThen)
    (Framed.base straightElse) true true
    (fun _ => Framed.isBase_base straightThen)
    (fun _ => Framed.isBase_base straightElse)

------------------------------------------------------------
-- Reduction Of The Transformation
------------------------------------------------------------

/-
  Each case of the dispatcher reduces to its operation by
  `rfl`, on concrete inputs and with no proof obligation.
-/
theorem hoistIte_reduces_general :
    hoistIte hExt f srcGuard loopOne loopTwo false false =
      hoistGeneral hExt f srcGuard loopOne loopTwo :=
  rfl

theorem hoistIte_reduces_thenLoop :
    hoistIte hExt f srcGuard loopOne
        (Framed.base straightElse) false true =
      hoistThenLoop hExt f srcGuard loopOne
        (Framed.base straightElse) :=
  rfl

theorem hoistIte_reduces_elseLoop :
    hoistIte hExt f srcGuard (Framed.base straightThen)
        loopTwo true false =
      hoistElseLoop hExt f srcGuard
        (Framed.base straightThen) loopTwo :=
  rfl

theorem hoistIte_reduces_flagFree :
    hoistIte hExt f srcGuard (Framed.base straightThen)
        (Framed.base straightElse) true true =
      (hoistFlagFree srcGuard (Framed.base straightThen)
        (Framed.base straightElse)).retagOn hExt :=
  rfl

/- Every case keeps the loop-free components loop-free. -/
theorem hoistIte_parts_general :
    (hoistIte hExt f srcGuard loopOne loopTwo
      false false).LoopFreeParts :=
  hoistIte_loopFreeParts hExt f srcGuard loopOne loopTwo
    false false (by decide) (by decide)

theorem hoistIte_parts_thenLoop :
    (hoistIte hExt f srcGuard loopOne
        (Framed.base straightElse)
        false true).LoopFreeParts :=
  hoistIte_loopFreeParts hExt f srcGuard loopOne
    (Framed.base straightElse) false true (by decide)
    (by decide)

theorem hoistIte_parts_flagFree :
    (hoistIte hExt f srcGuard (Framed.base straightThen)
      (Framed.base straightElse) true true).LoopFreeParts :=
  hoistIte_loopFreeParts hExt f srcGuard
    (Framed.base straightThen) (Framed.base straightElse)
    true true (by decide) (by decide)

/- The hoisted unfolding has exactly one loop. -/
#guard loops
  (hoistIte hExt f srcGuard loopOne loopTwo
    false false).unfold == 1

#guard loops
  (hoistIte hExt f srcGuard loopOne
    (Framed.base straightElse) false true).unfold == 1

#guard loops
  (hoistIte hExt f srcGuard (Framed.base straightThen)
    (Framed.base straightElse) true true).unfold == 1

end PreprocessHoist

end Tests

end Whiel
