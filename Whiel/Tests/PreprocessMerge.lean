-- Author: Jesse Comer
import Whiel.Preprocess.Merge
import Whiel.Concrete.Notation

/-
  Kernel-checked pins for the sequence merge of the generic
  preprocessor.

  Four small programs over `ProgramNames` exercise the four
  cases of `Whiel.Preprocess.mergeSeq`: a loop-free first
  source into the prefix, a loop-free second source into
  the suffix, the flag-free product of independent sources,
  and the two-flag general merge. Every constructed command
  is compared against a hand-written expected command by
  `decide +kernel`, so the transformation is checked to
  reduce by evaluation on concrete inputs.
-/

open Whiel.Concrete

set_option linter.hashCommand false

namespace Whiel

namespace Tests

namespace PreprocessMerge

open Whiel.Preprocess

------------------------------------------------------------
-- Schema, Flags, And Framed Loops
------------------------------------------------------------

/- Four unary program relations. -/
def base : UnnamedSchema ProgramNames :=
  programSch![ {R, U, V, W} (arity: 1) ]

/- The two flag identifiers the general merge draws. -/
def flagIds : List Nat := [0, 1]

/- The flag extension the general merge works over. -/
def ext : UnnamedSchema ProgramNames :=
  flagExt base flagIds

def hExt : ext.extensionOf base :=
  flagExt_extensionOf base flagIds

def f₁ : FlagSym ext :=
  flagSymOf base flagIds 0 (by decide) (by decide)

def f₂ : FlagSym ext :=
  flagSymOf base flagIds 1 (by decide) (by decide)

/- On a raw input schema the flag supply starts at zero. -/
#guard flagSeed base == 0

/- A framed loop over `R` and `U`. -/
def loopOne : Framed Data base where
  init := programCmd![ { ExecSchema: base } { U := ∅ } ]
  guard := programQF![ R ≠ ∅ ]
  body := programCmd![ { ExecSchema: base } { R := ∅ } ]
  close := programCmd![ { ExecSchema: base } { U := R } ]

/- A framed loop over `V` and `W`, independent of it. -/
def loopTwo : Framed Data base where
  init := programCmd![ { ExecSchema: base } { W := ∅ } ]
  guard := programQF![ V ≠ ∅ ]
  body := programCmd![ { ExecSchema: base } { V := ∅ } ]
  close := programCmd![ { ExecSchema: base } { W := V } ]

/- The same loop, made dependent by reading `R`. -/
def loopThree : Framed Data base where
  init := programCmd![ { ExecSchema: base } { V := R } ]
  guard := programQF![ V ≠ ∅ ]
  body := programCmd![ { ExecSchema: base } { V := ∅ } ]
  close := programCmd![ { ExecSchema: base } { W := V } ]

/- A loop-free source, entering as a base framed loop. -/
def straight : Cmd Data base :=
  programCmd![ { ExecSchema: base } { V := R } ]

/- The independence check is a list computation. -/
#guard independentCheck loopOne.unfold loopTwo.unfold

#guard ! independentCheck loopOne.unfold loopThree.unfold

/- The loop-free source really is loop-free. -/
#guard decide (LoopFree straight)

#guard ! decide (LoopFree loopOne.unfold)

------------------------------------------------------------
-- Case (i): Loop-Free Code Before A Loop
------------------------------------------------------------

/- The expected result of the loop-free-first case. -/
def expectedPrefix : Framed Data base where
  init :=
    programCmd![ { ExecSchema: base } { V := R; W := ∅ } ]
  guard := programQF![ V ≠ ∅ ]
  body := programCmd![ { ExecSchema: base } { V := ∅ } ]
  close := programCmd![ { ExecSchema: base } { W := V } ]

theorem prefixCase_toRaw :
    (mergeSeq hExt f₁ f₂ (Framed.base straight) loopTwo
        true false false).unfold.toRaw =
      expectedPrefix.unfold.toRaw := by
  decide +kernel

theorem prefixCase_equivMod :
    EquivMod hExt
      (.seq (Framed.base straight).unfold loopTwo.unfold)
      (mergeSeq hExt f₁ f₂ (Framed.base straight) loopTwo
        true false false).unfold :=
  mergeSeq_equivMod hExt f₁ f₂ (by decide) (by decide)
    (by decide) (Framed.base straight) loopTwo
    true false false
    (fun _ => Framed.isBase_base straight)
    (fun h => by cases h)
    (fun h => by cases h)

------------------------------------------------------------
-- Case (ii): Loop-Free Code After A Loop
------------------------------------------------------------

/- The expected result of the loop-free-second case. -/
def expectedSuffix : Framed Data base where
  init := programCmd![ { ExecSchema: base } { U := ∅ } ]
  guard := programQF![ R ≠ ∅ ]
  body := programCmd![ { ExecSchema: base } { R := ∅ } ]
  close :=
    programCmd![ { ExecSchema: base } { U := R; V := R } ]

theorem suffixCase_toRaw :
    (mergeSeq hExt f₁ f₂ loopOne (Framed.base straight)
        false true false).unfold.toRaw =
      expectedSuffix.unfold.toRaw := by
  decide +kernel

theorem suffixCase_equivMod :
    EquivMod hExt
      (.seq loopOne.unfold (Framed.base straight).unfold)
      (mergeSeq hExt f₁ f₂ loopOne (Framed.base straight)
        false true false).unfold :=
  mergeSeq_equivMod hExt f₁ f₂ (by decide) (by decide)
    (by decide) loopOne (Framed.base straight)
    false true false
    (fun h => by cases h)
    (fun _ => Framed.isBase_base straight)
    (fun h => by cases h)

------------------------------------------------------------
-- The Flag-Free Product
------------------------------------------------------------

/- The expected result of the independent case. -/
def expectedProduct : Framed Data base where
  init :=
    programCmd![ { ExecSchema: base } { U := ∅; W := ∅ } ]
  guard := programQF![ (R ≠ ∅) ∨ (V ≠ ∅) ]
  body :=
    programCmd![
      { ExecSchema: base }
      {
        IF R ≠ ∅ THEN R := ∅ ELSE SKIP END;
        IF V ≠ ∅ THEN V := ∅ ELSE SKIP END
      } ]
  close :=
    programCmd![ { ExecSchema: base } { U := R; W := V } ]

theorem productCase_toRaw :
    (mergeSeq hExt f₁ f₂ loopOne loopTwo
        false false true).unfold.toRaw =
      expectedProduct.unfold.toRaw := by
  decide +kernel

theorem productCase_equivMod :
    EquivMod hExt
      (.seq loopOne.unfold loopTwo.unfold)
      (mergeSeq hExt f₁ f₂ loopOne loopTwo
        false false true).unfold :=
  mergeSeq_equivMod hExt f₁ f₂ (by decide) (by decide)
    (by decide) loopOne loopTwo false false true
    (fun h => by cases h)
    (fun h => by cases h)
    (fun _ => independent_of_check (by decide))

------------------------------------------------------------
-- The General Merge
------------------------------------------------------------

/- Raw syntax for a base-schema command. -/
def rawOf (C : Cmd Data base) : RawCmd ProgramNames Data :=
  C.toRaw

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

/-
  The expected unfolding of the general merge, written out
  as the note's Definition "Merge" case (iii) prescribes.
-/
def expectedGeneralRaw : RawCmd ProgramNames Data :=
  .seq
    (.seq
      (rawOf
        programCmd![ { ExecSchema: base } { U := ∅ } ])
      (.seq (rawRaise 0) (rawLower 1)))
    (.seq
      (.«while» (.or (rawTest 0) (rawTest 1))
        (.ite (rawTest 0)
          (.ite
            ((programQF![ R ≠ ∅ ] :
              Guard Data base).toRaw)
            (rawOf
              programCmd![
                { ExecSchema: base } { R := ∅ } ])
            (.seq (rawLower 0)
              (.seq (rawRaise 1)
                (.seq
                  (rawOf
                    programCmd![
                      { ExecSchema: base } { U := R } ])
                  (rawOf
                    programCmd![
                      { ExecSchema: base }
                      { V := R } ])))))
          (.ite
            ((programQF![ V ≠ ∅ ] :
              Guard Data base).toRaw)
            (rawOf
              programCmd![
                { ExecSchema: base } { V := ∅ } ])
            (rawLower 1))))
      (rawOf
        programCmd![ { ExecSchema: base } { W := V } ]))

theorem generalCase_toRaw :
    (mergeSeq hExt f₁ f₂ loopOne loopThree
        false false false).unfold.toRaw =
      expectedGeneralRaw := by
  decide +kernel

theorem generalCase_equivMod :
    EquivMod hExt
      (.seq loopOne.unfold loopThree.unfold)
      (mergeSeq hExt f₁ f₂ loopOne loopThree
        false false false).unfold :=
  mergeSeq_equivMod hExt f₁ f₂ (by decide) (by decide)
    (by decide) loopOne loopThree false false false
    (fun h => by cases h)
    (fun h => by cases h)
    (fun h => by cases h)

theorem generalCase_flags_down
    {s t : Instance Data ext}
    (hRun :
      Cmd.BigStep
        (mergeGeneral hExt f₁ f₂ loopOne
          loopThree).unfold s t) :
    ¬ f₁.Up t ∧ ¬ f₂.Up t :=
  mergeGeneral_flags_down hExt f₁ f₂ (by decide)
    (by decide) (by decide) loopOne loopThree hRun

------------------------------------------------------------
-- Reduction Of The Transformation
------------------------------------------------------------

/-
  Each case of the dispatcher reduces to its operation by
  `rfl`, on concrete inputs and with no proof obligation.
-/
theorem mergeSeq_reduces_prefix :
    mergeSeq hExt f₁ f₂ (Framed.base straight) loopTwo
        true false false =
      (mergeIntoPrefix (Framed.base straight)
        loopTwo).retagOn hExt :=
  rfl

theorem mergeSeq_reduces_suffix :
    mergeSeq hExt f₁ f₂ loopOne (Framed.base straight)
        false true false =
      (mergeIntoSuffix loopOne
        (Framed.base straight)).retagOn hExt :=
  rfl

theorem mergeSeq_reduces_product :
    mergeSeq hExt f₁ f₂ loopOne loopTwo
        false false true =
      (mergeProduct loopOne loopTwo).retagOn hExt :=
  rfl

theorem mergeSeq_reduces_general :
    mergeSeq hExt f₁ f₂ loopOne loopThree
        false false false =
      mergeGeneral hExt f₁ f₂ loopOne loopThree :=
  rfl

/- Every case keeps the loop-free components loop-free. -/
theorem mergeSeq_parts_general :
    (mergeSeq hExt f₁ f₂ loopOne loopThree
      false false false).LoopFreeParts :=
  mergeSeq_loopFreeParts hExt f₁ f₂ loopOne loopThree
    false false false (by decide) (by decide)

theorem mergeSeq_parts_product :
    (mergeSeq hExt f₁ f₂ loopOne loopTwo
      false false true).LoopFreeParts :=
  mergeSeq_loopFreeParts hExt f₁ f₂ loopOne loopTwo
    false false true (by decide) (by decide)

/- The merged unfolding has exactly one loop. -/
#guard loops
  (mergeSeq hExt f₁ f₂ loopOne loopThree
    false false false).unfold == 1

#guard loops
  (mergeSeq hExt f₁ f₂ loopOne loopTwo
    false false true).unfold == 1

end PreprocessMerge

end Tests

end Whiel
