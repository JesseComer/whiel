-- Author: Jesse Comer
import Whiel.Preprocess.Transfer
import Whiel.Concrete.Notation

/-
  Kernel-checked pins for the preamble split and the
  preamble push.

  Three programs exercise the two cases of the note's
  Section 4.1: a prefix that is entirely safe, so nothing is
  pushed and no further flag is drawn; a prefix whose
  leading item reads its own assignment target, so the whole
  prefix is pushed under one more flag; and the note's
  Section 5 worked example, whose prefix is three
  assignments of constants to relations fresh for the
  precondition and for each other.
-/

open Whiel.Concrete

set_option linter.hashCommand false

namespace Whiel

namespace Tests

namespace PreprocessPreamble

open Whiel.Preprocess

------------------------------------------------------------
-- The Input Schema, Triple And Corpus
------------------------------------------------------------

/- Five unary program relations. -/
def base : UnnamedSchema ProgramNames :=
  programSch![ {R, T, U, V, W} (arity: 1) ]

/- A quantifier-free precondition over the input schema. -/
def pre : AssertExpr Data base :=
  programAssert![ (R ⊆ U) ]

#guard decide pre.NoBoundSymbols

theorem preNoBound : pre.NoBoundSymbols := by
  decide

/- A quantifier-free postcondition over the input schema. -/
def post : AssertExpr Data base :=
  programAssert![ (V ⊆ U) ]

theorem postNoBound : post.NoBoundSymbols := by
  decide

/-
  Two dependent loops: the general merge, whose prefix is
  two flag assignments to constants. Both are safe, so
  nothing is pushed.
-/
def progSafe : Cmd Data base :=
  programCmd![ { ExecSchema: base }
    { (WHILE R ≠ ∅ DO R := ∅ END) ;
      (WHILE R ≠ ∅ DO U := R END) } ]

/-
  The same program behind an assignment that reads its own
  target. Merge case (i) puts that assignment at the head of
  the prefix, where the quantifier-free strongest
  postcondition is undefined, so the whole prefix is pushed.
-/
def progPush : Cmd Data base :=
  programCmd![ { ExecSchema: base }
    { R := (R ∪ T) ;
      ((WHILE R ≠ ∅ DO R := ∅ END) ;
       (WHILE R ≠ ∅ DO U := R END)) } ]

/- The note's Section 5 worked example. -/
def progWorked : Cmd Data base :=
  programCmd![ { ExecSchema: base }
    { (WHILE T ≠ ∅ DO
        IF U ≠ ∅ THEN
          WHILE R ≠ ∅ DO R := ∅ END
        ELSE
          V := R
        END
      END) ;
      (WHILE W ≠ ∅ DO T := ∅ END) } ]

------------------------------------------------------------
-- The Split, Case By Case
------------------------------------------------------------

/- The safe prefix keeps everything and pushes nothing. -/
#guard (normalizedSplit progSafe pre
  preNoBound).push.isEmpty

#guard ! (normalizedSplit progSafe pre
  preNoBound).keep.isEmpty

/-
  With nothing pushed the flag set is the one the recursion
  drew, and no further identifier is taken.
-/
#guard (preprocess progSafe pre preNoBound).ids ==
  (normalize progSafe).ids

#guard (preprocess progSafe pre preNoBound).ids == [0, 1]

/-
  The obstructing prefix pushes: the leading assignment
  reads its own target, so the split keeps nothing and
  everything from that item onward goes into the body.
-/
#guard ! (normalizedSplit progPush pre
  preNoBound).push.isEmpty

#guard (normalizedSplit progPush pre
  preNoBound).keep.isEmpty

/- The push draws exactly one further identifier. -/
#guard (preprocess progPush pre preNoBound).ids ==
  (normalize progPush).ids ++ [normalizeNext progPush]

#guard (preprocess progPush pre preNoBound).ids ==
  [0, 1, 2]

#guard normalizeNext progPush == 2

/-
  The worked example's prefix is three assignments of
  constants to relations fresh for the precondition and for
  each other, so `m = k = 3`, nothing is pushed, and no
  fifth flag is drawn.
-/
#guard (normalizedSplit progWorked pre
  preNoBound).push.isEmpty

#guard (normalizedSplit progWorked pre
  preNoBound).keep.length == 3

#guard (preprocess progWorked pre preNoBound).ids ==
  [0, 1, 2, 3]

------------------------------------------------------------
-- The Same Pins In The Kernel
------------------------------------------------------------

/-
  The `#guard`s above run in the compiler's evaluator. The
  same facts are pinned here by `decide +kernel`, so the
  path from a source command to its preprocessed triple is
  checked to reduce in the kernel too, in both cases of the
  split.

  The repository's quantifier-free strongest postcondition
  tests `X ∈ pre.symbols ∨ X ∈ e.symbols` at an assignment,
  and those are `Finset` memberships. The split calls it
  once per item, so a `Finset` computation does enter the
  transformation --- inside the split's definedness test,
  not inside the loop transformation. It reduces, which is
  what these pins establish.
-/
theorem progSafe_ids :
    (preprocess progSafe pre preNoBound).ids = [0, 1] := by
  decide +kernel

theorem progSafe_split_push :
    (normalizedSplit progSafe pre preNoBound).push.length
      = 0 := by
  decide +kernel

theorem progSafe_loops :
    loops (preprocess progSafe pre preNoBound).loop.unfold
      = 1 := by
  decide +kernel

theorem progPush_ids :
    (preprocess progPush pre preNoBound).ids
      = [0, 1, 2] := by
  decide +kernel

theorem progPush_split_keep :
    (normalizedSplit progPush pre preNoBound).keep.length
      = 0 := by
  decide +kernel

theorem progPush_loops :
    loops (preprocess progPush pre preNoBound).loop.unfold
      = 1 := by
  decide +kernel

------------------------------------------------------------
-- The Shape And The Correctness Of The Output
------------------------------------------------------------

/- Every output is a framed loop with one loop. -/
#guard loops (preprocess progSafe pre
  preNoBound).loop.unfold == 1

#guard loops (preprocess progPush pre
  preNoBound).loop.unfold == 1

#guard loops (preprocess progWorked pre
  preNoBound).loop.unfold == 1

/-
  Theorem "Normalization" with Lemma "Push": each program is
  equivalent modulo the flags the whole transformation draws
  to the unfolding of its preprocessed framed loop.
-/
theorem progSafe_equivMod :
    EquivMod
      (flagExt_extensionOf base
        (preprocess progSafe pre preNoBound).ids)
      progSafe
      (preprocess progSafe pre preNoBound).loop.unfold :=
  preprocess_equivMod progSafe pre preNoBound

theorem progPush_equivMod :
    EquivMod
      (flagExt_extensionOf base
        (preprocess progPush pre preNoBound).ids)
      progPush
      (preprocess progPush pre preNoBound).loop.unfold :=
  preprocess_equivMod progPush pre preNoBound

theorem progWorked_equivMod :
    EquivMod
      (flagExt_extensionOf base
        (preprocess progWorked pre preNoBound).ids)
      progWorked
      (preprocess progWorked pre preNoBound).loop.unfold :=
  preprocess_equivMod progWorked pre preNoBound

/-
  Theorem "Transfer" on the pushed program: validity of the
  single-loop triple over the flag extension returns
  validity of the input triple over the input schema.
-/
theorem progPush_transfer
    (hValid :
      HoareValid
        (preprocess progPush pre preNoBound).pre
        (.«while»
          (preprocess progPush pre preNoBound).loop.guard
          (preprocess progPush pre preNoBound).loop.body)
        (closingAssertion
          (flagExt_extensionOf base
            (preprocess progPush pre preNoBound).ids)
          (preprocess progPush pre preNoBound).loop
          (preprocess_close_loopFree progPush pre
            preNoBound)
          post postNoBound)) :
    HoareValid pre.eval progPush post.eval :=
  preprocess_transfer progPush pre post preNoBound
    postNoBound hValid

/-
  The same on the worked example, where nothing is pushed.
-/
theorem progWorked_transfer
    (hValid :
      HoareValid
        (preprocess progWorked pre preNoBound).pre
        (.«while»
          (preprocess progWorked pre preNoBound).loop.guard
          (preprocess progWorked pre preNoBound).loop.body)
        (closingAssertion
          (flagExt_extensionOf base
            (preprocess progWorked pre preNoBound).ids)
          (preprocess progWorked pre preNoBound).loop
          (preprocess_close_loopFree progWorked pre
            preNoBound)
          post postNoBound)) :
    HoareValid pre.eval progWorked post.eval :=
  preprocess_transfer progWorked pre post preNoBound
    postNoBound hValid

end PreprocessPreamble

end Tests

end Whiel
