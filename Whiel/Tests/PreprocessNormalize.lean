-- Author: Jesse Comer
import Whiel.Preprocess.Normalize
import Whiel.Concrete.Notation

/-
  Kernel-checked pins for the normalizer of the generic
  preprocessor.

  Eight small programs over `ProgramNames` exercise every
  clause of `Whiel.Preprocess.normalizeAux`: a loop-free
  program, a single loop, two sequenced independent loops,
  two dependent loops, a loop inside a conditional, a loop
  inside a loop, the idempotent nesting, and one program
  combining a merge, a hoist and a flattening. Each
  unfolding is compared against a hand-written expected raw
  command by `decide +kernel` where the expected command is
  short enough to write out, and every program is pinned by
  its drawn flag identifiers, which equal the flag budget.
-/

open Whiel.Concrete

set_option linter.hashCommand false

namespace Whiel

namespace Tests

namespace PreprocessNormalize

open Whiel.Preprocess

------------------------------------------------------------
-- The Input Schema And The Corpus
------------------------------------------------------------

/- Five unary program relations. -/
def base : UnnamedSchema ProgramNames :=
  programSch![ {R, T, U, V, W} (arity: 1) ]

/- On a raw input schema the flag supply starts at zero. -/
#guard flagSeed base == 0

/- A wholly loop-free program. -/
def progFree : Cmd Data base :=
  programCmd![ { ExecSchema: base } { U := R; V := R } ]

/- One loop with a loop-free body. -/
def progLoop : Cmd Data base :=
  programCmd![ { ExecSchema: base }
    { WHILE R ≠ ∅ DO R := ∅ END } ]

/- Two sequenced loops on disjoint relations. -/
def progIndep : Cmd Data base :=
  programCmd![ { ExecSchema: base }
    { (WHILE R ≠ ∅ DO R := ∅ END) ;
      (WHILE V ≠ ∅ DO V := ∅ END) } ]

/- Two sequenced loops that share a relation. -/
def progDep : Cmd Data base :=
  programCmd![ { ExecSchema: base }
    { (WHILE R ≠ ∅ DO R := ∅ END) ;
      (WHILE R ≠ ∅ DO U := R END) } ]

/- A loop in one branch of a conditional. -/
def progIte : Cmd Data base :=
  programCmd![ { ExecSchema: base }
    { IF T ≠ ∅ THEN
        WHILE R ≠ ∅ DO R := ∅ END
      ELSE
        U := R
      END } ]

/- A loop inside a loop, on different guard terms. -/
def progNested : Cmd Data base :=
  programCmd![ { ExecSchema: base }
    { WHILE T ≠ ∅ DO
        WHILE R ≠ ∅ DO R := ∅ END
      END } ]

/- A loop inside a loop, on the same guard term. -/
def progIdem : Cmd Data base :=
  programCmd![ { ExecSchema: base }
    { WHILE T ≠ ∅ DO
        WHILE T ≠ ∅ DO R := ∅ END
      END } ]

/- A merge, a hoist and a flattening in one program. -/
def progAll : Cmd Data base :=
  programCmd![ { ExecSchema: base }
    { IF T ≠ ∅ THEN
        (WHILE R ≠ ∅ DO R := ∅ END) ;
        (WHILE R ≠ ∅ DO U := R END)
      ELSE
        WHILE V ≠ ∅ DO
          WHILE W ≠ ∅ DO W := ∅ END
        END
      END } ]

/-
  The note's Section 5 worked example: `C_a ; C_b`, where
  `C_a` is a loop whose body is a conditional with a loop in
  its then-branch, `C_b` is a second loop, and `C_b` assigns
  the relation `C_a`'s guard reads, so the two sources are
  not independent and the sequence goes to the general
  merge. It exercises a flattening, a one-sided hoist and a
  merge at once.
-/
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
-- The Source-Level Tests And The Flag Budget
------------------------------------------------------------

#guard decide (LoopFree progFree)

#guard ! decide (LoopFree progLoop)

/- The three loops the sequences are built from. -/
def loopR : Cmd Data base :=
  programCmd![ { ExecSchema: base }
    { WHILE R ≠ ∅ DO R := ∅ END } ]

def loopV : Cmd Data base :=
  programCmd![ { ExecSchema: base }
    { WHILE V ≠ ∅ DO V := ∅ END } ]

def loopUR : Cmd Data base :=
  programCmd![ { ExecSchema: base }
    { WHILE R ≠ ∅ DO U := R END } ]

def loopWorkedA : Cmd Data base :=
  programCmd![ { ExecSchema: base }
    { WHILE T ≠ ∅ DO
        IF U ≠ ∅ THEN
          WHILE R ≠ ∅ DO R := ∅ END
        ELSE
          V := R
        END
      END } ]

def loopWorkedB : Cmd Data base :=
  programCmd![ { ExecSchema: base }
    { WHILE W ≠ ∅ DO T := ∅ END } ]

#guard independentCheck loopR loopV

#guard ! independentCheck loopR loopUR

#guard flagBudget progFree == 0

#guard flagBudget progLoop == 0

#guard flagBudget progIndep == 0

#guard flagBudget progDep == 2

#guard flagBudget progIte == 1

#guard flagBudget progNested == 1

#guard flagBudget progIdem == 0

#guard flagBudget progAll == 4

/-
  The note's Section 5 arithmetic: three source loops, four
  flags and two two-loop applications.
-/
#guard loops progWorked == 3

#guard flagBudget progWorked == 4

#guard twoLoopApplications progWorked == 2

#guard ! independentCheck loopWorkedA loopWorkedB

/- The identifiers drawn are exactly the budget's. -/
#guard (normalize progFree).ids == []

#guard (normalize progLoop).ids == []

#guard (normalize progIndep).ids == []

#guard (normalize progDep).ids == [0, 1]

#guard (normalize progIte).ids == [0]

#guard (normalize progNested).ids == [0]

#guard (normalize progIdem).ids == []

#guard (normalize progAll).ids == [0, 1, 2, 3]

#guard (normalize progWorked).ids == [0, 1, 2, 3]

#guard (normalize progAll).ids ==
  flagIds (flagSeed base) (flagBudget progAll)

#guard (normalize progDep).ids.length ==
  flagBudget progDep

#guard (normalize progIte).ids.length ==
  flagBudget progIte

#guard (normalize progNested).ids.length ==
  flagBudget progNested

#guard (normalize progAll).ids.length ==
  flagBudget progAll

/- Every normalized unfolding has exactly one loop. -/
#guard loops (normalize progFree).loop.unfold == 1

#guard loops (normalize progLoop).loop.unfold == 1

#guard loops (normalize progIndep).loop.unfold == 1

#guard loops (normalize progDep).loop.unfold == 1

#guard loops (normalize progIte).loop.unfold == 1

#guard loops (normalize progNested).loop.unfold == 1

#guard loops (normalize progIdem).loop.unfold == 1

#guard loops (normalize progAll).loop.unfold == 1

#guard loops (normalize progWorked).loop.unfold == 1

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

/- The guards and assignments of the corpus. -/
def gR : RawGuard ProgramNames Data :=
  rawG programQF![ R ≠ ∅ ]

def gT : RawGuard ProgramNames Data :=
  rawG programQF![ T ≠ ∅ ]

def gV : RawGuard ProgramNames Data :=
  rawG programQF![ V ≠ ∅ ]

def aR : RawCmd ProgramNames Data :=
  rawOf programCmd![ { ExecSchema: base } { R := ∅ } ]

def aV : RawCmd ProgramNames Data :=
  rawOf programCmd![ { ExecSchema: base } { V := ∅ } ]

def aU : RawCmd ProgramNames Data :=
  rawOf programCmd![ { ExecSchema: base } { U := R } ]

/- The extra guards and assignments of Section 5. -/
def gU : RawGuard ProgramNames Data :=
  rawG programQF![ U ≠ ∅ ]

def gW : RawGuard ProgramNames Data :=
  rawG programQF![ W ≠ ∅ ]

def aVR : RawCmd ProgramNames Data :=
  rawOf programCmd![ { ExecSchema: base } { V := R } ]

def aT : RawCmd ProgramNames Data :=
  rawOf programCmd![ { ExecSchema: base } { T := ∅ } ]

------------------------------------------------------------
-- The Loop-Free Clause And The Single Loop
------------------------------------------------------------

/- Loop-free code becomes the base framed loop. -/
def expectedFreeRaw : RawCmd ProgramNames Data :=
  .seq .skip
    (.seq (.«while» .«false» .skip) (rawOf progFree))

theorem progFree_toRaw :
    (normalize progFree).loop.unfold.toRaw =
      expectedFreeRaw := by
  decide +kernel

/-
  A loop with a loop-free body is already a framed loop:
  the normalizer returns it unchanged up to the empty
  prefix and suffix of the base convention.
-/
def expectedLoopRaw : RawCmd ProgramNames Data :=
  .seq .skip (.seq (.«while» gR aR) .skip)

theorem progLoop_toRaw :
    (normalize progLoop).loop.unfold.toRaw =
      expectedLoopRaw := by
  decide +kernel

/- The idempotent clause discards the outer loop. -/
def expectedIdemRaw : RawCmd ProgramNames Data :=
  .seq .skip (.seq (.«while» gT aR) .skip)

theorem progIdem_toRaw :
    (normalize progIdem).loop.unfold.toRaw =
      expectedIdemRaw := by
  decide +kernel

------------------------------------------------------------
-- The Product Of Two Independent Loops
------------------------------------------------------------

/- Independent sources take the flag-free product. -/
def expectedIndepRaw : RawCmd ProgramNames Data :=
  .seq .skip
    (.seq
      (.«while» (.or gR gV)
        (.seq (.ite gR aR .skip) (.ite gV aV .skip)))
      .skip)

theorem progIndep_toRaw :
    (normalize progIndep).loop.unfold.toRaw =
      expectedIndepRaw := by
  decide +kernel

------------------------------------------------------------
-- The General Merge Of Two Dependent Loops
------------------------------------------------------------

/- Dependent sources take the two-flag general merge. -/
def expectedDepRaw : RawCmd ProgramNames Data :=
  .seq (.seq (rawRaise 0) (rawLower 1))
    (.seq
      (.«while» (.or (rawTest 0) (rawTest 1))
        (.ite (rawTest 0)
          (.ite gR aR
            (.seq (rawLower 0) (rawRaise 1)))
          (.ite gR aU (rawLower 1))))
      .skip)

theorem progDep_toRaw :
    (normalize progDep).loop.unfold.toRaw =
      expectedDepRaw := by
  decide +kernel

------------------------------------------------------------
-- The Hoist Of A Loop In A Branch
------------------------------------------------------------

/-
  Only the then-branch carries a loop, so the guard is
  `f ∧ H`, the body is the branch's body, and the loop-free
  else-branch goes to the suffix under the flag.
-/
def expectedIteRaw : RawCmd ProgramNames Data :=
  .seq
    (.ite gT (rawRaise 0) (rawLower 0))
    (.seq
      (.«while» (.and (rawTest 0) gR) aR)
      (.ite (rawTest 0) .skip aU))

theorem progIte_toRaw :
    (normalize progIte).loop.unfold.toRaw =
      expectedIteRaw := by
  decide +kernel

------------------------------------------------------------
-- The Flattening Of A Loop Inside A Loop
------------------------------------------------------------

/- The inner flag phases the two loops. -/
def expectedNestedRaw : RawCmd ProgramNames Data :=
  .seq (rawLower 0)
    (.seq
      (.«while» (.or (rawTest 0) gT)
        (.ite (rawTest 0)
          (.ite gR aR (rawLower 0))
          (rawRaise 0)))
      .skip)

theorem progNested_toRaw :
    (normalize progNested).loop.unfold.toRaw =
      expectedNestedRaw := by
  decide +kernel

------------------------------------------------------------
-- The Worked Example Of Section 5
------------------------------------------------------------

/-
  Step 2, the hoist with the loop-free else-branch and the
  flag `f_0`, as the final clean leaves it: the prefix keeps
  both branches and loses the empty prefix of the inner
  loop's base framed loop; the suffix keeps its `skip`,
  which is a branch of a conditional and says that the
  then-branch has nothing to close.
-/
def workedHoistInit : RawCmd ProgramNames Data :=
  .ite gU (rawRaise 0) (rawLower 0)

def workedHoistClose : RawCmd ProgramNames Data :=
  .ite (rawTest 0) .skip aVR

def workedHoistGuard : RawGuard ProgramNames Data :=
  .and (rawTest 0) gR

/- Step 3, the flattening with the flag `f_1`. -/
def workedFlattenGuard : RawGuard ProgramNames Data :=
  .or (rawTest 1) gT

def workedFlattenBody : RawCmd ProgramNames Data :=
  .ite (rawTest 1)
    (.ite workedHoistGuard aR
      (.seq (rawLower 1) workedHoistClose))
    (.seq workedHoistInit (rawRaise 1))

/-
  Step 5, the general merge with the flags `f_2` and `f_3`,
  and step 6, the clean: the `S_1; P_2` between the two
  loops was `skip; skip` and is gone, and the suffix is the
  whole suffix rather than an element of a sequence.
-/
def expectedWorkedRaw : RawCmd ProgramNames Data :=
  .seq
    (.seq (rawLower 1) (.seq (rawRaise 2) (rawLower 3)))
    (.seq
      (.«while» (.or (rawTest 2) (rawTest 3))
        (.ite (rawTest 2)
          (.ite workedFlattenGuard workedFlattenBody
            (.seq (rawLower 2) (rawRaise 3)))
          (.ite gW aT (rawLower 3))))
      .skip)

theorem progWorked_toRaw :
    (normalize progWorked).loop.unfold.toRaw =
      expectedWorkedRaw := by
  decide +kernel

------------------------------------------------------------
-- The Normalization Theorem On The Corpus
------------------------------------------------------------

/-
  Every program of the corpus is equivalent modulo its
  drawn flags to the unfolding of its normal form, in the
  arbitrary-start form.
-/
theorem progFree_equivMod :
    EquivMod
      (flagExt_extensionOf base (normalize progFree).ids)
      progFree (normalize progFree).loop.unfold :=
  normalize_equivMod progFree

theorem progLoop_equivMod :
    EquivMod
      (flagExt_extensionOf base (normalize progLoop).ids)
      progLoop (normalize progLoop).loop.unfold :=
  normalize_equivMod progLoop

theorem progIndep_equivMod :
    EquivMod
      (flagExt_extensionOf base (normalize progIndep).ids)
      progIndep (normalize progIndep).loop.unfold :=
  normalize_equivMod progIndep

theorem progDep_equivMod :
    EquivMod
      (flagExt_extensionOf base (normalize progDep).ids)
      progDep (normalize progDep).loop.unfold :=
  normalize_equivMod progDep

theorem progIte_equivMod :
    EquivMod
      (flagExt_extensionOf base (normalize progIte).ids)
      progIte (normalize progIte).loop.unfold :=
  normalize_equivMod progIte

theorem progNested_equivMod :
    EquivMod
      (flagExt_extensionOf base (normalize progNested).ids)
      progNested (normalize progNested).loop.unfold :=
  normalize_equivMod progNested

theorem progIdem_equivMod :
    EquivMod
      (flagExt_extensionOf base (normalize progIdem).ids)
      progIdem (normalize progIdem).loop.unfold :=
  normalize_equivMod progIdem

theorem progWorked_equivMod :
    EquivMod
      (flagExt_extensionOf base (normalize progWorked).ids)
      progWorked (normalize progWorked).loop.unfold :=
  normalize_equivMod progWorked

theorem progAll_equivMod :
    EquivMod
      (flagExt_extensionOf base (normalize progAll).ids)
      progAll (normalize progAll).loop.unfold :=
  normalize_equivMod progAll

/- The footprint of the combined program. -/
theorem progAll_footprint :
    (normalize progAll).loop.unfold.symbols ⊆
        progAll.symbols ∪
          flagNames (normalize progAll).ids ∧
      (normalize progAll).loop.unfold.assignedSymbols ⊆
        progAll.assignedSymbols ∪
          flagNames (normalize progAll).ids :=
  normalize_footprint progAll

/-
  The combined program's framed loop has loop-free parts.
-/
theorem progAll_loopFreeParts :
    (normalize progAll).loop.LoopFreeParts :=
  normalize_loopFreeParts progAll

/-
  Proposition "Loop count" on the combined program: the
  count of two-loop applications and the budget bound.
-/
#guard twoLoopApplications progAll ==
  max (loops progAll - 1) 0

#guard flagBudget progAll ≤
  2 * loops progAll + branchingLoops progAll

end PreprocessNormalize

end Tests

end Whiel
