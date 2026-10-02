-- Author: Jesse Comer
import Whiel.Synthesis.Enumerators.Seeded.Enumeration

/-
  Participation-capped variant of the seeded two-stream
  realization.

  The singleton stream is unchanged: every literal of the
  seeded universe is still emitted as a width-one clause at
  the stage it first appears. Only the combine stream ---
  the width >= 2 wave machinery, whose exact-width output
  grows combinatorially with the participating universe ---
  is restricted: it draws its literals from an *admitted*
  set that starts at the seeds and grows by a bounded number
  of admissions per stage, taken in canonical order from the
  currently available combine universe.

  Because admission is cumulative, the admitted universe
  grows monotonically under set inclusion, which is exactly
  the growth pattern the fresh-member machinery already
  supports: freshness marks are membership-based, and both
  the prior and current frontiers are canonical sorts of
  finite sets. A schedule with unbounded cap eventually
  admits every literal, so finite-prefix reference coverage
  is preserved; the re-proof lives in
  `CappedCorrectness.lean`.

  Key definitions include:
    * `Capped.Schedule`
    * `Capped.admitStep`
    * `Capped.CappedState`
    * `Capped.advanceSeededCapped`
    * `Capped.outputThroughSeededCapped`
-/

------------------------------------------------------------
-- Admission Schedules
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Enumerators

namespace Capped

open DisjunctiveClause Seeded

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}
variable [LinearOrder A] [LinearOrder D]

local instance : LinearOrder (Literal D Γ) :=
  StructuralOrder.literalLinearOrder

open Fast

/- Stable identity of the capped seeded realization. -/
def realizationId : String := "lean-fast-v3-capped"

/-
  Stable version of the capped realization. Version 3 caps
  combine-stream participation behind a cumulative admitted
  set fed by a per-stage schedule.
-/
def realizationVersion : Nat := 3

/-
  A participation schedule: the inclusive size budget for
  the admitted combine universe, given the stage and the
  length of the currently available universe. Seeing the
  available length is what lets a schedule guarantee
  *admission totality* --- infinitely many stages whose
  budget covers the whole current universe --- which the
  coverage theorem requires: pure unboundedness is not
  enough, because the universe also grows without bound and
  canonical-order admission can be preempted indefinitely
  by smaller late-arriving literals.
-/
abbrev Schedule := Nat → Nat → Nat

/-
  The amnesty period of the default schedule: stages one
  short of a multiple of this admit the whole available
  universe.
-/
def amnestyPeriod : Nat := 8

/-
  The default schedule: seeds always participate, the
  non-seed allowance doubles each stage from a small base,
  and every `amnestyPeriod`-th stage is an amnesty that
  admits everything currently available. Early wide waves
  stay narrow; totality is structural rather than an
  arithmetic race against universe growth.
-/
def defaultSchedule (seedCount : Nat) : Schedule :=
  fun stage availableLength =>
    if (stage + 1) % amnestyPeriod = 0 then
      seedCount + availableLength
    else
      seedCount + 8 * 2 ^ stage

------------------------------------------------------------
-- Cumulative Admission
------------------------------------------------------------

/-
  Admit further literals from the available universe, in
  the order the available list presents them, until the
  admitted set reaches the stage budget. Previously admitted
  literals are never revoked.
-/
def admitStep
    (available : List (Literal D Γ))
    (admitted : Finset (Literal D Γ))
    (budget : Nat) :
    Finset (Literal D Γ) :=
  admitted ∪
    ((available.filter
      (fun literal => literal ∉ admitted)).take
        (budget - admitted.card)).toFinset

/- The canonical sorted view of an admitted set. -/
def admittedOrder
    (admitted : Finset (Literal D Γ)) :
    List (Literal D Γ) :=
  admitted.sort (· ≤ ·)

------------------------------------------------------------
-- Capped Two-Stream State
------------------------------------------------------------

/-
  Frontier state of the capped realization. The singleton
  frontier is a literal list as in the uncapped stream; the
  combine frontier is the admitted set itself, whose sorted
  view is the combine universe of the next wave.
-/
structure CappedState where
  nextStage : Nat := 0
  priorSingleton : List (Literal D Γ) := []
  admitted : Finset (Literal D Γ) := ∅

/- Initial capped frontier: only the seeds participate. -/
def initialCappedState
    (seeds : Finset (Literal D Γ)) :
    CappedState (D := D) (Γ := Γ) :=
  { admitted := seeds }

------------------------------------------------------------
-- Capped Advance
------------------------------------------------------------

/- One exact capped wave and its successor state. -/
structure CappedBatch where
  stage : Nat
  representations : List (LiteralList D Γ)
  formulas : List (QFAssertExpr D Γ)
  freshTraversalStats : TraversalStats
  generatorWorkUnits : Nat
  nextState : CappedState (D := D) (Γ := Γ)

/-
  Advance the capped seeded enumerator by one stage.

  The singleton stream advances exactly as in
  `advanceSeeded`. The combine stream first admits new
  literals under the stage budget and then runs the
  unchanged wave machinery over the sorted admitted
  universe: the prior frontier is the previous admitted
  sort, so the fresh marks single out precisely the
  newly admitted literals.
-/
def advanceSeededCapped
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (schedule : Schedule)
    (state : CappedState (D := D) (Γ := Γ)) :
    CappedBatch (D := D) (Γ := Γ) :=
  let stage := state.nextStage
  let curSingle := seededLiteralOrder seeds alphabet stage
  let available := combineLiteralOrder seeds alphabet stage
  let admitted :=
    admitStep available state.admitted
      (schedule stage available.length)
  let priorCombine := admittedOrder state.admitted
  let curCombine := admittedOrder admitted
  let wave :=
    seededWaveFromCurrent
      { nextStage := stage
        priorSingleton := state.priorSingleton
        priorCombine := priorCombine }
      curSingle curCombine
  let representations := wave.representations
  { stage
    representations
    formulas := representations.map FullEnumeration.decode
    freshTraversalStats := wave.stats
    generatorWorkUnits :=
      wave.exactWidthOutputs + wave.stats.visitedNodes
    nextState :=
      { nextStage := stage + 1
        priorSingleton := curSingle
        admitted } }

/- Run a finite number of capped stages. -/
def runSeededCapped
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (schedule : Schedule) :
    Nat → CappedState (D := D) (Γ := Γ) ×
      List (QFAssertExpr D Γ)
| 0 => (initialCappedState seeds, [])
| completedStages + 1 =>
    let prior :=
      runSeededCapped alphabet seeds schedule
        completedStages
    let batch :=
      advanceSeededCapped alphabet seeds schedule prior.1
    (batch.nextState, prior.2 ++ batch.formulas)

/- Cumulative capped output after the given stage count. -/
def outputThroughSeededCapped
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (schedule : Schedule)
    (completedStages : Nat) :
    List (QFAssertExpr D Γ) :=
  (runSeededCapped alphabet seeds schedule
    completedStages).2

end Capped

end Enumerators

end Synthesis

end Whiel
