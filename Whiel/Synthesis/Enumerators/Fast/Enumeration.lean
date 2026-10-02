-- Author: Jesse Comer
import Whiel.Synthesis.DisjunctiveClause.FastContract
import Whiel.Synthesis.Enumerators.WaveMachinery
import Mathlib.Data.List.Sublists

/-
  First replaceable fast realization of the protected
  reference enumerator.

  The implementation builds only one exact formula wave.
  It never materializes or filters an earlier formula
  slice. It retains only the prior sorted literal frontier.

  This module is benchmark-blind. Its executable inputs are
  a typed alphabet and its own frontier state.

  Main declarations:
    * `State` and `initialState`
    * `advance`
    * `run` and `outputThrough`
-/

------------------------------------------------------------
-- Fresh-Member Sublists
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Enumerators

namespace Fast

open DisjunctiveClause

/- Stable identity of this replaceable realization. -/
def realizationId : String := "lean-fast-v1"

/- Stable version of this replaceable realization. -/
def realizationVersion : Nat := 1

end Fast

end Enumerators

end Synthesis

end Whiel

------------------------------------------------------------
-- Incremental Clause Waves
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Enumerators

namespace Fast

open DisjunctiveClause

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}
variable [LinearOrder A] [LinearOrder D]

open CanonicalEnumeration

/- Minimal state retained between exact waves. -/
structure State where
  nextStage : Nat := 0
  priorLiterals : List (Literal D Γ) := []

/- Initial frontier before stage zero. -/
def initialState : State (D := D) (Γ := Γ) := {}

/- One exact typed wave and its successor state. -/
structure Batch where
  stage : Nat
  representations : List (LiteralList D Γ)
  formulas : List (QFAssertExpr D Γ)
  freshTraversalStats : TraversalStats
  /-
    Cheap, stable work-unit population. Each emitted
    exact-width representation counts once. Each recursive
    incremental fresh-member state counts once. This does
    not claim to count Mathlib's internal recursion.
  -/
  generatorWorkUnits : Nat
  nextState : State (D := D) (Γ := Γ)

/- Exact representations and counters for one precomputed literal frontier. -/
def waveResultFromCurrent
    (state : State (D := D) (Γ := Γ))
    (current : List (Literal D Γ)) :
    RepresentationResult (D := D) (Γ := Γ) :=
  match state.nextStage with
  | 0 =>
      let exact := current.sublistsLen 0
      { representations := exact
        stats := {}
        exactWidthOutputs := exact.length }
  | stage + 1 =>
      let exact := current.sublistsLen (stage + 1)
      let introduced :=
        introducedRepresentationResult state.priorLiterals
          current (stage + 1)
      { representations := exact ++ introduced.representations
        stats := introduced.stats
        exactWidthOutputs := exact.length }

/- Exact representations and counters introduced at one stage. -/
def waveResult
    (alphabet : Alphabet D Γ)
    (state : State (D := D) (Γ := Γ)) :
    RepresentationResult (D := D) (Γ := Γ) :=
  waveResultFromCurrent state
    (literalOrder alphabet (referenceParameters state.nextStage))

/-
  Exact representations introduced at the state's stage.

  Stage zero introduces width zero. A positive stage adds
  the newly permitted exact width and every lower-width
  representation containing a newly eligible literal.
-/
def waveRepresentations
    (alphabet : Alphabet D Γ)
    (state : State (D := D) (Γ := Γ)) :
    List (LiteralList D Γ) :=
  (waveResult alphabet state).representations

/- Advance the exact incremental enumerator by one stage. -/
def advance
    (alphabet : Alphabet D Γ)
    (state : State (D := D) (Γ := Γ)) :
    Batch (D := D) (Γ := Γ) :=
  let stage := state.nextStage
  let current :=
    literalOrder alphabet (referenceParameters stage)
  let wave := waveResultFromCurrent state current
  let representations := wave.representations
  { stage
    representations
    formulas := representations.map FullEnumeration.decode
    freshTraversalStats := wave.stats
    generatorWorkUnits :=
      wave.exactWidthOutputs + wave.stats.visitedNodes
    nextState :=
      { nextStage := stage + 1
        priorLiterals := current } }

/-
  Run a finite number of actual `advance` calls and retain
  their cumulative typed output.
-/
def run
    (alphabet : Alphabet D Γ) :
    Nat → State (D := D) (Γ := Γ) ×
      List (QFAssertExpr D Γ)
| 0 => (initialState, [])
| completedStages + 1 =>
    let prior := run alphabet completedStages
    let batch := advance alphabet prior.1
    (batch.nextState, prior.2 ++ batch.formulas)

/- Cumulative output after the given number of stages. -/
def outputThrough
    (alphabet : Alphabet D Γ)
    (completedStages : Nat) :
    List (QFAssertExpr D Γ) :=
  (run alphabet completedStages).2

end Fast

end Enumerators

end Synthesis

end Whiel
