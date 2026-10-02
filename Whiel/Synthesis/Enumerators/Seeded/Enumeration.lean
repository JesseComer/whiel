-- Author: Jesse Comer
import Whiel.Synthesis.Enumerators.Fast.Enumeration
import Whiel.Hoare.Preproc

/-
  Program-derived literal seeding and the slowed parameter
  schedule for the seeded fast realization.

  This file specifies how a normalized task contributes
  seeded literals: every relational-algebra expression that
  occurs in the loop guard, the loop-free body, or the
  quantifier-free views of the pre- and postcondition, is
  harvested together with all of its subexpressions; the
  seeded literals are the signed equality and containment
  comparisons between harvested expressions of equal arity,
  excluding reflexive comparisons.

  Seeds are genuine synthesis inputs: harvesting inspects
  only the normalized task, never task identity or catalog
  metadata, so the seeded realization remains benchmark
  blind.

  Key definitions include:
    * `Seeded.harvestedTerms`
    * `Seeded.seedLiterals`
    * `Seeded.seededParameters`
    * `Seeded.seededLiteralOrder`
    * `Seeded.advanceSeeded`

  Correctness and freshness for the seeded stream are
  proved in `SeededEnumerationCorrectness.lean` and
  `SeededEnumerationFreshness.lean`.
-/

------------------------------------------------------------
-- Raw Subexpression Closure
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Enumerators

namespace Seeded

open DisjunctiveClause

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- One raw expression together with every subexpression. -/
def rawSubexpressions : RawRAExpr A D → List (RawRAExpr A D)
| .top => [.top]
| .empty n => [.empty n]
| .rel X => [.rel X]
| .single d => [.single d]
| .select φ e =>
    .select φ e :: rawSubexpressions e
| .proj idxs e =>
    .proj idxs e :: rawSubexpressions e
| .prod e₁ e₂ =>
    .prod e₁ e₂ ::
      (rawSubexpressions e₁ ++ rawSubexpressions e₂)
| .union e₁ e₂ =>
    .union e₁ e₂ ::
      (rawSubexpressions e₁ ++ rawSubexpressions e₂)
| .diff e₁ e₂ =>
    .diff e₁ e₂ ::
      (rawSubexpressions e₁ ++ rawSubexpressions e₂)

/- Check one raw expression back into a term. -/
def checkedTerm (expr : RawRAExpr A D) :
    Option (Term D Γ) :=
  match h : expr.arity? Γ with
  | some arity =>
      some { arity, expr, wellFormed := h }
  | none => none

/- Every checked subexpression term of one typed source. -/
def termClosure
    {n : Nat} (e : RAExpr D Γ n) :
    List (Term D Γ) :=
  (rawSubexpressions e.expr).filterMap checkedTerm

------------------------------------------------------------
-- Task Harvesting
------------------------------------------------------------

/- Terms harvested from one quantifier-free formula. -/
def guardTerms : Guard D Γ → List (Term D Γ)
| .«true» => []
| .«false» => []
| .eq e₁ e₂ => termClosure e₁ ++ termClosure e₂
| .subset e₁ e₂ => termClosure e₁ ++ termClosure e₂
| .and φ ψ => guardTerms φ ++ guardTerms ψ
| .or φ ψ => guardTerms φ ++ guardTerms ψ
| .not φ => guardTerms φ

/- Terms harvested from assignment right-hand sides. -/
def cmdTerms : Cmd D Γ → List (Term D Γ)
| .skip => []
| .assign _ e => termClosure e
| .seq C₁ C₂ => cmdTerms C₁ ++ cmdTerms C₂
| .ite G C₁ C₂ =>
    guardTerms G ++ cmdTerms C₁ ++ cmdTerms C₂
| .«while» G C => guardTerms G ++ cmdTerms C

end Seeded

end Enumerators

end Synthesis

end Whiel

------------------------------------------------------------
-- Task Seeds
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Enumerators

namespace Seeded

open DisjunctiveClause

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}
variable {inputPre inputPost : AssertExpr D Γ}
variable {inputCmd : Cmd D Γ}

/- Every term the normalized task contributes. -/
def harvestedTerms
    (P : Hoare.Preproc inputPre inputCmd inputPost) :
    List (Term D P.outSchema) :=
  (guardTerms P.loopGuard ++
    guardTerms (P.loopPre.toQFOfNoBound P.loopPre_noBound) ++
    guardTerms
      (P.loopPost.toQFOfNoBound P.loopPost_noBound) ++
    cmdTerms P.loopBody).dedup

/- Signed non-reflexive comparisons between two terms. -/
def pairLiterals
    {Ω : UnnamedSchema A}
    (left right : Term D Ω) :
    List (Literal D Ω) :=
  if h : left.arity = right.arity then
    if left = right then []
    else
      [AtomKind.equality, AtomKind.containment].flatMap
        fun kind =>
          [LiteralSign.positive, LiteralSign.negative].map
            fun sign =>
              ⟨sign, Atom.ofTerms kind left right h⟩
  else []

/- The seeded literal set of one normalized task. -/
def seedLiterals
    (P : Hoare.Preproc inputPre inputCmd inputPost) :
    Finset (Literal D P.outSchema) :=
  let terms := harvestedTerms P
  (terms.flatMap fun left =>
    terms.flatMap fun right =>
      pairLiterals left right).toFinset

------------------------------------------------------------
-- Slowed Parameter Schedule
------------------------------------------------------------

/-
  Alternating growth. Odd stages raise the clause width;
  even stages raise the reference literal universe. Stage 1
  is therefore the seeded literals plus only the cost-zero
  reference atoms, at width 1; the reference stage-1
  universe arrives at stage 2 and width 2 only at stage 3.
  Seeded comparisons are quadratic in the harvested terms
  and reference universes are large from stage 1 onward, so
  both growth axes are delayed to keep early pools small.
-/
def seededWidth (stage : Nat) : Nat := (stage + 1) / 2

/- The reference universe index active at one stage. -/
def seededUniverseIndex (stage : Nat) : Nat := stage / 2

/-
  The lagged universe index from which width ≥ 2 waves draw
  their literals. Combinations lag the singleton universe by
  a factor of two in index steps, so early multi-literal
  waves range over seeds and low-cost reference literals
  only; every literal still reaches the combine universe at
  a later stage, so cofinal coverage is preserved.
-/
def combineIndex (stage : Nat) : Nat := stage / 4

def seededParameters (stage : Nat) : Parameters :=
  { referenceParameters (seededUniverseIndex stage) with
      maxClauseWidth := seededWidth stage }

/- The parameters realized by the combine stream. -/
def combineParameters (stage : Nat) : Parameters :=
  { referenceParameters (combineIndex stage) with
      maxClauseWidth := seededWidth stage }

/- The slowed schedule is still cofinal. -/
theorem seededParameters_isCofinal :
    ParameterSchedule.IsCofinal seededParameters := by
  intro parameters
  rcases referenceParameters_isCofinal parameters with
    ⟨firstStage, hDominates⟩
  refine ⟨2 * firstStage + 1, fun stage hStage => ?_⟩
  obtain ⟨hBases, hOperators, hKinds, hSigns, hOps,
      hSelection, hProjection, hArity, _⟩ :=
    hDominates (stage / 2) (by omega)
  have hWidth :=
    (hDominates firstStage (Nat.le_refl _)).2.2.2.2.2.2.2.2
  simp only [referenceParameters] at hWidth
  exact ⟨hBases, hOperators, hKinds, hSigns, hOps,
    hSelection, hProjection, hArity, by
      simp only [seededParameters, seededUniverseIndex,
        seededWidth]
      omega⟩

end Seeded

end Enumerators

end Synthesis

end Whiel

------------------------------------------------------------
-- Seeded Literal Universe And Waves
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Enumerators

namespace Seeded

open DisjunctiveClause

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}
variable [LinearOrder A] [LinearOrder D]

local instance : LinearOrder (Literal D Γ) :=
  StructuralOrder.literalLinearOrder

open Fast

/- Stable identity of the seeded replaceable realization. -/
def realizationId : String := "lean-fast-v2-seeded"

/-
  Stable version of the seeded realization. Version 2 is the
  two-stream schedule: width ≥ 2 waves draw from the lagged
  combine universe, singleton waves from the full universe.
-/
def realizationVersion : Nat := 2

/- Frontier state for the two-stream seeded enumerator. -/
structure SeededState where
  nextStage : Nat := 0
  priorSingleton : List (Literal D Γ) := []
  priorCombine : List (Literal D Γ) := []

/- Initial frontier before seeded stage zero. -/
def initialSeededState : SeededState (D := D) (Γ := Γ) := {}

/-
  The sorted universe at one parameter point: seeded literals
  united with the parameters' reference literals. Sorting
  reuses the canonical structural order, so one point has
  exactly one representative per literal.
-/
def universeAt
    (seeds : Finset (Literal D Γ))
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    List (Literal D Γ) :=
  (seeds ∪
    FullEnumeration.literals alphabet
      parameters).sort (· ≤ ·)

/- The singleton-stream universe active at one stage. -/
def seededLiteralOrder
    (seeds : Finset (Literal D Γ))
    (alphabet : Alphabet D Γ)
    (stage : Nat) :
    List (Literal D Γ) :=
  universeAt seeds alphabet (seededParameters stage)

/- The combine-stream universe active at one stage. -/
def combineLiteralOrder
    (seeds : Finset (Literal D Γ))
    (alphabet : Alphabet D Γ)
    (stage : Nat) :
    List (Literal D Γ) :=
  universeAt seeds alphabet (combineParameters stage)

/-
  The singleton-stream wave: every literal is emitted as a
  width-one representation exactly once, at the stage its
  universe index first contains it. Stage zero instead emits
  the single width-zero representation.
-/
def singletonWave
    (priorSingleton current : List (Literal D Γ)) :
    RepresentationResult (D := D) (Γ := Γ) :=
  introducedRepresentationResult priorSingleton current 2

/-
  The combine-stream wave: all representations of width at
  least two, drawn from the lagged combine universe. A
  width-raising stage into width ≥ 2 emits the exact new
  width plus the fresh-literal representations below it; any
  other stage emits only fresh-literal representations at
  widths 2 through the current width. Width-one and
  width-zero representations never come from this stream, so
  the two streams are disjoint by representation length.
-/
def combineWave
    (priorWidth : Nat)
    (priorCombine current : List (Literal D Γ))
    (newWidth : Nat) :
    RepresentationResult (D := D) (Γ := Γ) :=
  if priorWidth < newWidth then
    if 2 ≤ newWidth then
      { representations :=
          current.sublistsLen newWidth ++
            (introducedRepresentationResult
              priorCombine current
              newWidth).representations.filter
                fun representation =>
                  2 ≤ representation.length
        stats :=
          (introducedRepresentationResult
            priorCombine current newWidth).stats
        exactWidthOutputs :=
          (current.sublistsLen newWidth).length }
    else
      { representations := []
        stats := {} }
  else
    { representations :=
        (introducedRepresentationResult
          priorCombine current
          (newWidth + 1)).representations.filter
            fun representation =>
              2 ≤ representation.length
      stats :=
        (introducedRepresentationResult
          priorCombine current (newWidth + 1)).stats }

/-
  The exact two-stream wave for one seeded stage. Stage zero
  emits the width-zero representation and every width-one
  singleton of the initial universe outright, so both prior
  frontiers can be recorded uniformly at every stage and the
  fresh-member machinery needs no stage exception.
-/
def seededWaveFromCurrent
    (state : SeededState (D := D) (Γ := Γ))
    (curSingle curCombine : List (Literal D Γ)) :
    RepresentationResult (D := D) (Γ := Γ) :=
  match state.nextStage with
  | 0 =>
      let exact :=
        curSingle.sublistsLen 0 ++ curSingle.sublistsLen 1
      { representations := exact
        stats := {}
        exactWidthOutputs := exact.length }
  | stage + 1 =>
      let singles :=
        singletonWave state.priorSingleton curSingle
      let combined :=
        combineWave (seededWidth stage)
          state.priorCombine curCombine
          (seededWidth (stage + 1))
      { representations :=
          singles.representations ++
            combined.representations
        stats := singles.stats.add combined.stats
        exactWidthOutputs := combined.exactWidthOutputs }

/- One exact seeded wave and its successor state. -/
structure SeededBatch where
  stage : Nat
  representations : List (LiteralList D Γ)
  formulas : List (QFAssertExpr D Γ)
  freshTraversalStats : TraversalStats
  generatorWorkUnits : Nat
  nextState : SeededState (D := D) (Γ := Γ)

/- Advance the seeded incremental enumerator by one stage. -/
def advanceSeeded
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (state : SeededState (D := D) (Γ := Γ)) :
    SeededBatch (D := D) (Γ := Γ) :=
  let stage := state.nextStage
  let curSingle := seededLiteralOrder seeds alphabet stage
  let curCombine := combineLiteralOrder seeds alphabet stage
  let wave :=
    seededWaveFromCurrent state curSingle curCombine
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
        priorCombine := curCombine } }

/- Run a finite number of seeded stages. -/
def runSeeded
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ)) :
    Nat → SeededState (D := D) (Γ := Γ) ×
      List (QFAssertExpr D Γ)
| 0 => (initialSeededState, [])
| completedStages + 1 =>
    let prior := runSeeded alphabet seeds completedStages
    let batch := advanceSeeded alphabet seeds prior.1
    (batch.nextState, prior.2 ++ batch.formulas)

/- Cumulative seeded output after the given stage count. -/
def outputThroughSeeded
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (completedStages : Nat) :
    List (QFAssertExpr D Γ) :=
  (runSeeded alphabet seeds completedStages).2

end Seeded

end Enumerators

end Synthesis

end Whiel
