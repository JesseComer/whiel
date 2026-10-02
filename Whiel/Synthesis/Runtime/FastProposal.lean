-- Author: Jesse Comer
import Whiel.Synthesis.Enumerators.Fast.Freshness
import Whiel.Synthesis.Enumerators.Seeded.Enumeration
import Whiel.Synthesis.Enumerators.Capped.Enumeration
import Whiel.Synthesis.Runtime.ReferenceProposal

/-
  Worker-facing adapter for replaceable proposal realizations.

  The fast enumerator sees only its typed alphabet and
  frontier. Task identity is attached after formula
  generation and is used only for transport provenance.
-/

------------------------------------------------------------
-- Proposal Realizations
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FastProposal

/- Shared proposal-page wire contract. -/
def protocolVersion : Nat := 4

/- Proposal realization fixed for one worker lifetime. -/
inductive Realization where
| referenceV3
| fastV1
| seededV1
| cappedV1
deriving DecidableEq, Repr

namespace Realization

/- Stable transport identity of one proposal realization. -/
def id : Realization → String
| .referenceV3 => "lean-reference-v3"
| .fastV1 => Enumerators.Fast.realizationId
| .seededV1 => Enumerators.Seeded.realizationId
| .cappedV1 => Enumerators.Capped.realizationId

/- Stable transport version of one proposal realization. -/
def version : Realization → Nat
| .referenceV3 => ReferenceProposal.version
| .fastV1 => Enumerators.Fast.realizationVersion
| .seededV1 => Enumerators.Seeded.realizationVersion
| .cappedV1 => Enumerators.Capped.realizationVersion

/- Parse one exact realization identity and version. -/
def parse? (realizationId : String) (realizationVersion : Nat) :
    Option Realization :=
  if realizationId = id .referenceV3 &&
      realizationVersion = version .referenceV3 then
    some .referenceV3
  else if realizationId = id .fastV1 &&
      realizationVersion = version .fastV1 then
    some .fastV1
  else if realizationId = id .seededV1 &&
      realizationVersion = version .seededV1 then
    some .seededV1
  else if realizationId = id .cappedV1 &&
      realizationVersion = version .cappedV1 then
    some .cappedV1
  else
    none

end Realization

end FastProposal
end Runtime
end Synthesis
end Whiel

------------------------------------------------------------
-- Fast Worker Batches
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FastProposal

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}
variable [LinearOrder A] [LinearOrder D]
variable [SolverKey A] [SolverKey D]

/- Stable task-scoped source identity for one fast entry. -/
def sourceId
    (taskCanonicalId : String)
    (stage ordinal : Nat) : String :=
  "symbolic.fast:" ++ taskCanonicalId ++
    ":v" ++ toString Realization.fastV1.version ++
    ":s" ++ toString stage ++
    ":o" ++ toString ordinal

def entriesFromFormulasAux
    (sourceOf : Nat → String) :
    Nat → List (QFAssertExpr D Γ) →
      List (ReferenceProposal.Entry (D := D) (Γ := Γ))
| _, [] => []
| ordinal, formula :: rest =>
    { sourceId := sourceOf ordinal
      identity := ReferenceProposal.identity formula
      display := formula.pretty
      formula } ::
    entriesFromFormulasAux sourceOf (ordinal + 1) rest

/- Attach task provenance after typed formula generation. -/
def entriesFromFormulas
    (taskCanonicalId : String)
    (stage : Nat)
    (formulas : List (QFAssertExpr D Γ)) :
    List (ReferenceProposal.Entry (D := D) (Γ := Γ)) :=
  entriesFromFormulasAux
    (sourceId taskCanonicalId stage) 0 formulas

omit [LinearOrder A] [LinearOrder D] in
theorem formulas_entriesFromFormulasAux
    (sourceOf : Nat → String)
    (ordinal : Nat)
    (formulas : List (QFAssertExpr D Γ)) :
    (entriesFromFormulasAux sourceOf ordinal
      formulas).map ReferenceProposal.Entry.formula = formulas := by
  induction formulas generalizing ordinal with
  | nil => rfl
  | cons formula rest ih =>
      simp [entriesFromFormulasAux, ih]

/- Transport metadata preserves the exact typed formula list. -/
omit [LinearOrder A] [LinearOrder D] in
theorem formulas_entriesFromFormulas
    (taskCanonicalId : String)
    (stage : Nat)
    (formulas : List (QFAssertExpr D Γ)) :
    (entriesFromFormulas taskCanonicalId stage formulas).map
      ReferenceProposal.Entry.formula = formulas := by
  exact formulas_entriesFromFormulasAux
    (sourceId taskCanonicalId stage) 0 formulas

/- One exact fast wave prepared for worker registration. -/
structure StageBatch where
  stage : Nat
  entries : List (ReferenceProposal.Entry (D := D) (Γ := Γ))
  decodedFormulaOccurrences : Nat
  equalityDistinctFormulas : Nat
  generatorWorkUnits : Nat
  freshTraversalNodes : Nat
  freshNoFreshPrunes : Nat
  freshTooShortPrunes : Nat
  nextState : Enumerators.Fast.State
    (D := D) (Γ := Γ)

/-
  Advance the exact executable once, then attach transport
  provenance. The protected freshness proof establishes
  that the formula wave is duplicate-free and disjoint from
  all prior reachable waves. The worker emits it directly.
-/
def stageBatch
    (taskCanonicalId : String)
    (alphabet : DisjunctiveClause.Alphabet D Γ)
    (state : Enumerators.Fast.State
      (D := D) (Γ := Γ)) :
    StageBatch (D := D) (Γ := Γ) :=
  let batch := Enumerators.Fast.advance alphabet state
  { stage := batch.stage
    entries := entriesFromFormulas taskCanonicalId batch.stage batch.formulas
    decodedFormulaOccurrences := batch.formulas.length
    equalityDistinctFormulas := batch.formulas.length
    generatorWorkUnits := batch.generatorWorkUnits
    freshTraversalNodes := batch.freshTraversalStats.visitedNodes
    freshNoFreshPrunes := batch.freshTraversalStats.noFreshPrunes
    freshTooShortPrunes := batch.freshTraversalStats.tooShortPrunes
    nextState := batch.nextState }

/- Worker entries contain exactly the current executable wave. -/
theorem stageBatch_formulas_eq_advance
    (taskCanonicalId : String)
    (alphabet : DisjunctiveClause.Alphabet D Γ)
    (state : Enumerators.Fast.State
      (D := D) (Γ := Γ)) :
    (stageBatch taskCanonicalId alphabet state).entries.map
        ReferenceProposal.Entry.formula =
      (Enumerators.Fast.advance
        alphabet state).formulas := by
  exact formulas_entriesFromFormulas taskCanonicalId
    (Enumerators.Fast.advance alphabet state).stage
    (Enumerators.Fast.advance alphabet state).formulas

/- Worker entries have exactly executable-wave membership. -/
theorem exists_stageBatch_entry_iff_mem_advance
    (taskCanonicalId : String)
    (alphabet : DisjunctiveClause.Alphabet D Γ)
    (state : Enumerators.Fast.State
      (D := D) (Γ := Γ))
    (formula : QFAssertExpr D Γ) :
    (∃ entry ∈
        (stageBatch taskCanonicalId alphabet state).entries,
      entry.formula = formula) ↔
      formula ∈
        (Enumerators.Fast.advance
          alphabet state).formulas := by
  let batch :=
    Enumerators.Fast.advance alphabet state
  have hFormulas :
      (entriesFromFormulas taskCanonicalId batch.stage batch.formulas).map
        ReferenceProposal.Entry.formula = batch.formulas :=
    formulas_entriesFromFormulas taskCanonicalId batch.stage batch.formulas
  change
    (∃ entry ∈
        entriesFromFormulas taskCanonicalId batch.stage batch.formulas,
      entry.formula = formula) ↔ formula ∈ batch.formulas
  constructor
  · rintro ⟨entry, hEntry, rfl⟩
    have hFormula : entry.formula ∈ batch.formulas := by
      rw [← hFormulas]
      exact List.mem_map_of_mem hEntry
    exact hFormula
  · intro hFormula
    rw [← hFormulas] at hFormula
    rcases List.mem_map.mp hFormula with
      ⟨entry, hEntry, hEntryFormula⟩
    exact ⟨entry, hEntry, hEntryFormula⟩

/- The worker-facing stage retains the proved duplicate-free wave. -/
theorem stageBatch_formulas_nodup
    (taskCanonicalId : String)
    (alphabet : DisjunctiveClause.Alphabet D Γ)
    (state : Enumerators.Fast.State
      (D := D) (Γ := Γ)) :
    ((stageBatch taskCanonicalId alphabet state).entries.map
      ReferenceProposal.Entry.formula).Nodup := by
  rw [stageBatch_formulas_eq_advance]
  exact Enumerators.Fast.advance_formulas_nodup
    alphabet state

/- Every reachable worker wave is fresh against all prior output. -/
theorem stageBatch_formulas_disjoint_prior_output
    (taskCanonicalId : String)
    (alphabet : DisjunctiveClause.Alphabet D Γ)
    (stage : Nat) :
    ((stageBatch taskCanonicalId alphabet
      (Enumerators.Fast.run
        alphabet (stage + 1)).1).entries.map
          ReferenceProposal.Entry.formula).Disjoint
      (Enumerators.Fast.outputThrough
        alphabet (stage + 1)) := by
  rw [stageBatch_formulas_eq_advance]
  exact Enumerators.Fast.advance_formulas_disjoint_prior_output
    alphabet stage

/-
  A worker stage reached by actual prior advances emits only
  formulas in the corresponding protected cumulative prefix.
-/
theorem stageBatch_entry_mem_outputThrough
    (taskCanonicalId : String)
    (alphabet : DisjunctiveClause.Alphabet D Γ)
    (completedStages : Nat)
    (state : Enumerators.Fast.State
      (D := D) (Γ := Γ))
    (hState : state =
      (Enumerators.Fast.run
        alphabet completedStages).1)
    {entry : ReferenceProposal.Entry (D := D) (Γ := Γ)}
    (hEntry : entry ∈
      (stageBatch taskCanonicalId alphabet state).entries) :
    entry.formula ∈
      Enumerators.Fast.outputThrough
        alphabet (completedStages + 1) := by
  have hCurrent : entry.formula ∈
      (Enumerators.Fast.advance
        alphabet state).formulas :=
    (exists_stageBatch_entry_iff_mem_advance
      taskCanonicalId alphabet state entry.formula).mp
        ⟨entry, hEntry, rfl⟩
  subst state
  exact List.mem_append_right _ hCurrent

/-
  The protected cumulative executable is realized exactly
  by the contiguous worker batches for its completed stages.
-/
theorem mem_outputThrough_iff_exists_stageBatch_entry
    (taskCanonicalId : String)
    (alphabet : DisjunctiveClause.Alphabet D Γ)
    (completedStages : Nat)
    (formula : QFAssertExpr D Γ) :
    formula ∈
        Enumerators.Fast.outputThrough
          alphabet completedStages ↔
      ∃ stage, stage < completedStages ∧
        ∃ entry ∈
          (stageBatch taskCanonicalId alphabet
            (Enumerators.Fast.run
              alphabet stage).1).entries,
          entry.formula = formula := by
  induction completedStages with
  | zero => simp [Enumerators.Fast.outputThrough,
      Enumerators.Fast.run]
  | succ completedStages ih =>
      change
        formula ∈
            Enumerators.Fast.outputThrough
              alphabet completedStages ++
            (Enumerators.Fast.advance alphabet
              (Enumerators.Fast.run
                alphabet completedStages).1).formulas ↔ _
      rw [List.mem_append]
      constructor
      · intro hMember
        rcases hMember with hPrior | hCurrent
        · rcases ih.mp hPrior with
            ⟨stage, hStage, entry, hEntry, hFormula⟩
          exact ⟨stage, Nat.lt_succ_of_lt hStage,
            entry, hEntry, hFormula⟩
        · rcases
            (exists_stageBatch_entry_iff_mem_advance
              taskCanonicalId alphabet
              (Enumerators.Fast.run
                alphabet completedStages).1 formula).mpr hCurrent with
            ⟨entry, hEntry, hFormula⟩
          exact ⟨completedStages, Nat.lt_add_one _,
            entry, hEntry, hFormula⟩
      · rintro ⟨stage, hStage, entry, hEntry, hFormula⟩
        have hStageLe : stage ≤ completedStages :=
          Nat.lt_succ_iff.mp hStage
        by_cases hPrior : stage < completedStages
        · exact Or.inl (ih.mpr
            ⟨stage, hPrior, entry, hEntry, hFormula⟩)
        · have hStageEq : stage = completedStages :=
            Nat.le_antisymm hStageLe (Nat.le_of_not_gt hPrior)
          subst stage
          apply Or.inr
          apply
            (exists_stageBatch_entry_iff_mem_advance
              taskCanonicalId alphabet
              (Enumerators.Fast.run
                alphabet completedStages).1 formula).mp
          exact ⟨entry, hEntry, hFormula⟩

/- Structural identity equality is exact formula equality. -/
omit [LinearOrder A] [LinearOrder D] in
theorem identity_eq_iff_formula_eq
    (left right : QFAssertExpr D Γ) :
    ReferenceProposal.identity left =
        ReferenceProposal.identity right ↔
      left = right := by
  constructor
  · intro hIdentity
    exact (@ReferenceProposal.identity_injective
      A D _ _ _ _ Γ) hIdentity
  · intro hFormula
    exact congrArg ReferenceProposal.identity hFormula

end FastProposal
end Runtime
end Synthesis
end Whiel
