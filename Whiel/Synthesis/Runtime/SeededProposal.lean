-- Author: Jesse Comer
import Whiel.Synthesis.Enumerators.Seeded.Freshness
import Whiel.Synthesis.Runtime.FastProposal

/-
  Worker-facing adapter for the seeded proposal realization.

  Extends the `FastProposal` namespace: the shared realization
  registry and provenance machinery live there; this module
  holds the seeded stream's provenance, batches, and bridge
  theorems onto the protected seeded executable.
-/

------------------------------------------------------------
-- Seeded Worker Provenance
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

/- Stable task-scoped source identity for one seeded entry. -/
def seededSourceId
    (taskCanonicalId : String)
    (stage ordinal : Nat) : String :=
  "symbolic.seeded:" ++ taskCanonicalId ++
    ":v" ++ toString Realization.seededV1.version ++
    ":s" ++ toString stage ++
    ":o" ++ toString ordinal


/- Attach seeded provenance after typed formula generation. -/
def seededEntriesFromFormulas
    (taskCanonicalId : String)
    (stage : Nat)
    (formulas : List (QFAssertExpr D Γ)) :
    List (ReferenceProposal.Entry (D := D) (Γ := Γ)) :=
  entriesFromFormulasAux
    (seededSourceId taskCanonicalId stage) 0 formulas


/- Seeded transport metadata preserves the formula list. -/
omit [LinearOrder A] [LinearOrder D] in
theorem formulas_seededEntriesFromFormulas
    (taskCanonicalId : String)
    (stage : Nat)
    (formulas : List (QFAssertExpr D Γ)) :
    (seededEntriesFromFormulas taskCanonicalId stage
      formulas).map
        ReferenceProposal.Entry.formula = formulas := by
  exact formulas_entriesFromFormulasAux
    (seededSourceId taskCanonicalId stage) 0 formulas


------------------------------------------------------------
-- Seeded Worker Batches
------------------------------------------------------------

/- One exact seeded wave prepared for worker registration. -/
structure SeededStageBatch where
  stage : Nat
  entries : List (ReferenceProposal.Entry (D := D) (Γ := Γ))
  decodedFormulaOccurrences : Nat
  equalityDistinctFormulas : Nat
  generatorWorkUnits : Nat
  freshTraversalNodes : Nat
  freshNoFreshPrunes : Nat
  freshTooShortPrunes : Nat
  nextState : Enumerators.Seeded.SeededState
    (D := D) (Γ := Γ)

/-
  Advance the exact seeded executable once, then attach
  seeded transport provenance. The protected seeded
  freshness proof establishes that the formula wave is
  duplicate-free and disjoint from all prior reachable
  seeded waves. The worker emits it directly.
-/
def seededStageBatch
    (taskCanonicalId : String)
    (alphabet : DisjunctiveClause.Alphabet D Γ)
    (seeds : Finset (DisjunctiveClause.Literal D Γ))
    (state : Enumerators.Seeded.SeededState
      (D := D) (Γ := Γ)) :
    SeededStageBatch (D := D) (Γ := Γ) :=
  let batch :=
    Enumerators.Seeded.advanceSeeded
      alphabet seeds state
  { stage := batch.stage
    entries :=
      seededEntriesFromFormulas taskCanonicalId
        batch.stage batch.formulas
    decodedFormulaOccurrences := batch.formulas.length
    equalityDistinctFormulas := batch.formulas.length
    generatorWorkUnits := batch.generatorWorkUnits
    freshTraversalNodes := batch.freshTraversalStats.visitedNodes
    freshNoFreshPrunes := batch.freshTraversalStats.noFreshPrunes
    freshTooShortPrunes := batch.freshTraversalStats.tooShortPrunes
    nextState := batch.nextState }

/- Worker entries contain exactly the current seeded wave. -/
theorem seededStageBatch_formulas_eq_advanceSeeded
    (taskCanonicalId : String)
    (alphabet : DisjunctiveClause.Alphabet D Γ)
    (seeds : Finset (DisjunctiveClause.Literal D Γ))
    (state : Enumerators.Seeded.SeededState
      (D := D) (Γ := Γ)) :
    (seededStageBatch taskCanonicalId alphabet seeds
        state).entries.map
        ReferenceProposal.Entry.formula =
      (Enumerators.Seeded.advanceSeeded
        alphabet seeds state).formulas := by
  exact formulas_seededEntriesFromFormulas taskCanonicalId
    (Enumerators.Seeded.advanceSeeded
      alphabet seeds state).stage
    (Enumerators.Seeded.advanceSeeded
      alphabet seeds state).formulas

/- Worker entries have exactly seeded-wave membership. -/
theorem exists_seededStageBatch_entry_iff_mem_advanceSeeded
    (taskCanonicalId : String)
    (alphabet : DisjunctiveClause.Alphabet D Γ)
    (seeds : Finset (DisjunctiveClause.Literal D Γ))
    (state : Enumerators.Seeded.SeededState
      (D := D) (Γ := Γ))
    (formula : QFAssertExpr D Γ) :
    (∃ entry ∈
        (seededStageBatch taskCanonicalId alphabet seeds
          state).entries,
      entry.formula = formula) ↔
      formula ∈
        (Enumerators.Seeded.advanceSeeded
          alphabet seeds state).formulas := by
  let batch :=
    Enumerators.Seeded.advanceSeeded
      alphabet seeds state
  have hFormulas :
      (seededEntriesFromFormulas taskCanonicalId
        batch.stage batch.formulas).map
        ReferenceProposal.Entry.formula = batch.formulas :=
    formulas_seededEntriesFromFormulas taskCanonicalId
      batch.stage batch.formulas
  change
    (∃ entry ∈
        seededEntriesFromFormulas taskCanonicalId
          batch.stage batch.formulas,
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

/- The worker-facing seeded stage keeps the nodup wave. -/
theorem seededStageBatch_formulas_nodup
    (taskCanonicalId : String)
    (alphabet : DisjunctiveClause.Alphabet D Γ)
    (seeds : Finset (DisjunctiveClause.Literal D Γ))
    (state : Enumerators.Seeded.SeededState
      (D := D) (Γ := Γ)) :
    ((seededStageBatch taskCanonicalId alphabet seeds
      state).entries.map
      ReferenceProposal.Entry.formula).Nodup := by
  rw [seededStageBatch_formulas_eq_advanceSeeded]
  exact Enumerators.Seeded.advanceSeeded_formulas_nodup
    alphabet seeds state

/- Every reachable seeded wave is fresh against prior output. -/
theorem seededStageBatch_formulas_disjoint_prior_output
    (taskCanonicalId : String)
    (alphabet : DisjunctiveClause.Alphabet D Γ)
    (seeds : Finset (DisjunctiveClause.Literal D Γ))
    (stage : Nat) :
    ((seededStageBatch taskCanonicalId alphabet seeds
      (Enumerators.Seeded.runSeeded
        alphabet seeds (stage + 1)).1).entries.map
          ReferenceProposal.Entry.formula).Disjoint
      (Enumerators.Seeded.outputThroughSeeded
        alphabet seeds (stage + 1)) := by
  rw [seededStageBatch_formulas_eq_advanceSeeded]
  exact Enumerators.Seeded.advanceSeeded_formulas_disjoint_prior_output
    alphabet seeds stage

/-
  A seeded worker stage reached by actual prior advances
  emits only formulas in the protected cumulative prefix.
-/
theorem seededStageBatch_entry_mem_outputThroughSeeded
    (taskCanonicalId : String)
    (alphabet : DisjunctiveClause.Alphabet D Γ)
    (seeds : Finset (DisjunctiveClause.Literal D Γ))
    (completedStages : Nat)
    (state : Enumerators.Seeded.SeededState
      (D := D) (Γ := Γ))
    (hState : state =
      (Enumerators.Seeded.runSeeded
        alphabet seeds completedStages).1)
    {entry : ReferenceProposal.Entry (D := D) (Γ := Γ)}
    (hEntry : entry ∈
      (seededStageBatch taskCanonicalId alphabet seeds
        state).entries) :
    entry.formula ∈
      Enumerators.Seeded.outputThroughSeeded
        alphabet seeds (completedStages + 1) := by
  have hCurrent : entry.formula ∈
      (Enumerators.Seeded.advanceSeeded
        alphabet seeds state).formulas :=
    (exists_seededStageBatch_entry_iff_mem_advanceSeeded
      taskCanonicalId alphabet seeds state entry.formula).mp
        ⟨entry, hEntry, rfl⟩
  subst state
  rw [Enumerators.Seeded.outputThroughSeeded_succ]
  exact List.mem_append_right _ hCurrent

/-
  The protected cumulative seeded executable is realized
  exactly by the contiguous seeded worker batches for its
  completed stages.
-/
theorem mem_outputThroughSeeded_iff_exists_seededStageBatch_entry
    (taskCanonicalId : String)
    (alphabet : DisjunctiveClause.Alphabet D Γ)
    (seeds : Finset (DisjunctiveClause.Literal D Γ))
    (completedStages : Nat)
    (formula : QFAssertExpr D Γ) :
    formula ∈
        Enumerators.Seeded.outputThroughSeeded
          alphabet seeds completedStages ↔
      ∃ stage, stage < completedStages ∧
        ∃ entry ∈
          (seededStageBatch taskCanonicalId alphabet seeds
            (Enumerators.Seeded.runSeeded
              alphabet seeds stage).1).entries,
          entry.formula = formula := by
  induction completedStages with
  | zero =>
      simp [Enumerators.Seeded.outputThroughSeeded,
        Enumerators.Seeded.runSeeded]
  | succ completedStages ih =>
      rw [Enumerators.Seeded.outputThroughSeeded_succ,
        List.mem_append]
      constructor
      · intro hMember
        rcases hMember with hPrior | hCurrent
        · rcases ih.mp hPrior with
            ⟨stage, hStage, entry, hEntry, hFormula⟩
          exact ⟨stage, Nat.lt_succ_of_lt hStage,
            entry, hEntry, hFormula⟩
        · rcases
            (exists_seededStageBatch_entry_iff_mem_advanceSeeded
              taskCanonicalId alphabet seeds
              (Enumerators.Seeded.runSeeded
                alphabet seeds completedStages).1
              formula).mpr hCurrent with
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
            (exists_seededStageBatch_entry_iff_mem_advanceSeeded
              taskCanonicalId alphabet seeds
              (Enumerators.Seeded.runSeeded
                alphabet seeds completedStages).1
              formula).mp
          exact ⟨entry, hEntry, hFormula⟩

end FastProposal
end Runtime
end Synthesis
end Whiel
