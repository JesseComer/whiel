-- Author: Jesse Comer
import Whiel.Synthesis.Enumerators.Capped.Freshness
import Whiel.Synthesis.Runtime.FastProposal

/-
  Worker-facing adapter for the capped seeded proposal
  realization.

  Extends the `FastProposal` namespace: the shared
  realization registry and provenance machinery live there;
  this module holds the capped stream's provenance, batches,
  and bridge theorems onto the protected capped executable.
  The worker serves the stream at the registry's fixed
  instantiation: the default amnesty schedule at the task's
  seed count.
-/

------------------------------------------------------------
-- Capped Worker Provenance
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

/- Stable task-scoped source identity for one capped entry. -/
def cappedSourceId
    (taskCanonicalId : String)
    (stage ordinal : Nat) : String :=
  "symbolic.capped:" ++ taskCanonicalId ++
    ":v" ++ toString Realization.cappedV1.version ++
    ":s" ++ toString stage ++
    ":o" ++ toString ordinal


/- Attach capped provenance after typed formula generation. -/
def cappedEntriesFromFormulas
    (taskCanonicalId : String)
    (stage : Nat)
    (formulas : List (QFAssertExpr D Γ)) :
    List (ReferenceProposal.Entry (D := D) (Γ := Γ)) :=
  entriesFromFormulasAux
    (cappedSourceId taskCanonicalId stage) 0 formulas


/- Capped transport metadata preserves the formula list. -/
omit [LinearOrder A] [LinearOrder D] in
theorem formulas_cappedEntriesFromFormulas
    (taskCanonicalId : String)
    (stage : Nat)
    (formulas : List (QFAssertExpr D Γ)) :
    (cappedEntriesFromFormulas taskCanonicalId stage
      formulas).map
        ReferenceProposal.Entry.formula = formulas := by
  exact formulas_entriesFromFormulasAux
    (cappedSourceId taskCanonicalId stage) 0 formulas


------------------------------------------------------------
-- Capped Worker Batches
------------------------------------------------------------

/- One exact capped wave prepared for worker registration. -/
structure CappedStageBatch where
  stage : Nat
  entries : List (ReferenceProposal.Entry (D := D) (Γ := Γ))
  decodedFormulaOccurrences : Nat
  equalityDistinctFormulas : Nat
  generatorWorkUnits : Nat
  freshTraversalNodes : Nat
  freshNoFreshPrunes : Nat
  freshTooShortPrunes : Nat
  nextState : Enumerators.Capped.CappedState
    (D := D) (Γ := Γ)

/-
  Advance the exact capped executable once, then attach
  capped transport provenance. The protected capped
  freshness proof establishes that the formula wave is
  duplicate-free and disjoint from all prior reachable
  capped waves. The worker emits it directly.
-/
def cappedStageBatch
    (taskCanonicalId : String)
    (alphabet : DisjunctiveClause.Alphabet D Γ)
    (seeds : Finset (DisjunctiveClause.Literal D Γ))
    (state : Enumerators.Capped.CappedState
      (D := D) (Γ := Γ)) :
    CappedStageBatch (D := D) (Γ := Γ) :=
  let batch :=
    Enumerators.Capped.advanceSeededCapped
      alphabet seeds
      (Enumerators.Capped.defaultSchedule seeds.card)
      state
  { stage := batch.stage
    entries :=
      cappedEntriesFromFormulas taskCanonicalId
        batch.stage batch.formulas
    decodedFormulaOccurrences := batch.formulas.length
    equalityDistinctFormulas := batch.formulas.length
    generatorWorkUnits := batch.generatorWorkUnits
    freshTraversalNodes := batch.freshTraversalStats.visitedNodes
    freshNoFreshPrunes := batch.freshTraversalStats.noFreshPrunes
    freshTooShortPrunes := batch.freshTraversalStats.tooShortPrunes
    nextState := batch.nextState }

/- Worker entries contain exactly the current capped wave. -/
theorem cappedStageBatch_formulas_eq_advanceSeededCapped
    (taskCanonicalId : String)
    (alphabet : DisjunctiveClause.Alphabet D Γ)
    (seeds : Finset (DisjunctiveClause.Literal D Γ))
    (state : Enumerators.Capped.CappedState
      (D := D) (Γ := Γ)) :
    (cappedStageBatch taskCanonicalId alphabet seeds
        state).entries.map
        ReferenceProposal.Entry.formula =
      (Enumerators.Capped.advanceSeededCapped
        alphabet seeds
        (Enumerators.Capped.defaultSchedule seeds.card)
        state).formulas := by
  exact formulas_cappedEntriesFromFormulas taskCanonicalId
    (Enumerators.Capped.advanceSeededCapped
      alphabet seeds
      (Enumerators.Capped.defaultSchedule seeds.card)
      state).stage
    (Enumerators.Capped.advanceSeededCapped
      alphabet seeds
      (Enumerators.Capped.defaultSchedule seeds.card)
      state).formulas

/- Worker entries have exactly capped-wave membership. -/
theorem
    exists_cappedStageBatch_entry_iff_mem_advanceSeededCapped
    (taskCanonicalId : String)
    (alphabet : DisjunctiveClause.Alphabet D Γ)
    (seeds : Finset (DisjunctiveClause.Literal D Γ))
    (state : Enumerators.Capped.CappedState
      (D := D) (Γ := Γ))
    (formula : QFAssertExpr D Γ) :
    (∃ entry ∈
        (cappedStageBatch taskCanonicalId alphabet seeds
          state).entries,
      entry.formula = formula) ↔
      formula ∈
        (Enumerators.Capped.advanceSeededCapped
          alphabet seeds
          (Enumerators.Capped.defaultSchedule seeds.card)
          state).formulas := by
  let batch :=
    Enumerators.Capped.advanceSeededCapped
      alphabet seeds
      (Enumerators.Capped.defaultSchedule seeds.card)
      state
  have hFormulas :
      (cappedEntriesFromFormulas taskCanonicalId
        batch.stage batch.formulas).map
        ReferenceProposal.Entry.formula = batch.formulas :=
    formulas_cappedEntriesFromFormulas taskCanonicalId
      batch.stage batch.formulas
  change
    (∃ entry ∈
        cappedEntriesFromFormulas taskCanonicalId
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

/- The worker-facing capped stage keeps the nodup wave. -/
theorem cappedStageBatch_formulas_nodup
    (taskCanonicalId : String)
    (alphabet : DisjunctiveClause.Alphabet D Γ)
    (seeds : Finset (DisjunctiveClause.Literal D Γ))
    (state : Enumerators.Capped.CappedState
      (D := D) (Γ := Γ)) :
    ((cappedStageBatch taskCanonicalId alphabet seeds
      state).entries.map
      ReferenceProposal.Entry.formula).Nodup := by
  rw [cappedStageBatch_formulas_eq_advanceSeededCapped]
  exact Enumerators.Capped.advanceSeededCapped_formulas_nodup
    alphabet seeds
    (Enumerators.Capped.defaultSchedule seeds.card) state

/- Every reachable capped wave is fresh against prior output. -/
theorem cappedStageBatch_formulas_disjoint_prior_output
    (taskCanonicalId : String)
    (alphabet : DisjunctiveClause.Alphabet D Γ)
    (seeds : Finset (DisjunctiveClause.Literal D Γ))
    (stage : Nat) :
    ((cappedStageBatch taskCanonicalId alphabet seeds
      (Enumerators.Capped.runSeededCapped
        alphabet seeds
          (Enumerators.Capped.defaultSchedule seeds.card)
          (stage + 1)).1).entries.map
          ReferenceProposal.Entry.formula).Disjoint
      (Enumerators.Capped.outputThroughSeededCapped
        alphabet seeds
          (Enumerators.Capped.defaultSchedule seeds.card)
          (stage + 1)) := by
  rw [cappedStageBatch_formulas_eq_advanceSeededCapped]
  exact
    Enumerators.Capped.advanceSeededCapped_formulas_disjoint_prior_output
      alphabet seeds
      (Enumerators.Capped.defaultSchedule seeds.card) stage

/-
  A capped worker stage reached by actual prior advances
  emits only formulas in the protected cumulative prefix.
-/
theorem cappedStageBatch_entry_mem_outputThroughSeededCapped
    (taskCanonicalId : String)
    (alphabet : DisjunctiveClause.Alphabet D Γ)
    (seeds : Finset (DisjunctiveClause.Literal D Γ))
    (completedStages : Nat)
    (state : Enumerators.Capped.CappedState
      (D := D) (Γ := Γ))
    (hState : state =
      (Enumerators.Capped.runSeededCapped
        alphabet seeds
          (Enumerators.Capped.defaultSchedule seeds.card)
          completedStages).1)
    {entry : ReferenceProposal.Entry (D := D) (Γ := Γ)}
    (hEntry : entry ∈
      (cappedStageBatch taskCanonicalId alphabet seeds
        state).entries) :
    entry.formula ∈
      Enumerators.Capped.outputThroughSeededCapped
        alphabet seeds
          (Enumerators.Capped.defaultSchedule seeds.card)
          (completedStages + 1) := by
  have hCurrent : entry.formula ∈
      (Enumerators.Capped.advanceSeededCapped
        alphabet seeds
        (Enumerators.Capped.defaultSchedule seeds.card)
        state).formulas :=
    (exists_cappedStageBatch_entry_iff_mem_advanceSeededCapped
      taskCanonicalId alphabet seeds state entry.formula).mp
        ⟨entry, hEntry, rfl⟩
  subst state
  rw [Enumerators.Capped.outputThroughSeededCapped_succ]
  exact List.mem_append_right _ hCurrent

/-
  The protected cumulative capped executable is realized
  exactly by the contiguous capped worker batches for its
  completed stages.
-/
theorem
    mem_outputThroughSeededCapped_iff_exists_cappedStageBatch_entry
    (taskCanonicalId : String)
    (alphabet : DisjunctiveClause.Alphabet D Γ)
    (seeds : Finset (DisjunctiveClause.Literal D Γ))
    (completedStages : Nat)
    (formula : QFAssertExpr D Γ) :
    formula ∈
        Enumerators.Capped.outputThroughSeededCapped
          alphabet seeds
            (Enumerators.Capped.defaultSchedule seeds.card)
            completedStages ↔
      ∃ stage, stage < completedStages ∧
        ∃ entry ∈
          (cappedStageBatch taskCanonicalId alphabet seeds
            (Enumerators.Capped.runSeededCapped
              alphabet seeds
                (Enumerators.Capped.defaultSchedule seeds.card)
                stage).1).entries,
          entry.formula = formula := by
  induction completedStages with
  | zero =>
      simp [Enumerators.Capped.outputThroughSeededCapped,
        Enumerators.Capped.runSeededCapped]
  | succ completedStages ih =>
      rw [Enumerators.Capped.outputThroughSeededCapped_succ,
        List.mem_append]
      constructor
      · intro hMember
        rcases hMember with hPrior | hCurrent
        · rcases ih.mp hPrior with
            ⟨stage, hStage, entry, hEntry, hFormula⟩
          exact ⟨stage, Nat.lt_succ_of_lt hStage,
            entry, hEntry, hFormula⟩
        · rcases
            (exists_cappedStageBatch_entry_iff_mem_advanceSeededCapped
              taskCanonicalId alphabet seeds
              (Enumerators.Capped.runSeededCapped
                alphabet seeds
                  (Enumerators.Capped.defaultSchedule seeds.card)
                  completedStages).1
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
            (exists_cappedStageBatch_entry_iff_mem_advanceSeededCapped
              taskCanonicalId alphabet seeds
              (Enumerators.Capped.runSeededCapped
                alphabet seeds
                  (Enumerators.Capped.defaultSchedule seeds.card)
                  completedStages).1
              formula).mp
          exact ⟨entry, hEntry, hFormula⟩

end FastProposal
end Runtime
end Synthesis
end Whiel
