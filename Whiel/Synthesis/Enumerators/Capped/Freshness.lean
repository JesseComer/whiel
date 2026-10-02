-- Author: Jesse Comer
import Whiel.Synthesis.Enumerators.Capped.Correctness
import Whiel.Synthesis.Enumerators.Seeded.Freshness

/-
  Freshness of the capped seeded realization: every wave is
  duplicate-free and disjoint from all earlier output, so
  the cumulative capped stream never repeats a formula.

  Main declarations:
    * `advanceSeededCapped_formulas_nodup`
    * `advanceSeededCapped_formulas_disjoint_prior_output`
    * `outputThroughSeededCapped_nodup`
-/

------------------------------------------------------------
-- Wave Nodup
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Enumerators

namespace Capped

open DisjunctiveClause

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}
variable [LinearOrder A] [LinearOrder D]

local instance : LinearOrder (Literal D Γ) :=
  StructuralOrder.literalLinearOrder

open Seeded
open Fast

/-
  The two-stream wave is duplicate-free over any
  duplicate-free frontiers; the seeded universes play no
  role beyond their nodup property.
-/
private theorem wave_representations_nodup
    (state : SeededState (D := D) (Γ := Γ))
    (curSingle curCombine : List (Literal D Γ))
    (hSingleNodup : curSingle.Nodup)
    (hCombineNodup : curCombine.Nodup) :
    ((seededWaveFromCurrent state curSingle
      curCombine).representations).Nodup := by
  cases hStage : state.nextStage with
  | zero =>
      simp only [seededWaveFromCurrent, hStage]
      apply List.Nodup.append
      · exact List.nodup_sublistsLen 0 hSingleNodup
      · exact List.nodup_sublistsLen 1 hSingleNodup
      · intro value hZero hOne
        have hLengthZero :=
          (List.mem_sublistsLen.mp hZero).2
        have hLengthOne :=
          (List.mem_sublistsLen.mp hOne).2
        omega
  | succ stage =>
      simp only [seededWaveFromCurrent, hStage]
      apply List.Nodup.append
      · exact introducedRepresentations_nodup
          state.priorSingleton curSingle 2 hSingleNodup
      · simp only [combineWave]
        by_cases hBump :
            seededWidth stage < seededWidth (stage + 1)
        · rw [if_pos hBump]
          by_cases hWide : 2 ≤ seededWidth (stage + 1)
          · rw [if_pos hWide]
            apply List.Nodup.append
            · exact List.nodup_sublistsLen
                (seededWidth (stage + 1)) hCombineNodup
            · exact (introducedRepresentations_nodup
                state.priorCombine curCombine
                (seededWidth (stage + 1))
                hCombineNodup).filter _
            · intro value hExact hFiltered
              have hIntroduced :=
                (List.mem_filter.mp hFiltered).1
              exact
                exact_disjoint_introducedRepresentations
                  state.priorCombine curCombine
                  (seededWidth (stage + 1))
                  hExact hIntroduced
          · rw [if_neg hWide]
            simp
        · rw [if_neg hBump]
          exact (introducedRepresentations_nodup
            state.priorCombine curCombine
            (seededWidth (stage + 1) + 1)
            hCombineNodup).filter _
      · intro value hSingle hCombine
        have hShort :=
          (singletonWave_properties _ _ hSingle).2
        have hWide :=
          (combineWave_properties _ _ _ _ hCombine).2.1
        omega

theorem advanceSeededCapped_formulas_nodup
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (schedule : Schedule)
    (state : CappedState (D := D) (Γ := Γ)) :
    (advanceSeededCapped alphabet seeds schedule
      state).formulas.Nodup := by
  apply List.Nodup.map LiteralList.formula_injective
  exact wave_representations_nodup _ _ _
    (universeAt_nodup seeds alphabet _)
    (admittedOrder_nodup _)

------------------------------------------------------------
-- Cumulative Characterization
------------------------------------------------------------

/-
  Every cumulative capped formula through `stage + 1`
  decodes one representation that is either narrow over the
  singleton universe or wide over the admitted universe, in
  both cases at the given stage's bounds.
-/
theorem outputThroughSeededCapped_characterization
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (schedule : Schedule)
    (stage : Nat) :
    ∀ formula ∈
        outputThroughSeededCapped alphabet seeds schedule
          (stage + 1),
      ∃ representation : LiteralList D Γ,
        FullEnumeration.decode representation = formula ∧
          (representation.length ≤ 1 ∧
              representation.Sublist
                (seededLiteralOrder seeds alphabet
                  stage) ∨
            2 ≤ representation.length ∧
              representation.Sublist
                (admittedOrder
                  (admittedAt alphabet seeds schedule
                    (stage + 1))) ∧
              representation.length ≤
                seededWidth stage) := by
  induction stage with
  | zero =>
      intro formula hFormula
      have hCurrent :
          formula ∈
            ((seededLiteralOrder seeds alphabet
              0).sublistsLen 0 ++
              (seededLiteralOrder seeds alphabet
                0).sublistsLen 1).map
              FullEnumeration.decode := by
        simpa [outputThroughSeededCapped, runSeededCapped,
          advanceSeededCapped, seededWaveFromCurrent,
          initialCappedState] using hFormula
      rcases List.mem_map.mp hCurrent with
        ⟨representation, hRepresentation, rfl⟩
      rw [List.mem_append] at hRepresentation
      refine ⟨representation, rfl, Or.inl ⟨?_, ?_⟩⟩
      · rcases hRepresentation with hEmpty | hSingle
        · have := (List.mem_sublistsLen.mp hEmpty).2
          omega
        · have := (List.mem_sublistsLen.mp hSingle).2
          omega
      · rcases hRepresentation with hEmpty | hSingle
        · exact (List.mem_sublistsLen.mp hEmpty).1
        · exact (List.mem_sublistsLen.mp hSingle).1
  | succ stage ih =>
      intro formula hFormula
      rw [outputThroughSeededCapped_succ,
        List.mem_append] at hFormula
      rcases hFormula with hPrior | hCurrent
      · rcases ih formula hPrior with
          ⟨representation, rfl, hNarrow | hWide⟩
        · exact ⟨representation, rfl, Or.inl
            ⟨hNarrow.1, hNarrow.2.trans
              (seededLiteralOrder_sublist_succ seeds
                alphabet stage)⟩⟩
        · exact ⟨representation, rfl, Or.inr
            ⟨hWide.1,
              hWide.2.1.trans
                (admittedOrder_sublist_of_subset
                  (admittedAt_le_succ alphabet seeds
                    schedule (stage + 1))),
              hWide.2.2.trans
                (seededWidth_le_succ stage)⟩⟩
      · rcases List.mem_map.mp hCurrent with
          ⟨representation, hRepresentation, rfl⟩
        rw [runSeededCapped_state_succ]
          at hRepresentation
        simp only [seededWaveFromCurrent,
          List.mem_append]
          at hRepresentation
        rcases hRepresentation with hSingle | hCombine
        · have hProperties :=
            singletonWave_properties _ _ hSingle
          exact ⟨representation, rfl, Or.inl
            ⟨hProperties.2, hProperties.1⟩⟩
        · have hProperties :=
            combineWave_properties _ _ _ _ hCombine
          refine ⟨representation, rfl, Or.inr
            ⟨hProperties.2.1, ?_, hProperties.2.2⟩⟩
          have hCurrentSub := hProperties.1
          rw [← admittedAt_succ] at hCurrentSub
          exact hCurrentSub

------------------------------------------------------------
-- Cross-Wave Disjointness
------------------------------------------------------------

/-
  No representation of the wave at `stage + 1` satisfies
  the cumulative bounds of the first `stage + 1` waves.
-/
theorem cappedWaveRepresentation_not_mem_previous
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (schedule : Schedule)
    (stage : Nat)
    {representation : LiteralList D Γ}
    (hMember :
      representation ∈
        (seededWaveFromCurrent
          { nextStage := stage + 1
            priorSingleton :=
              seededLiteralOrder seeds alphabet stage
            priorCombine :=
              admittedOrder
                (admittedAt alphabet seeds schedule
                  (stage + 1)) }
          (seededLiteralOrder seeds alphabet (stage + 1))
          (admittedOrder
            (admittedAt alphabet seeds schedule
              (stage + 2)))).representations)
    (hPrevious :
      representation.length ≤ 1 ∧
          representation.Sublist
            (seededLiteralOrder seeds alphabet stage) ∨
        2 ≤ representation.length ∧
          representation.Sublist
            (admittedOrder
              (admittedAt alphabet seeds schedule
                (stage + 1))) ∧
          representation.length ≤ seededWidth stage) :
    False := by
  simp only [seededWaveFromCurrent, List.mem_append]
    at hMember
  rcases hMember with hSingle | hCombine
  · have hShort :=
      (singletonWave_properties _ _ hSingle).2
    rcases singletonWave_fresh _ _ hSingle with
      ⟨literal, hLiteral, hNotPrior⟩
    rcases hPrevious with hNarrow | hWide
    · exact hNotPrior (hNarrow.2.subset hLiteral)
    · omega
  · have hWideMember :=
      (combineWave_properties _ _ _ _ hCombine).2.1
    rcases hPrevious with hNarrow | hWide
    · omega
    · rcases combineWave_fresh_or_exact _ _ _ _ hCombine
        with hExact | ⟨literal, hLiteral, hNotPrior⟩
      · have hBound := hWide.2.2
        omega
      · exact hNotPrior (hWide.2.1.subset hLiteral)

theorem advanceSeededCapped_formulas_disjoint_prior_output
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (schedule : Schedule)
    (stage : Nat) :
    (advanceSeededCapped alphabet seeds schedule
      (runSeededCapped alphabet seeds schedule
        (stage + 1)).1).formulas.Disjoint
          (outputThroughSeededCapped alphabet seeds
            schedule (stage + 1)) := by
  rw [List.disjoint_left]
  intro formula hCurrent hPrior
  rcases List.mem_map.mp hCurrent with
    ⟨representation, hRepresentation, hDecode⟩
  rcases outputThroughSeededCapped_characterization
    alphabet seeds schedule stage formula hPrior with
    ⟨previous, hPreviousDecode, hPreviousBounds⟩
  have hSame : representation = previous :=
    LiteralList.formula_injective
      (hDecode.trans hPreviousDecode.symm)
  subst previous
  rw [runSeededCapped_state_succ] at hRepresentation
  apply cappedWaveRepresentation_not_mem_previous
    alphabet seeds schedule stage ?_ hPreviousBounds
  simpa [advanceSeededCapped, admittedAt_succ] using
    hRepresentation

------------------------------------------------------------
-- Cumulative Nodup
------------------------------------------------------------

theorem outputThroughSeededCapped_nodup
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (schedule : Schedule)
    (completedStages : Nat) :
    (outputThroughSeededCapped alphabet seeds schedule
      completedStages).Nodup := by
  induction completedStages with
  | zero =>
      simp [outputThroughSeededCapped, runSeededCapped]
  | succ completedStages ih =>
      rw [outputThroughSeededCapped_succ]
      apply List.Nodup.append ih
        (advanceSeededCapped_formulas_nodup alphabet
          seeds schedule _)
      cases completedStages with
      | zero =>
          intro formula hPrior _
          simp [outputThroughSeededCapped,
            runSeededCapped] at hPrior
      | succ stage =>
          intro formula hPrior hCurrent
          exact
            (advanceSeededCapped_formulas_disjoint_prior_output
              alphabet seeds schedule stage)
              hCurrent hPrior

end Capped

end Enumerators

end Synthesis

end Whiel
