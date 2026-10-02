-- Author: Jesse Comer
import Whiel.Synthesis.Enumerators.Seeded.Correctness
import Whiel.Synthesis.Enumerators.Fast.Freshness

/-
  Syntactic freshness of the exact two-stream seeded waves.

  These results justify emitting `advanceSeeded.formulas`
  directly at the worker boundary: no formula deduplication
  and no cross-wave identity filter is required. The two
  streams are disjoint by representation length (at most one
  versus at least two); each stream is internally fresh over
  its own monotone universe.

  Main declarations:
    * `advanceSeeded_formulas_nodup`
    * `advanceSeeded_formulas_disjoint_prior_output`
    * `outputThroughSeeded_nodup`
-/

------------------------------------------------------------
-- Seeded Wave Freshness
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

/- Singleton waves emit fresh nonempty representations. -/
theorem singletonWave_fresh
    (priorSingleton current : List (Literal D Γ))
    {representation : LiteralList D Γ}
    (hMember :
      representation ∈
        (singletonWave priorSingleton
          current).representations) :
    ∃ literal ∈ representation,
      literal ∉ priorSingleton :=
  fresh_of_mem_introducedRepresentations
    priorSingleton current 2 hMember

/- Combine waves emit exact new widths or fresh members. -/
theorem combineWave_fresh_or_exact
    (priorWidth : Nat)
    (priorCombine current : List (Literal D Γ))
    (newWidth : Nat)
    {representation : LiteralList D Γ}
    (hMember :
      representation ∈
        (combineWave priorWidth priorCombine current
          newWidth).representations) :
    (priorWidth < representation.length ∧
        representation.length = newWidth) ∨
      ∃ literal ∈ representation,
        literal ∉ priorCombine := by
  simp only [combineWave] at hMember
  by_cases hBump : priorWidth < newWidth
  · rw [if_pos hBump] at hMember
    by_cases hWide : 2 ≤ newWidth
    · rw [if_pos hWide] at hMember
      simp only [List.mem_append, List.mem_filter,
        decide_eq_true_eq] at hMember
      rcases hMember with hExact | ⟨hIntroduced, _⟩
      · have hLength := (List.mem_sublistsLen.mp hExact).2
        exact Or.inl ⟨by omega, hLength⟩
      · exact Or.inr
          (fresh_of_mem_introducedRepresentations
            priorCombine current newWidth hIntroduced)
    · rw [if_neg hWide] at hMember
      simp at hMember
  · rw [if_neg hBump] at hMember
    simp only [List.mem_filter, decide_eq_true_eq]
      at hMember
    exact Or.inr
      (fresh_of_mem_introducedRepresentations
        priorCombine current (newWidth + 1) hMember.1)

/- One seeded wave has duplicate-free representations. -/
theorem seededWave_representations_nodup
    (seeds : Finset (Literal D Γ))
    (alphabet : Alphabet D Γ)
    (state : SeededState (D := D) (Γ := Γ)) :
    ((seededWaveFromCurrent state
      (seededLiteralOrder seeds alphabet state.nextStage)
      (combineLiteralOrder seeds alphabet
        state.nextStage)).representations).Nodup := by
  have hSingleNodup :
      (seededLiteralOrder seeds alphabet
        state.nextStage).Nodup :=
    universeAt_nodup seeds alphabet _
  have hCombineNodup :
      (combineLiteralOrder seeds alphabet
        state.nextStage).Nodup :=
    universeAt_nodup seeds alphabet _
  cases hStage : state.nextStage with
  | zero =>
      rw [hStage] at hSingleNodup
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
      rw [hStage] at hSingleNodup hCombineNodup
      simp only [seededWaveFromCurrent, hStage]
      apply List.Nodup.append
      · exact introducedRepresentations_nodup
          state.priorSingleton
          (seededLiteralOrder seeds alphabet (stage + 1))
          2 hSingleNodup
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
                state.priorCombine
                (combineLiteralOrder seeds alphabet
                  (stage + 1))
                (seededWidth (stage + 1))
                hCombineNodup).filter _
            · intro value hExact hFiltered
              have hIntroduced :=
                (List.mem_filter.mp hFiltered).1
              exact exact_disjoint_introducedRepresentations
                state.priorCombine
                (combineLiteralOrder seeds alphabet
                  (stage + 1))
                (seededWidth (stage + 1))
                hExact hIntroduced
          · rw [if_neg hWide]
            simp
        · rw [if_neg hBump]
          exact (introducedRepresentations_nodup
            state.priorCombine
            (combineLiteralOrder seeds alphabet
              (stage + 1))
            (seededWidth (stage + 1) + 1)
            hCombineNodup).filter _
      · intro value hSingle hCombine
        have hShort :=
          (singletonWave_properties _ _ hSingle).2
        have hWide :=
          (combineWave_properties _ _ _ _ hCombine).2.1
        omega

theorem advanceSeeded_formulas_nodup
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (state : SeededState (D := D) (Γ := Γ)) :
    (advanceSeeded alphabet seeds state).formulas.Nodup := by
  change
    ((seededWaveFromCurrent state
      (seededLiteralOrder seeds alphabet state.nextStage)
      (combineLiteralOrder seeds alphabet
        state.nextStage)).representations.map
          FullEnumeration.decode).Nodup
  exact (seededWave_representations_nodup seeds alphabet
    state).map LiteralList.formula_injective

------------------------------------------------------------
-- Cumulative Characterization
------------------------------------------------------------

/-
  Every cumulative seeded formula through `stage + 1`
  decodes one representation that is either narrow over the
  singleton universe or wide over the combine universe, in
  both cases at the given stage's bounds.
-/
theorem outputThroughSeeded_characterization
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (stage : Nat) :
    ∀ formula ∈
        outputThroughSeeded alphabet seeds (stage + 1),
      ∃ representation : LiteralList D Γ,
        FullEnumeration.decode representation = formula ∧
          (representation.length ≤ 1 ∧
              representation.Sublist
                (seededLiteralOrder seeds alphabet
                  stage) ∨
            2 ≤ representation.length ∧
              representation.Sublist
                (combineLiteralOrder seeds alphabet
                  stage) ∧
              representation.length ≤
                seededWidth stage) := by
  induction stage with
  | zero =>
      intro formula hFormula
      have hCurrent :
          formula ∈
            (advanceSeeded alphabet seeds
              (runSeeded alphabet seeds 0).1).formulas := by
        simpa [outputThroughSeeded, runSeeded] using
          hFormula
      rcases List.mem_map.mp hCurrent with
        ⟨representation, hRepresentation, rfl⟩
      have hProperties :=
        seededWave_properties seeds alphabet
          (runSeeded alphabet seeds 0).1 hRepresentation
      refine ⟨representation, rfl, Or.inl ⟨?_, ?_⟩⟩
      · have hCap := hProperties.2
        simp only [runSeeded_nextStage] at hCap
        have hZero : seededWidth 0 = 0 := rfl
        omega
      · simpa only [runSeeded_nextStage] using
          hProperties.1
  | succ stage ih =>
      intro formula hFormula
      rw [outputThroughSeeded_succ, List.mem_append]
        at hFormula
      rcases hFormula with hPrior | hCurrent
      · rcases ih formula hPrior with
          ⟨representation, rfl, hNarrow | hWide⟩
        · exact ⟨representation, rfl, Or.inl
            ⟨hNarrow.1, hNarrow.2.trans
              (seededLiteralOrder_sublist_succ seeds
                alphabet stage)⟩⟩
        · exact ⟨representation, rfl, Or.inr
            ⟨hWide.1, hWide.2.1.trans
              (combineLiteralOrder_sublist_succ seeds
                alphabet stage),
              hWide.2.2.trans
                (seededWidth_le_succ stage)⟩⟩
      · rcases List.mem_map.mp hCurrent with
          ⟨representation, hRepresentation, rfl⟩
        rw [runSeeded_state_succ] at hRepresentation
        simp only [seededWaveFromCurrent,
          List.mem_append] at hRepresentation
        rcases hRepresentation with hSingle | hCombine
        · have hProperties :=
            singletonWave_properties _ _ hSingle
          exact ⟨representation, rfl, Or.inl
            ⟨hProperties.2, hProperties.1⟩⟩
        · have hProperties :=
            combineWave_properties _ _ _ _ hCombine
          exact ⟨representation, rfl, Or.inr
            ⟨hProperties.2.1, hProperties.1,
              hProperties.2.2⟩⟩

------------------------------------------------------------
-- Cross-Wave Disjointness
------------------------------------------------------------

/-
  No representation of the wave at `stage + 1` satisfies the
  cumulative bounds of the first `stage + 1` waves.
-/
theorem seededWaveRepresentation_not_mem_previous
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (stage : Nat)
    {representation : LiteralList D Γ}
    (hMember :
      representation ∈
        (seededWaveFromCurrent
          { nextStage := stage + 1
            priorSingleton :=
              seededLiteralOrder seeds alphabet stage
            priorCombine :=
              combineLiteralOrder seeds alphabet stage }
          (seededLiteralOrder seeds alphabet (stage + 1))
          (combineLiteralOrder seeds alphabet
            (stage + 1))).representations)
    (hPrevious :
      representation.length ≤ 1 ∧
          representation.Sublist
            (seededLiteralOrder seeds alphabet stage) ∨
        2 ≤ representation.length ∧
          representation.Sublist
            (combineLiteralOrder seeds alphabet stage) ∧
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

theorem advanceSeeded_formulas_disjoint_prior_output
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (stage : Nat) :
    (advanceSeeded alphabet seeds
      (runSeeded alphabet seeds
        (stage + 1)).1).formulas.Disjoint
          (outputThroughSeeded alphabet seeds
            (stage + 1)) := by
  rw [List.disjoint_left]
  intro formula hCurrent hPrior
  rcases List.mem_map.mp hCurrent with
    ⟨representation, hRepresentation, hDecode⟩
  rcases outputThroughSeeded_characterization alphabet
    seeds stage formula hPrior with
    ⟨previous, hPreviousDecode, hPreviousBounds⟩
  have hSame : representation = previous :=
    LiteralList.formula_injective
      (hDecode.trans hPreviousDecode.symm)
  subst previous
  rw [runSeeded_state_succ] at hRepresentation
  exact seededWaveRepresentation_not_mem_previous
    alphabet seeds stage hRepresentation hPreviousBounds

theorem outputThroughSeeded_nodup
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (completedStages : Nat) :
    (outputThroughSeeded alphabet seeds
      completedStages).Nodup := by
  induction completedStages with
  | zero => simp [outputThroughSeeded, runSeeded]
  | succ completedStages ih =>
      rw [outputThroughSeeded_succ]
      apply List.Nodup.append ih
        (advanceSeeded_formulas_nodup alphabet seeds
          (runSeeded alphabet seeds completedStages).1)
      cases completedStages with
      | zero => simp [outputThroughSeeded, runSeeded]
      | succ stage =>
          exact (advanceSeeded_formulas_disjoint_prior_output
            alphabet seeds stage).symm

end Seeded

end Enumerators

end Synthesis

end Whiel
