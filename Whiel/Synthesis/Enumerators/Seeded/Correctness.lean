-- Author: Jesse Comer
import Whiel.Synthesis.Enumerators.Seeded.Enumeration
import Whiel.Synthesis.Enumerators.Fast.Correctness

/-
  Coverage of the reference stream by the two-stream seeded
  enumerator. The singleton stream emits every literal once
  as a width-one clause; the combine stream emits all wider
  clauses over the lagged combine universe. Coverage holds
  because both universe indices are cofinal in the reference
  schedule.

  Main declarations:
    * `seededRepresentation_mem_outputThroughSeeded`
    * `seededCoversReference`
-/

------------------------------------------------------------
-- Seeded Universe Facts
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

/- A sorted duplicate-free subset is a sublist. -/
theorem sublist_of_nodup_subset_pairwise
    {smaller larger : List (Literal D Γ)}
    (hNodup : smaller.Nodup)
    (hSubset : smaller ⊆ larger)
    (hSmaller : smaller.Pairwise (· ≤ ·))
    (hLarger : larger.Pairwise (· ≤ ·)) :
    smaller.Sublist larger :=
  List.sublist_of_subperm_of_pairwise
    (hNodup.subperm hSubset) hSmaller hLarger

theorem universeAt_nodup
    (seeds : Finset (Literal D Γ))
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    (universeAt seeds alphabet parameters).Nodup :=
  Finset.sort_nodup _ _

theorem universeAt_pairwise
    (seeds : Finset (Literal D Γ))
    (alphabet : Alphabet D Γ)
    (parameters : Parameters) :
    (universeAt seeds alphabet parameters).Pairwise
      (· ≤ ·) :=
  Finset.pairwise_sort _ _

@[simp] theorem mem_universeAt_iff
    (seeds : Finset (Literal D Γ))
    (alphabet : Alphabet D Γ)
    (parameters : Parameters)
    (literal : Literal D Γ) :
    literal ∈ universeAt seeds alphabet parameters ↔
      literal ∈ seeds ∨
        literal.IsEligible alphabet parameters := by
  simp [universeAt, Finset.mem_sort,
    Finset.mem_union]

/- The universe grows along parameter dominance. -/
theorem universeAt_subset_of_dominates
    (seeds : Finset (Literal D Γ))
    (alphabet : Alphabet D Γ)
    {smaller larger : Parameters}
    (hDominates : larger.Dominates smaller) :
    universeAt seeds alphabet smaller ⊆
      universeAt seeds alphabet larger := by
  intro literal hLiteral
  rw [mem_universeAt_iff] at hLiteral ⊢
  rcases hLiteral with hSeed | hEligible
  · exact Or.inl hSeed
  · exact Or.inr (hEligible.mono hDominates)

theorem universeAt_sublist_of_dominates
    (seeds : Finset (Literal D Γ))
    (alphabet : Alphabet D Γ)
    {smaller larger : Parameters}
    (hDominates : larger.Dominates smaller) :
    (universeAt seeds alphabet smaller).Sublist
      (universeAt seeds alphabet larger) :=
  sublist_of_nodup_subset_pairwise
    (universeAt_nodup seeds alphabet smaller)
    (universeAt_subset_of_dominates seeds alphabet
      hDominates)
    (universeAt_pairwise seeds alphabet smaller)
    (universeAt_pairwise seeds alphabet larger)

------------------------------------------------------------
-- Schedule Facts
------------------------------------------------------------

theorem seededWidth_le_succ (stage : Nat) :
    seededWidth stage ≤ seededWidth (stage + 1) := by
  simp only [seededWidth]
  omega

theorem seededUniverseIndex_le_succ (stage : Nat) :
    seededUniverseIndex stage ≤
      seededUniverseIndex (stage + 1) := by
  simp only [seededUniverseIndex]
  omega

theorem combineIndex_le_succ (stage : Nat) :
    combineIndex stage ≤ combineIndex (stage + 1) := by
  simp only [combineIndex]
  omega

/- Successive seeded parameters dominate their predecessor. -/
theorem seededParameters_dominates_succ
    (stage : Nat) :
    (seededParameters (stage + 1)).Dominates
      (seededParameters stage) := by
  refine ⟨Finset.Subset.refl _, Finset.Subset.refl _,
    Finset.Subset.refl _, Finset.Subset.refl _,
    ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [seededParameters, seededUniverseIndex,
      seededWidth, referenceParameters] <;>
    omega

/- Successive combine parameters dominate their predecessor. -/
theorem combineParameters_dominates_succ
    (stage : Nat) :
    (combineParameters (stage + 1)).Dominates
      (combineParameters stage) := by
  refine ⟨Finset.Subset.refl _, Finset.Subset.refl _,
    Finset.Subset.refl _, Finset.Subset.refl _,
    ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [combineParameters, combineIndex,
      seededWidth, referenceParameters] <;>
    omega

/- The singleton stream dominates the lagged combine stream. -/
theorem seededParameters_dominates_combineParameters
    (stage : Nat) :
    (seededParameters stage).Dominates
      (combineParameters stage) := by
  refine ⟨Finset.Subset.refl _, Finset.Subset.refl _,
    Finset.Subset.refl _, Finset.Subset.refl _,
    ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [seededParameters, combineParameters,
      seededUniverseIndex, combineIndex, seededWidth,
      referenceParameters] <;>
    omega

theorem seededLiteralOrder_sublist_succ
    (seeds : Finset (Literal D Γ))
    (alphabet : Alphabet D Γ)
    (stage : Nat) :
    (seededLiteralOrder seeds alphabet stage).Sublist
      (seededLiteralOrder seeds alphabet (stage + 1)) :=
  universeAt_sublist_of_dominates seeds alphabet
    (seededParameters_dominates_succ stage)

theorem combineLiteralOrder_sublist_succ
    (seeds : Finset (Literal D Γ))
    (alphabet : Alphabet D Γ)
    (stage : Nat) :
    (combineLiteralOrder seeds alphabet stage).Sublist
      (combineLiteralOrder seeds alphabet (stage + 1)) :=
  universeAt_sublist_of_dominates seeds alphabet
    (combineParameters_dominates_succ stage)

theorem combineLiteralOrder_sublist_seededLiteralOrder
    (seeds : Finset (Literal D Γ))
    (alphabet : Alphabet D Γ)
    (stage : Nat) :
    (combineLiteralOrder seeds alphabet stage).Sublist
      (seededLiteralOrder seeds alphabet stage) :=
  universeAt_sublist_of_dominates seeds alphabet
    (seededParameters_dominates_combineParameters stage)

------------------------------------------------------------
-- Seeded Frontier State
------------------------------------------------------------

@[simp] theorem runSeeded_nextStage
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (completedStages : Nat) :
    (runSeeded alphabet seeds completedStages).1.nextStage =
      completedStages := by
  induction completedStages with
  | zero => rfl
  | succ completedStages ih =>
      simp [runSeeded, advanceSeeded, ih]

theorem runSeeded_priorSingleton_succ
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (stage : Nat) :
    (runSeeded alphabet seeds
        (stage + 1)).1.priorSingleton =
      seededLiteralOrder seeds alphabet stage := by
  simp [runSeeded, advanceSeeded]

theorem runSeeded_priorCombine_succ
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (stage : Nat) :
    (runSeeded alphabet seeds
        (stage + 1)).1.priorCombine =
      combineLiteralOrder seeds alphabet stage := by
  simp [runSeeded, advanceSeeded]

theorem runSeeded_state_succ
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (stage : Nat) :
    (runSeeded alphabet seeds (stage + 1)).1 =
      { nextStage := stage + 1
        priorSingleton :=
          seededLiteralOrder seeds alphabet stage
        priorCombine :=
          combineLiteralOrder seeds alphabet stage } := by
  cases hRun : (runSeeded alphabet seeds (stage + 1)).1 with
  | mk nextStage priorSingleton priorCombine =>
      have hNext :=
        runSeeded_nextStage alphabet seeds (stage + 1)
      have hSingle :=
        runSeeded_priorSingleton_succ alphabet seeds stage
      have hCombine :=
        runSeeded_priorCombine_succ alphabet seeds stage
      simp only [hRun] at hNext hSingle hCombine
      subst nextStage
      subst priorSingleton
      subst priorCombine
      rfl

theorem outputThroughSeeded_succ
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (completedStages : Nat) :
    outputThroughSeeded alphabet seeds
        (completedStages + 1) =
      outputThroughSeeded alphabet seeds completedStages ++
        (advanceSeeded alphabet seeds
          (runSeeded alphabet seeds
            completedStages).1).formulas := by
  simp [outputThroughSeeded, runSeeded]

theorem mem_outputThroughSeeded_succ_of_mem
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (completedStages : Nat)
    {formula : QFAssertExpr D Γ}
    (hMember :
      formula ∈
        outputThroughSeeded alphabet seeds
          completedStages) :
    formula ∈
      outputThroughSeeded alphabet seeds
        (completedStages + 1) := by
  rw [outputThroughSeeded_succ, List.mem_append]
  exact Or.inl hMember

------------------------------------------------------------
-- Per-Stream Wave Properties
------------------------------------------------------------

/- Singleton waves emit only fresh width-one sublists. -/
theorem singletonWave_properties
    (priorSingleton current : List (Literal D Γ))
    {representation : LiteralList D Γ}
    (hMember :
      representation ∈
        (singletonWave priorSingleton
          current).representations) :
    representation.Sublist current ∧
      representation.length ≤ 1 := by
  have hProperties :=
    properties_of_mem_introducedRepresentations
      priorSingleton current representation 2 hMember
  exact ⟨hProperties.1, by omega⟩

/- Combine waves emit only wide bounded sublists. -/
theorem combineWave_properties
    (priorWidth : Nat)
    (priorCombine current : List (Literal D Γ))
    (newWidth : Nat)
    {representation : LiteralList D Γ}
    (hMember :
      representation ∈
        (combineWave priorWidth priorCombine current
          newWidth).representations) :
    representation.Sublist current ∧
      2 ≤ representation.length ∧
        representation.length ≤ newWidth := by
  simp only [combineWave] at hMember
  by_cases hBump : priorWidth < newWidth
  · rw [if_pos hBump] at hMember
    by_cases hWide : 2 ≤ newWidth
    · rw [if_pos hWide] at hMember
      simp only [List.mem_append, List.mem_filter,
        decide_eq_true_eq] at hMember
      rcases hMember with hExact | ⟨hIntroduced, hLength⟩
      · have hProperties :=
          List.mem_sublistsLen.mp hExact
        exact ⟨hProperties.1, by omega, hProperties.2.le⟩
      · have hProperties :=
          properties_of_mem_introducedRepresentations
            priorCombine current representation
            newWidth hIntroduced
        exact ⟨hProperties.1, hLength, by omega⟩
    · rw [if_neg hWide] at hMember
      simp at hMember
  · rw [if_neg hBump] at hMember
    simp only [List.mem_filter, decide_eq_true_eq]
      at hMember
    have hProperties :=
      properties_of_mem_introducedRepresentations
        priorCombine current representation
        (newWidth + 1) hMember.1
    exact ⟨hProperties.1, hMember.2, by omega⟩

/- Every seeded wave stays inside the stage universe. -/
theorem seededWave_properties
    (seeds : Finset (Literal D Γ))
    (alphabet : Alphabet D Γ)
    (state : SeededState (D := D) (Γ := Γ))
    {representation : LiteralList D Γ}
    (hMember :
      representation ∈
        (seededWaveFromCurrent state
          (seededLiteralOrder seeds alphabet
            state.nextStage)
          (combineLiteralOrder seeds alphabet
            state.nextStage)).representations) :
    representation.Sublist
        (seededLiteralOrder seeds alphabet
          state.nextStage) ∧
      representation.length ≤
        max 1 (seededWidth state.nextStage) := by
  cases hStage : state.nextStage with
  | zero =>
      simp only [seededWaveFromCurrent, hStage,
        List.mem_append] at hMember
      rcases hMember with hEmpty | hSingle
      · have hProperties := List.mem_sublistsLen.mp hEmpty
        exact ⟨hProperties.1, by omega⟩
      · have hProperties := List.mem_sublistsLen.mp hSingle
        exact ⟨hProperties.1, by omega⟩
  | succ stage =>
      simp only [seededWaveFromCurrent, hStage,
        List.mem_append] at hMember
      rcases hMember with hSingle | hCombine
      · have hProperties :=
          singletonWave_properties _ _ hSingle
        exact ⟨hProperties.1, by omega⟩
      · have hProperties :=
          combineWave_properties _ _ _ _ hCombine
        refine ⟨hProperties.1.trans
          (combineLiteralOrder_sublist_seededLiteralOrder
            seeds alphabet (stage + 1)), ?_⟩
        have := hProperties.2.2
        omega

------------------------------------------------------------
-- Cumulative Seeded Membership
------------------------------------------------------------

/- Mirror of the reference file's private freshness helper. -/
private theorem exists_fresh_of_not_sublist'
    (prior current representation :
      List (Literal D Γ))
    (hRepresentation : representation.Sublist current)
    (hNotPrior : ¬ representation.Sublist prior)
    (hCurrentNodup : current.Nodup)
    (hCurrentOrder : current.Pairwise (· ≤ ·))
    (hPriorOrder : prior.Pairwise (· ≤ ·)) :
    ∃ literal ∈ representation, literal ∉ prior := by
  by_contra hNoFresh
  push Not at hNoFresh
  have hSubset : representation ⊆ prior := by
    intro literal hLiteral
    exact hNoFresh literal hLiteral
  have hSubperm : List.Subperm representation prior :=
    (hCurrentNodup.sublist hRepresentation).subperm
      hSubset
  apply hNotPrior
  exact List.sublist_of_subperm_of_pairwise hSubperm
    (hCurrentOrder.sublist hRepresentation)
    hPriorOrder

/- The empty representation appears at stage zero. -/
theorem emptyRep_mem_outputThroughSeeded
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (stage : Nat) :
    FullEnumeration.decode ([] : LiteralList D Γ) ∈
      outputThroughSeeded alphabet seeds (stage + 1) := by
  induction stage with
  | zero =>
      simp [outputThroughSeeded, runSeeded, advanceSeeded,
        seededWaveFromCurrent, initialSeededState]
  | succ stage ih =>
      exact mem_outputThroughSeeded_succ_of_mem alphabet
        seeds (stage + 1) ih

/-
  Every literal appears as a width-one clause by the first
  stage whose singleton universe contains it.
-/
theorem singleton_mem_outputThroughSeeded
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (stage : Nat)
    (literal : Literal D Γ)
    (hMember :
      literal ∈ seededLiteralOrder seeds alphabet stage) :
    FullEnumeration.decode [literal] ∈
      outputThroughSeeded alphabet seeds (stage + 1) := by
  induction stage with
  | zero =>
      have hWave :
          [literal] ∈
            ((seededLiteralOrder seeds alphabet
              0).sublistsLen 0 ++
              (seededLiteralOrder seeds alphabet
                0).sublistsLen 1) := by
        rw [List.mem_append]
        exact Or.inr (List.mem_sublistsLen.mpr
          ⟨List.singleton_sublist.mpr hMember, rfl⟩)
      simpa [outputThroughSeeded, runSeeded, advanceSeeded,
        seededWaveFromCurrent, initialSeededState] using
        List.mem_map_of_mem
          (f := FullEnumeration.decode) hWave
  | succ stage ih =>
      by_cases hPrior :
          literal ∈ seededLiteralOrder seeds alphabet stage
      · exact mem_outputThroughSeeded_succ_of_mem alphabet
          seeds (stage + 1) (ih hPrior)
      · have hWave :
            [literal] ∈
              (singletonWave
                (seededLiteralOrder seeds alphabet stage)
                (seededLiteralOrder seeds alphabet
                  (stage + 1))).representations := by
          apply mem_introducedRepresentations_of
          · simp
          · exact List.singleton_sublist.mpr hMember
          · exact ⟨literal, List.mem_singleton_self literal,
              hPrior⟩
        rw [outputThroughSeeded_succ, List.mem_append]
        apply Or.inr
        rw [runSeeded_state_succ]
        refine List.mem_map_of_mem ?_
        simp only [seededWaveFromCurrent,
          List.mem_append]
        exact Or.inl hWave

/-
  Every wide sorted representation over the combine universe
  with admissible width occurs in the cumulative output.
-/
theorem combine_mem_outputThroughSeeded
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (stage : Nat)
    (representation : LiteralList D Γ)
    (hSublist :
      representation.Sublist
        (combineLiteralOrder seeds alphabet stage))
    (hWide : 2 ≤ representation.length)
    (hWidth :
      representation.length ≤ seededWidth stage) :
    FullEnumeration.decode representation ∈
      outputThroughSeeded alphabet seeds (stage + 1) := by
  induction stage with
  | zero =>
      have hZero : seededWidth 0 = 0 := rfl
      omega
  | succ stage ih =>
      by_cases hPrior :
          representation.Sublist
              (combineLiteralOrder seeds alphabet stage) ∧
            representation.length ≤ seededWidth stage
      · exact mem_outputThroughSeeded_succ_of_mem alphabet
          seeds (stage + 1) (ih hPrior.1 hPrior.2)
      · have hStep :
            seededWidth (stage + 1) ≤
              seededWidth stage + 1 := by
          simp only [seededWidth]
          omega
        have hWideNew :
            2 ≤ seededWidth (stage + 1) := by omega
        have hFreshFrom :
            ¬ representation.Sublist
                (combineLiteralOrder seeds alphabet
                  stage) →
              ∃ literal ∈ representation,
                literal ∉
                  combineLiteralOrder seeds alphabet
                    stage := by
          intro hNotSublist
          exact exists_fresh_of_not_sublist'
            (combineLiteralOrder seeds alphabet stage)
            (combineLiteralOrder seeds alphabet (stage + 1))
            representation hSublist hNotSublist
            (universeAt_nodup seeds alphabet _)
            (universeAt_pairwise seeds alphabet _)
            (universeAt_pairwise seeds alphabet _)
        have hWave :
            representation ∈
              (combineWave (seededWidth stage)
                (combineLiteralOrder seeds alphabet stage)
                (combineLiteralOrder seeds alphabet
                  (stage + 1))
                (seededWidth (stage + 1))).representations := by
          simp only [combineWave]
          by_cases hBump :
              seededWidth stage < seededWidth (stage + 1)
          · rw [if_pos hBump, if_pos hWideNew,
              List.mem_append]
            by_cases hLength :
                representation.length =
                  seededWidth (stage + 1)
            · exact Or.inl
                (List.mem_sublistsLen.mpr
                  ⟨hSublist, hLength⟩)
            · apply Or.inr
              apply List.mem_filter.mpr
              refine ⟨?_, by simpa using hWide⟩
              have hNotSublist :
                  ¬ representation.Sublist
                    (combineLiteralOrder seeds alphabet
                      stage) := by
                intro hContra
                exact hPrior ⟨hContra, by omega⟩
              exact mem_introducedRepresentations_of _ _
                representation (seededWidth (stage + 1))
                (by omega) hSublist
                (hFreshFrom hNotSublist)
          · rw [if_neg hBump]
            have hSame :
                seededWidth (stage + 1) =
                  seededWidth stage := by
              have := seededWidth_le_succ stage
              omega
            apply List.mem_filter.mpr
            refine ⟨?_, by simpa using hWide⟩
            have hNotSublist :
                ¬ representation.Sublist
                  (combineLiteralOrder seeds alphabet
                    stage) := by
              intro hContra
              exact hPrior ⟨hContra, by omega⟩
            exact mem_introducedRepresentations_of _ _
              representation (seededWidth (stage + 1) + 1)
              (by omega) hSublist
              (hFreshFrom hNotSublist)
        rw [outputThroughSeeded_succ, List.mem_append]
        apply Or.inr
        rw [runSeeded_state_succ]
        refine List.mem_map_of_mem ?_
        simp only [seededWaveFromCurrent,
          List.mem_append]
        exact Or.inr hWave

/-
  Every sorted representation over the combine universe with
  admissible width occurs in the cumulative seeded output.
-/
theorem seededRepresentation_mem_outputThroughSeeded
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (stage : Nat)
    (representation : LiteralList D Γ)
    (hSublist :
      representation.Sublist
        (combineLiteralOrder seeds alphabet stage))
    (hWidth :
      representation.length ≤
        max 1 (seededWidth stage)) :
    FullEnumeration.decode representation ∈
      outputThroughSeeded alphabet seeds (stage + 1) := by
  match representation, hSublist, hWidth with
  | [], _, _ =>
      exact emptyRep_mem_outputThroughSeeded alphabet
        seeds stage
  | [literal], hSublist, _ =>
      have hMember :
          literal ∈
            seededLiteralOrder seeds alphabet stage := by
        apply universeAt_subset_of_dominates seeds alphabet
          (seededParameters_dominates_combineParameters
            stage)
        exact hSublist.subset
          (List.mem_singleton_self literal)
      exact singleton_mem_outputThroughSeeded alphabet
        seeds stage literal hMember
  | literal₁ :: literal₂ :: rest, hSublist, hWidth =>
      have hWide :
          2 ≤ (literal₁ :: literal₂ :: rest).length := by
        simp
      exact combine_mem_outputThroughSeeded alphabet seeds
        stage _ hSublist hWide (by
          simp only [List.length_cons] at hWidth ⊢
          omega)

------------------------------------------------------------
-- Seeded Reference Coverage
------------------------------------------------------------

/- The combine schedule is still cofinal. -/
theorem combineParameters_isCofinal :
    ParameterSchedule.IsCofinal combineParameters := by
  intro parameters
  rcases referenceParameters_isCofinal parameters with
    ⟨firstStage, hDominates⟩
  refine ⟨4 * firstStage + 3, fun stage hStage => ?_⟩
  obtain ⟨hBases, hOperators, hKinds, hSigns, hOps,
      hSelection, hProjection, hArity, _⟩ :=
    hDominates (combineIndex stage) (by
      simp only [combineIndex]
      omega)
  have hWidth :=
    (hDominates firstStage (Nat.le_refl _)).2.2.2.2.2.2.2.2
  simp only [referenceParameters] at hWidth
  exact ⟨hBases, hOperators, hKinds, hSigns, hOps,
    hSelection, hProjection, hArity, by
      simp only [combineParameters, combineIndex,
        seededWidth]
      omega⟩

/- Mirror of the reference file's private slice lemma. -/
omit [LinearOrder A] [LinearOrder D] in
private theorem slice_mono'
    (alphabet : Alphabet D Γ)
    {smaller larger : Parameters}
    (hDominates : larger.Dominates smaller) :
    (slice alphabet smaller).clauses ⊆
      (slice alphabet larger).clauses := by
  intro formula hFormula
  rcases
      (mem_slice_iff alphabet smaller formula).mp
        hFormula with
    ⟨representation, hNormalized, hEligible, rfl⟩
  apply (mem_slice_iff alphabet larger _).mpr
  exact
    ⟨representation, hNormalized,
      hEligible.mono hDominates, rfl⟩

/- The seeded realization satisfies the stable contract. -/
theorem seededCoversReference
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ)) :
    FastEnumerator.CoversReference alphabet
      (outputThroughSeeded alphabet seeds) := by
  intro parameters
  rcases combineParameters_isCofinal parameters with
    ⟨firstStage, hDominates⟩
  refine ⟨firstStage + 1, ?_⟩
  intro formula hFormula
  have hSmallSlice :=
    proposalFor_sound alphabet parameters hFormula
  have hLargeSlice :
      formula ∈
        (slice alphabet
          (combineParameters firstStage)).clauses :=
    slice_mono' alphabet
      (hDominates firstStage (Nat.le_refl _)) hSmallSlice
  rcases
      proposalFor_complete_up_to_equiv alphabet
        (combineParameters firstStage) formula
          hLargeSlice with
    ⟨emitted, hEmitted, hEquiv⟩
  rcases Finset.mem_image.mp hEmitted with
    ⟨representation, hRepresentation, rfl⟩
  have hBounded :
      representation ∈
        CanonicalEnumeration.boundedLiteralLists alphabet
          (combineParameters firstStage) := by
    simpa [CanonicalEnumeration.representations] using
      hRepresentation
  have hProperties :=
    (CanonicalEnumeration.mem_boundedLiteralLists_iff
      alphabet (combineParameters firstStage)
      representation).mp hBounded
  have hSeededSublist :
      representation.Sublist
        (combineLiteralOrder seeds alphabet
          firstStage) := by
    apply sublist_of_nodup_subset_pairwise
    · exact
        (CanonicalEnumeration.literalOrder_nodup alphabet
          (combineParameters firstStage)).sublist
          hProperties.1
    · intro literal hLiteral
      have hOrder := hProperties.1.subset hLiteral
      rw [CanonicalEnumeration.mem_literalOrder_iff]
        at hOrder
      rw [combineLiteralOrder, mem_universeAt_iff]
      exact Or.inr hOrder
    · exact
        (CanonicalEnumeration.literalOrder_pairwise
          alphabet (combineParameters firstStage)).sublist
          hProperties.1
    · exact universeAt_pairwise seeds alphabet
        (combineParameters firstStage)
  have hSeededWidth :
      representation.length ≤
        max 1 (seededWidth firstStage) := by
    have hBound : representation.length ≤
        (combineParameters firstStage).maxClauseWidth :=
      hProperties.2
    simp only [combineParameters] at hBound
    omega
  exact
    ⟨FullEnumeration.decode representation,
      seededRepresentation_mem_outputThroughSeeded
        alphabet seeds firstStage representation
        hSeededSublist hSeededWidth,
      hEquiv⟩

end Seeded

end Enumerators

end Synthesis

end Whiel
