-- Author: Jesse Comer
import Whiel.Synthesis.Enumerators.Capped.Enumeration
import Whiel.Synthesis.Enumerators.Seeded.Correctness

/-
  Correctness of the participation-capped seeded
  realization: the capped stream satisfies the stable
  finite-prefix coverage contract, provided the schedule is
  *admitting* --- infinitely many stages budget the whole
  currently available universe. The default amnesty
  schedule is admitting by construction.

  Main declarations:
    * `admittedAt` and its monotonicity and containment
    * `Admitting` and `defaultSchedule_admitting`
    * `cappedCoversReference`
-/

------------------------------------------------------------
-- Admission Algebra
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

/- Previously admitted literals are never revoked. -/
omit [LinearOrder A] [LinearOrder D] in
theorem subset_admitStep
    (available : List (Literal D Γ))
    (admitted : Finset (Literal D Γ))
    (budget : Nat) :
    admitted ⊆ admitStep available admitted budget :=
  Finset.subset_union_left

/- Admission introduces only available literals. -/
omit [LinearOrder A] [LinearOrder D] in
theorem admitStep_subset
    (available : List (Literal D Γ))
    (admitted : Finset (Literal D Γ))
    (budget : Nat) :
    admitStep available admitted budget ⊆
      admitted ∪ available.toFinset := by
  intro literal hLiteral
  rcases Finset.mem_union.mp hLiteral with hOld | hNew
  · exact Finset.mem_union_left _ hOld
  · apply Finset.mem_union_right
    have hTake := List.mem_of_mem_take
      (List.mem_toFinset.mp hNew)
    exact List.mem_toFinset.mpr
      (List.mem_of_mem_filter hTake)

/-
  A budget covering a bounding set plus the whole available
  universe admits every available literal: the admitted set
  splits into its part outside `available` (contained in the
  bound) and its part inside, and the exact counting
  `admitted.card + fresh.length = outside.card +
  available.length` puts the whole fresh list inside the
  take.
-/
omit [LinearOrder A] [LinearOrder D] in
theorem available_subset_admitStep
    (available : List (Literal D Γ))
    (admitted bound : Finset (Literal D Γ))
    (budget : Nat)
    (hAvailable : available.Nodup)
    (hAdmitted : admitted ⊆ bound ∪ available.toFinset)
    (hBudget :
      bound.card + available.length ≤ budget) :
    available.toFinset ⊆
      admitStep available admitted budget := by
  intro literal hLiteral
  by_cases hOld : literal ∈ admitted
  · exact Finset.mem_union_left _ hOld
  · apply Finset.mem_union_right
    have hMemFresh :
        literal ∈
          available.filter (fun l => l ∉ admitted) := by
      refine List.mem_filter.mpr ⟨?_, ?_⟩
      · exact List.mem_toFinset.mp hLiteral
      · simpa using hOld
    have hOutside :
        (admitted.filter
          (fun l => l ∉ available)).card ≤ bound.card := by
      apply Finset.card_le_card
      intro l hMem
      rcases Finset.mem_filter.mp hMem with ⟨hAdm, hNot⟩
      rcases Finset.mem_union.mp (hAdmitted hAdm) with
        hBound | hAvail
      · exact hBound
      · exact absurd (List.mem_toFinset.mp hAvail) hNot
    have hSplit :
        (admitted.filter (fun l => l ∉ available)).card +
          (admitted.filter
            (fun l => l ∈ available)).card =
          admitted.card := by
      simpa using
        Finset.card_filter_add_card_filter_not
          (s := admitted)
          (p := fun l => l ∉ available)
    have hInterEq :
        (admitted.filter (fun l => l ∈ available)).card =
          (available.filter
            (fun l => l ∈ admitted)).length := by
      have hSetEq :
          admitted.filter (fun l => l ∈ available) =
            (available.filter
              (fun l => l ∈ admitted)).toFinset := by
        ext l
        simp [and_comm]
      rw [hSetEq,
        List.toFinset_card_of_nodup
          (hAvailable.filter _)]
    have hPartition :
        (available.filter
            (fun l => l ∈ admitted)).length +
          (available.filter
            (fun l => l ∉ admitted)).length =
          available.length := by
      have hPerm :=
        (List.filter_append_perm
          (fun l => decide (l ∈ admitted)) available)
      have hLen := hPerm.length_eq
      simpa [List.length_append] using hLen
    have hTakeAll :
        (available.filter
            (fun l => l ∉ admitted)).take
          (budget - admitted.card) =
          available.filter (fun l => l ∉ admitted) := by
      apply List.take_of_length_le
      omega
    rw [hTakeAll]
    exact List.mem_toFinset.mpr hMemFresh

------------------------------------------------------------
-- Run Plumbing
------------------------------------------------------------

/- The admitted set after a number of completed stages. -/
def admittedAt
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (schedule : Schedule)
    (stage : Nat) :
    Finset (Literal D Γ) :=
  (runSeededCapped alphabet seeds schedule stage).1.admitted

@[simp] theorem runSeededCapped_nextStage
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (schedule : Schedule)
    (stage : Nat) :
    (runSeededCapped alphabet seeds schedule
      stage).1.nextStage = stage := by
  induction stage with
  | zero => rfl
  | succ stage ih =>
      simp [runSeededCapped, advanceSeededCapped, ih]

@[simp] theorem admittedAt_zero
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (schedule : Schedule) :
    admittedAt alphabet seeds schedule 0 = seeds := rfl

theorem admittedAt_succ
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (schedule : Schedule)
    (stage : Nat) :
    admittedAt alphabet seeds schedule (stage + 1) =
      admitStep
        (combineLiteralOrder seeds alphabet stage)
        (admittedAt alphabet seeds schedule stage)
        (schedule stage
          (combineLiteralOrder seeds alphabet
            stage).length) := by
  simp [admittedAt, runSeededCapped, advanceSeededCapped]

theorem admittedAt_le_succ
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (schedule : Schedule)
    (stage : Nat) :
    admittedAt alphabet seeds schedule stage ⊆
      admittedAt alphabet seeds schedule (stage + 1) := by
  rw [admittedAt_succ]
  exact subset_admitStep _ _ _

theorem admittedAt_mono
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (schedule : Schedule)
    {smaller larger : Nat}
    (hStages : smaller ≤ larger) :
    admittedAt alphabet seeds schedule smaller ⊆
      admittedAt alphabet seeds schedule larger := by
  induction larger, hStages using Nat.le_induction with
  | base => exact fun _ h => h
  | succ larger _ ih =>
      exact fun literal hLiteral =>
        admittedAt_le_succ alphabet seeds schedule larger
          (ih hLiteral)

/-
  Everything ever admitted is a seed or lies in the current
  available universe (which only grows with the stage).
-/
theorem admittedAt_subset
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (schedule : Schedule)
    (stage : Nat) :
    admittedAt alphabet seeds schedule stage ⊆
      seeds ∪
        (combineLiteralOrder seeds alphabet
          stage).toFinset := by
  induction stage with
  | zero =>
      simp only [admittedAt_zero]
      exact Finset.subset_union_left
  | succ stage ih =>
      rw [admittedAt_succ]
      intro literal hLiteral
      rcases Finset.mem_union.mp
          (admitStep_subset _ _ _ hLiteral) with
        hOld | hNew
      · rcases Finset.mem_union.mp (ih hOld) with
          hSeed | hAvail
        · exact Finset.mem_union_left _ hSeed
        · apply Finset.mem_union_right
          apply List.mem_toFinset.mpr
          exact
            (combineLiteralOrder_sublist_succ seeds
              alphabet stage).subset
              (List.mem_toFinset.mp hAvail)
      · apply Finset.mem_union_right
        apply List.mem_toFinset.mpr
        exact
          (combineLiteralOrder_sublist_succ seeds
            alphabet stage).subset
            (List.mem_toFinset.mp hNew)

------------------------------------------------------------
-- Sorted Admitted Views
------------------------------------------------------------

theorem admittedOrder_nodup
    (admitted : Finset (Literal D Γ)) :
    (admittedOrder admitted).Nodup :=
  Finset.sort_nodup _ _

theorem admittedOrder_pairwise
    (admitted : Finset (Literal D Γ)) :
    (admittedOrder admitted).Pairwise (· ≤ ·) :=
  Finset.pairwise_sort _ _

@[simp] theorem mem_admittedOrder_iff
    (admitted : Finset (Literal D Γ))
    (literal : Literal D Γ) :
    literal ∈ admittedOrder admitted ↔
      literal ∈ admitted := by
  simp [admittedOrder]

theorem admittedOrder_sublist_of_subset
    {smaller larger : Finset (Literal D Γ)}
    (hSubset : smaller ⊆ larger) :
    (admittedOrder smaller).Sublist
      (admittedOrder larger) := by
  apply sublist_of_nodup_subset_pairwise
    (admittedOrder_nodup smaller)
  · intro literal hLiteral
    exact (mem_admittedOrder_iff larger literal).mpr
      (hSubset
        ((mem_admittedOrder_iff smaller literal).mp
          hLiteral))
  · exact admittedOrder_pairwise smaller
  · exact admittedOrder_pairwise larger

------------------------------------------------------------
-- Output Plumbing
------------------------------------------------------------

theorem runSeededCapped_priorSingleton_succ
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (schedule : Schedule)
    (stage : Nat) :
    (runSeededCapped alphabet seeds schedule
      (stage + 1)).1.priorSingleton =
      seededLiteralOrder seeds alphabet stage := by
  simp [runSeededCapped, advanceSeededCapped]

theorem outputThroughSeededCapped_succ
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (schedule : Schedule)
    (completedStages : Nat) :
    outputThroughSeededCapped alphabet seeds schedule
        (completedStages + 1) =
      outputThroughSeededCapped alphabet seeds schedule
          completedStages ++
        (advanceSeededCapped alphabet seeds schedule
          (runSeededCapped alphabet seeds schedule
            completedStages).1).formulas := by
  simp [outputThroughSeededCapped, runSeededCapped]

theorem mem_outputThroughSeededCapped_succ_of_mem
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (schedule : Schedule)
    (completedStages : Nat)
    {formula : QFAssertExpr D Γ}
    (hMember :
      formula ∈
        outputThroughSeededCapped alphabet seeds schedule
          completedStages) :
    formula ∈
      outputThroughSeededCapped alphabet seeds schedule
        (completedStages + 1) := by
  rw [outputThroughSeededCapped_succ, List.mem_append]
  exact Or.inl hMember

------------------------------------------------------------
-- Admitting Schedules
------------------------------------------------------------

/-
  A schedule is admitting when, beyond every stage, some
  stage budgets the seeds plus its whole available
  universe. Coverage requires this: schedule unboundedness
  alone is insufficient, because the available universe
  also grows without bound and canonical-order admission
  can be preempted indefinitely.
-/
def Admitting
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (schedule : Schedule) : Prop :=
  ∀ stage₀, ∃ stage, stage₀ ≤ stage ∧
    seeds.card +
        (combineLiteralOrder seeds alphabet
          stage).length ≤
      schedule stage
        (combineLiteralOrder seeds alphabet stage).length

/- Amnesty stages make the default schedule admitting. -/
theorem defaultSchedule_admitting
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ)) :
    Admitting alphabet seeds
      (defaultSchedule seeds.card) := by
  intro stage₀
  refine ⟨stage₀ * amnestyPeriod + (amnestyPeriod - 1),
    ?_, ?_⟩
  · simp only [amnestyPeriod]
    omega
  · have hAmnesty :
        (stage₀ * amnestyPeriod + (amnestyPeriod - 1) + 1) %
            amnestyPeriod = 0 := by
      simp only [amnestyPeriod]
      omega
    simp [defaultSchedule, hAmnesty]

/-
  At an admitting stage, the whole available universe is
  admitted at the next stage.
-/
theorem available_admitted_of_admitting_stage
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (schedule : Schedule)
    (stage : Nat)
    (hBudget :
      seeds.card +
          (combineLiteralOrder seeds alphabet
            stage).length ≤
        schedule stage
          (combineLiteralOrder seeds alphabet
            stage).length) :
    (combineLiteralOrder seeds alphabet
        stage).toFinset ⊆
      admittedAt alphabet seeds schedule (stage + 1) := by
  rw [admittedAt_succ]
  exact available_subset_admitStep _ _ seeds _
    (universeAt_nodup seeds alphabet _)
    (admittedAt_subset alphabet seeds schedule stage)
    hBudget


------------------------------------------------------------
-- Wave Membership
------------------------------------------------------------

/- Local copy of the seeded file's private lemma. -/
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

theorem runSeededCapped_state_succ
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (schedule : Schedule)
    (stage : Nat) :
    (runSeededCapped alphabet seeds schedule
      (stage + 1)).1 =
      { nextStage := stage + 1
        priorSingleton :=
          seededLiteralOrder seeds alphabet stage
        admitted :=
          admittedAt alphabet seeds schedule
            (stage + 1) } := by
  cases hRun :
      (runSeededCapped alphabet seeds schedule
        (stage + 1)).1 with
  | mk nextStage priorSingleton admitted =>
      have hNext :=
        runSeededCapped_nextStage alphabet seeds schedule
          (stage + 1)
      have hSingle :=
        runSeededCapped_priorSingleton_succ alphabet seeds
          schedule stage
      have hAdmitted :
          (runSeededCapped alphabet seeds schedule
            (stage + 1)).1.admitted =
            admittedAt alphabet seeds schedule
              (stage + 1) := rfl
      simp only [hRun] at hNext hSingle hAdmitted
      subst nextStage
      subst priorSingleton
      subst admitted
      rfl

theorem emptyRep_mem_outputThroughSeededCapped
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (schedule : Schedule)
    (stage : Nat) :
    FullEnumeration.decode ([] : LiteralList D Γ) ∈
      outputThroughSeededCapped alphabet seeds schedule
        (stage + 1) := by
  induction stage with
  | zero =>
      simp [outputThroughSeededCapped, runSeededCapped,
        advanceSeededCapped, seededWaveFromCurrent,
        initialCappedState]
  | succ stage ih =>
      exact mem_outputThroughSeededCapped_succ_of_mem
        alphabet seeds schedule (stage + 1) ih

/-
  Every literal appears as a width-one clause by the first
  stage whose singleton universe contains it: the singleton
  stream is uncapped.
-/
theorem singleton_mem_outputThroughSeededCapped
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (schedule : Schedule)
    (stage : Nat)
    (literal : Literal D Γ)
    (hMember :
      literal ∈ seededLiteralOrder seeds alphabet stage) :
    FullEnumeration.decode [literal] ∈
      outputThroughSeededCapped alphabet seeds schedule
        (stage + 1) := by
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
      simpa [outputThroughSeededCapped, runSeededCapped,
        advanceSeededCapped, seededWaveFromCurrent,
        initialCappedState] using
        List.mem_map_of_mem
          (f := FullEnumeration.decode) hWave
  | succ stage ih =>
      by_cases hPrior :
          literal ∈ seededLiteralOrder seeds alphabet stage
      · exact mem_outputThroughSeededCapped_succ_of_mem
          alphabet seeds schedule (stage + 1) (ih hPrior)
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
        rw [outputThroughSeededCapped_succ,
          List.mem_append]
        apply Or.inr
        rw [runSeededCapped_state_succ]
        refine List.mem_map_of_mem ?_
        simp only [seededWaveFromCurrent,
          List.mem_append]
        exact Or.inl hWave

/-
  Every wide sorted representation over the admitted
  universe with admissible width occurs in the cumulative
  capped output.
-/
theorem combine_mem_outputThroughSeededCapped
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (schedule : Schedule)
    (stage : Nat)
    (representation : LiteralList D Γ)
    (hSublist :
      representation.Sublist
        (admittedOrder
          (admittedAt alphabet seeds schedule
            (stage + 1))))
    (hWide : 2 ≤ representation.length)
    (hWidth :
      representation.length ≤ seededWidth stage) :
    FullEnumeration.decode representation ∈
      outputThroughSeededCapped alphabet seeds schedule
        (stage + 1) := by
  induction stage with
  | zero =>
      have hZero : seededWidth 0 = 0 := rfl
      omega
  | succ stage ih =>
      by_cases hPrior :
          representation.Sublist
              (admittedOrder
                (admittedAt alphabet seeds schedule
                  (stage + 1))) ∧
            representation.length ≤ seededWidth stage
      · exact mem_outputThroughSeededCapped_succ_of_mem
          alphabet seeds schedule (stage + 1)
          (ih hPrior.1 hPrior.2)
      · have hFreshFrom :
            ¬ representation.Sublist
                (admittedOrder
                  (admittedAt alphabet seeds schedule
                    (stage + 1))) →
              ∃ literal ∈ representation,
                literal ∉
                  admittedOrder
                    (admittedAt alphabet seeds schedule
                      (stage + 1)) := by
          intro hNotSublist
          exact exists_fresh_of_not_sublist'
            (admittedOrder
              (admittedAt alphabet seeds schedule
                (stage + 1)))
            (admittedOrder
              (admittedAt alphabet seeds schedule
                (stage + 2)))
            representation hSublist hNotSublist
            (admittedOrder_nodup _)
            (admittedOrder_pairwise _)
            (admittedOrder_pairwise _)
        have hWave :
            representation ∈
              (combineWave (seededWidth stage)
                (admittedOrder
                  (admittedAt alphabet seeds schedule
                    (stage + 1)))
                (admittedOrder
                  (admittedAt alphabet seeds schedule
                    (stage + 2)))
                (seededWidth
                  (stage + 1))).representations := by
          simp only [combineWave]
          by_cases hBump :
              seededWidth stage < seededWidth (stage + 1)
          · rw [if_pos hBump, if_pos (by omega :
              2 ≤ seededWidth (stage + 1)),
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
                    (admittedOrder
                      (admittedAt alphabet seeds schedule
                        (stage + 1))) := by
                intro hContra
                have hStep :
                    seededWidth (stage + 1) ≤
                      seededWidth stage + 1 := by
                  simp only [seededWidth]
                  omega
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
                  (admittedOrder
                    (admittedAt alphabet seeds schedule
                      (stage + 1))) := by
              intro hContra
              exact hPrior ⟨hContra, by omega⟩
            exact mem_introducedRepresentations_of _ _
              representation (seededWidth (stage + 1) + 1)
              (by omega) hSublist
              (hFreshFrom hNotSublist)
        rw [outputThroughSeededCapped_succ,
          List.mem_append]
        apply Or.inr
        rw [runSeededCapped_state_succ]
        refine List.mem_map_of_mem ?_
        simp only [seededWaveFromCurrent,
          List.mem_append]
        refine Or.inr ?_
        rw [← admittedAt_succ]
        exact hWave

------------------------------------------------------------
-- Capped Reference Coverage
------------------------------------------------------------

/- The available combine universe grows with the stage. -/
theorem combineLiteralOrder_subset_of_le
    (seeds : Finset (Literal D Γ))
    (alphabet : Alphabet D Γ)
    {smaller larger : Nat}
    (hStages : smaller ≤ larger) :
    combineLiteralOrder seeds alphabet smaller ⊆
      combineLiteralOrder seeds alphabet larger := by
  induction larger, hStages using Nat.le_induction with
  | base => exact fun _ h => h
  | succ larger _ ih =>
      exact fun literal hLiteral =>
        (combineLiteralOrder_sublist_succ seeds alphabet
          larger).subset (ih hLiteral)

omit [RelationNames A] [Domain D]
  [LinearOrder A] [LinearOrder D] in
theorem seededWidth_mono
    {smaller larger : Nat}
    (hStages : smaller ≤ larger) :
    seededWidth smaller ≤ seededWidth larger := by
  simp only [seededWidth]
  omega

/-
  Dispatch by width: every sorted representation over the
  admitted universe with admissible width occurs in the
  cumulative capped output.
-/
theorem cappedRepresentation_mem
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (schedule : Schedule)
    (stage : Nat)
    (representation : LiteralList D Γ)
    (hSublist :
      representation.Sublist
        (admittedOrder
          (admittedAt alphabet seeds schedule
            (stage + 1))))
    (hWidth :
      representation.length ≤
        max 1 (seededWidth (stage + 1))) :
    FullEnumeration.decode representation ∈
      outputThroughSeededCapped alphabet seeds schedule
        (stage + 2) := by
  match representation, hSublist, hWidth with
  | [], _, _ =>
      exact emptyRep_mem_outputThroughSeededCapped
        alphabet seeds schedule (stage + 1)
  | [literal], hSublist, _ =>
      have hAdmitted :
          literal ∈
            admittedAt alphabet seeds schedule
              (stage + 1) :=
        (mem_admittedOrder_iff _ literal).mp
          (hSublist.subset
            (List.mem_singleton_self literal))
      have hMember :
          literal ∈
            seededLiteralOrder seeds alphabet
              (stage + 1) := by
        rcases Finset.mem_union.mp
            (admittedAt_subset alphabet seeds schedule
              (stage + 1) hAdmitted) with
          hSeed | hAvail
        · rw [seededLiteralOrder, mem_universeAt_iff]
          exact Or.inl hSeed
        · apply universeAt_subset_of_dominates seeds
            alphabet
            (seededParameters_dominates_combineParameters
              (stage + 1))
          exact List.mem_toFinset.mp hAvail
      exact singleton_mem_outputThroughSeededCapped
        alphabet seeds schedule (stage + 1) literal
        hMember
  | literal₁ :: literal₂ :: rest, hSublist, hWidth =>
      have hWide :
          2 ≤ (literal₁ :: literal₂ :: rest).length := by
        simp
      have hLift :
          (literal₁ :: literal₂ :: rest).Sublist
            (admittedOrder
              (admittedAt alphabet seeds schedule
                (stage + 2))) :=
        hSublist.trans
          (admittedOrder_sublist_of_subset
            (admittedAt_le_succ alphabet seeds schedule
              (stage + 1)))
      exact combine_mem_outputThroughSeededCapped alphabet
        seeds schedule (stage + 1) _ hLift hWide (by
          simp only [List.length_cons] at hWidth ⊢
          omega)

/- Mirror of the reference file's private slice lemma. -/
omit [LinearOrder A] [LinearOrder D] in
private theorem slice_mono''
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

/-
  The capped realization satisfies the stable contract for
  every admitting schedule.
-/
theorem cappedCoversReference
    (alphabet : Alphabet D Γ)
    (seeds : Finset (Literal D Γ))
    (schedule : Schedule)
    (hAdmitting : Admitting alphabet seeds schedule) :
    FastEnumerator.CoversReference alphabet
      (outputThroughSeededCapped alphabet seeds
        schedule) := by
  intro parameters
  rcases combineParameters_isCofinal parameters with
    ⟨firstStage, hDominates⟩
  rcases hAdmitting firstStage with
    ⟨admitStage, hLate, hBudget⟩
  set finalStage :=
    max admitStage
      (2 * (combineParameters
        firstStage).maxClauseWidth) with hFinal
  refine ⟨finalStage + 2, ?_⟩
  intro formula hFormula
  have hSmallSlice :=
    proposalFor_sound alphabet parameters hFormula
  have hLargeSlice :
      formula ∈
        (slice alphabet
          (combineParameters firstStage)).clauses :=
    slice_mono'' alphabet
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
  have hAvailable :
      ∀ literal ∈ representation,
        literal ∈
          combineLiteralOrder seeds alphabet
            firstStage := by
    intro literal hLiteral
    have hOrder := hProperties.1.subset hLiteral
    rw [CanonicalEnumeration.mem_literalOrder_iff]
      at hOrder
    rw [combineLiteralOrder, mem_universeAt_iff]
    exact Or.inr hOrder
  have hAdmittedAll :
      ∀ literal ∈ representation,
        literal ∈
          admittedAt alphabet seeds schedule
            (finalStage + 1) := by
    intro literal hLiteral
    have hInAdmit :
        literal ∈
          admittedAt alphabet seeds schedule
            (admitStage + 1) := by
      apply available_admitted_of_admitting_stage
        alphabet seeds schedule admitStage hBudget
      apply List.mem_toFinset.mpr
      exact combineLiteralOrder_subset_of_le seeds
        alphabet hLate (hAvailable literal hLiteral)
    exact admittedAt_mono alphabet seeds schedule
      (by omega : admitStage + 1 ≤ finalStage + 1)
      hInAdmit
  have hCappedSublist :
      representation.Sublist
        (admittedOrder
          (admittedAt alphabet seeds schedule
            (finalStage + 1))) := by
    apply sublist_of_nodup_subset_pairwise
    · exact
        (CanonicalEnumeration.literalOrder_nodup alphabet
          (combineParameters firstStage)).sublist
          hProperties.1
    · intro literal hLiteral
      exact (mem_admittedOrder_iff _ literal).mpr
        (hAdmittedAll literal hLiteral)
    · exact
        (CanonicalEnumeration.literalOrder_pairwise
          alphabet (combineParameters firstStage)).sublist
          hProperties.1
    · exact admittedOrder_pairwise _
  have hCappedWidth :
      representation.length ≤
        max 1 (seededWidth (finalStage + 1)) := by
    have hBound : representation.length ≤
        (combineParameters firstStage).maxClauseWidth :=
      hProperties.2
    have hWide :
        (combineParameters firstStage).maxClauseWidth ≤
          seededWidth (finalStage + 1) := by
      have hLe :
          2 * (combineParameters
            firstStage).maxClauseWidth ≤ finalStage := by
        omega
      simp only [seededWidth]
      omega
    omega
  exact
    ⟨FullEnumeration.decode representation,
      cappedRepresentation_mem alphabet seeds schedule
        finalStage representation hCappedSublist
        hCappedWidth,
      hEquiv⟩


end Capped

end Enumerators

end Synthesis

end Whiel
