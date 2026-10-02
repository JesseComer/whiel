-- Author: Jesse Comer
import Whiel.Synthesis.Enumerators.WaveMachinery
import Mathlib.Data.List.Perm.Subperm

/-
  Generic lemmas about the shared incremental wave
  machinery: the filter characterization of fresh-member
  sublists, erasure of marks, and the exact membership and
  structural properties of introduced representations.
  Nothing here mentions a stage schedule, a universe
  construction, or a realization state.

  Main declarations:
    * `sublistsLenWithFresh_eq_filter`
    * `mem_introducedRepresentations_of`
    * `properties_of_mem_introducedRepresentations`
-/

------------------------------------------------------------
-- Fresh-Sublists Characterization
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Enumerators

open DisjunctiveClause

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

@[simp] theorem freshCount_eq_zero_iff
    {T : Type}
    (values : List (Marked T)) :
    freshCount values = 0 ↔
      ∀ value ∈ values, value.2 = false := by
  induction values with
  | nil => simp [freshCount]
  | cons value rest ih =>
      cases hFresh : value.2 <;>
        simp [freshCount, hFresh, ih]

private theorem filter_sublistsLen_hasFresh_eq_nil
    {T : Type}
    (width : Nat)
    (values : List (Marked T))
    (hNoFresh : freshCount values = 0) :
    (values.sublistsLen width).filter hasFresh = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro representation hRepresentation
  have hSublist : representation.Sublist values :=
    (List.mem_sublistsLen.mp hRepresentation).1
  have hValues :=
    (freshCount_eq_zero_iff values).mp hNoFresh
  have hRepresentationValues :
      ∀ value ∈ representation, value.2 = false := by
    intro value hValue
    exact hValues value (hSublist.subset hValue)
  have hHasFresh : hasFresh representation = false := by
    simpa [hasFresh, List.any_eq_false] using
      hRepresentationValues
  simp [hHasFresh]

theorem sublistsLenWithFresh_eq_filter
    {T : Type}
    (width : Nat)
    (values : List (Marked T)) :
    sublistsLenWithFresh width values =
      (values.sublistsLen width).filter hasFresh := by
  induction values generalizing width with
  | nil =>
      cases width <;>
        simp [sublistsLenWithFresh,
          sublistsLenWithFreshResult,
          sublistsLenWithFreshAux, hasFresh]
  | cons value rest ih =>
      cases width with
      | zero =>
          simp [sublistsLenWithFresh,
            sublistsLenWithFreshResult,
            sublistsLenWithFreshAux, hasFresh]
      | succ width =>
          by_cases hTooShort : rest.length < width
          · have hWholeTooShort :
                (value :: rest).length < width + 1 := by
              simpa using Nat.succ_lt_succ hTooShort
            rw [List.sublistsLen_of_length_lt
              hWholeTooShort]
            simp only [List.filter_nil]
            cases hFresh : value.2 with
            | false =>
                cases hCount : freshCount rest with
                | zero =>
                    simp [sublistsLenWithFresh,
                      sublistsLenWithFreshResult,
                      sublistsLenWithFreshAux, freshCount,
                      hFresh, hCount]
                | succ remainingFresh =>
                    simp [sublistsLenWithFresh,
                      sublistsLenWithFreshResult,
                      sublistsLenWithFreshAux, freshCount,
                      hFresh, hCount, hTooShort]
            | true =>
                simp [sublistsLenWithFresh,
                  sublistsLenWithFreshResult,
                  sublistsLenWithFreshAux, freshCount,
                  hFresh, hTooShort]
          · cases hFresh : value.2 with
            | false =>
                by_cases hNone : freshCount rest = 0
                · rw [List.sublistsLen_succ_cons,
                    List.filter_append, List.filter_map]
                  have hPredicate :
                      hasFresh ∘ List.cons value =
                        hasFresh := by
                    funext values
                    simp [hasFresh, hFresh]
                  rw [hPredicate]
                  rw [filter_sublistsLen_hasFresh_eq_nil
                    (width + 1) rest hNone,
                    filter_sublistsLen_hasFresh_eq_nil
                      width rest hNone]
                  simp [sublistsLenWithFresh,
                    sublistsLenWithFreshResult,
                    sublistsLenWithFreshAux, freshCount,
                    hFresh, hNone]
                · obtain ⟨remainingFresh, hCount⟩ :=
                    Nat.exists_eq_succ_of_ne_zero hNone
                  have hCount' :
                      freshCount rest = remainingFresh + 1 := by
                    simpa [Nat.succ_eq_add_one] using hCount
                  rw [List.sublistsLen_succ_cons,
                    List.filter_append]
                  rw [List.filter_map]
                  have hPredicate :
                      hasFresh ∘ List.cons value =
                        hasFresh := by
                    funext values
                    simp [hasFresh, hFresh]
                  rw [hPredicate]
                  simp only [sublistsLenWithFresh,
                    sublistsLenWithFreshResult, freshCount,
                    hFresh, Bool.false_eq_true, ↓reduceIte]
                  rw [hCount']
                  simp only [sublistsLenWithFreshAux,
                    hTooShort, hFresh, Bool.false_eq_true,
                    ↓reduceIte]
                  have hExcluded :
                      (sublistsLenWithFreshAux (width + 1)
                        rest.length (remainingFresh + 1)
                        rest).values =
                        (rest.sublistsLen (width + 1)).filter
                          hasFresh := by
                    rw [← hCount']
                    exact ih (width + 1)
                  have hIncluded :
                      (sublistsLenWithFreshAux width
                        rest.length (remainingFresh + 1)
                        rest).values =
                        (rest.sublistsLen width).filter
                          hasFresh := by
                    rw [← hCount']
                    exact ih width
                  rw [hExcluded, hIncluded]
            | true =>
                rw [List.sublistsLen_succ_cons,
                  List.filter_append]
                rw [List.filter_map]
                simp only [sublistsLenWithFresh,
                  sublistsLenWithFreshResult, freshCount,
                  hFresh, ↓reduceIte]
                simp only [sublistsLenWithFreshAux,
                  hTooShort, hFresh, ↓reduceIte]
                have hExcluded :
                    (sublistsLenWithFreshAux (width + 1)
                      rest.length (freshCount rest) rest).values =
                      (rest.sublistsLen (width + 1)).filter
                        hasFresh := ih (width + 1)
                rw [hExcluded]
                simp [Function.comp_def, hasFresh, hFresh]

private theorem introducedRepresentationsAux_representations
    {A D : Type}
    [RelationNames A] [Domain D]
    {Γ : UnnamedSchema A}
    [LinearOrder A] [LinearOrder D]
    (marked : List (Marked (Literal D Γ)))
    (widths : List Nat) :
    (introducedRepresentationsAux marked marked.length
      (freshCount marked) widths).representations =
      widths.flatMap fun width =>
        (sublistsLenWithFresh width marked).map eraseMarks := by
  induction widths with
  | nil => rfl
  | cons width widths ih =>
      simp [introducedRepresentationsAux, ih,
        sublistsLenWithFresh, sublistsLenWithFreshResult]

@[simp] theorem introducedRepresentationResult_representations
    {A D : Type}
    [RelationNames A] [Domain D]
    {Γ : UnnamedSchema A}
    [LinearOrder A] [LinearOrder D]
    (prior current : List (Literal D Γ))
    (newWidth : Nat) :
    (introducedRepresentationResult prior current
      newWidth).representations =
      (List.range newWidth).flatMap fun width =>
        (sublistsLenWithFresh width
          (markCurrent prior current)).map eraseMarks := by
  exact introducedRepresentationsAux_representations
    (markCurrent prior current) (List.range newWidth)

@[simp] theorem eraseMarks_map_mark
    {A D : Type}
    [RelationNames A] [Domain D]
    {Γ : UnnamedSchema A}
    (prior values : List (Literal D Γ)) :
    eraseMarks (values.map (mark prior)) = values := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      change value :: eraseMarks (rest.map (mark prior)) =
        value :: rest
      rw [ih]

theorem hasFresh_map_mark_iff
    {A D : Type}
    [RelationNames A] [Domain D]
    {Γ : UnnamedSchema A}
    (prior values : List (Literal D Γ)) :
    hasFresh (values.map (mark prior)) = true ↔
      ∃ literal ∈ values, literal ∉ prior := by
  simp [hasFresh, mark, List.any_eq_true]

theorem mem_introducedRepresentations_of
    {A D : Type}
    [RelationNames A] [Domain D]
    {Γ : UnnamedSchema A}
    [LinearOrder A] [LinearOrder D]
    (prior current representation :
      List (Literal D Γ))
    (newWidth : Nat)
    (hWidth : representation.length < newWidth)
    (hSublist : representation.Sublist current)
    (hFresh :
      ∃ literal ∈ representation,
        literal ∉ prior) :
    representation ∈
      introducedRepresentations prior current
        newWidth := by
  rw [introducedRepresentations,
    introducedRepresentationResult_representations]
  apply List.mem_flatMap.mpr
  refine ⟨representation.length, ?_, ?_⟩
  · exact List.mem_range.mpr hWidth
  · apply List.mem_map.mpr
    refine
      ⟨representation.map (mark prior), ?_, ?_⟩
    · rw [sublistsLenWithFresh_eq_filter]
      apply List.mem_filter.mpr
      constructor
      · apply List.mem_sublistsLen.mpr
        exact
          ⟨hSublist.map (mark prior), by simp⟩
      · exact
          (hasFresh_map_mark_iff prior
            representation).mpr hFresh
    · exact eraseMarks_map_mark prior representation

theorem properties_of_mem_introducedRepresentations
    {A D : Type}
    [RelationNames A] [Domain D]
    {Γ : UnnamedSchema A}
    [LinearOrder A] [LinearOrder D]
    (prior current representation :
      List (Literal D Γ))
    (newWidth : Nat)
    (hMember :
      representation ∈
        introducedRepresentations prior current
          newWidth) :
    representation.Sublist current ∧
      representation.length < newWidth := by
  rw [introducedRepresentations,
    introducedRepresentationResult_representations] at hMember
  rcases List.mem_flatMap.mp hMember with
    ⟨width, hWidth, hRepresentation⟩
  rcases List.mem_map.mp hRepresentation with
    ⟨marked, hMarked, rfl⟩
  rw [sublistsLenWithFresh_eq_filter] at hMarked
  have hMarkedProperties :=
    List.mem_sublistsLen.mp
      (List.mem_filter.mp hMarked).1
  have hMappedSublist :=
    hMarkedProperties.1.map Prod.fst
  constructor
  · simpa [markCurrent, eraseMarks, mark,
      Function.comp_def] using hMappedSublist
  · simpa [eraseMarks] using
      (show marked.length < newWidth by
        rw [hMarkedProperties.2]
        exact List.mem_range.mp hWidth)

end Enumerators

end Synthesis

end Whiel
