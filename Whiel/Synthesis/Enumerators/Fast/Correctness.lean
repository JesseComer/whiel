-- Author: Jesse Comer
import Whiel.Synthesis.Enumerators.Fast.Enumeration
import Whiel.Synthesis.Enumerators.WaveMachineryLemmas
import Mathlib.Data.List.Perm.Subperm

/-
  Correctness results for the current replaceable fast
  enumerator implementation.

  This module imports the executable itself. Optimization
  passes may change proof bodies here, but must preserve the
  stable coverage theorem in `FastContract.lean`.

  Main declarations:
    * `sublistsLenWithFresh_eq_filter`
    * `coversReference`
-/

------------------------------------------------------------
-- Direct Fresh-Sublists Characterization
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Enumerators

namespace Fast

open DisjunctiveClause

------------------------------------------------------------
-- Executable Frontier State
------------------------------------------------------------

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}
variable [LinearOrder A] [LinearOrder D]

local instance : LinearOrder (Literal D Γ) :=
  StructuralOrder.literalLinearOrder

@[simp] theorem run_nextStage
    (alphabet : Alphabet D Γ)
    (completedStages : Nat) :
    (run alphabet completedStages).1.nextStage =
      completedStages := by
  induction completedStages with
  | zero => rfl
  | succ completedStages ih =>
      simp [run, advance, ih]

theorem run_priorLiterals_succ
    (alphabet : Alphabet D Γ)
    (stage : Nat) :
    (run alphabet (stage + 1)).1.priorLiterals =
      CanonicalEnumeration.literalOrder alphabet
        (referenceParameters stage) := by
  simp [run, advance]

@[simp] theorem outputThrough_succ
    (alphabet : Alphabet D Γ)
    (completedStages : Nat) :
    outputThrough alphabet (completedStages + 1) =
      outputThrough alphabet completedStages ++
        (advance alphabet
          (run alphabet completedStages).1).formulas := by
  rfl

theorem waveRepresentations_properties
    (alphabet : Alphabet D Γ)
    (state : State (D := D) (Γ := Γ))
    {representation : LiteralList D Γ}
    (hMember :
      representation ∈ waveRepresentations alphabet state) :
    representation.Sublist
        (CanonicalEnumeration.literalOrder alphabet
          (referenceParameters state.nextStage)) ∧
      representation.length ≤ state.nextStage := by
  cases hStage : state.nextStage with
  | zero =>
      simp [waveRepresentations, waveResult,
        waveResultFromCurrent, hStage] at hMember
      subst representation
      simp
  | succ stage =>
      simp only [waveRepresentations, waveResult,
        waveResultFromCurrent, hStage,
        List.mem_append] at hMember
      rcases hMember with hWidth | hIntroduced
      · have hProperties :=
          List.mem_sublistsLen.mp hWidth
        exact ⟨hProperties.1, hProperties.2.le⟩
      · have hProperties :=
          properties_of_mem_introducedRepresentations
            state.priorLiterals
            (CanonicalEnumeration.literalOrder alphabet
              (referenceParameters (stage + 1)))
            representation (stage + 1) hIntroduced
        simpa [hStage] using
          And.intro hProperties.1 (Nat.le_of_lt hProperties.2)

------------------------------------------------------------
-- Reference-Prefix Coverage
------------------------------------------------------------

/- Every formula in one fast wave belongs to that stage's proposal. -/
theorem advance_formula_mem_referenceProposal
    (alphabet : Alphabet D Γ)
    (state : State (D := D) (Γ := Γ))
    {formula : QFAssertExpr D Γ}
    (hMember : formula ∈ (advance alphabet state).formulas) :
    formula ∈ referenceProposal alphabet state.nextStage := by
  rcases List.mem_map.mp hMember with
    ⟨representation, hRepresentation, rfl⟩
  have hProperties :=
    waveRepresentations_properties alphabet state
      hRepresentation
  apply Finset.mem_image.mpr
  refine ⟨representation, ?_, rfl⟩
  apply
    (CanonicalEnumeration.mem_representations_iff
      alphabet (referenceParameters state.nextStage)
        representation).mpr
  simpa [referenceParameters] using hProperties

/- Cumulative fast output is contained in the matching reference stage. -/
theorem outputThrough_subset_referenceProposal
    (alphabet : Alphabet D Γ)
    (stage : Nat) :
    ∀ formula ∈ outputThrough alphabet (stage + 1),
      formula ∈ referenceProposal alphabet stage := by
  induction stage with
  | zero =>
      intro formula hFormula
      have hCurrent :
          formula ∈
            (advance alphabet
              (run alphabet 0).1).formulas := by
        simpa [outputThrough, run] using hFormula
      simpa [run_nextStage] using
        advance_formula_mem_referenceProposal alphabet
          (run alphabet 0).1 hCurrent
  | succ stage ih =>
      intro formula hFormula
      rw [outputThrough_succ, List.mem_append] at hFormula
      rcases hFormula with hPrior | hCurrent
      · exact
          referenceProposal_mono alphabet
            (Nat.le_succ stage) (ih formula hPrior)
      · simpa [run_nextStage] using
          advance_formula_mem_referenceProposal alphabet
            (run alphabet (stage + 1)).1 hCurrent

private theorem exists_fresh_of_not_sublist
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

/-
  Every representation in reference stage `stage` occurs
  in the cumulative output of the first `stage + 1` actual
  fast advances.
-/
theorem referenceRepresentation_mem_outputThrough
    (alphabet : Alphabet D Γ)
    (stage : Nat)
    (representation : LiteralList D Γ)
    (hMember :
      representation ∈
        CanonicalEnumeration.boundedLiteralLists alphabet
          (referenceParameters stage)) :
    FullEnumeration.decode representation ∈
      outputThrough alphabet (stage + 1) := by
  induction stage with
  | zero =>
      have hProperties :=
        (CanonicalEnumeration.mem_boundedLiteralLists_iff
          alphabet (referenceParameters 0)
          representation).mp hMember
      have hEmpty : representation = [] := by
        apply List.eq_nil_of_length_eq_zero
        have hLength : representation.length ≤ 0 := by
          simpa [referenceParameters] using hProperties.2
        omega
      subst representation
      simp [outputThrough, run, advance,
        waveResultFromCurrent, initialState]
  | succ stage ih =>
      let prior :=
        CanonicalEnumeration.literalOrder alphabet
          (referenceParameters stage)
      let current :=
        CanonicalEnumeration.literalOrder alphabet
          (referenceParameters (stage + 1))
      have hProperties :=
        (CanonicalEnumeration.mem_boundedLiteralLists_iff
          alphabet (referenceParameters (stage + 1))
          representation).mp hMember
      have hBound :
          representation.length ≤ stage + 1 := by
        simpa [referenceParameters] using hProperties.2
      by_cases hPrior :
          representation.Sublist prior ∧
            representation.length ≤ stage
      · have hPriorMember :
            representation ∈
              CanonicalEnumeration.boundedLiteralLists
                alphabet (referenceParameters stage) :=
          (CanonicalEnumeration.mem_boundedLiteralLists_iff
            alphabet (referenceParameters stage)
            representation).mpr hPrior
        rw [outputThrough_succ, List.mem_append]
        exact Or.inl (ih hPriorMember)
      · have hState :
            (run alphabet (stage + 1)).1 =
              { nextStage := stage + 1
                priorLiterals := prior } := by
          cases hRun : (run alphabet (stage + 1)).1 with
          | mk nextStage priorLiterals =>
              have hNext :=
                run_nextStage alphabet (stage + 1)
              have hLiterals :=
                run_priorLiterals_succ alphabet stage
              simp only [hRun] at hNext hLiterals
              subst nextStage
              subst priorLiterals
              rfl
        have hWave :
            representation ∈
              waveRepresentations alphabet
                (run alphabet (stage + 1)).1 := by
          rw [hState]
          change
            representation ∈
              current.sublistsLen (stage + 1) ++
                introducedRepresentations prior current
                  (stage + 1)
          rw [List.mem_append]
          by_cases hLength :
              representation.length = stage + 1
          · apply Or.inl
            exact List.mem_sublistsLen.mpr
              ⟨hProperties.1, hLength⟩
          · apply Or.inr
            have hShort :
                representation.length < stage + 1 := by
              omega
            have hNotSublist :
                ¬ representation.Sublist prior := by
              intro hSublist
              apply hPrior
              exact ⟨hSublist, by omega⟩
            have hFresh :
                ∃ literal ∈ representation,
                  literal ∉ prior :=
              exists_fresh_of_not_sublist prior current
                representation hProperties.1 hNotSublist
                (CanonicalEnumeration.literalOrder_nodup
                  alphabet
                  (referenceParameters (stage + 1)))
                (CanonicalEnumeration.literalOrder_pairwise
                  alphabet
                  (referenceParameters (stage + 1)))
                (CanonicalEnumeration.literalOrder_pairwise
                  alphabet (referenceParameters stage))
            exact
              mem_introducedRepresentations_of prior current
                representation (stage + 1) hShort
                hProperties.1 hFresh
        have hFormula :
            FullEnumeration.decode representation ∈
              (advance alphabet
                (run alphabet (stage + 1)).1).formulas := by
          change
            FullEnumeration.decode representation ∈
              (waveRepresentations alphabet
                (run alphabet (stage + 1)).1).map
                  FullEnumeration.decode
          exact List.mem_map_of_mem hWave
        rw [outputThrough_succ, List.mem_append]
        exact Or.inr hFormula

/- The actual fast run has exactly the reference stage's formula content. -/
theorem mem_outputThrough_iff_mem_referenceProposal
    (alphabet : Alphabet D Γ)
    (stage : Nat)
    (formula : QFAssertExpr D Γ) :
    formula ∈ outputThrough alphabet (stage + 1) ↔
      formula ∈ referenceProposal alphabet stage := by
  constructor
  · exact outputThrough_subset_referenceProposal
      alphabet stage formula
  · intro hFormula
    rcases Finset.mem_image.mp hFormula with
      ⟨representation, hRepresentation, hDecode⟩
    rw [← hDecode]
    apply referenceRepresentation_mem_outputThrough
      alphabet stage representation
    simpa [CanonicalEnumeration.representations] using
      hRepresentation

/- Set equality form of the exact fast/reference correspondence. -/
theorem outputThrough_toFinset_eq_referenceProposal
    (alphabet : Alphabet D Γ)
    (stage : Nat) :
    (outputThrough alphabet (stage + 1)).toFinset =
      referenceProposal alphabet stage := by
  ext formula
  simpa using
    mem_outputThrough_iff_mem_referenceProposal
      alphabet stage formula

/- Full-slice membership grows under parameter domination. -/
omit [LinearOrder A] [LinearOrder D] in
private theorem slice_mono
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

/- The first fast realization satisfies the stable replacement contract. -/
theorem coversReference
    (alphabet : Alphabet D Γ) :
    FastEnumerator.CoversReference alphabet
      (outputThrough alphabet) := by
  intro parameters
  rcases referenceParameters_isCofinal parameters with
    ⟨referenceStage, hDominates⟩
  refine ⟨referenceStage + 1, ?_⟩
  intro formula hFormula
  have hSmallSlice :=
    proposalFor_sound alphabet parameters hFormula
  have hLargeSlice :
      formula ∈
        (slice alphabet
          (referenceParameters referenceStage)).clauses :=
    slice_mono alphabet
      (hDominates referenceStage (Nat.le_refl _))
        hSmallSlice
  rcases
      proposalFor_complete_up_to_equiv alphabet
        (referenceParameters referenceStage) formula
          hLargeSlice with
    ⟨emitted, hEmitted, hEquiv⟩
  exact
    ⟨emitted,
      (mem_outputThrough_iff_mem_referenceProposal
        alphabet referenceStage emitted).mpr hEmitted,
      hEquiv⟩

end Fast

end Enumerators

end Synthesis

end Whiel
