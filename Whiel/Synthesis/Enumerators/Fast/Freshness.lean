-- Author: Jesse Comer
import Whiel.Synthesis.Enumerators.Fast.Correctness

/-
  Syntactic freshness of the exact executable fast waves.

  These results justify emitting `advance.formulas` directly
  at the worker boundary. No formula deduplication or
  cross-wave identity filter is required.

  Main declarations:
    * `LiteralList.formula_injective`
    * `advance_formulas_nodup`
    * `advance_formulas_disjoint_prior_output`
    * `outputThrough_nodup`
-/

------------------------------------------------------------
-- Decoding Injectivity
------------------------------------------------------------

namespace Whiel.Synthesis.DisjunctiveClause

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

theorem Atom.formula_injective :
    Function.Injective (@Atom.formula A D _ _ Γ) := by
  intro left right h
  cases left with
  | mk leftKind leftArity leftRaw rightRaw leftWf rightWf =>
    cases right with
    | mk rightKind rightArity otherLeft otherRight otherLeftWf otherRightWf =>
      cases leftKind <;> cases rightKind <;>
        simp only [Atom.formula, Atom.leftExpr, Atom.rightExpr,
          QFAssertExpr.eq, QFAssertExpr.subset] at h
      · injection h with hArity hLeft hRight
        subst rightArity
        have hLeftRaw : leftRaw = otherLeft := by
          exact congrArg RAExpr.expr (eq_of_heq hLeft)
        have hRightRaw : rightRaw = otherRight := by
          exact congrArg RAExpr.expr (eq_of_heq hRight)
        subst otherLeft
        subst otherRight
        simp
      · contradiction
      · contradiction
      · injection h with hArity hLeft hRight
        subst rightArity
        have hLeftRaw : leftRaw = otherLeft := by
          exact congrArg RAExpr.expr (eq_of_heq hLeft)
        have hRightRaw : rightRaw = otherRight := by
          exact congrArg RAExpr.expr (eq_of_heq hRight)
        subst otherLeft
        subst otherRight
        simp

private theorem Atom.formula_ne_not
    (atom : Atom D Γ)
    (formula : QFAssertExpr D Γ) :
    atom.formula ≠ QFAssertExpr.not formula := by
  rcases atom with ⟨kind, arity, left, right, leftWf, rightWf⟩
  cases kind <;>
    simp [Atom.formula, Atom.leftExpr, Atom.rightExpr]

private theorem Atom.formula_ne_false
    (atom : Atom D Γ) :
    atom.formula ≠ QFAssertExpr.«false» := by
  rcases atom with ⟨kind, arity, left, right, leftWf, rightWf⟩
  cases kind <;>
    simp [Atom.formula, Atom.leftExpr, Atom.rightExpr]

private theorem Atom.formula_ne_or
    (atom : Atom D Γ)
    (left right : QFAssertExpr D Γ) :
    atom.formula ≠ QFAssertExpr.or left right := by
  rcases atom with ⟨kind, arity, leftRaw, rightRaw,
      leftWf, rightWf⟩
  cases kind <;>
    simp [Atom.formula, Atom.leftExpr, Atom.rightExpr]

theorem Literal.formula_injective :
    Function.Injective (@Literal.formula A D _ _ Γ) := by
  intro left right h
  cases left with
  | mk leftSign leftAtom =>
    cases right with
    | mk rightSign rightAtom =>
      cases leftSign <;> cases rightSign <;>
        simp only [Literal.formula] at h
      · rw [Atom.formula_injective h]
      · exact False.elim (Atom.formula_ne_not leftAtom _ h)
      · exact False.elim (Atom.formula_ne_not rightAtom _ h.symm)
      · injection h with hAtom
        rw [Atom.formula_injective hAtom]

private theorem Literal.formula_ne_false
    (literal : Literal D Γ) :
    literal.formula ≠ QFAssertExpr.«false» := by
  cases literal with
  | mk sign atom =>
    cases sign
    · exact Atom.formula_ne_false atom
    · simp [Literal.formula]

private theorem Literal.formula_ne_or
    (literal : Literal D Γ)
    (left right : QFAssertExpr D Γ) :
    literal.formula ≠ QFAssertExpr.or left right := by
  cases literal with
  | mk sign atom =>
    cases sign
    · exact Atom.formula_ne_or atom left right
    · simp [Literal.formula]

theorem LiteralList.formula_injective :
    Function.Injective (@LiteralList.formula A D _ _ Γ) := by
  intro left
  induction left with
  | nil =>
      intro right h
      cases right with
      | nil => rfl
      | cons head tail =>
          cases tail with
          | nil =>
              exact False.elim
                (Literal.formula_ne_false head h.symm)
          | cons next rest => contradiction
  | cons head tail ih =>
      intro right h
      cases tail with
      | nil =>
          cases right with
          | nil =>
              exact False.elim
                (Literal.formula_ne_false head h)
          | cons other otherTail =>
              cases otherTail with
              | nil =>
                  rw [Literal.formula_injective h]
              | cons next rest =>
                  exact False.elim
                    (Literal.formula_ne_or head _ _ h)
      | cons next rest =>
          cases right with
          | nil => contradiction
          | cons other otherTail =>
              cases otherTail with
              | nil =>
                  exact False.elim
                    (Literal.formula_ne_or other _ _ h.symm)
              | cons otherNext otherRest =>
                  injection h with hHead hTail
                  have hHead' := Literal.formula_injective hHead
                  have hRest := ih hTail
                  rw [hHead', hRest]

end Whiel.Synthesis.DisjunctiveClause

------------------------------------------------------------
-- Exact-Wave Freshness
------------------------------------------------------------

namespace Whiel.Synthesis.Enumerators.Fast

open Whiel.Synthesis.DisjunctiveClause

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}
variable [LinearOrder A] [LinearOrder D]

omit [LinearOrder A] [LinearOrder D] in
theorem mark_injective
    (prior : List (Literal D Γ)) :
    Function.Injective (mark prior) := by
  intro left right h
  exact congrArg Prod.fst h

omit [LinearOrder A] [LinearOrder D] in
theorem markCurrent_nodup
    (prior current : List (Literal D Γ))
    (hCurrent : current.Nodup) :
    (markCurrent prior current).Nodup := by
  exact hCurrent.map (mark_injective prior)

omit [LinearOrder A] [LinearOrder D] in
theorem map_mark_eraseMarks_of_sublist_markCurrent
    (prior current : List (Literal D Γ))
    (marked : List (Literal D Γ × Bool))
    (hMarked : marked.Sublist (markCurrent prior current)) :
    (eraseMarks marked).map (mark prior) = marked := by
  induction marked with
  | nil => rfl
  | cons value rest ih =>
      have hValue : value ∈ markCurrent prior current :=
        hMarked.subset (by simp)
      rcases List.mem_map.mp hValue with
        ⟨literal, _, hLiteral⟩
      have hRest : rest.Sublist (markCurrent prior current) :=
        (List.Sublist.cons value (List.Sublist.refl rest)).trans hMarked
      subst value
      change
        mark prior literal ::
            (eraseMarks rest).map (mark prior) =
          mark prior literal :: rest
      rw [ih hRest]

omit [LinearOrder A] [LinearOrder D] in
theorem eraseMarks_injective_of_sublist_markCurrent
    (prior current : List (Literal D Γ))
    {left right : List (Literal D Γ × Bool)}
    (hLeft : left.Sublist (markCurrent prior current))
    (hRight : right.Sublist (markCurrent prior current))
    (hErase : eraseMarks left = eraseMarks right) :
    left = right := by
  rw [← map_mark_eraseMarks_of_sublist_markCurrent
      prior current left hLeft,
    ← map_mark_eraseMarks_of_sublist_markCurrent
      prior current right hRight,
    hErase]

omit [LinearOrder A] [LinearOrder D] in
theorem map_eraseMarks_sublistsLenWithFresh_nodup
    (prior current : List (Literal D Γ))
    (width : Nat)
    (hCurrent : current.Nodup) :
    ((sublistsLenWithFresh width
      (markCurrent prior current)).map eraseMarks).Nodup := by
  rw [sublistsLenWithFresh_eq_filter]
  let marked := markCurrent prior current
  have hMarked : marked.Nodup :=
    markCurrent_nodup prior current hCurrent
  have hSublists : (marked.sublistsLen width).Nodup :=
    List.nodup_sublistsLen width hMarked
  apply (hSublists.filter hasFresh).map_on
  intro left hLeft right hRight hErase
  apply eraseMarks_injective_of_sublist_markCurrent
      prior current
  · exact (List.mem_sublistsLen.mp
      (List.mem_filter.mp hLeft).1).1
  · exact (List.mem_sublistsLen.mp
      (List.mem_filter.mp hRight).1).1
  · exact hErase

omit [LinearOrder A] [LinearOrder D] in
theorem length_of_mem_map_eraseMarks_sublistsLenWithFresh
    (prior current : List (Literal D Γ))
    (width : Nat)
    {representation : LiteralList D Γ}
    (hMember : representation ∈
      (sublistsLenWithFresh width
        (markCurrent prior current)).map eraseMarks) :
    representation.length = width := by
  rcases List.mem_map.mp hMember with
    ⟨marked, hMarked, rfl⟩
  rw [sublistsLenWithFresh_eq_filter] at hMarked
  have hLength :=
    (List.mem_sublistsLen.mp
      (List.mem_filter.mp hMarked).1).2
  simpa [eraseMarks] using hLength

theorem introducedRepresentations_nodup
    (prior current : List (Literal D Γ))
    (newWidth : Nat)
    (hCurrent : current.Nodup) :
    (introducedRepresentations prior current newWidth).Nodup := by
  rw [introducedRepresentations,
    introducedRepresentationResult_representations,
    List.nodup_flatMap]
  constructor
  · intro width hWidth
    exact map_eraseMarks_sublistsLenWithFresh_nodup
      prior current width hCurrent
  · apply List.nodup_range.imp
    intro left right hNe
    change
      ((sublistsLenWithFresh left
        (markCurrent prior current)).map eraseMarks).Disjoint
      ((sublistsLenWithFresh right
        (markCurrent prior current)).map eraseMarks)
    rw [List.disjoint_left]
    intro representation hLeft hRight
    have hLeftLength :=
      length_of_mem_map_eraseMarks_sublistsLenWithFresh
        prior current left hLeft
    have hRightLength :=
      length_of_mem_map_eraseMarks_sublistsLenWithFresh
        prior current right hRight
    exact hNe (hLeftLength.symm.trans hRightLength)

theorem length_lt_of_mem_introducedRepresentations
    (prior current : List (Literal D Γ))
    (newWidth : Nat)
    {representation : LiteralList D Γ}
    (hMember : representation ∈
      introducedRepresentations prior current newWidth) :
    representation.length < newWidth := by
  exact (properties_of_mem_introducedRepresentations
    prior current representation newWidth hMember).2

theorem exact_disjoint_introducedRepresentations
    (prior current : List (Literal D Γ))
    (newWidth : Nat) :
    (current.sublistsLen newWidth).Disjoint
      (introducedRepresentations prior current newWidth) := by
  rw [List.disjoint_left]
  intro representation hExact hIntroduced
  have hExactLength := (List.mem_sublistsLen.mp hExact).2
  have hIntroducedLength :=
    length_lt_of_mem_introducedRepresentations
      prior current newWidth hIntroduced
  omega

theorem waveRepresentations_nodup
    (alphabet : Alphabet D Γ)
    (state : State (D := D) (Γ := Γ)) :
    (waveRepresentations alphabet state).Nodup := by
  let current := CanonicalEnumeration.literalOrder alphabet
    (referenceParameters state.nextStage)
  have hCurrent : current.Nodup :=
    CanonicalEnumeration.literalOrder_nodup alphabet
      (referenceParameters state.nextStage)
  cases hStage : state.nextStage with
  | zero =>
      simp [waveRepresentations, waveResult,
        waveResultFromCurrent, hStage]
  | succ stage =>
      rw [waveRepresentations, waveResult,
        waveResultFromCurrent]
      simp only [hStage]
      apply List.Nodup.append
      · exact List.nodup_sublistsLen (stage + 1)
          (CanonicalEnumeration.literalOrder_nodup alphabet
            (referenceParameters (stage + 1)))
      · simpa [introducedRepresentations] using
          introducedRepresentations_nodup
            state.priorLiterals
            (CanonicalEnumeration.literalOrder alphabet
              (referenceParameters (stage + 1)))
            (stage + 1)
            (CanonicalEnumeration.literalOrder_nodup alphabet
              (referenceParameters (stage + 1)))
      · simpa [introducedRepresentations] using
          exact_disjoint_introducedRepresentations
            state.priorLiterals
            (CanonicalEnumeration.literalOrder alphabet
              (referenceParameters (stage + 1)))
            (stage + 1)

theorem advance_formulas_nodup
    (alphabet : Alphabet D Γ)
    (state : State (D := D) (Γ := Γ)) :
    (advance alphabet state).formulas.Nodup := by
  change
    ((waveRepresentations alphabet state).map
      FullEnumeration.decode).Nodup
  exact (waveRepresentations_nodup alphabet state).map
    LiteralList.formula_injective

theorem fresh_of_mem_introducedRepresentations
    (prior current : List (Literal D Γ))
    (newWidth : Nat)
    {representation : LiteralList D Γ}
    (hMember : representation ∈
      introducedRepresentations prior current newWidth) :
    ∃ literal ∈ representation, literal ∉ prior := by
  rw [introducedRepresentations,
    introducedRepresentationResult_representations] at hMember
  rcases List.mem_flatMap.mp hMember with
    ⟨width, _, hRepresentation⟩
  rcases List.mem_map.mp hRepresentation with
    ⟨marked, hMarked, rfl⟩
  rw [sublistsLenWithFresh_eq_filter] at hMarked
  have hSublist :=
    (List.mem_sublistsLen.mp
      (List.mem_filter.mp hMarked).1).1
  have hHasFresh := (List.mem_filter.mp hMarked).2
  have hRestore :=
    map_mark_eraseMarks_of_sublist_markCurrent
      prior current marked hSublist
  rw [← hRestore] at hHasFresh
  exact (hasFresh_map_mark_iff prior (eraseMarks marked)).mp
    hHasFresh

theorem run_state_succ
    (alphabet : Alphabet D Γ)
    (stage : Nat) :
    (run alphabet (stage + 1)).1 =
      { nextStage := stage + 1
        priorLiterals :=
          CanonicalEnumeration.literalOrder alphabet
            (referenceParameters stage) } := by
  cases hRun : (run alphabet (stage + 1)).1 with
  | mk nextStage priorLiterals =>
      have hNext := run_nextStage alphabet (stage + 1)
      have hPrior := run_priorLiterals_succ alphabet stage
      simp only [hRun] at hNext hPrior
      subst nextStage
      subst priorLiterals
      rfl

theorem waveRepresentation_not_mem_previous
    (alphabet : Alphabet D Γ)
    (stage : Nat)
    {representation : LiteralList D Γ}
    (hMember : representation ∈
      waveRepresentations alphabet
        (run alphabet (stage + 1)).1) :
    representation ∉
      CanonicalEnumeration.boundedLiteralLists alphabet
        (referenceParameters stage) := by
  rw [run_state_succ alphabet stage,
    waveRepresentations, waveResult,
    waveResultFromCurrent] at hMember
  simp only at hMember
  rw [List.mem_append] at hMember
  intro hPrevious
  have hPreviousProperties :=
    (CanonicalEnumeration.mem_boundedLiteralLists_iff
      alphabet (referenceParameters stage) representation).mp
      hPrevious
  rcases hMember with hExact | hIntroduced
  · have hExactLength := (List.mem_sublistsLen.mp hExact).2
    have hPreviousLength : representation.length ≤ stage := by
      simpa [referenceParameters] using hPreviousProperties.2
    omega
  · have hFresh := fresh_of_mem_introducedRepresentations
      (CanonicalEnumeration.literalOrder alphabet
        (referenceParameters stage))
      (CanonicalEnumeration.literalOrder alphabet
        (referenceParameters (stage + 1)))
      (stage + 1) hIntroduced
    rcases hFresh with ⟨literal, hLiteral, hNotPrior⟩
    exact hNotPrior (hPreviousProperties.1.subset hLiteral)

theorem advance_formula_not_mem_previous
    (alphabet : Alphabet D Γ)
    (stage : Nat)
    {formula : QFAssertExpr D Γ}
    (hMember : formula ∈
      (advance alphabet (run alphabet (stage + 1)).1).formulas) :
    formula ∉ referenceProposal alphabet stage := by
  rcases List.mem_map.mp hMember with
    ⟨representation, hRepresentation, hDecode⟩
  intro hPrevious
  rcases Finset.mem_image.mp hPrevious with
    ⟨priorRepresentation, hPriorRepresentation,
      hPriorDecode⟩
  have hRepresentationEq :
      representation = priorRepresentation :=
    LiteralList.formula_injective
      (hDecode.trans hPriorDecode.symm)
  subst priorRepresentation
  apply waveRepresentation_not_mem_previous alphabet stage
    hRepresentation
  simpa [CanonicalEnumeration.representations] using
    hPriorRepresentation

theorem advance_formulas_disjoint_prior_output
    (alphabet : Alphabet D Γ)
    (stage : Nat) :
    (advance alphabet
      (run alphabet (stage + 1)).1).formulas.Disjoint
        (outputThrough alphabet (stage + 1)) := by
  rw [List.disjoint_left]
  intro formula hCurrent hPrior
  apply advance_formula_not_mem_previous alphabet stage hCurrent
  exact (mem_outputThrough_iff_mem_referenceProposal
    alphabet stage formula).mp hPrior

theorem outputThrough_nodup
    (alphabet : Alphabet D Γ)
    (completedStages : Nat) :
    (outputThrough alphabet completedStages).Nodup := by
  induction completedStages with
  | zero => simp [outputThrough, run]
  | succ completedStages ih =>
      rw [outputThrough_succ]
      apply List.Nodup.append ih
        (advance_formulas_nodup alphabet
          (run alphabet completedStages).1)
      cases completedStages with
      | zero => simp [outputThrough, run]
      | succ stage =>
          exact (advance_formulas_disjoint_prior_output
            alphabet stage).symm

end Whiel.Synthesis.Enumerators.Fast
