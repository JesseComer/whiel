import Databases.RelCalc.AdomSemantics

/-
  Executable empty-active-domain counterexample checks for
  RelCalc entailments.

  Key definitions:
    * `RelCalc.SentenceEntailment.emptyCounterexample?`

  The final theorem shows that the Boolean search exactly
  decides `NoEmptyCounterexample`.

  The search only needs to consider choices for nullary
  relations, because every positive-arity relation is empty
  when the active domain is empty.
-/

------------------------------------------------------------
-- Nullary Assignment Support
------------------------------------------------------------

namespace RelCalc

namespace SentenceEntailment

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- Empty active finset implies empty instance adom. -/
private theorem adomEmpty_of_activeFinset_eq_empty
    (E : SentenceEntailment (D := D) Γ)
    (I : Instance D Γ)
    (hEmpty : E.activeFinset I = ∅) :
    I.AdomEmpty := by
  apply Finset.ext
  intro d
  constructor
  · intro hd
    have hdActive : d ∈ E.activeFinset I := by
      unfold activeFinset
      exact Finset.mem_union.mpr (Or.inl hd)
    rw [hEmpty] at hdActive
    exact False.elim (Finset.notMem_empty d hdActive)
  · intro hd
    exact False.elim (Finset.notMem_empty d hd)

/- Nullary assignments have empty active finset here. -/
private theorem ofNullaryAssignment_activeFinset_eq_empty
    (E : SentenceEntailment (D := D) Γ)
    (χ : Instance.NullaryAssignment Γ)
    (hConst : E.constants = ∅) :
    E.activeFinset
      (Instance.ofNullaryAssignment (D := D) χ) = ∅ := by
  rw [activeFinset,
    Instance.ofNullaryAssignment_adomEmpty,
    hConst, Finset.empty_union]

end SentenceEntailment

end RelCalc

------------------------------------------------------------
-- Boolean Checker and Semantic Soundness
------------------------------------------------------------

namespace RelCalc

namespace SentenceEntailment

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/-
  A nullary choice falsifies the entailment in the empty
  case.
-/
private def ChoiceEmptyCounterexample
    (E : SentenceEntailment (D := D) Γ)
    (χ : Instance.NullaryAssignment Γ) : Prop :=
  E.constants = ∅ ∧
    E.SatisfiesAxioms
        (Instance.ofNullaryAssignment (D := D) χ) ∧
      ¬ E.conjecture.SatIn
        (Instance.ofNullaryAssignment (D := D) χ)
        (E.activeDomain
          (Instance.ofNullaryAssignment (D := D) χ))

private instance
    (E : SentenceEntailment (D := D) Γ)
    (χ : Instance.NullaryAssignment Γ) :
    Decidable (ChoiceEmptyCounterexample E χ) := by
  unfold ChoiceEmptyCounterexample
  infer_instance

/- Existence of a nullary-choice counterexample. -/
private def HasChoiceEmptyCounterexample
    (E : SentenceEntailment (D := D) Γ) : Prop :=
  ∃ χ : Instance.NullaryAssignment Γ,
    ChoiceEmptyCounterexample E χ

private instance
    [Fintype Γ.syms]
    (E : SentenceEntailment (D := D) Γ) :
    Decidable (HasChoiceEmptyCounterexample E) := by
  unfold HasChoiceEmptyCounterexample
  infer_instance

/- Search for an empty-active-domain counterexample. -/
def emptyCounterexample?
    (E : SentenceEntailment (D := D) Γ)
    [Fintype Γ.syms] : Bool :=
  decide (HasChoiceEmptyCounterexample E)

private theorem hasChoice_of_hasEmpty
    (E : SentenceEntailment (D := D) Γ)
    (h : E.HasEmptyCounterexample) :
    HasChoiceEmptyCounterexample E := by
  rcases h with ⟨I, hEmpty, hAx, hConj⟩
  have hConst : E.constants = ∅ := by
    apply Finset.ext
    intro d
    constructor
    · intro hd
      have hdActive : d ∈ E.activeFinset I := by
        unfold activeFinset
        exact Finset.mem_union.mpr (Or.inr hd)
      rw [hEmpty] at hdActive
      exact False.elim (Finset.notMem_empty d hdActive)
    · intro hd
      simp at hd
  let χ := I.toNullaryAssignment
  have hAdom : I.AdomEmpty :=
    E.adomEmpty_of_activeFinset_eq_empty I hEmpty
  have hI :
      I = Instance.ofNullaryAssignment (D := D) χ :=
    Instance.eq_ofNullaryAssignment_toNullaryAssignment
      I hAdom
  have hAxChoice :
      E.SatisfiesAxioms
        (Instance.ofNullaryAssignment (D := D) χ) := by
    simpa [← hI] using hAx
  have hConjChoice :
      ¬ E.conjecture.SatIn
        (Instance.ofNullaryAssignment (D := D) χ)
        (E.activeDomain
          (Instance.ofNullaryAssignment (D := D) χ)) := by
    simpa [← hI] using hConj
  exact ⟨χ, hConst, hAxChoice, hConjChoice⟩

/-
  Empty choices produce empty-active-domain counterexamples.
-/
private theorem hasEmpty_of_hasChoice
    (E : SentenceEntailment (D := D) Γ)
    (h : HasChoiceEmptyCounterexample E) :
    E.HasEmptyCounterexample := by
  rcases h with ⟨χ, hConst, hAx, hConj⟩
  exact
    ⟨Instance.ofNullaryAssignment (D := D) χ,
      ofNullaryAssignment_activeFinset_eq_empty
        E χ hConst,
      hAx,
      hConj⟩

/-
  If the finite nullary-choice search finds no
  counterexample, the empty-active-domain side condition
  holds.
-/
theorem
    noEmptyCounterexample_of_emptyCounterexample?_eq_false
    [Fintype Γ.syms]
    (E : SentenceEntailment (D := D) Γ)
    (h : E.emptyCounterexample? = false) :
    E.NoEmptyCounterexample := by
  intro hEmpty
  have hChoice :
      HasChoiceEmptyCounterexample E :=
    E.hasChoice_of_hasEmpty hEmpty
  have hDec :
      decide (HasChoiceEmptyCounterexample E) = true :=
    decide_eq_true hChoice
  unfold emptyCounterexample? at h
  rw [hDec] at h
  simp at h

/-
  The Boolean search exactly decides the empty side
  condition.
-/
theorem emptyCounterexample?_eq_false_iff
    [Fintype Γ.syms]
    (E : SentenceEntailment (D := D) Γ) :
    E.emptyCounterexample? = false ↔
      E.NoEmptyCounterexample := by
  constructor
  · exact
      noEmptyCounterexample_of_emptyCounterexample?_eq_false
        E
  · intro hNoEmpty
    cases hCheck : E.emptyCounterexample?
    · rfl
    · have hChoice :
          HasChoiceEmptyCounterexample E := by
        unfold emptyCounterexample? at hCheck
        exact of_decide_eq_true hCheck
      exact False.elim
        (hNoEmpty (E.hasEmpty_of_hasChoice hChoice))

end SentenceEntailment

end RelCalc
