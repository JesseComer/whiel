-- Author: Jesse Comer
import Databases.FOL.ShallowSemantics
import Databases.RelCalc.DomainIndependence
import Databases.RelCalc.ToFOL

/-
  This file defines general augmentation and discharge for
  active-domain RelCalc entailments.

  Key definitions include:
    * `RelCalc.SentenceEntailment.prependAxioms`

  Correctness is proven by:
    * `RelCalc.SentenceEntailment.
        valid_of_prependAxioms`
    * `RelCalc.SentenceEntailment.
        valid_of_prependAxioms_shallow`

  Extra sentences may contain constants. Sound discharge
  requires each extra sentence to be `AdomValid`, each base
  sentence to be domain independent, and one relation name
  fresh for the entailment schema.
-/

------------------------------------------------------------
-- Entailment Augmentation
------------------------------------------------------------

namespace RelCalc
namespace SentenceEntailment

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- Prepend additional sentences as separate axioms. -/
def prependAxioms
    (extras : List (Sentence D Γ))
    (E : SentenceEntailment (D := D) Γ) :
    SentenceEntailment (D := D) Γ where
  axioms := extras ++ E.axioms
  conjecture := E.conjecture

private theorem sentenceListConstants_append
    (left right : List (Sentence D Γ)) :
    sentenceListConstants (left ++ right) =
      sentenceListConstants left ∪
        sentenceListConstants right := by
  induction left with
  | nil =>
      simp [sentenceListConstants]
  | cons φ left ih =>
      simp [sentenceListConstants, ih,
        Finset.union_assoc]

/- Constants of both inputs occur in the augmentation. -/
private theorem prependAxioms_constants
    (extras : List (Sentence D Γ))
    (E : SentenceEntailment (D := D) Γ) :
    (prependAxioms extras E).constants =
      sentenceListConstants extras ∪ E.constants := by
  rw [constants, constants]
  change
    sentenceListConstants (extras ++ E.axioms) ∪
        E.conjecture.constants = _
  rw [sentenceListConstants_append]
  simp only [Finset.union_assoc]

private theorem activeFinset_subset_prependAxioms
    (extras : List (Sentence D Γ))
    (E : SentenceEntailment (D := D) Γ)
    (I : Instance D Γ) :
    E.activeFinset I ⊆
      (prependAxioms extras E).activeFinset I := by
  intro d hd
  change d ∈ I.Adom ∪ E.constants at hd
  change d ∈ I.Adom ∪ (prependAxioms extras E).constants
  rw [prependAxioms_constants]
  rw [Finset.mem_union] at hd ⊢
  rcases hd with hd | hd
  · exact Or.inl hd
  · exact Or.inr (Finset.mem_union_right _ hd)

private theorem adom_subset_activeDomain
    {φ : Sentence D Γ}
    (E : SentenceEntailment (D := D) Γ)
    (I : Instance D Γ)
    (hConstants : φ.constants ⊆ E.constants) :
    Adom.toSet φ.1 I ⊆ E.activeDomain I := by
  intro d hd
  change d ∈ I.Adom ∪ φ.constants at hd
  change d ∈ I.Adom ∪ E.constants
  rw [Finset.mem_union] at hd ⊢
  rcases hd with hd | hd
  · exact Or.inl hd
  · exact Or.inr (hConstants hd)

end SentenceEntailment
end RelCalc

------------------------------------------------------------
-- General Axiom Discharge
------------------------------------------------------------

namespace RelCalc
namespace SentenceEntailment

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- A base empty check also covers any augmentation. -/
theorem noEmptyCounterexample_prependAxioms
    (extras : List (Sentence D Γ))
    (E : SentenceEntailment (D := D) Γ)
    (hNoEmpty : E.NoEmptyCounterexample) :
    (prependAxioms extras E).NoEmptyCounterexample := by
  intro hCounterexample
  rcases hCounterexample with
    ⟨I, hAugEmpty, hAugAxioms, hConjecture⟩
  have hBaseEmpty : E.activeFinset I = ∅ := by
    apply Finset.Subset.antisymm
    · intro d hd
      have hAugMem :=
        activeFinset_subset_prependAxioms extras E I hd
      rw [hAugEmpty] at hAugMem
      exact hAugMem
    · exact Finset.empty_subset _
  have hDomains :
      (prependAxioms extras E).activeDomain I =
        E.activeDomain I := by
    funext d
    apply propext
    change
      d ∈ (prependAxioms extras E).activeFinset I ↔
        d ∈ E.activeFinset I
    rw [hAugEmpty, hBaseEmpty]
  apply hNoEmpty
  refine ⟨I, hBaseEmpty, ?_, ?_⟩
  · intro φ hφ
    have hSat := hAugAxioms φ (by
      change φ ∈ extras ++ E.axioms
      exact List.mem_append_right extras hφ)
    rw [hDomains] at hSat
    exact hSat
  · change
      ¬E.conjecture.SatIn I
        ((prependAxioms extras E).activeDomain I)
      at hConjecture
    rw [hDomains] at hConjecture
    exact hConjecture

/- Discharge active-domain-valid additional axioms. -/
theorem valid_of_prependAxioms
    (extras : List (Sentence D Γ))
    (E : SentenceEntailment (D := D) Γ)
    (hFresh : ∃ X : A, X ∉ Γ.syms)
    (hExtras : ∀ φ ∈ extras, φ.AdomValid)
    (hAxioms : ∀ φ ∈ E.axioms,
      φ.DomainIndependent)
    (hConjecture : E.conjecture.DomainIndependent)
    (hAugmented : (prependAxioms extras E).Valid) :
    E.Valid := by
  intro I hBase
  let augmented := prependAxioms extras E
  have hBaseAtFormulaAdom :
      ∀ φ ∈ E.axioms,
        φ.SatIn I (Adom.toSet φ.1 I) := by
    intro φ hφ
    have hSupport := adom_subset_activeDomain E I
      (E.axiom_constants hφ)
    exact (hAxioms φ hφ I (E.activeDomain I)
      hSupport).mpr (hBase φ hφ)
  have hBaseAtAugmented :
      ∀ φ ∈ E.axioms,
        φ.SatIn I (augmented.activeDomain I) := by
    intro φ hφ
    have hInAugmented : φ ∈ augmented.axioms := by
      change φ ∈ extras ++ E.axioms
      exact List.mem_append_right extras hφ
    have hSupport := adom_subset_activeDomain
      augmented I (augmented.axiom_constants hInAugmented)
    exact (hAxioms φ hφ I
      (augmented.activeDomain I) hSupport).mp
      (hBaseAtFormulaAdom φ hφ)
  have hExtrasAtAugmented :
      ∀ φ ∈ extras,
        φ.SatIn I (augmented.activeDomain I) := by
    intro φ hφ
    have hInAugmented : φ ∈ augmented.axioms := by
      change φ ∈ extras ++ E.axioms
      exact List.mem_append_left E.axioms hφ
    have hSupport :
        RelCalc.Adom φ.1 I ⊆
          augmented.activeFinset I := by
      exact adom_subset_activeDomain augmented I
        (augmented.axiom_constants hInAugmented)
    exact Sentence.finiteExtensionValid_of_adomValid φ
      (hExtras φ hφ) hFresh I
        (augmented.activeFinset I)
        hSupport
  have hAugmentedAxioms :
      augmented.SatisfiesAxioms I := by
    intro φ hφ
    change φ ∈ extras ++ E.axioms at hφ
    rcases List.mem_append.mp hφ with hφ | hφ
    · exact hExtrasAtAugmented φ hφ
    · exact hBaseAtAugmented φ hφ
  have hAtAugmented := hAugmented I hAugmentedAxioms
  have hConjectureSupportAtAugmented :=
    adom_subset_activeDomain augmented I
      augmented.conjecture_constants
  have hAtFormulaAdom :=
    (hConjecture I (augmented.activeDomain I)
      hConjectureSupportAtAugmented).mpr hAtAugmented
  have hConjectureSupportAtBase :=
    adom_subset_activeDomain E I E.conjecture_constants
  exact (hConjecture I (E.activeDomain I)
    hConjectureSupportAtBase).mp hAtFormulaAdom

end SentenceEntailment
end RelCalc

------------------------------------------------------------
-- FOL And Shallow Discharge
------------------------------------------------------------

namespace RelCalc
namespace SentenceEntailment

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- Discharge additional axioms after FOL translation. -/
theorem valid_of_prependAxioms_toFOL
    [LinearOrder A]
    [LinearOrder D]
    (extras : List (Sentence D Γ))
    (E : SentenceEntailment (D := D) Γ)
    (hFresh : ∃ X : A, X ∉ Γ.syms)
    (hExtras : ∀ φ ∈ extras, φ.AdomValid)
    (hAxioms : ∀ φ ∈ E.axioms,
      φ.DomainIndependent)
    (hConjecture : E.conjecture.DomainIndependent)
    (hNoEmpty : E.NoEmptyCounterexample)
    (hFOL :
      FOL.SentenceEntailment.Valid (D := D)
        (toFOLWithSupportAxioms
          (prependAxioms extras E))) :
    E.Valid := by
  apply valid_of_prependAxioms extras E hFresh hExtras
    hAxioms hConjecture
  exact toFOLWithSupportAxioms_sound
    (prependAxioms extras E)
    (noEmptyCounterexample_prependAxioms
      extras E hNoEmpty) hFOL

/- Discharge additional axioms after shallow proof. -/
theorem valid_of_prependAxioms_shallow
    [LinearOrder A]
    [LinearOrder D]
    (extras : List (Sentence D Γ))
    (E : SentenceEntailment (D := D) Γ)
    (hFresh : ∃ X : A, X ∉ Γ.syms)
    (hExtras : ∀ φ ∈ extras, φ.AdomValid)
    (hAxioms : ∀ φ ∈ E.axioms,
      φ.DomainIndependent)
    (hConjecture : E.conjecture.DomainIndependent)
    (hNoEmpty : E.NoEmptyCounterexample)
    (hShallow :
      FOL.SentenceEntailment.ShallowValid
        (toFOLWithSupportAxioms
          (prependAxioms extras E))) :
    E.Valid := by
  apply valid_of_prependAxioms_toFOL
    extras E hFresh hExtras hAxioms hConjecture hNoEmpty
  exact FOL.SentenceEntailment.valid_of_shallowValid
    (toFOLWithSupportAxioms
      (prependAxioms extras E)) hShallow

end SentenceEntailment
end RelCalc
