-- Author: Jesse Comer
import Whiel.Vampire.EmptyCounterexample
import Whiel.AssertExpr.ToRelCalc
import Databases.RelCalc.ToFOL

/-
  Connect Vampire's FOL problems back to QF assertions.

  Key theorem:
    * `valid_of_noEmpty_and_toFOLWithSupportAxioms`
    * `emptyCounterexample?_eq_false_iff`
    * `adomEmptyCounterexample?_eq_false_iff`
    * `noEmpty_of_adomEmptyCounterexample?_eq_false`

  If the RelCalc-to-FOL problem is valid, and there is no
  empty-active-domain counterexample, then the original QF
  entailment is valid.

  The empty-counterexample checker uses direct QF
  evaluation on the unique empty instance when the schema
  has no nullary symbols, and otherwise retains the
  exhaustive RelCalc check.
-/

------------------------------------------------------------
-- FOL Soundness Bridge
------------------------------------------------------------

namespace QFEntailment

open RelCalc.SentenceEntailment

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Validity of the FOL translation with support axioms, plus
  the empty-instance side condition, implies source QF
  validity.
-/
theorem valid_of_noEmpty_and_toFOLWithSupportAxioms
    [LinearOrder A]
    [LinearOrder D]
    (E : QFEntailment (D := D) Γ)
    (hNoEmpty :
      E.toRelCalcEntailment.NoEmptyCounterexample)
    (hFOL :
      FOL.SentenceEntailment.Valid
        (D := D)
        E.toRelCalcEntailment.toFOLWithSupportAxioms) :
    E.Valid := by
  have hRel :
      E.toRelCalcEntailment.Valid :=
    RelCalc.SentenceEntailment.toFOLWithSupportAxioms_sound
      E.toRelCalcEntailment hNoEmpty hFOL
  exact E.valid_of_toRelCalc hRel

end QFEntailment

------------------------------------------------------------
-- Empty Active-Domain Side Condition
------------------------------------------------------------

namespace QFEntailment

open RelCalc
open RelCalc.SentenceEntailment

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- A schema contains a nullary relation symbol. -/
private def HasNullarySymbol
    (Γ : UnnamedSchema A) : Prop :=
  ∃ X : Γ.syms, Γ.arity X = 0

private instance
    (Γ : UnnamedSchema A)
    [Fintype Γ.syms] :
    Decidable (HasNullarySymbol Γ) := by
  unfold HasNullarySymbol
  infer_instance

/- Executable nullary-symbol test. -/
private def hasNullarySymbol?
    (Γ : UnnamedSchema A)
    [Fintype Γ.syms] : Bool :=
  decide (HasNullarySymbol Γ)

/- No relation symbol in a schema is nullary. -/
private def NoNullarySymbols
    (Γ : UnnamedSchema A) : Prop :=
  ∀ X : Γ.syms, Γ.arity X ≠ 0

/- A negative symbol test proves absence of nullaries. -/
private theorem noNullarySymbols_of_check_eq_false
    (Γ : UnnamedSchema A)
    [Fintype Γ.syms]
    (h : hasNullarySymbol? Γ = false) :
    NoNullarySymbols Γ := by
  intro X hAr
  have hExists : HasNullarySymbol Γ := ⟨X, hAr⟩
  have hTrue : hasNullarySymbol? Γ = true :=
    decide_eq_true hExists
  rw [h] at hTrue
  cases hTrue

/- QF counterexample at the canonical empty instance. -/
private def EmptyInstanceCounterexample
    (E : QFEntailment (D := D) Γ) : Prop :=
  E.constants = ∅ ∧
    (∀ φ ∈ E.axioms,
      φ.eval (Instance.empty Γ)) ∧
    ¬ E.conjecture.eval (Instance.empty Γ)

private instance
    (E : QFEntailment (D := D) Γ) :
    Decidable (EmptyInstanceCounterexample E) := by
  unfold EmptyInstanceCounterexample
  infer_instance

/- Check the canonical empty instance directly in QF. -/
private def emptyInstanceCounterexample?
    (E : QFEntailment (D := D) Γ) : Bool :=
  decide (EmptyInstanceCounterexample E)

/- A translated empty counterexample gives the QF one. -/
private theorem emptyInstanceCounterexample_of_hasEmpty
    (hNoNullary : NoNullarySymbols Γ)
    (E : QFEntailment (D := D) Γ)
    (h : E.toRelCalcEntailment.HasEmptyCounterexample) :
    EmptyInstanceCounterexample E := by
  rcases h with ⟨I, hActive, hAx, hConj⟩
  have hAdom : I.AdomEmpty := by
    apply Finset.ext
    intro d
    constructor
    · intro hd
      have hdActive :
          d ∈ E.toRelCalcEntailment.activeFinset I := by
        exact Finset.mem_union.mpr (Or.inl hd)
      rw [hActive] at hdActive
      exact False.elim
        (Finset.notMem_empty d hdActive)
    · intro hd
      exact False.elim (Finset.notMem_empty d hd)
  have hI : I = Instance.empty Γ :=
    Instance.eq_empty_of_adomEmpty I hAdom hNoNullary
  subst I
  have hRelConst :
      E.toRelCalcEntailment.constants = ∅ := by
    apply Finset.ext
    intro d
    constructor
    · intro hd
      have hdActive :
          d ∈ E.toRelCalcEntailment.activeFinset
            (Instance.empty Γ) := by
        exact Finset.mem_union.mpr (Or.inr hd)
      rw [hActive] at hdActive
      exact False.elim
        (Finset.notMem_empty d hdActive)
    · intro hd
      exact False.elim (Finset.notMem_empty d hd)
  have hConst : E.constants = ∅ := by
    rw [toRelCalcEntailment_constants E] at hRelConst
    exact hRelConst
  have hAxQF :
      ∀ φ ∈ E.axioms,
        φ.eval (Instance.empty Γ) := by
    intro φ hφ
    have hMember :
        φ.toRelCalcSentence ∈
          E.toRelCalcEntailment.axioms := by
      exact List.mem_map.mpr ⟨φ, hφ, rfl⟩
    exact
      (Whiel.QFAssertExpr.toRelCalcSentence_correct
        φ
        (E.toRelCalcEntailment.activeDomain
          (Instance.empty Γ))
        (Instance.empty Γ)
        (E.activeDomain_contains
          (E.axiom_constants hφ)
          (Instance.empty Γ))).mp
        (hAx φ.toRelCalcSentence hMember)
  have hNotConj :
      ¬ E.conjecture.eval (Instance.empty Γ) := by
    intro hEval
    apply hConj
    exact
      (Whiel.QFAssertExpr.toRelCalcSentence_correct
        E.conjecture
        (E.toRelCalcEntailment.activeDomain
          (Instance.empty Γ))
        (Instance.empty Γ)
        (E.activeDomain_contains
          E.conjecture_constants
          (Instance.empty Γ))).mpr hEval
  exact ⟨hConst, hAxQF, hNotConj⟩

/- The QF empty counterexample gives a translated one. -/
private theorem hasEmpty_of_emptyInstanceCounterexample
    (E : QFEntailment (D := D) Γ)
    (h : EmptyInstanceCounterexample E) :
    E.toRelCalcEntailment.HasEmptyCounterexample := by
  rcases h with ⟨hConst, hAx, hConj⟩
  have hAdom :
      (Instance.empty (D := D) Γ).AdomEmpty :=
    Instance.empty_adomEmpty Γ
  have hRelConst :
      E.toRelCalcEntailment.constants = ∅ := by
    rw [toRelCalcEntailment_constants E, hConst]
  have hActive :
      E.toRelCalcEntailment.activeFinset
        (Instance.empty Γ) = ∅ := by
    rw [RelCalc.SentenceEntailment.activeFinset,
      hAdom, hRelConst, Finset.empty_union]
  have hAxRel :
      E.toRelCalcEntailment.SatisfiesAxioms
        (Instance.empty Γ) :=
    E.relCalc_axioms_of_qf_axioms hAx
  have hNotConj :
      ¬ E.toRelCalcEntailment.conjecture.SatIn
        (Instance.empty Γ)
        (E.toRelCalcEntailment.activeDomain
          (Instance.empty Γ)) := by
    intro hSat
    apply hConj
    exact
      (Whiel.QFAssertExpr.toRelCalcSentence_correct
        E.conjecture
        (E.toRelCalcEntailment.activeDomain
          (Instance.empty Γ))
        (Instance.empty Γ)
        (E.activeDomain_contains
          E.conjecture_constants
          (Instance.empty Γ))).mp hSat
  exact
    ⟨Instance.empty Γ, hActive, hAxRel, hNotConj⟩

/- Search for an empty-active-domain counterexample. -/
def emptyCounterexample?
    (E : QFEntailment (D := D) Γ)
    [Fintype Γ.syms] : Bool :=
  if hasNullarySymbol? Γ then
    E.toRelCalcEntailment.emptyCounterexample?
  else
    emptyInstanceCounterexample? E

/-
  The optimized checker exactly decides the side condition.
-/
theorem emptyCounterexample?_eq_false_iff
    [Fintype Γ.syms]
    (E : QFEntailment (D := D) Γ) :
    E.emptyCounterexample? = false ↔
      E.toRelCalcEntailment.NoEmptyCounterexample := by
  cases hNullary : hasNullarySymbol? Γ
  · have hNoNullary : NoNullarySymbols Γ :=
      noNullarySymbols_of_check_eq_false Γ hNullary
    have hEmptyIff :
        EmptyInstanceCounterexample E ↔
          E.toRelCalcEntailment.HasEmptyCounterexample := by
      constructor
      · exact hasEmpty_of_emptyInstanceCounterexample E
      · exact
          emptyInstanceCounterexample_of_hasEmpty
            hNoNullary E
    unfold emptyCounterexample?
    rw [hNullary]
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold emptyInstanceCounterexample?
    rw [decide_eq_false_iff_not]
    exact not_congr hEmptyIff
  · simpa [emptyCounterexample?, hNullary] using
      (SentenceEntailment.emptyCounterexample?_eq_false_iff
        E.toRelCalcEntailment)

/-
  A negative executable empty-counterexample check supplies
  the side condition used by the ToFOL proof.
-/
theorem noEmpty_of_emptyCounterexample?_eq_false
    [Fintype Γ.syms]
    (E : QFEntailment (D := D) Γ)
    (h : E.emptyCounterexample? = false) :
    E.toRelCalcEntailment.NoEmptyCounterexample :=
  (emptyCounterexample?_eq_false_iff E).mp h

end QFEntailment

------------------------------------------------------------
-- Constant-Blind Adom-Empty Check
------------------------------------------------------------

namespace QFEntailment

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/-
  A QF countermodel at one adom-empty instance, whatever
  constants the entailment mentions. The empty-active-domain
  check above is vacuous once a constant occurs; this check
  decides validity over every adom-empty instance and is the
  one a reused solver proof needs (the proof covers the
  nonempty active domains of its own request only).
-/
def AdomEmptyCounterexample
    (E : QFEntailment (D := D) Γ)
    (χ : Instance.NullaryAssignment Γ) : Prop :=
  (∀ φ ∈ E.axioms,
    φ.eval (Instance.ofNullaryAssignment χ)) ∧
    ¬ E.conjecture.eval (Instance.ofNullaryAssignment χ)

instance
    (E : QFEntailment (D := D) Γ)
    (χ : Instance.NullaryAssignment Γ) :
    Decidable (AdomEmptyCounterexample E χ) := by
  unfold AdomEmptyCounterexample
  infer_instance

/- Some nullary choice is an adom-empty countermodel. -/
def HasAdomEmptyCounterexample
    (E : QFEntailment (D := D) Γ) : Prop :=
  ∃ χ : Instance.NullaryAssignment Γ,
    AdomEmptyCounterexample E χ

instance
    [Fintype Γ.syms]
    (E : QFEntailment (D := D) Γ) :
    Decidable (HasAdomEmptyCounterexample E) := by
  unfold HasAdomEmptyCounterexample
  infer_instance

/- Search every adom-empty instance for a countermodel. -/
def adomEmptyCounterexample?
    (E : QFEntailment (D := D) Γ)
    [Fintype Γ.syms] : Bool :=
  decide (HasAdomEmptyCounterexample E)

/- The check decides validity over adom-empty instances. -/
theorem adomEmptyCounterexample?_eq_false_iff
    [Fintype Γ.syms]
    (E : QFEntailment (D := D) Γ) :
    E.adomEmptyCounterexample? = false ↔
      ∀ I : Instance D Γ,
        I.AdomEmpty →
          (∀ φ ∈ E.axioms, φ.eval I) →
            E.conjecture.eval I := by
  unfold adomEmptyCounterexample?
  rw [decide_eq_false_iff_not]
  constructor
  · intro hNone I hAdom hAxioms
    by_contra hConj
    apply hNone
    rcases (Instance.adomEmpty_iff_exists_nullaryAssignment
      I).mp hAdom with ⟨χ, rfl⟩
    exact ⟨χ, hAxioms, hConj⟩
  · rintro hValid ⟨χ, hAxioms, hConj⟩
    exact hConj
      (hValid _ (Instance.ofNullaryAssignment_adomEmpty χ)
        hAxioms)

/-
  A negative constant-blind check gives the side condition
  of the FOL soundness bridge: an empty active domain is in
  particular an empty instance adom.
-/
theorem noEmpty_of_adomEmptyCounterexample?_eq_false
    [Fintype Γ.syms]
    (E : QFEntailment (D := D) Γ)
    (h : E.adomEmptyCounterexample? = false) :
    E.toRelCalcEntailment.NoEmptyCounterexample := by
  rintro ⟨I, hActive, hAxioms, hConj⟩
  have hAdom : I.AdomEmpty := by
    apply Finset.ext
    intro d
    constructor
    · intro hd
      have hdActive :
          d ∈ E.toRelCalcEntailment.activeFinset I :=
        Finset.mem_union.mpr (Or.inl hd)
      rw [hActive] at hdActive
      exact False.elim (Finset.notMem_empty d hdActive)
    · intro hd
      exact False.elim (Finset.notMem_empty d hd)
  have hValid :=
    (adomEmptyCounterexample?_eq_false_iff E).mp h
  apply hConj
  apply
    (Whiel.QFAssertExpr.toRelCalcSentence_correct
      E.conjecture
      (E.toRelCalcEntailment.activeDomain I) I
      (E.activeDomain_contains
        E.conjecture_constants I)).mpr
  apply hValid I hAdom
  intro φ hφ
  exact
    (Whiel.QFAssertExpr.toRelCalcSentence_correct
      φ (E.toRelCalcEntailment.activeDomain I) I
      (E.activeDomain_contains
        (E.axiom_constants hφ) I)).mp
      (hAxioms φ.toRelCalcSentence
        (List.mem_map.mpr ⟨φ, hφ, rfl⟩))

end QFEntailment
