-- Author: Jesse Comer
import Databases.RelCalc.Syntax
import Databases.UnnamedModel.RelAtom

/-
  Relational calculus formula semantics.

  `Formula.ArbitraryAssignSatIn` is the raw recursive truth
  predicate. Quantifiers range over a set `Q`, while free
  variables are read directly from the assignment.

  `Formula.SatIn` is the typed formula satisfaction
  predicate: it adds the requirement that all free variables
  are assigned values in `Q`.

  `Sentence.SatIn` is assignment-free satisfaction for
  relational-calculus sentences.

  This file uses the shared `Assign`, `RelTerm.eval`, and
  `RelAtom.Sat` declarations from `DBLib.UnnamedModel.RelAtom`.

  Other key declarations:
    * `Formula.satIn_eq_of_agreeOn_freeVars`
    * `Sentence.satIn_iff`
-/

------------------------------------------------------------
-- Shared Formula Semantics
------------------------------------------------------------

namespace RelCalc

namespace Formula

variable {A D : Type}
variable [Domain D]
variable [RelationNames A]
variable {Γ : UnnamedSchema A}

/-
  Recursive truth predicate for formulas under unrestricted
  assignments.

  Quantifiers range over the chosen domain `Q`, but free
  variables are read directly from `σ`. This definition
  does not require those free-variable values to lie in `Q`;
  that side condition is added by `Formula.SatIn`.
-/
def ArbitraryAssignSatIn
    (Q : Set D)
    (I : Instance D Γ)
    (σ : Assign D) :
    Formula D Γ → Prop
| .top => True
| .bot => False
| .eq t₁ t₂ => t₁.eval σ = t₂.eval σ
| .rel a =>
    a.Sat I σ
| .and φ ψ =>
    ArbitraryAssignSatIn Q I σ φ ∧
      ArbitraryAssignSatIn Q I σ ψ
| .or φ ψ =>
    ArbitraryAssignSatIn Q I σ φ ∨
      ArbitraryAssignSatIn Q I σ ψ
| .not φ =>
    ¬ ArbitraryAssignSatIn Q I σ φ
| .imp φ ψ =>
    ArbitraryAssignSatIn Q I σ φ →
      ArbitraryAssignSatIn Q I σ ψ
| .iff φ ψ =>
    ArbitraryAssignSatIn Q I σ φ ↔
      ArbitraryAssignSatIn Q I σ ψ
| .forall_ x φ =>
    ∀ d ∈ Q,
      ArbitraryAssignSatIn Q I
        (Assign.update σ x d) φ
| .exists_ x φ =>
    ∃ d ∈ Q,
      ArbitraryAssignSatIn Q I
        (Assign.update σ x d) φ

/-
  A finite-domain decidability constructor for unrestricted
  recursive truth.
-/
private def decidableArbitraryAssignSatIn
    (Q : Set D)
    [DecidablePred Q]
    [Fintype {d // Q d}]
    (I : Instance D Γ)
    (σ : Assign D) :
    (φ : Formula D Γ) →
      Decidable (Formula.ArbitraryAssignSatIn Q I σ φ)
| .top =>
    isTrue (by simp [Formula.ArbitraryAssignSatIn])
| .bot =>
    isFalse (by simp [Formula.ArbitraryAssignSatIn])
| .eq t₁ t₂ =>
    by
      unfold Formula.ArbitraryAssignSatIn
      infer_instance
| .rel a =>
    by
      unfold Formula.ArbitraryAssignSatIn RelAtom.Sat
        RelAtom.evalFact RelFact.Mem
      infer_instance
| .and φ ψ =>
    by
      haveI : Decidable
          (Formula.ArbitraryAssignSatIn Q I σ φ) :=
        decidableArbitraryAssignSatIn Q I σ φ
      haveI : Decidable
          (Formula.ArbitraryAssignSatIn Q I σ ψ) :=
        decidableArbitraryAssignSatIn Q I σ ψ
      simpa [Formula.ArbitraryAssignSatIn] using
        (inferInstance :
          Decidable
            (Formula.ArbitraryAssignSatIn Q I σ φ ∧
              Formula.ArbitraryAssignSatIn Q I σ ψ))
| .or φ ψ =>
    by
      haveI : Decidable
          (Formula.ArbitraryAssignSatIn Q I σ φ) :=
        decidableArbitraryAssignSatIn Q I σ φ
      haveI : Decidable
          (Formula.ArbitraryAssignSatIn Q I σ ψ) :=
        decidableArbitraryAssignSatIn Q I σ ψ
      simpa [Formula.ArbitraryAssignSatIn] using
        (inferInstance :
          Decidable
            (Formula.ArbitraryAssignSatIn Q I σ φ ∨
              Formula.ArbitraryAssignSatIn Q I σ ψ))
| .not φ =>
    by
      haveI : Decidable
          (Formula.ArbitraryAssignSatIn Q I σ φ) :=
        decidableArbitraryAssignSatIn Q I σ φ
      simpa [Formula.ArbitraryAssignSatIn] using
        (inferInstance :
          Decidable
            (¬ Formula.ArbitraryAssignSatIn Q I σ φ))
| .imp φ ψ =>
    by
      haveI : Decidable
          (Formula.ArbitraryAssignSatIn Q I σ φ) :=
        decidableArbitraryAssignSatIn Q I σ φ
      haveI : Decidable
          (Formula.ArbitraryAssignSatIn Q I σ ψ) :=
        decidableArbitraryAssignSatIn Q I σ ψ
      simpa [Formula.ArbitraryAssignSatIn] using
        (inferInstance :
          Decidable
            (Formula.ArbitraryAssignSatIn Q I σ φ →
              Formula.ArbitraryAssignSatIn Q I σ ψ))
| .iff φ ψ =>
    by
      haveI : Decidable
          (Formula.ArbitraryAssignSatIn Q I σ φ) :=
        decidableArbitraryAssignSatIn Q I σ φ
      haveI : Decidable
          (Formula.ArbitraryAssignSatIn Q I σ ψ) :=
        decidableArbitraryAssignSatIn Q I σ ψ
      simpa [Formula.ArbitraryAssignSatIn] using
        (inferInstance :
          Decidable
            (Formula.ArbitraryAssignSatIn Q I σ φ ↔
              Formula.ArbitraryAssignSatIn Q I σ ψ))
| .forall_ x φ =>
    by
      let P : D → Prop := fun d =>
        Formula.ArbitraryAssignSatIn Q I
          (Assign.update σ x d) φ
      have hP : ∀ d, Decidable (P d) := by
        intro d
        simpa [P] using
          decidableArbitraryAssignSatIn Q I
            (Assign.update σ x d) φ
      haveI : DecidablePred P := hP
      change Decidable (∀ d, Q d → P d)
      exact decidable_of_iff
        (∀ q : {d // Q d}, P q.1)
        ⟨
          fun h d hd => h ⟨d, hd⟩,
          fun h q => h q.1 q.2
        ⟩
| .exists_ x φ =>
    by
      let P : D → Prop := fun d =>
        Formula.ArbitraryAssignSatIn Q I
          (Assign.update σ x d) φ
      have hP : ∀ d, Decidable (P d) := by
        intro d
        simpa [P] using
          decidableArbitraryAssignSatIn Q I
            (Assign.update σ x d) φ
      haveI : DecidablePred P := hP
      change Decidable (∃ d, Q d ∧ P d)
      exact decidable_of_iff
        (∃ q : {d // Q d}, P q.1)
        ⟨
          fun ⟨q, hq⟩ => ⟨q.1, q.2, hq⟩,
          fun ⟨d, hd, hP⟩ => ⟨⟨d, hd⟩, hP⟩
        ⟩

/-
  Bounded-domain formula satisfaction.

  This is the public satisfaction relation relative to `Q`.
  It combines recursive truth with the condition that every
  free variable of the formula is assigned a value in `Q`.
  The extra side condition is needed because RelCalc
  assignments are plain functions `Var → D`, not functions
  into `Q`.
-/
def SatIn
    (φ : Formula D Γ)
    (I : Instance D Γ)
    (σ : Assign D)
    (Q : Set D) : Prop :=
  Assign.MapsInto σ φ.freeVars Q ∧
    Formula.ArbitraryAssignSatIn Q I σ φ

/-
  A finite-domain decidability constructor for typed
  bounded-domain formula satisfaction.
-/
def decidableSatIn
    (Q : Set D)
    [DecidablePred Q]
    [Fintype {d // Q d}]
    (φ : Formula D Γ)
    (I : Instance D Γ)
    (σ : Assign D) :
    Decidable (Formula.SatIn φ I σ Q) := by
  unfold Formula.SatIn
  let _ :=
    Formula.decidableArbitraryAssignSatIn
      (Q := Q) (I := I) (σ := σ) φ
  infer_instance

end Formula

end RelCalc

------------------------------------------------------------
-- Term Semantic Invariance
------------------------------------------------------------

namespace RelTerm

variable {D : Type}
variable [Domain D]

/- Term evaluation depends only on term variables. -/
private theorem eval_eq_of_agreeOn_vars
    {σ τ : Assign D}
    (t : RelTerm D)
    (h : Assign.AgreeOn σ τ t.vars) :
    RelTerm.eval σ t = RelTerm.eval τ t := by
  cases t with
  | var x =>
      exact h x (by simp [RelTerm.vars])
  | const _ =>
      rfl

/- Tuple evaluation depends only on tuple variables. -/
private theorem evalVector_eq_of_agreeOn_tupleVars
    {σ τ : Assign D}
    {n : Nat}
    (ts : Vector (RelTerm D) n)
    (h : Assign.AgreeOn σ τ (RelTerm.tupleVars ts)) :
    RelTerm.evalVector σ ts = RelTerm.evalVector τ ts := by
  apply Vector.ext
  intro i hi
  rw [RelTerm.evalVector, RelTerm.evalVector,
    Vector.getElem_ofFn,
    Vector.getElem_ofFn]
  have hTerm :
      Assign.AgreeOn σ τ
        (ts.get ⟨i, hi⟩).vars := by
    intro x hx
    exact h x
      (RelTerm.mem_tupleVars_of_mem_get_vars
        (ts := ts) (i := ⟨i, hi⟩) hx)
  exact eval_eq_of_agreeOn_vars
    (t := ts.get ⟨i, hi⟩) hTerm

end RelTerm

------------------------------------------------------------
-- Agreement for Formula Satisfaction
------------------------------------------------------------

namespace RelCalc

namespace Formula

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- Satisfaction depends only on the free variables. -/
theorem holdsIn_eq_of_agreeOn_freeVars
    {Q : Set D}
    {I : Instance D Γ}
    {σ τ : Assign D}
    (φ : Formula D Γ)
    (h : Assign.AgreeOn σ τ φ.freeVars) :
    Formula.ArbitraryAssignSatIn Q I σ φ ↔
      Formula.ArbitraryAssignSatIn Q I τ φ := by
  induction φ generalizing σ τ with
  | top =>
      simp [Formula.ArbitraryAssignSatIn]
  | bot =>
      simp [Formula.ArbitraryAssignSatIn]
  | eq t1 t2 =>
      have h1 :
          Assign.AgreeOn σ τ t1.vars :=
        Assign.agreeOn_mono h
          (by
            intro x hx
            exact Finset.mem_union.mpr
              (Or.inl hx))
      have h2 :
          Assign.AgreeOn σ τ t2.vars :=
        Assign.agreeOn_mono h
          (by
            intro x hx
            exact Finset.mem_union.mpr
              (Or.inr hx))
      simp [Formula.ArbitraryAssignSatIn,
        RelTerm.eval_eq_of_agreeOn_vars
          (t := t1) h1,
        RelTerm.eval_eq_of_agreeOn_vars
          (t := t2) h2]
  | rel a =>
      have hTs :
          a.evalTuple σ = a.evalTuple τ := by
        simpa [RelAtom.evalTuple] using
          RelTerm.evalVector_eq_of_agreeOn_tupleVars
            (ts := a.args) h
      unfold Formula.ArbitraryAssignSatIn RelAtom.Sat
        RelAtom.evalFact RelFact.Mem
      rw [hTs]
  | and φ ψ ihφ ihψ =>
      have hφ :
          Formula.ArbitraryAssignSatIn Q I σ φ ↔
            Formula.ArbitraryAssignSatIn Q I τ φ :=
        ihφ
          (Assign.agreeOn_mono h
            (by
              intro x hx
              exact Finset.mem_union.mpr
                (Or.inl hx)))
      have hψ :
          Formula.ArbitraryAssignSatIn Q I σ ψ ↔
            Formula.ArbitraryAssignSatIn Q I τ ψ :=
        ihψ
          (Assign.agreeOn_mono h
            (by
              intro x hx
              exact Finset.mem_union.mpr
                (Or.inr hx)))
      simp [Formula.ArbitraryAssignSatIn, hφ, hψ]
  | or φ ψ ihφ ihψ =>
      have hφ :
          Formula.ArbitraryAssignSatIn Q I σ φ ↔
            Formula.ArbitraryAssignSatIn Q I τ φ :=
        ihφ
          (Assign.agreeOn_mono h
            (by
              intro x hx
              exact Finset.mem_union.mpr
                (Or.inl hx)))
      have hψ :
          Formula.ArbitraryAssignSatIn Q I σ ψ ↔
            Formula.ArbitraryAssignSatIn Q I τ ψ :=
        ihψ
          (Assign.agreeOn_mono h
            (by
              intro x hx
              exact Finset.mem_union.mpr
                (Or.inr hx)))
      simp [Formula.ArbitraryAssignSatIn, hφ, hψ]
  | not φ ih =>
      have hφ :
          Formula.ArbitraryAssignSatIn Q I σ φ ↔
            Formula.ArbitraryAssignSatIn Q I τ φ := ih h
      simp [Formula.ArbitraryAssignSatIn, hφ]
  | imp φ ψ ihφ ihψ =>
      have hφ :
          Formula.ArbitraryAssignSatIn Q I σ φ ↔
            Formula.ArbitraryAssignSatIn Q I τ φ :=
        ihφ
          (Assign.agreeOn_mono h
            (by
              intro x hx
              exact Finset.mem_union.mpr
                (Or.inl hx)))
      have hψ :
          Formula.ArbitraryAssignSatIn Q I σ ψ ↔
            Formula.ArbitraryAssignSatIn Q I τ ψ :=
        ihψ
          (Assign.agreeOn_mono h
            (by
              intro x hx
              exact Finset.mem_union.mpr
                (Or.inr hx)))
      simp [Formula.ArbitraryAssignSatIn, hφ, hψ]
  | iff φ ψ ihφ ihψ =>
      have hφ :
          Formula.ArbitraryAssignSatIn Q I σ φ ↔
            Formula.ArbitraryAssignSatIn Q I τ φ :=
        ihφ
          (Assign.agreeOn_mono h
            (by
              intro x hx
              exact Finset.mem_union.mpr
                (Or.inl hx)))
      have hψ :
          Formula.ArbitraryAssignSatIn Q I σ ψ ↔
            Formula.ArbitraryAssignSatIn Q I τ ψ :=
        ihψ
          (Assign.agreeOn_mono h
            (by
              intro x hx
              exact Finset.mem_union.mpr
                (Or.inr hx)))
      simp [Formula.ArbitraryAssignSatIn, hφ, hψ]
  | forall_ x φ ih =>
      constructor
      · intro hSat d hd
        have hUpd :
            Assign.AgreeOn
              (Assign.update σ x d)
              (Assign.update τ x d)
              φ.freeVars :=
          Assign.update_agreeOn
            (σ := σ) (τ := τ)
            (S := φ.freeVars)
            (x := x) (d := d) h
        exact
          (ih (σ := Assign.update σ x d)
            (τ := Assign.update τ x d)
            hUpd).mp (hSat d hd)
      · intro hSat d hd
        have hUpd :
            Assign.AgreeOn
              (Assign.update σ x d)
              (Assign.update τ x d)
              φ.freeVars :=
          Assign.update_agreeOn
            (σ := σ) (τ := τ)
            (S := φ.freeVars)
            (x := x) (d := d) h
        exact
          (ih (σ := Assign.update σ x d)
            (τ := Assign.update τ x d)
            hUpd).mpr (hSat d hd)
  | exists_ x φ ih =>
      constructor
      · rintro ⟨d, hdQ, hSat⟩
        refine ⟨d, hdQ, ?_⟩
        have hUpd :
            Assign.AgreeOn
              (Assign.update σ x d)
              (Assign.update τ x d)
              φ.freeVars :=
          Assign.update_agreeOn
            (σ := σ) (τ := τ)
            (S := φ.freeVars)
            (x := x) (d := d) h
        exact
          (ih (σ := Assign.update σ x d)
            (τ := Assign.update τ x d)
            hUpd).mp hSat
      · rintro ⟨d, hdQ, hSat⟩
        refine ⟨d, hdQ, ?_⟩
        have hUpd :
            Assign.AgreeOn
              (Assign.update σ x d)
              (Assign.update τ x d)
              φ.freeVars :=
          Assign.update_agreeOn
            (σ := σ) (τ := τ)
            (S := φ.freeVars)
            (x := x) (d := d) h
        exact
          (ih (σ := Assign.update σ x d)
            (τ := Assign.update τ x d)
            hUpd).mpr hSat

/- Typed satisfaction depends only on the free variables. -/
theorem satIn_eq_of_agreeOn_freeVars
    {Q : Set D}
    {I : Instance D Γ}
    {σ τ : Assign D}
    (φ : Formula D Γ)
    (h : Assign.AgreeOn σ τ φ.freeVars) :
    φ.SatIn I σ Q ↔
      φ.SatIn I τ Q := by
  have hMap :
      Assign.MapsInto σ φ.freeVars Q ↔
        Assign.MapsInto τ φ.freeVars Q :=
    Assign.mapsInto_congr h
  have hSat :
      Formula.ArbitraryAssignSatIn Q I σ φ ↔
        Formula.ArbitraryAssignSatIn Q I τ φ :=
    Formula.holdsIn_eq_of_agreeOn_freeVars
      (Q := Q) (I := I)
      (σ := σ) (τ := τ)
      (φ := φ) h
  constructor
  · rintro ⟨hMaps, hRaw⟩
    exact ⟨hMap.mp hMaps, hSat.mp hRaw⟩
  · rintro ⟨hMaps, hRaw⟩
    exact ⟨hMap.mpr hMaps, hSat.mpr hRaw⟩

/- Satisfaction of a sentence is assignment-independent. -/
private theorem satIn_eq_of_isSentence
    {Q : Set D}
    {I : Instance D Γ}
    {σ τ : Assign D}
    (φ : Formula D Γ)
    (h : φ.IsSentence) :
    φ.SatIn I σ Q ↔
      φ.SatIn I τ Q := by
  apply Formula.satIn_eq_of_agreeOn_freeVars
  intro x hx
  rw [h] at hx
  simp at hx

end Formula

end RelCalc

------------------------------------------------------------
-- Sentence Satisfaction
------------------------------------------------------------

namespace RelCalc

namespace Sentence

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- Assignment-free satisfaction for RelCalc sentences. -/
def SatIn
    (φ : Sentence D Γ)
    (I : Instance D Γ)
    (Q : Set D) : Prop :=
  ∀ σ : Assign D, φ.1.SatIn I σ Q

/- Sentence satisfaction is equivalent to any assignment. -/
theorem satIn_iff
    (φ : Sentence D Γ)
    (I : Instance D Γ)
    (Q : Set D)
    (σ : Assign D) :
    φ.SatIn I Q ↔
      φ.1.SatIn I σ Q := by
  constructor
  · intro h
    exact h σ
  · intro h τ
    exact
      (Formula.satIn_eq_of_isSentence
        (Q := Q) (I := I)
        (σ := σ) (τ := τ)
        φ.1 φ.2).mp h

end Sentence

end RelCalc
