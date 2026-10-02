-- Author: Jesse Comer
import Databases.RelCalc.CQ.Syntax
import Databases.RelCalc.FormulaSemantics

/-
  This file proves monotonicity of conjunctive-query
  relational-calculus formulas.

  Key theorems include:
    * `IsConjunctive.arbitraryAssignSatIn_monotone`
    * `Formula.IsCQ.arbitraryAssignSatIn_monotone`
    * `RelCalc.CQFormula.satIn_monotone`

  Intervening definitions and lemmas are construction,
  helper, or proof support.
-/

------------------------------------------------------------
-- Monotonicity Properties
------------------------------------------------------------

namespace RelCalc

namespace Formula

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Conjunctive matrices are monotone under pointwise
  instance inclusion for a fixed quantifier domain.
-/
theorem IsConjunctive.arbitraryAssignSatIn_monotone
    {φ : Formula D Γ}
    (hφ : φ.IsConjunctive)
    {Q : Set D}
    {I J : Instance D Γ}
    {σ : Assign D}
    (hSub : Instance.Subset I J) :
    Formula.ArbitraryAssignSatIn Q I σ φ →
      Formula.ArbitraryAssignSatIn Q J σ φ := by
  induction φ with
  | top =>
      simp [Formula.ArbitraryAssignSatIn]
  | bot =>
      simp [Formula.ArbitraryAssignSatIn]
  | eq t₁ t₂ =>
      simp [Formula.ArbitraryAssignSatIn]
  | rel a =>
      intro h
      exact hSub a.rel h
  | and φ ψ ihφ ihψ =>
      have hPair :
          φ.IsConjunctive ∧ ψ.IsConjunctive := by
        simpa [Formula.IsConjunctive] using hφ
      intro h
      exact
        ⟨ihφ hPair.1 h.1,
          ihψ hPair.2 h.2⟩
  | or φ ψ ihφ ihψ =>
      simp [Formula.IsConjunctive] at hφ
  | not φ ih =>
      simp [Formula.IsConjunctive] at hφ
  | imp φ ψ ihφ ihψ =>
      simp [Formula.IsConjunctive] at hφ
  | iff φ ψ ihφ ihψ =>
      simp [Formula.IsConjunctive] at hφ
  | forall_ x φ ih =>
      simp [Formula.IsConjunctive] at hφ
  | exists_ x φ ih =>
      simp [Formula.IsConjunctive] at hφ

/-
  Conjunctive-matrix bounded-domain satisfaction is monotone
  under pointwise instance inclusion for a fixed quantifier
  domain.
-/
theorem IsConjunctive.satIn_monotone
    {φ : Formula D Γ}
    (hφ : φ.IsConjunctive)
    {Q : Set D}
    {I J : Instance D Γ}
    {σ : Assign D}
    (hSub : Instance.Subset I J) :
    φ.SatIn I σ Q →
      φ.SatIn J σ Q := by
  intro hSat
  exact
    ⟨hSat.1,
      hφ.arbitraryAssignSatIn_monotone hSub hSat.2⟩

/-
  CQ formulas are monotone under pointwise instance
  inclusion for a fixed quantifier domain.
-/
theorem IsCQ.arbitraryAssignSatIn_monotone
    {φ : Formula D Γ}
    (hφ : φ.IsCQ)
    {Q : Set D}
    {I J : Instance D Γ}
    {σ : Assign D}
    (hSub : Instance.Subset I J) :
    Formula.ArbitraryAssignSatIn Q I σ φ →
      Formula.ArbitraryAssignSatIn Q J σ φ := by
  induction φ generalizing σ with
  | top =>
      exact
        Formula.IsConjunctive.arbitraryAssignSatIn_monotone
          (by simp [Formula.IsConjunctive])
          hSub
  | bot =>
      exact
        Formula.IsConjunctive.arbitraryAssignSatIn_monotone
          (by simp [Formula.IsConjunctive])
          hSub
  | eq t₁ t₂ =>
      exact
        Formula.IsConjunctive.arbitraryAssignSatIn_monotone
          (by simp [Formula.IsConjunctive])
          hSub
  | rel a =>
      exact
        Formula.IsConjunctive.arbitraryAssignSatIn_monotone
          (by simp [Formula.IsConjunctive])
          hSub
  | and φ ψ ihφ ihψ =>
      exact
        Formula.IsConjunctive.arbitraryAssignSatIn_monotone
          (by simpa [Formula.IsCQ] using hφ)
          hSub
  | or φ ψ ihφ ihψ =>
      simp [Formula.IsCQ] at hφ
  | not φ ih =>
      simp [Formula.IsCQ] at hφ
  | imp φ ψ ihφ ihψ =>
      simp [Formula.IsCQ] at hφ
  | iff φ ψ ihφ ihψ =>
      simp [Formula.IsCQ] at hφ
  | forall_ x φ ih =>
      simp [Formula.IsCQ] at hφ
  | exists_ x φ ih =>
      intro hSat
      rcases hSat with ⟨d, hdQ, hBody⟩
      exact
        ⟨d, hdQ,
          ih (by simpa [Formula.IsCQ] using hφ) hBody⟩

/-
  CQ bounded-domain satisfaction is monotone under pointwise
  instance inclusion for a fixed quantifier domain.
-/
theorem IsCQ.satIn_monotone
    {φ : Formula D Γ}
    (hφ : φ.IsCQ)
    {Q : Set D}
    {I J : Instance D Γ}
    {σ : Assign D}
    (hSub : Instance.Subset I J) :
    φ.SatIn I σ Q →
      φ.SatIn J σ Q := by
  intro hSat
  exact
    ⟨hSat.1,
      hφ.arbitraryAssignSatIn_monotone hSub hSat.2⟩

end Formula

namespace CQFormula

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/-
  CQ formulas are monotone under pointwise instance
  inclusion for bounded-domain satisfaction.
-/
theorem satIn_monotone
    (φ : CQFormula D Γ)
    {Q : Set D}
    {I J : Instance D Γ}
    {σ : Assign D}
    (hSub : Instance.Subset I J) :
    φ.1.SatIn I σ Q →
      φ.1.SatIn J σ Q :=
  φ.2.satIn_monotone hSub

end CQFormula

end RelCalc
