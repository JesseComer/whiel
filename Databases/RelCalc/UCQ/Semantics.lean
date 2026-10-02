-- Author: Jesse Comer
import Databases.RelCalc.UCQ.Syntax
import Databases.RelCalc.CQ.Semantics

/-
  This file proves monotonicity of UCQ relational-calculus
  formulas.

  Key theorems include:
    * `RelCalc.Formula.IsUCQ.arbitraryAssignSatIn_monotone`
    * `RelCalc.UCQFormula.satIn_monotone`

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
  UCQ formulas are monotone under pointwise instance
  inclusion for a fixed quantifier domain.
-/
theorem IsUCQ.arbitraryAssignSatIn_monotone
    {φ : Formula D Γ}
    (hφ : φ.IsUCQ)
    {Q : Set D}
    {I J : Instance D Γ}
    {σ : Assign D}
    (hSub : Instance.Subset I J) :
    Formula.ArbitraryAssignSatIn Q I σ φ →
      Formula.ArbitraryAssignSatIn Q J σ φ := by
  induction φ generalizing σ with
  | top =>
      exact
        Formula.IsCQ.arbitraryAssignSatIn_monotone
          (by simpa [Formula.IsUCQ] using hφ)
          hSub
  | bot =>
      exact
        Formula.IsCQ.arbitraryAssignSatIn_monotone
          (by simpa [Formula.IsUCQ] using hφ)
          hSub
  | eq t₁ t₂ =>
      exact
        Formula.IsCQ.arbitraryAssignSatIn_monotone
          (by simpa [Formula.IsUCQ] using hφ)
          hSub
  | rel a =>
      exact
        Formula.IsCQ.arbitraryAssignSatIn_monotone
          (by simpa [Formula.IsUCQ] using hφ)
          hSub
  | and φ ψ ihφ ihψ =>
      exact
        Formula.IsCQ.arbitraryAssignSatIn_monotone
          (by simpa [Formula.IsUCQ] using hφ)
          hSub
  | or φ ψ ihφ ihψ =>
      have hPair : φ.IsUCQ ∧ ψ.IsUCQ := by
        simpa [Formula.IsUCQ] using hφ
      intro hSat
      rcases hSat with hSat | hSat
      · exact Or.inl (ihφ hPair.1 hSat)
      · exact Or.inr (ihψ hPair.2 hSat)
  | not φ ih =>
      simp [Formula.IsUCQ] at hφ
  | imp φ ψ ihφ ihψ =>
      simp [Formula.IsUCQ] at hφ
  | iff φ ψ ihφ ihψ =>
      simp [Formula.IsUCQ] at hφ
  | forall_ x φ ih =>
      simp [Formula.IsUCQ] at hφ
  | exists_ x φ ih =>
      exact
        Formula.IsCQ.arbitraryAssignSatIn_monotone
          (by simpa [Formula.IsUCQ] using hφ)
          hSub

/-
  UCQ bounded-domain satisfaction is monotone under
  pointwise inclusion for a fixed quantifier domain.
-/
theorem IsUCQ.satIn_monotone
    {φ : Formula D Γ}
    (hφ : φ.IsUCQ)
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

namespace UCQFormula

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/-
  UCQ formulas are monotone under pointwise instance
  inclusion for bounded-domain satisfaction.
-/
theorem satIn_monotone
    (φ : UCQFormula D Γ)
    {Q : Set D}
    {I J : Instance D Γ}
    {σ : Assign D}
    (hSub : Instance.Subset I J) :
    φ.1.SatIn I σ Q →
      φ.1.SatIn J σ Q :=
  φ.2.satIn_monotone hSub

end UCQFormula

end RelCalc
