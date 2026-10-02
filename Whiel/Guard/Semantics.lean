-- Author: Jesse Comer
import Whiel.Guard.Syntax
import Databases.UnnamedRA.Semantics

/-
  Prop-valued semantics for Whiel guards.

  Key declarations:
    * `Guard.eval`

  Reduct endpoints use explicit `onExtension` retagging.
-/

------------------------------------------------------------
-- Guard Evaluation
------------------------------------------------------------

namespace Whiel

namespace Guard

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Same-schema semantics of guards. -/
def eval
    (φ : Guard D Γ)
    (I : Instance D Γ) : Prop :=
  match φ with
  | .«true» => True
  | .«false» => False
  | .eq e₁ e₂ => e₁.eval I = e₂.eval I
  | .subset e₁ e₂ => e₁.eval I ⊆ e₂.eval I
  | .and φ ψ => eval φ I ∧ eval ψ I
  | .or φ ψ => eval φ I ∨ eval ψ I
  | .not φ => ¬ eval φ I

@[simp] theorem eval_self_iff
    (I : Instance D Γ)
    (φ : Guard D Γ) :
    φ.eval I ↔ φ.eval I := by
  rfl

def decidableEval
    (I : Instance D Γ) :
    (φ : Guard D Γ) → Decidable (eval φ I)
| .«true» =>
    isTrue trivial
| .«false» =>
    isFalse (fun h => h)
| .eq e₁ e₂ =>
    by
      change Decidable (e₁.eval I = e₂.eval I)
      exact inferInstance
| .subset e₁ e₂ =>
    by
      change Decidable (e₁.eval I ⊆ e₂.eval I)
      exact inferInstance
| .and φ ψ =>
    by
      haveI : Decidable (eval φ I) :=
        decidableEval I φ
      haveI : Decidable (eval ψ I) :=
        decidableEval I ψ
      change Decidable (eval φ I ∧ eval ψ I)
      exact inferInstance
| .or φ ψ =>
    by
      haveI : Decidable (eval φ I) :=
        decidableEval I φ
      haveI : Decidable (eval ψ I) :=
        decidableEval I ψ
      change Decidable (eval φ I ∨ eval ψ I)
      exact inferInstance
| .not φ =>
    by
      haveI : Decidable (eval φ I) :=
        decidableEval I φ
      change Decidable (¬ eval φ I)
      exact inferInstance

instance instDecidableEval
    (I : Instance D Γ)
    (φ : Guard D Γ) :
    Decidable (eval φ I) :=
  decidableEval I φ

end Guard

end Whiel

------------------------------------------------------------
-- Evaluation Unfolding Lemmas
------------------------------------------------------------

namespace Whiel

namespace Guard

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

@[simp] theorem eval_true_iff
    (I : Instance D Γ) :
    eval (.«true» : Guard D Γ) I ↔ True :=
  Iff.rfl

@[simp] theorem eval_false_iff
    (I : Instance D Γ) :
    eval (.«false» : Guard D Γ) I ↔ False :=
  Iff.rfl

@[simp] theorem eval_eq_iff
    (I : Instance D Γ)
    {n : Nat}
    (e₁ e₂ : RAExpr D Γ n) :
    eval (.eq e₁ e₂) I ↔
      e₁.eval I = e₂.eval I :=
  Iff.rfl

@[simp] theorem eval_subset_iff
    (I : Instance D Γ)
    {n : Nat}
    (e₁ e₂ : RAExpr D Γ n) :
    eval (.subset e₁ e₂) I ↔
      e₁.eval I ⊆ e₂.eval I :=
  Iff.rfl

@[simp] theorem eval_and_iff
    (I : Instance D Γ)
    (φ ψ : Guard D Γ) :
    eval (.and φ ψ) I ↔
      eval φ I ∧ eval ψ I :=
  Iff.rfl

@[simp] theorem eval_or_iff
    (I : Instance D Γ)
    (φ ψ : Guard D Γ) :
    eval (.or φ ψ) I ↔
      eval φ I ∨ eval ψ I :=
  Iff.rfl

@[simp] theorem eval_not_iff
    (I : Instance D Γ)
    (φ : Guard D Γ) :
    eval (.not φ) I ↔ ¬ eval φ I :=
  Iff.rfl

@[simp] theorem eval_implies_iff
    (I : Instance D Γ)
    (φ ψ : Guard D Γ) :
    eval (φ.implies ψ) I ↔
      (¬ eval φ I ∨ eval ψ I) :=
  Iff.rfl

end Guard

end Whiel

------------------------------------------------------------
-- Reduct Property
------------------------------------------------------------

namespace Whiel

namespace Guard

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Same-schema RA helper for guard atoms. -/
private theorem ra_eval_agree
    {n : Nat}
    (e : RAExpr D Γ n)
    {I J : Instance D Γ}
    (hAgree : Instance.agreeOn e.symbols I J) :
    e.eval I = e.eval J := by
  have hRelAgree :
      I.agreeOnRelations e.supportSchema.syms J :=
    Instance.agreeOnRelations_of_agreeOn
      (by
        intro X hX
        exact hAgree X hX)
  letI : Fact (Γ.extensionOf e.supportSchema) :=
    ⟨e.extension_supportSchema⟩
  have hEval :=
    RAExpr.expansion_invariance
      (e := e)
      (Δ₁ := Γ)
      (Δ₂ := Γ)
      (I₁ := I)
      (I₂ := J)
      (hRelAgree := hRelAgree)
  simpa [RAExpr.eval, RAExpr.onExtension] using hEval

/- RA reduct helper for guard atoms. -/
private theorem ra_eval_reduct
    {Δ : UnnamedSchema A}
    [hExt : Fact (Γ.extensionOf Δ)]
    {n : Nat}
    (e : RAExpr D Δ n)
    (I : Instance D Γ)
    (J : Instance D Δ)
    (hReduct : Instance.reduct hExt.out I = J) :
    (e.onExtension hExt.out).eval I =
      e.eval J := by
  have hEval :=
    RAExpr.reduct_property
      (Γ := Δ) (Δ := Γ)
      (e := e) I
  rw [hReduct] at hEval
  simpa [RAExpr.eval] using hEval

/-
  Guard truth is invariant under agreement on its symbols.
-/
theorem eval_reduct_property
    (φ : Guard D Γ)
    {I J : Instance D Γ}
    (hAgree : Instance.agreeOn φ.symbols I J) :
    φ.eval I ↔ φ.eval J := by
  induction φ with
  | «true» =>
      simp
  | «false» =>
      simp
  | eq e₁ e₂ =>
      have hAgree₁ :
          Instance.agreeOn e₁.symbols I J := by
        intro X hX
        exact hAgree X (by simp [Guard.symbols, hX])
      have hAgree₂ :
          Instance.agreeOn e₂.symbols I J := by
        intro X hX
        exact hAgree X (by simp [Guard.symbols, hX])
      have h₁ :
          e₁.eval I = e₁.eval J :=
        ra_eval_agree e₁ hAgree₁
      have h₂ :
          e₂.eval I = e₂.eval J :=
        ra_eval_agree e₂ hAgree₂
      constructor
      · intro h
        simpa [h₁, h₂] using h
      · intro h
        simpa [h₁, h₂] using h
  | subset e₁ e₂ =>
      have hAgree₁ :
          Instance.agreeOn e₁.symbols I J := by
        intro X hX
        exact hAgree X (by simp [Guard.symbols, hX])
      have hAgree₂ :
          Instance.agreeOn e₂.symbols I J := by
        intro X hX
        exact hAgree X (by simp [Guard.symbols, hX])
      have h₁ :
          e₁.eval I = e₁.eval J :=
        ra_eval_agree e₁ hAgree₁
      have h₂ :
          e₂.eval I = e₂.eval J :=
        ra_eval_agree e₂ hAgree₂
      constructor
      · intro h
        simpa [h₁, h₂] using h
      · intro h
        simpa [h₁, h₂] using h
  | and φ ψ ihφ ihψ =>
      have hAgreeφ :
          Instance.agreeOn φ.symbols I J := by
        intro X hX
        exact hAgree X (by simp [Guard.symbols, hX])
      have hAgreeψ :
          Instance.agreeOn ψ.symbols I J := by
        intro X hX
        exact hAgree X (by simp [Guard.symbols, hX])
      have hφ := ihφ hAgreeφ
      have hψ := ihψ hAgreeψ
      constructor
      · intro h
        exact ⟨hφ.mp h.1, hψ.mp h.2⟩
      · intro h
        exact ⟨hφ.mpr h.1, hψ.mpr h.2⟩
  | or φ ψ ihφ ihψ =>
      have hAgreeφ :
          Instance.agreeOn φ.symbols I J := by
        intro X hX
        exact hAgree X (by simp [Guard.symbols, hX])
      have hAgreeψ :
          Instance.agreeOn ψ.symbols I J := by
        intro X hX
        exact hAgree X (by simp [Guard.symbols, hX])
      have hφ := ihφ hAgreeφ
      have hψ := ihψ hAgreeψ
      constructor
      · intro h
        cases h with
        | inl hLeft =>
            exact Or.inl (hφ.mp hLeft)
        | inr hRight =>
            exact Or.inr (hψ.mp hRight)
      · intro h
        cases h with
        | inl hLeft =>
            exact Or.inl (hφ.mpr hLeft)
        | inr hRight =>
            exact Or.inr (hψ.mpr hRight)
  | not φ ih =>
      have hAgreeφ :
          Instance.agreeOn φ.symbols I J := by
        intro X hX
        exact hAgree X (by simp [Guard.symbols, hX])
      have hφ := ih hAgreeφ
      constructor
      · intro h hJ
        exact h (hφ.mpr hJ)
      · intro h hI
        exact h (hφ.mp hI)

/-
  Evaluation after retagging to an extension agrees with
  the reduct.
-/
theorem onExtension_eval_reduct
    {Δ : UnnamedSchema A}
    [hExt : Fact (Γ.extensionOf Δ)]
    (φ : Guard D Δ)
    (I : Instance D Γ)
    (J : Instance D Δ)
    (hReduct : Instance.reduct hExt.out I = J) :
    (φ.onExtension hExt.out).eval I ↔ φ.eval J := by
  induction φ generalizing I J with
  | «true» =>
      rfl
  | «false» =>
      rfl
  | eq e₁ e₂ =>
      have h₁ :
          (e₁.onExtension hExt.out).eval I =
            e₁.eval J := by
        exact ra_eval_reduct e₁ I J hReduct
      have h₂ :
          (e₂.onExtension hExt.out).eval I =
            e₂.eval J := by
        exact ra_eval_reduct e₂ I J hReduct
      constructor
      · intro h
        simpa [Guard.eval, Guard.onExtension, Guard.eval,
          h₁, h₂] using h
      · intro h
        simpa [Guard.eval, Guard.onExtension, Guard.eval,
          h₁, h₂] using h
  | subset e₁ e₂ =>
      have h₁ :
          (e₁.onExtension hExt.out).eval I =
            e₁.eval J := by
        exact ra_eval_reduct e₁ I J hReduct
      have h₂ :
          (e₂.onExtension hExt.out).eval I =
            e₂.eval J := by
        exact ra_eval_reduct e₂ I J hReduct
      constructor
      · intro h
        simpa [Guard.eval, Guard.onExtension, Guard.eval,
          h₁, h₂] using h
      · intro h
        simpa [Guard.eval, Guard.onExtension, Guard.eval,
          h₁, h₂] using h
  | and φ ψ ihφ ihψ =>
      exact and_congr (ihφ I J hReduct) (ihψ I J hReduct)
  | or φ ψ ihφ ihψ =>
      exact or_congr (ihφ I J hReduct) (ihψ I J hReduct)
  | not φ ih =>
      exact not_congr (ih I J hReduct)

/-
  Retagged guard truth is invariant under ambient
  agreement.
-/
theorem onExtension_eval_agree
    {Δ : UnnamedSchema A}
    [hExt : Fact (Δ.extensionOf Γ)]
    (φ : Guard D Γ)
    {I J : Instance D Δ}
    (hAgree : Instance.agreeOn φ.symbols I J) :
    (φ.onExtension hExt.out).eval I ↔
      (φ.onExtension hExt.out).eval J := by
  exact
    eval_reduct_property
      (φ.onExtension hExt.out)
      (by
        intro X hXS
        exact hAgree X (by simpa using hXS))

end Guard

end Whiel
