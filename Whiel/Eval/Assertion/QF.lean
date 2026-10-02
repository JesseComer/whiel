-- Author: Jesse Comer
import Whiel.Eval.RA.Fast
import Whiel.AssertExpr.Semantics

/-
  Fast Boolean evaluation for Whiel guards and no-bound
  assertions.

  Guards use `FastRA.eval` at atoms.  Full assertions are
  supported only when they have no existentially bound
  relation symbols.
-/

------------------------------------------------------------
-- Fast Guard Evaluation
------------------------------------------------------------

namespace Whiel

namespace FastGuard

variable {A D : Type}
variable [RelationNames A]
variable [Domain D] [LinearOrder D] [Hashable D]
variable {Γ : UnnamedSchema A}

/- Direct Boolean guard evaluation over materialized instances. -/
def eval
    (φ : Guard D Γ)
    (S : FastInstance D Γ) : Bool :=
  match φ with
  | .«true» => true
  | .«false» => false
  | .eq e₁ e₂ =>
      FastRelation.equal
        (FastRA.eval e₁ S)
        (FastRA.eval e₂ S)
  | .subset e₁ e₂ =>
      FastRelation.subset
        (FastRA.eval e₁ S)
        (FastRA.eval e₂ S)
  | .and φ ψ => eval φ S && eval ψ S
  | .or φ ψ => eval φ S || eval ψ S
  | .not φ => !(eval φ S)

/- Boolean fast guard evaluation reflects Prop guard semantics. -/
theorem eval_eq_true_iff
    (φ : Guard D Γ)
    (S : FastInstance D Γ) :
    eval φ S = true ↔ φ.eval S.toInstance := by
  induction φ with
  | «true» =>
      simp [eval, Guard.eval]
  | «false» =>
      simp [eval, Guard.eval]
  | eq e₁ e₂ =>
      simp [eval, Guard.eval, FastRelation.equal_iff,
        FastRA.eval_correct]
  | subset e₁ e₂ =>
      simp [eval, Guard.eval, FastRelation.subset_iff,
        FastRA.eval_correct]
  | and φ ψ ihφ ihψ =>
      simp [eval, Guard.eval, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      simp [eval, Guard.eval, ihφ, ihψ]
  | not φ ih =>
      constructor
      · intro hTrue hEval
        have hSub : eval φ S = true := ih.mpr hEval
        have hNot : !(eval φ S) = true := by
          simpa [eval] using hTrue
        rw [hSub] at hNot
        cases hNot
      · intro hNotEval
        cases hSub : eval φ S
        · simp [eval, hSub]
        · have hEval : φ.eval S.toInstance := ih.mp hSub
          exact False.elim (hNotEval hEval)

/- False fast guard evaluation reflects negated Prop semantics. -/
theorem eval_eq_false_iff
    (φ : Guard D Γ)
    (S : FastInstance D Γ) :
    eval φ S = false ↔ ¬ φ.eval S.toInstance := by
  constructor
  · intro hFalse hEval
    have hTrue : eval φ S = true :=
      (eval_eq_true_iff φ S).mpr hEval
    rw [hFalse] at hTrue
    cases hTrue
  · intro hNot
    cases h : eval φ S
    · rfl
    · have hEval : φ.eval S.toInstance :=
        (eval_eq_true_iff φ S).mp h
      exact False.elim (hNot hEval)

end FastGuard

end Whiel

------------------------------------------------------------
-- Fast No-Bound Assertion Evaluation
------------------------------------------------------------

namespace Whiel

namespace FastAssert

variable {A D : Type}
variable [RelationNames A]
variable [Domain D] [LinearOrder D] [Hashable D]
variable {Γ : UnnamedSchema A}

/- Fast assertion evaluation for no-bound assertions. -/
def evalNoBound?
    (φ : AssertExpr D Γ)
    (S : FastInstance D Γ) : Option Bool :=
  if hNo : φ.NoBoundSymbols then
    some (FastGuard.eval (φ.toQF hNo) S)
  else
    none

/- A `true` fast no-bound result implies assertion truth. -/
theorem evalNoBound?_eq_some_true
    (φ : AssertExpr D Γ)
    (S : FastInstance D Γ) :
    evalNoBound? φ S = some true →
      φ.eval S.toInstance := by
  by_cases hNo : φ.NoBoundSymbols
  · intro hEval
    have hGuard :
        FastGuard.eval (φ.toQF hNo) S = true := by
      simpa [evalNoBound?, hNo] using hEval
    have hQF :
        (φ.toQF hNo).eval S.toInstance :=
      (FastGuard.eval_eq_true_iff
        (φ.toQF hNo) S).mp hGuard
    exact (AssertExpr.toQF_eval_iff
      φ hNo S.toInstance).mp hQF
  · intro hEval
    simp [evalNoBound?, hNo] at hEval

/- A `false` fast no-bound result implies assertion falsity. -/
theorem evalNoBound?_eq_some_false
    (φ : AssertExpr D Γ)
    (S : FastInstance D Γ) :
    evalNoBound? φ S = some false →
      ¬ φ.eval S.toInstance := by
  by_cases hNo : φ.NoBoundSymbols
  · intro hEval hAssert
    have hGuard :
        FastGuard.eval (φ.toQF hNo) S = false := by
      simpa [evalNoBound?, hNo] using hEval
    have hNotQF :
        ¬ (φ.toQF hNo).eval S.toInstance :=
      (FastGuard.eval_eq_false_iff
        (φ.toQF hNo) S).mp hGuard
    have hQF :
        (φ.toQF hNo).eval S.toInstance :=
      (AssertExpr.toQF_eval_iff
        φ hNo S.toInstance).mpr hAssert
    exact hNotQF hQF
  · intro hEval
    simp [evalNoBound?, hNo] at hEval

end FastAssert

end Whiel
