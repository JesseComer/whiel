import Whiel.Rewrites.UnnamedRA
import Whiel.Guard.Semantics

/-
  Syntax-directed Whiel guard rewrites.

  Key declarations:
    * `Whiel.Guard.clean`
    * `Whiel.Guard.eval_clean_iff`
-/

namespace Whiel

namespace Guard

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Conjoin two guards, deleting boolean identities. -/
def cleanAnd :
    Guard D Γ → Guard D Γ → Guard D Γ
| .«true», ψ => ψ
| φ, .«true» => φ
| .«false», _ => .«false»
| _, .«false» => .«false»
| φ, ψ => .and φ ψ

/- Disjoin two guards, deleting boolean identities. -/
def cleanOr :
    Guard D Γ → Guard D Γ → Guard D Γ
| .«false», ψ => ψ
| φ, .«false» => φ
| .«true», _ => .«true»
| _, .«true» => .«true»
| φ, ψ => .or φ ψ

/- Negate a guard, simplifying boolean constants. -/
def cleanNot :
    Guard D Γ → Guard D Γ
| .«true» => .«false»
| .«false» => .«true»
| φ => .not φ

/-
  Remove boolean identities and clean embedded RA
  expressions.
-/
def clean :
    Guard D Γ → Guard D Γ
| .«true» => .«true»
| .«false» => .«false»
| .eq e₁ e₂ => .eq e₁.clean e₂.clean
| .subset e₁ e₂ => .subset e₁.clean e₂.clean
| .and φ ψ => cleanAnd (clean φ) (clean ψ)
| .or φ ψ => cleanOr (clean φ) (clean ψ)
| .not φ => cleanNot (clean φ)

/- Cleaning one conjunction preserves guard truth. -/
theorem eval_cleanAnd_iff
    (I : Instance D Γ)
    (φ ψ : Guard D Γ) :
    (cleanAnd φ ψ).eval I ↔
      (Guard.and φ ψ).eval I := by
  cases φ <;> cases ψ <;>
    simp [cleanAnd, eval]

/- Cleaning one disjunction preserves guard truth. -/
theorem eval_cleanOr_iff
    (I : Instance D Γ)
    (φ ψ : Guard D Γ) :
    (cleanOr φ ψ).eval I ↔
      (Guard.or φ ψ).eval I := by
  cases φ <;> cases ψ <;>
    simp [cleanOr, eval]

/- Cleaning one negation preserves guard truth. -/
theorem eval_cleanNot_iff
    (I : Instance D Γ)
    (φ : Guard D Γ) :
    (cleanNot φ).eval I ↔
      (Guard.not φ).eval I := by
  cases φ <;> simp [cleanNot, eval]

/- Removing boolean identities preserves guard truth. -/
theorem eval_clean_iff
    (I : Instance D Γ)
    (φ : Guard D Γ) :
    φ.clean.eval I ↔ φ.eval I := by
  induction φ with
  | «true» =>
      simp [clean]
  | «false» =>
      simp [clean]
  | eq e₁ e₂ =>
      simp [clean, eval]
  | subset e₁ e₂ =>
      simp [clean, eval]
  | and φ ψ ihφ ihψ =>
      rw [clean]
      rw [eval_cleanAnd_iff]
      simpa [eval] using and_congr ihφ ihψ
  | or φ ψ ihφ ihψ =>
      rw [clean]
      rw [eval_cleanOr_iff]
      simpa [eval] using or_congr ihφ ihψ
  | not φ ih =>
      rw [clean]
      rw [eval_cleanNot_iff]
      simpa [eval] using not_congr ih

end Guard

end Whiel
