-- Author: Jesse Comer
import Databases.UnnamedRA.Syntax

/-
  This file specifies the SPJU fragment of unnamed
  relational algebra.

  Key definitions include:
    * `RAExpr.IsSPJU`
    * `SPJUExpr`

  Intervening definitions and lemmas are construction,
  helper, or proof support.
-/

------------------------------------------------------------
-- SPJU Relational Algebra
------------------------------------------------------------

namespace RawRAExpr

variable {A D : Type} [RelationNames A] [Domain D]

/-
  `SPJU` expressions are built from relation names and
  singleton constants using `top`, `empty`, select,
  project, product, and union.
-/
def IsSPJU : RawRAExpr A D → Prop
| .top => True
| .empty _ => True
| .rel _ => True
| .single _ => True
| .select _ e => IsSPJU e
| .proj _ e => IsSPJU e
| .prod e₁ e₂ => IsSPJU e₁ ∧ IsSPJU e₂
| .union e₁ e₂ => IsSPJU e₁ ∧ IsSPJU e₂
| .diff _ _ => False

/-
  `SPJU` membership is decidable by structural recursion on
  the expression.
-/
def IsSPJU.decidable :
    (e : RawRAExpr A D) → Decidable (IsSPJU e)
| .top => isTrue trivial
| .empty _ => isTrue trivial
| .rel _ => isTrue trivial
| .single _ => isTrue trivial
| .select _ e => IsSPJU.decidable e
| .proj _ e => IsSPJU.decidable e
| .prod e₁ e₂ =>
    match IsSPJU.decidable e₁, IsSPJU.decidable e₂ with
    | isTrue h₁, isTrue h₂ => isTrue ⟨h₁, h₂⟩
    | isFalse h₁, _ =>
        isFalse (fun h => h₁ h.1)
    | _, isFalse h₂ =>
        isFalse (fun h => h₂ h.2)
| .union e₁ e₂ =>
    match IsSPJU.decidable e₁, IsSPJU.decidable e₂ with
    | isTrue h₁, isTrue h₂ => isTrue ⟨h₁, h₂⟩
    | isFalse h₁, _ =>
        isFalse (fun h => h₁ h.1)
    | _, isFalse h₂ =>
        isFalse (fun h => h₂ h.2)
| .diff _ _ => isFalse (fun h => h)

instance
    (e : RawRAExpr A D) :
    Decidable (IsSPJU e) :=
  IsSPJU.decidable e

end RawRAExpr

namespace RAExpr

variable {A D : Type} [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A} {n : Nat}

/- Typed SPJU membership for well-formed RA expressions. -/
def IsSPJU (e : RAExpr D Γ n) : Prop :=
  RawRAExpr.IsSPJU e.expr

instance
    (e : RAExpr D Γ n) :
    Decidable (IsSPJU e) :=
  inferInstanceAs (Decidable (RawRAExpr.IsSPJU e.expr))

end RAExpr

/- Well-formed `SPJU` expressions. -/
abbrev SPJUExpr
    {A : Type}
    {_ : RelationNames A}
    (D : Type) [Domain D]
    (Γ : UnnamedSchema A) (n : Nat) : Type :=
  {e : RAExpr D Γ n // e.IsSPJU}

namespace RAExpr

variable {A D : Type} [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A} {n : Nat}

/- Cast an RA expression with an `SPJU` proof. -/
def toSPJU
    (e : RAExpr D Γ n)
    (h : e.IsSPJU) :
    SPJUExpr D Γ n :=
  ⟨e, h⟩

end RAExpr
