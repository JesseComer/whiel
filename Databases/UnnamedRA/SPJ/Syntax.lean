-- Author: Jesse Comer
import Databases.UnnamedRA.SPJU.Syntax

/-
  This file specifies the SPJ fragment of unnamed
  relational algebra.

  Key definitions include:
    * `RAExpr.IsSPJ`
    * `SPJExpr`

  Main fragment casts include:
    * `SPJExpr.toSPJU`

  Intervening definitions and lemmas are construction,
  helper, or proof support.
-/

------------------------------------------------------------
-- SPJ Relational Algebra
------------------------------------------------------------

namespace RawRAExpr

variable {A D : Type} [RelationNames A] [Domain D]

/-
  `SPJ` expressions are built from relation names and
  singleton constants using `top`, `empty`, select,
  project, and product.
-/
def IsSPJ : RawRAExpr A D → Prop
| .top => True
| .empty _ => True
| .rel _ => True
| .single _ => True
| .select _ e => IsSPJ e
| .proj _ e => IsSPJ e
| .prod e₁ e₂ => IsSPJ e₁ ∧ IsSPJ e₂
| .union _ _ => False
| .diff _ _ => False

/-
  `SPJ` membership is decidable by structural recursion on
  the expression.
-/
def IsSPJ.decidable :
    (e : RawRAExpr A D) → Decidable (IsSPJ e)
| .top => isTrue trivial
| .empty _ => isTrue trivial
| .rel _ => isTrue trivial
| .single _ => isTrue trivial
| .select _ e => IsSPJ.decidable e
| .proj _ e => IsSPJ.decidable e
| .prod e₁ e₂ =>
    match IsSPJ.decidable e₁, IsSPJ.decidable e₂ with
    | isTrue h₁, isTrue h₂ => isTrue ⟨h₁, h₂⟩
    | isFalse h₁, _ =>
        isFalse (fun h => h₁ h.1)
    | _, isFalse h₂ =>
        isFalse (fun h => h₂ h.2)
| .union _ _ => isFalse (fun h => h)
| .diff _ _ => isFalse (fun h => h)

instance
    (e : RawRAExpr A D) :
    Decidable (IsSPJ e) :=
  IsSPJ.decidable e

/-
  Every `SPJ` expression is an `SPJU` expression.
-/
theorem IsSPJ.toIsSPJU
    {e : RawRAExpr A D}
    (h : IsSPJ e) :
    IsSPJU e := by
  induction e with
  | top =>
      simp [IsSPJU]
  | empty n =>
      simp [IsSPJU]
  | rel X =>
      simp [IsSPJU]
  | single d =>
      simp [IsSPJU]
  | select φ e ih =>
      have hSub : IsSPJ e := by
        simpa [IsSPJ] using h
      have hSPJU : IsSPJU e := ih hSub
      simpa [IsSPJ, IsSPJU]
        using hSPJU
  | proj idxs e ih =>
      have hSub : IsSPJ e := by
        simpa [IsSPJ] using h
      have hSPJU : IsSPJU e := ih hSub
      simpa [IsSPJ, IsSPJU]
        using hSPJU
  | prod e₁ e₂ ih₁ ih₂ =>
      have hPair : IsSPJ e₁ ∧ IsSPJ e₂ := by
        simpa [IsSPJ] using h
      have hSPJU₁ : IsSPJU e₁ := ih₁ hPair.1
      have hSPJU₂ : IsSPJU e₂ := ih₂ hPair.2
      simpa [IsSPJU]
        using And.intro hSPJU₁ hSPJU₂
  | union e₁ e₂ ih₁ ih₂ =>
      simp [IsSPJ] at h
  | diff e₁ e₂ ih₁ ih₂ =>
      simp [IsSPJ] at h

end RawRAExpr

namespace RAExpr

variable {A D : Type} [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A} {n : Nat}

/- Typed SPJ membership for well-formed RA expressions. -/
def IsSPJ (e : RAExpr D Γ n) : Prop :=
  RawRAExpr.IsSPJ e.expr

instance
    (e : RAExpr D Γ n) :
    Decidable (IsSPJ e) :=
  inferInstanceAs (Decidable (RawRAExpr.IsSPJ e.expr))

/-
  Every typed `SPJ` expression is typed `SPJU`.
-/
theorem IsSPJ.toIsSPJU
    {e : RAExpr D Γ n}
    (h : IsSPJ e) :
    IsSPJU e :=
  RawRAExpr.IsSPJ.toIsSPJU h

end RAExpr

/- Well-formed `SPJ` expressions. -/
abbrev SPJExpr
    {A : Type}
    {_ : RelationNames A}
    (D : Type) [Domain D]
    (Γ : UnnamedSchema A) (n : Nat) : Type :=
  {e : RAExpr D Γ n // e.IsSPJ}

namespace RAExpr

variable {A D : Type} [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A} {n : Nat}

/- Cast an RA expression with an `SPJ` proof. -/
def toSPJ
    (e : RAExpr D Γ n)
    (h : e.IsSPJ) :
    SPJExpr D Γ n :=
  ⟨e, h⟩

end RAExpr

namespace SPJExpr

variable {A D : Type} [Domain D]
variable {_ : RelationNames A}
variable {Γ : UnnamedSchema A}

/-
  Every typed `SPJ` expression induces a typed `SPJU`
  expression with the same underlying `RAExpr`.
-/
def toSPJU
    {n : Nat}
    (e : SPJExpr D Γ n) :
    SPJUExpr D Γ n :=
  ⟨e.1, RAExpr.IsSPJ.toIsSPJU e.2⟩

end SPJExpr
