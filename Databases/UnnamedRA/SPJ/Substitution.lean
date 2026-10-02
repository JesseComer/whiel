-- Author: Jesse Comer
import Databases.UnnamedRA.SPJ.Syntax
import Databases.UnnamedRA.Substitution

/-
  This file specifies substitution for SPJ unnamed
  relational algebra expressions.

  Key definitions include:
    * `SPJExpr.subst`

  Key theorems include:
    * `RAExpr.IsSPJ.subst`

  Intervening definitions and lemmas are construction,
  helper, or proof support.
-/

------------------------------------------------------------
-- SPJ Substitution
------------------------------------------------------------

namespace RawRAExpr

variable {A D : Type} [RelationNames A] [Domain D]

/-
  Substitution preserves `SPJ` if both the source and
  replacement expressions are in `SPJ`.
-/
theorem IsSPJ.subst
    {x : A}
    {e eRep : RawRAExpr A D}
    (hE : IsSPJ e)
    (hSub : IsSPJ eRep) :
    IsSPJ (e.subst x eRep) := by
  induction e with
  | top =>
      simp [RawRAExpr.subst, IsSPJ]
  | empty n =>
      simp [RawRAExpr.subst, IsSPJ]
  | rel y =>
      by_cases hy : y = x
      · subst hy
        simpa [RawRAExpr.subst] using hSub
      · simp [RawRAExpr.subst, hy, IsSPJ]
  | single d =>
      simp [RawRAExpr.subst, IsSPJ]
  | select φ e ih =>
      have hSPJ :=
          ih (by simpa [IsSPJ] using hE)
      simpa [RawRAExpr.subst, IsSPJ]
        using hSPJ
  | proj idxs e ih =>
      have hSPJ :=
          ih (by simpa [IsSPJ] using hE)
      simpa [RawRAExpr.subst, IsSPJ]
        using hSPJ
  | prod e₁ eRep ih₁ ih₂ =>
      have hPair : IsSPJ e₁ ∧ IsSPJ eRep := by
        simpa [IsSPJ] using hE
      have h₁ := ih₁ hPair.1
      have h₂ := ih₂ hPair.2
      simpa [RawRAExpr.subst, IsSPJ]
        using And.intro h₁ h₂
  | union e₁ eRep ih₁ ih₂ =>
      simp [IsSPJ] at hE
  | diff e₁ eRep ih₁ ih₂ =>
      simp [IsSPJ] at hE

end RawRAExpr

namespace RAExpr

variable {A D : Type} [Domain D]
variable {_ : RelationNames A}
variable {Γ : UnnamedSchema A}

/-
  Same-schema substitution preserves typed `SPJ`
  membership.
-/
theorem IsSPJ.subst
    {n : Nat}
    (e : RAExpr D Γ n)
    (X : Γ.syms)
    (eRep : RAExpr D Γ (Γ.arity X))
    (hE : e.IsSPJ)
    (hSub : eRep.IsSPJ) :
    (e.subst X eRep).IsSPJ := by
  simpa [IsSPJ, RAExpr.subst, RAExpr.substWithArityProof]
    using RawRAExpr.IsSPJ.subst
      (x := X.1)
      (e := e.expr)
      (eRep := eRep.expr)
      hE hSub

end RAExpr

namespace SPJExpr

variable {A D : Type} [Domain D]
variable {_ : RelationNames A}
variable {Γ : UnnamedSchema A}

/-
  Typed substitution preserves `SPJ` under an `SPJ`
  replacement of matching arity.
-/
def substWithArityProof
    {n m : Nat}
    (e : SPJExpr D Γ n)
    (x : A)
    (hX : Γ.arity? x = some m)
    (eRep : SPJExpr D Γ m) :
    SPJExpr D Γ n := by
  refine ⟨e.1.substWithArityProof x hX eRep.1, ?_⟩
  have hSPJ :
      RawRAExpr.IsSPJ
        (RawRAExpr.subst e.1.expr x eRep.1.expr) :=
    RawRAExpr.IsSPJ.subst
      (e := e.1.expr)
      (eRep := eRep.1.expr)
      e.2 eRep.2
  simpa [RAExpr.substWithArityProof] using hSPJ

/-
  Same-schema substitution at a schema symbol.
-/
def subst
    {n : Nat}
    (e : SPJExpr D Γ n)
    (X : Γ.syms)
    (eRep : SPJExpr D Γ (Γ.arity X)) :
    SPJExpr D Γ n :=
  e.substWithArityProof X.1
    (by
      simp [UnnamedSchema.arity?, X.2])
    eRep

end SPJExpr
