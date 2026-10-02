-- Author: Jesse Comer
import Databases.UnnamedRA.SPJU.Syntax
import Databases.UnnamedRA.Substitution

/-
  This file specifies substitution for SPJU unnamed
  relational algebra expressions.

  Key definitions include:
    * `SPJUExpr.subst`

  Key theorems include:
    * `RAExpr.IsSPJU.subst`

  Intervening definitions and lemmas are construction,
  helper, or proof support.
-/

------------------------------------------------------------
-- SPJU Substitution
------------------------------------------------------------

namespace RawRAExpr

variable {A D : Type} [RelationNames A] [Domain D]

/-
  Substitution preserves `SPJU` if both the source and
  replacement expressions are in `SPJU`.
-/
theorem IsSPJU.subst
    {x : A}
    {e eRep : RawRAExpr A D}
    (hE : IsSPJU e)
    (hSub : IsSPJU eRep) :
    IsSPJU (e.subst x eRep) := by
  induction e with
  | top =>
      simp [RawRAExpr.subst, IsSPJU]
  | empty n =>
      simp [RawRAExpr.subst, IsSPJU]
  | rel y =>
      by_cases hy : y = x
      · subst hy
        simpa [RawRAExpr.subst] using hSub
      · simp [RawRAExpr.subst, hy, IsSPJU]
  | single d =>
      simp [RawRAExpr.subst, IsSPJU]
  | select φ e ih =>
      have hSPJU :=
          ih (by simpa [IsSPJU] using hE)
      simpa [RawRAExpr.subst, IsSPJU]
        using hSPJU
  | proj idxs e ih =>
      have hSPJU :=
          ih (by simpa [IsSPJU] using hE)
      simpa [RawRAExpr.subst, IsSPJU]
        using hSPJU
  | prod e₁ eRep ih₁ ih₂ =>
      have hPair : IsSPJU e₁ ∧ IsSPJU eRep := by
        simpa [IsSPJU] using hE
      have h₁ := ih₁ hPair.1
      have h₂ := ih₂ hPair.2
      simpa [RawRAExpr.subst, IsSPJU]
        using And.intro h₁ h₂
  | union e₁ eRep ih₁ ih₂ =>
      have hPair : IsSPJU e₁ ∧ IsSPJU eRep := by
        simpa [IsSPJU] using hE
      have h₁ := ih₁ hPair.1
      have h₂ := ih₂ hPair.2
      simpa [RawRAExpr.subst, IsSPJU]
        using And.intro h₁ h₂
  | diff e₁ eRep ih₁ ih₂ =>
      simp [IsSPJU] at hE

end RawRAExpr

namespace RAExpr

variable {A D : Type} [Domain D]
variable {_ : RelationNames A}
variable {Γ : UnnamedSchema A}

/-
  Same-schema substitution preserves typed `SPJU`
  membership.
-/
theorem IsSPJU.subst
    {n : Nat}
    (e : RAExpr D Γ n)
    (X : Γ.syms)
    (eRep : RAExpr D Γ (Γ.arity X))
    (hE : e.IsSPJU)
    (hSub : eRep.IsSPJU) :
    (e.subst X eRep).IsSPJU := by
  simpa [IsSPJU, RAExpr.subst, RAExpr.substWithArityProof]
    using RawRAExpr.IsSPJU.subst
      (x := X.1)
      (e := e.expr)
      (eRep := eRep.expr)
      hE hSub

end RAExpr

namespace SPJUExpr

variable {A D : Type} [Domain D]
variable {_ : RelationNames A}
variable {Γ : UnnamedSchema A}

/-
  Typed substitution preserves `SPJU` under an `SPJU`
  replacement of matching arity.
-/
def substWithArityProof
    {n m : Nat}
    (e : SPJUExpr D Γ n)
    (x : A)
    (hX : Γ.arity? x = some m)
    (eRep : SPJUExpr D Γ m) :
    SPJUExpr D Γ n := by
  refine ⟨e.1.substWithArityProof x hX eRep.1, ?_⟩
  have hSPJU :
      RawRAExpr.IsSPJU
        (RawRAExpr.subst e.1.expr x eRep.1.expr) :=
    RawRAExpr.IsSPJU.subst
      (e := e.1.expr)
      (eRep := eRep.1.expr)
      e.2 eRep.2
  simpa [RAExpr.substWithArityProof] using hSPJU

/-
  Same-schema substitution at a schema symbol.
-/
def subst
    {n : Nat}
    (e : SPJUExpr D Γ n)
    (X : Γ.syms)
    (eRep : SPJUExpr D Γ (Γ.arity X)) :
    SPJUExpr D Γ n :=
  e.substWithArityProof X.1
    (by
      simp [UnnamedSchema.arity?, X.2])
    eRep

end SPJUExpr
