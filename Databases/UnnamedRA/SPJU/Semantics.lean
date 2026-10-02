-- Author: Jesse Comer
import Databases.UnnamedRA.Semantics
import Databases.UnnamedRA.SPJU.Syntax

/-
  This file proves monotonicity of SPJU unnamed
  relational algebra expressions.

  Key theorems include:
    * `SPJUExpr.eval_monotone`

  Intervening definitions and lemmas are construction,
  helper, or proof support.
-/

------------------------------------------------------------
-- Monotonicity Properties
------------------------------------------------------------

namespace FinRelation

variable {D : Type} [Domain D]

/-
  Selection is monotone with respect to subset inclusion.
-/
omit [Domain D] in private theorem select_mono
    {n : Nat}
    (p : Tuple D n → Prop)
    [DecidablePred p]
    {R S : FinRelation D n}
    (hRS : R ⊆ S) :
    FinRelation.select p R ⊆ FinRelation.select p S := by
  intro t ht
  rcases Finset.mem_filter.mp ht with ⟨htR, hp⟩
  exact Finset.mem_filter.mpr ⟨hRS htR, hp⟩

/-
  Projection is monotone with respect to subset inclusion.
-/
private theorem proj_mono
    {n : Nat}
    (idxs : List Nat)
    (h : ∀ i ∈ idxs, i < n)
    {R S : FinRelation D n}
    (hRS : R ⊆ S) :
    FinRelation.proj idxs R h ⊆
      FinRelation.proj idxs S h := by
  intro t ht
  rw [FinRelation.mem_proj_iff] at ht ⊢
  rcases ht with ⟨u, hu, hEq⟩
  exact ⟨u, hRS hu, hEq⟩

/-
  Product is monotone in both arguments.
-/
private theorem prod_mono
    {n m : Nat}
    {R₁ R₂ : FinRelation D n}
    {S₁ S₂ : FinRelation D m}
    (hR : R₁ ⊆ R₂)
    (hS : S₁ ⊆ S₂) :
    FinRelation.prod R₁ S₁ ⊆
      FinRelation.prod R₂ S₂ := by
  intro t ht
  rw [FinRelation.mem_prod_iff] at ht ⊢
  rcases ht with ⟨t₁, ht₁, t₂, ht₂, hEq⟩
  exact ⟨t₁, hR ht₁, t₂, hS ht₂, hEq⟩

end FinRelation

namespace RawRAExpr

variable {A D : Type} {_ : RelationNames A} [Domain D]

/-
  SPJU raw expressions are monotone under pointwise
  instance inclusion.
-/
private theorem eval?_monotone_of_spju
    {Γ : UnnamedSchema A}
    (e : RawRAExpr A D)
    (I J : Instance D Γ)
    (hSub : Instance.Subset I J) :
    ∀ {n}, IsSPJU e →
      e.arity? Γ = some n →
      ∃ RI RJ : FinRelation D n,
        e.eval? (Γ := Γ) I = some ⟨n, RI⟩ ∧
        e.eval? (Γ := Γ) J = some ⟨n, RJ⟩ ∧
        RI ⊆ RJ := by
  intro n hSPJU hAr
  induction e generalizing n with
  | top =>
      have hn : n = 0 := by
        simpa [RawRAExpr.arity?] using hAr.symm
      subst hn
      refine ⟨FinRelation.top, FinRelation.top, ?_⟩
      refine ⟨?_, ?_, ?_⟩
      · simp [RawRAExpr.eval?]
      · simp [RawRAExpr.eval?]
      · intro t ht
        exact ht
  | empty m =>
      have hn : n = m := by
        simpa [RawRAExpr.arity?] using hAr.symm
      subst hn
      refine ⟨∅, ∅, ?_⟩
      refine ⟨?_, ?_, ?_⟩
      · simp [RawRAExpr.eval?]
      · simp [RawRAExpr.eval?]
      · intro t ht
        exact ht
  | single d =>
      have hn : n = 1 := by
        simpa [RawRAExpr.arity?] using hAr.symm
      subst hn
      refine ⟨FinRelation.single d,
        FinRelation.single d, ?_⟩
      refine ⟨?_, ?_, ?_⟩
      · simp [RawRAExpr.eval?]
      · simp [RawRAExpr.eval?]
      · intro t ht
        exact ht
  | rel X =>
      by_cases hX : X ∈ Γ.syms
      · have hn : Γ.arity ⟨X, hX⟩ = n := by
          have hAr' :
              some (Γ.arity ⟨X, hX⟩) = some n := by
            simpa
              [RawRAExpr.arity?,
                UnnamedSchema.arity?, hX]
              using hAr
          exact Option.some.inj hAr'
        subst hn
        refine ⟨I ⟨X, hX⟩, J ⟨X, hX⟩, ?_⟩
        refine ⟨?_, ?_, hSub ⟨X, hX⟩⟩
        · simp [RawRAExpr.eval?, Instance.relation?, hX]
        · simp [RawRAExpr.eval?, Instance.relation?, hX]
      · exfalso
        simp
          [RawRAExpr.arity?,
            UnnamedSchema.arity?, hX] at hAr
  | select φ e ih =>
      have hSPJUE : IsSPJU e := by
        simpa [IsSPJU] using hSPJU
      cases hE : e.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, hE] at hAr
      | some m =>
          by_cases hReq : φ.arityReq < m
          · have hm : m = n := by
              simpa [RawRAExpr.arity?, hE, hReq] using hAr
            rcases ih hSPJUE hE with
              ⟨RI, RJ, hEI, hEJ, hRIJ⟩
            subst hm
            refine ⟨FinRelation.select
                (fun t => Sel.Holds φ t) RI,
              FinRelation.select
                (fun t => Sel.Holds φ t) RJ, ?_⟩
            refine ⟨?_, ?_, ?_⟩
            · simp [RawRAExpr.eval?, hEI, hReq]
            · simp [RawRAExpr.eval?, hEJ, hReq]
            · exact FinRelation.select_mono
                (p := fun t => Sel.Holds φ t) hRIJ
          · simp [RawRAExpr.arity?, hE, hReq] at hAr
  | proj idxs e ih =>
      have hSPJUE : IsSPJU e := by
        simpa [IsSPJU] using hSPJU
      cases hE : e.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, hE] at hAr
      | some m =>
          by_cases hOk : ∀ i ∈ idxs, i < m
          · have hm : idxs.length = n := by
              have hPair :
                  (∀ i ∈ idxs, i < m)
                    ∧ idxs.length = n := by
                simpa [RawRAExpr.arity?, hE, hOk] using hAr
              exact hPair.2
            rcases ih hSPJUE hE with
              ⟨RI, RJ, hEI, hEJ, hRIJ⟩
            subst hm
            refine ⟨FinRelation.proj (n := m) idxs RI hOk,
              FinRelation.proj (n := m) idxs RJ hOk, ?_⟩
            refine ⟨?_, ?_, ?_⟩
            · simpa [RawRAExpr.eval?, hEI] using hOk
            · simpa [RawRAExpr.eval?, hEJ] using hOk
            · exact FinRelation.proj_mono
                (idxs := idxs) (h := hOk) hRIJ
          · simp [RawRAExpr.arity?, hE, hOk] at hAr
  | prod e₁ e₂ ih₁ ih₂ =>
      have hPair : IsSPJU e₁ ∧ IsSPJU e₂ := by
        simpa [IsSPJU] using hSPJU
      cases h₁ : e₁.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, h₁] at hAr
      | some n₁ =>
          cases h₂ : e₂.arity? Γ with
          | none =>
              simp [RawRAExpr.arity?, h₁, h₂] at hAr
          | some n₂ =>
              have hsum : n₁ + n₂ = n := by
                simpa [RawRAExpr.arity?, h₁, h₂]
                  using hAr
              rcases ih₁ hPair.1 h₁ with
                ⟨RI₁, RJ₁, hEI₁, hEJ₁,
                  hSub₁⟩
              rcases ih₂ hPair.2 h₂ with
                ⟨RI₂, RJ₂, hEI₂, hEJ₂,
                  hSub₂⟩
              subst hsum
              refine ⟨FinRelation.prod RI₁ RI₂,
                FinRelation.prod RJ₁ RJ₂, ?_⟩
              refine ⟨?_, ?_, ?_⟩
              · simp [RawRAExpr.eval?, hEI₁, hEI₂]
              · simp [RawRAExpr.eval?, hEJ₁, hEJ₂]
              · exact FinRelation.prod_mono hSub₁ hSub₂
  | union e₁ e₂ ih₁ ih₂ =>
      have hPair : IsSPJU e₁ ∧ IsSPJU e₂ := by
        simpa [IsSPJU] using hSPJU
      cases h₁ : e₁.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, h₁] at hAr
      | some n₁ =>
          cases h₂ : e₂.arity? Γ with
          | none =>
              simp [RawRAExpr.arity?, h₁, h₂] at hAr
          | some n₂ =>
              by_cases hEq : n₁ = n₂
              · have hn : n₁ = n := by
                  simpa [RawRAExpr.arity?, h₁, h₂, hEq]
                    using hAr
                rcases ih₁ hPair.1 h₁ with
                  ⟨RI₁, RJ₁, hEI₁, hEJ₁,
                    hSub₁⟩
                rcases ih₂ hPair.2 h₂ with
                  ⟨RI₂, RJ₂, hEI₂, hEJ₂,
                    hSub₂⟩
                subst hEq
                subst hn
                refine ⟨FinRelation.union RI₁ RI₂,
                  FinRelation.union RJ₁ RJ₂, ?_⟩
                refine ⟨?_, ?_, ?_⟩
                · simp [RawRAExpr.eval?, hEI₁, hEI₂]
                · simp [RawRAExpr.eval?, hEJ₁, hEJ₂]
                · intro t ht
                  have hMem :=
                    FinRelation.mem_union_iff.mp ht
                  rcases hMem with
                    ht₁ | ht₂
                  · exact FinRelation.mem_union_iff.mpr
                      (Or.inl (hSub₁ ht₁))
                  · exact FinRelation.mem_union_iff.mpr
                      (Or.inr (hSub₂ ht₂))
              · simp [RawRAExpr.arity?, h₁, h₂, hEq]
                  at hAr
  | diff e₁ e₂ ih₁ ih₂ =>
      have : False := by
        simp [IsSPJU] at hSPJU
      exact False.elim this

end RawRAExpr

namespace SPJUExpr

variable {A D : Type} [Domain D]
variable {_ : RelationNames A}
variable {Γ : UnnamedSchema A}

/-
  Typed `SPJU` expressions are monotone under pointwise
  instance inclusion.
-/
theorem eval_monotone
    {n : Nat}
    (e : SPJUExpr D Γ n)
    {I J : Instance D Γ}
    (hSub : Instance.Subset I J) :
    e.1.eval I ⊆ e.1.eval J := by
  rcases RawRAExpr.eval?_monotone_of_spju
      (Γ := Γ) (e := e.1.expr) I J hSub e.2 e.1.wf with
    ⟨RI, RJ, hEI, hEJ, hRIJ⟩
  have hSpecI := RAExpr.raw_eval?_eq_eval (e := e.1) I
  have hSpecJ := RAExpr.raw_eval?_eq_eval (e := e.1) J
  have hEqI : RI = e.1.eval I := by
    have hOpt :
        some (⟨n, RI⟩ : Sigma (FinRelation D)) =
          some ⟨n, e.1.eval I⟩ := by
      calc
        some (⟨n, RI⟩ : Sigma (FinRelation D))
            = e.1.expr.eval? (Γ := Γ) I := by
              simpa using hEI.symm
        _ = some ⟨n, e.1.eval I⟩ := hSpecI
    injection hOpt with hSig
    injection hSig
  have hEqJ : RJ = e.1.eval J := by
    have hOpt :
        some (⟨n, RJ⟩ : Sigma (FinRelation D)) =
          some ⟨n, e.1.eval J⟩ := by
      calc
        some (⟨n, RJ⟩ : Sigma (FinRelation D))
            = e.1.expr.eval? (Γ := Γ) J := by
              simpa using hEJ.symm
        _ = some ⟨n, e.1.eval J⟩ := hSpecJ
    injection hOpt with hSig
    injection hSig
  subst hEqI
  subst hEqJ
  exact hRIJ

end SPJUExpr
