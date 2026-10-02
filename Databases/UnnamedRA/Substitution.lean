-- Author: Jesse Comer
import Databases.UnnamedRA.Semantics

/-
  Substitution for unnamed relational algebra expressions.

  The raw operation replaces relation symbols by raw RA
  expressions, but does not necessarily produce a well-
  formed expression. The operation `RAExpr.subst` only
  accepts well-formed inputs over the same schema, and
  is guaranteed to produce a well-formed expression.
  The `RAExpr.substitution_property` theorem says
  same-schema substitution corresponds to updating the
  substituted relation by the replacement's denotation.

  Key definitions:
    * `RawRAExpr.subst`
    * `RAExpr.subst`

  Key theorems:
    * `RAExpr.substitution_property`
    * `RAExpr.subst_eval`
-/

------------------------------------------------------------
-- Raw Substitution
------------------------------------------------------------

namespace RawRAExpr

variable {A D : Type} [RelationNames A] [Domain D]

/- Substitution on `RawRAExpr`s. -/
def subst
    (e : RawRAExpr A D)
    (x : A)
    (e' : RawRAExpr A D) :
    RawRAExpr A D :=
  match e with
  | .top => .top
  | .empty n => .empty n
  | .rel y => if y = x then e' else .rel y
  | .single d => .single d
  | .select φ e₁ => .select φ (e₁.subst x e')
  | .proj idxs e₁ => .proj idxs (e₁.subst x e')
  | .prod e₁ eRep =>
      .prod (e₁.subst x e') (eRep.subst x e')
  | .union e₁ eRep =>
      .union (e₁.subst x e') (eRep.subst x e')
  | .diff e₁ eRep =>
      .diff (e₁.subst x e') (eRep.subst x e')

/- If `x` does not occur, substitution is identity. -/
theorem subst_vacuous
    (x : A)
    (e' : RawRAExpr A D) :
    ∀ e : RawRAExpr A D,
      x ∉ e.symbols → e.subst x e' = e
  | .top, _ => by
      simp [subst]
  | .empty n, _ => by
      simp [subst]
  | .rel y, h => by
      by_cases hy : y = x
      · subst hy
        cases h (by simp [symbols])
      · simp [subst, hy]
  | .single d, _ => by
      simp [subst]
  | .select φ e₁, h => by
      have he₁ : x ∉ e₁.symbols := by
        simpa [symbols] using h
      simp [subst, subst_vacuous x e' e₁ he₁]
  | .proj idxs e₁, h => by
      have he₁ : x ∉ e₁.symbols := by
        simpa [symbols] using h
      simp [subst, subst_vacuous x e' e₁ he₁]
  | .prod e₁ eRep, h => by
      have he₁eRep :
          x ∉ e₁.symbols ∧ x ∉ eRep.symbols := by
        simpa [symbols] using h
      simp [subst, subst_vacuous x e' e₁ he₁eRep.1,
        subst_vacuous x e' eRep he₁eRep.2]
  | .union e₁ eRep, h => by
      have he₁eRep :
          x ∉ e₁.symbols ∧ x ∉ eRep.symbols := by
        simpa [symbols] using h
      simp [subst, subst_vacuous x e' e₁ he₁eRep.1,
        subst_vacuous x e' eRep he₁eRep.2]
  | .diff e₁ eRep, h => by
      have he₁eRep :
          x ∉ e₁.symbols ∧ x ∉ eRep.symbols := by
        simpa [symbols] using h
      simp [subst, subst_vacuous x e' e₁ he₁eRep.1,
        subst_vacuous x e' eRep he₁eRep.2]

/-
  If the source expression and replacement expression are
  well-formed, and the replacement has the arity required
  by the replaced relation name, then substitution preserves
  well-formedness and output arity.
-/
theorem subst_preserves_arity
    {Γ : UnnamedSchema A}
    {x : A}
    {eRep e : RawRAExpr A D}
    {m n : Nat}
    (hSub : eRep.arity? Γ = some m)
    (hX : Γ.arity? x = some m)
    (hE : e.arity? Γ = some n) :
    (e.subst x eRep).arity? Γ = some n := by
  induction e generalizing n with
  | top =>
      simpa [subst, arity?] using hE
  | empty k =>
      simpa [subst, arity?] using hE
  | rel y =>
      by_cases hy : y = x
      · have hyn : Γ.arity? y = some n := by
          simpa [arity?] using hE
        have hym : Γ.arity? y = some m := by
          simpa [hy] using hX
        have hmn : some m = some n := by
          exact hym.symm.trans hyn
        have hm : m = n := by
          cases hmn
          rfl
        simpa [subst, arity?, hy, hm] using hSub
      · simpa [subst, arity?, hy] using hE
  | single d =>
      simpa [subst, arity?] using hE
  | select φ e₁ ih =>
      cases hR : e₁.arity? Γ with
      | none =>
          simp [arity?, hR] at hE
      | some k =>
          by_cases hReq : φ.arityReq < k
          · have hk : k = n := by
              simpa [arity?, hR, hReq] using hE
            have hSubR :
                (e₁.subst x eRep).arity? Γ = some k :=
              ih hR
            have hSelK :
                (RawRAExpr.select φ
                  (e₁.subst x eRep)).arity? Γ
                  = some k := by
              simp [arity?, hSubR, hReq]
            have hOut :
                RawRAExpr.arity? Γ
                  ((RawRAExpr.select φ e₁).subst x eRep)
                  = some k := by
              simpa [subst] using hSelK
            calc
              RawRAExpr.arity? Γ
                ((RawRAExpr.select φ e₁).subst x eRep)
                  = some k := hOut
              _ = some n := by
                simp [hk]
          · simp [arity?, hR, hReq] at hE
  | proj idxs e₁ ih =>
      cases hR : e₁.arity? Γ with
      | none =>
          simp [arity?, hR] at hE
      | some k =>
          by_cases hOk : ∀ i ∈ idxs, i < k
          · have hlen : idxs.length = n := by
              have hPair :
                  (∀ i ∈ idxs, i < k)
                    ∧ idxs.length = n := by
                simpa [arity?, hR, hOk] using hE
              exact hPair.2
            have hSubR :
                (e₁.subst x eRep).arity? Γ = some k :=
              ih hR
            have hDec :
                decide (∀ i ∈ idxs, i < k) = true := by
              exact decide_eq_true hOk
            simp [subst, arity?, hSubR, hDec, hlen]
          · simp [arity?, hR, hOk] at hE
  | prod e₁ e₂ ihe₁ ihe₂ =>
      cases hR : e₁.arity? Γ with
      | none =>
          simp [arity?, hR] at hE
      | some nR =>
          cases hS : e₂.arity? Γ with
          | none =>
              simp [arity?, hR, hS] at hE
          | some nS =>
              have hsum : nR + nS = n := by
                simpa [arity?, hR, hS] using hE
              have hSubR :
                  (e₁.subst x eRep).arity? Γ = some nR :=
                ihe₁ hR
              have hSubS :
                  (e₂.subst x eRep).arity? Γ = some nS :=
                ihe₂ hS
              simp [subst, arity?, hSubR, hSubS, hsum]
  | union e₁ e₂ ihe₁ ihe₂ =>
      cases hR : e₁.arity? Γ with
      | none =>
          simp [arity?, hR] at hE
      | some nR =>
          cases hS : e₂.arity? Γ with
          | none =>
              simp [arity?, hR, hS] at hE
          | some nS =>
              by_cases hEq : nR = nS
              · have hn : nR = n := by
                  simpa [arity?, hR, hS, hEq] using hE
                have hSubR :
                    (e₁.subst x eRep).arity? Γ =
                      some nR :=
                  ihe₁ hR
                have hSubS :
                    (e₂.subst x eRep).arity? Γ =
                      some nS :=
                  ihe₂ hS
                have hsn : nS = n := by
                  calc
                    nS = nR := hEq.symm
                    _ = n := hn
                simp [subst, arity?, hSubR, hSubS,
                  hEq, hsn]
              · simp [arity?, hR, hS, hEq] at hE
  | diff e₁ e₂ ihe₁ ihe₂ =>
      cases hR : e₁.arity? Γ with
      | none =>
          simp [arity?, hR] at hE
      | some nR =>
          cases hS : e₂.arity? Γ with
          | none =>
              simp [arity?, hR, hS] at hE
          | some nS =>
              by_cases hEq : nR = nS
              · have hn : nR = n := by
                  simpa [arity?, hR, hS, hEq] using hE
                have hSubR :
                    (e₁.subst x eRep).arity? Γ =
                      some nR :=
                  ihe₁ hR
                have hSubS :
                    (e₂.subst x eRep).arity? Γ =
                      some nS :=
                  ihe₂ hS
                have hsn : nS = n := by
                  calc
                    nS = nR := hEq.symm
                    _ = n := hn
                simp [subst, arity?, hSubR, hSubS,
                  hEq, hsn]
              · simp [arity?, hR, hS, hEq] at hE

end RawRAExpr

------------------------------------------------------------
-- Typed Substitution
------------------------------------------------------------

namespace RAExpr

variable {A D : Type} [Domain D]
variable {_ : RelationNames A}
variable {Γ : UnnamedSchema A}

/-
  Typed substitution at a relation name whose schema arity
  is supplied explicitly, together with a proof that the
  arity matches the symbol to be replaced.
-/
def substWithArityProof
    {n m : Nat}
    (e : RAExpr D Γ n)
    (x : A)
    (hX : Γ.arity? x = some m)
    (e' : RAExpr D Γ m) :
    RAExpr D Γ n :=
{
  expr := e.expr.subst x e'.expr
  wf := RawRAExpr.subst_preserves_arity
    e'.wf hX e.wf
}

/-
  Same-schema substitution at a schema symbol. This is the
  primary typed substitution operation.
-/
def subst
    {n : Nat}
    (e : RAExpr D Γ n)
    (X : Γ.syms)
    (eRep : RAExpr D Γ (Γ.arity X)) :
    RAExpr D Γ n :=
  e.substWithArityProof X.1
    (by
      simp [UnnamedSchema.arity?, X.2])
    eRep

/-
  Substitution has no effect if the replaced variable does
  not appear in the expression.
-/
theorem substWithArityProof_vacuous
    {n m : Nat}
    (x : A)
    (hX : Γ.arity? x = some m)
    (e' : RAExpr D Γ m)
    (e : RAExpr D Γ n)
    (h : x ∉ e.symbols) :
    e.substWithArityProof x hX e' = e := by
  cases e with
  | mk expr wf =>
      have hRaw : x ∉ expr.symbols := by
        simpa [symbols] using h
      have hSub :
          expr.subst x e'.expr = expr :=
        RawRAExpr.subst_vacuous x e'.expr expr hRaw
      simp [substWithArityProof, hSub]

/-
  Same-schema substitution is vacuous for absent symbols.
-/
theorem subst_vacuous
    {n : Nat}
    (X : Γ.syms)
    (eRep : RAExpr D Γ (Γ.arity X))
    (e : RAExpr D Γ n)
    (h : X.1 ∉ e.symbols) :
    e.subst X eRep = e := by
  simpa [subst] using
    RAExpr.substWithArityProof_vacuous X.1
      (by
        simp [UnnamedSchema.arity?, X.2])
      eRep e h

end RAExpr

------------------------------------------------------------
-- Substitution Property
------------------------------------------------------------

namespace RawRAExpr

variable {A D : Type}
variable {_ : RelationNames A} [Domain D]

/-
  Stability of `eval?` under `Instance.update` when the
  updated relation name does not occur in the expression.
-/
theorem eval?_update_no_occur
    {Γ : UnnamedSchema A}
    (I : Instance D Γ)
    (X : Γ.syms)
    (R : FinRelation D (Γ.arity X))
    {e : RawRAExpr A D}
    (hNotMem : X.1 ∉ e.symbols) :
    e.eval? (Γ := Γ) (Instance.update I X R) =
      e.eval? (Γ := Γ) I := by
  induction e generalizing I with
  | top =>
      simp [RawRAExpr.eval?]
  | empty n =>
      simp [RawRAExpr.eval?]
  | single d =>
      simp [RawRAExpr.eval?]
  | rel Y =>
      by_cases hY : Y = X.1
      · subst hY
        exact (hNotMem (by simp [RawRAExpr.symbols])).elim
      · by_cases hMem : Y ∈ Γ.syms
        · have hNe :
            (⟨Y, hMem⟩ : Γ.syms) ≠ X := by
            intro hEq
            exact hY (congrArg Subtype.val hEq)
          simp [RawRAExpr.eval?, Instance.relation?,
            hMem, Instance.update, hNe]
        · simp [RawRAExpr.eval?, Instance.relation?, hMem]
  | select φ e ih =>
      have hSub : X.1 ∉ e.symbols := by
        simpa [RawRAExpr.symbols] using hNotMem
      simp [RawRAExpr.eval?, ih I hSub]
  | proj idxs e ih =>
      have hSub : X.1 ∉ e.symbols := by
        simpa [RawRAExpr.symbols] using hNotMem
      simp [RawRAExpr.eval?, ih I hSub]
  | prod e₁ eRep ih₁ ih₂ =>
      have hPair :
          X.1 ∉ e₁.symbols ∧
            X.1 ∉ eRep.symbols := by
        simpa [RawRAExpr.symbols] using hNotMem
      simp [RawRAExpr.eval?,
        ih₁ I hPair.1, ih₂ I hPair.2]
  | union e₁ eRep ih₁ ih₂ =>
      have hPair :
          X.1 ∉ e₁.symbols ∧
            X.1 ∉ eRep.symbols := by
        simpa [RawRAExpr.symbols] using hNotMem
      simp [RawRAExpr.eval?,
        ih₁ I hPair.1, ih₂ I hPair.2]
  | diff e₁ eRep ih₁ ih₂ =>
      have hPair :
          X.1 ∉ e₁.symbols ∧
            X.1 ∉ eRep.symbols := by
        simpa [RawRAExpr.symbols] using hNotMem
      simp [RawRAExpr.eval?,
        ih₁ I hPair.1, ih₂ I hPair.2]

/-
  Helper theorem for semantic substitution
  under one update.
-/
theorem eval?_subst_aux
    {Γ : UnnamedSchema A}
    (I : Instance D Γ)
    (X : {sym : A // sym ∈ Γ.syms})
    (eRep : RawRAExpr A D)
    {R : FinRelation D (Γ.arity X)}
    (hEvalSub :
      eRep.eval? (Γ := Γ) I =
        some ⟨Γ.arity X, R⟩) :
    ∀ e : RawRAExpr A D,
      e.eval? (Γ := Γ) (Instance.update I X R) =
        (e.subst X.1 eRep).eval? (Γ := Γ) I := by
  intro e
  induction e with
  | top =>
      simp [RawRAExpr.eval?, RawRAExpr.subst]
  | empty n =>
      simp [RawRAExpr.eval?, RawRAExpr.subst]
  | single d =>
      simp [RawRAExpr.eval?, RawRAExpr.subst]
  | rel Y =>
      by_cases hY : Y = X.1
      · subst hY
        have hMem : X.1 ∈ Γ.syms := X.2
        have hEqSub :
            (⟨X.1, hMem⟩ : Γ.syms) = X := by
          apply Subtype.ext
          rfl
        have hEvalRel :
            (.rel X.1 : RawRAExpr A D).eval?
              (Γ := Γ) (Instance.update I X R) =
            some ⟨Γ.arity X, R⟩ := by
          simp [RawRAExpr.eval?, Instance.relation?,
            hMem, Instance.update, hEqSub]
        calc
          (.rel X.1 : RawRAExpr A D).eval?
              (Γ := Γ) (Instance.update I X R)
              = some ⟨Γ.arity X, R⟩ := hEvalRel
          _ = eRep.eval? (Γ := Γ) I := hEvalSub.symm
          _ = ((.rel X.1 : RawRAExpr A D).subst
                X.1 eRep).eval? (Γ := Γ) I := by
                simp [RawRAExpr.subst]
      · by_cases hMem : Y ∈ Γ.syms
        · have hNe :
            (⟨Y, hMem⟩ : Γ.syms) ≠ X := by
            intro hEq
            exact hY (congrArg Subtype.val hEq)
          simp [RawRAExpr.eval?, Instance.relation?,
            RawRAExpr.subst,
            hY, hMem, Instance.update, hNe]
        · simp [RawRAExpr.eval?, Instance.relation?,
            RawRAExpr.subst, hY, hMem]
  | select φ e ih =>
      simp [RawRAExpr.eval?, RawRAExpr.subst, ih]
  | proj idxs e ih =>
      simp [RawRAExpr.eval?, RawRAExpr.subst, ih]
  | prod e₁ eRep ih₁ ih₂ =>
      simp [RawRAExpr.eval?, RawRAExpr.subst, ih₁, ih₂]
  | union e₁ eRep ih₁ ih₂ =>
      simp [RawRAExpr.eval?, RawRAExpr.subst, ih₁, ih₂]
  | diff e₁ eRep ih₁ ih₂ =>
      simp [RawRAExpr.eval?, RawRAExpr.subst, ih₁, ih₂]

end RawRAExpr

namespace RAExpr

variable {A D : Type}
variable {_ : RelationNames A} [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Lower-level same-schema substitution property, phrased
  using the explicit-arity-proof constructor.
-/
theorem eval_substWithArityProof
    {n : Nat}
    (e : RAExpr D Γ n)
    (I : Instance D Γ)
    (X : Γ.syms)
    (eRep : RAExpr D Γ (Γ.arity X)) :
    e.eval (Instance.update I X (eRep.eval I)) =
      (e.substWithArityProof X.1
        (by
          simp [UnnamedSchema.arity?, X.2])
        eRep).eval I := by
  have hSubEval :
      eRep.expr.eval? (Γ := Γ) I =
        some ⟨Γ.arity X, eRep.eval I⟩ :=
    RAExpr.raw_eval?_eq_eval eRep I
  have hRaw :
      e.expr.eval? (Γ := Γ)
        (Instance.update I X (eRep.eval I)) =
      (e.expr.subst X.1 eRep.expr).eval? (Γ := Γ) I :=
    RawRAExpr.eval?_subst_aux I X eRep.expr hSubEval e.expr
  have hX : Γ.arity? X.1 = some (Γ.arity X) := by
    simp [UnnamedSchema.arity?, X.2]
  have hOpt :
      some
          (⟨n, e.eval
            (Instance.update I X (eRep.eval I))⟩ :
              Sigma (FinRelation D))
      = some ⟨n,
          (e.substWithArityProof X.1 hX eRep).eval
            I⟩ := by
    calc
      some
          (⟨n, e.eval
            (Instance.update I X (eRep.eval I))⟩ :
              Sigma (FinRelation D))
          = e.expr.eval? (Γ := Γ)
              (Instance.update I X (eRep.eval I)) := by
            simpa using (RAExpr.raw_eval?_eq_eval e
              (Instance.update I X (eRep.eval I))).symm
      _ = (e.expr.subst X.1 eRep.expr).eval?
            (Γ := Γ) I := hRaw
      _ = ((e.substWithArityProof X.1 hX eRep).expr).eval?
            (Γ := Γ) I := by
            simp [RAExpr.substWithArityProof]
      _ = some ⟨n,
          (e.substWithArityProof X.1 hX eRep).eval
            I⟩ := by
            simpa using
              RAExpr.raw_eval?_eq_eval
                (e.substWithArityProof X.1 hX eRep) I
  have hEvalEq :
      e.eval (Instance.update I X (eRep.eval I)) =
        (e.substWithArityProof X.1 hX eRep).eval I := by
    injection hOpt with hEq
    injection hEq
  exact hEvalEq

/-
  Same-schema substitution as instance update: evaluating
  `e.subst X eRep` in `I` is the same as evaluating `e`
  after updating `X` to the value of `eRep` in `I`.
-/
theorem substitution_property
    {n : Nat}
    (e : RAExpr D Γ n)
    (I : Instance D Γ)
    (X : Γ.syms)
    (eRep : RAExpr D Γ (Γ.arity X)) :
    e.eval (Instance.update I X (eRep.eval I)) =
      (e.subst X eRep).eval I := by
  simpa [subst] using e.eval_substWithArityProof I X eRep

/- Same-schema substitution, stated with base evaluation. -/
theorem subst_eval
    {n : Nat}
    (e : RAExpr D Γ n)
    (I : Instance D Γ)
    (X : Γ.syms)
    (eRep : RAExpr D Γ (Γ.arity X)) :
    (e.subst X eRep).eval I =
      e.eval
        (Instance.update I X (eRep.eval I)) := by
  exact (RAExpr.substitution_property e I X eRep).symm

end RAExpr
