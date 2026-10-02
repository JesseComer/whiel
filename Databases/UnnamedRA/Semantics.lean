-- Author: Jesse Comer
import Databases.Core.Containment
import Databases.UnnamedRA.Syntax
import Databases.UnnamedModel.Instance
import Mathlib.Data.List.Perm.Basic

/-
  This file specifies Prop-valued semantics for unnamed
  relational algebra over finite unnamed instances.

  Key definitions include:
    * `Sel.Holds`
    * `RawRAExpr.eval?`
    * `RawRAExpr.answerContains`
    * `RAExpr.eval`

  Key theorems include:
    * `RawRAExpr.wf_total`
    * `RAExpr.raw_eval?_eq_eval`
    * `RawRAExpr.eval?_expansion_invariance`
    * `RawRAExpr.eval?_reduct_property`
    * `RAExpr.expansion_invariance`
    * `RAExpr.reduct_property`

  Constructor-specific answer-membership theorems
  characterize membership in raw expression denotations.

  Intervening definitions and lemmas are
  construction, helper, or proof support.
-/

------------------------------------------------------------
-- Selection Semantics
------------------------------------------------------------

namespace Sel

variable {D : Type} [Domain D]

/-
  Semantics for selection conditions.
-/
def Holds {n : Nat} : Sel D → Tuple D n → Prop
| .eqIdx i j, t =>
    match t.toList[i]?, t.toList[j]? with
    | some di, some dj => di = dj
    | _, _ => False
| .eqConst i c, t =>
    match t.toList[i]? with
    | some di => di = c
    | none => False
| .and φ₁ φ₂, t => Holds φ₁ t ∧ Holds φ₂ t
| .or φ₁ φ₂, t => Holds φ₁ t ∨ Holds φ₂ t
| .not φ, t => ¬ Holds φ t

private def decidableHolds
    {n : Nat}
    (t : Tuple D n) :
    (φ : Sel D) → Decidable (Holds φ t)
| .eqIdx i j => by
    unfold Holds
    cases t.toList[i]? <;>
      cases t.toList[j]? <;>
        infer_instance
| .eqConst i c => by
    unfold Holds
    cases t.toList[i]? <;>
      infer_instance
| .and φ₁ φ₂ => by
    letI : Decidable (Holds φ₁ t) :=
      decidableHolds t φ₁
    letI : Decidable (Holds φ₂ t) :=
      decidableHolds t φ₂
    unfold Holds
    infer_instance
| .or φ₁ φ₂ => by
    letI : Decidable (Holds φ₁ t) :=
      decidableHolds t φ₁
    letI : Decidable (Holds φ₂ t) :=
      decidableHolds t φ₂
    unfold Holds
    infer_instance
| .not φ => by
    letI : Decidable (Holds φ t) :=
      decidableHolds t φ
    unfold Holds
    infer_instance

instance
    {n : Nat}
    (t : Tuple D n)
    (φ : Sel D) :
    Decidable (Holds φ t) :=
  decidableHolds t φ

instance
    {n : Nat}
    (φ : Sel D) :
    DecidablePred
      (fun t : Tuple D n => Holds φ t) :=
  fun _ => by infer_instance

theorem holds_eqIdx_iff
    {n : Nat}
    (t : Tuple D n)
    {i j : Nat}
    (hi : i < n)
    (hj : j < n) :
    Holds (.eqIdx i j) t ↔ t[i] = t[j] := by
  unfold Holds
  simp [hi, hj]

theorem holds_eqConst_iff
    {n : Nat}
    (t : Tuple D n)
    {i : Nat}
    {c : D}
    (hi : i < n) :
    Holds (.eqConst i c) t ↔ t[i] = c := by
  unfold Holds
  simp [hi]

end Sel

------------------------------------------------------------
-- FinRelation Operations
------------------------------------------------------------

namespace FinRelation

variable {D : Type} [Domain D]

/-
  Constructive duplicate removal for list-backed finsets.
-/
private def dedupList
    {α : Type}
    [DecidableEq α] :
    List α → List α
| [] => []
| x :: xs =>
    if x ∈ xs then
      dedupList xs
    else
      x :: dedupList xs

/- Membership in constructive duplicate removal. -/
private theorem mem_dedupList_iff
    {α : Type}
    [DecidableEq α]
    (x : α) :
    ∀ xs : List α, x ∈ dedupList xs ↔ x ∈ xs
| [] => by
    simp [dedupList]
| y :: ys => by
    by_cases hy : y ∈ ys
    · by_cases hxy : x = y
      · subst hxy
        simp [dedupList, hy, mem_dedupList_iff]
      · simp [dedupList, hy, hxy, mem_dedupList_iff]
    · by_cases hxy : x = y
      · subst hxy
        simp [dedupList, hy]
      · simp [dedupList, hy, hxy, mem_dedupList_iff]

/- Constructive duplicate removal is duplicate-free. -/
private theorem nodup_dedupList
    {α : Type}
    [DecidableEq α] :
    ∀ xs : List α, (dedupList xs).Nodup
| [] => by
    simp [dedupList]
| x :: xs => by
    by_cases hx : x ∈ xs
    · simp [dedupList, hx, nodup_dedupList xs]
    · simp [dedupList, hx, nodup_dedupList xs,
        mem_dedupList_iff]

/- A finite set produced from a list without choice. -/
private def listFinset
    {α : Type}
    [DecidableEq α]
    (xs : List α) :
    Finset α :=
  ⟨dedupList xs, nodup_dedupList xs⟩

/- Membership in the constructive list-backed finite set. -/
private theorem mem_listFinset_iff
    {α : Type}
    [DecidableEq α]
    (x : α)
    (xs : List α) :
    x ∈ listFinset xs ↔ x ∈ xs :=
  mem_dedupList_iff x xs

/-
  Permuting the source list does not change its finite
  set.
-/
private theorem listFinset_eq_of_perm
    {α : Type}
    [DecidableEq α]
    {xs ys : List α}
    (h : xs.Perm ys) :
    listFinset xs = listFinset ys := by
  apply Finset.ext
  intro x
  rw [mem_listFinset_iff, mem_listFinset_iff]
  exact h.mem_iff

/- FinRelation with one empty tuple (arity `0`). -/
def top : FinRelation D 0 :=
  {Tuple.empty}

/- Unary singleton relation. -/
def single (d : D) : FinRelation D 1 :=
  {Vector.ofFn (fun _ : Fin 1 => d)}

/- Selection by a decidable predicate on tuples. -/
def select {n : Nat}
    (p : Tuple D n → Prop)
    [DecidablePred p]
    (R : FinRelation D n) :
    FinRelation D n :=
  R.filter p

/- Membership in a selection. -/
omit [Domain D] in
theorem mem_select_iff {n : Nat}
    {p : Tuple D n → Prop}
    [DecidablePred p]
    {R : FinRelation D n}
    {t : Tuple D n} :
    t ∈ select p R ↔ t ∈ R ∧ p t := by
  simp [select]

/- List-level relational product. -/
private def prodList {n m : Nat}
    (xs : List (Tuple D n))
    (ys : List (Tuple D m)) :
    List (Tuple D (n + m)) :=
  (xs.product ys).map
    (fun p => appendTuple p.1 p.2)

/- Product respects permutation of either input list. -/
omit [Domain D] in
private theorem prodList_perm {n m : Nat}
    {xs₁ xs₂ : List (Tuple D n)}
    {ys₁ ys₂ : List (Tuple D m)}
    (hxs : xs₁.Perm xs₂)
    (hys : ys₁.Perm ys₂) :
    (prodList xs₁ ys₁).Perm
      (prodList xs₂ ys₂) := by
  exact List.Perm.map _ (List.Perm.product hxs hys)

/- Membership in the list-level relational product. -/
omit [Domain D] in
private theorem mem_prodList_iff {n m : Nat}
    {xs : List (Tuple D n)}
    {ys : List (Tuple D m)}
    {t : Tuple D (n + m)} :
    t ∈ prodList xs ys ↔
      ∃ t₁ ∈ xs, ∃ t₂ ∈ ys,
        appendTuple t₁ t₂ = t := by
  constructor
  · intro ht
    rw [prodList] at ht
    rcases List.mem_map.mp ht with ⟨p, hp, hEq⟩
    rcases List.mem_product.mp hp with ⟨hp₁, hp₂⟩
    exact ⟨p.1, hp₁, p.2, hp₂, hEq⟩
  · rintro ⟨t₁, ht₁, t₂, ht₂, hEq⟩
    rw [prodList]
    exact List.mem_map.mpr
      ⟨(t₁, t₂),
        List.mem_product.mpr ⟨ht₁, ht₂⟩, hEq⟩

/- Relational product. -/
def prod {n m : Nat}
    (R : FinRelation D n)
    (S : FinRelation D m) :
    FinRelation D (n + m) :=
  Quotient.liftOn₂ R.1 S.1
    (fun xs ys => listFinset (prodList xs ys))
    (fun _ _ _ _ hxs hys =>
      listFinset_eq_of_perm (prodList_perm hxs hys))

/- Project one tuple along a list of indices. -/
def projTuple {n : Nat}
    (idxs : List Nat)
    (t : Tuple D n)
    (h : ∀ i ∈ idxs, i < n) :
    Tuple D idxs.length :=
  Vector.ofFn (fun j =>
    let i := idxs.get ⟨j.1, j.2⟩
    let hi : i < n := h i (List.get_mem idxs ⟨j.1, j.2⟩)
    t.get ⟨i, hi⟩)

/-
  The `j`th coordinate of a projected tuple is the
  coordinate of the source tuple named by `idxs[j]`.
-/
omit [Domain D] in
theorem projTuple_get
    {n : Nat}
    (idxs : List Nat)
    (t : Tuple D n)
    (h : ∀ i ∈ idxs, i < n)
    (j : Fin idxs.length) :
    (projTuple idxs t h).get j =
      t.get
        ⟨idxs.get j,
          h (idxs.get j) (List.get_mem idxs j)⟩ := by
  simp [projTuple, Vector.get, Vector.ofFn]

/- Project a relation along a list of indices. -/
def proj {n : Nat}
    (idxs : List Nat)
    (R : FinRelation D n)
    (h : ∀ i ∈ idxs, i < n) :
    FinRelation D idxs.length :=
  Quotient.liftOn R.1
    (fun xs =>
      listFinset
        (xs.map (fun t => projTuple idxs t h)))
    (fun _ _ hxy =>
      listFinset_eq_of_perm (List.Perm.map _ hxy))

/- Relational union. -/
def union {n : Nat}
    (R S : FinRelation D n) :
    FinRelation D n :=
  Quotient.liftOn₂ R.1 S.1
    (fun xs ys => listFinset (xs ++ ys))
    (fun _ _ _ _ hxs hys =>
      listFinset_eq_of_perm
        (List.Perm.append hxs hys))

/- Relational difference. -/
def diff {n : Nat}
    (R S : FinRelation D n) :
    FinRelation D n :=
  R.filter (fun t => t ∉ S)

/-
  Membership in a projection is witnessed by a tuple in
  the source relation whose projected coordinates are the
  target tuple.
-/
theorem mem_proj_iff
    {n : Nat}
    {idxs : List Nat}
    {R : FinRelation D n}
    {h : ∀ i ∈ idxs, i < n}
    {t : Tuple D idxs.length} :
    t ∈ proj idxs R h ↔
      ∃ s ∈ R, projTuple idxs s h = t := by
  cases R with
  | mk rs hrs =>
      change t ∈ proj idxs ⟨rs, hrs⟩ h ↔
        ∃ s, s ∈ rs ∧ projTuple idxs s h = t
      revert hrs
      refine Quotient.inductionOn rs ?_
      intro xs _hrs
      simp [proj, mem_listFinset_iff]

theorem mem_prod_iff
    {n m : Nat}
    {R : FinRelation D n}
    {S : FinRelation D m}
    {t : Tuple D (n + m)} :
    t ∈ prod R S ↔
      ∃ t₁ ∈ R, ∃ t₂ ∈ S,
        appendTuple t₁ t₂ = t := by
  cases R with
  | mk rs hrs =>
      cases S with
      | mk ss hss =>
          change t ∈ prod ⟨rs, hrs⟩ ⟨ss, hss⟩ ↔
            ∃ t₁, t₁ ∈ rs ∧
              ∃ t₂, t₂ ∈ ss ∧
                appendTuple t₁ t₂ = t
          revert hrs hss
          refine Quotient.inductionOn₂ rs ss ?_
          intro xs ys _hrs _hss
          change t ∈ listFinset (prodList xs ys) ↔
            ∃ t₁, t₁ ∈ xs ∧
              ∃ t₂, t₂ ∈ ys ∧
                appendTuple t₁ t₂ = t
          rw [mem_listFinset_iff, mem_prodList_iff]

/- Membership in a relational union. -/
theorem mem_union_iff
    {n : Nat}
    {R S : FinRelation D n}
    {t : Tuple D n} :
    t ∈ union R S ↔ t ∈ R ∨ t ∈ S := by
  cases R with
  | mk rs hrs =>
      cases S with
      | mk ss hss =>
          change t ∈ union ⟨rs, hrs⟩ ⟨ss, hss⟩ ↔
            t ∈ rs ∨ t ∈ ss
          revert hrs hss
          refine Quotient.inductionOn₂ rs ss ?_
          intro xs ys _hrs _hss
          simp [union, mem_listFinset_iff]

/- Membership in a relational difference. -/
theorem mem_diff_iff
    {n : Nat}
    {R S : FinRelation D n}
    {t : Tuple D n} :
    t ∈ diff R S ↔ t ∈ R ∧ t ∉ S := by
  simp [diff]

omit [Domain D] in
theorem single_isTupleOver
    {d : D}
    {t : Tuple D 1}
    (ht : t ∈ single d) :
    t.isTupleOver ({d} : Finset D) := by
  have hEq :
      t = Vector.ofFn
        (fun _ : Fin 1 => d) := by
    simpa [single] using ht
  subst hEq
  intro i
  have hi : i = 0 := Fin.eq_zero i
  subst hi
  simp [Vector.get, Vector.ofFn]

omit [Domain D] in
theorem projTuple_isTupleOver
    {n : Nat}
    {idxs : List Nat}
    {t : Tuple D n}
    {Q : Finset D}
    {h : ∀ i ∈ idxs, i < n}
    (ht : t.isTupleOver Q) :
    (projTuple idxs t h).isTupleOver Q := by
  cases t with
  | mk arr hSize =>
      intro j
      let i := idxs.get j
      have hi : i < n := h i (List.get_mem idxs j)
      have hCoord : arr[i] ∈ Q := by
        simpa [Tuple.isTupleOver] using
          ht ⟨i, hi⟩
      simpa [projTuple, Vector.get,
        Vector.ofFn, i, hi] using hCoord

theorem appendTuple_isTupleOver_union
    {n m : Nat}
    {t₁ : Tuple D n}
    {t₂ : Tuple D m}
    {Q₁ Q₂ : Finset D}
    (h₁ : t₁.isTupleOver Q₁)
    (h₂ : t₂.isTupleOver Q₂) :
    (appendTuple t₁ t₂).isTupleOver
      (Q₁ ∪ Q₂) := by
  cases t₁ with
  | mk arr₁ h₁size =>
      cases t₂ with
      | mk arr₂ h₂size =>
          intro i
          have hi :
              i.1 < (arr₁ ++ arr₂).size := by
            rw [Array.size_append, h₁size, h₂size]
            exact i.2
          change
            (arr₁ ++ arr₂)[i.1]'hi ∈
              Q₁ ∪ Q₂
          by_cases hlt : i.1 < n
          · have hLeft :
                arr₁[i.1] ∈ Q₁ := by
              simpa [Tuple.isTupleOver] using
                h₁ ⟨i.1, hlt⟩
            have hApp :
                (arr₁ ++ arr₂)[i.1]'hi =
                  arr₁[i.1] := by
              exact Array.getElem_append_left
                (h := hi)
                (by simpa [h₁size] using hlt)
            exact Finset.mem_union.mpr
              (Or.inl (by simpa [hApp] using hLeft))
          · have hge : n ≤ i.1 :=
              Nat.le_of_not_gt hlt
            let j : Fin m := ⟨i.1 - n, by
              have hSum : i.1 < n + m := i.2
              omega⟩
            have hRight :
                arr₂[j.1] ∈ Q₂ := by
              simpa [Tuple.isTupleOver, j] using
                h₂ j
            have hApp :
                (arr₁ ++ arr₂)[i.1]'hi =
                  arr₂[j.1] := by
              have hGet :=
                Array.getElem_append_right
                  (h := hi)
                  (by simpa [h₁size] using hge)
              simpa [j, h₁size] using hGet
            exact Finset.mem_union.mpr
              (Or.inr (by simpa [hApp] using hRight))

end FinRelation

------------------------------------------------------------
-- Raw Evaluation
------------------------------------------------------------

namespace RawRAExpr

variable {A D : Type}
variable {_ : RelationNames A} [Domain D]

/-
  (Partial) evaluation semantics for raw RA expressions.
  The output type of this function is either (1) `none` (if
  the expression has an arity mismatch or uses a relation
  name not occurring in the schema) or (2) `some ⟨n, R⟩`
  where `n` is the arity of the output relation and `R` is
  a relation of arity `n`. The type of pairs of this form
  is represented as a dependent pair type.
-/
def eval?
    (e : RawRAExpr A D)
    {Γ : UnnamedSchema A}
    (I : Instance D Γ) :
    Option (Sigma (FinRelation D)) :=
  match e with
  | .top =>
    some ⟨0, FinRelation.top⟩
  | .empty n =>
    some ⟨n, ∅⟩
  | .rel X =>
    I.relation? X
  | .single d =>
    some ⟨1, FinRelation.single d⟩
  | .select φ e =>
    match e.eval? (Γ := Γ) I with
    | some ⟨n, R⟩ =>
        if hReq : φ.arityReq < n then
          some ⟨n,
            FinRelation.select
              (fun t => Sel.Holds φ t) R⟩
        else
          none
    | none => none
  | .proj idxs e =>
    match e.eval? (Γ := Γ) I with
    | some ⟨n, R⟩ =>
        if hOk : ∀ i ∈ idxs, i < n then
          some ⟨idxs.length,
            FinRelation.proj idxs R hOk⟩
        else
          none
    | none => none
  | .prod e₁ e₂ =>
    match
        e₁.eval? (Γ := Γ) I,
        e₂.eval? (Γ := Γ) I with
    | some ⟨n, R⟩, some ⟨m, S⟩ =>
        some ⟨n + m, FinRelation.prod R S⟩
    | _, _ => none
  | .union e₁ e₂ =>
    match
        e₁.eval? (Γ := Γ) I,
        e₂.eval? (Γ := Γ) I with
    | some ⟨n, R⟩, some ⟨m, S⟩ =>
        if hEq : n = m then
          by
            subst hEq
            exact some ⟨n, FinRelation.union R S⟩
        else
          none
    | _, _ => none
  | .diff e₁ e₂ =>
    match
        e₁.eval? (Γ := Γ) I,
        e₂.eval? (Γ := Γ) I with
    | some ⟨n, R⟩, some ⟨m, S⟩ =>
        if hEq : n = m then
          by
            subst hEq
            exact some ⟨n, FinRelation.diff R S⟩
        else
          none
    | _, _ => none

/- Evaluation is always defined for well-formed RA. -/
theorem wf_total
    {Γ : UnnamedSchema A}
    (I : Instance D Γ)
    {e : RawRAExpr A D}
    {n : Nat}
    (hAr : e.arity? Γ = some n) :
    ∃ R : FinRelation D n,
      e.eval? (Γ := Γ) I = some ⟨n, R⟩ := by
  induction e generalizing n with
  | top =>
      have hn : n = 0 := by
        simpa [RawRAExpr.arity?] using hAr.symm
      subst hn
      refine ⟨FinRelation.top, ?_⟩
      simp [RawRAExpr.eval?]
  | empty k =>
      have hn : n = k := by
        simpa [RawRAExpr.arity?] using hAr.symm
      subst hn
      refine ⟨∅, ?_⟩
      simp [RawRAExpr.eval?]
  | single d =>
      have hn : n = 1 := by
        simpa [RawRAExpr.arity?] using hAr.symm
      subst hn
      refine ⟨FinRelation.single d, ?_⟩
      simp [RawRAExpr.eval?]
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
        refine ⟨I ⟨X, hX⟩, ?_⟩
        simp [RawRAExpr.eval?, Instance.relation?, hX]
      · exfalso
        simp
          [RawRAExpr.arity?,
            UnnamedSchema.arity?, hX] at hAr
  | select φ e ih =>
      cases hE : e.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, hE] at hAr
      | some m =>
          by_cases hReq : φ.arityReq < m
          · have hm : m = n := by
              simpa [RawRAExpr.arity?, hE, hReq] using hAr
            have hTot := ih hE
            rcases hTot with ⟨R, hEval⟩
            subst hm
            refine ⟨FinRelation.select
              (fun t => Sel.Holds φ t) R, ?_⟩
            simp [RawRAExpr.eval?, hEval, hReq]
          · simp [RawRAExpr.arity?, hE, hReq] at hAr
  | proj idxs e ih =>
      cases hE : e.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, hE] at hAr
      | some m =>
          by_cases hOk : ∀ i ∈ idxs, i < m
          · have hPair :
              (∀ i ∈ idxs, i < m) ∧
                idxs.length = n := by
              simpa [RawRAExpr.arity?, hE, hOk] using hAr
            have hm : idxs.length = n := hPair.2
            have hTot := ih hE
            rcases hTot with ⟨R, hEval⟩
            subst hm
            refine ⟨FinRelation.proj idxs R hOk, ?_⟩
            simpa [RawRAExpr.eval?, hEval, hOk]
          · simp [RawRAExpr.arity?, hE, hOk] at hAr
  | prod e₁ e₂ ih₁ ih₂ =>
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
              have hTot₁ := ih₁ h₁
              have hTot₂ := ih₂ h₂
              rcases hTot₁ with ⟨R₁, hEval₁⟩
              rcases hTot₂ with ⟨R₂, hEval₂⟩
              subst hsum
              refine ⟨FinRelation.prod R₁ R₂, ?_⟩
              simp [RawRAExpr.eval?, hEval₁, hEval₂]
  | union e₁ e₂ ih₁ ih₂ =>
      cases h₁ : e₁.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, h₁] at hAr
      | some n₁ =>
          cases h₂ : e₂.arity? Γ with
          | none =>
              simp [RawRAExpr.arity?, h₁, h₂] at hAr
          | some n₂ =>
              by_cases hEq : n₁ = n₂
              · subst hEq
                have hm : n₁ = n := by
                  simpa [RawRAExpr.arity?, h₁, h₂]
                    using hAr
                have hTot₁ := ih₁ h₁
                have hTot₂ := ih₂ h₂
                rcases hTot₁ with ⟨R₁, hEval₁⟩
                rcases hTot₂ with ⟨R₂, hEval₂⟩
                subst hm
                refine ⟨FinRelation.union R₁ R₂, ?_⟩
                simp [RawRAExpr.eval?, hEval₁, hEval₂]
              · simp [RawRAExpr.arity?, h₁, h₂, hEq]
                  at hAr
  | diff e₁ e₂ ih₁ ih₂ =>
      cases h₁ : e₁.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, h₁] at hAr
      | some n₁ =>
          cases h₂ : e₂.arity? Γ with
          | none =>
              simp [RawRAExpr.arity?, h₁, h₂] at hAr
          | some n₂ =>
              by_cases hEq : n₁ = n₂
              · subst hEq
                have hm : n₁ = n := by
                  simpa [RawRAExpr.arity?, h₁, h₂]
                    using hAr
                have hTot₁ := ih₁ h₁
                have hTot₂ := ih₂ h₂
                rcases hTot₁ with ⟨R₁, hEval₁⟩
                rcases hTot₂ with ⟨R₂, hEval₂⟩
                subst hm
                refine ⟨FinRelation.diff R₁ R₂, ?_⟩
                simp [RawRAExpr.eval?, hEval₁, hEval₂]
              · simp [RawRAExpr.arity?, h₁, h₂, hEq]
                  at hAr

end RawRAExpr

------------------------------------------------------------
-- Raw Membership Characterizations
------------------------------------------------------------

namespace RawRAExpr

variable {A D : Type}
variable {_ : RelationNames A} [Domain D]

/-
  Tuple membership in the denotation of a raw RA expression.
  `e.answerContains I t` means that evaluation of `e` on
  `I` succeeds at the arity of `t`, and the resulting
  finite relation contains `t`.
-/
def answerContains
    (e : RawRAExpr A D)
    {Γ : UnnamedSchema A}
    (I : Instance D Γ)
    {n : Nat}
    (t : Tuple D n) : Prop :=
  ∃ R : FinRelation D n,
    e.eval? (Γ := Γ) I = some ⟨n, R⟩ ∧ t ∈ R

theorem answer_iff_of_eval
    {Γ : UnnamedSchema A}
    {I : Instance D Γ}
    {e : RawRAExpr A D}
    {n : Nat}
    {R : FinRelation D n}
    (hEval : e.eval? (Γ := Γ) I = some ⟨n, R⟩)
    (t : Tuple D n) :
    e.answerContains I t ↔ t ∈ R := by
  constructor
  · rintro ⟨S, hS, ht⟩
    have hSome :
        some (Sigma.mk n S) = some (Sigma.mk n R) := by
      rw [← hS, hEval]
    have hSigma :
        Sigma.mk n S = Sigma.mk n R :=
      Option.some.inj hSome
    cases hSigma
    exact ht
  · intro ht
    exact ⟨R, hEval, ht⟩

theorem answer_empty_iff
    {Γ : UnnamedSchema A}
    {I : Instance D Γ}
    {n : Nat}
    (t : Tuple D n) :
    (.empty n : RawRAExpr A D).answerContains I t ↔
      False := by
  have hEval :
      (RawRAExpr.empty n : RawRAExpr A D).eval?
          (Γ := Γ) I =
        some ⟨n, (∅ : FinRelation D n)⟩ := by
    simp [RawRAExpr.eval?]
  rw [answer_iff_of_eval hEval t]
  simp

theorem answer_top_iff
    {Γ : UnnamedSchema A}
    {I : Instance D Γ}
    (t : Tuple D 0) :
    (.top : RawRAExpr A D).answerContains I t ↔ True := by
  have hEval :
      (RawRAExpr.top : RawRAExpr A D).eval? (Γ := Γ) I =
        some ⟨0, FinRelation.top⟩ := by
    simp [RawRAExpr.eval?]
  rw [answer_iff_of_eval hEval t]
  constructor
  · intro _
    trivial
  · intro _
    have ht :
        t = Tuple.empty := by
      apply Vector.ext
      intro i hi
      exact (Nat.not_lt_zero _ hi).elim
    subst ht
    change
      Tuple.empty ∈
        ({Tuple.empty} :
          Finset (Tuple D 0))
    exact Finset.mem_singleton.mpr rfl

theorem answer_single_iff
    {Γ : UnnamedSchema A}
    {I : Instance D Γ}
    {d : D}
    (t : Tuple D 1) :
    (.single d : RawRAExpr A D).answerContains I t ↔
      t[0] = d := by
  have hEval :
      (RawRAExpr.single d : RawRAExpr A D).eval?
          (Γ := Γ) I =
        some ⟨1, FinRelation.single d⟩ := by
    simp [RawRAExpr.eval?]
  rw [answer_iff_of_eval hEval t]
  constructor
  · intro ht
    have hOver := FinRelation.single_isTupleOver (d := d) ht
    simpa using hOver ⟨0, by omega⟩
  · intro h
    have ht :
        t = Vector.ofFn (fun _ : Fin 1 => d) := by
      apply Vector.ext
      intro i hi
      have hi0 : i = 0 := by omega
      subst hi0
      simpa using h
    simp [FinRelation.single, ht]

theorem answer_rel_iff
    {Γ : UnnamedSchema A}
    {I : Instance D Γ}
    {X : A}
    {n : Nat}
    (hAr : Γ.arity? X = some n)
    (t : Tuple D n) :
    (.rel X : RawRAExpr A D).answerContains I t ↔
      ∃ hX : X ∈ Γ.syms,
        ∃ hEq : Γ.arity ⟨X, hX⟩ = n,
          Tuple.castArity hEq t ∈ I ⟨X, hX⟩ := by
  by_cases hX : X ∈ Γ.syms
  · have hEq : Γ.arity ⟨X, hX⟩ = n := by
      have hSome :
          some (Γ.arity ⟨X, hX⟩) = some n := by
        simpa [UnnamedSchema.arity?, hX] using hAr
      exact Option.some.inj hSome
    cases hEq
    have hEval :
        (RawRAExpr.rel X : RawRAExpr A D).eval?
            (Γ := Γ) I =
          some
            ⟨Γ.arity ⟨X, hX⟩, I ⟨X, hX⟩⟩ := by
      simp [RawRAExpr.eval?, Instance.relation?, hX]
    rw [answer_iff_of_eval hEval t]
    constructor
    · intro ht
      exact ⟨hX, rfl, ht⟩
    · rintro ⟨hX', hEq, ht⟩
      have hSub :
          (⟨X, hX'⟩ : Γ.syms) = ⟨X, hX⟩ := by
        apply Subtype.ext
        rfl
      cases hSub
      cases hEq
      simpa using ht
  · have hNone : Γ.arity? X = none := by
      simp [UnnamedSchema.arity?, hX]
    simp [hNone] at hAr

theorem answer_select_iff
    {Γ : UnnamedSchema A}
    {I : Instance D Γ}
    {e : RawRAExpr A D}
    {s : Sel D}
    {n : Nat}
    (hE : e.arity? Γ = some n)
    (hReq : s.arityReq < n)
    (t : Tuple D n) :
    (RawRAExpr.select s e).answerContains I t ↔
      e.answerContains I t ∧ Sel.Holds s t := by
  obtain ⟨R, hEval⟩ := RawRAExpr.wf_total I hE
  have hSel :
      (RawRAExpr.select s e).eval? (Γ := Γ) I =
        some
          ⟨n, FinRelation.select
            (fun t => Sel.Holds s t) R⟩ := by
    simp [RawRAExpr.eval?, hEval, hReq]
  rw [answer_iff_of_eval hSel t, answer_iff_of_eval hEval t]
  simp [FinRelation.select]

theorem answer_proj_iff
    {Γ : UnnamedSchema A}
    {I : Instance D Γ}
    {e : RawRAExpr A D}
    {idxs : List Nat}
    {n : Nat}
    (hE : e.arity? Γ = some n)
    (hIdx : ∀ i ∈ idxs, i < n)
    (t : Tuple D idxs.length) :
    (RawRAExpr.proj idxs e).answerContains I t ↔
      ∃ u : Tuple D n,
        e.answerContains I u ∧
          FinRelation.projTuple idxs u hIdx = t := by
  obtain ⟨R, hEval⟩ := RawRAExpr.wf_total I hE
  have hProj :
      (RawRAExpr.proj idxs e).eval? (Γ := Γ) I =
        some
          ⟨idxs.length,
            FinRelation.proj idxs R hIdx⟩ := by
    simp only [RawRAExpr.eval?, hEval, dif_pos hIdx]
  rw [answer_iff_of_eval hProj t]
  constructor
  · intro ht
    rcases FinRelation.mem_proj_iff.mp ht with
      ⟨s, hs, hst⟩
    exact ⟨s, (answer_iff_of_eval hEval s).2 hs, hst⟩
  · rintro ⟨s, hs, hst⟩
    apply FinRelation.mem_proj_iff.mpr
    exact ⟨s, (answer_iff_of_eval hEval s).1 hs, hst⟩

theorem answer_prod_iff
    {Γ : UnnamedSchema A}
    {I : Instance D Γ}
    {e₁ e₂ : RawRAExpr A D}
    {n m : Nat}
    (h₁ : e₁.arity? Γ = some n)
    (h₂ : e₂.arity? Γ = some m)
    (t : Tuple D (n + m)) :
    (RawRAExpr.prod e₁ e₂).answerContains I t ↔
      ∃ t₁ : Tuple D n,
        e₁.answerContains I t₁ ∧
          ∃ t₂ : Tuple D m,
            e₂.answerContains I t₂ ∧
              FinRelation.appendTuple t₁ t₂ = t := by
  obtain ⟨R₁, hEval₁⟩ := RawRAExpr.wf_total I h₁
  obtain ⟨R₂, hEval₂⟩ := RawRAExpr.wf_total I h₂
  have hProd :
      (RawRAExpr.prod e₁ e₂).eval? (Γ := Γ) I =
        some ⟨n + m, FinRelation.prod R₁ R₂⟩ := by
    simp [RawRAExpr.eval?, hEval₁, hEval₂]
  rw [answer_iff_of_eval hProd t]
  constructor
  · intro ht
    rcases FinRelation.mem_prod_iff.mp ht with
      ⟨t₁, ht₁, t₂, ht₂, hApp⟩
    exact
      ⟨t₁, (answer_iff_of_eval hEval₁ t₁).2 ht₁,
        t₂, (answer_iff_of_eval hEval₂ t₂).2 ht₂,
        hApp⟩
  · rintro ⟨t₁, ht₁, t₂, ht₂, hApp⟩
    apply FinRelation.mem_prod_iff.mpr
    exact
      ⟨t₁, (answer_iff_of_eval hEval₁ t₁).1 ht₁,
        t₂, (answer_iff_of_eval hEval₂ t₂).1 ht₂,
        hApp⟩

theorem answer_union_iff
    {Γ : UnnamedSchema A}
    {I : Instance D Γ}
    {e₁ e₂ : RawRAExpr A D}
    {n : Nat}
    (h₁ : e₁.arity? Γ = some n)
    (h₂ : e₂.arity? Γ = some n)
    (t : Tuple D n) :
    (RawRAExpr.union e₁ e₂).answerContains I t ↔
      e₁.answerContains I t ∨
        e₂.answerContains I t := by
  obtain ⟨R₁, hEval₁⟩ := RawRAExpr.wf_total I h₁
  obtain ⟨R₂, hEval₂⟩ := RawRAExpr.wf_total I h₂
  have hUnion :
      (RawRAExpr.union e₁ e₂).eval? (Γ := Γ) I =
        some ⟨n, FinRelation.union R₁ R₂⟩ := by
    simp [RawRAExpr.eval?, hEval₁, hEval₂]
  rw [answer_iff_of_eval hUnion t,
    answer_iff_of_eval hEval₁ t,
    answer_iff_of_eval hEval₂ t]
  exact FinRelation.mem_union_iff

theorem answer_diff_iff
    {Γ : UnnamedSchema A}
    {I : Instance D Γ}
    {e₁ e₂ : RawRAExpr A D}
    {n : Nat}
    (h₁ : e₁.arity? Γ = some n)
    (h₂ : e₂.arity? Γ = some n)
    (t : Tuple D n) :
    (RawRAExpr.diff e₁ e₂).answerContains I t ↔
      e₁.answerContains I t ∧
        ¬ e₂.answerContains I t := by
  obtain ⟨R₁, hEval₁⟩ := RawRAExpr.wf_total I h₁
  obtain ⟨R₂, hEval₂⟩ := RawRAExpr.wf_total I h₂
  have hDiff :
      (RawRAExpr.diff e₁ e₂).eval? (Γ := Γ) I =
        some ⟨n, FinRelation.diff R₁ R₂⟩ := by
    simp [RawRAExpr.eval?, hEval₁, hEval₂]
  rw [answer_iff_of_eval hDiff t,
    answer_iff_of_eval hEval₁ t,
    answer_iff_of_eval hEval₂ t]
  exact FinRelation.mem_diff_iff

/-
  Every tuple in a raw RA answer uses only values from the
  instance active domain or constants appearing in the
  expression.
-/
theorem answer_over_adom
    {Γ : UnnamedSchema A}
    (I : Instance D Γ) :
    ∀ {e : RawRAExpr A D} {n : Nat} {t : Tuple D n},
      e.arity? Γ = some n →
      e.answerContains I t →
        t.isTupleOver (I.Adom ∪ e.constants) := by
  intro e
  induction e with
  | top =>
      intro n t hAr hAns
      have hn : n = 0 := by
        simpa [RawRAExpr.arity?] using hAr.symm
      subst hn
      intro i
      exact Fin.elim0 i
  | empty m =>
      intro n t hAr hAns
      have hn : n = m := by
        simpa [RawRAExpr.arity?] using hAr.symm
      subst hn
      exact False.elim
        ((answer_empty_iff (Γ := Γ) (I := I) t).1 hAns)
  | rel X =>
      intro n t hAr hAns
      have hR : Γ.arity? X = some n := by
        simpa [RawRAExpr.arity?] using hAr
      rcases
        (answer_rel_iff (Γ := Γ) (I := I) hR t).1
          hAns with
        ⟨hX, hEq, hMem⟩
      cases hEq
      have hOver :
          t.isTupleOver I.Adom :=
        I.isTupleOver_Adom_of_mem hMem
      exact Tuple.isTupleOver_mono
        (by
          intro x hx
          exact Finset.mem_union.mpr (Or.inl hx))
        hOver
  | single d =>
      intro n t hAr hAns
      have hn : n = 1 := by
        simpa [RawRAExpr.arity?] using hAr.symm
      subst hn
      have hCoord :
          t[0] = d :=
        (answer_single_iff
          (Γ := Γ) (I := I) (d := d) t).1 hAns
      intro i
      have hi0 : i = 0 := Fin.eq_zero i
      subst hi0
      change t[0] ∈ I.Adom ∪ ({d} : Finset D)
      exact Finset.mem_union.mpr
        (Or.inr (by simp [hCoord]))
  | select s e ih =>
      intro n t hAr hAns
      cases hE : e.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, hE] at hAr
      | some m =>
          by_cases hReq : s.arityReq < m
          · have hm : m = n := by
              simpa [RawRAExpr.arity?, hE, hReq] using hAr
            subst hm
            have hSubAns :
                e.answerContains I t :=
              ((answer_select_iff (Γ := Γ) (I := I)
                (e := e) (s := s) hE hReq t).1
                hAns).1
            have hOver := ih hE hSubAns
            exact Tuple.isTupleOver_mono
              (by
                intro x hx
                change x ∈ I.Adom ∪ e.constants at hx
                change x ∈
                  I.Adom ∪ (s.constants ∪ e.constants)
                rcases Finset.mem_union.mp hx with hx | hx
                · exact Finset.mem_union.mpr (Or.inl hx)
                · exact Finset.mem_union.mpr
                    (Or.inr
                      (Finset.mem_union.mpr
                        (Or.inr hx))))
              hOver
          · simp [RawRAExpr.arity?, hE, hReq] at hAr
  | proj idxs e ih =>
      intro outAr t hAr hAns
      cases hE : e.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, hE] at hAr
      | some srcAr =>
          by_cases hIdx : ∀ i ∈ idxs, i < srcAr
          · have hout : idxs.length = outAr := by
              have hPair :
                  (∀ i ∈ idxs, i < srcAr) ∧
                    idxs.length = outAr := by
                simpa [RawRAExpr.arity?, hE, hIdx] using hAr
              exact hPair.2
            subst hout
            rcases
              (answer_proj_iff (Γ := Γ) (I := I)
                (e := e) (idxs := idxs) hE hIdx t).1
                hAns with
              ⟨s, hAnsS, hEq⟩
            have hOverS := ih hE hAnsS
            have hOverT :
                t.isTupleOver (I.Adom ∪ e.constants) := by
              rw [← hEq]
              exact FinRelation.projTuple_isTupleOver hOverS
            simpa [RawRAExpr.constants] using hOverT
          · simp [RawRAExpr.arity?, hE, hIdx] at hAr
  | prod e₁ e₂ ih₁ ih₂ =>
      intro ar t hAr hAns
      cases h₁ : e₁.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, h₁] at hAr
      | some n =>
          cases h₂ : e₂.arity? Γ with
          | none =>
              simp [RawRAExpr.arity?, h₁, h₂] at hAr
          | some m =>
              have hsum : n + m = ar := by
                simpa [RawRAExpr.arity?, h₁, h₂]
                  using hAr
              subst hsum
              rcases
                (answer_prod_iff (Γ := Γ) (I := I)
                  (e₁ := e₁) (e₂ := e₂)
                  h₁ h₂ t).1
                  hAns with
                ⟨t₁, hAns₁, t₂, hAns₂, hApp⟩
              have hOver₁ := ih₁ h₁ hAns₁
              have hOver₂ := ih₂ h₂ hAns₂
              have hOverApp :
                  Tuple.isTupleOver
                    (FinRelation.appendTuple t₁ t₂)
                    ((I.Adom ∪ e₁.constants) ∪
                      (I.Adom ∪ e₂.constants)) :=
                FinRelation.appendTuple_isTupleOver_union
                  hOver₁ hOver₂
              rw [← hApp]
              exact Tuple.isTupleOver_mono
                (by
                  intro x hx
                  change
                    x ∈ I.Adom ∪
                      (e₁.constants ∪ e₂.constants)
                  change
                    x ∈ (I.Adom ∪ e₁.constants) ∪
                      (I.Adom ∪ e₂.constants) at hx
                  rcases Finset.mem_union.mp hx with hx | hx
                  · rcases Finset.mem_union.mp hx with
                    hxAdom | hxC₁
                    · exact Finset.mem_union.mpr
                        (Or.inl hxAdom)
                    · exact Finset.mem_union.mpr
                        (Or.inr
                          (Finset.mem_union.mpr
                            (Or.inl hxC₁)))
                  · rcases Finset.mem_union.mp hx with
                    hxAdom | hxC₂
                    · exact Finset.mem_union.mpr
                        (Or.inl hxAdom)
                    · exact Finset.mem_union.mpr
                        (Or.inr
                          (Finset.mem_union.mpr
                            (Or.inr hxC₂))))
                hOverApp
  | union e₁ e₂ ih₁ ih₂ =>
      intro n t hAr hAns
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
                subst hn
                subst hEq
                rcases
                  (answer_union_iff (Γ := Γ) (I := I)
                    (e₁ := e₁) (e₂ := e₂)
                    h₁ h₂ t).1 hAns with
                  hAns₁ | hAns₂
                · exact Tuple.isTupleOver_mono
                    (by
                      intro x hx
                      change
                        x ∈ I.Adom ∪
                          (e₁.constants ∪
                            e₂.constants)
                      change
                        x ∈ I.Adom ∪
                          e₁.constants at hx
                      exact (Finset.mem_union.mp hx).elim
                        (fun hxAdom =>
                          Finset.mem_union.mpr
                            (Or.inl hxAdom))
                        (fun hxC₁ =>
                          Finset.mem_union.mpr
                            (Or.inr
                              (Finset.mem_union.mpr
                                (Or.inl hxC₁)))))
                    (ih₁ h₁ hAns₁)
                · exact Tuple.isTupleOver_mono
                    (by
                      intro x hx
                      change
                        x ∈ I.Adom ∪
                          (e₁.constants ∪
                            e₂.constants)
                      change
                        x ∈ I.Adom ∪
                          e₂.constants at hx
                      exact (Finset.mem_union.mp hx).elim
                        (fun hxAdom =>
                          Finset.mem_union.mpr
                            (Or.inl hxAdom))
                        (fun hxC₂ =>
                          Finset.mem_union.mpr
                            (Or.inr
                              (Finset.mem_union.mpr
                                (Or.inr hxC₂)))))
                    (ih₂ h₂ hAns₂)
              · simp [RawRAExpr.arity?, h₁, h₂, hEq]
                  at hAr
  | diff e₁ e₂ ih₁ ih₂ =>
      intro n t hAr hAns
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
                subst hn
                subst hEq
                have hAns₁ :
                    e₁.answerContains I t :=
                  ((answer_diff_iff (Γ := Γ) (I := I)
                    (e₁ := e₁) (e₂ := e₂)
                    h₁ h₂ t).1
                    hAns).1
                exact Tuple.isTupleOver_mono
                  (by
                    intro x hx
                    change
                      x ∈ I.Adom ∪
                        (e₁.constants ∪ e₂.constants)
                    change x ∈ I.Adom ∪
                      e₁.constants at hx
                    exact (Finset.mem_union.mp hx).elim
                      (fun hxAdom =>
                        Finset.mem_union.mpr
                          (Or.inl hxAdom))
                      (fun hxC₁ =>
                        Finset.mem_union.mpr
                          (Or.inr
                            (Finset.mem_union.mpr
                              (Or.inl hxC₁)))))
                  (ih₁ h₁ hAns₁)
              · simp [RawRAExpr.arity?, h₁, h₂, hEq]
                  at hAr

end RawRAExpr

------------------------------------------------------------
-- Well-Formed Evaluation
------------------------------------------------------------

namespace RAExpr

variable {A D : Type}
variable {_ : RelationNames A} [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Total evaluation for well-formed RA expressions over
  their defining schema.
-/
def eval
    {n : Nat}
    (e : RAExpr D Γ n)
    (I : Instance D Γ) :
    FinRelation D n :=
  match e.expr.eval? (Γ := Γ) I with
  | none => ∅
  | some ⟨m, R⟩ =>
      if hm : m = n then
        cast (by cases hm; rfl) R
      else
        ∅

/-
  Well-formed RA expressions evaluate through the shared
  query interface.
-/
instance
    {n : Nat} :
    QueryEval (RAExpr D Γ n) D Γ n where
  eval e I := e.eval I

/-
  Evaluating an arity-cast expression is equivalent to
  evaluating the original expression and transporting the
  queried tuple along the inverse arity equality.
-/
theorem mem_eval_castArity
    {m n : Nat}
    (h : m = n)
    (e : RAExpr D Γ n)
    (I : Instance D Γ)
    (t : Tuple D m) :
    t ∈ (RAExpr.castArity h e).eval I ↔
      Tuple.castArity h.symm t ∈ e.eval I := by
  cases h
  simp [RAExpr.castArity]

/-
  Raw evaluator returns this base value at arity `n`.
-/
theorem raw_eval?_eq_eval
    {n : Nat}
    (e : RAExpr D Γ n)
    (I : Instance D Γ) :
    e.expr.eval? (Γ := Γ) I =
      some ⟨n, e.eval I⟩ := by
  rcases RawRAExpr.wf_total I e.wf with ⟨R, hR⟩
  simp [RAExpr.eval, hR]

theorem mem_eval_union_iff
    {n : Nat}
    (e₁ e₂ : RAExpr D Γ n)
    (J : Instance D Γ)
    (t : Tuple D n) :
    t ∈ (RAExpr.union e₁ e₂).eval J ↔
      t ∈ e₁.eval J ∨ t ∈ e₂.eval J := by
  have h₁ := RAExpr.raw_eval?_eq_eval e₁ J
  have h₂ := RAExpr.raw_eval?_eq_eval e₂ J
  have hUnion :
      (RAExpr.union e₁ e₂).expr.eval? (Γ := Γ) J =
        some
          ⟨n,
            FinRelation.union
              (e₁.eval J)
              (e₂.eval J)⟩ := by
    simp [RAExpr.union, RawRAExpr.eval?, h₁, h₂]
  have hSpec := RAExpr.raw_eval?_eq_eval
    (RAExpr.union e₁ e₂) J
  have hRel :
      (RAExpr.union e₁ e₂).eval J =
        FinRelation.union
          (e₁.eval J)
          (e₂.eval J) := by
    have hSome :
        some
            (⟨n, (RAExpr.union e₁ e₂).eval J⟩ :
              Sigma (FinRelation D)) =
          some
            ⟨n,
              FinRelation.union
                (e₁.eval J)
                (e₂.eval J)⟩ := by
      rw [← hSpec, hUnion]
    injection hSome with hSigma
    injection hSigma
  rw [hRel]
  exact FinRelation.mem_union_iff

/-
  Every tuple in a typed RA answer uses only values from the
  instance active domain or constants appearing in the
  expression.
-/
theorem mem_eval_over_adom
    {n : Nat}
    (e : RAExpr D Γ n)
    (I : Instance D Γ)
    {t : Tuple D n}
    (hMem : t ∈ e.eval I) :
    t.isTupleOver (I.Adom ∪ e.constants) := by
  have hAns :
      e.expr.answerContains I t :=
    (RawRAExpr.answer_iff_of_eval
      (raw_eval?_eq_eval (e := e) (I := I)) t).2 hMem
  simpa [RAExpr.constants] using
    RawRAExpr.answer_over_adom
      (Γ := Γ) I
      (e := e.expr) (n := n) (t := t)
      e.wf
      hAns

/-
  If the raw evaluator over the defining schema returns
  `some ⟨n, R⟩`, then the base evaluator returns
  exactly `R`.
-/
theorem eval_eq_of_raw_eval
    {n : Nat}
    (e : RAExpr D Γ n)
    (I : Instance D Γ)
    {R : FinRelation D n}
    (h :
      e.expr.eval? (Γ := Γ) I =
        some ⟨n, R⟩) :
    e.eval I = R := by
  have hSome :
      some (Sigma.mk n (e.eval I)) =
        some (Sigma.mk n R) := by
    rw [← raw_eval?_eq_eval (e := e) (I := I), h]
  have hSigma :
      Sigma.mk n (e.eval I) = Sigma.mk n R :=
    Option.some.inj hSome
  cases hSigma
  rfl

end RAExpr

------------------------------------------------------------
-- Expansion Invariance and the Reduct Property
------------------------------------------------------------

namespace RawRAExpr

variable {A D : Type}
variable {_ : RelationNames A} [Domain D]

/-
  Cross-schema expansion invariance:
  arities and interpretations agree on `e`'s symbols.
-/
theorem eval?_expansion_invariance
    (e : RawRAExpr A D)
    {Γ Δ : UnnamedSchema A}
    (I : Instance D Γ)
    (J : Instance D Δ)
    (hAr : Γ.agreeOnArities e.symbols Δ)
    (hRelAgree : I.agreeOnRelations e.symbols J) :
    e.eval? (Γ := Γ) I = e.eval? (Γ := Δ) J := by
  induction e generalizing I J with
  | top =>
      simp [RawRAExpr.eval?]
  | empty n =>
      simp [RawRAExpr.eval?]
  | single d =>
      simp [RawRAExpr.eval?]
  | rel X =>
      have hR :
          I.relation? X = J.relation? X :=
        hRelAgree X (by simp [RawRAExpr.symbols])
      simpa [RawRAExpr.eval?] using hR
  | select φ e ih =>
      have hArSub : Γ.agreeOnArities e.symbols Δ := by
        intro X hX
        exact hAr X (by simpa [RawRAExpr.symbols] using hX)
      have hRelAgreeSub : I.agreeOnRelations e.symbols J :=
        Instance.agreeOnRelations_of_subset
          (by
            intro X hX
            simpa [RawRAExpr.symbols] using hX)
          hRelAgree
      simp [RawRAExpr.eval?, ih I J hArSub hRelAgreeSub]
  | proj idxs e ih =>
      have hArSub : Γ.agreeOnArities e.symbols Δ := by
        intro X hX
        exact hAr X (by simpa [RawRAExpr.symbols] using hX)
      have hRelAgreeSub : I.agreeOnRelations e.symbols J :=
        Instance.agreeOnRelations_of_subset
          (by
            intro X hX
            simpa [RawRAExpr.symbols] using hX)
          hRelAgree
      simp [RawRAExpr.eval?, ih I J hArSub hRelAgreeSub]
  | prod e₁ e₂ ih₁ ih₂ =>
      have hAr₁ : Γ.agreeOnArities e₁.symbols Δ := by
        intro X hX
        have hrU : X ∈ e₁.symbols ∪ e₂.symbols :=
          Finset.mem_union.mpr (Or.inl hX)
        exact hAr X (by simpa [RawRAExpr.symbols] using hrU)
      have hAr₂ : Γ.agreeOnArities e₂.symbols Δ := by
        intro X hX
        have hrU : X ∈ e₁.symbols ∪ e₂.symbols :=
          Finset.mem_union.mpr (Or.inr hX)
        exact hAr X (by simpa [RawRAExpr.symbols] using hrU)
      have hRelAgree₁ :
          I.agreeOnRelations e₁.symbols J :=
        Instance.agreeOnRelations_of_subset
          (by
            intro X hX
            have hrU :
                X ∈ e₁.symbols ∪ e₂.symbols :=
              Finset.mem_union.mpr (Or.inl hX)
            simpa [RawRAExpr.symbols] using hrU)
          hRelAgree
      have hRelAgree₂ :
          I.agreeOnRelations e₂.symbols J :=
        Instance.agreeOnRelations_of_subset
          (by
            intro X hX
            have hrU :
                X ∈ e₁.symbols ∪ e₂.symbols :=
              Finset.mem_union.mpr (Or.inr hX)
            simpa [RawRAExpr.symbols] using hrU)
          hRelAgree
      simp [RawRAExpr.eval?,
        ih₁ I J hAr₁ hRelAgree₁,
        ih₂ I J hAr₂ hRelAgree₂]
  | union e₁ e₂ ih₁ ih₂ =>
      have hAr₁ : Γ.agreeOnArities e₁.symbols Δ := by
        intro X hX
        have hrU : X ∈ e₁.symbols ∪ e₂.symbols :=
          Finset.mem_union.mpr (Or.inl hX)
        exact hAr X (by simpa [RawRAExpr.symbols] using hrU)
      have hAr₂ : Γ.agreeOnArities e₂.symbols Δ := by
        intro X hX
        have hrU : X ∈ e₁.symbols ∪ e₂.symbols :=
          Finset.mem_union.mpr (Or.inr hX)
        exact hAr X (by simpa [RawRAExpr.symbols] using hrU)
      have hRelAgree₁ :
          I.agreeOnRelations e₁.symbols J :=
        Instance.agreeOnRelations_of_subset
          (by
            intro X hX
            have hrU :
                X ∈ e₁.symbols ∪ e₂.symbols :=
              Finset.mem_union.mpr (Or.inl hX)
            simpa [RawRAExpr.symbols] using hrU)
          hRelAgree
      have hRelAgree₂ :
          I.agreeOnRelations e₂.symbols J :=
        Instance.agreeOnRelations_of_subset
          (by
            intro X hX
            have hrU :
                X ∈ e₁.symbols ∪ e₂.symbols :=
              Finset.mem_union.mpr (Or.inr hX)
            simpa [RawRAExpr.symbols] using hrU)
          hRelAgree
      simp [RawRAExpr.eval?,
        ih₁ I J hAr₁ hRelAgree₁,
        ih₂ I J hAr₂ hRelAgree₂]
  | diff e₁ e₂ ih₁ ih₂ =>
      have hAr₁ : Γ.agreeOnArities e₁.symbols Δ := by
        intro X hX
        have hrU : X ∈ e₁.symbols ∪ e₂.symbols :=
          Finset.mem_union.mpr (Or.inl hX)
        exact hAr X (by simpa [RawRAExpr.symbols] using hrU)
      have hAr₂ : Γ.agreeOnArities e₂.symbols Δ := by
        intro X hX
        have hrU : X ∈ e₁.symbols ∪ e₂.symbols :=
          Finset.mem_union.mpr (Or.inr hX)
        exact hAr X (by simpa [RawRAExpr.symbols] using hrU)
      have hRelAgree₁ :
          I.agreeOnRelations e₁.symbols J :=
        Instance.agreeOnRelations_of_subset
          (by
            intro X hX
            have hrU :
                X ∈ e₁.symbols ∪ e₂.symbols :=
              Finset.mem_union.mpr (Or.inl hX)
            simpa [RawRAExpr.symbols] using hrU)
          hRelAgree
      have hRelAgree₂ :
          I.agreeOnRelations e₂.symbols J :=
        Instance.agreeOnRelations_of_subset
          (by
            intro X hX
            have hrU :
                X ∈ e₁.symbols ∪ e₂.symbols :=
              Finset.mem_union.mpr (Or.inr hX)
            simpa [RawRAExpr.symbols] using hrU)
          hRelAgree
      simp [RawRAExpr.eval?,
        ih₁ I J hAr₁ hRelAgree₁,
        ih₂ I J hAr₂ hRelAgree₂]

/-
  Evaluation over an extension agrees with evaluation over
  the reduct to a schema containing all symbols of `e`.
-/
theorem eval?_reduct_property
    {Γ Δ : UnnamedSchema A}
    [hExt : Fact (Δ.extensionOf Γ)]
    (e : RawRAExpr A D)
    (I : Instance D Δ)
    (hSyms : e.symbols ⊆ Γ.syms) :
    e.eval? (Γ := Δ) I =
      e.eval? (Γ := Γ) (Instance.reduct hExt.out I) := by
  apply eval?_expansion_invariance
    (e := e) (Γ := Δ) (Δ := Γ)
    I (Instance.reduct hExt.out I)
  · intro X hX
    have hXΓ : X ∈ Γ.syms := hSyms hX
    have hΔ :
        Δ.arity? X = some (Γ.arity ⟨X, hXΓ⟩) :=
      hExt.out.2 ⟨X, hXΓ⟩
    have hΓ :
        Γ.arity? X = some (Γ.arity ⟨X, hXΓ⟩) := by
      simp [UnnamedSchema.arity?, hXΓ]
    exact hΔ.trans hΓ.symm
  · intro X hX
    have hXΓ : X ∈ Γ.syms := hSyms hX
    have hXΔ : X ∈ Δ.syms := hExt.out.1 hXΓ
    have hAr :
        Δ.arity ⟨X, hXΔ⟩ =
          Γ.arity ⟨X, hXΓ⟩ :=
      UnnamedSchema.arity_eq_of_extensionOf
        hExt.out ⟨X, hXΓ⟩
    unfold Instance.relation? Instance.reduct
    simp [hXΓ, hXΔ, hAr]

end RawRAExpr

namespace RAExpr

variable {A D : Type}
variable {_ : RelationNames A} [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Typed expansion invariance for extensions of the support
  schema of the expression.
-/
theorem expansion_invariance
    {Γ Δ₁ Δ₂ : UnnamedSchema A}
    {n : Nat}
    (e : RAExpr D Γ n)
    [hExt₁ : Fact (Δ₁.extensionOf e.supportSchema)]
    [hExt₂ : Fact (Δ₂.extensionOf e.supportSchema)]
    (I₁ : Instance D Δ₁)
    (I₂ : Instance D Δ₂)
    (hRelAgree :
      I₁.agreeOnRelations e.supportSchema.syms I₂) :
    (e.onSupport.onExtension hExt₁.out).eval I₁ =
      (e.onSupport.onExtension hExt₂.out).eval I₂ := by
  have hAr :
      Δ₁.agreeOnArities
        e.onSupport.expr.symbols
        Δ₂ := by
    intro X hX
    have hXS : X ∈ e.supportSchema.syms :=
      e.onSupport.symbols_subset
        (by simpa [RAExpr.symbols] using hX)
    have h₁ :
        Δ₁.arity? X =
          some (e.supportSchema.arity ⟨X, hXS⟩) :=
      hExt₁.out.2 ⟨X, hXS⟩
    have h₂ :
        Δ₂.arity? X =
          some (e.supportSchema.arity ⟨X, hXS⟩) :=
      hExt₂.out.2 ⟨X, hXS⟩
    exact h₁.trans h₂.symm
  have hSym :
      I₁.agreeOnRelations
        e.onSupport.expr.symbols
        I₂ := by
    intro X hX
    exact hRelAgree X
      (e.onSupport.symbols_subset
        (by simpa [RAExpr.symbols] using hX))
  have hRaw :
      e.onSupport.expr.eval? (Γ := Δ₁) I₁ =
        e.onSupport.expr.eval? (Γ := Δ₂) I₂ :=
    RawRAExpr.eval?_expansion_invariance
      (e := e.onSupport.expr) (Γ := Δ₁) (Δ := Δ₂)
      I₁ I₂ hAr hSym
  let e₁ : RAExpr D Δ₁ n :=
    e.onSupport.onExtension hExt₁.out
  let e₂ : RAExpr D Δ₂ n :=
    e.onSupport.onExtension hExt₂.out
  have hOpt :
      some
          (⟨n, e₁.eval I₁⟩ :
            Sigma (FinRelation D)) =
        some ⟨n, e₂.eval I₂⟩ := by
    calc
      some (⟨n, e₁.eval I₁⟩ : Sigma (FinRelation D))
          = e.onSupport.expr.eval? (Γ := Δ₁) I₁ := by
            simpa [e₁, RAExpr.onExtension] using
              (RAExpr.raw_eval?_eq_eval e₁ I₁).symm
      _ = e.onSupport.expr.eval? (Γ := Δ₂) I₂ := hRaw
      _ = some
          ⟨n, e₂.eval I₂⟩ := by
            simpa [e₂, RAExpr.onExtension] using
              RAExpr.raw_eval?_eq_eval e₂ I₂
  have hEq :
      e₁.eval I₁ = e₂.eval I₂ := by
    injection hOpt with hEqSigma
    injection hEqSigma
  simpa [e₁, e₂] using hEq

/- RA evaluation depends only on mentioned symbols. -/
theorem eval_eq_of_agreeOn
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

/- Evaluation over an extension agrees with the reduct. -/
theorem reduct_property
    {Δ : UnnamedSchema A}
    [hExt : Fact (Δ.extensionOf Γ)]
    {n : Nat}
    (e : RAExpr D Γ n)
    (I : Instance D Δ) :
    (e.onExtension hExt.out).eval I =
      e.eval (Instance.reduct hExt.out I) := by
  have hExtSupport :
      Δ.extensionOf e.supportSchema := by
    refine ⟨?_, ?_⟩
    · intro X hX
      exact hExt.out.1 (e.symbols_subset hX)
    · intro X
      have hXΓ : X.1 ∈ Γ.syms :=
        e.symbols_subset X.2
      have hAr := hExt.out.2 ⟨X.1, hXΓ⟩
      simpa [RAExpr.supportSchema] using hAr
  letI : Fact (Δ.extensionOf e.supportSchema) :=
    ⟨hExtSupport⟩
  letI : Fact (Γ.extensionOf e.supportSchema) :=
    ⟨e.extension_supportSchema⟩
  have hRelAgree :
      I.agreeOnRelations e.supportSchema.syms
        (Instance.reduct hExt.out I) := by
    intro X hX
    have hXΓ : X ∈ Γ.syms :=
      e.symbols_subset hX
    have hXΔ : X ∈ Δ.syms :=
      hExt.out.1 hXΓ
    have hAr :
        Δ.arity ⟨X, hXΔ⟩ =
          Γ.arity ⟨X, hXΓ⟩ :=
      UnnamedSchema.arity_eq_of_extensionOf
        hExt.out ⟨X, hXΓ⟩
    unfold Instance.relation? Instance.reduct
    simp [hXΓ, hXΔ, hAr]
  have hEval :=
    expansion_invariance
      (e := e)
      (I₁ := I)
      (I₂ := Instance.reduct hExt.out I)
      (hRelAgree := hRelAgree)
  simpa [RAExpr.eval, RAExpr.onExtension] using hEval

end RAExpr
