import Databases.UnnamedRA.Semantics

/-
  Syntax-directed rewrites over unnamed relational algebra.

  Key declarations:
    * `RawRAExpr.mergeSelections`
    * `RawRAExpr.cleanVacuousProducts`
    * `RawRAExpr.cleanVacuousUnions`
    * `RawRAExpr.cleanVacuousProjections`
    * `RawRAExpr.clean`
    * `RAExpr.mergeSelections`
    * `RAExpr.cleanVacuousProducts`
    * `RAExpr.cleanVacuousUnions`
    * `RAExpr.cleanVacuousProjections`
    * `RAExpr.clean`

  The cleaning rewrites are proven to preserve UnnamedRA
  evaluation semantics in the following theorems:
    * `RawRAExpr.eval?_mergeSelections`
    * `eval_cleanVacuousProducts`
    * `eval_cleanVacuousUnions`
    * `eval_cleanVacuousProjections`
    * `RAExpr.eval_clean`
-/

------------------------------------------------------------
-- Relation Identities
------------------------------------------------------------

namespace FinRelation

variable {D : Type} [Domain D]

/-
  Appending the nullary tuple on the right changes no
  coordinates.
-/
omit [Domain D] in
theorem appendTuple_empty_right
    {n : Nat}
    (t : Tuple D n) :
    appendTuple t Tuple.empty = t := by
  apply Vector.ext
  intro i hi
  have h :=
    get_appendTuple_left t Tuple.empty ⟨i, hi⟩
  simpa using h

/-
  Product with the nullary singleton on the right is an
  identity.
-/
theorem prod_top_right
    {n : Nat}
    (R : FinRelation D n) :
    prod R top = R := by
  apply Finset.ext
  intro t
  constructor
  · intro ht
    rw [mem_prod_iff] at ht
    rcases ht with ⟨t₁, ht₁, t₂, ht₂, hEq⟩
    have ht₂eq : t₂ = Tuple.empty := by
      simpa [top] using ht₂
    subst ht₂eq
    rw [appendTuple_empty_right] at hEq
    simpa [← hEq] using ht₁
  · intro ht
    rw [mem_prod_iff]
    refine ⟨t, ht, Tuple.empty, ?_, ?_⟩
    · simp [top]
    · exact appendTuple_empty_right t

/-
  Projecting a tuple along `[0, ..., n - 1]` is the
  identity.
-/
omit [Domain D] in
theorem projTuple_range_eq
    {n : Nat}
    (t : Tuple D n)
    (h : ∀ i ∈ List.range n, i < n) :
    projTuple (List.range n) t h =
      Tuple.castArity
        (by simp [List.length_range] :
          (List.range n).length = n)
        t := by
  apply Vector.toList_inj.mp
  apply List.ext_getElem
  · simp [Tuple.castArity_toList]
  · intro i _ _
    simp [projTuple, Tuple.castArity_toList,
      Vector.get, Vector.ofFn]

/-
  Projecting a relation along `[0, ..., n - 1]` is the
  identity.
-/
theorem proj_range_eq
    {n : Nat}
    (R : FinRelation D n)
    (h : ∀ i ∈ List.range n, i < n) :
    cast
        (congrArg (FinRelation D)
          (by simp [List.length_range] :
            (List.range n).length = n))
        (FinRelation.proj (List.range n) R h) =
      R := by
  let hLen : (List.range n).length = n := by
    simp [List.length_range]
  apply Finset.ext
  intro t
  rw [FinRelation.mem_cast_iff (h := hLen)]
  constructor
  · intro ht
    rw [FinRelation.mem_proj_iff] at ht
    rcases ht with ⟨s, hs, hst⟩
    have hst' :
        Tuple.castArity hLen t =
          Tuple.castArity hLen s := by
      rw [← hst]
      simp [projTuple_range_eq]
    have hts : t = s := by
      have hcong :=
        congrArg (Tuple.castArity hLen.symm) hst'
      simpa [Tuple.castArity_symm] using hcong
    simpa [hts] using hs
  · intro ht
    rw [FinRelation.mem_proj_iff]
    refine ⟨t, ht, ?_⟩
    exact (projTuple_range_eq t h).trans
      (Tuple.castArity_proof_irrel _ hLen _)

end FinRelation

------------------------------------------------------------
-- Raw Expression Cleaning
------------------------------------------------------------

namespace RawRAExpr

variable {A D : Type}
variable [RelationNames A] [Domain D]

/- Merge one selection with a selected child. -/
private def mergeSelection
    (s : Sel D)
    (e : RawRAExpr A D) : RawRAExpr A D :=
  match e with
  | .select t f => .select (.and t s) f
  | e => .select s e

/- Merge every adjacent selection from inner to outer. -/
def mergeSelections :
    RawRAExpr A D → RawRAExpr A D
| .top => .top
| .empty n => .empty n
| .rel X => .rel X
| .single d => .single d
| .select s e =>
    mergeSelection s e.mergeSelections
| .proj idxs e => .proj idxs e.mergeSelections
| .prod e₁ e₂ =>
    .prod e₁.mergeSelections e₂.mergeSelections
| .union e₁ e₂ =>
    .union e₁.mergeSelections e₂.mergeSelections
| .diff e₁ e₂ =>
    .diff e₁.mergeSelections e₂.mergeSelections

/- Merging one selection preserves raw arity. -/
private theorem arity?_mergeSelection
    (Γ : UnnamedSchema A)
    (s : Sel D)
    (e : RawRAExpr A D) :
    (mergeSelection s e).arity? Γ =
      (RawRAExpr.select s e).arity? Γ := by
  cases e <;>
    simp only [mergeSelection]
  case select t f =>
    simp only [RawRAExpr.arity?, Sel.arityReq]
    cases f.arity? Γ with
    | none => rfl
    | some n =>
        by_cases ht : t.arityReq < n <;>
          by_cases hs : s.arityReq < n <;>
            simp [ht, hs]

/- Selection merging preserves raw arity checking. -/
theorem arity?_mergeSelections
    (Γ : UnnamedSchema A)
    (e : RawRAExpr A D) :
    e.mergeSelections.arity? Γ = e.arity? Γ := by
  induction e with
  | top => rfl
  | empty _ => rfl
  | rel _ => rfl
  | single _ => rfl
  | select s e ih =>
      rw [mergeSelections, arity?_mergeSelection]
      simp only [RawRAExpr.arity?, ih]
  | proj idxs e ih =>
      simp only [mergeSelections, RawRAExpr.arity?, ih]
  | prod e₁ e₂ ih₁ ih₂ =>
      simp only [mergeSelections, RawRAExpr.arity?,
        ih₁, ih₂]
  | union e₁ e₂ ih₁ ih₂ =>
      simp only [mergeSelections, RawRAExpr.arity?,
        ih₁, ih₂]
  | diff e₁ e₂ ih₁ ih₂ =>
      simp only [mergeSelections, RawRAExpr.arity?,
        ih₁, ih₂]

/- Merging one selection preserves raw evaluation. -/
private theorem eval?_mergeSelection
    (I : Instance D Γ)
    (s : Sel D)
    (e : RawRAExpr A D) :
    (mergeSelection s e).eval? I =
      (RawRAExpr.select s e).eval? I := by
  cases e <;>
    simp only [mergeSelection]
  case select t f =>
    simp only [RawRAExpr.eval?, Sel.arityReq]
    cases hEval : f.eval? I with
    | none => rfl
    | some p =>
        rcases p with ⟨n, R⟩
        by_cases ht : t.arityReq < n
        · by_cases hs : s.arityReq < n
          · have hmax :
                max t.arityReq s.arityReq < n :=
              max_lt_iff.mpr ⟨ht, hs⟩
            simp only [hmax, ht, hs, dite_true]
            apply congrArg
              (fun S : FinRelation D n =>
                some (⟨n, S⟩ : Sigma (FinRelation D)))
            apply Finset.ext
            intro u
            simp [FinRelation.select, Sel.Holds,
              and_assoc]
          · have hmax :
                ¬ max t.arityReq s.arityReq < n := by
              intro h
              exact hs (max_lt_iff.mp h).2
            simp [hmax, ht, hs]
        · have hmax :
              ¬ max t.arityReq s.arityReq < n := by
            intro h
            exact ht (max_lt_iff.mp h).1
          simp [hmax, ht]

/- Selection merging preserves raw evaluation. -/
theorem eval?_mergeSelections
    {Γ : UnnamedSchema A}
    (I : Instance D Γ)
    (e : RawRAExpr A D) :
    e.mergeSelections.eval? I = e.eval? I := by
  induction e with
  | top => rfl
  | empty _ => rfl
  | rel _ => rfl
  | single _ => rfl
  | select s e ih =>
      rw [mergeSelections, eval?_mergeSelection]
      simp only [RawRAExpr.eval?, ih]
  | proj idxs e ih =>
      simp only [mergeSelections, RawRAExpr.eval?, ih]
  | prod e₁ e₂ ih₁ ih₂ =>
      simp only [mergeSelections, RawRAExpr.eval?,
        ih₁, ih₂]
  | union e₁ e₂ ih₁ ih₂ =>
      simp only [mergeSelections, RawRAExpr.eval?,
        ih₁, ih₂]
  | diff e₁ e₂ ih₁ ih₂ =>
      simp only [mergeSelections, RawRAExpr.eval?,
        ih₁, ih₂]

/-
  Remove syntactic right-products by the nullary
  singleton.
-/
def cleanVacuousProducts :
    RawRAExpr A D → RawRAExpr A D
| .top => .top
| .empty n => .empty n
| .rel X => .rel X
| .single d => .single d
| .select φ e => .select φ e.cleanVacuousProducts
| .proj idxs e => .proj idxs e.cleanVacuousProducts
| .prod e₁ e₂ =>
    match e₂.cleanVacuousProducts with
    | .top => e₁.cleanVacuousProducts
    | e₂' => .prod e₁.cleanVacuousProducts e₂'
| .union e₁ e₂ =>
    .union
      e₁.cleanVacuousProducts
      e₂.cleanVacuousProducts
| .diff e₁ e₂ =>
    .diff
      e₁.cleanVacuousProducts
      e₂.cleanVacuousProducts

/- Product cleanup preserves raw arity checking. -/
theorem arity?_cleanVacuousProducts
    (Γ : UnnamedSchema A)
    (e : RawRAExpr A D) :
    e.cleanVacuousProducts.arity? Γ = e.arity? Γ := by
  induction e with
  | top =>
      simp [cleanVacuousProducts, arity?]
  | empty n =>
      simp [cleanVacuousProducts, arity?]
  | rel X =>
      simp [cleanVacuousProducts, arity?]
  | single d =>
      simp [cleanVacuousProducts, arity?]
  | select φ e ih =>
      simp [cleanVacuousProducts, arity?, ih]
  | proj idxs e ih =>
      simp [cleanVacuousProducts, arity?, ih]
  | prod e₁ e₂ ih₁ ih₂ =>
      cases h₂ : e₂.cleanVacuousProducts with
      | top =>
          have h₂Ar : e₂.arity? Γ = some 0 := by
            rw [← ih₂]
            simp [h₂, arity?]
          rw [cleanVacuousProducts, h₂]
          rw [ih₁]
          cases h₁ : e₁.arity? Γ <;>
            simp [arity?, h₁, h₂Ar]
      | empty n =>
          have h₂Ar :
              (.empty n : RawRAExpr A D).arity? Γ =
                e₂.arity? Γ := by
            simpa [h₂] using ih₂
          rw [cleanVacuousProducts, h₂]
          simp only
          simp [arity?, ih₁, ← h₂Ar]
      | rel X =>
          have h₂Ar :
              (.rel X : RawRAExpr A D).arity? Γ =
                e₂.arity? Γ := by
            simpa [h₂] using ih₂
          rw [cleanVacuousProducts, h₂]
          simp only
          simp [arity?, ih₁, ← h₂Ar]
      | single d =>
          have h₂Ar :
              (.single d : RawRAExpr A D).arity? Γ =
                e₂.arity? Γ := by
            simpa [h₂] using ih₂
          rw [cleanVacuousProducts, h₂]
          simp only
          simp [arity?, ih₁, ← h₂Ar]
      | select φ e =>
          have h₂Ar :
              (.select φ e : RawRAExpr A D).arity? Γ =
                e₂.arity? Γ := by
            simpa [h₂] using ih₂
          rw [cleanVacuousProducts, h₂]
          simp only
          simp [arity?, ih₁, ← h₂Ar]
      | proj idxs e =>
          have h₂Ar :
              (.proj idxs e : RawRAExpr A D).arity? Γ =
                e₂.arity? Γ := by
            simpa [h₂] using ih₂
          rw [cleanVacuousProducts, h₂]
          simp only
          simp [arity?, ih₁, ← h₂Ar]
      | prod e₁' e₂' =>
          have h₂Ar :
              (.prod e₁' e₂' :
                RawRAExpr A D).arity? Γ =
                e₂.arity? Γ := by
            simpa [h₂] using ih₂
          rw [cleanVacuousProducts, h₂]
          simp only
          simp [arity?, ih₁, ← h₂Ar]
      | union e₁' e₂' =>
          have h₂Ar :
              (.union e₁' e₂' :
                RawRAExpr A D).arity? Γ =
                e₂.arity? Γ := by
            simpa [h₂] using ih₂
          rw [cleanVacuousProducts, h₂]
          simp only
          simp [arity?, ih₁, ← h₂Ar]
      | diff e₁' e₂' =>
          have h₂Ar :
              (.diff e₁' e₂' :
                RawRAExpr A D).arity? Γ =
                e₂.arity? Γ := by
            simpa [h₂] using ih₂
          rw [cleanVacuousProducts, h₂]
          simp only
          simp [arity?, ih₁, ← h₂Ar]
  | union e₁ e₂ ih₁ ih₂ =>
      simp [cleanVacuousProducts, arity?, ih₁, ih₂]
  | diff e₁ e₂ ih₁ ih₂ =>
      simp [cleanVacuousProducts, arity?, ih₁, ih₂]

/- Product cleanup preserves raw evaluation. -/
theorem eval?_cleanVacuousProducts
    {Γ : UnnamedSchema A}
    (I : Instance D Γ)
    (e : RawRAExpr A D) :
    e.cleanVacuousProducts.eval? I = e.eval? I := by
  induction e with
  | top =>
      simp [cleanVacuousProducts, eval?]
  | empty n =>
      simp [cleanVacuousProducts, eval?]
  | rel X =>
      simp [cleanVacuousProducts, eval?]
  | single d =>
      simp [cleanVacuousProducts, eval?]
  | select φ e ih =>
      simp [cleanVacuousProducts, eval?, ih]
  | proj idxs e ih =>
      simp [cleanVacuousProducts, eval?, ih]
  | prod e₁ e₂ ih₁ ih₂ =>
      cases h₂ : e₂.cleanVacuousProducts with
      | top =>
          have h₂Eval :
              e₂.eval? I =
                some ⟨0, FinRelation.top⟩ := by
            rw [← ih₂]
            simp [h₂, eval?]
          rw [cleanVacuousProducts, h₂]
          rw [ih₁]
          cases h₁ : e₁.eval? I with
          | none =>
              simp [eval?, h₁, h₂Eval]
          | some s =>
              cases s with
              | mk n R =>
                  simp [eval?, h₁, h₂Eval,
                    FinRelation.prod_top_right]
      | empty n =>
          have h₂Eval :
              (.empty n : RawRAExpr A D).eval? I =
                e₂.eval? I := by
            simpa [h₂] using ih₂
          rw [cleanVacuousProducts, h₂]
          simp only
          simp [eval?, ih₁, ← h₂Eval]
      | rel X =>
          have h₂Eval :
              (.rel X : RawRAExpr A D).eval? I =
                e₂.eval? I := by
            simpa [h₂] using ih₂
          rw [cleanVacuousProducts, h₂]
          simp only
          simp [eval?, ih₁, ← h₂Eval]
      | single d =>
          have h₂Eval :
              (.single d : RawRAExpr A D).eval? I =
                e₂.eval? I := by
            simpa [h₂] using ih₂
          rw [cleanVacuousProducts, h₂]
          simp only
          simp [eval?, ih₁, ← h₂Eval]
      | select φ e =>
          have h₂Eval :
              (.select φ e : RawRAExpr A D).eval? I =
                e₂.eval? I := by
            simpa [h₂] using ih₂
          rw [cleanVacuousProducts, h₂]
          simp only
          simp [eval?, ih₁, ← h₂Eval]
      | proj idxs e =>
          have h₂Eval :
              (.proj idxs e : RawRAExpr A D).eval? I =
                e₂.eval? I := by
            simpa [h₂] using ih₂
          rw [cleanVacuousProducts, h₂]
          simp only
          simp [eval?, ih₁, ← h₂Eval]
      | prod e₁' e₂' =>
          have h₂Eval :
              (.prod e₁' e₂' : RawRAExpr A D).eval? I =
                e₂.eval? I := by
            simpa [h₂] using ih₂
          rw [cleanVacuousProducts, h₂]
          simp only
          simp [eval?, ih₁, ← h₂Eval]
      | union e₁' e₂' =>
          have h₂Eval :
              (.union e₁' e₂' : RawRAExpr A D).eval? I =
                e₂.eval? I := by
            simpa [h₂] using ih₂
          rw [cleanVacuousProducts, h₂]
          simp only
          simp [eval?, ih₁, ← h₂Eval]
      | diff e₁' e₂' =>
          have h₂Eval :
              (.diff e₁' e₂' : RawRAExpr A D).eval? I =
                e₂.eval? I := by
            simpa [h₂] using ih₂
          rw [cleanVacuousProducts, h₂]
          simp only
          simp [eval?, ih₁, ← h₂Eval]
  | union e₁ e₂ ih₁ ih₂ =>
      simp [cleanVacuousProducts, eval?, ih₁, ih₂]
  | diff e₁ e₂ ih₁ ih₂ =>
      simp [cleanVacuousProducts, eval?, ih₁, ih₂]

/-
  Return the arity of a syntactic empty relation, if
  present.
-/
def emptyArity? :
    RawRAExpr A D → Option Nat
| .empty n => some n
| _ => none

theorem answer_false_of_emptyArity
    {Γ : UnnamedSchema A}
    (I : Instance D Γ)
    {e : RawRAExpr A D}
    {m n : Nat}
    (hEmpty : e.emptyArity? = some m)
    (hAr : e.arity? Γ = some n)
    (t : Tuple D n) :
    e.answerContains I t ↔ False := by
  cases e with
  | empty k =>
      have hkn : k = n :=
        Option.some.inj
          (by simpa [RawRAExpr.arity?] using hAr)
      subst n
      exact RawRAExpr.answer_empty_iff t
  | top =>
      simp [emptyArity?] at hEmpty
  | rel X =>
      simp [emptyArity?] at hEmpty
  | single d =>
      simp [emptyArity?] at hEmpty
  | select φ e =>
      simp [emptyArity?] at hEmpty
  | proj idxs e =>
      simp [emptyArity?] at hEmpty
  | prod e₁ e₂ =>
      simp [emptyArity?] at hEmpty
  | union e₁ e₂ =>
      simp [emptyArity?] at hEmpty
  | diff e₁ e₂ =>
      simp [emptyArity?] at hEmpty

/-
  Remove syntactic unions with an empty same-arity branch.
-/
def cleanVacuousUnions :
    RawRAExpr A D → RawRAExpr A D
| .top => .top
| .empty n => .empty n
| .rel X => .rel X
| .single d => .single d
| .select φ e => .select φ e.cleanVacuousUnions
| .proj idxs e => .proj idxs e.cleanVacuousUnions
| .prod e₁ e₂ =>
    .prod e₁.cleanVacuousUnions e₂.cleanVacuousUnions
| .union e₁ e₂ =>
    let e₁' := e₁.cleanVacuousUnions
    let e₂' := e₂.cleanVacuousUnions
    match e₁'.emptyArity?, e₂'.emptyArity? with
    | some _, _ => e₂'
    | none, some _ => e₁'
    | none, none => .union e₁' e₂'
| .diff e₁ e₂ =>
    .diff e₁.cleanVacuousUnions e₂.cleanVacuousUnions

/-
  Union cleanup preserves arity for well-formed raw
  expressions.
-/
theorem arity?_cleanUnions
    (Γ : UnnamedSchema A)
    {e : RawRAExpr A D}
    {n : Nat}
    (h : e.arity? Γ = some n) :
    e.cleanVacuousUnions.arity? Γ = some n := by
  induction e generalizing n with
  | top =>
      simpa [cleanVacuousUnions, arity?] using h
  | empty m =>
      simpa [cleanVacuousUnions, arity?] using h
  | rel X =>
      simpa [cleanVacuousUnions, arity?] using h
  | single d =>
      simpa [cleanVacuousUnions, arity?] using h
  | select φ e ih =>
      cases hE : e.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, hE] at h
      | some m =>
          have hClean := ih hE
          by_cases hReq : φ.arityReq < m
          · simp [RawRAExpr.arity?, hE, hReq] at h
            subst n
            simp [cleanVacuousUnions, RawRAExpr.arity?,
              hClean, hReq]
          · simp [RawRAExpr.arity?, hE, hReq] at h
  | proj idxs e ih =>
      cases hE : e.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, hE] at h
      | some m =>
          have hClean := ih hE
          by_cases hIdx : ∀ i ∈ idxs, i < m
          · have hDec :
                decide (∀ i ∈ idxs, i < m) = true :=
              decide_eq_true hIdx
            simp [RawRAExpr.arity?, hE, hDec] at h
            subst n
            simp [cleanVacuousUnions, RawRAExpr.arity?,
              hClean, hDec]
          · simp [RawRAExpr.arity?, hE, hIdx] at h
  | prod e₁ e₂ ih₁ ih₂ =>
      cases h₁ : e₁.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, h₁] at h
      | some n₁ =>
          cases h₂ : e₂.arity? Γ with
          | none =>
              simp [RawRAExpr.arity?, h₁, h₂] at h
          | some n₂ =>
              have hClean₁ := ih₁ h₁
              have hClean₂ := ih₂ h₂
              simp [RawRAExpr.arity?, h₁, h₂] at h
              subst n
              simp [cleanVacuousUnions, RawRAExpr.arity?,
                hClean₁, hClean₂]
  | union e₁ e₂ ih₁ ih₂ =>
      cases h₁ : e₁.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, h₁] at h
      | some n₁ =>
          cases h₂ : e₂.arity? Γ with
          | none =>
              simp [RawRAExpr.arity?, h₁, h₂] at h
          | some n₂ =>
              by_cases hEq : n₁ = n₂
              · have hClean₁ := ih₁ h₁
                have hClean₂ := ih₂ h₂
                simp [arity?, h₁, h₂, hEq] at h
                subst n
                subst n₂
                cases hEmpty₁ :
                    e₁.cleanVacuousUnions.emptyArity?
                · cases hEmpty₂ :
                    e₂.cleanVacuousUnions.emptyArity?
                  · simp [cleanVacuousUnions, hEmpty₁,
                      hEmpty₂, RawRAExpr.arity?,
                      hClean₁, hClean₂]
                  · simpa [cleanVacuousUnions, hEmpty₁,
                      hEmpty₂] using hClean₁
                · simpa [cleanVacuousUnions, hEmpty₁]
                    using hClean₂
              · simp [arity?, h₁, h₂, hEq] at h
  | diff e₁ e₂ ih₁ ih₂ =>
      cases h₁ : e₁.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, h₁] at h
      | some n₁ =>
          cases h₂ : e₂.arity? Γ with
          | none =>
              simp [RawRAExpr.arity?, h₁, h₂] at h
          | some n₂ =>
              by_cases hEq : n₁ = n₂
              · have hClean₁ := ih₁ h₁
                have hClean₂ := ih₂ h₂
                simp [arity?, h₁, h₂, hEq] at h
                subst n
                subst n₂
                simp [cleanVacuousUnions, RawRAExpr.arity?,
                  hClean₁, hClean₂]
              · simp [arity?, h₁, h₂, hEq] at h

theorem answerContains_cleanUnions_iff
    {Γ : UnnamedSchema A}
    (I : Instance D Γ)
    {e : RawRAExpr A D}
    {n : Nat}
    (h : e.arity? Γ = some n)
    (t : Tuple D n) :
    e.cleanVacuousUnions.answerContains I t ↔
      e.answerContains I t := by
  induction e generalizing n with
  | top =>
      simp [cleanVacuousUnions]
  | empty m =>
      simp [cleanVacuousUnions]
  | rel X =>
      simp [cleanVacuousUnions]
  | single d =>
      simp [cleanVacuousUnions]
  | select φ e ih =>
      cases hE : e.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, hE] at h
      | some m =>
          by_cases hReq : φ.arityReq < m
          · have hn : m = n := by
              have hSome :
                  some m = some n := by
                simpa [RawRAExpr.arity?, hE, hReq] using h
              exact Option.some.inj hSome
            subst hn
            have hClean :=
              arity?_cleanUnions
                Γ hE
            have hReqClean :
                φ.arityReq < m := hReq
            simp only [cleanVacuousUnions]
            rw [RawRAExpr.answer_select_iff
              (e := e.cleanVacuousUnions) hClean
              hReqClean t]
            rw [RawRAExpr.answer_select_iff hE hReq t]
            exact and_congr_left'
              (ih hE t)
          · simp [RawRAExpr.arity?, hE, hReq] at h
  | proj idxs e ih =>
      cases hE : e.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, hE] at h
      | some m =>
          by_cases hIdx : ∀ i ∈ idxs, i < m
          · have hn : idxs.length = n := by
              have hDec :
                  decide (∀ i ∈ idxs, i < m) = true :=
                decide_eq_true hIdx
              have hSome :
                  some idxs.length = some n := by
                simpa [arity?, hE, hDec] using h
              exact Option.some.inj hSome
            subst hn
            have hClean :=
              arity?_cleanUnions
                Γ hE
            simp only [cleanVacuousUnions]
            rw [RawRAExpr.answer_proj_iff
              (e := e.cleanVacuousUnions) hClean
              hIdx t]
            rw [RawRAExpr.answer_proj_iff hE hIdx t]
            constructor
            · rintro ⟨s, hs, hst⟩
              exact ⟨s, (ih hE s).mp hs, hst⟩
            · rintro ⟨s, hs, hst⟩
              exact ⟨s, (ih hE s).mpr hs, hst⟩
          · simp [RawRAExpr.arity?, hE, hIdx] at h
  | prod e₁ e₂ ih₁ ih₂ =>
      cases h₁ : e₁.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, h₁] at h
      | some n₁ =>
          cases h₂ : e₂.arity? Γ with
          | none =>
              simp [RawRAExpr.arity?, h₁, h₂] at h
          | some n₂ =>
              have hn : n₁ + n₂ = n := by
                have hSome :
                    some (n₁ + n₂) = some n := by
                  simpa [arity?, h₁, h₂] using h
                exact Option.some.inj hSome
              subst hn
              have hClean₁ :=
                arity?_cleanUnions Γ h₁
              have hClean₂ :=
                arity?_cleanUnions Γ h₂
              simp only [cleanVacuousUnions]
              rw [RawRAExpr.answer_prod_iff
                (e₁ := e₁.cleanVacuousUnions)
                (e₂ := e₂.cleanVacuousUnions)
                hClean₁ hClean₂ t]
              rw [RawRAExpr.answer_prod_iff h₁ h₂ t]
              constructor
              · rintro ⟨t₁, ht₁, t₂, ht₂, hApp⟩
                exact
                  ⟨t₁, (ih₁ h₁ t₁).mp ht₁,
                    t₂,
                    (ih₂ h₂ t₂).mp ht₂, hApp⟩
              · rintro ⟨t₁, ht₁, t₂, ht₂, hApp⟩
                exact
                  ⟨t₁, (ih₁ h₁ t₁).mpr ht₁,
                    t₂,
                    (ih₂ h₂ t₂).mpr ht₂, hApp⟩
  | union e₁ e₂ ih₁ ih₂ =>
      cases h₁ : e₁.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, h₁] at h
      | some n₁ =>
          cases h₂ : e₂.arity? Γ with
          | none =>
              simp [RawRAExpr.arity?, h₁, h₂] at h
          | some n₂ =>
              by_cases hEq : n₁ = n₂
              · have hn : n₁ = n := by
                  have hSome :
                      some n₁ = some n := by
                    simpa [arity?, h₁, h₂, hEq]
                      using h
                  exact Option.some.inj hSome
                subst hn
                subst hEq
                have hClean₁ :=
                  arity?_cleanUnions Γ h₁
                have hClean₂ :=
                  arity?_cleanUnions Γ h₂
                cases hEmpty₁ :
                    e₁.cleanVacuousUnions.emptyArity? with
                | some k =>
                    rw [answer_union_iff h₁ h₂ t]
                    have hCleanLeftFalse :=
                      answer_false_of_emptyArity
                        I hEmpty₁ hClean₁ t
                    have hLeft :
                        e₁.answerContains I t ↔
                          False := by
                      rw [← ih₁ h₁ t]
                      exact hCleanLeftFalse
                    rw [hLeft]
                    simpa [cleanVacuousUnions,
                      hEmpty₁] using
                      (ih₂ h₂ t).trans (by simp)
                | none =>
                    cases hEmpty₂ :
                        e₂.cleanVacuousUnions.emptyArity?
                    with
                    | some k =>
                        rw [answer_union_iff h₁ h₂ t]
                        have hCleanRightFalse :=
                          answer_false_of_emptyArity
                            I hEmpty₂ hClean₂ t
                        have hRight :
                            e₂.answerContains I t ↔
                              False := by
                          rw [← ih₂ h₂ t]
                          exact hCleanRightFalse
                        rw [hRight]
                        simpa [cleanVacuousUnions,
                          hEmpty₁,
                          hEmpty₂] using
                          (ih₁ h₁ t).trans (by simp)
                    | none =>
                        simp only [cleanVacuousUnions,
                          hEmpty₁,
                          hEmpty₂]
                        rw [answer_union_iff
                          hClean₁ hClean₂ t]
                        rw [answer_union_iff h₁ h₂ t]
                        exact
                          or_congr
                            (ih₁ h₁ t) (ih₂ h₂ t)
              · simp [arity?, h₁, h₂, hEq] at h
  | diff e₁ e₂ ih₁ ih₂ =>
      cases h₁ : e₁.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, h₁] at h
      | some n₁ =>
          cases h₂ : e₂.arity? Γ with
          | none =>
              simp [RawRAExpr.arity?, h₁, h₂] at h
          | some n₂ =>
              by_cases hEq : n₁ = n₂
              · have hn : n₁ = n := by
                  have hSome :
                      some n₁ = some n := by
                    simpa [arity?, h₁, h₂, hEq]
                      using h
                  exact Option.some.inj hSome
                subst hn
                subst hEq
                have hClean₁ :=
                  arity?_cleanUnions Γ h₁
                have hClean₂ :=
                  arity?_cleanUnions Γ h₂
                simp only [cleanVacuousUnions]
                rw [RawRAExpr.answer_diff_iff
                  (e₁ := e₁.cleanVacuousUnions)
                  (e₂ := e₂.cleanVacuousUnions)
                  hClean₁ hClean₂ t]
                rw [RawRAExpr.answer_diff_iff h₁ h₂ t]
                exact
                  and_congr
                    (ih₁ h₁ t)
                    (not_congr (ih₂ h₂ t))
              · simp [arity?, h₁, h₂, hEq] at h

/-
  Union cleanup preserves raw evaluation on well-formed
  expressions.
-/
theorem eval?_cleanUnions
    {Γ : UnnamedSchema A}
    (I : Instance D Γ)
    {e : RawRAExpr A D}
    {n : Nat}
    (h : e.arity? Γ = some n) :
    e.cleanVacuousUnions.eval? I = e.eval? I := by
  have hClean :=
    arity?_cleanUnions Γ h
  rcases RawRAExpr.wf_total I hClean with
    ⟨Rclean, hRclean⟩
  rcases RawRAExpr.wf_total I h with ⟨R, hR⟩
  have hRel : Rclean = R := by
    apply Finset.ext
    intro t
    have hAns :=
      answerContains_cleanUnions_iff
        I h t
    rw [RawRAExpr.answer_iff_of_eval hRclean t,
      RawRAExpr.answer_iff_of_eval hR t] at hAns
    exact hAns
  rw [hRclean, hR, hRel]

/-
  Remove identity projections using the supplied schema
  for arity checks.
-/
def cleanVacuousProjections
    (Γ : UnnamedSchema A) :
    RawRAExpr A D → RawRAExpr A D
| .top => .top
| .empty n => .empty n
| .rel X => .rel X
| .single d => .single d
| .select φ e =>
    .select φ (e.cleanVacuousProjections Γ)
| .proj idxs e =>
    let e' := e.cleanVacuousProjections Γ
    match e'.arity? Γ with
    | some m =>
        if idxs = List.range m then
          e'
        else
          .proj idxs e'
    | none =>
        .proj idxs e'
| .prod e₁ e₂ =>
    .prod
      (e₁.cleanVacuousProjections Γ)
      (e₂.cleanVacuousProjections Γ)
| .union e₁ e₂ =>
    .union
      (e₁.cleanVacuousProjections Γ)
      (e₂.cleanVacuousProjections Γ)
| .diff e₁ e₂ =>
    .diff
      (e₁.cleanVacuousProjections Γ)
      (e₂.cleanVacuousProjections Γ)

/-
  Projection cleanup preserves arity for well-formed raw
  expressions.
-/
theorem arity?_cleanProjections
    (Γ : UnnamedSchema A)
    {e : RawRAExpr A D}
    {n : Nat}
    (h : e.arity? Γ = some n) :
    (e.cleanVacuousProjections Γ).arity? Γ = some n := by
  induction e generalizing n with
  | top =>
      simpa [cleanVacuousProjections, arity?] using h
  | empty m =>
      simpa [cleanVacuousProjections, arity?] using h
  | rel X =>
      simpa [cleanVacuousProjections, arity?] using h
  | single d =>
      simpa [cleanVacuousProjections, arity?] using h
  | select φ e ih =>
      cases hE : e.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, hE] at h
      | some m =>
          have hClean := ih hE
          by_cases hReq : φ.arityReq < m
          · simp [RawRAExpr.arity?, hE, hReq] at h
            subst n
            simp [cleanVacuousProjections, RawRAExpr.arity?,
              hClean, hReq]
          · simp [RawRAExpr.arity?, hE, hReq] at h
  | proj idxs e ih =>
      cases hE : e.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, hE] at h
      | some m =>
          by_cases hIdx : ∀ i ∈ idxs, i < m
          · have hn : idxs.length = n := by
              have hDec :
                  decide (∀ i ∈ idxs, i < m) = true :=
                decide_eq_true hIdx
              have hSome :
                  some idxs.length = some n := by
                simpa [arity?, hE, hDec] using h
              exact Option.some.inj hSome
            have hClean := ih hE
            simp only [cleanVacuousProjections]
            rw [hClean]
            by_cases hRange : idxs = List.range m
            · have hm : m = n := by
                subst idxs
                simpa [List.length_range] using hn
              subst n
              simpa [hRange, List.length_range] using hClean
            · subst n
              have hDec :
                  decide (∀ i ∈ idxs, i < m) = true :=
                decide_eq_true hIdx
              simp [hRange, RawRAExpr.arity?, hClean, hDec]
          · simp [RawRAExpr.arity?, hE, hIdx] at h
  | prod e₁ e₂ ih₁ ih₂ =>
      cases h₁ : e₁.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, h₁] at h
      | some n₁ =>
          cases h₂ : e₂.arity? Γ with
          | none =>
              simp [RawRAExpr.arity?, h₁, h₂] at h
          | some n₂ =>
              have hClean₁ := ih₁ h₁
              have hClean₂ := ih₂ h₂
              simp [RawRAExpr.arity?, h₁, h₂] at h
              subst n
              simp [cleanVacuousProjections, arity?,
                hClean₁, hClean₂]
  | union e₁ e₂ ih₁ ih₂ =>
      cases h₁ : e₁.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, h₁] at h
      | some n₁ =>
          cases h₂ : e₂.arity? Γ with
          | none =>
              simp [RawRAExpr.arity?, h₁, h₂] at h
          | some n₂ =>
              by_cases hEq : n₁ = n₂
              · have hClean₁ := ih₁ h₁
                have hClean₂ := ih₂ h₂
                simp [arity?, h₁, h₂, hEq] at h
                subst n
                subst n₂
                simp [cleanVacuousProjections, arity?,
                  hClean₁, hClean₂]
              · simp [arity?, h₁, h₂, hEq] at h
  | diff e₁ e₂ ih₁ ih₂ =>
      cases h₁ : e₁.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, h₁] at h
      | some n₁ =>
          cases h₂ : e₂.arity? Γ with
          | none =>
              simp [RawRAExpr.arity?, h₁, h₂] at h
          | some n₂ =>
              by_cases hEq : n₁ = n₂
              · have hClean₁ := ih₁ h₁
                have hClean₂ := ih₂ h₂
                simp [arity?, h₁, h₂, hEq] at h
                subst n
                subst n₂
                simp [cleanVacuousProjections, arity?,
                  hClean₁, hClean₂]
              · simp [arity?, h₁, h₂, hEq] at h

/-
  Projection cleanup preserves raw evaluation on well-
  formed expressions.
-/
theorem eval?_cleanProjections
    {Γ : UnnamedSchema A}
    (I : Instance D Γ)
    {e : RawRAExpr A D}
    {n : Nat}
    (h : e.arity? Γ = some n) :
    (e.cleanVacuousProjections Γ).eval? I = e.eval? I := by
  induction e generalizing n with
  | top =>
      simp [cleanVacuousProjections, eval?]
  | empty m =>
      simp [cleanVacuousProjections, eval?]
  | rel X =>
      simp [cleanVacuousProjections, eval?]
  | single d =>
      simp [cleanVacuousProjections, eval?]
  | select φ e ih =>
      cases hE : e.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, hE] at h
      | some m =>
          by_cases hReq : φ.arityReq < m
          · have hEval := ih hE
            have hClean :=
              arity?_cleanProjections Γ hE
            rcases RawRAExpr.wf_total I hClean with
              ⟨Rclean, hRclean⟩
            have hR :
                e.eval? I = some ⟨m, Rclean⟩ := by
              rw [← hEval]
              exact hRclean
            simp [cleanVacuousProjections, RawRAExpr.eval?,
              hRclean, hR, hReq]
          · simp [RawRAExpr.arity?, hE, hReq] at h
  | proj idxs e ih =>
      cases hE : e.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, hE] at h
      | some m =>
          by_cases hIdx : ∀ i ∈ idxs, i < m
          · have hn : idxs.length = n := by
              have hDec :
                  decide (∀ i ∈ idxs, i < m) = true :=
                decide_eq_true hIdx
              have hSome :
                  some idxs.length = some n := by
                simpa [arity?, hE, hDec] using h
              exact Option.some.inj hSome
            have hEval := ih hE
            have hClean :=
              arity?_cleanProjections Γ hE
            simp only [cleanVacuousProjections]
            rw [hClean]
            by_cases hRange : idxs = List.range m
            · subst idxs
              have hm : m = n := by
                simpa [List.length_range] using hn
              subst n
              rcases RawRAExpr.wf_total I hE with
                ⟨R, hR⟩
              simp only [↓reduceIte]
              rw [hEval, hR]
              simp only [RawRAExpr.eval?]
              rw [hR]
              simp only [List.mem_range, imp_self,
                implies_true, ↓reduceDIte,
                Option.some.injEq,
                Sigma.mk.injEq, List.length_range, true_and]
              exact
                (heq_of_cast_eq
                  (congrArg (FinRelation D)
                    (by simp [List.length_range] :
                      (List.range m).length = m))
                  (FinRelation.proj_range_eq R hIdx)).symm
            · subst n
              simp [hRange]
              simp [RawRAExpr.eval?, hEval]
          · simp [RawRAExpr.arity?, hE, hIdx] at h
  | prod e₁ e₂ ih₁ ih₂ =>
      cases h₁ : e₁.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, h₁] at h
      | some n₁ =>
          cases h₂ : e₂.arity? Γ with
          | none =>
              simp [RawRAExpr.arity?, h₁, h₂] at h
          | some n₂ =>
              have hEval₁ := ih₁ h₁
              have hEval₂ := ih₂ h₂
              simp [cleanVacuousProjections, eval?,
                hEval₁, hEval₂]
  | union e₁ e₂ ih₁ ih₂ =>
      cases h₁ : e₁.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, h₁] at h
      | some n₁ =>
          cases h₂ : e₂.arity? Γ with
          | none =>
              simp [RawRAExpr.arity?, h₁, h₂] at h
          | some n₂ =>
              by_cases hEq : n₁ = n₂
              · subst hEq
                have hEval₁ := ih₁ h₁
                have hEval₂ := ih₂ h₂
                simp [cleanVacuousProjections, eval?,
                  hEval₁, hEval₂]
              · simp [arity?, h₁, h₂, hEq] at h
  | diff e₁ e₂ ih₁ ih₂ =>
      cases h₁ : e₁.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, h₁] at h
      | some n₁ =>
          cases h₂ : e₂.arity? Γ with
          | none =>
              simp [RawRAExpr.arity?, h₁, h₂] at h
          | some n₂ =>
              by_cases hEq : n₁ = n₂
              · subst hEq
                have hEval₁ := ih₁ h₁
                have hEval₂ := ih₂ h₂
                simp [cleanVacuousProjections, eval?,
                  hEval₁, hEval₂]
              · simp [arity?, h₁, h₂, hEq] at h

/- Full raw cleanup used by generated Whiel programs. -/
def clean
    (Γ : UnnamedSchema A)
    (e : RawRAExpr A D) :
    RawRAExpr A D :=
  ((e.cleanVacuousProducts.cleanVacuousUnions)
    |>.cleanVacuousProjections Γ)
    |>.mergeSelections

/-
  Full cleanup preserves arity for well-formed raw
  expressions.
-/
theorem arity?_clean_of_eq_some
    (Γ : UnnamedSchema A)
    {e : RawRAExpr A D}
    {n : Nat}
    (h : e.arity? Γ = some n) :
    (e.clean Γ).arity? Γ = some n := by
  unfold clean
  rw [arity?_mergeSelections]
  apply arity?_cleanProjections
  apply arity?_cleanUnions
  rw [arity?_cleanVacuousProducts]
  exact h

/-
  Full cleanup preserves raw evaluation on well-formed
  expressions.
-/
theorem eval?_clean_of_eq_some
    {Γ : UnnamedSchema A}
    (I : Instance D Γ)
    {e : RawRAExpr A D}
    {n : Nat}
    (h : e.arity? Γ = some n) :
    (e.clean Γ).eval? I = e.eval? I := by
  unfold clean
  have hProdAr :
      e.cleanVacuousProducts.arity? Γ = some n := by
    rw [arity?_cleanVacuousProducts]
    exact h
  have hUnionAr :
      e.cleanVacuousProducts.cleanVacuousUnions.arity? Γ =
        some n :=
    arity?_cleanUnions Γ hProdAr
  rw [eval?_mergeSelections]
  rw [eval?_cleanProjections I hUnionAr]
  rw [eval?_cleanUnions I hProdAr]
  exact eval?_cleanVacuousProducts I e

end RawRAExpr

------------------------------------------------------------
-- Well-Formed Expression Cleaning
------------------------------------------------------------

namespace RAExpr

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Merge adjacent selections without changing arity. -/
def mergeSelections
    {n : Nat}
    (e : RAExpr D Γ n) : RAExpr D Γ n where
  expr := e.expr.mergeSelections
  wf := by
    rw [RawRAExpr.arity?_mergeSelections]
    exact e.wf

/-
  Remove right-products by `top` without changing output
  arity.
-/
def cleanVacuousProducts
    {n : Nat}
    (e : RAExpr D Γ n) :
    RAExpr D Γ n where
  expr := e.expr.cleanVacuousProducts
  wf := by
    rw [RawRAExpr.arity?_cleanVacuousProducts]
    exact e.wf

/-
  Remove same-arity unions with `empty` without changing
  output arity.
-/
def cleanVacuousUnions
    {n : Nat}
    (e : RAExpr D Γ n) :
    RAExpr D Γ n where
  expr := e.expr.cleanVacuousUnions
  wf :=
    RawRAExpr.arity?_cleanUnions
      Γ e.wf

/-
  Remove identity projections without changing output
  arity.
-/
def cleanVacuousProjections
    {n : Nat}
    (e : RAExpr D Γ n) :
    RAExpr D Γ n where
  expr := e.expr.cleanVacuousProjections Γ
  wf :=
    RawRAExpr.arity?_cleanProjections
      Γ e.wf

/-
  Clean an RA expression without changing its output
  arity.
-/
def clean
    {n : Nat}
    (e : RAExpr D Γ n) :
    RAExpr D Γ n :=
  e.cleanVacuousProducts
    |>.cleanVacuousUnions
    |>.cleanVacuousProjections
    |>.mergeSelections

/- Selection merging preserves RA evaluation. -/
@[simp] theorem eval_mergeSelections
    {n : Nat}
    (e : RAExpr D Γ n)
    (I : Instance D Γ) :
    e.mergeSelections.eval I = e.eval I := by
  have hRaw :=
    RawRAExpr.eval?_mergeSelections I e.expr
  have hMergedSpec :
      e.expr.mergeSelections.eval? I =
        some ⟨n, e.mergeSelections.eval I⟩ := by
    simpa [RAExpr.mergeSelections] using
      RAExpr.raw_eval?_eq_eval e.mergeSelections I
  rw [hMergedSpec, RAExpr.raw_eval?_eq_eval e I] at hRaw
  have hSigma :
      (⟨n, e.mergeSelections.eval I⟩ :
          Sigma (FinRelation D)) =
        ⟨n, e.eval I⟩ :=
    Option.some.inj hRaw
  simpa using (Sigma.mk.inj_iff.mp hSigma).2

/- Product cleanup preserves RA evaluation. -/
@[simp] theorem eval_cleanVacuousProducts
    {n : Nat}
    (e : RAExpr D Γ n)
    (I : Instance D Γ) :
    e.cleanVacuousProducts.eval I = e.eval I := by
  have hRaw := RawRAExpr.eval?_cleanVacuousProducts I e.expr
  have hCleanSpec :
      e.expr.cleanVacuousProducts.eval? I =
        some ⟨n, e.cleanVacuousProducts.eval I⟩ := by
    simpa [RAExpr.cleanVacuousProducts] using
      RAExpr.raw_eval?_eq_eval e.cleanVacuousProducts I
  rw [hCleanSpec, RAExpr.raw_eval?_eq_eval e I] at hRaw
  have hSigma :
      (⟨n, e.cleanVacuousProducts.eval I⟩ :
          Sigma (FinRelation D)) =
        ⟨n, e.eval I⟩ :=
    Option.some.inj hRaw
  simpa using (Sigma.mk.inj_iff.mp hSigma).2

/- Union cleanup preserves RA evaluation. -/
@[simp] theorem eval_cleanVacuousUnions
    {n : Nat}
    (e : RAExpr D Γ n)
    (I : Instance D Γ) :
    e.cleanVacuousUnions.eval I = e.eval I := by
  have hRaw :=
    RawRAExpr.eval?_cleanUnions
      I e.wf
  have hCleanSpec :
      e.expr.cleanVacuousUnions.eval? I =
        some ⟨n, e.cleanVacuousUnions.eval I⟩ := by
    simpa [RAExpr.cleanVacuousUnions] using
      RAExpr.raw_eval?_eq_eval e.cleanVacuousUnions I
  rw [hCleanSpec, RAExpr.raw_eval?_eq_eval e I] at hRaw
  have hSigma :
      (⟨n, e.cleanVacuousUnions.eval I⟩ :
          Sigma (FinRelation D)) =
        ⟨n, e.eval I⟩ :=
    Option.some.inj hRaw
  simpa using (Sigma.mk.inj_iff.mp hSigma).2

/- Projection cleanup preserves RA evaluation. -/
@[simp] theorem eval_cleanVacuousProjections
    {n : Nat}
    (e : RAExpr D Γ n)
    (I : Instance D Γ) :
    e.cleanVacuousProjections.eval I = e.eval I := by
  have hRaw :=
    RawRAExpr.eval?_cleanProjections
      I e.wf
  have hCleanSpec :
      (e.expr.cleanVacuousProjections Γ).eval? I =
        some ⟨n, e.cleanVacuousProjections.eval I⟩ := by
    simpa [RAExpr.cleanVacuousProjections] using
      RAExpr.raw_eval?_eq_eval e.cleanVacuousProjections I
  rw [hCleanSpec, RAExpr.raw_eval?_eq_eval e I] at hRaw
  have hSigma :
      (⟨n, e.cleanVacuousProjections.eval I⟩ :
          Sigma (FinRelation D)) =
        ⟨n, e.eval I⟩ :=
    Option.some.inj hRaw
  simpa using (Sigma.mk.inj_iff.mp hSigma).2

/- Cleaning preserves RA evaluation. -/
@[simp] theorem eval_clean
    {n : Nat}
    (e : RAExpr D Γ n)
    (I : Instance D Γ) :
    e.clean.eval I = e.eval I := by
  simp [clean]

end RAExpr
