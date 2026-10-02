-- Author: Jesse Comer
import Databases.UnnamedRA.Semantics
import Mathlib.Data.Finset.Sort
import Std.Data.HashSet.Lemmas
import Whiel.Eval.RA.Normalize

/-
  Materialized relational-algebra evaluation for Whiel.

  The runtime view stores sorted, duplicate-free tuple lists
  together with a whole-tuple membership index.  The proof
  interface is `toFinRelation`, and the main theorem states
  that fast evaluation agrees with `RAExpr.eval`.
-/

------------------------------------------------------------
-- Tuple Membership Indexes
------------------------------------------------------------

namespace Whiel

structure FastMemberIndex
    (D : Type)
    [DecidableEq D]
    [Hashable D]
    (n : Nat) where
  set : Std.HashSet (Tuple D n)

namespace FastMemberIndex

variable {D : Type}
variable [LinearOrder D] [DecidableEq D] [Hashable D]

/- Empty tuple membership index. -/
def empty {n : Nat} : FastMemberIndex D n where
  set := ∅

/- Boolean membership lookup. -/
def contains
    {n : Nat}
    (idx : FastMemberIndex D n)
    (t : Tuple D n) : Bool :=
  idx.set.contains t

/- Insert a tuple into the membership index. -/
def insert
    {n : Nat}
    (u : Tuple D n)
    (idx : FastMemberIndex D n) :
    FastMemberIndex D n where
  set := idx.set.insert u

/- Build a membership index from tuple data. -/
def ofList {n : Nat} :
    List (Tuple D n) → FastMemberIndex D n :=
  List.foldl (fun idx u => insert u idx) empty

omit [LinearOrder D] in
theorem contains_insert_iff
    {n : Nat}
    (idx : FastMemberIndex D n)
    (u t : Tuple D n) :
    (insert u idx).contains t = true ↔
      t = u ∨ idx.contains t = true := by
  unfold insert contains
  rw [Std.HashSet.contains_insert]
  by_cases h : u = t
  · subst h
    simp
  · have hBeq : (u == t) = false := by
      cases hEq : (u == t)
      · rfl
      · exact False.elim (h (LawfulBEq.eq_of_beq hEq))
    have hSym : t ≠ u := by
      intro htu
      exact h htu.symm
    simp [hBeq, hSym]

omit [LinearOrder D] in
theorem contains_foldl_insert_iff
    {n : Nat}
    (ts : List (Tuple D n))
    (idx : FastMemberIndex D n)
    (t : Tuple D n) :
    (ts.foldl (fun idx u => insert u idx) idx).contains t =
        true ↔
      idx.contains t = true ∨ t ∈ ts := by
  induction ts generalizing idx with
  | nil =>
      simp
  | cons u us ih =>
      rw [List.foldl_cons, ih, contains_insert_iff]
      constructor
      · intro h
        rcases h with hHeadOrIdx | hTail
        · rcases hHeadOrIdx with hEq | hIdx
          · exact Or.inr (List.mem_cons.mpr (Or.inl hEq))
          · exact Or.inl hIdx
        · exact Or.inr (List.mem_cons.mpr (Or.inr hTail))
      · intro h
        rcases h with hIdx | hMem
        · exact Or.inl (Or.inr hIdx)
        · rcases List.mem_cons.mp hMem with hEq | hTail
          · exact Or.inl (Or.inl hEq)
          · exact Or.inr hTail

omit [LinearOrder D] in
theorem contains_ofList_iff
    {n : Nat}
    (ts : List (Tuple D n))
    (t : Tuple D n) :
    (ofList ts).contains t = true ↔ t ∈ ts := by
  rw [ofList, contains_foldl_insert_iff]
  constructor
  · intro h
    rcases h with hEmpty | hMem
    · simp [empty, contains] at hEmpty
    · exact hMem
  · exact Or.inr

end FastMemberIndex

end Whiel

------------------------------------------------------------
-- Materialized Relations
------------------------------------------------------------

namespace Whiel

structure FastRelation
    (D : Type)
    [Domain D]
    [LinearOrder D]
    [Hashable D]
    (n : Nat) where
  tuples : List (Tuple D n)
  nodup_tuples : tuples.Nodup
  memberIndex : FastMemberIndex D n
  memberIndex_mem :
    ∀ t : Tuple D n,
      memberIndex.contains t = true ↔ t ∈ tuples

namespace FastRelation

variable {D : Type}
variable [Domain D] [LinearOrder D] [Hashable D]

/- Build a materialized relation from executable tuples. -/
def ofList
    {n : Nat}
    (ts : List (Tuple D n)) :
    FastRelation D n :=
  let us := TupleNormalize.normalize ts
  { tuples := us
    nodup_tuples := TupleNormalize.nodup_normalize ts
    memberIndex := FastMemberIndex.ofList us
    memberIndex_mem := by
      intro t
      exact FastMemberIndex.contains_ofList_iff us t }

/- Direct finite-relation view of a materialized relation. -/
def toFinRelation
    {n : Nat}
    (R : FastRelation D n) :
    FinRelation D n :=
  ⟨R.tuples, R.nodup_tuples⟩

theorem mem_toFinRelation_iff
    {n : Nat}
    (R : FastRelation D n)
    (t : Tuple D n) :
    t ∈ R.toFinRelation ↔ t ∈ R.tuples := by
  rfl

theorem mem_ofList_iff
    {n : Nat}
    (ts : List (Tuple D n))
    (t : Tuple D n) :
    t ∈ (ofList ts).toFinRelation ↔ t ∈ ts := by
  unfold ofList toFinRelation
  simp [TupleNormalize.mem_normalize_iff]

/- Build a materialized relation from a proof-facing relation. -/
def ofFinRelation
    {n : Nat}
    (R : FinRelation D n) :
    FastRelation D n :=
  ofList R.sort

theorem ofFinRelation_correct
    {n : Nat}
    (R : FinRelation D n) :
    (ofFinRelation R).toFinRelation = R := by
  apply Finset.ext
  intro t
  simp [ofFinRelation, mem_ofList_iff]

/- Empty materialized relation. -/
def empty (n : Nat) : FastRelation D n :=
  ofList []

@[simp] theorem empty_correct
    (n : Nat) :
    (empty (D := D) n).toFinRelation =
      (∅ : FinRelation D n) := by
  apply Finset.ext
  intro t
  simp [empty, mem_ofList_iff]

/- Materialized relation with one empty tuple. -/
def top : FastRelation D 0 :=
  ofFinRelation FinRelation.top

@[simp] theorem top_correct :
    (top (D := D)).toFinRelation = FinRelation.top :=
  ofFinRelation_correct FinRelation.top

/- Materialized unary singleton. -/
def single (d : D) : FastRelation D 1 :=
  ofFinRelation (FinRelation.single d)

@[simp] theorem single_correct
    (d : D) :
    (single d).toFinRelation = FinRelation.single d :=
  ofFinRelation_correct (FinRelation.single d)

/- Cast a materialized relation across an arity equality. -/
def castArity
    {m n : Nat}
    (h : m = n)
    (R : FastRelation D m) :
    FastRelation D n := by
  cases h
  exact R

@[simp] theorem castArity_toFinRelation
    {m n : Nat}
    (h : m = n)
    (R : FastRelation D m) :
    (castArity h R).toFinRelation =
      cast (by cases h; rfl) R.toFinRelation := by
  cases h
  rfl

/- Fast whole-tuple membership lookup. -/
def contains
    {n : Nat}
    (R : FastRelation D n)
    (t : Tuple D n) : Bool :=
  R.memberIndex.contains t

theorem contains_iff
    {n : Nat}
    (R : FastRelation D n)
    (t : Tuple D n) :
    R.contains t = true ↔ t ∈ R.toFinRelation := by
  rw [contains, R.memberIndex_mem, mem_toFinRelation_iff]

/- Selection by a decidable tuple predicate. -/
def select
    {n : Nat}
    (p : Tuple D n → Prop)
    [DecidablePred p]
    (R : FastRelation D n) :
    FastRelation D n :=
  ofList (R.tuples.filter p)

theorem select_correct
    {n : Nat}
    (p : Tuple D n → Prop)
    [DecidablePred p]
    (R : FastRelation D n) :
    (select p R).toFinRelation =
      FinRelation.select p R.toFinRelation := by
  apply Finset.ext
  intro t
  change t ∈ (ofList (R.tuples.filter p)).toFinRelation ↔
    t ∈ FinRelation.select p R.toFinRelation
  rw [mem_ofList_iff, FinRelation.mem_select_iff,
    mem_toFinRelation_iff]
  simp

/- Projection along a list of indices. -/
def proj
    {n : Nat}
    (idxs : List Nat)
    (R : FastRelation D n)
    (h : ∀ i ∈ idxs, i < n) :
    FastRelation D idxs.length :=
  ofList (R.tuples.map
    (fun t => FinRelation.projTuple idxs t h))

theorem proj_correct
    {n : Nat}
    (idxs : List Nat)
    (R : FastRelation D n)
    (h : ∀ i ∈ idxs, i < n) :
    (proj idxs R h).toFinRelation =
      FinRelation.proj idxs R.toFinRelation h := by
  apply Finset.ext
  intro t
  change t ∈ (ofList (R.tuples.map
      (fun t => FinRelation.projTuple idxs t h))).toFinRelation ↔
    t ∈ FinRelation.proj idxs R.toFinRelation h
  rw [mem_ofList_iff, FinRelation.mem_proj_iff]
  constructor
  · intro ht
    rcases List.mem_map.mp ht with ⟨s, hs, hEq⟩
    exact ⟨s, (mem_toFinRelation_iff R s).mpr hs, hEq⟩
  · rintro ⟨s, hs, hEq⟩
    exact List.mem_map.mpr
      ⟨s, (mem_toFinRelation_iff R s).mp hs, hEq⟩

/- Relational product. -/
def prod
    {n m : Nat}
    (R : FastRelation D n)
    (S : FastRelation D m) :
  FastRelation D (n + m) :=
  ofList ((R.tuples.product S.tuples).map
    (fun p => FinRelation.appendTuple p.1 p.2))

theorem prod_correct
    {n m : Nat}
    (R : FastRelation D n)
    (S : FastRelation D m) :
    (prod R S).toFinRelation =
      FinRelation.prod R.toFinRelation S.toFinRelation := by
  apply Finset.ext
  intro t
  change t ∈ (ofList ((R.tuples.product S.tuples).map
      (fun p => FinRelation.appendTuple p.1 p.2))).toFinRelation ↔
    t ∈ FinRelation.prod R.toFinRelation S.toFinRelation
  rw [mem_ofList_iff, FinRelation.mem_prod_iff]
  constructor
  · intro ht
    rcases List.mem_map.mp ht with ⟨p, hp, hEq⟩
    rcases List.mem_product.mp hp with ⟨h₁, h₂⟩
    exact
      ⟨p.1, (mem_toFinRelation_iff R p.1).mpr h₁,
        p.2, (mem_toFinRelation_iff S p.2).mpr h₂,
        hEq⟩
  · rintro ⟨t₁, ht₁, t₂, ht₂, hEq⟩
    exact List.mem_map.mpr
      ⟨(t₁, t₂),
        List.mem_product.mpr
          ⟨(mem_toFinRelation_iff R t₁).mp ht₁,
            (mem_toFinRelation_iff S t₂).mp ht₂⟩,
        hEq⟩

/- Relational union. -/
def union
    {n : Nat}
    (R S : FastRelation D n) :
    FastRelation D n :=
  ofList (R.tuples ++ S.tuples)

theorem union_correct
    {n : Nat}
    (R S : FastRelation D n) :
    (union R S).toFinRelation =
      FinRelation.union R.toFinRelation S.toFinRelation := by
  apply Finset.ext
  intro t
  change t ∈ (ofList (R.tuples ++ S.tuples)).toFinRelation ↔
    t ∈ FinRelation.union R.toFinRelation S.toFinRelation
  rw [mem_ofList_iff, FinRelation.mem_union_iff]
  simp [mem_toFinRelation_iff]

/- Relational difference using the membership index. -/
def diff
    {n : Nat}
    (R S : FastRelation D n) :
    FastRelation D n :=
  ofList (R.tuples.filter
    (fun t => !(S.contains t)))

theorem diff_correct
    {n : Nat}
    (R S : FastRelation D n) :
    (diff R S).toFinRelation =
      FinRelation.diff R.toFinRelation S.toFinRelation := by
  apply Finset.ext
  intro t
  change t ∈ (ofList (R.tuples.filter
      (fun t => !(S.contains t)))).toFinRelation ↔
    t ∈ FinRelation.diff R.toFinRelation S.toFinRelation
  rw [mem_ofList_iff, FinRelation.mem_diff_iff,
    mem_toFinRelation_iff]
  constructor
  · intro ht
    rcases List.mem_filter.mp ht with ⟨hR, hNot⟩
    refine ⟨hR, ?_⟩
    intro hS
    have hContains : S.contains t = true :=
      (contains_iff S t).mpr hS
    simp [hContains] at hNot
  · rintro ⟨hR, hNotS⟩
    apply List.mem_filter.mpr
    refine ⟨hR, ?_⟩
    have hContainsFalse : S.contains t = false := by
      cases hContains : S.contains t
      · rfl
      · have hS : t ∈ S.toFinRelation :=
          (contains_iff S t).mp hContains
        exact False.elim (hNotS hS)
    simp [hContainsFalse]

/- Boolean subset test backed by tuple membership. -/
def subsetList
    {n : Nat}
    (xs : List (Tuple D n))
    (S : FastRelation D n) : Bool :=
  match xs with
  | [] => true
  | t :: ts =>
      if S.contains t then
        subsetList ts S
      else
        false

theorem subsetList_iff
    {n : Nat}
    (xs : List (Tuple D n))
    (S : FastRelation D n) :
    subsetList xs S = true ↔
      ∀ t ∈ xs, t ∈ S.toFinRelation := by
  induction xs with
  | nil =>
      simp [subsetList]
  | cons t ts ih =>
      by_cases hContains : S.contains t = true
      · constructor
        · intro hSub u hu
          have hTail : subsetList ts S = true := by
            simpa [subsetList, hContains] using hSub
          have huCases := (List.mem_cons.mp hu)
          rcases huCases with hEq | huTail
          · cases hEq
            exact (contains_iff S t).mp hContains
          · exact ih.mp hTail u huTail
        · intro hAll
          have hTail :
              ∀ u ∈ ts, u ∈ S.toFinRelation := by
            intro u hu
            exact hAll u (List.mem_cons_of_mem t hu)
          change
            (if S.contains t then subsetList ts S else false) =
              true
          rw [hContains]
          exact ih.mpr hTail
      · have hFalse : S.contains t = false := by
          cases h : S.contains t
          · rfl
          · exact False.elim (hContains h)
        constructor
        · intro hSub
          change
            (if S.contains t then subsetList ts S else false) =
              true at hSub
          rw [hFalse] at hSub
          cases hSub
        · intro hAll
          have ht : t ∈ S.toFinRelation :=
            hAll t (by simp)
          have hTrue : S.contains t = true :=
            (contains_iff S t).mpr ht
          rw [hFalse] at hTrue
          cases hTrue

/- Boolean subset test. -/
def subset
    {n : Nat}
    (R S : FastRelation D n) : Bool :=
  subsetList R.tuples S

theorem subset_iff
    {n : Nat}
    (R S : FastRelation D n) :
    subset R S = true ↔
      R.toFinRelation ⊆ S.toFinRelation := by
  rw [subset, subsetList_iff]
  constructor
  · intro h t ht
    exact h t ((mem_toFinRelation_iff R t).mp ht)
  · intro h t ht
    exact h ((mem_toFinRelation_iff R t).mpr ht)

/- Boolean equality test. -/
def equal
    {n : Nat}
    (R S : FastRelation D n) : Bool :=
  subset R S && subset S R

theorem equal_iff
    {n : Nat}
    (R S : FastRelation D n) :
    equal R S = true ↔
      R.toFinRelation = S.toFinRelation := by
  unfold equal
  rw [Bool.and_eq_true, subset_iff, subset_iff]
  constructor
  · intro h
    exact Finset.Subset.antisymm h.1 h.2
  · intro h
    constructor
    · intro t ht
      simpa [h] using ht
    · intro t ht
      simpa [h] using ht

end FastRelation

end Whiel

------------------------------------------------------------
-- Materialized Instances
------------------------------------------------------------

namespace Whiel

structure FastInstance
    {A : Type} [RelationNames A]
    (D : Type)
    [Domain D] [LinearOrder D] [Hashable D]
    (Γ : UnnamedSchema A) where
  relation :
    (X : Γ.syms) → FastRelation D (Γ.arity X)

namespace FastInstance

variable {A D : Type}
variable [RelationNames A]
variable [Domain D] [LinearOrder D] [Hashable D]
variable {Γ : UnnamedSchema A}

/- Proof-facing instance view. -/
def toInstance
    (S : FastInstance D Γ) :
    Instance D Γ :=
  fun X => (S.relation X).toFinRelation

/- Build a materialized instance from a proof-facing one. -/
def ofInstance
    (I : Instance D Γ) :
    FastInstance D Γ where
  relation := fun X => FastRelation.ofFinRelation (I X)

@[simp] theorem toInstance_ofInstance
    (I : Instance D Γ) :
    (ofInstance I).toInstance = I := by
  ext X
  simp [ofInstance, toInstance,
    FastRelation.ofFinRelation_correct]

/- Relation lookup by raw symbol. -/
def relation?
    (S : FastInstance D Γ)
    (X : A) :
    Option (Sigma (FastRelation D)) :=
  if hX : X ∈ Γ.syms then
    some ⟨Γ.arity ⟨X, hX⟩, S.relation ⟨X, hX⟩⟩
  else
    none

theorem relation?_correct
    (S : FastInstance D Γ)
    (X : A) :
    match S.relation? X with
    | none => S.toInstance.relation? X = none
    | some ⟨n, R⟩ =>
        S.toInstance.relation? X =
          some ⟨n, R.toFinRelation⟩ := by
  by_cases hX : X ∈ Γ.syms
  · simp [relation?, Instance.relation?, toInstance, hX]
  · simp [relation?, Instance.relation?, hX]

/- Update one materialized relation. -/
def update
    (S : FastInstance D Γ)
    (X : Γ.syms)
    (R : FastRelation D (Γ.arity X)) :
    FastInstance D Γ where
  relation := fun Y =>
    if h : Y = X then
      FastRelation.castArity
        (by cases h; rfl) R
    else
      S.relation Y

theorem toInstance_update
    (S : FastInstance D Γ)
    (X : Γ.syms)
    (R : FastRelation D (Γ.arity X)) :
    (S.update X R).toInstance =
      Instance.update S.toInstance X R.toFinRelation := by
  ext Y
  by_cases h : Y = X
  · subst h
    simp [update, toInstance, Instance.update]
  · simp [update, toInstance, Instance.update, h]

end FastInstance

end Whiel

------------------------------------------------------------
-- Fast RA Evaluation
------------------------------------------------------------

namespace Whiel

namespace FastRA

variable {A D : Type}
variable [RelationNames A]
variable [Domain D] [LinearOrder D] [Hashable D]
variable {Γ : UnnamedSchema A}

/- Raw fast RA evaluation over materialized instances. -/
def evalRaw?
    (e : RawRAExpr A D)
    (S : FastInstance D Γ) :
    Option (Sigma (FastRelation D)) :=
  match e with
  | .top =>
      some ⟨0, FastRelation.top⟩
  | .empty n =>
      some ⟨n, FastRelation.empty n⟩
  | .rel X =>
      S.relation? X
  | .single d =>
      some ⟨1, FastRelation.single d⟩
  | .select φ e =>
      match evalRaw? e S with
      | some ⟨n, R⟩ =>
          if hReq : φ.arityReq < n then
            some ⟨n,
              FastRelation.select
                (fun t => Sel.Holds φ t) R⟩
          else
            none
      | none => none
  | .proj idxs e =>
      match evalRaw? e S with
      | some ⟨n, R⟩ =>
          if hOk : ∀ i ∈ idxs, i < n then
            some ⟨idxs.length,
              FastRelation.proj idxs R hOk⟩
          else
            none
      | none => none
  | .prod e₁ e₂ =>
      match evalRaw? e₁ S, evalRaw? e₂ S with
      | some ⟨n, R⟩, some ⟨m, T⟩ =>
          some ⟨n + m, FastRelation.prod R T⟩
      | _, _ => none
  | .union e₁ e₂ =>
      match evalRaw? e₁ S, evalRaw? e₂ S with
      | some ⟨n, R⟩, some ⟨m, T⟩ =>
          if hEq : n = m then
            by
              subst hEq
              exact some ⟨n, FastRelation.union R T⟩
          else
            none
      | _, _ => none
  | .diff e₁ e₂ =>
      match evalRaw? e₁ S, evalRaw? e₂ S with
      | some ⟨n, R⟩, some ⟨m, T⟩ =>
          if hEq : n = m then
            by
              subst hEq
              exact some ⟨n, FastRelation.diff R T⟩
          else
            none
      | _, _ => none

/- Typed fast RA evaluation. -/
def eval
    {n : Nat}
    (e : RAExpr D Γ n)
    (S : FastInstance D Γ) :
    FastRelation D n :=
  match evalRaw? e.expr S with
  | none => FastRelation.empty n
  | some ⟨m, R⟩ =>
      if hm : m = n then
        FastRelation.castArity hm R
      else
        FastRelation.empty n

end FastRA

end Whiel

------------------------------------------------------------
-- Fast RA Evaluation Correctness
------------------------------------------------------------

namespace Whiel

namespace FastRA

variable {A D : Type}
variable [RelationNames A]
variable [Domain D] [LinearOrder D] [Hashable D]
variable {Γ : UnnamedSchema A}

theorem evalRaw?_correct
    (e : RawRAExpr A D)
    (S : FastInstance D Γ) :
    match evalRaw? e S with
    | none =>
        e.eval? (Γ := Γ) S.toInstance = none
    | some ⟨n, R⟩ =>
        e.eval? (Γ := Γ) S.toInstance =
          some ⟨n, R.toFinRelation⟩ := by
  induction e with
  | top =>
      simp [evalRaw?, RawRAExpr.eval?]
  | empty n =>
      simp [evalRaw?, RawRAExpr.eval?,
        FastRelation.empty_correct]
  | rel X =>
      exact S.relation?_correct X
  | single d =>
      simp [evalRaw?, RawRAExpr.eval?]
  | select φ e ih =>
      simp only [evalRaw?]
      cases h : evalRaw? e S with
      | none =>
          have ih' := ih
          rw [h] at ih'
          simp [RawRAExpr.eval?, ih']
      | some r =>
          rcases r with ⟨n, R⟩
          have ih' := ih
          rw [h] at ih'
          by_cases hReq : φ.arityReq < n
          · simp [RawRAExpr.eval?, ih', hReq,
              FastRelation.select_correct]
          · simp [RawRAExpr.eval?, ih', hReq]
  | proj idxs e ih =>
      cases h : evalRaw? e S with
      | none =>
          have ih' := ih
          rw [h] at ih'
          simp [evalRaw?, RawRAExpr.eval?, h, ih']
      | some r =>
          rcases r with ⟨n, R⟩
          have ih' := ih
          rw [h] at ih'
          by_cases hOk : ∀ i ∈ idxs, i < n
          · simp only [evalRaw?, RawRAExpr.eval?, h, ih']
            rw [dif_pos hOk]
            rw [dif_pos hOk]
            simp [FastRelation.proj_correct]
          · simp [evalRaw?, RawRAExpr.eval?, h, ih', hOk]
  | prod e₁ e₂ ih₁ ih₂ =>
      simp only [evalRaw?]
      cases h₁ : evalRaw? e₁ S with
      | none =>
          have ih₁' := ih₁
          rw [h₁] at ih₁'
          simp [RawRAExpr.eval?, ih₁']
      | some r₁ =>
          rcases r₁ with ⟨n, R⟩
          have ih₁' := ih₁
          rw [h₁] at ih₁'
          cases h₂ : evalRaw? e₂ S with
          | none =>
              have ih₂' := ih₂
              rw [h₂] at ih₂'
              simp [RawRAExpr.eval?, ih₁', ih₂']
          | some r₂ =>
              rcases r₂ with ⟨m, T⟩
              have ih₂' := ih₂
              rw [h₂] at ih₂'
              simp [RawRAExpr.eval?, ih₁', ih₂',
                FastRelation.prod_correct]
  | union e₁ e₂ ih₁ ih₂ =>
      simp only [evalRaw?]
      cases h₁ : evalRaw? e₁ S with
      | none =>
          have ih₁' := ih₁
          rw [h₁] at ih₁'
          simp [RawRAExpr.eval?, ih₁']
      | some r₁ =>
          rcases r₁ with ⟨n, R⟩
          have ih₁' := ih₁
          rw [h₁] at ih₁'
          cases h₂ : evalRaw? e₂ S with
          | none =>
              have ih₂' := ih₂
              rw [h₂] at ih₂'
              simp [RawRAExpr.eval?, ih₁', ih₂']
          | some r₂ =>
              rcases r₂ with ⟨m, T⟩
              have ih₂' := ih₂
              rw [h₂] at ih₂'
              by_cases hEq : n = m
              · subst hEq
                simp [RawRAExpr.eval?, ih₁', ih₂',
                  FastRelation.union_correct]
              · simp [RawRAExpr.eval?, ih₁', ih₂', hEq]
  | diff e₁ e₂ ih₁ ih₂ =>
      simp only [evalRaw?]
      cases h₁ : evalRaw? e₁ S with
      | none =>
          have ih₁' := ih₁
          rw [h₁] at ih₁'
          simp [RawRAExpr.eval?, ih₁']
      | some r₁ =>
          rcases r₁ with ⟨n, R⟩
          have ih₁' := ih₁
          rw [h₁] at ih₁'
          cases h₂ : evalRaw? e₂ S with
          | none =>
              have ih₂' := ih₂
              rw [h₂] at ih₂'
              simp [RawRAExpr.eval?, ih₁', ih₂']
          | some r₂ =>
              rcases r₂ with ⟨m, T⟩
              have ih₂' := ih₂
              rw [h₂] at ih₂'
              by_cases hEq : n = m
              · subst hEq
                simp [RawRAExpr.eval?, ih₁', ih₂',
                  FastRelation.diff_correct]
              · simp [RawRAExpr.eval?, ih₁', ih₂', hEq]

/- Fast typed RA evaluation agrees with `RAExpr.eval`. -/
theorem eval_correct
    {n : Nat}
    (e : RAExpr D Γ n)
    (S : FastInstance D Γ) :
    (eval e S).toFinRelation = e.eval S.toInstance := by
  unfold eval RAExpr.eval
  have hRaw := evalRaw?_correct e.expr S
  cases hFast : evalRaw? e.expr S with
  | none =>
      rw [hFast] at hRaw
      rw [hRaw]
      simp
  | some r =>
      rcases r with ⟨m, R⟩
      rw [hFast] at hRaw
      rw [hRaw]
      by_cases hm : m = n
      · subst hm
        simp [FastRelation.castArity]
      · simp [hm]

section ConstructorChecks

example
    (S : FastInstance D Γ) :
    (eval (RAExpr.top : RAExpr D Γ 0) S).toFinRelation =
      (RAExpr.top : RAExpr D Γ 0).eval S.toInstance :=
  eval_correct _ S

example
    (n : Nat)
    (S : FastInstance D Γ) :
    (eval (RAExpr.empty (D := D) (Γ := Γ) n) S).toFinRelation =
      (RAExpr.empty (D := D) (Γ := Γ) n).eval
        S.toInstance :=
  eval_correct _ S

example
    (X : Γ.syms)
    (S : FastInstance D Γ) :
    (eval (RAExpr.rel (D := D) X) S).toFinRelation =
      (RAExpr.rel (D := D) X).eval S.toInstance :=
  eval_correct _ S

example
    (d : D)
    (S : FastInstance D Γ) :
    (eval (RAExpr.single (Γ := Γ) d) S).toFinRelation =
      (RAExpr.single (Γ := Γ) d).eval S.toInstance :=
  eval_correct _ S

example
    (d : D)
    (S : FastInstance D Γ) :
    (eval
        (RAExpr.select (Sel.eqIdx 0 0)
          (RAExpr.single (Γ := Γ) d)
          (by simp [Sel.arityReq]))
        S).toFinRelation =
      (RAExpr.select (Sel.eqIdx 0 0)
        (RAExpr.single (Γ := Γ) d)
        (by simp [Sel.arityReq])).eval S.toInstance :=
  eval_correct _ S

example
    (d : D)
    (S : FastInstance D Γ) :
    (eval
        (RAExpr.proj [0]
          (RAExpr.single (Γ := Γ) d)
          (by decide))
        S).toFinRelation =
      (RAExpr.proj [0]
        (RAExpr.single (Γ := Γ) d)
        (by decide)).eval S.toInstance :=
  eval_correct _ S

example
    (d : D)
    (S : FastInstance D Γ) :
    (eval
        (RAExpr.prod
          (RAExpr.top : RAExpr D Γ 0)
          (RAExpr.single (Γ := Γ) d))
        S).toFinRelation =
      (RAExpr.prod
        (RAExpr.top : RAExpr D Γ 0)
        (RAExpr.single (Γ := Γ) d)).eval S.toInstance :=
  eval_correct _ S

example
    (d : D)
    (S : FastInstance D Γ) :
    (eval
        (RAExpr.union
          (RAExpr.single (Γ := Γ) d)
          (RAExpr.empty (D := D) (Γ := Γ) 1))
        S).toFinRelation =
      (RAExpr.union
        (RAExpr.single (Γ := Γ) d)
        (RAExpr.empty (D := D) (Γ := Γ) 1)).eval
        S.toInstance :=
  eval_correct _ S

example
    (d : D)
    (S : FastInstance D Γ) :
    (eval
        (RAExpr.diff
          (RAExpr.single (Γ := Γ) d)
          (RAExpr.empty (D := D) (Γ := Γ) 1))
        S).toFinRelation =
      (RAExpr.diff
        (RAExpr.single (Γ := Γ) d)
        (RAExpr.empty (D := D) (Γ := Γ) 1)).eval
        S.toInstance :=
  eval_correct _ S

end ConstructorChecks

end FastRA

end Whiel
