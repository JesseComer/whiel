-- Author: Jesse Comer
import Databases.Core.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Lex
import Mathlib.Data.List.ProdSigma

/-
  This file defines tuple and finite-relation primitives
  shared by the syntactic and semantic layers.

  Key definitions include:
    * `Tuple`
    * `Tuple.MapsInto`
    * `Tuple.instLinearOrder`
    * `Tuple.instHashable`
    * `Tuple.castArity`
    * `Tuple.left`
    * `Tuple.right`
    * `Tuple.cons`
    * `Tuple.tail`
    * `Tuple.isTupleOver`
    * `Tuple.allOver`
    * `Tuple.sortDedup`
    * `FinRelation.appendTuple`
    * `FinRelation`
-/

------------------------------------------------------------
-- Tuple Type And Maps-Into
------------------------------------------------------------

/- Tuples over domain `D` of arity `n`. -/
abbrev Tuple (D : Type) (n : Nat) :=
  Vector D n

namespace Tuple

/- Every coordinate of `t` belongs to the set `Q`. -/
def MapsInto
    {D : Type}
    {n : Nat}
    (t : Tuple D n)
    (Q : Set D) : Prop :=
  ∀ i : Fin n, Q (t.get i)

instance
    {D : Type}
    {n : Nat}
    (t : Tuple D n)
    (Q : Set D)
    [DecidablePred Q] :
    Decidable (MapsInto t Q) := by
  unfold MapsInto
  infer_instance

instance instLinearOrder
    {D : Type}
    [LinearOrder D]
    {n : Nat} :
    LinearOrder (Tuple D n) :=
  LinearOrder.lift'
    (fun t : Tuple D n => t.toList)
    (fun _t _u h => Vector.toList_inj.mp h)

instance instHashable
    {D : Type}
    [Hashable D]
    {n : Nat} :
    Hashable (Tuple D n) where
  hash t :=
    t.toList.foldl
      (fun acc d => mixHash acc (hash d))
      (hash n)

end Tuple

------------------------------------------------------------
-- Tuple Arity Casting
------------------------------------------------------------

namespace Tuple

variable {D : Type}

/-
  Transport a tuple across an equality of arities.
-/
def castArity
    {m n : Nat}
    (h : m = n)
    (t : Tuple D n) :
    Tuple D m :=
  cast (congrArg (Tuple D) h.symm) t

@[simp] theorem castArity_rfl
    {n : Nat}
    (t : Tuple D n) :
    castArity rfl t = t :=
  rfl

/- Arity casts preserve the underlying tuple entries. -/
@[simp] theorem castArity_toList
    {m n : Nat}
    (h : m = n)
    (t : Tuple D n) :
    (castArity h t).toList = t.toList := by
  cases h
  rfl

theorem castArity_trans
    {k m n : Nat}
    (hkm : k = m)
    (hmn : m = n)
    (t : Tuple D n) :
    Tuple.castArity hkm (Tuple.castArity hmn t) =
      Tuple.castArity (hkm.trans hmn) t := by
  cases hkm
  cases hmn
  rfl

theorem castArity_proof_irrel
    {m n : Nat}
    (h₁ h₂ : m = n)
    (t : Tuple D n) :
    Tuple.castArity h₁ t = Tuple.castArity h₂ t := by
  cases h₁
  rfl

theorem castArity_symm
    {m n : Nat}
    (h : m = n)
    (t : Tuple D n) :
    Tuple.castArity h.symm (Tuple.castArity h t) = t := by
  cases h
  rfl

end Tuple

------------------------------------------------------------
-- Tuple Constructors And Coordinate Helpers
------------------------------------------------------------

namespace Tuple

variable {D : Type}

/- The unique tuple of arity zero. -/
def empty : Tuple D 0 :=
  Vector.ofFn (fun i : Fin 0 => nomatch i)

/- Convert a list to an arity-`n` tuple, when possible. -/
def ofList?
    (n : Nat)
    (xs : List D) : Option (Tuple D n) :=
  if h : xs.length = n then
    some ⟨xs.toArray, by simpa using h⟩
  else
    none

/- First `n` coordinates of a tuple of arity `n + m`. -/
def left
    {n m : Nat}
    (t : Tuple D (n + m)) : Tuple D n :=
  Vector.ofFn (fun i => t.get ⟨i.1, by omega⟩)

/- Last `m` coordinates of a tuple of arity `n + m`. -/
def right
    {n m : Nat}
    (t : Tuple D (n + m)) : Tuple D m :=
  Vector.ofFn (fun i => t.get ⟨n + i.1, by omega⟩)

/- The left projection preserves membership in `Q`. -/
theorem left_mapsInto
    {n m : Nat}
    {t : Tuple D (n + m)}
    {Q : Set D}
    (ht : MapsInto t Q) :
    MapsInto (left t) Q := by
  intro i
  simpa [left, Vector.get, Vector.ofFn] using
    ht ⟨i.1, by omega⟩

/- The right projection preserves membership in `Q`. -/
theorem right_mapsInto
    {n m : Nat}
    {t : Tuple D (n + m)}
    {Q : Set D}
    (ht : MapsInto t Q) :
    MapsInto (right (n := n) t) Q := by
  intro i
  simpa [right, Vector.get, Vector.ofFn] using
    ht ⟨n + i.1, by omega⟩

/- Add a head coordinate to a tuple. -/
def cons
    (d : D)
    {n : Nat}
    (t : Tuple D n) :
    Tuple D (n + 1) :=
  Vector.ofFn
    (fun i =>
      if h : i.1 = 0 then
        d
      else
        t.get ⟨i.1 - 1, by
          have hi : 1 ≤ i.1 :=
            Nat.succ_le_of_lt (Nat.pos_of_ne_zero h)
          omega⟩)

/- Remove the head coordinate from a nonempty tuple. -/
def tail
    {n : Nat}
    (t : Tuple D (n + 1)) :
    Tuple D n :=
  Vector.ofFn (fun j => t.get ⟨j.1 + 1, by omega⟩)

/- The head of a tuple built by `cons` is the new value. -/
theorem get_cons_zero
    (d : D)
    {n : Nat}
    (t : Tuple D n) :
    (cons d t)[0] = d := by
  simp [cons, Vector.get, Vector.ofFn]

/-
  Successor coordinates of a tuple built by `cons` recover
  the original tuple.
-/
theorem get_cons_succ
    (d : D)
    {n : Nat}
    (t : Tuple D n)
    (j : Fin n) :
    (cons d t)[j.1 + 1] = t.get j := by
  simp [cons, Vector.get, Vector.ofFn]

/-
  Splitting a nonempty tuple into head and tail is exact.
-/
theorem cons_tail
    {n : Nat}
    (t : Tuple D (n + 1)) :
    cons t[0] (tail t) = t := by
  apply Vector.ext
  intro j hj
  cases j with
  | zero =>
      simpa using get_cons_zero t[0] (tail t)
  | succ j' =>
      have hj' : j' < n := by
        simpa using hj
      simpa [tail, Vector.get, Vector.ofFn]
        using get_cons_succ t[0] (tail t) ⟨j', hj'⟩

/- A tuple coordinate is a member of its underlying list. -/
theorem get_mem_toList
    {n : Nat}
    (t : Tuple D n)
    (i : Fin n) :
    t.get i ∈ t.toList := by
  simp [Vector.get, Vector.toList]

/- A tuple coordinate belongs to its finite value set. -/
theorem mem_toList_toFinset_of_get
    [DecidableEq D]
    {n : Nat}
    (t : Tuple D n)
    (i : Fin n) :
    t.get i ∈ t.toList.toFinset := by
  cases t with
  | mk arr hSize =>
      simp [Vector.get, Vector.toList]

end Tuple

------------------------------------------------------------
-- Tuple Value Predicates
------------------------------------------------------------

namespace Tuple

variable {D : Type}

/- Every coordinate of `t` is an element of `Q`. -/
def isTupleOver
    {n : Nat}
    (t : Tuple D n)
    (Q : Finset D) : Prop :=
  ∀ i : Fin n, t.get i ∈ Q

instance
    [DecidableEq D]
    {n : Nat}
    (t : Tuple D n)
    (Q : Finset D) :
    Decidable (t.isTupleOver Q) := by
  unfold isTupleOver
  infer_instance

theorem isTupleOver_mono
    {n : Nat}
    {t : Tuple D n}
    {Q₁ Q₂ : Finset D}
    (hVals : Q₁ ⊆ Q₂)
    (ht : t.isTupleOver Q₁) :
    t.isTupleOver Q₂ := by
  intro i
  exact hVals (ht i)

end Tuple

------------------------------------------------------------
-- Tuple Enumeration
------------------------------------------------------------

namespace Tuple

variable {D : Type}

private def dedupList
    [DecidableEq D] :
    List D → List D
| [] => []
| x :: xs =>
    if x ∈ xs then
      dedupList xs
    else
      x :: dedupList xs

private theorem mem_dedupList_iff
    [DecidableEq D]
    (x : D) :
    ∀ xs : List D, x ∈ dedupList xs ↔ x ∈ xs
| [] => by
    simp [dedupList]
| y :: ys => by
    by_cases hy : y ∈ ys
    · by_cases hxy : x = y
      · simp [dedupList, hy, hxy, mem_dedupList_iff]
      · simp [dedupList, hy, hxy, mem_dedupList_iff]
    · by_cases hxy : x = y
      · simp [dedupList, hy, hxy]
      · simp [dedupList, hy, hxy, mem_dedupList_iff]

private theorem nodup_dedupList
    [DecidableEq D] :
    ∀ xs : List D, (dedupList xs).Nodup
| [] => by
    simp [dedupList]
| x :: xs => by
    by_cases hx : x ∈ xs
    · simp [dedupList, hx, nodup_dedupList xs]
    · simp [dedupList, hx, nodup_dedupList xs,
        mem_dedupList_iff]

private theorem length_dedupList_le
    [DecidableEq D] :
    ∀ xs : List D, (dedupList xs).length ≤ xs.length
| [] => by
    simp [dedupList]
| x :: xs => by
    by_cases hx : x ∈ xs
    · simp only [dedupList, hx, List.length_cons]
      exact Nat.le_trans (length_dedupList_le xs)
        (Nat.le_succ xs.length)
    · simp only [dedupList, hx, List.length_cons]
      exact Nat.succ_le_succ (length_dedupList_le xs)

/- A finite set produced from a list without choice. -/
private def listFinset
    [DecidableEq D]
    (xs : List D) :
    Finset D :=
  ⟨dedupList xs, nodup_dedupList xs⟩

private theorem mem_listFinset_iff
    [DecidableEq D]
    (x : D)
    (xs : List D) :
    x ∈ listFinset xs ↔ x ∈ xs :=
  mem_dedupList_iff x xs

private theorem listFinset_eq_of_perm
    [DecidableEq D]
    {xs ys : List D}
    (hxy : xs.Perm ys) :
    listFinset xs = listFinset ys := by
  apply Finset.ext
  intro x
  rw [mem_listFinset_iff, mem_listFinset_iff]
  exact hxy.mem_iff

private theorem listFinset_card_le_length
    [DecidableEq D]
    (xs : List D) :
    (listFinset xs).card ≤ xs.length := by
  simpa [listFinset] using length_dedupList_le (D := D) xs

private def consList
    (d : D)
    {n : Nat}
    (t : Tuple D n) :
    Tuple D (n + 1) :=
  ⟨(d :: t.toList).toArray, by
    simp [Vector.length_toList]⟩

private def tailList
    {n : Nat}
    (t : Tuple D (n + 1)) :
    Tuple D n :=
  ⟨t.toList.tail.toArray, by
    rw [List.size_toArray, List.length_tail,
      Vector.length_toList]
    simp⟩

private theorem get_consList_zero
    (d : D)
    {n : Nat}
    (t : Tuple D n) :
    (consList d t).get ⟨0, Nat.succ_pos n⟩ = d := by
  simp [consList, Vector.get]

private theorem get_consList_succ
    (d : D)
    {n : Nat}
    (t : Tuple D n)
    (j : Fin n) :
    (consList d t).get j.succ = t.get j := by
  simp [consList, Vector.get, Vector.getElem_toList]

private theorem get_tailList
    {n : Nat}
    (t : Tuple D (n + 1))
    (j : Fin n) :
    (tailList t).get j = t.get j.succ := by
  simp [tailList, Vector.get, Vector.getElem_toList]

private theorem consList_tailList
    {n : Nat}
    (t : Tuple D (n + 1)) :
    consList (t.get ⟨0, Nat.succ_pos n⟩) (tailList t) = t := by
  apply Vector.ext
  intro j hj
  cases j with
  | zero =>
      simpa using
        get_consList_zero
          (t.get ⟨0, Nat.succ_pos n⟩) (tailList t)
  | succ j' =>
      have hj' : j' < n := by
        simpa using hj
      have hCons :=
        get_consList_succ
          (t.get ⟨0, Nat.succ_pos n⟩)
          (tailList t) ⟨j', hj'⟩
      have hTail := get_tailList t ⟨j', hj'⟩
      simpa [hTail] using hCons

private def allOverList
    (xs : List D) :
    (n : Nat) → List (Tuple D n)
| 0 => [empty]
| n + 1 =>
    (xs.product (allOverList xs n)).map
      (fun p => consList p.1 p.2)

private theorem allOverList_perm
    {xs ys : List D}
    (hxy : xs.Perm ys) :
    ∀ n : Nat, (allOverList xs n).Perm (allOverList ys n)
| 0 => by
    simp [allOverList]
| n + 1 => by
    change
      (List.map (fun p : D × Tuple D n => consList p.1 p.2)
          (xs.product (allOverList xs n))).Perm
        (List.map (fun p : D × Tuple D n => consList p.1 p.2)
          (ys.product (allOverList ys n)))
    exact List.Perm.map _ (List.Perm.product hxy
      (allOverList_perm hxy n))

private theorem product_length
    {E : Type}
    (xs : List D)
    (ys : List E) :
    (xs.product ys).length = xs.length * ys.length := by
  induction xs with
  | nil =>
      simp only [List.product, List.flatMap_nil,
        List.length_nil, Nat.zero_mul]
  | cons x xs ih =>
      change
        (List.map (Prod.mk x) ys ++ xs.product ys).length =
          (xs.length + 1) * ys.length
      rw [List.length_append, List.length_map, ih,
        Nat.add_mul]
      simp [Nat.add_comm]

private theorem allOverList_length
    (xs : List D) :
    ∀ n : Nat, (allOverList xs n).length = xs.length ^ n
| 0 => by
    simp [allOverList]
| n + 1 => by
    calc
      (allOverList xs (n + 1)).length =
          (xs.product (allOverList xs n)).length := by
        simp [allOverList]
      _ = xs.length * (allOverList xs n).length :=
        product_length xs (allOverList xs n)
      _ = xs.length * xs.length ^ n := by
        rw [allOverList_length xs n]
      _ = xs.length ^ (n + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm]

private theorem mem_allOverList_iff
    (xs : List D) :
    ∀ {n : Nat} {t : Tuple D n},
      t ∈ allOverList xs n ↔
        ∀ i : Fin n, t.get i ∈ xs
| 0, t => by
    constructor
    · intro _ht i
      exact Fin.elim0 i
    · intro _ht
      change t ∈ [empty]
      rw [List.mem_singleton]
      apply Vector.ext
      intro i hi
      exact False.elim (Nat.not_lt_zero i hi)
| n + 1, t => by
    constructor
    · intro ht i
      change t ∈
        List.map (fun p : D × Tuple D n => consList p.1 p.2)
          (xs.product (allOverList xs n)) at ht
      rw [List.mem_map] at ht
      rcases ht with ⟨p, hp, hEq⟩
      rcases List.mem_product.mp hp with ⟨hpHead, hpTail⟩
      subst hEq
      cases i using Fin.cases with
      | zero =>
          have h0 :
              (consList p.1 p.2).get
                ⟨0, Nat.succ_pos n⟩ ∈ xs := by
            rw [get_consList_zero]
            exact hpHead
          simpa using h0
      | succ j =>
          have hTail :=
            (mem_allOverList_iff xs).mp hpTail j
          have hSucc :
              (consList p.1 p.2).get j.succ ∈ xs := by
            rw [get_consList_succ]
            exact hTail
          simpa using hSucc
    · intro ht
      let head : D := t.get ⟨0, Nat.succ_pos n⟩
      let tail : Tuple D n := tailList t
      have hHead : head ∈ xs :=
        ht ⟨0, Nat.succ_pos n⟩
      have hTail :
          tail ∈ allOverList xs n := by
        apply (mem_allOverList_iff xs).mpr
        intro i
        have hi := ht i.succ
        have hGet := get_tailList t i
        simpa [tail, hGet] using hi
      have hCons : consList head tail = t := by
        simpa [head, tail] using consList_tailList t
      rw [← hCons]
      change consList head tail ∈
        List.map (fun p : D × Tuple D n => consList p.1 p.2)
          (xs.product (allOverList xs n))
      rw [List.mem_map]
      exact ⟨(head, tail),
        List.mem_product.mpr ⟨hHead, hTail⟩, rfl⟩

/- The finite set of all arity-`n` tuples over `Q`. -/
def allOver
    [DecidableEq D]
    (Q : Finset D)
    (n : Nat) :
    Finset (Tuple D n) :=
  Quotient.liftOn Q.1
    (fun xs => listFinset (allOverList xs n))
    (fun _xs _ys hxy =>
      listFinset_eq_of_perm (allOverList_perm hxy n))

end Tuple

------------------------------------------------------------
-- Tuple Enumeration Properties
------------------------------------------------------------

namespace Tuple

variable {D : Type}

theorem mem_allOver_iff_isTupleOver
    [DecidableEq D]
    (Q : Finset D)
    {n : Nat}
    {t : Tuple D n} :
    t ∈ Tuple.allOver Q n ↔ t.isTupleOver Q := by
  cases Q with
  | mk val nodup =>
      induction val using Quotient.inductionOn with
      | h xs =>
          constructor
          · intro ht i
            change t ∈ listFinset (allOverList xs n) at ht
            have htList :
                t ∈ allOverList xs n :=
              (mem_listFinset_iff t (allOverList xs n)).mp ht
            have hi : t.get i ∈ xs :=
              (mem_allOverList_iff xs).mp htList i
            simpa [isTupleOver] using hi
          · intro ht
            change t ∈ listFinset (allOverList xs n)
            apply (mem_listFinset_iff t
              (allOverList xs n)).mpr
            apply (mem_allOverList_iff xs).mpr
            intro i
            have hi : t.get i ∈
                (Finset.mk (α := D) (Quotient.mk'' xs) nodup) :=
              ht i
            simpa [isTupleOver] using hi

/-
  Tuples over a finite set occur in the finite tuple
  enumeration for that set.
-/
theorem mem_allOver_of_isTupleOver
    [DecidableEq D]
    (Q : Finset D) :
    ∀ {n : Nat} {t : Tuple D n},
      t.isTupleOver Q →
        t ∈ Tuple.allOver Q n
| _n, _t, ht => by
    exact (mem_allOver_iff_isTupleOver Q).mpr ht

theorem isTupleOver_of_mem_allOver
    [DecidableEq D]
    (Q : Finset D)
    {n : Nat}
    {t : Tuple D n}
    (ht : t ∈ Tuple.allOver Q n) :
    t.isTupleOver Q :=
  (mem_allOver_iff_isTupleOver Q).mp ht

theorem allOver_card_le_pow
    [DecidableEq D]
    (Q : Finset D) :
    ∀ n : Nat, (Tuple.allOver Q n).card ≤ Q.card ^ n
| n => by
    cases Q with
    | mk val nodup =>
        induction val using Quotient.inductionOn with
        | h xs =>
            change
              (listFinset (allOverList xs n)).card ≤
                (Finset.mk (α := D) xs nodup).card ^ n
            have hCard :
                (Finset.mk (α := D) xs nodup).card =
                  xs.length := rfl
            rw [hCard]
            exact
              Nat.le_trans (listFinset_card_le_length
                (allOverList xs n))
                (by rw [allOverList_length])

end Tuple

------------------------------------------------------------
-- Tuple Append Helpers
------------------------------------------------------------

namespace FinRelation

variable {D : Type}

/- Append two tuples. -/
def appendTuple
    {n m : Nat}
    (t₁ : Tuple D n)
    (t₂ : Tuple D m) :
    Tuple D (n + m) :=
  Vector.append t₁ t₂

/-
  Left coordinates of an appended tuple recover the left
  input tuple.
-/
theorem get_appendTuple_left
    {n m : Nat}
    (t₁ : Tuple D n)
    (t₂ : Tuple D m)
    (i : Fin n) :
    (appendTuple t₁ t₂).get
        ⟨i.1, by omega⟩ =
      t₁.get i := by
  cases t₁ with
  | mk arr₁ h₁size =>
      cases t₂ with
      | mk arr₂ h₂size =>
          simp [appendTuple, Vector.get,
            Vector.append, h₁size]

/-
  Right coordinates of an appended tuple recover the right
  input tuple.
-/
theorem get_appendTuple_right
    {n m : Nat}
    (t₁ : Tuple D n)
    (t₂ : Tuple D m)
    (i : Fin m) :
    (appendTuple t₁ t₂).get ⟨n + i.1, by omega⟩ =
      t₂.get i := by
  cases t₁ with
  | mk arr₁ h₁size =>
      cases t₂ with
      | mk arr₂ h₂size =>
          simp [appendTuple, Vector.get,
            Vector.append, h₁size]

/-
  Splitting an appended tuple by arity and then appending
  the pieces returns the original tuple.
-/
theorem appendTuple_split
    {n m : Nat}
    (t : Tuple D (n + m)) :
    appendTuple
      (Tuple.left t)
      (Tuple.right (n := n) t) = t := by
  apply Vector.ext
  intro i hi
  by_cases hlt : i < n
  · let j : Fin n := ⟨i, hlt⟩
    have hLeft :=
      get_appendTuple_left
        (Tuple.left t)
        (Tuple.right (n := n) t) j
    simpa [Tuple.left, Vector.get, Vector.ofFn, j]
      using hLeft
  · have hge : n ≤ i := Nat.le_of_not_gt hlt
    let j : Fin m := ⟨i - n, by omega⟩
    have hRight :=
      get_appendTuple_right
        (Tuple.left t)
        (Tuple.right (n := n) t) j
    simpa [Tuple.right, Vector.get, Vector.ofFn,
      j, hge] using hRight

end FinRelation

------------------------------------------------------------
-- Tuple Ordered Deduplication
------------------------------------------------------------

namespace Tuple

variable {D : Type}

private theorem nodup_eraseDupsBy_loop_beq
    {α : Type}
    [BEq α] [LawfulBEq α] :
    ∀ (xs acc : List α), acc.Nodup →
      (List.eraseDupsBy.loop
        (fun x y => x == y) xs acc).Nodup
| [], acc, hAcc => by
    rw [List.eraseDupsBy.loop.eq_1]
    exact List.nodup_reverse.mpr hAcc
| x :: xs, acc, hAcc => by
    rw [List.eraseDupsBy.loop.eq_2]
    cases hAny : acc.any (fun y => x == y)
    · apply nodup_eraseDupsBy_loop_beq xs (x :: acc)
      rw [List.nodup_cons]
      refine ⟨?_, hAcc⟩
      intro hx
      have hAnyTrue :
          acc.any (fun y => x == y) = true := by
        rw [List.any_eq_true]
        exact ⟨x, hx, by simp⟩
      simp [hAny] at hAnyTrue
    · exact nodup_eraseDupsBy_loop_beq xs acc hAcc

private theorem nodup_eraseDups
    {α : Type}
    [BEq α] [LawfulBEq α]
    (xs : List α) :
    xs.eraseDups.Nodup := by
  unfold List.eraseDups List.eraseDupsBy
  exact nodup_eraseDupsBy_loop_beq xs [] (by simp)

/-
  Sort tuples lexicographically by coordinate values, then
  remove duplicates. This is intended for executable
  evaluators that accumulate candidate facts in lists before
  crossing back to `Finset` semantics.
-/
def sortDedup
    [LinearOrder D]
    {n : Nat}
    (ts : List (Tuple D n)) :
    List (Tuple D n) :=
  (ts.mergeSort
    (fun t u => decide (t.toList ≤ u.toList))).eraseDups

theorem mem_sortDedup_iff
    [LinearOrder D]
    {n : Nat}
    (t : Tuple D n)
    (ts : List (Tuple D n)) :
    t ∈ Tuple.sortDedup ts ↔ t ∈ ts := by
  unfold Tuple.sortDedup
  rw [List.mem_eraseDups, List.mem_mergeSort]

theorem nodup_sortDedup
    [LinearOrder D]
    {n : Nat}
    (ts : List (Tuple D n)) :
    (Tuple.sortDedup ts).Nodup := by
  unfold Tuple.sortDedup
  exact nodup_eraseDups _

theorem sortDedup_toFinset
    [LinearOrder D]
    {n : Nat}
    (ts : List (Tuple D n)) :
    (Tuple.sortDedup ts).toFinset = ts.toFinset := by
  apply Finset.ext
  intro t
  simp [List.mem_toFinset, Tuple.mem_sortDedup_iff]

end Tuple

------------------------------------------------------------
-- Finite Relations
------------------------------------------------------------

/- A finite relation is a finite set of arity-`n` tuples. -/
abbrev FinRelation (D : Type) (n : Nat) :=
  Finset (Tuple D n)

------------------------------------------------------------
-- Finite Relation Arity Casting
------------------------------------------------------------

namespace FinRelation

variable {D : Type}

theorem mem_cast_iff
    {m n : Nat}
    (h : m = n)
    (R : FinRelation D m)
    (t : Tuple D n) :
    t ∈ cast (congrArg (FinRelation D) h) R ↔
      Tuple.castArity h t ∈ R := by
  cases h
  rfl

theorem cast_trans
    {k m n : Nat}
    (hkm : k = m)
    (hmn : m = n)
    (R : FinRelation D k) :
    cast (congrArg (FinRelation D) hmn)
        (cast (congrArg (FinRelation D) hkm) R) =
      cast (congrArg (FinRelation D) (hkm.trans hmn)) R := by
  cases hkm
  cases hmn
  rfl

theorem cast_proof_irrel
    {m n : Nat}
    (h₁ h₂ : m = n)
    (R : FinRelation D m) :
    cast (congrArg (FinRelation D) h₁) R =
      cast (congrArg (FinRelation D) h₂) R := by
  cases h₁
  rfl

end FinRelation
