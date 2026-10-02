-- Author: Jesse Comer
import Std.Data.HashMap.Lemmas
import Whiel.Eval.RA.Fast

/-
  A temporary hash index for one relation column.

  `JoinIndex.ofRelation` indexes one tuple coordinate.
  Its lookup theorem says a bucket contains exactly the
  source tuples having the requested column value.
  The index is assignment-local with no logical denotation.
-/

------------------------------------------------------------
-- Temporary Join Column Index
------------------------------------------------------------

namespace Whiel

structure JoinIndex
    (D : Type)
    [Domain D] [Hashable D]
    (n : Nat) where
  map : Std.HashMap D (List (Tuple D n))

namespace JoinIndex

variable {D : Type}
variable [Domain D] [LinearOrder D] [Hashable D]

/- Empty temporary column index. -/
def empty {n : Nat} : JoinIndex D n where
  map := ∅

/- Look up the bucket for one projected key. -/
def lookup
    {n : Nat}
    (idx : JoinIndex D n)
    (key : D) : List (Tuple D n) :=
  idx.map.getD key []

/- Add one tuple to its projected-key bucket. -/
def insert
    {n : Nat}
    (i : Fin n)
    (u : Tuple D n)
    (idx : JoinIndex D n) : JoinIndex D n where
  map := idx.map.insert (u.get i)
    (u :: idx.lookup (u.get i))

/- Build an index from a relation's materialized tuples. -/
def ofList
    {n : Nat}
    (i : Fin n) :
    List (Tuple D n) → JoinIndex D n
| [] => empty
| u :: us => insert i u (ofList i us)

/- Build an index from one materialized relation. -/
def ofRelation
    {n : Nat}
    (i : Fin n)
    (R : FastRelation D n) : JoinIndex D n :=
  ofList i R.tuples

/- An inserted tuple appears exactly in its own bucket. -/
omit [LinearOrder D] in
theorem mem_lookup_insert_iff
    {n : Nat}
    (idx : JoinIndex D n)
    (i : Fin n)
    (u t : Tuple D n)
    (key : D) :
    t ∈ (idx.insert i u).lookup key ↔
      (t = u ∧ u.get i = key) ∨
        t ∈ idx.lookup key := by
  unfold insert lookup
  rw [Std.HashMap.getD_insert]
  by_cases h : u.get i = key
  · simp [h]
  · have hBeq : ((u.get i) == key) = false := by
      cases hEq : ((u.get i) == key)
      · rfl
      · exact False.elim (h (LawfulBEq.eq_of_beq hEq))
    simp [hBeq, h]

/- Lookup exactly characterizes a source tuple and key. -/
omit [LinearOrder D] in
theorem mem_lookup_ofList_iff
    {n : Nat}
    (i : Fin n)
    (ts : List (Tuple D n))
    (key : D)
    (t : Tuple D n) :
    t ∈ (ofList i ts).lookup key ↔
      t ∈ ts ∧ t.get i = key := by
  induction ts with
  | nil =>
      simp [ofList, empty, lookup]
  | cons u us ih =>
      constructor
      · intro ht
        rcases (mem_lookup_insert_iff
          (ofList i us) i u t key).mp ht with h | h
        · exact ⟨List.mem_cons.mpr (Or.inl h.1),
            by simpa [h.1] using h.2⟩
        · rcases ih.mp h with ⟨hMem, hGet⟩
          exact ⟨List.mem_cons.mpr (Or.inr hMem), hGet⟩
      · intro ht
        rcases ht with ⟨hMem, hGet⟩
        rcases List.mem_cons.mp hMem with hEq | hMem
        · change t ∈
            (insert i u (ofList i us)).lookup key
          apply (mem_lookup_insert_iff
            (ofList i us) i u t key).mpr
          left
          refine ⟨hEq, ?_⟩
          simpa [hEq] using hGet
        · change t ∈
            (insert i u (ofList i us)).lookup key
          apply (mem_lookup_insert_iff
            (ofList i us) i u t key).mpr
          right
          exact ih.mpr ⟨hMem, hGet⟩

/- Lookup exactly characterizes the indexed relation. -/
theorem mem_lookup_ofRelation_iff
    {n : Nat}
    (i : Fin n)
    (R : FastRelation D n)
    (key : D)
    (t : Tuple D n) :
    t ∈ (ofRelation i R).lookup key ↔
      t ∈ R.toFinRelation ∧ t.get i = key := by
  rw [ofRelation, mem_lookup_ofList_iff,
    FastRelation.mem_toFinRelation_iff]

end JoinIndex

end Whiel
