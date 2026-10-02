-- Author: Jesse Comer
import Databases.Core.FinRelation
import Mathlib.Data.List.Destutter

/-
  Linear normalization for materialized Whiel tuples.

  `TupleNormalize.normalize` merge-sorts tuples in the
  established lexicographic order.  It then removes adjacent
  duplicates.  Its membership and duplicate-freedom theorems
  support the `FastRelation.ofList` physical construction.
-/

------------------------------------------------------------
-- Adjacent Tuple Normalization
------------------------------------------------------------

namespace Whiel

namespace TupleNormalize

variable {D : Type}

/- Sort tuples, then remove adjacent equal tuple blocks. -/
def normalize
    [LinearOrder D]
    {n : Nat}
    (ts : List (Tuple D n)) :
    List (Tuple D n) :=
  (ts.mergeSort
    (fun t u => decide (t.toList ≤ u.toList))).destutter
      (fun t u => t ≠ u)

private theorem pairwise_mergeSort
    [LinearOrder D]
    {n : Nat}
    (ts : List (Tuple D n)) :
    (ts.mergeSort
      (fun t u => decide (t.toList ≤ u.toList))).Pairwise
        (fun t u => t.toList ≤ u.toList) := by
  simpa only [decide_eq_true_eq] using
    (List.pairwise_mergeSort
      (le := fun t u => decide (t.toList ≤ u.toList))
      (by
        intro t u v htu huv
        simp only [decide_eq_true_eq] at htu huv ⊢
        exact le_trans htu huv)
      (by
        intro t u
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact le_total _ _)
      ts)

private theorem normalize_eq_dedup_sort
    [LinearOrder D]
    {n : Nat}
    (ts : List (Tuple D n)) :
    normalize ts =
      List.dedup
        (ts.mergeSort
          (fun t u => decide (t.toList ≤ u.toList))) := by
  unfold normalize
  letI : Std.Antisymm
      (fun (t u : Tuple D n) => t.toList ≤ u.toList) :=
    { antisymm := by
        intro t u htu hut
        exact Vector.toList_inj.mp
          (le_antisymm htu hut) }
  exact (pairwise_mergeSort ts).destutter_eq_dedup

/- Adjacent normalization preserves tuple membership. -/
theorem mem_normalize_iff
    [LinearOrder D]
    {n : Nat}
    (t : Tuple D n)
    (ts : List (Tuple D n)) :
    t ∈ normalize ts ↔ t ∈ ts := by
  rw [normalize_eq_dedup_sort, List.mem_dedup,
    List.mem_mergeSort]

/- Adjacent normalization produces no duplicate tuples. -/
theorem nodup_normalize
    [LinearOrder D]
    {n : Nat}
    (ts : List (Tuple D n)) :
    (normalize ts).Nodup := by
  rw [normalize_eq_dedup_sort]
  exact List.nodup_dedup _

end TupleNormalize

end Whiel
