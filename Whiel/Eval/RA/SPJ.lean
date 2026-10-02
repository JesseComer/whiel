-- Author: Jesse Comer
import Whiel.Eval.RA.JoinIndex

/-
  Fused select-project-join execution for one binary
  equijoin.

  `SPJFast.eval` enumerates the input tuple lists directly,
  constructs appended tuples only for equal join keys,
  projects
  them immediately, and normalizes the final candidate list.
  Its denotation theorem connects this physical path to the
  logical product, selection, and projection operators.
  `SPJFast.evalIndexed` builds a temporary right-column
  index.  Both strategies have the same logical denotation.
-/

------------------------------------------------------------
-- Fused Equijoin Execution
------------------------------------------------------------

namespace Whiel

namespace SPJFast

variable {D : Type}
variable [Domain D] [LinearOrder D] [Hashable D]

/- Fused projected candidates for one checked equijoin. -/
def candidates
    {n m : Nat}
    (idxs : List Nat)
    (i j : Nat)
    (R : FastRelation D n)
    (S : FastRelation D m)
    (hi : i < n)
    (hj : j < m)
    (hIdx : ∀ k ∈ idxs, k < n + m) :
    List (Tuple D idxs.length) :=
  R.tuples.flatMap (fun t =>
    S.tuples.filterMap (fun u =>
      if _ : t.get ⟨i, hi⟩ = u.get ⟨j, hj⟩ then
        some (FinRelation.projTuple idxs
          (FinRelation.appendTuple t u) hIdx)
      else
        none))

/- Evaluate a checked projected binary equijoin. -/
def eval
    {n m : Nat}
    (idxs : List Nat)
    (i j : Nat)
    (R : FastRelation D n)
    (S : FastRelation D m)
    (hi : i < n)
    (hj : j < m)
    (hIdx : ∀ k ∈ idxs, k < n + m) :
    FastRelation D idxs.length :=
  FastRelation.ofList
    (candidates idxs i j R S hi hj hIdx)

/- Indexed projected candidates for one checked equijoin. -/
def candidatesIndexed
    {n m : Nat}
    (idxs : List Nat)
    (i j : Nat)
    (R : FastRelation D n)
    (S : FastRelation D m)
    (hi : i < n)
    (hj : j < m)
    (hIdx : ∀ k ∈ idxs, k < n + m) :
    List (Tuple D idxs.length) :=
  let index := JoinIndex.ofRelation ⟨j, hj⟩ S
  R.tuples.flatMap (fun t =>
    (index.lookup (t.get ⟨i, hi⟩)).map (fun u =>
      FinRelation.projTuple idxs
        (FinRelation.appendTuple t u) hIdx))

/- Evaluate with a temporary right-column hash index. -/
def evalIndexed
    {n m : Nat}
    (idxs : List Nat)
    (i j : Nat)
    (R : FastRelation D n)
    (S : FastRelation D m)
    (hi : i < n)
    (hj : j < m)
    (hIdx : ∀ k ∈ idxs, k < n + m) :
    FastRelation D idxs.length :=
  FastRelation.ofList
    (candidatesIndexed idxs i j R S hi hj hIdx)

end SPJFast

end Whiel

------------------------------------------------------------
-- Fused Equijoin Denotation
------------------------------------------------------------

namespace Whiel

namespace SPJFast

variable {D : Type}
variable [Domain D] [LinearOrder D] [Hashable D]

/- The fused result denotes selected-product projection. -/
theorem eval_correct
    {n m : Nat}
    (idxs : List Nat)
    (i j : Nat)
    (R : FastRelation D n)
    (S : FastRelation D m)
    (hi : i < n)
    (hj : j < m)
    (hIdx : ∀ k ∈ idxs, k < n + m) :
    (eval idxs i j R S hi hj hIdx).toFinRelation =
      FinRelation.proj idxs
        (FinRelation.select
          (fun t => Sel.Holds (.eqIdx i (n + j)) t)
          (FinRelation.prod
            R.toFinRelation S.toFinRelation))
        hIdx := by
  apply Finset.ext
  intro t
  unfold eval
  rw [FastRelation.mem_ofList_iff,
    FinRelation.mem_proj_iff]
  constructor
  · intro ht
    simp only [candidates, List.mem_flatMap,
      List.mem_filterMap] at ht
    rcases ht with ⟨u, hu, w, hw, hMap⟩
    by_cases hEq :
        u.get ⟨i, hi⟩ = w.get ⟨j, hj⟩
    · have hProj :
          FinRelation.projTuple idxs
              (FinRelation.appendTuple u w) hIdx = t := by
        simpa [hEq] using hMap
      refine ⟨FinRelation.appendTuple u w, ?_, hProj⟩
      rw [FinRelation.mem_select_iff]
      refine ⟨FinRelation.mem_prod_iff.mpr ?_, ?_⟩
      · exact ⟨u,
          (FastRelation.mem_toFinRelation_iff R u).mpr hu,
          w,
          (FastRelation.mem_toFinRelation_iff S w).mpr hw,
          rfl⟩
      · rw [Sel.holds_eqIdx_iff _ (by omega) (by omega)]
        calc
          (FinRelation.appendTuple u w).get
              ⟨i, by omega⟩ = u.get ⟨i, hi⟩ := by
            simpa using
              (FinRelation.get_appendTuple_left
                u w ⟨i, hi⟩)
          _ = w.get ⟨j, hj⟩ := hEq
          _ = (FinRelation.appendTuple u w).get
              ⟨n + j, by omega⟩ := by
            simpa using
              (FinRelation.get_appendTuple_right
                u w ⟨j, hj⟩).symm
    · simp [hEq] at hMap
  · rintro ⟨u, hu, hProj⟩
    rw [FinRelation.mem_select_iff] at hu
    rcases FinRelation.mem_prod_iff.mp hu.1 with
      ⟨v, hv, w, hw, hAppend⟩
    subst u
    have hEq :
        v.get ⟨i, hi⟩ = w.get ⟨j, hj⟩ := by
      rw [Sel.holds_eqIdx_iff _ (by omega) (by omega)] at hu
      calc
        v.get ⟨i, hi⟩ =
            (FinRelation.appendTuple v w).get
            ⟨i, by omega⟩ := by
          simpa using
            (FinRelation.get_appendTuple_left
              v w ⟨i, hi⟩).symm
        _ = (FinRelation.appendTuple v w).get
            ⟨n + j, by omega⟩ := hu.2
        _ = w.get ⟨j, hj⟩ := by
          simpa using
            (FinRelation.get_appendTuple_right
              v w ⟨j, hj⟩)
    simp only [candidates, List.mem_flatMap,
      List.mem_filterMap]
    exact ⟨v,
      (FastRelation.mem_toFinRelation_iff R v).mp hv,
      w,
      (FastRelation.mem_toFinRelation_iff S w).mp hw,
      by simp [hEq, hProj]⟩

/- Indexed result denotes selected-product projection. -/
theorem evalIndexed_correct
    {n m : Nat}
    (idxs : List Nat)
    (i j : Nat)
    (R : FastRelation D n)
    (S : FastRelation D m)
    (hi : i < n)
    (hj : j < m)
    (hIdx : ∀ k ∈ idxs, k < n + m) :
    (evalIndexed idxs i j R S hi hj hIdx).toFinRelation =
      FinRelation.proj idxs
        (FinRelation.select
          (fun t => Sel.Holds (.eqIdx i (n + j)) t)
          (FinRelation.prod
            R.toFinRelation S.toFinRelation))
        hIdx := by
  apply Finset.ext
  intro t
  unfold evalIndexed
  rw [FastRelation.mem_ofList_iff,
    FinRelation.mem_proj_iff]
  constructor
  · intro ht
    simp only [candidatesIndexed, List.mem_flatMap,
      List.mem_map] at ht
    rcases ht with ⟨u, hu, w, hw, hProj⟩
    rw [JoinIndex.mem_lookup_ofRelation_iff] at hw
    refine ⟨FinRelation.appendTuple u w, ?_, hProj⟩
    rw [FinRelation.mem_select_iff]
    refine ⟨FinRelation.mem_prod_iff.mpr ?_, ?_⟩
    · exact ⟨u,
        (FastRelation.mem_toFinRelation_iff R u).mpr hu,
        w, hw.1, rfl⟩
    · rw [Sel.holds_eqIdx_iff _ (by omega) (by omega)]
      calc
        (FinRelation.appendTuple u w).get
            ⟨i, by omega⟩ = u.get ⟨i, hi⟩ := by
          simpa using
            (FinRelation.get_appendTuple_left
              u w ⟨i, hi⟩)
        _ = w.get ⟨j, hj⟩ := hw.2.symm
        _ = (FinRelation.appendTuple u w).get
            ⟨n + j, by omega⟩ := by
          simpa using
            (FinRelation.get_appendTuple_right
              u w ⟨j, hj⟩).symm
  · rintro ⟨u, hu, hProj⟩
    rw [FinRelation.mem_select_iff] at hu
    rcases FinRelation.mem_prod_iff.mp hu.1 with
      ⟨v, hv, w, hw, hAppend⟩
    subst u
    have hEq :
        v.get ⟨i, hi⟩ = w.get ⟨j, hj⟩ := by
      rw [Sel.holds_eqIdx_iff _ (by omega) (by omega)] at hu
      calc
        v.get ⟨i, hi⟩ =
            (FinRelation.appendTuple v w).get
              ⟨i, by omega⟩ := by
          simpa using
            (FinRelation.get_appendTuple_left
              v w ⟨i, hi⟩).symm
        _ = (FinRelation.appendTuple v w).get
            ⟨n + j, by omega⟩ := hu.2
        _ = w.get ⟨j, hj⟩ := by
          simpa using
            (FinRelation.get_appendTuple_right
              v w ⟨j, hj⟩)
    simp only [candidatesIndexed, List.mem_flatMap,
      List.mem_map]
    refine ⟨v,
      (FastRelation.mem_toFinRelation_iff R v).mp hv,
      w, ?_, hProj⟩
    rw [JoinIndex.mem_lookup_ofRelation_iff]
    exact ⟨(FastRelation.mem_toFinRelation_iff S w).mp hw,
      hEq.symm⟩

/- Nested and indexed strategies have one denotation. -/
theorem eval_eq_evalIndexed
    {n m : Nat}
    (idxs : List Nat)
    (i j : Nat)
    (R : FastRelation D n)
    (S : FastRelation D m)
    (hi : i < n)
    (hj : j < m)
    (hIdx : ∀ k ∈ idxs, k < n + m) :
    (eval idxs i j R S hi hj hIdx).toFinRelation =
      (evalIndexed idxs i j R S hi hj hIdx).toFinRelation :=
    by
  rw [eval_correct, evalIndexed_correct]

end SPJFast

end Whiel
