-- Author: Jesse Comer
import Databases.RelCalc.AdomSemantics
import Mathlib.Data.Finset.Union

/-
  This file defines term substitution for RelCalc terms
  and formulas.

  Key definitions include:
    * `RelTerm.substTerm`
    * `RelTerm.Substitution`
    * `RelTerm.substTerms`
    * `RelCalc.Formula.substTerm`
    * `RelCalc.Formula.substTerms`
    * `RelCalc.Formula.FreeForTermSubst`
    * `RelCalc.Formula.FreeForTermSubstMap`

  Correctness is proven by:
    * `RelTerm.eval_substTerm`
    * `RelTerm.eval_substTerms`
    * `RelCalc.Formula.arbitraryAssignSatIn_substTerm`
    * `RelCalc.Formula.arbitraryAssignSatIn_substTerms`
    * `RelCalc.Formula.satIn_substTerm`
    * `RelCalc.Formula.satIn_substTerms`
    * `RelCalc.Formula.adomSat_substTerm`
    * `RelCalc.Formula.adomSat_substTerms`

  Relation-symbol substitution lives in the formula
  substitution file.
-/

------------------------------------------------------------
-- Term Substitution
------------------------------------------------------------

open RelCalc

namespace RelTerm

variable {D : Type}
variable [Domain D]

/- Substitute a term for one variable in a term. -/
def substTerm
    (t : RelTerm D)
    (x : Var)
    (u : RelTerm D) :
    RelTerm D :=
  match t with
  | .var y => if y = x then u else .var y
  | .const d => .const d

/- Substitute through a tuple of terms. -/
private def substTermTuple
    {n : Nat}
    (ts : Vector (RelTerm D) n)
    (x : Var)
    (u : RelTerm D) :
    Vector (RelTerm D) n :=
  Vector.ofFn (fun i => (ts.get i).substTerm x u)

/-
  Updating a variable absent from a term does not affect it.
-/
private theorem eval_update_of_not_mem
    {σ : Assign D}
    {x : Var}
    {d : D}
    (t : RelTerm D)
    (hx : x ∉ t.vars) :
    t.eval (Assign.update σ x d) = t.eval σ := by
  cases t with
  | var y =>
      have hyx : y ≠ x := by
        intro h
        exact hx (by simp [vars, h])
      simp [eval, Assign.update, hyx]
  | const _ =>
      simp [eval]

/- Term substitution is assignment update semantically. -/
theorem eval_substTerm
    (t : RelTerm D)
    (x : Var)
    (u : RelTerm D)
    (σ : Assign D) :
    (t.substTerm x u).eval σ =
      t.eval (Assign.update σ x (u.eval σ)) := by
  cases t with
  | var y =>
      by_cases hyx : y = x
      · subst hyx
        simp [substTerm, eval, Assign.update]
      · simp [substTerm, eval, Assign.update, hyx]
  | const _ =>
      simp [substTerm, eval]

/- Substitution is identity when the variable is absent. -/
private theorem substTerm_vacuous
    (t : RelTerm D)
    {x : Var}
    {u : RelTerm D}
    (hx : x ∉ t.vars) :
    t.substTerm x u = t := by
  cases t with
  | var y =>
      have hyx : y ≠ x := by
        intro h
        exact hx (by simp [vars, h])
      simp [substTerm, hyx]
  | const _ =>
      simp [substTerm]

/- Variables after term substitution. -/
private theorem mem_vars_substTerm_iff
    {t u : RelTerm D}
    {x z : Var} :
    z ∈ (t.substTerm x u).vars ↔
      (z ∈ t.vars ∧ z ≠ x) ∨
        (z ∈ u.vars ∧ x ∈ t.vars) := by
  cases t with
  | var y =>
      by_cases hyx : y = x
      · subst x
        simp [substTerm, vars]
      · by_cases hzy : z = y
        · subst hzy
          simp [substTerm, vars, hyx]
        · have hxy : x ≠ y := by
            intro h
            exact hyx h.symm
          simp [substTerm, vars, hyx, hzy, hxy]
  | const _ =>
      simp [substTerm, vars]

/- Constants after term substitution. -/
private theorem constants_substTerm_subset
    (t u : RelTerm D)
    (x : Var) :
    (t.substTerm x u).constants ⊆
      t.constants ∪ u.constants := by
  intro d hd
  cases t with
  | var y =>
      by_cases hyx : y = x
      · have hdU : d ∈ u.constants := by
          simpa [substTerm, constants, hyx] using hd
        exact Finset.mem_union.mpr (Or.inr hdU)
      · simp [substTerm, constants, hyx] at hd
  | const c =>
      exact Finset.mem_union.mpr <| by
        left
        simpa [substTerm, constants] using hd

/- List variables are exactly variables of member terms. -/
theorem mem_listVars_iff
    {ts : List (RelTerm D)}
    {x : Var} :
    x ∈ listVars ts ↔
      ∃ t ∈ ts, x ∈ t.vars := by
  induction ts with
  | nil =>
      simp [listVars]
  | cons t ts ih =>
      simp [listVars, ih, Finset.mem_union]

/- Tuple variables are exactly variables of coordinates. -/
theorem mem_tupleVars_iff
    {n : Nat}
    {ts : Vector (RelTerm D) n}
    {x : Var} :
    x ∈ tupleVars ts ↔
      ∃ i : Fin n, x ∈ (ts.get i).vars := by
  rw [tupleVars, mem_listVars_iff]
  constructor
  · rintro ⟨t, ht, hx⟩
    rcases (List.mem_iff_get.mp ht) with ⟨i, hi⟩
    let j : Fin n :=
      ⟨i.1, by
        simpa [Vector.length_toList] using i.2⟩
    have hVec : ts.get j = t := by
      change ts[j.1] = t
      have hList : ts.toList[i.1] = t := by
        simpa using hi
      have hCoord : ts.toList[i.1] = ts[i.1] :=
        Vector.getElem_toList i.2
      exact hCoord.symm.trans hList
    exact ⟨j, by simpa [hVec] using hx⟩
  · rintro ⟨i, hx⟩
    exact ⟨ts.get i, List.get_mem _ _, hx⟩

/- Tuple substitution is assignment update semantically. -/
theorem evalVector_substTermTuple
    {σ : Assign D}
    {n : Nat}
    (ts : Vector (RelTerm D) n)
    (x : Var)
    (u : RelTerm D) :
    evalVector σ (substTermTuple ts x u) =
      evalVector (Assign.update σ x (u.eval σ)) ts := by
  apply Vector.ext
  intro i hi
  rw [evalVector, evalVector,
    Vector.getElem_ofFn,
    Vector.getElem_ofFn]
  change
    eval σ ((substTermTuple ts x u)[i]) =
      eval (Assign.update σ x (u.eval σ)) (ts[i])
  rw [substTermTuple, Vector.getElem_ofFn]
  exact eval_substTerm (ts.get ⟨i, hi⟩) x u σ

/-
  Tuple substitution is identity when the variable is
  absent.
-/
private theorem substTermTuple_vacuous
    {n : Nat}
    (ts : Vector (RelTerm D) n)
    {x : Var}
    {u : RelTerm D}
    (hx : x ∉ tupleVars ts) :
    substTermTuple ts x u = ts := by
  apply Vector.ext
  intro i hi
  simp only [substTermTuple, Vector.getElem_ofFn]
  exact substTerm_vacuous (ts.get ⟨i, hi⟩) (by
    intro hxTerm
    exact hx
      ((mem_tupleVars_iff
        (ts := ts) (x := x)).mpr ⟨⟨i, hi⟩, hxTerm⟩))

/- Variables after tuple substitution. -/
private theorem mem_tupleVars_substTermTuple_iff
    {n : Nat}
    {ts : Vector (RelTerm D) n}
    {x z : Var}
    {u : RelTerm D} :
    z ∈ tupleVars (substTermTuple ts x u) ↔
      (z ∈ tupleVars ts ∧ z ≠ x) ∨
        (z ∈ u.vars ∧ x ∈ tupleVars ts) := by
  constructor
  · intro hz
    rcases
        (mem_tupleVars_iff
          (ts := substTermTuple ts x u) (x := z)).mp hz with
      ⟨i, hi⟩
    have hTerm :
        z ∈ ((ts.get i).substTerm x u).vars := by
      have hi' :
          z ∈ ((substTermTuple ts x u)[i.1]).vars := by
        simpa using hi
      rw [substTermTuple, Vector.getElem_ofFn] at hi'
      exact hi'
    rcases
        (mem_vars_substTerm_iff
          (t := ts.get i) (u := u)
          (x := x) (z := z)).mp hTerm with
      h | h
    · exact Or.inl
        ⟨(mem_tupleVars_iff
          (ts := ts) (x := z)).mpr ⟨i, h.1⟩,
          h.2⟩
    · exact Or.inr
        ⟨h.1,
          (mem_tupleVars_iff
            (ts := ts) (x := x)).mpr ⟨i, h.2⟩⟩
  · intro hz
    rcases hz with h | h
    · rcases
          (mem_tupleVars_iff
            (ts := ts) (x := z)).mp h.1 with
        ⟨i, hi⟩
      apply
        (mem_tupleVars_iff
          (ts := substTermTuple ts x u) (x := z)).mpr
      refine ⟨i, ?_⟩
      change z ∈ ((substTermTuple ts x u)[i.1]).vars
      rw [substTermTuple, Vector.getElem_ofFn]
      exact
        (mem_vars_substTerm_iff
          (t := ts.get i) (u := u)
          (x := x) (z := z)).mpr
          (Or.inl ⟨hi, h.2⟩)
    · rcases
          (mem_tupleVars_iff
            (ts := ts) (x := x)).mp h.2 with
        ⟨i, hi⟩
      apply
        (mem_tupleVars_iff
          (ts := substTermTuple ts x u) (x := z)).mpr
      refine ⟨i, ?_⟩
      change z ∈ ((substTermTuple ts x u)[i.1]).vars
      rw [substTermTuple, Vector.getElem_ofFn]
      exact
        (mem_vars_substTerm_iff
          (t := ts.get i) (u := u)
          (x := x) (z := z)).mpr
          (Or.inr ⟨h.1, hi⟩)

/- List constants are exactly constants of member terms. -/
private theorem mem_listConstants_iff
    {ts : List (RelTerm D)}
    {d : D} :
    d ∈ listConstants ts ↔
      ∃ t ∈ ts, d ∈ t.constants := by
  induction ts with
  | nil =>
      simp [listConstants]
  | cons t ts ih =>
      simp [listConstants, ih, Finset.mem_union]

/- Tuple constants are exactly constants of coordinates. -/
private theorem mem_tupleConstants_iff
    {n : Nat}
    {ts : Vector (RelTerm D) n}
    {d : D} :
    d ∈ tupleConstants ts ↔
      ∃ i : Fin n, d ∈ (ts.get i).constants := by
  rw [tupleConstants, mem_listConstants_iff]
  constructor
  · rintro ⟨t, ht, hd⟩
    rcases (List.mem_iff_get.mp ht) with ⟨i, hi⟩
    let j : Fin n :=
      ⟨i.1, by
        simpa [Vector.length_toList] using i.2⟩
    have hVec : ts.get j = t := by
      change ts[j.1] = t
      have hList : ts.toList[i.1] = t := by
        simpa using hi
      have hCoord : ts.toList[i.1] = ts[i.1] :=
        Vector.getElem_toList i.2
      exact hCoord.symm.trans hList
    exact ⟨j, by simpa [hVec] using hd⟩
  · rintro ⟨i, hd⟩
    exact ⟨ts.get i, List.get_mem _ _, hd⟩

/- Constants after tuple substitution are controlled. -/
private theorem tupleConstants_substTermTuple_subset
    {n : Nat}
    (ts : Vector (RelTerm D) n)
    (x : Var)
    (u : RelTerm D) :
    tupleConstants (substTermTuple ts x u) ⊆
      tupleConstants ts ∪ u.constants := by
  intro d hd
  rcases
      (mem_tupleConstants_iff
        (ts := substTermTuple ts x u) (d := d)).mp hd with
    ⟨i, hi⟩
  have hTerm :
      d ∈ ((ts.get i).substTerm x u).constants := by
    have hi' :
        d ∈ ((substTermTuple ts x u)[i.1]).constants := by
      simpa using hi
    rw [substTermTuple, Vector.getElem_ofFn] at hi'
    exact hi'
  have hSub :=
    constants_substTerm_subset (ts.get i) u x hTerm
  rcases Finset.mem_union.mp hSub with hOld | hNew
  · exact Finset.mem_union.mpr <|
      Or.inl
        ((mem_tupleConstants_iff
          (ts := ts) (d := d)).mpr ⟨i, hOld⟩)
  · exact Finset.mem_union.mpr (Or.inr hNew)

end RelTerm

------------------------------------------------------------
-- Simultaneous Term Substitution
------------------------------------------------------------

namespace RelTerm

variable {D : Type}
variable [Domain D]

/- A simultaneous substitution sends variables to terms. -/
abbrev Substitution (D : Type) [Domain D] :=
  Var → RelTerm D

namespace Substitution

/- The identity substitution. -/
def ident : Substitution D :=
  fun x => .var x

/- Update a simultaneous substitution at one variable. -/
def update
    (ρ : Substitution D)
    (x : Var)
    (t : RelTerm D) :
    Substitution D :=
  fun y => if y = x then t else ρ y

/- Evaluate a substitution to an assignment. -/
def eval
    (ρ : Substitution D)
    (σ : Assign D) :
    Assign D :=
  fun x => (ρ x).eval σ

/- Build substitution from parameters and arguments. -/
def ofVector
    {n : Nat}
    (xs : Vector Var n)
    (ts : Vector (RelTerm D) n) :
    Substitution D :=
  fun x =>
    match xs.toList.idxOf? x with
    | none => .var x
    | some i =>
        match ts.toList[i]? with
        | none => .var x
        | some t => t

/- The variables introduced by a substitution over `S`. -/
def varsOn
    (ρ : Substitution D)
    (S : Finset Var) :
    Finset Var :=
  S.biUnion fun x => (ρ x).vars

/- Lookup of vector-built substitutions at parameters. -/
theorem ofVector_get
    {n : Nat}
    {xs : Vector Var n}
    {ts : Vector (RelTerm D) n}
    (hNoDup : xs.toList.Nodup)
    (i : Fin n) :
    ofVector xs ts (xs.get i) = ts.get i := by
  unfold ofVector
  have hxMem : xs.get i ∈ xs.toList := by
    change xs[i.1] ∈ xs.toList
    rw [Vector.mem_toList_iff]
    exact Vector.getElem_mem i.2
  cases hIdx : xs.toList.idxOf? (xs.get i) with
  | none =>
      have hNot :
          xs.get i ∉ xs.toList :=
        (List.idxOf?_eq_none_iff
          (l := xs.toList) (a := xs.get i)).mp hIdx
      exact False.elim (hNot hxMem)
  | some j =>
      rcases
          (List.idxOf?_eq_some_iff
            (l := xs.toList) (a := xs.get i)
            (i := j)).mp hIdx with
        ⟨hjList, hGet, _⟩
      have hj : j < n := by
        simpa [Vector.length_toList] using hjList
      have hiList : i.1 < xs.toList.length := by
        simp [Vector.length_toList]
      have hAtI :
          xs.toList[i.1] = xs.get i := by
        exact Vector.getElem_toList hiList
      have hji : j = i.1 := by
        exact (hNoDup.getElem_inj_iff).mp
          (by rw [hGet, hAtI])
      have hjTerm : j < ts.toList.length := by
        simpa [Vector.length_toList] using hj
      have hVal :
          (match ts.toList[j]? with
          | none => .var (xs.get i)
          | some t => t) = ts.get i := by
        rw [List.getElem?_eq_getElem hjTerm]
        subst hji
        rw [Vector.getElem_toList hjTerm]
        rfl
      simpa [hIdx] using hVal

/- Vector-built substitutions realize evaluated tuples. -/
theorem eval_ofVector_realizes
    {σ : Assign D}
    {n : Nat}
    {xs : Vector Var n}
    {ts : Vector (RelTerm D) n}
    (hNoDup : xs.toList.Nodup) :
    Assign.Realizes
      (eval (ofVector xs ts) σ)
      xs
      (RelTerm.evalVector σ ts) := by
  intro i
  have hGet := ofVector_get
    (D := D) (xs := xs) (ts := ts)
    hNoDup i
  rw [RelTerm.evalVector]
  change
    (ofVector xs ts (xs.get i)).eval σ =
      (Vector.ofFn
        (fun i => RelTerm.eval σ (ts.get i)))[i.1]
  rw [Vector.getElem_ofFn]
  rw [hGet]

/- Vector-built substitution variables are tuple vars. -/
theorem varsOn_ofVector
    {n : Nat}
    {xs : Vector Var n}
    {ts : Vector (RelTerm D) n}
    (hNoDup : xs.toList.Nodup) :
    varsOn (ofVector xs ts) xs.toList.toFinset =
      RelTerm.tupleVars ts := by
  ext z
  constructor
  · intro hz
    rcases Finset.mem_biUnion.mp hz with
      ⟨x, hxSet, hzx⟩
    have hxList : x ∈ xs.toList := by
      simpa using hxSet
    rcases List.mem_iff_get.mp hxList with
      ⟨i, hi⟩
    let j : Fin n :=
      ⟨i.1, by
        simpa [Vector.length_toList] using i.2⟩
    have hVar : xs.get j = x := by
      change xs[i.1] = x
      have hCoord :
          xs.toList[i.1] = xs[i.1] :=
        Vector.getElem_toList i.2
      exact hCoord.symm.trans hi
    have hGet := ofVector_get
      (D := D) (xs := xs) (ts := ts)
      hNoDup j
    have hTerm :
        ofVector xs ts x = ts.get j := by
      simpa [hVar] using hGet
    exact
      (RelTerm.mem_tupleVars_iff
        (ts := ts) (x := z)).mpr
        ⟨j, by simpa [hTerm] using hzx⟩
  · intro hz
    rcases
        (RelTerm.mem_tupleVars_iff
          (ts := ts) (x := z)).mp hz with
      ⟨i, hzi⟩
    have hGet := ofVector_get
      (D := D) (xs := xs) (ts := ts)
      hNoDup i
    exact Finset.mem_biUnion.mpr
      ⟨xs.get i,
        by
          change xs[i.1] ∈ xs.toList.toFinset
          simp,
        by simpa [hGet] using hzi⟩

/- `varsOn` distributes over union. -/
private theorem varsOn_union
    (ρ : Substitution D)
    (S T : Finset Var) :
    varsOn ρ (S ∪ T) =
      varsOn ρ S ∪ varsOn ρ T := by
  ext z
  constructor
  · intro hz
    rcases Finset.mem_biUnion.mp hz with
      ⟨x, hx, hzx⟩
    rcases Finset.mem_union.mp hx with hxS | hxT
    · exact Finset.mem_union.mpr <|
        Or.inl (Finset.mem_biUnion.mpr ⟨x, hxS, hzx⟩)
    · exact Finset.mem_union.mpr <|
        Or.inr (Finset.mem_biUnion.mpr ⟨x, hxT, hzx⟩)
  · intro hz
    rcases Finset.mem_union.mp hz with hzS | hzT
    · rcases Finset.mem_biUnion.mp hzS with
        ⟨x, hx, hzx⟩
      exact Finset.mem_biUnion.mpr
        ⟨x, Finset.mem_union.mpr (Or.inl hx), hzx⟩
    · rcases Finset.mem_biUnion.mp hzT with
        ⟨x, hx, hzx⟩
      exact Finset.mem_biUnion.mpr
        ⟨x, Finset.mem_union.mpr (Or.inr hx), hzx⟩

/- Erasing a shadowed binder commutes with `varsOn`. -/
private theorem erase_varsOn_update
    (ρ : Substitution D)
    (S : Finset Var)
    (x : Var)
    (hFree :
      ∀ z ∈ S.erase x, x ∉ (ρ z).vars) :
    (varsOn (update ρ x (.var x)) S).erase x =
      varsOn ρ (S.erase x) := by
  ext z
  constructor
  · intro hz
    rcases Finset.mem_erase.mp hz with
      ⟨hzx, hzOn⟩
    rcases Finset.mem_biUnion.mp hzOn with
      ⟨w, hwS, hzw⟩
    by_cases hwx : w = x
    · have hzwx :
          z ∈ (RelTerm.var (D := D) x).vars := by
        simpa [update, hwx] using hzw
      have hzx' : z = x := by
        simpa [RelTerm.vars] using hzwx
      exact False.elim (hzx hzx')
    · exact Finset.mem_biUnion.mpr
        ⟨w, Finset.mem_erase.mpr ⟨hwx, hwS⟩,
          by simpa [update, hwx] using hzw⟩
  · intro hz
    rcases Finset.mem_biUnion.mp hz with
      ⟨w, hwErase, hzw⟩
    rcases Finset.mem_erase.mp hwErase with
      ⟨hwx, hwS⟩
    have hzx : z ≠ x := by
      intro h
      exact hFree w hwErase (by simpa [h] using hzw)
    apply Finset.mem_erase.mpr
    refine ⟨hzx, ?_⟩
    exact Finset.mem_biUnion.mpr
      ⟨w, hwS, by simpa [update, hwx] using hzw⟩

/- Shadowing commutes with evaluated assignments. -/
private theorem eval_update_agreeOn
    {ρ : Substitution D}
    {σ : Assign D}
    {x : Var}
    {d : D}
    {S : Finset Var}
    (hFree :
      ∀ z ∈ S.erase x, x ∉ (ρ z).vars) :
    Assign.AgreeOn
      (eval (update ρ x (.var x))
        (Assign.update σ x d))
      (Assign.update (eval ρ σ) x d) S := by
  intro z hz
  by_cases hzx : z = x
  · subst hzx
    simp [eval, update, Assign.update, RelTerm.eval]
  · have hzErase : z ∈ S.erase x :=
      Finset.mem_erase.mpr ⟨hzx, hz⟩
    have hEval :
        (ρ z).eval (Assign.update σ x d) =
          (ρ z).eval σ :=
      RelTerm.eval_update_of_not_mem (ρ z)
        (hFree z hzErase)
    simp [eval, update, Assign.update, hzx, hEval]

end Substitution

/- Apply a simultaneous substitution to a term. -/
def substTerms
    (t : RelTerm D)
    (ρ : Substitution D) :
    RelTerm D :=
  match t with
  | .var x => ρ x
  | .const d => .const d

/- Apply a simultaneous substitution to a tuple. -/
private def substTermsTuple
    {n : Nat}
    (ts : Vector (RelTerm D) n)
    (ρ : Substitution D) :
    Vector (RelTerm D) n :=
  Vector.ofFn fun i => (ts.get i).substTerms ρ

/- Semantics of simultaneous substitution on terms. -/
theorem eval_substTerms
    (t : RelTerm D)
    (ρ : Substitution D)
    (σ : Assign D) :
    (t.substTerms ρ).eval σ =
      t.eval (Substitution.eval ρ σ) := by
  cases t with
  | var x =>
      simp [substTerms, Substitution.eval, eval]
  | const d =>
      simp [substTerms, eval]

/- Semantics of simultaneous substitution on tuples. -/
theorem evalVector_substTermsTuple
    {n : Nat}
    (ts : Vector (RelTerm D) n)
    (ρ : Substitution D)
    (σ : Assign D) :
    evalVector σ (substTermsTuple ts ρ) =
      evalVector (Substitution.eval ρ σ) ts := by
  apply Vector.ext
  intro i hi
  rw [evalVector, evalVector,
    Vector.getElem_ofFn, Vector.getElem_ofFn]
  change
    eval σ ((substTermsTuple ts ρ)[i]) =
      eval (Substitution.eval ρ σ) (ts[i])
  rw [substTermsTuple, Vector.getElem_ofFn]
  exact eval_substTerms (ts.get ⟨i, hi⟩) ρ σ

/- Variables after simultaneous term substitution. -/
private theorem vars_substTerms
    (t : RelTerm D)
    (ρ : Substitution D) :
    (t.substTerms ρ).vars =
      Substitution.varsOn ρ t.vars := by
  cases t with
  | var x =>
      simp [substTerms, Substitution.varsOn, vars]
  | const d =>
      simp [substTerms, Substitution.varsOn, vars]

/- Variables after simultaneous tuple substitution. -/
private theorem tupleVars_substTermsTuple
    {n : Nat}
    (ts : Vector (RelTerm D) n)
    (ρ : Substitution D) :
    tupleVars (substTermsTuple ts ρ) =
      Substitution.varsOn ρ (tupleVars ts) := by
  ext z
  constructor
  · intro hz
    rcases
        (mem_tupleVars_iff
          (ts := substTermsTuple ts ρ) (x := z)).mp hz with
      ⟨i, hi⟩
    change z ∈ ((substTermsTuple ts ρ)[i.1]).vars at hi
    rw [substTermsTuple, Vector.getElem_ofFn] at hi
    have hVars :=
      congrArg (fun S => z ∈ S)
        (vars_substTerms (ts.get i) ρ)
    have hzOn :
        z ∈ Substitution.varsOn ρ (ts.get i).vars := by
      simpa using hVars.mp hi
    rcases Finset.mem_biUnion.mp hzOn with
      ⟨x, hx, hzx⟩
    apply Finset.mem_biUnion.mpr
    exact ⟨x,
      (mem_tupleVars_iff
        (ts := ts) (x := x)).mpr ⟨i, hx⟩,
      hzx⟩
  · intro hz
    rcases Finset.mem_biUnion.mp hz with
      ⟨x, hx, hzx⟩
    rcases
        (mem_tupleVars_iff
          (ts := ts) (x := x)).mp hx with
      ⟨i, hi⟩
    apply
      (mem_tupleVars_iff
        (ts := substTermsTuple ts ρ) (x := z)).mpr
    refine ⟨i, ?_⟩
    change z ∈ ((substTermsTuple ts ρ)[i.1]).vars
    rw [substTermsTuple, Vector.getElem_ofFn]
    have hVars :=
      congrArg (fun S => z ∈ S)
        (vars_substTerms (ts.get i) ρ)
    apply hVars.mpr
    exact Finset.mem_biUnion.mpr ⟨x, hi, hzx⟩

end RelTerm

------------------------------------------------------------
-- Formula Substitution
------------------------------------------------------------

namespace RelCalc

namespace Formula

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- Substitute a term for one free variable in a formula. -/
def substTerm
    (φ : Formula D Γ)
    (x : Var)
    (u : RelTerm D) :
    Formula D Γ :=
  match φ with
  | .top => .top
  | .bot => .bot
  | .eq t₁ t₂ =>
      .eq (t₁.substTerm x u) (t₂.substTerm x u)
  | .rel a =>
      .rel
        { rel := a.rel
          args := RelTerm.substTermTuple a.args x u }
  | .and φ ψ =>
      .and (substTerm φ x u) (substTerm ψ x u)
  | .or φ ψ =>
      .or (substTerm φ x u) (substTerm ψ x u)
  | .not φ =>
      .not (substTerm φ x u)
  | .imp φ ψ =>
      .imp (substTerm φ x u) (substTerm ψ x u)
  | .iff φ ψ =>
      .iff (substTerm φ x u) (substTerm ψ x u)
  | .forall_ y φ =>
      if y = x then .forall_ y φ
      else .forall_ y (substTerm φ x u)
  | .exists_ y φ =>
      if y = x then .exists_ y φ
      else .exists_ y (substTerm φ x u)

/- `u` may replace free `x` in `φ` without capture. -/
def FreeForTermSubst :
    Formula D Γ → Var → RelTerm D → Prop
| .top, _, _ => True
| .bot, _, _ => True
| .eq _ _, _, _ => True
| .rel _, _, _ => True
| .and φ ψ, x, u =>
    FreeForTermSubst φ x u ∧ FreeForTermSubst ψ x u
| .or φ ψ, x, u =>
    FreeForTermSubst φ x u ∧ FreeForTermSubst ψ x u
| .not φ, x, u =>
    FreeForTermSubst φ x u
| .imp φ ψ, x, u =>
    FreeForTermSubst φ x u ∧ FreeForTermSubst ψ x u
| .iff φ ψ, x, u =>
    FreeForTermSubst φ x u ∧ FreeForTermSubst ψ x u
| .forall_ y φ, x, u =>
    y = x ∨ (y ∉ u.vars ∧ FreeForTermSubst φ x u)
| .exists_ y φ, x, u =>
    y = x ∨ (y ∉ u.vars ∧ FreeForTermSubst φ x u)

/- Constants after formula substitution are controlled. -/
private theorem constants_substTerm_subset
    (φ : Formula D Γ)
    (x : Var)
    (u : RelTerm D) :
    (φ.substTerm x u).constants ⊆
      φ.constants ∪ u.constants := by
  induction φ with
  | top =>
      intro d hd
      simp [substTerm, constants] at hd
  | bot =>
      intro d hd
      simp [substTerm, constants] at hd
  | eq t₁ t₂ =>
      intro d hd
      simp only [substTerm, constants,
        Finset.mem_union, or_assoc] at hd ⊢
      rcases hd with hd | hd
      · have hSub :=
          RelTerm.constants_substTerm_subset t₁ u x hd
        rcases Finset.mem_union.mp hSub with hOld | hNew
        · exact Or.inl hOld
        · exact Or.inr (Or.inr hNew)
      · have hSub :=
          RelTerm.constants_substTerm_subset t₂ u x hd
        rcases Finset.mem_union.mp hSub with hOld | hNew
        · exact Or.inr (Or.inl hOld)
        · exact Or.inr (Or.inr hNew)
  | rel a =>
      intro d hd
      have hSub :=
        RelTerm.tupleConstants_substTermTuple_subset
          a.args x u hd
      simpa [substTerm, constants] using hSub
  | and φ ψ ihφ ihψ =>
      intro d hd
      simp only [substTerm, constants,
        Finset.mem_union, or_assoc] at hd ⊢
      rcases hd with hd | hd
      · have hSub := ihφ hd
        rcases Finset.mem_union.mp hSub with hOld | hNew
        · exact Or.inl hOld
        · exact Or.inr (Or.inr hNew)
      · have hSub := ihψ hd
        rcases Finset.mem_union.mp hSub with hOld | hNew
        · exact Or.inr (Or.inl hOld)
        · exact Or.inr (Or.inr hNew)
  | or φ ψ ihφ ihψ =>
      intro d hd
      simp only [substTerm, constants,
        Finset.mem_union, or_assoc] at hd ⊢
      rcases hd with hd | hd
      · have hSub := ihφ hd
        rcases Finset.mem_union.mp hSub with hOld | hNew
        · exact Or.inl hOld
        · exact Or.inr (Or.inr hNew)
      · have hSub := ihψ hd
        rcases Finset.mem_union.mp hSub with hOld | hNew
        · exact Or.inr (Or.inl hOld)
        · exact Or.inr (Or.inr hNew)
  | not φ ih =>
      intro d hd
      exact ih (by simpa [substTerm, constants] using hd)
  | imp φ ψ ihφ ihψ =>
      intro d hd
      simp only [substTerm, constants,
        Finset.mem_union, or_assoc] at hd ⊢
      rcases hd with hd | hd
      · have hSub := ihφ hd
        rcases Finset.mem_union.mp hSub with hOld | hNew
        · exact Or.inl hOld
        · exact Or.inr (Or.inr hNew)
      · have hSub := ihψ hd
        rcases Finset.mem_union.mp hSub with hOld | hNew
        · exact Or.inr (Or.inl hOld)
        · exact Or.inr (Or.inr hNew)
  | iff φ ψ ihφ ihψ =>
      intro d hd
      simp only [substTerm, constants,
        Finset.mem_union, or_assoc] at hd ⊢
      rcases hd with hd | hd
      · have hSub := ihφ hd
        rcases Finset.mem_union.mp hSub with hOld | hNew
        · exact Or.inl hOld
        · exact Or.inr (Or.inr hNew)
      · have hSub := ihψ hd
        rcases Finset.mem_union.mp hSub with hOld | hNew
        · exact Or.inr (Or.inl hOld)
        · exact Or.inr (Or.inr hNew)
  | forall_ y φ ih =>
      intro d hd
      by_cases hyx : y = x
      · have hOld : d ∈ φ.constants :=
          by simpa [substTerm, constants, hyx] using hd
        exact Finset.mem_union.mpr (Or.inl hOld)
      · have hSub := ih
          (by simpa [substTerm, constants, hyx] using hd)
        simpa [constants] using hSub
  | exists_ y φ ih =>
      intro d hd
      by_cases hyx : y = x
      · have hOld : d ∈ φ.constants :=
          by simpa [substTerm, constants, hyx] using hd
        exact Finset.mem_union.mpr (Or.inl hOld)
      · have hSub := ih
          (by simpa [substTerm, constants, hyx] using hd)
        simpa [constants] using hSub

/-
  Membership in substituted free variables is controlled.
-/
private theorem mem_freeVars_substTerm_of
    {φ : Formula D Γ}
    {x z : Var}
    {u : RelTerm D}
    (hz : z ∈ (φ.substTerm x u).freeVars) :
    (z ∈ φ.freeVars ∧ z ≠ x) ∨ z ∈ u.vars := by
  induction φ with
  | top =>
      simp [substTerm, freeVars] at hz
  | bot =>
      simp [substTerm, freeVars] at hz
  | eq t₁ t₂ =>
      simp only [substTerm, freeVars,
        Finset.mem_union] at hz ⊢
      rcases hz with hz | hz
      · rcases
          (RelTerm.mem_vars_substTerm_iff
            (t := t₁) (u := u)
            (x := x) (z := z)).mp hz with
          h | h
        · exact Or.inl ⟨Or.inl h.1, h.2⟩
        · exact Or.inr h.1
      · rcases
          (RelTerm.mem_vars_substTerm_iff
            (t := t₂) (u := u)
            (x := x) (z := z)).mp hz with
          h | h
        · exact Or.inl ⟨Or.inr h.1, h.2⟩
        · exact Or.inr h.1
  | rel a =>
      simp only [substTerm, freeVars] at hz ⊢
      rcases
          (RelTerm.mem_tupleVars_substTermTuple_iff
            (ts := a.args) (x := x)
            (z := z) (u := u)).mp hz with
        h | h
      · exact Or.inl h
      · exact Or.inr h.1
  | and φ ψ ihφ ihψ =>
      simp only [substTerm, freeVars,
        Finset.mem_union] at hz ⊢
      rcases hz with hz | hz
      · rcases ihφ hz with h | h
        · exact Or.inl ⟨Or.inl h.1, h.2⟩
        · exact Or.inr h
      · rcases ihψ hz with h | h
        · exact Or.inl ⟨Or.inr h.1, h.2⟩
        · exact Or.inr h
  | or φ ψ ihφ ihψ =>
      simp only [substTerm, freeVars,
        Finset.mem_union] at hz ⊢
      rcases hz with hz | hz
      · rcases ihφ hz with h | h
        · exact Or.inl ⟨Or.inl h.1, h.2⟩
        · exact Or.inr h
      · rcases ihψ hz with h | h
        · exact Or.inl ⟨Or.inr h.1, h.2⟩
        · exact Or.inr h
  | not φ ih =>
      exact ih (by simpa [substTerm, freeVars] using hz)
  | imp φ ψ ihφ ihψ =>
      simp only [substTerm, freeVars,
        Finset.mem_union] at hz ⊢
      rcases hz with hz | hz
      · rcases ihφ hz with h | h
        · exact Or.inl ⟨Or.inl h.1, h.2⟩
        · exact Or.inr h
      · rcases ihψ hz with h | h
        · exact Or.inl ⟨Or.inr h.1, h.2⟩
        · exact Or.inr h
  | iff φ ψ ihφ ihψ =>
      simp only [substTerm, freeVars,
        Finset.mem_union] at hz ⊢
      rcases hz with hz | hz
      · rcases ihφ hz with h | h
        · exact Or.inl ⟨Or.inl h.1, h.2⟩
        · exact Or.inr h
      · rcases ihψ hz with h | h
        · exact Or.inl ⟨Or.inr h.1, h.2⟩
        · exact Or.inr h
  | forall_ y φ ih =>
      by_cases hyx : y = x
      · have hzBody : z ∈ φ.freeVars.erase x :=
          by simpa [substTerm, freeVars, hyx] using hz
        exact Or.inl
          ⟨by
            simpa [freeVars, hyx] using hzBody,
          (Finset.mem_erase.mp hzBody).1⟩
      · have hzBody :
            z ∈ (φ.substTerm x u).freeVars.erase y :=
          by simpa [substTerm, freeVars, hyx] using hz
        rcases Finset.mem_erase.mp hzBody with
          ⟨hzy, hzSub⟩
        rcases ih hzSub with h | h
        · exact Or.inl
            ⟨by
              simp [freeVars, Finset.mem_erase, hzy, h.1],
            h.2⟩
        · exact Or.inr h
  | exists_ y φ ih =>
      by_cases hyx : y = x
      · have hzBody : z ∈ φ.freeVars.erase x :=
          by simpa [substTerm, freeVars, hyx] using hz
        exact Or.inl
          ⟨by
            simpa [freeVars, hyx] using hzBody,
          (Finset.mem_erase.mp hzBody).1⟩
      · have hzBody :
            z ∈ (φ.substTerm x u).freeVars.erase y :=
          by simpa [substTerm, freeVars, hyx] using hz
        rcases Finset.mem_erase.mp hzBody with
          ⟨hzy, hzSub⟩
        rcases ih hzSub with h | h
        · exact Or.inl
            ⟨by
              simp [freeVars, Finset.mem_erase, hzy, h.1],
            h.2⟩
        · exact Or.inr h

/- Exact free-variable behavior for free substitutions. -/
private theorem mem_freeVars_substTerm_iff
    {φ : Formula D Γ}
    {x z : Var}
    {u : RelTerm D}
    (hFree : φ.FreeForTermSubst x u) :
    z ∈ (φ.substTerm x u).freeVars ↔
      (z ∈ φ.freeVars ∧ z ≠ x) ∨
        (z ∈ u.vars ∧ x ∈ φ.freeVars) := by
  induction φ with
  | top =>
      simp [substTerm, freeVars]
  | bot =>
      simp [substTerm, freeVars]
  | eq t₁ t₂ =>
      constructor
      · intro hz
        simp only [substTerm, freeVars,
          Finset.mem_union] at hz
        rcases hz with hz | hz
        · rcases
            (RelTerm.mem_vars_substTerm_iff
              (t := t₁) (u := u)
              (x := x) (z := z)).mp hz with
            h | h
          · exact Or.inl
              ⟨by
                simpa [freeVars] using
                  Finset.mem_union.mpr (Or.inl h.1),
              h.2⟩
          · exact Or.inr
              ⟨h.1, Finset.mem_union.mpr (Or.inl h.2)⟩
        · rcases
            (RelTerm.mem_vars_substTerm_iff
              (t := t₂) (u := u)
              (x := x) (z := z)).mp hz with
            h | h
          · exact Or.inl
              ⟨by
                simpa [freeVars] using
                  Finset.mem_union.mpr (Or.inr h.1),
              h.2⟩
          · exact Or.inr
              ⟨h.1, Finset.mem_union.mpr (Or.inr h.2)⟩
      · intro hz
        simp only [substTerm, freeVars,
          Finset.mem_union] at hz ⊢
        rcases hz with h | h
        · rcases h.1 with hz₁ | hz₂
          · exact Or.inl
              ((RelTerm.mem_vars_substTerm_iff
                (t := t₁) (u := u)
                (x := x) (z := z)).mpr
                (Or.inl ⟨hz₁, h.2⟩))
          · exact Or.inr
              ((RelTerm.mem_vars_substTerm_iff
                (t := t₂) (u := u)
                (x := x) (z := z)).mpr
                (Or.inl ⟨hz₂, h.2⟩))
        · rcases h.2 with hx₁ | hx₂
          · exact Or.inl
              ((RelTerm.mem_vars_substTerm_iff
                (t := t₁) (u := u)
                (x := x) (z := z)).mpr
                (Or.inr ⟨h.1, hx₁⟩))
          · exact Or.inr
              ((RelTerm.mem_vars_substTerm_iff
                (t := t₂) (u := u)
                (x := x) (z := z)).mpr
                (Or.inr ⟨h.1, hx₂⟩))
  | rel a =>
      simpa [substTerm, freeVars, RelAtom.vars] using
        (RelTerm.mem_tupleVars_substTermTuple_iff
          (ts := a.args) (x := x) (z := z) (u := u))
  | and φ ψ ihφ ihψ =>
      rcases hFree with ⟨hφ, hψ⟩
      constructor
      · intro hz
        simp only [substTerm, freeVars,
          Finset.mem_union] at hz
        rcases hz with hz | hz
        · rcases (ihφ hφ).mp hz with h | h
          · exact Or.inl
              ⟨by
                simpa [freeVars] using
                  Finset.mem_union.mpr (Or.inl h.1),
              h.2⟩
          · exact Or.inr
              ⟨h.1, Finset.mem_union.mpr (Or.inl h.2)⟩
        · rcases (ihψ hψ).mp hz with h | h
          · exact Or.inl
              ⟨by
                simpa [freeVars] using
                  Finset.mem_union.mpr (Or.inr h.1),
              h.2⟩
          · exact Or.inr
              ⟨h.1, Finset.mem_union.mpr (Or.inr h.2)⟩
      · intro hz
        simp only [substTerm, freeVars,
          Finset.mem_union] at hz ⊢
        rcases hz with h | h
        · rcases h.1 with hzφ | hzψ
          · exact Or.inl ((ihφ hφ).mpr
              (Or.inl ⟨hzφ, h.2⟩))
          · exact Or.inr ((ihψ hψ).mpr
              (Or.inl ⟨hzψ, h.2⟩))
        · rcases h.2 with hxφ | hxψ
          · exact Or.inl ((ihφ hφ).mpr
              (Or.inr ⟨h.1, hxφ⟩))
          · exact Or.inr ((ihψ hψ).mpr
              (Or.inr ⟨h.1, hxψ⟩))
  | or φ ψ ihφ ihψ =>
      rcases hFree with ⟨hφ, hψ⟩
      constructor
      · intro hz
        simp only [substTerm, freeVars,
          Finset.mem_union] at hz
        rcases hz with hz | hz
        · rcases (ihφ hφ).mp hz with h | h
          · exact Or.inl
              ⟨by
                simpa [freeVars] using
                  Finset.mem_union.mpr (Or.inl h.1),
              h.2⟩
          · exact Or.inr
              ⟨h.1, Finset.mem_union.mpr (Or.inl h.2)⟩
        · rcases (ihψ hψ).mp hz with h | h
          · exact Or.inl
              ⟨by
                simpa [freeVars] using
                  Finset.mem_union.mpr (Or.inr h.1),
              h.2⟩
          · exact Or.inr
              ⟨h.1, Finset.mem_union.mpr (Or.inr h.2)⟩
      · intro hz
        simp only [substTerm, freeVars,
          Finset.mem_union] at hz ⊢
        rcases hz with h | h
        · rcases h.1 with hzφ | hzψ
          · exact Or.inl ((ihφ hφ).mpr
              (Or.inl ⟨hzφ, h.2⟩))
          · exact Or.inr ((ihψ hψ).mpr
              (Or.inl ⟨hzψ, h.2⟩))
        · rcases h.2 with hxφ | hxψ
          · exact Or.inl ((ihφ hφ).mpr
              (Or.inr ⟨h.1, hxφ⟩))
          · exact Or.inr ((ihψ hψ).mpr
              (Or.inr ⟨h.1, hxψ⟩))
  | not φ ih =>
      simpa [substTerm, freeVars] using ih hFree
  | imp φ ψ ihφ ihψ =>
      rcases hFree with ⟨hφ, hψ⟩
      constructor
      · intro hz
        simp only [substTerm, freeVars,
          Finset.mem_union] at hz
        rcases hz with hz | hz
        · rcases (ihφ hφ).mp hz with h | h
          · exact Or.inl
              ⟨by
                simpa [freeVars] using
                  Finset.mem_union.mpr (Or.inl h.1),
              h.2⟩
          · exact Or.inr
              ⟨h.1, Finset.mem_union.mpr (Or.inl h.2)⟩
        · rcases (ihψ hψ).mp hz with h | h
          · exact Or.inl
              ⟨by
                simpa [freeVars] using
                  Finset.mem_union.mpr (Or.inr h.1),
              h.2⟩
          · exact Or.inr
              ⟨h.1, Finset.mem_union.mpr (Or.inr h.2)⟩
      · intro hz
        simp only [substTerm, freeVars,
          Finset.mem_union] at hz ⊢
        rcases hz with h | h
        · rcases h.1 with hzφ | hzψ
          · exact Or.inl ((ihφ hφ).mpr
              (Or.inl ⟨hzφ, h.2⟩))
          · exact Or.inr ((ihψ hψ).mpr
              (Or.inl ⟨hzψ, h.2⟩))
        · rcases h.2 with hxφ | hxψ
          · exact Or.inl ((ihφ hφ).mpr
              (Or.inr ⟨h.1, hxφ⟩))
          · exact Or.inr ((ihψ hψ).mpr
              (Or.inr ⟨h.1, hxψ⟩))
  | iff φ ψ ihφ ihψ =>
      rcases hFree with ⟨hφ, hψ⟩
      constructor
      · intro hz
        simp only [substTerm, freeVars,
          Finset.mem_union] at hz
        rcases hz with hz | hz
        · rcases (ihφ hφ).mp hz with h | h
          · exact Or.inl
              ⟨by
                simpa [freeVars] using
                  Finset.mem_union.mpr (Or.inl h.1),
              h.2⟩
          · exact Or.inr
              ⟨h.1, Finset.mem_union.mpr (Or.inl h.2)⟩
        · rcases (ihψ hψ).mp hz with h | h
          · exact Or.inl
              ⟨by
                simpa [freeVars] using
                  Finset.mem_union.mpr (Or.inr h.1),
              h.2⟩
          · exact Or.inr
              ⟨h.1, Finset.mem_union.mpr (Or.inr h.2)⟩
      · intro hz
        simp only [substTerm, freeVars,
          Finset.mem_union] at hz ⊢
        rcases hz with h | h
        · rcases h.1 with hzφ | hzψ
          · exact Or.inl ((ihφ hφ).mpr
              (Or.inl ⟨hzφ, h.2⟩))
          · exact Or.inr ((ihψ hψ).mpr
              (Or.inl ⟨hzψ, h.2⟩))
        · rcases h.2 with hxφ | hxψ
          · exact Or.inl ((ihφ hφ).mpr
              (Or.inr ⟨h.1, hxφ⟩))
          · exact Or.inr ((ihψ hψ).mpr
              (Or.inr ⟨h.1, hxψ⟩))
  | forall_ y φ ih =>
      by_cases hyx : y = x
      · subst hyx
        by_cases hzy : z = y
        · subst hzy
          simp [substTerm, freeVars]
        · simp [substTerm, freeVars, Finset.mem_erase, hzy]
      · have hParts :
            y ∉ u.vars ∧ φ.FreeForTermSubst x u := by
          rcases hFree with hEq | hRest
          · exact False.elim (hyx hEq)
          · exact hRest
        by_cases hzy : z = y
        · subst hzy
          simp [substTerm, freeVars, hyx, hParts.1]
        · simp [substTerm, freeVars, Finset.mem_erase,
            hyx, hzy, ih hParts.2]
          tauto
  | exists_ y φ ih =>
      by_cases hyx : y = x
      · subst hyx
        by_cases hzy : z = y
        · subst hzy
          simp [substTerm, freeVars]
        · simp [substTerm, freeVars, Finset.mem_erase, hzy]
      · have hParts :
            y ∉ u.vars ∧ φ.FreeForTermSubst x u := by
          rcases hFree with hEq | hRest
          · exact False.elim (hyx hEq)
          · exact hRest
        by_cases hzy : z = y
        · subst hzy
          simp [substTerm, freeVars, hyx, hParts.1]
        · simp [substTerm, freeVars, Finset.mem_erase,
            hyx, hzy, ih hParts.2]
          tauto

/- Free-variable set after a free substitution. -/
theorem freeVars_substTerm
    (φ : Formula D Γ)
    (x : Var)
    (u : RelTerm D)
    (hFree : φ.FreeForTermSubst x u) :
    (φ.substTerm x u).freeVars =
      φ.freeVars.erase x ∪
        if x ∈ φ.freeVars then u.vars else ∅ := by
  ext z
  by_cases hx : x ∈ φ.freeVars
  · constructor
    · intro hz
      rcases
          (mem_freeVars_substTerm_iff
            (φ := φ) (x := x) (z := z)
            (u := u) hFree).mp hz with
        hOld | hNew
      · exact Finset.mem_union.mpr <|
          Or.inl (Finset.mem_erase.mpr ⟨hOld.2, hOld.1⟩)
      · have hIf :
            z ∈
              (if x ∈ φ.freeVars then
                u.vars
              else
                ∅) := by
          simpa [hx] using hNew.1
        exact Finset.mem_union.mpr (Or.inr hIf)
    · intro hz
      rcases Finset.mem_union.mp hz with hOld | hNew
      · rcases
          Finset.mem_erase.mp hOld with
        ⟨hzx, hzφ⟩
        exact
          (mem_freeVars_substTerm_iff
            (φ := φ) (x := x) (z := z)
            (u := u) hFree).mpr
            (Or.inl ⟨hzφ, hzx⟩)
      · have hU : z ∈ u.vars := by
          simpa [hx] using hNew
        exact
          (mem_freeVars_substTerm_iff
            (φ := φ) (x := x) (z := z)
            (u := u) hFree).mpr
            (Or.inr ⟨hU, hx⟩)
  · constructor
    · intro hz
      rcases
          (mem_freeVars_substTerm_iff
            (φ := φ) (x := x) (z := z)
            (u := u) hFree).mp hz with
        hOld | hNew
      · exact Finset.mem_union.mpr <|
          Or.inl (Finset.mem_erase.mpr ⟨hOld.2, hOld.1⟩)
      · exact False.elim (hx hNew.2)
    · intro hz
      rcases Finset.mem_union.mp hz with hOld | hNew
      · rcases
          Finset.mem_erase.mp hOld with
        ⟨hzx, hzφ⟩
        exact
          (mem_freeVars_substTerm_iff
            (φ := φ) (x := x) (z := z)
            (u := u) hFree).mpr
            (Or.inl ⟨hzφ, hzx⟩)
      · have hEmpty : z ∈ (∅ : Finset Var) := by
          have hIf :
              (if x ∈ φ.freeVars then u.vars else ∅) =
                (∅ : Finset Var) := by
            simp [hx]
          rw [hIf] at hNew
          exact hNew
        simp at hEmpty

/-
  Substitution is identity when the variable is not free.
-/
private theorem substTerm_vacuous
    (φ : Formula D Γ)
    {x : Var}
    {u : RelTerm D}
    (hx : x ∉ φ.freeVars) :
    φ.substTerm x u = φ := by
  induction φ with
  | top =>
      simp [substTerm]
  | bot =>
      simp [substTerm]
  | eq t₁ t₂ =>
      have hx₁ : x ∉ t₁.vars := by
        intro h
        exact hx (by simp [freeVars, h])
      have hx₂ : x ∉ t₂.vars := by
        intro h
        exact hx (by simp [freeVars, h])
      simp [substTerm, RelTerm.substTerm_vacuous t₁ hx₁,
        RelTerm.substTerm_vacuous t₂ hx₂]
  | rel a =>
      have hxTs : x ∉ RelTerm.tupleVars a.args := by
        intro h
        exact hx (by simpa [freeVars] using h)
      simp [substTerm, RelTerm.substTermTuple_vacuous a.args hxTs]
  | and φ ψ ihφ ihψ =>
      have hxφ : x ∉ φ.freeVars := by
        intro h
        exact hx (by simp [freeVars, h])
      have hxψ : x ∉ ψ.freeVars := by
        intro h
        exact hx (by simp [freeVars, h])
      simp [substTerm, ihφ hxφ, ihψ hxψ]
  | or φ ψ ihφ ihψ =>
      have hxφ : x ∉ φ.freeVars := by
        intro h
        exact hx (by simp [freeVars, h])
      have hxψ : x ∉ ψ.freeVars := by
        intro h
        exact hx (by simp [freeVars, h])
      simp [substTerm, ihφ hxφ, ihψ hxψ]
  | not φ ih =>
      simp [substTerm, ih hx]
  | imp φ ψ ihφ ihψ =>
      have hxφ : x ∉ φ.freeVars := by
        intro h
        exact hx (by simp [freeVars, h])
      have hxψ : x ∉ ψ.freeVars := by
        intro h
        exact hx (by simp [freeVars, h])
      simp [substTerm, ihφ hxφ, ihψ hxψ]
  | iff φ ψ ihφ ihψ =>
      have hxφ : x ∉ φ.freeVars := by
        intro h
        exact hx (by simp [freeVars, h])
      have hxψ : x ∉ ψ.freeVars := by
        intro h
        exact hx (by simp [freeVars, h])
      simp [substTerm, ihφ hxφ, ihψ hxψ]
  | forall_ y φ ih =>
      by_cases hyx : y = x
      · simp [substTerm, hyx]
      · have hxφ : x ∉ φ.freeVars := by
          intro h
          have hxy : x ≠ y := by
            intro hEq
            exact hyx hEq.symm
          exact hx (by
            simp [freeVars, Finset.mem_erase,
              hxy, h])
        simp [substTerm, hyx, ih hxφ]
  | exists_ y φ ih =>
      by_cases hyx : y = x
      · simp [substTerm, hyx]
      · have hxφ : x ∉ φ.freeVars := by
          intro h
          have hxy : x ≠ y := by
            intro hEq
            exact hyx hEq.symm
          exact hx (by
            simp [freeVars, Finset.mem_erase,
              hxy, h])
        simp [substTerm, hyx, ih hxφ]

end Formula

end RelCalc

------------------------------------------------------------
-- Simultaneous Formula Substitution
------------------------------------------------------------

namespace RelCalc

namespace Formula

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- Apply a simultaneous substitution to a formula. -/
def substTerms
    (φ : Formula D Γ)
    (ρ : RelTerm.Substitution D) :
    Formula D Γ :=
  match φ with
  | .top => .top
  | .bot => .bot
  | .eq t₁ t₂ =>
      .eq (t₁.substTerms ρ) (t₂.substTerms ρ)
  | .rel a =>
      .rel
        { rel := a.rel
          args := RelTerm.substTermsTuple a.args ρ }
  | .and φ ψ =>
      .and (substTerms φ ρ) (substTerms ψ ρ)
  | .or φ ψ =>
      .or (substTerms φ ρ) (substTerms ψ ρ)
  | .not φ =>
      .not (substTerms φ ρ)
  | .imp φ ψ =>
      .imp (substTerms φ ρ) (substTerms ψ ρ)
  | .iff φ ψ =>
      .iff (substTerms φ ρ) (substTerms ψ ρ)
  | .forall_ x φ =>
      .forall_ x
        (substTerms φ
          (RelTerm.Substitution.update ρ x (.var x)))
  | .exists_ x φ =>
      .exists_ x
        (substTerms φ
          (RelTerm.Substitution.update ρ x (.var x)))

/- A simultaneous substitution is capture-free for `φ`. -/
def FreeForTermSubstMap :
    Formula D Γ → RelTerm.Substitution D → Prop
| .top, _ => True
| .bot, _ => True
| .eq _ _, _ => True
| .rel _, _ => True
| .and φ ψ, ρ =>
    FreeForTermSubstMap φ ρ ∧ FreeForTermSubstMap ψ ρ
| .or φ ψ, ρ =>
    FreeForTermSubstMap φ ρ ∧ FreeForTermSubstMap ψ ρ
| .not φ, ρ =>
    FreeForTermSubstMap φ ρ
| .imp φ ψ, ρ =>
    FreeForTermSubstMap φ ρ ∧ FreeForTermSubstMap ψ ρ
| .iff φ ψ, ρ =>
    FreeForTermSubstMap φ ρ ∧ FreeForTermSubstMap ψ ρ
| .forall_ x φ, ρ =>
    (∀ z ∈ φ.freeVars.erase x,
      x ∉ (ρ z).vars) ∧
      FreeForTermSubstMap φ
        (RelTerm.Substitution.update ρ x (.var x))
| .exists_ x φ, ρ =>
    (∀ z ∈ φ.freeVars.erase x,
      x ∉ (ρ z).vars) ∧
      FreeForTermSubstMap φ
        (RelTerm.Substitution.update ρ x (.var x))

/- Free variables after simultaneous substitution. -/
theorem freeVars_substTerms
    (φ : Formula D Γ)
    (ρ : RelTerm.Substitution D)
    (hFree : φ.FreeForTermSubstMap ρ) :
    (φ.substTerms ρ).freeVars =
      RelTerm.Substitution.varsOn ρ φ.freeVars := by
  induction φ generalizing ρ with
  | top =>
      simp [substTerms, freeVars, RelTerm.Substitution.varsOn]
  | bot =>
      simp [substTerms, freeVars, RelTerm.Substitution.varsOn]
  | eq t₁ t₂ =>
      simp [substTerms, freeVars,
        RelTerm.vars_substTerms,
        RelTerm.Substitution.varsOn_union]
  | rel a =>
      simpa [substTerms, freeVars, RelAtom.vars] using
        RelTerm.tupleVars_substTermsTuple a.args ρ
  | and φ ψ ihφ ihψ =>
      rcases hFree with ⟨hφ, hψ⟩
      simp [substTerms, freeVars,
        ihφ ρ hφ, ihψ ρ hψ,
        RelTerm.Substitution.varsOn_union]
  | or φ ψ ihφ ihψ =>
      rcases hFree with ⟨hφ, hψ⟩
      simp [substTerms, freeVars,
        ihφ ρ hφ, ihψ ρ hψ,
        RelTerm.Substitution.varsOn_union]
  | not φ ih =>
      simp [substTerms, freeVars, ih ρ hFree]
  | imp φ ψ ihφ ihψ =>
      rcases hFree with ⟨hφ, hψ⟩
      simp [substTerms, freeVars,
        ihφ ρ hφ, ihψ ρ hψ,
        RelTerm.Substitution.varsOn_union]
  | iff φ ψ ihφ ihψ =>
      rcases hFree with ⟨hφ, hψ⟩
      simp [substTerms, freeVars,
        ihφ ρ hφ, ihψ ρ hψ,
        RelTerm.Substitution.varsOn_union]
  | forall_ x φ ih =>
      rcases hFree with ⟨hAvoid, hBody⟩
      have hErase :=
        RelTerm.Substitution.erase_varsOn_update
          ρ φ.freeVars x hAvoid
      simpa [substTerms, freeVars, ih _ hBody] using hErase
  | exists_ x φ ih =>
      rcases hFree with ⟨hAvoid, hBody⟩
      have hErase :=
        RelTerm.Substitution.erase_varsOn_update
          ρ φ.freeVars x hAvoid
      simpa [substTerms, freeVars, ih _ hBody] using hErase

end Formula

end RelCalc

------------------------------------------------------------
-- Semantic Substitution
------------------------------------------------------------

namespace RelCalc

namespace Formula

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- A term variable with a value in `Q` maps into `Q`. -/
private theorem mem_of_eval_mem
    {σ : Assign D}
    {Q : Set D}
    {u : RelTerm D}
    {z : Var}
    (hz : z ∈ u.vars)
    (hEval : Q (u.eval σ)) :
    Q (σ z) := by
  cases u with
  | var y =>
      have hzy : z = y := by
        simpa [RelTerm.vars] using hz
      simpa [RelTerm.eval, hzy] using hEval
  | const _ =>
      simp [RelTerm.vars] at hz

/- Substitution preserves recursive unrestricted truth. -/
theorem arbitraryAssignSatIn_substTerm
    {Q : Set D}
    {I : Instance D Γ}
    {σ : Assign D}
    (φ : Formula D Γ)
    (x : Var)
    (u : RelTerm D)
    (hFree : φ.FreeForTermSubst x u) :
    Formula.ArbitraryAssignSatIn Q I σ
        (φ.substTerm x u) ↔
      Formula.ArbitraryAssignSatIn Q I
        (Assign.update σ x (u.eval σ)) φ := by
  induction φ generalizing σ x u with
  | top =>
      simp [substTerm, Formula.ArbitraryAssignSatIn]
  | bot =>
      simp [substTerm, Formula.ArbitraryAssignSatIn]
  | eq t₁ t₂ =>
      simp [substTerm, Formula.ArbitraryAssignSatIn,
        RelTerm.eval_substTerm]
  | rel a =>
      have hTs :=
        RelTerm.evalVector_substTermTuple
          (σ := σ) a.args x u
      unfold substTerm Formula.ArbitraryAssignSatIn
        RelAtom.Sat RelAtom.evalFact RelFact.Mem
        RelAtom.evalTuple
      rw [hTs]
  | and φ ψ ihφ ihψ =>
      rcases hFree with ⟨hφ, hψ⟩
      simp [substTerm, Formula.ArbitraryAssignSatIn,
        ihφ (σ := σ) (x := x) (u := u) hφ,
        ihψ (σ := σ) (x := x) (u := u) hψ]
  | or φ ψ ihφ ihψ =>
      rcases hFree with ⟨hφ, hψ⟩
      simp [substTerm, Formula.ArbitraryAssignSatIn,
        ihφ (σ := σ) (x := x) (u := u) hφ,
        ihψ (σ := σ) (x := x) (u := u) hψ]
  | not φ ih =>
      simp [substTerm, Formula.ArbitraryAssignSatIn,
        ih (σ := σ) (x := x) (u := u) hFree]
  | imp φ ψ ihφ ihψ =>
      rcases hFree with ⟨hφ, hψ⟩
      simp [substTerm, Formula.ArbitraryAssignSatIn,
        ihφ (σ := σ) (x := x) (u := u) hφ,
        ihψ (σ := σ) (x := x) (u := u) hψ]
  | iff φ ψ ihφ ihψ =>
      rcases hFree with ⟨hφ, hψ⟩
      simp [substTerm, Formula.ArbitraryAssignSatIn,
        ihφ (σ := σ) (x := x) (u := u) hφ,
        ihψ (σ := σ) (x := x) (u := u) hψ]
  | forall_ y φ ih =>
      by_cases hyx : y = x
      · subst hyx
        have hAgree :
            Assign.AgreeOn σ
              (Assign.update σ y (u.eval σ))
              (Formula.forall_ y φ).freeVars := by
          apply Assign.agreeOn_update_of_not_mem
          simp [freeVars]
        simpa [substTerm] using
          (holdsIn_eq_of_agreeOn_freeVars
            (Q := Q) (I := I)
            (σ := σ)
            (τ := Assign.update σ y (u.eval σ))
            (φ := Formula.forall_ y φ) hAgree)
      · have hParts :
            y ∉ u.vars ∧ φ.FreeForTermSubst x u := by
          rcases hFree with hEq | hRest
          · exact False.elim (hyx hEq)
          · exact hRest
        have hxy : x ≠ y := by
          intro h
          exact hyx h.symm
        constructor
        · intro hSat d hd
          have hSatForall :
              Formula.ArbitraryAssignSatIn Q I σ
                (Formula.forall_ y (φ.substTerm x u)) := by
            simpa [substTerm, hyx] using hSat
          have hStep :
              Formula.ArbitraryAssignSatIn Q I
                (Assign.update
                  (Assign.update σ y d) x
                  (u.eval (Assign.update σ y d))) φ :=
            (ih
              (σ := Assign.update σ y d)
              (x := x) (u := u) hParts.2).mp
              (hSatForall d hd)
          have hEval :
              u.eval (Assign.update σ y d) = u.eval σ :=
            RelTerm.eval_update_of_not_mem u hParts.1
          have hAssign :
              Assign.update
                  (Assign.update σ y d) x
                  (u.eval (Assign.update σ y d)) =
                Assign.update
                  (Assign.update σ x (u.eval σ)) y d := by
            rw [hEval]
            exact (Assign.update_comm
              (σ := σ) (x := x) (y := y)
              (d := u.eval σ) (e := d) hxy).symm
          simpa [Formula.ArbitraryAssignSatIn,
            hAssign] using hStep
        · intro hSat
          have hForall :
              Formula.ArbitraryAssignSatIn Q I σ
                (Formula.forall_ y (φ.substTerm x u)) := by
            intro d hd
            have hEval :
                u.eval (Assign.update σ y d) = u.eval σ :=
              RelTerm.eval_update_of_not_mem u hParts.1
            have hAssign :
                Assign.update
                    (Assign.update σ y d) x
                    (u.eval (Assign.update σ y d)) =
                  Assign.update
                    (Assign.update σ x (u.eval σ))
                    y d := by
              rw [hEval]
              exact (Assign.update_comm
                (σ := σ) (x := x) (y := y)
                (d := u.eval σ) (e := d) hxy).symm
            have hBody :
                Formula.ArbitraryAssignSatIn Q I
                  (Assign.update
                    (Assign.update σ y d) x
                    (u.eval (Assign.update σ y d)))
                  φ := by
              simpa [hAssign] using hSat d hd
            exact
              (ih
                (σ := Assign.update σ y d)
                (x := x) (u := u) hParts.2).mpr hBody
          simpa [substTerm, hyx] using hForall
  | exists_ y φ ih =>
      by_cases hyx : y = x
      · subst hyx
        have hAgree :
            Assign.AgreeOn σ
              (Assign.update σ y (u.eval σ))
              (Formula.exists_ y φ).freeVars := by
          apply Assign.agreeOn_update_of_not_mem
          simp [freeVars]
        simpa [substTerm] using
          (holdsIn_eq_of_agreeOn_freeVars
            (Q := Q) (I := I)
            (σ := σ)
            (τ := Assign.update σ y (u.eval σ))
            (φ := Formula.exists_ y φ) hAgree)
      · have hParts :
            y ∉ u.vars ∧ φ.FreeForTermSubst x u := by
          rcases hFree with hEq | hRest
          · exact False.elim (hyx hEq)
          · exact hRest
        have hxy : x ≠ y := by
          intro h
          exact hyx h.symm
        constructor
        · intro hSat
          have hExists :
              Formula.ArbitraryAssignSatIn Q I σ
                (Formula.exists_ y (φ.substTerm x u)) := by
            simpa [substTerm, hyx] using hSat
          rcases hExists with ⟨d, hd, hSatBody⟩
          refine ⟨d, hd, ?_⟩
          have hStep :
              Formula.ArbitraryAssignSatIn Q I
                (Assign.update
                  (Assign.update σ y d) x
                  (u.eval (Assign.update σ y d))) φ :=
            (ih
              (σ := Assign.update σ y d)
              (x := x) (u := u) hParts.2).mp
              hSatBody
          have hEval :
              u.eval (Assign.update σ y d) = u.eval σ :=
            RelTerm.eval_update_of_not_mem u hParts.1
          have hAssign :
              Assign.update
                  (Assign.update σ y d) x
                  (u.eval (Assign.update σ y d)) =
                Assign.update
                  (Assign.update σ x (u.eval σ)) y d := by
            rw [hEval]
            exact (Assign.update_comm
              (σ := σ) (x := x) (y := y)
              (d := u.eval σ) (e := d) hxy).symm
          simpa [hAssign] using hStep
        · rintro ⟨d, hd, hSat⟩
          have hExists :
              Formula.ArbitraryAssignSatIn Q I σ
                (Formula.exists_ y (φ.substTerm x u)) := by
            refine ⟨d, hd, ?_⟩
            have hEval :
                u.eval (Assign.update σ y d) = u.eval σ :=
              RelTerm.eval_update_of_not_mem u hParts.1
            have hAssign :
                Assign.update
                    (Assign.update σ y d) x
                    (u.eval (Assign.update σ y d)) =
                  Assign.update
                    (Assign.update σ x (u.eval σ))
                    y d := by
              rw [hEval]
              exact (Assign.update_comm
                (σ := σ) (x := x) (y := y)
                (d := u.eval σ) (e := d) hxy).symm
            have hBody :
                Formula.ArbitraryAssignSatIn Q I
                  (Assign.update
                    (Assign.update σ y d) x
                    (u.eval (Assign.update σ y d)))
                  φ := by
              simpa [hAssign] using hSat
            exact
              (ih
                (σ := Assign.update σ y d)
                (x := x) (u := u) hParts.2).mpr hBody
          simpa [substTerm, hyx] using hExists

/- MapsInto matches substitution under the guard. -/
private theorem mapsInto_substTerm
    {Q : Set D}
    {σ : Assign D}
    (φ : Formula D Γ)
    (x : Var)
    (u : RelTerm D)
    (hFree : φ.FreeForTermSubst x u)
    (hEval : x ∈ φ.freeVars → Q (u.eval σ)) :
    Assign.MapsInto σ (φ.substTerm x u).freeVars Q ↔
      Assign.MapsInto
        (Assign.update σ x (u.eval σ))
        φ.freeVars Q := by
  constructor
  · intro hMap z hz
    by_cases hzx : z = x
    · subst hzx
      simpa [Assign.update] using hEval hz
    · have hzSub :
          z ∈ (φ.substTerm x u).freeVars := by
        exact
          (mem_freeVars_substTerm_iff
            (φ := φ) (x := x) (z := z)
            (u := u) hFree).mpr
            (Or.inl ⟨hz, hzx⟩)
      simpa [Assign.update, hzx] using hMap z hzSub
  · intro hMap z hz
    rcases
        (mem_freeVars_substTerm_iff
          (φ := φ) (x := x) (z := z)
          (u := u) hFree).mp hz with
      hOld | hNew
    · have hzx : z ≠ x := hOld.2
      simpa [Assign.update, hzx] using hMap z hOld.1
    · have hQEval : Q (u.eval σ) := hEval hNew.2
      exact mem_of_eval_mem
        (σ := σ) (Q := Q) hNew.1 hQEval

/- Public satisfaction obeys guarded substitution. -/
theorem satIn_substTerm
    {Q : Set D}
    {I : Instance D Γ}
    {σ : Assign D}
    (φ : Formula D Γ)
    (x : Var)
    (u : RelTerm D)
    (hFree : φ.FreeForTermSubst x u)
    (hEval : x ∈ φ.freeVars → Q (u.eval σ)) :
    (φ.substTerm x u).SatIn I σ Q ↔
      φ.SatIn I
        (Assign.update σ x (u.eval σ)) Q := by
  have hMap :=
    mapsInto_substTerm
      (φ := φ) (x := x) (u := u)
      (Q := Q) (σ := σ) hFree hEval
  have hSat :=
    arbitraryAssignSatIn_substTerm
      (Q := Q) (I := I) (σ := σ)
      φ x u hFree
  constructor
  · rintro ⟨hMaps, hRaw⟩
    exact ⟨hMap.mp hMaps, hSat.mp hRaw⟩
  · rintro ⟨hMaps, hRaw⟩
    exact ⟨hMap.mpr hMaps, hSat.mpr hRaw⟩

/- MapsInto matches simultaneous substitution. -/
private theorem mapsInto_substTerms
    {Q : Set D}
    {σ : Assign D}
    (φ : Formula D Γ)
    (ρ : RelTerm.Substitution D)
    (hFree : φ.FreeForTermSubstMap ρ)
    (hEval :
      ∀ x ∈ φ.freeVars, Q ((ρ x).eval σ)) :
    Assign.MapsInto σ (φ.substTerms ρ).freeVars Q ↔
      Assign.MapsInto
        (RelTerm.Substitution.eval ρ σ)
        φ.freeVars Q := by
  constructor
  · intro _ x hx
    exact hEval x hx
  · intro hMap z hz
    have hzOn :
        z ∈ RelTerm.Substitution.varsOn ρ φ.freeVars := by
      simpa [freeVars_substTerms φ ρ hFree] using hz
    rcases Finset.mem_biUnion.mp hzOn with
      ⟨x, hx, hzx⟩
    exact mem_of_eval_mem
      (σ := σ) (Q := Q) hzx (hMap x hx)

/- Simultaneous substitution preserves recursive truth. -/
theorem arbitraryAssignSatIn_substTerms
    {Q : Set D}
    {I : Instance D Γ}
    {σ : Assign D}
    (φ : Formula D Γ)
    (ρ : RelTerm.Substitution D)
    (hFree : φ.FreeForTermSubstMap ρ) :
    Formula.ArbitraryAssignSatIn Q I σ
        (φ.substTerms ρ) ↔
      Formula.ArbitraryAssignSatIn Q I
        (RelTerm.Substitution.eval ρ σ) φ := by
  induction φ generalizing σ ρ with
  | top =>
      simp [substTerms, Formula.ArbitraryAssignSatIn]
  | bot =>
      simp [substTerms, Formula.ArbitraryAssignSatIn]
  | eq t₁ t₂ =>
      simp [substTerms, Formula.ArbitraryAssignSatIn,
        RelTerm.eval_substTerms]
  | rel a =>
      have hTs :=
        RelTerm.evalVector_substTermsTuple a.args ρ σ
      unfold substTerms Formula.ArbitraryAssignSatIn
        RelAtom.Sat RelAtom.evalFact RelFact.Mem
        RelAtom.evalTuple
      rw [hTs]
  | and φ ψ ihφ ihψ =>
      rcases hFree with ⟨hφ, hψ⟩
      simp [substTerms, Formula.ArbitraryAssignSatIn,
        ihφ (σ := σ) (ρ := ρ) hφ,
        ihψ (σ := σ) (ρ := ρ) hψ]
  | or φ ψ ihφ ihψ =>
      rcases hFree with ⟨hφ, hψ⟩
      simp [substTerms, Formula.ArbitraryAssignSatIn,
        ihφ (σ := σ) (ρ := ρ) hφ,
        ihψ (σ := σ) (ρ := ρ) hψ]
  | not φ ih =>
      simp [substTerms, Formula.ArbitraryAssignSatIn,
        ih (σ := σ) (ρ := ρ) hFree]
  | imp φ ψ ihφ ihψ =>
      rcases hFree with ⟨hφ, hψ⟩
      simp [substTerms, Formula.ArbitraryAssignSatIn,
        ihφ (σ := σ) (ρ := ρ) hφ,
        ihψ (σ := σ) (ρ := ρ) hψ]
  | iff φ ψ ihφ ihψ =>
      rcases hFree with ⟨hφ, hψ⟩
      simp [substTerms, Formula.ArbitraryAssignSatIn,
        ihφ (σ := σ) (ρ := ρ) hφ,
        ihψ (σ := σ) (ρ := ρ) hψ]
  | forall_ x φ ih =>
      rcases hFree with ⟨hAvoid, hBody⟩
      constructor
      · intro hSat d hd
        have hSub :
            Formula.ArbitraryAssignSatIn Q I
              (Assign.update σ x d)
              (φ.substTerms
                (RelTerm.Substitution.update ρ x
                  (.var x))) := by
          simpa [substTerms, Formula.ArbitraryAssignSatIn]
            using hSat d hd
        have hStep :
            Formula.ArbitraryAssignSatIn Q I
              (RelTerm.Substitution.eval
                (RelTerm.Substitution.update ρ x (.var x))
                (Assign.update σ x d)) φ :=
          (ih
            (σ := Assign.update σ x d)
            (ρ := RelTerm.Substitution.update ρ x (.var x))
            hBody).mp hSub
        have hAgree :
            Assign.AgreeOn
              (RelTerm.Substitution.eval
                (RelTerm.Substitution.update ρ x (.var x))
                (Assign.update σ x d))
              (Assign.update
                (RelTerm.Substitution.eval ρ σ) x d)
              φ.freeVars :=
          RelTerm.Substitution.eval_update_agreeOn
            (ρ := ρ) (σ := σ)
            (x := x) (d := d)
            (S := φ.freeVars) hAvoid
        exact
          (holdsIn_eq_of_agreeOn_freeVars
            (Q := Q) (I := I)
            (φ := φ) hAgree).mp hStep
      · intro hSat d hd
        have hBodySat :
            Formula.ArbitraryAssignSatIn Q I
              (Assign.update
                (RelTerm.Substitution.eval ρ σ) x d) φ :=
          hSat d hd
        have hAgree :
            Assign.AgreeOn
              (RelTerm.Substitution.eval
                (RelTerm.Substitution.update ρ x (.var x))
                (Assign.update σ x d))
              (Assign.update
                (RelTerm.Substitution.eval ρ σ) x d)
              φ.freeVars :=
          RelTerm.Substitution.eval_update_agreeOn
            (ρ := ρ) (σ := σ)
            (x := x) (d := d)
            (S := φ.freeVars) hAvoid
        have hLeft :
            Formula.ArbitraryAssignSatIn Q I
              (RelTerm.Substitution.eval
                (RelTerm.Substitution.update ρ x (.var x))
                (Assign.update σ x d)) φ :=
          (holdsIn_eq_of_agreeOn_freeVars
            (Q := Q) (I := I)
            (φ := φ) hAgree).mpr hBodySat
        have hSub :
            Formula.ArbitraryAssignSatIn Q I
              (Assign.update σ x d)
              (φ.substTerms
                (RelTerm.Substitution.update ρ x (.var x))) :=
          (ih
            (σ := Assign.update σ x d)
            (ρ := RelTerm.Substitution.update ρ x (.var x))
            hBody).mpr hLeft
        simpa [substTerms, Formula.ArbitraryAssignSatIn]
          using hSub
  | exists_ x φ ih =>
      rcases hFree with ⟨hAvoid, hBody⟩
      constructor
      · intro hSat
        have hExists :
            ∃ d ∈ Q,
              Formula.ArbitraryAssignSatIn Q I
                (Assign.update σ x d)
                (φ.substTerms
                  (RelTerm.Substitution.update ρ x
                    (.var x))) := by
          simpa [substTerms, Formula.ArbitraryAssignSatIn]
            using hSat
        rcases hExists with ⟨d, hd, hSub⟩
        refine ⟨d, hd, ?_⟩
        have hStep :
            Formula.ArbitraryAssignSatIn Q I
              (RelTerm.Substitution.eval
                (RelTerm.Substitution.update ρ x (.var x))
                (Assign.update σ x d)) φ :=
          (ih
            (σ := Assign.update σ x d)
            (ρ := RelTerm.Substitution.update ρ x (.var x))
            hBody).mp hSub
        have hAgree :
            Assign.AgreeOn
              (RelTerm.Substitution.eval
                (RelTerm.Substitution.update ρ x (.var x))
                (Assign.update σ x d))
              (Assign.update
                (RelTerm.Substitution.eval ρ σ) x d)
              φ.freeVars :=
          RelTerm.Substitution.eval_update_agreeOn
            (ρ := ρ) (σ := σ)
            (x := x) (d := d)
            (S := φ.freeVars) hAvoid
        exact
          (holdsIn_eq_of_agreeOn_freeVars
            (Q := Q) (I := I)
            (φ := φ) hAgree).mp hStep
      · rintro ⟨d, hd, hSat⟩
        have hAgree :
            Assign.AgreeOn
              (RelTerm.Substitution.eval
                (RelTerm.Substitution.update ρ x (.var x))
                (Assign.update σ x d))
              (Assign.update
                (RelTerm.Substitution.eval ρ σ) x d)
              φ.freeVars :=
          RelTerm.Substitution.eval_update_agreeOn
            (ρ := ρ) (σ := σ)
            (x := x) (d := d)
            (S := φ.freeVars) hAvoid
        have hLeft :
            Formula.ArbitraryAssignSatIn Q I
              (RelTerm.Substitution.eval
                (RelTerm.Substitution.update ρ x (.var x))
                (Assign.update σ x d)) φ :=
          (holdsIn_eq_of_agreeOn_freeVars
            (Q := Q) (I := I)
            (φ := φ) hAgree).mpr hSat
        have hSub :
            Formula.ArbitraryAssignSatIn Q I
              (Assign.update σ x d)
              (φ.substTerms
                (RelTerm.Substitution.update ρ x (.var x))) :=
          (ih
            (σ := Assign.update σ x d)
            (ρ := RelTerm.Substitution.update ρ x (.var x))
            hBody).mpr hLeft
        refine ⟨d, hd, ?_⟩
        simpa [substTerms, Formula.ArbitraryAssignSatIn]
          using hSub

/- Public satisfaction obeys simultaneous substitution. -/
theorem satIn_substTerms
    {Q : Set D}
    {I : Instance D Γ}
    {σ : Assign D}
    (φ : Formula D Γ)
    (ρ : RelTerm.Substitution D)
    (hFree : φ.FreeForTermSubstMap ρ)
    (hEval :
      ∀ x ∈ φ.freeVars, Q ((ρ x).eval σ)) :
    (φ.substTerms ρ).SatIn I σ Q ↔
      φ.SatIn I
        (RelTerm.Substitution.eval ρ σ) Q := by
  have hMap :=
    mapsInto_substTerms
      (φ := φ) (ρ := ρ)
      (Q := Q) (σ := σ) hFree hEval
  have hSat :=
    arbitraryAssignSatIn_substTerms
      (Q := Q) (I := I) (σ := σ)
      φ ρ hFree
  constructor
  · rintro ⟨hMaps, hRaw⟩
    exact ⟨hMap.mp hMaps, hSat.mp hRaw⟩
  · rintro ⟨hMaps, hRaw⟩
    exact ⟨hMap.mpr hMaps, hSat.mpr hRaw⟩

/- Active-domain satisfaction obeys term substitution. -/
theorem adomSat_substTerm
    {I : Instance D Γ}
    {σ : Assign D}
    (φ : Formula D Γ)
    (x : Var)
    (u : RelTerm D)
    (hFree : φ.FreeForTermSubst x u)
    (hEval :
      x ∈ φ.freeVars →
        Adom.toSet (φ.substTerm x u) I
          (u.eval σ)) :
    (φ.substTerm x u).AdomSat I σ ↔
      φ.SatIn I
        (Assign.update σ x (u.eval σ))
        (Adom.toSet (φ.substTerm x u) I) := by
  simpa [Formula.AdomSat] using
    satIn_substTerm
      (Q := Adom.toSet (φ.substTerm x u) I)
      (I := I) (σ := σ)
      φ x u hFree hEval

/- Active-domain satisfaction obeys simultaneous terms. -/
theorem adomSat_substTerms
    {I : Instance D Γ}
    {σ : Assign D}
    (φ : Formula D Γ)
    (ρ : RelTerm.Substitution D)
    (hFree : φ.FreeForTermSubstMap ρ)
    (hEval :
      ∀ x ∈ φ.freeVars,
        Adom.toSet (φ.substTerms ρ) I
          ((ρ x).eval σ)) :
    (φ.substTerms ρ).AdomSat I σ ↔
      φ.SatIn I
        (RelTerm.Substitution.eval ρ σ)
        (Adom.toSet (φ.substTerms ρ) I) := by
  simpa [Formula.AdomSat] using
    satIn_substTerms
      (Q := Adom.toSet (φ.substTerms ρ) I)
      (I := I) (σ := σ)
      φ ρ hFree hEval

end Formula

end RelCalc
