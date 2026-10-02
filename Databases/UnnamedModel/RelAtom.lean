-- Author: Jesse Comer
import Databases.UnnamedModel.Instance

/-
  This file defines the shared variable-assignment,
  function-free relational term, relational atom, and
  relational fact layer used by Datalog and relational
  calculus over unnamed instances.

  Key definitions include:
    * `Assign`
    * `Assign.update`
    * `Assign.AgreeOn`
    * `Assign.MapsInto`
    * `Assign.Realizes`
    * `Assign.ofListTuple`
    * `Assign.toListTuple`
    * `Assign.ofVectorTuple`
    * `Assign.toVectorTuple`
    * `Assign.TupleConsistent`
    * `RelTerm`
    * `RelTerm.IsVar`
    * `RelTerm.IsConst`
    * `RelTerm.eval`
    * `RelTerm.evalVector`
    * `RelTerm.IsGround`
    * `RelTerm.ConstFree`
    * `RelAtom`
    * `RelAtom.evalTuple`
    * `RelAtom.evalFact`
    * `RelAtom.Sat`
    * `RelAtom.IsGround`
    * `RelAtom.ConstFree`
    * `RelFact`
    * `RelFact.Mem`
-/

------------------------------------------------------------
-- Assignments
------------------------------------------------------------

/-
  An assignment maps each variable to a value.
-/
abbrev Assign (D : Type) :=
  Var → D

namespace Assign

variable {D : Type}

/- Update one variable in an assignment. -/
def update
    (σ : Assign D)
    (x : Var)
    (v : D) : Assign D :=
  fun y => if y = x then v else σ y

/-
  Updating a variable with its current value leaves the
  assignment unchanged.
-/
theorem update_self
    (σ : Assign D)
    (x : Var) :
    update σ x (σ x) = σ := by
  funext y
  by_cases hy : y = x
  · subst hy
    simp [update]
  · simp [update, hy]

/- Agreement on a finite set of variables. -/
def AgreeOn
    (σ τ : Assign D)
    (S : Finset Var) : Prop :=
  ∀ x ∈ S, σ x = τ x

instance
    [DecidableEq D]
    (σ τ : Assign D)
    (S : Finset Var) :
    Decidable (AgreeOn σ τ S) := by
  unfold AgreeOn
  infer_instance

/- Assignment values on `S` lie in `Q`. -/
def MapsInto
    (σ : Assign D)
    (S : Finset Var)
    (Q : Set D) : Prop :=
  ∀ x ∈ S, Q (σ x)

instance
    (σ : Assign D)
    (S : Finset Var)
    (Q : Set D)
    [DecidablePred Q] :
    Decidable (MapsInto σ S Q) := by
  unfold MapsInto
  infer_instance

/- An assignment realizes a tuple on an output vector. -/
def Realizes
    {n : Nat}
    (σ : Assign D)
    (xs : Vector Var n)
    (t : Tuple D n) : Prop :=
  ∀ i : Fin n,
    σ (xs.get i) = t.get i

instance
    [DecidableEq D]
    {n : Nat}
    (σ : Assign D)
    (xs : Vector Var n)
    (t : Tuple D n) :
    Decidable (Realizes σ xs t) := by
  unfold Realizes
  infer_instance

/- Convert a tuple indexed by a list into an assignment. -/
def ofListTuple
    [Domain D]
    (xs : List Var)
    (t : Tuple D xs.length) :
    Assign D :=
  fun x =>
    match xs.idxOf? x with
    | none => default
    | some i =>
        match t.toList[i]? with
        | none => default
        | some d => d

/- The tuple of assignment values in list order. -/
def toListTuple
    (xs : List Var)
    (σ : Assign D) :
    Tuple D xs.length :=
  Vector.ofFn (fun i => σ xs[i])

/- Convert a tuple indexed by a vector into an assignment. -/
def ofVectorTuple
    [Domain D]
    {n : Nat}
    (xs : Vector Var n)
    (t : Tuple D n) :
    Assign D :=
  fun x =>
    match xs.toList.idxOf? x with
    | none => default
    | some i =>
        match t.toList[i]? with
        | none => default
        | some d => d

/- The tuple of assignment values in vector order. -/
def toVectorTuple
    {n : Nat}
    (xs : Vector Var n)
    (σ : Assign D) :
    Tuple D n :=
  Vector.ofFn (fun i => σ (xs.get i))

/-
  A tuple is consistent with a variable vector when repeated
  variables receive equal tuple values.
-/
def TupleConsistent
    {n : Nat}
    (xs : Vector Var n)
    (t : Tuple D n) : Prop :=
  ∀ i j : Fin n,
    xs.get i = xs.get j →
      t.get i = t.get j

instance
    {n : Nat}
    (xs : Vector Var n)
    (t : Tuple D n)
    [DecidableEq D] :
    Decidable (TupleConsistent xs t) := by
  unfold TupleConsistent
  infer_instance

/- `ofListTuple` recovers listed variables from `toListTuple`. -/
theorem ofListTuple_toListTuple_of_mem
    [Domain D]
    {xs : List Var}
    {σ : Assign D}
    {x : Var}
    (hx : x ∈ xs) :
    ofListTuple xs (toListTuple xs σ) x = σ x := by
  unfold ofListTuple toListTuple
  cases hxIdx : xs.idxOf? x with
  | none =>
      have hNot : ¬ x ∈ xs := by
        exact
          (List.idxOf?_eq_none_iff
            (l := xs) (a := x)).mp hxIdx
      exact (hNot hx).elim
  | some i =>
      rcases
          (List.idxOf?_eq_some_iff
            (l := xs) (a := x) (i := i)).mp hxIdx with
        ⟨hi, hGet, _hFirst⟩
      simp [hi, Vector.toList_ofFn, hGet]

/-
  If an assignment maps every variable in `xs` into `Q`,
  then its tuple over `xs` is enumerated by `Tuple.allOver`.
-/
theorem toListTuple_mem_allOver_of_forall_mem
    [Domain D]
    {xs : List Var}
    {σ : Assign D}
    {Q : Finset D}
    (hσ : ∀ x : Var, x ∈ xs → σ x ∈ Q) :
    toListTuple xs σ ∈ Tuple.allOver Q xs.length := by
  apply Tuple.mem_allOver_of_isTupleOver
  intro i
  change (toListTuple xs σ)[i.1] ∈ Q
  simpa only [toListTuple, Vector.getElem_ofFn]
    using hσ xs[i] (List.getElem_mem i.2)

/-
  Reading a listed variable from an enumerated assignment
  tuple produces a value in the enumerating set.
-/
theorem ofListTuple_mem_of_mem_allOver
    [Domain D]
    {xs : List Var}
    {u : Tuple D xs.length}
    {Q : Finset D}
    {x : Var}
    (hu : u ∈ Tuple.allOver Q xs.length)
    (hx : x ∈ xs) :
    ofListTuple xs u x ∈ Q := by
  have hOver := Tuple.isTupleOver_of_mem_allOver Q hu
  unfold ofListTuple
  cases hxIdx : xs.idxOf? x with
  | none =>
      have hNot : ¬ x ∈ xs :=
        (List.idxOf?_eq_none_iff
          (l := xs) (a := x)).mp hxIdx
      exact (hNot hx).elim
  | some i =>
      rcases
          (List.idxOf?_eq_some_iff
            (l := xs) (a := x) (i := i)).mp hxIdx with
        ⟨hi, _hGet, _hFirst⟩
      have hLen : i < u.toList.length := by
        simpa [Vector.length_toList] using hi
      simp only
      rw [List.getElem?_eq_getElem hLen]
      have hCoord := hOver ⟨i, hi⟩
      simpa [Vector.getElem_toList hLen] using hCoord

/- The tuple induced by a vector realizes the assignment. -/
theorem toVectorTuple_realizes
    {n : Nat}
    (xs : Vector Var n)
    (σ : Assign D) :
    Realizes σ xs (toVectorTuple xs σ) := by
  intro i
  simp [toVectorTuple, Vector.get]

/- A consistent vector tuple realizes its canonical assignment. -/
theorem ofVectorTuple_realizes
    [Domain D]
    {n : Nat}
    {xs : Vector Var n}
    {t : Tuple D n}
    (hCons : TupleConsistent xs t) :
    Realizes (ofVectorTuple xs t) xs t := by
  intro i
  unfold ofVectorTuple
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
            (l := xs.toList) (a := xs.get i) (i := j)).mp
            hIdx with
        ⟨hjList, hGet, _hFirst⟩
      have hj : j < n := by
        simpa [Vector.length_toList] using hjList
      have hjLen : j < t.toList.length := by
        simpa [Vector.length_toList] using hj
      have hVar :
          xs.get ⟨j, hj⟩ = xs.get i := by
        simpa [Vector.getElem_toList hjList] using hGet
      have hCoord := hCons ⟨j, hj⟩ i hVar
      have hVal :
          (match t.toList[j]? with
          | none => default
          | some d => d) = t.get i := by
        rw [List.getElem?_eq_getElem hjLen]
        simpa [Vector.getElem_toList hjLen] using hCoord
      simpa [hIdx] using hVal

/- Realized tuples are consistent on repeated variables. -/
theorem tupleConsistent_of_realizes
    {σ : Assign D}
    {n : Nat}
    {xs : Vector Var n}
    {t : Tuple D n}
    (hReal : Realizes σ xs t) :
    TupleConsistent xs t := by
  intro i j hVar
  have hi := hReal i
  have hj := hReal j
  rw [← hi, ← hj, hVar]

/- A realizing assignment agrees with the canonical one. -/
theorem agreeOn_of_realizes_ofVectorTuple
    [Domain D]
    {σ : Assign D}
    {n : Nat}
    {xs : Vector Var n}
    {t : Tuple D n}
    (hReal : Realizes σ xs t)
    (hCons : TupleConsistent xs t) :
    AgreeOn σ (ofVectorTuple xs t) xs.toList.toFinset := by
  have hOut := ofVectorTuple_realizes
    (xs := xs) (t := t) hCons
  intro x hx
  have hxList : x ∈ xs.toList := by
    simpa using hx
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
  have hσj := hReal j
  have hτj := hOut j
  rw [hVar] at hσj hτj
  exact hσj.trans hτj.symm

/- Realizers of the same tuple agree on vector variables. -/
theorem agreeOn_of_realizes
    {σ τ : Assign D}
    {n : Nat}
    {xs : Vector Var n}
    {t : Tuple D n}
    (hσ : Realizes σ xs t)
    (hτ : Realizes τ xs t) :
    AgreeOn σ τ xs.toList.toFinset := by
  intro x hx
  have hxList : x ∈ xs.toList := by
    simpa using hx
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
  have hσj := hσ j
  have hτj := hτ j
  rw [hVar] at hσj hτj
  exact hσj.trans hτj.symm

/-
  Agreement on a larger set implies agreement on a subset.
-/
theorem agreeOn_mono
    {σ τ : Assign D}
    {S T : Finset Var}
    (h : AgreeOn σ τ T)
    (hST : S ⊆ T) :
    AgreeOn σ τ S := by
  intro x hx
  exact h x (hST hx)

/- `MapsInto` is unchanged by agreement on `S`. -/
theorem mapsInto_congr
    {σ τ : Assign D}
    {S : Finset Var}
    {Q : Set D}
    (h : AgreeOn σ τ S) :
    MapsInto σ S Q ↔ MapsInto τ S Q := by
  constructor
  · intro hMap x hx
    simpa [h x hx] using hMap x hx
  · intro hMap x hx
    simpa [h x hx] using hMap x hx

/- Updating two agreeing assignments preserves agreement. -/
theorem update_agreeOn
    {σ τ : Assign D}
    {S : Finset Var}
    {x : Var}
    {d : D}
    (h : AgreeOn σ τ (S.erase x)) :
    AgreeOn (update σ x d)
      (update τ x d) S := by
  intro z hz
  by_cases hzX : z = x
  · subst hzX
    simp [update]
  · have hzErase : z ∈ S.erase x :=
      Finset.mem_erase.mpr ⟨hzX, hz⟩
    have hEq : σ z = τ z := h z hzErase
    simp [update, hzX, hEq]

/- An update away from `S` agrees on `S`. -/
theorem agreeOn_update_of_not_mem
    (σ : Assign D)
    {S : Finset Var}
    {x : Var}
    {d : D}
    (hx : x ∉ S) :
    AgreeOn σ (update σ x d) S := by
  intro z hz
  have hzx : z ≠ x := by
    intro h
    exact hx (by simpa [h] using hz)
  simp [update, hzx]

/- Updates at distinct variables commute. -/
theorem update_comm
    (σ : Assign D)
    {x y : Var}
    {d e : D}
    (hxy : x ≠ y) :
    update (update σ x d) y e =
      update (update σ y e) x d := by
  funext z
  by_cases hzX : z = x
  · subst hzX
    simp [update, hxy]
  · by_cases hzY : z = y
    · have hyx : y ≠ x := by
        intro h
        exact hxy h.symm
      simp [update, hzY, hyx]
    · simp [update, hzX, hzY]

end Assign

------------------------------------------------------------
-- Relational (Function-Free) Terms
------------------------------------------------------------

/- Function-free relational terms are variables or constants. -/
inductive RelTerm
    (D : Type) [Domain D] where
| var : Var → RelTerm D
| const : D → RelTerm D
deriving DecidableEq, Repr

namespace RelTerm

variable {D : Type} [Domain D]

/- The variable carried by a term, if it has one. -/
def var? : RelTerm D → Option Var
| .var x => some x
| .const _ => none

/- The constant carried by a term, if it has one. -/
def const? : RelTerm D → Option D
| .var _ => none
| .const d => some d

/- A term is a variable term. -/
def IsVar : RelTerm D → Prop
| .var _ => True
| .const _ => False

instance (t : RelTerm D) : Decidable t.IsVar := by
  cases t <;> unfold IsVar <;> infer_instance

/- A term is a constant term. -/
def IsConst : RelTerm D → Prop
| .var _ => False
| .const _ => True

instance (t : RelTerm D) : Decidable t.IsConst := by
  cases t <;> unfold IsConst <;> infer_instance

/- Variables in a term, with duplicates and in order. -/
def varList : RelTerm D → List Var
| .var x => [x]
| .const _ => []

/- Constants in a term, with duplicates and in order. -/
private def constList : RelTerm D → List D
| .var _ => []
| .const d => [d]

/- Free variables in a term. -/
def vars : RelTerm D → Finset Var
| .var x => {x}
| .const _ => ∅

/- Constants occurring in a term. -/
def constants : RelTerm D → Finset D
| .var _ => ∅
| .const d => {d}

/- Variables occurring in a list of terms. -/
def listVars : List (RelTerm D) → Finset Var
| [] => ∅
| t :: ts => t.vars ∪ listVars ts

/- Constants occurring in a list of terms. -/
def listConstants : List (RelTerm D) → Finset D
| [] => ∅
| t :: ts => t.constants ∪ listConstants ts

/- Variables occurring in a tuple of terms. -/
def tupleVars
    {n : Nat}
    (ts : Vector (RelTerm D) n) : Finset Var :=
  listVars ts.toList

/- Constants occurring in a tuple of terms. -/
def tupleConstants
    {n : Nat}
    (ts : Vector (RelTerm D) n) : Finset D :=
  listConstants ts.toList

/- Variables occurring in a list of terms, preserving order. -/
def listVarList : List (RelTerm D) → List Var
| [] => []
| t :: ts => t.varList ++ listVarList ts

/- Constants occurring in a list of terms, preserving order. -/
private def listConstList : List (RelTerm D) → List D
| [] => []
| t :: ts => t.constList ++ listConstList ts

/- Variables occurring in a term tuple as a list. -/
def tupleVarList
    {n : Nat}
    (ts : Vector (RelTerm D) n) : List Var :=
  listVarList ts.toList

/- Constants occurring in a term tuple as a list. -/
private def tupleConstList
    {n : Nat}
    (ts : Vector (RelTerm D) n) : List D :=
  listConstList ts.toList

/- A term is ground when it has no variables. -/
def IsGround (t : RelTerm D) : Prop :=
  t.varList = []

instance (t : RelTerm D) : Decidable t.IsGround := by
  unfold IsGround
  infer_instance

/- A term is constant-free when it is a variable. -/
def ConstFree : RelTerm D → Prop
| .var _ => True
| .const _ => False

instance (t : RelTerm D) : Decidable t.ConstFree := by
  cases t <;> unfold ConstFree <;> infer_instance

/- A constant-free term is some variable. -/
private theorem exists_var_of_constFree
    {t : RelTerm D}
    (ht : t.ConstFree) :
    ∃ x : Var, t = RelTerm.var x := by
  cases t with
  | var x =>
      exact ⟨x, rfl⟩
  | const _ =>
      cases ht

/- Evaluate a term under an assignment. -/
def eval (σ : Assign D) : RelTerm D → D
| .var x => σ x
| .const d => d

private theorem map_eval_eq_filterMap_var?_map_of_constFree
    (σ : Assign D) :
    ∀ ts : List (RelTerm D),
      (∀ t ∈ ts, t.ConstFree) →
        ts.map (RelTerm.eval σ) =
          (ts.filterMap RelTerm.var?).map σ
| [], _ => by
    simp
| t :: ts, hFree => by
    have htFree : t.ConstFree :=
      hFree t (by simp)
    have htsFree : ∀ u ∈ ts, u.ConstFree := by
      intro u hu
      exact hFree u (by simp [hu])
    rcases exists_var_of_constFree htFree with ⟨x, htx⟩
    subst htx
    simp [RelTerm.var?, RelTerm.eval,
      map_eval_eq_filterMap_var?_map_of_constFree σ ts htsFree]

/- Term evaluation depends only on the term's variable. -/
theorem eval_eq_of_assign_eq_on_var?
    (t : RelTerm D)
    {σ₁ σ₂ : Assign D}
    (hσ :
      ∀ x : Var,
        t.var? = some x → σ₁ x = σ₂ x) :
    t.eval σ₁ = t.eval σ₂ := by
  cases t with
  | var x =>
      exact hσ x rfl
  | const _ =>
      rfl

/- Evaluate a vector of terms under an assignment. -/
def evalVector
    (σ : Assign D)
    {n : Nat}
    (ts : Vector (RelTerm D) n) :
    Tuple D n :=
  Vector.ofFn (fun i => eval σ (ts.get i))

/- Vector evaluation is coordinatewise term evaluation. -/
theorem evalVector_eq_map
    (σ : Assign D)
    {n : Nat}
    (ts : Vector (RelTerm D) n) :
    evalVector σ ts = ts.map (eval σ) := by
  apply Vector.ext
  intro i hi
  simp [evalVector, Vector.get, Vector.getElem_map,
    Vector.getElem_ofFn]

private theorem mem_listVars_of_mem_term :
    ∀ {ts : List (RelTerm D)}
      {t : RelTerm D}
      {x : Var},
      t ∈ ts → x ∈ t.vars →
        x ∈ listVars ts
| [], _, _, ht, _ =>
    by cases ht
| u :: us, t, x, ht, hx =>
    by
      have hcases : t = u ∨ t ∈ us := by
        simpa using ht
      exact Finset.mem_union.mpr <| by
        cases hcases with
        | inl h =>
            cases h
            exact Or.inl hx
        | inr h =>
            exact Or.inr
              (mem_listVars_of_mem_term h hx)

/- A coordinate variable appears in tuple variables. -/
theorem mem_tupleVars_of_mem_get_vars
    {n : Nat}
    {ts : Vector (RelTerm D) n}
    {i : Fin n}
    {x : Var}
    (hx : x ∈ (ts.get i).vars) :
    x ∈ tupleVars ts := by
  have ht : ts.get i ∈ ts.toList := by
    exact List.get_mem _ _
  exact mem_listVars_of_mem_term ht hx

end RelTerm

------------------------------------------------------------
-- Relational Atoms
------------------------------------------------------------

/-
  A relational atom is a schema relation name with an
  arity-correct vector of function-free terms.
-/
structure RelAtom
    (D : Type) [Domain D]
    {A : Type} [RelationNames A]
    (Γ : UnnamedSchema A) where
  rel : Γ.syms
  args : Vector (RelTerm D) (Γ.arity rel)
deriving DecidableEq, Repr

namespace RelAtom

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Variables in an atom, with duplicates and in order. -/
def varList (a : RelAtom D Γ) : List Var :=
  a.args.toList.filterMap RelTerm.var?

/- Constants in an atom, with duplicates and in order. -/
def constList (a : RelAtom D Γ) : List D :=
  a.args.toList.filterMap RelTerm.const?

/- Variables occurring in an atom. -/
def vars (a : RelAtom D Γ) : Finset Var :=
  RelTerm.tupleVars a.args

/- Constants occurring in an atom. -/
def constants (a : RelAtom D Γ) : Finset D :=
  RelTerm.tupleConstants a.args

/- A relational atom is ground when it has no variables. -/
def IsGround (a : RelAtom D Γ) : Prop :=
  a.varList = []

instance (a : RelAtom D Γ) : Decidable a.IsGround := by
  unfold IsGround
  infer_instance

/- A relational atom is constant-free when all arguments are variables. -/
def ConstFree (a : RelAtom D Γ) : Prop :=
  ∀ i : Fin (Γ.arity a.rel), (a.args.get i).ConstFree

instance (a : RelAtom D Γ) : Decidable a.ConstFree := by
  unfold ConstFree
  infer_instance

/- A coordinate of a constant-free atom is some variable. -/
private theorem exists_var_arg_of_constFree
    (a : RelAtom D Γ)
    (hFree : a.ConstFree)
    (i : Fin (Γ.arity a.rel)) :
    ∃ x : Var, a.args.get i = RelTerm.var x :=
  RelTerm.exists_var_of_constFree (hFree i)

/- A coordinate of a constant-free atom is some variable. -/
private theorem exists_var_getElem_of_constFree
    (a : RelAtom D Γ)
    (hFree : a.ConstFree)
    {i : Nat}
    (hi : i < Γ.arity a.rel) :
    ∃ x : Var, a.args[i] = RelTerm.var x := by
  let j : Fin (Γ.arity a.rel) := ⟨i, hi⟩
  simpa [Vector.get] using
    exists_var_arg_of_constFree a hFree j

/- Evaluate an atom's terms to its tuple value. -/
def evalTuple
    (σ : Assign D)
    (a : RelAtom D Γ) :
    Tuple D (Γ.arity a.rel) :=
  RelTerm.evalVector σ a.args

/- Atom tuple evaluation as a list. -/
theorem evalTuple_toList
    (a : RelAtom D Γ)
    (σ : Assign D) :
    (a.evalTuple σ).toList =
      a.args.toList.map (fun term => term.eval σ) := by
  simp [RelAtom.evalTuple, RelTerm.evalVector_eq_map,
    Vector.toList_map]

/- A variable argument appears in the atom variable list. -/
private theorem var_mem_varList_of_getElem
    (a : RelAtom D Γ)
    {i : Nat}
    (hi : i < Γ.arity a.rel)
    {x : Var}
    (hArg : a.args[i] = RelTerm.var x) :
    x ∈ a.varList := by
  unfold varList
  apply List.mem_filterMap.mpr
  refine ⟨a.args[i], ?_, ?_⟩
  · rw [Vector.mem_toList_iff]
    exact Vector.getElem_mem hi
  · simp [RelTerm.var?, hArg]

/- A coordinate of a constant-free atom appears in its variable list. -/
theorem exists_var_mem_varList_of_constFree_getElem
    (a : RelAtom D Γ)
    (hFree : a.ConstFree)
    {i : Nat}
    (hi : i < Γ.arity a.rel) :
    ∃ x : Var,
      a.args[i] = RelTerm.var x ∧ x ∈ a.varList := by
  rcases exists_var_getElem_of_constFree a hFree hi with
    ⟨x, hArg⟩
  exact
    ⟨x, hArg,
      a.var_mem_varList_of_getElem hi hArg⟩

private theorem toList_constFree
    (a : RelAtom D Γ)
    (hFree : a.ConstFree) :
    ∀ t ∈ a.args.toList, t.ConstFree := by
  intro t ht
  rcases List.mem_iff_get.mp ht with ⟨i, hi⟩
  let j : Fin (Γ.arity a.rel) :=
    ⟨i.1, by
      simpa [Vector.length_toList] using i.2⟩
  have hGet : a.args.get j = t := by
    change a.args[i.1] = t
    have hCoord :
        a.args.toList[i.1] = a.args[i.1] :=
      Vector.getElem_toList i.2
    exact hCoord.symm.trans hi
  simpa [hGet] using hFree j

/- A constant-free atom has one variable-list entry per argument. -/
theorem varList_length_eq_arity_of_constFree
    (a : RelAtom D Γ)
    (hFree : a.ConstFree) :
    a.varList.length = Γ.arity a.rel := by
  have hMap :=
    RelTerm.map_eval_eq_filterMap_var?_map_of_constFree
      (fun _ => default) a.args.toList
      (a.toList_constFree hFree)
  have hLen := congrArg List.length hMap
  simpa [varList, Vector.length_toList] using hLen.symm

/- Constant-free atom evaluation follows the atom variable list. -/
theorem evalTuple_toList_eq_varList_map_of_constFree
    (a : RelAtom D Γ)
    (hFree : a.ConstFree)
    (σ : Assign D) :
    (a.evalTuple σ).toList = a.varList.map σ := by
  rw [evalTuple_toList]
  unfold varList
  exact
    RelTerm.map_eval_eq_filterMap_var?_map_of_constFree
      σ a.args.toList (a.toList_constFree hFree)

/- Atom evaluation depends only on variables in the atom. -/
theorem evalTuple_eq_of_assign_eq_on_vars
    (a : RelAtom D Γ)
    {σ₁ σ₂ : Assign D}
    (hσ : ∀ x : Var, x ∈ a.varList → σ₁ x = σ₂ x) :
    a.evalTuple σ₁ = a.evalTuple σ₂ := by
  apply Vector.ext
  intro i hi
  cases hArg : a.args[i] with
  | var x =>
      have hx := a.var_mem_varList_of_getElem hi hArg
      simp [RelAtom.evalTuple, RelTerm.evalVector_eq_map,
        Vector.getElem_map, hArg, RelTerm.eval, hσ x hx]
  | const _ =>
      simp [RelAtom.evalTuple, RelTerm.evalVector_eq_map,
        Vector.getElem_map, hArg, RelTerm.eval]

/- Variables in the atom variable list occur in atom variables. -/
theorem mem_vars_of_mem_varList
    (a : RelAtom D Γ)
    {x : Var}
    (hx : x ∈ a.varList) :
    x ∈ a.vars := by
  unfold varList at hx
  rcases List.mem_filterMap.mp hx with
    ⟨t, ht, htVar⟩
  have htVars : x ∈ t.vars := by
    cases t with
    | var y =>
        have hxy : y = x :=
          Option.some.inj htVar
        simp [RelTerm.vars, hxy]
    | const d =>
        simp [RelTerm.var?] at htVar
  unfold vars RelTerm.tupleVars
  exact RelTerm.mem_listVars_of_mem_term ht htVars

/-
  If an evaluated atom tuple is over `Q`, then every
  variable occurring in the atom is assigned a value in
  `Q`.
-/
theorem value_mem_of_var_mem_evalTuple_over
    (a : RelAtom D Γ)
    {σ : Assign D}
    {Q : Finset D}
    (hOver : (a.evalTuple σ).isTupleOver Q)
    {x : Var}
    (hx : x ∈ a.varList) :
    σ x ∈ Q := by
  unfold varList at hx
  rcases List.mem_filterMap.mp hx with
    ⟨term, hTerm, hVar⟩
  cases term with
  | var y =>
      simp only [RelTerm.var?] at hVar
      have hExists :
          ∃ i, ∃ hi : i < a.args.toList.length,
            a.args.toList[i] = RelTerm.var y := by
        exact
          (List.exists_mem_iff_getElem
            (p := fun term => term = RelTerm.var y)).mp
            ⟨RelTerm.var y, hTerm, rfl⟩
      rcases hExists with
        ⟨i, hi, hArgList⟩
      have hiArg : i < Γ.arity a.rel := by
        simpa [Vector.length_toList] using hi
      have hArgY : a.args[i] = RelTerm.var y := by
        simpa [Vector.getElem_toList hi] using hArgList
      have hyx : y = x := by
        cases hVar
        rfl
      have hArg : a.args[i] = RelTerm.var x := by
        simpa [hyx] using hArgY
      have hCoord := hOver ⟨i, hiArg⟩
      change (a.evalTuple σ)[i] ∈ Q at hCoord
      simpa [RelAtom.evalTuple, RelTerm.evalVector_eq_map,
        Vector.getElem_map, hArg, RelTerm.eval]
        using hCoord
  | const _ =>
      simp only [RelTerm.var?] at hVar
      cases hVar

end RelAtom

------------------------------------------------------------
-- Relational Facts
------------------------------------------------------------

/-
  A relational fact is a relation name paired with an
  arity-correct tuple for that relation.
-/
structure RelFact
    (D : Type) [Domain D]
    {A : Type} [RelationNames A]
    (Γ : UnnamedSchema A) where
  rel : Γ.syms
  tuple : Tuple D (Γ.arity rel)

namespace RelFact

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Fact membership in an instance. -/
def Mem
    (f : RelFact D Γ)
    (I : Instance D Γ) : Prop :=
  f.tuple ∈ I f.rel

instance
    (f : RelFact D Γ)
    (I : Instance D Γ) :
    Decidable (f.Mem I) := by
  unfold Mem
  infer_instance

end RelFact

------------------------------------------------------------
-- Relational Atom Satisfaction
------------------------------------------------------------

namespace RelAtom

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Evaluate an atom to a relational fact under an assignment. -/
def evalFact
    (a : RelAtom D Γ)
    (σ : Assign D) :
    RelFact D Γ where
  rel := a.rel
  tuple := a.evalTuple σ

/- Relational atom satisfaction in an instance. -/
def Sat
    (I : Instance D Γ)
    (σ : Assign D)
    (a : RelAtom D Γ) : Prop :=
  (a.evalFact σ).Mem I

instance
    (I : Instance D Γ)
    (σ : Assign D)
    (a : RelAtom D Γ) :
    Decidable (a.Sat I σ) := by
  unfold Sat RelFact.Mem evalFact
  infer_instance

end RelAtom
