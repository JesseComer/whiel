-- Author: Jesse Comer
import Databases.Datalog.OperationalSemantics
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Perm.Basic
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet.Lemmas
import Std.Data.TreeMap.Lemmas

set_option linter.unusedSectionVars false

/-
  This file implements executable semi-naive Datalog
  evaluation and proves it correct against the theorem-
  facing operational semantics.

  Key high-level definitions:
    * `Program.snLFPState`
    * `Program.snLFP`
    * `Query.snAnswer`

  The materialized state definitions are implementation
  details of the evaluator:
    * `Program.MaterializedInput`
    * `Program.MaterializedRelation`
    * `Program.MaterializedIDB`
    * `Program.SemiNaiveState`
    * `Program.CompiledRule`
    * `Program.CompiledProgram`
    * `Program.compileForSN`
    * `Program.materializeInput`
    * `Program.snLFPStateWithInput`
    * `Program.semiNaiveInitialState`
    * `Program.semiNaiveStep`
    * `Program.semiNaiveIterate`

  The main correctness theorems are:
    * `Program.snLFP_fixedOnInputAdom`
    * `Program.snLFP_eq_LFP`
    * `Program.snLFP_eq_minimalModel`
    * `Query.snAnswer_eq_answer`
-/

------------------------------------------------------------
-- Executable Partial Assignments
------------------------------------------------------------

namespace Datalog

/-
  A partial variable assignment built while joining relation
  tuples.
-/
abbrev PartialAssign (D : Type) :=
  List (Var × D)

namespace PartialAssign

variable {D : Type} [Domain D]

/- Look up a variable in a partial assignment. -/
def lookup : PartialAssign D → Var → Option D
| [], _x => none
| (y, d) :: ρ, x =>
    if y = x then
      some d
    else
      lookup ρ x

/-
  Bind a variable, rejecting inconsistent duplicate
  values.
-/
def bind
    (ρ : PartialAssign D)
    (x : Var)
    (d : D) :
    Option (PartialAssign D) :=
  match lookup ρ x with
  | none => some ((x, d) :: ρ)
  | some d' =>
      if d' = d then
        some ρ
      else
        none

/-
  Read a term from a partial assignment, if all variables
  are bound.
-/
def evalTerm?
    (ρ : PartialAssign D) :
    RelTerm D → Option D
| .var x => lookup ρ x
| .const d => some d

/- Turn a partial assignment into a total assignment. -/
def toAssign
    (ρ : PartialAssign D) :
    Assign D :=
  fun x =>
    match lookup ρ x with
    | some d => d
    | none => default

end PartialAssign

------------------------------------------------------------
-- Executable Slot Assignments
------------------------------------------------------------

/-
  Slot terms are normalized relational terms whose variables
  have been compiled to dense rule-local slots.
-/
inductive SlotTerm (D : Type) where
| var : Var → Nat → SlotTerm D
| const : D → SlotTerm D
deriving DecidableEq

namespace SlotTerm

variable {D : Type} [Domain D]

/- The source relational term represented by a slot term. -/
def toRelTerm : SlotTerm D → RelTerm D
| .var x _slot => RelTerm.var x
| .const d => RelTerm.const d

end SlotTerm

/-
  A relational atom whose variables have slot metadata.
  The source atom is recovered by dropping slot positions.
-/
structure SlotRelAtom
    (D : Type)
    [Domain D]
    {A : Type} [RelationNames A]
    (Γ : UnnamedSchema A) where
  source : RelAtom D Γ
  args : Vector (SlotTerm D) (Γ.arity source.rel)
  args_toRel :
    args.map SlotTerm.toRelTerm = source.args

namespace SlotRelAtom

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Drop slot metadata from a compiled relational atom. -/
def toRelAtom
    (a : SlotRelAtom D Γ) :
    RelAtom D Γ :=
  a.source

/- Slot arguments erase to the source atom arguments. -/
theorem args_toRel_toList
    (a : SlotRelAtom D Γ) :
    a.args.toList.map SlotTerm.toRelTerm =
      a.source.args.toList := by
  rw [← Vector.toList_map, a.args_toRel]

end SlotRelAtom

/-
  Rule-local variable-to-slot metadata. The map is used by
  compiled execution; the variable list records the
  deterministic slot order.
-/
structure SlotEnv where
  slots : Std.TreeMap Var Nat compare
  vars : List Var

namespace SlotEnv

/- Empty slot environment. -/
def empty : SlotEnv where
  slots := Std.TreeMap.empty
  vars := []

/- Number of slots in an environment. -/
def size (env : SlotEnv) : Nat :=
  env.vars.length

/- List-backed slot lookup used by proofs and compilation. -/
def slotOfListFrom :
    Nat → List Var → Var → Option Nat
| _n, [], _x => none
| n, y :: ys, x =>
    if x = y then
      some n
    else
      slotOfListFrom (n + 1) ys x

/- Look up the slot assigned to a variable. -/
def slotOf
    (env : SlotEnv)
    (x : Var) :
    Option Nat :=
  slotOfListFrom 0 env.vars x

/- A slot environment is well-formed when slot names are unique. -/
def WellFormed
    (env : SlotEnv) :
    Prop :=
  env.vars.Nodup

/- Insert a variable if it has not already been assigned. -/
def insertVar
    (env : SlotEnv)
    (x : Var) :
    SlotEnv :=
  match env.slotOf x with
  | some _slot => env
  | none =>
      { slots := env.slots.insert x env.size
        vars := env.vars ++ [x] }

/- Build slots from a deterministic variable list. -/
def ofVars
    (xs : List Var) :
    SlotEnv :=
  xs.foldl insertVar empty

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Compile one relational term using this environment. -/
def compileTerm
    (env : SlotEnv) :
    RelTerm D → SlotTerm D
| .var x =>
    match env.slotOf x with
    | some slot => SlotTerm.var x slot
    | none => SlotTerm.var x 0
| .const d => SlotTerm.const d

/- Compile one relational atom using this environment. -/
def compileRelAtom
    (env : SlotEnv)
    (a : RelAtom D Γ) :
    SlotRelAtom D Γ where
  source := a
  args := a.args.map env.compileTerm
  args_toRel := by
    apply Vector.ext
    intro i hi
    rw [Vector.getElem_map, Vector.getElem_map]
    cases hTerm : a.args[i] with
    | var x =>
        unfold compileTerm
        cases hSlot : env.slotOf x <;>
          simp [SlotTerm.toRelTerm, hSlot]
    | const d =>
        rfl

/- Compile relational body entries using this environment. -/
def compileRelEntries
    (env : SlotEnv) :
    List (Nat × RelAtom D Γ) →
      List (Nat × SlotRelAtom D Γ)
| [] => []
| (idx, a) :: entries =>
    (idx, env.compileRelAtom a) ::
      compileRelEntries env entries

set_option linter.flexible false in
theorem slotOfListFrom_bound
    {n : Nat}
    {xs : List Var}
    {x : Var}
    {slot : Nat}
    (hSlot : slotOfListFrom n xs x = some slot) :
    slot < n + xs.length := by
  induction xs generalizing n with
  | nil =>
      simp [slotOfListFrom] at hSlot
  | cons y ys ih =>
      unfold slotOfListFrom at hSlot
      by_cases hxy : x = y
      · simp [hxy] at hSlot
        cases hSlot
        simp
      · simp [hxy] at hSlot
        have hBound := ih hSlot
        simpa [Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm] using hBound

set_option linter.flexible false in
theorem slotOfListFrom_ge
    {n : Nat}
    {xs : List Var}
    {x : Var}
    {slot : Nat}
    (hSlot : slotOfListFrom n xs x = some slot) :
    n ≤ slot := by
  induction xs generalizing n with
  | nil =>
      simp [slotOfListFrom] at hSlot
  | cons y ys ih =>
      unfold slotOfListFrom at hSlot
      by_cases hxy : x = y
      · simp [hxy] at hSlot
        cases hSlot
        omega
      · simp [hxy] at hSlot
        have hGe := ih hSlot
        omega

theorem slotOf_bound
    {env : SlotEnv}
    {x : Var}
    {slot : Nat}
    (hSlot : env.slotOf x = some slot) :
    slot < env.size := by
  change slot < env.vars.length
  change slotOfListFrom 0 env.vars x = some slot at hSlot
  simpa using
    slotOfListFrom_bound (n := 0) (xs := env.vars)
      (x := x) hSlot

theorem slotOfListFrom_none_iff
    (n : Nat)
    (xs : List Var)
    (x : Var) :
    slotOfListFrom n xs x = none ↔ x ∉ xs := by
  induction xs generalizing n with
  | nil =>
      simp [slotOfListFrom]
  | cons y ys ih =>
      unfold slotOfListFrom
      by_cases hxy : x = y
      · simp [hxy]
      · simp [hxy, ih (n + 1), List.mem_cons]

theorem slotOf_none_iff
    (env : SlotEnv)
    (x : Var) :
    env.slotOf x = none ↔ x ∉ env.vars := by
  exact slotOfListFrom_none_iff 0 env.vars x

theorem slotOf_some_of_mem
    {env : SlotEnv}
    {x : Var}
    (hx : x ∈ env.vars) :
    ∃ slot : Nat, env.slotOf x = some slot := by
  cases hSlot : env.slotOf x with
  | none =>
      have hxNot := (slotOf_none_iff env x).mp hSlot
      exact False.elim (hxNot hx)
  | some slot =>
      exact ⟨slot, rfl⟩

theorem mem_vars_insertVar_of_mem
    {env : SlotEnv}
    {x y : Var}
    (hy : y ∈ env.vars) :
    y ∈ (env.insertVar x).vars := by
  unfold insertVar
  cases hSlot : env.slotOf x with
  | some slot =>
      simpa [hSlot] using hy
  | none =>
      simp [hy]

theorem mem_vars_insertVar_self
    (env : SlotEnv)
    (x : Var) :
    x ∈ (env.insertVar x).vars := by
  unfold insertVar
  cases hSlot : env.slotOf x with
  | some slot =>
      have hx : x ∈ env.vars := by
        by_contra hx
        have hNone := (slotOf_none_iff env x).mpr hx
        rw [hSlot] at hNone
        contradiction
      simpa [hSlot] using hx
  | none =>
      simp

set_option linter.flexible false in
theorem mem_vars_foldl_insertVar_of_mem_env
    (xs : List Var)
    {env : SlotEnv}
    {y : Var}
    (hy : y ∈ env.vars) :
    y ∈ (xs.foldl insertVar env).vars := by
  induction xs generalizing env with
  | nil =>
      simpa using hy
  | cons x xs ih =>
      simp [List.foldl]
      exact ih (mem_vars_insertVar_of_mem hy)

set_option linter.flexible false in
theorem mem_vars_foldl_insertVar_of_mem_list
    (xs : List Var)
    {env : SlotEnv}
    {y : Var}
    (hy : y ∈ xs) :
    y ∈ (xs.foldl insertVar env).vars := by
  induction xs generalizing env with
  | nil =>
      simp at hy
  | cons x xs ih =>
      simp [List.foldl] at hy ⊢
      rcases hy with hy | hy
      · subst y
        exact
          mem_vars_foldl_insertVar_of_mem_env xs
            (mem_vars_insertVar_self env x)
      · exact ih hy

theorem mem_vars_ofVars_of_mem
    {xs : List Var}
    {x : Var}
    (hx : x ∈ xs) :
    x ∈ (ofVars xs).vars := by
  unfold ofVars
  exact mem_vars_foldl_insertVar_of_mem_list xs hx

set_option linter.flexible false in
theorem slotOfListFrom_injective
    {n : Nat}
    {xs : List Var}
    (hNoDup : xs.Nodup)
    {x y : Var}
    {slot : Nat}
    (hx : slotOfListFrom n xs x = some slot)
    (hy : slotOfListFrom n xs y = some slot) :
    x = y := by
  induction xs generalizing n with
  | nil =>
      simp [slotOfListFrom] at hx
  | cons z zs ih =>
      have hNoDup' : z ∉ zs ∧ zs.Nodup := by
        simpa [List.nodup_cons] using hNoDup
      have hNoDupTail : zs.Nodup := hNoDup'.2
      unfold slotOfListFrom at hx hy
      by_cases hxz : x = z
      · have hSlotEq : n = slot := by
          simpa [hxz] using hx
        by_cases hyz : y = z
        · exact hxz.trans hyz.symm
        · simp [hyz] at hy
          have hBound :=
            slotOfListFrom_ge
              (n := n + 1) (xs := zs) (x := y) hy
          omega
      · simp [hxz] at hx
        by_cases hyz : y = z
        · have hSlotEq : n = slot := by
            simpa [hyz] using hy
          have hBound :=
            slotOfListFrom_ge
              (n := n + 1) (xs := zs) (x := x) hx
          omega
        · simp [hyz] at hy
          exact ih hNoDupTail hx hy

theorem slotOf_injective
    {env : SlotEnv}
    (hWF : env.WellFormed)
    {x y : Var}
    {slot : Nat}
    (hx : env.slotOf x = some slot)
    (hy : env.slotOf y = some slot) :
    x = y := by
  unfold slotOf at hx hy
  exact slotOfListFrom_injective hWF hx hy

theorem empty_wellFormed :
    (empty : SlotEnv).WellFormed := by
  simp [WellFormed, empty]

theorem insertVar_wellFormed
    {env : SlotEnv}
    (hWF : env.WellFormed)
    (x : Var) :
    (env.insertVar x).WellFormed := by
  unfold insertVar
  cases hSlot : env.slotOf x with
  | some slot =>
      simpa [hSlot] using hWF
  | none =>
      have hxNot : x ∉ env.vars :=
        (slotOf_none_iff env x).mp hSlot
      simpa [hSlot, WellFormed] using hWF.concat hxNot

set_option linter.flexible false in
theorem foldl_insertVar_wellFormed
    (xs : List Var)
    {env : SlotEnv}
    (hWF : env.WellFormed) :
    (xs.foldl insertVar env).WellFormed := by
  induction xs generalizing env with
  | nil =>
      simpa using hWF
  | cons x xs ih =>
      simp [List.foldl]
      exact ih (insertVar_wellFormed hWF x)

theorem ofVars_wellFormed
    (xs : List Var) :
    (ofVars xs).WellFormed := by
  unfold ofVars
  exact foldl_insertVar_wellFormed xs empty_wellFormed

end SlotEnv

namespace SlotTerm

variable {D : Type} [Domain D]

/-
  A slot term is well-formed when its variable slots come
  from an environment.
-/
def WF
    (env : SlotEnv) :
    SlotTerm D → Prop
| .var x slot => env.slotOf x = some slot
| .const _d => True

end SlotTerm

namespace SlotRelAtom

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- A slot atom is well-formed when all of its terms are. -/
def WF
    (env : SlotEnv)
    (a : SlotRelAtom D Γ) :
    Prop :=
  ∀ i : Fin (Γ.arity a.source.rel),
    (a.args.get i).WF env

end SlotRelAtom

namespace SlotEnv

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

theorem compileTerm_wf
    (env : SlotEnv)
    (term : RelTerm D)
    (hMem :
      ∀ x : Var, term.var? = some x → x ∈ env.vars) :
    SlotTerm.WF env (env.compileTerm term) := by
  cases term with
  | var x =>
      rcases slotOf_some_of_mem (hMem x rfl) with
        ⟨slot, hSlot⟩
      simp [compileTerm, hSlot, SlotTerm.WF]
  | const d =>
      simp [compileTerm, SlotTerm.WF]

theorem compileRelAtom_wf
    (env : SlotEnv)
    (a : RelAtom D Γ)
    (hMem :
      ∀ x : Var, x ∈ a.varList → x ∈ env.vars) :
    SlotRelAtom.WF env (env.compileRelAtom a) := by
  unfold SlotRelAtom.WF
  intro i
  have hTerm :
      SlotTerm.WF env
        (env.compileTerm (a.args.get i)) := by
    apply compileTerm_wf
    intro x hx
    apply hMem
    unfold RelAtom.varList
    rw [List.mem_filterMap]
    refine ⟨a.args.get i, ?_, hx⟩
    simp [Vector.get]
  simpa [compileRelAtom, Vector.get] using hTerm

end SlotEnv

/-
  Runtime slot assignment. The array is the execution view;
  `bindings` is retained as the proof-facing assignment view
  and is updated consistently by the constructors below.
-/
structure SlotAssign (D : Type) where
  values : Array (Option D)
  bindings : PartialAssign D

namespace SlotAssign

variable {D : Type} [Domain D]

/- Empty slot assignment with a fixed slot count. -/
def empty
    (slotCount : Nat) :
    SlotAssign D where
  values := Array.mk (List.replicate slotCount none)
  bindings := []

/- Read a slot value. Malformed out-of-bounds reads fail. -/
def lookupSlot
    (ρ : SlotAssign D)
    (slot : Nat) :
    Option D :=
  match ρ.values[slot]? with
  | some value => value
  | none => none

/- Read a compiled term from a slot assignment. -/
def evalTerm? :
    SlotAssign D → SlotTerm D → Option D
| ρ, SlotTerm.var _x slot => ρ.lookupSlot slot
| _ρ, SlotTerm.const d => some d

/- Bind a variable slot, rejecting inconsistent values. -/
def bind
    (ρ : SlotAssign D)
    (x : Var)
    (slot : Nat)
    (d : D) :
    Option (SlotAssign D) :=
  if hSlot : slot < ρ.values.size then
    match ρ.values[slot] with
    | none =>
        match PartialAssign.bind ρ.bindings x d with
        | none => none
        | some bindings' =>
            some
              { values := ρ.values.set slot (some d) hSlot
                bindings := bindings' }
    | some d' =>
        if d' = d then
          match PartialAssign.bind ρ.bindings x d with
          | none => none
          | some bindings' =>
              some
                { values := ρ.values
                  bindings := bindings' }
        else
          none
  else
    none

/- Match a compiled term against a concrete tuple value. -/
def matchTerm
    (ρ : SlotAssign D)
    (term : SlotTerm D)
    (d : D) :
    Option (SlotAssign D) :=
  match term with
  | SlotTerm.var x slot => ρ.bind x slot d
  | SlotTerm.const c =>
      if c = d then
        some ρ
      else
        none

variable {A : Type} [RelationNames A]
variable {Γ : UnnamedSchema A}

/- Match compiled atom arguments against concrete tuple values. -/
def matchTerms :
    SlotAssign D → List (SlotTerm D) → List D →
      Option (SlotAssign D)
| ρ, [], [] => some ρ
| ρ, term :: terms, d :: ds =>
    match matchTerm ρ term d with
    | none => none
    | some ρ' => matchTerms ρ' terms ds
| _ρ, _, _ => none

/- Extend a slot assignment using one tuple of an atom. -/
def extendWithAtomTuple
    (ρ : SlotAssign D)
    (a : SlotRelAtom D Γ)
    (t : Tuple D (Γ.arity a.source.rel)) :
    Option (SlotAssign D) :=
  matchTerms ρ a.args.toList t.toList

/- Directly materialize a compiled atom's tuple. -/
def evalAtomTuple
    (a : SlotRelAtom D Γ)
    (ρ : SlotAssign D) :
    Tuple D (Γ.arity a.source.rel) :=
  Vector.ofFn
    (fun i =>
      match ρ.evalTerm? (a.args.get i) with
      | some d => d
      | none => default)

/-
  A slot assignment coherently mirrors the proof-facing
  bindings.
-/
def Coherent
    (env : SlotEnv)
    (ρ : SlotAssign D) :
    Prop :=
  ρ.values.size = env.size ∧
    ∀ x slot,
      env.slotOf x = some slot →
        ρ.lookupSlot slot = PartialAssign.lookup ρ.bindings x

end SlotAssign

end Datalog

------------------------------------------------------------
-- Tuple List Set Operations
------------------------------------------------------------

namespace Tuple

variable {D : Type} [LinearOrder D]

/-
  Tuple-list union for execution state. This places the
  fresh right argument first so a step does not traverse the
  large old tuple list just to extend it.
-/
def listUnion
    {n : Nat}
    (xs ys : List (Tuple D n)) :
    List (Tuple D n) :=
  ys ++ xs

omit [LinearOrder D] in
theorem mem_listUnion_iff
    {n : Nat}
    (xs ys : List (Tuple D n))
    (t : Tuple D n) :
    t ∈ listUnion xs ys ↔ t ∈ xs ∨ t ∈ ys := by
  unfold listUnion
  constructor
  · intro ht
    rcases List.mem_append.mp ht with h | h
    · exact Or.inr h
    · exact Or.inl h
  · intro ht
    rcases ht with h | h
    · exact List.mem_append.mpr (Or.inr h)
    · exact List.mem_append.mpr (Or.inl h)

theorem listUnion_toFinset
    {n : Nat}
    (xs ys : List (Tuple D n)) :
    (listUnion xs ys).toFinset = xs.toFinset ∪ ys.toFinset := by
  apply Finset.ext
  intro t
  simp [List.mem_toFinset, mem_listUnion_iff]

omit [LinearOrder D] in
theorem nodup_listUnion
    {n : Nat}
    {xs ys : List (Tuple D n)}
    (hxs : xs.Nodup)
    (hys : ys.Nodup)
    (hFresh : ∀ t : Tuple D n, t ∈ ys → t ∉ xs) :
    (listUnion xs ys).Nodup := by
  unfold listUnion
  rw [List.nodup_append]
  exact ⟨hys, hxs, by
    intro t htys u huxs hEq
    exact hFresh t htys (by simpa [hEq] using huxs)⟩

/- List difference for tuple execution state. -/
def listDiff
    {n : Nat}
    (xs ys : List (Tuple D n)) :
    List (Tuple D n) :=
  xs.filter (fun t => decide (t ∉ ys))

theorem mem_listDiff_iff
    {n : Nat}
    (xs ys : List (Tuple D n))
    (t : Tuple D n) :
    t ∈ listDiff xs ys ↔ t ∈ xs ∧ t ∉ ys := by
  unfold listDiff
  simp [List.mem_filter]

theorem listDiff_toFinset
    {n : Nat}
    (xs ys : List (Tuple D n)) :
    (listDiff xs ys).toFinset = xs.toFinset \ ys.toFinset := by
  apply Finset.ext
  intro t
  simp [List.mem_toFinset, mem_listDiff_iff]

/- Fresh candidate tuples relative to an old tuple list. -/
def listFresh
    {n : Nat}
    (candidates old : List (Tuple D n)) :
    List (Tuple D n) :=
  listDiff (Tuple.sortDedup candidates) old

theorem mem_listFresh_iff
    {n : Nat}
    (candidates old : List (Tuple D n))
    (t : Tuple D n) :
    t ∈ listFresh candidates old ↔
      t ∈ candidates ∧ t ∉ old := by
  unfold listFresh
  rw [mem_listDiff_iff]
  simp [Tuple.mem_sortDedup_iff]

theorem listFresh_toFinset
    {n : Nat}
    (candidates old : List (Tuple D n)) :
    (listFresh candidates old).toFinset =
      candidates.toFinset \ old.toFinset := by
  apply Finset.ext
  intro t
  simp [List.mem_toFinset, mem_listFresh_iff]

variable [Hashable D]

/- Whole-tuple membership index for fast freshness checks. -/
structure MemberIndex
    (D : Type)
    [DecidableEq D]
    [Hashable D]
    (n : Nat) where
  set : Std.HashSet (Tuple D n)

namespace MemberIndex

variable {D : Type} [LinearOrder D] [DecidableEq D] [Hashable D]

/- Empty tuple membership index. -/
def empty
    {n : Nat} :
    MemberIndex D n where
  set := ∅

/- Boolean membership lookup in a tuple membership index. -/
def contains
    {n : Nat}
    (idx : MemberIndex D n)
    (t : Tuple D n) :
    Bool :=
  idx.set.contains t

/- Insert one tuple into a membership index. -/
def insert
    {n : Nat}
    (u : Tuple D n)
    (idx : MemberIndex D n) :
    MemberIndex D n where
  set := idx.set.insert u

/- Build a membership index from tuple data. -/
def ofList
    {n : Nat} :
    List (Tuple D n) → MemberIndex D n
| [] => empty
| u :: us => insert u (ofList us)

/- Insert a list of tuples into a membership index. -/
def insertList
    {n : Nat} :
    List (Tuple D n) → MemberIndex D n → MemberIndex D n
| [], idx => idx
| u :: us, idx => insertList us (insert u idx)

theorem contains_insert_iff
    {n : Nat}
    (idx : MemberIndex D n)
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

theorem contains_ofList_iff
    {n : Nat}
    (ts : List (Tuple D n))
    (t : Tuple D n) :
    (ofList ts).contains t = true ↔ t ∈ ts := by
  induction ts with
  | nil =>
      simp [ofList, empty, contains]
  | cons u us ih =>
      rw [ofList, contains_insert_iff, ih]
      constructor
      · intro h
        rcases h with h | h
        · exact List.mem_cons.mpr (Or.inl h)
        · exact List.mem_cons.mpr (Or.inr h)
      · intro h
        rcases List.mem_cons.mp h with h | h
        · exact Or.inl h
        · exact Or.inr h

theorem contains_insertList_iff
    {n : Nat}
    (fresh : List (Tuple D n))
    (idx : MemberIndex D n)
    (t : Tuple D n) :
    (insertList fresh idx).contains t = true ↔
      t ∈ fresh ∨ idx.contains t = true := by
  induction fresh generalizing idx with
  | nil =>
      simp [insertList]
  | cons u us ih =>
      rw [insertList, ih (insert u idx),
        contains_insert_iff]
      constructor
      · intro h
        rcases h with hFresh | hOld
        · exact
            Or.inl (List.mem_cons.mpr (Or.inr hFresh))
        · rcases hOld with hNew | hOld
          · exact
              Or.inl (List.mem_cons.mpr (Or.inl hNew))
          · exact Or.inr hOld
      · intro h
        rcases h with hFresh | hOld
        · rcases List.mem_cons.mp hFresh with hHead | hTail
          · exact Or.inr (Or.inl hHead)
          · exact Or.inl hTail
        · exact Or.inr (Or.inr hOld)

end MemberIndex

/- One hash-map index for a tuple column. -/
structure ColumnIndex
    (D : Type)
    [DecidableEq D]
    [Hashable D]
    (n : Nat) where
  map : Std.HashMap D (List (Tuple D n))

namespace ColumnIndex

variable {D : Type} [LinearOrder D] [DecidableEq D] [Hashable D]

/- Empty column index. -/
def empty
    {n : Nat} :
    ColumnIndex D n where
  map := ∅

/- Look up tuples whose indexed column has a key. -/
def lookup
    {n : Nat}
    (idx : ColumnIndex D n)
    (d : D) :
    List (Tuple D n) :=
  idx.map.getD d []

/- Insert a tuple into a column index. -/
def insert
    {n : Nat}
    (i : Fin n)
    (u : Tuple D n)
    (idx : ColumnIndex D n) :
    ColumnIndex D n where
  map := idx.map.insert (u.get i)
    (u :: idx.lookup (u.get i))

/- Build a column index from tuple data. -/
def ofList
    {n : Nat}
    (i : Fin n) :
    List (Tuple D n) → ColumnIndex D n
| [] => empty
| u :: us => insert i u (ofList i us)

theorem mem_lookup_insert_iff
    {n : Nat}
    (idx : ColumnIndex D n)
    (i : Fin n)
    (u t : Tuple D n)
    (d : D) :
    t ∈ (idx.insert i u).lookup d ↔
      (t = u ∧ u.get i = d) ∨ t ∈ idx.lookup d := by
  unfold insert lookup
  rw [Std.HashMap.getD_insert]
  by_cases h : u.get i = d
  · simp [h]
  · have hBeq : ((u.get i) == d) = false := by
      cases hEq : ((u.get i) == d)
      · rfl
      · exact False.elim (h (LawfulBEq.eq_of_beq hEq))
    simp [hBeq, h]

theorem mem_lookup_ofList_iff
    {n : Nat}
    (i : Fin n)
    (ts : List (Tuple D n))
    (d : D)
    (t : Tuple D n) :
    t ∈ (ofList i ts).lookup d ↔
      t ∈ ts ∧ t.get i = d := by
  induction ts with
  | nil =>
      simp [ofList, empty, lookup]
  | cons u us ih =>
      constructor
      · intro ht
        rcases
            (mem_lookup_insert_iff
              (ofList i us) i u t d).mp ht with h | h
        · exact
            ⟨List.mem_cons.mpr (Or.inl h.1),
              by simpa [h.1] using h.2⟩
        · rcases ih.mp h with ⟨hMem, hGet⟩
          exact ⟨List.mem_cons.mpr (Or.inr hMem), hGet⟩
      · intro ht
        rcases ht with ⟨hMem, hGet⟩
        rcases List.mem_cons.mp hMem with hEq | hMem
        · exact
            (mem_lookup_insert_iff
              (ofList i us) i u t d).mpr
              (Or.inl ⟨hEq, by simpa [hEq] using hGet⟩)
        · exact
            (mem_lookup_insert_iff
              (ofList i us) i u t d).mpr
              (Or.inr (ih.mpr ⟨hMem, hGet⟩))

end ColumnIndex

/- Per-column tuple indexes for one relation. -/
structure Index
    (D : Type)
    [DecidableEq D]
    [Hashable D]
    (n : Nat) where
  columns : Vector (ColumnIndex D n) n

namespace Index

variable {D : Type} [LinearOrder D] [DecidableEq D] [Hashable D]

/- Build every column index for a tuple list. -/
def ofList
    {n : Nat}
    (ts : List (Tuple D n)) :
    Index D n where
  columns :=
    Vector.ofFn
      (fun i : Fin n => ColumnIndex.ofList i ts)

/- Look up tuples whose `i`th coordinate has value `d`. -/
def lookup
    {n : Nat}
    (idx : Index D n)
    (i : Fin n)
    (d : D) :
    List (Tuple D n) :=
  (idx.columns.get i).lookup d

/- Insert one tuple into every column index. -/
def insert
    {n : Nat}
    (u : Tuple D n)
    (idx : Index D n) :
    Index D n where
  columns :=
    Vector.ofFn
      (fun i : Fin n =>
        (idx.columns.get i).insert i u)

/- Insert a list of tuples into every column index. -/
def insertList
    {n : Nat} :
    List (Tuple D n) → Index D n → Index D n
| [], idx => idx
| u :: us, idx => insertList us (insert u idx)

theorem mem_lookup_iff
    {n : Nat}
    (ts : List (Tuple D n))
    (i : Fin n)
    (d : D)
    (t : Tuple D n) :
    t ∈ (ofList ts).lookup i d ↔ t ∈ ts ∧ t.get i = d := by
  simp [ofList, lookup, Vector.get,
    ColumnIndex.mem_lookup_ofList_iff]

theorem mem_lookup_insert_iff
    {n : Nat}
    (idx : Index D n)
    (u t : Tuple D n)
    (i : Fin n)
    (d : D) :
    t ∈ (insert u idx).lookup i d ↔
      (t = u ∧ u.get i = d) ∨ t ∈ idx.lookup i d := by
  simp [insert, lookup, Vector.get,
    ColumnIndex.mem_lookup_insert_iff]

theorem mem_lookup_insertList_iff
    {n : Nat}
    (fresh : List (Tuple D n))
    (idx : Index D n)
    (i : Fin n)
    (d : D)
    (t : Tuple D n) :
    t ∈ (insertList fresh idx).lookup i d ↔
      (t ∈ fresh ∧ t.get i = d) ∨
        t ∈ idx.lookup i d := by
  induction fresh generalizing idx with
  | nil =>
      simp [insertList]
  | cons u us ih =>
      rw [insertList, ih (insert u idx)]
      rw [mem_lookup_insert_iff]
      constructor
      · intro ht
        rcases ht with hFresh | hOld
        · exact
            Or.inl
              ⟨List.mem_cons.mpr (Or.inr hFresh.1),
                hFresh.2⟩
        · rcases hOld with hNew | hOld
          · exact
              Or.inl
                ⟨List.mem_cons.mpr (Or.inl hNew.1),
                  by simpa [hNew.1] using hNew.2⟩
          · exact Or.inr hOld
      · intro ht
        rcases ht with hFresh | hOld
        · rcases List.mem_cons.mp hFresh.1 with hHead | hTail
          · exact
              Or.inr
                (Or.inl
                  ⟨hHead, by simpa [hHead] using hFresh.2⟩)
          · exact Or.inl ⟨hTail, hFresh.2⟩
        · exact Or.inr (Or.inr hOld)

end Index

end Tuple

------------------------------------------------------------
-- Materialized Semi-Naive State
------------------------------------------------------------

namespace Datalog

namespace Program

variable {A D : Type}
variable [RelationNames A] [Domain D] [LinearOrder D] [Hashable D]
variable {Γ : UnnamedSchema A}

/- One materialized relation for a single IDB symbol. -/
structure MaterializedRelation (P : Program D Γ) where
  sym : P.IDBSym
  tuples : List (Tuple D (Γ.arity sym.1))
  nodup_tuples : tuples.Nodup
  index : Tuple.Index D (Γ.arity sym.1)
  index_mem :
    ∀ (i : Fin (Γ.arity sym.1)) (d : D)
      (t : Tuple D (Γ.arity sym.1)),
      t ∈ index.lookup i d ↔ t ∈ tuples ∧ t.get i = d
  memberIndex : Tuple.MemberIndex D (Γ.arity sym.1)
  memberIndex_mem :
    ∀ t : Tuple D (Γ.arity sym.1),
      memberIndex.contains t = true ↔ t ∈ tuples

namespace MaterializedRelation

/-
  Build a materialized relation from executable candidate
  tuples, sorting and deduplicating at the relation
  boundary.
-/
def ofTupleList
    [LinearOrder D]
    {P : Program D Γ}
    (X : P.IDBSym)
    (ts : List (Tuple D (Γ.arity X.1))) :
    MaterializedRelation P :=
  let us := Tuple.sortDedup ts
  { sym := X
    tuples := us
    nodup_tuples := Tuple.nodup_sortDedup ts
    index := Tuple.Index.ofList us
    index_mem := by
      intro i d t
      exact Tuple.Index.mem_lookup_iff us i d t
    memberIndex := Tuple.MemberIndex.ofList us
    memberIndex_mem := by
      intro t
      exact Tuple.MemberIndex.contains_ofList_iff us t }

/- Build a materialized relation from a proof-facing relation. -/
def ofFacts
    [LinearOrder D]
    {P : Program D Γ}
    (X : P.IDBSym)
    (R : FinRelation D (Γ.arity X.1)) :
  MaterializedRelation P :=
  ofTupleList X R.sort

/- Indexed lookup in one materialized relation. -/
def lookupByValue
    {P : Program D Γ}
    (R : MaterializedRelation P)
    (i : Fin (Γ.arity R.sym.1))
    (d : D) :
    List (Tuple D (Γ.arity R.sym.1)) :=
  R.index.lookup i d

theorem mem_lookupByValue_iff
    {P : Program D Γ}
    (R : MaterializedRelation P)
    (i : Fin (Γ.arity R.sym.1))
    (d : D)
    (t : Tuple D (Γ.arity R.sym.1)) :
    t ∈ R.lookupByValue i d ↔
      t ∈ R.tuples ∧ t.get i = d := by
  exact R.index_mem i d t

/- Whole-tuple membership lookup in one materialized relation. -/
def contains
    {P : Program D Γ}
    (R : MaterializedRelation P)
    (t : Tuple D (Γ.arity R.sym.1)) :
    Bool :=
  R.memberIndex.contains t

theorem contains_iff
    {P : Program D Γ}
    (R : MaterializedRelation P)
    (t : Tuple D (Γ.arity R.sym.1)) :
    R.contains t = true ↔ t ∈ R.tuples := by
  exact R.memberIndex_mem t

/- Direct finite relation construction from deduped tuples. -/
private def finRelationOfNodupList
    {n : Nat}
    (ts : List (Tuple D n))
    (hNodup : ts.Nodup) :
    FinRelation D n :=
  ⟨ts, hNodup⟩

/- Proof-facing relation view of a materialized relation. -/
def toFinRelation
    {P : Program D Γ}
    (R : MaterializedRelation P) :
    FinRelation D (Γ.arity R.sym.1) :=
  finRelationOfNodupList R.tuples R.nodup_tuples

theorem mem_toFinRelation_iff
    {P : Program D Γ}
    (R : MaterializedRelation P)
    (t : Tuple D (Γ.arity R.sym.1)) :
    t ∈ R.toFinRelation ↔ t ∈ R.tuples := by
  simp [toFinRelation, finRelationOfNodupList]

omit [LinearOrder D] in
theorem mem_facts_ofTupleList_iff
    [LinearOrder D]
    {P : Program D Γ}
    (X : P.IDBSym)
    (ts : List (Tuple D (Γ.arity X.1)))
    (t : Tuple D (Γ.arity X.1)) :
    t ∈ (ofTupleList X ts).toFinRelation ↔ t ∈ ts := by
  unfold ofTupleList
  simp [toFinRelation, finRelationOfNodupList,
    Tuple.mem_sortDedup_iff]

end MaterializedRelation

/- Explicit IDB relations in `P.idbSymList` order. -/
structure MaterializedIDB (P : Program D Γ) where
  relations : List (MaterializedRelation P)

namespace MaterializedIDB

/-
  Scan materialized relation entries for an IDB symbol,
  falling back to empty on malformed states.
-/
def lookupRelations
    (P : Program D Γ) :
    List (MaterializedRelation P) →
      (X : Γ.syms) → X ∈ P.idb →
        FinRelation D (Γ.arity X)
| [], _X, _hX => ∅
| relation :: relations, X, hX =>
    if h : relation.sym.1 = X then
      cast
        (congrArg
          (fun Z : Γ.syms =>
            FinRelation D (Γ.arity Z))
          h)
        relation.toFinRelation
    else
      lookupRelations P relations X hX

/-
  Scan materialized relation entries for the executable
  tuple list of an IDB symbol.
-/
def lookupTupleLists
    (P : Program D Γ) :
    List (MaterializedRelation P) →
      (X : Γ.syms) → X ∈ P.idb →
        List (Tuple D (Γ.arity X))
| [], _X, _hX => []
| relation :: relations, X, hX =>
    if h : relation.sym.1 = X then
      cast
        (congrArg
          (fun Z : Γ.syms => List (Tuple D (Γ.arity Z)))
          h)
        relation.tuples
    else
      lookupTupleLists P relations X hX

/-
  Scan materialized relation entries for an IDB relation's
  tuple index.
-/
def lookupIndexLists
    (P : Program D Γ) :
    List (MaterializedRelation P) →
      (X : Γ.syms) → X ∈ P.idb →
        Tuple.Index D (Γ.arity X)
| [], _X, _hX => Tuple.Index.ofList []
| relation :: relations, X, hX =>
    if h : relation.sym.1 = X then
      cast
        (congrArg
          (fun Z : Γ.syms => Tuple.Index D (Γ.arity Z))
          h)
        relation.index
    else
      lookupIndexLists P relations X hX

/-
  Scan materialized relation entries for an IDB relation's
  whole-tuple membership index.
-/
def lookupMemberIndexLists
    (P : Program D Γ) :
    List (MaterializedRelation P) →
      (X : Γ.syms) → X ∈ P.idb →
        Tuple.MemberIndex D (Γ.arity X)
| [], _X, _hX => Tuple.MemberIndex.ofList []
| relation :: relations, X, hX =>
    if h : relation.sym.1 = X then
      cast
        (congrArg
          (fun Z : Γ.syms =>
            Tuple.MemberIndex D (Γ.arity Z))
          h)
        relation.memberIndex
    else
      lookupMemberIndexLists P relations X hX

/-
  Scan materialized relation entries for indexed tuples of
  an IDB symbol.
-/
def lookupIndexedTupleLists
    (P : Program D Γ) :
    List (MaterializedRelation P) →
      (X : Γ.syms) → X ∈ P.idb →
        Fin (Γ.arity X) → D →
          List (Tuple D (Γ.arity X))
| [], _X, _hX, _i, _d => []
| relation :: relations, X, hX, i, d =>
    if h : relation.sym.1 = X then
      let hAr : Γ.arity relation.sym.1 = Γ.arity X :=
        congrArg Γ.arity h
      cast
        (congrArg
          (fun Z : Γ.syms => List (Tuple D (Γ.arity Z)))
          h)
        (relation.lookupByValue (Fin.cast hAr.symm i) d)
    else
      lookupIndexedTupleLists P relations X hX i d

/- Read an IDB relation from the explicit state. -/
def lookup
    {P : Program D Γ}
    (S : MaterializedIDB P)
    (X : Γ.syms)
    (hX : X ∈ P.idb) :
    FinRelation D (Γ.arity X) :=
  lookupRelations P S.relations X hX

/- Read executable IDB tuples from the explicit state. -/
def lookupTuples
    {P : Program D Γ}
    (S : MaterializedIDB P)
    (X : Γ.syms)
    (hX : X ∈ P.idb) :
    List (Tuple D (Γ.arity X)) :=
  lookupTupleLists P S.relations X hX

/- Read an IDB relation's tuple index from the explicit state. -/
def lookupIndex
    {P : Program D Γ}
    (S : MaterializedIDB P)
    (X : Γ.syms)
    (hX : X ∈ P.idb) :
    Tuple.Index D (Γ.arity X) :=
  lookupIndexLists P S.relations X hX

/- Read an IDB relation's tuple membership index. -/
def lookupMemberIndex
    {P : Program D Γ}
    (S : MaterializedIDB P)
    (X : Γ.syms)
    (hX : X ∈ P.idb) :
    Tuple.MemberIndex D (Γ.arity X) :=
  lookupMemberIndexLists P S.relations X hX

/- Read indexed executable IDB tuples from the explicit state. -/
def lookupIndexedTuples
    {P : Program D Γ}
    (S : MaterializedIDB P)
    (X : Γ.syms)
    (hX : X ∈ P.idb)
    (i : Fin (Γ.arity X))
    (d : D) :
    List (Tuple D (Γ.arity X)) :=
  (S.lookupIndex X hX).lookup i d

/- Read whole-tuple membership for executable IDB tuples. -/
def containsTuple
    {P : Program D Γ}
    (S : MaterializedIDB P)
    (X : Γ.syms)
    (hX : X ∈ P.idb)
    (t : Tuple D (Γ.arity X)) :
    Bool :=
  (S.lookupMemberIndex X hX).contains t

theorem mem_lookupIndexLists_iff
    {P : Program D Γ} :
    ∀ (relations : List (MaterializedRelation P))
      (X : Γ.syms) (hX : X ∈ P.idb)
      (i : Fin (Γ.arity X)) (d : D)
      (t : Tuple D (Γ.arity X)),
        t ∈ (lookupIndexLists P relations X hX).lookup i d ↔
          t ∈ lookupTupleLists P relations X hX ∧
            t.get i = d
| [], X, hX, i, d, t => by
    simp [lookupIndexLists, lookupTupleLists,
      Tuple.Index.mem_lookup_iff]
| relation :: relations, X, hX, i, d, t => by
    unfold lookupIndexLists lookupTupleLists
    by_cases h : relation.sym.1 = X
    · subst h
      simpa [lookupIndexLists, lookupTupleLists] using
        relation.index_mem i d t
    · simp [h, mem_lookupIndexLists_iff
        relations X hX i d t]

theorem mem_lookupIndex_iff
    {P : Program D Γ}
    (S : MaterializedIDB P)
    (X : Γ.syms)
    (hX : X ∈ P.idb)
    (i : Fin (Γ.arity X))
    (d : D)
    (t : Tuple D (Γ.arity X)) :
    t ∈ (S.lookupIndex X hX).lookup i d ↔
      t ∈ S.lookupTuples X hX ∧ t.get i = d :=
  mem_lookupIndexLists_iff S.relations X hX i d t

theorem mem_lookupMemberIndexLists_iff
    {P : Program D Γ} :
    ∀ (relations : List (MaterializedRelation P))
      (X : Γ.syms) (hX : X ∈ P.idb)
      (t : Tuple D (Γ.arity X)),
        (lookupMemberIndexLists P relations X hX).contains t =
          true ↔
            t ∈ lookupTupleLists P relations X hX
| [], _X, _hX, t => by
    simp [lookupMemberIndexLists, lookupTupleLists,
      Tuple.MemberIndex.contains_ofList_iff]
| relation :: relations, X, hX, t => by
    unfold lookupMemberIndexLists lookupTupleLists
    by_cases h : relation.sym.1 = X
    · subst h
      simpa using relation.memberIndex_mem t
    · simp [h,
        mem_lookupMemberIndexLists_iff relations X hX t]

theorem mem_lookupMemberIndex_iff
    {P : Program D Γ}
    (S : MaterializedIDB P)
    (X : Γ.syms)
    (hX : X ∈ P.idb)
    (t : Tuple D (Γ.arity X)) :
    (S.lookupMemberIndex X hX).contains t = true ↔
      t ∈ S.lookupTuples X hX :=
  mem_lookupMemberIndexLists_iff S.relations X hX t

theorem containsTuple_iff
    {P : Program D Γ}
    (S : MaterializedIDB P)
    (X : Γ.syms)
    (hX : X ∈ P.idb)
    (t : Tuple D (Γ.arity X)) :
    S.containsTuple X hX t = true ↔
      t ∈ S.lookupTuples X hX :=
  S.mem_lookupMemberIndex_iff X hX t

theorem mem_lookupIndexedTupleLists_iff
    {P : Program D Γ} :
    ∀ (relations : List (MaterializedRelation P))
      (X : Γ.syms) (hX : X ∈ P.idb)
      (i : Fin (Γ.arity X)) (d : D)
      (t : Tuple D (Γ.arity X)),
        t ∈ lookupIndexedTupleLists P relations X hX i d ↔
          t ∈ lookupTupleLists P relations X hX ∧
            t.get i = d
| [], _X, _hX, i, d, t => by
    simp [lookupIndexedTupleLists, lookupTupleLists]
| relation :: relations, X, hX, i, d, t => by
    unfold lookupIndexedTupleLists lookupTupleLists
    by_cases h : relation.sym.1 = X
    · subst h
      simp [MaterializedRelation.mem_lookupByValue_iff]
    · simp [h,
        mem_lookupIndexedTupleLists_iff
          relations X hX i d t]

theorem mem_lookupIndexedTuples_iff
    {P : Program D Γ}
    (S : MaterializedIDB P)
    (X : Γ.syms)
    (hX : X ∈ P.idb)
    (i : Fin (Γ.arity X))
    (d : D)
    (t : Tuple D (Γ.arity X)) :
    t ∈ S.lookupIndexedTuples X hX i d ↔
      t ∈ S.lookupTuples X hX ∧ t.get i = d :=
  S.mem_lookupIndex_iff X hX i d t

theorem mem_lookupTupleLists_iff
    {P : Program D Γ} :
    ∀ (relations : List (MaterializedRelation P))
      (X : Γ.syms) (hX : X ∈ P.idb)
      (t : Tuple D (Γ.arity X)),
        t ∈ lookupTupleLists P relations X hX ↔
          t ∈ lookupRelations P relations X hX
| [], _X, _hX, t => by
    simp [lookupTupleLists, lookupRelations]
| relation :: relations, X, hX, t => by
    unfold lookupTupleLists lookupRelations
    by_cases h : relation.sym.1 = X
    · subst h
      simp [MaterializedRelation.toFinRelation,
        MaterializedRelation.finRelationOfNodupList]
    · simp [h, mem_lookupTupleLists_iff relations X hX t]

theorem nodup_lookupTupleLists
    {P : Program D Γ} :
    ∀ (relations : List (MaterializedRelation P))
      (X : Γ.syms) (hX : X ∈ P.idb),
        (lookupTupleLists P relations X hX).Nodup
| [], _X, _hX => by
    simp [lookupTupleLists]
| relation :: relations, X, hX => by
    unfold lookupTupleLists
    by_cases h : relation.sym.1 = X
    · subst h
      simpa using relation.nodup_tuples
    · simp [h, nodup_lookupTupleLists relations X hX]

theorem mem_lookupTuples_iff
    {P : Program D Γ}
    (S : MaterializedIDB P)
    (X : Γ.syms)
    (hX : X ∈ P.idb)
    (t : Tuple D (Γ.arity X)) :
    t ∈ S.lookupTuples X hX ↔ t ∈ S.lookup X hX :=
  mem_lookupTupleLists_iff S.relations X hX t

theorem lookup_eq_lookupTuples_toFinset
    {P : Program D Γ}
    (S : MaterializedIDB P)
    (X : Γ.syms)
    (hX : X ∈ P.idb) :
    S.lookup X hX = (S.lookupTuples X hX).toFinset := by
  apply Finset.ext
  intro t
  simp [List.mem_toFinset, mem_lookupTuples_iff]

theorem lookupTuples_nodup
    {P : Program D Γ}
    (S : MaterializedIDB P)
    (X : Γ.syms)
    (hX : X ∈ P.idb) :
    (S.lookupTuples X hX).Nodup :=
  nodup_lookupTupleLists S.relations X hX

/-
  IDB list membership is equivalent to IDB set membership.
-/
omit [LinearOrder D] in
theorem idbList_mem_iff_idb
    (P : Program D Γ)
    {X : Γ.syms} :
    X ∈ P.idbList ↔ X ∈ P.idb := by
  simp [Program.idbList, Program.idb]

/-
  Build materialized relation storage from a list known to
  contain IDB symbols.
-/
def relationsOfIdbFn
    {P : Program D Γ}
    (f : (X : Γ.syms) → X ∈ P.idb →
      FinRelation D (Γ.arity X)) :
    (xs : List Γ.syms) →
      (∀ X : Γ.syms, X ∈ xs → X ∈ P.idb) →
        List (MaterializedRelation P)
| [], _hAll => []
| Y :: Ys, hAll =>
    MaterializedRelation.ofFacts
      ⟨Y, hAll Y (by simp)⟩
      (f Y (hAll Y (by simp))) ::
      relationsOfIdbFn f Ys
        (fun X hX => hAll X (List.mem_cons_of_mem Y hX))

/-
  Build a complete materialized state by supplying every
  IDB relation.
-/
def ofIdbFn
    {P : Program D Γ}
    (f : (X : Γ.syms) → X ∈ P.idb →
      FinRelation D (Γ.arity X)) :
    MaterializedIDB P :=
  { relations :=
      relationsOfIdbFn f P.idbList
        (fun _X hX => P.idbList_mem_idb hX) }

/-
  Looking up a complete function-backed state recovers the
  supplied relation.
-/
theorem lookupRelations_relationsOfIdbFn
    {P : Program D Γ}
    (f : (X : Γ.syms) → X ∈ P.idb →
      FinRelation D (Γ.arity X)) :
    ∀ (xs : List Γ.syms)
      (hAll : ∀ X : Γ.syms, X ∈ xs → X ∈ P.idb)
      (X : Γ.syms) (hX : X ∈ P.idb),
        X ∈ xs →
          lookupRelations P (relationsOfIdbFn f xs hAll) X hX =
            f X hX
| [], _hAll, _X, _hX, hMem => by
    cases hMem
| Y :: Ys, hAll, X, hX, hMem => by
    unfold relationsOfIdbFn lookupRelations
    unfold MaterializedRelation.ofFacts
      MaterializedRelation.ofTupleList
    by_cases hYX : Y = X
    · subst hYX
      apply Finset.ext
      intro t
      simp [MaterializedRelation.toFinRelation,
        MaterializedRelation.finRelationOfNodupList,
        Tuple.mem_sortDedup_iff]
    · have hMemTail : X ∈ Ys := by
        exact
            (List.mem_cons.mp hMem).elim
              (fun h => False.elim (hYX h.symm))
            id
      rw [dif_neg hYX]
      exact
        lookupRelations_relationsOfIdbFn f Ys
          (fun X hX =>
            hAll X (List.mem_cons_of_mem Y hX))
          X hX hMemTail

theorem lookup_ofIdbFn
    {P : Program D Γ}
    (f : (X : Γ.syms) → X ∈ P.idb →
      FinRelation D (Γ.arity X))
    (X : Γ.syms)
    (hX : X ∈ P.idb) :
    (ofIdbFn f).lookup X hX = f X hX := by
  unfold ofIdbFn lookup
  exact
    lookupRelations_relationsOfIdbFn f P.idbList
      (fun _X hX => P.idbList_mem_idb hX)
      X hX ((idbList_mem_iff_idb P).mpr hX)

/-
  Build materialized relation storage by supplying both
  proof-facing relations and executable tuple lists.
-/
def relationsOfIdbDataFn
    {P : Program D Γ}
    (facts : (X : Γ.syms) → X ∈ P.idb →
      FinRelation D (Γ.arity X))
    (tuples : (X : Γ.syms) → X ∈ P.idb →
      List (Tuple D (Γ.arity X)))
    (hMem : ∀ (X : Γ.syms) (hX : X ∈ P.idb)
      (t : Tuple D (Γ.arity X)),
        t ∈ tuples X hX ↔ t ∈ facts X hX)
    (hNodup : ∀ (X : Γ.syms) (hX : X ∈ P.idb),
      (tuples X hX).Nodup) :
    (xs : List Γ.syms) →
      (∀ X : Γ.syms, X ∈ xs → X ∈ P.idb) →
        List (MaterializedRelation P)
| [], _hAll => []
| Y :: Ys, hAll =>
    { sym := ⟨Y, hAll Y (by simp)⟩
      tuples := tuples Y (hAll Y (by simp))
      nodup_tuples := hNodup Y (hAll Y (by simp))
      index :=
        Tuple.Index.ofList
          (tuples Y (hAll Y (by simp)))
      index_mem := by
        intro i d t
        exact
          Tuple.Index.mem_lookup_iff
            (tuples Y (hAll Y (by simp))) i d t
      memberIndex :=
        Tuple.MemberIndex.ofList
          (tuples Y (hAll Y (by simp)))
      memberIndex_mem := by
        intro t
        exact
          Tuple.MemberIndex.contains_ofList_iff
            (tuples Y (hAll Y (by simp))) t } ::
      relationsOfIdbDataFn facts tuples hMem hNodup Ys
        (fun X hX => hAll X (List.mem_cons_of_mem Y hX))

/-
  Build a complete materialized state from proof-facing
  relations and executable tuple lists.
-/
def ofIdbDataFn
    {P : Program D Γ}
    (facts : (X : Γ.syms) → X ∈ P.idb →
      FinRelation D (Γ.arity X))
    (tuples : (X : Γ.syms) → X ∈ P.idb →
      List (Tuple D (Γ.arity X)))
    (hMem : ∀ (X : Γ.syms) (hX : X ∈ P.idb)
      (t : Tuple D (Γ.arity X)),
        t ∈ tuples X hX ↔ t ∈ facts X hX)
    (hNodup : ∀ (X : Γ.syms) (hX : X ∈ P.idb),
      (tuples X hX).Nodup) :
    MaterializedIDB P :=
  { relations :=
      relationsOfIdbDataFn facts tuples hMem hNodup P.idbList
        (fun _X hX => P.idbList_mem_idb hX) }

theorem lookupRelations_relationsOfIdbDataFn
    {P : Program D Γ}
    (facts : (X : Γ.syms) → X ∈ P.idb →
      FinRelation D (Γ.arity X))
    (tuples : (X : Γ.syms) → X ∈ P.idb →
      List (Tuple D (Γ.arity X)))
    (hMem : ∀ (X : Γ.syms) (hX : X ∈ P.idb)
      (t : Tuple D (Γ.arity X)),
        t ∈ tuples X hX ↔ t ∈ facts X hX)
    (hNodup : ∀ (X : Γ.syms) (hX : X ∈ P.idb),
      (tuples X hX).Nodup) :
    ∀ (xs : List Γ.syms)
      (hAll : ∀ X : Γ.syms, X ∈ xs → X ∈ P.idb)
      (X : Γ.syms) (hX : X ∈ P.idb),
        X ∈ xs →
          lookupRelations P
              (relationsOfIdbDataFn facts tuples hMem
                hNodup xs hAll) X hX =
            facts X hX
| [], _hAll, _X, _hX, hMemX => by
    cases hMemX
| Y :: Ys, hAll, X, hX, hMemX => by
    unfold relationsOfIdbDataFn lookupRelations
    by_cases hYX : Y = X
    · subst hYX
      apply Finset.ext
      intro t
      simp [MaterializedRelation.toFinRelation,
        MaterializedRelation.finRelationOfNodupList, hMem]
    · have hMemTail : X ∈ Ys := by
        exact
          (List.mem_cons.mp hMemX).elim
            (fun h => False.elim (hYX h.symm))
            id
      simp only [hYX, ↓reduceDIte]
      exact
        lookupRelations_relationsOfIdbDataFn
          facts tuples hMem hNodup Ys
          (fun X hX =>
            hAll X (List.mem_cons_of_mem Y hX))
          X hX hMemTail

theorem lookup_ofIdbDataFn
    {P : Program D Γ}
    (facts : (X : Γ.syms) → X ∈ P.idb →
      FinRelation D (Γ.arity X))
    (tuples : (X : Γ.syms) → X ∈ P.idb →
      List (Tuple D (Γ.arity X)))
    (hMem : ∀ (X : Γ.syms) (hX : X ∈ P.idb)
      (t : Tuple D (Γ.arity X)),
        t ∈ tuples X hX ↔ t ∈ facts X hX)
    (hNodup : ∀ (X : Γ.syms) (hX : X ∈ P.idb),
      (tuples X hX).Nodup)
    (X : Γ.syms)
    (hX : X ∈ P.idb) :
    (ofIdbDataFn facts tuples hMem hNodup).lookup X hX =
      facts X hX := by
  unfold ofIdbDataFn lookup
  exact
    lookupRelations_relationsOfIdbDataFn
      facts tuples hMem hNodup P.idbList
      (fun _X hX => P.idbList_mem_idb hX)
      X hX ((idbList_mem_iff_idb P).mpr hX)

/- Build a complete materialized state from tuple lists. -/
def ofIdbTupleFn
    {P : Program D Γ}
    (tuples : (X : Γ.syms) → X ∈ P.idb →
      List (Tuple D (Γ.arity X))) :
    MaterializedIDB P :=
  ofIdbDataFn
    (fun X hX => (tuples X hX).toFinset)
    (fun X hX => Tuple.sortDedup (tuples X hX))
    (by
      intro X hX t
      simp [List.mem_toFinset, Tuple.mem_sortDedup_iff])
    (by
      intro X hX
      exact Tuple.nodup_sortDedup (tuples X hX))

theorem lookup_ofIdbTupleFn
    {P : Program D Γ}
    (tuples : (X : Γ.syms) → X ∈ P.idb →
      List (Tuple D (Γ.arity X)))
    (X : Γ.syms)
    (hX : X ∈ P.idb) :
    (ofIdbTupleFn tuples).lookup X hX =
      (tuples X hX).toFinset := by
  unfold ofIdbTupleFn
  rw [lookup_ofIdbDataFn]

/- Build a complete state from executable tuple lists. -/
def ofTupleListIdbFn
    {P : Program D Γ}
    (f : (X : Γ.syms) → X ∈ P.idb →
      List (Tuple D (Γ.arity X))) :
    MaterializedIDB P :=
  ofIdbTupleFn
    (fun X hX => Tuple.sortDedup (f X hX))

theorem lookup_ofTupleListIdbFn
    {P : Program D Γ}
    (f : (X : Γ.syms) → X ∈ P.idb →
      List (Tuple D (Γ.arity X)))
    (X : Γ.syms)
    (hX : X ∈ P.idb) :
    (ofTupleListIdbFn f).lookup X hX =
      (Tuple.sortDedup (f X hX)).toFinset := by
  unfold ofTupleListIdbFn
  rw [lookup_ofIdbTupleFn]

/-
  The initial program-schema instance copies EDB input
  relations and interprets every non-input relation as
  empty.
-/
def initialInstance
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    Instance D Γ :=
  Instance.expandEmpty P.ambient_extension_edbSchema I

/-
  Convert explicit IDB relations to an ordinary instance
  view.
-/
def toInstance
    {P : Program D Γ}
    (S : MaterializedIDB P)
    (I : Instance D P.edbSchema) :
    Instance D Γ :=
  fun X =>
    if hX : X ∈ P.idb then
      S.lookup X hX
    else
      initialInstance P I X

/- Empty explicit state for all IDB relations. -/
def empty
    (P : Program D Γ) :
    MaterializedIDB P :=
  ofIdbFn (P := P) (fun _X _hX => ∅)

end MaterializedIDB

/-
  Current IDB relations plus the previous step's fresh-fact
  relations.
-/
structure SemiNaiveState (P : Program D Γ) where
  current : MaterializedIDB P
  delta : MaterializedIDB P

namespace SemiNaiveState

/- True when every materialized delta relation is empty. -/
def deltaEmpty
    {P : Program D Γ}
    (S : SemiNaiveState P) :
  Bool :=
  P.idbSymList.all
    (fun (X : P.IDBSym) =>
      (S.delta.lookupTuples X.1 X.2).isEmpty)

/-
  Convert the current materialized IDB relations to an
  instance.
-/
def toInstance
    {P : Program D Γ}
    (S : SemiNaiveState P)
    (I : Instance D P.edbSchema) :
    Instance D Γ :=
  S.current.toInstance I

end SemiNaiveState

end Program

end Datalog

------------------------------------------------------------
-- Tuple Join Evaluation
------------------------------------------------------------

namespace Datalog

namespace Program

variable {A D : Type}
variable [RelationNames A] [Domain D] [LinearOrder D] [Hashable D]
variable {Γ : UnnamedSchema A}

/- Match a term against a concrete tuple value. -/
def matchTerm
    (ρ : PartialAssign D)
    (term : RelTerm D)
    (d : D) :
    Option (PartialAssign D) :=
  match term with
  | .var x => PartialAssign.bind ρ x d
  | .const c =>
      if c = d then
        some ρ
      else
        none

/-
  Match an atom's argument list against a concrete tuple
  list.
-/
def matchTerms :
    PartialAssign D → List (RelTerm D) → List D →
      Option (PartialAssign D)
| ρ, [], [] => some ρ
| ρ, term :: terms, d :: ds =>
    match matchTerm ρ term d with
    | none => none
    | some ρ' => matchTerms ρ' terms ds
| _ρ, _, _ => none

/-
  Extend a partial assignment using one tuple of a
  relational atom.
-/
def extendWithAtomRow
    (ρ : PartialAssign D)
    (a : RelAtom D Γ)
    (t : Tuple D (Γ.arity a.rel)) :
    Option (PartialAssign D) :=
  matchTerms ρ a.args.toList t.toList

/-
  Convert an optional value to either a singleton or empty
  finite set.
-/
def optionToFinset
    {α : Type}
    [DecidableEq α] :
    Option α → Finset α
| none => ∅
| some a => {a}

/- Does an atom mention an IDB relation? -/
def atomUsesIDB
    (P : Program D Γ) :
    Atom D Γ → Bool
| .rel a => decide (a.rel ∈ P.idb)
| .eq _ _ => false

/- Does a rule body mention any IDB relation? -/
def bodyUsesIDB
    (P : Program D Γ)
    (body : List (Atom D Γ)) :
    Bool :=
  body.any (atomUsesIDB P)

/- Body positions occupied by IDB relational atoms. -/
def idbRelAtomIndicesFrom
    (P : Program D Γ) :
    Nat → List (Atom D Γ) → List Nat
| _idx, [] => []
| idx, b :: body =>
    let rest := idbRelAtomIndicesFrom P (idx + 1) body
    match b with
    | .rel a =>
        if a.rel ∈ P.idb then
          idx :: rest
        else
          rest
    | .eq _ _ => rest

def idbRelAtomIndices
    (P : Program D Γ)
    (body : List (Atom D Γ)) :
    List Nat :=
  idbRelAtomIndicesFrom P 0 body

/- Relational body atoms paired with original body index. -/
def relBodyAtomsFrom :
    Nat → List (Atom D Γ) → List (Nat × RelAtom D Γ)
| _idx, [] => []
| idx, .rel a :: body =>
    (idx, a) :: relBodyAtomsFrom (idx + 1) body
| idx, .eq _ _ :: body =>
    relBodyAtomsFrom (idx + 1) body

def relBodyAtomEntries
    (body : List (Atom D Γ)) :
    List (Nat × RelAtom D Γ) :=
  relBodyAtomsFrom 0 body

/- Equality atoms from a rule body. -/
def equalityAtomPairs :
    List (Atom D Γ) → List (RelTerm D × RelTerm D)
| [] => []
| .rel _ :: body => equalityAtomPairs body
| .eq lhs rhs :: body => (lhs, rhs) :: equalityAtomPairs body

/-
  A finite rewrite list for equality-normalized relational
  terms. Rewrites are applied left-to-right.
-/
abbrev EqRewrite (D : Type) [Domain D] :=
  List (Var × RelTerm D)

/- Replace one variable in a function-free relational term. -/
def substRelTermVar
    (x : Var)
    (replacement : RelTerm D) :
    RelTerm D → RelTerm D
| .var y => if y = x then replacement else .var y
| .const d => .const d

/- Apply an equality rewrite list to a term. -/
def rewriteRelTerm :
    EqRewrite D → RelTerm D → RelTerm D
| [], term => term
| (x, replacement) :: rw, term =>
    rewriteRelTerm rw (substRelTermVar x replacement term)

/- Apply an equality rewrite list to a relational atom. -/
def rewriteRelAtom
    (rw : EqRewrite D)
    (a : RelAtom D Γ) :
    RelAtom D Γ where
  rel := a.rel
  args := Vector.ofFn
    (fun i => rewriteRelTerm rw (a.args.get i))

/- Apply an equality rewrite list to an indexed body atom. -/
def rewriteRelEntry
    (rw : EqRewrite D)
    (entry : Nat × RelAtom D Γ) :
    Nat × RelAtom D Γ :=
  (entry.1, rewriteRelAtom rw entry.2)

/- Apply an equality rewrite list to indexed body atoms. -/
def rewriteRelEntries
    (rw : EqRewrite D)
    (entries : List (Nat × RelAtom D Γ)) :
    List (Nat × RelAtom D Γ) :=
  entries.map (rewriteRelEntry rw)

/- Add one normalized equality to a rewrite list. -/
def addEqualityRewrite
    (rw : EqRewrite D)
    (lhs rhs : RelTerm D) :
    Option (EqRewrite D) :=
  match rewriteRelTerm rw lhs, rewriteRelTerm rw rhs with
  | .const d₁, .const d₂ =>
      if d₁ = d₂ then some rw else none
  | .var x, .const d =>
      some (rw ++ [(x, .const d)])
  | .const d, .var x =>
      some (rw ++ [(x, .const d)])
  | .var x, .var y =>
      if x = y then
        some rw
      else if x < y then
        some (rw ++ [(y, .var x)])
      else
        some (rw ++ [(x, .var y)])

/- Build a rewrite list from body equality atoms. -/
def equalityRewriteFrom :
    EqRewrite D → List (Atom D Γ) → Option (EqRewrite D)
| rw, [] => some rw
| rw, .rel _ :: body => equalityRewriteFrom rw body
| rw, .eq lhs rhs :: body =>
    match addEqualityRewrite rw lhs rhs with
    | none => none
    | some rw' => equalityRewriteFrom rw' body

/- Build the equality rewrite list for a rule body. -/
def equalityRewrite
    (body : List (Atom D Γ)) :
    Option (EqRewrite D) :=
  equalityRewriteFrom [] body

/- Normalize a rule head using body equalities. -/
def normalizedHeadFor
    (r : Rule D Γ) :
    RelAtom D Γ :=
  match equalityRewrite r.body with
  | none => r.head
  | some rw => rewriteRelAtom rw r.head

/- Normalize relational body atoms using body equalities. -/
def normalizedRelBodyAtomsFor
    (body : List (Atom D Γ)) :
    List (Nat × RelAtom D Γ) :=
  match equalityRewrite body with
  | none => []
  | some rw => rewriteRelEntries rw (relBodyAtomEntries body)

/- Whether equality normalization found an impossible rule body. -/
def normalizedImpossibleFor
    (body : List (Atom D Γ)) :
    Bool :=
  match equalityRewrite body with
  | none => true
  | some _ => false

/- A normalized head keeps the source head relation symbol. -/
omit [LinearOrder D] in
theorem normalizedHeadFor_rel_eq
    (r : Rule D Γ) :
    (normalizedHeadFor r).rel = r.head.rel := by
  unfold normalizedHeadFor
  cases equalityRewrite r.body with
  | none => rfl
  | some rw =>
      simp [rewriteRelAtom]

/- Assignment induced by an equality rewrite list. -/
def normalizedAssign
    (rw : EqRewrite D)
    (σ : Assign D) :
    Assign D :=
  fun x => (rewriteRelTerm rw (.var x)).eval σ

omit [LinearOrder D] in
theorem rewriteRelTerm_const
    (rw : EqRewrite D)
    (d : D) :
    rewriteRelTerm rw (.const d) = .const d := by
  induction rw with
  | nil => rfl
  | cons pair rw ih =>
      cases pair with
      | mk x replacement =>
          simp [rewriteRelTerm, substRelTermVar, ih]

omit [LinearOrder D] in
theorem rewriteRelTerm_eval_normalizedAssign
    (rw : EqRewrite D)
    (term : RelTerm D)
    (σ : Assign D) :
    (rewriteRelTerm rw term).eval σ =
      term.eval (normalizedAssign rw σ) := by
  cases term with
  | var x =>
      simp [normalizedAssign, RelTerm.eval]
  | const d =>
      simp [rewriteRelTerm_const, RelTerm.eval]

omit [LinearOrder D] in
theorem rewriteRelAtom_evalTuple_normalizedAssign
    (rw : EqRewrite D)
    (a : RelAtom D Γ)
    (σ : Assign D) :
    (rewriteRelAtom rw a).evalTuple σ =
      a.evalTuple (normalizedAssign rw σ) := by
  apply Vector.ext
  intro i hi
  let j : Fin (Γ.arity a.rel) := ⟨i, hi⟩
  change
    ((rewriteRelAtom rw a).evalTuple σ).get j =
      (a.evalTuple (normalizedAssign rw σ)).get j
  simp [rewriteRelAtom, RelAtom.evalTuple,
    RelTerm.evalVector, Vector.get,
    rewriteRelTerm_eval_normalizedAssign]

omit [LinearOrder D] in
theorem cast_evalTuple_eq_of_atom_eq
    {a b : RelAtom D Γ}
    (h : a = b)
    (hRel : a.rel = b.rel)
    (σ : Assign D) :
    cast
        (congrArg
          (fun X : Γ.syms => Tuple D (Γ.arity X))
          hRel)
        (a.evalTuple σ) =
      b.evalTuple σ := by
  cases h
  change
    Tuple.castArity
        (congrArg Γ.arity hRel).symm
        (a.evalTuple σ) =
      a.evalTuple σ
  rw [Tuple.castArity_proof_irrel
    (congrArg Γ.arity hRel).symm rfl]
  rfl

/- A total assignment respects every binding in a rewrite list. -/
def RewriteRespects
    (rw : EqRewrite D)
    (σ : Assign D) :
    Prop :=
  ∀ (x : Var) (term : RelTerm D),
    (x, term) ∈ rw → σ x = term.eval σ

omit [LinearOrder D] in
theorem RewriteRespects.nil
    (σ : Assign D) :
    RewriteRespects ([] : EqRewrite D) σ := by
  intro x term h
  simp at h

omit [LinearOrder D] in
theorem RewriteRespects.tail
    {rw : EqRewrite D}
    {σ : Assign D}
    {x : Var}
    {term : RelTerm D}
    (h : RewriteRespects ((x, term) :: rw) σ) :
    RewriteRespects rw σ := by
  intro y s hs
  exact h y s (List.mem_cons.mpr (Or.inr hs))

omit [LinearOrder D] in
theorem eval_substRelTermVar_of_eq
    {σ : Assign D}
    {x : Var}
    {replacement : RelTerm D}
    (hσ : σ x = replacement.eval σ)
    (term : RelTerm D) :
    (substRelTermVar x replacement term).eval σ =
      term.eval σ := by
  cases term with
  | var y =>
      by_cases hyx : y = x
      · subst hyx
        simp [substRelTermVar, RelTerm.eval, hσ]
      · simp [substRelTermVar, RelTerm.eval, hyx]
  | const d =>
      simp [substRelTermVar, RelTerm.eval]

omit [LinearOrder D] in
theorem rewriteRelTerm_eval_of_respects
    {rw : EqRewrite D}
    {σ : Assign D}
    (hRespect : RewriteRespects rw σ)
    (term : RelTerm D) :
    (rewriteRelTerm rw term).eval σ = term.eval σ := by
  induction rw generalizing term with
  | nil =>
      simp [rewriteRelTerm]
  | cons pair rw ih =>
      cases pair with
      | mk x replacement =>
          have hHead :
              σ x = replacement.eval σ :=
            hRespect x replacement (by simp)
          have hTail :
              RewriteRespects rw σ :=
            RewriteRespects.tail hRespect
          calc
            (rewriteRelTerm ((x, replacement) :: rw) term).eval σ =
                (rewriteRelTerm rw
                  (substRelTermVar x replacement term)).eval σ := by
              rfl
            _ = (substRelTermVar x replacement term).eval σ := by
              exact ih hTail (substRelTermVar x replacement term)
            _ = term.eval σ := by
              exact eval_substRelTermVar_of_eq hHead term

omit [LinearOrder D] in
theorem rewriteRelAtom_evalTuple_of_respects
    {rw : EqRewrite D}
    {σ : Assign D}
    (hRespect : RewriteRespects rw σ)
    (a : RelAtom D Γ) :
    (rewriteRelAtom rw a).evalTuple σ =
      a.evalTuple σ := by
  apply Vector.ext
  intro i hi
  let j : Fin (Γ.arity a.rel) := ⟨i, hi⟩
  change
    ((rewriteRelAtom rw a).evalTuple σ).get j =
      (a.evalTuple σ).get j
  simp [rewriteRelAtom, RelAtom.evalTuple,
    RelTerm.evalVector, Vector.get,
    rewriteRelTerm_eval_of_respects hRespect]

/- Variables occurring in relational body entries. -/
def relEntryVarList
    (entries : List (Nat × RelAtom D Γ)) :
    List Var :=
  entries.flatMap (fun entry => entry.2.varList)

omit [LinearOrder D] in
theorem SlotEnv.compileRelEntries_wf
    (env : SlotEnv) :
    ∀ (entries : List (Nat × RelAtom D Γ)),
      (∀ x : Var,
        x ∈ relEntryVarList (D := D) entries →
          x ∈ env.vars) →
        ∀ entry : Nat × SlotRelAtom D Γ,
          entry ∈ env.compileRelEntries entries →
            entry.2.WF env
| [], _hMem, entry, hEntry => by
    simp [SlotEnv.compileRelEntries] at hEntry
| (idx, a) :: entries, hMem, entry, hEntry => by
    unfold SlotEnv.compileRelEntries at hEntry
    rcases List.mem_cons.mp hEntry with hHead | hTail
    · subst hHead
      exact
        SlotEnv.compileRelAtom_wf env a
          (by
            intro x hx
            apply hMem
            simp [relEntryVarList, hx])
    · exact
        SlotEnv.compileRelEntries_wf env entries
          (by
            intro x hx
            apply hMem
            unfold relEntryVarList at hx ⊢
            rw [List.mem_flatMap] at hx ⊢
            rcases hx with ⟨entry, hEntry, hxEntry⟩
            exact ⟨entry, by simp [hEntry], hxEntry⟩)
          entry hTail

/- A term has a known value from constants or bound variables. -/
def termBoundByVars
    (boundVars : List Var) :
    RelTerm D → Bool
| .const _ => true
| .var x => decide (x ∈ boundVars)

/- Count atom columns whose values are already known. -/
def boundColumnCount
    (boundVars : List Var) :
    List (RelTerm D) → Nat
| [] => 0
| term :: terms =>
    (if termBoundByVars (D := D) boundVars term then 1 else 0) +
      boundColumnCount boundVars terms

/- Count known columns for a relational atom. -/
def relAtomBoundColumnCount
    (boundVars : List Var)
    (a : RelAtom D Γ) :
    Nat :=
  boundColumnCount (D := D) boundVars a.args.toList

/- Add a variable to a binding-pattern list if absent. -/
def addBoundVar
    (boundVars : List Var)
    (x : Var) :
    List Var :=
  if x ∈ boundVars then
    boundVars
  else
    x :: boundVars

/- Add all variables from an atom to a binding-pattern list. -/
def addRelAtomBoundVars
    (boundVars : List Var)
    (a : RelAtom D Γ) :
    List Var :=
  a.varList.foldl addBoundVar boundVars

/- Relation symbols from relational atoms in a body. -/
def bodyRelSymbolList :
    List (Atom D Γ) → List Γ.syms
| [] => []
| .rel a :: body => a.rel :: bodyRelSymbolList body
| .eq _ _ :: body => bodyRelSymbolList body

/- A rule with body metadata precomputed for execution. -/
structure CompiledRule (P : Program D Γ) where
  source : Rule D Γ
  bodyAtoms : List (Atom D Γ)
  bodyAtoms_eq : bodyAtoms = source.body
  idbBodyPositions : List Nat
  idbBodyPositions_eq :
    idbBodyPositions = idbRelAtomIndices P source.body
  relBodyAtoms : List (Nat × RelAtom D Γ)
  relBodyAtoms_eq :
    relBodyAtoms = relBodyAtomEntries source.body
  equalityAtoms : List (RelTerm D × RelTerm D)
  equalityAtoms_eq :
    equalityAtoms = equalityAtomPairs source.body
  normalizedHead : RelAtom D Γ
  normalizedHead_eq :
    normalizedHead = normalizedHeadFor source
  normalizedHead_rel_eq :
    normalizedHead.rel = source.head.rel
  normalizedRelBodyAtoms : List (Nat × RelAtom D Γ)
  normalizedRelBodyAtoms_eq :
    normalizedRelBodyAtoms =
      normalizedRelBodyAtomsFor source.body
  normalizedImpossible : Bool
  normalizedImpossible_eq :
    normalizedImpossible = normalizedImpossibleFor source.body
  slotEnv : SlotEnv
  slotEnv_vars_cover :
    ∀ x : Var,
      x ∈ normalizedHead.varList ++
          relEntryVarList (D := D) normalizedRelBodyAtoms →
        x ∈ slotEnv.vars
  slotHead : SlotRelAtom D Γ
  slotHead_source_eq :
    slotHead.source = normalizedHead
  slotHead_rel_eq :
    slotHead.source.rel = source.head.rel
  slotRelBodyAtoms : List (Nat × SlotRelAtom D Γ)
  slotRelBodyAtoms_eq :
    slotRelBodyAtoms =
      slotEnv.compileRelEntries normalizedRelBodyAtoms
  slotEnv_wellFormed : slotEnv.WellFormed
  slotHead_wf : slotHead.WF slotEnv
  slotRelBodyAtoms_wf :
    ∀ entry : Nat × SlotRelAtom D Γ,
      entry ∈ slotRelBodyAtoms →
        entry.2.WF slotEnv
  headVars : List Var
  headVars_eq : headVars = source.head.varList

namespace CompiledRule

/- Compile the rule-local metadata that does not change during iteration. -/
def ofRule
    (P : Program D Γ)
    (r : Rule D Γ) :
    CompiledRule P :=
  let normalizedHead := normalizedHeadFor r
  let normalizedRelBodyAtoms := normalizedRelBodyAtomsFor r.body
  let slotEnv :=
    SlotEnv.ofVars
      (normalizedHead.varList ++
        relEntryVarList (D := D) normalizedRelBodyAtoms)
  { source := r
    bodyAtoms := r.body
    bodyAtoms_eq := rfl
    idbBodyPositions := idbRelAtomIndices P r.body
    idbBodyPositions_eq := rfl
    relBodyAtoms := relBodyAtomEntries r.body
    relBodyAtoms_eq := rfl
    equalityAtoms := equalityAtomPairs r.body
    equalityAtoms_eq := rfl
    normalizedHead := normalizedHead
    normalizedHead_eq := rfl
    normalizedHead_rel_eq := normalizedHeadFor_rel_eq r
    normalizedRelBodyAtoms := normalizedRelBodyAtoms
    normalizedRelBodyAtoms_eq := rfl
    normalizedImpossible := normalizedImpossibleFor r.body
    normalizedImpossible_eq := rfl
    slotEnv := slotEnv
    slotEnv_vars_cover := by
      intro x hx
      exact SlotEnv.mem_vars_ofVars_of_mem hx
    slotHead := slotEnv.compileRelAtom normalizedHead
    slotHead_source_eq := rfl
    slotHead_rel_eq := normalizedHeadFor_rel_eq r
    slotRelBodyAtoms :=
      slotEnv.compileRelEntries normalizedRelBodyAtoms
    slotRelBodyAtoms_eq := rfl
    slotEnv_wellFormed := SlotEnv.ofVars_wellFormed _
    slotHead_wf := by
      apply SlotEnv.compileRelAtom_wf
      intro x hx
      apply SlotEnv.mem_vars_ofVars_of_mem
      simp [hx]
    slotRelBodyAtoms_wf := by
      intro entry hEntry
      exact
        SlotEnv.compileRelEntries_wf slotEnv
          normalizedRelBodyAtoms
          (by
            intro x hx
            apply SlotEnv.mem_vars_ofVars_of_mem
            simp [hx])
          entry hEntry
    headVars := r.head.varList
    headVars_eq := rfl }

end CompiledRule

/- Program rules grouped by head relation for execution. -/
structure CompiledProgram (P : Program D Γ) where
  rulesForHead : Γ.syms → List (CompiledRule P)
  rulesForHead_sources :
    ∀ X : Γ.syms,
      (rulesForHead X).map (fun r => r.source) =
        P.rules.filter (fun r => decide (r.head.rel = X))

namespace CompiledProgram

/- Compile the program once into per-head rule groups. -/
def ofProgram
    (P : Program D Γ) :
    CompiledProgram P :=
  { rulesForHead :=
      fun X =>
        (P.rules.filter
          (fun r => decide (r.head.rel = X))).map
            (CompiledRule.ofRule P)
    rulesForHead_sources := by
      intro X
      rw [List.map_map]
      change
        List.map id
            (P.rules.filter
              (fun r => decide (r.head.rel = X))) =
          P.rules.filter (fun r => decide (r.head.rel = X))
      simp }

end CompiledProgram

/- Compile a program for semi-naive execution. -/
def compile
    (P : Program D Γ) :
    CompiledProgram P :=
  CompiledProgram.ofProgram P

/- Compile a program for the optimized semi-naive pipeline. -/
def compileForSN
    (P : Program D Γ) :
    CompiledProgram P :=
  P.compile

/- Relation symbols appearing in program bodies. -/
def bodyRelSymbols
    (P : Program D Γ) :
    List Γ.syms :=
  (P.rules.map (fun r => bodyRelSymbolList r.body)).flatten

/- Non-IDB body relation symbols worth indexing from the input. -/
def inputRelSymbols
    (P : Program D Γ) :
    List Γ.syms :=
  (P.bodyRelSymbols.filter
    (fun X => decide (X ∉ P.idb))).eraseDups

/- One indexed non-IDB input relation. -/
structure IndexedInputRelation
    (P : Program D Γ)
    (I : Instance D P.edbSchema) where
  sym : Γ.syms
  tuples : List (Tuple D (Γ.arity sym))
  index : Tuple.Index D (Γ.arity sym)
  memberIndex : Tuple.MemberIndex D (Γ.arity sym)
  tuples_mem :
    ∀ t : Tuple D (Γ.arity sym),
      t ∈ tuples ↔ t ∈ MaterializedIDB.initialInstance P I sym
  index_mem :
    ∀ (i : Fin (Γ.arity sym)) (d : D)
      (t : Tuple D (Γ.arity sym)),
      t ∈ index.lookup i d ↔ t ∈ tuples ∧ t.get i = d
  memberIndex_mem :
    ∀ t : Tuple D (Γ.arity sym),
      memberIndex.contains t = true ↔ t ∈ tuples

namespace IndexedInputRelation

/- Build an indexed input relation from the initial instance view. -/
def ofSymbol
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (X : Γ.syms) :
    IndexedInputRelation P I :=
  let ts := (MaterializedIDB.initialInstance P I X).sort
  { sym := X
    tuples := ts
    index := Tuple.Index.ofList ts
    memberIndex := Tuple.MemberIndex.ofList ts
    tuples_mem := by
      intro t
      simp [ts, Finset.mem_sort]
    index_mem := by
      intro i d t
      exact Tuple.Index.mem_lookup_iff ts i d t
    memberIndex_mem := by
      intro t
      exact Tuple.MemberIndex.contains_ofList_iff ts t }

/- Indexed lookup in one input relation. -/
def lookupByValue
    {P : Program D Γ}
    {I : Instance D P.edbSchema}
    (R : IndexedInputRelation P I)
    (i : Fin (Γ.arity R.sym))
    (d : D) :
    List (Tuple D (Γ.arity R.sym)) :=
  R.index.lookup i d

/- Whole-tuple membership lookup in one input relation. -/
def contains
    {P : Program D Γ}
    {I : Instance D P.edbSchema}
    (R : IndexedInputRelation P I)
    (t : Tuple D (Γ.arity R.sym)) :
    Bool :=
  R.memberIndex.contains t

theorem mem_lookupByValue_iff
    {P : Program D Γ}
    {I : Instance D P.edbSchema}
    (R : IndexedInputRelation P I)
    (i : Fin (Γ.arity R.sym))
    (d : D)
    (t : Tuple D (Γ.arity R.sym)) :
    t ∈ R.lookupByValue i d ↔
      t ∈ R.tuples ∧ t.get i = d :=
  R.index_mem i d t

theorem contains_iff
    {P : Program D Γ}
    {I : Instance D P.edbSchema}
    (R : IndexedInputRelation P I)
    (t : Tuple D (Γ.arity R.sym)) :
    R.contains t = true ↔ t ∈ R.tuples :=
  R.memberIndex_mem t

end IndexedInputRelation

/- Indexed input relations used by a compiled run. -/
structure IndexedInput
    (P : Program D Γ)
    (I : Instance D P.edbSchema) where
  relations : List (IndexedInputRelation P I)

namespace IndexedInput

/- Build the input cache for non-IDB body relations. -/
def ofInput
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    IndexedInput P I where
  relations :=
    P.inputRelSymbols.map
      (fun X => IndexedInputRelation.ofSymbol P I X)

/- Lookup cached input tuples, with a safe fallback. -/
def lookupTupleLists
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    List (IndexedInputRelation P I) →
      (X : Γ.syms) → List (Tuple D (Γ.arity X))
| [], X => (MaterializedIDB.initialInstance P I X).sort
| relation :: relations, X =>
    if h : relation.sym = X then
      cast
        (congrArg
          (fun Y : Γ.syms => List (Tuple D (Γ.arity Y)))
          h)
        relation.tuples
    else
      lookupTupleLists P I relations X

/- Lookup cached input tuples by column value. -/
def lookupIndexedTupleLists
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    List (IndexedInputRelation P I) →
      (X : Γ.syms) → Fin (Γ.arity X) → D →
        List (Tuple D (Γ.arity X))
| [], X, i, d =>
    ((MaterializedIDB.initialInstance P I X).sort).filter
      (fun t => decide (t.get i = d))
| relation :: relations, X, i, d =>
    if h : relation.sym = X then
      let hAr : Γ.arity relation.sym = Γ.arity X :=
        congrArg Γ.arity h
      cast
        (congrArg
          (fun Y : Γ.syms => List (Tuple D (Γ.arity Y)))
          h)
        (relation.lookupByValue (Fin.cast hAr.symm i) d)
    else
      lookupIndexedTupleLists P I relations X i d

/- Lookup cached input whole-tuple membership. -/
def lookupContainsTupleLists
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    List (IndexedInputRelation P I) →
      (X : Γ.syms) → Tuple D (Γ.arity X) → Bool
| [], X, t =>
    decide (t ∈ MaterializedIDB.initialInstance P I X)
| relation :: relations, X, t =>
    if h : relation.sym = X then
      let hAr : Γ.arity relation.sym = Γ.arity X :=
        congrArg Γ.arity h
      relation.contains (Tuple.castArity hAr t)
    else
      lookupContainsTupleLists P I relations X t

/- Read cached input tuples. -/
def lookupTuples
    {P : Program D Γ}
    {I : Instance D P.edbSchema}
    (C : IndexedInput P I)
    (X : Γ.syms) :
    List (Tuple D (Γ.arity X)) :=
  lookupTupleLists P I C.relations X

/- Read cached input tuples by column value. -/
def lookupIndexedTuples
    {P : Program D Γ}
    {I : Instance D P.edbSchema}
    (C : IndexedInput P I)
    (X : Γ.syms)
    (i : Fin (Γ.arity X))
    (d : D) :
    List (Tuple D (Γ.arity X)) :=
  lookupIndexedTupleLists P I C.relations X i d

/- Read cached input whole-tuple membership. -/
def containsTuple
    {P : Program D Γ}
    {I : Instance D P.edbSchema}
    (C : IndexedInput P I)
    (X : Γ.syms)
    (t : Tuple D (Γ.arity X)) :
    Bool :=
  lookupContainsTupleLists P I C.relations X t

theorem mem_lookupIndexedTupleLists_iff
    {P : Program D Γ}
    (I : Instance D P.edbSchema) :
    ∀ (relations : List (IndexedInputRelation P I))
      (X : Γ.syms) (i : Fin (Γ.arity X)) (d : D)
      (t : Tuple D (Γ.arity X)),
        t ∈ lookupIndexedTupleLists P I relations X i d ↔
          t ∈ lookupTupleLists P I relations X ∧
            t.get i = d
| [], X, i, d, t => by
    simp [lookupIndexedTupleLists, lookupTupleLists,
      List.mem_filter]
| relation :: relations, X, i, d, t => by
    unfold lookupIndexedTupleLists lookupTupleLists
    by_cases h : relation.sym = X
    · subst h
      simp [IndexedInputRelation.mem_lookupByValue_iff]
    · simp [h, mem_lookupIndexedTupleLists_iff I
        relations X i d t]

theorem mem_lookupTupleLists_iff
    {P : Program D Γ}
    (I : Instance D P.edbSchema) :
    ∀ (relations : List (IndexedInputRelation P I))
      (X : Γ.syms) (t : Tuple D (Γ.arity X)),
        t ∈ lookupTupleLists P I relations X ↔
          t ∈ MaterializedIDB.initialInstance P I X
| [], X, t => by
    simp [lookupTupleLists, Finset.mem_sort]
| relation :: relations, X, t => by
    unfold lookupTupleLists
    by_cases h : relation.sym = X
    · subst h
      simp [IndexedInputRelation.tuples_mem]
    · simp [h, mem_lookupTupleLists_iff I relations X t]

theorem mem_lookupContainsTupleLists_iff
    {P : Program D Γ}
    (I : Instance D P.edbSchema) :
    ∀ (relations : List (IndexedInputRelation P I))
      (X : Γ.syms) (t : Tuple D (Γ.arity X)),
        lookupContainsTupleLists P I relations X t = true ↔
          t ∈ lookupTupleLists P I relations X
| [], X, t => by
    simp [lookupContainsTupleLists, lookupTupleLists,
      Finset.mem_sort]
| relation :: relations, X, t => by
    unfold lookupContainsTupleLists lookupTupleLists
    by_cases h : relation.sym = X
    · subst h
      simp [IndexedInputRelation.contains_iff]
    · simp [h, mem_lookupContainsTupleLists_iff I
        relations X t]

theorem mem_lookupTuples_iff
    {P : Program D Γ}
    {I : Instance D P.edbSchema}
    (C : IndexedInput P I)
    (X : Γ.syms)
    (t : Tuple D (Γ.arity X)) :
    t ∈ C.lookupTuples X ↔
      t ∈ MaterializedIDB.initialInstance P I X :=
  mem_lookupTupleLists_iff I C.relations X t

theorem containsTuple_iff
    {P : Program D Γ}
    {I : Instance D P.edbSchema}
    (C : IndexedInput P I)
    (X : Γ.syms)
    (t : Tuple D (Γ.arity X)) :
    C.containsTuple X t = true ↔ t ∈ C.lookupTuples X :=
  mem_lookupContainsTupleLists_iff I C.relations X t

theorem mem_lookupIndexedTuples_iff
    {P : Program D Γ}
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (X : Γ.syms)
    (i : Fin (Γ.arity X))
    (d : D)
    (t : Tuple D (Γ.arity X)) :
    t ∈ C.lookupIndexedTuples X i d ↔
      t ∈ C.lookupTuples X ∧ t.get i = d :=
  mem_lookupIndexedTupleLists_iff I C.relations X i d t

end IndexedInput

/- Materialized EDB input used by one semi-naive run. -/
abbrev MaterializedInput
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :=
  IndexedInput P I

/- Build the materialized EDB input for one semi-naive run. -/
def materializeInput
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    MaterializedInput P I :=
  IndexedInput.ofInput P I

/-
  Relation tuples used for an atom in one semi-naive
  variant.
-/
def atomRelationFor
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (idx : Nat)
    (a : RelAtom D Γ) :
    FinRelation D (Γ.arity a.rel) :=
  if deltaAt? = some idx then
    if hIDB : a.rel ∈ P.idb then
      S.delta.lookup a.rel hIDB
    else
      ∅
    else
      if hIDB : a.rel ∈ P.idb then
        S.current.lookup a.rel hIDB
      else
        MaterializedIDB.initialInstance P I a.rel

set_option linter.flexible false in
theorem atomRelationFor_rewriteRelAtom
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (idx : Nat)
    (rw : EqRewrite D)
    (a : RelAtom D Γ) :
    P.atomRelationFor I S deltaAt? idx
        (rewriteRelAtom rw a) =
      P.atomRelationFor I S deltaAt? idx a := by
  apply Finset.ext
  intro t
  unfold atomRelationFor
  simp [rewriteRelAtom]
  by_cases hDelta : deltaAt? = some idx
  · by_cases hIDB : a.rel ∈ P.idb
    · simp [hDelta, hIDB]
    · simp [hDelta, hIDB]
      try exact Iff.rfl
  · by_cases hIDB : a.rel ∈ P.idb
    · simp [hDelta, hIDB]
    · simp [hDelta, hIDB]
      try exact Iff.rfl

/-
  Executable tuple list used for an atom in one semi-naive
  variant.
-/
def atomTuplesFor
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (idx : Nat)
    (a : RelAtom D Γ) :
    List (Tuple D (Γ.arity a.rel)) :=
  if deltaAt? = some idx then
    if hIDB : a.rel ∈ P.idb then
      S.delta.lookupTuples a.rel hIDB
    else
      []
  else
    if hIDB : a.rel ∈ P.idb then
      S.current.lookupTuples a.rel hIDB
    else
      (MaterializedIDB.initialInstance P I a.rel).sort

theorem mem_atomTuplesFor_iff
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (idx : Nat)
    (a : RelAtom D Γ)
    (t : Tuple D (Γ.arity a.rel)) :
    t ∈ P.atomTuplesFor I S deltaAt? idx a ↔
      t ∈ P.atomRelationFor I S deltaAt? idx a := by
  unfold atomTuplesFor atomRelationFor
  by_cases hDelta : deltaAt? = some idx
  · simp [hDelta]
    by_cases hIDB : a.rel ∈ P.idb
    · simp [hIDB, MaterializedIDB.mem_lookupTuples_iff]
    · simp [hIDB]
  · simp [hDelta]
    by_cases hIDB : a.rel ∈ P.idb
    · simp [hIDB, MaterializedIDB.mem_lookupTuples_iff]
    · simp [hIDB, Finset.mem_sort]

/- Cached tuple-source length for planning one atom. -/
def atomTupleCountFor
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (idx : Nat)
    (a : RelAtom D Γ) :
    Nat :=
  if deltaAt? = some idx then
    if hIDB : a.rel ∈ P.idb then
      (S.delta.lookupTuples a.rel hIDB).length
    else
      0
  else
    if hIDB : a.rel ∈ P.idb then
      (S.current.lookupTuples a.rel hIDB).length
    else
      (C.lookupTuples a.rel).length

/- Whether an entry is the selected delta atom. -/
def relEntryUsesSelectedDelta
    (deltaAt? : Option Nat)
    (entry : Nat × RelAtom D Γ) :
    Bool :=
  decide (deltaAt? = some entry.1)

/- Greedy comparison for selecting the next join atom. -/
def relEntryBetter
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (boundVars : List Var)
    (entry best : Nat × RelAtom D Γ) :
    Bool :=
  let entryBound :=
    relAtomBoundColumnCount (D := D) boundVars entry.2
  let bestBound :=
    relAtomBoundColumnCount (D := D) boundVars best.2
  if bestBound < entryBound then
    true
  else if entryBound < bestBound then
    false
  else
    let entryDelta :=
      relEntryUsesSelectedDelta (D := D) deltaAt? entry
    let bestDelta :=
      relEntryUsesSelectedDelta (D := D) deltaAt? best
    if entryDelta && !bestDelta then
      true
    else if bestDelta && !entryDelta then
      false
    else
      atomTupleCountFor P I C S deltaAt? entry.1 entry.2 <
        atomTupleCountFor P I C S deltaAt? best.1 best.2

/- Select the first best element, returning the rest. -/
def selectBestRelEntry
    (better :
      (Nat × RelAtom D Γ) → (Nat × RelAtom D Γ) → Bool) :
    List (Nat × RelAtom D Γ) →
      Option ((Nat × RelAtom D Γ) ×
        List (Nat × RelAtom D Γ))
| [] => none
| entry :: entries =>
    match selectBestRelEntry better entries with
    | none => some (entry, [])
    | some (best, rest) =>
        if better best entry then
          some (best, entry :: rest)
        else
          some (entry, best :: rest)

/- Greedily plan a join order with a fuel bound. -/
def planRelEntriesWithFuel
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat) :
    Nat → List Var → List (Nat × RelAtom D Γ) →
      List (Nat × RelAtom D Γ)
| 0, _boundVars, entries => entries
| _fuel + 1, boundVars, entries =>
    match
        selectBestRelEntry
          (relEntryBetter P I C S deltaAt? boundVars)
          entries with
    | none => entries
    | some (entry, rest) =>
        entry ::
          planRelEntriesWithFuel P I C S deltaAt? _fuel
            (addRelAtomBoundVars boundVars entry.2) rest

/- Planned relational body order for indexed execution. -/
def plannedRelBodyAtoms
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (entries : List (Nat × RelAtom D Γ)) :
    List (Nat × RelAtom D Γ) :=
  planRelEntriesWithFuel P I C S deltaAt?
    entries.length [] entries

omit [LinearOrder D] in
theorem selectBestRelEntry_perm
    (better :
      (Nat × RelAtom D Γ) → (Nat × RelAtom D Γ) → Bool) :
    ∀ {entries : List (Nat × RelAtom D Γ)}
      {best : Nat × RelAtom D Γ}
      {rest : List (Nat × RelAtom D Γ)},
      selectBestRelEntry better entries = some (best, rest) →
        List.Perm (best :: rest) entries
| [], _best, _rest, h => by
    simp [selectBestRelEntry] at h
| entry :: entries, best, rest, h => by
    unfold selectBestRelEntry at h
    cases hSelect :
        selectBestRelEntry better entries with
    | none =>
        cases entries with
        | nil =>
            have hPair : entry = best ∧ rest = [] := by
              simpa [hSelect] using h
            rcases hPair with ⟨hBest, hRest⟩
            subst best
            subst rest
            rfl
        | cons entry' entries' =>
            cases hSelect' :
                selectBestRelEntry better entries' with
            | none =>
                simp [selectBestRelEntry, hSelect'] at hSelect
            | some selected' =>
                rcases selected' with ⟨best', rest'⟩
                by_cases hBetter' : better best' entry' = true
                · simp [selectBestRelEntry, hSelect',
                    hBetter'] at hSelect
                · simp [selectBestRelEntry, hSelect',
                    hBetter'] at hSelect
    | some selected =>
        rcases selected with ⟨tailBest, tailRest⟩
        have hTail :
            List.Perm (tailBest :: tailRest) entries :=
          selectBestRelEntry_perm better hSelect
        by_cases hBetter : better tailBest entry = true
        · have hPair :
              tailBest = best ∧ entry :: tailRest = rest := by
            simpa [hSelect, hBetter] using h
          rcases hPair with ⟨hBest, hRest⟩
          subst best
          subst rest
          exact (List.Perm.swap tailBest entry tailRest).symm.trans
            (hTail.cons entry)
        · have hPair :
              entry = best ∧ tailBest :: tailRest = rest := by
            simpa [hSelect, hBetter] using h
          rcases hPair with ⟨hBest, hRest⟩
          subst best
          subst rest
          exact hTail.cons entry

theorem planRelEntriesWithFuel_perm
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat) :
    ∀ (fuel : Nat) (boundVars : List Var)
      (entries : List (Nat × RelAtom D Γ)),
      entries.length ≤ fuel →
        List.Perm
          (planRelEntriesWithFuel P I C S deltaAt?
            fuel boundVars entries)
          entries
| 0, _boundVars, entries, _hFuel => by
    simp [planRelEntriesWithFuel]
| fuel + 1, boundVars, entries, hFuel => by
    unfold planRelEntriesWithFuel
    cases hSelect :
        selectBestRelEntry
          (relEntryBetter P I C S deltaAt? boundVars)
          entries with
    | none =>
        rfl
    | some selected =>
        rcases selected with ⟨entry, rest⟩
        have hSelected :
            List.Perm (entry :: rest) entries :=
          selectBestRelEntry_perm
            (relEntryBetter P I C S deltaAt? boundVars)
            hSelect
        have hRestFuel : rest.length ≤ fuel := by
          have hLen := hSelected.length_eq
          simp at hLen
          omega
        exact
          (List.Perm.cons entry
            (planRelEntriesWithFuel_perm P I C S deltaAt?
              fuel (addRelAtomBoundVars boundVars entry.2)
              rest hRestFuel)).trans hSelected

theorem plannedRelBodyAtoms_perm
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (entries : List (Nat × RelAtom D Γ)) :
    List.Perm
      (plannedRelBodyAtoms P I C S deltaAt? entries)
      entries := by
  unfold plannedRelBodyAtoms
  exact
    planRelEntriesWithFuel_perm P I C S deltaAt?
      entries.length [] entries (le_rfl)

/- A column whose atom argument is already bound. -/
structure BoundColumn
    (ρ : PartialAssign D)
    (a : RelAtom D Γ) where
  index : Fin (Γ.arity a.rel)
  value : D
  eval_eq :
    PartialAssign.evalTerm? ρ (a.args.get index) =
      some value

/- Search a finite list of columns for a bound atom argument. -/
def boundColumnFrom
    (ρ : PartialAssign D)
    (a : RelAtom D Γ) :
    List (Fin (Γ.arity a.rel)) → Option (BoundColumn ρ a)
| [] => none
| i :: is =>
    match hEval :
        PartialAssign.evalTerm? ρ (a.args.get i) with
    | some d =>
        some
          { index := i
            value := d
            eval_eq := hEval }
    | none => boundColumnFrom ρ a is

/- First bound constant or variable column for an atom. -/
def boundColumn?
    (ρ : PartialAssign D)
    (a : RelAtom D Γ) :
    Option (BoundColumn ρ a) :=
  boundColumnFrom ρ a (List.finRange (Γ.arity a.rel))

/- Proof-free bound-column data for proof bridges. -/
def boundColumnDataFrom
    (ρ : PartialAssign D)
    (a : RelAtom D Γ) :
    List (Fin (Γ.arity a.rel)) → Option (Fin (Γ.arity a.rel) × D)
| [] => none
| i :: is =>
    match PartialAssign.evalTerm? ρ (a.args.get i) with
    | some d => some (i, d)
    | none => boundColumnDataFrom ρ a is

/- First proof-free bound column for an atom. -/
def boundColumnData?
    (ρ : PartialAssign D)
    (a : RelAtom D Γ) :
    Option (Fin (Γ.arity a.rel) × D) :=
  boundColumnDataFrom ρ a (List.finRange (Γ.arity a.rel))

set_option linter.flexible false in
omit [LinearOrder D] in
theorem boundColumnDataFrom_eval_eq
    (ρ : PartialAssign D)
    (a : RelAtom D Γ) :
    ∀ {cols : List (Fin (Γ.arity a.rel))}
      {i : Fin (Γ.arity a.rel)} {d : D},
      boundColumnDataFrom ρ a cols = some (i, d) →
        PartialAssign.evalTerm? ρ (a.args.get i) = some d
| [], i, d, h => by
    simp [boundColumnDataFrom] at h
| j :: js, i, d, h => by
    unfold boundColumnDataFrom at h
    cases hEval :
        PartialAssign.evalTerm? ρ (a.args.get j) with
    | none =>
        simp [hEval] at h
        exact boundColumnDataFrom_eval_eq ρ a h
    | some e =>
        simp [hEval] at h
        rcases h with ⟨hIndex, hValue⟩
        cases hIndex
        cases hValue
        exact hEval

omit [LinearOrder D] in
theorem boundColumnData_eval_eq
    {ρ : PartialAssign D}
    {a : RelAtom D Γ}
    {i : Fin (Γ.arity a.rel)}
    {d : D}
    (hColumn : boundColumnData? ρ a = some (i, d)) :
    PartialAssign.evalTerm? ρ (a.args.get i) = some d := by
  unfold boundColumnData? at hColumn
  exact boundColumnDataFrom_eval_eq ρ a hColumn

/- Whether every variable used by an atom is already bound. -/
def atomVarsBound
    (ρ : PartialAssign D)
    (a : RelAtom D Γ) :
    Bool :=
  a.varList.all
    (fun x => (PartialAssign.lookup ρ x).isSome)

/- Direct tuple for an atom whose variables are all bound. -/
def allBoundAtomTuple?
    (ρ : PartialAssign D)
    (a : RelAtom D Γ) :
    Option (Tuple D (Γ.arity a.rel)) :=
  if atomVarsBound ρ a then
    some (a.evalTuple (PartialAssign.toAssign ρ))
  else
    none

/-
  Indexed tuple source for one bound column. This is only a
  candidate reducer; `extendWithAtomRow` remains the final
  semantic match.
-/
def atomIndexedTuplesFor
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (idx : Nat)
    (a : RelAtom D Γ)
    (i : Fin (Γ.arity a.rel))
    (d : D) :
    List (Tuple D (Γ.arity a.rel)) :=
  if deltaAt? = some idx then
    if hIDB : a.rel ∈ P.idb then
      S.delta.lookupIndexedTuples a.rel hIDB i d
    else
      []
  else
    if hIDB : a.rel ∈ P.idb then
      S.current.lookupIndexedTuples a.rel hIDB i d
    else
      C.lookupIndexedTuples a.rel i d

/- Whole-tuple membership for one atom source. -/
def atomContainsTupleFor
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (idx : Nat)
    (a : RelAtom D Γ)
    (t : Tuple D (Γ.arity a.rel)) :
    Bool :=
  if deltaAt? = some idx then
    if hIDB : a.rel ∈ P.idb then
      S.delta.containsTuple a.rel hIDB t
    else
      false
  else
    if hIDB : a.rel ∈ P.idb then
      S.current.containsTuple a.rel hIDB t
    else
      C.containsTuple a.rel t

/- Singleton candidate source for all-bound atom membership. -/
def atomTupleMembershipCandidatesFor
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (idx : Nat)
    (a : RelAtom D Γ)
    (t : Tuple D (Γ.arity a.rel)) :
    List (Tuple D (Γ.arity a.rel)) :=
  if P.atomContainsTupleFor I C S deltaAt? idx a t then
    [t]
  else
    []

/- Candidate source when an atom is completely bound. -/
def allBoundAtomCandidatesFor
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (idx : Nat)
    (ρ : PartialAssign D)
    (a : RelAtom D Γ) :
    Option (List (Tuple D (Γ.arity a.rel))) :=
  match allBoundAtomTuple? ρ a with
  | none => none
  | some t =>
      some
        (P.atomTupleMembershipCandidatesFor
          I C S deltaAt? idx a t)

theorem mem_atomIndexedTuplesFor_iff
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (idx : Nat)
    (a : RelAtom D Γ)
    (i : Fin (Γ.arity a.rel))
    (d : D)
    (t : Tuple D (Γ.arity a.rel)) :
    t ∈ P.atomIndexedTuplesFor I C S deltaAt? idx a i d ↔
      t ∈ P.atomTuplesFor I S deltaAt? idx a ∧
        t.get i = d := by
  unfold atomIndexedTuplesFor atomTuplesFor
  by_cases hDelta : deltaAt? = some idx
  · simp [hDelta]
    by_cases hIDB : a.rel ∈ P.idb
    · simp [hIDB,
        MaterializedIDB.mem_lookupIndexedTuples_iff]
    · simp [hIDB]
  · simp [hDelta]
    by_cases hIDB : a.rel ∈ P.idb
    · simp [hIDB,
        MaterializedIDB.mem_lookupIndexedTuples_iff]
    · simp [hIDB, IndexedInput.mem_lookupIndexedTuples_iff,
        IndexedInput.mem_lookupTuples_iff, Finset.mem_sort]

/- Indexed candidates for one atom and partial assignment. -/
def indexedAtomCandidatesFor
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (idx : Nat)
    (ρ : PartialAssign D)
    (a : RelAtom D Γ) :
    List (Tuple D (Γ.arity a.rel)) :=
  match P.allBoundAtomCandidatesFor I C S deltaAt? idx ρ a with
  | some tuples => tuples
  | none =>
      match boundColumnData? ρ a with
      | none => P.atomTuplesFor I S deltaAt? idx a
      | some column =>
          P.atomIndexedTuplesFor I C S deltaAt? idx a
            column.1 column.2

/- A column whose compiled atom argument is already bound. -/
structure SlotBoundColumn
    (ρ : SlotAssign D)
    (a : SlotRelAtom D Γ) where
  index : Fin (Γ.arity a.source.rel)
  value : D
  eval_eq :
    SlotAssign.evalTerm? ρ (a.args.get index) =
      some value

/- Search a finite list of columns for a bound compiled argument. -/
def slotBoundColumnFrom
    (ρ : SlotAssign D)
    (a : SlotRelAtom D Γ) :
    List (Fin (Γ.arity a.source.rel)) → Option (SlotBoundColumn ρ a)
| [] => none
| i :: is =>
    match hEval :
        SlotAssign.evalTerm? ρ (a.args.get i) with
    | some d =>
        some
          { index := i
            value := d
            eval_eq := hEval }
    | none => slotBoundColumnFrom ρ a is

/- First bound constant or slot column for a compiled atom. -/
def slotBoundColumn?
    (ρ : SlotAssign D)
    (a : SlotRelAtom D Γ) :
    Option (SlotBoundColumn ρ a) :=
  slotBoundColumnFrom ρ a
    (List.finRange (Γ.arity a.source.rel))

/- Proof-free bound-column data for compiled slot atoms. -/
def slotBoundColumnDataFrom
    (ρ : SlotAssign D)
    (a : SlotRelAtom D Γ) :
    List (Fin (Γ.arity a.source.rel)) →
      Option (Fin (Γ.arity a.source.rel) × D)
| [] => none
| i :: is =>
    match SlotAssign.evalTerm? ρ (a.args.get i) with
    | some d => some (i, d)
    | none => slotBoundColumnDataFrom ρ a is

/- First proof-free bound column for a compiled atom. -/
def slotBoundColumnData?
    (ρ : SlotAssign D)
    (a : SlotRelAtom D Γ) :
    Option (Fin (Γ.arity a.source.rel) × D) :=
  slotBoundColumnDataFrom ρ a
    (List.finRange (Γ.arity a.source.rel))

/- Indexed tuple source for one bound column of a compiled atom. -/
def slotAtomIndexedTuplesFor
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (idx : Nat)
    (a : SlotRelAtom D Γ)
    (i : Fin (Γ.arity a.source.rel))
    (d : D) :
    List (Tuple D (Γ.arity a.source.rel)) :=
  if deltaAt? = some idx then
    if hIDB : a.source.rel ∈ P.idb then
      S.delta.lookupIndexedTuples a.source.rel hIDB i d
    else
      []
  else
    if hIDB : a.source.rel ∈ P.idb then
      S.current.lookupIndexedTuples a.source.rel hIDB i d
    else
      C.lookupIndexedTuples a.source.rel i d

/- Direct tuple for a compiled atom whose variables are all bound. -/
def slotAllBoundAtomTuple?
    (ρ : SlotAssign D)
    (a : SlotRelAtom D Γ) :
    Option (Tuple D (Γ.arity a.source.rel)) :=
  allBoundAtomTuple? ρ.bindings a.toRelAtom

/- Singleton candidate source for all-bound compiled atom membership. -/
def slotAtomTupleMembershipCandidatesFor
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (idx : Nat)
    (a : SlotRelAtom D Γ)
    (t : Tuple D (Γ.arity a.source.rel)) :
    List (Tuple D (Γ.arity a.source.rel)) :=
  P.atomTupleMembershipCandidatesFor
    I C S deltaAt? idx a.toRelAtom t

/- Candidate source when a compiled atom is completely bound. -/
def slotAllBoundAtomCandidatesFor
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (idx : Nat)
    (ρ : SlotAssign D)
    (a : SlotRelAtom D Γ) :
    Option (List (Tuple D (Γ.arity a.source.rel))) :=
  match slotAllBoundAtomTuple? ρ a with
  | none => none
  | some t =>
      some
        (P.slotAtomTupleMembershipCandidatesFor
          I C S deltaAt? idx a t)

/- Full tuple source for a compiled atom. -/
def slotAtomTuplesFor
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (idx : Nat)
    (a : SlotRelAtom D Γ) :
    List (Tuple D (Γ.arity a.source.rel)) :=
  P.atomTuplesFor I S deltaAt? idx a.toRelAtom

/- Indexed candidates for one compiled atom and slot assignment. -/
def indexedSlotAtomCandidatesFor
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (idx : Nat)
    (ρ : SlotAssign D)
    (a : SlotRelAtom D Γ) :
    List (Tuple D (Γ.arity a.source.rel)) :=
  match P.slotAllBoundAtomCandidatesFor I C S deltaAt? idx ρ a with
  | some tuples => tuples
  | none =>
      match slotBoundColumnData? ρ a with
      | none => P.slotAtomTuplesFor I S deltaAt? idx a
      | some column =>
        P.slotAtomIndexedTuplesFor I C S deltaAt? idx a
          column.1 column.2

/-
  Extend all partial assignments using all tuples of one
  atom.
-/
def extendAssignmentsWithAtom
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (idx : Nat)
    (assignments : Finset (PartialAssign D))
    (a : RelAtom D Γ) :
    Finset (PartialAssign D) :=
  let R := atomRelationFor P I S deltaAt? idx a
  assignments.biUnion
    (fun ρ =>
      R.biUnion
        (fun t =>
          optionToFinset
            (extendWithAtomRow ρ a t)))

/-
  Extend all partial assignments using executable tuple
  lists.
-/
def extendAssignmentsWithAtomList
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (idx : Nat)
    (assignments : List (PartialAssign D))
    (a : RelAtom D Γ) :
    List (PartialAssign D) :=
  let tuples := P.atomTuplesFor I S deltaAt? idx a
  assignments.flatMap
    (fun ρ =>
      tuples.filterMap
        (fun t => extendWithAtomRow ρ a t))

/-
  Extend all partial assignments using indexed tuple
  candidates when the current assignment binds a column.
-/
def extendAssignmentsWithAtomIndexedList
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (idx : Nat)
    (assignments : List (PartialAssign D))
    (a : RelAtom D Γ) :
    List (PartialAssign D) :=
  assignments.flatMap
    (fun ρ =>
      (P.indexedAtomCandidatesFor I C S deltaAt? idx ρ a).filterMap
        (fun t => extendWithAtomRow ρ a t))

/-
  Extend all slot assignments using indexed tuple candidates
  when the current assignment binds a column.
-/
def extendSlotAssignmentsWithAtomIndexedList
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (idx : Nat)
    (assignments : List (SlotAssign D))
    (a : SlotRelAtom D Γ) :
    List (SlotAssign D) :=
  assignments.flatMap
    (fun ρ =>
      (P.indexedSlotAtomCandidatesFor I C S deltaAt? idx ρ a).filterMap
        (fun t => SlotAssign.extendWithAtomTuple ρ a t))

/-
  Join all relational atoms in a body, skipping equalities
  for now.
-/
def joinRelAtomsFrom
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat) :
    Nat → List (Atom D Γ) → Finset (PartialAssign D) →
      Finset (PartialAssign D)
| _idx, [], assignments => assignments
| idx, b :: body, assignments =>
    let assignments' :=
      match b with
      | .rel a =>
          extendAssignmentsWithAtom
            P I S deltaAt? idx assignments a
      | .eq _ _ => assignments
    joinRelAtomsFrom P I S deltaAt?
      (idx + 1) body assignments'

/-
  Join all relational atoms in a body using executable
  tuple lists, skipping equalities for now.
-/
def joinRelAtomsFromList
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat) :
    Nat → List (Atom D Γ) → List (PartialAssign D) →
      List (PartialAssign D)
| _idx, [], assignments => assignments
| idx, b :: body, assignments =>
    let assignments' :=
      match b with
      | .rel a =>
          extendAssignmentsWithAtomList
            P I S deltaAt? idx assignments a
      | .eq _ _ => assignments
    joinRelAtomsFromList P I S deltaAt?
      (idx + 1) body assignments'

/- Check one equality atom against a partial assignment. -/
def equalityHolds
    (ρ : PartialAssign D)
    (lhs rhs : RelTerm D) :
    Bool :=
  match PartialAssign.evalTerm? ρ lhs,
      PartialAssign.evalTerm? ρ rhs with
  | some d₁, some d₂ => decide (d₁ = d₂)
  | _, _ => false

/- Check all equality atoms in a body. -/
def equalitiesHold
    (ρ : PartialAssign D) :
    List (Atom D Γ) → Bool
| [] => true
| .rel _ :: body => equalitiesHold ρ body
| .eq lhs rhs :: body =>
    equalityHolds ρ lhs rhs && equalitiesHold ρ body

/- Check pre-split equality atoms against a partial assignment. -/
def compiledEqualitiesHold
    (ρ : PartialAssign D) :
    List (RelTerm D × RelTerm D) → Bool
| [] => true
| (lhs, rhs) :: atoms =>
    equalityHolds ρ lhs rhs &&
      compiledEqualitiesHold ρ atoms

omit [LinearOrder D] in
theorem compiledEqualitiesHold_equalityAtomPairs
    (ρ : PartialAssign D) :
    ∀ body : List (Atom D Γ),
      compiledEqualitiesHold ρ (equalityAtomPairs body) =
        equalitiesHold ρ body
| [] => rfl
| .rel _ :: body =>
    compiledEqualitiesHold_equalityAtomPairs ρ body
| .eq lhs rhs :: body => by
    simp [equalityAtomPairs, compiledEqualitiesHold,
      equalitiesHold,
      compiledEqualitiesHold_equalityAtomPairs ρ body]

/-
  Evaluate one rule body with an optional selected delta
  atom.
-/
def bodyAssignments
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (body : List (Atom D Γ)) :
    Finset (PartialAssign D) :=
  (joinRelAtomsFrom P I S deltaAt? 0 body {[]}).filter
    (fun ρ => equalitiesHold ρ body)

/-
  Executable body assignments, accumulated as a list. This
  may contain duplicates; deduplication happens once per
  IDB relation at the iteration boundary.
-/
def bodyAssignmentList
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (body : List (Atom D Γ)) :
    List (PartialAssign D) :=
  (joinRelAtomsFromList P I S deltaAt? 0 body [[]]).filter
    (fun ρ => equalitiesHold ρ body)

/-
  Join pre-split relational body atoms using executable
  tuple lists.
-/
def joinCompiledRelAtomsFromList
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat) :
    List (Nat × RelAtom D Γ) →
      List (PartialAssign D) → List (PartialAssign D)
| [], assignments => assignments
| (idx, a) :: atoms, assignments =>
    joinCompiledRelAtomsFromList P I S deltaAt? atoms
      (extendAssignmentsWithAtomList
        P I S deltaAt? idx assignments a)

/-
  Join pre-split relational body atoms using indexed tuple
  candidates.
-/
def joinCompiledRelAtomsFromIndexedList
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat) :
    List (Nat × RelAtom D Γ) →
      List (PartialAssign D) → List (PartialAssign D)
| [], assignments => assignments
| (idx, a) :: atoms, assignments =>
    joinCompiledRelAtomsFromIndexedList P I C S deltaAt? atoms
      (extendAssignmentsWithAtomIndexedList
        P I C S deltaAt? idx assignments a)

/-
  Join pre-split compiled slot atoms using indexed tuple
  candidates.
-/
def joinCompiledSlotRelAtomsFromIndexedList
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat) :
    List (Nat × SlotRelAtom D Γ) →
      List (SlotAssign D) → List (SlotAssign D)
| [], assignments => assignments
| (idx, a) :: atoms, assignments =>
    joinCompiledSlotRelAtomsFromIndexedList
      P I C S deltaAt? atoms
      (extendSlotAssignmentsWithAtomIndexedList
        P I C S deltaAt? idx assignments a)

/-
  Join relational body atoms in the planned order using
  indexed tuple candidates.
-/
def joinPlannedRelAtomsFromIndexedList
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (entries : List (Nat × RelAtom D Γ))
    (assignments : List (PartialAssign D)) :
    List (PartialAssign D) :=
  joinCompiledRelAtomsFromIndexedList P I C S deltaAt?
    (plannedRelBodyAtoms P I C S deltaAt? entries)
    assignments

/-
  Join normalized relational atoms in planned order using
  slot assignments.
-/
def joinPlannedSlotRelAtomsFromIndexedList
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (r : CompiledRule P)
    (assignments : List (SlotAssign D)) :
    List (SlotAssign D) :=
  let planned :=
    plannedRelBodyAtoms P I C S deltaAt?
      r.normalizedRelBodyAtoms
  joinCompiledSlotRelAtomsFromIndexedList
    P I C S deltaAt?
    (r.slotEnv.compileRelEntries planned)
    assignments

/- Whether one slot assignment can satisfy a compiled atom list. -/
def joinCompiledSlotRelAtomsExistsFrom
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat) :
    List (Nat × SlotRelAtom D Γ) → SlotAssign D → Bool
| [], _ρ => true
| (idx, a) :: atoms, ρ =>
    (P.indexedSlotAtomCandidatesFor
        I C S deltaAt? idx ρ a).any
      (fun t =>
        match SlotAssign.extendWithAtomTuple ρ a t with
        | none => false
        | some ρ' =>
            joinCompiledSlotRelAtomsExistsFrom
              P I C S deltaAt? atoms ρ')

/- Whether any slot assignment can satisfy a compiled atom list. -/
def joinCompiledSlotRelAtomsAny
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (entries : List (Nat × SlotRelAtom D Γ))
    (assignments : List (SlotAssign D)) :
    Bool :=
  assignments.any
    (fun ρ =>
      P.joinCompiledSlotRelAtomsExistsFrom
        I C S deltaAt? entries ρ)

/- Whether a compiled rule has a satisfying body witness. -/
def compiledBodySlotAssignmentExists
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (r : CompiledRule P) :
    Bool :=
  if r.normalizedImpossible then
    false
  else
    let planned :=
      plannedRelBodyAtoms P I C S deltaAt?
        r.normalizedRelBodyAtoms
    P.joinCompiledSlotRelAtomsAny I C S deltaAt?
      (r.slotEnv.compileRelEntries planned)
      [SlotAssign.empty r.slotEnv.size]

theorem joinCompiledRelAtomsFromList_relBodyAtomsFrom
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat) :
    ∀ (idx : Nat) (body : List (Atom D Γ))
      (assignments : List (PartialAssign D)),
      joinCompiledRelAtomsFromList P I S deltaAt?
          (relBodyAtomsFrom idx body) assignments =
        joinRelAtomsFromList P I S deltaAt?
          idx body assignments
| _idx, [], _assignments => rfl
| idx, .rel a :: body, assignments => by
    simp [relBodyAtomsFrom, joinCompiledRelAtomsFromList,
      joinRelAtomsFromList,
      joinCompiledRelAtomsFromList_relBodyAtomsFrom
        P I S deltaAt? (idx + 1) body]
| idx, .eq _ _ :: body, assignments => by
    simp [relBodyAtomsFrom, joinRelAtomsFromList,
      joinCompiledRelAtomsFromList_relBodyAtomsFrom
        P I S deltaAt? (idx + 1) body]

theorem joinCompiledRelAtomsFromList_relBodyAtomEntries
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (body : List (Atom D Γ))
    (assignments : List (PartialAssign D)) :
    joinCompiledRelAtomsFromList P I S deltaAt?
        (relBodyAtomEntries body) assignments =
      joinRelAtomsFromList P I S deltaAt?
        0 body assignments :=
  joinCompiledRelAtomsFromList_relBodyAtomsFrom
    P I S deltaAt? 0 body assignments

/- Executable assignments using compiled body metadata. -/
def compiledBodyAssignmentList
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (r : CompiledRule P) :
    List (PartialAssign D) :=
  (joinCompiledRelAtomsFromList
    P I S deltaAt? r.relBodyAtoms [[]]).filter
      (fun ρ => compiledEqualitiesHold ρ r.equalityAtoms)

/- Executable assignments using indexed compiled body metadata. -/
def compiledBodyAssignmentIndexedList
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (r : CompiledRule P) :
    List (PartialAssign D) :=
  if r.normalizedImpossible then
    []
  else
    joinPlannedRelAtomsFromIndexedList
      P I C S deltaAt? r.normalizedRelBodyAtoms [[]]

/-
  Executable assignments using slot-based indexed compiled
  body metadata.
-/
def compiledBodySlotAssignmentIndexedList
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (r : CompiledRule P) :
    List (SlotAssign D) :=
  if r.normalizedImpossible then
    []
  else
    P.joinPlannedSlotRelAtomsFromIndexedList
      I C S deltaAt? r
      [SlotAssign.empty r.slotEnv.size]

/- Nullary head tuple cast to a source rule head arity. -/
def nullaryHeadTuple
    {P : Program D Γ}
    (r : CompiledRule P)
    (hArity : Γ.arity r.source.head.rel = 0) :
    Tuple D (Γ.arity r.source.head.rel) :=
  Tuple.castArity hArity Tuple.empty

theorem compiledBodyAssignmentList_eq_bodyAssignmentList
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (r : CompiledRule P) :
    P.compiledBodyAssignmentList I S deltaAt? r =
      P.bodyAssignmentList I S deltaAt? r.source.body := by
  unfold compiledBodyAssignmentList bodyAssignmentList
  rw [r.relBodyAtoms_eq, r.equalityAtoms_eq]
  rw [joinCompiledRelAtomsFromList_relBodyAtomEntries]
  apply List.filter_congr
  intro ρ _hρ
  exact compiledEqualitiesHold_equalityAtomPairs ρ r.source.body

/-
  Materialize head tuples from joined partial assignments.
-/
def headTuplesOfAssignments
    (r : Rule D Γ)
    (assignments : Finset (PartialAssign D)) :
    FinRelation D (Γ.arity r.head.rel) :=
  assignments.image
    (fun ρ =>
      r.head.evalTuple (PartialAssign.toAssign ρ))

/-
  Directly materialize a head tuple from a partial
  assignment. For safe rules this reads only bound head
  variables.
-/
def headTupleOfPartial
    (r : Rule D Γ)
    (ρ : PartialAssign D) :
    Tuple D (Γ.arity r.head.rel) :=
  Vector.ofFn
    (fun i =>
      match r.head.args.get i with
      | .var x =>
          match PartialAssign.lookup ρ x with
          | some d => d
          | none => default
      | .const d => d)

omit [LinearOrder D] in
theorem headTupleOfPartial_eq_evalTuple_toAssign
    (r : Rule D Γ)
    (ρ : PartialAssign D) :
    headTupleOfPartial r ρ =
      r.head.evalTuple (PartialAssign.toAssign ρ) := by
  apply Vector.ext
  intro i hi
  let j : Fin (Γ.arity r.head.rel) := ⟨i, hi⟩
  change
    (headTupleOfPartial r ρ).get j =
      (r.head.evalTuple (PartialAssign.toAssign ρ)).get j
  simp [headTupleOfPartial, RelAtom.evalTuple,
    RelTerm.evalVector, Vector.get, RelTerm.eval,
    PartialAssign.toAssign]
  rfl

/-
  Directly materialize a tuple for an arbitrary relational
  atom from a partial assignment.
-/
def headTupleOfAtomPartial
    (a : RelAtom D Γ)
    (ρ : PartialAssign D) :
    Tuple D (Γ.arity a.rel) :=
  Vector.ofFn
    (fun i =>
      match a.args.get i with
      | .var x =>
          match PartialAssign.lookup ρ x with
          | some d => d
          | none => default
      | .const d => d)

omit [LinearOrder D] in
theorem headTupleOfAtomPartial_eq_evalTuple_toAssign
    (a : RelAtom D Γ)
    (ρ : PartialAssign D) :
    headTupleOfAtomPartial a ρ =
      a.evalTuple (PartialAssign.toAssign ρ) := by
  apply Vector.ext
  intro i hi
  let j : Fin (Γ.arity a.rel) := ⟨i, hi⟩
  change
    (headTupleOfAtomPartial a ρ).get j =
      (a.evalTuple (PartialAssign.toAssign ρ)).get j
  simp [headTupleOfAtomPartial, RelAtom.evalTuple,
    RelTerm.evalVector, Vector.get, RelTerm.eval,
    PartialAssign.toAssign]
  rfl

/-
  Candidate head tuples from executable body assignments.
-/
def headTupleListOfAssignments
    (r : Rule D Γ)
    (assignments : List (PartialAssign D)) :
    List (Tuple D (Γ.arity r.head.rel)) :=
  assignments.map (headTupleOfPartial r)

/-
  Candidate head tuples for a compiled normalized head,
  cast back to the source rule head arity.
-/
def compiledHeadTupleListOfAssignments
    {P : Program D Γ}
    (r : CompiledRule P)
    (assignments : List (PartialAssign D)) :
    List (Tuple D (Γ.arity r.source.head.rel)) :=
  (assignments.map
      (headTupleOfAtomPartial r.normalizedHead)).map
    (fun t =>
      cast
        (congrArg
          (fun X : Γ.syms => Tuple D (Γ.arity X))
          r.normalizedHead_rel_eq)
        t)

/- Candidate head tuple from one slot assignment. -/
def compiledHeadTupleOfSlotAssignment
    {P : Program D Γ}
    (r : CompiledRule P)
    (ρ : SlotAssign D) :
    Tuple D (Γ.arity r.source.head.rel) :=
  cast
    (congrArg
      (fun X : Γ.syms => Tuple D (Γ.arity X))
      r.normalizedHead_rel_eq)
    (cast
      (congrArg
        (fun a : RelAtom D Γ => Tuple D (Γ.arity a.rel))
        r.slotHead_source_eq)
      (SlotAssign.evalAtomTuple r.slotHead ρ))

/-
  Candidate head tuples from slot assignments for a
  compiled normalized head.
-/
def compiledHeadTupleListOfSlotAssignments
    {P : Program D Γ}
    (r : CompiledRule P)
    (assignments : List (SlotAssign D)) :
    List (Tuple D (Γ.arity r.source.head.rel)) :=
  assignments.map (compiledHeadTupleOfSlotAssignment r)

/- Insert a tuple into a list unless it is already present. -/
def insertTupleIfFresh
    {n : Nat}
    (t : Tuple D n)
    (seen : List (Tuple D n)) :
    List (Tuple D n) :=
  if t ∈ seen then
    seen
  else
    t :: seen

/- Variable slots mentioned by a compiled term. -/
def slotTermSlotList :
    SlotTerm D → List Nat
| .var _ slot => [slot]
| .const _ => []

/- Variable slots mentioned by a compiled atom. -/
def slotRelAtomSlotList
    (a : SlotRelAtom D Γ) :
    List Nat :=
  a.args.toList.flatMap slotTermSlotList

/- Add a slot to a list if absent. -/
def addSlot
    (slots : List Nat)
    (slot : Nat) :
    List Nat :=
  if slot ∈ slots then
    slots
  else
    slot :: slots

/- Add all slots from an atom to a binding-pattern list. -/
def addSlotRelAtomSlots
    (slots : List Nat)
    (a : SlotRelAtom D Γ) :
    List Nat :=
  (slotRelAtomSlotList a).foldl addSlot slots

/- Do all slots in `needed` occur in `bound`? -/
def allSlotsBound
    (needed bound : List Nat) :
    Bool :=
  needed.all (fun slot => decide (slot ∈ bound))

/-
  True when the planned order can determine the head key
  before the final relational atom. This gates the
  projection-distinct path so ordinary recursive joins avoid
  extra checks.
-/
def projectionKeyAvailableBeforeEnd
    (headSlots : List Nat) :
    List (Nat × SlotRelAtom D Γ) → List Nat → Bool
| [], _bound => false
| [_entry], bound => allSlotsBound headSlots bound
| (_idx, a) :: entries, bound =>
    if allSlotsBound headSlots bound then
      true
    else
      projectionKeyAvailableBeforeEnd headSlots entries
        (addSlotRelAtomSlots bound a)

/- Whether a compiled rule should use projection distinctness. -/
def compiledProjectionCanUseDistinctPath
    {P : Program D Γ}
    (r : CompiledRule P)
    (planned : List (Nat × SlotRelAtom D Γ)) :
    Bool :=
  let headSlots := slotRelAtomSlotList r.slotHead
  projectionKeyAvailableBeforeEnd headSlots planned []

/- Projection-distinct candidate tuples for one compiled rule. -/
def compiledProjectionDistinctRuleConsequenceIndexedList
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (r : CompiledRule P) :
    List (Tuple D (Γ.arity r.source.head.rel)) :=
  if r.normalizedImpossible then
    []
  else
    (P.compiledBodySlotAssignmentIndexedList
        I C S deltaAt? r).foldl
      (fun seen ρ =>
        insertTupleIfFresh
          (compiledHeadTupleOfSlotAssignment r ρ) seen)
      []

/-
  Projection-aware candidate head tuples. For nullary heads,
  all satisfying body witnesses produce the same tuple, so
  the evaluator only needs to know whether one witness
  exists.
-/
def compiledProjectedHeadTupleListOfSlotAssignments
    {P : Program D Γ}
    (r : CompiledRule P)
    (assignments : List (SlotAssign D)) :
    List (Tuple D (Γ.arity r.source.head.rel)) :=
  if hArity : Γ.arity r.source.head.rel = 0 then
    if assignments.isEmpty then
      []
    else
      [nullaryHeadTuple r hArity]
  else
    compiledHeadTupleListOfSlotAssignments r assignments

/- Projection-aware candidate tuple list for one compiled rule. -/
def compiledProjectedRuleConsequenceIndexedListCore
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (r : CompiledRule P) :
    List (Tuple D (Γ.arity r.source.head.rel)) :=
  if hArity : Γ.arity r.source.head.rel = 0 then
    if P.compiledBodySlotAssignmentExists I C S deltaAt? r then
      [nullaryHeadTuple r hArity]
    else
      []
  else
    let planned :=
      plannedRelBodyAtoms P I C S deltaAt?
        r.normalizedRelBodyAtoms
    if compiledProjectionCanUseDistinctPath r
        (r.slotEnv.compileRelEntries planned) then
      P.compiledProjectionDistinctRuleConsequenceIndexedList
        I C S deltaAt? r
    else
      compiledHeadTupleListOfSlotAssignments r
        (P.compiledBodySlotAssignmentIndexedList
          I C S deltaAt? r)

/- Projection-aware candidate tuple list for one compiled rule. -/
def compiledProjectedRuleConsequenceIndexedList
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (r : CompiledRule P) :
    List (Tuple D (Γ.arity r.source.head.rel)) :=
  P.compiledProjectedRuleConsequenceIndexedListCore
    I C S deltaAt? r

/-
  Rule consequence for one optional delta-position
  variant.
-/
def ruleConsequenceWithDeltaAt
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (r : Rule D Γ) :
    FinRelation D (Γ.arity r.head.rel) :=
  headTuplesOfAssignments r
    (bodyAssignments P I S deltaAt? r.body)

/-
  Candidate tuple list for one optional delta-position
  variant.
-/
def ruleConsequenceListWithDeltaAt
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (r : Rule D Γ) :
    List (Tuple D (Γ.arity r.head.rel)) :=
  headTupleListOfAssignments r
    (bodyAssignmentList P I S deltaAt? r.body)

/-
  Initial rule consequence: nonrecursive-body rules only.
-/
def initialRuleConsequence
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (r : Rule D Γ) :
    FinRelation D (Γ.arity r.head.rel) :=
  if bodyUsesIDB P r.body then
    ∅
  else
    let emptyState : SemiNaiveState P :=
      { current := MaterializedIDB.empty P
        delta := MaterializedIDB.empty P }
    ruleConsequenceWithDeltaAt P I emptyState none r

/-
  Candidate tuple list for initial nonrecursive-body rule
  consequences.
-/
def initialRuleConsequenceList
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (r : Rule D Γ) :
    List (Tuple D (Γ.arity r.head.rel)) :=
  if bodyUsesIDB P r.body then
    []
  else
    let emptyState : SemiNaiveState P :=
      { current := MaterializedIDB.empty P
        delta := MaterializedIDB.empty P }
    ruleConsequenceListWithDeltaAt P I emptyState none r

/-
  Candidate tuple list for an initial compiled rule
  consequence.
-/
def compiledInitialRuleConsequenceList
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (r : CompiledRule P) :
    List (Tuple D (Γ.arity r.source.head.rel)) :=
  if bodyUsesIDB P r.source.body then
    []
  else
    let emptyState : SemiNaiveState P :=
      { current := MaterializedIDB.empty P
        delta := MaterializedIDB.empty P }
    headTupleListOfAssignments r.source
      (compiledBodyAssignmentList P I emptyState none r)

/-
  Indexed candidate tuple list for an initial compiled rule
  consequence.
-/
def compiledInitialRuleConsequenceIndexedListCore
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (r : CompiledRule P) :
    List (Tuple D (Γ.arity r.source.head.rel)) :=
  if bodyUsesIDB P r.source.body then
    []
  else
    let emptyState : SemiNaiveState P :=
      { current := MaterializedIDB.empty P
        delta := MaterializedIDB.empty P }
    P.compiledProjectedRuleConsequenceIndexedListCore
      I C emptyState none r

/-
  Indexed candidate tuple list for an initial compiled rule
  consequence.
-/
def compiledInitialRuleConsequenceIndexedList
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (r : CompiledRule P) :
    List (Tuple D (Γ.arity r.source.head.rel)) :=
  P.compiledInitialRuleConsequenceIndexedListCore I C r

/-
  Semi-naive rule consequence: one variant per IDB body
  atom.
-/
def semiNaiveRuleConsequence
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (r : Rule D Γ) :
    FinRelation D (Γ.arity r.head.rel) :=
  (idbRelAtomIndices P r.body).foldl
    (fun acc idx =>
      acc ∪ ruleConsequenceWithDeltaAt P I S (some idx) r)
    ∅

/-
  Candidate tuple list for one rule: one variant per IDB
  body atom.
-/
def semiNaiveRuleConsequenceList
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (r : Rule D Γ) :
    List (Tuple D (Γ.arity r.head.rel)) :=
  (idbRelAtomIndices P r.body).flatMap
    (fun idx =>
      ruleConsequenceListWithDeltaAt P I S (some idx) r)

/-
  Candidate tuple list for one compiled rule: one variant
  per precomputed IDB body atom.
-/
def compiledSemiNaiveRuleConsequenceList
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (r : CompiledRule P) :
    List (Tuple D (Γ.arity r.source.head.rel)) :=
  r.idbBodyPositions.flatMap
    (fun idx =>
      headTupleListOfAssignments r.source
        (compiledBodyAssignmentList P I S (some idx) r))

/- Indexed candidate tuple list for one compiled rule. -/
def compiledSemiNaiveRuleConsequenceIndexedListCore
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (r : CompiledRule P) :
    List (Tuple D (Γ.arity r.source.head.rel)) :=
  r.idbBodyPositions.flatMap
    (fun idx =>
      P.compiledProjectedRuleConsequenceIndexedListCore
        I C S (some idx) r)

/- Indexed candidate tuple list for one compiled rule. -/
def compiledSemiNaiveRuleConsequenceIndexedList
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (r : CompiledRule P) :
    List (Tuple D (Γ.arity r.source.head.rel)) :=
  P.compiledSemiNaiveRuleConsequenceIndexedListCore I C S r


/-
  Accumulate rule consequences with a specified head
  symbol.
-/
def ruleConsequencesForHead
    (P : Program D Γ)
    (X : Γ.syms)
    (ruleEval : (r : Rule D Γ) →
      FinRelation D (Γ.arity r.head.rel)) :
    List (Rule D Γ) → FinRelation D (Γ.arity X)
| [] => ∅
| r :: rs =>
    let rest := ruleConsequencesForHead P X ruleEval rs
    if hHead : r.head.rel = X then
      cast
        (congrArg
          (fun Y : Γ.syms => FinRelation D (Γ.arity Y))
          hHead)
        (ruleEval r) ∪ rest
    else
      rest

/-
  Accumulate candidate tuples from rules with a specified
  head symbol.
-/
def ruleConsequenceListsForHead
    (P : Program D Γ)
    (X : Γ.syms)
    (ruleEval : (r : Rule D Γ) →
      List (Tuple D (Γ.arity r.head.rel))) :
    List (Rule D Γ) → List (Tuple D (Γ.arity X))
| [] => []
| r :: rs =>
    let rest := ruleConsequenceListsForHead P X ruleEval rs
    if hHead : r.head.rel = X then
      cast
        (congrArg
          (fun Y : Γ.syms => List (Tuple D (Γ.arity Y)))
          hHead)
        (ruleEval r) ++ rest
    else
      rest

/-
  Accumulate candidate tuples from compiled rules with a
  specified head symbol.
-/
def compiledRuleConsequenceListsForHeadStep
    (P : Program D Γ)
    (X : Γ.syms)
    (ruleEval : (r : CompiledRule P) →
      List (Tuple D (Γ.arity r.source.head.rel)))
    (acc : List (Tuple D (Γ.arity X)))
    (r : CompiledRule P) :
    List (Tuple D (Γ.arity X)) :=
    if hHead : r.source.head.rel = X then
      cast
        (congrArg
          (fun Y : Γ.syms => List (Tuple D (Γ.arity Y)))
          hHead)
        (ruleEval r) ++ acc
    else
      acc

def compiledRuleConsequenceListsForHead
    (P : Program D Γ)
    (X : Γ.syms)
    (ruleEval : (r : CompiledRule P) →
      List (Tuple D (Γ.arity r.source.head.rel)))
    (rules : List (CompiledRule P)) :
    List (Tuple D (Γ.arity X)) :=
  rules.foldl
    (compiledRuleConsequenceListsForHeadStep P X ruleEval)
    []

/- Initial derived facts for one IDB symbol. -/
def initialConsequencesForHead
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (X : Γ.syms) :
    FinRelation D (Γ.arity X) :=
  ruleConsequencesForHead P X
    (fun r => initialRuleConsequence P I r)
    P.rules

/- Initial derived candidate tuples for one IDB symbol. -/
def initialConsequenceListForHead
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (X : Γ.syms) :
    List (Tuple D (Γ.arity X)) :=
  ruleConsequenceListsForHead P X
    (fun r => initialRuleConsequenceList P I r)
    P.rules

/- Initial derived candidate tuples from compiled rules. -/
def CompiledProgram.initialConsequenceListForHeadWithInputCore
    {P : Program D Γ}
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema)
    (input : MaterializedInput P I)
    (X : Γ.syms) :
    List (Tuple D (Γ.arity X)) :=
  compiledRuleConsequenceListsForHead P X
    (fun r =>
      compiledInitialRuleConsequenceIndexedListCore P I input r)
    (compiled.rulesForHead X)

/- Initial derived candidate tuples from compiled rules. -/
def CompiledProgram.initialConsequenceListForHeadWithInput
    {P : Program D Γ}
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema)
    (input : MaterializedInput P I)
    (X : Γ.syms) :
    List (Tuple D (Γ.arity X)) :=
  compiled.initialConsequenceListForHeadWithInputCore
    I input X

/- Initial derived candidate tuples from compiled rules. -/
def CompiledProgram.initialConsequenceListForHead
    {P : Program D Γ}
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema)
    (X : Γ.syms) :
    List (Tuple D (Γ.arity X)) :=
  compiled.initialConsequenceListForHeadWithInputCore
    I (P.materializeInput I) X

/- Semi-naive newly produced facts for one IDB symbol. -/
def semiNaiveConsequencesForHead
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (X : Γ.syms) :
    FinRelation D (Γ.arity X) :=
  ruleConsequencesForHead P X
    (fun r => semiNaiveRuleConsequence P I S r)
    P.rules

/- Semi-naive newly produced candidate tuples for one IDB symbol. -/
def semiNaiveConsequenceListForHead
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (X : Γ.syms) :
    List (Tuple D (Γ.arity X)) :=
  ruleConsequenceListsForHead P X
    (fun r => semiNaiveRuleConsequenceList P I S r)
    P.rules

/- Semi-naive candidate tuples from compiled rules. -/
def CompiledProgram.semiNaiveConsequenceListForHeadWithInputCore
    {P : Program D Γ}
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema)
    (input : MaterializedInput P I)
    (S : SemiNaiveState P)
    (X : Γ.syms) :
    List (Tuple D (Γ.arity X)) :=
  compiledRuleConsequenceListsForHead P X
    (fun r =>
      compiledSemiNaiveRuleConsequenceIndexedListCore
        P I input S r)
    (compiled.rulesForHead X)

/- Semi-naive candidate tuples from compiled rules. -/
def CompiledProgram.semiNaiveConsequenceListForHeadWithInput
    {P : Program D Γ}
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema)
    (input : MaterializedInput P I)
    (S : SemiNaiveState P)
    (X : Γ.syms) :
    List (Tuple D (Γ.arity X)) :=
  compiled.semiNaiveConsequenceListForHeadWithInputCore
    I input S X

/- Semi-naive candidate tuples from compiled rules. -/
def CompiledProgram.semiNaiveConsequenceListForHead
    {P : Program D Γ}
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (X : Γ.syms) :
    List (Tuple D (Γ.arity X)) :=
  compiled.semiNaiveConsequenceListForHeadWithInputCore
    I (P.materializeInput I) S X

/- Initial derived candidate tuples for one IDB symbol. -/
def initialCompiledConsequenceListForHeadWithInput
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (input : MaterializedInput P I)
    (X : Γ.syms) :
    List (Tuple D (Γ.arity X)) :=
  (P.compile).initialConsequenceListForHeadWithInputCore I input X

/- Initial derived candidate tuples for one IDB symbol. -/
def initialCompiledConsequenceListForHead
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (X : Γ.syms) :
    List (Tuple D (Γ.arity X)) :=
  P.initialCompiledConsequenceListForHeadWithInput
    I (P.materializeInput I) X

/- Semi-naive compiled candidate tuples for one IDB symbol. -/
def semiNaiveCompiledConsequenceListForHeadWithInput
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (input : MaterializedInput P I)
    (S : SemiNaiveState P)
    (X : Γ.syms) :
    List (Tuple D (Γ.arity X)) :=
  (P.compile).semiNaiveConsequenceListForHeadWithInputCore
    I input S X

/- Semi-naive compiled candidate tuples for one IDB symbol. -/
def semiNaiveCompiledConsequenceListForHead
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (X : Γ.syms) :
    List (Tuple D (Γ.arity X)) :=
  P.semiNaiveCompiledConsequenceListForHeadWithInput
    I (P.materializeInput I) S X

end Program

end Datalog

------------------------------------------------------------
-- Semi-Naive Fixed Point
------------------------------------------------------------

namespace Datalog

namespace Program

variable {A D : Type}
variable [RelationNames A] [Domain D] [LinearOrder D] [Hashable D]
variable {Γ : UnnamedSchema A}

/-
  Initial semi-naive state: nonrecursive-body
  consequences.
-/
def snInitialStateWithInput
    {P : Program D Γ}
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema)
    (input : MaterializedInput P I) :
    SemiNaiveState P :=
  let S :=
    MaterializedIDB.ofTupleListIdbFn
      (P := P)
      (fun X _hX =>
        compiled.initialConsequenceListForHeadWithInputCore
          I input X)
  { current := S
    delta := S }

/- Initial semi-naive state using a precompiled program. -/
def semiNaiveInitialStateWith
    {P : Program D Γ}
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema) :
    SemiNaiveState P :=
  P.snInitialStateWithInput compiled I (P.materializeInput I)

/- Initial semi-naive state using the program's compiled rules. -/
def semiNaiveInitialState
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    SemiNaiveState P :=
  P.semiNaiveInitialStateWith P.compile I

/- Fresh candidate tuples relative to an old relation. -/
def freshTuples
    {n : Nat}
    (old : List (Tuple D n))
    (candidates : List (Tuple D n)) :
    List (Tuple D n) :=
  Tuple.listFresh candidates old

omit [Domain D] in
theorem mem_freshTuples_iff
    {n : Nat}
    (old : List (Tuple D n))
    (candidates : List (Tuple D n))
    (t : Tuple D n) :
    t ∈ freshTuples old candidates ↔
      t ∈ candidates ∧ t ∉ old := by
  unfold freshTuples
  exact Tuple.mem_listFresh_iff candidates old t

theorem freshTuples_toFinset_eq_sdiff
    {n : Nat}
    (old : List (Tuple D n))
    (candidates : List (Tuple D n)) :
    (freshTuples old candidates).toFinset =
      candidates.toFinset \ old.toFinset := by
  apply Finset.ext
  intro t
  simp [List.mem_toFinset, mem_freshTuples_iff]

/- Fresh candidate tuples relative to an indexed old relation. -/
def freshTuplesUsingIndex
    {n : Nat}
    (oldIndex : Tuple.MemberIndex D n)
    (candidates : List (Tuple D n)) :
    List (Tuple D n) :=
  (Tuple.sortDedup candidates).filter
    (fun t => !(oldIndex.contains t))

theorem mem_freshTuplesUsingIndex_iff
    {n : Nat}
    (oldIndex : Tuple.MemberIndex D n)
    (old candidates : List (Tuple D n))
    (hOld : ∀ t : Tuple D n,
      oldIndex.contains t = true ↔ t ∈ old)
    (t : Tuple D n) :
    t ∈ freshTuplesUsingIndex oldIndex candidates ↔
      t ∈ candidates ∧ t ∉ old := by
  unfold freshTuplesUsingIndex
  constructor
  · intro ht
    rcases List.mem_filter.mp ht with ⟨hCand, hFresh⟩
    refine
      ⟨(Tuple.mem_sortDedup_iff t candidates).mp hCand,
        ?_⟩
    intro hOldMem
    have hContains := (hOld t).mpr hOldMem
    simp [hContains] at hFresh
  · intro ht
    apply List.mem_filter.mpr
    refine
      ⟨(Tuple.mem_sortDedup_iff t candidates).mpr ht.1,
        ?_⟩
    have hContains : oldIndex.contains t = false := by
      cases h : oldIndex.contains t with
      | false => rfl
      | true =>
          exact False.elim (ht.2 ((hOld t).mp h))
    simp [hContains]

theorem freshTuplesUsingIndex_toFinset_eq
    {n : Nat}
    (oldIndex : Tuple.MemberIndex D n)
    (old candidates : List (Tuple D n))
    (hOld : ∀ t : Tuple D n,
      oldIndex.contains t = true ↔ t ∈ old) :
    (freshTuplesUsingIndex oldIndex candidates).toFinset =
      (freshTuples old candidates).toFinset := by
  apply Finset.ext
  intro t
  simp [List.mem_toFinset,
    mem_freshTuplesUsingIndex_iff oldIndex old candidates hOld,
    mem_freshTuples_iff]

theorem nodup_freshTuplesUsingIndex
    {n : Nat}
    (oldIndex : Tuple.MemberIndex D n)
    (candidates : List (Tuple D n)) :
    (freshTuplesUsingIndex oldIndex candidates).Nodup := by
  unfold freshTuplesUsingIndex
  exact (Tuple.nodup_sortDedup candidates).filter _

theorem freshTuplesUsingIndex_eq
    {n : Nat}
    (oldIndex : Tuple.MemberIndex D n)
    (old candidates : List (Tuple D n))
    (hOld : ∀ t : Tuple D n,
      oldIndex.contains t = true ↔ t ∈ old) :
    freshTuplesUsingIndex oldIndex candidates =
      freshTuples old candidates := by
  unfold freshTuplesUsingIndex freshTuples
  unfold Tuple.listFresh Tuple.listDiff
  apply List.filter_congr
  intro t _ht
  have hBool :
      oldIndex.contains t = decide (t ∈ old) := by
    by_cases hMem : t ∈ old
    · have hTrue : oldIndex.contains t = true :=
        (hOld t).mpr hMem
      simp [hMem, hTrue]
    · have hFalse : oldIndex.contains t = false := by
        cases hContains : oldIndex.contains t with
        | false => rfl
        | true =>
            exact False.elim (hMem ((hOld t).mp hContains))
      simp [hMem, hFalse]
  simp [hBool]

/- Shared current/delta update for one IDB relation. -/
structure StepRelationUpdate
    (P : Program D Γ) where
  sym : P.IDBSym
  currentTuples : List (Tuple D (Γ.arity sym.1))
  currentNodup : currentTuples.Nodup
  currentIndex : Tuple.Index D (Γ.arity sym.1)
  currentIndex_mem :
    ∀ (i : Fin (Γ.arity sym.1)) (d : D)
      (t : Tuple D (Γ.arity sym.1)),
      t ∈ currentIndex.lookup i d ↔
        t ∈ currentTuples ∧ t.get i = d
  currentMemberIndex : Tuple.MemberIndex D (Γ.arity sym.1)
  currentMemberIndex_mem :
    ∀ t : Tuple D (Γ.arity sym.1),
      currentMemberIndex.contains t = true ↔
        t ∈ currentTuples
  deltaTuples : List (Tuple D (Γ.arity sym.1))
  deltaNodup : deltaTuples.Nodup
  deltaIndex : Tuple.Index D (Γ.arity sym.1)
  deltaIndex_mem :
    ∀ (i : Fin (Γ.arity sym.1)) (d : D)
      (t : Tuple D (Γ.arity sym.1)),
      t ∈ deltaIndex.lookup i d ↔
        t ∈ deltaTuples ∧ t.get i = d
  deltaMemberIndex : Tuple.MemberIndex D (Γ.arity sym.1)
  deltaMemberIndex_mem :
    ∀ t : Tuple D (Γ.arity sym.1),
      deltaMemberIndex.contains t = true ↔
        t ∈ deltaTuples

/-
  Compute one IDB relation update once, sharing the fresh
  delta between the next current state and next delta state.
-/
def stepRelationUpdateWithInput
    {P : Program D Γ}
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema)
    (input : MaterializedInput P I)
    (S : SemiNaiveState P)
    (X : P.IDBSym) :
    StepRelationUpdate P :=
  let oldTuples := S.current.lookupTuples X.1 X.2
  let produced :=
    compiled.semiNaiveConsequenceListForHeadWithInputCore
      I input S X.1
  let oldMemberIndex := S.current.lookupMemberIndex X.1 X.2
  let fresh := freshTuplesUsingIndex oldMemberIndex produced
  let oldIndex := S.current.lookupIndex X.1 X.2
  { sym := X
    currentTuples := Tuple.listUnion oldTuples fresh
    currentNodup := by
      apply Tuple.nodup_listUnion
      · exact MaterializedIDB.lookupTuples_nodup
          S.current X.1 X.2
      · exact nodup_freshTuplesUsingIndex oldMemberIndex
          produced
      · intro t htFresh htOld
        have hOldIndex :
            ∀ u : Tuple D (Γ.arity X.1),
              oldMemberIndex.contains u = true ↔
                u ∈ oldTuples := by
          intro u
          simpa [oldMemberIndex, oldTuples] using
            (MaterializedIDB.mem_lookupMemberIndex_iff
              S.current X.1 X.2 u)
        exact
          ((mem_freshTuplesUsingIndex_iff oldMemberIndex
              oldTuples produced hOldIndex t).mp htFresh).2
            htOld
    currentIndex := Tuple.Index.insertList fresh oldIndex
    currentIndex_mem := by
      intro i d t
      rw [Tuple.Index.mem_lookup_insertList_iff]
      rw [MaterializedIDB.mem_lookupIndex_iff]
      constructor
      · intro ht
        rcases ht with hFresh | hOld
        · exact
            ⟨(Tuple.mem_listUnion_iff oldTuples fresh t).mpr
                (Or.inr hFresh.1),
              hFresh.2⟩
        · exact
            ⟨(Tuple.mem_listUnion_iff oldTuples fresh t).mpr
                (Or.inl hOld.1),
              hOld.2⟩
      · intro ht
        rcases
            (Tuple.mem_listUnion_iff oldTuples fresh t).mp
              ht.1 with hOld | hFresh
        · exact Or.inr ⟨hOld, ht.2⟩
        · exact Or.inl ⟨hFresh, ht.2⟩
    currentMemberIndex :=
      Tuple.MemberIndex.insertList fresh oldMemberIndex
    currentMemberIndex_mem := by
      intro t
      rw [Tuple.MemberIndex.contains_insertList_iff]
      rw [MaterializedIDB.mem_lookupMemberIndex_iff]
      constructor
      · intro ht
        rcases ht with hFresh | hOld
        · exact
            (Tuple.mem_listUnion_iff oldTuples fresh t).mpr
              (Or.inr hFresh)
        · exact
            (Tuple.mem_listUnion_iff oldTuples fresh t).mpr
              (Or.inl hOld)
      · intro ht
        rcases
            (Tuple.mem_listUnion_iff oldTuples fresh t).mp
              ht with hOld | hFresh
        · exact Or.inr hOld
        · exact Or.inl hFresh
    deltaTuples := fresh
    deltaNodup :=
      nodup_freshTuplesUsingIndex oldMemberIndex produced
    deltaIndex := Tuple.Index.ofList fresh
    deltaIndex_mem := by
      intro i d t
      exact Tuple.Index.mem_lookup_iff fresh i d t
    deltaMemberIndex := Tuple.MemberIndex.ofList fresh
    deltaMemberIndex_mem := by
      intro t
      exact Tuple.MemberIndex.contains_ofList_iff fresh t }

/- Compute one IDB relation update using a precompiled program. -/
def stepRelationUpdate
    {P : Program D Γ}
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (X : P.IDBSym) :
    StepRelationUpdate P :=
  stepRelationUpdateWithInput
    compiled I (P.materializeInput I) S X

/- Compute all IDB relation updates for one step. -/
def stepRelationUpdatesWithInput
    {P : Program D Γ}
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema)
    (input : MaterializedInput P I)
    (S : SemiNaiveState P) :
    List (StepRelationUpdate P) :=
  P.idbSymList.map
    (fun X => stepRelationUpdateWithInput
      compiled I input S X)

/- Compute all IDB relation updates for one step. -/
def stepRelationUpdates
    {P : Program D Γ}
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P) :
    List (StepRelationUpdate P) :=
  stepRelationUpdatesWithInput
    compiled I (P.materializeInput I) S

/- Lookup current tuples from precomputed step updates. -/
def lookupCurrentUpdateTuples
    {P : Program D Γ} :
    List (StepRelationUpdate P) →
      (X : Γ.syms) → X ∈ P.idb →
        List (Tuple D (Γ.arity X))
| [], _X, _hX => []
| update :: updates, X, hX =>
    if h : update.sym.1 = X then
      cast
        (congrArg
          (fun Y : Γ.syms => List (Tuple D (Γ.arity Y)))
          h)
        update.currentTuples
    else
      lookupCurrentUpdateTuples updates X hX

/- Lookup delta tuples from precomputed step updates. -/
def lookupDeltaUpdateTuples
    {P : Program D Γ} :
    List (StepRelationUpdate P) →
      (X : Γ.syms) → X ∈ P.idb →
        List (Tuple D (Γ.arity X))
| [], _X, _hX => []
| update :: updates, X, hX =>
    if h : update.sym.1 = X then
      cast
        (congrArg
          (fun Y : Γ.syms => List (Tuple D (Γ.arity Y)))
          h)
        update.deltaTuples
    else
      lookupDeltaUpdateTuples updates X hX

/- Current materialized relations from step updates. -/
def currentRelationsOfStepUpdates
    {P : Program D Γ} :
    List (StepRelationUpdate P) → List (MaterializedRelation P)
| [] => []
| update :: updates =>
    { sym := update.sym
      tuples := update.currentTuples
      nodup_tuples := update.currentNodup
      index := update.currentIndex
      index_mem := update.currentIndex_mem
      memberIndex := update.currentMemberIndex
      memberIndex_mem := update.currentMemberIndex_mem } ::
      currentRelationsOfStepUpdates updates

/- Delta materialized relations from step updates. -/
def deltaRelationsOfStepUpdates
    {P : Program D Γ} :
    List (StepRelationUpdate P) → List (MaterializedRelation P)
| [] => []
| update :: updates =>
    { sym := update.sym
      tuples := update.deltaTuples
      nodup_tuples := update.deltaNodup
      index := update.deltaIndex
      index_mem := update.deltaIndex_mem
      memberIndex := update.deltaMemberIndex
      memberIndex_mem := update.deltaMemberIndex_mem } ::
      deltaRelationsOfStepUpdates updates

/- Current materialized IDB state from step updates. -/
def currentIdbOfStepUpdates
    {P : Program D Γ}
    (updates : List (StepRelationUpdate P)) :
    MaterializedIDB P :=
  { relations := currentRelationsOfStepUpdates updates }

/- Delta materialized IDB state from step updates. -/
def deltaIdbOfStepUpdates
    {P : Program D Γ}
    (updates : List (StepRelationUpdate P)) :
    MaterializedIDB P :=
  { relations := deltaRelationsOfStepUpdates updates }

private theorem lookupTupleLists_currentRelationsOfStepUpdates
    {P : Program D Γ} :
    ∀ (updates : List (StepRelationUpdate P))
      (X : Γ.syms) (hX : X ∈ P.idb),
      MaterializedIDB.lookupTupleLists P
          (currentRelationsOfStepUpdates updates) X hX =
        lookupCurrentUpdateTuples updates X hX
| [], _X, _hX => rfl
| update :: updates, X, hX => by
    unfold currentRelationsOfStepUpdates
      MaterializedIDB.lookupTupleLists
      lookupCurrentUpdateTuples
    by_cases h : update.sym.1 = X
    · simp [h]
    · simp [h,
        lookupTupleLists_currentRelationsOfStepUpdates
          updates X hX]

private theorem lookupTupleLists_deltaRelationsOfStepUpdates
    {P : Program D Γ} :
    ∀ (updates : List (StepRelationUpdate P))
      (X : Γ.syms) (hX : X ∈ P.idb),
      MaterializedIDB.lookupTupleLists P
          (deltaRelationsOfStepUpdates updates) X hX =
        lookupDeltaUpdateTuples updates X hX
| [], _X, _hX => rfl
| update :: updates, X, hX => by
    unfold deltaRelationsOfStepUpdates
      MaterializedIDB.lookupTupleLists
      lookupDeltaUpdateTuples
    by_cases h : update.sym.1 = X
    · simp [h]
    · simp [h,
        lookupTupleLists_deltaRelationsOfStepUpdates
          updates X hX]

theorem lookup_currentIdbOfStepUpdates
    {P : Program D Γ}
    (updates : List (StepRelationUpdate P))
    (X : Γ.syms)
    (hX : X ∈ P.idb) :
    (currentIdbOfStepUpdates updates).lookup X hX =
      (lookupCurrentUpdateTuples updates X hX).toFinset := by
  rw [MaterializedIDB.lookup_eq_lookupTuples_toFinset]
  change
    (MaterializedIDB.lookupTupleLists P
      (currentRelationsOfStepUpdates updates) X hX).toFinset =
        (lookupCurrentUpdateTuples updates X hX).toFinset
  rw [lookupTupleLists_currentRelationsOfStepUpdates]

theorem lookup_deltaIdbOfStepUpdates
    {P : Program D Γ}
    (updates : List (StepRelationUpdate P))
    (X : Γ.syms)
    (hX : X ∈ P.idb) :
    (deltaIdbOfStepUpdates updates).lookup X hX =
      (lookupDeltaUpdateTuples updates X hX).toFinset := by
  rw [MaterializedIDB.lookup_eq_lookupTuples_toFinset]
  change
    (MaterializedIDB.lookupTupleLists P
      (deltaRelationsOfStepUpdates updates) X hX).toFinset =
        (lookupDeltaUpdateTuples updates X hX).toFinset
  rw [lookupTupleLists_deltaRelationsOfStepUpdates]

omit [LinearOrder D] in
private theorem idbSymList_mem_of_idb_for_updates
    {P : Program D Γ}
    {X : Γ.syms}
    (hX : X ∈ P.idb) :
    (⟨X, hX⟩ : P.IDBSym) ∈ P.idbSymList := by
  let hList : X ∈ P.idbList :=
    (MaterializedIDB.idbList_mem_iff_idb P).mpr hX
  unfold Program.idbSymList
  apply List.mem_map.mpr
  refine ⟨⟨X, hList⟩, List.mem_attach _ _, ?_⟩
  apply Subtype.ext
  rfl

set_option linter.flexible false in
private theorem lookupCurrentUpdateTuples_map_stepRelationUpdateWithInput
    {P : Program D Γ}
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema)
    (input : MaterializedInput P I)
    (S : SemiNaiveState P)
    (X : Γ.syms)
    (hX : X ∈ P.idb)
    (xs : List P.IDBSym)
    (hMem : (⟨X, hX⟩ : P.IDBSym) ∈ xs) :
    lookupCurrentUpdateTuples
        (xs.map
          (fun Y => stepRelationUpdateWithInput
            compiled I input S Y))
        X hX =
      Tuple.listUnion (S.current.lookupTuples X hX)
        (freshTuples (S.current.lookupTuples X hX)
          (compiled.semiNaiveConsequenceListForHeadWithInputCore
            I input S X)) := by
  induction xs with
  | nil =>
      cases hMem
  | cons Y Ys ih =>
      simp only [List.map_cons]
      unfold lookupCurrentUpdateTuples
      by_cases hYX : Y.1 = X
      · cases Y with
        | mk Y hY =>
            subst hYX
            have hFresh :
                freshTuplesUsingIndex
                    (S.current.lookupMemberIndex Y hY)
                    (compiled.semiNaiveConsequenceListForHeadWithInputCore
                      I input S Y) =
                  freshTuples (S.current.lookupTuples Y hY)
                    (compiled.semiNaiveConsequenceListForHeadWithInputCore
                      I input S Y) :=
              freshTuplesUsingIndex_eq
                (S.current.lookupMemberIndex Y hY)
                (S.current.lookupTuples Y hY)
                (compiled.semiNaiveConsequenceListForHeadWithInputCore
                  I input S Y)
                (fun t =>
                  MaterializedIDB.mem_lookupMemberIndex_iff
                    S.current Y hY t)
            simp [stepRelationUpdateWithInput, hFresh]
      · have hUpdate :
            (stepRelationUpdateWithInput compiled I input S Y).sym.1 ≠
              X := by
          intro h
          exact hYX h
        rw [dif_neg hUpdate]
        have hMemTail :
            (⟨X, hX⟩ : P.IDBSym) ∈ Ys := by
          rcases List.mem_cons.mp hMem with hEq | hTail
          · cases hEq
            exact False.elim (hYX rfl)
          · exact hTail
        exact ih hMemTail

theorem lookupCurrentUpdateTuples_stepRelationUpdatesWithInput
    {P : Program D Γ}
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema)
    (input : MaterializedInput P I)
    (S : SemiNaiveState P)
    (X : Γ.syms)
    (hX : X ∈ P.idb) :
    lookupCurrentUpdateTuples
        (stepRelationUpdatesWithInput compiled I input S) X hX =
      Tuple.listUnion (S.current.lookupTuples X hX)
        (freshTuples (S.current.lookupTuples X hX)
          (compiled.semiNaiveConsequenceListForHeadWithInputCore
            I input S X)) := by
  unfold stepRelationUpdatesWithInput
  apply lookupCurrentUpdateTuples_map_stepRelationUpdateWithInput
  exact idbSymList_mem_of_idb_for_updates hX

set_option linter.flexible false in
private theorem lookupCurrentUpdateTuples_map_stepRelationUpdate
    {P : Program D Γ}
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (X : Γ.syms)
    (hX : X ∈ P.idb)
    (xs : List P.IDBSym)
    (hMem : (⟨X, hX⟩ : P.IDBSym) ∈ xs) :
    lookupCurrentUpdateTuples
        (xs.map (fun Y => stepRelationUpdate compiled I S Y))
        X hX =
      Tuple.listUnion (S.current.lookupTuples X hX)
        (freshTuples (S.current.lookupTuples X hX)
          (compiled.semiNaiveConsequenceListForHead I S X)) := by
  simpa [stepRelationUpdate,
    CompiledProgram.semiNaiveConsequenceListForHead] using
    lookupCurrentUpdateTuples_map_stepRelationUpdateWithInput
      compiled I (P.materializeInput I) S X hX xs hMem

theorem lookupCurrentUpdateTuples_stepRelationUpdates
    {P : Program D Γ}
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (X : Γ.syms)
    (hX : X ∈ P.idb) :
    lookupCurrentUpdateTuples
        (stepRelationUpdates compiled I S) X hX =
      Tuple.listUnion (S.current.lookupTuples X hX)
        (freshTuples (S.current.lookupTuples X hX)
          (compiled.semiNaiveConsequenceListForHead I S X)) := by
  unfold stepRelationUpdates
  apply lookupCurrentUpdateTuples_map_stepRelationUpdate
  exact idbSymList_mem_of_idb_for_updates hX

set_option linter.flexible false in
private theorem lookupDeltaUpdateTuples_map_stepRelationUpdateWithInput
    {P : Program D Γ}
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema)
    (input : MaterializedInput P I)
    (S : SemiNaiveState P)
    (X : Γ.syms)
    (hX : X ∈ P.idb)
    (xs : List P.IDBSym)
    (hMem : (⟨X, hX⟩ : P.IDBSym) ∈ xs) :
    lookupDeltaUpdateTuples
        (xs.map
          (fun Y => stepRelationUpdateWithInput
            compiled I input S Y))
        X hX =
      freshTuples (S.current.lookupTuples X hX)
        (compiled.semiNaiveConsequenceListForHeadWithInputCore
          I input S X) := by
  induction xs with
  | nil =>
      cases hMem
  | cons Y Ys ih =>
      simp only [List.map_cons]
      unfold lookupDeltaUpdateTuples
      by_cases hYX : Y.1 = X
      · cases Y with
        | mk Y hY =>
            subst hYX
            have hFresh :
                freshTuplesUsingIndex
                    (S.current.lookupMemberIndex Y hY)
                    (compiled.semiNaiveConsequenceListForHeadWithInputCore
                      I input S Y) =
                  freshTuples (S.current.lookupTuples Y hY)
                    (compiled.semiNaiveConsequenceListForHeadWithInputCore
                      I input S Y) :=
              freshTuplesUsingIndex_eq
                (S.current.lookupMemberIndex Y hY)
                (S.current.lookupTuples Y hY)
                (compiled.semiNaiveConsequenceListForHeadWithInputCore
                  I input S Y)
                (fun t =>
                  MaterializedIDB.mem_lookupMemberIndex_iff
                    S.current Y hY t)
            simp [stepRelationUpdateWithInput, hFresh]
      · have hUpdate :
            (stepRelationUpdateWithInput compiled I input S Y).sym.1 ≠
              X := by
          intro h
          exact hYX h
        rw [dif_neg hUpdate]
        have hMemTail :
            (⟨X, hX⟩ : P.IDBSym) ∈ Ys := by
          rcases List.mem_cons.mp hMem with hEq | hTail
          · cases hEq
            exact False.elim (hYX rfl)
          · exact hTail
        exact ih hMemTail

theorem lookupDeltaUpdateTuples_stepRelationUpdatesWithInput
    {P : Program D Γ}
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema)
    (input : MaterializedInput P I)
    (S : SemiNaiveState P)
    (X : Γ.syms)
    (hX : X ∈ P.idb) :
    lookupDeltaUpdateTuples
        (stepRelationUpdatesWithInput compiled I input S) X hX =
      freshTuples (S.current.lookupTuples X hX)
        (compiled.semiNaiveConsequenceListForHeadWithInputCore
          I input S X) := by
  unfold stepRelationUpdatesWithInput
  apply lookupDeltaUpdateTuples_map_stepRelationUpdateWithInput
  exact idbSymList_mem_of_idb_for_updates hX

set_option linter.flexible false in
private theorem lookupDeltaUpdateTuples_map_stepRelationUpdate
    {P : Program D Γ}
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (X : Γ.syms)
    (hX : X ∈ P.idb)
    (xs : List P.IDBSym)
    (hMem : (⟨X, hX⟩ : P.IDBSym) ∈ xs) :
    lookupDeltaUpdateTuples
        (xs.map (fun Y => stepRelationUpdate compiled I S Y))
        X hX =
      freshTuples (S.current.lookupTuples X hX)
        (compiled.semiNaiveConsequenceListForHead I S X) := by
  simpa [stepRelationUpdate,
    CompiledProgram.semiNaiveConsequenceListForHead] using
    lookupDeltaUpdateTuples_map_stepRelationUpdateWithInput
      compiled I (P.materializeInput I) S X hX xs hMem

theorem lookupDeltaUpdateTuples_stepRelationUpdates
    {P : Program D Γ}
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (X : Γ.syms)
    (hX : X ∈ P.idb) :
    lookupDeltaUpdateTuples
        (stepRelationUpdates compiled I S) X hX =
      freshTuples (S.current.lookupTuples X hX)
        (compiled.semiNaiveConsequenceListForHead I S X) := by
  unfold stepRelationUpdates
  apply lookupDeltaUpdateTuples_map_stepRelationUpdate
  exact idbSymList_mem_of_idb_for_updates hX

/- One semi-naive step using a materialized input cache. -/
def snStepWithInput
    {P : Program D Γ}
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema)
    (input : MaterializedInput P I)
    (S : SemiNaiveState P) :
    SemiNaiveState P :=
  let updates := stepRelationUpdatesWithInput compiled I input S
  { current := currentIdbOfStepUpdates updates
    delta := deltaIdbOfStepUpdates updates }

/- One semi-naive step using a precompiled program. -/
def semiNaiveStepWith
    {P : Program D Γ}
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P) :
    SemiNaiveState P :=
  P.snStepWithInput compiled I (P.materializeInput I) S

/- One semi-naive step using the program's compiled rules. -/
def semiNaiveStep
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P) :
    SemiNaiveState P :=
  P.semiNaiveStepWith P.compile I S

/-
  Cheap fact-capacity fuel bound over the input active
  domain.
-/
def semiNaiveFuel
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    Nat :=
  P.idbList.foldl
    (fun acc X => acc + (P.adom I).card ^ Γ.arity X)
    0 + 1

/-
  Total semi-naive iteration with a cheap fact-capacity
  fuel.
-/
def snIterateWithInput
    {P : Program D Γ}
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema)
    (input : MaterializedInput P I) :
    Nat → SemiNaiveState P → SemiNaiveState P
| 0, S => S
| n + 1, S =>
    if S.deltaEmpty then
      S
    else
      P.snIterateWithInput compiled I input n
        (P.snStepWithInput compiled I input S)

def semiNaiveIterateWith
    {P : Program D Γ}
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema) :
    Nat → SemiNaiveState P → SemiNaiveState P :=
  P.snIterateWithInput compiled I (P.materializeInput I)

def semiNaiveIterate
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    Nat → SemiNaiveState P → SemiNaiveState P :=
  P.semiNaiveIterateWith P.compile I

/- Optimized semi-naive fixed-point state from explicit phases. -/
def snLFPStateWithInput
    (P : Program D Γ)
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema) :
    MaterializedInput P I →
    SemiNaiveState P :=
  fun input =>
  P.snIterateWithInput compiled I input
    (P.semiNaiveFuel I)
    (P.snInitialStateWithInput compiled I input)

/- Optimized semi-naive fixed-point state. -/
def snLFPState
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    SemiNaiveState P :=
  let compiled := P.compileForSN
  let input := P.materializeInput I
  P.snLFPStateWithInput compiled I input

/- Reify a materialized semi-naive state as an instance. -/
def reifySNOutput
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P) :
    Instance D Γ :=
  S.toInstance I

/- Optimized semi-naive fixed-point instance. -/
def snLFP
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    Instance D Γ :=
  P.reifySNOutput I (P.snLFPState I)

/-
  Temporary compatibility alias for the optimized semi-
  naive state.
-/
abbrev semiNaiveLFPState
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    SemiNaiveState P :=
  P.snLFPState I

/-
  Temporary compatibility alias for the optimized semi-
  naive instance.
-/
abbrev semiNaiveLFP
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    Instance D Γ :=
  P.snLFP I

end Program

end Datalog

------------------------------------------------------------
-- Query API
------------------------------------------------------------

namespace Datalog

namespace Query

variable {A D : Type}
variable [RelationNames A] [Domain D] [LinearOrder D] [Hashable D]
variable {Γ : UnnamedSchema A}

/- Query answer tuples from the materialized semi-naive state. -/
def snAnswerTuples
    (q : Query D Γ n)
    (I : Instance D q.program.edbSchema) :
    List (Tuple D n) :=
  cast (congrArg (fun k => List (Tuple D k)) q.arity)
    ((q.program.snLFPState I).current.lookupTuples
      q.output.val q.output.property)

/- Query answer tuple count from the materialized semi-naive state. -/
def snAnswerTupleCount
    (q : Query D Γ n)
    (I : Instance D q.program.edbSchema) :
    Nat :=
  (q.snAnswerTuples I).length

/- Query answer from the optimized semi-naive evaluator. -/
def snAnswer
    (q : Query D Γ n)
    (I : Instance D q.program.edbSchema) :
    FinRelation D n :=
  q.outputRelation (q.program.snLFP I)

/-
  Temporary compatibility alias for the optimized semi-
  naive answer.
-/
abbrev semiNaiveAnswer
    (q : Query D Γ n)
    (I : Instance D q.program.edbSchema) :
    FinRelation D n :=
  q.snAnswer I

end Query

end Datalog

------------------------------------------------------------
-- Partial Assignment Correctness Helpers
------------------------------------------------------------

namespace Datalog

namespace PartialAssign

variable {D : Type} [Domain D]

/-
  A partial assignment extends another when it preserves
  all existing bindings.
-/
def Extends (ρ' ρ : PartialAssign D) : Prop :=
  ∀ x d, lookup ρ x = some d → lookup ρ' x = some d

/-
  A partial assignment is consistent with a total
  assignment when every stored binding has the total
  assignment's value.
-/
def ConsistentWith
    (ρ : PartialAssign D)
    (σ : Assign D) : Prop :=
  ∀ x d, lookup ρ x = some d → d = σ x

/-
  A partial assignment agrees with a total assignment on a
  finite list of variables when all of them are bound.
-/
def AgreesOn
    (ρ : PartialAssign D)
    (σ : Assign D)
    (xs : List Var) : Prop :=
  ∀ x, x ∈ xs → lookup ρ x = some (σ x)

omit [Domain D] in
theorem Extends.refl
    (ρ : PartialAssign D) :
    Extends ρ ρ := by
  intro x d h
  exact h

omit [Domain D] in
theorem Extends.trans
    {ρ₂ ρ₁ ρ₀ : PartialAssign D}
    (h₂₁ : Extends ρ₂ ρ₁)
    (h₁₀ : Extends ρ₁ ρ₀) :
    Extends ρ₂ ρ₀ := by
  intro x d h
  exact h₂₁ x d (h₁₀ x d h)

omit [Domain D] in
theorem ConsistentWith.nil
    (σ : Assign D) :
    ConsistentWith ([] : PartialAssign D) σ := by
  intro x d h
  simp [lookup] at h

omit [Domain D] in
theorem Extends.consistentWith
    {ρ ρ' : PartialAssign D}
    {σ : Assign D}
    (hExt : Extends ρ' ρ)
    (hCons : ConsistentWith ρ' σ) :
    ConsistentWith ρ σ := by
  intro x d hLookup
  exact hCons x d (hExt x d hLookup)

theorem AgreesOn.toAssign_eq
    {ρ : PartialAssign D}
    {σ : Assign D}
    {xs : List Var}
    (hAgree : AgreesOn ρ σ xs)
    {x : Var}
    (hx : x ∈ xs) :
    toAssign ρ x = σ x := by
  have hLookup := hAgree x hx
  simp [toAssign, hLookup]

omit [Domain D] in
theorem AgreesOn.mono_extends
    {ρ ρ' : PartialAssign D}
    {σ : Assign D}
    {xs : List Var}
    (hExt : Extends ρ' ρ)
    (hAgree : AgreesOn ρ σ xs) :
    AgreesOn ρ' σ xs := by
  intro x hx
  exact hExt x (σ x) (hAgree x hx)

theorem lookup_bind_self
    {ρ ρ' : PartialAssign D}
    {x : Var} {d : D}
    (hBind : bind ρ x d = some ρ') :
    lookup ρ' x = some d := by
  unfold bind at hBind
  cases hLookup : lookup ρ x with
  | none =>
      rw [hLookup] at hBind
      change some ((x, d) :: ρ) = some ρ' at hBind
      cases hBind
      simp [lookup]
  | some d' =>
      rw [hLookup] at hBind
      change (if d' = d then some ρ else none) =
        some ρ' at hBind
      by_cases hEq : d' = d
      · rw [if_pos hEq] at hBind
        cases hBind
        simpa [hEq] using hLookup
      · rw [if_neg hEq] at hBind
        cases hBind

theorem bind_extends
    {ρ ρ' : PartialAssign D}
    {x : Var} {d : D}
    (hBind : bind ρ x d = some ρ') :
    Extends ρ' ρ := by
  unfold bind at hBind
  cases hLookup : lookup ρ x with
  | none =>
      rw [hLookup] at hBind
      change some ((x, d) :: ρ) = some ρ' at hBind
      cases hBind
      intro y e hy
      by_cases hxy : x = y
      · subst hxy
        rw [hLookup] at hy
        cases hy
      · simpa [lookup, hxy] using hy
  | some d' =>
      rw [hLookup] at hBind
      change (if d' = d then some ρ else none) =
        some ρ' at hBind
      by_cases hEq : d' = d
      · rw [if_pos hEq] at hBind
        cases hBind
        exact Extends.refl ρ
      · rw [if_neg hEq] at hBind
        cases hBind

theorem lookup_bind_eq
    {ρ ρ' : PartialAssign D}
    {x y : Var} {d : D}
    (hBind : bind ρ x d = some ρ') :
    lookup ρ' y =
      if y = x then some d else lookup ρ y := by
  unfold bind at hBind
  cases hLookup : lookup ρ x with
  | none =>
      rw [hLookup] at hBind
      change some ((x, d) :: ρ) = some ρ' at hBind
      cases hBind
      by_cases hyx : y = x
      · subst hyx
        simp [lookup]
      · have hxy : x ≠ y := by
          intro h
          exact hyx h.symm
        simp [lookup, hyx, hxy]
  | some d' =>
      rw [hLookup] at hBind
      change (if d' = d then some ρ else none) =
        some ρ' at hBind
      by_cases hEq : d' = d
      · rw [if_pos hEq] at hBind
        cases hBind
        by_cases hyx : y = x
        · subst hyx
          simp [hLookup, hEq]
        · simp [hyx]
      · rw [if_neg hEq] at hBind
        cases hBind

theorem bind_consistentWith
    {ρ ρ' : PartialAssign D}
    {σ : Assign D}
    {x : Var} {d : D}
    (hCons : ConsistentWith ρ σ)
    (hd : d = σ x)
    (hBind : bind ρ x d = some ρ') :
    ConsistentWith ρ' σ := by
  unfold bind at hBind
  cases hLookup : lookup ρ x with
  | none =>
      rw [hLookup] at hBind
      change some ((x, d) :: ρ) = some ρ' at hBind
      cases hBind
      intro y e hy
      by_cases hxy : x = y
      · subst hxy
        simp [lookup] at hy
        exact hy.symm.trans hd
      · have hyρ : lookup ρ y = some e := by
          simpa [lookup, hxy] using hy
        exact hCons y e hyρ
  | some d' =>
      rw [hLookup] at hBind
      change (if d' = d then some ρ else none) =
        some ρ' at hBind
      by_cases hEq : d' = d
      · rw [if_pos hEq] at hBind
        cases hBind
        exact hCons
      · rw [if_neg hEq] at hBind
        cases hBind

theorem evalTerm?_some_eval
    {ρ : PartialAssign D}
    {term : RelTerm D}
    {d : D}
    (hEval : evalTerm? ρ term = some d) :
    term.eval (toAssign ρ) = d := by
  cases term with
  | var x =>
      have hLookup : lookup ρ x = some d := by
        simpa [evalTerm?] using hEval
      simp [toAssign, RelTerm.eval, hLookup]
  | const c =>
      simpa [evalTerm?, RelTerm.eval] using hEval

theorem evalTerm?_some_eval_of_extends
    {ρ ρ' : PartialAssign D}
    {term : RelTerm D}
    {d : D}
    (hExt : Extends ρ' ρ)
    (hEval : evalTerm? ρ term = some d) :
    term.eval (toAssign ρ') = d := by
  cases term with
  | var x =>
      have hLookup : lookup ρ' x = some d :=
        hExt x d (by simpa [evalTerm?] using hEval)
      simp [toAssign, RelTerm.eval, hLookup]
  | const c =>
      simpa [evalTerm?, RelTerm.eval] using hEval

end PartialAssign

end Datalog

------------------------------------------------------------
-- Semi-Naive Representation Predicates
------------------------------------------------------------

namespace Datalog

namespace Program

variable {A D : Type}
variable [RelationNames A] [Domain D] [LinearOrder D] [Hashable D]
variable {Γ : UnnamedSchema A}

namespace MaterializedIDB

/-
  A materialized IDB state represents an ordinary program
  instance when converting it back to an instance view
  yields that instance.
-/
structure RepresentsInstance
    {P : Program D Γ}
    (S : MaterializedIDB P)
    (I : Instance D P.edbSchema)
    (J : Instance D Γ) : Prop where
  toInstance_eq : S.toInstance I = J

end MaterializedIDB

namespace SemiNaiveState

/-
  A semi-naive state represents one naive immediate step
  from `prev` to `curr`, with `delta` storing exactly the
  newly added IDB facts.
-/
structure RepresentsStep
    {P : Program D Γ}
    (S : SemiNaiveState P)
    (I : Instance D P.edbSchema)
    (prev curr : Instance D Γ) : Prop where
  toInstance_eq :
    S.toInstance I = curr
  curr_eq_immediate :
    curr = P.immediateOnInputAdom I prev
  delta_eq :
    ∀ (X : Γ.syms) (hX : X ∈ P.idb),
      S.delta.lookup X hX = curr X \ prev X
  prev_subset_curr :
    Instance.Subset prev curr
  prev_bounded :
    Instance.BoundedByValues (P.adom I) prev
  curr_bounded :
    Instance.BoundedByValues (P.adom I) curr

end SemiNaiveState

end Program

end Datalog

------------------------------------------------------------
-- Indexed Body Semantics
------------------------------------------------------------

namespace Datalog

namespace Program

variable {A D : Type}
variable [RelationNames A] [Domain D] [LinearOrder D] [Hashable D]
variable {Γ : UnnamedSchema A}

/-
  Semantic body satisfaction for the semi-naive evaluator
  with an optional selected delta body-atom position. The
  `idx` parameter tracks the current body position.
-/
def BodySatWithDelta
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat) :
    Nat → List (Atom D Γ) → Assign D → Prop
| _idx, [], _σ => True
| idx, b :: body, σ =>
    match b with
    | .rel a =>
        a.evalTuple σ ∈
          P.atomRelationFor I S deltaAt? idx a ∧
        BodySatWithDelta P I S deltaAt? (idx + 1)
          body σ
    | .eq lhs rhs =>
        lhs.eval σ = rhs.eval σ ∧
        BodySatWithDelta P I S deltaAt? (idx + 1)
          body σ

/-
  Relational-atom-only body satisfaction for the executable
  tuple join. Equality atoms are checked by a separate
  Boolean filter in `bodyAssignments`.
-/
def RelBodySatWithDelta
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat) :
    Nat → List (Atom D Γ) → Assign D → Prop
| _idx, [], _σ => True
| idx, b :: body, σ =>
    match b with
    | .rel a =>
        a.evalTuple σ ∈
          P.atomRelationFor I S deltaAt? idx a ∧
        RelBodySatWithDelta P I S deltaAt? (idx + 1)
          body σ
    | .eq _lhs _rhs =>
        RelBodySatWithDelta P I S deltaAt? (idx + 1)
          body σ

/- Semantic satisfaction of one indexed relational entry. -/
def RelEntrySatWithDelta
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (entry : Nat × RelAtom D Γ)
    (σ : Assign D) :
    Prop :=
  entry.2.evalTuple σ ∈
    P.atomRelationFor I S deltaAt? entry.1 entry.2

/- Semantic satisfaction of a list of relational entries. -/
def RelEntriesSatWithDelta
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (entries : List (Nat × RelAtom D Γ))
    (σ : Assign D) :
    Prop :=
  ∀ entry : Nat × RelAtom D Γ,
    entry ∈ entries →
      RelEntrySatWithDelta P I S deltaAt? entry σ

end Program

end Datalog

------------------------------------------------------------
-- Tuple Join Soundness And Completeness
------------------------------------------------------------

namespace Datalog

namespace Program

variable {A D : Type}
variable [RelationNames A] [Domain D] [LinearOrder D] [Hashable D]
variable {Γ : UnnamedSchema A}

omit [LinearOrder D] in
theorem matchTerm_extends
    (ρ ρ' : PartialAssign D)
    (term : RelTerm D)
    (d : D)
    (hMatch : matchTerm ρ term d = some ρ') :
    PartialAssign.Extends ρ' ρ := by
  cases term with
  | var x =>
      exact PartialAssign.bind_extends hMatch
  | const c =>
      unfold matchTerm at hMatch
      change (if c = d then some ρ else none) =
        some ρ' at hMatch
      by_cases hEq : c = d
      · rw [if_pos hEq] at hMatch
        cases hMatch
        exact PartialAssign.Extends.refl ρ
      · rw [if_neg hEq] at hMatch
        cases hMatch

omit [LinearOrder D] in
theorem matchTerm_eval_of_extends
    (ρ ρ' ρ'' : PartialAssign D)
    (term : RelTerm D)
    (d : D)
    (hMatch : matchTerm ρ term d = some ρ')
    (hExt : PartialAssign.Extends ρ'' ρ') :
    term.eval (PartialAssign.toAssign ρ'') = d := by
  cases term with
  | var x =>
      have hLookupρ' :
          PartialAssign.lookup ρ' x = some d :=
        PartialAssign.lookup_bind_self hMatch
      have hLookupρ'' :
          PartialAssign.lookup ρ'' x = some d :=
        hExt x d hLookupρ'
      simp [PartialAssign.toAssign, RelTerm.eval, hLookupρ'']
  | const c =>
      unfold matchTerm at hMatch
      by_cases hEq : c = d
      · simp [hEq] at hMatch
        simp [RelTerm.eval, hEq]
      · simp [hEq] at hMatch

omit [LinearOrder D] in
theorem bind_complete
    {ρ : PartialAssign D}
    {σ : Assign D}
    (hCons : PartialAssign.ConsistentWith ρ σ)
    (x : Var) :
    ∃ ρ' : PartialAssign D,
      PartialAssign.bind ρ x (σ x) = some ρ' ∧
        PartialAssign.ConsistentWith ρ' σ ∧
        PartialAssign.Extends ρ' ρ ∧
        PartialAssign.lookup ρ' x = some (σ x) := by
  unfold PartialAssign.bind
  cases hLookup : PartialAssign.lookup ρ x with
  | none =>
      refine ⟨(x, σ x) :: ρ, by simp, ?_, ?_, ?_⟩
      · intro y d hy
        by_cases hxy : x = y
        · subst hxy
          simp [PartialAssign.lookup] at hy
          exact hy.symm
        · have hyρ :
              PartialAssign.lookup ρ y = some d := by
            simpa [PartialAssign.lookup, hxy] using hy
          exact hCons y d hyρ
      · intro y d hy
        by_cases hxy : x = y
        · subst hxy
          rw [hLookup] at hy
          cases hy
        · simpa [PartialAssign.lookup, hxy] using hy
      · simp [PartialAssign.lookup]
  | some d =>
      have hd : d = σ x := hCons x d hLookup
      refine ⟨ρ, ?_, ?_, ?_, ?_⟩
      · simp [hd]
      · exact hCons
      · exact PartialAssign.Extends.refl ρ
      · simpa [hd] using hLookup

omit [LinearOrder D] in
theorem matchTerm_complete
    (ρ : PartialAssign D)
    (σ : Assign D)
    (term : RelTerm D)
    (hCons : PartialAssign.ConsistentWith ρ σ) :
    ∃ ρ' : PartialAssign D,
      matchTerm ρ term (term.eval σ) = some ρ' ∧
        PartialAssign.ConsistentWith ρ' σ ∧
        PartialAssign.Extends ρ' ρ ∧
        (∀ x : Var,
          term.var? = some x →
            PartialAssign.lookup ρ' x = some (σ x)) := by
  cases term with
  | var x =>
      rcases bind_complete hCons x with
        ⟨ρ', hBind, hCons', hExt, hLookup⟩
      exact
        ⟨ρ', by simpa [matchTerm, RelTerm.eval] using hBind,
          hCons', hExt, by
            intro y hy
            cases hy
            exact hLookup⟩
  | const c =>
      exact
        ⟨ρ, by simp [matchTerm, RelTerm.eval],
          hCons, PartialAssign.Extends.refl ρ, by
            intro x hx
            simp [RelTerm.var?] at hx⟩

omit [LinearOrder D] in
theorem matchTerms_complete
    {ρ : PartialAssign D}
    {σ : Assign D} :
    ∀ (terms : List (RelTerm D))
      (_ : PartialAssign.ConsistentWith ρ σ),
      ∃ ρ' : PartialAssign D,
        matchTerms ρ terms
            (terms.map (fun term => term.eval σ)) =
          some ρ' ∧
          PartialAssign.ConsistentWith ρ' σ ∧
          PartialAssign.Extends ρ' ρ ∧
          PartialAssign.AgreesOn ρ' σ
            (terms.filterMap RelTerm.var?)
| [], hCons => by
    exact
      ⟨ρ, by simp [matchTerms], hCons,
        PartialAssign.Extends.refl ρ, by
          intro x hx
          simp at hx⟩
| term :: terms, hCons => by
    rcases matchTerm_complete ρ σ term hCons with
      ⟨ρ₁, hTerm, hCons₁, hExt₁, hTermAgree⟩
    rcases
      matchTerms_complete
        (ρ := ρ₁) (σ := σ) terms hCons₁ with
      ⟨ρ₂, hTail, hCons₂, hExt₂, hTailAgree⟩
    refine
      ⟨ρ₂, ?_, hCons₂, hExt₂.trans hExt₁, ?_⟩
    · simp [matchTerms, hTerm, hTail]
    · intro x hx
      rcases List.mem_filterMap.mp hx with
        ⟨term', hMem, hVar⟩
      rcases List.mem_cons.mp hMem with hHead | hTailMem
      · subst hHead
        exact hExt₂ x (σ x) (hTermAgree x hVar)
      · exact
          hTailAgree x
            (List.mem_filterMap.mpr
              ⟨term', hTailMem, hVar⟩)

omit [LinearOrder D] in
theorem extendWithAtomRow_complete
    (ρ : PartialAssign D)
    (σ : Assign D)
    (a : RelAtom D Γ)
    (hCons : PartialAssign.ConsistentWith ρ σ) :
    ∃ ρ' : PartialAssign D,
      extendWithAtomRow ρ a (a.evalTuple σ) = some ρ' ∧
        PartialAssign.ConsistentWith ρ' σ ∧
        PartialAssign.Extends ρ' ρ ∧
        PartialAssign.AgreesOn ρ' σ a.varList := by
  unfold extendWithAtomRow
  rcases matchTerms_complete
      (ρ := ρ) (σ := σ) a.args.toList hCons with
    ⟨ρ', hMatch, hCons', hExt, hAgree⟩
  refine ⟨ρ', ?_, hCons', hExt, ?_⟩
  · simpa [RelAtom.evalTuple_toList] using hMatch
  · simpa [RelAtom.varList] using hAgree

omit [LinearOrder D] in
theorem matchTerms_extends
    {ρ ρ' : PartialAssign D} :
    ∀ (terms : List (RelTerm D)) (ds : List D),
      matchTerms ρ terms ds = some ρ' →
        PartialAssign.Extends ρ' ρ
| [], [], hMatch => by
    unfold matchTerms at hMatch
    cases hMatch
    exact PartialAssign.Extends.refl ρ
| [], _d :: _ds, hMatch => by
    unfold matchTerms at hMatch
    cases hMatch
| _term :: _terms, [], hMatch => by
    unfold matchTerms at hMatch
    cases hMatch
| term :: terms, d :: ds, hMatch => by
    unfold matchTerms at hMatch
    cases hStep : matchTerm ρ term d with
    | none =>
        simp [hStep] at hMatch
    | some ρ₁ =>
        have hTail :
            PartialAssign.Extends ρ' ρ₁ :=
          matchTerms_extends
            (ρ := ρ₁) (ρ' := ρ') terms ds
            (by simpa [hStep] using hMatch)
        have hHead :
            PartialAssign.Extends ρ₁ ρ :=
          matchTerm_extends ρ ρ₁ term d hStep
        exact hTail.trans hHead

omit [LinearOrder D] in
theorem matchTerms_map_eval_of_extends
    {ρ ρ' ρ'' : PartialAssign D} :
    ∀ (terms : List (RelTerm D)) (ds : List D),
      matchTerms ρ terms ds = some ρ' →
        PartialAssign.Extends ρ'' ρ' →
          terms.map (fun term =>
            term.eval (PartialAssign.toAssign ρ'')) = ds
| [], [], hMatch, _hExt => by
    rfl
| [], _d :: _ds, hMatch, _hExt => by
    unfold matchTerms at hMatch
    cases hMatch
| _term :: _terms, [], hMatch, _hExt => by
    unfold matchTerms at hMatch
    cases hMatch
| term :: terms, d :: ds, hMatch, hExt => by
    unfold matchTerms at hMatch
    cases hStep : matchTerm ρ term d with
    | none =>
        simp [hStep] at hMatch
    | some ρ₁ =>
        have hTailMatch :
            matchTerms ρ₁ terms ds = some ρ' := by
          simpa [hStep] using hMatch
        have hρ'Extρ₁ :
            PartialAssign.Extends ρ' ρ₁ :=
          matchTerms_extends
            (ρ := ρ₁) (ρ' := ρ') terms ds
            hTailMatch
        have hρ''Extρ₁ :
            PartialAssign.Extends ρ'' ρ₁ :=
          hExt.trans hρ'Extρ₁
        have hHead :
            term.eval (PartialAssign.toAssign ρ'') = d :=
          matchTerm_eval_of_extends ρ ρ₁ ρ'' term d
            hStep hρ''Extρ₁
        have hTail :
            terms.map
                (fun term =>
                  term.eval (PartialAssign.toAssign ρ'')) =
              ds :=
          matchTerms_map_eval_of_extends
            (ρ := ρ₁) (ρ' := ρ') (ρ'' := ρ'')
            terms ds hTailMatch hExt
        simp [hHead, hTail]

omit [LinearOrder D] in
theorem extendWithAtomRow_extends
    (ρ ρ' : PartialAssign D)
    (a : RelAtom D Γ)
    (t : Tuple D (Γ.arity a.rel))
    (hExtend : extendWithAtomRow ρ a t = some ρ') :
    PartialAssign.Extends ρ' ρ := by
  unfold extendWithAtomRow at hExtend
  exact matchTerms_extends a.args.toList t.toList hExtend

omit [LinearOrder D] in
theorem extendWithAtomRow_evalTuple_of_extends
    (ρ ρ' ρ'' : PartialAssign D)
    (a : RelAtom D Γ)
    (t : Tuple D (Γ.arity a.rel))
    (hExtend : extendWithAtomRow ρ a t = some ρ')
    (hExt : PartialAssign.Extends ρ'' ρ') :
    a.evalTuple (PartialAssign.toAssign ρ'') = t := by
  apply Vector.toList_inj.mp
  unfold extendWithAtomRow at hExtend
  have hList :=
    matchTerms_map_eval_of_extends
      (ρ := ρ) (ρ' := ρ') (ρ'' := ρ'')
      a.args.toList t.toList hExtend hExt
  simpa [RelAtom.evalTuple_toList] using hList

omit [LinearOrder D] in
theorem boundColumn_get_eq_of_extend
    (ρ ρ' : PartialAssign D)
    (a : RelAtom D Γ)
    (t : Tuple D (Γ.arity a.rel))
    (column : BoundColumn ρ a)
    (hExtend : extendWithAtomRow ρ a t = some ρ') :
    t.get column.index = column.value := by
  have hρ'Extρ :
      PartialAssign.Extends ρ' ρ :=
    extendWithAtomRow_extends ρ ρ' a t hExtend
  have hEval :
      (a.args.get column.index).eval
          (PartialAssign.toAssign ρ') =
        column.value :=
    PartialAssign.evalTerm?_some_eval_of_extends
      hρ'Extρ column.eval_eq
  have hTuple :
      a.evalTuple (PartialAssign.toAssign ρ') = t :=
    extendWithAtomRow_evalTuple_of_extends
      ρ ρ' ρ' a t hExtend
      (PartialAssign.Extends.refl ρ')
  have hCoord :
      (a.evalTuple (PartialAssign.toAssign ρ')).get
          column.index =
        (a.args.get column.index).eval
          (PartialAssign.toAssign ρ') := by
    simp [RelAtom.evalTuple, RelTerm.evalVector,
      Vector.get]
  rw [← hTuple, hCoord, hEval]

theorem mem_optionToFinset_iff
    {α : Type} [DecidableEq α]
    {o : Option α} {a : α} :
    a ∈ optionToFinset o ↔ o = some a := by
  cases o <;> simp [optionToFinset, eq_comm]

theorem joinRelAtomsFrom_sound
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat) :
    ∀ (idx : Nat) (body : List (Atom D Γ))
      (assignments : Finset (PartialAssign D))
      {ρ : PartialAssign D},
      ρ ∈ P.joinRelAtomsFrom I S deltaAt? idx body
          assignments →
        ∃ ρ₀ : PartialAssign D,
          ρ₀ ∈ assignments ∧
            PartialAssign.Extends ρ ρ₀ ∧
              RelBodySatWithDelta P I S deltaAt? idx body
                (PartialAssign.toAssign ρ)
| _idx, [], assignments, ρ, hρ => by
    exact
      ⟨ρ, hρ, PartialAssign.Extends.refl ρ, trivial⟩
| idx, b :: body, assignments, ρ, hρ => by
    cases b with
    | rel a =>
        unfold joinRelAtomsFrom at hρ
        rcases
          joinRelAtomsFrom_sound P I S deltaAt?
            (idx + 1) body
            (P.extendAssignmentsWithAtom
              I S deltaAt? idx assignments a)
            hρ with
          ⟨ρ₁, hρ₁, hρExtρ₁, hTail⟩
        unfold extendAssignmentsWithAtom at hρ₁
        rw [Finset.mem_biUnion] at hρ₁
        rcases hρ₁ with ⟨ρ₀, hρ₀, hρ₁⟩
        rw [Finset.mem_biUnion] at hρ₁
        rcases hρ₁ with ⟨t, ht, hOpt⟩
        have hExtend :
            extendWithAtomRow ρ₀ a t = some ρ₁ :=
          mem_optionToFinset_iff.mp hOpt
        have hρ₁Extρ₀ :
            PartialAssign.Extends ρ₁ ρ₀ :=
          extendWithAtomRow_extends ρ₀ ρ₁ a t hExtend
        have hρExtρ₀ :
            PartialAssign.Extends ρ ρ₀ :=
          hρExtρ₁.trans hρ₁Extρ₀
        have hAtomEq :
            a.evalTuple (PartialAssign.toAssign ρ) = t :=
          extendWithAtomRow_evalTuple_of_extends
            ρ₀ ρ₁ ρ a t hExtend hρExtρ₁
        have hAtom :
            a.evalTuple (PartialAssign.toAssign ρ) ∈
              P.atomRelationFor I S deltaAt? idx a := by
          simpa [hAtomEq] using ht
        exact
          ⟨ρ₀, hρ₀, hρExtρ₀, hAtom, hTail⟩
    | eq lhs rhs =>
        unfold joinRelAtomsFrom at hρ
        rcases
          joinRelAtomsFrom_sound P I S deltaAt?
            (idx + 1) body assignments hρ with
          ⟨ρ₀, hρ₀, hExt, hTail⟩
        exact ⟨ρ₀, hρ₀, hExt, hTail⟩

theorem BodySatWithDelta.rel
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (σ : Assign D) :
    ∀ (idx : Nat) (body : List (Atom D Γ)),
      BodySatWithDelta P I S deltaAt? idx body σ →
        RelBodySatWithDelta P I S deltaAt? idx body σ
| _idx, [], _hBody => trivial
| idx, b :: body, hBody => by
    cases b with
    | rel a =>
        exact
          ⟨hBody.1,
            BodySatWithDelta.rel P I S deltaAt? σ
              (idx + 1) body hBody.2⟩
    | eq lhs rhs =>
        exact
          BodySatWithDelta.rel P I S deltaAt? σ
            (idx + 1) body hBody.2

theorem joinRelAtomsFrom_complete
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat) :
    ∀ (idx : Nat) (body : List (Atom D Γ))
      (assignments : Finset (PartialAssign D))
      (σ : Assign D) (ρ₀ : PartialAssign D),
      ρ₀ ∈ assignments →
        PartialAssign.ConsistentWith ρ₀ σ →
        RelBodySatWithDelta P I S deltaAt? idx body σ →
          ∃ ρ : PartialAssign D,
            ρ ∈ P.joinRelAtomsFrom I S deltaAt? idx
                body assignments ∧
              PartialAssign.ConsistentWith ρ σ ∧
              PartialAssign.Extends ρ ρ₀ ∧
              PartialAssign.AgreesOn ρ σ
                (Body.relVarList body)
| _idx, [], assignments, σ, ρ₀, hρ₀, hCons,
    _hRel => by
    exact
      ⟨ρ₀, hρ₀, hCons,
        PartialAssign.Extends.refl ρ₀,
        by
          intro x hx
          simp [Body.relVarList, Atom.listRelVarList] at hx⟩
| idx, b :: body, assignments, σ, ρ₀, hρ₀,
    hCons, hRel => by
    cases b with
    | rel a =>
        rcases hRel with ⟨hAtom, hTailRel⟩
        rcases extendWithAtomRow_complete
            ρ₀ σ a hCons with
          ⟨ρ₁, hExtend, hCons₁,
            hExt₁, hAtomAgree⟩
        have hρ₁ :
            ρ₁ ∈ P.extendAssignmentsWithAtom
              I S deltaAt? idx assignments a := by
          unfold extendAssignmentsWithAtom
          rw [Finset.mem_biUnion]
          refine ⟨ρ₀, hρ₀, ?_⟩
          rw [Finset.mem_biUnion]
          refine ⟨a.evalTuple σ, hAtom, ?_⟩
          exact mem_optionToFinset_iff.mpr hExtend
        rcases
          joinRelAtomsFrom_complete P I S deltaAt?
            (idx + 1) body
            (P.extendAssignmentsWithAtom
              I S deltaAt? idx assignments a)
            σ ρ₁ hρ₁ hCons₁ hTailRel with
          ⟨ρ, hρ, hConsρ, hExtρ₁, hTailAgree⟩
        refine
          ⟨ρ, ?_, hConsρ, hExtρ₁.trans hExt₁, ?_⟩
        · simpa [joinRelAtomsFrom] using hρ
        · intro x hx
          have hx' :
              x ∈ a.varList ∨
                x ∈ Body.relVarList body := by
            simpa [Body.relVarList, Atom.listRelVarList,
              Atom.relVarList]
              using hx
          rcases hx' with hxAtom | hxTail
          · exact hExtρ₁ x (σ x) (hAtomAgree x hxAtom)
          · exact hTailAgree x hxTail
    | eq lhs rhs =>
        rcases
          joinRelAtomsFrom_complete P I S deltaAt?
            (idx + 1) body assignments σ ρ₀
            hρ₀ hCons hRel with
          ⟨ρ, hρ, hConsρ, hExtρ₀, hAgree⟩
        refine ⟨ρ, ?_, hConsρ, hExtρ₀, ?_⟩
        · simpa [joinRelAtomsFrom] using hρ
        · intro x hx
          exact hAgree x
            (by
              simpa [Body.relVarList,
                Atom.relVarList]
                using hx)

omit [LinearOrder D] in
theorem equalityHolds_sound
    (ρ : PartialAssign D)
    (lhs rhs : RelTerm D)
    (hEq : equalityHolds ρ lhs rhs = true) :
    lhs.eval (PartialAssign.toAssign ρ) =
      rhs.eval (PartialAssign.toAssign ρ) := by
  unfold equalityHolds at hEq
  cases hL : PartialAssign.evalTerm? ρ lhs with
  | none =>
      simp [hL] at hEq
  | some dL =>
      cases hR : PartialAssign.evalTerm? ρ rhs with
      | none =>
          simp [hL, hR] at hEq
      | some dR =>
          simp [hL, hR] at hEq
          have hL' :
              lhs.eval (PartialAssign.toAssign ρ) = dL :=
            PartialAssign.evalTerm?_some_eval hL
          have hR' :
              rhs.eval (PartialAssign.toAssign ρ) = dR :=
            PartialAssign.evalTerm?_some_eval hR
          simpa [hL', hR'] using hEq

theorem equalitiesHold_sound
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (ρ : PartialAssign D) :
    ∀ (idx : Nat) (body : List (Atom D Γ)),
      equalitiesHold ρ body = true →
        RelBodySatWithDelta P I S deltaAt? idx body
          (PartialAssign.toAssign ρ) →
          BodySatWithDelta P I S deltaAt? idx body
            (PartialAssign.toAssign ρ)
| _idx, [], _hEq, _hRel => trivial
| idx, b :: body, hEq, hRel => by
    cases b with
    | rel a =>
        change
          a.evalTuple (PartialAssign.toAssign ρ) ∈
              P.atomRelationFor I S deltaAt? idx a ∧
            RelBodySatWithDelta P I S deltaAt? (idx + 1)
              body (PartialAssign.toAssign ρ) at hRel
        exact
          ⟨hRel.1,
            equalitiesHold_sound P I S deltaAt? ρ
              (idx + 1) body hEq hRel.2⟩
    | eq lhs rhs =>
        have hBoth :
            equalityHolds ρ lhs rhs = true ∧
              equalitiesHold ρ body = true := by
          simpa [equalitiesHold] using hEq
        have hEqAtom :
            equalityHolds ρ lhs rhs = true :=
          hBoth.1
        have hEqTail :
            equalitiesHold ρ body = true :=
          hBoth.2
        exact
          ⟨equalityHolds_sound ρ lhs rhs hEqAtom,
            equalitiesHold_sound P I S deltaAt? ρ
              (idx + 1) body hEqTail hRel⟩

omit [LinearOrder D] in
theorem evalTerm?_eq_some_of_agrees
    {ρ : PartialAssign D}
    {σ : Assign D}
    {xs : List Var}
    (hAgree : PartialAssign.AgreesOn ρ σ xs)
    (term : RelTerm D)
    (hTerm :
      ∀ x : Var, term.var? = some x → x ∈ xs) :
    PartialAssign.evalTerm? ρ term =
      some (term.eval σ) := by
  cases term with
  | var x =>
      exact hAgree x (hTerm x rfl)
  | const d =>
      simp [PartialAssign.evalTerm?, RelTerm.eval]

omit [LinearOrder D] in
theorem equalityHolds_complete
    {ρ : PartialAssign D}
    {σ : Assign D}
    {xs : List Var}
    (hAgree : PartialAssign.AgreesOn ρ σ xs)
    (lhs rhs : RelTerm D)
    (hL :
      ∀ x : Var, lhs.var? = some x → x ∈ xs)
    (hR :
      ∀ x : Var, rhs.var? = some x → x ∈ xs)
    (hEq : lhs.eval σ = rhs.eval σ) :
    equalityHolds ρ lhs rhs = true := by
  have hL' :=
    evalTerm?_eq_some_of_agrees hAgree lhs hL
  have hR' :=
    evalTerm?_eq_some_of_agrees hAgree rhs hR
  unfold equalityHolds
  simp [hL', hR', hEq]

theorem equalitiesHold_complete
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (ρ : PartialAssign D)
    (σ : Assign D)
    (xs : List Var) :
    ∀ (idx : Nat) (body : List (Atom D Γ)),
      (∀ x : Var,
        x ∈ Body.varList body → x ∈ xs) →
        PartialAssign.AgreesOn ρ σ xs →
        BodySatWithDelta P I S deltaAt? idx body σ →
          equalitiesHold ρ body = true
| _idx, [], _hBound, _hAgree, _hBody => by
    simp [equalitiesHold]
| idx, b :: body, hBound, hAgree, hBody => by
    cases b with
    | rel a =>
        have hBoundTail :
            ∀ x : Var,
              x ∈ Body.varList body → x ∈ xs := by
          intro x hx
          have hxAll :
              x ∈ Body.varList
                (Atom.rel a :: body) := by
            simpa [Body.varList, Atom.listVarList,
              Atom.varList] using
              Or.inr hx
          exact hBound x hxAll
        exact
          equalitiesHold_complete P I S deltaAt? ρ σ xs
            (idx + 1) body hBoundTail hAgree hBody.2
    | eq lhs rhs =>
        have hEqAtom :
            equalityHolds ρ lhs rhs = true := by
          apply equalityHolds_complete
            (xs := xs)
            hAgree lhs rhs
          · intro x hx
            have hxEq :
                x ∈
                  (Atom.eq lhs rhs :
                    Atom D Γ).varList := by
              simp [Atom.varList, hx]
            exact hBound x
              (by
                simpa [Body.varList, Atom.listVarList] using
                  Or.inl hxEq)
          · intro x hx
            have hxEq :
                x ∈
                  (Atom.eq lhs rhs :
                    Atom D Γ).varList := by
              simp [Atom.varList, hx]
            exact hBound x
              (by
                simpa [Body.varList, Atom.listVarList] using
                  Or.inl hxEq)
          · exact hBody.1
        have hBoundTail :
            ∀ x : Var,
              x ∈ Body.varList body → x ∈ xs := by
          intro x hx
          have hxAll :
              x ∈ Body.varList
                (Atom.eq lhs rhs :: body) := by
            simpa [Body.varList, Atom.listVarList,
              Atom.varList] using
              Or.inr hx
          exact hBound x hxAll
        have hTail :=
          equalitiesHold_complete P I S deltaAt? ρ σ xs
            (idx + 1) body hBoundTail hAgree hBody.2
        simp [equalitiesHold, hEqAtom, hTail]

/-
  Assignments returned by the executable tuple-join body
  evaluator satisfy the indexed semi-naive body semantics.
-/
theorem bodyAssignments_sound
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (body : List (Atom D Γ))
    {ρ : PartialAssign D}
    (hρ : ρ ∈ P.bodyAssignments I S deltaAt? body) :
    BodySatWithDelta P I S deltaAt? 0 body
      (PartialAssign.toAssign ρ) := by
  unfold bodyAssignments at hρ
  rcases Finset.mem_filter.mp hρ with ⟨hJoin, hEq⟩
  rcases
    joinRelAtomsFrom_sound P I S deltaAt? 0 body
      {[]} hJoin with
    ⟨_ρ₀, _hρ₀, _hExt, hRel⟩
  exact
    equalitiesHold_sound P I S deltaAt? ρ 0 body hEq hRel

/-
  Satisfying indexed semi-naive body assignments appear in
  the executable tuple-join body evaluator, provided the
  total assignment is representable by a partial assignment.
-/
theorem bodyAssignments_complete
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (body : List (Atom D Γ))
    (σ : Assign D)
    (hBound :
      ∀ x : Var,
        x ∈ Body.varList body →
          x ∈ Body.relVarList body)
    (hBody :
      BodySatWithDelta P I S deltaAt? 0 body σ) :
    ∃ ρ : PartialAssign D,
      ρ ∈ P.bodyAssignments I S deltaAt? body ∧
        ∀ x : Var,
          x ∈ Body.varList body →
            PartialAssign.toAssign ρ x = σ x := by
  have hRel :
      RelBodySatWithDelta P I S deltaAt? 0 body σ :=
    BodySatWithDelta.rel P I S deltaAt? σ 0 body hBody
  rcases
    joinRelAtomsFrom_complete P I S deltaAt? 0 body
      {[]} σ [] (by simp)
      (PartialAssign.ConsistentWith.nil σ) hRel with
    ⟨ρ, hJoin, _hCons, _hExt, hAgreeRel⟩
  have hEq :
      equalitiesHold ρ body = true :=
    equalitiesHold_complete P I S deltaAt? ρ σ
      (Body.relVarList body) 0 body
      hBound hAgreeRel hBody
  refine ⟨ρ, ?_, ?_⟩
  · unfold bodyAssignments
    exact Finset.mem_filter.mpr ⟨hJoin, hEq⟩
  · intro x hx
    exact
      PartialAssign.AgreesOn.toAssign_eq hAgreeRel
        (hBound x hx)

theorem extendAssignmentsWithAtomList_toFinset
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (idx : Nat)
    (assignments : List (PartialAssign D))
    (a : RelAtom D Γ) :
    (P.extendAssignmentsWithAtomList I S deltaAt? idx
        assignments a).toFinset =
      P.extendAssignmentsWithAtom I S deltaAt? idx
        assignments.toFinset a := by
  apply Finset.ext
  intro ρ'
  simp [extendAssignmentsWithAtomList,
    extendAssignmentsWithAtom, List.mem_toFinset,
    List.mem_flatMap, List.mem_filterMap,
    Finset.mem_biUnion,
    mem_optionToFinset_iff,
    P.mem_atomTuplesFor_iff I S deltaAt? idx a]

theorem atomContainsTupleFor_iff
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (idx : Nat)
    (a : RelAtom D Γ)
    (t : Tuple D (Γ.arity a.rel)) :
    P.atomContainsTupleFor I C S deltaAt? idx a t = true ↔
      t ∈ P.atomTuplesFor I S deltaAt? idx a := by
  unfold atomContainsTupleFor atomTuplesFor
  by_cases hDelta : deltaAt? = some idx
  · simp [hDelta]
    by_cases hIDB : a.rel ∈ P.idb
    · simp [hIDB, MaterializedIDB.containsTuple_iff]
    · simp [hIDB]
  · simp [hDelta]
    by_cases hIDB : a.rel ∈ P.idb
    · simp [hIDB, MaterializedIDB.containsTuple_iff]
    · simp [hIDB, IndexedInput.containsTuple_iff,
        IndexedInput.mem_lookupTuples_iff, Finset.mem_sort]

theorem mem_atomTupleMembershipCandidatesFor_iff
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (idx : Nat)
    (a : RelAtom D Γ)
    (u t : Tuple D (Γ.arity a.rel)) :
    t ∈ P.atomTupleMembershipCandidatesFor
        I C S deltaAt? idx a u ↔
      t = u ∧ u ∈ P.atomTuplesFor I S deltaAt? idx a := by
  unfold atomTupleMembershipCandidatesFor
  by_cases hContains :
      P.atomContainsTupleFor I C S deltaAt? idx a u = true
  · have hMem :
        u ∈ P.atomTuplesFor I S deltaAt? idx a :=
      (P.atomContainsTupleFor_iff I C S deltaAt? idx a u).mp
        hContains
    simp [hContains, hMem]
  · have hMem :
        ¬ u ∈ P.atomTuplesFor I S deltaAt? idx a := by
      intro hTuple
      exact hContains
        ((P.atomContainsTupleFor_iff I C S deltaAt? idx a u).mpr
          hTuple)
    simp [hContains, hMem]

theorem evalTuple_eq_of_atomVarsBound_extends
    {ρ ρ' : PartialAssign D}
    {a : RelAtom D Γ}
    (hBound : atomVarsBound ρ a = true)
    (hExt : PartialAssign.Extends ρ' ρ) :
    a.evalTuple (PartialAssign.toAssign ρ') =
      a.evalTuple (PartialAssign.toAssign ρ) := by
  apply a.evalTuple_eq_of_assign_eq_on_vars
  intro x hx
  have hxSome :
      (PartialAssign.lookup ρ x).isSome = true :=
    (List.all_eq_true.mp hBound) x hx
  rcases Option.isSome_iff_exists.mp hxSome with
    ⟨d, hLookup⟩
  have hLookup' : PartialAssign.lookup ρ' x = some d :=
    hExt x d hLookup
  simp [PartialAssign.toAssign, hLookup, hLookup']

set_option linter.flexible false in
theorem allBoundAtomTuple_eq_of_extend
    {ρ ρ' : PartialAssign D}
    {a : RelAtom D Γ}
    {u t : Tuple D (Γ.arity a.rel)}
    (hAll : allBoundAtomTuple? ρ a = some u)
    (hExtend : extendWithAtomRow ρ a t = some ρ') :
    u = t := by
  unfold allBoundAtomTuple? at hAll
  cases hBound : atomVarsBound ρ a
  · simp [hBound] at hAll
  · simp [hBound] at hAll
    cases hAll
    have hExt : PartialAssign.Extends ρ' ρ :=
      extendWithAtomRow_extends ρ ρ' a t hExtend
    have hStable :
        a.evalTuple (PartialAssign.toAssign ρ') =
          a.evalTuple (PartialAssign.toAssign ρ) :=
      evalTuple_eq_of_atomVarsBound_extends hBound hExt
    have hTuple :
        a.evalTuple (PartialAssign.toAssign ρ') = t :=
      extendWithAtomRow_evalTuple_of_extends
        ρ ρ' ρ' a t hExtend
        (PartialAssign.Extends.refl ρ')
    exact hStable.symm.trans hTuple

set_option linter.flexible false in
theorem indexedAtomCandidatesFor_mem_of_extend
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (idx : Nat)
    (ρ ρ' : PartialAssign D)
    (a : RelAtom D Γ)
    (t : Tuple D (Γ.arity a.rel))
    (hExtend : extendWithAtomRow ρ a t = some ρ') :
    t ∈ P.indexedAtomCandidatesFor I C S deltaAt? idx ρ a ↔
      t ∈ P.atomTuplesFor I S deltaAt? idx a := by
  unfold indexedAtomCandidatesFor allBoundAtomCandidatesFor
  cases hAll : allBoundAtomTuple? ρ a with
  | some u =>
      simp
      rw [P.mem_atomTupleMembershipCandidatesFor_iff
        I C S deltaAt? idx a u t]
      constructor
      · intro ht
        simpa [ht.1] using ht.2
      · intro ht
        have hut : u = t :=
          allBoundAtomTuple_eq_of_extend hAll hExtend
        exact ⟨hut.symm, by simpa [hut] using ht⟩
  | none =>
      simp
      cases hColumn : boundColumnData? ρ a with
      | none =>
          simp
      | some column =>
          rcases column with ⟨i, d⟩
          rw [P.mem_atomIndexedTuplesFor_iff I C S deltaAt?
            idx a i d t]
          constructor
          · intro ht
            exact ht.1
          · intro ht
            have hEval :
                PartialAssign.evalTerm? ρ (a.args.get i) =
                  some d :=
              boundColumnData_eval_eq hColumn
            exact
              ⟨ht,
                boundColumn_get_eq_of_extend
                  ρ ρ' a t
                  { index := i
                    value := d
                    eval_eq := hEval }
                  hExtend⟩

theorem extendAssignmentsWithAtomIndexedList_toFinset
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (idx : Nat)
    (assignments : List (PartialAssign D))
    (a : RelAtom D Γ) :
    (P.extendAssignmentsWithAtomIndexedList I C S deltaAt? idx
        assignments a).toFinset =
      (P.extendAssignmentsWithAtomList I S deltaAt? idx
        assignments a).toFinset := by
  apply Finset.ext
  intro ρ'
  constructor
  · intro hρ'
    rw [List.mem_toFinset] at hρ' ⊢
    rw [extendAssignmentsWithAtomIndexedList,
      List.mem_flatMap] at hρ'
    rw [extendAssignmentsWithAtomList,
      List.mem_flatMap]
    rcases hρ' with ⟨ρ, hρ, hρ'⟩
    rw [List.mem_filterMap] at hρ'
    rcases hρ' with ⟨t, ht, hExtend⟩
    refine ⟨ρ, hρ, ?_⟩
    rw [List.mem_filterMap]
    exact
      ⟨t,
        (P.indexedAtomCandidatesFor_mem_of_extend
          I C S deltaAt? idx ρ ρ' a t hExtend).mp ht,
        hExtend⟩
  · intro hρ'
    rw [List.mem_toFinset] at hρ' ⊢
    rw [extendAssignmentsWithAtomList,
      List.mem_flatMap] at hρ'
    rw [extendAssignmentsWithAtomIndexedList,
      List.mem_flatMap]
    rcases hρ' with ⟨ρ, hρ, hρ'⟩
    rw [List.mem_filterMap] at hρ'
    rcases hρ' with ⟨t, ht, hExtend⟩
    refine ⟨ρ, hρ, ?_⟩
    rw [List.mem_filterMap]
    exact
      ⟨t,
        (P.indexedAtomCandidatesFor_mem_of_extend
          I C S deltaAt? idx ρ ρ' a t hExtend).mpr ht,
        hExtend⟩

theorem extendAssignmentsWithAtomList_toFinset_congr
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (idx : Nat)
    (a : RelAtom D Γ)
    {assignments₁ assignments₂ : List (PartialAssign D)}
    (hAssignments : assignments₁.toFinset = assignments₂.toFinset) :
    (P.extendAssignmentsWithAtomList I S deltaAt? idx
        assignments₁ a).toFinset =
      (P.extendAssignmentsWithAtomList I S deltaAt? idx
        assignments₂ a).toFinset := by
  rw [P.extendAssignmentsWithAtomList_toFinset,
    P.extendAssignmentsWithAtomList_toFinset,
    hAssignments]

theorem filter_toFinset_eq_of_toFinset_eq
    {α : Type}
    [DecidableEq α]
    (p : α → Bool)
    {xs ys : List α}
    (h : xs.toFinset = ys.toFinset) :
    (xs.filter p).toFinset = (ys.filter p).toFinset := by
  apply Finset.ext
  intro x
  have hx :
      x ∈ xs ↔ x ∈ ys := by
    have hxFin :
        x ∈ xs.toFinset ↔ x ∈ ys.toFinset := by
      rw [h]
    simpa [List.mem_toFinset] using hxFin
  simp [List.mem_toFinset, hx]

theorem map_toFinset_eq_of_toFinset_eq
    {α β : Type}
    [DecidableEq α]
    [DecidableEq β]
    (f : α → β)
    {xs ys : List α}
    (h : xs.toFinset = ys.toFinset) :
    (xs.map f).toFinset = (ys.map f).toFinset := by
  apply Finset.ext
  intro y
  have hx :
      ∀ x : α, x ∈ xs ↔ x ∈ ys := by
    intro x
    have hxFin :
        x ∈ xs.toFinset ↔ x ∈ ys.toFinset := by
      rw [h]
    simpa [List.mem_toFinset] using hxFin
  simp [List.mem_toFinset, List.mem_map, hx]

theorem joinCompiledRelAtomsFromIndexedList_toFinset_congr
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat) :
    ∀ (atoms : List (Nat × RelAtom D Γ))
      (assignments₁ assignments₂ : List (PartialAssign D)),
      assignments₁.toFinset = assignments₂.toFinset →
        (P.joinCompiledRelAtomsFromIndexedList I C S
            deltaAt? atoms assignments₁).toFinset =
          (P.joinCompiledRelAtomsFromList I S
            deltaAt? atoms assignments₂).toFinset
| [], assignments₁, assignments₂, hAssignments => hAssignments
| (idx, a) :: atoms, assignments₁, assignments₂,
    hAssignments => by
    unfold joinCompiledRelAtomsFromIndexedList
      joinCompiledRelAtomsFromList
    apply
      joinCompiledRelAtomsFromIndexedList_toFinset_congr
        P I C S deltaAt? atoms
    rw [P.extendAssignmentsWithAtomIndexedList_toFinset]
    exact
      P.extendAssignmentsWithAtomList_toFinset_congr
        I S deltaAt? idx a hAssignments

theorem relEntriesSatWithDelta_iff_of_perm
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    {entries₁ entries₂ : List (Nat × RelAtom D Γ)}
    (hPerm : List.Perm entries₁ entries₂)
    (σ : Assign D) :
    RelEntriesSatWithDelta P I S deltaAt? entries₁ σ ↔
      RelEntriesSatWithDelta P I S deltaAt? entries₂ σ := by
  constructor
  · intro h entry hEntry
    exact h entry ((hPerm.mem_iff).mpr hEntry)
  · intro h entry hEntry
    exact h entry ((hPerm.mem_iff).mp hEntry)

theorem relEntriesSatWithDelta_relBodyAtomsFrom_iff
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat) :
    ∀ (idx : Nat) (body : List (Atom D Γ)) (σ : Assign D),
      RelEntriesSatWithDelta P I S deltaAt?
          (relBodyAtomsFrom idx body) σ ↔
        RelBodySatWithDelta P I S deltaAt? idx body σ
| _idx, [], _σ => by
    simp [RelEntriesSatWithDelta, RelBodySatWithDelta,
      relBodyAtomsFrom]
| idx, .rel a :: body, σ => by
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · exact h (idx, a) (by simp [relBodyAtomsFrom])
      · exact
          (relEntriesSatWithDelta_relBodyAtomsFrom_iff
            P I S deltaAt? (idx + 1) body σ).mp
            (by
              intro entry hEntry
              exact h entry
                (by simpa [relBodyAtomsFrom] using
                  Or.inr hEntry))
    · intro h entry hEntry
      have hEntry' :
          entry = (idx, a) ∨
            entry ∈ relBodyAtomsFrom (idx + 1) body := by
        simpa [relBodyAtomsFrom] using hEntry
      rcases hEntry' with hHead | hTail
      · cases hHead
        exact h.1
      · exact
          (relEntriesSatWithDelta_relBodyAtomsFrom_iff
            P I S deltaAt? (idx + 1) body σ).mpr h.2
            entry hTail
| idx, .eq _ _ :: body, σ => by
    simpa [relBodyAtomsFrom, RelBodySatWithDelta] using
      relEntriesSatWithDelta_relBodyAtomsFrom_iff
        P I S deltaAt? (idx + 1) body σ

omit [LinearOrder D] in
theorem relEntryVarList_relBodyAtomsFrom
    (idx : Nat)
    (body : List (Atom D Γ)) :
    relEntryVarList (D := D) (relBodyAtomsFrom idx body) =
      Body.relVarList body := by
  induction body generalizing idx with
  | nil =>
      simp [relEntryVarList, relBodyAtomsFrom,
        Body.relVarList, Atom.listRelVarList]
  | cons b body ih =>
      cases b with
      | rel a =>
          simpa [relEntryVarList, relBodyAtomsFrom,
            Body.relVarList, Atom.listRelVarList,
            Atom.relVarList] using ih (idx + 1)
      | eq lhs rhs =>
          simpa [relEntryVarList, relBodyAtomsFrom,
            Body.relVarList, Atom.listRelVarList,
            Atom.relVarList] using ih (idx + 1)

omit [LinearOrder D] in
theorem mem_relEntryVarList_iff_of_perm
    {entries₁ entries₂ : List (Nat × RelAtom D Γ)}
    (hPerm : List.Perm entries₁ entries₂)
    (x : Var) :
    x ∈ relEntryVarList (D := D) entries₁ ↔
      x ∈ relEntryVarList (D := D) entries₂ := by
  unfold relEntryVarList
  have hFlat :
      List.Perm
        (entries₁.flatMap (fun entry => entry.2.varList))
        (entries₂.flatMap (fun entry => entry.2.varList)) :=
    hPerm.flatMap (fun _entry _hEntry => List.Perm.refl _)
  exact hFlat.mem_iff

omit [LinearOrder D] in
theorem exists_source_var_of_mem_rewriteRelAtom_varList
    (rw : EqRewrite D)
    (a : RelAtom D Γ)
    (hFree : a.ConstFree)
    {x : Var}
    (hx : x ∈ (rewriteRelAtom rw a).varList) :
    ∃ y : Var,
      y ∈ a.varList ∧
        x ∈ (rewriteRelTerm rw (.var y)).varList := by
  unfold RelAtom.varList at hx
  rcases List.mem_filterMap.mp hx with
    ⟨term, hTerm, hVar⟩
  rcases List.mem_iff_get.mp hTerm with ⟨i, hGet⟩
  have hiArity : i.1 < Γ.arity a.rel := by
    simpa [rewriteRelAtom, Vector.length_toList] using i.2
  rcases
      a.exists_var_mem_varList_of_constFree_getElem
        hFree hiArity with
    ⟨y, hArg, hy⟩
  refine ⟨y, hy, ?_⟩
  have hTermEq :
      term = rewriteRelTerm rw (.var y) := by
    have hCoord :
        (rewriteRelAtom rw a).args.toList[i.1] =
          (rewriteRelAtom rw a).args[i.1] :=
      Vector.getElem_toList i.2
    have hRewritten :
        (rewriteRelAtom rw a).args[i.1] =
          rewriteRelTerm rw (.var y) := by
      simp [rewriteRelAtom, Vector.get, hArg]
    exact hGet.symm.trans (hCoord.trans hRewritten)
  rw [hTermEq] at hVar
  cases hRewrite : rewriteRelTerm rw (.var y) with
  | var z =>
      rw [hRewrite] at hVar
      simp [RelTerm.var?] at hVar
      simpa [RelTerm.varList] using hVar.symm
  | const d =>
      simp [RelTerm.var?, hRewrite] at hVar

omit [LinearOrder D] in
theorem mem_rewriteRelAtom_varList_of_mem_varList
    (rw : EqRewrite D)
    (a : RelAtom D Γ)
    {x y : Var}
    (hy : y ∈ a.varList)
    (hx : x ∈ (rewriteRelTerm rw (.var y)).varList) :
    x ∈ (rewriteRelAtom rw a).varList := by
  unfold RelAtom.varList at hy ⊢
  rcases List.mem_filterMap.mp hy with
    ⟨term, hTerm, hVar⟩
  cases term with
  | var z =>
      have hzy : z = y := by
        simpa [RelTerm.var?] using Option.some.inj hVar
      subst y
      apply List.mem_filterMap.mpr
      refine
        ⟨rewriteRelTerm rw (.var z), ?_, ?_⟩
      · rcases List.mem_iff_get.mp hTerm with ⟨i, hGet⟩
        have hiArity : i.1 < Γ.arity a.rel := by
          simpa [Vector.length_toList] using i.2
        have hArg : a.args[i.1] = RelTerm.var z := by
          have hCoord :
              a.args.toList[i.1] = a.args[i.1] :=
            Vector.getElem_toList i.2
          exact hCoord.symm.trans hGet
        have hRewritten :
            (rewriteRelAtom rw a).args[i.1] =
              rewriteRelTerm rw (.var z) := by
          simp [rewriteRelAtom, Vector.get, hArg]
        rw [← hRewritten]
        rw [Vector.mem_toList_iff]
        exact Vector.getElem_mem hiArity
      · cases hRewrite : rewriteRelTerm rw (.var z) with
        | var z' =>
            rw [hRewrite] at hx
            simp [RelTerm.varList] at hx
            simpa [RelTerm.var?] using hx.symm
        | const d =>
            simp [RelTerm.varList, hRewrite] at hx
  | const d =>
      simp [RelTerm.var?] at hVar

omit [LinearOrder D] in
theorem mem_rewriteRelEntryVarList_of_mem
    (rw : EqRewrite D)
    (entries : List (Nat × RelAtom D Γ))
    {x y : Var}
    (hy : y ∈ relEntryVarList (D := D) entries)
    (hx : x ∈ (rewriteRelTerm rw (.var y)).varList) :
    x ∈ relEntryVarList (D := D)
      (rewriteRelEntries rw entries) := by
  unfold relEntryVarList at hy ⊢
  rw [List.mem_flatMap] at hy ⊢
  rcases hy with ⟨entry, hEntry, hyEntry⟩
  cases entry with
  | mk idx a =>
      refine
        ⟨(idx, rewriteRelAtom rw a), ?_, ?_⟩
      · unfold rewriteRelEntries rewriteRelEntry
        exact List.mem_map.mpr
          ⟨(idx, a), hEntry, rfl⟩
      · exact
          mem_rewriteRelAtom_varList_of_mem_varList
            rw a hyEntry hx

omit [LinearOrder D] in
theorem normalizedHead_varList_subset_relEntryVarList
    (r : Rule D Γ)
    {rw : EqRewrite D}
    (_hRewrite : equalityRewrite r.body = some rw)
    {x : Var}
    (hx : x ∈ (rewriteRelAtom rw r.head).varList) :
    x ∈ relEntryVarList (D := D)
      (rewriteRelEntries rw (relBodyAtomEntries r.body)) := by
  rcases
      exists_source_var_of_mem_rewriteRelAtom_varList
        rw r.head r.noHeadConst hx with
    ⟨y, hyHead, hxRewrite⟩
  have hyHeadVars : y ∈ r.head.vars :=
    r.head.mem_vars_of_mem_varList hyHead
  have hyRelVars : y ∈ Body.relVars r.body :=
    r.safe y (Finset.mem_union.mpr (Or.inl hyHeadVars))
  have hyRelList : y ∈ Body.relVarList r.body := by
    unfold Body.relVars Atom.relVars at hyRelVars
    exact List.mem_toFinset.mp hyRelVars
  have hyEntries :
      y ∈ relEntryVarList (D := D)
        (relBodyAtomEntries r.body) := by
    unfold relBodyAtomEntries
    rw [relEntryVarList_relBodyAtomsFrom]
    exact hyRelList
  exact
    mem_rewriteRelEntryVarList_of_mem
      rw (relBodyAtomEntries r.body) hyEntries hxRewrite

omit [LinearOrder D] in
theorem rewriteRelTerm_append
    (rw extra : EqRewrite D)
    (term : RelTerm D) :
    rewriteRelTerm (rw ++ extra) term =
      rewriteRelTerm extra (rewriteRelTerm rw term) := by
  induction rw generalizing term with
  | nil =>
      rfl
  | cons pair rw ih =>
      cases pair with
      | mk x replacement =>
          simp [rewriteRelTerm, ih]

set_option linter.flexible false in
omit [LinearOrder D] in
theorem addEqualityRewrite_extends
    {rw rw' : EqRewrite D}
    {lhs rhs : RelTerm D}
    (hAdd : addEqualityRewrite rw lhs rhs = some rw') :
    ∃ extra : EqRewrite D, rw' = rw ++ extra := by
  cases hL : rewriteRelTerm rw lhs <;>
    cases hR : rewriteRelTerm rw rhs
  · rename_i x y
    by_cases hxy : x = y
    · simp [addEqualityRewrite, hL, hR, hxy] at hAdd
      subst rw'
      exact ⟨[], by simp⟩
    · by_cases hlt : x < y
      · simp [addEqualityRewrite, hL, hR, hxy, hlt] at hAdd
        subst rw'
        exact ⟨[(y, RelTerm.var x)], by simp⟩
      · simp [addEqualityRewrite, hL, hR, hxy, hlt] at hAdd
        subst rw'
        exact ⟨[(x, RelTerm.var y)], by simp⟩
  · rename_i x d
    simp [addEqualityRewrite, hL, hR] at hAdd
    subst rw'
    exact ⟨[(x, RelTerm.const d)], by simp⟩
  · rename_i d x
    simp [addEqualityRewrite, hL, hR] at hAdd
    subst rw'
    exact ⟨[(x, RelTerm.const d)], by simp⟩
  · rename_i d₁ d₂
    by_cases hEq : d₁ = d₂
    · simp [addEqualityRewrite, hL, hR, hEq] at hAdd
      subst rw'
      exact ⟨[], by simp⟩
    · simp [addEqualityRewrite, hL, hR, hEq] at hAdd

set_option linter.flexible false in
omit [LinearOrder D] in
theorem equalityRewriteFrom_extends
    {rw rw' : EqRewrite D}
    {body : List (Atom D Γ)}
    (hRewrite : equalityRewriteFrom rw body = some rw') :
    ∃ extra : EqRewrite D, rw' = rw ++ extra := by
  induction body generalizing rw with
  | nil =>
      simp [equalityRewriteFrom] at hRewrite
      subst rw'
      exact ⟨[], by simp⟩
  | cons b body ih =>
      cases b with
      | rel a =>
          exact ih hRewrite
      | eq lhs rhs =>
          unfold equalityRewriteFrom at hRewrite
          cases hAdd : addEqualityRewrite rw lhs rhs with
          | none =>
              simp [hAdd] at hRewrite
          | some rw₁ =>
              have hTail :
                  equalityRewriteFrom rw₁ body = some rw' := by
                simpa [hAdd] using hRewrite
              rcases addEqualityRewrite_extends hAdd with
                ⟨extra₁, hExt₁⟩
              rcases ih hTail with ⟨extra₂, hExt₂⟩
              subst rw₁
              subst rw'
              exact ⟨extra₁ ++ extra₂, by simp [List.append_assoc]⟩

omit [LinearOrder D] in
theorem rewriteRelTerm_eq_of_extends
    {rw rw' : EqRewrite D}
    {lhs rhs : RelTerm D}
    (hExt : ∃ extra : EqRewrite D, rw' = rw ++ extra)
    (hEq : rewriteRelTerm rw lhs = rewriteRelTerm rw rhs) :
    rewriteRelTerm rw' lhs = rewriteRelTerm rw' rhs := by
  rcases hExt with ⟨extra, rfl⟩
  simp [rewriteRelTerm_append, hEq]

set_option linter.flexible false in
omit [LinearOrder D] in
theorem addEqualityRewrite_rewrites_eq
    {rw rw' : EqRewrite D}
    {lhs rhs : RelTerm D}
    (hAdd : addEqualityRewrite rw lhs rhs = some rw') :
    rewriteRelTerm rw' lhs = rewriteRelTerm rw' rhs := by
  cases hL : rewriteRelTerm rw lhs <;>
    cases hR : rewriteRelTerm rw rhs
  · rename_i x y
    by_cases hxy : x = y
    · simp [addEqualityRewrite, hL, hR, hxy] at hAdd
      subst rw'
      simp [hL, hR, hxy]
    · by_cases hlt : x < y
      · simp [addEqualityRewrite, hL, hR, hxy, hlt] at hAdd
        subst rw'
        rw [rewriteRelTerm_append, rewriteRelTerm_append,
          hL, hR]
        simp [rewriteRelTerm, substRelTermVar, hxy]
      · simp [addEqualityRewrite, hL, hR, hxy, hlt] at hAdd
        subst rw'
        rw [rewriteRelTerm_append, rewriteRelTerm_append,
          hL, hR]
        have hyx : y ≠ x := by
          intro h
          exact hxy h.symm
        simp [rewriteRelTerm, substRelTermVar, hyx]
  · rename_i x d
    simp [addEqualityRewrite, hL, hR] at hAdd
    subst rw'
    rw [rewriteRelTerm_append, rewriteRelTerm_append,
      hL, hR]
    simp [rewriteRelTerm, substRelTermVar]
  · rename_i d x
    simp [addEqualityRewrite, hL, hR] at hAdd
    subst rw'
    rw [rewriteRelTerm_append, rewriteRelTerm_append,
      hL, hR]
    simp [rewriteRelTerm, substRelTermVar]
  · rename_i d₁ d₂
    by_cases hEq : d₁ = d₂
    · simp [addEqualityRewrite, hL, hR, hEq] at hAdd
      subst rw'
      simp [hL, hR, hEq]
    · simp [addEqualityRewrite, hL, hR, hEq] at hAdd

omit [LinearOrder D] in
theorem equalityRewriteFrom_rewrites_equalities
    {rw rw' : EqRewrite D}
    {body : List (Atom D Γ)}
    (hRewrite : equalityRewriteFrom rw body = some rw') :
    ∀ lhs rhs : RelTerm D,
      (lhs, rhs) ∈ equalityAtomPairs body →
        rewriteRelTerm rw' lhs = rewriteRelTerm rw' rhs := by
  induction body generalizing rw with
  | nil =>
      intro lhs rhs hMem
      simp [equalityAtomPairs] at hMem
  | cons b body ih =>
      cases b with
      | rel a =>
          intro lhs rhs hMem
          exact ih hRewrite lhs rhs hMem
      | eq lhs₀ rhs₀ =>
          unfold equalityRewriteFrom at hRewrite
          cases hAdd : addEqualityRewrite rw lhs₀ rhs₀ with
          | none =>
              simp [hAdd] at hRewrite
          | some rw₁ =>
              have hTail :
                  equalityRewriteFrom rw₁ body = some rw' := by
                simpa [hAdd] using hRewrite
              intro lhs rhs hMem
              have hMem' :
                  (lhs = lhs₀ ∧ rhs = rhs₀) ∨
                    (lhs, rhs) ∈ equalityAtomPairs body := by
                simpa [equalityAtomPairs] using hMem
              rcases hMem' with hHead | hTailMem
              · rcases hHead with ⟨rfl, rfl⟩
                have hEq₁ :=
                  addEqualityRewrite_rewrites_eq hAdd
                have hExt :=
                  equalityRewriteFrom_extends hTail
                exact rewriteRelTerm_eq_of_extends hExt hEq₁
              · exact ih hTail lhs rhs hTailMem

omit [LinearOrder D] in
theorem equalities_true_of_equalityRewrite
    {body : List (Atom D Γ)}
    {rw : EqRewrite D}
    (hRewrite :
      equalityRewrite body = some rw)
    (σ : Assign D) :
    ∀ lhs rhs : RelTerm D,
      (lhs, rhs) ∈ equalityAtomPairs body →
        lhs.eval (normalizedAssign rw σ) =
          rhs.eval (normalizedAssign rw σ) := by
  intro lhs rhs hMem
  have hEq :
      rewriteRelTerm rw lhs = rewriteRelTerm rw rhs := by
    unfold equalityRewrite at hRewrite
    exact
      equalityRewriteFrom_rewrites_equalities
        hRewrite lhs rhs hMem
  rw [← rewriteRelTerm_eval_normalizedAssign rw lhs σ,
    ← rewriteRelTerm_eval_normalizedAssign rw rhs σ,
    hEq]

theorem bodySatWithDelta_of_rel_and_equalities
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (σ : Assign D) :
    ∀ (idx : Nat) (body : List (Atom D Γ)),
      RelBodySatWithDelta P I S deltaAt? idx body σ →
        (∀ lhs rhs : RelTerm D,
          (lhs, rhs) ∈ equalityAtomPairs body →
            lhs.eval σ = rhs.eval σ) →
          BodySatWithDelta P I S deltaAt? idx body σ
| _idx, [], _hRel, _hEq => trivial
| idx, .rel a :: body, hRel, hEq => by
    refine ⟨hRel.1, ?_⟩
    exact
      bodySatWithDelta_of_rel_and_equalities
        P I S deltaAt? σ (idx + 1) body hRel.2
        (by
          intro lhs rhs hMem
          exact hEq lhs rhs
            (by simpa [equalityAtomPairs] using hMem))
| idx, .eq lhs rhs :: body, hRel, hEq => by
    refine ⟨?_, ?_⟩
    · exact hEq lhs rhs (by simp [equalityAtomPairs])
    · exact
        bodySatWithDelta_of_rel_and_equalities
          P I S deltaAt? σ (idx + 1) body hRel
          (by
            intro lhs' rhs' hMem
            exact hEq lhs' rhs'
              (by
                simpa [equalityAtomPairs] using
                  Or.inr hMem))

theorem relBodySat_rewrite_sound
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (rw : EqRewrite D) :
    ∀ (idx : Nat) (body : List (Atom D Γ))
      (σ : Assign D),
      RelEntriesSatWithDelta P I S deltaAt?
          (rewriteRelEntries rw (relBodyAtomsFrom idx body)) σ →
        RelBodySatWithDelta P I S deltaAt? idx body
          (normalizedAssign rw σ)
| _idx, [], σ, _hRel => trivial
| idx, .rel a :: body, σ, hRel => by
    have hHead :
        (rewriteRelAtom rw a).evalTuple σ ∈
          P.atomRelationFor I S deltaAt? idx
            (rewriteRelAtom rw a) :=
      hRel (idx, rewriteRelAtom rw a)
        (by simp [rewriteRelEntries, rewriteRelEntry,
          relBodyAtomsFrom])
    have hAtom :
        a.evalTuple (normalizedAssign rw σ) ∈
          P.atomRelationFor I S deltaAt? idx a := by
      rw [← atomRelationFor_rewriteRelAtom
        P I S deltaAt? idx rw a]
      simpa [rewriteRelAtom_evalTuple_normalizedAssign
        rw a σ] using hHead
    refine ⟨hAtom, ?_⟩
    exact
      relBodySat_rewrite_sound P I S deltaAt? rw
        (idx + 1) body σ
        (by
          intro entry hEntry
          exact hRel entry
            (by
              simpa [rewriteRelEntries, rewriteRelEntry,
                relBodyAtomsFrom] using
                List.mem_cons.mpr (Or.inr hEntry)))
| idx, .eq lhs rhs :: body, σ, hRel => by
    exact
      relBodySat_rewrite_sound P I S deltaAt? rw
        (idx + 1) body σ
        (by
          intro entry hEntry
          exact hRel entry
            (by
              simpa [rewriteRelEntries, rewriteRelEntry,
                relBodyAtomsFrom] using hEntry))

theorem relEntriesSat_rewrite_complete
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (rw : EqRewrite D)
    {σ : Assign D}
    (hRespect : RewriteRespects rw σ) :
    ∀ (idx : Nat) (body : List (Atom D Γ)),
      RelBodySatWithDelta P I S deltaAt? idx body σ →
        RelEntriesSatWithDelta P I S deltaAt?
          (rewriteRelEntries rw (relBodyAtomsFrom idx body)) σ
| _idx, [], _hRel, entry, hEntry => by
    simp [rewriteRelEntries, relBodyAtomsFrom] at hEntry
| idx, .rel a :: body, hRel, entry, hEntry => by
    have hEntry' :
        entry = (idx, rewriteRelAtom rw a) ∨
          entry ∈
            rewriteRelEntries rw
              (relBodyAtomsFrom (idx + 1) body) := by
      simpa [rewriteRelEntries, rewriteRelEntry,
        relBodyAtomsFrom] using hEntry
    rcases hEntry' with hHead | hTail
    · cases hHead
      have hAtom :
          (rewriteRelAtom rw a).evalTuple σ ∈
            P.atomRelationFor I S deltaAt? idx
              (rewriteRelAtom rw a) := by
        rw [atomRelationFor_rewriteRelAtom
          P I S deltaAt? idx rw a]
        simpa [rewriteRelAtom_evalTuple_of_respects
          hRespect a] using hRel.1
      exact hAtom
    · exact
        relEntriesSat_rewrite_complete P I S deltaAt?
          rw hRespect (idx + 1) body hRel.2 entry hTail
| idx, .eq lhs rhs :: body, hRel, entry, hEntry => by
    exact
      relEntriesSat_rewrite_complete P I S deltaAt?
        rw hRespect (idx + 1) body hRel entry
        (by
          simpa [rewriteRelEntries, rewriteRelEntry,
            relBodyAtomsFrom] using hEntry)

set_option linter.flexible false in
omit [LinearOrder D] in
theorem addEqualityRewrite_some_respects
    {rw rw' : EqRewrite D}
    {lhs rhs : RelTerm D}
    {σ : Assign D}
    (hRespect : RewriteRespects rw σ)
    (hEq : lhs.eval σ = rhs.eval σ)
    (hAdd : addEqualityRewrite rw lhs rhs = some rw') :
    RewriteRespects rw' σ := by
  have hRewriteEqBase :
      (rewriteRelTerm rw lhs).eval σ =
        (rewriteRelTerm rw rhs).eval σ := by
    calc
      (rewriteRelTerm rw lhs).eval σ = lhs.eval σ :=
        rewriteRelTerm_eval_of_respects hRespect lhs
      _ = rhs.eval σ := hEq
      _ = (rewriteRelTerm rw rhs).eval σ := by
        rw [rewriteRelTerm_eval_of_respects hRespect rhs]
  cases hL : rewriteRelTerm rw lhs <;>
    cases hR : rewriteRelTerm rw rhs
  · rename_i x y
    have hRewriteEq : σ x = σ y := by
      simpa [hL, hR, RelTerm.eval] using hRewriteEqBase
    by_cases hxy : x = y
    · simp [addEqualityRewrite, hL, hR, hxy] at hAdd
      subst rw'
      exact hRespect
    · by_cases hlt : x < y
      · simp [addEqualityRewrite, hL, hR, hxy, hlt] at hAdd
        subst rw'
        intro z term hMem
        rcases List.mem_append.mp hMem with hOld | hNew
        · exact hRespect z term hOld
        · simp at hNew
          rcases hNew with ⟨hz, ht⟩
          subst hz
          subst ht
          simpa [RelTerm.eval] using hRewriteEq.symm
      · simp [addEqualityRewrite, hL, hR, hxy, hlt] at hAdd
        subst rw'
        intro z term hMem
        rcases List.mem_append.mp hMem with hOld | hNew
        · exact hRespect z term hOld
        · simp at hNew
          rcases hNew with ⟨hz, ht⟩
          subst hz
          subst ht
          simpa [RelTerm.eval] using hRewriteEq
  · rename_i x d
    have hRewriteEq : σ x = d := by
      simpa [hL, hR, RelTerm.eval] using hRewriteEqBase
    simp [addEqualityRewrite, hL, hR] at hAdd
    subst rw'
    intro z term hMem
    rcases List.mem_append.mp hMem with hOld | hNew
    · exact hRespect z term hOld
    · simp at hNew
      rcases hNew with ⟨hz, ht⟩
      subst hz
      subst ht
      simpa [RelTerm.eval] using hRewriteEq
  · rename_i d x
    have hRewriteEq : d = σ x := by
      simpa [hL, hR, RelTerm.eval] using hRewriteEqBase
    simp [addEqualityRewrite, hL, hR] at hAdd
    subst rw'
    intro z term hMem
    rcases List.mem_append.mp hMem with hOld | hNew
    · exact hRespect z term hOld
    · simp at hNew
      rcases hNew with ⟨hz, ht⟩
      subst hz
      subst ht
      simpa [RelTerm.eval] using hRewriteEq.symm
  · rename_i d₁ d₂
    by_cases hConst : d₁ = d₂
    · simp [addEqualityRewrite, hL, hR, hConst] at hAdd
      subst rw'
      exact hRespect
    · simp [addEqualityRewrite, hL, hR, hConst] at hAdd

set_option linter.flexible false in
omit [LinearOrder D] in
theorem addEqualityRewrite_none_contradiction
    {rw : EqRewrite D}
    {lhs rhs : RelTerm D}
    {σ : Assign D}
    (hRespect : RewriteRespects rw σ)
    (hEq : lhs.eval σ = rhs.eval σ)
    (hAdd : addEqualityRewrite rw lhs rhs = none) :
    False := by
  have hRewriteEqBase :
      (rewriteRelTerm rw lhs).eval σ =
        (rewriteRelTerm rw rhs).eval σ := by
    calc
      (rewriteRelTerm rw lhs).eval σ = lhs.eval σ :=
        rewriteRelTerm_eval_of_respects hRespect lhs
      _ = rhs.eval σ := hEq
      _ = (rewriteRelTerm rw rhs).eval σ := by
        rw [rewriteRelTerm_eval_of_respects hRespect rhs]
  cases hL : rewriteRelTerm rw lhs <;>
    cases hR : rewriteRelTerm rw rhs
  · rename_i x y
    by_cases hxy : x = y
    · simp [addEqualityRewrite, hL, hR, hxy] at hAdd
    · by_cases hlt : x < y
      · simp [addEqualityRewrite, hL, hR, hxy, hlt] at hAdd
      · simp [addEqualityRewrite, hL, hR, hxy, hlt] at hAdd
  · simp [addEqualityRewrite, hL, hR] at hAdd
  · simp [addEqualityRewrite, hL, hR] at hAdd
  · rename_i d₁ d₂
    have hRewriteEq : d₁ = d₂ := by
      simpa [hL, hR, RelTerm.eval] using hRewriteEqBase
    by_cases hConst : d₁ = d₂
    · simp [addEqualityRewrite, hL, hR, hConst] at hAdd
    · simp at hRewriteEq
      exact hConst hRewriteEq

set_option linter.flexible false in
theorem equalityRewriteFrom_respects_of_bodySat
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    {rw rw' : EqRewrite D}
    {σ : Assign D} :
    ∀ (idx : Nat) (body : List (Atom D Γ)),
      equalityRewriteFrom rw body = some rw' →
        RewriteRespects rw σ →
          BodySatWithDelta P I S deltaAt? idx body σ →
            RewriteRespects rw' σ
| _idx, [], hRewrite, hRespect, _hBody => by
    simp [equalityRewriteFrom] at hRewrite
    subst rw'
    exact hRespect
| idx, .rel a :: body, hRewrite, hRespect, hBody => by
    exact
      equalityRewriteFrom_respects_of_bodySat P I S
        deltaAt? (idx + 1) body hRewrite hRespect hBody.2
| idx, .eq lhs rhs :: body, hRewrite, hRespect,
    hBody => by
    unfold equalityRewriteFrom at hRewrite
    cases hAdd : addEqualityRewrite rw lhs rhs with
    | none =>
        simp [hAdd] at hRewrite
    | some rw₁ =>
        have hTail :
            equalityRewriteFrom rw₁ body = some rw' := by
          simpa [hAdd] using hRewrite
        have hRespect₁ :
            RewriteRespects rw₁ σ :=
          addEqualityRewrite_some_respects
            hRespect hBody.1 hAdd
        exact
          equalityRewriteFrom_respects_of_bodySat P I S
            deltaAt? (idx + 1) body hTail
            hRespect₁ hBody.2

theorem equalityRewriteFrom_none_no_bodySat
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    {rw : EqRewrite D}
    {σ : Assign D} :
    ∀ (idx : Nat) (body : List (Atom D Γ)),
      equalityRewriteFrom rw body = none →
        RewriteRespects rw σ →
          BodySatWithDelta P I S deltaAt? idx body σ →
            False
| _idx, [], hRewrite, _hRespect, _hBody => by
    simp [equalityRewriteFrom] at hRewrite
| idx, .rel a :: body, hRewrite, hRespect, hBody => by
    exact
      equalityRewriteFrom_none_no_bodySat P I S deltaAt?
        (idx + 1) body hRewrite hRespect hBody.2
| idx, .eq lhs rhs :: body, hRewrite, hRespect,
    hBody => by
    unfold equalityRewriteFrom at hRewrite
    cases hAdd : addEqualityRewrite rw lhs rhs with
    | none =>
        exact
          addEqualityRewrite_none_contradiction
            hRespect hBody.1 hAdd
    | some rw₁ =>
        have hTail :
            equalityRewriteFrom rw₁ body = none := by
          simpa [hAdd] using hRewrite
        have hRespect₁ :
            RewriteRespects rw₁ σ :=
          addEqualityRewrite_some_respects
            hRespect hBody.1 hAdd
        exact
          equalityRewriteFrom_none_no_bodySat P I S
            deltaAt? (idx + 1) body hTail
            hRespect₁ hBody.2

theorem equalityRewrite_none_no_bodySat
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    {body : List (Atom D Γ)}
    {σ : Assign D}
    (hRewrite : equalityRewrite body = none)
    (hBody : BodySatWithDelta P I S deltaAt? 0 body σ) :
    False := by
  unfold equalityRewrite at hRewrite
  exact
    equalityRewriteFrom_none_no_bodySat P I S deltaAt?
      0 body hRewrite (RewriteRespects.nil σ) hBody

theorem source_bodySat_to_normalized_relEntries
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    {body : List (Atom D Γ)}
    {rw : EqRewrite D}
    {σ : Assign D}
    (hRewrite : equalityRewrite body = some rw)
    (hBody : BodySatWithDelta P I S deltaAt? 0 body σ) :
    RelEntriesSatWithDelta P I S deltaAt?
      (rewriteRelEntries rw (relBodyAtomEntries body)) σ := by
  have hRespect :
      RewriteRespects rw σ := by
    unfold equalityRewrite at hRewrite
    exact
      equalityRewriteFrom_respects_of_bodySat
        P I S deltaAt? 0 body hRewrite
        (RewriteRespects.nil σ) hBody
  have hRel :
      RelBodySatWithDelta P I S deltaAt? 0 body σ :=
    BodySatWithDelta.rel P I S deltaAt? σ 0 body hBody
  exact
    relEntriesSat_rewrite_complete P I S deltaAt?
      rw hRespect 0 body hRel

theorem normalized_relEntries_to_source_bodySat
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    {body : List (Atom D Γ)}
    {rw : EqRewrite D}
    {σ : Assign D}
    (hRewrite : equalityRewrite body = some rw)
    (hRel :
      RelEntriesSatWithDelta P I S deltaAt?
        (rewriteRelEntries rw (relBodyAtomEntries body)) σ) :
    BodySatWithDelta P I S deltaAt? 0 body
      (normalizedAssign rw σ) := by
  have hRelBody :
      RelBodySatWithDelta P I S deltaAt? 0 body
        (normalizedAssign rw σ) :=
    relBodySat_rewrite_sound P I S deltaAt?
      rw 0 body σ hRel
  exact
    bodySatWithDelta_of_rel_and_equalities
      P I S deltaAt? (normalizedAssign rw σ)
      0 body hRelBody
      (equalities_true_of_equalityRewrite hRewrite σ)

omit [Domain D] [LinearOrder D] in
theorem SlotAssign.lookupSlot_eq_getElem
    {ρ : SlotAssign D}
    {slot : Nat}
    (hSlot : slot < ρ.values.size) :
    ρ.lookupSlot slot = ρ.values[slot] := by
  simp [SlotAssign.lookupSlot, hSlot]

omit [Domain D] [LinearOrder D] in
theorem SlotAssign.empty_coherent
    (env : SlotEnv) :
    SlotAssign.Coherent env (SlotAssign.empty (D := D) env.size) := by
  constructor
  · simp [SlotAssign.empty, SlotEnv.size]
  · intro x slot hSlot
    have hBound := SlotEnv.slotOf_bound hSlot
    change (SlotAssign.empty (D := D) env.size).lookupSlot
        slot = PartialAssign.lookup [] x
    unfold SlotAssign.lookupSlot
    have hSize :
        slot <
          (SlotAssign.empty (D := D) env.size).values.size := by
      simpa [SlotAssign.empty, SlotEnv.size] using hBound
    rw [Array.getElem?_eq_getElem hSize]
    simp [SlotAssign.empty, PartialAssign.lookup]

omit [LinearOrder D] in
theorem SlotAssign.evalTerm?_eq_partial_of_coherent
    {env : SlotEnv}
    {ρ : SlotAssign D}
    {term : SlotTerm D}
    (hCoherent : ρ.Coherent env)
    (hTerm : term.WF env) :
    ρ.evalTerm? term =
      PartialAssign.evalTerm? ρ.bindings term.toRelTerm := by
  cases term with
  | var x slot =>
      exact hCoherent.2 x slot hTerm
  | const d =>
      rfl

omit [LinearOrder D] in
theorem SlotAssign.evalAtomTuple_eq_headTupleOfAtomPartial_of_coherent
    {env : SlotEnv}
    {a : SlotRelAtom D Γ}
    {ρ : SlotAssign D}
    (hCoherent : ρ.Coherent env)
    (hAtom : a.WF env) :
    SlotAssign.evalAtomTuple a ρ =
      headTupleOfAtomPartial a.toRelAtom ρ.bindings := by
  apply Vector.ext
  intro i hi
  let j : Fin (Γ.arity a.source.rel) := ⟨i, hi⟩
  change
    (SlotAssign.evalAtomTuple a ρ).get j =
      (headTupleOfAtomPartial a.toRelAtom ρ.bindings).get j
  have hArg :
      SlotTerm.toRelTerm (a.args.get j) =
        a.source.args.get j := by
    simpa [Vector.get, Vector.getElem_map] using
      congrArg (fun v => v.get j) a.args_toRel
  have hEval :=
    SlotAssign.evalTerm?_eq_partial_of_coherent
      (env := env) hCoherent (hAtom j)
  rw [hArg] at hEval
  cases hTerm : a.args.get j with
  | var x slot =>
      have hSource :
          a.source.args.get j = RelTerm.var x := by
        simpa [hTerm, SlotTerm.toRelTerm] using hArg.symm
      have hTerm' :
          a.args[j.1] = SlotTerm.var x slot := by
        simpa [Vector.get] using hTerm
      have hSource' :
          a.source.args[j.1] = RelTerm.var x := by
        simpa [Vector.get] using hSource
      have hEval' :
          ρ.lookupSlot slot =
            PartialAssign.lookup ρ.bindings x := by
        simpa [hTerm, hSource, SlotAssign.evalTerm?,
          PartialAssign.evalTerm?] using hEval
      simp [SlotAssign.evalAtomTuple,
        headTupleOfAtomPartial, SlotRelAtom.toRelAtom,
        Vector.get, hTerm', hSource',
        SlotAssign.evalTerm?, hEval']
  | const d =>
      have hSource :
          a.source.args.get j = RelTerm.const d := by
        simpa [hTerm, SlotTerm.toRelTerm] using hArg.symm
      have hTerm' :
          a.args[j.1] = SlotTerm.const d := by
        simpa [Vector.get] using hTerm
      have hSource' :
          a.source.args[j.1] = RelTerm.const d := by
        simpa [Vector.get] using hSource
      simp [SlotAssign.evalAtomTuple,
        headTupleOfAtomPartial, SlotRelAtom.toRelAtom,
        Vector.get, hTerm', hSource',
        SlotAssign.evalTerm?]

/-
  These lemmas bridge the array-backed slot runtime to the
  proof-facing partial-assignment semantics. The executable
  path reads, binds, selects indexed candidates, and
  materializes heads from slot arrays; the proofs below use
  `SlotAssign.Coherent` and `SlotRelAtom.WF` to connect that
  execution view to the existing semantic proofs.
-/

set_option linter.flexible false in
omit [LinearOrder D] in
theorem slot_matchTerm_bindings
    {ρ ρ' : SlotAssign D}
    {term : SlotTerm D}
    {d : D}
    (hMatch :
      SlotAssign.matchTerm ρ term d = some ρ') :
    matchTerm ρ.bindings term.toRelTerm d =
      some ρ'.bindings := by
  cases term with
  | var x slot =>
      unfold SlotAssign.matchTerm SlotAssign.bind at hMatch
      unfold matchTerm SlotTerm.toRelTerm
      by_cases hSlot : slot < ρ.values.size
      · simp [hSlot] at hMatch
        cases hVal : ρ.values[slot] with
        | none =>
            simp [hVal] at hMatch
            cases hBind :
                PartialAssign.bind ρ.bindings x d with
            | none =>
                simp [hBind] at hMatch
            | some bindings' =>
                simp [hBind] at hMatch
                cases hMatch
                simp [hBind]
        | some d' =>
            simp [hVal] at hMatch
            by_cases hEq : d' = d
            · simp [hEq] at hMatch
              cases hBind :
                  PartialAssign.bind ρ.bindings x d with
              | none =>
                  simp [hBind] at hMatch
              | some bindings' =>
                  simp [hBind] at hMatch
                  cases hMatch
                  simp [hBind]
            · simp [hEq] at hMatch
      · simp [hSlot] at hMatch
  | const c =>
      unfold matchTerm SlotTerm.toRelTerm
      by_cases hEq : c = d
      · simp [SlotAssign.matchTerm, hEq] at hMatch
        simp [hEq]
        cases hMatch
        rfl
      · simp [SlotAssign.matchTerm, hEq] at hMatch

set_option linter.flexible false in
omit [LinearOrder D] in
theorem SlotAssign.bind_bindings_option_of_coherent
    {env : SlotEnv}
    {ρ : SlotAssign D}
    {x : Var}
    {slot : Nat}
    {d : D}
    (hCoherent : ρ.Coherent env)
    (hSlotEnv : env.slotOf x = some slot) :
    (ρ.bind x slot d).map (fun ρ' => ρ'.bindings) =
      PartialAssign.bind ρ.bindings x d := by
  have hSlotBoundEnv := SlotEnv.slotOf_bound hSlotEnv
  have hSlotBound : slot < ρ.values.size := by
    simpa [hCoherent.1] using hSlotBoundEnv
  have hLookup := hCoherent.2 x slot hSlotEnv
  rw [SlotAssign.lookupSlot_eq_getElem hSlotBound] at hLookup
  unfold SlotAssign.bind PartialAssign.bind
  simp [hSlotBound]
  cases hVal : ρ.values[slot] with
  | none =>
      have hLookupNone :
          PartialAssign.lookup ρ.bindings x = none := by
        simpa [hVal] using hLookup.symm
      simp [hLookupNone]
  | some d' =>
      have hLookupSome :
          PartialAssign.lookup ρ.bindings x = some d' := by
        simpa [hVal] using hLookup.symm
      by_cases hEq : d' = d
      · simp [hEq, hLookupSome]
      · simp [hEq, hLookupSome]

set_option linter.flexible false in
omit [LinearOrder D] in
theorem SlotAssign.bind_coherent
    {env : SlotEnv}
    {ρ ρ' : SlotAssign D}
    {x : Var}
    {slot : Nat}
    {d : D}
    (hEnvWF : env.WellFormed)
    (hCoherent : ρ.Coherent env)
    (hSlotEnv : env.slotOf x = some slot)
    (hBind : ρ.bind x slot d = some ρ') :
    ρ'.Coherent env := by
  have hSlotBoundEnv := SlotEnv.slotOf_bound hSlotEnv
  have hSlotBound : slot < ρ.values.size := by
    simpa [hCoherent.1] using hSlotBoundEnv
  have hLookup := hCoherent.2 x slot hSlotEnv
  rw [SlotAssign.lookupSlot_eq_getElem hSlotBound] at hLookup
  unfold SlotAssign.bind at hBind
  simp [hSlotBound] at hBind
  cases hVal : ρ.values[slot] with
  | none =>
      simp [hVal] at hBind
      cases hPartial :
          PartialAssign.bind ρ.bindings x d with
      | none =>
          simp [hPartial] at hBind
      | some bindings' =>
          simp [hPartial] at hBind
          cases hBind
          constructor
          · simp [Array.size_set, hCoherent.1]
          · intro y slotY hSlotY
            have hSlotYBoundEnv :=
              SlotEnv.slotOf_bound hSlotY
            have hSlotYBound :
                slotY < ρ.values.size := by
              simpa [hCoherent.1] using hSlotYBoundEnv
            have hLookupOld := hCoherent.2 y slotY hSlotY
            have hPartialLookup :=
              PartialAssign.lookup_bind_eq
                (ρ := ρ.bindings) (ρ' := bindings')
                (x := x) (y := y) (d := d) hPartial
            unfold SlotAssign.lookupSlot
            rw [Array.getElem?_set hSlotBound]
            by_cases hSlotEq : slot = slotY
            · have hyx : y = x :=
                SlotEnv.slotOf_injective hEnvWF
                  hSlotY
                  (by simpa [hSlotEq] using hSlotEnv)
              subst hyx
              simp [hSlotEq, hPartialLookup]
            · have hyx : y ≠ x := by
                intro hyx
                subst hyx
                rw [hSlotEnv] at hSlotY
                cases hSlotY
                exact hSlotEq rfl
              simp [hSlotEq, hPartialLookup, hyx]
              exact hLookupOld
  | some d' =>
      simp [hVal] at hBind
      by_cases hEq : d' = d
      · simp [hEq] at hBind
        cases hPartial :
            PartialAssign.bind ρ.bindings x d with
        | none =>
            simp [hPartial] at hBind
        | some bindings' =>
            simp [hPartial] at hBind
            cases hBind
            constructor
            · exact hCoherent.1
            · intro y slotY hSlotY
              have hLookupOld := hCoherent.2 y slotY hSlotY
              have hPartialLookup :=
                PartialAssign.lookup_bind_eq
                  (ρ := ρ.bindings) (ρ' := bindings')
                  (x := x) (y := y) (d := d) hPartial
              by_cases hyx : y = x
              · subst hyx
                rw [hSlotEnv] at hSlotY
                cases hSlotY
                have hOldSlot :
                    ρ.lookupSlot slot = some d := by
                  rw [SlotAssign.lookupSlot_eq_getElem hSlotBound,
                    hVal, hEq]
                simpa [hPartialLookup] using hOldSlot
              · simpa [hPartialLookup, hyx] using hLookupOld
      · simp [hEq] at hBind

omit [LinearOrder D] in
theorem slot_matchTerm_bindings_option
    {env : SlotEnv}
    {ρ : SlotAssign D}
    {term : SlotTerm D}
    {d : D}
    (hCoherent : ρ.Coherent env)
    (hTerm : term.WF env) :
    (SlotAssign.matchTerm ρ term d).map
        (fun ρ' => ρ'.bindings) =
      matchTerm ρ.bindings term.toRelTerm d := by
  cases term with
  | var x slot =>
      exact
        SlotAssign.bind_bindings_option_of_coherent
          hCoherent hTerm
  | const c =>
      by_cases hEq : c = d
      · simp [SlotAssign.matchTerm, matchTerm,
          SlotTerm.toRelTerm, hEq]
      · simp [SlotAssign.matchTerm, matchTerm,
          SlotTerm.toRelTerm, hEq]

set_option linter.flexible false in
omit [LinearOrder D] in
theorem slot_matchTerm_coherent
    {env : SlotEnv}
    {ρ ρ' : SlotAssign D}
    {term : SlotTerm D}
    {d : D}
    (hEnvWF : env.WellFormed)
    (hCoherent : ρ.Coherent env)
    (hTerm : term.WF env)
    (hMatch : SlotAssign.matchTerm ρ term d = some ρ') :
    ρ'.Coherent env := by
  cases term with
  | var x slot =>
      exact
        SlotAssign.bind_coherent hEnvWF hCoherent
          hTerm hMatch
  | const c =>
      unfold SlotAssign.matchTerm at hMatch
      by_cases hEq : c = d
      · simp [hEq] at hMatch
        cases hMatch
        exact hCoherent
      · simp [hEq] at hMatch

omit [LinearOrder D] in
theorem slot_matchTerms_bindings_option :
    ∀ {env : SlotEnv} (ρ : SlotAssign D)
      (terms : List (SlotTerm D)) (ds : List D),
      env.WellFormed →
      ρ.Coherent env →
      (∀ term : SlotTerm D, term ∈ terms → term.WF env) →
      (SlotAssign.matchTerms ρ terms ds).map
          (fun ρ' => ρ'.bindings) =
        matchTerms ρ.bindings
          (terms.map SlotTerm.toRelTerm) ds
| env, ρ, [], [], _hEnvWF, _hCoherent, _hTerms => by
    simp [SlotAssign.matchTerms, matchTerms]
| env, ρ, [], _d :: _ds, _hEnvWF, _hCoherent, _hTerms => by
    simp [SlotAssign.matchTerms, matchTerms]
| env, ρ, _term :: _terms, [], _hEnvWF, _hCoherent, _hTerms => by
    simp [SlotAssign.matchTerms, matchTerms]
| env, ρ, term :: terms, d :: ds, hEnvWF, hCoherent, hTerms => by
    unfold SlotAssign.matchTerms matchTerms
    have hTerm : term.WF env :=
      hTerms term (by simp)
    have hOption :=
      slot_matchTerm_bindings_option
        (env := env) (ρ := ρ) (term := term) (d := d)
        hCoherent hTerm
    cases hMatch : SlotAssign.matchTerm ρ term d with
    | none =>
        have hOld :
            matchTerm ρ.bindings term.toRelTerm d = none := by
          simpa [hMatch] using hOption.symm
        simp [hOld]
    | some ρ' =>
        have hOld :
            matchTerm ρ.bindings term.toRelTerm d =
              some ρ'.bindings := by
          simpa [hMatch] using hOption.symm
        have hCoherent' :
            ρ'.Coherent env :=
          slot_matchTerm_coherent
            (env := env) hEnvWF hCoherent hTerm hMatch
        have hTermsTail :
            ∀ term' : SlotTerm D,
              term' ∈ terms → term'.WF env := by
          intro term' hterm'
          exact hTerms term' (by simp [hterm'])
        simp [hOld,
          slot_matchTerms_bindings_option
            (env := env) ρ' terms ds hEnvWF hCoherent'
            hTermsTail]

set_option linter.flexible false in
omit [LinearOrder D] in
theorem slot_matchTerms_coherent :
    ∀ {env : SlotEnv} {ρ ρ' : SlotAssign D}
      (terms : List (SlotTerm D)) (ds : List D),
      env.WellFormed →
      ρ.Coherent env →
      (∀ term : SlotTerm D, term ∈ terms → term.WF env) →
      SlotAssign.matchTerms ρ terms ds = some ρ' →
        ρ'.Coherent env
| env, ρ, ρ', [], [], _hEnvWF, hCoherent,
    _hTerms, hMatch => by
    simp [SlotAssign.matchTerms] at hMatch
    cases hMatch
    exact hCoherent
| env, ρ, ρ', [], _d :: _ds, _hEnvWF, _hCoherent,
    _hTerms, hMatch => by
    simp [SlotAssign.matchTerms] at hMatch
| env, ρ, ρ', _term :: _terms, [], _hEnvWF,
    _hCoherent, _hTerms, hMatch => by
    simp [SlotAssign.matchTerms] at hMatch
| env, ρ, ρ', term :: terms, d :: ds, hEnvWF,
    hCoherent, hTerms, hMatch => by
    unfold SlotAssign.matchTerms at hMatch
    have hTerm : term.WF env :=
      hTerms term (by simp)
    cases hHead :
        SlotAssign.matchTerm ρ term d with
    | none =>
        simp [hHead] at hMatch
    | some ρ₁ =>
        have hCoherent₁ :
            ρ₁.Coherent env :=
          slot_matchTerm_coherent
            (env := env) hEnvWF hCoherent hTerm hHead
        have hTermsTail :
            ∀ term' : SlotTerm D,
              term' ∈ terms → term'.WF env := by
          intro term' hterm'
          exact hTerms term' (by simp [hterm'])
        exact
          slot_matchTerms_coherent
            (env := env) (ρ := ρ₁) (ρ' := ρ')
            terms ds hEnvWF hCoherent₁ hTermsTail
            (by simpa [hHead] using hMatch)

omit [LinearOrder D] in
theorem SlotRelAtom.wf_of_mem_args_toList
    {env : SlotEnv}
    {a : SlotRelAtom D Γ}
    (hAtom : a.WF env)
    {term : SlotTerm D}
    (hTerm : term ∈ a.args.toList) :
    term.WF env := by
  rcases List.get_of_mem hTerm with ⟨i, hGet⟩
  have hi : i.1 < Γ.arity a.source.rel := by
    simpa [Vector.length_toList] using i.2
  let j : Fin (Γ.arity a.source.rel) := ⟨i.1, hi⟩
  have hCoord :
      a.args.toList[i.1] = a.args[i.1] :=
    Vector.getElem_toList i.2
  have hTermEq :
      term = a.args.get j := by
    have hGetElem :
        a.args.toList[i.1] = term := by
      simpa using hGet
    have hCoord' :
        a.args.toList[i.1] = a.args.get j := by
      simp [Vector.get, j] at hCoord ⊢
    exact hGetElem.symm.trans
      hCoord'
  simpa [hTermEq] using hAtom j

omit [LinearOrder D] in
theorem slot_extendWithAtomTuple_bindings_option
    {env : SlotEnv}
    (ρ : SlotAssign D)
    (a : SlotRelAtom D Γ)
    (t : Tuple D (Γ.arity a.source.rel))
    (hEnvWF : env.WellFormed)
    (hCoherent : ρ.Coherent env)
    (hAtom : a.WF env) :
    (SlotAssign.extendWithAtomTuple ρ a t).map
        (fun ρ' => ρ'.bindings) =
      extendWithAtomRow ρ.bindings a.toRelAtom t := by
  unfold SlotAssign.extendWithAtomTuple extendWithAtomRow
  rw [slot_matchTerms_bindings_option
    (env := env) ρ a.args.toList t.toList hEnvWF
      hCoherent
      (by
        intro term hTerm
        exact SlotRelAtom.wf_of_mem_args_toList hAtom hTerm)]
  rw [SlotRelAtom.args_toRel_toList]
  rfl

omit [LinearOrder D] in
theorem slot_extendWithAtomTuple_coherent
    {env : SlotEnv}
    {ρ ρ' : SlotAssign D}
    {a : SlotRelAtom D Γ}
    {t : Tuple D (Γ.arity a.source.rel)}
    (hEnvWF : env.WellFormed)
    (hCoherent : ρ.Coherent env)
    (hAtom : a.WF env)
    (hExtend :
      SlotAssign.extendWithAtomTuple ρ a t = some ρ') :
    ρ'.Coherent env := by
  unfold SlotAssign.extendWithAtomTuple at hExtend
  exact
    slot_matchTerms_coherent
      (env := env) (ρ := ρ) (ρ' := ρ')
      a.args.toList t.toList hEnvWF hCoherent
      (by
        intro term hTerm
        exact SlotRelAtom.wf_of_mem_args_toList hAtom hTerm)
      hExtend

omit [LinearOrder D] in
theorem slot_filterMap_extendWithAtomTuple_bindings
    {env : SlotEnv}
    (ρ : SlotAssign D)
    (a : SlotRelAtom D Γ)
    (hEnvWF : env.WellFormed)
    (hCoherent : ρ.Coherent env)
    (hAtom : a.WF env) :
    ∀ tuples : List (Tuple D (Γ.arity a.source.rel)),
      ((tuples.filterMap
        (fun t => SlotAssign.extendWithAtomTuple ρ a t)).map
          (fun ρ' => ρ'.bindings)) =
        tuples.filterMap
          (fun t => extendWithAtomRow ρ.bindings a.toRelAtom t)
| [] => by
    rfl
| t :: tuples => by
    have hOption :=
      slot_extendWithAtomTuple_bindings_option
        (env := env) ρ a t hEnvWF hCoherent hAtom
    cases hSlot :
        SlotAssign.extendWithAtomTuple ρ a t with
    | none =>
        have hOld :
            extendWithAtomRow ρ.bindings a.toRelAtom t =
              none := by
          simpa [hSlot] using hOption.symm
        simp [List.filterMap, hSlot, hOld,
          slot_filterMap_extendWithAtomTuple_bindings
            (env := env) ρ a hEnvWF hCoherent hAtom tuples]
    | some ρ' =>
        have hOld :
            extendWithAtomRow ρ.bindings a.toRelAtom t =
              some ρ'.bindings := by
          simpa [hSlot] using hOption.symm
        simp [List.filterMap, hSlot, hOld,
          slot_filterMap_extendWithAtomTuple_bindings
            (env := env) ρ a hEnvWF hCoherent hAtom tuples]

omit [LinearOrder D] in
theorem slotBoundColumnDataFrom_eq_boundColumnDataFrom
    {env : SlotEnv}
    {ρ : SlotAssign D}
    {a : SlotRelAtom D Γ}
    (hCoherent : ρ.Coherent env)
    (hAtom : a.WF env) :
    ∀ cols : List (Fin (Γ.arity a.source.rel)),
      slotBoundColumnDataFrom ρ a cols =
        boundColumnDataFrom ρ.bindings a.toRelAtom cols
| [] => rfl
| i :: is => by
    have hArg :
        SlotTerm.toRelTerm (a.args.get i) =
          a.source.args.get i := by
      simpa [Vector.get, Vector.getElem_map] using
        congrArg (fun v => v.get i) a.args_toRel
    have hEval :
        SlotAssign.evalTerm? ρ (a.args.get i) =
          PartialAssign.evalTerm? ρ.bindings
            (a.toRelAtom.args.get i) := by
      have hEval' :=
        SlotAssign.evalTerm?_eq_partial_of_coherent
          (env := env) hCoherent (hAtom i)
      simpa [SlotRelAtom.toRelAtom, hArg] using hEval'
    unfold slotBoundColumnDataFrom boundColumnDataFrom
    cases hSlotEval :
        SlotAssign.evalTerm? ρ (a.args.get i) with
    | none =>
        have hPartialEval :
            PartialAssign.evalTerm? ρ.bindings
                (a.toRelAtom.args.get i) =
              none := by
          simpa [hSlotEval] using hEval.symm
        simp [hPartialEval,
          slotBoundColumnDataFrom_eq_boundColumnDataFrom
            hCoherent hAtom is]
    | some d =>
        have hPartialEval :
            PartialAssign.evalTerm? ρ.bindings
                (a.toRelAtom.args.get i) =
              some d := by
          simpa [hSlotEval] using hEval.symm
        simp [hPartialEval]
        rfl

omit [LinearOrder D] in
theorem slotBoundColumnData_eq_boundColumnData
    {env : SlotEnv}
    {ρ : SlotAssign D}
    {a : SlotRelAtom D Γ}
    (hCoherent : ρ.Coherent env)
    (hAtom : a.WF env) :
    slotBoundColumnData? ρ a =
      boundColumnData? ρ.bindings a.toRelAtom := by
  unfold slotBoundColumnData? boundColumnData?
  exact slotBoundColumnDataFrom_eq_boundColumnDataFrom
    hCoherent hAtom _

set_option linter.flexible false in
theorem indexedSlotAtomCandidatesFor_eq
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (idx : Nat)
    {env : SlotEnv}
    (ρ : SlotAssign D)
    (a : SlotRelAtom D Γ)
    (hCoherent : ρ.Coherent env)
    (hAtom : a.WF env) :
    P.indexedSlotAtomCandidatesFor I C S deltaAt? idx ρ a =
      P.indexedAtomCandidatesFor I C S deltaAt? idx
        ρ.bindings a.toRelAtom := by
  have hPair :=
    slotBoundColumnData_eq_boundColumnData
      (env := env) (ρ := ρ) (a := a) hCoherent hAtom
  unfold indexedSlotAtomCandidatesFor indexedAtomCandidatesFor
    slotAllBoundAtomCandidatesFor allBoundAtomCandidatesFor
    slotAllBoundAtomTuple?
  cases hAll :
      allBoundAtomTuple? ρ.bindings a.toRelAtom with
  | some u =>
      simp [slotAtomTupleMembershipCandidatesFor,
        SlotRelAtom.toRelAtom]
  | none =>
      simp
      cases hSlot : slotBoundColumnData? ρ a with
      | none =>
          cases hPartial :
              boundColumnData? ρ.bindings a.toRelAtom with
          | none =>
              simp [slotAtomTuplesFor]
          | some column =>
              have hDataNone :
                  boundColumnData? ρ.bindings a.toRelAtom =
                    none := by
                rw [← hPair, hSlot]
                rfl
              rw [hDataNone] at hPartial
              simp at hPartial
      | some slotColumn =>
          cases hPartial :
              boundColumnData? ρ.bindings a.toRelAtom with
          | none =>
              have hDataSome :
                  boundColumnData? ρ.bindings a.toRelAtom =
                    some slotColumn := by
                rw [← hPair, hSlot]
              rw [hPartial] at hDataSome
              simp at hDataSome
          | some column =>
              have hDataSlot :
                  boundColumnData? ρ.bindings a.toRelAtom =
                    some slotColumn := by
                rw [← hPair, hSlot]
              have hSome :
                  slotColumn = column := by
                apply Option.some.inj
                rw [← hDataSlot, hPartial]
                rfl
              cases hSome
              simp [slotAtomIndexedTuplesFor,
                atomIndexedTuplesFor, SlotRelAtom.toRelAtom]

theorem extendSlotAssignmentsWithAtomIndexedList_bindings
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (idx : Nat)
    {env : SlotEnv}
    (assignments : List (SlotAssign D))
    (a : SlotRelAtom D Γ)
    (hEnvWF : env.WellFormed)
    (hAssignments :
      ∀ ρ : SlotAssign D, ρ ∈ assignments →
        ρ.Coherent env)
    (hAtom : a.WF env) :
    (P.extendSlotAssignmentsWithAtomIndexedList
        I C S deltaAt? idx assignments a).map
        (fun ρ => ρ.bindings) =
      P.extendAssignmentsWithAtomIndexedList
        I C S deltaAt? idx
        (assignments.map (fun ρ => ρ.bindings))
        a.toRelAtom := by
  induction assignments with
  | nil =>
      simp [extendSlotAssignmentsWithAtomIndexedList,
        extendAssignmentsWithAtomIndexedList]
  | cons ρ assignments ih =>
      have hρ : ρ.Coherent env :=
        hAssignments ρ (by simp)
      have hTail :
          ∀ ρ' : SlotAssign D, ρ' ∈ assignments →
            ρ'.Coherent env := by
        intro ρ' hρ'
        exact hAssignments ρ' (by simp [hρ'])
      unfold extendSlotAssignmentsWithAtomIndexedList
        extendAssignmentsWithAtomIndexedList
      simp only [List.flatMap_cons, List.map_append,
        List.map_cons]
      rw [indexedSlotAtomCandidatesFor_eq
        P I C S deltaAt? idx ρ a hρ hAtom]
      rw [slot_filterMap_extendWithAtomTuple_bindings
        (env := env) ρ a hEnvWF hρ hAtom]
      exact congrArg
        (fun tail =>
          List.filterMap
              (fun t =>
                extendWithAtomRow ρ.bindings a.toRelAtom t)
              (P.indexedAtomCandidatesFor I C S deltaAt?
                idx ρ.bindings a.toRelAtom) ++ tail)
        (ih hTail)

theorem extendSlotAssignmentsWithAtomIndexedList_coherent
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (idx : Nat)
    {env : SlotEnv}
    (assignments : List (SlotAssign D))
    (a : SlotRelAtom D Γ)
    (hEnvWF : env.WellFormed)
    (hAssignments :
      ∀ ρ : SlotAssign D, ρ ∈ assignments →
        ρ.Coherent env)
    (hAtom : a.WF env) :
    ∀ ρ' : SlotAssign D,
      ρ' ∈
          P.extendSlotAssignmentsWithAtomIndexedList
            I C S deltaAt? idx assignments a →
        ρ'.Coherent env := by
  intro ρ' hρ'
  unfold extendSlotAssignmentsWithAtomIndexedList at hρ'
  rw [List.mem_flatMap] at hρ'
  rcases hρ' with ⟨ρ, hρ, hρ'⟩
  rw [List.mem_filterMap] at hρ'
  rcases hρ' with ⟨t, _ht, hExtend⟩
  exact
    slot_extendWithAtomTuple_coherent
      (env := env) hEnvWF
      (hAssignments ρ hρ) hAtom hExtend

theorem joinCompiledSlotRelAtomsFromIndexedList_bindings
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat) :
    ∀ {env : SlotEnv}
      (entries : List (Nat × SlotRelAtom D Γ))
      (assignments : List (SlotAssign D)),
      env.WellFormed →
      (∀ entry : Nat × SlotRelAtom D Γ,
        entry ∈ entries → entry.2.WF env) →
      (∀ ρ : SlotAssign D, ρ ∈ assignments →
        ρ.Coherent env) →
      (P.joinCompiledSlotRelAtomsFromIndexedList
          I C S deltaAt? entries assignments).map
          (fun ρ => ρ.bindings) =
        P.joinCompiledRelAtomsFromIndexedList
          I C S deltaAt?
          (entries.map (fun entry =>
            (entry.1, entry.2.toRelAtom)))
          (assignments.map (fun ρ => ρ.bindings))
| env, [], assignments, _hEnvWF, _hEntries, _hAssignments => by
    simp [joinCompiledSlotRelAtomsFromIndexedList,
      joinCompiledRelAtomsFromIndexedList]
| env, (idx, a) :: entries, assignments, hEnvWF,
    hEntries, hAssignments => by
    have hAtom : a.WF env :=
      hEntries (idx, a) (by simp)
    have hEntriesTail :
        ∀ entry : Nat × SlotRelAtom D Γ,
          entry ∈ entries → entry.2.WF env := by
      intro entry hEntry
      exact hEntries entry (by simp [hEntry])
    have hExtendedCoherent :
        ∀ ρ : SlotAssign D,
          ρ ∈
              P.extendSlotAssignmentsWithAtomIndexedList
                I C S deltaAt? idx assignments a →
            ρ.Coherent env :=
      extendSlotAssignmentsWithAtomIndexedList_coherent
        P I C S deltaAt? idx assignments a hEnvWF
        hAssignments hAtom
    simp [joinCompiledSlotRelAtomsFromIndexedList,
      joinCompiledRelAtomsFromIndexedList,
      joinCompiledSlotRelAtomsFromIndexedList_bindings
        P I C S deltaAt? (env := env) entries
        (P.extendSlotAssignmentsWithAtomIndexedList
          I C S deltaAt? idx assignments a)
        hEnvWF hEntriesTail hExtendedCoherent,
      extendSlotAssignmentsWithAtomIndexedList_bindings
        P I C S deltaAt? idx assignments a hEnvWF
        hAssignments hAtom]

theorem joinCompiledSlotRelAtomsFromIndexedList_coherent
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat) :
    ∀ {env : SlotEnv}
      (entries : List (Nat × SlotRelAtom D Γ))
      (assignments : List (SlotAssign D)),
      env.WellFormed →
      (∀ entry : Nat × SlotRelAtom D Γ,
        entry ∈ entries → entry.2.WF env) →
      (∀ ρ : SlotAssign D, ρ ∈ assignments →
        ρ.Coherent env) →
      ∀ ρ : SlotAssign D,
        ρ ∈ P.joinCompiledSlotRelAtomsFromIndexedList
              I C S deltaAt? entries assignments →
          ρ.Coherent env
| env, [], assignments, _hEnvWF, _hEntries,
    hAssignments, ρ, hρ => by
    simpa [joinCompiledSlotRelAtomsFromIndexedList] using
      hAssignments ρ hρ
| env, (idx, a) :: entries, assignments, hEnvWF,
    hEntries, hAssignments, ρ, hρ => by
    have hAtom : a.WF env :=
      hEntries (idx, a) (by simp)
    have hEntriesTail :
        ∀ entry : Nat × SlotRelAtom D Γ,
          entry ∈ entries → entry.2.WF env := by
      intro entry hEntry
      exact hEntries entry (by simp [hEntry])
    have hExtendedCoherent :
        ∀ ρ : SlotAssign D,
          ρ ∈
              P.extendSlotAssignmentsWithAtomIndexedList
                I C S deltaAt? idx assignments a →
            ρ.Coherent env :=
      extendSlotAssignmentsWithAtomIndexedList_coherent
        P I C S deltaAt? idx assignments a hEnvWF
        hAssignments hAtom
    exact
      joinCompiledSlotRelAtomsFromIndexedList_coherent
        P I C S deltaAt? (env := env) entries
        (P.extendSlotAssignmentsWithAtomIndexedList
          I C S deltaAt? idx assignments a)
        hEnvWF hEntriesTail hExtendedCoherent ρ
        (by simpa [joinCompiledSlotRelAtomsFromIndexedList] using hρ)

omit [LinearOrder D] in
theorem SlotEnv.compileRelEntries_toRelAtom
    (env : SlotEnv) :
    ∀ entries : List (Nat × RelAtom D Γ),
      (env.compileRelEntries entries).map
          (fun entry => (entry.1, entry.2.toRelAtom)) =
        entries
| [] => by
    simp [SlotEnv.compileRelEntries]
| (idx, a) :: entries => by
    unfold SlotEnv.compileRelEntries
    change
      (idx, (env.compileRelAtom a).toRelAtom) ::
          (env.compileRelEntries entries).map
            (fun entry => (entry.1, entry.2.toRelAtom)) =
        (idx, a) :: entries
    simp [SlotEnv.compileRelAtom, SlotRelAtom.toRelAtom]
    simpa [SlotRelAtom.toRelAtom] using
      SlotEnv.compileRelEntries_toRelAtom env entries

theorem joinPlannedSlotRelAtomsFromIndexedList_bindings
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (r : CompiledRule P)
    (assignments : List (SlotAssign D)) :
    (∀ ρ : SlotAssign D, ρ ∈ assignments →
        ρ.Coherent r.slotEnv) →
    (P.joinPlannedSlotRelAtomsFromIndexedList
        I C S deltaAt? r assignments).map
        (fun ρ => ρ.bindings) =
      P.joinPlannedRelAtomsFromIndexedList
        I C S deltaAt? r.normalizedRelBodyAtoms
        (assignments.map (fun ρ => ρ.bindings)) := by
  intro hAssignments
  unfold joinPlannedSlotRelAtomsFromIndexedList
    joinPlannedRelAtomsFromIndexedList
  let planned :=
    plannedRelBodyAtoms P I C S deltaAt?
      r.normalizedRelBodyAtoms
  have hEntriesWF :
      ∀ entry : Nat × SlotRelAtom D Γ,
        entry ∈ r.slotEnv.compileRelEntries planned →
          entry.2.WF r.slotEnv := by
    apply SlotEnv.compileRelEntries_wf
    intro x hx
    have hPerm :
        List.Perm planned r.normalizedRelBodyAtoms :=
      plannedRelBodyAtoms_perm P I C S deltaAt?
        r.normalizedRelBodyAtoms
    have hxNorm :
        x ∈ relEntryVarList (D := D)
          r.normalizedRelBodyAtoms :=
      (mem_relEntryVarList_iff_of_perm hPerm x).mp hx
    exact r.slotEnv_vars_cover x (by simp [hxNorm])
  rw [joinCompiledSlotRelAtomsFromIndexedList_bindings
    P I C S deltaAt? (env := r.slotEnv)
      (r.slotEnv.compileRelEntries planned) assignments
      r.slotEnv_wellFormed hEntriesWF hAssignments]
  rw [SlotEnv.compileRelEntries_toRelAtom]

theorem joinPlannedSlotRelAtomsFromIndexedList_coherent
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (r : CompiledRule P)
    (assignments : List (SlotAssign D))
    (hAssignments :
      ∀ ρ : SlotAssign D, ρ ∈ assignments →
        ρ.Coherent r.slotEnv) :
    ∀ ρ : SlotAssign D,
      ρ ∈ P.joinPlannedSlotRelAtomsFromIndexedList
            I C S deltaAt? r assignments →
        ρ.Coherent r.slotEnv := by
  intro ρ hρ
  unfold joinPlannedSlotRelAtomsFromIndexedList at hρ
  let planned :=
    plannedRelBodyAtoms P I C S deltaAt?
      r.normalizedRelBodyAtoms
  have hEntriesWF :
      ∀ entry : Nat × SlotRelAtom D Γ,
        entry ∈ r.slotEnv.compileRelEntries planned →
          entry.2.WF r.slotEnv := by
    apply SlotEnv.compileRelEntries_wf
    intro x hx
    have hPerm :
        List.Perm planned r.normalizedRelBodyAtoms :=
      plannedRelBodyAtoms_perm P I C S deltaAt?
        r.normalizedRelBodyAtoms
    have hxNorm :
        x ∈ relEntryVarList (D := D)
          r.normalizedRelBodyAtoms :=
      (mem_relEntryVarList_iff_of_perm hPerm x).mp hx
    exact r.slotEnv_vars_cover x (by simp [hxNorm])
  exact
    joinCompiledSlotRelAtomsFromIndexedList_coherent
      P I C S deltaAt? (env := r.slotEnv)
      (r.slotEnv.compileRelEntries planned) assignments
      r.slotEnv_wellFormed hEntriesWF hAssignments ρ hρ

set_option linter.flexible false in
theorem joinCompiledSlotRelAtomsAny_iff_exists_mem
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat) :
    ∀ (entries : List (Nat × SlotRelAtom D Γ))
      (assignments : List (SlotAssign D)),
      P.joinCompiledSlotRelAtomsAny I C S deltaAt?
          entries assignments = true ↔
        ∃ ρ : SlotAssign D,
          ρ ∈ P.joinCompiledSlotRelAtomsFromIndexedList
            I C S deltaAt? entries assignments
| [], assignments => by
    simp [joinCompiledSlotRelAtomsAny,
      joinCompiledSlotRelAtomsFromIndexedList,
      joinCompiledSlotRelAtomsExistsFrom,
      List.any_eq_true]
| (idx, a) :: entries, assignments => by
    let extended :=
      P.extendSlotAssignmentsWithAtomIndexedList
        I C S deltaAt? idx assignments a
    have ih :=
      joinCompiledSlotRelAtomsAny_iff_exists_mem
        P I C S deltaAt? entries
    constructor
    · intro hAny
      unfold joinCompiledSlotRelAtomsAny at hAny
      rw [List.any_eq_true] at hAny
      rcases hAny with ⟨ρ, hρ, hExists⟩
      unfold joinCompiledSlotRelAtomsExistsFrom at hExists
      rw [List.any_eq_true] at hExists
      rcases hExists with ⟨t, ht, hExtendExists⟩
      cases hExtend :
          SlotAssign.extendWithAtomTuple ρ a t with
      | none =>
          simp [hExtend] at hExtendExists
      | some ρ' =>
          simp [hExtend] at hExtendExists
          have hρ'Extended :
              ρ' ∈ extended := by
            unfold extended extendSlotAssignmentsWithAtomIndexedList
            rw [List.mem_flatMap]
            refine ⟨ρ, hρ, ?_⟩
            rw [List.mem_filterMap]
            exact ⟨t, ht, hExtend⟩
          have hTailAny :
              P.joinCompiledSlotRelAtomsAny I C S deltaAt?
                  entries extended = true := by
            unfold joinCompiledSlotRelAtomsAny
            rw [List.any_eq_true]
            exact ⟨ρ', hρ'Extended, hExtendExists⟩
          rcases (ih extended).mp hTailAny with
            ⟨ρFinal, hρFinal⟩
          exact
            ⟨ρFinal, by
              simpa [joinCompiledSlotRelAtomsFromIndexedList,
                extended] using hρFinal⟩
    · intro hMem
      rcases hMem with ⟨ρFinal, hρFinal⟩
      have hTailMem :
          ∃ ρFinal : SlotAssign D,
            ρFinal ∈
              P.joinCompiledSlotRelAtomsFromIndexedList
                I C S deltaAt? entries extended := by
        exact
          ⟨ρFinal, by
            simpa [joinCompiledSlotRelAtomsFromIndexedList,
              extended] using hρFinal⟩
      have hTailAny :
          P.joinCompiledSlotRelAtomsAny I C S deltaAt?
              entries extended = true :=
        (ih extended).mpr hTailMem
      unfold joinCompiledSlotRelAtomsAny at hTailAny
      rw [List.any_eq_true] at hTailAny
      rcases hTailAny with ⟨ρ', hρ'Extended, hExistsTail⟩
      unfold extended extendSlotAssignmentsWithAtomIndexedList
        at hρ'Extended
      rw [List.mem_flatMap] at hρ'Extended
      rcases hρ'Extended with ⟨ρ, hρ, hρ'⟩
      rw [List.mem_filterMap] at hρ'
      rcases hρ' with ⟨t, ht, hExtend⟩
      unfold joinCompiledSlotRelAtomsAny
      rw [List.any_eq_true]
      refine ⟨ρ, hρ, ?_⟩
      unfold joinCompiledSlotRelAtomsExistsFrom
      rw [List.any_eq_true]
      refine ⟨t, ht, ?_⟩
      simp [hExtend, hExistsTail]

set_option linter.flexible false in
theorem compiledBodySlotAssignmentExists_iff_exists_mem
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (r : CompiledRule P) :
    P.compiledBodySlotAssignmentExists I C S deltaAt? r = true ↔
      ∃ ρ : SlotAssign D,
        ρ ∈ P.compiledBodySlotAssignmentIndexedList
          I C S deltaAt? r := by
  unfold compiledBodySlotAssignmentExists
    compiledBodySlotAssignmentIndexedList
  by_cases hImpossible : r.normalizedImpossible
  · simp [hImpossible]
  · simp [hImpossible]
    let planned :=
      plannedRelBodyAtoms P I C S deltaAt?
        r.normalizedRelBodyAtoms
    exact
      P.joinCompiledSlotRelAtomsAny_iff_exists_mem
        I C S deltaAt?
        (r.slotEnv.compileRelEntries planned)
        [SlotAssign.empty r.slotEnv.size]

omit [LinearOrder D] in
theorem tuple_eq_nullaryHeadTuple
    {P : Program D Γ}
    (r : CompiledRule P)
    (hArity : Γ.arity r.source.head.rel = 0)
    (t : Tuple D (Γ.arity r.source.head.rel)) :
    t = nullaryHeadTuple r hArity := by
  have hEmpty :
      Tuple.castArity hArity.symm t = Tuple.empty := by
    apply Vector.ext
    intro i hi
    omega
  have hBack :=
    Tuple.castArity_symm hArity.symm t
  rw [hEmpty] at hBack
  exact hBack.symm

set_option linter.flexible false in
theorem compiledBodySlotAssignmentIndexedList_bindings
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (r : CompiledRule P) :
    (P.compiledBodySlotAssignmentIndexedList
        I C S deltaAt? r).map (fun ρ => ρ.bindings) =
      P.compiledBodyAssignmentIndexedList
        I C S deltaAt? r := by
  unfold compiledBodySlotAssignmentIndexedList
    compiledBodyAssignmentIndexedList
  by_cases hImpossible : r.normalizedImpossible
  · simp [hImpossible]
  · simp [hImpossible]
    rw [joinPlannedSlotRelAtomsFromIndexedList_bindings
      P I C S deltaAt? r [SlotAssign.empty r.slotEnv.size]
      (by
        intro ρ hρ
        simp at hρ
        subst ρ
        exact SlotAssign.empty_coherent r.slotEnv)]
    simp [SlotAssign.empty]

theorem compiledBodySlotAssignmentIndexedList_coherent
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (r : CompiledRule P) :
    ∀ ρ : SlotAssign D,
      ρ ∈ P.compiledBodySlotAssignmentIndexedList
            I C S deltaAt? r →
        ρ.Coherent r.slotEnv := by
  intro ρ hρ
  unfold compiledBodySlotAssignmentIndexedList at hρ
  by_cases hImpossible : r.normalizedImpossible
  · simp [hImpossible] at hρ
  · exact
      joinPlannedSlotRelAtomsFromIndexedList_coherent
        P I C S deltaAt? r
        [SlotAssign.empty r.slotEnv.size]
        (by
          intro ρ hρ
          simp at hρ
          subst ρ
          exact SlotAssign.empty_coherent r.slotEnv)
        ρ (by simpa [hImpossible] using hρ)

omit [LinearOrder D] in
theorem cast_headTupleOfAtomPartial_eq_of_atom_eq
    {a b : RelAtom D Γ}
    (h : a = b)
    (ρ : PartialAssign D) :
    cast
        (congrArg
          (fun a : RelAtom D Γ => Tuple D (Γ.arity a.rel))
          h)
        (headTupleOfAtomPartial a ρ) =
      headTupleOfAtomPartial b ρ := by
  cases h
  rfl

omit [LinearOrder D] in
theorem compiledHeadTupleOfSlotAssignment_eq_of_coherent
    {P : Program D Γ}
    (r : CompiledRule P)
    (ρ : SlotAssign D)
    (hCoherent : ρ.Coherent r.slotEnv)
    (hHeadWF : r.slotHead.WF r.slotEnv) :
    compiledHeadTupleOfSlotAssignment r ρ =
      cast
        (congrArg
          (fun X : Γ.syms => Tuple D (Γ.arity X))
          r.normalizedHead_rel_eq)
        (headTupleOfAtomPartial r.normalizedHead
          ρ.bindings) := by
  have hEval :=
    SlotAssign.evalAtomTuple_eq_headTupleOfAtomPartial_of_coherent
      (env := r.slotEnv) (a := r.slotHead) (ρ := ρ)
      hCoherent hHeadWF
  unfold compiledHeadTupleOfSlotAssignment
  rw [hEval]
  congr 1
  simpa [SlotRelAtom.toRelAtom] using
    cast_headTupleOfAtomPartial_eq_of_atom_eq
      r.slotHead_source_eq ρ.bindings

set_option linter.flexible false in
omit [LinearOrder D] in
theorem compiledHeadTupleListOfSlotAssignments_eq_of_coherent
    {P : Program D Γ}
    (r : CompiledRule P)
    (assignments : List (SlotAssign D))
    (hCoherent :
      ∀ ρ : SlotAssign D,
        ρ ∈ assignments → ρ.Coherent r.slotEnv)
    (hHeadWF : r.slotHead.WF r.slotEnv) :
    compiledHeadTupleListOfSlotAssignments r assignments =
      compiledHeadTupleListOfAssignments r
        (assignments.map (fun ρ => ρ.bindings)) := by
  simp [compiledHeadTupleListOfSlotAssignments,
    compiledHeadTupleListOfAssignments, List.map_map]
  intro ρ hρ
  simpa using
    compiledHeadTupleOfSlotAssignment_eq_of_coherent
      r ρ (hCoherent ρ hρ) hHeadWF

set_option linter.flexible false in
omit [LinearOrder D] in
theorem compiledProjectedHeadTupleListOfSlotAssignments_toFinset
    {P : Program D Γ}
    (r : CompiledRule P)
    (assignments : List (SlotAssign D)) :
    (compiledProjectedHeadTupleListOfSlotAssignments
        r assignments).toFinset =
      (compiledHeadTupleListOfSlotAssignments
        r assignments).toFinset := by
  unfold compiledProjectedHeadTupleListOfSlotAssignments
  by_cases hArity : Γ.arity r.source.head.rel = 0
  · simp [hArity]
    cases assignments with
    | nil =>
        simp [compiledHeadTupleListOfSlotAssignments]
    | cons ρ ρs =>
        apply Finset.ext
        intro t
        constructor
        · intro ht
          rw [List.mem_toFinset]
          unfold compiledHeadTupleListOfSlotAssignments
          rw [List.mem_map]
          refine
            ⟨ρ, by simp, ?_⟩
          · rw [tuple_eq_nullaryHeadTuple r hArity t]
            rw [tuple_eq_nullaryHeadTuple r hArity
              (compiledHeadTupleOfSlotAssignment r ρ)]
        · intro ht
          rw [List.mem_toFinset] at ht
          rw [List.mem_toFinset]
          rw [tuple_eq_nullaryHeadTuple r hArity t]
          simp
  · simp [hArity]

set_option linter.flexible false in
omit [LinearOrder D] in
theorem mem_insertTupleIfFresh_iff
    {n : Nat}
    (t u : Tuple D n)
    (seen : List (Tuple D n)) :
    u ∈ insertTupleIfFresh t seen ↔ u = t ∨ u ∈ seen := by
  unfold insertTupleIfFresh
  by_cases ht : t ∈ seen
  · simp [ht]
    intro hut
    rw [hut]
    exact ht
  · simp [ht]

omit [LinearOrder D] in
theorem mem_distinctHeadFold_iff
    {P : Program D Γ}
    (r : CompiledRule P)
    (assignments : List (SlotAssign D))
    (seen : List (Tuple D (Γ.arity r.source.head.rel)))
    (t : Tuple D (Γ.arity r.source.head.rel)) :
    t ∈ assignments.foldl
        (fun seen ρ =>
          insertTupleIfFresh
            (compiledHeadTupleOfSlotAssignment r ρ) seen)
        seen ↔
      t ∈ seen ∨
        ∃ ρ : SlotAssign D,
          ρ ∈ assignments ∧
            compiledHeadTupleOfSlotAssignment r ρ = t := by
  induction assignments generalizing seen with
  | nil =>
      simp
  | cons ρ assignments ih =>
      rw [List.foldl_cons, ih]
      rw [mem_insertTupleIfFresh_iff]
      constructor
      · intro h
        cases h with
        | inl h =>
            cases h with
            | inl ht =>
                exact Or.inr ⟨ρ, by simp, ht.symm⟩
            | inr ht =>
                exact Or.inl ht
        | inr h =>
            rcases h with ⟨ρ', hρ', hHead⟩
            exact Or.inr ⟨ρ', by simp [hρ'], hHead⟩
      · intro h
        cases h with
        | inl ht =>
            exact Or.inl (Or.inr ht)
        | inr h =>
            rcases h with ⟨ρ', hρ', hHead⟩
            rcases List.mem_cons.mp hρ' with hEq | hTail
            · subst hEq
              exact Or.inl (Or.inl hHead.symm)
            · exact Or.inr ⟨ρ', hTail, hHead⟩

omit [LinearOrder D] in
theorem distinctHeadFold_toFinset
    {P : Program D Γ}
    (r : CompiledRule P)
    (assignments : List (SlotAssign D)) :
    (assignments.foldl
        (fun seen ρ =>
          insertTupleIfFresh
            (compiledHeadTupleOfSlotAssignment r ρ) seen)
        []).toFinset =
      (compiledHeadTupleListOfSlotAssignments r
        assignments).toFinset := by
  apply Finset.ext
  intro t
  simp [List.mem_toFinset,
    mem_distinctHeadFold_iff, compiledHeadTupleListOfSlotAssignments,
    List.mem_map]

theorem compiledProjectionDistinctRuleConsequenceIndexedList_toFinset
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (r : CompiledRule P) :
    (P.compiledProjectionDistinctRuleConsequenceIndexedList
        I C S deltaAt? r).toFinset =
      (compiledHeadTupleListOfSlotAssignments r
        (P.compiledBodySlotAssignmentIndexedList
          I C S deltaAt? r)).toFinset := by
  unfold compiledProjectionDistinctRuleConsequenceIndexedList
  by_cases hImpossible : r.normalizedImpossible
  · simp [hImpossible, compiledBodySlotAssignmentIndexedList,
      compiledHeadTupleListOfSlotAssignments]
  · simp [hImpossible, distinctHeadFold_toFinset]

theorem compiledProjectedRuleConsequenceIndexedList_toFinset
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (r : CompiledRule P) :
    (P.compiledProjectedRuleConsequenceIndexedListCore
        I C S deltaAt? r).toFinset =
      (compiledHeadTupleListOfSlotAssignments r
        (P.compiledBodySlotAssignmentIndexedList
          I C S deltaAt? r)).toFinset := by
  unfold compiledProjectedRuleConsequenceIndexedListCore
  by_cases hArity : Γ.arity r.source.head.rel = 0
  · simp [hArity]
    by_cases hExists :
        P.compiledBodySlotAssignmentExists
          I C S deltaAt? r = true
    · rcases
        (P.compiledBodySlotAssignmentExists_iff_exists_mem
          I C S deltaAt? r).mp hExists with
        ⟨ρ, hρ⟩
      have hOldSingleton :
          (compiledHeadTupleListOfSlotAssignments r
            (P.compiledBodySlotAssignmentIndexedList
              I C S deltaAt? r)).toFinset =
            {nullaryHeadTuple r hArity} := by
        apply Finset.ext
        intro t
        constructor
        · intro _ht
          exact Finset.mem_singleton.mpr
            (tuple_eq_nullaryHeadTuple r hArity t)
        · intro ht
          have htEq :
              t = nullaryHeadTuple r hArity :=
            Finset.mem_singleton.mp ht
          rw [List.mem_toFinset]
          unfold compiledHeadTupleListOfSlotAssignments
          rw [List.mem_map]
          refine ⟨ρ, hρ, ?_⟩
          rw [htEq]
          exact tuple_eq_nullaryHeadTuple r hArity _
      simp [hExists, hOldSingleton]
    · have hOldEmpty :
          (compiledHeadTupleListOfSlotAssignments r
            (P.compiledBodySlotAssignmentIndexedList
              I C S deltaAt? r)).toFinset =
            ∅ := by
        apply Finset.ext
        intro t
        constructor
        · intro ht
          rw [List.mem_toFinset] at ht
          unfold compiledHeadTupleListOfSlotAssignments at ht
          rw [List.mem_map] at ht
          rcases ht with ⟨ρ, hρ, _hHead⟩
          have hExistsTrue :
              P.compiledBodySlotAssignmentExists
                I C S deltaAt? r = true :=
            (P.compiledBodySlotAssignmentExists_iff_exists_mem
              I C S deltaAt? r).mpr ⟨ρ, hρ⟩
          exact False.elim (hExists hExistsTrue)
        · intro ht
          simp at ht
      simp [hExists, hOldEmpty]
  · simp [hArity]
    by_cases hDistinct :
        compiledProjectionCanUseDistinctPath r
          (r.slotEnv.compileRelEntries
            (plannedRelBodyAtoms P I C S deltaAt?
              r.normalizedRelBodyAtoms)) = true
    · simp [hDistinct,
        compiledProjectionDistinctRuleConsequenceIndexedList_toFinset]
    · simp [hDistinct]

theorem joinCompiledRelAtomsFromIndexedList_sound_entries
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat) :
    ∀ (entries : List (Nat × RelAtom D Γ))
      (assignments : List (PartialAssign D))
      {ρ : PartialAssign D},
      ρ ∈ P.joinCompiledRelAtomsFromIndexedList
          I C S deltaAt? entries assignments →
        ∃ ρ₀ : PartialAssign D,
          ρ₀ ∈ assignments ∧
            PartialAssign.Extends ρ ρ₀ ∧
              RelEntriesSatWithDelta P I S deltaAt?
                entries (PartialAssign.toAssign ρ)
| [], assignments, ρ, hρ => by
    exact
      ⟨ρ, hρ, PartialAssign.Extends.refl ρ, by
        intro entry hEntry
        simp at hEntry⟩
| (idx, a) :: entries, assignments, ρ, hρ => by
    unfold joinCompiledRelAtomsFromIndexedList at hρ
    rcases
      joinCompiledRelAtomsFromIndexedList_sound_entries
        P I C S deltaAt? entries
        (P.extendAssignmentsWithAtomIndexedList
          I C S deltaAt? idx assignments a)
        hρ with
      ⟨ρ₁, hρ₁, hρExtρ₁, hTail⟩
    rw [extendAssignmentsWithAtomIndexedList,
      List.mem_flatMap] at hρ₁
    rcases hρ₁ with ⟨ρ₀, hρ₀, hρ₁⟩
    rw [List.mem_filterMap] at hρ₁
    rcases hρ₁ with ⟨t, ht, hExtend⟩
    have hρ₁Extρ₀ :
        PartialAssign.Extends ρ₁ ρ₀ :=
      extendWithAtomRow_extends ρ₀ ρ₁ a t hExtend
    have hρExtρ₀ :
        PartialAssign.Extends ρ ρ₀ :=
      hρExtρ₁.trans hρ₁Extρ₀
    have htSource :
        t ∈ P.atomTuplesFor I S deltaAt? idx a :=
      (P.indexedAtomCandidatesFor_mem_of_extend
        I C S deltaAt? idx ρ₀ ρ₁ a t hExtend).mp ht
    have hAtomEq :
        a.evalTuple (PartialAssign.toAssign ρ) = t :=
      extendWithAtomRow_evalTuple_of_extends
        ρ₀ ρ₁ ρ a t hExtend hρExtρ₁
    have hAtom :
        RelEntrySatWithDelta P I S deltaAt?
          (idx, a) (PartialAssign.toAssign ρ) := by
      unfold RelEntrySatWithDelta
      rw [hAtomEq]
      exact (P.mem_atomTuplesFor_iff I S deltaAt? idx a t).mp
        htSource
    exact
      ⟨ρ₀, hρ₀, hρExtρ₀, by
        intro entry hEntry
        rcases List.mem_cons.mp hEntry with hHead | hTailEntry
        · cases hHead
          exact hAtom
        · exact hTail entry hTailEntry⟩

theorem joinCompiledRelAtomsFromIndexedList_complete_entries
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat) :
    ∀ (entries : List (Nat × RelAtom D Γ))
      (assignments : List (PartialAssign D))
      (σ : Assign D) (ρ₀ : PartialAssign D),
      ρ₀ ∈ assignments →
        PartialAssign.ConsistentWith ρ₀ σ →
        RelEntriesSatWithDelta P I S deltaAt?
          entries σ →
          ∃ ρ : PartialAssign D,
            ρ ∈ P.joinCompiledRelAtomsFromIndexedList
                I C S deltaAt? entries assignments ∧
              PartialAssign.ConsistentWith ρ σ ∧
              PartialAssign.Extends ρ ρ₀ ∧
              PartialAssign.AgreesOn ρ σ
                (relEntryVarList (D := D) entries)
| [], assignments, _σ, ρ₀, hρ₀, hCons, _hEntries => by
    exact
      ⟨ρ₀, hρ₀, hCons,
        PartialAssign.Extends.refl ρ₀, by
          intro x hx
          simp [relEntryVarList] at hx⟩
| (idx, a) :: entries, assignments, σ, ρ₀, hρ₀,
    hCons, hEntries => by
    have hAtom :
        RelEntrySatWithDelta P I S deltaAt? (idx, a) σ :=
      hEntries (idx, a) (by simp)
    rcases extendWithAtomRow_complete
        ρ₀ σ a hCons with
      ⟨ρ₁, hExtend, hCons₁, hExt₁, hAtomAgree⟩
    have hTupleSource :
        a.evalTuple σ ∈
          P.atomTuplesFor I S deltaAt? idx a := by
      exact
        (P.mem_atomTuplesFor_iff I S deltaAt? idx a
          (a.evalTuple σ)).mpr hAtom
    have hCandidate :
        a.evalTuple σ ∈
          P.indexedAtomCandidatesFor I C S deltaAt?
            idx ρ₀ a :=
      (P.indexedAtomCandidatesFor_mem_of_extend
        I C S deltaAt? idx ρ₀ ρ₁ a
        (a.evalTuple σ) hExtend).mpr hTupleSource
    have hρ₁ :
        ρ₁ ∈
          P.extendAssignmentsWithAtomIndexedList
            I C S deltaAt? idx assignments a := by
      unfold extendAssignmentsWithAtomIndexedList
      rw [List.mem_flatMap]
      refine ⟨ρ₀, hρ₀, ?_⟩
      rw [List.mem_filterMap]
      exact ⟨a.evalTuple σ, hCandidate, hExtend⟩
    have hTailEntries :
        RelEntriesSatWithDelta P I S deltaAt?
          entries σ := by
      intro entry hEntry
      exact hEntries entry (List.mem_cons.mpr (Or.inr hEntry))
    rcases
      joinCompiledRelAtomsFromIndexedList_complete_entries
        P I C S deltaAt? entries
        (P.extendAssignmentsWithAtomIndexedList
          I C S deltaAt? idx assignments a)
        σ ρ₁ hρ₁ hCons₁ hTailEntries with
      ⟨ρ, hρ, hConsρ, hExtρ₁, hTailAgree⟩
    refine
      ⟨ρ, ?_, hConsρ, hExtρ₁.trans hExt₁, ?_⟩
    · simpa [joinCompiledRelAtomsFromIndexedList] using hρ
    · intro x hx
      have hx' :
          x ∈ a.varList ∨
            x ∈ relEntryVarList (D := D) entries := by
        simpa [relEntryVarList] using hx
      rcases hx' with hxAtom | hxTail
      · exact hExtρ₁ x (σ x) (hAtomAgree x hxAtom)
      · exact hTailAgree x
          (by simpa [relEntryVarList] using hxTail)

omit [LinearOrder D] in
private theorem atomRelVarList_subset_varList_for_planned
    (b : Atom D Γ)
    {x : Var}
    (hx : x ∈ b.relVarList) :
    x ∈ b.varList := by
  cases b with
  | rel a =>
      simpa [Atom.relVarList, Atom.varList] using hx
  | eq lhs rhs =>
      simp [Atom.relVarList] at hx

omit [LinearOrder D] in
private theorem bodyRelVarList_subset_varList_for_planned
    (body : List (Atom D Γ))
    {x : Var}
    (hx : x ∈ Body.relVarList body) :
    x ∈ Body.varList body := by
  unfold Body.relVarList Body.varList Atom.listRelVarList
    Atom.listVarList at *
  rw [List.mem_flatten] at hx ⊢
  rcases hx with ⟨xs, hxs, hx⟩
  rcases List.mem_map.mp hxs with ⟨b, hb, rfl⟩
  exact
    ⟨b.varList, List.mem_map.mpr ⟨b, hb, rfl⟩,
      atomRelVarList_subset_varList_for_planned b hx⟩

theorem headTupleListOfPlannedAssignments_toFinset
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (r : CompiledRule P) :
    (compiledHeadTupleListOfAssignments r
      (P.compiledBodyAssignmentIndexedList I C S
        deltaAt? r)).toFinset =
      P.ruleConsequenceWithDeltaAt I S deltaAt? r.source := by
  apply Finset.ext
  intro t
  constructor
  · intro ht
    rw [List.mem_toFinset] at ht
    unfold compiledHeadTupleListOfAssignments at ht
    rw [List.mem_map] at ht
    rcases ht with ⟨tn, htn, hCast⟩
    rw [List.mem_map] at htn
    rcases htn with ⟨ρ, hρ, hHead⟩
    by_cases hImpossible : r.normalizedImpossible = true
    · have hEmpty :
          P.compiledBodyAssignmentIndexedList I C S
            deltaAt? r = [] := by
        simp [compiledBodyAssignmentIndexedList, hImpossible]
      simp [hEmpty] at hρ
    · have hImpossibleFalse :
          r.normalizedImpossible = false :=
        Bool.eq_false_of_not_eq_true hImpossible
      have hRewriteSome :
          ∃ rw : EqRewrite D,
            equalityRewrite r.source.body = some rw := by
        have hNorm :
            normalizedImpossibleFor r.source.body = false := by
          rw [← r.normalizedImpossible_eq]
          exact hImpossibleFalse
        unfold normalizedImpossibleFor at hNorm
        cases hRewrite : equalityRewrite r.source.body with
        | none =>
            simp [hRewrite] at hNorm
        | some rw =>
            exact ⟨rw, rfl⟩
      rcases hRewriteSome with ⟨rw, hRewrite⟩
      have hρJoin :
          ρ ∈ P.joinPlannedRelAtomsFromIndexedList
            I C S deltaAt? r.normalizedRelBodyAtoms [[]] := by
        simpa [compiledBodyAssignmentIndexedList,
          hImpossibleFalse] using hρ
      have hNormEntries :
          r.normalizedRelBodyAtoms =
            rewriteRelEntries rw
              (relBodyAtomEntries r.source.body) := by
        rw [r.normalizedRelBodyAtoms_eq]
        simp [normalizedRelBodyAtomsFor, hRewrite]
      have hNormHead :
          r.normalizedHead =
            rewriteRelAtom rw r.source.head := by
        rw [r.normalizedHead_eq]
        simp [normalizedHeadFor, hRewrite]
      let planned :=
        plannedRelBodyAtoms P I C S deltaAt?
          r.normalizedRelBodyAtoms
      have hPermPlanned :
          List.Perm planned r.normalizedRelBodyAtoms := by
        exact plannedRelBodyAtoms_perm P I C S deltaAt?
          r.normalizedRelBodyAtoms
      unfold joinPlannedRelAtomsFromIndexedList at hρJoin
      rcases
        P.joinCompiledRelAtomsFromIndexedList_sound_entries
          I C S deltaAt? planned [[]] hρJoin with
        ⟨ρ₀, hρ₀, _hExtρ₀, hEntriesPlanned⟩
      have hρ₀ : ρ₀ = ([] : PartialAssign D) := by
        simpa using hρ₀
      subst ρ₀
      have hEntriesNormalized :
          RelEntriesSatWithDelta P I S deltaAt?
            r.normalizedRelBodyAtoms
            (PartialAssign.toAssign ρ) := by
        exact
          (P.relEntriesSatWithDelta_iff_of_perm
            I S deltaAt? hPermPlanned
            (PartialAssign.toAssign ρ)).mp hEntriesPlanned
      have hEntriesRewrite :
          RelEntriesSatWithDelta P I S deltaAt?
            (rewriteRelEntries rw
              (relBodyAtomEntries r.source.body))
            (PartialAssign.toAssign ρ) := by
        simpa [hNormEntries] using hEntriesNormalized
      have hBody :
          BodySatWithDelta P I S deltaAt? 0
            r.source.body
            (normalizedAssign rw
              (PartialAssign.toAssign ρ)) :=
        normalized_relEntries_to_source_bodySat
          P I S deltaAt? hRewrite hEntriesRewrite
      have hBound :
          ∀ x : Var,
            x ∈ Body.varList r.source.body →
              x ∈ Body.relVarList r.source.body := by
        intro x hx
        have hxBodyVars : x ∈ Body.vars r.source.body := by
          change x ∈ Atom.vars r.source.body
          unfold Atom.vars
          exact List.mem_toFinset.mpr hx
        have hSafe :=
          r.source.safe x
            (Finset.mem_union.mpr (Or.inr hxBodyVars))
        change x ∈ Atom.relVars r.source.body at hSafe
        unfold Atom.relVars at hSafe
        exact List.mem_toFinset.mp hSafe
      rcases
        P.bodyAssignments_complete I S deltaAt?
          r.source.body
          (normalizedAssign rw (PartialAssign.toAssign ρ))
          hBound hBody with
        ⟨ρ', hρ', hAgreeBody⟩
      have hSourceHeadEval :
          r.source.head.evalTuple
              (PartialAssign.toAssign ρ') =
            r.source.head.evalTuple
              (normalizedAssign rw
                (PartialAssign.toAssign ρ)) := by
        apply r.source.head.evalTuple_eq_of_assign_eq_on_vars
        intro x hxHead
        have hxHeadVars : x ∈ r.source.head.vars := by
          exact r.source.head.mem_vars_of_mem_varList hxHead
        have hxRel : x ∈ Body.relVarList r.source.body := by
          have hSafe :=
            r.source.safe x
              (Finset.mem_union.mpr (Or.inl hxHeadVars))
          change x ∈ Atom.relVars r.source.body at hSafe
          unfold Atom.relVars at hSafe
          exact List.mem_toFinset.mp hSafe
        exact hAgreeBody x
          (bodyRelVarList_subset_varList_for_planned
            r.source.body hxRel)
      have hNormHeadEval :
          cast
              (congrArg
                (fun X : Γ.syms =>
                  Tuple D (Γ.arity X))
                r.normalizedHead_rel_eq)
              (r.normalizedHead.evalTuple
                (PartialAssign.toAssign ρ)) =
            r.source.head.evalTuple
              (normalizedAssign rw
                (PartialAssign.toAssign ρ)) := by
        have hCastNorm :
            cast
                (congrArg
                  (fun X : Γ.syms =>
                    Tuple D (Γ.arity X))
                  r.normalizedHead_rel_eq)
                (r.normalizedHead.evalTuple
                  (PartialAssign.toAssign ρ)) =
              (rewriteRelAtom rw r.source.head).evalTuple
                (PartialAssign.toAssign ρ) :=
          cast_evalTuple_eq_of_atom_eq
            hNormHead r.normalizedHead_rel_eq
            (PartialAssign.toAssign ρ)
        exact hCastNorm.trans
          (rewriteRelAtom_evalTuple_normalizedAssign
            rw r.source.head (PartialAssign.toAssign ρ))
      have hPartial :
          cast
              (congrArg
                (fun X : Γ.syms =>
                  Tuple D (Γ.arity X))
                r.normalizedHead_rel_eq)
              tn =
            r.source.head.evalTuple
              (normalizedAssign rw
                (PartialAssign.toAssign ρ)) := by
        rw [← hHead]
        rw [headTupleOfAtomPartial_eq_evalTuple_toAssign]
        exact hNormHeadEval
      unfold ruleConsequenceWithDeltaAt headTuplesOfAssignments
      refine Finset.mem_image.mpr ?_
      refine ⟨ρ', hρ', ?_⟩
      rw [hSourceHeadEval, ← hPartial, hCast]
  · intro ht
    unfold ruleConsequenceWithDeltaAt headTuplesOfAssignments at ht
    rcases Finset.mem_image.mp ht with ⟨ρ₀, hρ₀, hHead⟩
    let σ : Assign D := PartialAssign.toAssign ρ₀
    have hBody :
        BodySatWithDelta P I S deltaAt? 0
          r.source.body σ :=
      P.bodyAssignments_sound I S deltaAt?
        r.source.body hρ₀
    by_cases hImpossible : r.normalizedImpossible = true
    · have hRewriteNone :
          equalityRewrite r.source.body = none := by
        have hNorm :
            normalizedImpossibleFor r.source.body = true := by
          rw [← r.normalizedImpossible_eq]
          exact hImpossible
        unfold normalizedImpossibleFor at hNorm
        cases hRewrite : equalityRewrite r.source.body with
        | none => exact rfl
        | some rw => simp [hRewrite] at hNorm
      exact False.elim
        (equalityRewrite_none_no_bodySat
          P I S deltaAt? hRewriteNone hBody)
    · have hImpossibleFalse :
          r.normalizedImpossible = false :=
        Bool.eq_false_of_not_eq_true hImpossible
      have hRewriteSome :
          ∃ rw : EqRewrite D,
            equalityRewrite r.source.body = some rw := by
        have hNorm :
            normalizedImpossibleFor r.source.body = false := by
          rw [← r.normalizedImpossible_eq]
          exact hImpossibleFalse
        unfold normalizedImpossibleFor at hNorm
        cases hRewrite : equalityRewrite r.source.body with
        | none => simp [hRewrite] at hNorm
        | some rw => exact ⟨rw, rfl⟩
      rcases hRewriteSome with ⟨rw, hRewrite⟩
      have hNormEntries :
          r.normalizedRelBodyAtoms =
            rewriteRelEntries rw
              (relBodyAtomEntries r.source.body) := by
        rw [r.normalizedRelBodyAtoms_eq]
        simp [normalizedRelBodyAtomsFor, hRewrite]
      have hNormHead :
          r.normalizedHead =
            rewriteRelAtom rw r.source.head := by
        rw [r.normalizedHead_eq]
        simp [normalizedHeadFor, hRewrite]
      let planned :=
        plannedRelBodyAtoms P I C S deltaAt?
          r.normalizedRelBodyAtoms
      have hPermPlanned :
          List.Perm planned r.normalizedRelBodyAtoms := by
        exact plannedRelBodyAtoms_perm P I C S deltaAt?
          r.normalizedRelBodyAtoms
      have hRelRewrite :
          RelEntriesSatWithDelta P I S deltaAt?
            (rewriteRelEntries rw
              (relBodyAtomEntries r.source.body)) σ :=
        source_bodySat_to_normalized_relEntries
          P I S deltaAt? hRewrite hBody
      have hRelNormalized :
          RelEntriesSatWithDelta P I S deltaAt?
            r.normalizedRelBodyAtoms σ := by
        simpa [hNormEntries] using hRelRewrite
      have hRelPlanned :
          RelEntriesSatWithDelta P I S deltaAt?
            planned σ :=
        (P.relEntriesSatWithDelta_iff_of_perm
          I S deltaAt? hPermPlanned σ).mpr
          hRelNormalized
      rcases
        P.joinCompiledRelAtomsFromIndexedList_complete_entries
          I C S deltaAt? planned [[]] σ [] (by simp)
          (PartialAssign.ConsistentWith.nil σ)
          hRelPlanned with
        ⟨ρ, hJoin, _hCons, _hExt, hAgreePlanned⟩
      have hNormHeadVars :
          PartialAssign.AgreesOn ρ σ
            r.normalizedHead.varList := by
        intro x hx
        have hxPlanned :
            x ∈ relEntryVarList (D := D) planned := by
          have hxNormEntries :
              x ∈ relEntryVarList (D := D)
                r.normalizedRelBodyAtoms := by
            have hxRewriteHead :
                x ∈ (rewriteRelAtom rw r.source.head).varList := by
              simpa [hNormHead] using hx
            simpa [hNormEntries] using
              normalizedHead_varList_subset_relEntryVarList
                r.source hRewrite hxRewriteHead
          exact
            (mem_relEntryVarList_iff_of_perm
              hPermPlanned x).mpr hxNormEntries
        exact hAgreePlanned x hxPlanned
      have hHeadEval :
          r.normalizedHead.evalTuple
              (PartialAssign.toAssign ρ) =
            r.normalizedHead.evalTuple σ := by
        apply r.normalizedHead.evalTuple_eq_of_assign_eq_on_vars
        intro x hx
        exact PartialAssign.AgreesOn.toAssign_eq
          hNormHeadVars hx
      have hNormHeadEval :
          cast
              (congrArg
                (fun X : Γ.syms =>
                  Tuple D (Γ.arity X))
                r.normalizedHead_rel_eq)
              (r.normalizedHead.evalTuple σ) =
            r.source.head.evalTuple σ := by
        have hCastNorm :
            cast
                (congrArg
                  (fun X : Γ.syms =>
                    Tuple D (Γ.arity X))
                  r.normalizedHead_rel_eq)
                (r.normalizedHead.evalTuple σ) =
              (rewriteRelAtom rw r.source.head).evalTuple σ :=
          cast_evalTuple_eq_of_atom_eq
            hNormHead r.normalizedHead_rel_eq σ
        exact hCastNorm.trans
          (rewriteRelAtom_evalTuple_of_respects
            (by
              unfold equalityRewrite at hRewrite
              exact
                equalityRewriteFrom_respects_of_bodySat
                  P I S deltaAt? 0 r.source.body
                  hRewrite (RewriteRespects.nil σ) hBody)
            r.source.head)
      rw [List.mem_toFinset]
      unfold compiledHeadTupleListOfAssignments
      rw [List.mem_map]
      refine
        ⟨r.normalizedHead.evalTuple
            (PartialAssign.toAssign ρ), ?_, ?_⟩
      · rw [List.mem_map]
        refine ⟨ρ, ?_, ?_⟩
        · have hMem :
              ρ ∈ P.joinPlannedRelAtomsFromIndexedList
                I C S deltaAt? r.normalizedRelBodyAtoms [[]] := by
            unfold joinPlannedRelAtomsFromIndexedList
            exact hJoin
          simpa [compiledBodyAssignmentIndexedList,
            hImpossibleFalse] using hMem
        · exact (headTupleOfAtomPartial_eq_evalTuple_toAssign
            r.normalizedHead ρ).symm
      · rw [hHeadEval, hNormHeadEval, hHead]

theorem slotHeadTupleListOfPlannedAssignments_toFinset
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (r : CompiledRule P) :
    (compiledHeadTupleListOfSlotAssignments r
      (P.compiledBodySlotAssignmentIndexedList I C S
        deltaAt? r)).toFinset =
      P.ruleConsequenceWithDeltaAt I S deltaAt? r.source := by
  rw [compiledHeadTupleListOfSlotAssignments_eq_of_coherent
    r
    (P.compiledBodySlotAssignmentIndexedList I C S
      deltaAt? r)
    (compiledBodySlotAssignmentIndexedList_coherent
      P I C S deltaAt? r)
    r.slotHead_wf]
  rw [compiledBodySlotAssignmentIndexedList_bindings]
  exact
    P.headTupleListOfPlannedAssignments_toFinset
      I C S deltaAt? r

omit [LinearOrder D] in
theorem headTupleListOfAssignments_toFinset_congr
    (r : Rule D Γ)
    {assignments₁ assignments₂ : List (PartialAssign D)}
    (hAssignments : assignments₁.toFinset =
      assignments₂.toFinset) :
    (headTupleListOfAssignments r assignments₁).toFinset =
      (headTupleListOfAssignments r assignments₂).toFinset := by
  unfold headTupleListOfAssignments
  exact
    map_toFinset_eq_of_toFinset_eq
      (headTupleOfPartial r) hAssignments

theorem joinRelAtomsFromList_toFinset
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat) :
    ∀ (idx : Nat) (body : List (Atom D Γ))
      (assignments : List (PartialAssign D)),
      (P.joinRelAtomsFromList I S deltaAt? idx
          body assignments).toFinset =
        P.joinRelAtomsFrom I S deltaAt? idx
          body assignments.toFinset
| _idx, [], assignments => by
    simp [joinRelAtomsFromList, joinRelAtomsFrom]
| idx, .rel a :: body, assignments => by
    simp [joinRelAtomsFromList, joinRelAtomsFrom,
      joinRelAtomsFromList_toFinset P I S deltaAt?
        (idx + 1) body,
      extendAssignmentsWithAtomList_toFinset]
| idx, .eq lhs rhs :: body, assignments => by
    simp [joinRelAtomsFromList, joinRelAtomsFrom,
      joinRelAtomsFromList_toFinset P I S deltaAt?
        (idx + 1) body]

theorem bodyAssignmentList_toFinset
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (body : List (Atom D Γ)) :
    (P.bodyAssignmentList I S deltaAt? body).toFinset =
      P.bodyAssignments I S deltaAt? body := by
  apply Finset.ext
  intro ρ
  simp [bodyAssignmentList, bodyAssignments,
    Finset.mem_filter,
    joinRelAtomsFromList_toFinset]

theorem ruleConsequenceListWithDeltaAt_toFinset
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (r : Rule D Γ) :
    (P.ruleConsequenceListWithDeltaAt I S deltaAt? r).toFinset =
      P.ruleConsequenceWithDeltaAt I S deltaAt? r := by
  apply Finset.ext
  intro t
  unfold ruleConsequenceListWithDeltaAt
    ruleConsequenceWithDeltaAt
    headTupleListOfAssignments headTuplesOfAssignments
  rw [← bodyAssignmentList_toFinset P I S deltaAt? r.body]
  simp [List.mem_toFinset,
    List.mem_map, Finset.mem_image,
    headTupleOfPartial_eq_evalTuple_toAssign]

theorem initialRuleConsequenceList_toFinset
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (r : Rule D Γ) :
    (P.initialRuleConsequenceList I r).toFinset =
      P.initialRuleConsequence I r := by
  unfold initialRuleConsequenceList initialRuleConsequence
  by_cases hUses : bodyUsesIDB P r.body
  · simp [hUses]
  · simp [hUses, ruleConsequenceListWithDeltaAt_toFinset]

theorem semiNaiveRuleConsequenceList_toFinset
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (r : Rule D Γ) :
    (P.semiNaiveRuleConsequenceList I S r).toFinset =
      P.semiNaiveRuleConsequence I S r := by
  unfold semiNaiveRuleConsequenceList semiNaiveRuleConsequence
  let step :=
    fun (acc : FinRelation D (Γ.arity r.head.rel)) idx =>
      acc ∪ P.ruleConsequenceWithDeltaAt I S (some idx) r
  have h :
      ∀ (idxs : List Nat)
        (acc : FinRelation D (Γ.arity r.head.rel)),
        acc ∪
            (idxs.flatMap
              (fun idx =>
                P.ruleConsequenceListWithDeltaAt I S
                  (some idx) r)).toFinset =
          idxs.foldl step acc := by
    intro idxs
    induction idxs with
    | nil =>
        intro acc
        simp [step]
    | cons idx idxs ih =>
        intro acc
        rw [List.flatMap_cons, List.toFinset_append,
          ruleConsequenceListWithDeltaAt_toFinset,
          List.foldl_cons]
        rw [← ih (acc ∪
          P.ruleConsequenceWithDeltaAt I S (some idx) r)]
        ac_rfl
  simpa using
    h (idbRelAtomIndices P r.body) ∅

omit [LinearOrder D] in
theorem ruleConsequenceListsForHead_toFinset
    (P : Program D Γ)
    (X : Γ.syms)
    (ruleEvalList : (r : Rule D Γ) →
      List (Tuple D (Γ.arity r.head.rel)))
    (ruleEvalSet : (r : Rule D Γ) →
      FinRelation D (Γ.arity r.head.rel))
    (hEval :
      ∀ r : Rule D Γ,
        (ruleEvalList r).toFinset = ruleEvalSet r) :
    ∀ rules : List (Rule D Γ),
      (P.ruleConsequenceListsForHead X ruleEvalList
          rules).toFinset =
        P.ruleConsequencesForHead X ruleEvalSet rules
| [] => by
    simp [ruleConsequenceListsForHead,
      ruleConsequencesForHead]
| r :: rs => by
    unfold ruleConsequenceListsForHead
      ruleConsequencesForHead
    by_cases hHead : r.head.rel = X
    · subst hHead
      simp [List.toFinset_append,
        ruleConsequenceListsForHead_toFinset P r.head.rel
          ruleEvalList ruleEvalSet hEval rs,
        hEval r]
    · simp [hHead,
        ruleConsequenceListsForHead_toFinset P X
          ruleEvalList ruleEvalSet hEval rs]

theorem compiledInitialRuleConsequenceList_toFinset
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (r : CompiledRule P) :
    (P.compiledInitialRuleConsequenceList I r).toFinset =
      P.initialRuleConsequence I r.source := by
  have hList :
      P.compiledInitialRuleConsequenceList I r =
        P.initialRuleConsequenceList I r.source := by
    unfold compiledInitialRuleConsequenceList
      initialRuleConsequenceList
    by_cases hUses : bodyUsesIDB P r.source.body
    · simp [hUses]
    · simp [hUses, ruleConsequenceListWithDeltaAt,
        compiledBodyAssignmentList_eq_bodyAssignmentList]
  rw [hList]
  exact P.initialRuleConsequenceList_toFinset I r.source

theorem compiledSemiNaiveRuleConsequenceList_toFinset
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (r : CompiledRule P) :
    (P.compiledSemiNaiveRuleConsequenceList I S r).toFinset =
      P.semiNaiveRuleConsequence I S r.source := by
  have hList :
      P.compiledSemiNaiveRuleConsequenceList I S r =
        P.semiNaiveRuleConsequenceList I S r.source := by
    unfold compiledSemiNaiveRuleConsequenceList
      semiNaiveRuleConsequenceList
    simp [r.idbBodyPositions_eq,
      ruleConsequenceListWithDeltaAt, bodyAssignmentList,
      compiledBodyAssignmentList_eq_bodyAssignmentList]
  rw [hList]
  exact P.semiNaiveRuleConsequenceList_toFinset I S r.source

theorem compiledInitialRuleConsequenceIndexedList_toFinset
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (r : CompiledRule P) :
    (P.compiledInitialRuleConsequenceIndexedListCore I C r).toFinset =
      P.initialRuleConsequence I r.source := by
  unfold compiledInitialRuleConsequenceIndexedListCore
  by_cases hUses : bodyUsesIDB P r.source.body
  · simp [hUses, initialRuleConsequence]
  · rw [if_neg hUses]
    let emptyState : SemiNaiveState P :=
      { current := MaterializedIDB.empty P
        delta := MaterializedIDB.empty P }
    have hHead :=
      P.slotHeadTupleListOfPlannedAssignments_toFinset
        I C emptyState none r
    rw [P.compiledProjectedRuleConsequenceIndexedList_toFinset]
    simpa [compiledInitialRuleConsequenceIndexedList,
      initialRuleConsequence, hUses, emptyState] using hHead

theorem compiledSemiNaiveRuleConsequenceIndexedList_toFinset
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (C : IndexedInput P I)
    (S : SemiNaiveState P)
    (r : CompiledRule P) :
    (P.compiledSemiNaiveRuleConsequenceIndexedListCore I C S r).toFinset =
      P.semiNaiveRuleConsequence I S r.source := by
  unfold compiledSemiNaiveRuleConsequenceIndexedListCore
  let stepListIndexed :=
    fun idx =>
      P.compiledProjectedRuleConsequenceIndexedListCore
        I C S (some idx) r
  let stepList :=
    fun idx =>
      headTupleListOfAssignments r.source
        (P.compiledBodyAssignmentList
          I S (some idx) r)
  have h :
      ∀ idx : Nat,
        (stepListIndexed idx).toFinset =
          (stepList idx).toFinset := by
    intro idx
    unfold stepListIndexed stepList
    rw [P.compiledProjectedRuleConsequenceIndexedList_toFinset]
    rw [P.slotHeadTupleListOfPlannedAssignments_toFinset
      I C S (some idx) r]
    have hStepList :
        headTupleListOfAssignments r.source
            (P.compiledBodyAssignmentList I S
              (some idx) r) =
          P.ruleConsequenceListWithDeltaAt I S
            (some idx) r.source := by
      unfold ruleConsequenceListWithDeltaAt
      rw [P.compiledBodyAssignmentList_eq_bodyAssignmentList]
    rw [hStepList]
    exact (P.ruleConsequenceListWithDeltaAt_toFinset
      I S (some idx) r.source).symm
  have hFlat :
      (r.idbBodyPositions.flatMap stepListIndexed).toFinset =
        (r.idbBodyPositions.flatMap stepList).toFinset := by
    induction r.idbBodyPositions with
    | nil =>
        simp
    | cons idx idxs ih =>
        rw [List.flatMap_cons, List.flatMap_cons,
          List.toFinset_append, List.toFinset_append,
          h idx, ih]
  rw [hFlat]
  exact P.compiledSemiNaiveRuleConsequenceList_toFinset I S r

private def compiledRuleConsequenceListsForHeadRec
    (P : Program D Γ)
    (X : Γ.syms)
    (ruleEvalList : (r : CompiledRule P) →
      List (Tuple D (Γ.arity r.source.head.rel))) :
    List (CompiledRule P) → List (Tuple D (Γ.arity X))
| [] => []
| r :: rs =>
    let rest :=
      compiledRuleConsequenceListsForHeadRec P X
        ruleEvalList rs
    if hHead : r.source.head.rel = X then
      cast
        (congrArg
          (fun Y : Γ.syms => List (Tuple D (Γ.arity Y)))
          hHead)
        (ruleEvalList r) ++ rest
    else
      rest

omit [LinearOrder D] in
theorem compiledRuleConsequenceListsForHeadRec_toFinset
    (P : Program D Γ)
    (X : Γ.syms)
    (ruleEvalList : (r : CompiledRule P) →
      List (Tuple D (Γ.arity r.source.head.rel)))
    (ruleEvalSet : (r : Rule D Γ) →
      FinRelation D (Γ.arity r.head.rel))
    (hEval : ∀ r : CompiledRule P,
      (ruleEvalList r).toFinset =
        ruleEvalSet r.source) :
    ∀ rules : List (CompiledRule P),
      (compiledRuleConsequenceListsForHeadRec P X
          ruleEvalList rules).toFinset =
        P.ruleConsequencesForHead X ruleEvalSet
          (rules.map (fun r => r.source))
| [] => by
    simp [compiledRuleConsequenceListsForHeadRec,
      ruleConsequencesForHead]
| r :: rs => by
    unfold compiledRuleConsequenceListsForHeadRec
      ruleConsequencesForHead
    by_cases hHead : r.source.head.rel = X
    · subst hHead
      simp [List.toFinset_append, hEval r,
        compiledRuleConsequenceListsForHeadRec_toFinset
          P r.source.head.rel ruleEvalList ruleEvalSet
          hEval rs]
    · simp [hHead,
        compiledRuleConsequenceListsForHeadRec_toFinset
          P X ruleEvalList ruleEvalSet hEval rs]

set_option linter.flexible false in
set_option linter.unusedSimpArgs false in
omit [LinearOrder D] in
theorem compiledRuleConsequenceListsForHead_foldl_toRec
    (P : Program D Γ)
    (X : Γ.syms)
    (ruleEvalList : (r : CompiledRule P) →
      List (Tuple D (Γ.arity r.source.head.rel))) :
    ∀ (rules : List (CompiledRule P))
      (acc : List (Tuple D (Γ.arity X))),
      (rules.foldl
          (compiledRuleConsequenceListsForHeadStep
            P X ruleEvalList) acc).toFinset =
        acc.toFinset ∪
          (compiledRuleConsequenceListsForHeadRec
            P X ruleEvalList rules).toFinset
| [] => by
    intro acc
    simp [compiledRuleConsequenceListsForHeadRec]
| r :: rs => by
    intro acc
    rw [List.foldl_cons]
    rw [compiledRuleConsequenceListsForHead_foldl_toRec
      P X ruleEvalList rs
      (compiledRuleConsequenceListsForHeadStep
        P X ruleEvalList acc r)]
    unfold compiledRuleConsequenceListsForHeadStep
      compiledRuleConsequenceListsForHeadRec
    by_cases hHead : r.source.head.rel = X
    · subst hHead
      apply Finset.ext
      intro t
      cases rs with
      | nil =>
          simp [compiledRuleConsequenceListsForHeadRec,
            List.mem_toFinset, List.mem_append,
            or_assoc, or_left_comm, or_comm]
      | cons r' rs =>
          by_cases h' :
              r'.source.head.rel = r.source.head.rel
          · simp [compiledRuleConsequenceListsForHeadRec,
              h', List.mem_toFinset, List.mem_append,
              or_assoc, or_left_comm, or_comm]
          · simp [compiledRuleConsequenceListsForHeadRec,
              h', List.mem_toFinset, List.mem_append,
              or_assoc, or_left_comm, or_comm]
    · simp [hHead]
      apply Finset.ext
      intro t
      cases rs with
      | nil =>
          simp [compiledRuleConsequenceListsForHeadRec,
            List.mem_toFinset]
      | cons r' rs =>
          by_cases h' : r'.source.head.rel = X
          · simp [compiledRuleConsequenceListsForHeadRec,
              h', List.mem_toFinset, List.mem_append]
          · simp [compiledRuleConsequenceListsForHeadRec,
              h', List.mem_toFinset]

omit [LinearOrder D] in
theorem compiledRuleConsequenceListsForHead_toFinset
    (P : Program D Γ)
    (X : Γ.syms)
    (ruleEvalList : (r : CompiledRule P) →
      List (Tuple D (Γ.arity r.source.head.rel)))
    (ruleEvalSet : (r : Rule D Γ) →
      FinRelation D (Γ.arity r.head.rel))
    (hEval : ∀ r : CompiledRule P,
      (ruleEvalList r).toFinset =
        ruleEvalSet r.source)
    (rules : List (CompiledRule P)) :
    (P.compiledRuleConsequenceListsForHead X
        ruleEvalList rules).toFinset =
      P.ruleConsequencesForHead X ruleEvalSet
        (rules.map (fun r => r.source)) := by
  unfold compiledRuleConsequenceListsForHead
  rw [compiledRuleConsequenceListsForHead_foldl_toRec
    P X ruleEvalList rules []]
  simp [compiledRuleConsequenceListsForHeadRec_toFinset
    P X ruleEvalList ruleEvalSet hEval rules]

omit [LinearOrder D] in
theorem ruleConsequencesForHead_filter_head_eq
    (P : Program D Γ)
    (X : Γ.syms)
    (ruleEval : (r : Rule D Γ) →
      FinRelation D (Γ.arity r.head.rel)) :
    ∀ rules : List (Rule D Γ),
      P.ruleConsequencesForHead X ruleEval
          (rules.filter (fun r => decide (r.head.rel = X))) =
        P.ruleConsequencesForHead X ruleEval rules
| [] => by
    simp [ruleConsequencesForHead]
| r :: rs => by
    by_cases hHead : r.head.rel = X
    · simp [ruleConsequencesForHead, hHead,
        ruleConsequencesForHead_filter_head_eq P X
          ruleEval rs]
    · simp [ruleConsequencesForHead, hHead,
        ruleConsequencesForHead_filter_head_eq P X
          ruleEval rs]

theorem CompiledProgram.initialConsequenceListForHeadWithInput_toFinset
    {P : Program D Γ}
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema)
    (input : MaterializedInput P I)
    (X : Γ.syms) :
    (compiled.initialConsequenceListForHeadWithInput
      I input X).toFinset =
      P.initialConsequencesForHead I X := by
  unfold CompiledProgram.initialConsequenceListForHeadWithInput
    initialConsequencesForHead
  unfold CompiledProgram.initialConsequenceListForHeadWithInputCore
  rw [P.compiledRuleConsequenceListsForHead_toFinset X
    (fun r =>
      P.compiledInitialRuleConsequenceIndexedListCore I input r)
    (fun r => P.initialRuleConsequence I r)
    (fun r =>
      P.compiledInitialRuleConsequenceIndexedList_toFinset
        I input r)
    (compiled.rulesForHead X)]
  rw [compiled.rulesForHead_sources X]
  exact
    P.ruleConsequencesForHead_filter_head_eq X
      (fun r => P.initialRuleConsequence I r) P.rules

theorem CompiledProgram.initialConsequenceListForHead_toFinset
    {P : Program D Γ}
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema)
    (X : Γ.syms) :
    (compiled.initialConsequenceListForHead I X).toFinset =
      P.initialConsequencesForHead I X := by
  unfold CompiledProgram.initialConsequenceListForHead
  exact
    compiled.initialConsequenceListForHeadWithInput_toFinset
      I (P.materializeInput I) X

theorem CompiledProgram.semiNaiveConsequenceListForHeadWithInput_toFinset
    {P : Program D Γ}
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema)
    (input : MaterializedInput P I)
    (S : SemiNaiveState P)
    (X : Γ.syms) :
    (compiled.semiNaiveConsequenceListForHeadWithInput
      I input S X).toFinset =
      P.semiNaiveConsequencesForHead I S X := by
  unfold CompiledProgram.semiNaiveConsequenceListForHeadWithInput
    semiNaiveConsequencesForHead
  unfold CompiledProgram.semiNaiveConsequenceListForHeadWithInputCore
  rw [P.compiledRuleConsequenceListsForHead_toFinset X
    (fun r =>
      P.compiledSemiNaiveRuleConsequenceIndexedListCore I
        input S r)
    (fun r => P.semiNaiveRuleConsequence I S r)
    (fun r =>
      P.compiledSemiNaiveRuleConsequenceIndexedList_toFinset
        I input S r)
    (compiled.rulesForHead X)]
  rw [compiled.rulesForHead_sources X]
  exact
    P.ruleConsequencesForHead_filter_head_eq X
      (fun r => P.semiNaiveRuleConsequence I S r) P.rules

theorem CompiledProgram.semiNaiveConsequenceListForHead_toFinset
    {P : Program D Γ}
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (X : Γ.syms) :
    (compiled.semiNaiveConsequenceListForHead I S X).toFinset =
      P.semiNaiveConsequencesForHead I S X := by
  unfold CompiledProgram.semiNaiveConsequenceListForHead
  exact
    compiled.semiNaiveConsequenceListForHeadWithInput_toFinset
      I (P.materializeInput I) S X

theorem initialCompiledConsequenceListForHead_toFinset
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (X : Γ.syms) :
    (P.initialCompiledConsequenceListForHead I X).toFinset =
      P.initialConsequencesForHead I X := by
  unfold initialCompiledConsequenceListForHead
  exact (P.compile).initialConsequenceListForHead_toFinset I X

theorem semiNaiveCompiledConsequenceListForHead_toFinset
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (X : Γ.syms) :
    (P.semiNaiveCompiledConsequenceListForHead I S X).toFinset =
      P.semiNaiveConsequencesForHead I S X := by
  unfold semiNaiveCompiledConsequenceListForHead
  exact (P.compile).semiNaiveConsequenceListForHead_toFinset I S X

theorem initialConsequenceListForHead_toFinset
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (X : Γ.syms) :
    (P.initialConsequenceListForHead I X).toFinset =
      P.initialConsequencesForHead I X := by
  unfold initialConsequenceListForHead
    initialConsequencesForHead
  exact
    P.ruleConsequenceListsForHead_toFinset X
      (fun r => P.initialRuleConsequenceList I r)
      (fun r => P.initialRuleConsequence I r)
      (fun r => P.initialRuleConsequenceList_toFinset I r)
      P.rules

theorem semiNaiveConsequenceListForHead_toFinset
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (X : Γ.syms) :
    (P.semiNaiveConsequenceListForHead I S X).toFinset =
      P.semiNaiveConsequencesForHead I S X := by
  unfold semiNaiveConsequenceListForHead
    semiNaiveConsequencesForHead
  exact
    P.ruleConsequenceListsForHead_toFinset X
      (fun r => P.semiNaiveRuleConsequenceList I S r)
      (fun r => P.semiNaiveRuleConsequence I S r)
      (fun r => P.semiNaiveRuleConsequenceList_toFinset I S r)
      P.rules

omit [LinearOrder D] in
theorem Atom.relVarList_subset_varList
    (b : Atom D Γ)
    {x : Var}
    (hx : x ∈ b.relVarList) :
    x ∈ b.varList := by
  cases b with
  | rel a =>
      simpa [Atom.relVarList, Atom.varList] using hx
  | eq lhs rhs =>
      simp [Atom.relVarList] at hx

omit [LinearOrder D] in
theorem Body.relVarList_subset_varList
    (body : List (Atom D Γ))
    {x : Var}
    (hx : x ∈ Body.relVarList body) :
    x ∈ Body.varList body := by
  unfold Body.relVarList Body.varList Atom.listRelVarList
    Atom.listVarList at *
  rw [List.mem_flatten] at hx ⊢
  rcases hx with ⟨xs, hxs, hx⟩
  rcases List.mem_map.mp hxs with ⟨b, hb, rfl⟩
  exact
    ⟨b.varList, List.mem_map.mpr ⟨b, hb, rfl⟩,
      Atom.relVarList_subset_varList b hx⟩

/-
  One semi-naive rule consequence is sound for the indexed
  semi-naive body semantics.
-/
theorem ruleConsequenceWithDeltaAt_sound
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (r : Rule D Γ)
    {t : Tuple D (Γ.arity r.head.rel)}
    (ht :
      t ∈ P.ruleConsequenceWithDeltaAt I S
        deltaAt? r) :
    ∃ σ : Assign D,
      BodySatWithDelta P I S deltaAt? 0 r.body σ ∧
        r.head.evalTuple σ = t := by
  unfold ruleConsequenceWithDeltaAt at ht
  unfold headTuplesOfAssignments at ht
  rcases Finset.mem_image.mp ht with ⟨ρ, hρ, hEq⟩
  exact
    ⟨PartialAssign.toAssign ρ,
      P.bodyAssignments_sound I S deltaAt? r.body hρ,
      hEq⟩

/-
  Satisfying indexed semi-naive body assignments appear in
  the corresponding rule consequence.
-/
theorem ruleConsequenceWithDeltaAt_complete
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (deltaAt? : Option Nat)
    (r : Rule D Γ)
    (σ : Assign D)
    (hBody :
      BodySatWithDelta P I S deltaAt? 0 r.body σ) :
    r.head.evalTuple σ ∈
      P.ruleConsequenceWithDeltaAt I S deltaAt? r := by
  have hBound :
      ∀ x : Var,
        x ∈ Body.varList r.body →
          x ∈ Body.relVarList r.body := by
    intro x hx
    have hxBodyVars : x ∈ Body.vars r.body := by
      change x ∈ Atom.vars r.body
      unfold Atom.vars
      exact List.mem_toFinset.mpr hx
    have hSafe :=
      r.safe x (Finset.mem_union.mpr (Or.inr hxBodyVars))
    change x ∈ Atom.relVars r.body at hSafe
    unfold Atom.relVars at hSafe
    exact List.mem_toFinset.mp hSafe
  rcases
    P.bodyAssignments_complete I S deltaAt? r.body σ
      hBound hBody with
    ⟨ρ, hρ, hAgreeBody⟩
  have hHeadEval :
      r.head.evalTuple (PartialAssign.toAssign ρ) =
        r.head.evalTuple σ := by
    apply r.head.evalTuple_eq_of_assign_eq_on_vars
    intro x hxHead
    have hxHeadVars : x ∈ r.head.vars := by
      exact r.head.mem_vars_of_mem_varList hxHead
    have hxRel : x ∈ Body.relVarList r.body := by
      have hSafe :=
        r.safe x (Finset.mem_union.mpr (Or.inl hxHeadVars))
      change x ∈ Atom.relVars r.body at hSafe
      unfold Atom.relVars at hSafe
      exact List.mem_toFinset.mp hSafe
    exact hAgreeBody x
      (Body.relVarList_subset_varList r.body hxRel)
  unfold ruleConsequenceWithDeltaAt headTuplesOfAssignments
  refine Finset.mem_image.mpr ?_
  exact ⟨ρ, hρ, hHeadEval⟩

/-
  Rule consequences accumulated for a fixed head symbol are
  sound for the supplied rule evaluator.
-/
omit [LinearOrder D] in
theorem ruleConsequencesForHead_sound
    (P : Program D Γ)
    (X : Γ.syms)
    (ruleEval : (r : Rule D Γ) →
      FinRelation D (Γ.arity r.head.rel))
    (ruleSound :
      ∀ (r : Rule D Γ)
        {t : Tuple D (Γ.arity r.head.rel)},
        t ∈ ruleEval r →
          ∃ σ : Assign D, r.head.evalTuple σ = t)
    (rs : List (Rule D Γ))
    {t : Tuple D (Γ.arity X)}
    (ht : t ∈ P.ruleConsequencesForHead X ruleEval rs) :
    ∃ r : Rule D Γ,
      r ∈ rs ∧
        ∃ hHead : r.head.rel = X,
          ∃ σ : Assign D,
            r.headEvalTupleAs X hHead σ = t := by
  induction rs with
  | nil =>
      simp [ruleConsequencesForHead] at ht
  | cons r rs ih =>
      by_cases hHead : r.head.rel = X
      · subst X
        have ht' :
            t ∈ ruleEval r ∪
              P.ruleConsequencesForHead r.head.rel
                ruleEval rs := by
          simpa [ruleConsequencesForHead] using ht
        rcases Finset.mem_union.mp ht' with htRule | htRest
        · rcases ruleSound r htRule with ⟨σ, hTuple⟩
          exact
            ⟨r, by simp, rfl, σ,
              by
                simpa [Rule.headEvalTupleAs] using hTuple⟩
        · rcases ih htRest with
            ⟨r', hr', hHead', σ, hTuple⟩
          exact
            ⟨r', by simp [hr'], hHead', σ, hTuple⟩
      · have htRest :
            t ∈ P.ruleConsequencesForHead X
              ruleEval rs := by
          simpa [ruleConsequencesForHead, hHead] using ht
        rcases ih htRest with
          ⟨r', hr', hHead', σ, hTuple⟩
        exact
          ⟨r', by simp [hr'], hHead', σ, hTuple⟩

/-
  Rule consequences accumulated for a fixed head symbol are
  complete for a listed rule with matching head.
-/
omit [LinearOrder D] in
theorem ruleConsequencesForHead_complete
    (P : Program D Γ)
    (X : Γ.syms)
    (ruleEval : (r : Rule D Γ) →
      FinRelation D (Γ.arity r.head.rel))
    (rs : List (Rule D Γ))
    (r : Rule D Γ)
    (hr : r ∈ rs)
    (hHead : r.head.rel = X)
    {t : Tuple D (Γ.arity r.head.rel)}
    (ht : t ∈ ruleEval r) :
    Tuple.castArity (by rw [hHead]) t ∈
      P.ruleConsequencesForHead X ruleEval rs := by
  induction rs with
  | nil =>
      cases hr
  | cons r' rs ih =>
      by_cases hHead' : r'.head.rel = X
      · rcases List.mem_cons.mp hr with hrEq | hrRest
        · subst hrEq
          subst X
          have hMem :
              t ∈ ruleEval r ∪
                P.ruleConsequencesForHead r.head.rel
                  ruleEval rs :=
            Finset.mem_union.mpr (Or.inl ht)
          simpa [ruleConsequencesForHead] using hMem
        · have hRest :=
            ih hrRest
          have hMem :
              Tuple.castArity (by rw [hHead]) t ∈
                cast
                  (congrArg
                    (fun Y : Γ.syms =>
                      FinRelation D (Γ.arity Y))
                    hHead')
                  (ruleEval r') ∪
                  P.ruleConsequencesForHead X ruleEval rs :=
            Finset.mem_union.mpr (Or.inr hRest)
          simpa [ruleConsequencesForHead, hHead'] using hMem
      · rcases List.mem_cons.mp hr with hrEq | hrRest
        · subst hrEq
          exact False.elim (hHead' hHead)
        · have hRest :=
            ih hrRest
          simpa [ruleConsequencesForHead,
            hHead'] using hRest

/-
  Semi-naive rule consequences are sound: membership gives
  a rule, a selected IDB body-atom position, and an indexed
  body witness.
-/
theorem semiNaiveRuleConsequence_sound
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (r : Rule D Γ)
    {t : Tuple D (Γ.arity r.head.rel)}
    (ht : t ∈ P.semiNaiveRuleConsequence I S r) :
    ∃ idx : Nat,
      idx ∈ P.idbRelAtomIndices r.body ∧
        ∃ σ : Assign D,
          BodySatWithDelta P I S (some idx) 0 r.body σ ∧
            r.head.evalTuple σ = t := by
  unfold semiNaiveRuleConsequence at ht
  let step :=
    fun
        (acc : FinRelation D (Γ.arity r.head.rel))
        (idx : Nat) =>
      acc ∪ P.ruleConsequenceWithDeltaAt I S (some idx) r
  have hFold :
      ∀ (idxs : List Nat)
        (acc : FinRelation D (Γ.arity r.head.rel))
        {t : Tuple D (Γ.arity r.head.rel)},
        t ∈ idxs.foldl step acc →
          t ∈ acc ∨
            ∃ idx : Nat,
              idx ∈ idxs ∧
                t ∈ P.ruleConsequenceWithDeltaAt I S
                  (some idx) r := by
    intro idxs
    induction idxs with
    | nil =>
        intro acc t ht
        exact Or.inl ht
    | cons idx idxs ih =>
        intro acc t ht
        have ht' :
            t ∈ (acc ∪
                  P.ruleConsequenceWithDeltaAt I S
                    (some idx) r) ∨
              ∃ idx' : Nat,
                idx' ∈ idxs ∧
                  t ∈ P.ruleConsequenceWithDeltaAt I S
                    (some idx') r :=
          ih (acc ∪
            P.ruleConsequenceWithDeltaAt I S
              (some idx) r) ht
        rcases ht' with htHead | htTail
        · have htUnion := Finset.mem_union.mp htHead
          rcases htUnion with htAcc | htRule
          · exact Or.inl htAcc
          · exact
              Or.inr
                ⟨idx, by simp, htRule⟩
        · rcases htTail with ⟨idx', hIdx', htRule⟩
          exact
            Or.inr
              ⟨idx', by simp [hIdx'], htRule⟩
  rcases hFold (P.idbRelAtomIndices r.body) ∅ ht with
    hEmpty | hRule
  · simp at hEmpty
  · rcases hRule with ⟨idx, hIdx, htRule⟩
    rcases
      P.ruleConsequenceWithDeltaAt_sound I S
        (some idx) r htRule with
      ⟨σ, hBody, hTuple⟩
    exact ⟨idx, hIdx, σ, hBody, hTuple⟩

/-
  Semi-naive consequences for a head symbol are sound:
  membership gives the source program rule, matching head,
  selected IDB body-atom position, and indexed body witness.
-/
theorem semiNaiveConsequencesForHead_sound
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (X : Γ.syms)
    {t : Tuple D (Γ.arity X)}
    (ht : t ∈ P.semiNaiveConsequencesForHead I S X) :
    ∃ r : Rule D Γ,
      r ∈ P.rules ∧
        ∃ hHead : r.head.rel = X,
          ∃ idx : Nat,
            idx ∈ P.idbRelAtomIndices r.body ∧
              ∃ σ : Assign D,
                BodySatWithDelta P I S
                  (some idx) 0 r.body σ ∧
                  r.headEvalTupleAs X hHead σ = t := by
  unfold semiNaiveConsequencesForHead at ht
  have hRules :
      ∀ (rs : List (Rule D Γ))
        {t : Tuple D (Γ.arity X)},
        t ∈ P.ruleConsequencesForHead X
            (fun r =>
              P.semiNaiveRuleConsequence I S r) rs →
          ∃ r : Rule D Γ,
            r ∈ rs ∧
              ∃ hHead : r.head.rel = X,
                ∃ idx : Nat,
                  idx ∈ P.idbRelAtomIndices r.body ∧
                    ∃ σ : Assign D,
                      BodySatWithDelta P I S
                        (some idx) 0 r.body σ ∧
                        r.headEvalTupleAs X hHead σ =
                          t := by
    intro rs
    induction rs with
    | nil =>
        intro t ht
        simp [ruleConsequencesForHead] at ht
    | cons r rs ih =>
        intro t ht
        by_cases hHead : r.head.rel = X
        · subst X
          have ht' :
              t ∈ P.semiNaiveRuleConsequence I S r ∪
                P.ruleConsequencesForHead r.head.rel
                  (fun r =>
                    P.semiNaiveRuleConsequence I S r)
                  rs := by
            simpa [ruleConsequencesForHead] using ht
          have htUnion := Finset.mem_union.mp ht'
          rcases htUnion with htRule | htRest
          · rcases
              P.semiNaiveRuleConsequence_sound I S r
                htRule with
              ⟨idx, hIdx, σ, hBody, hTuple⟩
            exact
              ⟨r, by simp, rfl, idx, hIdx, σ, hBody,
                by
                  simpa [Rule.headEvalTupleAs]
                    using hTuple⟩
          · rcases ih htRest with
              ⟨r', hr', hHead', idx, hIdx, σ, hBody,
                hTuple⟩
            exact
              ⟨r', by simp [hr'], hHead', idx, hIdx, σ,
                hBody, hTuple⟩
        · have htRest :
              t ∈ P.ruleConsequencesForHead X
                (fun r =>
                  P.semiNaiveRuleConsequence I S r)
                rs := by
            simpa [ruleConsequencesForHead, hHead] using ht
          rcases ih htRest with
            ⟨r', hr', hHead', idx, hIdx, σ, hBody,
              hTuple⟩
          exact
            ⟨r', by simp [hr'], hHead', idx, hIdx, σ,
              hBody, hTuple⟩
  exact hRules P.rules ht

/-
  Semi-naive rule consequences are complete for a selected
  IDB body-atom position.
-/
theorem semiNaiveRuleConsequence_complete
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (r : Rule D Γ)
    (idx : Nat)
    (hIdx : idx ∈ P.idbRelAtomIndices r.body)
    (σ : Assign D)
    (hBody :
      BodySatWithDelta P I S (some idx) 0 r.body σ) :
    r.head.evalTuple σ ∈
      P.semiNaiveRuleConsequence I S r := by
  unfold semiNaiveRuleConsequence
  let step :=
    fun
        (acc : FinRelation D (Γ.arity r.head.rel))
        (idx : Nat) =>
      acc ∪ P.ruleConsequenceWithDeltaAt I S (some idx) r
  have hAcc :
      ∀ (idxs : List Nat)
        (acc : FinRelation D (Γ.arity r.head.rel))
        {t : Tuple D (Γ.arity r.head.rel)},
        t ∈ acc → t ∈ idxs.foldl step acc := by
    intro idxs
    induction idxs with
    | nil =>
        intro acc t ht
        exact ht
    | cons idx' idxs ih =>
        intro acc t ht
        exact
          ih (acc ∪
            P.ruleConsequenceWithDeltaAt I S
              (some idx') r)
            (Finset.mem_union.mpr (Or.inl ht))
  have hInsert :
      ∀ (idxs : List Nat)
        (acc : FinRelation D (Γ.arity r.head.rel)),
        idx ∈ idxs →
          r.head.evalTuple σ ∈
            P.ruleConsequenceWithDeltaAt I S
              (some idx) r →
          r.head.evalTuple σ ∈ idxs.foldl step acc := by
    intro idxs
    induction idxs with
    | nil =>
        intro acc hMem _ht
        cases hMem
    | cons idx' idxs ih =>
        intro acc hMem ht
        rcases List.mem_cons.mp hMem with hEq | hTail
        · subst hEq
          exact
            hAcc idxs
              (acc ∪
                P.ruleConsequenceWithDeltaAt I S
                  (some idx) r)
              (Finset.mem_union.mpr (Or.inr ht))
        · exact
            ih
              (acc ∪
                P.ruleConsequenceWithDeltaAt I S
                  (some idx') r)
              hTail ht
  have hRule :
      r.head.evalTuple σ ∈
        P.ruleConsequenceWithDeltaAt I S (some idx) r :=
    P.ruleConsequenceWithDeltaAt_complete I S
      (some idx) r σ hBody
  exact hInsert (P.idbRelAtomIndices r.body) ∅ hIdx hRule

/-
  In a represented step, converting the current materialized
  IDB relations to an instance yields `curr`.
-/
theorem current_lookup_eq_curr
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (prev curr : Instance D Γ)
    (hS : S.RepresentsStep I prev curr)
    (X : Γ.syms)
    (hX : X ∈ P.idb) :
    S.current.lookup X hX = curr X := by
  have hInst := congrFun hS.toInstance_eq X
  simpa [SemiNaiveState.toInstance,
    MaterializedIDB.toInstance, hX] using hInst

/-
  In a represented step, delta relations are exactly the
  fresh IDB facts.
-/
theorem delta_lookup_eq_curr_sdiff_prev
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (prev curr : Instance D Γ)
    (hS : S.RepresentsStep I prev curr)
    (X : Γ.syms)
    (hX : X ∈ P.idb) :
    S.delta.lookup X hX = curr X \ prev X :=
  hS.delta_eq X hX

/-
  Non-IDB relations are unchanged across a represented
  input-domain immediate step.
-/
theorem non_idb_curr_eq_prev
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (prev curr : Instance D Γ)
    (hS : S.RepresentsStep I prev curr)
    (X : Γ.syms)
    (hX : X ∉ P.idb) :
    curr X = prev X := by
  rw [hS.curr_eq_immediate]
  exact P.immediateOnInputAdom_preserves_edb I prev X hX

/-
  Tuples selected by `atomRelationFor` are always tuples of
  the represented current instance.
-/
theorem atomRelationFor_subset_curr
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (prev curr : Instance D Γ)
    (hS : S.RepresentsStep I prev curr)
    (deltaAt? : Option Nat)
    (idx : Nat)
    (a : RelAtom D Γ) :
    P.atomRelationFor I S deltaAt? idx a ⊆
      curr a.rel := by
  intro t ht
  unfold atomRelationFor at ht
  by_cases hDelta : deltaAt? = some idx
  · rw [if_pos hDelta] at ht
    by_cases hIDB : a.rel ∈ P.idb
    · rw [dif_pos hIDB] at ht
      rw [P.delta_lookup_eq_curr_sdiff_prev
        I S prev curr hS a.rel hIDB] at ht
      exact Finset.sdiff_subset ht
    · simp [dif_neg hIDB] at ht
  · rw [if_neg hDelta] at ht
    by_cases hIDB : a.rel ∈ P.idb
    · rw [dif_pos hIDB] at ht
      rw [P.current_lookup_eq_curr
        I S prev curr hS a.rel hIDB] at ht
      exact ht
    · rw [dif_neg hIDB] at ht
      have hInst := congrFun hS.toInstance_eq a.rel
      have hEq :
          MaterializedIDB.initialInstance P I a.rel =
            curr a.rel := by
        simpa [SemiNaiveState.toInstance,
          MaterializedIDB.toInstance, hIDB] using hInst
      rw [hEq] at ht
      exact ht

/-
  Indexed semi-naive body satisfaction implies ordinary body
  satisfaction in the represented current instance.
-/
theorem BodySatWithDelta_bodySat_curr_from_idx
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (prev curr : Instance D Γ)
    (hS : S.RepresentsStep I prev curr)
    (deltaAt? : Option Nat)
    (σ : Assign D) :
    ∀ (idx : Nat) (body : List (Atom D Γ)),
      BodySatWithDelta P I S deltaAt? idx body σ →
        Body.Satisfied body curr σ
| _idx, [], _hBody => trivial
| idx, b :: body, hBody => by
    cases b with
    | rel a =>
        change
          a.evalTuple σ ∈
              P.atomRelationFor I S deltaAt? idx a ∧
            BodySatWithDelta P I S deltaAt? (idx + 1)
              body σ at hBody
        exact
          ⟨P.atomRelationFor_subset_curr
              I S prev curr hS deltaAt? idx a hBody.1,
            BodySatWithDelta_bodySat_curr_from_idx
              P I S prev curr hS deltaAt? σ
              (idx + 1) body hBody.2⟩
    | eq lhs rhs =>
        change
          lhs.eval σ = rhs.eval σ ∧
            BodySatWithDelta P I S deltaAt? (idx + 1)
              body σ at hBody
        exact
          ⟨hBody.1,
            BodySatWithDelta_bodySat_curr_from_idx
              P I S prev curr hS deltaAt? σ
              (idx + 1) body hBody.2⟩

theorem BodySatWithDelta_bodySat_curr
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (prev curr : Instance D Γ)
    (hS : S.RepresentsStep I prev curr)
    (deltaAt? : Option Nat)
    (body : List (Atom D Γ))
    (σ : Assign D)
    (hBody :
      BodySatWithDelta P I S deltaAt? 0 body σ) :
    Body.Satisfied body curr σ := by
  exact
    P.BodySatWithDelta_bodySat_curr_from_idx
      I S prev curr hS deltaAt? σ 0 body hBody

theorem atomRelationFor_current_mem_of_curr
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (prev curr : Instance D Γ)
    (hS : S.RepresentsStep I prev curr)
    (deltaAt? : Option Nat)
    (idx : Nat)
    (a : RelAtom D Γ)
    (σ : Assign D)
    (hNe : deltaAt? ≠ some idx)
    (hMem : a.evalTuple σ ∈ curr a.rel) :
    a.evalTuple σ ∈
      P.atomRelationFor I S deltaAt? idx a := by
  unfold atomRelationFor
  rw [if_neg hNe]
  by_cases hIDB : a.rel ∈ P.idb
  · rw [dif_pos hIDB]
    rw [P.current_lookup_eq_curr
      I S prev curr hS a.rel hIDB]
    exact hMem
  · rw [dif_neg hIDB]
    have hInst := congrFun hS.toInstance_eq a.rel
    have hEq :
        MaterializedIDB.initialInstance P I a.rel =
          curr a.rel := by
      simpa [SemiNaiveState.toInstance,
        MaterializedIDB.toInstance, hIDB] using hInst
    simpa [hEq] using hMem

theorem bodySatWithDelta_of_selected_lt
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (prev curr : Instance D Γ)
    (hS : S.RepresentsStep I prev curr)
    (selected idx : Nat)
    (σ : Assign D)
    (hLt : selected < idx) :
    ∀ (body : List (Atom D Γ)),
      Body.Satisfied body curr σ →
        BodySatWithDelta P I S (some selected) idx body σ
| [], _hBody => trivial
| b :: body, hBody => by
    cases b with
    | rel a =>
        have hNe :
            (some selected : Option Nat) ≠ some idx := by
          intro h
          injection h with hEq
          omega
        exact
          ⟨P.atomRelationFor_current_mem_of_curr
              I S prev curr hS (some selected) idx a σ
              hNe hBody.1,
            P.bodySatWithDelta_of_selected_lt
              I S prev curr hS selected (idx + 1) σ
              (by omega) body hBody.2⟩
    | eq lhs rhs =>
        exact
          ⟨hBody.1,
            P.bodySatWithDelta_of_selected_lt
              I S prev curr hS selected (idx + 1) σ
              (by omega) body hBody.2⟩

omit [LinearOrder D] in
theorem idbRelAtomIndicesFrom_ge
    (P : Program D Γ) :
    ∀ (start : Nat) (body : List (Atom D Γ)) {idx : Nat},
      idx ∈ P.idbRelAtomIndicesFrom start body →
        start ≤ idx
| _start, [], idx, hIdx => by
    simp [idbRelAtomIndicesFrom] at hIdx
| start, b :: body, idx, hIdx => by
    cases b with
    | rel a =>
        by_cases hIDB : a.rel ∈ P.idb
        · have hIdx' :
              idx = start ∨
                idx ∈
                  P.idbRelAtomIndicesFrom
                    (start + 1) body := by
            simpa [idbRelAtomIndicesFrom, hIDB] using hIdx
          rcases hIdx' with hEq | hTail
          · omega
          · have hGe :=
              idbRelAtomIndicesFrom_ge P
                (start + 1) body hTail
            omega
        · have hTail :
              idx ∈
                P.idbRelAtomIndicesFrom
                  (start + 1) body := by
            simpa [idbRelAtomIndicesFrom, hIDB] using hIdx
          have hGe :=
            idbRelAtomIndicesFrom_ge P
              (start + 1) body hTail
          omega
    | eq lhs rhs =>
        have hTail :
            idx ∈
              P.idbRelAtomIndicesFrom
                (start + 1) body := by
          simpa [idbRelAtomIndicesFrom] using hIdx
        have hGe :=
          idbRelAtomIndicesFrom_ge P
            (start + 1) body hTail
        omega

theorem exists_delta_atom_from_idx
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (prev curr : Instance D Γ)
    (hS : S.RepresentsStep I prev curr)
    (σ : Assign D) :
    ∀ (idx : Nat) (body : List (Atom D Γ)),
      Body.Satisfied body curr σ →
        ¬ Body.Satisfied body prev σ →
          ∃ selected : Nat,
            selected ∈ P.idbRelAtomIndicesFrom idx
              body ∧
              BodySatWithDelta P I S (some selected)
                idx body σ
| _idx, [], _hCurr, hNotPrev => by
    exact False.elim (hNotPrev trivial)
| idx, b :: body, hCurr, hNotPrev => by
    cases b with
    | rel a =>
        by_cases hPrevAtom : a.evalTuple σ ∈ prev a.rel
        · have hNotPrevTail : ¬ Body.Satisfied body prev σ := by
            intro hPrevTail
            exact hNotPrev ⟨hPrevAtom, hPrevTail⟩
          rcases
            exists_delta_atom_from_idx
              P I S prev curr hS σ (idx + 1) body
              hCurr.2 hNotPrevTail with
            ⟨selected, hSelected, hDeltaTail⟩
          have hNe :
              (some selected : Option Nat) ≠
                some idx := by
            intro h
            injection h with hEq
            have hGe :=
              P.idbRelAtomIndicesFrom_ge
                (idx + 1) body hSelected
            omega
          have hHead :
              a.evalTuple σ ∈
                P.atomRelationFor I S (some selected)
                  idx a :=
            P.atomRelationFor_current_mem_of_curr
              I S prev curr hS (some selected) idx a σ
              hNe hCurr.1
          have hSelectedFull :
              selected ∈
                P.idbRelAtomIndicesFrom idx
                  (Atom.rel a :: body) := by
            by_cases hIDB : a.rel ∈ P.idb
            · simp [idbRelAtomIndicesFrom,
                hIDB, hSelected]
            · simpa [idbRelAtomIndicesFrom, hIDB] using
                hSelected
          exact
            ⟨selected, hSelectedFull, hHead, hDeltaTail⟩
        · by_cases hIDB : a.rel ∈ P.idb
          · have hDeltaMem :
                a.evalTuple σ ∈
                  S.delta.lookup a.rel hIDB := by
              rw [P.delta_lookup_eq_curr_sdiff_prev
                I S prev curr hS a.rel hIDB]
              exact Finset.mem_sdiff.mpr
                ⟨hCurr.1, hPrevAtom⟩
            have hHead :
                a.evalTuple σ ∈
                  P.atomRelationFor I S (some idx)
                    idx a := by
              unfold atomRelationFor
              rw [if_pos rfl, dif_pos hIDB]
              exact hDeltaMem
            have hTail :
                BodySatWithDelta P I S (some idx)
                  (idx + 1) body σ :=
              P.bodySatWithDelta_of_selected_lt
                I S prev curr hS idx (idx + 1) σ
                (by omega) body hCurr.2
            exact
              ⟨idx,
                by simp [idbRelAtomIndicesFrom, hIDB],
                hHead, hTail⟩
          · have hEq :=
              P.non_idb_curr_eq_prev
                I S prev curr hS a.rel hIDB
            have hPrev :
                a.evalTuple σ ∈ prev a.rel := by
              rw [← hEq]
              exact hCurr.1
            exact False.elim (hPrevAtom hPrev)
    | eq lhs rhs =>
        have hNotPrevTail : ¬ Body.Satisfied body prev σ := by
          intro hPrevTail
          exact hNotPrev ⟨hCurr.1, hPrevTail⟩
        rcases
          exists_delta_atom_from_idx
            P I S prev curr hS σ (idx + 1) body
            hCurr.2 hNotPrevTail with
          ⟨selected, hSelected, hDeltaTail⟩
        have hSelectedFull :
            selected ∈ P.idbRelAtomIndicesFrom idx
              (Atom.eq lhs rhs :: body) := by
          simpa [idbRelAtomIndicesFrom] using hSelected
        exact
          ⟨selected, hSelectedFull, hCurr.1, hDeltaTail⟩

/-
  If a positive body is true in `curr` but not in `prev`,
  some IDB relational atom in the body uses a fresh delta
  tuple.
-/
theorem exists_idb_delta_atom_of_bodySat_curr_not_prev
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (prev curr : Instance D Γ)
    (hS : S.RepresentsStep I prev curr)
    (body : List (Atom D Γ))
    (σ : Assign D)
    (hCurr : Body.Satisfied body curr σ)
    (hNotPrev : ¬ Body.Satisfied body prev σ) :
    ∃ idx : Nat,
      idx ∈ P.idbRelAtomIndices body ∧
        BodySatWithDelta P I S (some idx) 0 body σ := by
  simpa [idbRelAtomIndices] using
    P.exists_delta_atom_from_idx
      I S prev curr hS σ 0 body hCurr hNotPrev

/-
  Fresh semi-naive consequences are contained in fresh naive
  consequences over the represented current instance.
-/
theorem snConsequences_sdiff_subset_naive_sdiff
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (prev curr : Instance D Γ)
    (X : Γ.syms)
    (hS : S.RepresentsStep I prev curr) :
    P.semiNaiveConsequencesForHead I S X \ curr X ⊆
      P.IDBConsequenceOnInputAdom I curr X \ curr X := by
  intro t ht
  rw [Finset.mem_sdiff] at ht ⊢
  rcases ht with ⟨hSN, hFresh⟩
  rcases P.semiNaiveConsequencesForHead_sound I S X hSN with
    ⟨r, hr, hHead, idx, _hIdx, σ, hBodyDelta, hTuple⟩
  have hBodyCurr :
      Body.Satisfied r.body curr σ :=
    P.BodySatWithDelta_bodySat_curr
      I S prev curr hS (some idx) r.body σ hBodyDelta
  let r' : {r : Rule D Γ // r ∈ P.rules} := ⟨r, hr⟩
  have hVals :
      ∀ x : Var,
        x ∈ r'.1.varList → σ x ∈ P.adom I := by
    intro x hx
    exact
      P.value_mem_of_rule_var_of_bounded
        hS.curr_bounded r' σ hBodyCurr hx
  have hConsequence :
      r'.1.headEvalTupleAs X hHead σ ∈
        P.IDBConsequenceOnForRules (P.adom I) curr X
          P.rules.attach := by
    exact
      P.mem_IDBConsequenceOnForRules_of_bodySat
        (P.adom I) curr X P.rules.attach r'
        (by simp [r'])
        hHead σ hVals hBodyCurr
  constructor
  · rw [← hTuple]
    simpa [IDBConsequenceOnInputAdom, IDBConsequenceOn]
      using hConsequence
  · exact hFresh

/-
  Fresh naive consequences over the represented current
  instance are contained in fresh semi-naive consequences.
-/
theorem naive_sdiff_subset_snConsequences_sdiff
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (prev curr : Instance D Γ)
    (X : Γ.syms)
    (hS : S.RepresentsStep I prev curr) :
    P.IDBConsequenceOnInputAdom I curr X \ curr X ⊆
      P.semiNaiveConsequencesForHead I S X \ curr X := by
  intro t ht
  rw [Finset.mem_sdiff] at ht ⊢
  rcases ht with ⟨hNaive, hFresh⟩
  have hRaw :
      t ∈ P.IDBConsequenceOnForRules (P.adom I)
        curr X P.rules.attach := by
    simpa [IDBConsequenceOnInputAdom, IDBConsequenceOn]
      using hNaive
  rcases
    P.IDBConsequenceOnForRules_sound
      (P.adom I) curr X t P.rules.attach hRaw with
    ⟨r, hrAttach, hHead, σ, hBodyCurr, hTuple⟩
  have hNotPrevBody : ¬ Body.Satisfied r.1.body prev σ := by
    intro hBodyPrev
    have hX : X ∈ P.idb := by
      simpa [hHead] using P.head_mem_idb r.2
    have hValsPrev :
        ∀ x : Var,
          x ∈ r.1.varList → σ x ∈ P.adom I := by
      intro x hx
      exact
        P.value_mem_of_rule_var_of_bounded
          hS.prev_bounded r σ hBodyPrev hx
    have hPrevCons :
        r.1.headEvalTupleAs X hHead σ ∈
          P.IDBConsequenceOnForRules (P.adom I)
            prev X P.rules.attach :=
      P.mem_IDBConsequenceOnForRules_of_bodySat
        (P.adom I) prev X P.rules.attach r
        hrAttach
        hHead σ hValsPrev hBodyPrev
    have hInImmediate :
        r.1.headEvalTupleAs X hHead σ ∈
          P.immediateOnInputAdom I prev X := by
      unfold immediateOnInputAdom immediateOn
      rw [if_pos hX]
      apply Finset.mem_union.mpr
      right
      simpa [IDBConsequenceOnInputAdom, IDBConsequenceOn]
        using hPrevCons
    have hInCurr :
        r.1.headEvalTupleAs X hHead σ ∈ curr X := by
      rw [hS.curr_eq_immediate]
      exact hInImmediate
    exact hFresh (by simpa [hTuple] using hInCurr)
  rcases
    P.exists_idb_delta_atom_of_bodySat_curr_not_prev
      I S prev curr hS r.1.body σ
      hBodyCurr hNotPrevBody with
    ⟨idx, hIdx, hBodyDelta⟩
  have hRule :
      r.1.head.evalTuple σ ∈
        P.semiNaiveRuleConsequence I S r.1 :=
    P.semiNaiveRuleConsequence_complete
      I S r.1 idx hIdx σ hBodyDelta
  have hSN :
      r.1.headEvalTupleAs X hHead σ ∈
        P.semiNaiveConsequencesForHead I S X := by
    unfold semiNaiveConsequencesForHead
    simpa [Rule.headEvalTupleAs] using
      P.ruleConsequencesForHead_complete X
        (fun r => P.semiNaiveRuleConsequence I S r)
        P.rules r.1 r.2 hHead hRule
  constructor
  · rw [← hTuple]
    exact hSN
  · exact hFresh

end Program

end Datalog

------------------------------------------------------------
-- Initial And Step Representation
------------------------------------------------------------

namespace Datalog

namespace Program

variable {A D : Type}
variable [RelationNames A] [Domain D] [LinearOrder D] [Hashable D]
variable {Γ : UnnamedSchema A}

/-
  The empty initial instance interprets every IDB relation
  as empty.
-/
omit [LinearOrder D] in
theorem initial_eq_empty_of_idb
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (X : Γ.syms)
    (hX : X ∈ P.idb) :
    P.initial I X = ∅ := by
  have hNotEdb : X.1 ∉ P.edbSchema.syms := by
    intro hEdb
    have hEdbName : X.1 ∈ P.edbNames := by
      simpa [Program.edbSchema] using hEdb
    have hIdbName : X.1 ∈ P.idbNames :=
      Finset.mem_image.mpr ⟨X, hX, rfl⟩
    exact
      (Finset.disjoint_left.mp P.disjoint_edb_idb)
        hEdbName hIdbName
  simpa [initial] using
    Instance.expandEmpty_eq_empty_of_not_mem
      P.ambient_extension_edbSchema I X hNotEdb

/-
  Empty materialized IDB relations used while computing
  initial facts.
-/
def initialEmptyState
    (P : Program D Γ) :
    SemiNaiveState P :=
  { current := MaterializedIDB.empty P
    delta := MaterializedIDB.empty P }

set_option linter.flexible false in
theorem atomRelationFor_empty_none_eq_initial
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (idx : Nat)
    (a : RelAtom D Γ) :
    P.atomRelationFor I (P.initialEmptyState) none idx a =
      P.initial I a.rel := by
  unfold atomRelationFor initialEmptyState
  by_cases hIDB : a.rel ∈ P.idb
  · simp [hIDB]
    unfold MaterializedIDB.empty
    rw [MaterializedIDB.lookup_ofIdbFn]
    exact (P.initial_eq_empty_of_idb I a.rel hIDB).symm
  · simp [hIDB]
    rfl

theorem bodySatWithDelta_empty_none_iff_initial
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (σ : Assign D) :
    ∀ (idx : Nat) (body : List (Atom D Γ)),
      BodySatWithDelta P I (P.initialEmptyState)
          none idx body σ ↔
        Body.Satisfied body (P.initial I) σ
| _idx, [] => by
    simp [BodySatWithDelta, Body.Satisfied]
| idx, b :: body => by
    cases b with
    | rel a =>
        change
          (a.evalTuple σ ∈
              P.atomRelationFor I (P.initialEmptyState)
                none idx a ∧
            BodySatWithDelta P I (P.initialEmptyState) none
              (idx + 1) body σ) ↔
            (a.evalTuple σ ∈ P.initial I a.rel ∧
              Body.Satisfied body (P.initial I) σ)
        rw [bodySatWithDelta_empty_none_iff_initial
          P I σ (idx + 1) body]
        rw [P.atomRelationFor_empty_none_eq_initial I idx a]
    | eq lhs rhs =>
        change
          (lhs.eval σ = rhs.eval σ ∧
            BodySatWithDelta P I (P.initialEmptyState) none
              (idx + 1) body σ) ↔
            (lhs.eval σ = rhs.eval σ ∧
              Body.Satisfied body (P.initial I) σ)
        rw [bodySatWithDelta_empty_none_iff_initial
          P I σ (idx + 1) body]

omit [LinearOrder D] in
theorem bodyUsesIDB_exists_idb_atom
    (P : Program D Γ) :
    ∀ (body : List (Atom D Γ)),
      bodyUsesIDB P body = true →
        ∃ a : RelAtom D Γ,
          Atom.rel a ∈ body ∧ a.rel ∈ P.idb
| [], hUses => by
    simp [bodyUsesIDB] at hUses
| b :: body, hUses => by
    cases b with
    | rel a =>
        by_cases hIDB : a.rel ∈ P.idb
        · exact ⟨a, by simp, hIDB⟩
        · have hTail : bodyUsesIDB P body = true := by
            simpa [bodyUsesIDB, atomUsesIDB,
              hIDB] using hUses
          rcases
            bodyUsesIDB_exists_idb_atom P body hTail with
            ⟨a', ha', hIDB'⟩
          exact ⟨a', by simp [ha'], hIDB'⟩
    | eq lhs rhs =>
        have hTail : bodyUsesIDB P body = true := by
          simpa [bodyUsesIDB, atomUsesIDB] using hUses
        rcases bodyUsesIDB_exists_idb_atom P body hTail with
          ⟨a, ha, hIDB⟩
        exact ⟨a, by simp [ha], hIDB⟩

omit [LinearOrder D] in
theorem not_bodySat_initial_of_bodyUsesIDB
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (body : List (Atom D Γ))
    (σ : Assign D)
    (hUses : bodyUsesIDB P body = true) :
    ¬ Body.Satisfied body (P.initial I) σ := by
  intro hBody
  rcases P.bodyUsesIDB_exists_idb_atom body hUses with
    ⟨a, ha, hIDB⟩
  have hSat :=
    Body.sat_of_satisfied (P.initial I) σ body ha hBody
  change a.Sat (P.initial I) σ at hSat
  unfold RelAtom.Sat RelAtom.evalFact RelFact.Mem at hSat
  rw [P.initial_eq_empty_of_idb I a.rel hIDB] at hSat
  change
    a.evalTuple σ ∈
      (∅ : Finset (Tuple D (Γ.arity a.rel))) at hSat
  cases hSat

theorem initialRuleConsequence_sound
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (r : Rule D Γ)
    {t : Tuple D (Γ.arity r.head.rel)}
    (ht : t ∈ P.initialRuleConsequence I r) :
    ∃ σ : Assign D,
      Body.Satisfied r.body (P.initial I) σ ∧
        r.head.evalTuple σ = t := by
  unfold initialRuleConsequence at ht
  by_cases hUses : bodyUsesIDB P r.body
  · simp [hUses] at ht
  · rcases
      P.ruleConsequenceWithDeltaAt_sound I
        (P.initialEmptyState) none r
        (by simpa [hUses, initialEmptyState] using ht) with
      ⟨σ, hBody, hTuple⟩
    exact
      ⟨σ,
        (P.bodySatWithDelta_empty_none_iff_initial
          I σ 0 r.body).mp hBody,
        hTuple⟩

theorem initialRuleConsequence_complete
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (r : Rule D Γ)
    (σ : Assign D)
    (hBody : Body.Satisfied r.body (P.initial I) σ) :
    r.head.evalTuple σ ∈
      P.initialRuleConsequence I r := by
  unfold initialRuleConsequence
  by_cases hUses : bodyUsesIDB P r.body
  · exact False.elim
      (P.not_bodySat_initial_of_bodyUsesIDB I r.body σ
        hUses hBody)
  · have hDelta :
        BodySatWithDelta P I (P.initialEmptyState) none 0
          r.body σ :=
      (P.bodySatWithDelta_empty_none_iff_initial
        I σ 0 r.body).mpr hBody
    have hMem :=
      P.ruleConsequenceWithDeltaAt_complete I
        (P.initialEmptyState) none r σ hDelta
    simpa [hUses, initialEmptyState] using hMem

theorem initialConsequencesForHead_sound
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (X : Γ.syms)
    {t : Tuple D (Γ.arity X)}
    (ht : t ∈ P.initialConsequencesForHead I X) :
    ∃ r : Rule D Γ,
      r ∈ P.rules ∧
        ∃ hHead : r.head.rel = X,
          ∃ σ : Assign D,
            Body.Satisfied r.body (P.initial I) σ ∧
              r.headEvalTupleAs X hHead σ = t := by
  unfold initialConsequencesForHead at ht
  have hRules :
      ∀ (rs : List (Rule D Γ))
        {t : Tuple D (Γ.arity X)},
        t ∈ P.ruleConsequencesForHead X
            (fun r => P.initialRuleConsequence I r) rs →
          ∃ r : Rule D Γ,
            r ∈ rs ∧
              ∃ hHead : r.head.rel = X,
                ∃ σ : Assign D,
                  Body.Satisfied r.body (P.initial I) σ ∧
                    r.headEvalTupleAs X hHead σ = t := by
    intro rs
    induction rs with
    | nil =>
        intro t ht
        simp [ruleConsequencesForHead] at ht
    | cons r rs ih =>
        intro t ht
        by_cases hHead : r.head.rel = X
        · subst X
          have ht' :
              t ∈ P.initialRuleConsequence I r ∪
                P.ruleConsequencesForHead r.head.rel
                  (fun r =>
                    P.initialRuleConsequence I r) rs := by
            simpa [ruleConsequencesForHead] using ht
          have htUnion := Finset.mem_union.mp ht'
          rcases htUnion with htRule | htRest
          · rcases
              P.initialRuleConsequence_sound I r htRule with
              ⟨σ, hBody, hTuple⟩
            exact
              ⟨r, by simp, rfl, σ, hBody,
                by
                  simpa [Rule.headEvalTupleAs]
                    using hTuple⟩
          · rcases ih htRest with
              ⟨r', hr', hHead', σ, hBody, hTuple⟩
            exact
              ⟨r', by simp [hr'], hHead', σ, hBody,
                hTuple⟩
        · have htRest :
              t ∈ P.ruleConsequencesForHead X
                (fun r =>
                  P.initialRuleConsequence I r) rs := by
            simpa [ruleConsequencesForHead, hHead] using ht
          rcases ih htRest with
            ⟨r', hr', hHead', σ, hBody, hTuple⟩
          exact
            ⟨r', by simp [hr'], hHead', σ, hBody,
              hTuple⟩
  exact hRules P.rules ht

/-
  Initial semi-naive rule consequences agree with naive
  consequences over the initial instance. This is the first
  tuple-join/consequence boundary proof to discharge.
-/
theorem initialConsequences_eq_naive_initial
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (X : Γ.syms) :
    P.initialConsequencesForHead I X =
      P.IDBConsequenceOnInputAdom I (P.initial I) X := by
  apply Finset.ext
  intro t
  constructor
  · intro ht
    rcases P.initialConsequencesForHead_sound I X ht with
      ⟨r, hr, hHead, σ, hBody, hTuple⟩
    let r' : {r : Rule D Γ // r ∈ P.rules} := ⟨r, hr⟩
    have hVals :
        ∀ x : Var,
          x ∈ r'.1.varList → σ x ∈ P.adom I := by
      intro x hx
      exact
        P.value_mem_of_rule_var_of_bounded
          (P.initial_boundedByValues I) r' σ hBody hx
    have hConsequence :
        r'.1.headEvalTupleAs X hHead σ ∈
          P.IDBConsequenceOnForRules (P.adom I)
            (P.initial I) X P.rules.attach :=
      P.mem_IDBConsequenceOnForRules_of_bodySat
        (P.adom I) (P.initial I) X P.rules.attach r'
        (by simp [r'])
        hHead σ hVals hBody
    rw [← hTuple]
    simpa [IDBConsequenceOnInputAdom, IDBConsequenceOn]
      using hConsequence
  · intro ht
    have hRaw :
        t ∈ P.IDBConsequenceOnForRules (P.adom I)
          (P.initial I) X P.rules.attach := by
      simpa [IDBConsequenceOnInputAdom, IDBConsequenceOn]
        using ht
    rcases
      P.IDBConsequenceOnForRules_sound
        (P.adom I) (P.initial I) X t
        P.rules.attach hRaw with
      ⟨r, _hrAttach, hHead, σ, hBody, hTuple⟩
    have hRule :
        r.1.head.evalTuple σ ∈
          P.initialRuleConsequence I r.1 :=
      P.initialRuleConsequence_complete I r.1 σ hBody
    have hInit :
        r.1.headEvalTupleAs X hHead σ ∈
          P.initialConsequencesForHead I X := by
      unfold initialConsequencesForHead
      simpa [Rule.headEvalTupleAs] using
        P.ruleConsequencesForHead_complete X
          (fun r => P.initialRuleConsequence I r)
          P.rules r.1 r.2 hHead hRule
    rw [← hTuple]
    exact hInit

/-
  The core semi-naive delta theorem: for a represented
  `prev -> curr`, semi-naive production contributes
  exactly the fresh naive consequences over `curr`.
-/
theorem snConsequences_sdiff_eq_naive_sdiff
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (prev curr : Instance D Γ)
    (X : Γ.syms)
    (hS : S.RepresentsStep I prev curr) :
    P.semiNaiveConsequencesForHead I S X \ curr X =
      P.IDBConsequenceOnInputAdom I curr X \ curr X := by
  apply Finset.Subset.antisymm
  · exact
      P.snConsequences_sdiff_subset_naive_sdiff
        I S prev curr X hS
  · exact
      P.naive_sdiff_subset_snConsequences_sdiff
        I S prev curr X hS

/-
  The initial semi-naive state represents the first naive
  immediate-consequence step from the empty-IDB initial
  instance.
-/
theorem snInitialStateWithInput_represents_initial_step
    (P : Program D Γ)
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema)
    (input : MaterializedInput P I) :
    (P.snInitialStateWithInput compiled I input).RepresentsStep
      I (P.initial I)
        (P.immediateOnInputAdom I (P.initial I)) := by
  refine
    ⟨?toInstance, rfl, ?delta, ?mono,
      ?prevBound, ?currBound⟩
  · apply Instance.ext
    intro X
    by_cases hX : X ∈ P.idb
    · unfold snInitialStateWithInput SemiNaiveState.toInstance
        MaterializedIDB.toInstance
      rw [dif_pos hX]
      rw [MaterializedIDB.lookup_ofTupleListIdbFn]
      calc
        (Tuple.sortDedup
            (compiled.initialConsequenceListForHeadWithInput
              I input X)).toFinset =
            (compiled.initialConsequenceListForHeadWithInput
              I input X).toFinset := by
          apply Finset.ext
          intro t
          simp [List.mem_toFinset, Tuple.mem_sortDedup_iff]
        _ = P.initialConsequencesForHead I X := by
          exact
            compiled.initialConsequenceListForHeadWithInput_toFinset
              I input X
        _ = P.IDBConsequenceOnInputAdom I
              (P.initial I) X := by
          exact P.initialConsequences_eq_naive_initial I X
        _ = P.immediateOnInputAdom I (P.initial I) X := by
          have hInit : P.initial I X = ∅ :=
            P.initial_eq_empty_of_idb I X hX
          simp [IDBConsequenceOnInputAdom,
            immediateOnInputAdom, immediateOn, hX, hInit]
    · simp [SemiNaiveState.toInstance,
        MaterializedIDB.toInstance, hX,
        MaterializedIDB.initialInstance, initial,
        immediateOnInputAdom, immediateOn]
  · intro X hX
    unfold snInitialStateWithInput
    rw [MaterializedIDB.lookup_ofTupleListIdbFn]
    calc
      (Tuple.sortDedup
          (compiled.initialConsequenceListForHeadWithInput
            I input X)).toFinset =
          (compiled.initialConsequenceListForHeadWithInput
            I input X).toFinset := by
        apply Finset.ext
        intro t
        simp [List.mem_toFinset, Tuple.mem_sortDedup_iff]
      _ = P.initialConsequencesForHead I X := by
        exact
          compiled.initialConsequenceListForHeadWithInput_toFinset
            I input X
      _ = P.IDBConsequenceOnInputAdom I
            (P.initial I) X := by
        exact P.initialConsequences_eq_naive_initial I X
      _ = P.immediateOnInputAdom I (P.initial I) X \
            P.initial I X := by
        have hInit : P.initial I X = ∅ :=
          P.initial_eq_empty_of_idb I X hX
        simp [IDBConsequenceOnInputAdom,
          immediateOnInputAdom, immediateOn, hInit, hX]
  · exact
      P.immediateOnInputAdom_inflationary I
        (P.initial I)
  · exact P.initial_boundedByValues I
  · exact
      P.immediateOnInputAdom_preserves_boundedByValues I
        (P.initial_boundedByValues I)

theorem semiNaiveInitialStateWith_represents_initial_step
    (P : Program D Γ)
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema) :
    (P.semiNaiveInitialStateWith compiled I).RepresentsStep
      I (P.initial I)
        (P.immediateOnInputAdom I (P.initial I)) := by
  simpa [semiNaiveInitialStateWith] using
    P.snInitialStateWithInput_represents_initial_step
      compiled I (P.materializeInput I)

theorem semiNaiveInitialState_represents_initial_step
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    (P.semiNaiveInitialState I).RepresentsStep
      I (P.initial I)
        (P.immediateOnInputAdom I (P.initial I)) := by
  simpa [semiNaiveInitialState] using
    P.semiNaiveInitialStateWith_represents_initial_step
      P.compile I

/-
  Candidate for a shared Finset helper section if this
  pattern repeats outside the semi-naive proof.
-/
theorem finset_union_sdiff_eq_union
    {α : Type} [DecidableEq α]
    (A B : Finset α) :
    A ∪ (B \ A) = A ∪ B := by
  ext x
  by_cases hx : x ∈ A <;> simp [hx]

theorem finset_union_sdiff_eq_sdiff
    {α : Type} [DecidableEq α]
    (A B : Finset α) :
    (A ∪ B) \ A = B \ A := by
  ext x
  by_cases hx : x ∈ A <;> simp [hx]

/-
  One semi-naive push represents one naive immediate step
  from the represented current instance.
-/
theorem snStepWithInput_represents_next_step
    (P : Program D Γ)
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema)
    (input : MaterializedInput P I)
    (S : SemiNaiveState P)
    (prev curr : Instance D Γ)
    (hS : S.RepresentsStep I prev curr) :
    (P.snStepWithInput compiled I input S).RepresentsStep
      I curr (P.immediateOnInputAdom I curr) := by
  refine
    ⟨?toInstance, rfl, ?delta, ?mono,
      ?prevBound, ?currBound⟩
  · apply Instance.ext
    intro X
    by_cases hX : X ∈ P.idb
    · unfold snStepWithInput SemiNaiveState.toInstance
        MaterializedIDB.toInstance
      rw [dif_pos hX]
      rw [lookup_currentIdbOfStepUpdates]
      rw [lookupCurrentUpdateTuples_stepRelationUpdatesWithInput]
      have hOldTuples :
          (S.current.lookupTuples X hX).toFinset = curr X := by
        calc
          (S.current.lookupTuples X hX).toFinset =
              S.current.lookup X hX := by
            exact
              (MaterializedIDB.lookup_eq_lookupTuples_toFinset
                S.current X hX).symm
          _ = curr X := by
            exact P.current_lookup_eq_curr I S prev curr hS X hX
      change
        (Tuple.listUnion (S.current.lookupTuples X hX)
            (freshTuples (S.current.lookupTuples X hX)
              (compiled.semiNaiveConsequenceListForHeadWithInput
                I input S X))).toFinset =
          P.immediateOnInputAdom I curr X
      let oldTuples := S.current.lookupTuples X hX
      let produced :=
        compiled.semiNaiveConsequenceListForHeadWithInput
          I input S X
      let fresh := freshTuples oldTuples produced
      have hOldMem :
          ∀ t : Tuple D (Γ.arity X),
            t ∈ oldTuples ↔ t ∈ curr X := by
        intro t
        have hEq :=
          congrArg
            (fun R : FinRelation D (Γ.arity X) => t ∈ R)
            hOldTuples
        simpa [List.mem_toFinset, oldTuples] using hEq
      have hUnion :
          (Tuple.listUnion oldTuples fresh).toFinset =
            curr X ∪ fresh.toFinset := by
        apply Finset.ext
        intro t
        simp [List.mem_toFinset, Tuple.mem_listUnion_iff,
          hOldMem t]
      have hFresh :
          fresh.toFinset = produced.toFinset \ curr X := by
        apply Finset.ext
        intro t
        simp [List.mem_toFinset, mem_freshTuples_iff,
          hOldMem t, oldTuples, produced, fresh]
      rw [hUnion, hFresh]
      rw [compiled.semiNaiveConsequenceListForHeadWithInput_toFinset]
      rw [P.snConsequences_sdiff_eq_naive_sdiff
        I S prev curr X hS]
      have hImm :
          P.immediateOnInputAdom I curr X =
            curr X ∪
              P.IDBConsequenceOnInputAdom I curr X := by
        simp [immediateOnInputAdom, immediateOn,
          IDBConsequenceOnInputAdom, hX]
      rw [hImm]
      exact
        finset_union_sdiff_eq_union
          (curr X) (P.IDBConsequenceOnInputAdom I curr X)
    · unfold snStepWithInput SemiNaiveState.toInstance
        MaterializedIDB.toInstance
      rw [dif_neg hX]
      have hInst := congrFun hS.toInstance_eq X
      have hInit :
          MaterializedIDB.initialInstance P I X =
            curr X := by
        simpa [SemiNaiveState.toInstance,
          MaterializedIDB.toInstance, hX] using hInst
      rw [hInit]
      exact
        (P.immediateOnInputAdom_preserves_edb
          I curr X hX).symm
  · intro X hX
    unfold snStepWithInput
    rw [lookup_deltaIdbOfStepUpdates]
    rw [lookupDeltaUpdateTuples_stepRelationUpdatesWithInput]
    have hOldTuples :
        (S.current.lookupTuples X hX).toFinset = curr X := by
      calc
        (S.current.lookupTuples X hX).toFinset =
            S.current.lookup X hX := by
          exact
            (MaterializedIDB.lookup_eq_lookupTuples_toFinset
              S.current X hX).symm
        _ = curr X := by
          exact P.current_lookup_eq_curr I S prev curr hS X hX
    change
      (freshTuples (S.current.lookupTuples X hX)
        (compiled.semiNaiveConsequenceListForHeadWithInput
          I input S X)).toFinset =
        P.immediateOnInputAdom I curr X \ curr X
    rw [freshTuples_toFinset_eq_sdiff]
    rw [hOldTuples]
    rw [compiled.semiNaiveConsequenceListForHeadWithInput_toFinset]
    rw [P.snConsequences_sdiff_eq_naive_sdiff
      I S prev curr X hS]
    have hImm :
        P.immediateOnInputAdom I curr X =
          curr X ∪
            P.IDBConsequenceOnInputAdom I curr X := by
      simp [immediateOnInputAdom, immediateOn,
        IDBConsequenceOnInputAdom, hX]
    rw [hImm]
    exact
      (finset_union_sdiff_eq_sdiff
        (curr X)
        (P.IDBConsequenceOnInputAdom I curr X)).symm
  · exact P.immediateOnInputAdom_inflationary I curr
  · exact hS.curr_bounded
  · exact
      P.immediateOnInputAdom_preserves_boundedByValues I
        hS.curr_bounded

theorem semiNaiveStepWith_represents_next_step
    (P : Program D Γ)
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (prev curr : Instance D Γ)
    (hS : S.RepresentsStep I prev curr) :
    (P.semiNaiveStepWith compiled I S).RepresentsStep
      I curr (P.immediateOnInputAdom I curr) := by
  simpa [semiNaiveStepWith] using
    P.snStepWithInput_represents_next_step
      compiled I (P.materializeInput I) S prev curr hS

theorem semiNaiveStep_represents_next_step
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (prev curr : Instance D Γ)
    (hS : S.RepresentsStep I prev curr) :
    (P.semiNaiveStep I S).RepresentsStep
      I curr (P.immediateOnInputAdom I curr) := by
  simpa [semiNaiveStep] using
    P.semiNaiveStepWith_represents_next_step
      P.compile I S prev curr hS

/-
  Convenient projection of the single-step representation:
  the materialized state after one semi-naive step converts
  to the naive immediate-consequence instance.
-/
theorem semiNaiveStepWith_toInstance_eq_immediateOnInputAdom
    (P : Program D Γ)
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (prev curr : Instance D Γ)
    (hS : S.RepresentsStep I prev curr) :
    (P.semiNaiveStepWith compiled I S).toInstance I =
      P.immediateOnInputAdom I curr := by
  exact
    (P.semiNaiveStepWith_represents_next_step
      compiled I S prev curr hS).toInstance_eq

theorem semiNaiveStep_toInstance_eq_immediateOnInputAdom
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (prev curr : Instance D Γ)
    (hS : S.RepresentsStep I prev curr) :
    (P.semiNaiveStep I S).toInstance I =
      P.immediateOnInputAdom I curr := by
  exact
    (P.semiNaiveStep_represents_next_step
      I S prev curr hS).toInstance_eq

end Program

end Datalog

------------------------------------------------------------
-- Fuel, Fixedness, And Initial Inclusion
------------------------------------------------------------

namespace Datalog

namespace Program

variable {A D : Type}
variable [RelationNames A] [Domain D] [LinearOrder D] [Hashable D]
variable {Γ : UnnamedSchema A}

set_option linter.flexible false in
omit [LinearOrder D] in
theorem idbSymList_mem_idbList
    (P : Program D Γ)
    (X : P.IDBSym)
    (hX : X ∈ P.idbSymList) :
    X.1 ∈ P.idbList := by
  simp [Program.idbSymList] at hX
  rcases hX with ⟨a, b, ha, hEq⟩
  cases hEq
  exact ha

set_option linter.flexible false in
omit [LinearOrder D] in
theorem idbSymList_mem_of_idb
    (P : Program D Γ)
    (X : Γ.syms)
    (hX : X ∈ P.idb) :
    (⟨X, hX⟩ : P.IDBSym) ∈ P.idbSymList := by
  simp [Program.idbSymList]
  exact (MaterializedIDB.idbList_mem_iff_idb P).mpr hX

theorem deltaEmpty_lookup_eq_empty
    (P : Program D Γ)
    (S : SemiNaiveState P)
    (hEmpty : S.deltaEmpty = true)
    (X : Γ.syms)
    (hX : X ∈ P.idb) :
    S.delta.lookup X hX = ∅ := by
  have hAll :
      ∀ Y ∈ P.idbSymList,
        (S.delta.lookupTuples Y.1 Y.2).isEmpty = true := by
    exact
      (List.all_eq_true.mp
        (by simpa [SemiNaiveState.deltaEmpty] using hEmpty))
  have hEmptyListBool :=
    hAll ⟨X, hX⟩ (P.idbSymList_mem_of_idb X hX)
  have hEmptyList :
      S.delta.lookupTuples X hX = [] :=
    List.isEmpty_iff.mp hEmptyListBool
  rw [MaterializedIDB.lookup_eq_lookupTuples_toFinset,
    hEmptyList]
  simp

theorem exists_new_of_deltaEmpty_false
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (prev curr : Instance D Γ)
    (hS : S.RepresentsStep I prev curr)
    (hEmpty : S.deltaEmpty = false) :
    ∃ X : Γ.syms,
      X ∈ P.idbList ∧
        ∃ t : Tuple D (Γ.arity X),
          t ∈ curr X ∧ t ∉ prev X := by
  have hExists :
      ∃ Y ∈ P.idbSymList,
        ¬(S.delta.lookupTuples Y.1 Y.2).isEmpty = true := by
    exact
      (List.all_eq_false.mp
        (by simpa [SemiNaiveState.deltaEmpty] using hEmpty))
  rcases hExists with ⟨Y, hYMem, hYNonempty⟩
  have hListNe :
      S.delta.lookupTuples Y.1 Y.2 ≠ [] := by
    intro hNil
    exact hYNonempty (List.isEmpty_iff.mpr hNil)
  rcases
    List.exists_mem_of_ne_nil
      (S.delta.lookupTuples Y.1 Y.2) hListNe with
    ⟨t, htList⟩
  have ht :
      t ∈ S.delta.lookup Y.1 Y.2 :=
    (MaterializedIDB.mem_lookupTuples_iff
      S.delta Y.1 Y.2 t).mp htList
  have htDiff : t ∈ curr Y.1 \ prev Y.1 := by
    simpa [hS.delta_eq Y.1 Y.2] using ht
  exact
    ⟨Y.1, P.idbSymList_mem_idbList Y hYMem, t,
      (Finset.mem_sdiff.mp htDiff).1,
      (Finset.mem_sdiff.mp htDiff).2⟩

theorem fixedOnInputAdom_of_deltaEmpty
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P)
    (prev curr : Instance D Γ)
    (hS : S.RepresentsStep I prev curr)
    (hEmpty : S.deltaEmpty = true) :
    P.immediateOnInputAdom I curr = curr := by
  have hPrevCurr : prev = curr := by
    apply Instance.ext
    intro X
    by_cases hX : X ∈ P.idb
    · apply Finset.ext
      intro t
      constructor
      · intro ht
        exact hS.prev_subset_curr X ht
      · intro ht
        by_cases htPrev : t ∈ prev X
        · exact htPrev
        · have htDiff : t ∈ curr X \ prev X := by
            exact Finset.mem_sdiff.mpr ⟨ht, htPrev⟩
          have htDelta :
              t ∈ S.delta.lookup X hX := by
            simpa [hS.delta_eq X hX] using htDiff
          have hDeltaEmpty :=
            P.deltaEmpty_lookup_eq_empty S hEmpty X hX
          rw [hDeltaEmpty] at htDelta
          simp at htDelta
    · rw [hS.curr_eq_immediate]
      exact
        (P.immediateOnInputAdom_preserves_edb
          I prev X hX).symm
  rw [← hPrevCurr]
  have hFixedPrev :
      prev = P.immediateOnInputAdom I prev := by
    simpa [hPrevCurr] using hS.curr_eq_immediate
  exact hFixedPrev.symm

def tupleCapacityForSyms
    (Q : Finset D) :
    List Γ.syms → Nat
| [] => 0
| X :: Xs =>
    Q.card ^ Γ.arity X +
      tupleCapacityForSyms Q Xs

omit [Domain D] [LinearOrder D] in
theorem tupleCapacityForSyms_foldl
    (Q : Finset D) :
    ∀ (xs : List Γ.syms) (acc : Nat),
      xs.foldl
          (fun acc X => acc + Q.card ^ Γ.arity X)
          acc =
        acc + tupleCapacityForSyms (Γ := Γ) Q xs
| [], acc => by
    simp [tupleCapacityForSyms]
| X :: Xs, acc => by
    rw [List.foldl_cons]
    rw [tupleCapacityForSyms_foldl Q Xs
      (acc + Q.card ^ Γ.arity X)]
    simp [tupleCapacityForSyms, Nat.add_assoc]

omit [LinearOrder D] in
theorem remainingCapacityForSyms_initial_le_tupleCapacity
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    ∀ xs : List Γ.syms,
      (∀ X : Γ.syms, X ∈ xs → X ∈ P.idb) →
        remainingCapacityForSyms
            (P.adom I) (P.initial I) xs ≤
          tupleCapacityForSyms (Γ := Γ) (P.adom I) xs
| [], _hAll => by
    simp [remainingCapacityForSyms, tupleCapacityForSyms]
| X :: Xs, hAll => by
    have hX : X ∈ P.idb := hAll X (by simp)
    have hTail :
        remainingCapacityForSyms
            (P.adom I) (P.initial I) Xs ≤
          tupleCapacityForSyms (Γ := Γ) (P.adom I) Xs :=
      remainingCapacityForSyms_initial_le_tupleCapacity
        P I Xs
        (fun Y hY => hAll Y (List.mem_cons_of_mem X hY))
    have hHead :
        ((Tuple.allOver (P.adom I) (Γ.arity X)) \
            P.initial I X).card ≤
          (P.adom I).card ^ Γ.arity X := by
      have hInitial : P.initial I X = ∅ :=
        P.initial_eq_empty_of_idb I X hX
      rw [hInitial]
      simpa using
        Tuple.allOver_card_le_pow (P.adom I) (Γ.arity X)
    simpa [remainingCapacityForSyms,
      tupleCapacityForSyms] using
      Nat.add_le_add hHead hTail

omit [LinearOrder D] in
theorem remainingCapacity_initial_lt_semiNaiveFuel
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    P.remainingCapacity (P.adom I) (P.initial I) <
      P.semiNaiveFuel I := by
  unfold remainingCapacity semiNaiveFuel
  have hLe :
      remainingCapacityForSyms
          (P.adom I) (P.initial I) P.idbList ≤
        tupleCapacityForSyms (Γ := Γ)
          (P.adom I) P.idbList :=
    P.remainingCapacityForSyms_initial_le_tupleCapacity
      I P.idbList
      (fun X hX => P.idbList_mem_idb hX)
  have hFold :
      P.idbList.foldl
          (fun acc X => acc + (P.adom I).card ^ Γ.arity X)
          0 =
        tupleCapacityForSyms (Γ := Γ)
          (P.adom I) P.idbList := by
    simpa using
      tupleCapacityForSyms_foldl (Γ := Γ)
        (P.adom I) P.idbList 0
  rw [hFold]
  exact Nat.lt_succ_of_le hLe

theorem snStepWithInput_inflationary
    (P : Program D Γ)
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema)
    (input : MaterializedInput P I)
    (S : SemiNaiveState P) :
    Instance.Subset (S.toInstance I)
      ((P.snStepWithInput compiled I input S).toInstance I) := by
  intro X t ht
  by_cases hX : X ∈ P.idb
  · have htOld : t ∈ S.current.lookup X hX := by
      simpa [SemiNaiveState.toInstance,
        MaterializedIDB.toInstance, hX] using ht
    unfold snStepWithInput SemiNaiveState.toInstance
      MaterializedIDB.toInstance
    rw [dif_pos hX]
    rw [lookup_currentIdbOfStepUpdates]
    rw [lookupCurrentUpdateTuples_stepRelationUpdatesWithInput]
    change
      t ∈ (Tuple.listUnion (S.current.lookupTuples X hX)
        (freshTuples (S.current.lookupTuples X hX)
          (compiled.semiNaiveConsequenceListForHeadWithInput
            I input S X))).toFinset
    rw [List.mem_toFinset, Tuple.mem_listUnion_iff]
    exact Or.inl
      ((MaterializedIDB.mem_lookupTuples_iff
        S.current X hX t).mpr htOld)
  · have htInitial :
        t ∈ MaterializedIDB.initialInstance
          P I X := by
      simpa [SemiNaiveState.toInstance,
        MaterializedIDB.toInstance, hX] using ht
    unfold snStepWithInput SemiNaiveState.toInstance
      MaterializedIDB.toInstance
    rw [dif_neg hX]
    exact htInitial

theorem semiNaiveStepWith_inflationary
    (P : Program D Γ)
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P) :
    Instance.Subset (S.toInstance I)
      ((P.semiNaiveStepWith compiled I S).toInstance I) := by
  simpa [semiNaiveStepWith] using
    P.snStepWithInput_inflationary
      compiled I (P.materializeInput I) S

theorem semiNaiveStep_inflationary
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (S : SemiNaiveState P) :
    Instance.Subset (S.toInstance I)
      ((P.semiNaiveStep I S).toInstance I) := by
  simpa [semiNaiveStep] using
    P.semiNaiveStepWith_inflationary P.compile I S

set_option linter.flexible false in
theorem snIterateWithInput_inflationary
    (P : Program D Γ)
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema)
    (input : MaterializedInput P I) :
    ∀ n : Nat,
      ∀ S : SemiNaiveState P,
        Instance.Subset (S.toInstance I)
          ((P.snIterateWithInput compiled I input n S).toInstance I)
| 0, S => by
    simpa [snIterateWithInput] using
      Instance.Subset_refl (S.toInstance I)
| n + 1, S => by
    rw [snIterateWithInput]
    by_cases hEmpty : S.deltaEmpty = true
    · simp [hEmpty]
      exact Instance.Subset_refl (S.toInstance I)
    · have hFalse : S.deltaEmpty = false :=
        Bool.eq_false_of_not_eq_true hEmpty
      simp [hFalse]
      exact
        Instance.Subset_trans
          (P.snStepWithInput_inflationary
            compiled I input S)
          (snIterateWithInput_inflationary P
            compiled I input n
            (P.snStepWithInput compiled I input S))

set_option linter.flexible false in
theorem semiNaiveIterateWith_inflationary
    (P : Program D Γ)
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema) :
    ∀ n : Nat,
      ∀ S : SemiNaiveState P,
        Instance.Subset (S.toInstance I)
          ((P.semiNaiveIterateWith compiled I n S).toInstance I) := by
  intro n S
  simpa [semiNaiveIterateWith] using
    P.snIterateWithInput_inflationary
      compiled I (P.materializeInput I) n S

set_option linter.flexible false in
theorem semiNaiveIterate_inflationary
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    ∀ n : Nat,
      ∀ S : SemiNaiveState P,
        Instance.Subset (S.toInstance I)
          ((P.semiNaiveIterate I n S).toInstance I) := by
  intro n S
  simpa [semiNaiveIterate] using
    P.semiNaiveIterateWith_inflationary
      P.compile I n S

set_option linter.flexible false in
theorem snIterateWithInput_fixed_of_remainingCapacity_lt
    (P : Program D Γ)
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema)
    (input : MaterializedInput P I) :
    ∀ n : Nat,
      ∀ (S : SemiNaiveState P)
        (prev curr : Instance D Γ),
        S.RepresentsStep I prev curr →
          P.remainingCapacity (P.adom I) prev < n →
            P.immediateOnInputAdom I
                ((P.snIterateWithInput compiled I input n S).toInstance I) =
              (P.snIterateWithInput compiled I input n S).toInstance I
| 0, _S, _prev, _curr, _hS, hFuel => by
    exact False.elim (Nat.not_lt_zero _ hFuel)
| n + 1, S, prev, curr, hS, hFuel => by
    rw [snIterateWithInput.eq_def]
    by_cases hEmpty : S.deltaEmpty = true
    · simp [hEmpty]
      rw [hS.toInstance_eq]
      exact
        P.fixedOnInputAdom_of_deltaEmpty
          I S prev curr hS hEmpty
    · have hFalse : S.deltaEmpty = false :=
        Bool.eq_false_of_not_eq_true hEmpty
      simp [hFalse]
      have hStep :
          (P.snStepWithInput compiled I input S).RepresentsStep
            I curr (P.immediateOnInputAdom I curr) :=
        P.snStepWithInput_represents_next_step
          compiled I input S prev curr hS
      have hNew :=
        P.exists_new_of_deltaEmpty_false
          I S prev curr hS hFalse
      rcases hNew with ⟨X, hXList, hTuple⟩
      have hDecrease :
          P.remainingCapacity (P.adom I) curr <
            P.remainingCapacity (P.adom I) prev := by
        unfold remainingCapacity
        exact
          remainingCapacityForSyms_lt_of_new
            (P.adom I)
            hS.prev_subset_curr hS.curr_bounded
            X hTuple P.idbList hXList
      have hFuelLe :
          P.remainingCapacity (P.adom I) prev ≤ n :=
        Nat.le_of_lt_succ hFuel
      exact
        snIterateWithInput_fixed_of_remainingCapacity_lt
          P compiled I input n
          (P.snStepWithInput compiled I input S)
          curr (P.immediateOnInputAdom I curr)
          hStep
          (Nat.lt_of_lt_of_le hDecrease hFuelLe)

set_option linter.flexible false in
theorem semiNaiveIterateWith_fixed_of_remainingCapacity_lt
    (P : Program D Γ)
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema) :
    ∀ n : Nat,
      ∀ (S : SemiNaiveState P)
        (prev curr : Instance D Γ),
        S.RepresentsStep I prev curr →
          P.remainingCapacity (P.adom I) prev < n →
            P.immediateOnInputAdom I
                ((P.semiNaiveIterateWith compiled I n S).toInstance I) =
              (P.semiNaiveIterateWith compiled I n S).toInstance I := by
  intro n S prev curr hS hFuel
  simpa [semiNaiveIterateWith] using
    P.snIterateWithInput_fixed_of_remainingCapacity_lt
      compiled I (P.materializeInput I) n S prev curr hS hFuel

set_option linter.flexible false in
theorem semiNaiveIterate_fixed_of_remainingCapacity_lt
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    ∀ n : Nat,
      ∀ (S : SemiNaiveState P)
        (prev curr : Instance D Γ),
        S.RepresentsStep I prev curr →
          P.remainingCapacity (P.adom I) prev < n →
            P.immediateOnInputAdom I
                ((P.semiNaiveIterate I n S).toInstance I) =
              (P.semiNaiveIterate I n S).toInstance I := by
  intro n S prev curr hS hFuel
  simpa [semiNaiveIterate] using
    P.semiNaiveIterateWith_fixed_of_remainingCapacity_lt
      P.compile I n S prev curr hS hFuel

set_option linter.flexible false in
theorem snIterateWithInput_subset_of_prefixed
    (P : Program D Γ)
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema)
    (input : MaterializedInput P I)
    (J : Instance D Γ)
    (hClosed :
      Instance.Subset (P.immediateOnInputAdom I J) J) :
    ∀ n : Nat,
      ∀ (S : SemiNaiveState P)
        (prev curr : Instance D Γ),
        S.RepresentsStep I prev curr →
          Instance.Subset curr J →
            Instance.Subset
              ((P.snIterateWithInput compiled I input n S).toInstance I) J
| 0, S, _prev, curr, hS, hCurrM => by
  intro X t ht
  exact hCurrM X
    (by
      simpa [snIterateWithInput,
        hS.toInstance_eq] using ht)
| n + 1, S, prev, curr, hS, hCurrM => by
    rw [snIterateWithInput.eq_def]
    by_cases hEmpty : S.deltaEmpty = true
    · simp [hEmpty]
      intro X t ht
      exact hCurrM X (by simpa [hS.toInstance_eq] using ht)
    · have hFalse : S.deltaEmpty = false :=
        Bool.eq_false_of_not_eq_true hEmpty
      simp [hFalse]
      have hStep :
          (P.snStepWithInput compiled I input S).RepresentsStep
            I curr (P.immediateOnInputAdom I curr) :=
        P.snStepWithInput_represents_next_step
          compiled I input S prev curr hS
      have hNextM :
          Instance.Subset
            (P.immediateOnInputAdom I curr) J :=
        Instance.Subset_trans
          (P.immediateOnInputAdom_mono I hCurrM)
          hClosed
      exact
        snIterateWithInput_subset_of_prefixed
          P compiled I input J hClosed n
          (P.snStepWithInput compiled I input S)
          curr (P.immediateOnInputAdom I curr)
          hStep hNextM

set_option linter.flexible false in
theorem semiNaiveIterateWith_subset_of_prefixed
    (P : Program D Γ)
    (compiled : CompiledProgram P)
    (I : Instance D P.edbSchema)
    (J : Instance D Γ)
    (hClosed :
      Instance.Subset (P.immediateOnInputAdom I J) J) :
    ∀ n : Nat,
      ∀ (S : SemiNaiveState P)
        (prev curr : Instance D Γ),
        S.RepresentsStep I prev curr →
          Instance.Subset curr J →
            Instance.Subset
              ((P.semiNaiveIterateWith compiled I n S).toInstance I) J := by
  intro n S prev curr hS hCurrM
  simpa [semiNaiveIterateWith] using
    P.snIterateWithInput_subset_of_prefixed
      compiled I (P.materializeInput I) J hClosed
      n S prev curr hS hCurrM

set_option linter.flexible false in
theorem semiNaiveIterate_subset_of_prefixed
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (J : Instance D Γ)
    (hClosed :
      Instance.Subset (P.immediateOnInputAdom I J) J) :
    ∀ n : Nat,
      ∀ (S : SemiNaiveState P)
        (prev curr : Instance D Γ),
        S.RepresentsStep I prev curr →
          Instance.Subset curr J →
            Instance.Subset
              ((P.semiNaiveIterate I n S).toInstance I) J := by
  intro n S prev curr hS hCurrM
  simpa [semiNaiveIterate] using
    P.semiNaiveIterateWith_subset_of_prefixed
      P.compile I J hClosed n S prev curr hS hCurrM

/-
  Final semi-naive output is closed under one input-domain
  immediate-consequence step.
-/
theorem snLFP_fixedOnInputAdom
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    P.immediateOnInputAdom I (P.snLFP I) = P.snLFP I := by
  unfold snLFP snLFPState
  exact
    P.semiNaiveIterate_fixed_of_remainingCapacity_lt I
      (P.semiNaiveFuel I)
      (P.semiNaiveInitialState I)
      (P.initial I)
      (P.immediateOnInputAdom I (P.initial I))
      (P.semiNaiveInitialState_represents_initial_step I)
      (P.remainingCapacity_initial_lt_semiNaiveFuel I)

/-
  The initial empty-IDB instance is contained in the
  semi-naive fixed-point output.
-/
theorem initial_subset_snLFP
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    Instance.Subset (P.initial I) (P.snLFP I) := by
  unfold snLFP snLFPState
  have hInitState :=
    P.semiNaiveInitialState_represents_initial_step I
  have hInitCurr :
      Instance.Subset (P.initial I)
        ((P.semiNaiveInitialState I).toInstance I) := by
    rw [hInitState.toInstance_eq]
    exact
      P.immediateOnInputAdom_inflationary I
        (P.initial I)
  exact
    Instance.Subset_trans hInitCurr
      (P.semiNaiveIterate_inflationary I
        (P.semiNaiveFuel I)
        (P.semiNaiveInitialState I))

end Program

end Datalog

------------------------------------------------------------
-- Least Fixed-Point and Minimal Model Correctness
------------------------------------------------------------

namespace Datalog

namespace Program

variable {A D : Type}
variable [RelationNames A] [Domain D] [LinearOrder D] [Hashable D]
variable {Γ : UnnamedSchema A}

/-
  The actual semi-naive evaluator agrees with the existing
  operational LFP.
-/
theorem snLFP_eq_LFP
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    P.snLFP I = P.LFP I := by
  apply Instance.ext
  intro X
  apply Finset.ext
  intro t
  constructor
  · intro ht
    have hInitState :=
      P.semiNaiveInitialState_represents_initial_step I
    have hClosed :
        Instance.Subset
          (P.immediateOnInputAdom I (P.LFP I))
          (P.LFP I) := by
      rw [P.LFP_fixedOnInputAdom I]
      exact Instance.Subset_refl (P.LFP I)
    have hStart :
        Instance.Subset
          (P.immediateOnInputAdom I (P.initial I))
          (P.LFP I) :=
      Instance.Subset_trans
        (P.immediateOnInputAdom_mono I
          (P.initial_subset_LFP I))
        hClosed
    have hIter :
        Instance.Subset
          ((P.semiNaiveIterate I
              (P.semiNaiveFuel I)
              (P.semiNaiveInitialState I)).toInstance I)
          (P.LFP I) :=
      P.semiNaiveIterate_subset_of_prefixed I (P.LFP I)
        hClosed
        (P.semiNaiveFuel I)
        (P.semiNaiveInitialState I)
        (P.initial I)
        (P.immediateOnInputAdom I (P.initial I))
        hInitState hStart
    exact hIter X (by simpa [snLFP, snLFPState] using ht)
  · intro ht
    have hClosed :
        Instance.Subset
          (P.immediateOnInputAdom I (P.snLFP I))
          (P.snLFP I) := by
      rw [P.snLFP_fixedOnInputAdom I]
      exact Instance.Subset_refl (P.snLFP I)
    have hSub :
        Instance.Subset (P.LFP I) (P.snLFP I) :=
      P.LFP_subset_of_immediateOnInputAdom_prefixed_point I
        (P.snLFP I)
        (P.initial_subset_snLFP I)
        hClosed
    exact hSub X ht

/-
  The actual semi-naive evaluator agrees with the
  model-theoretic minimal model.
-/
theorem snLFP_eq_minimalModel
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    P.snLFP I = P.minimalModel I := by
  exact (P.snLFP_eq_LFP I).trans (P.LFP_eq_minimalModel I)

end Program

end Datalog

------------------------------------------------------------
-- Query Correctness
------------------------------------------------------------

namespace Datalog

namespace Query

variable {A D : Type}
variable [RelationNames A] [Domain D] [LinearOrder D] [Hashable D]
variable {Γ : UnnamedSchema A}

/-
  Query answers computed by the semi-naive evaluator agree
  with the model-theoretic query answer.
-/
theorem snAnswer_eq_answer
    (q : Query D Γ n)
    (I : Instance D q.program.edbSchema) :
    q.snAnswer I = q.answer I := by
  unfold snAnswer answer
  rw [q.program.snLFP_eq_minimalModel I]

end Query

end Datalog
