-- Author: Jesse Comer
import Databases.RelCalc.AdomSemantics
import Databases.UnnamedRA.Semantics

/-
  This file defines the standard compositional translation
  of relational algebra into relational calculus, used for
  the forward direction of Codd's theorem.

  The construction uses canonical variable blocks to mirror
  the positional arguments of RA output tuples. If an RA
  expression has output arity n, the translated formula
  uses the variables from start through start + n - 1. The
  offset start is an arbitrary allocation choice in the
  infinite RelCalc variable supply; products and projections
  allocate adjacent blocks to keep positional roles
  explicit.

  The main construction is:
    * `RAExpr.toRelCalcQuery`

  The specification is equivalence of RA tuple membership
  with RelCalc formula satisfaction, then equality of the
  RA denotation and translated query denotation.

  Key theorems include:
    * `RAExpr.toRelCalcQuery_formula_iff`
    * `RAExpr.toRelCalcQuery_eval_eq`
    * `RAExpr.exists_equiv_relCalcQuery`

  Intervening definitions and lemmas are translation,
  metadata, and proof support.
-/

------------------------------------------------------------
-- Canonical Variable Blocks
------------------------------------------------------------

namespace UnnamedRA

namespace ToRelCalc

open RelCalc

namespace Var

/- Canonical block of `count` consecutive variables. -/
def block
    (start count : Nat) : List Var :=
  List.ofFn (fun i : Fin count => start + i)

theorem length_block
    (start count : Nat) :
    (block start count).length = count := by
  simp [block]

theorem nodup_block
    (start count : Nat) :
    (block start count).Nodup := by
  rw [block, List.nodup_ofFn]
  intro i j hij
  exact Fin.ext (Nat.add_left_cancel hij)

/-
  Membership in a canonical block is equivalent to lying
  in the corresponding half-open interval.
-/
theorem mem_toFinset_block_iff
    {x start count : Nat} :
    x ∈ (block start count).toFinset ↔
      start ≤ x ∧ x < start + count := by
  constructor
  · intro hx
    rw [block, List.mem_toFinset] at hx
    rcases List.mem_ofFn.mp hx with ⟨i, rfl⟩
    constructor
    · exact Nat.le_add_right start i
    · omega
  · rintro ⟨hStart, hEnd⟩
    rw [block, List.mem_toFinset]
    refine List.mem_ofFn.mpr ?_
    refine ⟨⟨x - start, by omega⟩, ?_⟩
    exact Nat.add_sub_of_le hStart

theorem block_zero
    (start : Nat) :
    block start 0 = [] := by
  simp [block]

theorem block_succ
    (start count : Nat) :
    block start (count + 1) =
      start :: block (start + 1) count := by
  rw [block, List.ofFn_succ, block]
  congr
  funext i
  simp [Nat.add_comm, Nat.add_left_comm]

/- Adjacent variable blocks concatenate. -/
theorem block_add
    (start n m : Nat) :
    block start (n + m) =
      block start n ++ block (start + n) m := by
  induction n generalizing start with
  | zero =>
      simp [block_zero]
  | succ n ih =>
      have hAdd : n + 1 + m = (n + m) + 1 := by
        omega
      rw [hAdd, block_succ, block_succ, ih]
      simp [Nat.add_left_comm, Nat.add_comm]

/-
  The finset of a larger block is the union of two
  adjacent sub-blocks.
-/
theorem toFinset_block_add
    (start n m : Nat) :
    (block start (n + m)).toFinset =
      (block start n).toFinset ∪
        (block (start + n) m).toFinset := by
  rw [block_add]
  simp

/- Adjacent canonical blocks are disjoint. -/
theorem disjoint_toFinset_block_add
    (start n m : Nat) :
    Disjoint
      (block start n).toFinset
      (block (start + n) m).toFinset := by
  rw [Finset.disjoint_left]
  intro x hxLeft hxRight
  rw [mem_toFinset_block_iff] at hxLeft
  rw [mem_toFinset_block_iff] at hxRight
  omega

end Var

namespace Term

variable {D : Type}
variable [Domain D]

/- Canonical tuple of consecutive variables. -/
def varTuple
    (start n : Nat) :
    Vector (RelTerm D) n :=
  Vector.ofFn (fun i => .var (start + i))

theorem listVars_map_var
    (xs : List Var) :
    RelTerm.listVars
        (xs.map (RelTerm.var (D := D))) =
      xs.toFinset := by
  induction xs with
  | nil =>
      simp [RelTerm.listVars]
  | cons x xs ih =>
      simp [RelTerm.listVars, RelTerm.vars, ih]

theorem listConstants_map_var
    (xs : List Var) :
    RelTerm.listConstants
        (xs.map (RelTerm.var (D := D))) =
      ∅ := by
  induction xs with
  | nil =>
      simp [RelTerm.listConstants]
  | cons x xs ih =>
      simp [RelTerm.listConstants,
        RelTerm.constants, ih]

theorem tupleVars_varTuple
    (start n : Nat) :
    RelTerm.tupleVars (varTuple (D := D) start n) =
      (Var.block start n).toFinset := by
  rw [RelTerm.tupleVars, varTuple, Vector.toList_ofFn]
  simpa [Var.block] using
    (listVars_map_var (D := D)
      (List.ofFn fun i : Fin n => start + i))

end Term

namespace BlockAssign

variable {D : Type}
variable [Domain D]

/-
  Assignment sending a consecutive variable block to tuple
  coordinates.
-/
def onBlock
    (start : Nat)
    {n : Nat}
    (t : Tuple D n) : Assign D :=
  fun x =>
    if h : start ≤ x ∧ x < start + n then
      t[(x - start)]'(by
        exact (Nat.sub_lt_iff_lt_add' h.1).2 h.2)
    else
      default

/-
  Fill a consecutive variable block, leaving the rest
  unchanged.
-/
def withBlock
    (σ : Assign D)
    (start : Nat)
    {n : Nat}
    (t : Tuple D n) :
    Assign D :=
  fun x =>
    if h : start ≤ x ∧ x < start + n then
      t[(x - start)]'(by
        exact (Nat.sub_lt_iff_lt_add' h.1).2 h.2)
    else
      σ x

theorem onBlock_eq
    (start : Nat)
    {n : Nat}
    (t : Tuple D n)
    (i : Fin n) :
    onBlock start t (start + i) = t.get i := by
  have h :
      start ≤ start + i ∧
        start + i < start + n := by
    omega
  have hsub : start + i - start = i := by
    omega
  simp [onBlock, h, hsub, Vector.get]

omit [Domain D] in
theorem withBlock_eq
    (σ : Assign D)
    (start : Nat)
    {n : Nat}
    (t : Tuple D n)
    (i : Fin n) :
    withBlock σ start t (start + i) = t.get i := by
  have h :
      start ≤ start + i ∧
        start + i < start + n := by
    omega
  have hsub : start + i - start = i := by
    omega
  simp [withBlock, h, hsub, Vector.get]

omit [Domain D] in
theorem withBlock_eq_of_lt
    (σ : Assign D)
    (start : Nat)
    {n : Nat}
    (t : Tuple D n)
    {x : Var}
    (hx : x < start) :
    withBlock σ start t x = σ x := by
  have hFalse : ¬ (start ≤ x ∧ x < start + n) := by
    intro h
    exact Nat.not_le_of_gt hx h.1
  simp [withBlock, hFalse]

theorem mapsInto_onBlock
    (start : Nat)
    {n : Nat}
    {Q : Set D}
    {t : Tuple D n}
    (ht : Tuple.MapsInto t Q) :
    Assign.MapsInto
      (onBlock start t)
      ((Var.block start n).toFinset)
      Q := by
  intro x hx
  rw [Var.mem_toFinset_block_iff] at hx
  let i : Fin n := ⟨x - start, by omega⟩
  have hxEq : x = start + i := by
    dsimp [i]
    exact (Nat.add_sub_of_le hx.1).symm
  rw [hxEq]
  rw [onBlock_eq start t i]
  exact ht i

omit [Domain D] in
theorem mapsInto_withBlock
    (σ : Assign D)
    (start : Nat)
    {n : Nat}
    {t : Tuple D n}
    {Q : Set D}
    (ht : Tuple.MapsInto t Q) :
    Assign.MapsInto
      (withBlock σ start t)
      ((Var.block start n).toFinset)
      Q := by
  intro x hx
  rw [Var.mem_toFinset_block_iff] at hx
  let i : Fin n := ⟨x - start, by omega⟩
  have hxEq : x = start + i := by
    dsimp [i]
    exact (Nat.add_sub_of_le hx.1).symm
  rw [hxEq]
  rw [withBlock_eq σ start t i]
  exact ht i

theorem withBlock_agreeOn_onBlock
    (σ : Assign D)
    (start : Nat)
    {n : Nat}
    (t : Tuple D n) :
    Assign.AgreeOn
      (withBlock σ start t)
      (onBlock start t)
      ((Var.block start n).toFinset) := by
  intro x hx
  rw [Var.mem_toFinset_block_iff] at hx
  let i : Fin n := ⟨x - start, by omega⟩
  have hxEq : x = start + i := by
    dsimp [i]
    exact (Nat.add_sub_of_le hx.1).symm
  rw [hxEq]
  rw [withBlock_eq σ start t i, onBlock_eq start t i]

end BlockAssign

/-
  Canonical variable blocks as vectors for indexed queries.
-/
def blockVector
    (start count : Nat) :
    Vector Var count :=
  Vector.ofFn (fun i : Fin count => start + i)

@[simp] theorem blockVector_toList
    (start count : Nat) :
    (blockVector start count).toList =
      Var.block start count := by
  rw [blockVector, Vector.toList_ofFn]
  rfl

end ToRelCalc

end UnnamedRA

------------------------------------------------------------
-- Formula Builders Over Blocks
------------------------------------------------------------

namespace UnnamedRA

namespace ToRelCalc

open RelCalc

section Builders

variable {A D : Type}
variable [RelationNames A] [Domain D]

/-
  Formula builders are the only place where canonical
  variable blocks are exposed. The translator below
  treats them as an allocation discipline, not as a separate
  proof object.
-/

/-
  Translate a selection predicate against a block with start
  variable `start`.
-/
def selFormulaAt
    {Γ : UnnamedSchema A}
    (start : Nat) : Sel D → Formula D Γ
| .eqIdx i j =>
    .eq (.var (start + i)) (.var (start + j))
| .eqConst i c =>
    .eq (.var (start + i)) (.const c)
| .and s₁ s₂ =>
    .and (selFormulaAt start s₁) (selFormulaAt start s₂)
| .or s₁ s₂ =>
    .or (selFormulaAt start s₁) (selFormulaAt start s₂)
| .not s =>
    .not (selFormulaAt start s)

/- A tautology mentioning exactly a canonical block. -/
def supportAt
    {Γ : UnnamedSchema A} :
    Nat → Nat → Formula D Γ
| _, 0 => .top
| start, count + 1 =>
    .and (.eq (.var start) (.var start))
      (supportAt (start + 1) count)

/- A contradiction mentioning exactly a canonical block. -/
def emptyAt
    {Γ : UnnamedSchema A}
    (start count : Nat) :
    Formula D Γ :=
  .and (supportAt (D := D) (Γ := Γ) start count) .bot

/- Canonical relation atom over a variable block. -/
def atomAt
    {Γ : UnnamedSchema A}
    (X : Γ.syms)
    (start : Nat) :
    Formula D Γ :=
  .rel { rel := X, args := Term.varTuple (D := D) start (Γ.arity X) }

/- Canonical singleton atom at one variable. -/
def singleAt
    {Γ : UnnamedSchema A}
    (d : D)
    (start : Nat) :
    Formula D Γ :=
  .eq (.var start) (.const d)

/-
  Projection links from output variables to selected source
  variables.
-/
def projLinksAt
    {Γ : UnnamedSchema A}
    (start srcStart : Nat) :
    List Nat → Formula D Γ
| [] => .top
| i :: idxs =>
    .and
      (.eq (.var start) (.var (srcStart + i)))
      (projLinksAt (start + 1) srcStart idxs)

theorem freeVars_supportAt
    {Γ : UnnamedSchema A}
    (start count : Nat) :
    (supportAt (D := D) (Γ := Γ) start count).freeVars =
      (Var.block start count).toFinset := by
  induction count generalizing start with
  | zero =>
      simp [supportAt, Formula.freeVars, Var.block_zero]
  | succ count ih =>
      simp [supportAt, Formula.freeVars, RelTerm.vars, ih,
        Var.block_succ]

theorem constants_supportAt
    {Γ : UnnamedSchema A}
    (start count : Nat) :
    (supportAt (D := D) (Γ := Γ) start count).constants =
      ∅ := by
  induction count generalizing start with
  | zero =>
      simp [supportAt, Formula.constants]
  | succ count ih =>
      simp [supportAt, Formula.constants,
        RelTerm.constants, ih]

theorem freeVars_emptyAt
    {Γ : UnnamedSchema A}
    (start count : Nat) :
    (emptyAt (D := D) (Γ := Γ) start count).freeVars =
      (Var.block start count).toFinset := by
  simp [emptyAt, Formula.freeVars, freeVars_supportAt]

theorem constants_emptyAt
    {Γ : UnnamedSchema A}
    (start count : Nat) :
    (emptyAt (D := D) (Γ := Γ) start count).constants =
      ∅ := by
  simp [emptyAt, Formula.constants, constants_supportAt]

theorem not_satIn_emptyAt
    {Q : Set D}
    {Γ : UnnamedSchema A}
    {I : Instance D Γ}
    {σ : Assign D}
    (start count : Nat) :
    ¬ Formula.ArbitraryAssignSatIn Q I σ
        (emptyAt (D := D) (Γ := Γ) start count) := by
  simp [emptyAt, Formula.ArbitraryAssignSatIn]

theorem freeVars_atomAt
    {Γ : UnnamedSchema A}
    (X : Γ.syms)
    (start : Nat) :
  (atomAt (D := D) X start).freeVars =
      (Var.block start (Γ.arity X)).toFinset := by
  simp [atomAt, Formula.freeVars, RelAtom.vars,
    UnnamedRA.ToRelCalc.Term.tupleVars_varTuple]

theorem tupleConstants_varTuple
    (start n : Nat) :
    RelTerm.tupleConstants
        (Term.varTuple (D := D) start n) =
      ∅ := by
  rw [RelTerm.tupleConstants, Term.varTuple,
    Vector.toList_ofFn]
  simpa [Var.block] using
    UnnamedRA.ToRelCalc.Term.listConstants_map_var (D := D)
      (Var.block start n)

theorem constants_atomAt
    {Γ : UnnamedSchema A}
    (X : Γ.syms)
    (start : Nat) :
  (atomAt (D := D) X start).constants =
      ∅ := by
  simp [atomAt, Formula.constants, RelAtom.constants,
    tupleConstants_varTuple]

theorem freeVars_singleAt
    {Γ : UnnamedSchema A}
    (d : D)
    (start : Nat) :
    (singleAt (D := D) (Γ := Γ) d start).freeVars =
      (Var.block start 1).toFinset := by
  simp [singleAt, Formula.freeVars, RelTerm.vars,
    Var.block_succ, Var.block_zero]

theorem constants_singleAt
    {Γ : UnnamedSchema A}
    (d : D)
    (start : Nat) :
    (singleAt (D := D) (Γ := Γ) d start).constants =
      {d} := by
  simp [singleAt, Formula.constants, RelTerm.constants]

theorem constants_selFormulaAt
    {Γ : UnnamedSchema A}
    (start : Nat) :
    ∀ s : Sel D,
      (selFormulaAt (D := D) (Γ := Γ) start s).constants =
        s.constants
| .eqIdx _ _ => by
    simp [selFormulaAt, Formula.constants, Sel.constants,
      RelTerm.constants]
| .eqConst _ c => by
    simp [selFormulaAt, Formula.constants, Sel.constants,
      RelTerm.constants]
| .and s₁ s₂ => by
    simp [selFormulaAt, Formula.constants, Sel.constants,
      constants_selFormulaAt start s₁,
      constants_selFormulaAt start s₂]
| .or s₁ s₂ => by
    simp [selFormulaAt, Formula.constants, Sel.constants,
      constants_selFormulaAt start s₁,
      constants_selFormulaAt start s₂]
| .not s => by
    simp [selFormulaAt, Formula.constants, Sel.constants,
      constants_selFormulaAt start s]

theorem freeVars_selFormulaAt_subset
    {Γ : UnnamedSchema A}
    {start n : Nat} :
    ∀ s : Sel D,
      s.arityReq < n →
      (selFormulaAt
          (D := D) (Γ := Γ) start s).freeVars ⊆
        (Var.block start n).toFinset
  | .eqIdx i j, hAr => by
    have hi : i < n :=
      Nat.lt_of_le_of_lt (Nat.le_max_left i j) hAr
    have hj : j < n :=
      Nat.lt_of_le_of_lt (Nat.le_max_right i j) hAr
    intro x hx
    have hx' : x = start + i ∨ x = start + j := by
      simpa [selFormulaAt, Formula.freeVars,
        RelTerm.vars] using hx
    rw [Var.mem_toFinset_block_iff]
    rcases hx' with rfl | rfl
    · omega
    · omega
  | .eqConst i c, hAr => by
    have hi : i < n := by
      simpa [Sel.arityReq] using hAr
    intro x hx
    have hx' : x = start + i := by
      simpa [selFormulaAt, Formula.freeVars,
        RelTerm.vars] using hx
    rw [Var.mem_toFinset_block_iff]
    rw [hx']
    exact
      ⟨Nat.le_add_right start i,
        Nat.add_lt_add_left hi start⟩
  | .and s₁ s₂, hAr => by
    have h₁ : s₁.arityReq < n :=
      Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hAr
    have h₂ : s₂.arityReq < n :=
      Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hAr
    intro x hx
    have hx' :
        x ∈
            (selFormulaAt
              (D := D) (Γ := Γ) start s₁).freeVars ∨
          x ∈
            (selFormulaAt
              (D := D) (Γ := Γ) start s₂).freeVars := by
      simpa [selFormulaAt, Formula.freeVars] using hx
    rcases hx' with hx | hx
    · exact freeVars_selFormulaAt_subset s₁ h₁ hx
    · exact freeVars_selFormulaAt_subset s₂ h₂ hx
  | .or s₁ s₂, hAr => by
    have h₁ : s₁.arityReq < n :=
      Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hAr
    have h₂ : s₂.arityReq < n :=
      Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hAr
    intro x hx
    have hx' :
        x ∈
            (selFormulaAt
              (D := D) (Γ := Γ) start s₁).freeVars ∨
          x ∈
            (selFormulaAt
              (D := D) (Γ := Γ) start s₂).freeVars := by
      simpa [selFormulaAt, Formula.freeVars] using hx
    rcases hx' with hx | hx
    · exact freeVars_selFormulaAt_subset s₁ h₁ hx
    · exact freeVars_selFormulaAt_subset s₂ h₂ hx
  | .not s, hAr => by
    simpa [selFormulaAt, Formula.freeVars] using
      freeVars_selFormulaAt_subset s hAr

theorem satIn_selFormulaAt_iff
    {Q : Set D}
    {Γ : UnnamedSchema A}
    {I : Instance D Γ}
    {σ : Assign D}
    {n start : Nat}
    {t : Tuple D n}
    (hσ : ∀ i : Fin n, σ (start + i) = t.get i) :
    ∀ s : Sel D,
      s.arityReq < n →
      (Formula.ArbitraryAssignSatIn Q I σ
          (selFormulaAt (D := D) (Γ := Γ) start s) ↔
        Sel.Holds s t)
| .eqIdx i j, hAr => by
    have hi : i < n :=
      Nat.lt_of_le_of_lt (Nat.le_max_left i j) hAr
    have hj : j < n :=
      Nat.lt_of_le_of_lt (Nat.le_max_right i j) hAr
    calc
      Formula.ArbitraryAssignSatIn Q I σ
          (selFormulaAt
            (D := D) (Γ := Γ) start (.eqIdx i j)) ↔
          σ (start + i) = σ (start + j) := by
            simp [selFormulaAt,
              Formula.ArbitraryAssignSatIn, RelTerm.eval]
      _ ↔ t[i] = t[j] := by
            constructor <;> intro h <;>
              simpa [hσ ⟨i, hi⟩, hσ ⟨j, hj⟩]
                using h
      _ ↔ Sel.Holds (.eqIdx i j) t := by
            simpa using (Sel.holds_eqIdx_iff t hi hj).symm
| .eqConst i c, hAr => by
    have hi : i < n := by
      simpa [Sel.arityReq] using hAr
    calc
      Formula.ArbitraryAssignSatIn Q I σ
          (selFormulaAt
            (D := D) (Γ := Γ) start (.eqConst i c)) ↔
          σ (start + i) = c := by
            simp [selFormulaAt,
              Formula.ArbitraryAssignSatIn, RelTerm.eval]
      _ ↔ t[i] = c := by
            constructor <;> intro h <;>
              simpa [hσ ⟨i, hi⟩] using h
      _ ↔ Sel.Holds (.eqConst i c) t := by
            simpa using (Sel.holds_eqConst_iff t hi).symm
| .and s₁ s₂, hAr => by
    have h₁ : s₁.arityReq < n :=
      Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hAr
    have h₂ : s₂.arityReq < n :=
      Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hAr
    simp [selFormulaAt, Formula.ArbitraryAssignSatIn,
      Sel.Holds,
      satIn_selFormulaAt_iff hσ s₁ h₁,
      satIn_selFormulaAt_iff hσ s₂ h₂]
| .or s₁ s₂, hAr => by
    have h₁ : s₁.arityReq < n :=
      Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hAr
    have h₂ : s₂.arityReq < n :=
      Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hAr
    simp [selFormulaAt, Formula.ArbitraryAssignSatIn,
      Sel.Holds,
      satIn_selFormulaAt_iff hσ s₁ h₁,
      satIn_selFormulaAt_iff hσ s₂ h₂]
| .not s, hAr => by
    simp [selFormulaAt, Formula.ArbitraryAssignSatIn,
      Sel.Holds,
      satIn_selFormulaAt_iff hσ s hAr]

theorem freeVars_projLinksAt
    {Γ : UnnamedSchema A}
    (start srcStart : Nat)
    (idxs : List Nat) :
    (projLinksAt
        (D := D) (Γ := Γ)
        start srcStart idxs).freeVars =
      (Var.block start idxs.length).toFinset ∪
        (idxs.map (fun i => srcStart + i)).toFinset := by
  induction idxs generalizing start with
  | nil =>
      simp [projLinksAt, Var.block_zero,
        Formula.freeVars]
  | cons i idxs ih =>
      simp [projLinksAt, Formula.freeVars, RelTerm.vars, ih,
        Var.block_succ, Finset.union_left_comm,
        Finset.union_comm]

theorem constants_projLinksAt
    {Γ : UnnamedSchema A}
    (start srcStart : Nat)
    (idxs : List Nat) :
    (projLinksAt
        (D := D) (Γ := Γ)
        start srcStart idxs).constants =
      ∅ := by
  induction idxs generalizing start with
  | nil =>
      simp [projLinksAt, Formula.constants]
  | cons i idxs ih =>
      simp [projLinksAt, Formula.constants,
        RelTerm.constants, ih]

theorem satIn_singleAt_iff
    {Q : Set D}
    {Γ : UnnamedSchema A}
    {I : Instance D Γ}
    {σ : Assign D}
    {d : D}
    {start : Nat}
    {t : Tuple D 1}
    (hσ : σ start = t[0]) :
    Formula.ArbitraryAssignSatIn Q I σ
      (singleAt (D := D) (Γ := Γ) d start) ↔
        t[0] = d := by
  simp [singleAt, Formula.ArbitraryAssignSatIn,
    RelTerm.eval, hσ]

theorem satIn_atomAt_iff
    {Q : Set D}
    {Γ : UnnamedSchema A}
    {I : Instance D Γ}
    {σ : Assign D}
    {X : Γ.syms}
    {start : Nat}
    {t : Tuple D (Γ.arity X)}
    (hσ :
      ∀ i : Fin (Γ.arity X),
        σ (start + i) = t.get i) :
    Formula.ArbitraryAssignSatIn Q I σ
      (atomAt (D := D) X start) ↔ t ∈ I X := by
  have hEval :
      RelTerm.evalVector σ
        (Term.varTuple
          (D := D) start (Γ.arity X)) = t := by
    apply Vector.ext
    intro i hi
    rw [RelTerm.evalVector, Vector.getElem_ofFn]
    change
      RelTerm.eval σ
        ((Term.varTuple
          (D := D) start (Γ.arity X))[i]) =
          t[i]
    have hVar :
        (Term.varTuple (D := D) start (Γ.arity X))[i] =
          RelTerm.var (start + i) := by
      simp [Term.varTuple, Vector.getElem_ofFn]
    simpa [RelTerm.eval, hVar] using hσ ⟨i, hi⟩
  constructor
  · intro hSat
    unfold Formula.ArbitraryAssignSatIn atomAt RelAtom.Sat
      RelAtom.evalFact RelFact.Mem at hSat
    change
      RelTerm.evalVector σ
        (Term.varTuple (D := D) start (Γ.arity X)) ∈ I X
      at hSat
    rw [hEval] at hSat
    simpa using hSat
  · intro hMem
    unfold Formula.ArbitraryAssignSatIn atomAt RelAtom.Sat
      RelAtom.evalFact RelFact.Mem
    change
      RelTerm.evalVector σ
        (Term.varTuple (D := D) start (Γ.arity X)) ∈ I X
    rw [hEval]
    simpa using hMem

theorem satIn_projLinksAt_iff
    {Q : Set D}
    {Γ : UnnamedSchema A}
    {I : Instance D Γ}
    {σ : Assign D}
    {n : Nat}
    {idxs : List Nat}
    {start srcStart : Nat}
    {u : Tuple D n}
    {t : Tuple D idxs.length}
    (hIdx : ∀ i ∈ idxs, i < n)
    (hOut :
      ∀ j : Fin idxs.length,
        σ (start + j) = t.get j)
    (hSrc :
      ∀ i : Fin n,
        σ (srcStart + i) = u.get i) :
    Formula.ArbitraryAssignSatIn Q I σ
      (projLinksAt (D := D) (Γ := Γ)
        start srcStart idxs) ↔
      FinRelation.projTuple idxs u hIdx = t := by
  induction idxs generalizing start with
  | nil =>
      constructor
      · intro _
        apply Vector.ext
        intro i hi
        exact (Nat.not_lt_zero _ hi).elim
      · intro _
        simp [projLinksAt, Formula.ArbitraryAssignSatIn]
  | cons i idxs ih =>
      constructor
      · intro hSat
        rcases hSat with ⟨hHead, hTail⟩
        have hi : i < n := hIdx i (by simp)
        have hEqVars :
            σ start = σ (srcStart + i) := by
          simpa [projLinksAt, Formula.ArbitraryAssignSatIn,
            RelTerm.eval] using hHead
        have hHeadEq : t[0] = u[i] := by
          have hOut0 : σ start = t[0] := by
            simpa using hOut ⟨0, by simp⟩
          have hSrcI : σ (srcStart + i) = u[i] := by
            simpa using hSrc ⟨i, hi⟩
          rw [hOut0, hSrcI] at hEqVars
          exact hEqVars
        let tTail : Tuple D idxs.length :=
          Vector.ofFn
            (fun j =>
              t.get ⟨j.1 + 1, by simp [j.2]⟩)
        have hOutTail :
            ∀ j : Fin idxs.length,
              σ ((start + 1) + j) =
                tTail.get j := by
          intro j
          have hOutJ :=
            hOut ⟨j.1 + 1, by simp [j.2]⟩
          simpa [tTail, Vector.get, Vector.ofFn,
            Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm] using hOutJ
        have hIdxTail :
            ∀ j ∈ idxs, j < n := by
          intro j hj
          exact hIdx j (by simp [hj])
        have hEqTail :
            FinRelation.projTuple idxs u hIdxTail = tTail :=
          (ih hIdxTail hOutTail).1 hTail
        apply Vector.ext
        intro j hj
        cases j with
        | zero =>
            simpa [FinRelation.projTuple, Vector.get,
              Vector.ofFn] using hHeadEq.symm
        | succ j' =>
            have hj' : j' < idxs.length := by
              simpa using hj
            let jj : Fin idxs.length := ⟨j', hj'⟩
            have hTailCoord :=
              congrArg (fun v => v.get jj) hEqTail
            simpa [FinRelation.projTuple, Vector.get,
              Vector.ofFn,
              tTail, jj] using hTailCoord
      · intro hEq
        constructor
        · have hi : i < n := hIdx i (by simp)
          have hHead :
              t[0] = u.get ⟨i, hi⟩ := by
            have hCoord :=
              congrArg
                (fun v : Tuple D (i :: idxs).length =>
                  v.get ⟨0, by simp⟩) hEq
            simpa [FinRelation.projTuple, Vector.get,
              Vector.ofFn, hi] using hCoord.symm
          have hOut0 : σ start = t[0] := by
            simpa using hOut ⟨0, by simp⟩
          have hSrcI :
              σ (srcStart + i) = u.get ⟨i, hi⟩ := by
            simpa using hSrc ⟨i, hi⟩
          simpa [projLinksAt,
            Formula.ArbitraryAssignSatIn, RelTerm.eval,
            hOut0, hSrcI] using hHead
        · let tTail : Tuple D idxs.length :=
            Vector.ofFn
              (fun j =>
                t.get ⟨j.1 + 1, by simp [j.2]⟩)
          have hEqTail :
              FinRelation.projTuple idxs u
                (fun j hj => hIdx j (by simp [hj])) =
                  tTail := by
            apply Vector.ext
            intro j hj
            have hCoord :=
              congrArg
                (fun v : Tuple D (i :: idxs).length =>
                  v.get ⟨j + 1, by simpa using hj⟩) hEq
            simpa [FinRelation.projTuple, Vector.get,
              Vector.ofFn,
              tTail] using hCoord
          have hOutTail :
              ∀ j : Fin idxs.length,
                σ ((start + 1) + j) =
                  tTail.get j := by
            intro j
            have hOutJ :=
              hOut ⟨j.1 + 1, by simp [j.2]⟩
            simpa [tTail, Vector.get, Vector.ofFn,
              Nat.add_assoc, Nat.add_left_comm,
              Nat.add_comm] using hOutJ
          exact
            (ih
              (fun j hj => hIdx j (by simp [hj]))
              hOutTail).2 hEqTail

namespace BlockAssign

variable {D : Type}
variable [Domain D]

omit [Domain D] in
theorem withBlock_cons
    (σ : Assign D)
    (start : Nat)
    (d : D)
    {n : Nat}
    (t : Tuple D n) :
    withBlock σ start (Tuple.cons d t) =
      withBlock
        (Assign.update σ start d)
        (start + 1) t := by
  funext x
  by_cases hxEq : x = start
  · subst x
    have hLeft :
        withBlock σ start (Tuple.cons d t) start = d := by
      have h := withBlock_eq σ start
        (Tuple.cons d t) ⟨0, by omega⟩
      exact h.trans (Tuple.get_cons_zero d t)
    have hRight :
        withBlock
          (Assign.update σ start d)
          (start + 1) t start =
            Assign.update σ start d start := by
      simpa using
        withBlock_eq_of_lt
          (σ := Assign.update σ start d)
          (start := start + 1)
          (t := t)
          (x := start)
          (Nat.lt_succ_self start)
    rw [hLeft, hRight]
    simp [Assign.update]
  · by_cases hTail :
      start + 1 ≤ x ∧ x < start + 1 + n
    · have hFull :
          start ≤ x ∧ x < start + (1 + n) := by
        constructor
        · exact Nat.le_trans (Nat.le_succ start) hTail.1
        · simpa [Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm] using hTail.2
      have hFull' :
          start ≤ x ∧ x < start + (n + 1) := by
        constructor
        · exact hFull.1
        · simpa [Nat.add_assoc,
            Nat.add_left_comm,
            Nat.add_comm] using hFull.2
      let i : Fin n := ⟨x - (start + 1), by
        exact (Nat.sub_lt_iff_lt_add' hTail.1).2 hTail.2⟩
      have hLeft :
          withBlock σ start (Tuple.cons d t) x =
            t.get i := by
        let k : Fin (n + 1) := ⟨x - start, by
          exact
            (Nat.sub_lt_iff_lt_add' hFull'.1).2
              hFull'.2⟩
        have hxK : x = start + k := by
          dsimp [k]
          exact (Nat.add_sub_of_le hFull'.1).symm
        have hFill :
            withBlock σ start (Tuple.cons d t) x =
              (Tuple.cons d t).get k := by
          rw [hxK]
          exact withBlock_eq σ start (Tuple.cons d t) k
        have hCons :
            (Tuple.cons d t).get k = t.get i := by
          have hk : k = ⟨i.1 + 1, by omega⟩ := by
            apply Fin.ext
            dsimp [k, i]
            omega
          rw [hk]
          simpa [Nat.add_comm] using
            Tuple.get_cons_succ d t i
        exact hFill.trans hCons
      have hRight :
          withBlock
            (Assign.update σ start d)
            (start + 1) t x =
            t.get i := by
        have hxI : x = (start + 1) + i := by
          dsimp [i]
          exact (Nat.add_sub_of_le hTail.1).symm
        rw [hxI]
        exact withBlock_eq
          (Assign.update σ start d)
          (start + 1) t i
      rw [hLeft, hRight]
    · have hFullFalse :
          ¬ (start ≤ x ∧ x < start + (n + 1)) := by
        intro hFull'
        have hFull :
            start ≤ x ∧ x < start + (1 + n) := by
          constructor
          · exact hFull'.1
          · simpa [Nat.add_assoc, Nat.add_left_comm,
              Nat.add_comm] using hFull'.2
        have hxTail :
            start + 1 ≤ x ∧ x < start + 1 + n := by
          constructor
          · exact Nat.succ_le_of_lt
              (lt_of_le_of_ne hFull.1
                (Ne.symm hxEq))
          · simpa [Nat.add_assoc,
              Nat.add_left_comm,
              Nat.add_comm] using hFull.2
        exact hTail hxTail
      have hUpdate :
          Assign.update σ start d x = σ x := by
        simp [Assign.update, hxEq]
      simp [withBlock, hFullFalse, hTail, hUpdate]

end BlockAssign

theorem satIn_existsMany_block_iff
    {Q : Set D}
    {Γ : UnnamedSchema A}
    {I : Instance D Γ}
    {σ : Assign D}
    (start : Nat)
    {n : Nat}
    (φ : Formula D Γ) :
    Formula.ArbitraryAssignSatIn Q I σ
      (Formula.existsMany (Var.block start n) φ) ↔
      ∃ t : Tuple D n,
        Tuple.MapsInto t Q ∧
          Formula.ArbitraryAssignSatIn Q I
            (BlockAssign.withBlock σ start t) φ := by
  induction n generalizing start σ with
  | zero =>
      let t0 : Tuple D 0 :=
        Vector.ofFn (fun i => nomatch i)
      have hWith :
          BlockAssign.withBlock σ start t0 = σ := by
        funext x
        have hFalse :
            ¬ (start ≤ x ∧ x < start + 0) := by
          intro h
          exact Nat.not_lt_of_ge h.1 (by simpa using h.2)
        simp [BlockAssign.withBlock, t0]
      constructor
      · intro hSat
        refine ⟨t0, ?_, ?_⟩
        · intro i
          exact Fin.elim0 i
        · simpa [Var.block_zero, Formula.existsMany,
            hWith] using hSat
      · rintro ⟨t, hQ, hSat⟩
        have ht : t = t0 := by
          apply Vector.ext
          intro i hi
          exact (Nat.not_lt_zero _ hi).elim
        simpa [Var.block_zero, Formula.existsMany,
          ht, hWith] using hSat
  | succ n ih =>
      constructor
      · intro hSat
        rcases (by
          simpa [Var.block_succ, Formula.existsMany,
            Formula.ArbitraryAssignSatIn] using hSat) with
          ⟨d, hdQ, hTail⟩
        rcases (ih
          (σ := Assign.update σ start d)
          (start := start + 1)).1 hTail with
          ⟨u, hUQ, hSatBody⟩
        let t : Tuple D (n + 1) := Tuple.cons d u
        refine ⟨t, ?_, ?_⟩
        · intro i
          cases i using Fin.cases with
          | zero =>
              simpa [t] using
                (show Q ((Tuple.cons d u)[0]) from by
                  rw [Tuple.get_cons_zero]
                  exact hdQ)
          | succ j =>
              simpa [t] using
                (show Q ((Tuple.cons d u)[j.1 + 1]) from by
                  rw [Tuple.get_cons_succ]
                  exact hUQ j)
        · simpa [t] using
            (show Formula.ArbitraryAssignSatIn Q I
              (BlockAssign.withBlock σ start t) φ from by
                rw [BlockAssign.withBlock_cons]
                exact hSatBody)
      · rintro ⟨t, hQ, hSat⟩
        let d : D := t[0]
        let u : Tuple D n := Tuple.tail t
        have hUQ : Tuple.MapsInto u Q := by
          intro j
          simpa [u, Tuple.tail, Vector.get,
            Vector.ofFn] using
            hQ ⟨j.1 + 1, by omega⟩
        have hSatBody :
            Formula.ArbitraryAssignSatIn Q I
              (BlockAssign.withBlock
                (Assign.update σ start d)
                (start + 1) u) φ := by
          rw [← BlockAssign.withBlock_cons
            (σ := σ) (start := start) (d := d) (t := u)]
          simpa [d, u, Tuple.cons_tail] using hSat
        have hTail :
            Formula.ArbitraryAssignSatIn Q I
              (Assign.update σ start d)
              (Formula.existsMany
                (Var.block (start + 1) n) φ) :=
          (ih
            (σ := Assign.update σ start d)
            (start := start + 1)).2
            ⟨u, hUQ, hSatBody⟩
        have hdQ : Q d := by
          simpa [d] using hQ ⟨0, by omega⟩
        simpa [Var.block_succ, Formula.existsMany,
          Formula.ArbitraryAssignSatIn, d] using
          show ∃ d' ∈ Q,
              Formula.ArbitraryAssignSatIn Q I
                (Assign.update σ start d')
                (Formula.existsMany
                  (Var.block (start + 1) n) φ) from
            ⟨d, hdQ, hTail⟩

namespace BlockAssign

variable {D : Type}
variable [Domain D]

theorem onBlock_left_agree
    (start : Nat)
    {n m : Nat}
    (t : Tuple D (n + m)) :
    Assign.AgreeOn
      (onBlock start t)
      (onBlock start (Tuple.left t))
      ((Var.block start n).toFinset) := by
  intro x hx
  rw [Var.mem_toFinset_block_iff] at hx
  let i : Fin n := ⟨x - start, by omega⟩
  have hxEq : x = start + i := by
    dsimp [i]
    exact (Nat.add_sub_of_le hx.1).symm
  rw [hxEq]
  have hFull :
      onBlock start t (start + i) =
        t.get ⟨i.1, by omega⟩ := by
    simpa using onBlock_eq start t ⟨i.1, by omega⟩
  have hLeft :
      onBlock start (Tuple.left t) (start + i) =
        (Tuple.left t).get i := by
    simpa using onBlock_eq start (Tuple.left t) i
  rw [hFull, hLeft]
  simp [Tuple.left, Vector.get, Vector.ofFn]

theorem onBlock_right_agree
    (start : Nat)
    {n m : Nat}
    (t : Tuple D (n + m)) :
    Assign.AgreeOn
      (onBlock start t)
      (onBlock (start + n) (Tuple.right (n := n) t))
      ((Var.block (start + n) m).toFinset) := by
  intro x hx
  rw [Var.mem_toFinset_block_iff] at hx
  let i : Fin m := ⟨x - (start + n), by omega⟩
  have hxEq : x = start + n + i := by
    dsimp [i]
    exact (Nat.add_sub_of_le hx.1).symm
  rw [hxEq]
  have hFull :
      onBlock start t (start + n + i) =
        t.get ⟨n + i.1, by omega⟩ := by
    simpa [Nat.add_assoc] using
      onBlock_eq start t ⟨n + i.1, by omega⟩
  have hRight :
      onBlock (start + n) (Tuple.right (n := n) t)
          (start + n + i) =
        (Tuple.right (n := n) t).get i := by
    simpa [Nat.add_assoc] using
      onBlock_eq (start + n) (Tuple.right (n := n) t) i
  rw [hFull, hRight]
  simp [Tuple.right, Vector.get, Vector.ofFn]

end BlockAssign

theorem projIndices_subset_block
    (srcStart : Nat)
    {n : Nat}
    {idxs : List Nat}
    (hIdx : ∀ i ∈ idxs, i < n) :
    (idxs.map (fun i => srcStart + i)).toFinset ⊆
      (Var.block srcStart n).toFinset := by
  intro x hx
  rw [List.mem_toFinset] at hx
  rcases List.mem_map.mp hx with ⟨i, hi, rfl⟩
  rw [Var.mem_toFinset_block_iff]
  exact ⟨Nat.le_add_right srcStart i,
    Nat.add_lt_add_left (hIdx i hi) _⟩

theorem foldr_erase_list_union
    (xs : List Var)
    (S : Finset Var)
    (hNodup : xs.Nodup)
    (hDisj : Disjoint S xs.toFinset) :
    xs.foldr (fun x T => T.erase x)
        (S ∪ xs.toFinset) = S := by
  induction xs generalizing S with
  | nil =>
      simp
  | cons x xs ih =>
      rcases List.nodup_cons.mp hNodup with
        ⟨hxNotMem, hNodupTail⟩
      have hNotMemS : x ∉ S := by
        intro hxS
        exact (Finset.disjoint_left.mp hDisj) hxS (by simp)
      have hDisjTail : Disjoint S xs.toFinset := by
        refine Finset.disjoint_of_subset_right ?_ hDisj
        intro y hy
        simp [hy]
      have hDisjInsert :
          Disjoint (insert x S) xs.toFinset := by
        rw [Finset.disjoint_left]
        intro y hy hyXs
        rcases Finset.mem_insert.mp hy with rfl | hyS
        · exact hxNotMem (List.mem_toFinset.mp hyXs)
        · exact
            (Finset.disjoint_left.mp hDisjTail) hyS hyXs
      have hInsertUnion :
          insert x S ∪ xs.toFinset =
            insert x (S ∪ xs.toFinset) := by
        ext y
        simp
      calc
        (x :: xs).foldr (fun x T => T.erase x)
            (S ∪ (x :: xs).toFinset)
            = (List.foldr (fun x T => T.erase x)
                (insert x (S ∪ xs.toFinset)) xs).erase
              x := by
                  simp
        _ = ((insert x S).erase x : Finset Var) := by
              rw [← hInsertUnion,
                ih (insert x S) hNodupTail hDisjInsert]
        _ = S := by simp [hNotMemS]

theorem foldr_erase_source_block_union
    (start outAr srcAr : Nat) :
    (Var.block (start + outAr) srcAr).foldr
        (fun x S => S.erase x)
        ((Var.block start outAr).toFinset ∪
          (Var.block (start + outAr) srcAr).toFinset) =
      (Var.block start outAr).toFinset := by
  refine foldr_erase_list_union
    (xs := Var.block (start + outAr) srcAr)
    (S := (Var.block start outAr).toFinset)
    ?_ ?_
  · exact Var.nodup_block _ _
  · exact Var.disjoint_toFinset_block_add start outAr srcAr

end Builders

end ToRelCalc

end UnnamedRA

------------------------------------------------------------
-- Translation Construction
------------------------------------------------------------

namespace RawRAExpr

variable {A D : Type}
variable [RelationNames A] [Domain D]

open UnnamedRA.ToRelCalc

/-
  Target-driven RA-to-RelCalc translation. The requested
  output block starts at `start`. Projection allocates a
  fresh source block after the output block and links output
  coordinates back to source coordinates with equalities.
-/
def toRelCalcFormula?
    (Γ : UnnamedSchema A)
    (start : Nat) :
    RawRAExpr A D → Option (RelCalc.Formula D Γ)
| .top =>
    some
      (UnnamedRA.ToRelCalc.supportAt
        (Γ := Γ) start 0)
| .empty n =>
    some
      (UnnamedRA.ToRelCalc.emptyAt
        (Γ := Γ) start n)
| .rel X =>
    if hX : X ∈ Γ.syms then
      some
        (UnnamedRA.ToRelCalc.atomAt
          (D := D) ⟨X, hX⟩ start)
    else
      none
| .single d =>
    some
      (singleAt (D := D) (Γ := Γ) d start)
| .select φ e =>
    match e.arity? Γ, toRelCalcFormula? Γ start e with
    | some n, some ψ =>
        if φ.arityReq < n then
          some
            (.and ψ
              (UnnamedRA.ToRelCalc.selFormulaAt
                (Γ := Γ) start φ))
        else
          none
    | _, _ => none
| .proj idxs e =>
    match e.arity? Γ,
        toRelCalcFormula? Γ (start + idxs.length) e with
    | some n, some ψ =>
        if _h : ∀ i ∈ idxs, i < n then
          some <|
            RelCalc.Formula.existsMany
              (Var.block (start + idxs.length) n)
              (.and ψ
                (UnnamedRA.ToRelCalc.projLinksAt
                  (Γ := Γ)
                  start (start + idxs.length) idxs))
        else
          none
    | _, _ => none
| .prod e₁ e₂ =>
    match e₁.arity? Γ, e₂.arity? Γ,
        toRelCalcFormula? Γ start e₁ with
    | some n, some _m, some φ₁ =>
        match toRelCalcFormula? Γ (start + n) e₂ with
        | some φ₂ => some (.and φ₁ φ₂)
        | none => none
    | _, _, _ => none
| .union e₁ e₂ =>
    match e₁.arity? Γ, e₂.arity? Γ,
        toRelCalcFormula? Γ start e₁,
        toRelCalcFormula? Γ start e₂ with
    | some n, some m, some φ₁, some φ₂ =>
        if n = m then some (.or φ₁ φ₂) else none
    | _, _, _, _ => none
| .diff e₁ e₂ =>
    match e₁.arity? Γ, e₂.arity? Γ,
        toRelCalcFormula? Γ start e₁,
        toRelCalcFormula? Γ start e₂ with
    | some n, some m, some φ₁, some φ₂ =>
        if n = m then
          some (.and φ₁ (.not φ₂))
        else
          none
    | _, _, _, _ => none

/-
  The target-driven translator is total on expressions whose
  schema-relative arity computation succeeds.
-/
theorem toRelCalcFormula?_exists
    {Γ : UnnamedSchema A}
    (start : Nat) :
    ∀ {e : RawRAExpr A D} {n : Nat},
      e.arity? Γ = some n →
        ∃ φ, toRelCalcFormula? Γ start e = some φ := by
  intro e
  induction e generalizing start with
  | top =>
      intro n hAr
      refine ⟨
        UnnamedRA.ToRelCalc.supportAt
          (D := D) (Γ := Γ) start 0, ?_⟩
      simp [toRelCalcFormula?]
  | empty m =>
      intro n hAr
      refine ⟨
        UnnamedRA.ToRelCalc.emptyAt
          (D := D) (Γ := Γ) start m, ?_⟩
      simp [toRelCalcFormula?]
  | rel X =>
      intro n hAr
      have hR : Γ.arity? X = some n := by
        simpa [RawRAExpr.arity?] using hAr
      have hX : X ∈ Γ.syms := by
        by_cases hX : X ∈ Γ.syms
        · exact hX
        · simp [UnnamedSchema.arity?, hX] at hR
      refine ⟨
        UnnamedRA.ToRelCalc.atomAt
          (D := D) ⟨X, hX⟩ start, ?_⟩
      simp [toRelCalcFormula?, hX]
  | single d =>
      intro n hAr
      refine ⟨
        singleAt
          (D := D) (Γ := Γ) d start, ?_⟩
      simp [toRelCalcFormula?]
  | select φ e ih =>
      intro n hAr
      cases hE : e.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, hE] at hAr
      | some m =>
          by_cases hReq : φ.arityReq < m
          · obtain ⟨ψ, hψ⟩ := ih (start := start) hE
            refine ⟨RelCalc.Formula.and ψ
              (UnnamedRA.ToRelCalc.selFormulaAt
                (A := A) start φ), ?_⟩
            simp [toRelCalcFormula?, hE, hψ, hReq]
          · simp [RawRAExpr.arity?, hE, hReq] at hAr
  | proj idxs e ih =>
      intro n hAr
      cases hE : e.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, hE] at hAr
      | some m =>
          by_cases hIdx : ∀ i ∈ idxs, i < m
          · obtain ⟨ψ, hψ⟩ :=
              ih (start := start + idxs.length) hE
            refine ⟨RelCalc.Formula.existsMany
              (Var.block (start + idxs.length) m)
              (RelCalc.Formula.and ψ
                (UnnamedRA.ToRelCalc.projLinksAt
                  (A := A) (D := D)
                  start (start + idxs.length) idxs)), ?_⟩
            simp only [toRelCalcFormula?, hE, hψ,
              dif_pos hIdx]
          · simp [RawRAExpr.arity?, hE, hIdx] at hAr
  | prod e₁ e₂ ih₁ ih₂ =>
      intro n hAr
      cases h₁ : e₁.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, h₁] at hAr
      | some n₁ =>
          cases h₂ : e₂.arity? Γ with
          | none =>
              simp [RawRAExpr.arity?, h₁, h₂] at hAr
          | some n₂ =>
              obtain ⟨φ₁, hφ₁⟩ :=
                ih₁ (start := start) h₁
              obtain ⟨φ₂, hφ₂⟩ :=
                ih₂ (start := start + n₁) h₂
              refine ⟨
                RelCalc.Formula.and φ₁ φ₂, ?_⟩
              simp [toRelCalcFormula?, h₁, h₂,
                hφ₁, hφ₂]
  | union e₁ e₂ ih₁ ih₂ =>
      intro n hAr
      cases h₁ : e₁.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, h₁] at hAr
      | some n₁ =>
          cases h₂ : e₂.arity? Γ with
          | none =>
              simp [RawRAExpr.arity?, h₁, h₂] at hAr
          | some n₂ =>
              by_cases hEq : n₁ = n₂
              · obtain ⟨φ₁, hφ₁⟩ :=
                  ih₁ (start := start) h₁
                obtain ⟨φ₂, hφ₂⟩ :=
                  ih₂ (start := start) h₂
                refine ⟨
                  RelCalc.Formula.or φ₁ φ₂, ?_⟩
                simp [toRelCalcFormula?, h₁, h₂,
                  hφ₁, hφ₂, hEq]
              · simp [RawRAExpr.arity?, h₁, h₂, hEq]
                  at hAr
  | diff e₁ e₂ ih₁ ih₂ =>
      intro n hAr
      cases h₁ : e₁.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, h₁] at hAr
      | some n₁ =>
          cases h₂ : e₂.arity? Γ with
          | none =>
              simp [RawRAExpr.arity?, h₁, h₂] at hAr
          | some n₂ =>
              by_cases hEq : n₁ = n₂
              · obtain ⟨φ₁, hφ₁⟩ :=
                  ih₁ (start := start) h₁
                obtain ⟨φ₂, hφ₂⟩ :=
                  ih₂ (start := start) h₂
                refine ⟨
                  RelCalc.Formula.and φ₁
                    (RelCalc.Formula.not φ₂), ?_⟩
                simp [toRelCalcFormula?, h₁, h₂,
                  hφ₁, hφ₂, hEq]
              · simp [RawRAExpr.arity?, h₁, h₂, hEq]
                  at hAr

end RawRAExpr

namespace RawRAExpr

variable {A D : Type}
variable [RelationNames A] [Domain D]

open RelCalc
open UnnamedRA.ToRelCalc

/- Metadata produced by a successful translation. -/
theorem toRelCalcFormula?_metadata
    {Γ : UnnamedSchema A}
    (start : Nat) :
    ∀ {e : RawRAExpr A D} {n : Nat}
      {φ : Formula D Γ},
      e.arity? Γ = some n →
      toRelCalcFormula? Γ start e = some φ →
        φ.freeVars =
          (Var.block start n).toFinset ∧
        φ.constants = e.constants := by
  intro e
  induction e generalizing start with
  | top =>
      intro n φ hAr hφ
      have hn : n = 0 := by
        simpa [arity?] using hAr.symm
      subst hn
      have hφEq :
          φ =
            supportAt
              (D := D) (Γ := Γ) start 0 :=
        (Option.some.inj hφ).symm
      subst φ
      simp [freeVars_supportAt,
        constants_supportAt,
        constants]
  | empty m =>
      intro n φ hAr hφ
      have hn : n = m := by
        simpa [arity?] using hAr.symm
      subst hn
      have hφEq :
          φ =
            emptyAt
              (D := D) (Γ := Γ) start n :=
        (Option.some.inj hφ).symm
      subst φ
      simp [freeVars_emptyAt,
        constants_emptyAt,
        constants]
  | rel X =>
      intro n φ hAr hφ
      have hR : Γ.arity? X = some n := by
        simpa [arity?] using hAr
      have hX : X ∈ Γ.syms := by
        by_cases hX : X ∈ Γ.syms
        · exact hX
        · simp [UnnamedSchema.arity?, hX] at hR
      have hArEq : Γ.arity ⟨X, hX⟩ = n := by
        simpa [UnnamedSchema.arity?, hX] using hR
      simp [toRelCalcFormula?, hX] at hφ
      have hφEq :
          φ =
            atomAt
              (D := D) ⟨X, hX⟩ start :=
        hφ.symm
      subst φ
      simp [freeVars_atomAt, hArEq,
        constants_atomAt,
        constants]
  | single d =>
      intro n φ hAr hφ
      have hn : n = 1 := by
        simpa [arity?] using hAr.symm
      subst hn
      have hφEq :
          φ =
            singleAt
              (D := D) (Γ := Γ) d start :=
        (Option.some.inj hφ).symm
      subst φ
      simp [freeVars_singleAt,
        constants_singleAt,
        constants]
  | select s e ih =>
      intro n φ hAr hφ
      cases hE : e.arity? Γ with
      | none =>
          simp [arity?, hE] at hAr
      | some m =>
          by_cases hReq : s.arityReq < m
          · have hn : m = n := by
              simpa [arity?, hE, hReq] using hAr
            subst hn
            obtain ⟨ψ, hψ⟩ :=
              toRelCalcFormula?_exists
                (A := A) (D := D) (Γ := Γ) start hE
            simp only [toRelCalcFormula?, hE, hψ,
              if_pos hReq] at hφ
            have hφEq :
                φ =
                  Formula.and ψ
                    (selFormulaAt
                      (D := D) (Γ := Γ) start s) :=
              (Option.some.inj hφ).symm
            subst φ
            rcases ih (start := start) hE hψ with
              ⟨hFV, hConst⟩
            constructor
            · rw [Formula.freeVars, hFV]
              apply Finset.union_eq_left.mpr
              exact
                freeVars_selFormulaAt_subset
                  (D := D) (Γ := Γ)
                  (start := start) (n := m) s hReq
            · simp [Formula.constants, hConst,
                constants_selFormulaAt,
                constants,
                Finset.union_comm]
          · simp [arity?, hE, hReq] at hAr
  | proj idxs e ih =>
      intro outAr φ hAr hφ
      cases hE : e.arity? Γ with
      | none =>
          simp [arity?, hE] at hAr
      | some srcAr =>
          by_cases hIdx : ∀ i ∈ idxs, i < srcAr
          · have hout : idxs.length = outAr := by
              have hPair :
                  (∀ i ∈ idxs, i < srcAr) ∧
                    idxs.length = outAr := by
                simpa [arity?, hE, hIdx] using hAr
              exact hPair.2
            subst hout
            let srcStart := start + idxs.length
            obtain ⟨ψ, hψ⟩ :=
              toRelCalcFormula?_exists (A := A) (D := D)
                (Γ := Γ) srcStart hE
            let target : Formula D Γ :=
              Formula.existsMany
                (Var.block srcStart srcAr)
                (Formula.and ψ
                  (projLinksAt
                    (D := D) (Γ := Γ)
                    start srcStart idxs))
            have hφPair :
                (∀ i ∈ idxs, i < srcAr) ∧
                  target = φ := by
              simpa [
                target, srcStart, toRelCalcFormula?,
                hE, hψ] using hφ
            have hEqφ : φ = target := hφPair.2.symm
            subst φ
            rcases ih (start := srcStart) hE hψ with
              ⟨hFV, hConst⟩
            constructor
            · rw [Formula.freeVars_existsMany]
              have hBody :
                  (Formula.and ψ
                    (projLinksAt
                      (D := D) (Γ := Γ)
                      start srcStart idxs)).freeVars =
                    (Var.block
                      start idxs.length).toFinset ∪
                      (Var.block
                        srcStart srcAr).toFinset := by
                rw [Formula.freeVars, hFV,
                  freeVars_projLinksAt]
                apply Finset.ext
                intro x
                constructor <;> intro hx
                · rcases Finset.mem_union.mp hx with
                  hx | hx
                  · exact Finset.mem_union.mpr (Or.inr hx)
                  · rcases Finset.mem_union.mp hx with
                    hx | hx
                    · exact
                        Finset.mem_union.mpr (Or.inl hx)
                    · exact Finset.mem_union.mpr
                        (Or.inr <|
                          projIndices_subset_block
                            (srcStart :=
                              start + idxs.length)
                            (hIdx := hIdx) hx)
                · rcases Finset.mem_union.mp hx with
                  hx | hx
                  · exact Finset.mem_union.mpr
                      (Or.inr <| Finset.mem_union.mpr
                        (Or.inl hx))
                  · exact Finset.mem_union.mpr (Or.inl hx)
              rw [hBody]
              exact
                foldr_erase_source_block_union
                start idxs.length srcAr
            · dsimp [target]
              simp [Formula.constants_existsMany,
                Formula.constants, hConst,
                constants_projLinksAt,
                constants]
          · simp [arity?, hE, hIdx] at hAr
  | prod e₁ e₂ ih₁ ih₂ =>
      intro n φ hAr hφ
      cases h₁ : e₁.arity? Γ with
      | none =>
          simp [arity?, h₁] at hAr
      | some n₁ =>
          cases h₂ : e₂.arity? Γ with
          | none =>
              simp [arity?, h₁, h₂] at hAr
          | some n₂ =>
              have hsum : n₁ + n₂ = n := by
                simpa [arity?, h₁, h₂] using hAr
              subst hsum
              obtain ⟨φ₁, hφ₁⟩ :=
                toRelCalcFormula?_exists
                  (A := A) (D := D) (Γ := Γ) start h₁
              obtain ⟨φ₂, hφ₂⟩ :=
                toRelCalcFormula?_exists
                  (A := A) (D := D) (Γ := Γ)
                  (start + n₁) h₂
              simp only [toRelCalcFormula?, h₁, h₂,
                hφ₁, hφ₂] at hφ
              have hφEq :
                  φ = Formula.and φ₁ φ₂ :=
                (Option.some.inj hφ).symm
              subst φ
              rcases ih₁ (start := start) h₁ hφ₁ with
                ⟨hFV₁, hC₁⟩
              rcases ih₂
                  (start := start + n₁) h₂ hφ₂ with
                ⟨hFV₂, hC₂⟩
              constructor
              · simp [
                  Formula.freeVars, hFV₁, hFV₂,
                  Var.toFinset_block_add]
              · simp [Formula.constants, hC₁, hC₂,
                  constants]
  | union e₁ e₂ ih₁ ih₂ =>
      intro n φ hAr hφ
      cases h₁ : e₁.arity? Γ with
      | none =>
          simp [arity?, h₁] at hAr
      | some n₁ =>
          cases h₂ : e₂.arity? Γ with
          | none =>
              simp [arity?, h₁, h₂] at hAr
          | some n₂ =>
              by_cases hEq : n₁ = n₂
              · have hn : n₁ = n := by
                  simpa [arity?, h₁, h₂, hEq]
                    using hAr
                subst hn
                subst hEq
                obtain ⟨φ₁, hφ₁⟩ :=
                  toRelCalcFormula?_exists
                    (A := A) (D := D) (Γ := Γ) start h₁
                obtain ⟨φ₂, hφ₂⟩ :=
                  toRelCalcFormula?_exists
                    (A := A) (D := D) (Γ := Γ) start h₂
                simp only [toRelCalcFormula?, h₁, h₂,
                  hφ₁, hφ₂] at hφ
                have hφEq :
                    φ = Formula.or φ₁ φ₂ :=
                  (Option.some.inj hφ).symm
                subst φ
                rcases ih₁
                    (start := start) h₁ hφ₁ with
                  ⟨hFV₁, hC₁⟩
                rcases ih₂
                    (start := start) h₂ hφ₂ with
                  ⟨hFV₂, hC₂⟩
                constructor
                · simp [
                    Formula.freeVars, hFV₁, hFV₂]
                · simp [Formula.constants, hC₁, hC₂,
                    constants]
              · simp [
                  arity?, h₁, h₂, hEq] at hAr
  | diff e₁ e₂ ih₁ ih₂ =>
      intro n φ hAr hφ
      cases h₁ : e₁.arity? Γ with
      | none =>
          simp [arity?, h₁] at hAr
      | some n₁ =>
          cases h₂ : e₂.arity? Γ with
          | none =>
              simp [arity?, h₁, h₂] at hAr
          | some n₂ =>
              by_cases hEq : n₁ = n₂
              · have hn : n₁ = n := by
                  simpa [arity?, h₁, h₂, hEq]
                    using hAr
                subst hn
                subst hEq
                obtain ⟨φ₁, hφ₁⟩ :=
                  toRelCalcFormula?_exists
                    (A := A) (D := D) (Γ := Γ) start h₁
                obtain ⟨φ₂, hφ₂⟩ :=
                  toRelCalcFormula?_exists
                    (A := A) (D := D) (Γ := Γ) start h₂
                simp only [toRelCalcFormula?, h₁, h₂,
                  hφ₁, hφ₂] at hφ
                have hφEq :
                    φ =
                      Formula.and φ₁
                        (Formula.not φ₂) :=
                  (Option.some.inj hφ).symm
                subst φ
                rcases ih₁
                    (start := start) h₁ hφ₁ with
                  ⟨hFV₁, hC₁⟩
                rcases ih₂
                    (start := start) h₂ hφ₂ with
                  ⟨hFV₂, hC₂⟩
                constructor
                · simp [
                    Formula.freeVars, hFV₁, hFV₂]
                · simp [Formula.constants, hC₁, hC₂,
                    constants]
              · simp [
                  arity?, h₁, h₂, hEq] at hAr

theorem toRelCalcFormula?_freeVars
    {Γ : UnnamedSchema A}
    {start n : Nat}
    {e : RawRAExpr A D}
    {φ : Formula D Γ}
    (hAr : e.arity? Γ = some n)
    (hφ : toRelCalcFormula? Γ start e = some φ) :
    φ.freeVars = (Var.block start n).toFinset :=
  (toRelCalcFormula?_metadata (A := A) (D := D)
    (Γ := Γ) start hAr hφ).1

theorem toRelCalcFormula?_constants
    {Γ : UnnamedSchema A}
    {start n : Nat}
    {e : RawRAExpr A D}
    {φ : Formula D Γ}
    (hAr : e.arity? Γ = some n)
    (hφ : toRelCalcFormula? Γ start e = some φ) :
    φ.constants = e.constants :=
  (toRelCalcFormula?_metadata (A := A) (D := D)
    (Γ := Γ) start hAr hφ).2

end RawRAExpr

------------------------------------------------------------
-- Translation Satisfaction Equivalences
------------------------------------------------------------

namespace RawRAExpr

variable {A D : Type}
variable [RelationNames A] [Domain D]

open RelCalc
open UnnamedRA.ToRelCalc
open RelCalc.Formula
open FinRelation
open Finset

/-
  Equivalence for the recursive RelCalc truth predicate.
  The public `SatIn` free-variable side condition is added
  by `toRelCalcFormula?_answerContains_iff_satIn`.
-/
theorem toRelCalcFormula?_answerContains_iff_arbitraryAssignSatIn
    {Γ : UnnamedSchema A}
    {start n : Nat}
    {e : RawRAExpr A D}
    {φ : Formula D Γ}
    (hAr : e.arity? Γ = some n)
    (hφ : toRelCalcFormula? Γ start e = some φ)
    (Q : Set D)
    (I : Instance D Γ)
    (t : Tuple D n)
    (hContain :
      (↑(I.Adom ∪ e.constants) : Set D) ⊆ Q)
    (hQ : Tuple.MapsInto t Q) :
    e.answerContains I t ↔
      Formula.ArbitraryAssignSatIn Q I
        (BlockAssign.onBlock start t) φ := by
  induction e generalizing start n φ t with
  | top =>
        have hn : n = 0 := by
          simpa [arity?] using hAr.symm
        subst hn
        have hφEq :
            φ =
              supportAt
                (A := A) (D := D) start 0 :=
          (Option.some.inj hφ).symm
        subst φ
        exact
          (answer_top_iff (Γ := Γ) (I := I) t).trans
            (by
              simp [supportAt,
                Formula.ArbitraryAssignSatIn])
  | empty m =>
      have hn : n = m := by
        simpa [arity?] using hAr.symm
      subst hn
      have hφEq :
          φ =
            emptyAt
              (A := A) (D := D) start n :=
        (Option.some.inj hφ).symm
      subst φ
      constructor
      · intro hAns
        exact False.elim
          ((answer_empty_iff (Γ := Γ) (I := I) t).1 hAns)
      · intro hSat
        exact False.elim
          (not_satIn_emptyAt
            (A := A) (D := D)
            (Q := Q) (Γ := Γ) (I := I)
            (σ := BlockAssign.onBlock start t)
            (start := start) (count := n) hSat)
    | rel X =>
        have hR : Γ.arity? X = some n := by
          simpa [arity?] using hAr
        have hX : X ∈ Γ.syms := by
          by_cases hX : X ∈ Γ.syms
          · exact hX
          · have hNone := hφ
            simp [toRelCalcFormula?, hX] at hNone
        have hArEq : Γ.arity ⟨X, hX⟩ = n := by
          have hSome :
              some (Γ.arity ⟨X, hX⟩) = some n := by
            simpa [UnnamedSchema.arity?, hX] using hR
          exact Option.some.inj hSome
        cases hArEq
        have hφSome :
            some (atomAt (D := D) ⟨X, hX⟩ start) =
              some φ := by
          simpa [toRelCalcFormula?, hX] using hφ
        have hφEq :
            φ =
              atomAt (D := D) ⟨X, hX⟩ start :=
          (Option.some.inj hφSome).symm
        subst φ
        have hRel :
            (∃ hX' : X ∈ Γ.syms,
                ∃ hEq :
                  Γ.arity ⟨X, hX'⟩ =
                    Γ.arity ⟨X, hX⟩,
                  Tuple.castArity hEq t ∈
                    I ⟨X, hX'⟩) ↔
              t ∈ I ⟨X, hX⟩ := by
          constructor
          · rintro ⟨hX', hEq, ht⟩
            have hSub :
                (⟨X, hX'⟩ : Γ.syms) = ⟨X, hX⟩ := by
              apply Subtype.ext
              rfl
            cases hSub
            cases hEq
            simpa using ht
          · intro ht
            exact ⟨hX, rfl, ht⟩
        exact
          (answer_rel_iff (Γ := Γ) (I := I) hR t).trans
            (hRel.trans
              (satIn_atomAt_iff
                (A := A) (D := D)
                (Q := Q) (Γ := Γ) (I := I)
                (σ := BlockAssign.onBlock start t)
                (X := ⟨X, hX⟩) (start := start)
                (fun i =>
                  BlockAssign.onBlock_eq start t i)).symm)
  | single d =>
      have hn : n = 1 := by
        simpa [arity?] using hAr.symm
      subst hn
      have hφEq :
          φ =
            singleAt
              (A := A) d start :=
        (Option.some.inj hφ).symm
      subst φ
      exact
        (answer_single_iff
          (Γ := Γ) (I := I) (d := d) t).trans
          (satIn_singleAt_iff
            (A := A) (D := D) (Q := Q)
            (Γ := Γ) (I := I)
            (σ := BlockAssign.onBlock start t)
            (d := d) (start := start) (t := t)
            (by
              simpa using
                (BlockAssign.onBlock_eq
                  start t ⟨0, by omega⟩))).symm
  | select s e ih =>
      cases hE : e.arity? Γ with
      | none =>
          simp [arity?, hE] at hAr
      | some m =>
          cases hψ : toRelCalcFormula? Γ start e with
          | none =>
              simp [toRelCalcFormula?, hE, hψ] at hφ
          | some ψ =>
              by_cases hReq : s.arityReq < m
              · have hm : m = n := by
                  simpa [arity?, hE, hReq] using hAr
                subst hm
                simp only [toRelCalcFormula?, hE, hψ,
                  if_pos hReq] at hφ
                have hφEq :
                    φ =
                      .and ψ
                        (selFormulaAt
                          (A := A) start s) :=
                  (Option.some.inj hφ).symm
                subst φ
                have hContainE :
                    Set.Subset
                      (fun d =>
                        d ∈ I.Adom ∪ e.constants)
                      Q := by
                  intro d hd
                  apply hContain
                  change d ∈ I.Adom ∪
                    (s.constants ∪ e.constants)
                  change d ∈ I.Adom ∪
                    e.constants at hd
                  rcases mem_union.mp hd with hAd | hC
                  · exact mem_union.mpr (Or.inl hAd)
                  · exact mem_union.mpr
                      (Or.inr (mem_union.mpr (Or.inr hC)))
                have hIH :=
                  ih (start := start) (n := m) (φ := ψ)
                    hE hψ t hContainE hQ
                have hSel :
                    Formula.ArbitraryAssignSatIn Q I
                      (BlockAssign.onBlock start t)
                      (selFormulaAt
                        (A := A) start s) ↔
                    Sel.Holds s t :=
                  satIn_selFormulaAt_iff
                    (A := A) (D := D) (Q := Q)
                    (Γ := Γ) (I := I)
                    (σ := BlockAssign.onBlock start t)
                    (start := start) (t := t)
                    (fun i =>
                      BlockAssign.onBlock_eq start t i)
                    s hReq
                calc
                  (RawRAExpr.select s e).answerContains I t
                      ↔
                        e.answerContains I t ∧
                          Sel.Holds s t :=
                        answer_select_iff hE hReq t
                  _ ↔ Formula.ArbitraryAssignSatIn Q I
                          (BlockAssign.onBlock
                            start t) ψ ∧
                        Formula.ArbitraryAssignSatIn Q I
                          (BlockAssign.onBlock start t)
                          (selFormulaAt
                            (A := A) start s) := by
                        exact and_congr hIH hSel.symm
                    _ ↔ Formula.ArbitraryAssignSatIn Q I
                            (BlockAssign.onBlock start t)
                            (.and ψ
                              (selFormulaAt
                                (A := A) start s)) := by
                          rfl
              · simp [arity?, hE, hReq] at hAr
  | proj idxs e ih =>
      cases hE : e.arity? Γ with
      | none =>
          simp [arity?, hE] at hAr
      | some srcAr =>
          cases hψ :
              toRelCalcFormula? Γ
                (start + idxs.length) e with
          | none =>
              simp [toRelCalcFormula?, hE, hψ] at hφ
          | some ψ =>
              by_cases hIdx : ∀ i ∈ idxs, i < srcAr
              · have hn : idxs.length = n := by
                  have hPair :
                      (∀ i ∈ idxs, i < srcAr) ∧
                        idxs.length = n := by
                    simpa [arity?, hE, hIdx] using hAr
                  exact hPair.2
                subst hn
                let srcStart := start + idxs.length
                let body : Formula D Γ :=
                  .and ψ
                    (projLinksAt
                      (A := A) (D := D) start srcStart idxs)
                have hφPair :
                    (∀ i ∈ idxs, i < srcAr) ∧
                      Formula.existsMany
                        (Var.block srcStart srcAr)
                        body = φ := by
                  simpa [toRelCalcFormula?, hE, hψ,
                    srcStart, body] using hφ
                have hφEq :
                    φ =
                      Formula.existsMany
                        (Var.block srcStart srcAr) body :=
                  hφPair.2.symm
                subst φ
                have hContainE :
                    Set.Subset
                      (fun d =>
                        d ∈ I.Adom ∪ e.constants)
                      Q := by
                  intro d hd
                  exact hContain (by
                    simpa [constants] using hd)
                have hFVψ :
                    ψ.freeVars =
                      (Var.block srcStart srcAr).toFinset :=
                  toRelCalcFormula?_freeVars
                    (A := A) (D := D) (Γ := Γ)
                    (start := srcStart) hE hψ
                have hExists :
                    Formula.ArbitraryAssignSatIn Q I
                      (BlockAssign.onBlock start t)
                      (Formula.existsMany
                        (Var.block srcStart srcAr) body) ↔
                    ∃ u : Tuple D srcAr,
                      Tuple.MapsInto u Q ∧
                        Formula.ArbitraryAssignSatIn Q I
                          (BlockAssign.withBlock
                            (BlockAssign.onBlock start t)
                            srcStart u) body :=
                  satIn_existsMany_block_iff
                    (A := A) (D := D)
                    (Q := Q) (Γ := Γ) (I := I)
                    (σ := BlockAssign.onBlock start t)
                    srcStart body
                constructor
                · intro hAns
                  rcases
                    (answer_proj_iff hE hIdx t).1 hAns
                  with
                    ⟨s, hAnsS, hProj⟩
                  have hSQ : Tuple.MapsInto s Q := by
                    have hOver :
                        s.isTupleOver
                          (I.Adom ∪ e.constants) :=
                      answer_over_adom (A := A) (D := D)
                        (Γ := Γ) I hE hAnsS
                    intro i
                    exact hContainE (by
                      change
                        s.get i ∈ I.Adom ∪ e.constants
                      exact hOver i)
                  have hSatOn :
                      Formula.ArbitraryAssignSatIn Q I
                        (BlockAssign.onBlock srcStart s) ψ :=
                    (ih (start := srcStart)
                      (n := srcAr) (φ := ψ)
                      hE hψ s hContainE hSQ).1 hAnsS
                  have hAgree :
                      Assign.AgreeOn
                        (BlockAssign.withBlock
                          (BlockAssign.onBlock start t)
                          srcStart s)
                        (BlockAssign.onBlock srcStart s)
                        ψ.freeVars := by
                    rw [hFVψ]
                    exact BlockAssign.withBlock_agreeOn_onBlock
                      (BlockAssign.onBlock start t) srcStart s
                  have hSatWith :
                      Formula.ArbitraryAssignSatIn Q I
                        (BlockAssign.withBlock
                          (BlockAssign.onBlock start t)
                          srcStart s) ψ :=
                    (holdsIn_eq_of_agreeOn_freeVars
                      (Q := Q) (Γ := Γ) (I := I)
                      (φ := ψ) hAgree).2 hSatOn
                  have hOut :
                      ∀ j : Fin idxs.length,
                        BlockAssign.withBlock
                            (BlockAssign.onBlock start t)
                            srcStart s (start + j) =
                          t.get j := by
                    intro j
                    have hLt : start + j.1 < srcStart := by
                      dsimp [srcStart]
                      omega
                    have hBase :
                        BlockAssign.withBlock
                            (BlockAssign.onBlock start t)
                            srcStart s (start + j) =
                          (BlockAssign.onBlock start t)
                            (start + j) := by
                      exact BlockAssign.withBlock_eq_of_lt
                        (σ := BlockAssign.onBlock start t)
                        (start := srcStart) (t := s)
                        (x := start + j) hLt
                    rw [hBase]
                    exact BlockAssign.onBlock_eq start t j
                  have hSrc :
                      ∀ i : Fin srcAr,
                        BlockAssign.withBlock
                            (BlockAssign.onBlock start t)
                            srcStart s (srcStart + i) =
                          s.get i := by
                    intro i
                    exact BlockAssign.withBlock_eq
                      (BlockAssign.onBlock start t) srcStart s i
                  have hLinks :
                      Formula.ArbitraryAssignSatIn Q I
                        (BlockAssign.withBlock
                          (BlockAssign.onBlock start t)
                          srcStart s)
                        (projLinksAt
                          (A := A) (D := D)
                          start srcStart idxs) :=
                    (satIn_projLinksAt_iff
                      (A := A) (D := D)
                      (Q := Q) (Γ := Γ) (I := I)
                      (σ := BlockAssign.withBlock
                        (BlockAssign.onBlock start t)
                        srcStart s)
                      (hIdx := hIdx)
                      (hOut := hOut) (hSrc := hSrc)).2
                      hProj
                  exact
                    hExists.2 ⟨s, hSQ, hSatWith, hLinks⟩
                · intro hSat
                  rcases hExists.1 hSat with
                    ⟨s, hSQ, hBody⟩
                  rcases hBody with ⟨hSatWith, hLinks⟩
                  have hAgree :
                      Assign.AgreeOn
                        (BlockAssign.withBlock
                          (BlockAssign.onBlock start t)
                          srcStart s)
                        (BlockAssign.onBlock srcStart s)
                        ψ.freeVars := by
                    rw [hFVψ]
                    exact BlockAssign.withBlock_agreeOn_onBlock
                      (BlockAssign.onBlock start t) srcStart s
                  have hSatOn :
                      Formula.ArbitraryAssignSatIn Q I
                        (BlockAssign.onBlock srcStart s) ψ :=
                    (holdsIn_eq_of_agreeOn_freeVars
                      (Q := Q) (Γ := Γ) (I := I)
                      (φ := ψ) hAgree).1 hSatWith
                  have hAnsS :
                      e.answerContains I s :=
                    (ih (start := srcStart)
                      (n := srcAr) (φ := ψ)
                      hE hψ s hContainE hSQ).2 hSatOn
                  have hOut :
                      ∀ j : Fin idxs.length,
                        BlockAssign.withBlock
                            (BlockAssign.onBlock start t)
                            srcStart s (start + j) =
                          t.get j := by
                    intro j
                    have hLt : start + j.1 < srcStart := by
                      dsimp [srcStart]
                      omega
                    have hBase :
                        BlockAssign.withBlock
                            (BlockAssign.onBlock start t)
                            srcStart s (start + j) =
                          (BlockAssign.onBlock start t)
                            (start + j) := by
                      exact BlockAssign.withBlock_eq_of_lt
                        (σ := BlockAssign.onBlock start t)
                        (start := srcStart) (t := s)
                        (x := start + j) hLt
                    rw [hBase]
                    exact BlockAssign.onBlock_eq start t j
                  have hSrc :
                      ∀ i : Fin srcAr,
                        BlockAssign.withBlock
                            (BlockAssign.onBlock start t)
                            srcStart s (srcStart + i) =
                          s.get i := by
                    intro i
                    exact BlockAssign.withBlock_eq
                      (BlockAssign.onBlock start t) srcStart s i
                  have hProj :
                      projTuple idxs s hIdx = t :=
                    (satIn_projLinksAt_iff
                      (A := A) (D := D)
                      (Q := Q) (Γ := Γ) (I := I)
                      (σ := BlockAssign.withBlock
                        (BlockAssign.onBlock start t)
                        srcStart s)
                      (hIdx := hIdx)
                      (hOut := hOut) (hSrc := hSrc)).1
                      hLinks
                  exact (answer_proj_iff hE hIdx t).2
                    ⟨s, hAnsS, hProj⟩
              · simp [arity?, hE, hIdx] at hAr
  | prod e₁ e₂ ih₁ ih₂ =>
      cases h₁ : e₁.arity? Γ with
      | none =>
          simp [arity?, h₁] at hAr
      | some n₁ =>
          cases h₂ : e₂.arity? Γ with
          | none =>
              simp [arity?, h₁, h₂] at hAr
          | some n₂ =>
              cases hφ₁ :
                  toRelCalcFormula? Γ start e₁ with
              | none =>
                  simp [toRelCalcFormula?, h₁, h₂,
                    hφ₁] at hφ
              | some φ₁ =>
                  cases hφ₂ :
                      toRelCalcFormula? Γ
                        (start + n₁) e₂ with
                  | none =>
                      simp [toRelCalcFormula?, h₁, h₂,
                        hφ₁, hφ₂] at hφ
                  | some φ₂ =>
                      have hn : n₁ + n₂ = n := by
                        simpa [arity?, h₁, h₂] using hAr
                      subst hn
                      simp only [toRelCalcFormula?,
                        h₁, h₂, hφ₁, hφ₂] at hφ
                      have hφEq :
                          φ = .and φ₁ φ₂ :=
                        (Option.some.inj hφ).symm
                      subst φ
                      have hContain₁ :
                          Set.Subset
                            (fun d =>
                              d ∈
                                I.Adom ∪ e₁.constants)
                            Q := by
                        intro d hd
                        apply hContain
                        change d ∈ I.Adom ∪
                          (e₁.constants ∪
                            e₂.constants)
                        change
                          d ∈
                            I.Adom ∪ e₁.constants at hd
                        rcases mem_union.mp hd with hAd | hC
                        · exact mem_union.mpr (Or.inl hAd)
                        · exact mem_union.mpr
                            (Or.inr
                              (mem_union.mpr (Or.inl hC)))
                      have hContain₂ :
                          Set.Subset
                            (fun d =>
                              d ∈
                                I.Adom ∪ e₂.constants)
                            Q := by
                        intro d hd
                        apply hContain
                        change d ∈ I.Adom ∪
                          (e₁.constants ∪
                            e₂.constants)
                        change
                          d ∈
                            I.Adom ∪ e₂.constants at hd
                        rcases mem_union.mp hd with hAd | hC
                        · exact mem_union.mpr (Or.inl hAd)
                        · exact mem_union.mpr
                            (Or.inr
                              (mem_union.mpr (Or.inr hC)))
                      have hFV₁ :
                          φ₁.freeVars =
                            (Var.block start
                              n₁).toFinset :=
                        toRelCalcFormula?_freeVars
                          (A := A) (D := D) (Γ := Γ)
                          (start := start) h₁ hφ₁
                      let block₂ :=
                        Var.block (start + n₁) n₂
                      have hFV₂ :
                          φ₂.freeVars =
                            block₂.toFinset := by
                        dsimp [block₂]
                        exact
                          toRelCalcFormula?_freeVars
                            (A := A) (D := D) (Γ := Γ)
                            (start := start + n₁)
                            h₂ hφ₂
                      constructor
                      · intro hAns
                        have hProd :=
                          (answer_prod_iff h₁ h₂ t).1
                            hAns
                        rcases hProd
                        with
                          ⟨t₁, hAns₁, t₂,
                            hAns₂, hApp⟩
                        have hQ₁ :
                            Tuple.MapsInto t₁ Q := by
                          have hOver :
                              t₁.isTupleOver
                                (I.Adom ∪
                                  e₁.constants) :=
                            answer_over_adom
                              (A := A) (D := D)
                              (Γ := Γ) I h₁ hAns₁
                          intro i
                          exact hContain₁ (by
                            change
                              t₁.get i ∈
                                I.Adom ∪ e₁.constants
                            exact hOver i)
                        have hQ₂ :
                            Tuple.MapsInto t₂ Q := by
                          have hOver :
                              t₂.isTupleOver
                                (I.Adom ∪
                                  e₂.constants) :=
                            answer_over_adom
                              (A := A) (D := D)
                              (Γ := Γ) I h₂ hAns₂
                          intro i
                          exact hContain₂ (by
                            change
                              t₂.get i ∈
                                I.Adom ∪ e₂.constants
                            exact hOver i)
                        have hSat₁On :
                            Formula.ArbitraryAssignSatIn Q I
                              (BlockAssign.onBlock
                                start t₁) φ₁ :=
                          (ih₁ (start := start)
                            (n := n₁) (φ := φ₁)
                            h₁ hφ₁ t₁
                            hContain₁ hQ₁).1 hAns₁
                        have hSat₂On :
                            Formula.ArbitraryAssignSatIn Q I
                              (BlockAssign.onBlock
                                (start + n₁)
                                t₂) φ₂ :=
                          (ih₂ (start := start + n₁)
                            (n := n₂) (φ := φ₂)
                            h₂ hφ₂ t₂
                            hContain₂ hQ₂).1 hAns₂
                        subst t
                        have hAgree₁ :
                            Assign.AgreeOn
                              (BlockAssign.onBlock start
                                (appendTuple t₁ t₂))
                              (BlockAssign.onBlock start t₁)
                              φ₁.freeVars := by
                          rw [hFV₁]
                          intro x hx
                          rw [Var.mem_toFinset_block_iff]
                            at hx
                          let i : Fin n₁ :=
                            ⟨x - start, by omega⟩
                          have hxEq : x = start + i := by
                            dsimp [i]
                            exact
                              (Nat.add_sub_of_le hx.1).symm
                          rw [hxEq]
                          have hL :=
                            BlockAssign.onBlock_eq start
                              (appendTuple t₁ t₂)
                              ⟨i.1, by omega⟩
                          have hR :=
                            BlockAssign.onBlock_eq
                              start t₁ i
                          rw [hL, hR]
                          exact
                            get_appendTuple_left t₁ t₂ i
                        have hAgree₂ :
                            Assign.AgreeOn
                              (BlockAssign.onBlock start
                                (appendTuple t₁ t₂))
                              (BlockAssign.onBlock
                                (start + n₁) t₂)
                              φ₂.freeVars := by
                          rw [hFV₂]
                          intro x hx
                          rw [Var.mem_toFinset_block_iff]
                            at hx
                          let i : Fin n₂ :=
                            ⟨x - (start + n₁),
                              by omega⟩
                          have hxEq :
                              x = start + n₁ + i := by
                            dsimp [i]
                            exact
                              (Nat.add_sub_of_le hx.1).symm
                          rw [hxEq]
                          have hL :=
                            BlockAssign.onBlock_eq start
                              (appendTuple t₁ t₂)
                              ⟨n₁ + i.1, by omega⟩
                          have hR :=
                            BlockAssign.onBlock_eq
                              (start + n₁) t₂ i
                          have hL' :
                              BlockAssign.onBlock start
                                  (appendTuple t₁ t₂)
                                  (start + n₁ + i) =
                                (appendTuple t₁ t₂).get
                                  ⟨n₁ + i.1,
                                    by omega⟩ := by
                            simpa [Nat.add_assoc] using hL
                          rw [hL', hR]
                          exact
                            get_appendTuple_right
                              t₁ t₂ i
                        exact
                          ⟨(holdsIn_eq_of_agreeOn_freeVars
                              (Q := Q) (Γ := Γ) (I := I)
                              (φ := φ₁) hAgree₁).2
                              hSat₁On,
                            (holdsIn_eq_of_agreeOn_freeVars
                              (Q := Q) (Γ := Γ) (I := I)
                              (φ := φ₂) hAgree₂).2
                              hSat₂On⟩
                      · intro hSat
                        rcases hSat with
                          ⟨hSat₁, hSat₂⟩
                        let t₁ :=
                          Tuple.left
                            (n := n₁) (m := n₂) t
                        let t₂ :=
                          Tuple.right
                            (n := n₁) (m := n₂) t
                        have hQ₁ :
                            Tuple.MapsInto t₁ Q := by
                          exact
                            Tuple.left_mapsInto
                              (n := n₁) (m := n₂) hQ
                        have hQ₂ :
                            Tuple.MapsInto t₂ Q := by
                          exact
                            Tuple.right_mapsInto
                              (n := n₁) (m := n₂) hQ
                        have hAgree₁ :
                            Assign.AgreeOn
                              (BlockAssign.onBlock start t)
                              (BlockAssign.onBlock start t₁)
                              φ₁.freeVars := by
                          rw [hFV₁]
                          exact
                            BlockAssign.onBlock_left_agree
                              start t
                        have hAgree₂ :
                            Assign.AgreeOn
                              (BlockAssign.onBlock start t)
                              (BlockAssign.onBlock
                                (start + n₁) t₂)
                              φ₂.freeVars := by
                          rw [hFV₂]
                          exact
                            BlockAssign.onBlock_right_agree
                              start t
                        have hSat₁On :
                            Formula.ArbitraryAssignSatIn Q I
                              (BlockAssign.onBlock
                                start t₁) φ₁ :=
                          (holdsIn_eq_of_agreeOn_freeVars
                            (Q := Q) (Γ := Γ) (I := I)
                            (φ := φ₁) hAgree₁).1
                            hSat₁
                        have hSat₂On :
                            Formula.ArbitraryAssignSatIn Q I
                              (BlockAssign.onBlock
                                (start + n₁)
                                t₂) φ₂ :=
                          (holdsIn_eq_of_agreeOn_freeVars
                            (Q := Q) (Γ := Γ) (I := I)
                            (φ := φ₂) hAgree₂).1
                            hSat₂
                        have hAns₁ :
                            e₁.answerContains I t₁ :=
                          (ih₁ (start := start)
                            (n := n₁) (φ := φ₁)
                            h₁ hφ₁ t₁
                            hContain₁ hQ₁).2 hSat₁On
                        have hAns₂ :
                            e₂.answerContains I t₂ :=
                          (ih₂ (start := start + n₁)
                            (n := n₂) (φ := φ₂)
                            h₂ hφ₂ t₂
                            hContain₂ hQ₂).2 hSat₂On
                        exact
                          (answer_prod_iff h₁ h₂ t).2
                          ⟨t₁, hAns₁, t₂, hAns₂,
                            by
                              dsimp [t₁, t₂]
                              let hSplit :=
                                appendTuple_split t
                              exact hSplit⟩
  | union e₁ e₂ ih₁ ih₂ =>
      cases h₁ : e₁.arity? Γ with
      | none =>
          simp [arity?, h₁] at hAr
      | some n₁ =>
          cases h₂ : e₂.arity? Γ with
          | none =>
              simp [arity?, h₁, h₂] at hAr
          | some n₂ =>
              cases hφ₁ :
                  toRelCalcFormula? Γ start e₁ with
              | none =>
                  simp [toRelCalcFormula?, h₁, h₂,
                    hφ₁] at hφ
              | some φ₁ =>
                  cases hφ₂ :
                      toRelCalcFormula? Γ start e₂ with
                  | none =>
                      simp [toRelCalcFormula?, h₁, h₂,
                        hφ₁, hφ₂] at hφ
                  | some φ₂ =>
                      by_cases hEq : n₁ = n₂
                      · have hn : n₁ = n := by
                          simpa [arity?, h₁, h₂, hEq]
                            using hAr
                        subst hn
                        subst hEq
                        simp only [toRelCalcFormula?,
                          h₁, h₂, hφ₁, hφ₂] at hφ
                        have hφEq :
                            φ = .or φ₁ φ₂ :=
                          (Option.some.inj hφ).symm
                        subst φ
                        have hContain₁ :
                          Set.Subset
                            (fun d =>
                                d ∈
                                  I.Adom ∪ e₁.constants)
                              Q := by
                          intro d hd
                          apply hContain
                          change d ∈ I.Adom ∪
                            (e₁.constants ∪
                              e₂.constants)
                          change
                            d ∈
                              I.Adom ∪ e₁.constants
                            at hd
                          have hdU := mem_union.mp hd
                          rcases hdU with hAd | hC
                          · exact
                              mem_union.mpr (Or.inl hAd)
                          · exact mem_union.mpr
                              (Or.inr
                                (mem_union.mpr (Or.inl hC)))
                        have hContain₂ :
                          Set.Subset
                            (fun d =>
                                d ∈
                                  I.Adom ∪ e₂.constants)
                              Q := by
                          intro d hd
                          apply hContain
                          change d ∈ I.Adom ∪
                            (e₁.constants ∪
                              e₂.constants)
                          change
                            d ∈
                              I.Adom ∪ e₂.constants
                            at hd
                          have hdU := mem_union.mp hd
                          rcases hdU with hAd | hC
                          · exact
                              mem_union.mpr (Or.inl hAd)
                          · exact mem_union.mpr
                              (Or.inr
                                (mem_union.mpr (Or.inr hC)))
                        let Sat :=
                          Formula.ArbitraryAssignSatIn Q I
                        calc
                          answerContains
                              (RawRAExpr.union e₁ e₂)
                              I t
                              ↔
                                e₁.answerContains I t ∨
                                  e₂.answerContains I t :=
                                answer_union_iff h₁ h₂ t
                          _ ↔
                                Sat
                                  (BlockAssign.onBlock start t)
                                  φ₁ ∨
                                Sat
                                  (BlockAssign.onBlock start t)
                                  φ₂ := by
                                exact or_congr
                                  (ih₁ (start := start)
                                    (n := n₁)
                                    (φ := φ₁)
                                    h₁ hφ₁ t
                                    hContain₁ hQ)
                                  (ih₂ (start := start)
                                    (n := n₁)
                                    (φ := φ₂)
                                    h₂ hφ₂ t
                                    hContain₂ hQ)
                            _ ↔
                                  Sat
                                    (BlockAssign.onBlock start t)
                                    (.or φ₁ φ₂) := by
                                  rfl
                      · simp [arity?, h₁, h₂, hEq]
                          at hAr
  | diff e₁ e₂ ih₁ ih₂ =>
      cases h₁ : e₁.arity? Γ with
      | none =>
          simp [arity?, h₁] at hAr
      | some n₁ =>
          cases h₂ : e₂.arity? Γ with
          | none =>
              simp [arity?, h₁, h₂] at hAr
          | some n₂ =>
              cases hφ₁ :
                  toRelCalcFormula? Γ start e₁ with
              | none =>
                  simp [toRelCalcFormula?, h₁, h₂,
                    hφ₁] at hφ
              | some φ₁ =>
                  cases hφ₂ :
                      toRelCalcFormula? Γ start e₂ with
                  | none =>
                      simp [toRelCalcFormula?, h₁, h₂,
                        hφ₁, hφ₂] at hφ
                  | some φ₂ =>
                      by_cases hEq : n₁ = n₂
                      · have hn : n₁ = n := by
                          simpa [arity?, h₁, h₂, hEq]
                            using hAr
                        subst hn
                        subst hEq
                        simp only [toRelCalcFormula?,
                          h₁, h₂, hφ₁, hφ₂] at hφ
                        have hφEq :
                            φ =
                              .and φ₁
                                (.not φ₂) :=
                          (Option.some.inj hφ).symm
                        subst φ
                        have hContain₁ :
                          Set.Subset
                            (fun d =>
                                d ∈
                                  I.Adom ∪ e₁.constants)
                              Q := by
                          intro d hd
                          apply hContain
                          change d ∈ I.Adom ∪
                            (e₁.constants ∪
                              e₂.constants)
                          change
                            d ∈
                              I.Adom ∪ e₁.constants
                            at hd
                          have hdU := mem_union.mp hd
                          rcases hdU with hAd | hC
                          · exact
                              mem_union.mpr (Or.inl hAd)
                          · exact mem_union.mpr
                              (Or.inr
                                (mem_union.mpr (Or.inl hC)))
                        have hContain₂ :
                          Set.Subset
                            (fun d =>
                                d ∈
                                  I.Adom ∪ e₂.constants)
                              Q := by
                          intro d hd
                          apply hContain
                          change d ∈ I.Adom ∪
                            (e₁.constants ∪
                              e₂.constants)
                          change
                            d ∈
                              I.Adom ∪ e₂.constants
                            at hd
                          have hdU := mem_union.mp hd
                          rcases hdU with hAd | hC
                          · exact
                              mem_union.mpr (Or.inl hAd)
                          · exact mem_union.mpr
                              (Or.inr
                                (mem_union.mpr (Or.inr hC)))
                        let Sat :=
                          Formula.ArbitraryAssignSatIn Q I
                        calc
                          answerContains
                              (RawRAExpr.diff e₁ e₂)
                              I t
                              ↔
                                e₁.answerContains I t ∧
                                  ¬ e₂.answerContains I t :=
                                answer_diff_iff h₁ h₂ t
                          _ ↔
                                Sat
                                  (BlockAssign.onBlock start t)
                                  φ₁ ∧
                                ¬
                                  Sat
                                    (BlockAssign.onBlock start t)
                                    φ₂ := by
                                exact and_congr
                                  (ih₁ (start := start)
                                    (n := n₁)
                                    (φ := φ₁)
                                    h₁ hφ₁ t
                                    hContain₁ hQ)
                                  (not_congr
                                    (ih₂ (start := start)
                                      (n := n₁)
                                      (φ := φ₂)
                                      h₂ hφ₂ t
                                      hContain₂ hQ))
                            _ ↔
                                  Sat
                                    (BlockAssign.onBlock start t)
                                    (.and φ₁
                                      (.not φ₂)) := by
                                  rfl
                      · simp [arity?, h₁, h₂, hEq]
                          at hAr

/-
  Satisfaction equivalence for the raw target-driven
  translator.

  The theorem is deliberately stated over `answerContains`,
  the raw relational-algebra answer predicate above, so
  downstream well-formed packaging does not need to inspect
  `eval?`'s dependent `Sigma` result.
-/
theorem toRelCalcFormula?_answerContains_iff_satIn
    {Γ : UnnamedSchema A}
    {start n : Nat}
    {e : RawRAExpr A D}
    {φ : Formula D Γ}
    (hAr : e.arity? Γ = some n)
    (hφ : toRelCalcFormula? Γ start e = some φ)
      (Q : Set D)
      (I : Instance D Γ)
      (t : Tuple D n)
      (hContain :
        (↑(I.Adom ∪ e.constants) : Set D) ⊆ Q)
      (hQ : Tuple.MapsInto t Q) :
      e.answerContains I t ↔
        φ.SatIn I (BlockAssign.onBlock start t) Q := by
    have hMaps :
        Assign.MapsInto
          (BlockAssign.onBlock start t)
          φ.freeVars Q := by
      rw [toRelCalcFormula?_freeVars
        (A := A) (D := D) (Γ := Γ) hAr hφ]
      exact BlockAssign.mapsInto_onBlock start hQ
    exact
      (toRelCalcFormula?_answerContains_iff_arbitraryAssignSatIn
        (A := A) (D := D) (Γ := Γ)
        (start := start) (n := n)
        (e := e) (φ := φ)
        hAr hφ Q I t hContain hQ).trans
      (by
        constructor
        · intro hHolds
          exact ⟨hMaps, hHolds⟩
        · intro hSat
          exact hSat.2)

end RawRAExpr

namespace RAExpr

open UnnamedRA.ToRelCalc

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  The formula selected by the typed RA-to-RelCalc query
  construction. The `.bot` branch is unreachable for
  well-formed expressions and is eliminated by
  `toRelCalcFormula?_total`.
-/
def toRelCalcFormula
    {n : Nat}
    (e : RAExpr D Γ n) :
    RelCalc.Formula D Γ :=
  match RawRAExpr.toRelCalcFormula? Γ 0 e.expr with
  | some φ => φ
  | none => .bot

theorem toRelCalcFormula?_total
    {n : Nat}
    (e : RAExpr D Γ n) :
    RawRAExpr.toRelCalcFormula? Γ 0 e.expr =
      some
        (toRelCalcFormula
          (A := A) (D := D) (Γ := Γ) e) := by
  dsimp [toRelCalcFormula]
  cases h :
      RawRAExpr.toRelCalcFormula? Γ 0 e.expr with
  | none =>
      rcases RawRAExpr.toRelCalcFormula?_exists
        (A := A) (D := D) (Γ := Γ) 0 e.wf with
      ⟨φ, hφ⟩
      rw [h] at hφ
      contradiction
  | some φ =>
      simp

/-
  The relational-calculus query produced by the typed
  RA-to-RelCalc translator.
-/
def toRelCalcQuery
    {n : Nat}
    (e : RAExpr D Γ n) :
      RelCalc.Query D Γ n :=
    { vars := blockVector 0 n
      form :=
        toRelCalcFormula (A := A) (D := D) (Γ := Γ) e
      freeVars_eq := by
        rw [blockVector_toList]
        exact RawRAExpr.toRelCalcFormula?_freeVars
          (A := A) (D := D) (Γ := Γ)
          (start := 0) (n := n)
          (e := e.expr)
          (φ := toRelCalcFormula
            (A := A) (D := D) (Γ := Γ) e)
          e.wf
          (toRelCalcFormula?_total
            (A := A) (D := D) (Γ := Γ) e) }

theorem toRelCalcQuery_constants
    {n : Nat}
    (e : RAExpr D Γ n) :
    e.toRelCalcQuery.constants =
      e.constants := by
  change
    (toRelCalcFormula
      (A := A) (D := D) (Γ := Γ) e).constants =
      e.expr.constants
  exact RawRAExpr.toRelCalcFormula?_constants
    (A := A) (D := D) (Γ := Γ)
    (start := 0) (n := n)
    (e := e.expr)
    e.wf
    (toRelCalcFormula?_total
      (A := A) (D := D) (Γ := Γ) e)

/-
  A tuple is in the RA denotation exactly when the canonical
  tuple assignment satisfies the translated RelCalc formula.
-/
theorem toRelCalcQuery_formula_iff
    {n : Nat}
    (e : RAExpr D Γ n)
    (I : Instance D Γ)
    (t : Tuple D n) :
    t ∈ e.eval I ↔
      e.toRelCalcQuery.form.AdomSat I
        (BlockAssign.onBlock 0 t) := by
  let q := e.toRelCalcQuery
  let Qad : Set D := fun d => d ∈ RelCalc.Adom q.form I
  let φ :=
    toRelCalcFormula
      (A := A) (D := D) (Γ := Γ) e
  have hφ :
      RawRAExpr.toRelCalcFormula? Γ 0 e.expr =
        some φ :=
    toRelCalcFormula?_total
      (A := A) (D := D) (Γ := Γ) e
  have hRawEval :
      e.expr.eval? (Γ := Γ) I =
        some ⟨n, e.eval I⟩ :=
    RAExpr.raw_eval?_eq_eval e I
  have hAdom :
      RelCalc.Adom q.form I = I.Adom ∪ e.constants := by
    subst q
    change I.Adom ∪ e.toRelCalcQuery.constants =
      I.Adom ∪ e.constants
    rw [toRelCalcQuery_constants
      (A := A) (D := D) (Γ := Γ) e]
  constructor
  · intro hAns
    have hRawAns :
        e.expr.answerContains I t :=
      (RawRAExpr.answer_iff_of_eval hRawEval t).2
        hAns
    have htQ :
        Tuple.MapsInto t Qad := by
      have hOver :
          t.isTupleOver (I.Adom ∪ e.constants) :=
        RawRAExpr.answer_over_adom (A := A) (D := D)
          (Γ := Γ) I e.wf hRawAns
      intro i
      change t.get i ∈ RelCalc.Adom q I
      simpa [hAdom] using hOver i
    have hContain :
        (↑(I.Adom ∪ e.constants) : Set D) ⊆
          Qad := by
      intro d hd
      change d ∈ RelCalc.Adom q I
      simpa [hAdom] using hd
    have hReal :
        Assign.Realizes
          (BlockAssign.onBlock 0 t)
          q.vars t := by
      subst q
      intro i
      simpa [toRelCalcQuery,
        blockVector, Vector.get] using
        BlockAssign.onBlock_eq 0 t i
    have hSatQ :
        q.form.SatIn I
          (BlockAssign.onBlock 0 t) Qad := by
      subst q
      change
        φ.SatIn I
          (BlockAssign.onBlock 0 t) Qad
      exact
        (RawRAExpr.toRelCalcFormula?_answerContains_iff_satIn
          (A := A) (D := D) (Γ := Γ)
          (start := 0) (n := n)
          (e := e.expr) (φ := φ)
          e.wf hφ
          Qad
          I t hContain htQ).1 hRawAns
    simpa [RelCalc.Formula.AdomSat,
      RelCalc.Adom.toSet, Qad, q] using hSatQ
  · intro hSat
    have hSatQ :
        q.form.SatIn I
          (BlockAssign.onBlock 0 t) Qad := by
      simpa [RelCalc.Formula.AdomSat,
        RelCalc.Adom.toSet, Qad, q] using hSat
    have htQ :
        Tuple.MapsInto t Qad := by
      intro i
      have hVar :
          q.vars.get i ∈ q.form.freeVars := by
        rw [q.freeVars_eq]
        exact List.mem_toFinset.mpr
          (Tuple.get_mem_toList q.vars i)
      have hVal :
          BlockAssign.onBlock 0 t
            (q.vars.get i) ∈ RelCalc.Adom q.form I :=
        hSatQ.1 _ hVar
      have hVarQ : q.vars.get i = (0 : Nat) + i := by
        subst q
        simp [toRelCalcQuery,
          blockVector, Vector.get]
      rw [hVarQ] at hVal
      rw [BlockAssign.onBlock_eq 0 t i] at hVal
      exact hVal
    have hContain :
        (↑(I.Adom ∪ e.constants) : Set D) ⊆
          Qad := by
      intro d hd
      change d ∈ RelCalc.Adom q.form I
      simpa [hAdom] using hd
    have hCanonical' :
        φ.SatIn I
          (BlockAssign.onBlock 0 t) Qad := by
      subst q
      simpa [toRelCalcQuery, φ] using hSatQ
    have hRawAns :
        e.expr.answerContains I t :=
      (RawRAExpr.toRelCalcFormula?_answerContains_iff_satIn
        (A := A) (D := D) (Γ := Γ)
        (start := 0) (n := n)
        (e := e.expr) (φ := φ)
        e.wf hφ
        Qad
        I t hContain htQ).2 hCanonical'
    have hMem : t ∈ e.eval I :=
      (RawRAExpr.answer_iff_of_eval hRawEval t).1 hRawAns
    exact hMem

/-
  The translated query has exactly the same finite
  denotation as the source RA expression.
-/
theorem toRelCalcQuery_eval_eq
    {n : Nat}
    (e : RAExpr D Γ n)
    (I : Instance D Γ) :
    e.eval I = e.toRelCalcQuery.eval I := by
  let q := e.toRelCalcQuery
  let Qad : Set D := fun d => d ∈ RelCalc.Adom q I
  apply Finset.ext
  intro t
  constructor
  · intro hAns
    have hFormula :
        q.form.AdomSat I
          (BlockAssign.onBlock 0 t) := by
      subst q
      exact (e.toRelCalcQuery_formula_iff I t).1 hAns
    have hReal :
        Assign.Realizes
          (BlockAssign.onBlock 0 t)
          q.vars t := by
      subst q
      intro i
      simpa [toRelCalcQuery,
        blockVector, Vector.get] using
        BlockAssign.onBlock_eq 0 t i
    exact
      (RelCalc.Query.in_eval_iff_satTuple q I t).2
        ⟨BlockAssign.onBlock 0 t,
          hReal, hFormula⟩
  · intro hAns
    have hEvalCorrect :=
      RelCalc.Query.in_eval_iff_satTuple q I t
    rcases
        hEvalCorrect.1 hAns with
      ⟨σ, hReal, hSat⟩
    have hFree :
        q.form.freeVars =
          (Var.block 0 n).toFinset := by
      subst q
      exact RawRAExpr.toRelCalcFormula?_freeVars
        (A := A) (D := D) (Γ := Γ)
          (start := 0) (n := n)
          (e := e.expr)
          (φ := toRelCalcFormula
            (A := A) (D := D) (Γ := Γ) e)
          e.wf
          (toRelCalcFormula?_total
            (A := A) (D := D) (Γ := Γ) e)
    have hAgree :
        Assign.AgreeOn
          (BlockAssign.onBlock 0 t) σ
          q.form.freeVars := by
      rw [hFree]
      intro x hx
      rw [Var.mem_toFinset_block_iff] at hx
      let i : Fin n := ⟨x, by simpa using hx.2⟩
      have hxEq : x = (0 : Nat) + i := by
        simp [i]
      have hVarQ : q.vars.get i = (0 : Nat) + i := by
        subst q
        simp [toRelCalcQuery,
          blockVector, Vector.get]
      have hσ : σ ((0 : Nat) + i) = t.get i := by
        have hRealI := hReal i
        rw [hVarQ] at hRealI
        exact hRealI
      rw [hxEq]
      exact
        (BlockAssign.onBlock_eq 0 t i).trans
          hσ.symm
    have hSatIn :
        q.form.SatIn I σ Qad := by
      simpa [RelCalc.Formula.AdomSat, RelCalc.Adom.toSet,
        Qad] using hSat
    have hCanonical :
        q.form.SatIn I
          (BlockAssign.onBlock 0 t) Qad :=
      (RelCalc.Formula.satIn_eq_of_agreeOn_freeVars
        (Q := Qad)
        (I := I)
        (φ := q.form)
        (σ := BlockAssign.onBlock 0 t)
        (τ := σ) hAgree).2 hSatIn
    have hFormula :
        q.form.AdomSat I
          (BlockAssign.onBlock 0 t) := by
      simpa [RelCalc.Formula.AdomSat, RelCalc.Adom.toSet,
        Qad] using hCanonical
    subst q
    exact (e.toRelCalcQuery_formula_iff I t).2 hFormula

/- Existential form of `RAExpr.toRelCalcQuery_eval_eq`. -/
theorem exists_equiv_relCalcQuery
    {n : Nat}
    (e : RAExpr D Γ n) :
    ∃ q : RelCalc.Query D Γ n,
      ∀ I : Instance D Γ,
        e.eval I = q.eval I :=
  ⟨e.toRelCalcQuery, e.toRelCalcQuery_eval_eq⟩

end RAExpr
