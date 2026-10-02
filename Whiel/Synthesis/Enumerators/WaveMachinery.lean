-- Author: Jesse Comer
import Whiel.Synthesis.DisjunctiveClause.Spec
import Mathlib.Data.List.Sublists

/-
  Shared incremental wave machinery for replaceable
  enumerator realizations.

  A realization retains a growing literal frontier between
  stages. The machinery here marks the current frontier
  against the prior one, generates exactly the fresh-member
  sublists of a requested width without constructing
  old-only results, and accounts traversal work. It is
  independent of any particular stage schedule, universe
  construction, or parameter policy: those live in the
  per-enumerator folders.

  Key definitions include:
    * `Marked`, `mark`, `markCurrent`, `eraseMarks`
    * `TraversalStats`
    * `sublistsLenWithFresh`
    * `RepresentationResult`
    * `introducedRepresentationResult`

  Generic lemmas are proved in `WaveMachineryLemmas.lean`.
-/

------------------------------------------------------------
-- Fresh-Member Sublists
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace Enumerators

open DisjunctiveClause

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- A value paired with its current-wave freshness bit. -/
abbrev Marked (T : Type) := T × Bool

/- True exactly when a marked list contains a fresh value. -/
def hasFresh {T : Type} (values : List (Marked T)) : Bool :=
  values.any Prod.snd

/- Number of fresh values in one remaining marked suffix. -/
def freshCount {T : Type} : List (Marked T) → Nat
| [] => 0
| value :: rest =>
    if value.2 then freshCount rest + 1
    else freshCount rest

/- Work counters for the direct fresh-member traversal. -/
structure TraversalStats where
  visitedNodes : Nat := 0
  noFreshPrunes : Nat := 0
  tooShortPrunes : Nat := 0
deriving DecidableEq, Repr

namespace TraversalStats

/- Add independent traversal counters. -/
def add (left right : TraversalStats) : TraversalStats :=
  { visitedNodes := left.visitedNodes + right.visitedNodes
    noFreshPrunes := left.noFreshPrunes + right.noFreshPrunes
    tooShortPrunes := left.tooShortPrunes + right.tooShortPrunes }

/- One ordinary recursive node. -/
def visited : TraversalStats :=
  { visitedNodes := 1 }

/- One subtree pruned because no fresh value remains. -/
def noFresh : TraversalStats :=
  { visitedNodes := 1, noFreshPrunes := 1 }

/- One subtree pruned because its suffix is too short. -/
def tooShort : TraversalStats :=
  { visitedNodes := 1, tooShortPrunes := 1 }

end TraversalStats

/- Values and counters produced by one direct traversal. -/
structure FreshSublistsResult (T : Type) where
  values : List (List (Marked T))
  stats : TraversalStats

/-
  Exact-length sublists containing a fresh value.

  The two counters describe the remaining suffix. They make
  the two important dead-branch checks constant-time: no
  fresh value remains, or too few values remain for the
  requested width.
-/
def sublistsLenWithFreshAux {T : Type} :
    Nat → Nat → Nat → List (Marked T) →
      FreshSublistsResult T
| 0, _, _, _ =>
    { values := [], stats := TraversalStats.visited }
| _ + 1, 0, _, _ =>
    { values := [], stats := TraversalStats.tooShort }
| _ + 1, _ + 1, 0, _ =>
    { values := [], stats := TraversalStats.noFresh }
| _ + 1, _ + 1, _ + 1, [] =>
    { values := [], stats := TraversalStats.visited }
| width + 1, remainingLength + 1,
    remainingFresh + 1, value :: rest =>
    if remainingLength < width then
      { values := [], stats := TraversalStats.tooShort }
    else if value.2 then
      let excluded := sublistsLenWithFreshAux (width + 1)
        remainingLength remainingFresh rest
      { values := excluded.values ++
          (rest.sublistsLen width).map (value :: ·)
        stats := TraversalStats.visited.add excluded.stats }
    else
      let excluded := sublistsLenWithFreshAux (width + 1)
        remainingLength (remainingFresh + 1) rest
      let included := sublistsLenWithFreshAux width
        remainingLength (remainingFresh + 1) rest
      { values := excluded.values ++
          included.values.map (value :: ·)
        stats := TraversalStats.visited.add
          (excluded.stats.add included.stats) }

------------------------------------------------------------
-- Tail-Recursive Traversal Twin
------------------------------------------------------------

/-
  `sublistsLenWithFreshAux` recurses once per frontier value,
  so its compiled form costs call-stack space linear in the
  frontier. Deep-stage frontiers exceed any fixed thread
  stack. The twin below computes the same result by folding
  a width-indexed suffix table along the reversed frontier:
  every unbounded walk is a `foldl` or a plain tail loop, so
  the compiled traversal runs in constant stack. The `csimp`
  equality swaps it in for compiled callers only; every
  theorem keeps reasoning about the direct recursion.
-/

/- Counter values after consuming one marked prefix. -/
def countersAfter {T : Type} :
    Nat → Nat → List (Marked T) → Nat × Nat
| remainingLength, remainingFresh, [] =>
    (remainingLength, remainingFresh)
| remainingLength, remainingFresh, value :: rest =>
    countersAfter (remainingLength - 1)
      (if value.2 then remainingFresh - 1
        else remainingFresh) rest

/- Each value with the counters its traversal node sees. -/
def annotateCounters {T : Type} :
    Nat → Nat → List (Marked T) →
      List (Marked T × Nat × Nat)
| _, _, [] => []
| remainingLength, remainingFresh, value :: rest =>
    (value, remainingLength, remainingFresh) ::
      annotateCounters (remainingLength - 1)
        (if value.2 then remainingFresh - 1
          else remainingFresh) rest

/-
  One suffix-table cell: the traversal result at one width,
  next to the plain exact-width sublists of the same suffix
  that fresh-branch nodes splice in.
-/
structure FreshCell (T : Type) where
  result : FreshSublistsResult T
  plain : List (List (Marked T))

/- The width-zero cell of any suffix. -/
def zeroCell {T : Type} : FreshCell T :=
  { result := { values := [], stats := .visited }
    plain := [[]] }

/- The cell of the empty suffix at one positive width. -/
def emptySuffixCell {T : Type}
    (finalLength finalFresh : Nat) : FreshCell T :=
  { result :=
      match finalLength, finalFresh with
      | 0, _ => { values := [], stats := .tooShort }
      | _ + 1, 0 => { values := [], stats := .noFresh }
      | _ + 1, _ + 1 => { values := [], stats := .visited }
    plain := [] }

/- The empty-suffix cell at any width. -/
def baseCell {T : Type}
    (finalLength finalFresh : Nat) :
    Nat → FreshCell T
| 0 => zeroCell
| _ + 1 => emptySuffixCell finalLength finalFresh

/-
  One positive-width parent cell from the two child cells at
  its width and one width below, mirroring the direct cons
  node exactly.
-/
def stepCell {T : Type}
    (value : Marked T)
    (remainingLength remainingFresh : Nat)
    (atWidth belowWidth : FreshCell T)
    (width : Nat) : FreshCell T :=
  { plain := atWidth.plain ++
      belowWidth.plain.map (value :: ·)
    result :=
      match remainingLength, remainingFresh with
      | 0, _ => { values := [], stats := .tooShort }
      | _ + 1, 0 => { values := [], stats := .noFresh }
      | shorter + 1, _ + 1 =>
          if shorter < width then
            { values := [], stats := .tooShort }
          else if value.2 then
            { values := atWidth.result.values ++
                belowWidth.plain.map (value :: ·)
              stats := TraversalStats.visited.add
                atWidth.result.stats }
          else
            { values := atWidth.result.values ++
                belowWidth.result.values.map (value :: ·)
              stats := TraversalStats.visited.add
                (atWidth.result.stats.add
                  belowWidth.result.stats) } }

/- Positive-width parent cells above one running child. -/
def stepRowAux {T : Type}
    (value : Marked T)
    (remainingLength remainingFresh : Nat) :
    Nat → FreshCell T → List (FreshCell T) →
      List (FreshCell T)
| _, _, [] => []
| width, below, cell :: rest =>
    stepCell value remainingLength remainingFresh
        cell below width ::
      stepRowAux value remainingLength remainingFresh
        (width + 1) cell rest

/- The full parent row of one child suffix row. -/
def stepRow {T : Type}
    (value : Marked T)
    (remainingLength remainingFresh : Nat) :
    List (FreshCell T) → List (FreshCell T)
| [] => []
| cell :: rest =>
    zeroCell ::
      stepRowAux value remainingLength remainingFresh
        0 cell rest

/- The suffix table of one annotated frontier. -/
def rowFor {T : Type}
    (width remainingLength remainingFresh : Nat)
    (values : List (Marked T)) :
    List (FreshCell T) :=
  let (finalLength, finalFresh) :=
    countersAfter remainingLength remainingFresh values
  (annotateCounters remainingLength remainingFresh
      values).reverse.foldl
    (fun row entry =>
      stepRow entry.1 entry.2.1 entry.2.2 row)
    ((List.range (width + 1)).map
      (baseCell finalLength finalFresh))

/- The constant-stack traversal twin. -/
def sublistsLenWithFreshAuxTR {T : Type}
    (width remainingLength remainingFresh : Nat)
    (values : List (Marked T)) :
    FreshSublistsResult T :=
  ((rowFor width remainingLength remainingFresh
      values).getLastD zeroCell).result

/- The cell every table position must equal. -/
def cellSpec {T : Type}
    (width remainingLength remainingFresh : Nat)
    (values : List (Marked T)) : FreshCell T :=
  { result := sublistsLenWithFreshAux width
      remainingLength remainingFresh values
    plain := values.sublistsLen width }

/- The empty-suffix base cells meet the specification. -/
theorem baseCell_eq_cellSpec {T : Type}
    (finalLength finalFresh width : Nat) :
    baseCell (T := T) finalLength finalFresh width =
      cellSpec width finalLength finalFresh [] := by
  match width with
  | 0 =>
      simp [baseCell, zeroCell, cellSpec,
        sublistsLenWithFreshAux, List.sublistsLen_zero]
  | width + 1 =>
      match finalLength, finalFresh with
      | 0, _ =>
          simp [baseCell, emptySuffixCell, cellSpec,
            sublistsLenWithFreshAux,
            List.sublistsLen_succ_nil]
      | _ + 1, 0 =>
          simp [baseCell, emptySuffixCell, cellSpec,
            sublistsLenWithFreshAux,
            List.sublistsLen_succ_nil]
      | _ + 1, _ + 1 =>
          simp [baseCell, emptySuffixCell, cellSpec,
            sublistsLenWithFreshAux,
            List.sublistsLen_succ_nil]

/- One parent cell from specified child cells is specified. -/
theorem stepCell_eq_cellSpec {T : Type}
    (value : Marked T)
    (remainingLength remainingFresh width : Nat)
    (rest : List (Marked T)) :
    stepCell value remainingLength remainingFresh
        (cellSpec (width + 1) (remainingLength - 1)
          (if value.2 then remainingFresh - 1
            else remainingFresh) rest)
        (cellSpec width (remainingLength - 1)
          (if value.2 then remainingFresh - 1
            else remainingFresh) rest)
        width =
      cellSpec (width + 1) remainingLength
        remainingFresh (value :: rest) := by
  match remainingLength, remainingFresh with
  | 0, remainingFresh =>
      simp [stepCell, cellSpec,
        sublistsLenWithFreshAux,
        List.sublistsLen_succ_cons]
  | shorter + 1, 0 =>
      simp [stepCell, cellSpec,
        sublistsLenWithFreshAux,
        List.sublistsLen_succ_cons]
  | shorter + 1, fresher + 1 =>
      by_cases hFresh : value.2 <;>
        simp [stepCell, cellSpec,
          sublistsLenWithFreshAux, hFresh,
          List.sublistsLen_succ_cons]

/- Stepping a specified child tail yields specified cells. -/
theorem stepRowAux_eq_cellSpec {T : Type}
    (value : Marked T)
    (remainingLength remainingFresh : Nat)
    (rest : List (Marked T)) :
    ∀ (count start : Nat),
      stepRowAux value remainingLength remainingFresh
          start
          (cellSpec start (remainingLength - 1)
            (if value.2 then remainingFresh - 1
              else remainingFresh) rest)
          ((List.range count).map fun index =>
            cellSpec (start + 1 + index)
              (remainingLength - 1)
              (if value.2 then remainingFresh - 1
                else remainingFresh) rest) =
        (List.range count).map fun index =>
          cellSpec (start + 1 + index) remainingLength
            remainingFresh (value :: rest) := by
  intro count
  induction count with
  | zero => intro start; simp [stepRowAux]
  | succ count ih =>
      intro start
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map]
      rw [stepRowAux]
      have hZero : start + 1 + 0 = start + 1 := by omega
      rw [hZero, stepCell_eq_cellSpec value
        remainingLength remainingFresh start rest]
      refine List.cons_eq_cons.mpr ⟨rfl, ?_⟩
      have hChild :
          ((fun index =>
              cellSpec (T := T) (start + 1 + index)
                (remainingLength - 1)
                (if value.2 then remainingFresh - 1
                  else remainingFresh) rest) ∘
            Nat.succ) =
            fun index =>
              cellSpec (start + 1 + 1 + index)
                (remainingLength - 1)
                (if value.2 then remainingFresh - 1
                  else remainingFresh) rest := by
        funext index
        have hArith : start + 1 + Nat.succ index =
            start + 1 + 1 + index := by omega
        simp only [Function.comp_apply, hArith]
      have hParent :
          ((fun index =>
              cellSpec (T := T) (start + 1 + index)
                remainingLength remainingFresh
                (value :: rest)) ∘ Nat.succ) =
            fun index =>
              cellSpec (start + 1 + 1 + index)
                remainingLength remainingFresh
                (value :: rest) := by
        funext index
        have hArith : start + 1 + Nat.succ index =
            start + 1 + 1 + index := by omega
        simp only [Function.comp_apply, hArith]
      rw [hChild, hParent]
      exact ih (start + 1)

/- Stepping a specified row yields the parent row spec. -/
theorem stepRow_eq_cellSpec {T : Type}
    (value : Marked T)
    (remainingLength remainingFresh width : Nat)
    (rest : List (Marked T)) :
    stepRow value remainingLength remainingFresh
        ((List.range (width + 1)).map fun index =>
          cellSpec index (remainingLength - 1)
            (if value.2 then remainingFresh - 1
              else remainingFresh) rest) =
      (List.range (width + 1)).map fun index =>
        cellSpec index remainingLength remainingFresh
          (value :: rest) := by
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map]
  rw [stepRow]
  refine List.cons_eq_cons.mpr ⟨?_, ?_⟩
  · simp [zeroCell, cellSpec, sublistsLenWithFreshAux,
      List.sublistsLen_zero]
  · have hAux := stepRowAux_eq_cellSpec value
      remainingLength remainingFresh rest width 0
    have hChild :
        ((fun index =>
            cellSpec (T := T) index
              (remainingLength - 1)
              (if value.2 then remainingFresh - 1
                else remainingFresh) rest) ∘
          Nat.succ) =
          fun index =>
            cellSpec (0 + 1 + index)
              (remainingLength - 1)
              (if value.2 then remainingFresh - 1
                else remainingFresh) rest := by
      funext index
      have hArith : Nat.succ index = 0 + 1 + index := by
        omega
      simp only [Function.comp_apply, hArith]
    have hParent :
        ((fun index =>
            cellSpec (T := T) index remainingLength
              remainingFresh (value :: rest)) ∘
          Nat.succ) =
          fun index =>
            cellSpec (0 + 1 + index) remainingLength
              remainingFresh (value :: rest) := by
      funext index
      have hArith : Nat.succ index = 0 + 1 + index := by
        omega
      simp only [Function.comp_apply, hArith]
    rw [hChild, hParent]
    exact hAux

/- The whole suffix table meets the specification. -/
theorem rowFor_eq_cellSpec {T : Type}
    (width : Nat) (values : List (Marked T)) :
    ∀ remainingLength remainingFresh,
      rowFor width remainingLength remainingFresh
          values =
        (List.range (width + 1)).map fun index =>
          cellSpec index remainingLength remainingFresh
            values := by
  induction values with
  | nil =>
      intro remainingLength remainingFresh
      simp only [rowFor, countersAfter,
        annotateCounters, List.reverse_nil,
        List.foldl_nil]
      exact List.map_congr_left fun index _ =>
        baseCell_eq_cellSpec remainingLength
          remainingFresh index
  | cons value rest ih =>
      intro remainingLength remainingFresh
      have hUnfold :
          rowFor width remainingLength remainingFresh
              (value :: rest) =
            stepRow value remainingLength remainingFresh
              (rowFor width (remainingLength - 1)
                (if value.2 then remainingFresh - 1
                  else remainingFresh) rest) := by
        simp [rowFor, countersAfter, annotateCounters,
          List.reverse_cons, List.foldl_append]
      rw [hUnfold, ih, stepRow_eq_cellSpec]

/- The twin computes the direct traversal exactly. -/
@[csimp]
theorem sublistsLenWithFreshAux_eq_tr :
    @sublistsLenWithFreshAux =
      @sublistsLenWithFreshAuxTR := by
  funext T width remainingLength remainingFresh values
  rw [sublistsLenWithFreshAuxTR, rowFor_eq_cellSpec]
  rw [List.range_succ, List.map_append]
  simp [cellSpec]

/- One direct traversal with exact counters computed once. -/
def sublistsLenWithFreshResult {T : Type}
    (width : Nat)
    (values : List (Marked T)) :
    FreshSublistsResult T :=
  sublistsLenWithFreshAux width values.length
    (freshCount values) values

/-
  Compute the exact counters once, then enumerate the direct
  fresh-member wave without constructing old-only results.
-/
def sublistsLenWithFresh {T : Type}
    (width : Nat)
    (values : List (Marked T)) :
    List (List (Marked T)) :=
  (sublistsLenWithFreshResult width values).values

/- Erase freshness bits from one marked representation. -/
def eraseMarks {T : Type}
    (values : List (Marked T)) : List T :=
  values.map Prod.fst

------------------------------------------------------------
-- Marking and Introduced Representations
------------------------------------------------------------

/- Mark one literal against the prior frontier. -/
def mark
    (prior : List (Literal D Γ))
    (literal : Literal D Γ) :
    Marked (Literal D Γ) :=
  (literal, decide (literal ∉ prior))

/- Mark the current literal frontier against the prior one. -/
def markCurrent
    (prior current : List (Literal D Γ)) :
    List (Marked (Literal D Γ)) :=
  current.map (mark prior)

/- Representations and counters for one incremental wave. -/
structure RepresentationResult where
  representations : List (LiteralList D Γ)
  stats : TraversalStats
  exactWidthOutputs : Nat := 0

def introducedRepresentationsAux
    (marked : List (Marked (Literal D Γ)))
    (remainingLength remainingFresh : Nat) :
    List Nat → RepresentationResult (D := D) (Γ := Γ)
| [] => { representations := [], stats := {} }
| width :: widths =>
    let current := sublistsLenWithFreshAux width
      remainingLength remainingFresh marked
    let later := introducedRepresentationsAux marked
      remainingLength remainingFresh widths
    { representations :=
        current.values.map eraseMarks ++ later.representations
      stats := current.stats.add later.stats }

/-
  Lower-width representations and traversal counters for one
  incremental literal frontier.
-/
def introducedRepresentationResult
    (prior current : List (Literal D Γ))
    (newWidth : Nat) :
    RepresentationResult (D := D) (Γ := Γ) :=
  let marked := markCurrent prior current
  introducedRepresentationsAux marked marked.length
    (freshCount marked) (List.range newWidth)

/-
  Lower-width representations introduced by at least one
  fresh literal. The direct generator does not construct an
  old-only representation.
-/
def introducedRepresentations
    (prior current : List (Literal D Γ))
    (newWidth : Nat) :
    List (LiteralList D Γ) :=
  (introducedRepresentationResult prior current
    newWidth).representations

end Enumerators

end Synthesis

end Whiel
