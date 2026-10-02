-- Author: Jesse Comer
import Databases.Core.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Function.Iterate
import Lean.Elab.Tactic.Omega

/-
  Generic Whiel relation-name supplies.

  Key definitions include:
    * `Whiel.RelationNameSupply`
    * `Whiel.RelationNameSupply.freshName`
    * `Whiel.RelationNameSupply.freshNames`

  Key theorems include:
    * `Whiel.RelationNameSupply.freshName_fresh`
    * `Whiel.RelationNameSupply.freshName_on_chain`
    * `Whiel.RelationNameSupply.freshIndex_least`
    * `Whiel.RelationNameSupply.freshNames_fresh`
    * `Whiel.RelationNameSupply.freshNames_nodup`

  The supply exposes a successor operation on relation
  names.  Starting from `X`, the stream
  `next X`, `next (next X)`, ... gives candidate generated
  names.  Injectivity says two names cannot share the same
  immediate successor, so generated names retain a unique
  predecessor when one exists.  Acyclicity says the stream
  from one name never loops back to that name.  Finite-set
  freshness is obtained by bounded search along this stream.
-/

------------------------------------------------------------
-- Relation-Name Supplies
------------------------------------------------------------

namespace Whiel

/-
  Relation-name carriers equipped with a successor operation
  for generated auxiliary names.  The successor is injective
  and has no positive cycle from any name.
-/
class RelationNameSupply (A : Type)
    extends RelationNames A where
  next : A → A
  next_injective : Function.Injective next
  next_acyclic :
    ∀ X n, 0 < n → Nat.iterate next n X ≠ X

end Whiel

------------------------------------------------------------
-- Chains
------------------------------------------------------------

namespace Whiel

namespace RelationNameSupply

variable {A : Type} [RelationNameSupply A]

/- The `n`th name in the generated chain from `X`. -/
def nameAt
    (X : A)
    (n : Nat) :
    A :=
  Nat.iterate RelationNameSupply.next n X

/- Each generated chain has no repeated names. -/
theorem orbit_injective
    (X : A) :
    Function.Injective (fun n : Nat => nameAt X n) := by
  intro m n hEq
  by_contra hNe
  rcases Nat.lt_or_gt_of_ne hNe with hLt | hGt
  · have hCycle :
        Nat.iterate RelationNameSupply.next (n - m) X = X :=
      Function.iterate_cancel
        (f := RelationNameSupply.next)
        (a := X)
        (m := n)
        (n := m)
        RelationNameSupply.next_injective
        hEq.symm
    exact
      RelationNameSupply.next_acyclic
        X (n - m) (Nat.sub_pos_of_lt hLt) hCycle
  · have hCycle :
        Nat.iterate RelationNameSupply.next (m - n) X = X :=
      Function.iterate_cancel
        (f := RelationNameSupply.next)
        (a := X)
        (m := m)
        (n := n)
        RelationNameSupply.next_injective
        hEq
    exact
      RelationNameSupply.next_acyclic
        X (m - n) (Nat.sub_pos_of_lt hGt) hCycle

end RelationNameSupply

end Whiel

------------------------------------------------------------
-- Bounded Fresh Search
------------------------------------------------------------

namespace Whiel

namespace RelationNameSupply

variable {A : Type} [RelationNameSupply A]

/-
  Search from `start` for at most `fuel` steps, returning
  the first index whose chain name is absent from `avoid`.
-/
def freshIndexFromFuel
    (fuel start : Nat)
    (X : A)
    (avoid : Finset A) :
    Nat :=
  match fuel with
  | 0 => start
  | fuel + 1 =>
      if nameAt X start ∈ avoid then
        freshIndexFromFuel fuel (start + 1) X avoid
      else
        start

/- Bounded search never returns an index before `start`. -/
theorem start_le_freshIndexFromFuel
    (fuel start : Nat)
    (X : A)
    (avoid : Finset A) :
    start ≤ freshIndexFromFuel fuel start X avoid := by
  induction fuel generalizing start with
  | zero =>
      simp [freshIndexFromFuel]
  | succ fuel ih =>
      unfold freshIndexFromFuel
      by_cases hMem : nameAt X start ∈ avoid
      · simp [hMem]
        have hNext := ih (start + 1)
        omega
      · simp [hMem]

/- Bounded search returns within the allotted fuel. -/
theorem freshIndexFromFuel_le_bound
    (fuel start : Nat)
    (X : A)
    (avoid : Finset A) :
    freshIndexFromFuel fuel start X avoid ≤
      start + fuel := by
  induction fuel generalizing start with
  | zero =>
      simp [freshIndexFromFuel]
  | succ fuel ih =>
      unfold freshIndexFromFuel
      by_cases hMem : nameAt X start ∈ avoid
      · simp [hMem]
        have hBound := ih (start + 1)
        omega
      · simp [hMem]

/-
  Every earlier searched index was blocked by `avoid`.
-/
theorem freshIndexFromFuel_least
    {fuel start j : Nat}
    {X : A}
    {avoid : Finset A}
    (hStart : start ≤ j)
    (hLt : j < freshIndexFromFuel fuel start X avoid) :
    nameAt X j ∈ avoid := by
  induction fuel generalizing start j with
  | zero =>
      simp [freshIndexFromFuel] at hLt
      omega
  | succ fuel ih =>
      unfold freshIndexFromFuel at hLt
      by_cases hMem : nameAt X start ∈ avoid
      · have hLtNext :
            j <
              freshIndexFromFuel
                fuel (start + 1) X avoid := by
          simpa [hMem] using hLt
        by_cases hEq : j = start
        · subst hEq
          exact hMem
        · have hStartNext : start + 1 ≤ j := by
            omega
          exact ih hStartNext hLtNext
      · have hLtStart : j < start := by
          simpa [hMem] using hLt
        omega

/-
  If a fresh index appears inside the fuel window, bounded
  search returns a fresh index.
-/
theorem freshIndexFromFuel_fresh
    {fuel start : Nat}
    {X : A}
    {avoid : Finset A}
    (hExists :
      ∃ k,
        start ≤ k ∧
          k < start + fuel ∧
            nameAt X k ∉ avoid) :
    nameAt X (freshIndexFromFuel fuel start X avoid)
        ∉ avoid := by
  induction fuel generalizing start with
  | zero =>
      rcases hExists with ⟨k, hStart, hLt, _hFresh⟩
      simp at hLt
      omega
  | succ fuel ih =>
      unfold freshIndexFromFuel
      by_cases hMem : nameAt X start ∈ avoid
      · rw [if_pos hMem]
        apply ih
        rcases hExists with ⟨k, hStart, hLt, hFresh⟩
        have hNe : k ≠ start := by
          intro hEq
          subst hEq
          exact hFresh hMem
        refine ⟨k, ?_, ?_, hFresh⟩
        · omega
        · omega
      · rw [if_neg hMem]
        exact hMem

end RelationNameSupply

end Whiel

------------------------------------------------------------
-- Finite-Set Freshness
------------------------------------------------------------

namespace Whiel

namespace RelationNameSupply

variable {A : Type} [RelationNameSupply A]

/-
  Some positive chain index is fresh for any finite set.
-/
theorem exists_fresh_index
    (X : A)
    (avoid : Finset A) :
    ∃ k,
      1 ≤ k ∧
        k < 1 + (avoid.card + 1) ∧
          nameAt X k ∉ avoid := by
  by_contra hNone
  have hAll :
      ∀ k,
        1 ≤ k →
          k < 1 + (avoid.card + 1) →
            nameAt X k ∈ avoid := by
    intro k hPos hBound
    by_contra hFresh
    exact hNone ⟨k, hPos, hBound, hFresh⟩
  let generated : Finset A :=
    (Finset.range (avoid.card + 1)).image
      (fun i => nameAt X (i + 1))
  have hSub : generated ⊆ avoid := by
    intro Y hY
    rcases Finset.mem_image.mp hY with ⟨i, hi, hEq⟩
    subst hEq
    have hiLt : i < avoid.card + 1 := by
      simpa using hi
    exact hAll (i + 1) (by omega) (by omega)
  have hInj :
      Function.Injective
        (fun i : Nat => nameAt X (i + 1)) := by
    intro i j hEq
    have hSucc :
        i + 1 = j + 1 :=
      orbit_injective X hEq
    omega
  have hCard :
      generated.card = avoid.card + 1 := by
    simp [generated, Finset.card_image_of_injective,
      hInj]
  have hLe :
      generated.card ≤ avoid.card :=
    Finset.card_le_card hSub
  omega

/- The fuel bound needed to find a fresh generated name. -/
def freshFuel
    (_X : A)
    (avoid : Finset A) :
    Nat :=
  avoid.card + 1

/-
  First positive chain index whose name is absent from
  `avoid`.
-/
def freshIndex
    (X : A)
    (avoid : Finset A) :
    Nat :=
  freshIndexFromFuel (freshFuel X avoid) 1 X avoid

/- The generated name selected by `freshIndex`. -/
def freshName
    (X : A)
    (avoid : Finset A) :
    A :=
  nameAt X (freshIndex X avoid)

/- `freshIndex` is positive. -/
theorem freshIndex_pos
    (X : A)
    (avoid : Finset A) :
    0 < freshIndex X avoid := by
  have hStart :
      1 ≤ freshIndex X avoid := by
    unfold freshIndex freshFuel
    exact start_le_freshIndexFromFuel
      (avoid.card + 1) 1 X avoid
  omega

/- `freshIndex` stays within the finite search bound. -/
theorem freshIndex_le_bound
    (X : A)
    (avoid : Finset A) :
    freshIndex X avoid ≤ 1 + (avoid.card + 1) := by
  unfold freshIndex freshFuel
  exact
    freshIndexFromFuel_le_bound
      (avoid.card + 1) 1 X avoid

/- `freshName` is absent from the avoided names. -/
theorem freshName_fresh
    (X : A)
    (avoid : Finset A) :
    freshName X avoid ∉ avoid := by
  unfold freshName freshIndex freshFuel
  exact freshIndexFromFuel_fresh
    (exists_fresh_index X avoid)

/-
  Every positive chain index before `freshIndex` is present
  in `avoid`.
-/
theorem freshIndex_least
    (X : A)
    (avoid : Finset A)
    {k : Nat}
    (hPos : 1 ≤ k)
    (hLt : k < freshIndex X avoid) :
    nameAt X k ∈ avoid := by
  unfold freshIndex freshFuel at hLt
  exact freshIndexFromFuel_least hPos hLt

/- `freshName` lies on the positive chain from `X`. -/
theorem freshName_on_chain
    (X : A)
    (avoid : Finset A) :
    ∃ k,
      0 < k ∧ freshName X avoid = nameAt X k := by
  exact ⟨freshIndex X avoid,
    freshIndex_pos X avoid, rfl⟩

end RelationNameSupply

end Whiel

------------------------------------------------------------
-- Batch Freshness
------------------------------------------------------------

namespace Whiel

namespace RelationNameSupply

variable {A : Type} [RelationNameSupply A]

/-
  Generate one fresh name for each input name, updating the
  avoid set after every generated name.
-/
def freshNames :
    Finset A → List A → List A
| _avoid, [] => []
| avoid, X :: Xs =>
    let Y := freshName X avoid
    Y :: freshNames (insert Y avoid) Xs

/- Batch generation preserves list length. -/
theorem freshNames_length
    (avoid : Finset A)
    (Xs : List A) :
    (freshNames avoid Xs).length = Xs.length := by
  induction Xs generalizing avoid with
  | nil =>
      simp [freshNames]
  | cons X Xs ih =>
      simp [freshNames, ih]

/- Batch-generated names avoid the original avoid set. -/
theorem freshNames_fresh
    {avoid : Finset A}
    {Xs : List A}
    {Y : A}
    (hY : Y ∈ freshNames avoid Xs) :
    Y ∉ avoid := by
  induction Xs generalizing avoid with
  | nil =>
      simp [freshNames] at hY
  | cons X Xs ih =>
      have hCases :
          Y = freshName X avoid ∨
            Y ∈
              freshNames
                (insert (freshName X avoid) avoid) Xs := by
        simpa [freshNames] using hY
      rcases hCases with hY | hY
      · subst hY
        exact freshName_fresh X avoid
      · have hFresh :
            Y ∉ insert (freshName X avoid) avoid :=
          ih hY
        intro hAvoid
        exact hFresh (Finset.mem_insert.mpr (Or.inr hAvoid))

/- Batch-generated names have no duplicates. -/
theorem freshNames_nodup
    (avoid : Finset A)
    (Xs : List A) :
    (freshNames avoid Xs).Nodup := by
  induction Xs generalizing avoid with
  | nil =>
      simp [freshNames]
  | cons X Xs ih =>
      simp only [freshNames]
      apply List.nodup_cons.mpr
      constructor
      · intro hMem
        have hFresh :
            freshName X avoid ∉
              insert (freshName X avoid) avoid :=
          freshNames_fresh hMem
        exact hFresh (Finset.mem_insert_self _ _)
      · exact ih (insert (freshName X avoid) avoid)

end RelationNameSupply

end Whiel
