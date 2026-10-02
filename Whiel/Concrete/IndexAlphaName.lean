-- Author: Jesse Comer
import Whiel.RelationNames.NameSupply
import Whiel.Concrete.Order
import Mathlib.Data.Prod.Lex

/-
  Concrete relation-name carrier for Whiel examples and
  verification artifacts.

  Key declarations include:
    * `Whiel.Concrete.AlphaString`
    * `Whiel.Concrete.IndexAlphaName`
    * `Whiel.Concrete.IndexAlphaName.next`
    * `RelationNameSupply Whiel.Concrete.IndexAlphaName`

  The intended display convention is:
    * `index `0` displays as the base name;`
    * `index `n + 1` displays as `base_(n+2)`.`

  The successor operation increments the internal index, so
  it sends `base` to `base_2`, and sends `base_n` to
  `base_(n+1)`. This gives the generic Whiel compiler a
  concrete fresh-name stream.
-/

------------------------------------------------------------
-- Alphabetical Base Names
------------------------------------------------------------

namespace Whiel

namespace Concrete

/-
  Strings whose characters are all alphabetical. These are
  used as base names for concrete indexed relation names.
-/
structure AlphaString where
  value : String
  isAlpha : value.toList.all Char.isAlpha = true

namespace AlphaString

instance : DecidableEq AlphaString := by
  intro s t
  cases s with
  | mk sv sh =>
  cases t with
  | mk tv th =>
      by_cases h : sv = tv
      · subst tv
        exact isTrue (by simp)
      · exact isFalse (by
          intro hEq
          cases hEq
          exact h rfl)

/-
  Render an alphabetical base name without string quotes.
-/
def pretty (s : AlphaString) : String :=
  s.value

instance : Repr AlphaString where
  reprPrec s _ := s.pretty

/- Lexicographic order on alphabetical strings. -/
def lexLt : AlphaString → AlphaString → Prop :=
  InvImage stringLexLt AlphaString.value

instance : DecidableRel lexLt := by
  unfold lexLt
  infer_instance

private theorem value_injective :
    Function.Injective AlphaString.value := by
  intro s t h
  cases s with
  | mk sv sh =>
  cases t with
  | mk tv th =>
      simp at h
      subst tv
      rfl

private instance lexLt_isStrictTotalOrder :
    IsStrictTotalOrder AlphaString lexLt := by
  unfold lexLt
  exact invImage_isStrictTotalOrder
    AlphaString.value value_injective

instance : LinearOrder AlphaString :=
  linearOrderOfSTO lexLt

/- Checked construction from a raw string. -/
def ofString? (s : String) : Option AlphaString :=
  if h : s.toList.all Char.isAlpha = true then
    some ⟨s, h⟩
  else
    none

end AlphaString

end Concrete

end Whiel

------------------------------------------------------------
-- Indexed Relation Names
------------------------------------------------------------

namespace Whiel

namespace Concrete

/-
  A concrete relation name with an alphabetical base and a
  natural index.
-/
structure IndexAlphaName where
  baseName : AlphaString
  index : Nat
deriving DecidableEq

namespace IndexAlphaName

/- The base relation name. -/
def base (s : AlphaString) : IndexAlphaName where
  baseName := s
  index := 0

/- The base relation name from a checked string. -/
def baseString
    (s : String)
    (h : s.toList.all Char.isAlpha = true := by decide) :
    IndexAlphaName :=
  base ⟨s, h⟩

/- A suffixed relation name `base_(n+1)`. -/
def numbered
    (s : AlphaString)
    (n : Nat) :
    IndexAlphaName where
  baseName := s
  index := n - 1

/- Render an indexed relation name. -/
def pretty (X : IndexAlphaName) : String :=
  if X.index = 0 then
    X.baseName.pretty
  else
    X.baseName.pretty ++ "_" ++ reprStr (X.index + 1)

instance : Repr IndexAlphaName where
  reprPrec X _ := X.pretty

/- Lexicographic order key: base name first, then index. -/
def orderKey (X : IndexAlphaName) : AlphaString ×ₗ Nat :=
  toLex (X.baseName, X.index)

/- Lexicographic order on indexed relation names. -/
def lexLt : IndexAlphaName → IndexAlphaName → Prop :=
  InvImage (· < ·) orderKey

instance : DecidableRel lexLt := by
  unfold lexLt
  infer_instance

private theorem orderKey_injective :
    Function.Injective orderKey := by
  intro X Y h
  cases X with
  | mk XBase XIndex =>
  cases Y with
  | mk YBase YIndex =>
      change toLex (XBase, XIndex) =
        toLex (YBase, YIndex) at h
      have hPair :
          (XBase, XIndex) = (YBase, YIndex) :=
        congrArg ofLex h
      cases hPair
      rfl

private instance lexLt_isStrictTotalOrder :
    IsStrictTotalOrder IndexAlphaName lexLt := by
  unfold lexLt
  exact invImage_isStrictTotalOrder
    orderKey orderKey_injective

instance : LinearOrder IndexAlphaName :=
  linearOrderOfSTO lexLt

/- Successor on display indexes. -/
def nextIndex (i : Nat) : Nat :=
  i + 1

/- Successor on concrete indexed relation names. -/
def next (X : IndexAlphaName) : IndexAlphaName where
  baseName := X.baseName
  index := nextIndex X.index

/- The successor preserves the base name. -/
@[simp] theorem next_baseName
    (X : IndexAlphaName) :
    (next X).baseName = X.baseName :=
  rfl

/- The successor applies `nextIndex` to the index. -/
@[simp] theorem next_index
    (X : IndexAlphaName) :
    (next X).index = nextIndex X.index :=
  rfl

/- `nextIndex` is injective. -/
theorem nextIndex_injective :
    Function.Injective nextIndex := by
  intro i j hEq
  unfold nextIndex at hEq
  omega

/- The successor operation is injective. -/
theorem next_injective :
    Function.Injective next := by
  intro X Y hEq
  have hBase :
      X.baseName = Y.baseName := by
    have hBaseNext :
        (next X).baseName = (next Y).baseName := by
      rw [hEq]
    simpa [next] using hBaseNext
  have hNextIndex :
      nextIndex X.index = nextIndex Y.index := by
    have hIndexNext :
        (next X).index = (next Y).index := by
      rw [hEq]
    simpa [next] using hIndexNext
  have hIndex :
      X.index = Y.index :=
    nextIndex_injective hNextIndex
  cases X with
  | mk XBase XIndex =>
  cases Y with
  | mk YBase YIndex =>
  simp at hBase hIndex
  subst YBase
  subst YIndex
  rfl

/- Applying `nextIndex` increases rank by one. -/
theorem indexRank_nextIndex
    (i : Nat) :
    nextIndex i = i + 1 := by
  rfl

/-
  Iterated `nextIndex` increases rank by the iterate count.
-/
theorem indexRank_iterate_nextIndex
    (i : Nat)
    (n : Nat) :
    Nat.iterate nextIndex n i = i + n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      rw [indexRank_nextIndex]
      rw [ih]
      omega

/- Iterating `next` iterates `nextIndex` on indexes. -/
theorem iterate_next_index
    (X : IndexAlphaName)
    (n : Nat) :
    (Nat.iterate next n X).index =
      Nat.iterate nextIndex n X.index := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      rw [Function.iterate_succ_apply']
      simp [ih]

/- The `next` operation has no positive cycles. -/
theorem next_acyclic
    (X : IndexAlphaName)
    (n : Nat)
    (hPos : 0 < n) :
    Nat.iterate next n X ≠ X := by
  intro hCycle
  have hIndex :
      Nat.iterate nextIndex n X.index = X.index := by
    rw [← iterate_next_index X n]
    exact congrArg IndexAlphaName.index hCycle
  have hRankEq :
      Nat.iterate nextIndex n X.index = X.index := by
    rw [hIndex]
  have hRankIter :=
    indexRank_iterate_nextIndex X.index n
  rw [hRankEq] at hRankIter
  omega

/-
  The `whielSch!` spelling of an indexed name is its
  `pretty`, which is also its `Repr`; the instance names it
  explicitly so the spelling survives a change of `Repr`.
-/
instance : RelationNameSupply IndexAlphaName where
  decEq := inferInstance
  repr := inferInstance
  spelling := ⟨pretty⟩
  next := next
  next_injective := next_injective
  next_acyclic := next_acyclic

end IndexAlphaName

end Concrete

end Whiel
