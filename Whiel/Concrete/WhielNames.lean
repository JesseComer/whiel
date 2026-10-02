-- Author: Jesse Comer
import Databases.Core.UnnamedSchema
import Whiel.Concrete.IndexAlphaName

/-
  Concrete relation names for the fixed-ambient Whiel
  schema.

  `ProgramNames` separates user program names from names
  supplied explicitly to auxiliary constructions, and
  reserves flag names for control state introduced by
  preprocessing. Every family retains indexed variants for
  transformations that need them. `WhielNames` then makes
  disjoint ordinary and prophecy copies of those names.

  Only `ProgramNames` has a generic successor supply.
  Prophecy names are selected explicitly, so there is no
  `RelationNameSupply WhielNames` instance.

  Both carriers also fix their surface `Spelling`, the text
  the concrete notation reads back as the same name. A
  spelling is not the derived `Repr`: `Repr` stays the
  structural form that solver keys and committed
  certificates are built from.
-/

------------------------------------------------------------
-- Program Names
------------------------------------------------------------

namespace Whiel

namespace Concrete

/-
  Program-visible, explicitly supplied auxiliary, and
  reserved flag relation names. In every family `index` is
  the snapshot generation, and index zero is the base form.
  A flag's `id` is its identity, never a snapshot index.
-/
inductive ProgramNames : Type
| programSymbol (base : AlphaString) (index : Nat)
| auxiliarySymbol (base : AlphaString) (index : Nat)
| flagSymbol (id index : Nat)
deriving DecidableEq, Repr

namespace ProgramNames

/- The alphabetical base of a non-flag program name. -/
def baseName? : ProgramNames → Option AlphaString
| .programSymbol base _ => some base
| .auxiliarySymbol base _ => some base
| .flagSymbol _ _ => none

/- The internal index of a program name. -/
def index : ProgramNames → Nat
| .programSymbol _ index => index
| .auxiliarySymbol _ index => index
| .flagSymbol _ index => index

/- Whether a program name has its base index. -/
def IsBase (name : ProgramNames) : Prop :=
  name.index = 0

instance (name : ProgramNames) : Decidable name.IsBase :=
  by
    unfold IsBase
    infer_instance

@[simp] theorem isBase_programSymbol
    (base : AlphaString)
    (index : Nat) :
    IsBase (.programSymbol base index) ↔ index = 0 :=
  Iff.rfl

@[simp] theorem isBase_auxiliarySymbol
    (base : AlphaString)
    (index : Nat) :
    IsBase (.auxiliarySymbol base index) ↔ index = 0 :=
  Iff.rfl

@[simp] theorem isBase_flagSymbol
    (id index : Nat) :
    IsBase (.flagSymbol id index) ↔ index = 0 :=
  Iff.rfl

/- Whether a program name is a reserved flag name. -/
def IsFlag : ProgramNames → Prop
| .programSymbol _ _ => False
| .auxiliarySymbol _ _ => False
| .flagSymbol _ _ => True

instance (name : ProgramNames) : Decidable name.IsFlag :=
  by
    cases name <;> unfold IsFlag <;> infer_instance

@[simp] theorem not_isFlag_programSymbol
    (base : AlphaString)
    (index : Nat) :
    ¬ IsFlag (.programSymbol base index) := by
  simp [IsFlag]

@[simp] theorem not_isFlag_auxiliarySymbol
    (base : AlphaString)
    (index : Nat) :
    ¬ IsFlag (.auxiliarySymbol base index) := by
  simp [IsFlag]

@[simp] theorem isFlag_flagSymbol
    (id index : Nat) :
    IsFlag (.flagSymbol id index) :=
  trivial

/-
  Raw input names are program or auxiliary names at base
  index zero. Flags are reserved for preprocessing.
-/
def IsRawInput (name : ProgramNames) : Prop :=
  name.IsBase ∧ ¬ name.IsFlag

instance (name : ProgramNames) :
    Decidable name.IsRawInput :=
  by
    unfold IsRawInput
    infer_instance

@[simp] theorem isRawInput_programSymbol
    (base : AlphaString)
    (index : Nat) :
    IsRawInput (.programSymbol base index) ↔ index = 0 := by
  simp [IsRawInput]

@[simp] theorem isRawInput_auxiliarySymbol
    (base : AlphaString)
    (index : Nat) :
    IsRawInput (.auxiliarySymbol base index) ↔
      index = 0 := by
  simp [IsRawInput]

@[simp] theorem not_isRawInput_flagSymbol
    (id index : Nat) :
    ¬ IsRawInput (.flagSymbol id index) := by
  simp [IsRawInput]

end ProgramNames

end Concrete

end Whiel

------------------------------------------------------------
-- Program-Name Spelling
------------------------------------------------------------

namespace Whiel

namespace Concrete

namespace ProgramNames

/-
  The concrete notation's spelling of one program name.
  Index zero has no suffix, a positive index `n` is written
  `_n`, and an auxiliary name carries `_aux` before any
  index, so `programSch!`, `programAssert!` and
  `programCmd!` read each of these spellings back as the
  name it came from. The same holds of the flag spelling
  below.

  A flag is spelled `flag_id_index`, with both numerals
  canonical and neither suffix elided, so that the flag
  extension a preprocessed program lives over is written in
  the same notation as the rest of it. The form is
  unreachable from a base name: a base is a purely
  alphabetical `AlphaString`, so the three spellings above
  carry at most one numeric suffix, and the only
  three-segment one has the literal middle segment `aux`.
  A flag therefore never collides with a program or
  auxiliary name, whatever its base, including the base
  `flag` itself, whose spellings are `flag`, `flag_n`,
  `flag_aux` and `flag_aux_n`.
-/
def spell : ProgramNames → String
| .programSymbol base 0 => base.pretty
| .programSymbol base index =>
    base.pretty ++ "_" ++ toString index
| .auxiliarySymbol base 0 => base.pretty ++ "_aux"
| .auxiliarySymbol base index =>
    base.pretty ++ "_aux_" ++ toString index
| .flagSymbol id index =>
    "flag_" ++ toString id ++ "_" ++ toString index

end ProgramNames

end Concrete

end Whiel

------------------------------------------------------------
-- Program-Name Supply
------------------------------------------------------------

namespace Whiel

namespace Concrete

namespace ProgramNames

/- Increment an internal program-name index. -/
def next : ProgramNames → ProgramNames
| .programSymbol base index =>
    .programSymbol base (index + 1)
| .auxiliarySymbol base index =>
    .auxiliarySymbol base (index + 1)
| .flagSymbol id index =>
    .flagSymbol id (index + 1)

@[simp] theorem baseName?_next
    (name : ProgramNames) :
    (next name).baseName? = name.baseName? := by
  cases name <;> rfl

@[simp] theorem index_next
    (name : ProgramNames) :
    (next name).index = name.index + 1 := by
  cases name <;> rfl

theorem next_injective :
    Function.Injective next := by
  intro left right hEq
  cases left <;> cases right <;>
    simp_all [next]

@[simp] theorem index_iterate_next
    (name : ProgramNames)
    (count : Nat) :
    (Nat.iterate next count name).index =
      name.index + count := by
  induction count with
  | zero =>
      simp
  | succ count ih =>
      rw [Function.iterate_succ_apply']
      rw [index_next, ih]
      omega

theorem next_acyclic
    (name : ProgramNames)
    (count : Nat)
    (hPositive : 0 < count) :
    Nat.iterate next count name ≠ name := by
  intro hCycle
  have hIndex := congrArg index hCycle
  rw [index_iterate_next] at hIndex
  omega

instance : RelationNameSupply ProgramNames where
  decEq := inferInstance
  repr := inferInstance
  spelling := ⟨spell⟩
  next := next
  next_injective := next_injective
  next_acyclic := next_acyclic

end ProgramNames

end Concrete

end Whiel

------------------------------------------------------------
-- Ordinary and Prophecy Names
------------------------------------------------------------

namespace Whiel

namespace Concrete

/-
  The fixed ambient Whiel carrier. Prophecy is a disjoint
  copy, not a flag encoded into a program-name string.
-/
inductive WhielNames : Type
| ordinary (name : ProgramNames)
| prophecy (name : ProgramNames)
deriving DecidableEq, Repr

namespace WhielNames

/- Forget the ordinary/prophecy constructor. -/
def programName : WhielNames → ProgramNames
| .ordinary name => name
| .prophecy name => name

/- Whether a name belongs to the ordinary copy. -/
def IsOrdinary : WhielNames → Prop
| .ordinary _ => True
| .prophecy _ => False

instance (name : WhielNames) : Decidable name.IsOrdinary :=
  by
    cases name <;> unfold IsOrdinary <;> infer_instance

/-
  Raw input names are ordinary names at base index zero.
-/
def BaseNameOnly : WhielNames → Prop
| .ordinary name => name.IsBase
| .prophecy _ => False

instance (name : WhielNames) :
    Decidable name.BaseNameOnly :=
  by
    cases name <;> unfold BaseNameOnly <;> infer_instance

@[simp] theorem isOrdinary_ordinary
    (name : ProgramNames) :
    IsOrdinary (.ordinary name) :=
  trivial

@[simp] theorem not_isOrdinary_prophecy
    (name : ProgramNames) :
    ¬ IsOrdinary (.prophecy name) := by
  simp [IsOrdinary]

@[simp] theorem baseNameOnly_ordinary
    (name : ProgramNames) :
    BaseNameOnly (.ordinary name) ↔ name.IsBase :=
  Iff.rfl

@[simp] theorem not_baseNameOnly_prophecy
    (name : ProgramNames) :
    ¬ BaseNameOnly (.prophecy name) := by
  simp [BaseNameOnly]

/- Read the underlying name only from the ordinary copy. -/
def ordinaryName? : WhielNames → Option ProgramNames
| .ordinary name => some name
| .prophecy _ => none

/- Read the underlying name only from the prophecy copy. -/
def prophecyName? : WhielNames → Option ProgramNames
| .ordinary _ => none
| .prophecy name => some name

/- Select the matching prophecy of an ordinary name. -/
def prophecyPartner? : WhielNames → Option WhielNames
| .ordinary name => some (.prophecy name)
| .prophecy _ => none

/- Select the matching ordinary of a prophecy name. -/
def ordinaryPartner? : WhielNames → Option WhielNames
| .ordinary _ => none
| .prophecy name => some (.ordinary name)

@[simp] theorem prophecyPartner?_ordinary
    (name : ProgramNames) :
    prophecyPartner? (.ordinary name) =
      some (.prophecy name) :=
  rfl

@[simp] theorem prophecyPartner?_prophecy
    (name : ProgramNames) :
    prophecyPartner? (.prophecy name) = none :=
  rfl

@[simp] theorem ordinaryPartner?_prophecy
    (name : ProgramNames) :
    ordinaryPartner? (.prophecy name) =
      some (.ordinary name) :=
  rfl

@[simp] theorem ordinaryPartner?_ordinary
    (name : ProgramNames) :
    ordinaryPartner? (.ordinary name) = none :=
  rfl

/-
  The concrete notation's spelling of one Whiel name. The
  ordinary copy is spelled as its program name, and the
  prophecy copy carries the postfix `∞`, which is exactly
  what the `WhielNames` style of the notation reads.
-/
def spell : WhielNames → String
| .ordinary name => name.spell
| .prophecy name => name.spell ++ "∞"

end WhielNames

instance : RelationNames WhielNames where
  decEq := inferInstance
  repr := inferInstance
  spelling := ⟨WhielNames.spell⟩

end Concrete

end Whiel

------------------------------------------------------------
-- Ordinary Schema Symbols
------------------------------------------------------------

namespace UnnamedSchema

/- Ordinary symbols present in a fixed ambient schema. -/
def programSymbols
    (Γ : UnnamedSchema Whiel.Concrete.WhielNames) :
    Finset Whiel.Concrete.WhielNames :=
  Γ.syms.filter Whiel.Concrete.WhielNames.IsOrdinary

@[simp] theorem mem_programSymbols
    {Γ : UnnamedSchema Whiel.Concrete.WhielNames}
    {name : Whiel.Concrete.WhielNames} :
    name ∈ Γ.programSymbols ↔
      name ∈ Γ.syms ∧
        Whiel.Concrete.WhielNames.IsOrdinary name := by
  simp [programSymbols]

/-
  Every relation of a raw input schema is a program or
  auxiliary name at index zero; flags are excluded.
-/
def RawIndexZero
    (Γ : UnnamedSchema Whiel.Concrete.ProgramNames) :
    Prop :=
  ∀ X ∈ Γ.syms, X.IsRawInput

instance (Γ : UnnamedSchema Whiel.Concrete.ProgramNames) :
    Decidable Γ.RawIndexZero :=
  by
    unfold RawIndexZero
    infer_instance

end UnnamedSchema
