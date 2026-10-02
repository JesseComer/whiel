-- Author: Jesse Comer

/-
  This file contains the small shared typeclasses used as
  assumptions on domains and symbol carriers.

  Key definitions include:
    * `Var`
    * `Domain`
    * `Spelling`
    * `RelationNames`
    * `FunctionNames`
    * `Attributes`
-/

------------------------------------------------------------
-- Shared Concepts
------------------------------------------------------------

/- Shared variable identifiers for syntactic languages. -/
abbrev Var := Nat

/-
  A domain is a type equipped with an `Inhabited` instance,
  decidable equality, and a printable representation. The
  `Inhabited` field supplies a distinguished `default : D`.
-/
class Domain (D : Type) where
  [inhabited : Inhabited D]
  [decEq : DecidableEq D]
  [repr : Repr D]

attribute [reducible, instance]
  Domain.inhabited Domain.decEq Domain.repr

/-
  How a carrier's values are spelled in the surface
  notation that reads them back. A rendered name must be
  the exact text the notation parses to that name, so a
  rendered program re-reads to the program it came from.

  This is deliberately separate from `Repr`. `Repr` is the
  structural form solver keys are derived from and that
  committed certificates embed, so it is frozen; a spelling
  is a display convention and may be chosen freely.
-/
class Spelling (A : Type) where
  spell : A → String

/-
  A relation-name carrier has decidable equality, a
  printable representation, and a surface spelling. The
  spelling defaults to the structural representation, which
  is right for carriers whose `Repr` already is their
  notation form.
-/
class RelationNames (A : Type) where
  [decEq : DecidableEq A]
  [repr : Repr A]
  spelling : Spelling A := ⟨fun X => @reprStr A repr X⟩

attribute [reducible, instance]
  RelationNames.decEq RelationNames.repr
  RelationNames.spelling

/- Spell a relation name in its surface notation. -/
abbrev spellName
    {A : Type} [RelationNames A] (X : A) : String :=
  Spelling.spell X

/-
  A function-name carrier has decidable equality and a
  printable representation.
-/
class FunctionNames (F : Type) where
  [decEq : DecidableEq F]
  [repr : Repr F]

attribute [reducible, instance]
  FunctionNames.decEq FunctionNames.repr

/- The empty type supports function-free signatures. -/
instance : FunctionNames Empty where
  decEq := inferInstance
  repr := inferInstance

/- Domain values can serve as names for constant symbols. -/
instance {D : Type} [Domain D] :
    FunctionNames D where
  decEq := inferInstance
  repr := inferInstance

/-
  An attribute-name carrier has decidable equality and a
  printable representation. This is used by named schemas.
-/
class Attributes (α : Type) where
  [decEq : DecidableEq α]
  [repr : Repr α]

attribute [reducible, instance]
  Attributes.decEq Attributes.repr
