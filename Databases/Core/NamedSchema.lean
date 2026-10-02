-- Author: Jesse Comer
import Databases.Core.Basic
import Mathlib.Data.Finset.Defs

/-
  This file defines named relational schemas.

  Key definitions include:
    * `NamedSchema`
    * `NamedSchema.attrs?`
-/

------------------------------------------------------------
-- Named Schemas
------------------------------------------------------------

/-
  A named schema assigns a finite attribute set to each
  relation name present in the schema.
-/
structure NamedSchema
    (A α : Type)
    [RelationNames A]
    [Attributes α] where
  syms : Finset A
  attrs : {s : A // s ∈ syms} → Finset α

namespace NamedSchema

variable {A α : Type}
variable {_ : RelationNames A}
variable {_ : Attributes α}

/-
  Partial attribute lookup in a named schema. Returns
  `none` outside `Γ.syms`.
-/
def attrs?
    (Γ : NamedSchema A α)
    (s : A) : Option (Finset α) :=
  if h : s ∈ Γ.syms then
    some (Γ.attrs ⟨s, h⟩)
  else
    none

end NamedSchema
