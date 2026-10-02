-- Author: Jesse Comer
import Databases.Core.UnnamedSchema

/-
  This file defines first-order signatures and the
  standard expansion from unnamed schemas to signatures
  with nullary function symbols for constants.

  Key definitions include:
    * `Signature`
    * `Signature.Rel`
    * `Signature.Fun`
    * `Signature.func`
    * `Signature.funArity?`
    * `UnnamedSchema.toFOLSignature`
-/

------------------------------------------------------------
-- Signatures
------------------------------------------------------------

/-
  A first-order signature extends an unnamed relational
  schema with a finite set of function symbols and their
  arities.
-/
structure Signature
    (A F : Type)
    [RelationNames A]
    [FunctionNames F]
    extends UnnamedSchema A where
  funs : Finset F
  funArity : {f : F // f ∈ funs} → Nat

namespace Signature

variable {A F : Type}
variable {_ : RelationNames A}
variable {_ : FunctionNames F}

/- The subtype of relation names present in `Λ`. -/
abbrev Rel
    (Λ : Signature A F) : Type :=
  {X : A // X ∈ Λ.syms}

/- The subtype of function names present in `Λ`. -/
abbrev Fun
    (Λ : Signature A F) : Type :=
  {f : F // f ∈ Λ.funs}

/- Checked view of a raw name as a function symbol. -/
def func
    (Λ : Signature A F)
    (f : F)
    (h : f ∈ Λ.funs := by decide) :
    Signature.Fun Λ :=
  ⟨f, h⟩

/- Function arity lookup; `none` outside `Λ`. -/
def funArity?
    (Λ : Signature A F)
    (f : F) : Option Nat :=
  if hf : f ∈ Λ.funs then
    some (Λ.funArity ⟨f, hf⟩)
  else
    none

end Signature

------------------------------------------------------------
-- Schema-To-Signature Expansions
------------------------------------------------------------

namespace UnnamedSchema

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]

/-
  Expand a relational schema with one nullary function
  symbol for each listed constant.
-/
def toFOLSignature
    (Γ : UnnamedSchema A)
    (C : Finset D) :
    Signature A D where
  toUnnamedSchema := Γ
  funs := C
  funArity := fun _ => 0

end UnnamedSchema
