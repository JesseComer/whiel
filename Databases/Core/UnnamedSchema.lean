-- Author: Jesse Comer
import Databases.Core.FinRelation
import Mathlib.Data.Fintype.Basic

/-
  This file defines unnamed relational schemas and schema
  extension operations.

  Key definitions include:
    * `UnnamedSchema`
    * `UnnamedSchema.sym`
    * `UnnamedSchema.arity?`
    * `UnnamedSchema.agreeOnArities`
    * `UnnamedSchema.insertFresh`
    * `UnnamedSchema.extensionOf`
    * `UnnamedSchema.restrict`
    * `UnnamedSchema.symOfExtension`
    * `Tuple.toExtension`
-/

------------------------------------------------------------
-- Unnamed Schemas
------------------------------------------------------------

/-
  An unnamed schema is a finite set of relation names with
  an arity assignment on exactly those names.
-/
structure UnnamedSchema
    (A : Type) [RelationNames A] where
  syms : Finset A
  arity : {s : A // s ∈ syms} → Nat

namespace UnnamedSchema

variable {A : Type} {_ : RelationNames A}

/- Checked view of a raw name as a schema symbol. -/
def sym
    (Γ : UnnamedSchema A)
    (X : A)
    (h : X ∈ Γ.syms := by decide) :
    Γ.syms :=
  ⟨X, h⟩

/-
  Partial arity lookup in a schema. Returns `none` for
  names outside `Γ.syms`.
-/
def arity?
    (Γ : UnnamedSchema A)
    (s : A) : Option Nat :=
  if h : s ∈ Γ.syms then
    some (Γ.arity ⟨s, h⟩)
  else
    none

end UnnamedSchema

------------------------------------------------------------
-- Arity Agreement
------------------------------------------------------------

namespace UnnamedSchema

variable {A : Type} {_ : RelationNames A}

/-
  Two schemas agree on arities over a finite set of raw
  relation names when their partial arity lookups agree
  there.
-/
def agreeOnArities
    (Γ : UnnamedSchema A)
    (S : Finset A)
    (Δ : UnnamedSchema A) : Prop :=
  ∀ X, X ∈ S → Γ.arity? X = Δ.arity? X

instance
    (Γ Δ : UnnamedSchema A)
    (S : Finset A) :
    Decidable (Γ.agreeOnArities S Δ) := by
  dsimp [UnnamedSchema.agreeOnArities]
  infer_instance

/- Arity agreement is reflexive. -/
theorem agreeOnArities_refl
    (Γ : UnnamedSchema A)
    (S : Finset A) :
    Γ.agreeOnArities S Γ := by
  intro X _hr
  rfl

/- Arity agreement is symmetric. -/
theorem agreeOnArities_symm
    {Γ Δ : UnnamedSchema A}
    {S : Finset A}
    (hAgree : Γ.agreeOnArities S Δ) :
    Δ.agreeOnArities S Γ := by
  intro X hX
  exact (hAgree X hX).symm

/- Arity agreement on `S` implies agreement on subsets. -/
theorem agreeOnArities_of_subset
    {Γ Δ : UnnamedSchema A}
    {S T : Finset A}
    (hSub : T ⊆ S)
    (hAgree : Γ.agreeOnArities S Δ) :
    Γ.agreeOnArities T Δ := by
  intro X hX
  exact hAgree X (hSub hX)

end UnnamedSchema

------------------------------------------------------------
-- Fresh Symbol Insertion
------------------------------------------------------------

namespace UnnamedSchema

variable {A : Type} {_ : RelationNames A}

/-
  Extend a schema by one fresh relation name with
  arity `n`.
-/
def insertFresh
    (Γ : UnnamedSchema A)
    (X : A)
    (n : Nat)
    (_hFresh : X ∉ Γ.syms) :
    UnnamedSchema A where
  syms := insert X Γ.syms
  arity := fun Y =>
    if hY : Y.1 = X then
      n
    else
      Γ.arity
        ⟨Y.1, by
          have hMem := Y.2
          exact
            (Finset.mem_insert.mp hMem).resolve_left hY⟩

/- The inserted name belongs to the extended schema. -/
def insertedSym
    (Γ : UnnamedSchema A)
    (X : A)
    (n : Nat)
    (hFresh : X ∉ Γ.syms) :
    (Γ.insertFresh X n hFresh).syms :=
  ⟨X, by simp [insertFresh]⟩

/- The inserted name has the requested arity. -/
@[simp] theorem arity_insertedSym
    (Γ : UnnamedSchema A)
    (X : A)
    (n : Nat)
    (hFresh : X ∉ Γ.syms) :
    (Γ.insertFresh X n hFresh).arity
        (Γ.insertedSym X n hFresh) = n := by
  simp [insertedSym, insertFresh]

end UnnamedSchema

------------------------------------------------------------
-- Schema Extensions And Restrictions
------------------------------------------------------------

namespace UnnamedSchema

variable {A : Type} {_ : RelationNames A}

/-
  `Δ.extensionOf Γ` means `Δ` contains all relation names
  of `Γ` and agrees with `Γ` on their arities.
-/
def extensionOf
    (Δ Γ : UnnamedSchema A) : Prop :=
  Γ.syms ⊆ Δ.syms ∧
    ∀ s : Γ.syms, Δ.arity? s.1 = some (Γ.arity s)

instance
    (Δ Γ : UnnamedSchema A) :
    Decidable (Δ.extensionOf Γ) := by
  dsimp [UnnamedSchema.extensionOf]
  infer_instance

/-
  Extending by one fresh symbol preserves all old
  symbols.
-/
theorem insertFresh_extensionOf
    (Γ : UnnamedSchema A)
    (X : A)
    (n : Nat)
    (hFresh : X ∉ Γ.syms) :
    (Γ.insertFresh X n hFresh).extensionOf Γ := by
  refine ⟨?_, ?_⟩
  · intro Y hY
    simp [insertFresh, hY]
  · intro Y
    have hNe : Y.1 ≠ X := by
      intro hEq
      exact hFresh (by simpa [hEq] using Y.2)
    simp [arity?, insertFresh, hNe, Y.2]

/-
  `Γ.restrictionOf Δ` means `Γ` is a restriction of `Δ`.
-/
def restrictionOf
    (Γ Δ : UnnamedSchema A) : Prop :=
  Δ.extensionOf Γ

instance
    (Γ Δ : UnnamedSchema A) :
    Decidable (Γ.restrictionOf Δ) := by
  dsimp [UnnamedSchema.restrictionOf]
  infer_instance

/- Restrict `Δ` to a smaller name set `S`. -/
def restrict
    (Δ : UnnamedSchema A)
    (S : Finset A)
    (hS : S ⊆ Δ.syms) : UnnamedSchema A where
  syms := S
  arity := fun s => Δ.arity ⟨s.1, hS s.2⟩

/-
  The original schema extends each of its restrictions.
-/
theorem extensionOf_restrict
    (Δ : UnnamedSchema A)
    (S : Finset A)
    (hS : S ⊆ Δ.syms) :
    Δ.extensionOf (restrict Δ S hS) := by
  refine ⟨hS, ?_⟩
  intro s
  simp [arity?, restrict, hS s.2]

/-
  If `Δ.extensionOf Γ`, then arities agree on every symbol
  in `Γ`.
-/
theorem arity_eq_of_extensionOf
    {Γ Δ : UnnamedSchema A}
    (hExt : Δ.extensionOf Γ)
    (s : Γ.syms) :
    Δ.arity ⟨s.1, hExt.1 s.2⟩ = Γ.arity s := by
  have hs := hExt.2 s
  unfold arity? at hs
  simpa [hExt.1 s.2] using hs

/- Reflexive extension witness for any schema. -/
theorem extensionOf_refl
    (Γ : UnnamedSchema A) :
    Γ.extensionOf Γ := by
  refine ⟨subset_rfl, ?_⟩
  intro s
  simp [UnnamedSchema.arity?]

/- Schema extension is transitive. -/
theorem extensionOf_trans
    {Γ Δ Θ : UnnamedSchema A}
    (hΘΔ : Θ.extensionOf Δ)
    (hΔΓ : Δ.extensionOf Γ) :
    Θ.extensionOf Γ := by
  refine ⟨?_, ?_⟩
  · intro X hX
    exact hΘΔ.1 (hΔΓ.1 hX)
  · intro X
    have hArΘΔ :=
      UnnamedSchema.arity_eq_of_extensionOf
        hΘΔ ⟨X.1, hΔΓ.1 X.2⟩
    have hArΔΓ :=
      UnnamedSchema.arity_eq_of_extensionOf hΔΓ X
    unfold UnnamedSchema.arity?
    simp [hΘΔ.1 (hΔΓ.1 X.2), hArΘΔ, hArΔΓ]

/-
  An extension that adds no symbol is the schema itself.
  This is schema extensionality in the only form the
  definition supports: the symbol sets coincide and the
  extension witness already forces the arities to agree.
-/
theorem eq_of_extensionOf_of_syms_subset
    {Γ Δ : UnnamedSchema A}
    (hExt : Δ.extensionOf Γ)
    (hSub : Δ.syms ⊆ Γ.syms) :
    Δ = Γ := by
  obtain ⟨hSup, hAr⟩ := hExt
  have hSyms : Δ.syms = Γ.syms :=
    Finset.Subset.antisymm hSub hSup
  obtain ⟨sΔ, aΔ⟩ := Δ
  obtain ⟨sΓ, aΓ⟩ := Γ
  simp only at hSyms
  subst hSyms
  congr 1
  funext s
  have h := hAr s
  simp [UnnamedSchema.arity?, s.2] at h
  exact h

instance
    (Γ : UnnamedSchema A) :
    Fact (Γ.extensionOf Γ) :=
  ⟨extensionOf_refl Γ⟩

end UnnamedSchema

------------------------------------------------------------
-- Extension Symbol Transport
------------------------------------------------------------

namespace UnnamedSchema

variable {A : Type} {_ : RelationNames A}

/- View a schema symbol inside an extension schema. -/
def symOfExtension
    {Γ Δ : UnnamedSchema A}
    (hExt : Δ.extensionOf Γ)
    (X : Γ.syms) :
    Δ.syms :=
  ⟨X.1, hExt.1 X.2⟩

/-
  If `Δ` extends `Γ`, and a symbol of `Δ` also belongs to
  `Γ`, then the two arity lookups agree.
-/
theorem arity_eq_of_extension_mem
    {Γ Δ : UnnamedSchema A}
    (hExt : Δ.extensionOf Γ)
    (X : Δ.syms)
    (hX : X.1 ∈ Γ.syms) :
    Γ.arity ⟨X.1, hX⟩ = Δ.arity X := by
  have hExtAr :=
    arity_eq_of_extensionOf hExt ⟨X.1, hX⟩
  have hEq :
      (⟨X.1, hExt.1 hX⟩ : Δ.syms) = X := by
    exact Subtype.ext rfl
  simpa [hEq] using hExtAr.symm

end UnnamedSchema

------------------------------------------------------------
-- Tuple Transport Across Schema Extensions
------------------------------------------------------------

namespace Tuple

variable {A D : Type}
variable {_ : RelationNames A}
variable {Γ Δ : UnnamedSchema A}

/-
  Transport a tuple to the corresponding arity in an
  extension schema.
-/
def toExtension
    (hExt : Δ.extensionOf Γ)
    (X : Γ.syms)
    (t : Tuple D (Γ.arity X)) :
    Tuple D
      (Δ.arity (UnnamedSchema.symOfExtension hExt X)) :=
  cast
    (congrArg (Tuple D)
      (UnnamedSchema.arity_eq_of_extensionOf hExt X).symm)
    t

end Tuple
