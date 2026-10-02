-- Author: Jesse Comer
import Whiel.Guard.Syntax

/-
  Whiel assertion syntax.

  Key declarations:
    * `QFAssertExpr`
    * `QFAssertExpr.andList`
    * `QFAssertExpr.orList`
    * `AssertExpr`
    * `AssertExpr.ofQF`
    * `AssertExpr.ofFormula`
    * `AssertExpr.freeSymbols`
    * `AssertExpr.NoBoundSymbols`
    * `AssertExpr.toQFOfNoBound`

  The quantifier-free assertion language is the Whiel guard
  language. Full assertions add existential second-order
  relation quantification by extending the free schema.
-/

------------------------------------------------------------
-- Quantifier-Free Assertion Syntax
------------------------------------------------------------

namespace Whiel

/- Assertion-language name for Whiel guards. -/
abbrev QFAssertExpr
    {A : Type} [RelationNames A]
    (D : Type) [Domain D]
    (Γ : UnnamedSchema A) : Type :=
  Guard D Γ

end Whiel

------------------------------------------------------------
-- Quantifier-Free Assertion Syntactic Support
------------------------------------------------------------

namespace Whiel

namespace QFAssertExpr

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Truth as a quantifier-free assertion. -/
abbrev «true» : QFAssertExpr D Γ :=
  Guard.«true»

/- Falsity as a quantifier-free assertion. -/
abbrev «false» : QFAssertExpr D Γ :=
  Guard.«false»

/- Equality between same-arity RA expressions. -/
abbrev eq
    {n : Nat}
    (e₁ e₂ : RAExpr D Γ n) :
    QFAssertExpr D Γ :=
  Guard.eq e₁ e₂

/- Containment between same-arity RA expressions. -/
abbrev subset
    {n : Nat}
    (e₁ e₂ : RAExpr D Γ n) :
    QFAssertExpr D Γ :=
  Guard.subset e₁ e₂

/- Conjunction of quantifier-free assertions. -/
abbrev and
    (φ ψ : QFAssertExpr D Γ) :
    QFAssertExpr D Γ :=
  Guard.and φ ψ

/- Conjoin a list of quantifier-free assertions. -/
def andList :
    List (QFAssertExpr D Γ) → QFAssertExpr D Γ
| [] => QFAssertExpr.«true»
| [φ] => φ
| φ :: φs => QFAssertExpr.and φ (andList φs)

/- Disjunction of quantifier-free assertions. -/
abbrev or
    (φ ψ : QFAssertExpr D Γ) :
    QFAssertExpr D Γ :=
  Guard.or φ ψ

/- Disjoin a list of quantifier-free assertions. -/
def orList :
    List (QFAssertExpr D Γ) → QFAssertExpr D Γ
| [] => QFAssertExpr.«false»
| [φ] => φ
| φ :: φs => QFAssertExpr.or φ (orList φs)

/- Negation of a quantifier-free assertion. -/
abbrev not
    (φ : QFAssertExpr D Γ) :
    QFAssertExpr D Γ :=
  Guard.not φ

/- Reinterpret a QF assertion over an extending schema. -/
abbrev onExtension
    {Δ : UnnamedSchema A}
    (hExt : Δ.extensionOf Γ)
    (φ : QFAssertExpr D Γ) :
    QFAssertExpr D Δ :=
  Guard.onExtension hExt φ

/-
  Relation names occurring in a quantifier-free assertion.
-/
abbrev symbols
    (φ : QFAssertExpr D Γ) :
    Finset A :=
  Guard.symbols φ

/-
  Domain constants occurring in a quantifier-free
  assertion.
-/
abbrev constants
    (φ : QFAssertExpr D Γ) :
    Finset D :=
  Guard.constants φ

/- Derived implication, represented as `¬φ ∨ ψ`. -/
abbrev implies
    (φ ψ : QFAssertExpr D Γ) :
    QFAssertExpr D Γ :=
  Guard.implies φ ψ

/-
  Retyping over an extension does not change the symbol
  set.
-/
@[simp] theorem symbols_onExtension
    {Δ : UnnamedSchema A}
    (hExt : Δ.extensionOf Γ)
    (φ : QFAssertExpr D Γ) :
    (φ.onExtension hExt).symbols = φ.symbols :=
  Guard.symbols_onExtension hExt φ

/- Retyping over an extension does not change constants. -/
@[simp] theorem constants_onExtension
    {Δ : UnnamedSchema A}
    (hExt : Δ.extensionOf Γ)
    (φ : QFAssertExpr D Γ) :
    (φ.onExtension hExt).constants = φ.constants :=
  Guard.constants_onExtension hExt φ

end QFAssertExpr

end Whiel

------------------------------------------------------------
-- Assertion Syntax
------------------------------------------------------------

namespace Whiel

/-
  Assertions over a free schema `Γ`.

  The quantifier-free formula is interpreted over
  `fullSchema`. Existentially bound relation variables are
  exactly the symbols of `fullSchema` not already in `Γ`.
-/
structure AssertExpr
    {A : Type} [RelationNames A]
    (D : Type) [Domain D]
    (Γ : UnnamedSchema A) where
  fullSchema : UnnamedSchema A
  extendsFree : fullSchema.extensionOf Γ
  formula : QFAssertExpr D fullSchema

end Whiel

------------------------------------------------------------
-- Assertion Syntactic Support
------------------------------------------------------------

namespace Whiel

namespace AssertExpr

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- View a QF assertion as a full assertion. -/
def ofQF
    (φ : QFAssertExpr D Γ) :
    AssertExpr D Γ where
  fullSchema := Γ
  extendsFree := UnnamedSchema.extensionOf_refl Γ
  formula := φ

/- Build a full assertion over an explicit extension. -/
def ofFormula
    {Δ : UnnamedSchema A}
    (hExt : Δ.extensionOf Γ)
    (φ : QFAssertExpr D Δ) :
    AssertExpr D Γ where
  fullSchema := Δ
  extendsFree := hExt
  formula := φ

/- Relation names existentially bound by an assertion. -/
def boundSymbols (φ : AssertExpr D Γ) : Finset A :=
  φ.fullSchema.syms \ Γ.syms

/-
  An assertion has no existentially bound relation names.
-/
def NoBoundSymbols
    (φ : AssertExpr D Γ) : Prop :=
  φ.boundSymbols = ∅

/- Quantifier-free assertions bind no relation symbols. -/
theorem ofQF_noBound
    (φ : QFAssertExpr D Γ) :
    (ofQF φ).NoBoundSymbols := by
  simp [ofQF, NoBoundSymbols, boundSymbols]

instance
    (φ : AssertExpr D Γ) :
    Decidable φ.NoBoundSymbols := by
  unfold NoBoundSymbols
  infer_instance

/-
  No-bound assertions have no full-schema symbols outside
  the free schema.
-/
theorem fullSchema_syms_subset_free
    (φ : AssertExpr D Γ)
    (hNo : φ.NoBoundSymbols) :
    φ.fullSchema.syms ⊆ Γ.syms := by
  intro X hX
  by_contra hNot
  have hBound : X ∈ φ.boundSymbols := by
    exact Finset.mem_sdiff.mpr ⟨hX, hNot⟩
  rw [NoBoundSymbols] at hNo
  rw [hNo] at hBound
  exact Finset.notMem_empty X hBound

/-
  The free schema extends the full schema when no bound
  symbols remain.
-/
theorem free_extension_full
    (φ : AssertExpr D Γ)
    (hNo : φ.NoBoundSymbols) :
    Γ.extensionOf φ.fullSchema := by
  constructor
  · exact φ.fullSchema_syms_subset_free hNo
  · intro X
    have hΓ : X.1 ∈ Γ.syms :=
      φ.fullSchema_syms_subset_free hNo X.2
    have hFullLookup :
        φ.fullSchema.arity? X.1 =
          some (φ.fullSchema.arity X) := by
      simp [UnnamedSchema.arity?, X.2]
    have hFreeLookup :
        φ.fullSchema.arity? X.1 =
          some (Γ.arity ⟨X.1, hΓ⟩) := by
      exact φ.extendsFree.2 ⟨X.1, hΓ⟩
    rw [hFullLookup] at hFreeLookup
    injection hFreeLookup with hAr
    simp [UnnamedSchema.arity?, hΓ, hAr]

/-
  Retag the quantifier-free body of a no-bound assertion
  over the free schema.
-/
def toQF
    (φ : AssertExpr D Γ)
    (hNo : φ.NoBoundSymbols) :
    QFAssertExpr D Γ :=
  φ.formula.onExtension (φ.free_extension_full hNo)

/-
  Proof-indexed conversion to a quantifier-free
  assertion.
-/
def toQFOfNoBound
    (φ : AssertExpr D Γ) :
    φ.NoBoundSymbols →
      QFAssertExpr D Γ :=
  φ.toQF

/-
  Relation names occurring in the quantifier-free formula.
-/
def formulaSymbols (φ : AssertExpr D Γ) : Finset A :=
  φ.formula.symbols

/-
  Free formula symbols are the formula symbols already in
  `Γ`.
-/
def freeSymbols (φ : AssertExpr D Γ) : Finset A :=
  φ.formulaSymbols ∩ Γ.syms

/- Domain constants occurring in an assertion. -/
def constants (φ : AssertExpr D Γ) : Finset D :=
  φ.formula.constants

/-
  Erase an assertion's formula to raw guard syntax. The
  raw syntax does not mention the full schema, so two
  assertions over different full schemas still have
  comparable erasures.
-/
def toRaw (φ : AssertExpr D Γ) : RawGuard A D :=
  φ.formula.toRaw

/-
  Equal full schemas and equal raw formulas give equal
  assertions.

  This is the assertion counterpart of `Cmd.eq_of_toRaw_eq`
  and `Guard.eq_of_toRaw_eq`. It splits an assertion
  equality into a schema equality, which is small, and a
  raw-syntax equality on a schema-free type, which carries
  the whole formula and is decidable, so a caller can send
  the formula half to the kernel rather than reducing the
  assertion in the elaborator.
-/
theorem eq_of_toRaw_eq
    {φ ψ : AssertExpr D Γ}
    (hSchema : φ.fullSchema = ψ.fullSchema)
    (hRaw : φ.toRaw = ψ.toRaw) :
    φ = ψ := by
  obtain ⟨Δφ, hφ, gφ⟩ := φ
  obtain ⟨Δψ, hψ, gψ⟩ := ψ
  cases hSchema
  have hGuard : gφ = gψ :=
    Guard.eq_of_toRaw_eq hRaw
  cases hGuard
  rfl

/- A no-bound assertion's full schema is the free schema. -/
theorem fullSchema_eq_of_noBound
    (φ : AssertExpr D Γ)
    (hNo : φ.NoBoundSymbols) :
    φ.fullSchema = Γ :=
  UnnamedSchema.eq_of_extensionOf_of_syms_subset
    φ.extendsFree
    (φ.fullSchema_syms_subset_free hNo)

/-
  Two quantifier-free assertions over the same free schema
  with the same raw formula are equal.

  Every hypothesis is decidable, so the whole obligation
  can be discharged by the kernel: an assertion equality
  never has to be reduced in the elaborator.
-/
theorem eq_of_noBound_toRaw_eq
    {φ ψ : AssertExpr D Γ}
    (hφ : φ.NoBoundSymbols)
    (hψ : ψ.NoBoundSymbols)
    (hRaw : φ.toRaw = ψ.toRaw) :
    φ = ψ :=
  eq_of_toRaw_eq
    ((φ.fullSchema_eq_of_noBound hφ).trans
      (ψ.fullSchema_eq_of_noBound hψ).symm)
    hRaw

end AssertExpr

end Whiel
