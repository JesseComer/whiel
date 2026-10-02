-- Author: Jesse Comer
import Whiel.AssertExpr.Renaming

/-
  Abstract alpha-conversion and freshness specifications
  for Whiel assertions.

  Key definitions include:
    * `Whiel.AssertExpr.AlphaEquivalent`
    * `Whiel.AssertExpr.BoundRenameSpec`
    * `Whiel.AssertExpr.renameBound`
    * `Whiel.AssertExpr.FreshExtension`

  The file fixes the contracts needed by later SP/WP work
  without choosing a concrete fresh-name generator.
-/

------------------------------------------------------------
-- Freshness Specifications
------------------------------------------------------------

namespace Whiel

namespace AssertExpr

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- A raw name absent from the full QF formula. -/
def FormulaFresh
    (X : A)
    (φ : AssertExpr D Γ) : Prop :=
  X ∉ φ.formulaSymbols

/- A raw name absent from the assertion's free schema. -/
def FreeSchemaFresh
    (X : A)
    (_φ : AssertExpr D Γ) : Prop :=
  X ∉ Γ.syms

/- A raw name fresh for an assertion alpha target. -/
def AlphaTargetFresh
    (X : A)
    (φ : AssertExpr D Γ) : Prop :=
  FreeSchemaFresh X φ ∧ FormulaFresh X φ

/- A raw relation name fresh for a schema and set. -/
structure FreshRelationName
    (Γ : UnnamedSchema A)
    (avoid : Finset A)
    (X : A) where
  notInSchema : X ∉ Γ.syms
  notInAvoid : X ∉ avoid

/-
  An extension whose new symbols avoid a specified finite
  set. This is the abstract naming contract for generated
  auxiliary relations.
-/
structure FreshExtension
    (Γ Δ : UnnamedSchema A)
    (avoid : Finset A) where
  extendsSchema : Δ.extensionOf Γ
  avoidsNew :
    ∀ X, X ∈ Δ.syms → X ∉ Γ.syms → X ∉ avoid

end AssertExpr

end Whiel

------------------------------------------------------------
-- Alpha Equivalence
------------------------------------------------------------

namespace Whiel

namespace AssertExpr

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Semantic alpha equivalence over the same free schema. -/
def AlphaEquivalent
    (φ ψ : AssertExpr D Γ) : Prop :=
  ∀ I : Instance D Γ, φ.eval I ↔ ψ.eval I

/- Alpha equivalence is reflexive. -/
theorem AlphaEquivalent.refl
    (φ : AssertExpr D Γ) :
    AlphaEquivalent φ φ := by
  intro I
  rfl

/- Alpha equivalence is symmetric. -/
theorem AlphaEquivalent.symm
    {φ ψ : AssertExpr D Γ}
    (h : AlphaEquivalent φ ψ) :
    AlphaEquivalent ψ φ := by
  intro I
  exact (h I).symm

/- Alpha equivalence is transitive. -/
theorem AlphaEquivalent.trans
    {φ ψ χ : AssertExpr D Γ}
    (h₁ : AlphaEquivalent φ ψ)
    (h₂ : AlphaEquivalent ψ χ) :
    AlphaEquivalent φ χ := by
  intro I
  exact (h₁ I).trans (h₂ I)

/-
  Full alpha-conversion contract: semantics is preserved,
  and the observable syntactic support is unchanged.
-/
structure AlphaConversionSpec
    (φ ψ : AssertExpr D Γ) where
  eval : AlphaEquivalent φ ψ
  freeSymbols : ψ.freeSymbols = φ.freeSymbols
  constants : ψ.constants = φ.constants

end AssertExpr

end Whiel

------------------------------------------------------------
-- Bound Symbol Renaming
------------------------------------------------------------

namespace Whiel

namespace AssertExpr

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Side conditions for renaming a bound full-schema symbol.
  The target is already present in the full schema; a later
  naming pass may create such a target by extension.
-/
structure BoundRenameSpec
    (φ : AssertExpr D Γ)
    (X Y : φ.fullSchema.syms) where
  sourceBound : X.1 ∉ Γ.syms
  targetBound : Y.1 ∉ Γ.syms
  targetFresh : Y.1 ∉ φ.formulaSymbols
  sameArity : φ.fullSchema.arity X = φ.fullSchema.arity Y

/- Rename a bound relation symbol in the QF body. -/
def renameBound
    (φ : AssertExpr D Γ)
    {X Y : φ.fullSchema.syms}
    (h : BoundRenameSpec φ X Y) :
    AssertExpr D Γ where
  fullSchema := φ.fullSchema
  extendsFree := φ.extendsFree
  formula := φ.formula.rename X Y h.sameArity

/-
  Semantic obligation for a concrete bound-symbol rename.
  The obligation is separated from the syntax so later work
  can prove it with the needed witness-transport lemmas.
-/
def BoundRenameCorrect
    (φ : AssertExpr D Γ)
    {X Y : φ.fullSchema.syms}
    (h : BoundRenameSpec φ X Y) : Prop :=
  AlphaEquivalent (φ.renameBound h) φ

/- Bound renaming leaves the full schema unchanged. -/
@[simp] theorem renameBound_fullSchema
    (φ : AssertExpr D Γ)
    {X Y : φ.fullSchema.syms}
    (h : BoundRenameSpec φ X Y) :
    (φ.renameBound h).fullSchema = φ.fullSchema :=
  rfl

/-
  Bound renaming leaves the free-extension proof
  unchanged.
-/
@[simp] theorem renameBound_extendsFree
    (φ : AssertExpr D Γ)
    {X Y : φ.fullSchema.syms}
    (h : BoundRenameSpec φ X Y) :
    (φ.renameBound h).extendsFree = φ.extendsFree :=
  rfl

end AssertExpr

end Whiel
