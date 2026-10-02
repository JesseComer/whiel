-- Author: Jesse Comer
import Whiel.AssertExpr.Semantics

/-
  Entailments for Whiel assertions.

  Key declarations:
    * `AssertExpr.Entailment`
    * `AssertExpr.Entailment.Valid`
    * `QFAssertExpr.entails`
    * `QFAssertExpr.equiv`
    * `QFEntailment`
    * `QFEntailment.Valid`
-/

------------------------------------------------------------
-- AssertExpr Entailments
------------------------------------------------------------

namespace Whiel

namespace AssertExpr

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Entailment between syntactic assertions. -/
def entails
    (pre post : AssertExpr D Γ) : Prop :=
  ∀ I : Instance D Γ,
    pre.eval I → post.eval I

/- A syntactic assertion entailment obligation. -/
structure Entailment
    (D : Type) [Domain D]
    (Γ : UnnamedSchema A) where
  lhs : AssertExpr D Γ
  rhs : AssertExpr D Γ

namespace Entailment

/- Validity of a syntactic assertion entailment. -/
def Valid
    (E : Entailment D Γ) : Prop :=
  E.lhs.entails E.rhs

end Entailment

end AssertExpr

end Whiel

------------------------------------------------------------
-- Direct QF Assertion Relations
------------------------------------------------------------

namespace Whiel

namespace QFAssertExpr

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Semantic entailment between QF assertions. -/
def entails
    (φ ψ : QFAssertExpr D Γ) : Prop :=
  ∀ I : Instance D Γ, φ.eval I → ψ.eval I

/- Semantic equivalence between QF assertions. -/
def equiv
    (φ ψ : QFAssertExpr D Γ) : Prop :=
  entails φ ψ ∧ entails ψ φ

/- QF entailment is reflexive. -/
theorem entails_refl
    (φ : QFAssertExpr D Γ) :
    entails φ φ := by
  intro I hφ
  exact hφ

/- QF entailment is transitive. -/
theorem entails_trans
    {φ ψ χ : QFAssertExpr D Γ}
    (hφψ : entails φ ψ)
    (hψχ : entails ψ χ) :
    entails φ χ := by
  intro I hφ
  exact hψχ I (hφψ I hφ)

/- QF semantic equivalence is reflexive. -/
theorem equiv_refl
    (φ : QFAssertExpr D Γ) :
    equiv φ φ :=
  ⟨entails_refl φ, entails_refl φ⟩

/- QF semantic equivalence is symmetric. -/
theorem equiv_symm
    {φ ψ : QFAssertExpr D Γ}
    (h : equiv φ ψ) :
    equiv ψ φ :=
  ⟨h.2, h.1⟩

/- QF semantic equivalence is transitive. -/
theorem equiv_trans
    {φ ψ χ : QFAssertExpr D Γ}
    (hφψ : equiv φ ψ)
    (hψχ : equiv ψ χ) :
    equiv φ χ :=
  ⟨entails_trans hφψ.1 hψχ.1,
    entails_trans hψχ.2 hφψ.2⟩

/- Equivalence is pointwise equivalence of evaluation. -/
theorem equiv_iff_eval_iff
    (φ ψ : QFAssertExpr D Γ) :
    equiv φ ψ ↔
      ∀ I : Instance D Γ, φ.eval I ↔ ψ.eval I := by
  constructor
  · intro h I
    exact ⟨h.1 I, h.2 I⟩
  · intro h
    exact
      ⟨fun I => (h I).mp,
       fun I => (h I).mpr⟩

/- Entailment into a conjunction is pointwise. -/
theorem entails_andList_iff
    (φ : QFAssertExpr D Γ)
    (ψs : List (QFAssertExpr D Γ)) :
    entails φ (andList ψs) ↔
      ∀ ψ ∈ ψs, entails φ ψ := by
  constructor
  · intro h ψ hMem I hφ
    exact (andList_eval_iff ψs I).mp
      (h I hφ) ψ hMem
  · intro h I hφ
    apply (andList_eval_iff ψs I).mpr
    intro ψ hMem
    exact h ψ hMem I hφ

/- A conjunction entails each of its members. -/
theorem andList_entails_of_mem
    {φ : QFAssertExpr D Γ}
    {φs : List (QFAssertExpr D Γ)}
    (hMem : φ ∈ φs) :
    entails (andList φs) φ := by
  intro I hφs
  exact (andList_eval_iff φs I).mp hφs φ hMem

end QFAssertExpr

end Whiel

------------------------------------------------------------
-- QF Assertion Entailment Obligations
------------------------------------------------------------

structure QFEntailment
    {A D : Type}
    [RelationNames A]
    [Domain D]
    (Γ : UnnamedSchema A) where
  axioms : List (Whiel.QFAssertExpr D Γ)
  conjecture : Whiel.QFAssertExpr D Γ

namespace QFEntailment

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- Constants occurring in a list of QF assertions. -/
def formulaListConstants :
    List (Whiel.QFAssertExpr D Γ) → Finset D
| [] => ∅
| φ :: φs => φ.constants ∪ formulaListConstants φs

/- All constants occurring in a QF entailment. -/
def constants
    (E : QFEntailment (D := D) Γ) : Finset D :=
  formulaListConstants E.axioms ∪ E.conjecture.constants

/- Source QF entailment validity over all instances. -/
def Valid
    (E : QFEntailment (D := D) Γ) : Prop :=
  ∀ I : Instance D Γ,
    (∀ φ ∈ E.axioms, φ.eval I) →
      E.conjecture.eval I

/- List-axiom validity is conjunction entailment. -/
theorem valid_iff_andList_entails
    (E : QFEntailment (D := D) Γ) :
    E.Valid ↔
      (Whiel.QFAssertExpr.andList E.axioms).entails
        E.conjecture := by
  constructor
  · intro h I hAxioms
    apply h I
    exact
      (Whiel.QFAssertExpr.andList_eval_iff
        E.axioms I).mp hAxioms
  · intro h I hAxioms
    apply h I
    exact
      (Whiel.QFAssertExpr.andList_eval_iff
        E.axioms I).mpr hAxioms

end QFEntailment
