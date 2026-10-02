-- Author: Jesse Comer
import Databases.FOL.Semantics

/-
  FOL sentence entailments.

  Key declarations:
    * `FOL.Sentence.conjoin`
    * `FOL.SentenceEntailment`
    * `FOL.SentenceEntailment.toImplication`
    * `FOL.SentenceEntailment.Valid`
    * `FOL.SentenceEntailment.ValidOn`
-/

------------------------------------------------------------
-- Sentence Conjunctions
------------------------------------------------------------

namespace FOL

namespace Sentence

variable {A F : Type}
variable [RelationNames A]
variable [FunctionNames F]
variable {Λ : Signature A F}

/- Canonical right-associated sentence conjunction. -/
def conjoin :
    List (FOL.Sentence Λ) → FOL.Sentence Λ
| [] =>
    ⟨.top, by
      unfold Formula.IsSentence
      rfl⟩
| φ :: [] => φ
| φ :: ψ :: φs =>
    let rest := conjoin (ψ :: φs)
    ⟨.and φ.1 rest.1, by
      unfold Formula.IsSentence
      rw [Formula.freeVars]
      rw [show φ.1.freeVars = ∅ from φ.2]
      rw [show rest.1.freeVars = ∅ from rest.2]
      rfl⟩

end Sentence

end FOL

------------------------------------------------------------
-- Entailments
------------------------------------------------------------

namespace FOL

structure SentenceEntailment
    {A F : Type}
    [RelationNames A]
    [FunctionNames F]
    (Λ : Signature A F) where
  axioms : List (FOL.Sentence Λ)
  conjecture : FOL.Sentence Λ

namespace SentenceEntailment

variable {A F : Type}
variable [RelationNames A]
variable [FunctionNames F]
variable {Λ : Signature A F}

/- Close an entailment as one implication sentence. -/
def toImplication
    (E : SentenceEntailment Λ) :
    FOL.Sentence Λ :=
  let antecedent := Sentence.conjoin E.axioms
  ⟨.imp antecedent.1 E.conjecture.1, by
    unfold Formula.IsSentence
    rw [Formula.freeVars]
    rw [show antecedent.1.freeVars = ∅
      from antecedent.2]
    rw [show E.conjecture.1.freeVars = ∅
      from E.conjecture.2]
    rfl⟩

end SentenceEntailment

namespace SentenceEntailment

variable {A F D : Type}
variable [RelationNames A]
variable [FunctionNames F]
variable [Domain D]
variable {Λ : Signature A F}

/- Validity relative to a class of finite structures. -/
def ValidOn
    (E : SentenceEntailment Λ)
    (P : FinStruct D Λ → Prop) : Prop :=
  ∀ M : FinStruct D Λ,
    P M →
      (∀ φ ∈ E.axioms, φ.Sat M) →
        E.conjecture.Sat M

/- Ordinary finite-structure validity. -/
def Valid
    (E : SentenceEntailment Λ) : Prop :=
  E.ValidOn (D := D) (fun _ => True)

end SentenceEntailment

end FOL
