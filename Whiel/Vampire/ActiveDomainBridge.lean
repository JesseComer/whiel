-- Author: Jesse Comer
import Databases.FOL.ShallowSemantics
import Databases.RelCalc.ToFOL

/-
  This file stages active-domain shallow semantics through
  explicit symbol lists. The bridge consumes the support
  environment directly, preventing generated certificates
  from elaborating canonical sentence satisfaction.
-/

------------------------------------------------------------
-- Active-Domain Shallow Semantics
------------------------------------------------------------

namespace Whiel
namespace Vampire
namespace ActiveDomainBridge

variable {A D ι : Type}
variable [RelationNames A]
variable [Domain D]
variable [LinearOrder A]
variable [LinearOrder D]

/-
  Extract and specialize the active-domain support axiom
  after replacing canonical sorts with explicit lists.
-/
theorem supportAxiomSatOfSortedLists
    (Γ : UnnamedSchema A)
    (E : RelCalc.SentenceEntailment (D := D) Γ)
    (I : FOL.Shallow.Model
      (Λ := Γ.toFOLSignature E.constants) ι)
    (σ : Var → ι)
    {cs : List E.constants}
    {rs : List Γ.syms}
    (hConstants : E.constants.attach.sort = cs)
    (hRelations : Γ.syms.attach.sort = rs)
    (hAxioms :
      ∀ φ ∈ E.toFOLWithSupportAxioms.axioms,
        FOL.Shallow.SentenceSat φ I) :
    FOL.Shallow.Sat
      (.forall_ 0
        (RelCalc.ToFOL.activeDomainFormulaOfLists
          Γ E.constants 0 cs rs))
      I σ := by
  subst cs
  subst rs
  exact
    hAxioms
      (RelCalc.ToFOL.activeDomainSentence
        Γ E.constants)
      (by
        unfold
          RelCalc.SentenceEntailment.toFOLWithSupportAxioms
        unfold RelCalc.ToFOL.supportAxioms
        exact List.mem_append_left _ (by simp))
      σ

end ActiveDomainBridge
end Vampire
end Whiel
