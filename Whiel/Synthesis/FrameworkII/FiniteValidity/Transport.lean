-- Author: Jesse Comer
import Databases.RelCalc.Valid
import Whiel.AssertExpr.ToRelCalc

/-
  Framework-II transport for the RelCalc finite-validity
  library. The unrestricted prover checks the translated
  augmented entailment; Lean returns through FOL support
  soundness and discharges every checked RelCalc antecedent.
-/

------------------------------------------------------------
-- Framework-II Library Transport
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FiniteValidity

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable [LinearOrder A]
variable [LinearOrder D]
variable {Gamma : UnnamedSchema A}

open RelCalc.SentenceEntailment

/-
  Discharge checked additional axioms after shallow proof of
  an augmented translated Framework-II entailment, using one
  relation name fresh for the task schema.
-/
theorem valid_of_prependAxioms_shallowValid
    (extras : List (RelCalc.Sentence D Gamma))
    (base : QFEntailment (D := D) Gamma)
    (hFresh : ∃ X : A, X ∉ Gamma.syms)
    (hExtras : ∀ φ ∈ extras, φ.AdomValid)
    (baseNoEmpty :
      base.toRelCalcEntailment.NoEmptyCounterexample)
    (augmentedValid :
      FOL.SentenceEntailment.ShallowValid
        (RelCalc.SentenceEntailment.toFOLWithSupportAxioms
          (base.toRelCalcEntailment.prependAxioms
            extras))) :
    base.Valid := by
  apply QFEntailment.valid_of_toRelCalc base
  apply valid_of_prependAxioms_shallow
    extras base.toRelCalcEntailment hFresh hExtras
  · exact base.toRelCalcEntailment_axioms_domainIndependent
  · exact
      Whiel.QFAssertExpr.toRelCalcSentence_domainIndependent
        base.conjecture
  · exact baseNoEmpty
  · exact augmentedValid

end FiniteValidity
end FrameworkII
end Synthesis
end Whiel
