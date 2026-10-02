-- Author: Jesse Comer
import Whiel.Synthesis.DisjunctiveClause.Coverage

/-
  Stable semantic contract for replaceable fast
  disjunctive-clause enumerators.

  The contract constrains only eventual finite-prefix
  coverage. An implementation may emit additional typed
  QF assertions and may use different stages or orders.

  Main declarations:
    * `FastEnumerator.CoversReference`
    * `FastEnumerator.fast_eventual_qf_witness_completeness`
-/

------------------------------------------------------------
-- Finite-Prefix Reference Coverage
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace DisjunctiveClause

namespace FastEnumerator

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}
variable [LinearOrder A] [LinearOrder D]

/-
  Every finite reference proposal is simultaneously
  covered, up to semantic equivalence, by one finite fast
  prefix.
-/
def CoversReference
    (alphabet : Alphabet D Γ)
    (outputThrough : Nat → List (QFAssertExpr D Γ)) : Prop :=
  ∀ parameters, ∃ fastStage, ∀ formula,
    formula ∈ proposalFor alphabet parameters →
      ∃ emitted,
        emitted ∈ outputThrough fastStage ∧
          QFAssertExpr.equiv emitted formula

------------------------------------------------------------
-- Transferred Witness Completeness
------------------------------------------------------------

variable {A' D' : Type}
variable [RelationNameSupply A'] [Domain D']
variable {Γ' : UnnamedSchema A'}
variable [LinearOrder A'] [LinearOrder D']
variable {inputPre inputPost : AssertExpr D' Γ'}
variable {inputCmd : Cmd D' Γ'}

/-
  Reference coverage transfers the QF witness guarantee to
  any fast enumerator. Extra emitted clauses are permitted;
  the finite sufficient subcandidate is selected from one
  covered output prefix.
-/
theorem fast_eventual_qf_witness_completeness
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (witness : QFAssertExpr D' P.outSchema)
    (outputThrough : Nat → List (QFAssertExpr D' P.outSchema))
    (hCovers :
      CoversReference (Alphabet.ofPreproc P) outputThrough)
    (hConstants :
      witness.constants ⊆ programConstants P)
    (hSufficient :
      Assertion.IsSufficientFor P witness.eval) :
    ∃ fastStage, ∃ fastCandidate : Candidate D' P.outSchema,
      (∀ clause ∈ fastCandidate,
        clause ∈ outputThrough fastStage) ∧
      Assertion.equiv fastCandidate.denote witness.eval ∧
      Candidate.IsSufficientFor P fastCandidate := by
  classical
  rcases
      CNF.eventual_qf_witness_completeness P witness
        referenceParameters referenceParameters_isCofinal
          hConstants hSufficient with
    ⟨referenceStage, hReference⟩
  have hAtStage :=
    hReference referenceStage (Nat.le_refl _)
  rcases
      hCovers (referenceParameters referenceStage) with
    ⟨fastStage, hCovered⟩
  let fastCandidate : Candidate D' P.outSchema :=
    (outputThrough fastStage).toFinset.filter fun emitted =>
      ∃ reference ∈ CNF.canonicalCandidate witness,
        QFAssertExpr.equiv emitted reference
  have hDenote :
      Assertion.equiv fastCandidate.denote
        (CNF.canonicalCandidate witness).denote := by
    constructor
    · intro I hFast reference hReferenceMember
      have hProposalMember :=
        hAtStage.1 hReferenceMember
      rcases hCovered reference hProposalMember with
        ⟨emitted, hEmitted, hEquiv⟩
      have hFastMember : emitted ∈ fastCandidate := by
        apply Finset.mem_filter.mpr
        exact
          ⟨List.mem_toFinset.mpr hEmitted,
            reference, hReferenceMember, hEquiv⟩
      exact hEquiv.1 I (hFast emitted hFastMember)
    · intro I hReference emitted hEmitted
      rcases Finset.mem_filter.mp hEmitted with
        ⟨_, reference, hReferenceMember, hEquiv⟩
      exact hEquiv.2 I
        (hReference reference hReferenceMember)
  have hWitness :=
    CNF.canonicalCandidate_denote_equiv witness
  have hFastWitness :
      Assertion.equiv fastCandidate.denote witness.eval :=
    ⟨fun I hFast => hWitness.1 I (hDenote.1 I hFast),
      fun I hInput => hDenote.2 I (hWitness.2 I hInput)⟩
  refine ⟨fastStage, fastCandidate, ?_, hFastWitness, ?_⟩
  · intro clause hClause
    exact List.mem_toFinset.mp
      (Finset.mem_filter.mp hClause).1
  · exact
      (Assertion.isSufficientFor_congr P hDenote).mpr
        hAtStage.2

end FastEnumerator

end DisjunctiveClause

end Synthesis

end Whiel
