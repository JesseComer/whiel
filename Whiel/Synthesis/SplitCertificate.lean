-- Author: Jesse Comer
import Whiel.Synthesis.Correspondence
import Whiel.Vampire.CandidateVerification

/-
  Split-certificate assembly.

  A published validity certificate discharges one small
  obligation per core clause instead of three monolithic
  ones: per-clause initialization, per-clause step under the
  whole candidate, and whole-candidate termination. This
  module holds the one generic assembly theorem turning
  those per-obligation validity facts into the source Hoare
  triple.

  The per-obligation `QFEntailment.Valid` hypotheses are the
  stable interface for the tiered reconstruction ladder:
  today a certificate produces each one from a declared
  trust axiom through
  `QFEntailment.valid_of_noEmpty_and_toFOLWithSupportAxioms`;
  a reconstruction upgrade later replaces one same-name
  declaration per obligation and nothing else changes.
-/

------------------------------------------------------------
-- Per-Clause Assembly
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace SplitCertificate

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable {Γ : UnnamedSchema A}
variable {inputPre inputPost : AssertExpr D Γ}
variable {inputCmd : Cmd D Γ}

/- Per-clause validity assembles the source Hoare triple. -/
theorem hoareValid_of_perClause
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (clauses : List (Clause D P.outSchema))
    (hInit :
      ∀ clause ∈ clauses,
        (ClauseObligation.init P clause).Valid)
    (hStep :
      ∀ clause ∈ clauses,
        (ClauseObligation.step P clauses clause).Valid)
    (hTerm :
      (ClauseObligation.termCandidate P clauses).Valid) :
    HoareValid inputPre inputCmd inputPost := by
  apply Hoare.Preproc.valid_of_sufficient P
    (Candidate.denote clauses.toFinset)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · apply
      (Candidate.init_denote_iff P clauses.toFinset).mpr
    intro clause hMember
    exact
      (ClauseObligation.init_valid_iff P clause).mp
        (hInit clause (List.mem_toFinset.mp hMember))
  · apply
      (Candidate.maint_denote_iff P clauses.toFinset).mpr
    intro clause hMember
    exact
      (ClauseObligation.step_valid_iff
        P clauses clause).mp
        (hStep clause (List.mem_toFinset.mp hMember))
  · exact
      (ClauseObligation.termCandidate_valid_iff
        P clauses).mp hTerm

end SplitCertificate

end Synthesis

end Whiel

------------------------------------------------------------
-- Batched Side Conditions And FOL Assembly
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace SplitCertificate

variable {A D : Type}
variable [RelationNameSupply A] [Domain D]
variable [LinearOrder A] [LinearOrder D]
variable {Γ : UnnamedSchema A}
variable [Fintype Γ.syms]
variable {inputPre inputPost : AssertExpr D Γ}
variable {inputCmd : Cmd D Γ}

/-
  One batched boolean check discharges every per-obligation
  empty-domain side condition: a single kernel evaluation
  shares the candidate antecedent across all obligations.
-/
omit [LinearOrder A] [LinearOrder D] in
theorem noEmpty_of_all_mem
    {Ω : UnnamedSchema A}
    (clauses : List (Clause D Ω))
    (check : Clause D Ω → QFEntailment (D := D) Ω)
    (hAll :
      (clauses.all fun clause =>
        !(check clause).emptyCounterexample?) = true)
    {clause : Clause D Ω}
    (hMember : clause ∈ clauses) :
    (check clause).toRelCalcEntailment
      |>.NoEmptyCounterexample := by
  have hCheck := List.all_eq_true.mp hAll clause hMember
  have hFalse :
      (check clause).emptyCounterexample? = false := by
    simpa using hCheck
  exact
    (QFEntailment.emptyCounterexample?_eq_false_iff
      (check clause)).mp hFalse

/-
  Package maintenance FOL facts behind a named boundary so
  concrete certificates do not normalize every step
  obligation while matching an assembly theorem.
-/
structure MaintFOLFacts
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (clauses : List (Clause D P.outSchema)) : Prop where
  valid :
    ∀ clause ∈ clauses,
      FOL.SentenceEntailment.Valid (D := D)
        ((ClauseObligation.step P clauses
          clause).toRelCalcEntailment
            |>.toFOLWithSupportAxioms)

/-
  The certificate-facing assembly: three batched boolean
  side conditions plus one FOL-validity fact per obligation
  give the source Hoare triple. The FOL hypotheses are the
  tier ladder's interface; certificates instantiate them
  from declared trust axioms today and from reconstructed
  proofs later, one same-name declaration at a time.
-/
omit [Fintype Γ.syms] in
theorem hoareValid_of_perClause_fol
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (clauses : List (Clause D P.outSchema))
    (hInitNoEmpty :
      (clauses.all fun clause =>
        !(ClauseObligation.init P
          clause).emptyCounterexample?) = true)
    (hStepNoEmpty :
      (clauses.all fun clause =>
        !(ClauseObligation.step P clauses
          clause).emptyCounterexample?) = true)
    (hTermNoEmpty :
      (ClauseObligation.termCandidate P
        clauses).emptyCounterexample? = false)
    (hInitFOL :
      ∀ clause ∈ clauses,
        FOL.SentenceEntailment.Valid (D := D)
          ((ClauseObligation.init P
            clause).toRelCalcEntailment
              |>.toFOLWithSupportAxioms))
    (hStepFOL :
      ∀ clause ∈ clauses,
        FOL.SentenceEntailment.Valid (D := D)
          ((ClauseObligation.step P clauses
            clause).toRelCalcEntailment
              |>.toFOLWithSupportAxioms))
    (hTermFOL :
      FOL.SentenceEntailment.Valid (D := D)
        ((ClauseObligation.termCandidate P
          clauses).toRelCalcEntailment
            |>.toFOLWithSupportAxioms)) :
    HoareValid inputPre inputCmd inputPost := by
  apply hoareValid_of_perClause P clauses
  · intro clause hMember
    exact
      QFEntailment.valid_of_noEmpty_and_toFOLWithSupportAxioms
        _
        (noEmpty_of_all_mem clauses _ hInitNoEmpty hMember)
        (hInitFOL clause hMember)
  · intro clause hMember
    exact
      QFEntailment.valid_of_noEmpty_and_toFOLWithSupportAxioms
        _
        (noEmpty_of_all_mem clauses _ hStepNoEmpty hMember)
        (hStepFOL clause hMember)
  · exact
      QFEntailment.valid_of_noEmpty_and_toFOLWithSupportAxioms
        _
        ((QFEntailment.emptyCounterexample?_eq_false_iff
          _).mp hTermNoEmpty)
        hTermFOL

/-
  Assemble through the named maintenance boundary while
  preserving the direct theorem for existing callers.
-/
omit [Fintype Γ.syms] in
theorem hoareValid_of_perClause_fol_with_maint
    (P : Hoare.Preproc inputPre inputCmd inputPost)
    (clauses : List (Clause D P.outSchema))
    (hInitNoEmpty :
      (clauses.all fun clause =>
        !(ClauseObligation.init P
          clause).emptyCounterexample?) = true)
    (hStepNoEmpty :
      (clauses.all fun clause =>
        !(ClauseObligation.step P clauses
          clause).emptyCounterexample?) = true)
    (hTermNoEmpty :
      (ClauseObligation.termCandidate P
        clauses).emptyCounterexample? = false)
    (hInitFOL :
      ∀ clause ∈ clauses,
        FOL.SentenceEntailment.Valid (D := D)
          ((ClauseObligation.init P
            clause).toRelCalcEntailment
              |>.toFOLWithSupportAxioms))
    (hMaintFOL : MaintFOLFacts P clauses)
    (hTermFOL :
      FOL.SentenceEntailment.Valid (D := D)
        ((ClauseObligation.termCandidate P
          clauses).toRelCalcEntailment
            |>.toFOLWithSupportAxioms)) :
    HoareValid inputPre inputCmd inputPost := by
  exact hoareValid_of_perClause_fol P clauses
    hInitNoEmpty hStepNoEmpty hTermNoEmpty hInitFOL
    hMaintFOL.valid hTermFOL

end SplitCertificate

end Synthesis

end Whiel
