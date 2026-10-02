-- Author: Jesse Comer
import Whiel.Synthesis.Correspondence
import Whiel.Synthesis.SplitCertificate
import Whiel.Synthesis.DisjunctiveClause.Coverage
import Whiel.Synthesis.Enumerators.BaseSlice.Enumeration
import Whiel.Synthesis.Enumerators.Fast.Freshness
import Whiel.Synthesis.DisjunctiveClause.Subsumption
import Whiel.Synthesis.WLayer.Enumeration
import Whiel.Synthesis.Runtime.FastProposal
import Whiel.Synthesis.Runtime.SeededProposal
import Whiel.Synthesis.Runtime.CappedProposal
import Whiel.Synthesis.Runtime.ReferenceProposal
import Whiel.Synthesis.Runtime.Task
import Whiel.Vampire.StableEncoding
import Whiel.Hoare.Preproc
import Whiel.Synthesis.Enumerators.Seeded.Freshness
import Whiel.Eval.CounterExample.Kernel
import Whiel.Synthesis.Runtime.RealizationRegistry
import Databases.RelCalc.Valid

/-
  Manual axiom audit for the synthesis semantic spine and
  the current clause-class slices.
-/

open Whiel.Synthesis
open Whiel.Synthesis.Enumerators
open DisjunctiveClause
open DisjunctiveClause.LiteralList
open Whiel.Synthesis.Enumerators.BaseSlice
open DisjunctiveClause.FullEnumeration

#print axioms
  Whiel.Synthesis.Candidate.denote_entails_of_mem
#print axioms
  Whiel.Synthesis.Candidate.init_denote_iff
#print axioms
  Whiel.Synthesis.Candidate.step_denote_iff
#print axioms
  Whiel.Synthesis.Candidate.maint_denote_iff
#print axioms Whiel.Assertion.init_congr
#print axioms Whiel.Assertion.step_congr
#print axioms Whiel.Assertion.maint_congr
#print axioms
  Whiel.Assertion.isInductiveFor_congr
#print axioms Whiel.Assertion.term_congr
#print axioms
  Whiel.Assertion.isSufficientFor_congr
#print axioms
  ClauseObligation.materialize_eval_iff_denote
#print axioms
  ClauseObligation.materialize_equiv_denote
#print axioms
  ClauseObligation.materialize_equiv_of_toFinset_eq
#print axioms
  Whiel.QFInvariantObligation.conversion_valid_iff
#print axioms
  Whiel.QFInvariantObligation.init_valid_iff
#print axioms
  Whiel.QFInvariantObligation.step_valid_iff
#print axioms
  Whiel.QFInvariantObligation.term_valid_iff
#print axioms
  Whiel.Synthesis.ClauseObligation.init_valid_iff
#print axioms
  Whiel.Synthesis.ClauseObligation.initCandidate_valid_iff
#print axioms
  Whiel.Synthesis.ClauseObligation.step_valid_iff
#print axioms
  ClauseObligation.maintCandidate_valid_iff
#print axioms
  ClauseObligation.termCandidate_valid_iff
#print axioms
  Whiel.Synthesis.SplitCertificate.hoareValid_of_perClause
#print axioms
  Whiel.Hoare.Preproc.loopValid_of_sufficient
#print axioms
  Whiel.Hoare.Preproc.valid_of_sufficient
#print axioms
  Whiel.Cmd.BigStep.exists_of_loopFree
#print axioms
  Whiel.AssertExpr.spLoopFree_eval_imp_fixed
#print axioms
  Whiel.Hoare.Preproc.loopPre_eval_imp_sourcePrefix_fixed
#print axioms
  Whiel.Hoare.Preproc.counterExample_input_of_loop_counterExample
#print axioms
  Whiel.Hoare.Preproc.loopOnlyInitValid_of_sourcePrefixInitValid
#print axioms
  Whiel.Hoare.ofPreprocessed
#print axioms
  Whiel.Hoare.preprocess
#print axioms
  Whiel.Assertion.orList_apply_iff
#print axioms
  Whiel.Hoare.wp_orList_apply_iff
#print axioms
  Whiel.QFAssertExpr.wpLoopFree_orList_eval_iff
#print axioms
  Whiel.QFAssertExpr.wpLoopFree_orList_equiv

------------------------------------------------------------
-- Clause-Class and Enumeration Audit
------------------------------------------------------------

#print axioms
  Whiel.Synthesis.Clause.instDecidableEq
#print axioms
  Whiel.Synthesis.ClauseClass.Slice.mem_class
#print axioms
  DisjunctiveClause.baseSlice
#print axioms
  DisjunctiveClause.mem_baseSlice_iff
#print axioms
  formula_eval_iff
#print axioms
  formula_equiv_of_sameLiterals
#print axioms
  DisjunctiveClause.mem_clauseClass_iff
#print axioms
  formula_mem_clauseClass
#print axioms
  Enumerators.BaseSlice.mem_baseTerms_iff
#print axioms
  baseRepresentations_sound
#print axioms
  baseRepresentations_complete_up_to_equiv
#print axioms
  sameLiterals_iff_eq_of_mem_baseRepresentations
#print axioms slice
#print axioms mem_slice_iff
#print axioms baseSlice_subset_slice
#print axioms
  slice_eq_baseSlice_of_maxRAOps_eq_zero
#print axioms mem_selectionConditions_iff
#print axioms mem_projectionLists_iff
#print axioms mem_terms_iff
#print axioms mem_representations_iff
#print axioms representations_sound
#print axioms representations_complete
#print axioms
  representations_complete_up_to_equiv
namespace Whiel
namespace Synthesis
namespace DisjunctiveClause
namespace StructuralOrder

#print axioms literalCode_injective
#print axioms literalLinearOrder

end StructuralOrder
namespace CanonicalEnumeration

#print axioms sameLiterals_iff_eq_of_mem_representations
#print axioms representations_complete_up_to_equiv

end CanonicalEnumeration
end DisjunctiveClause
end Synthesis
end Whiel
#print axioms referenceParameters_isCofinal
#print axioms proposalFor_sound
#print axioms proposalFor_complete_up_to_equiv
#print axioms proposalFor_subset_clauseClass
#print axioms Term.eventually_isEligible

namespace Whiel.Synthesis.DisjunctiveClause.CNF

#print axioms formula_equiv
#print axioms candidate_denote_equiv
#print axioms eventually_clausesEligible
#print axioms canonicalCandidate_denote_equiv
#print axioms
  canonicalCandidate_subset_proposalFor
#print axioms
  eventually_canonical_subset_proposalFor
#print axioms
  canonicalCandidate_member_init_of_inductive
#print axioms
  canonicalCandidate_maint_of_inductive
#print axioms
  canonicalCandidate_term_of_sufficient
#print axioms
  canonicalCandidate_obligations_of_sufficient
#print axioms
  eventual_qf_witness_completeness

end Whiel.Synthesis.DisjunctiveClause.CNF

namespace Whiel.Synthesis.DisjunctiveClause

#print axioms
  FastEnumerator.fast_eventual_qf_witness_completeness
#print axioms
  Fast.mem_outputThrough_iff_mem_referenceProposal
#print axioms
  Fast.outputThrough_toFinset_eq_referenceProposal
#print axioms Fast.coversReference
#print axioms
  LiteralList.formula_injective
#print axioms
  Fast.advance_formulas_nodup
#print axioms
  Fast.advance_formulas_disjoint_prior_output
#print axioms
  Fast.outputThrough_nodup
#print axioms
  LiteralList.formula_entails_of_subset
#print axioms
  LiteralList.initCoverage_of_subset
#print axioms
  LiteralList.maintCoverage_of_subset

end Whiel.Synthesis.DisjunctiveClause

#print axioms
  WLayer.Enumeration.mem_clauses_iff
#print axioms
  WLayer.formula_succ_eval_iff
#print axioms
  WLayer.loop_counterExample_of_not_formula
#print axioms
  WLayer.counterExample_input_of_not_formula
#print axioms
  WLayer.formula_succ_step
#print axioms
  WLayer.term_iff_entails_zero
#print axioms
  WLayer.isSufficientFor_of_isInductiveFor_of_mem_zero
#print axioms
  WLayer.mem_candidateUpTo_iff
#print axioms
  WLayer.candidateUpTo_isSufficientFor
#print axioms
  WLayer.entails_formula_of_isSufficientFor

------------------------------------------------------------
-- Stable Solver Encoding Audit
------------------------------------------------------------

#print axioms
  Whiel.Vampire.TPTP.eraseDupsPreserve_nodup
#print axioms
  Whiel.Vampire.TPTP.nodup_map_snd_assignSolverNames
#print axioms
  Whiel.Vampire.TPTP.all_legalTptpName_assignSolverNames
#print axioms
  Whiel.Vampire.TPTP.NameEnv.wellFormed_ofSentences
#print axioms
  Whiel.Vampire.TPTP.NameEnv.wellFormed_ofEntailment
#print axioms
  Whiel.Vampire.TPTP.NameEnv.appendBindings?_appendOnly
#print axioms
  Whiel.Vampire.TPTP.sentenceWithEnv?_eq_some_of_appendOnly
#print axioms
  Whiel.Vampire.TPTP.sentenceWithEnv_toFOLWithConstants_stable
#print axioms
  Whiel.Vampire.TPTP.roleNeutralBody_stable
#print axioms
  Whiel.Vampire.TPTP.roleNeutralBodies_stable
#print axioms
  Whiel.Synthesis.Runtime.SolverKey.dataKey_injective
#print axioms
  Whiel.Synthesis.Runtime.SolverKey.relationKey_injective
#print axioms
  Whiel.Synthesis.Runtime.SolverKey.dataOfKey?_dataKey
#print axioms
  Whiel.Synthesis.Runtime.ReferenceProposal.stageBatch_entries_eq_entries
#print axioms
  Whiel.Synthesis.Runtime.ReferenceProposal.stageBatch_rawFormulaCount
#print axioms
  Whiel.Synthesis.Runtime.ReferenceProposal.stageBatch_canonicalFormulaCount
#print axioms
  Whiel.Synthesis.Runtime.FastProposal.exists_stageBatch_entry_iff_mem_advance
#print axioms
  Whiel.Synthesis.Runtime.FastProposal.stageBatch_formulas_eq_advance
#print axioms
  Whiel.Synthesis.Runtime.FastProposal.stageBatch_formulas_nodup
#print axioms
  Whiel.Synthesis.Runtime.FastProposal.stageBatch_formulas_disjoint_prior_output
#print axioms
  Whiel.Synthesis.Runtime.FastProposal.stageBatch_entry_mem_outputThrough
#print axioms
  Whiel.Synthesis.Runtime.FastProposal.mem_outputThrough_iff_exists_stageBatch_entry
#print axioms
  Whiel.Synthesis.Runtime.FastProposal.identity_eq_iff_formula_eq
#print axioms
  Whiel.Synthesis.Runtime.FastProposal.exists_seededStageBatch_entry_iff_mem_advanceSeeded
#print axioms
  Whiel.Synthesis.Runtime.FastProposal.seededStageBatch_formulas_eq_advanceSeeded
#print axioms
  Whiel.Synthesis.Runtime.FastProposal.seededStageBatch_formulas_nodup
#print axioms
  Whiel.Synthesis.Runtime.FastProposal.seededStageBatch_formulas_disjoint_prior_output
#print axioms
  Whiel.Synthesis.Runtime.FastProposal.seededStageBatch_entry_mem_outputThroughSeeded
#print axioms
  Whiel.Synthesis.Runtime.FastProposal.mem_outputThroughSeeded_iff_exists_seededStageBatch_entry
#print axioms
  Whiel.Synthesis.Runtime.FastProposal.exists_cappedStageBatch_entry_iff_mem_advanceSeededCapped
#print axioms
  Whiel.Synthesis.Runtime.FastProposal.cappedStageBatch_formulas_eq_advanceSeededCapped
#print axioms
  Whiel.Synthesis.Runtime.FastProposal.cappedStageBatch_formulas_nodup
#print axioms
  Whiel.Synthesis.Runtime.FastProposal.cappedStageBatch_formulas_disjoint_prior_output
#print axioms
  Whiel.Synthesis.Runtime.FastProposal.cappedStageBatch_entry_mem_outputThroughSeededCapped
#print axioms
  Whiel.Synthesis.Runtime.FastProposal.mem_outputThroughSeededCapped_iff_exists_cappedStageBatch_entry

------------------------------------------------------------
-- Seeded Fast Realization Audit
------------------------------------------------------------

#print axioms
  Whiel.Synthesis.Enumerators.Seeded.seededParameters_isCofinal
#print axioms
  Whiel.Synthesis.Enumerators.Seeded.seededCoversReference
#print axioms
  Whiel.Synthesis.Enumerators.Seeded.seededRepresentation_mem_outputThroughSeeded
#print axioms
  Whiel.Synthesis.Enumerators.Seeded.advanceSeeded_formulas_nodup
#print axioms
  Whiel.Synthesis.Enumerators.Seeded.advanceSeeded_formulas_disjoint_prior_output
#print axioms
  Whiel.Synthesis.Enumerators.Seeded.outputThroughSeeded_nodup

------------------------------------------------------------
-- Compiled-Twin Audit
------------------------------------------------------------

/-
  The wave traversal ships a tail-recursive compiled twin
  behind `csimp`; this equality is the entire trust link
  between the proved recursion and the executed loop.
-/
#print axioms
  Whiel.Synthesis.Enumerators.sublistsLenWithFreshAux_eq_tr

------------------------------------------------------------
-- Capped Fast Realization Audit
------------------------------------------------------------

#print axioms
  Whiel.Synthesis.Enumerators.Capped.defaultSchedule_admitting
#print axioms
  Whiel.Synthesis.Enumerators.Capped.cappedCoversReference
#print axioms
  Whiel.Synthesis.Enumerators.Capped.cappedRepresentation_mem
#print axioms
  Whiel.Synthesis.Enumerators.Capped.advanceSeededCapped_formulas_nodup
#print axioms
  Whiel.Synthesis.Enumerators.Capped.advanceSeededCapped_formulas_disjoint_prior_output
#print axioms
  Whiel.Synthesis.Enumerators.Capped.outputThroughSeededCapped_nodup

------------------------------------------------------------
-- Proven Realization Registry Audit
------------------------------------------------------------

/-
  One print covers every proof carried by the registry: the
  coverage and nodup fields of all proven entries are part
  of `provenEntry`'s definition.
-/
#print axioms
  Whiel.Synthesis.Runtime.FastProposal.Realization.provenEntry
#print axioms
  Whiel.Synthesis.Runtime.FastProposal.Realization.provenEntry_id
#print axioms
  Whiel.Synthesis.Runtime.FastProposal.Realization.provenEntry_version

------------------------------------------------------------
-- Relational-Calculus Validity Audit
------------------------------------------------------------

#print axioms
  RelCalc.Sentence.exists_finite_quantifierDomain_satIn_iff
#print axioms
  RelCalc.Sentence.adomValid_iff_localAdomValid_and_domainIndependent
#print axioms
  RelCalc.SentenceEntailment.valid_of_prependAxioms
#print axioms
  RelCalc.SentenceEntailment.valid_of_prependAxioms_shallow

------------------------------------------------------------
-- Kernel Invalidity Certification Audit
------------------------------------------------------------

#print axioms
  Whiel.Hoare.CounterExample.invalid_of_kernelRefutes
#print axioms
  Whiel.Hoare.CounterExample.certifyKernel
