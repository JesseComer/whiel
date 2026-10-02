-- Author: Jesse Comer
import Whiel.Tests.PreprocessNormalize

/-
  Explicit axiom audit for the normalizer of the generic
  preprocessor.

  Every theorem of `Whiel/Preprocess/Normalize.lean` and
  `Whiel/Tests/PreprocessNormalize.lean` is audited here.
  Every one depends on the standard three axioms or fewer.
-/

set_option linter.hashCommand false

------------------------------------------------------------
-- Source-Level Tests
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.eq_of_guardSame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.eq_of_guardSame

------------------------------------------------------------
-- The Flag Budget
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.flagBudget_eq_zero_of_loopFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flagBudget_eq_zero_of_loopFree

/-- info: 'Whiel.Preprocess.branchingLoops_eq_zero_of_loopFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.branchingLoops_eq_zero_of_loopFree

/-- info: 'Whiel.Preprocess.flagBudget_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flagBudget_bound

/-- info: 'Whiel.Preprocess.flagBudget_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flagBudget_le

/-- info: 'Whiel.Preprocess.loops_pos_of_idemCheck' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.loops_pos_of_idemCheck

/-- info: 'Whiel.Preprocess.twoLoopApplications_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.twoLoopApplications_eq

------------------------------------------------------------
-- The Flag Supply Of The Recursion
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.mem_flagIds_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mem_flagIds_iff

/-- info: 'Whiel.Preprocess.length_flagIds' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.length_flagIds

/-- info: 'Whiel.Preprocess.flagIds_zero' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flagIds_zero

/-- info: 'Whiel.Preprocess.flagIds_succ' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flagIds_succ

/-- info: 'Whiel.Preprocess.flagIds_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flagIds_append

/-- info: 'Whiel.Preprocess.flagIds_one' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flagIds_one

/-- info: 'Whiel.Preprocess.flagIds_two' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flagIds_two

/-- info: 'Whiel.Preprocess.mem_flagNames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mem_flagNames

/-- info: 'Whiel.Preprocess.flagNames_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flagNames_subset

/-- info: 'Whiel.Preprocess.flagExt_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flagExt_mono

/-- info: 'Whiel.Preprocess.subsetAppendLeft' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.subsetAppendLeft

/-- info: 'Whiel.Preprocess.subsetAppendRight' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.subsetAppendRight

------------------------------------------------------------
-- The Result Of The Recursion
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.flagName_flagAt_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flagName_flagAt_not_mem

/-- info: 'Whiel.Preprocess.NormResult.clean_ids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.NormResult.clean_ids

/-- info: 'Whiel.Preprocess.NormResult.clean_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.NormResult.clean_loop

/-- info: 'Whiel.Preprocess.normalize_eq_clean_normalizeRaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.normalize_eq_clean_normalizeRaw

------------------------------------------------------------
-- The Identifiers The Recursion Draws
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.flagAt_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flagAt_add

/-- info: 'Whiel.Preprocess.flagIds_append_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flagIds_append_one

/-- info: 'Whiel.Preprocess.flagIds_append_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flagIds_append_two

/-- info: 'Whiel.Preprocess.baseResult_ids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.baseResult_ids

/-- info: 'Whiel.Preprocess.loopFreeResult_ids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.loopFreeResult_ids

/-- info: 'Whiel.Preprocess.seqResult_ids_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.seqResult_ids_first

/-- info: 'Whiel.Preprocess.seqResult_ids_second' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.seqResult_ids_second

/-- info: 'Whiel.Preprocess.seqResult_ids_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.seqResult_ids_product

/-- info: 'Whiel.Preprocess.seqResult_ids_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.seqResult_ids_general

/-- info: 'Whiel.Preprocess.iteResult_ids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.iteResult_ids

/-- info: 'Whiel.Preprocess.loopResult_ids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.loopResult_ids

/-- info: 'Whiel.Preprocess.normalizeAux_ids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.normalizeAux_ids

/-- info: 'Whiel.Preprocess.normalize_ids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.normalize_ids

/-- info: 'Whiel.Preprocess.flagName_normalizeNext_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flagName_normalizeNext_not_mem

/-- info: 'Whiel.Preprocess.normalizeNext_not_mem_ids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.normalizeNext_not_mem_ids

/-- info: 'Whiel.Preprocess.normalize_ids_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.normalize_ids_length

------------------------------------------------------------
-- The Clauses Of The Recursion
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.seqResult_eq_intoPrefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.seqResult_eq_intoPrefix

/-- info: 'Whiel.Preprocess.seqResult_eq_intoSuffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.seqResult_eq_intoSuffix

/-- info: 'Whiel.Preprocess.seqResult_eq_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.seqResult_eq_product

/-- info: 'Whiel.Preprocess.seqResult_eq_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.seqResult_eq_general

/-- info: 'Whiel.Preprocess.normalizeAux_eq_base_seq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.normalizeAux_eq_base_seq

/-- info: 'Whiel.Preprocess.normalizeAux_eq_seq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.normalizeAux_eq_seq

/-- info: 'Whiel.Preprocess.normalizeAux_eq_base_ite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.normalizeAux_eq_base_ite

/-- info: 'Whiel.Preprocess.normalizeAux_eq_ite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.normalizeAux_eq_ite

/-- info: 'Whiel.Preprocess.normalizeAux_eq_idem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.normalizeAux_eq_idem

/-- info: 'Whiel.Preprocess.normalizeAux_eq_loopFreeBody' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.normalizeAux_eq_loopFreeBody

/-- info: 'Whiel.Preprocess.normalizeAux_eq_flatten' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.normalizeAux_eq_flatten

------------------------------------------------------------
-- The Shape Of The Output
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.loopFreeParts_retagOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.loopFreeParts_retagOn

/-- info: 'Whiel.Preprocess.baseResult_loopFreeParts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.baseResult_loopFreeParts

/-- info: 'Whiel.Preprocess.seqLeft_loopFreeParts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.seqLeft_loopFreeParts

/-- info: 'Whiel.Preprocess.seqRight_loopFreeParts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.seqRight_loopFreeParts

/-- info: 'Whiel.Preprocess.seqResult_loopFreeParts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.seqResult_loopFreeParts

/-- info: 'Whiel.Preprocess.iteResult_loopFreeParts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.iteResult_loopFreeParts

/-- info: 'Whiel.Preprocess.loopFreeResult_loopFreeParts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.loopFreeResult_loopFreeParts

/-- info: 'Whiel.Preprocess.loopResult_loopFreeParts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.loopResult_loopFreeParts

/-- info: 'Whiel.Preprocess.normalizeAux_loopFreeParts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.normalizeAux_loopFreeParts

/-- info: 'Whiel.Preprocess.loops_normalizeAux_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.loops_normalizeAux_unfold

/-- info: 'Whiel.Preprocess.normalize_loopFreeParts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.normalize_loopFreeParts

/-- info: 'Whiel.Preprocess.loops_normalize_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.loops_normalize_unfold

------------------------------------------------------------
-- Footprints Of The Operations
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.symbols_topExpr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.symbols_topExpr

/-- info: 'Whiel.Preprocess.symbols_emptyExpr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.symbols_emptyExpr

/-- info: 'Whiel.Preprocess.symbols_raise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.symbols_raise

/-- info: 'Whiel.Preprocess.symbols_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.symbols_lower

/-- info: 'Whiel.Preprocess.symbols_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.symbols_test

/-- info: 'Whiel.Preprocess.symbols_unfold_retagOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.symbols_unfold_retagOn

/-- info: 'Whiel.Preprocess.assignedSymbols_unfold_retagOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.assignedSymbols_unfold_retagOn

/-- info: 'Whiel.Preprocess.symbols_unfold_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.symbols_unfold_base

/-- info: 'Whiel.Preprocess.assignedSymbols_unfold_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.assignedSymbols_unfold_base

/-- info: 'Whiel.Preprocess.mergeIntoPrefix_symbols_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mergeIntoPrefix_symbols_subset

/-- info: 'Whiel.Preprocess.mergeIntoPrefix_assignedSymbols_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mergeIntoPrefix_assignedSymbols_subset

/-- info: 'Whiel.Preprocess.mergeIntoSuffix_symbols_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mergeIntoSuffix_symbols_subset

/-- info: 'Whiel.Preprocess.mergeIntoSuffix_assignedSymbols_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mergeIntoSuffix_assignedSymbols_subset

/-- info: 'Whiel.Preprocess.mergeProduct_symbols_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mergeProduct_symbols_subset

/-- info: 'Whiel.Preprocess.mergeProduct_assignedSymbols_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mergeProduct_assignedSymbols_subset

/-- info: 'Whiel.Preprocess.mergeGeneral_symbols_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mergeGeneral_symbols_subset

/-- info: 'Whiel.Preprocess.mergeGeneral_assignedSymbols_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mergeGeneral_assignedSymbols_subset

/-- info: 'Whiel.Preprocess.hoistIte_symbols_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistIte_symbols_subset

/-- info: 'Whiel.Preprocess.hoistIte_assignedSymbols_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistIte_assignedSymbols_subset

/-- info: 'Whiel.Preprocess.flattenGeneral_symbols_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flattenGeneral_symbols_subset

/-- info: 'Whiel.Preprocess.flattenGeneral_assignedSymbols_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flattenGeneral_assignedSymbols_subset

/-- info: 'Whiel.Preprocess.flattenLoopFree_symbols_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flattenLoopFree_symbols_subset

/-- info: 'Whiel.Preprocess.flattenLoopFree_assignedSymbols_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flattenLoopFree_assignedSymbols_subset

------------------------------------------------------------
-- The Footprint Lemma
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.footprint_combine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.footprint_combine

/-- info: 'Whiel.Preprocess.footprint_combine₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.footprint_combine₂

/-- info: 'Whiel.Preprocess.footprint_combine_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.footprint_combine_one

/-- info: 'Whiel.Preprocess.seqLeft_symbols' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.seqLeft_symbols

/-- info: 'Whiel.Preprocess.seqLeft_assignedSymbols' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.seqLeft_assignedSymbols

/-- info: 'Whiel.Preprocess.seqRight_symbols' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.seqRight_symbols

/-- info: 'Whiel.Preprocess.seqRight_assignedSymbols' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.seqRight_assignedSymbols

/-- info: 'Whiel.Preprocess.baseResult_symbols' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.baseResult_symbols

/-- info: 'Whiel.Preprocess.baseResult_assignedSymbols' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.baseResult_assignedSymbols

/-- info: 'Whiel.Preprocess.loopFreeResult_symbols' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.loopFreeResult_symbols

/-- info: 'Whiel.Preprocess.loopFreeResult_assignedSymbols' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.loopFreeResult_assignedSymbols

/-- info: 'Whiel.Preprocess.drawnFlag_sym_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.drawnFlag_sym_val

/-- info: 'Whiel.Preprocess.flagNames_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flagNames_mono

/-- info: 'Whiel.Preprocess.seqResult_footprint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.seqResult_footprint

/-- info: 'Whiel.Preprocess.iteResult_footprint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.iteResult_footprint

/-- info: 'Whiel.Preprocess.loopResult_footprint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.loopResult_footprint

/-- info: 'Whiel.Preprocess.normalizeAux_footprint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.normalizeAux_footprint

/-- info: 'Whiel.Preprocess.normalize_footprint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.normalize_footprint

------------------------------------------------------------
-- The Three Congruence Steps
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.EquivMod.trans_bigStepEquiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.EquivMod.trans_bigStepEquiv

/-- info: 'Whiel.Preprocess.EquivMod.of_bigStepEquiv_left' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.EquivMod.of_bigStepEquiv_left

/-- info: 'Whiel.Preprocess.equivMod_seq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.equivMod_seq

/-- info: 'Whiel.Preprocess.equivMod_ite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.equivMod_ite

/-- info: 'Whiel.Preprocess.equivMod_while' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.equivMod_while

/-- info: 'Whiel.Preprocess.isBase_retagOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.isBase_retagOn

------------------------------------------------------------
-- Symbols Lie In The Schema
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.guard_symbols_subset_syms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.guard_symbols_subset_syms

/-- info: 'Whiel.Preprocess.cmd_symbols_subset_syms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.cmd_symbols_subset_syms

------------------------------------------------------------
-- Freshness And Independence Of The Drawn Flags
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.seqPair_ids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.seqPair_ids

/-- info: 'Whiel.Preprocess.flagAt_not_mem_flagIds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flagAt_not_mem_flagIds

/-- info: 'Whiel.Preprocess.normalizeAux_ids_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.normalizeAux_ids_ge

/-- info: 'Whiel.Preprocess.normalizeAux_ids_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.normalizeAux_ids_lt

/-- info: 'Whiel.Preprocess.normalizeAux_ids_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.normalizeAux_ids_fresh

/-- info: 'Whiel.Preprocess.drawnFlag_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.drawnFlag_fresh

/-- info: 'Whiel.Preprocess.drawnFlag_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.drawnFlag_ne

/-- info: 'Whiel.Preprocess.independent_of_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.independent_of_source

/-- info: 'Whiel.Preprocess.normalizeAux_of_loopFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.normalizeAux_of_loopFree

/-- info: 'Whiel.Preprocess.baseResult_loop_isBase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.baseResult_loop_isBase

/-- info: 'Whiel.Preprocess.bigStepEquiv_of_idemCheck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.bigStepEquiv_of_idemCheck

------------------------------------------------------------
-- The Normalization Theorem
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.baseResult_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.baseResult_equivMod

/-- info: 'Whiel.Preprocess.seqResult_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.seqResult_equivMod

/-- info: 'Whiel.Preprocess.iteResult_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.iteResult_equivMod

/-- info: 'Whiel.Preprocess.loopResult_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.loopResult_equivMod

/-- info: 'Whiel.Preprocess.normalizeAux_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.normalizeAux_equivMod

/-- info: 'Whiel.Preprocess.normalize_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.normalize_equivMod

/-- info: 'Whiel.Preprocess.normalize_simulates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.normalize_simulates

------------------------------------------------------------
-- The Output As A Program
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.NormResult.toProgram_cmd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.NormResult.toProgram_cmd

/-- info: 'Whiel.Preprocess.NormResult.toProgram_execSchema' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.NormResult.toProgram_execSchema

/-- info: 'Whiel.Preprocess.NormResult.initialInstance_eq_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.NormResult.initialInstance_eq_lift

/-- info: 'Whiel.Preprocess.NormResult.observe_eq_project' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.NormResult.observe_eq_project

/-- info: 'Whiel.Preprocess.NormResult.bigStep_toProgram_iff_of_equivMod' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.NormResult.bigStep_toProgram_iff_of_equivMod

/-- info: 'Whiel.Preprocess.normalize_toProgram_bigStep_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.normalize_toProgram_bigStep_iff

------------------------------------------------------------
-- The Loop-Free Clause And The Single Loop
------------------------------------------------------------

/-- info: 'Whiel.Tests.PreprocessNormalize.progFree_toRaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessNormalize.progFree_toRaw

/-- info: 'Whiel.Tests.PreprocessNormalize.progLoop_toRaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessNormalize.progLoop_toRaw

/-- info: 'Whiel.Tests.PreprocessNormalize.progIdem_toRaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessNormalize.progIdem_toRaw

------------------------------------------------------------
-- The Product Of Two Independent Loops
------------------------------------------------------------

/-- info: 'Whiel.Tests.PreprocessNormalize.progIndep_toRaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessNormalize.progIndep_toRaw

------------------------------------------------------------
-- The General Merge Of Two Dependent Loops
------------------------------------------------------------

/-- info: 'Whiel.Tests.PreprocessNormalize.progDep_toRaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessNormalize.progDep_toRaw

------------------------------------------------------------
-- The Hoist Of A Loop In A Branch
------------------------------------------------------------

/-- info: 'Whiel.Tests.PreprocessNormalize.progIte_toRaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessNormalize.progIte_toRaw

------------------------------------------------------------
-- The Flattening Of A Loop Inside A Loop
------------------------------------------------------------

/-- info: 'Whiel.Tests.PreprocessNormalize.progNested_toRaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessNormalize.progNested_toRaw

------------------------------------------------------------
-- The Worked Example Of Section 5
------------------------------------------------------------

/-- info: 'Whiel.Tests.PreprocessNormalize.progWorked_toRaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessNormalize.progWorked_toRaw

------------------------------------------------------------
-- The Normalization Theorem On The Corpus
------------------------------------------------------------

/-- info: 'Whiel.Tests.PreprocessNormalize.progFree_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessNormalize.progFree_equivMod

/-- info: 'Whiel.Tests.PreprocessNormalize.progLoop_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessNormalize.progLoop_equivMod

/-- info: 'Whiel.Tests.PreprocessNormalize.progIndep_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessNormalize.progIndep_equivMod

/-- info: 'Whiel.Tests.PreprocessNormalize.progDep_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessNormalize.progDep_equivMod

/-- info: 'Whiel.Tests.PreprocessNormalize.progIte_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessNormalize.progIte_equivMod

/-- info: 'Whiel.Tests.PreprocessNormalize.progNested_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessNormalize.progNested_equivMod

/-- info: 'Whiel.Tests.PreprocessNormalize.progIdem_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessNormalize.progIdem_equivMod

/-- info: 'Whiel.Tests.PreprocessNormalize.progWorked_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessNormalize.progWorked_equivMod

/-- info: 'Whiel.Tests.PreprocessNormalize.progAll_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessNormalize.progAll_equivMod

/-- info: 'Whiel.Tests.PreprocessNormalize.progAll_footprint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessNormalize.progAll_footprint

/-- info: 'Whiel.Tests.PreprocessNormalize.progAll_loopFreeParts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessNormalize.progAll_loopFreeParts
