-- Author: Jesse Comer
import Whiel.Tests.PreprocessMerge

/-
  Explicit axiom audit for the foundations and the
  sequence merge of the generic preprocessor.

  Every theorem of `Whiel/Preprocess/Framed.lean`,
  `Whiel/Preprocess/Flags.lean`,
  `Whiel/Preprocess/Equiv.lean`,
  `Whiel/Preprocess/Merge.lean` and
  `Whiel/Tests/PreprocessMerge.lean` is audited here.
  Every one depends on the standard three axioms or fewer.
-/

set_option linter.hashCommand false


------------------------------------------------------------
-- Framed Loops
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.loopFree_skip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.loopFree_skip

/-- info: 'Whiel.Preprocess.loopFree_assign' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.loopFree_assign

/-- info: 'Whiel.Preprocess.loopFree_seq_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.loopFree_seq_iff

/-- info: 'Whiel.Preprocess.loopFree_ite_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.loopFree_ite_iff

/-- info: 'Whiel.Preprocess.not_loopFree_while' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.not_loopFree_while

/-- info: 'Whiel.Preprocess.Framed.base_init' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.Framed.base_init

/-- info: 'Whiel.Preprocess.Framed.base_guard' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.Framed.base_guard

/-- info: 'Whiel.Preprocess.Framed.base_body' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.Framed.base_body

/-- info: 'Whiel.Preprocess.Framed.base_close' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.Framed.base_close

/-- info: 'Whiel.Preprocess.Framed.isBase_base' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.Framed.isBase_base

/-- info: 'Whiel.Preprocess.Framed.loopFreeParts_base_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.Framed.loopFreeParts_base_iff

/-- info: 'Whiel.Preprocess.Framed.eq_base_of_isBase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.Framed.eq_base_of_isBase

/-- info: 'Whiel.Preprocess.Framed.loops_unfold' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.Framed.loops_unfold

/-- info: 'Whiel.Preprocess.Framed.bigStep_unfold_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.Framed.bigStep_unfold_iff

/-- info: 'Whiel.Preprocess.Framed.bigStep_while_false_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.Framed.bigStep_while_false_iff

/-- info: 'Whiel.Preprocess.Framed.bigStep_base_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.Framed.bigStep_base_iff


------------------------------------------------------------
-- Flags And Retagging
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.reduct_update_symOfExtension' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.reduct_update_symOfExtension

/-- info: 'Whiel.Preprocess.eq_of_cast_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.eq_of_cast_eq

/-- info: 'Whiel.Preprocess.eval_castArity_cast' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.eval_castArity_cast

/-- info: 'Whiel.Preprocess.assignedSymbols_retag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.assignedSymbols_retag

/-- info: 'Whiel.Preprocess.symbols_retag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.symbols_retag

/-- info: 'Whiel.Preprocess.loops_retag' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.loops_retag

/-- info: 'Whiel.Preprocess.project_lift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.project_lift

/-- info: 'Whiel.Preprocess.lift_eq_empty_of_not_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.lift_eq_empty_of_not_mem

/-- info: 'Whiel.Preprocess.retag_eval_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.retag_eval_iff

/-- info: 'Whiel.Preprocess.retag_bigStep_project' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.retag_bigStep_project

/-- info: 'Whiel.Preprocess.retag_bigStep_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.retag_bigStep_lift

/-- info: 'Whiel.Preprocess.retag_preserves_new' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.retag_preserves_new

/-- info: 'Whiel.Preprocess.FlagSym.eval_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.FlagSym.eval_rel

/-- info: 'Whiel.Preprocess.FlagSym.cast_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.FlagSym.cast_empty

/-- info: 'Whiel.Preprocess.FlagSym.eval_emptyExpr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.FlagSym.eval_emptyExpr

/-- info: 'Whiel.Preprocess.FlagSym.eval_topExpr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.FlagSym.eval_topExpr

/-- info: 'Whiel.Preprocess.FlagSym.eval_topExpr_ne_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.FlagSym.eval_topExpr_ne_empty

/-- info: 'Whiel.Preprocess.FlagSym.tuple_zero_eq_empty' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.FlagSym.tuple_zero_eq_empty

/-- info: 'Whiel.Preprocess.FlagSym.nullary_eq_top_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.FlagSym.nullary_eq_top_iff

/-- info: 'Whiel.Preprocess.FlagSym.eq_cast_top_iff_ne_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.FlagSym.eq_cast_top_iff_ne_empty

/-- info: 'Whiel.Preprocess.FlagSym.up_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.FlagSym.up_iff

/-- info: 'Whiel.Preprocess.FlagSym.assignedSymbols_raise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.FlagSym.assignedSymbols_raise

/-- info: 'Whiel.Preprocess.FlagSym.assignedSymbols_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.FlagSym.assignedSymbols_lower

/-- info: 'Whiel.Preprocess.FlagSym.bigStep_raise_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.FlagSym.bigStep_raise_iff

/-- info: 'Whiel.Preprocess.FlagSym.bigStep_lower_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.FlagSym.bigStep_lower_iff

/-- info: 'Whiel.Preprocess.FlagSym.up_of_bigStep_raise' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.FlagSym.up_of_bigStep_raise

/-- info: 'Whiel.Preprocess.FlagSym.not_up_of_bigStep_lower' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.FlagSym.not_up_of_bigStep_lower

/-- info: 'Whiel.Preprocess.FlagSym.up_congr_of_not_assigned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.FlagSym.up_congr_of_not_assigned

/-- info: 'Whiel.Preprocess.FlagSym.up_congr_of_bigStep_raise_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.FlagSym.up_congr_of_bigStep_raise_ne

/-- info: 'Whiel.Preprocess.FlagSym.up_congr_of_bigStep_lower_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.FlagSym.up_congr_of_bigStep_lower_ne

/-- info: 'Whiel.Preprocess.Framed.unfold_retagOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.Framed.unfold_retagOn

/-- info: 'Whiel.Preprocess.eq_of_reduct_eq_of_agree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.eq_of_reduct_eq_of_agree

/-- info: 'Whiel.Preprocess.retag_bigStep_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.retag_bigStep_iff

/-- info: 'Whiel.Preprocess.project_update_of_not_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.project_update_of_not_mem

/-- info: 'Whiel.Preprocess.not_up_lift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.not_up_lift

/-- info: 'Whiel.Preprocess.project_of_bigStep_raise' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.project_of_bigStep_raise

/-- info: 'Whiel.Preprocess.project_of_bigStep_lower' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.project_of_bigStep_lower

/-- info: 'Whiel.Preprocess.not_assigned_retag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.not_assigned_retag

/-- info: 'Whiel.Preprocess.up_congr_retag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.up_congr_retag

/-- info: 'Whiel.Preprocess.isFlag_flagName' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.isFlag_flagName

/-- info: 'Whiel.Preprocess.isBase_flagName' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.isBase_flagName

/-- info: 'Whiel.Preprocess.flagName_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flagName_injective

/-- info: 'Whiel.Preprocess.mem_flagNames_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mem_flagNames_iff

/-- info: 'Whiel.Preprocess.flagExt_extensionOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flagExt_extensionOf

/-- info: 'Whiel.Preprocess.flagSymOf_sym_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flagSymOf_sym_val

/-- info: 'Whiel.Preprocess.flagSymOf_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flagSymOf_ne

/-- info: 'Whiel.Preprocess.flagName_not_mem_of_rawIndexZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flagName_not_mem_of_rawIndexZero

/-- info: 'Whiel.Preprocess.flagName_not_mem_of_flagSeed_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flagName_not_mem_of_flagSeed_le

/-- info: 'Whiel.Preprocess.flagSeed_eq_zero_of_rawIndexZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flagSeed_eq_zero_of_rawIndexZero


------------------------------------------------------------
-- Equivalence Modulo Flags
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.EquivMod.simulates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.EquivMod.simulates

/-- info: 'Whiel.Preprocess.EquivMod.projectRun' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.EquivMod.projectRun

/-- info: 'Whiel.Preprocess.equivMod_refl_of_bigStepEquiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.equivMod_refl_of_bigStepEquiv

/-- info: 'Whiel.Preprocess.EquivMod.compose' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.EquivMod.compose

/-- info: 'Whiel.Preprocess.Simulates.compose' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.Simulates.compose

/-- info: 'Whiel.Preprocess.equivMod_retag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.equivMod_retag

/-- info: 'Whiel.Preprocess.equivMod_retag_of_bigStepEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.equivMod_retag_of_bigStepEquiv

/-- info: 'Whiel.Preprocess.flagInit_raise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flagInit_raise

/-- info: 'Whiel.Preprocess.flagInit_raise_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flagInit_raise_lower


------------------------------------------------------------
-- The Sequence Merge
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.mem_rawSymbolList_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mem_rawSymbolList_iff

/-- info: 'Whiel.Preprocess.mem_guardSymbolList_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mem_guardSymbolList_iff

/-- info: 'Whiel.Preprocess.mem_assignedList_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mem_assignedList_iff

/-- info: 'Whiel.Preprocess.mem_symbolList_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mem_symbolList_iff

/-- info: 'Whiel.Preprocess.Independent.symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.Independent.symm

/-- info: 'Whiel.Preprocess.independent_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.independent_of_check

/-- info: 'Whiel.Preprocess.agreeOn_of_bigStep_of_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.agreeOn_of_bigStep_of_disjoint

/-- info: 'Whiel.Preprocess.bigStep_seq_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.bigStep_seq_comm

/-- info: 'Whiel.Preprocess.bigStep_seq_comm_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.bigStep_seq_comm_iff

/-- info: 'Whiel.Preprocess.mergeSeq_eq_of_loopFreeFirst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mergeSeq_eq_of_loopFreeFirst

/-- info: 'Whiel.Preprocess.mergeSeq_eq_of_loopFreeSecond' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mergeSeq_eq_of_loopFreeSecond

/-- info: 'Whiel.Preprocess.mergeSeq_eq_of_independent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mergeSeq_eq_of_independent

/-- info: 'Whiel.Preprocess.mergeSeq_eq_general' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mergeSeq_eq_general

/-- info: 'Whiel.Preprocess.mergeIntoPrefix_base_bigStepEquiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mergeIntoPrefix_base_bigStepEquiv

/-- info: 'Whiel.Preprocess.mergeIntoPrefix_bigStepEquiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mergeIntoPrefix_bigStepEquiv

/-- info: 'Whiel.Preprocess.mergeIntoSuffix_base_bigStepEquiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mergeIntoSuffix_base_bigStepEquiv

/-- info: 'Whiel.Preprocess.mergeIntoSuffix_bigStepEquiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mergeIntoSuffix_bigStepEquiv

/-- info: 'Whiel.Preprocess.agreeOn_refl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.agreeOn_refl

/-- info: 'Whiel.Preprocess.agreeOn_trans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.agreeOn_trans

/-- info: 'Whiel.Preprocess.Independent.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.Independent.mono

/-- info: 'Whiel.Preprocess.mem_unfold_assignedSymbols_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mem_unfold_assignedSymbols_iff

/-- info: 'Whiel.Preprocess.mem_unfold_symbols_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mem_unfold_symbols_iff

/-- info: 'Whiel.Preprocess.init_assignedSymbols_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.init_assignedSymbols_subset

/-- info: 'Whiel.Preprocess.init_symbols_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.init_symbols_subset

/-- info: 'Whiel.Preprocess.close_assignedSymbols_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.close_assignedSymbols_subset

/-- info: 'Whiel.Preprocess.close_symbols_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.close_symbols_subset

/-- info: 'Whiel.Preprocess.body_assignedSymbols_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.body_assignedSymbols_subset

/-- info: 'Whiel.Preprocess.body_symbols_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.body_symbols_subset

/-- info: 'Whiel.Preprocess.guard_symbols_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.guard_symbols_subset

/-- info: 'Whiel.Preprocess.loop_assignedSymbols_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.loop_assignedSymbols_subset

/-- info: 'Whiel.Preprocess.loop_symbols_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.loop_symbols_subset

/-- info: 'Whiel.Preprocess.productLoop_project_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.productLoop_project_left

/-- info: 'Whiel.Preprocess.productLoop_project_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.productLoop_project_right

/-- info: 'Whiel.Preprocess.productLoop_terminates_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.productLoop_terminates_right

/-- info: 'Whiel.Preprocess.productLoop_terminates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.productLoop_terminates

/-- info: 'Whiel.Preprocess.productLoop_bigStepEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.productLoop_bigStepEquiv

/-- info: 'Whiel.Preprocess.bigStepEquiv_seq_left' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.bigStepEquiv_seq_left

/-- info: 'Whiel.Preprocess.bigStepEquiv_seq_right' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.bigStepEquiv_seq_right

/-- info: 'Whiel.Preprocess.bigStepEquiv_seq_assoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.bigStepEquiv_seq_assoc

/-- info: 'Whiel.Preprocess.bigStepEquiv_seq_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.bigStepEquiv_seq_swap

/-- info: 'Whiel.Preprocess.mergeProduct_bigStepEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mergeProduct_bigStepEquiv

/-- info: 'Whiel.Preprocess.mergeGeneral_project' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mergeGeneral_project

/-- info: 'Whiel.Preprocess.mergeGeneral_lift_second' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mergeGeneral_lift_second

/-- info: 'Whiel.Preprocess.mergeGeneral_lift_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mergeGeneral_lift_first

/-- info: 'Whiel.Preprocess.mergeGeneral_bigStep_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mergeGeneral_bigStep_iff

/-- info: 'Whiel.Preprocess.mergeGeneral_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mergeGeneral_equivMod

/-- info: 'Whiel.Preprocess.mergeGeneral_flags_down' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mergeGeneral_flags_down

/-- info: 'Whiel.Preprocess.loopFree_retag_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.loopFree_retag_iff

/-- info: 'Whiel.Preprocess.mergeIntoPrefix_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mergeIntoPrefix_equivMod

/-- info: 'Whiel.Preprocess.mergeIntoSuffix_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mergeIntoSuffix_equivMod

/-- info: 'Whiel.Preprocess.mergeProduct_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mergeProduct_equivMod

/-- info: 'Whiel.Preprocess.mergeSeq_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mergeSeq_equivMod

/-- info: 'Whiel.Preprocess.mergeIntoPrefix_loopFreeParts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mergeIntoPrefix_loopFreeParts

/-- info: 'Whiel.Preprocess.mergeIntoSuffix_loopFreeParts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mergeIntoSuffix_loopFreeParts

/-- info: 'Whiel.Preprocess.mergeProduct_loopFreeParts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mergeProduct_loopFreeParts

/-- info: 'Whiel.Preprocess.mergeGeneral_loopFreeParts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mergeGeneral_loopFreeParts

/-- info: 'Whiel.Preprocess.mergeSeq_loopFreeParts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mergeSeq_loopFreeParts


------------------------------------------------------------
-- The Merge Test Corpus
------------------------------------------------------------

/-- info: 'Whiel.Tests.PreprocessMerge.prefixCase_toRaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessMerge.prefixCase_toRaw

/-- info: 'Whiel.Tests.PreprocessMerge.prefixCase_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessMerge.prefixCase_equivMod

/-- info: 'Whiel.Tests.PreprocessMerge.suffixCase_toRaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessMerge.suffixCase_toRaw

/-- info: 'Whiel.Tests.PreprocessMerge.suffixCase_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessMerge.suffixCase_equivMod

/-- info: 'Whiel.Tests.PreprocessMerge.productCase_toRaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessMerge.productCase_toRaw

/-- info: 'Whiel.Tests.PreprocessMerge.productCase_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessMerge.productCase_equivMod

/-- info: 'Whiel.Tests.PreprocessMerge.generalCase_toRaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessMerge.generalCase_toRaw

/-- info: 'Whiel.Tests.PreprocessMerge.generalCase_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessMerge.generalCase_equivMod

/-- info: 'Whiel.Tests.PreprocessMerge.generalCase_flags_down' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessMerge.generalCase_flags_down

/-- info: 'Whiel.Tests.PreprocessMerge.mergeSeq_reduces_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessMerge.mergeSeq_reduces_prefix

/-- info: 'Whiel.Tests.PreprocessMerge.mergeSeq_reduces_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessMerge.mergeSeq_reduces_suffix

/-- info: 'Whiel.Tests.PreprocessMerge.mergeSeq_reduces_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessMerge.mergeSeq_reduces_product

/-- info: 'Whiel.Tests.PreprocessMerge.mergeSeq_reduces_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessMerge.mergeSeq_reduces_general

/-- info: 'Whiel.Tests.PreprocessMerge.mergeSeq_parts_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessMerge.mergeSeq_parts_general

/-- info: 'Whiel.Tests.PreprocessMerge.mergeSeq_parts_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessMerge.mergeSeq_parts_product
