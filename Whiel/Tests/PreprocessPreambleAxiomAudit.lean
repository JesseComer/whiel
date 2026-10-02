-- Author: Jesse Comer
import Whiel.Tests.PreprocessPreamble

/-
  Explicit axiom audit for the preamble split and the
  preamble push of the generic preprocessor.

  Every theorem of `Whiel/Preprocess/Preamble.lean` and
  `Whiel/Tests/PreprocessPreamble.lean` is audited here.
  Every one depends on the standard three axioms or fewer.
-/

set_option linter.hashCommand false

------------------------------------------------------------
-- Loop-Freeness In Both Spellings
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.cmdLoopFree_iff_loopFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.cmdLoopFree_iff_loopFree

/-- info: 'Whiel.Preprocess.cmdLoopFree_of_loopFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.cmdLoopFree_of_loopFree

------------------------------------------------------------
-- The Prefix As Top-Level Items
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.bigStep_seq_skip_right_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.bigStep_seq_skip_right_iff

/-- info: 'Whiel.Preprocess.bigStepEquiv_seqOfItems_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.bigStepEquiv_seqOfItems_append

/-- info: 'Whiel.Preprocess.bigStepEquiv_seqOfItems_seqItems' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.bigStepEquiv_seqOfItems_seqItems

/-- info: 'Whiel.Preprocess.loopFree_of_mem_seqItems' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.loopFree_of_mem_seqItems

/-- info: 'Whiel.Preprocess.loopFree_seqOfItems' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.loopFree_seqOfItems

------------------------------------------------------------
-- Retagging A Quantifier-Free Assertion
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.retagAssert_noBoundSymbols' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.retagAssert_noBoundSymbols

/-- info: 'Whiel.Preprocess.retag_assert_eval_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.retag_assert_eval_iff

------------------------------------------------------------
-- The Split Of The Preamble
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.splitItems_keep_append_push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.splitItems_keep_append_push

/-- info: 'Whiel.Preprocess.mem_of_mem_splitItems_keep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mem_of_mem_splitItems_keep

/-- info: 'Whiel.Preprocess.mem_of_mem_splitItems_push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.mem_of_mem_splitItems_push

/-- info: 'Whiel.Preprocess.bigStepEquiv_splitItems' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.bigStepEquiv_splitItems

------------------------------------------------------------
-- The Quantifier-Free Strongest Postcondition Of The Keep
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.spLoopFreeNoFresh?_seq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.spLoopFreeNoFresh?_seq

/-- info: 'Whiel.Preprocess.splitItems_keep_sp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.splitItems_keep_sp

------------------------------------------------------------
-- The Preamble Push
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.pushGuard_of_up' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.pushGuard_of_up

/-- info: 'Whiel.Preprocess.pushGuard_eval_down' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.pushGuard_eval_down

------------------------------------------------------------
-- The Push Lemma, Forward
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.pushLoop_project' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.pushLoop_project

------------------------------------------------------------
-- The Push Lemma, Backward
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.pushLoop_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.pushLoop_lift

------------------------------------------------------------
-- The Push Lemma
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.pushFramed_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.pushFramed_equivMod

/-- info: 'Whiel.Preprocess.pushFramed_flag_down' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.pushFramed_flag_down

/-- info: 'Whiel.Preprocess.pushFramed_loopFreeParts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.pushFramed_loopFreeParts

------------------------------------------------------------
-- The Loop-Head Fixed Point
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.loopHead_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.loopHead_fixed

/-- info: 'Whiel.Preprocess.loopHead_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.loopHead_exact

/-- info: 'Whiel.Preprocess.loopHead_noBoundSymbols' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.loopHead_noBoundSymbols

------------------------------------------------------------
-- The Loop-Head Assertion Of The Push
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.splitItems_mid_noBoundSymbols' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.splitItems_mid_noBoundSymbols

/-- info: 'Whiel.Preprocess.pushedPre_noBoundSymbols' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.pushedPre_noBoundSymbols

/-- info: 'Whiel.Preprocess.pushedPre_eval_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.pushedPre_eval_iff

------------------------------------------------------------
-- The Preprocessed Triple
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.pushFlag_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.pushFlag_fresh

------------------------------------------------------------
-- The Two Cases Of The Preprocessor
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.preprocess_eq_of_no_push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.preprocess_eq_of_no_push

/-- info: 'Whiel.Preprocess.preprocess_eq_of_push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.preprocess_eq_of_push

/-- info: 'Whiel.Preprocess.preprocess_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.preprocess_equivMod

/-- info: 'Whiel.Preprocess.preprocess_push_flag_down' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.preprocess_push_flag_down

/-- info: 'Whiel.Preprocess.preprocess_loopFreeParts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.preprocess_loopFreeParts

/-- info: 'Whiel.Preprocess.loops_preprocess_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.loops_preprocess_unfold

/-- info: 'Whiel.Preprocess.preprocess_pre_noBoundSymbols' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.preprocess_pre_noBoundSymbols

------------------------------------------------------------
-- The Input Schema, Triple And Corpus
------------------------------------------------------------

/-- info: 'Whiel.Tests.PreprocessPreamble.preNoBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessPreamble.preNoBound

/-- info: 'Whiel.Tests.PreprocessPreamble.postNoBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessPreamble.postNoBound

------------------------------------------------------------
-- The Same Pins In The Kernel
------------------------------------------------------------

/-- info: 'Whiel.Tests.PreprocessPreamble.progSafe_ids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessPreamble.progSafe_ids

/-- info: 'Whiel.Tests.PreprocessPreamble.progSafe_split_push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessPreamble.progSafe_split_push

/-- info: 'Whiel.Tests.PreprocessPreamble.progSafe_loops' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessPreamble.progSafe_loops

/-- info: 'Whiel.Tests.PreprocessPreamble.progPush_ids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessPreamble.progPush_ids

/-- info: 'Whiel.Tests.PreprocessPreamble.progPush_split_keep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessPreamble.progPush_split_keep

/-- info: 'Whiel.Tests.PreprocessPreamble.progPush_loops' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessPreamble.progPush_loops

------------------------------------------------------------
-- The Shape And The Correctness Of The Output
------------------------------------------------------------

/-- info: 'Whiel.Tests.PreprocessPreamble.progSafe_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessPreamble.progSafe_equivMod

/-- info: 'Whiel.Tests.PreprocessPreamble.progPush_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessPreamble.progPush_equivMod

/-- info: 'Whiel.Tests.PreprocessPreamble.progWorked_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessPreamble.progWorked_equivMod

/-- info: 'Whiel.Tests.PreprocessPreamble.progPush_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessPreamble.progPush_transfer

/-- info: 'Whiel.Tests.PreprocessPreamble.progWorked_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessPreamble.progWorked_transfer
