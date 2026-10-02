-- Author: Jesse Comer
import Whiel.Preprocess.Transfer

/-
  Explicit axiom audit for the transfer theorem and the
  refutation corollary of the generic preprocessor.

  Every theorem of `Whiel/Preprocess/Transfer.lean` is
  audited here. Every one depends on the standard three
  axioms or fewer.
-/

set_option linter.hashCommand false

------------------------------------------------------------
-- A Framed Loop As A Program
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.programOfFramed_cmd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.programOfFramed_cmd

/-- info: 'Whiel.Preprocess.programOfFramed_initialInstance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.programOfFramed_initialInstance

/-- info: 'Whiel.Preprocess.programOfFramed_observe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.programOfFramed_observe

/-- info: 'Whiel.Preprocess.bigStep_programOfFramed_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.bigStep_programOfFramed_iff

------------------------------------------------------------
-- The Closing Assertion
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.closingAssertion_noBoundSymbols' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.closingAssertion_noBoundSymbols

------------------------------------------------------------
-- The Transfer Theorem
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.transfer_of_loopHead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.transfer_of_loopHead

/-- info: 'Whiel.Preprocess.hoareValid_of_transfer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoareValid_of_transfer

------------------------------------------------------------
-- The Refutation Corollary
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.refutation_of_loopHead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.refutation_of_loopHead

/-- info: 'Whiel.Preprocess.not_hoareValid_of_loopHead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.not_hoareValid_of_loopHead

------------------------------------------------------------
-- Nested Lifts And Projections
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.project_lift_trans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.project_lift_trans

/-- info: 'Whiel.Preprocess.bigStep_raise_self_of_up' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.bigStep_raise_self_of_up

/-- info: 'Whiel.Preprocess.bigStep_retag_self_of_project_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.bigStep_retag_self_of_project_self

------------------------------------------------------------
-- The Loop Head Of The Preprocessor
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.keptPrefix_loopFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.keptPrefix_loopFree

/-- info: 'Whiel.Preprocess.keptPrefix_sp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.keptPrefix_sp

/-- info: 'Whiel.Preprocess.bigStepEquiv_keptPrefix_of_no_push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.bigStepEquiv_keptPrefix_of_no_push

------------------------------------------------------------
-- Transfer For The Preprocessor, No Push
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.loopHead_of_no_push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.loopHead_of_no_push

/-- info: 'Whiel.Preprocess.loopHeadFixed_of_no_push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.loopHeadFixed_of_no_push

------------------------------------------------------------
-- Transfer For The Preprocessor, After A Push
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.loopHead_of_push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.loopHead_of_push

/-- info: 'Whiel.Preprocess.loopHeadFixed_of_push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.loopHeadFixed_of_push

------------------------------------------------------------
-- Theorem "Transfer" And Corollary "Refutation Transfer"
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.preprocess_close_loopFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.preprocess_close_loopFree

/-- info: 'Whiel.Preprocess.preprocess_loopHead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.preprocess_loopHead

/-- info: 'Whiel.Preprocess.preprocess_loopHead_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.preprocess_loopHead_fixed

/-- info: 'Whiel.Preprocess.preprocess_transfer_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.preprocess_transfer_program

/-- info: 'Whiel.Preprocess.preprocess_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.preprocess_transfer

/-- info: 'Whiel.Preprocess.preprocess_refutation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.preprocess_refutation

/-- info: 'Whiel.Preprocess.preprocess_not_hoareValid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.preprocess_not_hoareValid
