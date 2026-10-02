-- Author: Jesse Comer
import Whiel.Tests.PreprocessHoist

/-
  Explicit axiom audit for the conditional hoist of the
  generic preprocessor.

  Every theorem of `Whiel/Preprocess/Hoist.lean` and
  `Whiel/Tests/PreprocessHoist.lean` is audited here.
  Every one depends on the standard three axioms or fewer.
-/

set_option linter.hashCommand false

------------------------------------------------------------
-- The Hoist Operations
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.hoistOf_init' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistOf_init

/-- info: 'Whiel.Preprocess.hoistOf_close' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistOf_close

/-- info: 'Whiel.Preprocess.hoistIte_eq_flagFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistIte_eq_flagFree

/-- info: 'Whiel.Preprocess.hoistIte_eq_elseLoop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistIte_eq_elseLoop

/-- info: 'Whiel.Preprocess.hoistIte_eq_thenLoop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistIte_eq_thenLoop

/-- info: 'Whiel.Preprocess.hoistIte_eq_general' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistIte_eq_general

------------------------------------------------------------
-- Lowering A Flag In A Prefix
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.flagInit_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flagInit_lower

------------------------------------------------------------
-- Loops Under A Stable Condition
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.bigStep_while_eq_of_not_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.bigStep_while_eq_of_not_eval

/-- info: 'Whiel.Preprocess.bigStep_unfold_iff_of_isBase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.bigStep_unfold_iff_of_isBase

/-- info: 'Whiel.Preprocess.flagLoop_project' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flagLoop_project

/-- info: 'Whiel.Preprocess.flagLoop_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flagLoop_lift

------------------------------------------------------------
-- The Guards And Bodies Of The Hoisted Loop
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.hoistGuard_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistGuard_iff

/-- info: 'Whiel.Preprocess.hoistGuard_eval_up' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistGuard_eval_up

/-- info: 'Whiel.Preprocess.hoistGuard_eval_down' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistGuard_eval_down

/-- info: 'Whiel.Preprocess.hoistThenGuard_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistThenGuard_iff

/-- info: 'Whiel.Preprocess.hoistElseGuard_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistElseGuard_iff

/-- info: 'Whiel.Preprocess.hoistBody_iff_up' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistBody_iff_up

/-- info: 'Whiel.Preprocess.hoistBody_iff_down' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistBody_iff_down

/-- info: 'Whiel.Preprocess.hoist_up_pres' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoist_up_pres

/-- info: 'Whiel.Preprocess.hoist_down_pres' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoist_down_pres

------------------------------------------------------------
-- The Hoist Lemma
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.hoistOf_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistOf_equivMod

/-- info: 'Whiel.Preprocess.hoistOf_flag_records_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistOf_flag_records_branch

------------------------------------------------------------
-- The General Hoist
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.hoistGeneral_project_up' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistGeneral_project_up

/-- info: 'Whiel.Preprocess.hoistGeneral_project_down' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistGeneral_project_down

/-- info: 'Whiel.Preprocess.hoistGeneral_lift_up' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistGeneral_lift_up

/-- info: 'Whiel.Preprocess.hoistGeneral_lift_down' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistGeneral_lift_down

/-- info: 'Whiel.Preprocess.hoistGeneral_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistGeneral_equivMod

/-- info: 'Whiel.Preprocess.hoistGeneral_flag_records_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistGeneral_flag_records_branch

------------------------------------------------------------
-- The One-Branch Hoists
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.hoistThenLoop_project_up' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistThenLoop_project_up

/-- info: 'Whiel.Preprocess.hoistThenLoop_project_down' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistThenLoop_project_down

/-- info: 'Whiel.Preprocess.hoistThenLoop_lift_up' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistThenLoop_lift_up

/-- info: 'Whiel.Preprocess.hoistThenLoop_lift_down' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistThenLoop_lift_down

/-- info: 'Whiel.Preprocess.hoistThenLoop_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistThenLoop_equivMod

/-- info: 'Whiel.Preprocess.hoistThenLoop_flag_records_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistThenLoop_flag_records_branch

/-- info: 'Whiel.Preprocess.hoistElseLoop_project_down' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistElseLoop_project_down

/-- info: 'Whiel.Preprocess.hoistElseLoop_project_up' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistElseLoop_project_up

/-- info: 'Whiel.Preprocess.hoistElseLoop_lift_down' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistElseLoop_lift_down

/-- info: 'Whiel.Preprocess.hoistElseLoop_lift_up' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistElseLoop_lift_up

/-- info: 'Whiel.Preprocess.hoistElseLoop_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistElseLoop_equivMod

/-- info: 'Whiel.Preprocess.hoistElseLoop_flag_records_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistElseLoop_flag_records_branch

------------------------------------------------------------
-- The Flag-Free Hoist
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.hoistFlagFree_bigStepEquiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistFlagFree_bigStepEquiv

/-- info: 'Whiel.Preprocess.hoistFlagFree_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistFlagFree_equivMod

------------------------------------------------------------
-- The Dispatcher
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.hoistIte_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistIte_equivMod

/-- info: 'Whiel.Preprocess.hoistIte_flag_records_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistIte_flag_records_branch

------------------------------------------------------------
-- Loop-Freeness Of The Hoisted Components
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.loopFree_of_retag' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.loopFree_of_retag

/-- info: 'Whiel.Preprocess.hoistInit_loopFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistInit_loopFree

/-- info: 'Whiel.Preprocess.hoistClose_loopFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistClose_loopFree

/-- info: 'Whiel.Preprocess.hoistGeneral_loopFreeParts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistGeneral_loopFreeParts

/-- info: 'Whiel.Preprocess.hoistThenLoop_loopFreeParts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistThenLoop_loopFreeParts

/-- info: 'Whiel.Preprocess.hoistElseLoop_loopFreeParts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistElseLoop_loopFreeParts

/-- info: 'Whiel.Preprocess.hoistFlagFree_loopFreeParts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistFlagFree_loopFreeParts

/-- info: 'Whiel.Preprocess.hoistIte_loopFreeParts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.hoistIte_loopFreeParts

------------------------------------------------------------
-- Test Corpus For The Hoist
------------------------------------------------------------

/-- info: 'Whiel.Tests.PreprocessHoist.generalCase_toRaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessHoist.generalCase_toRaw

/-- info: 'Whiel.Tests.PreprocessHoist.generalCase_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessHoist.generalCase_equivMod

/-- info: 'Whiel.Tests.PreprocessHoist.generalCase_records_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessHoist.generalCase_records_branch

/-- info: 'Whiel.Tests.PreprocessHoist.thenLoopCase_toRaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessHoist.thenLoopCase_toRaw

/-- info: 'Whiel.Tests.PreprocessHoist.thenLoopCase_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessHoist.thenLoopCase_equivMod

/-- info: 'Whiel.Tests.PreprocessHoist.thenLoopCase_records_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessHoist.thenLoopCase_records_branch

/-- info: 'Whiel.Tests.PreprocessHoist.elseLoopCase_toRaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessHoist.elseLoopCase_toRaw

/-- info: 'Whiel.Tests.PreprocessHoist.elseLoopCase_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessHoist.elseLoopCase_equivMod

/-- info: 'Whiel.Tests.PreprocessHoist.elseLoopCase_records_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessHoist.elseLoopCase_records_branch

/-- info: 'Whiel.Tests.PreprocessHoist.flagFreeCase_toRaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessHoist.flagFreeCase_toRaw

/-- info: 'Whiel.Tests.PreprocessHoist.flagFreeCase_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessHoist.flagFreeCase_equivMod

/-- info: 'Whiel.Tests.PreprocessHoist.hoistIte_reduces_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessHoist.hoistIte_reduces_general

/-- info: 'Whiel.Tests.PreprocessHoist.hoistIte_reduces_thenLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessHoist.hoistIte_reduces_thenLoop

/-- info: 'Whiel.Tests.PreprocessHoist.hoistIte_reduces_elseLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessHoist.hoistIte_reduces_elseLoop

/-- info: 'Whiel.Tests.PreprocessHoist.hoistIte_reduces_flagFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessHoist.hoistIte_reduces_flagFree

/-- info: 'Whiel.Tests.PreprocessHoist.hoistIte_parts_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessHoist.hoistIte_parts_general

/-- info: 'Whiel.Tests.PreprocessHoist.hoistIte_parts_thenLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessHoist.hoistIte_parts_thenLoop

/-- info: 'Whiel.Tests.PreprocessHoist.hoistIte_parts_flagFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessHoist.hoistIte_parts_flagFree
