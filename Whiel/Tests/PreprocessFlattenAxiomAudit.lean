-- Author: Jesse Comer
import Whiel.Tests.PreprocessFlatten

/-
  Explicit axiom audit for the loop flattening of the
  generic preprocessor.

  Every theorem of `Whiel/Preprocess/Flatten.lean` and
  `Whiel/Tests/PreprocessFlatten.lean` is audited here.
  Every one depends on the standard three axioms or fewer.
-/

set_option linter.hashCommand false

------------------------------------------------------------
-- The Flatten Operations
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.flattenWhile_eq_idem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flattenWhile_eq_idem

/-- info: 'Whiel.Preprocess.flattenWhile_eq_loopFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flattenWhile_eq_loopFree

/-- info: 'Whiel.Preprocess.flattenWhile_eq_general' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flattenWhile_eq_general

------------------------------------------------------------
-- The Merged Guard And The Flatten Prefix
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.flattenGuard_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flattenGuard_iff

/-- info: 'Whiel.Preprocess.flattenGuard_of_up' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flattenGuard_of_up

/-- info: 'Whiel.Preprocess.flattenGuard_eval_down' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flattenGuard_eval_down

/-- info: 'Whiel.Preprocess.flattenInit_lowers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flattenInit_lowers

------------------------------------------------------------
-- Idempotent Nesting
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.not_eval_of_bigStep_while' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.not_eval_of_bigStep_while

/-- info: 'Whiel.Preprocess.while_idem_bigStepEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.while_idem_bigStepEquiv

/-- info: 'Whiel.Preprocess.bigStepEquiv_while' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.bigStepEquiv_while

------------------------------------------------------------
-- The Flatten Lemma, Forward
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.flattenGeneral_project' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flattenGeneral_project

------------------------------------------------------------
-- The Flatten Lemma, Backward
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.flattenGeneral_lift_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flattenGeneral_lift_inner

/-- info: 'Whiel.Preprocess.flattenGeneral_lift_outer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flattenGeneral_lift_outer

------------------------------------------------------------
-- The Flatten Lemma
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.flattenGeneral_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flattenGeneral_equivMod

/-- info: 'Whiel.Preprocess.flattenGeneral_flag_down' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flattenGeneral_flag_down

------------------------------------------------------------
-- The Flag-Free Flattenings
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.flattenLoopFree_bigStepEquiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flattenLoopFree_bigStepEquiv

/-- info: 'Whiel.Preprocess.flattenLoopFree_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flattenLoopFree_equivMod

/-- info: 'Whiel.Preprocess.flattenIdem_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flattenIdem_equivMod

------------------------------------------------------------
-- The Dispatcher
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.flattenWhile_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flattenWhile_equivMod

------------------------------------------------------------
-- Loop-Freeness Of The Flattened Components
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.flattenGeneral_loopFreeParts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flattenGeneral_loopFreeParts

/-- info: 'Whiel.Preprocess.flattenLoopFree_loopFreeParts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flattenLoopFree_loopFreeParts

/-- info: 'Whiel.Preprocess.flattenWhile_loopFreeParts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.flattenWhile_loopFreeParts

------------------------------------------------------------
-- The Source Body Carries A Loop
------------------------------------------------------------

/-- info: 'Whiel.Tests.PreprocessFlatten.generalCase_toRaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessFlatten.generalCase_toRaw

/-- info: 'Whiel.Tests.PreprocessFlatten.generalCase_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessFlatten.generalCase_equivMod

/-- info: 'Whiel.Tests.PreprocessFlatten.generalCase_flag_down' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessFlatten.generalCase_flag_down

------------------------------------------------------------
-- A Loop-Free Source Body
------------------------------------------------------------

/-- info: 'Whiel.Tests.PreprocessFlatten.loopFreeCase_toRaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessFlatten.loopFreeCase_toRaw

/-- info: 'Whiel.Tests.PreprocessFlatten.loopFreeCase_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessFlatten.loopFreeCase_equivMod

------------------------------------------------------------
-- Idempotent Nesting
------------------------------------------------------------

/-- info: 'Whiel.Tests.PreprocessFlatten.idem_bigStepEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessFlatten.idem_bigStepEquiv

/-- info: 'Whiel.Tests.PreprocessFlatten.idemCase_toRaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessFlatten.idemCase_toRaw

/-- info: 'Whiel.Tests.PreprocessFlatten.idemCase_equivMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessFlatten.idemCase_equivMod

------------------------------------------------------------
-- Reduction Of The Transformation
------------------------------------------------------------

/-- info: 'Whiel.Tests.PreprocessFlatten.flattenWhile_reduces_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessFlatten.flattenWhile_reduces_general

/-- info: 'Whiel.Tests.PreprocessFlatten.flattenWhile_reduces_loopFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessFlatten.flattenWhile_reduces_loopFree

/-- info: 'Whiel.Tests.PreprocessFlatten.flattenWhile_reduces_idem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessFlatten.flattenWhile_reduces_idem

/-- info: 'Whiel.Tests.PreprocessFlatten.flattenWhile_parts_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessFlatten.flattenWhile_parts_general

/-- info: 'Whiel.Tests.PreprocessFlatten.flattenWhile_parts_loopFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessFlatten.flattenWhile_parts_loopFree

/-- info: 'Whiel.Tests.PreprocessFlatten.flattenWhile_parts_idem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Tests.PreprocessFlatten.flattenWhile_parts_idem
