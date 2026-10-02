-- Author: Jesse Comer
import Whiel.Preprocess.Clean

/-
  Explicit axiom audit for the final clean of the generic
  preprocessor.

  Every theorem of `Whiel/Preprocess/Clean.lean` is audited
  here. Every one depends on the standard three axioms or
  fewer.
-/

set_option linter.hashCommand false

------------------------------------------------------------
-- Cleaning Adds No Relation Symbol
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.rawSymbols_mergeSelections_select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.rawSymbols_mergeSelections_select

/-- info: 'Whiel.Preprocess.rawSymbols_mergeSelections_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.rawSymbols_mergeSelections_subset

/-- info: 'Whiel.Preprocess.rawSymbols_cleanVacuousProducts_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.rawSymbols_cleanVacuousProducts_subset

/-- info: 'Whiel.Preprocess.rawSymbols_cleanVacuousUnions_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.rawSymbols_cleanVacuousUnions_subset

/-- info: 'Whiel.Preprocess.rawSymbols_cleanVacuousProjections_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.rawSymbols_cleanVacuousProjections_subset

/-- info: 'Whiel.Preprocess.raSymbols_clean_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.raSymbols_clean_subset

------------------------------------------------------------
-- Cleaning A Guard And A Command
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.guardSymbols_cleanAnd_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.guardSymbols_cleanAnd_subset

/-- info: 'Whiel.Preprocess.guardSymbols_cleanOr_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.guardSymbols_cleanOr_subset

/-- info: 'Whiel.Preprocess.guardSymbols_cleanNot_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.guardSymbols_cleanNot_subset

/-- info: 'Whiel.Preprocess.guardSymbols_clean_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.guardSymbols_clean_subset

/-- info: 'Whiel.Preprocess.symbols_cleanSeq_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.symbols_cleanSeq_subset

/-- info: 'Whiel.Preprocess.symbols_clean_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.symbols_clean_subset

------------------------------------------------------------
-- Cleaning Adds No Loop
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.loopFree_cleanSeq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.loopFree_cleanSeq

/-- info: 'Whiel.Preprocess.loopFree_clean' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.loopFree_clean

------------------------------------------------------------
-- The Final Clean Of A Framed Loop
------------------------------------------------------------

/-- info: 'Whiel.Preprocess.bigStep_while_congr_body' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.bigStep_while_congr_body

/-- info: 'Whiel.Preprocess.Framed.clean_init' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.Framed.clean_init

/-- info: 'Whiel.Preprocess.Framed.clean_guard' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.Framed.clean_guard

/-- info: 'Whiel.Preprocess.Framed.clean_body' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.Framed.clean_body

/-- info: 'Whiel.Preprocess.Framed.clean_close' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.Framed.clean_close

/-- info: 'Whiel.Preprocess.Framed.bigStepEquiv_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.Framed.bigStepEquiv_clean

/-- info: 'Whiel.Preprocess.Framed.loopFreeParts_clean' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.Framed.loopFreeParts_clean

/-- info: 'Whiel.Preprocess.Framed.symbols_unfold_clean_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.Framed.symbols_unfold_clean_subset

/-- info: 'Whiel.Preprocess.Framed.assignedSymbols_unfold_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Preprocess.Framed.assignedSymbols_unfold_clean
