-- Author: Jesse Comer
import Whiel.Hoare.ProphecyFreeInitialization

/-
  Axiom audit for initialization finality of prophecy-free
  clauses.
-/

------------------------------------------------------------
-- Prophecy-Free Initialization Axiom Audit
------------------------------------------------------------

open Whiel.Hoare.FixedAmbientProphecy

/-- info: 'Whiel.Hoare.FixedAmbientProphecy.initValid_of_initZeroValid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms initValid_of_initZeroValid

/-- info: 'Whiel.Hoare.FixedAmbientProphecy.prophecyFree_holds_on_halting_of_vcs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prophecyFree_holds_on_halting_of_vcs

/-- info: 'Whiel.Hoare.FixedAmbientProphecy.prophecyFree_holds_on_halting_of_initValid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prophecyFree_holds_on_halting_of_initValid
