-- Author: Jesse Comer
import Whiel.Tests.FixedAmbientProphecy

/-
  Explicit axiom audit for the fixed-ambient Framework-II
  foundation and its exact raw Hoare canary.
-/

------------------------------------------------------------
-- Fixed-Ambient Axiom Audit
------------------------------------------------------------

open Whiel.Hoare.FixedAmbientProphecy

#print axioms hoareValid_while_of_leveled_vcs

open Whiel.Hoare.WhielNamesProphecy.Task

#print axioms semanticCollapse_exitLift

open Whiel.Tests.FixedAmbientProphecyCanary

#print axioms inputTriple_valid
