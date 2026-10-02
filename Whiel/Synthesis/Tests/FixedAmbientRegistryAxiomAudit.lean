-- Author: Jesse Comer
import Whiel.Synthesis.Tests.FixedAmbientRegistry
import Whiel.Synthesis.Runtime.FixedAmbientWorker

/- Axiom audit for the exact registry assembly. The
   per-entry preprocessing theorems are audited in the
   generated `FixedAmbientRegistryCaseAxiomAudit.lean`. -/

open Whiel.Synthesis.Tests.FixedAmbientRegistryTest
open Whiel.Synthesis.Runtime.FixedAmbientRegistry.Example0001

/-- info: 'Whiel.Synthesis.Tests.FixedAmbientRegistryTest.registry_supply_free_preprocessing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms registry_supply_free_preprocessing

/-- info: 'Whiel.Synthesis.Tests.FixedAmbientRegistryTest.refutable_supply_free_preprocessing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms refutable_supply_free_preprocessing

/-- info: 'Whiel.Synthesis.Tests.FixedAmbientRegistryTest.exact_input_of_worker_vcs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exact_input_of_worker_vcs

/-- info: 'Whiel.Synthesis.FrameworkII.FixedAmbient.Preproc.certifyProgramInput_of_clauseProofs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Synthesis.FrameworkII.FixedAmbient.Preproc.certifyProgramInput_of_clauseProofs
