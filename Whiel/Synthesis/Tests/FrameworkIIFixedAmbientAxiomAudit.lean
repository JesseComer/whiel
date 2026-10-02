-- Author: Jesse Comer
import Whiel.Synthesis.Tests.FrameworkIIFixedAmbient
import Whiel.Synthesis.FrameworkII.FixedAmbient.Precondition
import Whiel.Synthesis.FrameworkII.FixedAmbient.CertificateJobs

/- Axiom audit for same-schema Framework-II assembly. -/

open Whiel.Synthesis.FrameworkII.FixedAmbient

/-- info: 'Whiel.Synthesis.FrameworkII.FixedAmbient.LeveledFamily.hoareValid_of_valid_vcs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeveledFamily.hoareValid_of_valid_vcs

/-- info: 'Whiel.Synthesis.FrameworkII.FixedAmbient.Preproc.certifyInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Preproc.certifyInput

/-- info: 'Whiel.Synthesis.FrameworkII.FixedAmbient.LoopTriple.valid_of_valid_vcs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LoopTriple.valid_of_valid_vcs

/-- info: 'Whiel.Synthesis.FrameworkII.FixedAmbient.Preproc.certifyProgramInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Preproc.certifyProgramInput

/-- info: 'Whiel.Synthesis.FrameworkII.FixedAmbient.Preproc.certifyProgramInput_of_clauseProofs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Preproc.certifyProgramInput_of_clauseProofs

/-- info: 'Whiel.Hoare.LoopTriple.hoareValid_of_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Hoare.LoopTriple.hoareValid_of_lift

/-- info: 'Whiel.Hoare.liftedTask' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Whiel.Hoare.liftedTask

/-- info: 'Whiel.Synthesis.FrameworkII.FixedAmbient.EdbPrecondition.initVC_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EdbPrecondition.initVC_valid

/-- info: 'Whiel.Synthesis.FrameworkII.FixedAmbient.EdbPrecondition.maintenanceVC_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EdbPrecondition.maintenanceVC_valid

open Whiel.Synthesis.Tests.FrameworkIIFixedAmbient

/-- info: 'Whiel.Synthesis.Tests.FrameworkIIFixedAmbient.exact_jobs_assemble' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exact_jobs_assemble

/-- info: 'Whiel.Synthesis.Tests.FrameworkIIFixedAmbient.program_input_assembles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms program_input_assembles
