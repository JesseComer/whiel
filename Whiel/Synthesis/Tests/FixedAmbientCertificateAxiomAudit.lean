-- Author: Jesse Comer
import Benchmark.Example0001.Certificate.ProposalBinding
import Benchmark.Example0001.Certificate.Valid
import Benchmark.Example0013.Certificate.Invalid
import Benchmark.Example4001.Certificate.Valid
import Benchmark.Example4041.Certificate.Valid
import Benchmark.Example4002.Certificate.Invalid
import Benchmark.Example4037.Certificate.Invalid
import Whiel.Synthesis.FrameworkII.FixedAmbient.CertificateEmitter
import
  Whiel.Synthesis.FrameworkII.FixedAmbient.DictionarySoundness

/-
  Axiom audit for the emitted fixed-ambient certificates,
  valid and invalid, and the Lean theorems every certificate
  applies. Each must report exactly std3: `propext`,
  `Classical.choice`, and `Quot.sound`.
-/

/-- info: 'Whiel.Benchmark.Example0001.Certificate.input_hoare_triple_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Benchmark.Example0001.Certificate.input_hoare_triple_valid

/-- info: 'Whiel.Benchmark.Example4001.Certificate.input_hoare_triple_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Benchmark.Example4001.Certificate.input_hoare_triple_valid

/-- info: 'Whiel.Benchmark.Example4041.Certificate.input_hoare_triple_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Benchmark.Example4041.Certificate.input_hoare_triple_valid

/-- info: 'Whiel.Benchmark.Example0013.Certificate.input_hoare_triple_invalid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Benchmark.Example0013.Certificate.input_hoare_triple_invalid

/-- info: 'Whiel.Benchmark.Example4002.Certificate.input_hoare_triple_invalid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Benchmark.Example4002.Certificate.input_hoare_triple_invalid

/-- info: 'Whiel.Benchmark.Example4037.Certificate.input_hoare_triple_invalid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Benchmark.Example4037.Certificate.input_hoare_triple_invalid

/-- info: 'Whiel.Hoare.CounterExample.certifyKernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Hoare.CounterExample.certifyKernel

/-- info: 'Whiel.Hoare.CounterExample.invalid_of_kernelRefutes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Hoare.CounterExample.invalid_of_kernelRefutes

/-- info: 'Whiel.CmdFuel.evalCount_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.CmdFuel.evalCount_fst

/-- info: 'Whiel.CmdFuel.eval_halted_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.CmdFuel.eval_halted_mono

/-- info: 'Whiel.CmdFuel.eval_evalConsumed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.CmdFuel.eval_evalConsumed

/-- info: 'Whiel.Hoare.CounterExample.kernelRefutes_evalConsumed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Hoare.CounterExample.kernelRefutes_evalConsumed

/-- info: 'Whiel.Benchmark.Example0001.Certificate.initShallow0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Benchmark.Example0001.Certificate.initShallow0

/-- info: 'Whiel.Benchmark.Example0001.Certificate.initValid0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Benchmark.Example0001.Certificate.initValid0

/-- info: 'Whiel.Benchmark.Example0001.Certificate.maintValid1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Benchmark.Example0001.Certificate.maintValid1

/-- info: 'Whiel.Benchmark.Example0001.Certificate.termValid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Benchmark.Example0001.Certificate.termValid

/-- info: 'Whiel.Synthesis.FrameworkII.FixedAmbient.CertificateJob.valid_of_fullProof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Synthesis.FrameworkII.FixedAmbient.CertificateJob.valid_of_fullProof

/-- info: 'Whiel.Synthesis.FrameworkII.FixedAmbient.CertificateJob.closedEntailment_eq_ofLists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Synthesis.FrameworkII.FixedAmbient.CertificateJob.closedEntailment_eq_ofLists

/-- info: 'Whiel.Synthesis.FrameworkII.FixedAmbient.Preproc.certifyProgramInput_of_clauseProofs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Synthesis.FrameworkII.FixedAmbient.Preproc.certifyProgramInput_of_clauseProofs

/-- info: 'Whiel.Hoare.LoopTriple.hoareValid_of_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Hoare.LoopTriple.hoareValid_of_lift

/-- info: 'Whiel.Hoare.liftedTask' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Hoare.liftedTask

/-- info: 'Whiel.Synthesis.FrameworkII.FixedAmbient.PreconditionRowConfirmation.initVC_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Synthesis.FrameworkII.FixedAmbient.PreconditionRowConfirmation.initVC_valid

/-- info: 'Whiel.Synthesis.FrameworkII.FixedAmbient.PreconditionRowConfirmation.maintenanceVC_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Synthesis.FrameworkII.FixedAmbient.PreconditionRowConfirmation.maintenanceVC_valid

/-
  The semantic dictionary's reuse rules
  (`DictionarySoundness.lean`). The dictionary has no
  certificate influence, but every rule it applies is one of
  these theorems; each reports at most std3.
-/

/-- info: 'QFEntailment.valid_of_axioms_subset' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  QFEntailment.valid_of_axioms_subset

/-- info: 'QFEntailment.fullTaggedSet_hit_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  QFEntailment.fullTaggedSet_hit_sound

/-- info: 'QFEntailment.not_valid_of_countermodel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  QFEntailment.not_valid_of_countermodel

/-- info: 'QFEntailment.countermodel_of_axioms_subset' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  QFEntailment.countermodel_of_axioms_subset

/-- info: 'QFEntailment.valid_iff_validOnNonempty_and_validOnEmpty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  QFEntailment.valid_iff_validOnNonempty_and_validOnEmpty

/-- info: 'QFEntailment.validOnNonempty_of_axioms_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  QFEntailment.validOnNonempty_of_axioms_subset

/-- info: 'QFEntailment.valid_of_proofHit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  QFEntailment.valid_of_proofHit

/-- info: 'Whiel.QFAssertExpr.BodyInvariant.not' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.QFAssertExpr.BodyInvariant.not

/-- info: 'Whiel.QFAssertExpr.wpLoopFree_valid_of_bodyInvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.QFAssertExpr.wpLoopFree_valid_of_bodyInvariant

/-- info: 'Whiel.Hoare.WhielNamesProphecy.Task.semanticCollapse_eq_of_bigStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Hoare.WhielNamesProphecy.Task.semanticCollapse_eq_of_bigStep

/-- info: 'Whiel.Hoare.WhielNamesProphecy.Task.theta_bodyInvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Hoare.WhielNamesProphecy.Task.theta_bodyInvariant

/-- info: 'Whiel.Synthesis.FrameworkII.FixedAmbient.ProphecyContext.premises_bodyInvariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Synthesis.FrameworkII.FixedAmbient.ProphecyContext.premises_bodyInvariant

/-- info: 'Whiel.Synthesis.FrameworkII.FixedAmbient.LeveledFamily.maintenanceVC_valid_of_initProof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Synthesis.FrameworkII.FixedAmbient.LeveledFamily.maintenanceVC_valid_of_initProof

/-- info: 'Whiel.Synthesis.FrameworkII.FixedAmbient.LeveledFamily.initVC_zero_axioms_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Synthesis.FrameworkII.FixedAmbient.LeveledFamily.initVC_zero_axioms_subset

/-- info: 'Whiel.Synthesis.FrameworkII.FixedAmbient.LeveledFamily.initVC_zero_countermodel_of_countermodel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Synthesis.FrameworkII.FixedAmbient.LeveledFamily.initVC_zero_countermodel_of_countermodel

/-- info: 'Whiel.Synthesis.FrameworkII.FixedAmbient.LeveledFamily.initVC_valid_of_initObligation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Synthesis.FrameworkII.FixedAmbient.LeveledFamily.initVC_valid_of_initObligation

/-- info: 'Whiel.Synthesis.FrameworkII.FixedAmbient.LeveledFamily.not_initObligation_zero_of_countermodel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Synthesis.FrameworkII.FixedAmbient.LeveledFamily.not_initObligation_zero_of_countermodel

/-- info: 'QFEntailment.adomEmptyCounterexample?_eq_false_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  QFEntailment.adomEmptyCounterexample?_eq_false_iff

/-- info: 'QFEntailment.noEmpty_of_adomEmptyCounterexample?_eq_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  QFEntailment.noEmpty_of_adomEmptyCounterexample?_eq_false

/-- info: 'QFEntailment.validOnEmpty_iff_adomEmptyCounterexample?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  QFEntailment.validOnEmpty_iff_adomEmptyCounterexample?
