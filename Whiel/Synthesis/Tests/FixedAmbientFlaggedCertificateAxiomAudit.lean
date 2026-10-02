-- Author: Jesse Comer
import Benchmark.FlaggedEmissions.Certificate.Valid

/-
  Explicit scratch-overlay gate. The driver emits and builds
  its imported certificate before checking this file. It is
  intentionally outside the ordinary test aggregate.
-/

namespace Whiel.Synthesis.Tests.FixedAmbientFlaggedAudit

open FixedAmbientFlaggedFixture

/- The actual emitted theorem at the original fixture type. -/
example : HoareValid inputPre inputCmd inputPost :=
  Benchmark.FlaggedEmissions.Certificate.input_hoare_triple_valid

end Whiel.Synthesis.Tests.FixedAmbientFlaggedAudit

/-- info: 'Whiel.Benchmark.FlaggedEmissions.Certificate.input_hoare_triple_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Whiel.Benchmark.FlaggedEmissions.Certificate.input_hoare_triple_valid
