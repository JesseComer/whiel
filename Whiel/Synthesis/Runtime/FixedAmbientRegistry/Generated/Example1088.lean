-- Generated fixed-ambient registry format: 1
import Benchmark.Example1088.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example1088

open Benchmark.Example1088

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example1088"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example1088.Input"
  namespaceName :=
    "Whiel.Benchmark.Example1088"
  sourceSha256 :=
    "281e58900ba8fe777c4a1b7ede1cf04f" ++
      "425691bb577b36372cbb00596e04ced1"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example1088.inputPre,
    Whiel.Benchmark.Example1088.inputCmd,
    Whiel.Benchmark.Example1088.inputPost,
    Whiel.Benchmark.Example1088.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example1088
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
