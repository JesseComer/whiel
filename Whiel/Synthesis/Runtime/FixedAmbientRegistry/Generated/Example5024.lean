-- Generated fixed-ambient registry format: 1
import Benchmark.Example5024.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example5024

open Benchmark.Example5024

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example5024"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example5024.Input"
  namespaceName :=
    "Whiel.Benchmark.Example5024"
  sourceSha256 :=
    "7003cb2f4a95b0bd84b4c9298be3f849" ++
      "9228112eb2d6a0154ec1b35f756faf81"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example5024.inputPre,
    Whiel.Benchmark.Example5024.inputCmd,
    Whiel.Benchmark.Example5024.inputPost,
    Whiel.Benchmark.Example5024.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example5024
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
