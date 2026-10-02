-- Generated fixed-ambient registry format: 1
import Benchmark.Example5036.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example5036

open Benchmark.Example5036

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example5036"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example5036.Input"
  namespaceName :=
    "Whiel.Benchmark.Example5036"
  sourceSha256 :=
    "33cc982829372569d86240a640e537c1" ++
      "74ebbdf59dc9155e34fe40a176fcdefd"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example5036.inputPre,
    Whiel.Benchmark.Example5036.inputCmd,
    Whiel.Benchmark.Example5036.inputPost,
    Whiel.Benchmark.Example5036.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example5036
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
