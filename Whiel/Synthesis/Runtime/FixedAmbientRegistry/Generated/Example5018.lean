-- Generated fixed-ambient registry format: 1
import Benchmark.Example5018.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example5018

open Benchmark.Example5018

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example5018"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example5018.Input"
  namespaceName :=
    "Whiel.Benchmark.Example5018"
  sourceSha256 :=
    "41b4bedaf3919ad5990364bcfb2337d5" ++
      "c011d11f64068f48322dccf4defca400"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example5018.inputPre,
    Whiel.Benchmark.Example5018.inputCmd,
    Whiel.Benchmark.Example5018.inputPost,
    Whiel.Benchmark.Example5018.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example5018
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
