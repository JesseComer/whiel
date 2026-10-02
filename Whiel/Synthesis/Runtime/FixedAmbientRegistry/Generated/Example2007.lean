-- Generated fixed-ambient registry format: 1
import Benchmark.Example2007.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example2007

open Benchmark.Example2007

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example2007"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example2007.Input"
  namespaceName :=
    "Whiel.Benchmark.Example2007"
  sourceSha256 :=
    "2d2bd314f6481b08e44c76f515aabb55" ++
      "97c90e3d56d90fd76763a8d408ec098d"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example2007.inputPre,
    Whiel.Benchmark.Example2007.inputCmd,
    Whiel.Benchmark.Example2007.inputPost,
    Whiel.Benchmark.Example2007.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example2007
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
