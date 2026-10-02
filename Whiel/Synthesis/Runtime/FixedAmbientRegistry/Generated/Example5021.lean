-- Generated fixed-ambient registry format: 1
import Benchmark.Example5021.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example5021

open Benchmark.Example5021

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example5021"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example5021.Input"
  namespaceName :=
    "Whiel.Benchmark.Example5021"
  sourceSha256 :=
    "9f77e5e9ab4aae12d25a87c2ea27d396" ++
      "9dc2d319ce9f27a5c35ecb7dbef66502"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example5021.inputPre,
    Whiel.Benchmark.Example5021.inputCmd,
    Whiel.Benchmark.Example5021.inputPost,
    Whiel.Benchmark.Example5021.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example5021
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
