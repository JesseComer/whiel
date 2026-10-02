-- Generated fixed-ambient registry format: 1
import Benchmark.Example4034.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example4034

open Benchmark.Example4034

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example4034"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example4034.Input"
  namespaceName :=
    "Whiel.Benchmark.Example4034"
  sourceSha256 :=
    "4255db6e9430a54bdc663ba289ce92b6" ++
      "6bece9b87893a6e1439ba400b733fab6"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example4034.inputPre,
    Whiel.Benchmark.Example4034.inputCmd,
    Whiel.Benchmark.Example4034.inputPost,
    Whiel.Benchmark.Example4034.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example4034
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
