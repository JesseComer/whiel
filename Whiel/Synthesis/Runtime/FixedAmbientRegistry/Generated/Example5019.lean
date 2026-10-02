-- Generated fixed-ambient registry format: 1
import Benchmark.Example5019.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example5019

open Benchmark.Example5019

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example5019"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example5019.Input"
  namespaceName :=
    "Whiel.Benchmark.Example5019"
  sourceSha256 :=
    "1496d54080696007a8ba84932c28c977" ++
      "f246a8df35de6f8c8dfdea265c0314a1"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example5019.inputPre,
    Whiel.Benchmark.Example5019.inputCmd,
    Whiel.Benchmark.Example5019.inputPost,
    Whiel.Benchmark.Example5019.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example5019
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
