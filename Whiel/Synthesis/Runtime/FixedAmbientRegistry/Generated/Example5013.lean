-- Generated fixed-ambient registry format: 1
import Benchmark.Example5013.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example5013

open Benchmark.Example5013

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example5013"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example5013.Input"
  namespaceName :=
    "Whiel.Benchmark.Example5013"
  sourceSha256 :=
    "3e9346848048d8d8b7bde6477cbba791" ++
      "1c60269014b4e17e70e053381f6a0380"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example5013.inputPre,
    Whiel.Benchmark.Example5013.inputCmd,
    Whiel.Benchmark.Example5013.inputPost,
    Whiel.Benchmark.Example5013.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example5013
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
