-- Generated fixed-ambient registry format: 1
import Benchmark.Example0125.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example0125

open Benchmark.Example0125

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example0125"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example0125.Input"
  namespaceName :=
    "Whiel.Benchmark.Example0125"
  sourceSha256 :=
    "7c1c3e431ad05791560f18b8a1451081" ++
      "609ef78d0c0a225b7a6a5aa8009b407f"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example0125.inputPre,
    Whiel.Benchmark.Example0125.inputCmd,
    Whiel.Benchmark.Example0125.inputPost,
    Whiel.Benchmark.Example0125.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example0125
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
