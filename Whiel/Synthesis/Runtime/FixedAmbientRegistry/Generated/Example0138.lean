-- Generated fixed-ambient registry format: 1
import Benchmark.Example0138.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example0138

open Benchmark.Example0138

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example0138"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example0138.Input"
  namespaceName :=
    "Whiel.Benchmark.Example0138"
  sourceSha256 :=
    "5940e2217558d4e7d403bb65cb6e88d8" ++
      "9382b8ba4900641dc611e2032e2be5a3"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example0138.inputPre,
    Whiel.Benchmark.Example0138.inputCmd,
    Whiel.Benchmark.Example0138.inputPost,
    Whiel.Benchmark.Example0138.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example0138
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
