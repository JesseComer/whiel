-- Generated fixed-ambient registry format: 1
import Benchmark.Example0133.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example0133

open Benchmark.Example0133

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example0133"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example0133.Input"
  namespaceName :=
    "Whiel.Benchmark.Example0133"
  sourceSha256 :=
    "53d86e0585a548d9b656434da5fb6fd4" ++
      "2a33d60cbaeff47f84e929c824502b6a"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example0133.inputPre,
    Whiel.Benchmark.Example0133.inputCmd,
    Whiel.Benchmark.Example0133.inputPost,
    Whiel.Benchmark.Example0133.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example0133
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
