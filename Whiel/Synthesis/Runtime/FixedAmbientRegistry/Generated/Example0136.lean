-- Generated fixed-ambient registry format: 1
import Benchmark.Example0136.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example0136

open Benchmark.Example0136

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example0136"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example0136.Input"
  namespaceName :=
    "Whiel.Benchmark.Example0136"
  sourceSha256 :=
    "98b2eab1b4584a92f9b21b4406754426" ++
      "5d98078babaf17957dee85310985d3e3"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example0136.inputPre,
    Whiel.Benchmark.Example0136.inputCmd,
    Whiel.Benchmark.Example0136.inputPost,
    Whiel.Benchmark.Example0136.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example0136
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
