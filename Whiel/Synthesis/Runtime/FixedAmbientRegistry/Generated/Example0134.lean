-- Generated fixed-ambient registry format: 1
import Benchmark.Example0134.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example0134

open Benchmark.Example0134

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example0134"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example0134.Input"
  namespaceName :=
    "Whiel.Benchmark.Example0134"
  sourceSha256 :=
    "c4b6478e0fcc3f46f5aae518c1448552" ++
      "d70b6457fb4bb21880eaa50781dbb3ae"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example0134.inputPre,
    Whiel.Benchmark.Example0134.inputCmd,
    Whiel.Benchmark.Example0134.inputPost,
    Whiel.Benchmark.Example0134.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example0134
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
