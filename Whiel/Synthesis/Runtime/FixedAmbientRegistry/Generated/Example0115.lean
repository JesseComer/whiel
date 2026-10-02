-- Generated fixed-ambient registry format: 1
import Benchmark.Example0115.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example0115

open Benchmark.Example0115

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example0115"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example0115.Input"
  namespaceName :=
    "Whiel.Benchmark.Example0115"
  sourceSha256 :=
    "058b5a2ed312ad8760e1d8eb7f8b7467" ++
      "d0fbafcd4a66489c7ea09affd8ebf26d"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example0115.inputPre,
    Whiel.Benchmark.Example0115.inputCmd,
    Whiel.Benchmark.Example0115.inputPost,
    Whiel.Benchmark.Example0115.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example0115
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
