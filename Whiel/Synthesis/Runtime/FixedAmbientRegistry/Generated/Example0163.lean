-- Generated fixed-ambient registry format: 1
import Benchmark.Example0163.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example0163

open Benchmark.Example0163

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example0163"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example0163.Input"
  namespaceName :=
    "Whiel.Benchmark.Example0163"
  sourceSha256 :=
    "039b4b5bcd8e9f0ace2f8073a9224c68" ++
      "bc805092a18e1fa9b9e77e40455d9bb8"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example0163.inputPre,
    Whiel.Benchmark.Example0163.inputCmd,
    Whiel.Benchmark.Example0163.inputPost,
    Whiel.Benchmark.Example0163.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example0163
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
