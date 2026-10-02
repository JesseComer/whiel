-- Generated fixed-ambient registry format: 1
import Benchmark.Example0137.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example0137

open Benchmark.Example0137

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example0137"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example0137.Input"
  namespaceName :=
    "Whiel.Benchmark.Example0137"
  sourceSha256 :=
    "06331d3a3d5ae901d3a33b571b767278" ++
      "598fbd88c67e5206f21a757912251ab3"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example0137.inputPre,
    Whiel.Benchmark.Example0137.inputCmd,
    Whiel.Benchmark.Example0137.inputPost,
    Whiel.Benchmark.Example0137.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example0137
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
