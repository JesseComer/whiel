-- Generated fixed-ambient registry format: 1
import Benchmark.Example5037.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example5037

open Benchmark.Example5037

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example5037"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example5037.Input"
  namespaceName :=
    "Whiel.Benchmark.Example5037"
  sourceSha256 :=
    "27e9e255f639a0630a2b78b92370f5f0" ++
      "3dcc89830595ec114b2066ee16cdabdb"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example5037.inputPre,
    Whiel.Benchmark.Example5037.inputCmd,
    Whiel.Benchmark.Example5037.inputPost,
    Whiel.Benchmark.Example5037.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example5037
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
