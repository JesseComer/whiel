-- Generated fixed-ambient registry format: 1
import Benchmark.Example5008.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example5008

open Benchmark.Example5008

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example5008"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example5008.Input"
  namespaceName :=
    "Whiel.Benchmark.Example5008"
  sourceSha256 :=
    "365cb5a5bdf02d1327207781afc9189a" ++
      "a75a84b1c8e4f5ec9a4e78f22a416f64"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example5008.inputPre,
    Whiel.Benchmark.Example5008.inputCmd,
    Whiel.Benchmark.Example5008.inputPost,
    Whiel.Benchmark.Example5008.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example5008
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
