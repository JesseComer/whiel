-- Generated fixed-ambient registry format: 1
import Benchmark.Example5015.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example5015

open Benchmark.Example5015

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example5015"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example5015.Input"
  namespaceName :=
    "Whiel.Benchmark.Example5015"
  sourceSha256 :=
    "73288257a0c98cf0c6638eb2600b705a" ++
      "07a1210b97d046bedc0185c619528154"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example5015.inputPre,
    Whiel.Benchmark.Example5015.inputCmd,
    Whiel.Benchmark.Example5015.inputPost,
    Whiel.Benchmark.Example5015.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example5015
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
