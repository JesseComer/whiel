-- Generated fixed-ambient registry format: 1
import Benchmark.Example3014.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example3014

open Benchmark.Example3014

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example3014"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example3014.Input"
  namespaceName :=
    "Whiel.Benchmark.Example3014"
  sourceSha256 :=
    "1b7d03fe13f1d2fd9006fc487aae09b2" ++
      "7d3e2668e17f7de5bc2ed9b6403d8134"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example3014.inputPre,
    Whiel.Benchmark.Example3014.inputCmd,
    Whiel.Benchmark.Example3014.inputPost,
    Whiel.Benchmark.Example3014.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example3014
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
