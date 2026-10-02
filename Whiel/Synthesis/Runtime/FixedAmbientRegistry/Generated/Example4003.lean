-- Generated fixed-ambient registry format: 1
import Benchmark.Example4003.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example4003

open Benchmark.Example4003

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example4003"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example4003.Input"
  namespaceName :=
    "Whiel.Benchmark.Example4003"
  sourceSha256 :=
    "ad74b3c06b92a5ed101b578b177c3d78" ++
      "866f5b9bdc0adf3166e8666fc735113f"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example4003.inputPre,
    Whiel.Benchmark.Example4003.inputCmd,
    Whiel.Benchmark.Example4003.inputPost,
    Whiel.Benchmark.Example4003.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example4003
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
