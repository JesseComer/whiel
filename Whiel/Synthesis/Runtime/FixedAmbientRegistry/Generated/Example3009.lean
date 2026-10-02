-- Generated fixed-ambient registry format: 1
import Benchmark.Example3009.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example3009

open Benchmark.Example3009

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example3009"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example3009.Input"
  namespaceName :=
    "Whiel.Benchmark.Example3009"
  sourceSha256 :=
    "00f2c8a21d18603e3ace39754fdd0a2e" ++
      "ba9a273b92fdc5d431db9f35396cb1d2"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example3009.inputPre,
    Whiel.Benchmark.Example3009.inputCmd,
    Whiel.Benchmark.Example3009.inputPost,
    Whiel.Benchmark.Example3009.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example3009
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
