-- Generated fixed-ambient registry format: 1
import Benchmark.Example4040.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example4040

open Benchmark.Example4040

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example4040"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example4040.Input"
  namespaceName :=
    "Whiel.Benchmark.Example4040"
  sourceSha256 :=
    "52dd46ecd8d6411e17f11e4caf2d116f" ++
      "ac3e7eed43f0560412b0c79794b8aa95"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example4040.inputPre,
    Whiel.Benchmark.Example4040.inputCmd,
    Whiel.Benchmark.Example4040.inputPost,
    Whiel.Benchmark.Example4040.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example4040
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
