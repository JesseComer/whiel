-- Generated fixed-ambient registry format: 1
import Benchmark.Example0132.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example0132

open Benchmark.Example0132

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example0132"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example0132.Input"
  namespaceName :=
    "Whiel.Benchmark.Example0132"
  sourceSha256 :=
    "aea3006276ddba92ad7e6fd29b7980ed" ++
      "bc5d5a81a8be61b7cf624ae597adedec"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example0132.inputPre,
    Whiel.Benchmark.Example0132.inputCmd,
    Whiel.Benchmark.Example0132.inputPost,
    Whiel.Benchmark.Example0132.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example0132
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
