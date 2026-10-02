-- Generated fixed-ambient registry format: 1
import Benchmark.Example0013.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example0013

open Benchmark.Example0013

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example0013"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example0013.Input"
  namespaceName :=
    "Whiel.Benchmark.Example0013"
  sourceSha256 :=
    "c5d684e37855496e60b35e668408fd54" ++
      "f713716492c70864fe41c3e1493d852d"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example0013.inputPre,
    Whiel.Benchmark.Example0013.inputCmd,
    Whiel.Benchmark.Example0013.inputPost,
    Whiel.Benchmark.Example0013.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example0013
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
