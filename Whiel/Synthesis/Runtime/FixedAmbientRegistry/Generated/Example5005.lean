-- Generated fixed-ambient registry format: 1
import Benchmark.Example5005.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example5005

open Benchmark.Example5005

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example5005"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example5005.Input"
  namespaceName :=
    "Whiel.Benchmark.Example5005"
  sourceSha256 :=
    "1b2a0af26c806c5a576da429fe40c4d3" ++
      "6da6ead8b2cb707ab6d1e7d9441dadc3"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example5005.inputPre,
    Whiel.Benchmark.Example5005.inputCmd,
    Whiel.Benchmark.Example5005.inputPost,
    Whiel.Benchmark.Example5005.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example5005
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
