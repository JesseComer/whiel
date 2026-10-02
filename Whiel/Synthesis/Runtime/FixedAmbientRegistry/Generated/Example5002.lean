-- Generated fixed-ambient registry format: 1
import Benchmark.Example5002.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example5002

open Benchmark.Example5002

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example5002"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example5002.Input"
  namespaceName :=
    "Whiel.Benchmark.Example5002"
  sourceSha256 :=
    "e1e44b7c5243ce6286aa8b7af44c0d4b" ++
      "d7931a53e140e8d7ae7a9c0fb34ca57a"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example5002.inputPre,
    Whiel.Benchmark.Example5002.inputCmd,
    Whiel.Benchmark.Example5002.inputPost,
    Whiel.Benchmark.Example5002.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example5002
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
