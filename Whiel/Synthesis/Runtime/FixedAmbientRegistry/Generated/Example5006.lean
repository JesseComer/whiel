-- Generated fixed-ambient registry format: 1
import Benchmark.Example5006.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example5006

open Benchmark.Example5006

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example5006"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example5006.Input"
  namespaceName :=
    "Whiel.Benchmark.Example5006"
  sourceSha256 :=
    "985d5da37171116353ff5c5cbc60a2ad" ++
      "eb870c9cc0b26b4fc1644344796f7cb9"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example5006.inputPre,
    Whiel.Benchmark.Example5006.inputCmd,
    Whiel.Benchmark.Example5006.inputPost,
    Whiel.Benchmark.Example5006.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example5006
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
