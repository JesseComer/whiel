-- Generated fixed-ambient registry format: 1
import Benchmark.Example1061.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example1061

open Benchmark.Example1061

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example1061"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example1061.Input"
  namespaceName :=
    "Whiel.Benchmark.Example1061"
  sourceSha256 :=
    "43dd498bb181955d4c5cccaa7dacd492" ++
      "89943248ea4d39e1e1eb7aa5bc415819"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example1061.inputPre,
    Whiel.Benchmark.Example1061.inputCmd,
    Whiel.Benchmark.Example1061.inputPost,
    Whiel.Benchmark.Example1061.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example1061
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
