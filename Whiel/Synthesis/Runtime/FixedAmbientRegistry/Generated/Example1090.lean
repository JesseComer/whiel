-- Generated fixed-ambient registry format: 1
import Benchmark.Example1090.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example1090

open Benchmark.Example1090

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example1090"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example1090.Input"
  namespaceName :=
    "Whiel.Benchmark.Example1090"
  sourceSha256 :=
    "fd58a308fda67c8eb1a86a9e354b04a0" ++
      "478c1ea3d7533aadfafbc525ad091a87"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example1090.inputPre,
    Whiel.Benchmark.Example1090.inputCmd,
    Whiel.Benchmark.Example1090.inputPost,
    Whiel.Benchmark.Example1090.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example1090
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
