-- Generated fixed-ambient registry format: 1
import Benchmark.Example1091.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example1091

open Benchmark.Example1091

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example1091"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example1091.Input"
  namespaceName :=
    "Whiel.Benchmark.Example1091"
  sourceSha256 :=
    "f24f518fef12a4423d3218abc7bb3616" ++
      "eddd39bbaa7469b45047a51180c9a789"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example1091.inputPre,
    Whiel.Benchmark.Example1091.inputCmd,
    Whiel.Benchmark.Example1091.inputPost,
    Whiel.Benchmark.Example1091.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example1091
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
