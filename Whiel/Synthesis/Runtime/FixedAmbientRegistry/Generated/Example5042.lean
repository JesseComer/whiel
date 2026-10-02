-- Generated fixed-ambient registry format: 1
import Benchmark.Example5042.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example5042

open Benchmark.Example5042

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example5042"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example5042.Input"
  namespaceName :=
    "Whiel.Benchmark.Example5042"
  sourceSha256 :=
    "dd06fcb31b366ab369e31e0bef8a24fa" ++
      "7c38157576cea3064bdc38abd7988548"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example5042.inputPre,
    Whiel.Benchmark.Example5042.inputCmd,
    Whiel.Benchmark.Example5042.inputPost,
    Whiel.Benchmark.Example5042.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example5042
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
