-- Generated fixed-ambient registry format: 1
import Benchmark.Example5012.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example5012

open Benchmark.Example5012

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example5012"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example5012.Input"
  namespaceName :=
    "Whiel.Benchmark.Example5012"
  sourceSha256 :=
    "16ddfc37740dde1b4d8a79705ebf1499" ++
      "3d6b122e4b4976a2415d6ef7d696bafd"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example5012.inputPre,
    Whiel.Benchmark.Example5012.inputCmd,
    Whiel.Benchmark.Example5012.inputPost,
    Whiel.Benchmark.Example5012.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example5012
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
