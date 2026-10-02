-- Generated fixed-ambient registry format: 1
import Benchmark.Example5030.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example5030

open Benchmark.Example5030

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example5030"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example5030.Input"
  namespaceName :=
    "Whiel.Benchmark.Example5030"
  sourceSha256 :=
    "b06e7e624104dbbe90adec2c77151450" ++
      "8b50dddd444698dc870908c836ac9fef"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example5030.inputPre,
    Whiel.Benchmark.Example5030.inputCmd,
    Whiel.Benchmark.Example5030.inputPost,
    Whiel.Benchmark.Example5030.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example5030
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
