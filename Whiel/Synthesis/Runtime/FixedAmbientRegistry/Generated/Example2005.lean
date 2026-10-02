-- Generated fixed-ambient registry format: 1
import Benchmark.Example2005.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example2005

open Benchmark.Example2005

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example2005"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example2005.Input"
  namespaceName :=
    "Whiel.Benchmark.Example2005"
  sourceSha256 :=
    "bc24f3807b0beb6c0cbdda81163b059d" ++
      "0b168ef2112d36e8bee842ee92ec0403"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example2005.inputPre,
    Whiel.Benchmark.Example2005.inputCmd,
    Whiel.Benchmark.Example2005.inputPost,
    Whiel.Benchmark.Example2005.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example2005
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
