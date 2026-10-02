-- Generated fixed-ambient registry format: 1
import Benchmark.Example2006.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example2006

open Benchmark.Example2006

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example2006"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example2006.Input"
  namespaceName :=
    "Whiel.Benchmark.Example2006"
  sourceSha256 :=
    "d325674aba7acd1d994b873667400f81" ++
      "2e49c724ed18f39163b2aec2c465bfae"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example2006.inputPre,
    Whiel.Benchmark.Example2006.inputCmd,
    Whiel.Benchmark.Example2006.inputPost,
    Whiel.Benchmark.Example2006.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example2006
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
