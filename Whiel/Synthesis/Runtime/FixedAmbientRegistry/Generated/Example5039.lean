-- Generated fixed-ambient registry format: 1
import Benchmark.Example5039.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example5039

open Benchmark.Example5039

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example5039"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example5039.Input"
  namespaceName :=
    "Whiel.Benchmark.Example5039"
  sourceSha256 :=
    "4726397c2c326f6070b6d1f85f8f44ba" ++
      "83d42cf5055d9f76ab12042160a55ba7"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example5039.inputPre,
    Whiel.Benchmark.Example5039.inputCmd,
    Whiel.Benchmark.Example5039.inputPost,
    Whiel.Benchmark.Example5039.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example5039
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
