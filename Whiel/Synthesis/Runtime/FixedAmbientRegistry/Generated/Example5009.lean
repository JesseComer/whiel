-- Generated fixed-ambient registry format: 1
import Benchmark.Example5009.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example5009

open Benchmark.Example5009

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example5009"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example5009.Input"
  namespaceName :=
    "Whiel.Benchmark.Example5009"
  sourceSha256 :=
    "6a8b1ac0727a0c4772109ed335d388ea" ++
      "9f8ccefb330104850d1df8c72a503e61"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example5009.inputPre,
    Whiel.Benchmark.Example5009.inputCmd,
    Whiel.Benchmark.Example5009.inputPost,
    Whiel.Benchmark.Example5009.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example5009
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
