-- Generated fixed-ambient registry format: 1
import Benchmark.Example5007.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example5007

open Benchmark.Example5007

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example5007"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example5007.Input"
  namespaceName :=
    "Whiel.Benchmark.Example5007"
  sourceSha256 :=
    "a5220098c9470f9661a94d9c8a94b612" ++
      "dc0949e0824262148edab02e10d556ff"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example5007.inputPre,
    Whiel.Benchmark.Example5007.inputCmd,
    Whiel.Benchmark.Example5007.inputPost,
    Whiel.Benchmark.Example5007.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example5007
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
