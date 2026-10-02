-- Generated fixed-ambient registry format: 1
import Benchmark.Example5032.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example5032

open Benchmark.Example5032

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example5032"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example5032.Input"
  namespaceName :=
    "Whiel.Benchmark.Example5032"
  sourceSha256 :=
    "218fed79065346b00a4977b084ec7fc6" ++
      "379caf00a520400317d89140e66c563c"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example5032.inputPre,
    Whiel.Benchmark.Example5032.inputCmd,
    Whiel.Benchmark.Example5032.inputPost,
    Whiel.Benchmark.Example5032.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example5032
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
