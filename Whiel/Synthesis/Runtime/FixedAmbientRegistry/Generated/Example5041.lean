-- Generated fixed-ambient registry format: 1
import Benchmark.Example5041.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example5041

open Benchmark.Example5041

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example5041"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example5041.Input"
  namespaceName :=
    "Whiel.Benchmark.Example5041"
  sourceSha256 :=
    "a3e774301716277b3e0fb51652bc9db3" ++
      "ba9b172f9c84f101e3da0b5d4ae2695c"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example5041.inputPre,
    Whiel.Benchmark.Example5041.inputCmd,
    Whiel.Benchmark.Example5041.inputPost,
    Whiel.Benchmark.Example5041.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example5041
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
