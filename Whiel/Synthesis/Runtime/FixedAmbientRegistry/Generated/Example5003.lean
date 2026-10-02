-- Generated fixed-ambient registry format: 1
import Benchmark.Example5003.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example5003

open Benchmark.Example5003

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example5003"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example5003.Input"
  namespaceName :=
    "Whiel.Benchmark.Example5003"
  sourceSha256 :=
    "02611d79ddd6990e8ab98f505b0d475b" ++
      "548d775d393c67a66db9707a0bba8afa"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example5003.inputPre,
    Whiel.Benchmark.Example5003.inputCmd,
    Whiel.Benchmark.Example5003.inputPost,
    Whiel.Benchmark.Example5003.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example5003
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
