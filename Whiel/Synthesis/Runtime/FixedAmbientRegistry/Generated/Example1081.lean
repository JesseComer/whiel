-- Generated fixed-ambient registry format: 1
import Benchmark.Example1081.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example1081

open Benchmark.Example1081

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example1081"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example1081.Input"
  namespaceName :=
    "Whiel.Benchmark.Example1081"
  sourceSha256 :=
    "5917639083b4f1f91a39c08a24528e35" ++
      "668e55bf0b761122a52d83427a68c408"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example1081.inputPre,
    Whiel.Benchmark.Example1081.inputCmd,
    Whiel.Benchmark.Example1081.inputPost,
    Whiel.Benchmark.Example1081.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example1081
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
