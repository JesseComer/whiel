-- Generated fixed-ambient registry format: 1
import Benchmark.Example5004.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example5004

open Benchmark.Example5004

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example5004"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example5004.Input"
  namespaceName :=
    "Whiel.Benchmark.Example5004"
  sourceSha256 :=
    "e729177e1fa1da3f93a8a67d33247221" ++
      "f81821e13715451c25aba0b9fa829ef2"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example5004.inputPre,
    Whiel.Benchmark.Example5004.inputCmd,
    Whiel.Benchmark.Example5004.inputPost,
    Whiel.Benchmark.Example5004.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example5004
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
