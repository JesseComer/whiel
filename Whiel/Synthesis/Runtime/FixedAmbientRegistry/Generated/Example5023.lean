-- Generated fixed-ambient registry format: 1
import Benchmark.Example5023.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example5023

open Benchmark.Example5023

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example5023"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example5023.Input"
  namespaceName :=
    "Whiel.Benchmark.Example5023"
  sourceSha256 :=
    "89d08d68b8c4c44ee97a446106ae4272" ++
      "c5f44e28cd688f0e20e40ce17b964ef1"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example5023.inputPre,
    Whiel.Benchmark.Example5023.inputCmd,
    Whiel.Benchmark.Example5023.inputPost,
    Whiel.Benchmark.Example5023.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example5023
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
