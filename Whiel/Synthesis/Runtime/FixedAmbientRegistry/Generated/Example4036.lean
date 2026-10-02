-- Generated fixed-ambient registry format: 1
import Benchmark.Example4036.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example4036

open Benchmark.Example4036

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example4036"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example4036.Input"
  namespaceName :=
    "Whiel.Benchmark.Example4036"
  sourceSha256 :=
    "b8c0ca6835879d141930cd5dd149329e" ++
      "3b8f295079c3658f7b2bd3690f577d4a"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example4036.inputPre,
    Whiel.Benchmark.Example4036.inputCmd,
    Whiel.Benchmark.Example4036.inputPost,
    Whiel.Benchmark.Example4036.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example4036
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
