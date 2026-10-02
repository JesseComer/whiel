-- Generated fixed-ambient registry format: 1
import Benchmark.Example5031.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example5031

open Benchmark.Example5031

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example5031"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example5031.Input"
  namespaceName :=
    "Whiel.Benchmark.Example5031"
  sourceSha256 :=
    "6bd393f495cdc99cb0db24e66b3ceaba" ++
      "c09f235564abae1b00c4c5aefd33e871"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example5031.inputPre,
    Whiel.Benchmark.Example5031.inputCmd,
    Whiel.Benchmark.Example5031.inputPost,
    Whiel.Benchmark.Example5031.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example5031
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
