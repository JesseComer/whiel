-- Generated fixed-ambient registry format: 1
import Benchmark.Example4041.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example4041

open Benchmark.Example4041

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example4041"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example4041.Input"
  namespaceName :=
    "Whiel.Benchmark.Example4041"
  sourceSha256 :=
    "23bee2091d6c93a1a8a5dcf693fa2da7" ++
      "8a935864ff7463c7f663048987531885"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example4041.inputPre,
    Whiel.Benchmark.Example4041.inputCmd,
    Whiel.Benchmark.Example4041.inputPost,
    Whiel.Benchmark.Example4041.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example4041
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
