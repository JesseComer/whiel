-- Generated fixed-ambient registry format: 1
import Benchmark.Example4002.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example4002

open Benchmark.Example4002

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example4002"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example4002.Input"
  namespaceName :=
    "Whiel.Benchmark.Example4002"
  sourceSha256 :=
    "2893a2e2e97c53e15d17a79cc201a7e5" ++
      "0fed531080f4b1ad96452eedb32dfa25"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example4002.inputPre,
    Whiel.Benchmark.Example4002.inputCmd,
    Whiel.Benchmark.Example4002.inputPost,
    Whiel.Benchmark.Example4002.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example4002
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
