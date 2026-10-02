-- Generated fixed-ambient registry format: 1
import Benchmark.Example5020.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example5020

open Benchmark.Example5020

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example5020"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example5020.Input"
  namespaceName :=
    "Whiel.Benchmark.Example5020"
  sourceSha256 :=
    "abcda887352e57117c06517d7db8d764" ++
      "e7880b00e9738f3cff52199fb28251b7"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example5020.inputPre,
    Whiel.Benchmark.Example5020.inputCmd,
    Whiel.Benchmark.Example5020.inputPost,
    Whiel.Benchmark.Example5020.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example5020
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
