-- Generated fixed-ambient registry format: 1
import Benchmark.Example0130.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example0130

open Benchmark.Example0130

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example0130"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example0130.Input"
  namespaceName :=
    "Whiel.Benchmark.Example0130"
  sourceSha256 :=
    "4a1b8264869a13d4afb7dc343265aa13" ++
      "642ae64a21fef68c460048bb0b4a6187"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example0130.inputPre,
    Whiel.Benchmark.Example0130.inputCmd,
    Whiel.Benchmark.Example0130.inputPost,
    Whiel.Benchmark.Example0130.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example0130
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
