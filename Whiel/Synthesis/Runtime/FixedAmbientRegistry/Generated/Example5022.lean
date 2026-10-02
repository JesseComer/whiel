-- Generated fixed-ambient registry format: 1
import Benchmark.Example5022.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example5022

open Benchmark.Example5022

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example5022"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example5022.Input"
  namespaceName :=
    "Whiel.Benchmark.Example5022"
  sourceSha256 :=
    "3671018190f24a0b7ffe47e44d570701" ++
      "0128d207bac9e0b2cf3f301380277ca9"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example5022.inputPre,
    Whiel.Benchmark.Example5022.inputCmd,
    Whiel.Benchmark.Example5022.inputPost,
    Whiel.Benchmark.Example5022.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example5022
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
