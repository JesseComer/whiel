-- Generated fixed-ambient registry format: 1
import Benchmark.Example0108.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example0108

open Benchmark.Example0108

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example0108"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example0108.Input"
  namespaceName :=
    "Whiel.Benchmark.Example0108"
  sourceSha256 :=
    "3aa5e4ebdd9a369d18831e5a1b2c9a76" ++
      "5196cc7220c4279e02d7b96d50daf3b9"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example0108.inputPre,
    Whiel.Benchmark.Example0108.inputCmd,
    Whiel.Benchmark.Example0108.inputPost,
    Whiel.Benchmark.Example0108.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example0108
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
