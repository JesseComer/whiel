-- Generated fixed-ambient registry format: 1
import Benchmark.Example5040.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example5040

open Benchmark.Example5040

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example5040"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example5040.Input"
  namespaceName :=
    "Whiel.Benchmark.Example5040"
  sourceSha256 :=
    "4e2c87f7897ae667457c68ac0c20954d" ++
      "17732cb14c5aa4a6d7ea1c2471e2cf2a"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example5040.inputPre,
    Whiel.Benchmark.Example5040.inputCmd,
    Whiel.Benchmark.Example5040.inputPost,
    Whiel.Benchmark.Example5040.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example5040
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
