-- Generated fixed-ambient registry format: 1
import Benchmark.Example5017.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example5017

open Benchmark.Example5017

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example5017"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example5017.Input"
  namespaceName :=
    "Whiel.Benchmark.Example5017"
  sourceSha256 :=
    "d39cc4451ca3d4844a58b4803ca962a5" ++
      "80733f37b75fbf5010f967bf6236044d"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example5017.inputPre,
    Whiel.Benchmark.Example5017.inputCmd,
    Whiel.Benchmark.Example5017.inputPost,
    Whiel.Benchmark.Example5017.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example5017
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
