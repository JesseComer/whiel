-- Generated fixed-ambient registry format: 1
import Benchmark.Example1030.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example1030

open Benchmark.Example1030

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example1030"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example1030.Input"
  namespaceName :=
    "Whiel.Benchmark.Example1030"
  sourceSha256 :=
    "4d2f56d0db210de8a0e497aba3567b7e" ++
      "287cd2138827b04305069114d7e628fc"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example1030.inputPre,
    Whiel.Benchmark.Example1030.inputCmd,
    Whiel.Benchmark.Example1030.inputPost,
    Whiel.Benchmark.Example1030.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example1030
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
