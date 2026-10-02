-- Generated fixed-ambient registry format: 1
import Benchmark.Example0001.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example0001

open Benchmark.Example0001

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example0001"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example0001.Input"
  namespaceName :=
    "Whiel.Benchmark.Example0001"
  sourceSha256 :=
    "ad0bb6c66d181b376d467d611c75a12a" ++
      "9949ed73c2c463819411ccc70811f9a9"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example0001.inputPre,
    Whiel.Benchmark.Example0001.inputCmd,
    Whiel.Benchmark.Example0001.inputPost,
    Whiel.Benchmark.Example0001.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example0001
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
