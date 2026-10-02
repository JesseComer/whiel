-- Generated fixed-ambient registry format: 1
import Benchmark.Example1093.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example1093

open Benchmark.Example1093

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example1093"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example1093.Input"
  namespaceName :=
    "Whiel.Benchmark.Example1093"
  sourceSha256 :=
    "b3f81346d67f001a8a553093fec8b2bb" ++
      "5644994a9cf7f1771cdb717e1676a25f"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example1093.inputPre,
    Whiel.Benchmark.Example1093.inputCmd,
    Whiel.Benchmark.Example1093.inputPost,
    Whiel.Benchmark.Example1093.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example1093
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
