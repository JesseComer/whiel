-- Generated fixed-ambient registry format: 1
import Benchmark.Example4001.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example4001

open Benchmark.Example4001

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example4001"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example4001.Input"
  namespaceName :=
    "Whiel.Benchmark.Example4001"
  sourceSha256 :=
    "119411f2e73f437a564111f399452c8e" ++
      "773574f315bb7d030b39f0cfa08bda2e"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example4001.inputPre,
    Whiel.Benchmark.Example4001.inputCmd,
    Whiel.Benchmark.Example4001.inputPost,
    Whiel.Benchmark.Example4001.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example4001
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
