-- Generated fixed-ambient registry format: 1
import Benchmark.Example4004.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example4004

open Benchmark.Example4004

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example4004"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example4004.Input"
  namespaceName :=
    "Whiel.Benchmark.Example4004"
  sourceSha256 :=
    "2cc4f6aca5bdbcadd2ed414a9bf9cf67" ++
      "9375bce2358f1c8ec8098ea8c874a492"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example4004.inputPre,
    Whiel.Benchmark.Example4004.inputCmd,
    Whiel.Benchmark.Example4004.inputPost,
    Whiel.Benchmark.Example4004.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example4004
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
