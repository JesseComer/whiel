-- Generated fixed-ambient registry format: 1
import Benchmark.Example0106.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example0106

open Benchmark.Example0106

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example0106"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example0106.Input"
  namespaceName :=
    "Whiel.Benchmark.Example0106"
  sourceSha256 :=
    "543f302b5e0a8cabaaf4f422bc87cd5d" ++
      "7c34c527680d8e3dee14e52f5aa00a9b"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example0106.inputPre,
    Whiel.Benchmark.Example0106.inputCmd,
    Whiel.Benchmark.Example0106.inputPost,
    Whiel.Benchmark.Example0106.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example0106
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
