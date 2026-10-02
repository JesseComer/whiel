-- Generated fixed-ambient registry format: 1
import Benchmark.Example0109.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example0109

open Benchmark.Example0109

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example0109"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example0109.Input"
  namespaceName :=
    "Whiel.Benchmark.Example0109"
  sourceSha256 :=
    "d2116040a758cb5c45b5d159dcbfd47d" ++
      "f62a909a20f66fbd4bd87b8ca7031f5e"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example0109.inputPre,
    Whiel.Benchmark.Example0109.inputCmd,
    Whiel.Benchmark.Example0109.inputPost,
    Whiel.Benchmark.Example0109.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example0109
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
