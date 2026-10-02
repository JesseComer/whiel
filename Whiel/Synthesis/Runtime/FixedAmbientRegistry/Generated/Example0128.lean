-- Generated fixed-ambient registry format: 1
import Benchmark.Example0128.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example0128

open Benchmark.Example0128

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example0128"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example0128.Input"
  namespaceName :=
    "Whiel.Benchmark.Example0128"
  sourceSha256 :=
    "72e961a45a9e82508e37e62dc8827f74" ++
      "6912548d866bf30810041663e36f4904"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example0128.inputPre,
    Whiel.Benchmark.Example0128.inputCmd,
    Whiel.Benchmark.Example0128.inputPost,
    Whiel.Benchmark.Example0128.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example0128
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
