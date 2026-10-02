-- Generated fixed-ambient registry format: 1
import Benchmark.Example5001.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example5001

open Benchmark.Example5001

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example5001"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example5001.Input"
  namespaceName :=
    "Whiel.Benchmark.Example5001"
  sourceSha256 :=
    "79416197d874dbcd226af1cd326cdbf1" ++
      "973d00c6f91dd2d47edee7e74cc1f4af"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example5001.inputPre,
    Whiel.Benchmark.Example5001.inputCmd,
    Whiel.Benchmark.Example5001.inputPost,
    Whiel.Benchmark.Example5001.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example5001
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
