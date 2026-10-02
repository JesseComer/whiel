-- Generated fixed-ambient registry format: 1
import Benchmark.Example0107.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example0107

open Benchmark.Example0107

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example0107"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example0107.Input"
  namespaceName :=
    "Whiel.Benchmark.Example0107"
  sourceSha256 :=
    "1aeafc5bfcf2d3179cd8ddcdd849dd59" ++
      "7799363742b66469359c468799132404"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example0107.inputPre,
    Whiel.Benchmark.Example0107.inputCmd,
    Whiel.Benchmark.Example0107.inputPost,
    Whiel.Benchmark.Example0107.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example0107
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
