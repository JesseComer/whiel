-- Generated fixed-ambient registry format: 1
import Benchmark.Example5014.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example5014

open Benchmark.Example5014

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example5014"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example5014.Input"
  namespaceName :=
    "Whiel.Benchmark.Example5014"
  sourceSha256 :=
    "00a3db747033d32ecbf884a0e0ceff13" ++
      "6648c85429f19d5fdafc2a3fc3983808"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example5014.inputPre,
    Whiel.Benchmark.Example5014.inputCmd,
    Whiel.Benchmark.Example5014.inputPost,
    Whiel.Benchmark.Example5014.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example5014
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
