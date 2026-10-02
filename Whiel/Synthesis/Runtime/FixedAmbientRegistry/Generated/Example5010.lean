-- Generated fixed-ambient registry format: 1
import Benchmark.Example5010.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example5010

open Benchmark.Example5010

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example5010"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example5010.Input"
  namespaceName :=
    "Whiel.Benchmark.Example5010"
  sourceSha256 :=
    "ab6f80a45e2ac0cf1b6ad9b470e75bf5" ++
      "9904d1bd7d8dacc80b42d7660facb455"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example5010.inputPre,
    Whiel.Benchmark.Example5010.inputCmd,
    Whiel.Benchmark.Example5010.inputPost,
    Whiel.Benchmark.Example5010.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example5010
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
