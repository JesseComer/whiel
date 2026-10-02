-- Generated fixed-ambient registry format: 1
import Benchmark.Example0123.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example0123

open Benchmark.Example0123

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example0123"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example0123.Input"
  namespaceName :=
    "Whiel.Benchmark.Example0123"
  sourceSha256 :=
    "4fd9e312bfe9a310de69774dd93a6422" ++
      "b2beec0bd732df71733a945f15524f60"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example0123.inputPre,
    Whiel.Benchmark.Example0123.inputCmd,
    Whiel.Benchmark.Example0123.inputPost,
    Whiel.Benchmark.Example0123.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example0123
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
