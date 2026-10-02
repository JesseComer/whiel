-- Generated fixed-ambient registry format: 1
import Benchmark.Example0117.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example0117

open Benchmark.Example0117

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example0117"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example0117.Input"
  namespaceName :=
    "Whiel.Benchmark.Example0117"
  sourceSha256 :=
    "ef8a48f7188fa708410afff33af6aaa1" ++
      "f02b29625c33e38265adc85663ae4189"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example0117.inputPre,
    Whiel.Benchmark.Example0117.inputCmd,
    Whiel.Benchmark.Example0117.inputPost,
    Whiel.Benchmark.Example0117.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example0117
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
