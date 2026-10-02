-- Generated fixed-ambient registry format: 1
import Benchmark.Example5016.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example5016

open Benchmark.Example5016

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example5016"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example5016.Input"
  namespaceName :=
    "Whiel.Benchmark.Example5016"
  sourceSha256 :=
    "bfd4314a0dfdfde879b0b7f635c53328" ++
      "5c4668c7721d8b92c099153b7fc9f8f7"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example5016.inputPre,
    Whiel.Benchmark.Example5016.inputCmd,
    Whiel.Benchmark.Example5016.inputPost,
    Whiel.Benchmark.Example5016.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example5016
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
