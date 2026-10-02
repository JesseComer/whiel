-- Generated fixed-ambient registry format: 1
import Benchmark.Example5038.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example5038

open Benchmark.Example5038

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example5038"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example5038.Input"
  namespaceName :=
    "Whiel.Benchmark.Example5038"
  sourceSha256 :=
    "bdb4f946d2989a1ce6c8940dc38faca5" ++
      "42f9492f70e9c260366aa8430c369379"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example5038.inputPre,
    Whiel.Benchmark.Example5038.inputCmd,
    Whiel.Benchmark.Example5038.inputPost,
    Whiel.Benchmark.Example5038.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example5038
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
