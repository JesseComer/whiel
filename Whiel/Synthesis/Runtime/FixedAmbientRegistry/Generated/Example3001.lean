-- Generated fixed-ambient registry format: 1
import Benchmark.Example3001.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example3001

open Benchmark.Example3001

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example3001"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example3001.Input"
  namespaceName :=
    "Whiel.Benchmark.Example3001"
  sourceSha256 :=
    "a7d6270b19f17b05b447fb8ee79eb7dc" ++
      "39690f60f9d6cfa5fbaa5fa80ce03b30"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example3001.inputPre,
    Whiel.Benchmark.Example3001.inputCmd,
    Whiel.Benchmark.Example3001.inputPost,
    Whiel.Benchmark.Example3001.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example3001
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
