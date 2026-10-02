-- Generated fixed-ambient registry format: 1
import Benchmark.Example2012.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example2012

open Benchmark.Example2012

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example2012"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example2012.Input"
  namespaceName :=
    "Whiel.Benchmark.Example2012"
  sourceSha256 :=
    "22600fa7fe4fffe397f1d3cc2ef42401" ++
      "e2c612251accd9ca1c211db6262cf562"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example2012.inputPre,
    Whiel.Benchmark.Example2012.inputCmd,
    Whiel.Benchmark.Example2012.inputPost,
    Whiel.Benchmark.Example2012.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example2012
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
