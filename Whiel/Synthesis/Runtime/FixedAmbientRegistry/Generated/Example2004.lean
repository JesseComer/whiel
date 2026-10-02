-- Generated fixed-ambient registry format: 1
import Benchmark.Example2004.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example2004

open Benchmark.Example2004

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example2004"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example2004.Input"
  namespaceName :=
    "Whiel.Benchmark.Example2004"
  sourceSha256 :=
    "253d18bebe266f88a599f98c4887cefe" ++
      "2c8a8c94b7ae1b3e0d8b76e31d2a2f55"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example2004.inputPre,
    Whiel.Benchmark.Example2004.inputCmd,
    Whiel.Benchmark.Example2004.inputPost,
    Whiel.Benchmark.Example2004.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example2004
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
