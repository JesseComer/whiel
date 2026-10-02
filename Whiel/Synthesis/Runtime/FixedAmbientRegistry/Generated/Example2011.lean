-- Generated fixed-ambient registry format: 1
import Benchmark.Example2011.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example2011

open Benchmark.Example2011

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example2011"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example2011.Input"
  namespaceName :=
    "Whiel.Benchmark.Example2011"
  sourceSha256 :=
    "837c8d1fa6c69a6ee40a27c3583e7b68" ++
      "5bb860c0214f3cbff84a12d361633a88"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example2011.inputPre,
    Whiel.Benchmark.Example2011.inputCmd,
    Whiel.Benchmark.Example2011.inputPost,
    Whiel.Benchmark.Example2011.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example2011
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
