-- Generated fixed-ambient registry format: 1
import Benchmark.Example2010.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example2010

open Benchmark.Example2010

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example2010"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example2010.Input"
  namespaceName :=
    "Whiel.Benchmark.Example2010"
  sourceSha256 :=
    "33efb8a8771b79a0f2cefd9c5909509d" ++
      "86e9996873a07bb962b9914e26b3c884"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example2010.inputPre,
    Whiel.Benchmark.Example2010.inputCmd,
    Whiel.Benchmark.Example2010.inputPost,
    Whiel.Benchmark.Example2010.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example2010
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
