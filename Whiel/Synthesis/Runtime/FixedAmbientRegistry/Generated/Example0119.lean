-- Generated fixed-ambient registry format: 1
import Benchmark.Example0119.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example0119

open Benchmark.Example0119

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example0119"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example0119.Input"
  namespaceName :=
    "Whiel.Benchmark.Example0119"
  sourceSha256 :=
    "28f06208df12f137f82ab2b0ec07780d" ++
      "c32c8101a958d687460f25f563ff1803"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example0119.inputPre,
    Whiel.Benchmark.Example0119.inputCmd,
    Whiel.Benchmark.Example0119.inputPost,
    Whiel.Benchmark.Example0119.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example0119
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
