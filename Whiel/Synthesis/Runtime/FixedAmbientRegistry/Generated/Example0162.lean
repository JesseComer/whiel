-- Generated fixed-ambient registry format: 1
import Benchmark.Example0162.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example0162

open Benchmark.Example0162

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example0162"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example0162.Input"
  namespaceName :=
    "Whiel.Benchmark.Example0162"
  sourceSha256 :=
    "2dee08773615da204a53250256338380" ++
      "20a88916044292823c1ca18109df7a55"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example0162.inputPre,
    Whiel.Benchmark.Example0162.inputCmd,
    Whiel.Benchmark.Example0162.inputPost,
    Whiel.Benchmark.Example0162.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example0162
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
