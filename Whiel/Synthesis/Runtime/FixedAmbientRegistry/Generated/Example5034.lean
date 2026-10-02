-- Generated fixed-ambient registry format: 1
import Benchmark.Example5034.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example5034

open Benchmark.Example5034

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example5034"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example5034.Input"
  namespaceName :=
    "Whiel.Benchmark.Example5034"
  sourceSha256 :=
    "a282f0516e85ef137f40ba99e6371e8e" ++
      "dfed66f08eccd80cd891bc763518c971"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example5034.inputPre,
    Whiel.Benchmark.Example5034.inputCmd,
    Whiel.Benchmark.Example5034.inputPost,
    Whiel.Benchmark.Example5034.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example5034
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
