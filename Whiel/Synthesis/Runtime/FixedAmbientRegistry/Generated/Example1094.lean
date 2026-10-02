-- Generated fixed-ambient registry format: 1
import Benchmark.Example1094.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example1094

open Benchmark.Example1094

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example1094"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example1094.Input"
  namespaceName :=
    "Whiel.Benchmark.Example1094"
  sourceSha256 :=
    "4e7be289c29631d052bc848c2cd7edae" ++
      "0e4754d6fd77b292453b4ae641d19b54"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example1094.inputPre,
    Whiel.Benchmark.Example1094.inputCmd,
    Whiel.Benchmark.Example1094.inputPost,
    Whiel.Benchmark.Example1094.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example1094
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
