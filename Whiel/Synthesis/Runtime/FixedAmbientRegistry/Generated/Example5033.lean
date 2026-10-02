-- Generated fixed-ambient registry format: 1
import Benchmark.Example5033.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example5033

open Benchmark.Example5033

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example5033"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example5033.Input"
  namespaceName :=
    "Whiel.Benchmark.Example5033"
  sourceSha256 :=
    "7d47991ae22022fbeee39f64b491c970" ++
      "e52abb59b651b6b02c1f7b08d4f39e40"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example5033.inputPre,
    Whiel.Benchmark.Example5033.inputCmd,
    Whiel.Benchmark.Example5033.inputPost,
    Whiel.Benchmark.Example5033.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example5033
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
