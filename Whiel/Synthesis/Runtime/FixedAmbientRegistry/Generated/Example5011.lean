-- Generated fixed-ambient registry format: 1
import Benchmark.Example5011.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example5011

open Benchmark.Example5011

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example5011"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example5011.Input"
  namespaceName :=
    "Whiel.Benchmark.Example5011"
  sourceSha256 :=
    "3debeb43c314a263f4b062056ddf70ba" ++
      "0ab8424183edacd8bb1be414ac451975"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example5011.inputPre,
    Whiel.Benchmark.Example5011.inputCmd,
    Whiel.Benchmark.Example5011.inputPost,
    Whiel.Benchmark.Example5011.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example5011
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
