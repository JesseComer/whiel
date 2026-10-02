-- Generated fixed-ambient registry format: 1
import Benchmark.Example4037.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example4037

open Benchmark.Example4037

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example4037"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example4037.Input"
  namespaceName :=
    "Whiel.Benchmark.Example4037"
  sourceSha256 :=
    "c691342416c50568869a8e5ff74100ca" ++
      "6417b79fe4e21bc1e131824439f16094"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example4037.inputPre,
    Whiel.Benchmark.Example4037.inputCmd,
    Whiel.Benchmark.Example4037.inputPost,
    Whiel.Benchmark.Example4037.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example4037
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
