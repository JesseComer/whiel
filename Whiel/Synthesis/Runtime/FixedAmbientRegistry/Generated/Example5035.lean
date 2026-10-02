-- Generated fixed-ambient registry format: 1
import Benchmark.Example5035.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example5035

open Benchmark.Example5035

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example5035"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example5035.Input"
  namespaceName :=
    "Whiel.Benchmark.Example5035"
  sourceSha256 :=
    "c2ae7ed48cd902c24ffb2227fa8180dc" ++
      "fa29e2dc8e289ccc159e442a9de1d6cd"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example5035.inputPre,
    Whiel.Benchmark.Example5035.inputCmd,
    Whiel.Benchmark.Example5035.inputPost,
    Whiel.Benchmark.Example5035.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example5035
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
