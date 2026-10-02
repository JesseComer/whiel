-- Generated fixed-ambient registry format: 1
import Benchmark.Example4035.Input
import Whiel.Synthesis.Runtime.FixedAmbientRegistry.Support

/- Typed registration derived from the authoritative Input. -/

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientRegistry
namespace Example4035

open Benchmark.Example4035

/- Canonical input identity: the digest covers the five declarations. -/
def canonicalId : String :=
  "Example4035"

def identity : TaskIdentity where
  canonicalId := canonicalId
  moduleName := "Benchmark.Example4035.Input"
  namespaceName :=
    "Whiel.Benchmark.Example4035"
  sourceSha256 :=
    "31bf108face6f261a1652ec03484d857" ++
      "c1545e4358395c71e7a30786ffd915b5"
  semanticVersion := 1
  encodingVersion := 1

/- Evaluated over the computed preprocessing schema. -/
def manifest : BoundTaskManifest :=
  liftedTaskJson% identity,
    Whiel.Benchmark.Example4035.inputPre,
    Whiel.Benchmark.Example4035.inputCmd,
    Whiel.Benchmark.Example4035.inputPost,
    Whiel.Benchmark.Example4035.inputPreproc

/- Registration uses the production preprocessing path. -/
theorem inputPreproc_eq_preprocess :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

/- All typed worker operations use the shared constructor. -/
def entry : Entry :=
  Entry.ofInput identity manifest inputPreproc

end Example4035
end FixedAmbientRegistry
end Runtime
end Synthesis
end Whiel
-- End generated fixed-ambient registry format: 1
