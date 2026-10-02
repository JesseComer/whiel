-- Author: Jesse Comer
import Whiel.Synthesis.Runtime.EncodingWorker
import Whiel.Synthesis.Runtime.Task

/-
  Common trusted boundary for compiled benchmark tasks.

  A generated dispatcher supplies exact declarations from
  one imported module. Rust selects a canonical ID;
  it does not parse or elaborate Lean source text.
-/

------------------------------------------------------------
-- Benchmark Task Identities
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Runtime

open Concrete

/- Exact identity shared by a manifest and worker. -/
def benchmarkTaskIdentity
    (canonicalId moduleName namespaceName : String)
    (sourceSha256 : String) : TaskIdentity where
  canonicalId := canonicalId
  moduleName := moduleName
  namespaceName := namespaceName
  sourceSha256 := sourceSha256

end Runtime
end Synthesis
end Whiel

------------------------------------------------------------
-- Benchmark Encoding Registry
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Runtime

open Concrete

private def resolveBenchmarkRelation
    (Gamma : UnnamedSchema IndexAlphaName)
    (key : String) : Option IndexAlphaName :=
  Gamma.syms.sort.find?
    (fun relation => SolverKey.key relation == key)

private def resolveBenchmarkSource
    {Gamma : UnnamedSchema IndexAlphaName}
    {inputPre : AssertExpr Data Gamma}
    {inputCmd : Cmd Data Gamma}
    {inputPost : AssertExpr Data Gamma}
    (preproc : Hoare.Preproc inputPre inputCmd inputPost)
    (sourceId : String) :
    Option (SolverBodySource Data preproc.outSchema) :=
  match sourceId with
  | "task.preprocessed_pre" =>
      some (.assert sourceId preproc.loopPre
        preproc.loopPre_noBound)
  | "task.preprocessed_post" =>
      some (.assert sourceId preproc.loopPost
        preproc.loopPost_noBound)
  | "task.preprocessed_pre_qf" =>
      some (.qf sourceId
        (preproc.loopPre.toQFOfNoBound
          preproc.loopPre_noBound))
  | _ => none

private def benchmarkReferenceAlphabet
    {Gamma : UnnamedSchema IndexAlphaName}
    (inputPre : AssertExpr Data Gamma)
    (inputCmd : Cmd Data Gamma)
    (inputPost : AssertExpr Data Gamma)
    (preproc : Hoare.Preproc inputPre inputCmd inputPost) :
    DisjunctiveClause.Alphabet Data preproc.outSchema where
  relations := preproc.outSchema.syms.attach
  constants :=
    inputPre.constants ∪ inputCmd.constants ∪
      inputPost.constants ∪ preproc.loopPre.constants ∪
      preproc.loopGuard.constants ∪
      preproc.loopCmd.constants ∪
      preproc.loopPost.constants

/-
  Construct the registry from exact compiled benchmark
  declarations.
-/
def benchmarkEncodingRegistry
    {Gamma : UnnamedSchema IndexAlphaName}
    (identity : TaskIdentity)
    (inputPre : AssertExpr Data Gamma)
    (inputCmd : Cmd Data Gamma)
    (inputPost : AssertExpr Data Gamma)
    (preproc : Hoare.Preproc inputPre inputCmd inputPost)
    (contextId : String) :
    EncodingTaskRegistry IndexAlphaName Data :=
  {
  identity :=
    { contextId := contextId
      semanticVersion := identity.semanticVersion
      encodingVersion := identity.encodingVersion
      taskCanonicalId := identity.canonicalId
      taskModule := identity.moduleName
      taskNamespace := identity.namespaceName
      taskSourceSha256 := identity.sourceSha256 }
  schema := preproc.outSchema
  loopGuard := preproc.loopGuard
  loopBody := preproc.loopBody
  loopBodyLoopFree := preproc.loopBody_loopFree
  resolveRelation :=
    resolveBenchmarkRelation preproc.outSchema
  resolveConstant := SolverKey.dataOfKey?
  resolveSource := resolveBenchmarkSource preproc
  referenceAlphabet :=
    benchmarkReferenceAlphabet
      inputPre inputCmd inputPost preproc
  seedLiterals :=
    Enumerators.Seeded.seedLiterals preproc
  }

end Runtime
end Synthesis
end Whiel
