-- Author: Jesse Comer
import Benchmark2.Example0012.Certificate.Proposal
import Whiel.Synthesis.Runtime.EncodingWorker
import Whiel.Synthesis.WLayer.Spec
import Whiel.Vampire.CandidateVerification
import Whiel.Vampire.SolverName.Concrete

/-
  Concrete synthesis-runtime launcher for Example0012.

  This executable imports the task once and serves its exact
  preprocessed pre/post declarations through the common
  persistent worker. Future task launchers supply the same
  registry boundary.
-/

------------------------------------------------------------
-- Task-Specific Key Resolution
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Runtime
namespace Example0012EncodingWorker

open Concrete
open Benchmark.Example0012

private def resolveRelation
    (key : String) : Option IndexAlphaName :=
  programSchema.syms.sort.find?
    (fun relation => SolverKey.key relation == key)

private def resolveConstant
    (key : String) : Option Data :=
  SolverKey.dataOfKey? key

/- Exact task alphabet used by the reference enumerator. -/
def referenceAlphabet :
    DisjunctiveClause.Alphabet Data programSchema where
  relations := programSchema.syms.attach
  constants :=
    inputPre.constants ∪ inputCmd.constants ∪
      inputPost.constants

/- Ordered typed incremental reference wave at one stage. -/
def referenceProposal
    (stage : Nat) :
    List (QFAssertExpr Data programSchema) :=
  ReferenceProposal.wave referenceAlphabet stage

/- Exact QF source used to exercise the shared QF boundary. -/
def qfFixture : QFAssertExpr Data programSchema :=
  QFAssertExpr.true

/- QF fixture whose Data order differs from key-string order. -/
def qfMixedConstantsFixture :
    QFAssertExpr Data programSchema :=
  QFAssertExpr.and
    (QFAssertExpr.eq
      (RAExpr.single (Data.num 2))
      (RAExpr.single (Data.num 10)))
    (QFAssertExpr.and
      (QFAssertExpr.eq
        (RAExpr.single (Data.bool Bool.false))
        (RAExpr.single (Data.str "mixed")))
      QFAssertExpr.true)

/- QF fixture with colliding sanitized constant keys. -/
def qfCollidingConstantsFixture :
    QFAssertExpr Data programSchema :=
  QFAssertExpr.eq
    (RAExpr.single (Data.str "a-b"))
    (RAExpr.single (Data.str "a_b"))

/- Representative Catalog clause. -/
def catalogClause : QFAssertExpr Data programSchema :=
  Certificate.candidateClause0

/- Remaining clauses of the known-valid fixed Phase 3E proposal. -/
def catalogClause1 : QFAssertExpr Data programSchema :=
  Certificate.candidateClause1

def catalogClause2 : QFAssertExpr Data programSchema :=
  Certificate.candidateClause2

/- Conjoined candidate, as the retired monolithic shape had. -/
def candidateQF : QFAssertExpr Data programSchema :=
  QFAssertExpr.andList Certificate.candidateClauses

/- Representative cached maintenance WP. -/
def catalogMaintenanceWP :
    QFAssertExpr Data programSchema :=
  (Vampire.CandidateVerification.ofPreproc
    inputPreproc candidateQF).maintQF.conjecture

/- First exact symbolic W layer. -/
def symbolicWZero : QFAssertExpr Data programSchema :=
  Synthesis.WLayer.formula inputPreproc 0

/- Next exact symbolic W layer, used as a prepared WP bundle. -/
def symbolicWOne : QFAssertExpr Data programSchema :=
  Synthesis.WLayer.formula inputPreproc 1

/- Static regression oracles for the dynamic W recurrence. -/
def symbolicWZeroWP : QFAssertExpr Data programSchema :=
  QFAssertExpr.wpLoopFree inputPreproc.loopBody
    inputPreproc.loopBody_loopFree symbolicWZero

def symbolicWOneWP : QFAssertExpr Data programSchema :=
  QFAssertExpr.wpLoopFree inputPreproc.loopBody
    inputPreproc.loopBody_loopFree symbolicWOne

/- Representative one-off AgentNaive proposal. -/
def agentNaiveOneOff : QFAssertExpr Data programSchema :=
  Certificate.candidateClause1

/- Formula with an empty-active-domain counterexample. -/
def falseFixture : QFAssertExpr Data programSchema :=
  QFAssertExpr.false

/- Exact source axiom of the tracked initialization VC. -/
def legacyInitAxiom : QFAssertExpr Data programSchema :=
  inputPreproc.loopPre.toQFOfNoBound
    inputPreproc.loopPre_noBound

/- Exact source goal of the tracked initialization VC. -/
def legacyInitGoal : QFAssertExpr Data programSchema :=
  candidateQF

private def resolveSource
    (sourceId : String) :
    Option (SolverBodySource Data programSchema) :=
  match sourceId with
  | "task.preprocessed_pre" =>
      some (.assert sourceId inputPreproc.loopPre
        inputPreproc.loopPre_noBound)
  | "task.preprocessed_post" =>
      some (.assert sourceId inputPreproc.loopPost
        inputPreproc.loopPost_noBound)
  | "task.preprocessed_pre_qf" =>
      some (.qf sourceId
        (inputPreproc.loopPre.toQFOfNoBound
          inputPreproc.loopPre_noBound))
  | "task.phase2c_qf_fixture" =>
      some (.qf sourceId qfFixture)
  | "task.phase2c_qf_mixed_constants" =>
      some (.qf sourceId qfMixedConstantsFixture)
  | "task.phase2d_qf_colliding_constants" =>
      some (.qf sourceId qfCollidingConstantsFixture)
  | "catalog.clause.0" =>
      some (.qf sourceId catalogClause)
  | "catalog.clause.0.alias" =>
      some (.qf sourceId catalogClause)
  | "catalog.clause.1" =>
      some (.qf sourceId catalogClause1)
  | "catalog.clause.2" =>
      some (.qf sourceId catalogClause2)
  | "catalog.wp.0" =>
      some (.qf sourceId catalogMaintenanceWP)
  | "symbolic.w.0" =>
      some (.qf sourceId symbolicWZero)
  | "symbolic.w.1" =>
      some (.qf sourceId symbolicWOne)
  | "symbolic.w.0.wp" =>
      some (.qf sourceId symbolicWZeroWP)
  | "symbolic.w.1.wp" =>
      some (.qf sourceId symbolicWOneWP)
  | "agent_naive.one_off" =>
      some (.qf sourceId agentNaiveOneOff)
  | "phase2d.false" =>
      some (.qf sourceId falseFixture)
  | "legacy.init.axiom.0" =>
      some (.qf sourceId legacyInitAxiom)
  | "legacy.init.goal" =>
      some (.qf sourceId legacyInitGoal)
  | _ => none

/- Registry imported and fixed by the executable. -/
def registry
    (contextId : String) :
    EncodingTaskRegistry IndexAlphaName Data where
  identity :=
    { contextId
      semanticVersion := 1
      encodingVersion := 1
      taskCanonicalId := "Example0012"
      taskModule := "Benchmark.Example0012.Input"
      taskNamespace := "Whiel.Benchmark.Example0012"
      taskSourceSha256 :=
        "6fe56e9493eefa68d69085d1602adda3" ++
          "a0d522d964f1a8bf6ef3996f08cd3195" }
  schema := programSchema
  loopGuard := inputPreproc.loopGuard
  loopBody := inputPreproc.loopBody
  loopBodyLoopFree := inputPreproc.loopBody_loopFree
  resolveRelation := resolveRelation
  resolveConstant := resolveConstant
  resolveSource := resolveSource
  referenceAlphabet := referenceAlphabet

end Example0012EncodingWorker
end Runtime
end Synthesis
end Whiel

/- Run the concrete worker for one run-unique context id. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [contextId] =>
      Whiel.Synthesis.Runtime.runEncodingWorker
        (Whiel.Synthesis.Runtime.Example0012EncodingWorker.registry
          contextId)
  | _ =>
      let stderr ← IO.getStderr
      stderr.putStrLn
        "usage: example0012_encoding_worker <context-id>"
      return 2
