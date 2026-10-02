-- Author: Jesse Comer
import Lean.Elab.Command
import Whiel.Concrete.Notation
import Whiel.Vampire.InvariantObligations
import Whiel.Vampire.SolverName.Concrete

open Whiel.Concrete

/-
  Build-only checks for the Vampire manifest path.

  These checks make sure Lean emits the expected job list,
  manifest fields, scheduling conditions, and support-axiom
  names.
-/

------------------------------------------------------------
-- Smoke Inputs
------------------------------------------------------------

namespace Whiel

namespace Vampire

namespace Smoke

def smokeSchema : UnnamedSchema IndexAlphaName :=
  whielSch![
    {E, T, TBound} (arity: 2),
    _ (arity: 0)
  ]

def smokePre : AssertExpr Data smokeSchema :=
  assert![E ⊆ TBound]

def smokePost : AssertExpr Data smokeSchema :=
  assert![T ⊆ TBound]

def smokeInv : QFAssertExpr Data smokeSchema :=
  guard![T ⊆ TBound]

end Smoke
end Vampire
end Whiel

------------------------------------------------------------
-- Job Scheduling Checks
------------------------------------------------------------

namespace Whiel

namespace Vampire

namespace Smoke

def smokeJobs : List Job :=
  [ initJob
      "init_check" none
      smokePre (by decide) smokeInv,
    stepJob
      "maint_check" none
      smokeInv smokeInv Guard.«true»
      Cmd.skip Cmd.loopFree_skip,
    termJob
      "term_check" none
      smokeInv smokePost (by decide) Guard.«true» ]

def smokeWhen : Condition :=
  Condition.all
    [ Condition.atom "init_check" [Outcome.proved],
      Condition.any
        [ Condition.atom "maint_check" [Outcome.refuted],
          Condition.atom "maint_check" [Outcome.timeout] ] ]

def smokeConditionalJob : Job :=
  stepJob
    "conditional_step" (some smokeWhen)
    smokeInv smokeInv Guard.«true»
    Cmd.skip Cmd.loopFree_skip

def smokeJobsWithCondition : List Job :=
  smokeJobs ++ [smokeConditionalJob]

run_cmd
  unless smokeJobs.length == 3 do
    throwError "expected three smoke jobs"
  unless
      smokeJobs.map (fun job => job.id) ==
        ["init_check", "maint_check", "term_check"] do
    throwError "unexpected smoke job ids"
  unless smokeConditionalJob.when?.isSome do
    throwError "expected conditional smoke job"

end Smoke
end Vampire
end Whiel

------------------------------------------------------------
-- TPTP Name Checks
------------------------------------------------------------

namespace Whiel

namespace Vampire

namespace Smoke

/-
  Two carriers whose spellings differ only outside the
  identifier alphabet. The renderer used to rename the second
  one apart; it no longer renames anything, so the property
  checked here changed from "renamed apart" to "refused":
  `wellFormed` rejects the environment, and the two consumers
  that read one — a worker's binding update and the exact
  reconstruction telescope — reject it in turn.

  `SolverName.ofRepr` is the fallback naming for a carrier
  with nothing proved about it, which is exactly the case the
  refusal exists to cover.
-/
inductive CollisionRel
| edgeDash
| edgeUnderscore
deriving DecidableEq

instance : Repr CollisionRel where
  reprPrec
  | .edgeDash, _ => "Edge-X"
  | .edgeUnderscore, _ => "Edge_X"

instance : RelationNames CollisionRel where
  decEq := inferInstance
  repr := inferInstance

instance : SolverName CollisionRel where
  solverName := SolverName.ofRepr "r"

inductive CollisionConst
| widgetDash
| widgetUnderscore
deriving DecidableEq

instance : Repr CollisionConst where
  reprPrec
  | .widgetDash, _ => "Widget-X"
  | .widgetUnderscore, _ => "Widget_X"

instance : FunctionNames CollisionConst where
  decEq := inferInstance
  repr := inferInstance

instance : SolverName CollisionConst where
  solverName := SolverName.ofRepr "f"

def collisionEnv : TPTP.NameEnv CollisionRel CollisionConst where
  relNames :=
    TPTP.assignSolverNames
      [CollisionRel.edgeDash, CollisionRel.edgeUnderscore]
  funNames :=
    TPTP.assignSolverNames
      [CollisionConst.widgetDash, CollisionConst.widgetUnderscore]

run_cmd
  unless
      collisionEnv.relNames.map (fun p => p.2) ==
        ["r_Edge_X", "r_Edge_X"] do
    throwError "unexpected collision relation names"
  unless
      collisionEnv.funNames.map (fun p => p.2) ==
        ["f_Widget_X", "f_Widget_X"] do
    throwError "unexpected collision function names"
  if collisionEnv.wellFormed then
    throwError "expected the colliding environment to be refused"

/- One legal name each: the same environment is accepted. -/
def distinctEnv : TPTP.NameEnv CollisionRel CollisionConst where
  relNames := [(CollisionRel.edgeDash, "r_edge_dash")]
  funNames := [(CollisionConst.widgetDash, "f_widget_dash")]

run_cmd
  unless distinctEnv.wellFormed do
    throwError "expected the distinct environment to be accepted"
  unless
      (distinctEnv.appendRelation?
        CollisionRel.edgeUnderscore "r_edge_dash").isNone do
    throwError "expected a repeated relation name to be refused"
  unless
      (distinctEnv.appendFunction?
        CollisionConst.widgetUnderscore "r_edge_dash").isNone do
    throwError "expected a cross-kind name to be refused"

/-
  Two legal, distinct names each: every symbol the environment
  declares is named, so the map comment has one line per
  symbol rather than per kind.
-/
def namedSymbolsEnv : TPTP.NameEnv CollisionRel CollisionConst where
  relNames :=
    [ (CollisionRel.edgeDash, "r_edge_dash"),
      (CollisionRel.edgeUnderscore, "r_edge_underscore") ]
  funNames :=
    [ (CollisionConst.widgetDash, "f_widget_dash"),
      (CollisionConst.widgetUnderscore, "f_widget_underscore") ]

run_cmd
  unless namedSymbolsEnv.wellFormed do
    throwError "expected the named-symbols environment to be accepted"

def namedSymbolsMapComment : String :=
  namedSymbolsEnv.symbolMapComment (funLabel := "constant")

run_cmd
  unless namedSymbolsMapComment.contains "% TPTP symbol map:" do
    throwError "expected symbol map header"
  unless
      namedSymbolsMapComment.contains
        "% relation Edge-X -> r_edge_dash" do
    throwError "expected Edge-X relation map"
  unless
      namedSymbolsMapComment.contains
        "% relation Edge_X -> r_edge_underscore" do
    throwError "expected Edge_X relation map"
  unless
      namedSymbolsMapComment.contains
        "% constant Widget-X -> f_widget_dash" do
    throwError "expected Widget-X constant map"
  unless
      namedSymbolsMapComment.contains
        "% constant Widget_X -> f_widget_underscore" do
    throwError "expected Widget_X constant map"

end Smoke
end Vampire
end Whiel

------------------------------------------------------------
-- Manifest And TPTP Checks
------------------------------------------------------------

namespace Whiel

namespace Vampire

namespace Smoke

def smokeJson : String :=
  Lean.Json.compress
    (manifestJson "/tmp/vampire_smoke" smokeJobsWithCondition)

run_cmd
  unless smokeJson.contains "\"manifest_version\":2" do
    throwError "expected manifest version"
  unless
      smokeJson.contains
        "\"artifact_dir\":\"/tmp/vampire_smoke\"" do
    throwError "expected artifact directory"
  unless smokeJson.contains "\"id\":\"init_check\"" do
    throwError "expected init_check job"
  unless smokeJson.contains "\"id\":\"maint_check\"" do
    throwError "expected maint_check job"
  unless smokeJson.contains "\"id\":\"term_check\"" do
    throwError "expected term_check job"
  unless smokeJson.contains "\"id\":\"conditional_step\"" do
    throwError "expected conditional_step job"
  unless smokeJson.contains "\"when\"" do
    throwError "expected conditional field"
  unless smokeJson.contains "\"and\"" do
    throwError "expected and condition"
  unless smokeJson.contains "\"or\"" do
    throwError "expected or condition"
  unless smokeJson.contains "\"job\":\"init_check\"" do
    throwError "expected init_check condition atom"
  unless smokeJson.contains "\"proved\"" do
    throwError "expected proved outcome"
  unless smokeJson.contains "\"refuted\"" do
    throwError "expected refuted outcome"
  unless smokeJson.contains "\"timeout\"" do
    throwError "expected timeout outcome"
  if smokeJson.contains "\"kind\"" then
    throwError "unexpected kind field"
  if smokeJson.contains "clause_id" then
    throwError "unexpected clause_id field"
  if smokeJson.contains "group_id" then
    throwError "unexpected group_id field"
  if smokeJson.contains "job_id" then
    throwError "unexpected job_id field"
  if smokeJson.contains "phase" then
    throwError "unexpected phase field"
  if smokeJson.contains "diagnostic_only" then
    throwError "unexpected diagnostic_only field"
  if smokeJson.contains "expectation" then
    throwError "unexpected expectation field"
  if smokeJson.contains "no_empty_counterexample" then
    throwError "unexpected no_empty_counterexample field"
  if smokeJson.contains "init_diagnostics" then
    throwError "unexpected init_diagnostics field"
  if smokeJson.contains "maint_diagnostics" then
    throwError "unexpected maint_diagnostics field"

def smokeAxioms : String :=
  match smokeJobs with
  | job :: _ => job.axioms
  | _ => ""

run_cmd
  unless smokeAxioms.contains "fof(adom_ax, axiom," do
    throwError "expected smoke adom axiom"
  unless smokeAxioms.contains "fof(source_ax_0, axiom," do
    throwError "expected smoke source axiom"
  unless smokeAxioms.contains "% TPTP symbol map:" do
    throwError "expected smoke symbol map"
  unless smokeAxioms.contains "% relation E -> r_E" do
    throwError "expected smoke relation map"

def smokeConstQF :
    QFEntailment (D := Data) smokeSchema where
  axioms := []
  conjecture := guard![σ[#0 = 0 ∧ #1 = 1] E ⊆ E]

def smokeConstJob : Job :=
  jobOfQF "const_check" none smokeConstQF

run_cmd
  unless smokeConstJob.axioms.contains "fof(cons_ax_0, axiom," do
    throwError "expected constant support axiom"
  unless smokeConstJob.axioms.contains "% constant 0 -> kn0" do
    throwError "expected constant symbol map"

------------------------------------------------------------
-- The One-Shot Environment Is Decided, Not Assumed
------------------------------------------------------------

/-
  The one-shot manifest carrier supplies a name function and
  proves nothing about it, so the entries that emit its
  problem text and its reconstruction metadata decide
  `NameEnv.wellFormed` instead of assuming it. These checks
  pin both answers: the environment a real smoke job renders
  under is usable, and one whose two relations were handed
  the same name, or whose one relation was handed a name no
  solver would read, is not.
-/

def smokeJobEnv :
    TPTP.NameEnv IndexAlphaName Data :=
  jobNameEnvOfQF (initQF smokePre (by decide) smokeInv)

private def relationNamed
    (base : String)
    (hBase : base.toList.all Char.isAlpha = true) :
    IndexAlphaName :=
  { baseName := ⟨base, hBase⟩, index := 0 }

/- Two distinct relations handed one name. -/
def clashingEnv :
    TPTP.NameEnv IndexAlphaName Data :=
  { relNames :=
      [ (relationNamed "E" (by decide), "r_E"),
        (relationNamed "T" (by decide), "r_E") ]
    funNames := [] }

/- One relation handed a name no solver would read. -/
def illegalEnv :
    TPTP.NameEnv IndexAlphaName Data :=
  { relNames := [(relationNamed "E" (by decide), "R E")]
    funNames := [] }

run_cmd
  unless smokeJobEnv.wellFormed do
    throwError "expected a usable smoke job environment"
  if clashingEnv.wellFormed then
    throwError "expected a repeated name to be refused"
  if illegalEnv.wellFormed then
    throwError "expected an illegal name to be refused"

end Smoke
end Vampire
end Whiel
