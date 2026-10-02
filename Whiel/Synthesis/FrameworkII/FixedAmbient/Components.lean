-- Author: Jesse Comer
import Whiel.Synthesis.FrameworkII.FixedAmbient.Admission
import Whiel.Synthesis.FrameworkII.FixedAmbient.Assembly
import Whiel.Synthesis.Runtime.CanonicalDigest
import Whiel.Synthesis.Runtime.Encoding

/-
  Immutable formula components for the fixed-ambient
  Framework-II product path.

  Every component is typed by the same prophecy schema and
  derived from the lifted loop triple. Canonical source,
  presentation text, and complete structural identity
  remain distinct fields.
-/

namespace Whiel

namespace Synthesis

namespace FrameworkII

namespace FixedAmbient

namespace Component

open Concrete

open Runtime

variable {Gamma : UnnamedSchema WhielNames}

------------------------------------------------------------
-- Formula Packages
------------------------------------------------------------

/- Complete identity of one typed QF formula. -/
def formulaIdentity
    (formula : QFAssertExpr Data Gamma) : Lean.Json :=
  Lean.Json.mkObj
    [ ("kind", Lean.Json.str "whiel_qf_formula"),
      ("version", Lean.Json.num 3),
      ("formula",
        (ReferenceProposal.identity formula).toJson) ]

/- Worker package for one exact Lean formula. -/
def formulaPackage
    (sourceId : String)
    (formula : QFAssertExpr Data Gamma) : Lean.Json :=
  Lean.Json.mkObj
    [ ("source_id", Lean.Json.str sourceId),
      ("formula_identity", formulaIdentity formula),
      ("canonical_source", Lean.Json.str
        (SurfaceSyntax.source formula)),
      ("display", Lean.Json.str
        (SurfaceSyntax.display formula)),
      ("relation_keys", Lean.Json.arr
        (formula.symbols.sort.map
          (fun relation => Lean.Json.str
            (SolverKey.key relation))).toArray),
      ("constant_keys", Lean.Json.arr
        (formula.constants.sort.map
          (fun constant => Lean.Json.str
            (SolverKey.key constant))).toArray),
      ("semantic_theorem", Lean.Json.str
        "Whiel.QFAssertExpr.toRelCalcSentence_correct") ]

/- One same-schema immutable component. -/
structure Metadata
    (Gamma : UnnamedSchema WhielNames) where
  role : String
  baseClauseIdentity? : Option Lean.Json
  sourceId : String
  formula : QFAssertExpr Data Gamma

namespace Metadata

/- Complete identity of one component. -/
def identity
    (scopeIdentity : Lean.Json)
    (metadata : Metadata Gamma) : Lean.Json :=
  let baseFields :=
    match metadata.baseClauseIdentity? with
    | none => []
    | some identity =>
        [("base_clause_identity", identity)]
  Lean.Json.mkObj <| baseFields ++
    [ ("kind", Lean.Json.str
        "whiel_framework_ii_fixed_ambient_component"),
      ("version", Lean.Json.num 1),
      ("scope_identity", scopeIdentity),
      ("role", Lean.Json.str metadata.role),
      ("result_formula_identity",
        formulaIdentity metadata.formula),
      ("source_id", Lean.Json.str metadata.sourceId) ]

/- Stable link to the complete component identity. -/
def digest
    (scopeIdentity : Lean.Json)
    (metadata : Metadata Gamma) : String :=
  CanonicalDigest.jsonSha256
    (metadata.identity scopeIdentity)

/- Admission-time component package. -/
def toJson
    (scopeIdentity : Lean.Json)
    (metadata : Metadata Gamma) : Lean.Json :=
  Lean.Json.mkObj
    [ ("component_identity",
        metadata.identity scopeIdentity),
      ("component_digest", Lean.Json.str
        (metadata.digest scopeIdentity)),
      ("formula", formulaPackage metadata.sourceId
        metadata.formula) ]

end Metadata

private def taskSourceId
    (scopeIdentity : Lean.Json)
    (role : String) : String :=
  "framework_ii.fixed_ambient.component." ++
    CanonicalDigest.jsonSha256 scopeIdentity ++
      "." ++ role

private def clauseSourceId
    (scopeIdentity clauseIdentity : Lean.Json)
    (role : String) : String :=
  taskSourceId scopeIdentity role ++ "." ++
    CanonicalDigest.jsonSha256 clauseIdentity

private def taskMetadata
    (scopeIdentity : Lean.Json)
    (role : String)
    (formula : QFAssertExpr Data Gamma) :
    Metadata Gamma where
  role := role
  baseClauseIdentity? := none
  sourceId := taskSourceId scopeIdentity role
  formula := formula

private def clauseMetadata
    (scopeIdentity : Lean.Json)
    (clause : Clause Gamma)
    (role : String)
    (formula : QFAssertExpr Data Gamma) :
    Metadata Gamma where
  role := role
  baseClauseIdentity? := some clause.identityJson
  sourceId := clauseSourceId scopeIdentity
    clause.identityJson role
  formula := formula

end Component

end FixedAmbient

end FrameworkII

end Synthesis

end Whiel

------------------------------------------------------------
-- Task and Clause Components
------------------------------------------------------------

namespace Whiel

namespace Synthesis

namespace FrameworkII

namespace FixedAmbient

namespace Component

open Concrete

variable {Gamma : UnnamedSchema WhielNames}

/- All immutable components derived from one lifted loop. -/
def taskComponents
    (scopeIdentity : Lean.Json)
    (loop : Hoare.LoopTriple Data Gamma)
    (task : Task loop.body) : List (Metadata Gamma) :=
  [ taskMetadata scopeIdentity "precondition" loop.pre,
    taskMetadata scopeIdentity "guard" loop.guard,
    taskMetadata scopeIdentity "negated_theta_guard"
      (QFAssertExpr.not (task.theta loop.guard)),
    taskMetadata scopeIdentity "negated_guard"
      (QFAssertExpr.not loop.guard),
    taskMetadata scopeIdentity "postcondition" loop.post ]

/- All immutable components derived from one clause. -/
def clauseComponents
    (scopeIdentity : Lean.Json)
    (loop : Hoare.LoopTriple Data Gamma)
    (task : Task loop.body)
    (clause : Clause Gamma) : List (Metadata Gamma) :=
  [ clauseMetadata scopeIdentity clause "clause"
      clause.formula,
    clauseMetadata scopeIdentity clause "theta_clause"
      (task.theta clause.formula),
    clauseMetadata scopeIdentity clause "maintenance_wp"
      (QFAssertExpr.wpLoopFree loop.body
        loop.body_loopFree clause.formula),
    clauseMetadata scopeIdentity clause "collapsed_clause"
      (task.collapseFormula clause.formula) ]

/- Serialize the task component bundle. -/
def taskComponentsJson
    (scopeIdentity : Lean.Json)
    (loop : Hoare.LoopTriple Data Gamma)
    (task : Task loop.body) : Lean.Json :=
  Lean.Json.arr <|
    ((taskComponents scopeIdentity loop task).map
      (Metadata.toJson scopeIdentity)).toArray

/- Serialize one clause component bundle. -/
def clauseComponentsJson
    (scopeIdentity : Lean.Json)
    (loop : Hoare.LoopTriple Data Gamma)
    (task : Task loop.body)
    (clause : Clause Gamma) : Lean.Json :=
  Lean.Json.arr <|
    ((clauseComponents scopeIdentity loop task clause).map
      (Metadata.toJson scopeIdentity)).toArray

/- Resolve exactly one component by complete identity. -/
def resolve?
    (scopeIdentity componentIdentity : Lean.Json)
    (loop : Hoare.LoopTriple Data Gamma)
    (task : Task loop.body)
    (clauses : List (Clause Gamma)) :
    Option (Metadata Gamma) :=
  let components :=
    taskComponents scopeIdentity loop task ++
      clauses.flatMap fun clause =>
        clauseComponents scopeIdentity loop task clause
  components.find? fun metadata =>
    metadata.identity scopeIdentity == componentIdentity

end Component

end FixedAmbient

end FrameworkII

end Synthesis

end Whiel
