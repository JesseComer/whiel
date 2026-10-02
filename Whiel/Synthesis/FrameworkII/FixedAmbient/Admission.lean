-- Author: Jesse Comer
import Whiel.Concrete.WhielNames.Order
import
  Whiel.Synthesis.FrameworkII.FixedAmbient.SurfaceSyntax
import Whiel.Synthesis.Runtime.ReferenceProposal

/-
  Lean-owned clause admission over one fixed ambient schema.

  Accepted clauses retain their exact typed formula and
  complete structural identity. Canonical source is a
  separate, parseable representation for Proposal.lean;
  display text is never used as reconstruction authority.
-/

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FixedAmbient

open Concrete
open Runtime

------------------------------------------------------------
-- Admission Diagnostics
------------------------------------------------------------

/- One bounded, agent-correctable admission diagnostic. -/
structure AdmissionDiagnostic where
  code : String
  message : String
  itemIndex? : Option Nat := none
  offset? : Option Nat := none
deriving DecidableEq, Repr

namespace AdmissionDiagnostic

/- Serialize a diagnostic without submitted source text. -/
def toJson (diagnostic : AdmissionDiagnostic) : Lean.Json :=
  let itemFields := match diagnostic.itemIndex? with
    | none => []
    | some index =>
        [("item_index", Lean.Json.num index)]
  let offsetFields := match diagnostic.offset? with
    | none => []
    | some offset =>
        [("offset", Lean.Json.num offset)]
  Lean.Json.mkObj <|
    [ ("code", Lean.Json.str diagnostic.code),
      ("message", Lean.Json.str diagnostic.message) ] ++
      itemFields ++ offsetFields

/- Attach the failing batch ordinal. -/
def atItem
    (index : Nat)
    (diagnostic : AdmissionDiagnostic) :
    AdmissionDiagnostic :=
  { diagnostic with itemIndex? := some index }

end AdmissionDiagnostic

/- Separate correctable content from boundary faults. -/
inductive ClauseAdmissionFailure where
| correctable (diagnostic : AdmissionDiagnostic)
| infrastructure (message : String)
deriving DecidableEq, Repr

/-
  Classify one parser failure.

  Only a lexical or grammatical failure is a defect of the
  submitted clause, and only those two reach the proposer as
  correctable diagnostics. The three resource kinds are not
  verdicts on a proposal:

  * `inputLimit` and `tokenLimit` can fire only when the run
    sets the host limit `clause_text_bytes`, and the host
    refuses an oversized clause under that limit before it is
    ever submitted. Reaching them here means the host and
    this parser disagree about the limit in force.
  * `parserFuel` is a termination guard derived from the
    token count, which no submitted clause can reach.

  All three therefore fail the batch as infrastructure.
-/
private def parserFailure
    (error : SurfaceParser.Error) :
    ClauseAdmissionFailure :=
  match error.kind with
  | .lexical =>
      .correctable
        { code := "clause_lexical_error"
          message :=
            "clause contains unsupported lexical input"
          offset? := some error.offset }
  | .syntax =>
      .correctable
        { code := "clause_syntax_error"
          message :=
            "clause does not match the surface grammar"
          offset? := some error.offset }
  | .inputLimit =>
      .infrastructure
        ("the parser's character bound disagrees with the " ++
          "host clause_text_bytes limit")
  | .tokenLimit =>
      .infrastructure
        ("the parser's token bound disagrees with the " ++
          "host clause_text_bytes limit")
  | .parserFuel =>
      .infrastructure
        "the surface parser exhausted its structural fuel"

private def schemaDiagnostic : AdmissionDiagnostic :=
  { code := "clause_schema_error"
    message :=
      "clause is not well formed over the ambient schema" }

------------------------------------------------------------
-- Admitted Clauses
------------------------------------------------------------

/- One admitted clause over one exact ambient schema. -/
structure Clause
    (Gamma : UnnamedSchema WhielNames) where
  private mk ::
  formula : QFAssertExpr Data Gamma
  identity : ReferenceProposal.StructuralGuard
  identityJson : Lean.Json
  orderKey : String
  canonicalSource : String
  display : String
  relationKeys : List String
  mentionsProphecy : Bool
  minimumLevel : Nat

namespace Clause

/- The complete identity includes an explicit format tag. -/
def tokenJson
    (identity : ReferenceProposal.StructuralGuard) :
    Lean.Json :=
  Lean.Json.mkObj
    [ ("kind", Lean.Json.str
        "whiel_fixed_ambient_clause"),
      ("version", Lean.Json.num 1),
      ("formula", identity.toJson) ]

private def isProphecy : WhielNames -> Bool
| .ordinary _ => false
| .prophecy _ => true

private def formulaMentionsProphecy
    {Gamma : UnnamedSchema WhielNames}
    (formula : QFAssertExpr Data Gamma) : Bool :=
  formula.symbols.sort.any isProphecy

/- Construct metadata from one already checked formula. -/
def ofFormula
    {Gamma : UnnamedSchema WhielNames}
    (formula : QFAssertExpr Data Gamma) : Clause Gamma :=
  let identity := ReferenceProposal.identity formula
  let identityJson := tokenJson identity
  let mentionsProphecy := formulaMentionsProphecy formula
  Clause.mk formula identity identityJson
    identityJson.compress
    (SurfaceSyntax.source formula)
    (SurfaceSyntax.display formula)
    (formula.symbols.sort.map SolverKey.key)
    mentionsProphecy
    (if mentionsProphecy then 1 else 0)

/- Serialize one accepted clause for Rust transport. -/
def toJson
    {Gamma : UnnamedSchema WhielNames}
    (clause : Clause Gamma) : Lean.Json :=
  Lean.Json.mkObj
    [ ("identity", clause.identityJson),
      ("order_key", Lean.Json.str clause.orderKey),
      ("source", Lean.Json.str clause.canonicalSource),
      ("display", Lean.Json.str clause.display),
      ("relation_keys", Lean.Json.arr
        (clause.relationKeys.map Lean.Json.str).toArray),
      ("mentions_prophecy",
        Lean.Json.bool clause.mentionsProphecy),
      ("minimum_level", Lean.Json.num
        clause.minimumLevel) ]

end Clause

------------------------------------------------------------
-- Typed Admission
------------------------------------------------------------

/-
  Admit one raw clause over the exact ambient schema.

  `limits` carries the run's optional host bound on clause
  text and is absent by default: nothing here bounds what a
  proposer may submit.
-/
def admitClause
    (Gamma : UnnamedSchema WhielNames)
    (text : String)
    (limits : SurfaceParser.Limits := {}) :
    Except ClauseAdmissionFailure (Clause Gamma) := do
  let raw <- match SurfaceSyntax.parseWithLimits limits text with
    | .ok raw => .ok raw
    | .error error =>
        .error (parserFailure error)
  match raw.wellFormedError? Gamma with
  | some _ =>
      .error (.correctable schemaDiagnostic)
  | none =>
      match raw.toGuard? Gamma with
      | some formula =>
          return Clause.ofFormula formula
      | none =>
          .error (.infrastructure
            ("schema diagnostics and typed checking " ++
              "disagree"))

private def admitClausesFrom
    (Gamma : UnnamedSchema WhielNames)
    (limits : SurfaceParser.Limits) :
    Nat -> List String ->
      Except ClauseAdmissionFailure (List (Clause Gamma))
| _, [] => .ok []
| index, text :: texts => do
    let clause <- match admitClause Gamma text limits with
      | .ok clause => .ok clause
      | .error (.correctable diagnostic) =>
          .error (.correctable
            (diagnostic.atItem index))
      | .error (.infrastructure message) =>
          .error (.infrastructure message)
    let rest <-
      admitClausesFrom Gamma limits (index + 1) texts
    return clause :: rest

/-
  Admit one batch atomically at its first defect. The batch
  has no item bound: a large submission costs more admission
  work, which is a resource question the host's own timeout
  answers, never a defect of the proposal.
-/
def admitClauses
    (Gamma : UnnamedSchema WhielNames)
    (texts : List String)
    (limits : SurfaceParser.Limits := {}) :
    Except ClauseAdmissionFailure (List (Clause Gamma)) :=
  admitClausesFrom Gamma limits 0 texts

private def uniqueClauseJsonFrom
    {Gamma : UnnamedSchema WhielNames} :
    List ReferenceProposal.StructuralGuard ->
      List (Clause Gamma) -> List Lean.Json
| _, [] => []
| seen, clause :: clauses =>
    if clause.identity ∈ seen then
      uniqueClauseJsonFrom seen clauses
    else
      clause.toJson ::
        uniqueClauseJsonFrom
          (clause.identity :: seen) clauses

/- Admit and deduplicate one batch for Rust transport. -/
def admitClauseJson
    (Gamma : UnnamedSchema WhielNames)
    (texts : List String)
    (limits : SurfaceParser.Limits := {}) :
    Except ClauseAdmissionFailure (List Lean.Json) := do
  let clauses <- admitClauses Gamma texts limits
  return uniqueClauseJsonFrom [] clauses

end FixedAmbient
end FrameworkII
end Synthesis
end Whiel
