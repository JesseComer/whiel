-- Author: Jesse Comer
import Whiel.Synthesis.Runtime.FixedAmbientWorker

set_option linter.hashCommand false

/-
  In-memory protocol checks for the fixed-ambient worker.
  Requests exercise the same pure dispatch function used by
  the framed stdin/stdout loop, under both registered
  bindings.
-/

------------------------------------------------------------
-- Test Fixtures
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Tests
namespace FixedAmbientWorkerTest

open Concrete
open Benchmark.Example0001
open FrameworkII.FixedAmbient
open Runtime.FixedAmbientWorker

private def entry :=
  Runtime.FixedAmbientRegistry.Example0001.entry

/-
  Every check below is stated against the production entry,
  so the file binds the worker to it once. The refutable
  entry is bound explicitly where it is exercised.
-/
local instance productionBound : Runtime.FixedAmbientWorker.Bound :=
  ⟨entry⟩

private abbrev RelationRow :=
  Runtime.FixedAmbientRegistry.Example0001.RelationRow

private abbrev Clause :=
  Runtime.FixedAmbientRegistry.Example0001.Clause

private def emptyPayload : Lean.Json :=
  Lean.Json.mkObj []

private def responseStatus
    (result : Dispatch) : Option String :=
  (result.response.getObjValAs? String "status").toOption

private def responsePayload
    (result : Dispatch) : Lean.Json :=
  result.response.getObjValD "payload"

private def responseErrorKind
    (result : Dispatch) : Option String :=
  ((result.response.getObjValD "error").getObjValAs?
    String "kind").toOption

private def responseField
    (result : Dispatch)
    (field : String) : Lean.Json :=
  result.response.getObjValD field

private def payloadString
    (result : Dispatch)
    (field : String) : Option String :=
  ((responsePayload result).getObjValAs?
    String field).toOption

/-
  One offered relation binding. The controller computes the
  name, but it is a function of the symbol, so a test that
  wants an accepted binding offers exactly that name.
-/
private def relationBinding
    (row : RelationRow) :
    Lean.Json :=
  Lean.Json.mkObj
    [ ("key", Lean.Json.str row.key),
      ("name", Lean.Json.str
        (Vampire.solverName row.relation.1)) ]

private def relationBindings :
    List RelationRow -> List Lean.Json
| [] => []
| row :: rows =>
    relationBinding row :: relationBindings rows

private def fullNameEnvPayload : Lean.Json :=
  Lean.Json.mkObj
    [ ("next_revision", Lean.Json.num 1),
      ("relations", Lean.Json.arr
        (relationBindings entry.relationTable).toArray),
      ("constants", Lean.Json.arr #[]) ]

private def fullNameEnvDispatch : Dispatch :=
  dispatch {} <| Request.forOperation 1 0
    "extend_name_env" fullNameEnvPayload

private def fullNameEnvState : State :=
  fullNameEnvDispatch.state

/- Admit one canonical clause over the prophecy schema. -/
private def admitted (source : String) : Clause :=
  match entry.admitClause source {} with
  | .ok clause => clause
  | .error _ => Clause.ofFormula .true

/- Level-zero Core clause: `S` is the one-step image. -/
private def ordinarySource : String :=
  "(op_zS = (op_zE ∪ π[0,3] (σ[#1 = #2] ((op_zE × op_zT)))))"

/- Level-one Core clause: the prophecy `T∞` is closed. -/
private def levelOneSource : String :=
  "(π[0,3] (σ[#1 = #2] ((op_zT × yp_zT))) ⊆ yp_zT)"

#guard (admitted ordinarySource).canonicalSource ==
  ordinarySource

#guard (admitted levelOneSource).canonicalSource ==
  levelOneSource

#guard (admitted "(yp_zT = ∅[2])").canonicalSource ==
  "(yp_zT = ∅[2])"

#guard (admitted "(¬((op_zT = ∅[2])))").canonicalSource ==
  "(¬((op_zT = ∅[2])))"

private def ordinaryClause : Clause :=
  admitted ordinarySource

/- Mentions a prophecy copy, so its minimum level is one. -/
private def levelOneClause : Clause :=
  admitted levelOneSource

private def prophecyClause : Clause :=
  admitted "(yp_zT = ∅[2])"

private def snapshotRowJson
    (clauseId level : Nat)
    (source : String)
    (identity : Lean.Json) : Lean.Json :=
  Lean.Json.mkObj
    [ ("clause_id", Lean.Json.num clauseId),
      ("level", Lean.Json.num level),
      ("canonical_source", Lean.Json.str source),
      ("identity", identity) ]

private def rowJson
    (clauseId level : Nat)
    (clause : Clause) :
    Lean.Json :=
  snapshotRowJson clauseId level clause.canonicalSource
    clause.identityJson

private def snapshotJson
    (rows : List Lean.Json) : Lean.Json :=
  Lean.Json.mkObj
    [("rows", Lean.Json.arr rows.toArray)]

private def selectorJson
    (kind : String)
    (clauseId? : Option Nat := none) : Lean.Json :=
  match clauseId? with
  | none =>
      Lean.Json.mkObj [("kind", Lean.Json.str kind)]
  | some clauseId =>
      Lean.Json.mkObj
        [ ("kind", Lean.Json.str kind),
          ("clause_id", Lean.Json.num clauseId) ]

private def jobPayload
    (snapshot selector : Lean.Json) : Lean.Json :=
  Lean.Json.mkObj
    [ ("snapshot", snapshot),
      ("selector", selector) ]

private def boundJobPayload
    (job identity : Lean.Json) : Lean.Json :=
  Lean.Json.mkObj
    [ ("obligation_identity", identity),
      ("selector", job.getObjValD "selector"),
      ("snapshot", job.getObjValD "snapshot") ]

private def oneRowSnapshot : Lean.Json :=
  snapshotJson [rowJson 7 0 ordinaryClause]

private def initJobPayload : Lean.Json :=
  jobPayload oneRowSnapshot
    (selectorJson "initialization" (some 7))

private def maintenanceJobPayload : Lean.Json :=
  jobPayload oneRowSnapshot
    (selectorJson "maintenance" (some 7))

private def firstTaskComponentIdentity : Lean.Json :=
  match entry.taskComponents with
  | [] => Lean.Json.null
  | metadata :: _ => metadata.identity entry.scopeIdentity

private def taskComponentPayload : Lean.Json :=
  Lean.Json.mkObj
    [ ("component_identity", firstTaskComponentIdentity),
      ("clause_sources", Lean.Json.arr #[]) ]

private def addExtraField (json : Lean.Json) : Lean.Json :=
  match json with
  | .obj fields =>
      .obj (fields.insert "extra" Lean.Json.null)
  | other => other

------------------------------------------------------------
-- Checked Package and Envelope
------------------------------------------------------------

/- The worker consumes only the production path. -/
example :
    inputPreproc =
      Hoare.preprocess inputPre inputCmd inputPost := by
  rfl

private def describeDispatch : Dispatch :=
  dispatch {} <| Request.forOperation 2 0
    "describe" emptyPayload

#guard responseStatus describeDispatch == some "ok"

/- The raw index-zero check lives in `inputPreproc`; no
  descriptor field claims it. -/
#guard
  ((responsePayload describeDispatch).getObjValAs?
    Bool "raw_base_name_only_checked").toOption == none

#guard
  ((responsePayload describeDispatch).getObjVal? "manifest"
    |>.toOption.bind fun manifest =>
      (manifest.getObjValAs? Nat "format_version").toOption) ==
    some 4

private def pingRequest : Request :=
  Request.forOperation 3 0 "ping" emptyPayload

#guard
  responseStatus (dispatch {} pingRequest) == some "ok"

#guard
  responseErrorKind
      (dispatch {} { pingRequest with
        formatVersion := formatVersion + 1 }) ==
    some "invalid_envelope"

#guard
  responseErrorKind
      (dispatch {} { pingRequest with
        semanticVersion :=
          pingRequest.semanticVersion + 1 }) ==
    some "invalid_envelope"

#guard
  responseErrorKind
      (dispatch {} { pingRequest with
        encodingVersion :=
          pingRequest.encodingVersion + 1 }) ==
    some "invalid_envelope"

#guard
  responseErrorKind
      (dispatch {} { pingRequest with
        taskSourceSha256 := "wrong" }) ==
    some "invalid_envelope"

#guard
  responseErrorKind
      (dispatch {} { pingRequest with
        taskCanonicalId := "wrong" }) ==
    some "invalid_envelope"

#guard
  responseErrorKind
      (dispatch {} { pingRequest with
        taskModule := "wrong" }) ==
    some "invalid_envelope"

#guard
  responseErrorKind
      (dispatch {} { pingRequest with
        taskNamespace := "wrong" }) ==
    some "invalid_envelope"

#guard
  responseErrorKind
      (dispatch {} { pingRequest with
        scopeIdentity := Lean.Json.null }) ==
    some "invalid_envelope"

#guard
  responseErrorKind
      (dispatchJson {} <|
        addExtraField pingRequest.toJson) ==
    some "malformed_request"

/-
  A frame bound to no registry entry echoes no identity. It
  resolved no entry, so reporting one would name a task that
  never saw the frame.
-/
private def unregisteredDispatch : Dispatch :=
  dispatch {} { pingRequest with
    taskCanonicalId := "Not-Registered" }

#guard responseStatus unregisteredDispatch == some "error"

#guard responseErrorKind unregisteredDispatch ==
  some "invalid_envelope"

#guard responseField unregisteredDispatch "task_identity" ==
  Lean.Json.null

#guard responseField unregisteredDispatch "scope_identity" ==
  Lean.Json.null

/- It still echoes the request's own envelope fields. -/
#guard responseField unregisteredDispatch "operation" ==
  Lean.Json.str "ping"

#guard responseField unregisteredDispatch "request_id" ==
  Lean.Json.num pingRequest.requestId

#guard responseField unregisteredDispatch "semantic_version" ==
  Lean.Json.num pingRequest.semanticVersion

#guard responseField unregisteredDispatch "encoding_version" ==
  Lean.Json.num pingRequest.encodingVersion

/- An unparsed frame is bound to no entry either. -/
private def malformedDispatch : Dispatch :=
  dispatchJson {} <| addExtraField pingRequest.toJson

#guard responseField malformedDispatch "task_identity" ==
  Lean.Json.null

#guard responseField malformedDispatch "scope_identity" ==
  Lean.Json.null

/- Every accepted frame still carries the identity it ran
   under. -/
#guard
  ((responseField (dispatch {} pingRequest)
    "task_identity").getObjValAs? String
      "canonical_id").toOption ==
    some "Example0001"

/- So does an envelope error raised under a resolved entry:
   the frame did bind to that task. -/
#guard
  ((responseField
      (dispatch {} { pingRequest with
        taskSourceSha256 := "wrong" })
    "task_identity").getObjValAs? String
      "canonical_id").toOption ==
    some "Example0001"

#guard responseStatus fullNameEnvDispatch == some "ok"

#guard fullNameEnvState.nameEnvRevision == 1

/-
  A legal, unused, unambiguous name that is not the symbol's
  own solver name. The worker refuses it: a name is not a
  choice the controller and the worker agree on, it is the
  value of Lean's own function at that symbol.
-/
private def renamedRelationPayload : Lean.Json :=
  Lean.Json.mkObj
    [ ("next_revision", Lean.Json.num 1),
      ("relations", Lean.Json.arr #[
        Lean.Json.mkObj
          [ ("key", Lean.Json.str "o:p::E"),
            ("name", Lean.Json.str "op_zRenamed") ] ]),
      ("constants", Lean.Json.arr #[]) ]

#guard
  responseErrorKind
      (dispatch {} <| Request.forOperation 28 0
        "extend_name_env" renamedRelationPayload) ==
    some "name_environment"

/-
  The same refusal for a constant: `num:2`'s own solver name
  is `kn2` (pinned above), so a binding that offers it `kn3`
  is refused even though `kn3` is itself a legal, unused name.
-/
private def renamedConstantPayload : Lean.Json :=
  Lean.Json.mkObj
    [ ("next_revision", Lean.Json.num 1),
      ("relations", Lean.Json.arr #[]),
      ("constants", Lean.Json.arr #[
        Lean.Json.mkObj
          [ ("key", Lean.Json.str "num:2"),
            ("name", Lean.Json.str "kn3") ] ]) ]

#guard
  responseErrorKind
      (dispatch {} <| Request.forOperation 29 0
        "extend_name_env" renamedConstantPayload) ==
    some "name_environment"

#guard
  responseErrorKind
      (dispatch fullNameEnvState <|
        Request.forOperation 4 0 "ping" emptyPayload) ==
    some "invalid_envelope"

------------------------------------------------------------
-- Admission and Components
------------------------------------------------------------

/-
  One `admit_clauses` payload. `clause_text_bytes` is the
  run's optional host limit on submitted clause text, and
  `null` — the default of every run — means unbounded.
-/
private def admissionPayloadWith
    (textBytes : Lean.Json)
    (sources : Array Lean.Json) : Lean.Json :=
  Lean.Json.mkObj
    [ ("clause_text_bytes", textBytes),
      ("clauses", Lean.Json.arr sources) ]

private def admissionPayload : Lean.Json :=
  admissionPayloadWith Lean.Json.null
    #[Lean.Json.str ordinaryClause.canonicalSource]

private def admissionDispatch : Dispatch :=
  dispatch {} <| Request.forOperation 5 0
    "admit_clauses" admissionPayload

#guard responseStatus admissionDispatch == some "ok"

#guard payloadString admissionDispatch "outcome" ==
  some "accepted"

private def duplicateAdmissionDispatch : Dispatch :=
  dispatch {} <| Request.forOperation 24 0
    "admit_clauses" <|
      admissionPayloadWith Lean.Json.null
        #[Lean.Json.str ordinaryClause.canonicalSource,
          Lean.Json.str <|
            " " ++ ordinaryClause.canonicalSource]

#guard
  let payload := responsePayload duplicateAdmissionDispatch
  ((payload.getObjValAs?
    (List Lean.Json) "clauses").toOption.map
      List.length) == some 1

private def correctableAdmission : Dispatch :=
  dispatch {} <| Request.forOperation 6 0
    "admit_clauses" <|
      admissionPayloadWith Lean.Json.null
        #[Lean.Json.str "not a clause"]

#guard responseStatus correctableAdmission == some "ok"

#guard payloadString correctableAdmission "outcome" ==
  some "correctable"

/-
  Pass 7.7b: the run's optional `clause_text_bytes` host
  limit travels in the admission payload. Absent (`null`) is
  the default and means unbounded; a value the host itself
  already enforced is carried so the two sides cannot
  silently disagree about the bound in force.
-/
private def boundedAdmission : Dispatch :=
  dispatch {} <| Request.forOperation 60 0
    "admit_clauses" <|
      admissionPayloadWith (Lean.Json.num 4096)
        #[Lean.Json.str ordinaryClause.canonicalSource]

#guard responseStatus boundedAdmission == some "ok"

#guard payloadString boundedAdmission "outcome" ==
  some "accepted"

/-
  Exceeding the host's own limit here means the host and the
  parser disagree — the host refuses an oversized clause
  before submitting it — so the batch fails as
  infrastructure and never as a correctable clause defect.
-/
private def overBoundedAdmission : Dispatch :=
  dispatch {} <| Request.forOperation 61 0
    "admit_clauses" <|
      admissionPayloadWith (Lean.Json.num 4)
        #[Lean.Json.str ordinaryClause.canonicalSource]

#guard responseErrorKind overBoundedAdmission ==
  some "clause_admission"

/- The limit is a required field of the payload contract. -/
#guard
  responseErrorKind
      (dispatch {} <| Request.forOperation 62 0
        "admit_clauses" <| Lean.Json.mkObj
          [("clauses", Lean.Json.arr #[
            Lean.Json.str
              ordinaryClause.canonicalSource])]) ==
    some "malformed_payload"

#guard
  responseErrorKind
      (dispatch {} <| Request.forOperation 63 0
        "admit_clauses" <|
          admissionPayloadWith (Lean.Json.str "4096")
            #[Lean.Json.str
              ordinaryClause.canonicalSource]) ==
    some "malformed_payload"

private def componentDispatch : Dispatch :=
  dispatch fullNameEnvState <|
    Request.forOperation 7 1
      "prepare_component" taskComponentPayload

#guard responseStatus componentDispatch == some "ok"

private def incompleteComponentDispatch : Dispatch :=
  dispatch {} <| Request.forOperation 8 0
    "prepare_component" taskComponentPayload

#guard
  responseErrorKind incompleteComponentDispatch ==
    some "name_environment"

private def extraSourceComponentPayload : Lean.Json :=
  Lean.Json.mkObj
    [ ("component_identity", firstTaskComponentIdentity),
      ("clause_sources", Lean.Json.arr #[
        Lean.Json.str ordinaryClause.canonicalSource]) ]

#guard
  responseErrorKind
      (dispatch fullNameEnvState <|
        Request.forOperation 9 1 "prepare_component"
          extraSourceComponentPayload) ==
    some "component_identity"

------------------------------------------------------------
-- Exact Obligations
------------------------------------------------------------

private def buildDispatch : Dispatch :=
  dispatch {} <| Request.forOperation 10 0
    "build_exact_obligation" initJobPayload

#guard responseStatus buildDispatch == some "ok"

private def builtObligationIdentity : Lean.Json :=
  (responsePayload buildDispatch).getObjValD
    "obligation_identity"

private def boundInitJobPayload : Lean.Json :=
  boundJobPayload initJobPayload builtObligationIdentity

private def prepareDispatch : Dispatch :=
  dispatch fullNameEnvState <|
    Request.forOperation 11 1
      "prepare_exact_obligation" boundInitJobPayload

#guard responseStatus prepareDispatch == some "ok"

private def incompletePrepareDispatch : Dispatch :=
  dispatch {} <| Request.forOperation 12 0
    "prepare_exact_obligation" boundInitJobPayload

#guard
  responseErrorKind incompletePrepareDispatch ==
    some "name_environment"

private def emptyDispatch : Dispatch :=
  dispatch fullNameEnvState <|
    Request.forOperation 13 1
      "check_empty_counterexample" boundInitJobPayload

#guard responseStatus emptyDispatch == some "ok"

#guard
  (responsePayload prepareDispatch).getObjValD
      "obligation_identity" == builtObligationIdentity

#guard
  (responsePayload emptyDispatch).getObjValD
      "obligation_identity" == builtObligationIdentity

private def tamperedBoundJobPayload : Lean.Json :=
  boundJobPayload initJobPayload Lean.Json.null

#guard
  responseErrorKind
      (dispatch fullNameEnvState <|
        Request.forOperation 25 1
          "prepare_exact_obligation"
          tamperedBoundJobPayload) ==
    some "obligation_identity"

#guard
  responseErrorKind
      (dispatch fullNameEnvState <|
        Request.forOperation 26 1
          "check_empty_counterexample"
          tamperedBoundJobPayload) ==
    some "obligation_identity"

private def unknownSelectorPayload : Lean.Json :=
  jobPayload oneRowSnapshot
    (selectorJson "initialization" (some 99))

#guard
  responseErrorKind
      (dispatch {} <| Request.forOperation 14 0
        "build_exact_obligation" unknownSelectorPayload) ==
    some "obligation_identity"

private def noncanonicalSnapshot : Lean.Json :=
  snapshotJson [snapshotRowJson 7 0
    (" " ++ ordinaryClause.canonicalSource)
    ordinaryClause.identityJson]

#guard
  responseErrorKind
      (dispatch {} <| Request.forOperation 15 0
        "build_exact_obligation" <|
          jobPayload noncanonicalSnapshot
            (selectorJson "initialization" (some 7))) ==
    some "obligation_identity"

private def mismatchedSnapshot : Lean.Json :=
  snapshotJson [snapshotRowJson 7 0
    ordinaryClause.canonicalSource
    levelOneClause.identityJson]

#guard
  responseErrorKind
      (dispatch {} <| Request.forOperation 16 0
        "build_exact_obligation" <|
          jobPayload mismatchedSnapshot
            (selectorJson "initialization" (some 7))) ==
    some "obligation_identity"

private def duplicateIdSnapshot : Lean.Json :=
  snapshotJson
    [ rowJson 7 0 ordinaryClause,
      rowJson 7 1 levelOneClause ]

#guard
  responseErrorKind
      (dispatch {} <| Request.forOperation 17 0
        "build_exact_obligation" <|
          jobPayload duplicateIdSnapshot
            (selectorJson "initialization" (some 7))) ==
    some "obligation_identity"

private def duplicateIdentitySnapshot : Lean.Json :=
  snapshotJson
    [ rowJson 7 0 ordinaryClause,
      rowJson 8 1 ordinaryClause ]

#guard
  responseErrorKind
      (dispatch {} <| Request.forOperation 18 0
        "build_exact_obligation" <|
          jobPayload duplicateIdentitySnapshot
            (selectorJson "initialization" (some 7))) ==
    some "obligation_identity"

private def belowMinimumSnapshot : Lean.Json :=
  snapshotJson [rowJson 7 0 prophecyClause]

#guard
  responseErrorKind
      (dispatch {} <| Request.forOperation 19 0
        "build_exact_obligation" <|
          jobPayload belowMinimumSnapshot
            (selectorJson "initialization" (some 7))) ==
    some "obligation_identity"

private def unorderedSnapshot : Lean.Json :=
  snapshotJson
    [ rowJson 8 1 levelOneClause,
      rowJson 7 0 ordinaryClause ]

#guard
  responseErrorKind
      (dispatch {} <| Request.forOperation 20 0
        "build_exact_obligation" <|
          jobPayload unorderedSnapshot
            (selectorJson "initialization" (some 7))) ==
    some "obligation_identity"

private def conjectureSourceId
    (result : Dispatch) : Option String :=
  let conjecture :=
    responsePayload result |>
      (fun payload =>
        payload.getObjValD "conjecture_body")
  (conjecture.getObjValAs? String "source_id").toOption

private def maintenanceBuildDispatch : Dispatch :=
  dispatch {} <| Request.forOperation 27 0
    "build_exact_obligation" maintenanceJobPayload

private def maintenanceBoundJobPayload : Lean.Json :=
  let identity :=
    (responsePayload maintenanceBuildDispatch).getObjValD
      "obligation_identity"
  boundJobPayload maintenanceJobPayload identity

private def maintenancePrepareDispatch : Dispatch :=
  dispatch fullNameEnvState <|
    Request.forOperation 21 1
      "prepare_exact_obligation" maintenanceBoundJobPayload

#guard
  responseStatus maintenancePrepareDispatch == some "ok"

#guard
  conjectureSourceId prepareDispatch !=
    conjectureSourceId maintenancePrepareDispatch

------------------------------------------------------------
-- Axiom Role Tags
------------------------------------------------------------

private def axiomTagsOf (result : Dispatch) : List Lean.Json :=
  ((responsePayload result).getObjValAs?
    (List Lean.Json) "axiom_tags").toOption.getD []

private def axiomBodiesOf
    (result : Dispatch) : List Lean.Json :=
  ((responsePayload result).getObjValAs?
    (List Lean.Json) "axiom_bodies").toOption.getD []

private def tagAt
    (result : Dispatch) (index : Nat) : Lean.Json :=
  (axiomTagsOf result).getD index Lean.Json.null

private def tagName (tag : Lean.Json) : Option String :=
  (tag.getObjValAs? String "name").toOption

private def tagRole (tag : Lean.Json) : Option String :=
  (tag.getObjValAs? String "tag").toOption

private def tagIdentity (tag : Lean.Json) : Lean.Json :=
  tag.getObjValD "identity"

private def bodySourceId (body : Lean.Json) : Option String :=
  (body.getObjValAs? String "source_id").toOption

/- Roles of the axiom-list prefix, before the appended
   support entries. -/
private def axiomPrefixRoles
    (result : Dispatch) : List (Option String) :=
  ((axiomTagsOf result).take
    (axiomBodiesOf result).length).map tagRole

/- Roles of the appended support entries. -/
private def supportSuffixRoles
    (result : Dispatch) : List (Option String) :=
  ((axiomTagsOf result).drop
    (axiomBodiesOf result).length).map tagRole

/-
  The axiom-list prefix of the table names the emitted axiom
  bodies one-to-one, in the same order.
-/
private def axiomTagNamesMatchBodies
    (result : Dispatch) : Bool :=
  let bodies := axiomBodiesOf result
  let tags := axiomTagsOf result
  (bodies.map bodySourceId) ==
    (tags.take bodies.length).map tagName

/- Every table entry names a distinct axiom. -/
private def axiomTagNamesUnique (result : Dispatch) : Bool :=
  let names := (axiomTagsOf result).filterMap tagName
  names.eraseDups.length == names.length

/- The mixed-arity, levels-0/1 two-row Core used below. -/
private def lowerAndSameLevelSnapshot : Lean.Json :=
  snapshotJson
    [ rowJson 60 0 ordinaryClause,
      rowJson 61 1 levelOneClause ]

private def levelOneInitJobPayload : Lean.Json :=
  jobPayload lowerAndSameLevelSnapshot
    (selectorJson "initialization" (some 61))

private def levelOneMaintenanceJobPayload : Lean.Json :=
  jobPayload lowerAndSameLevelSnapshot
    (selectorJson "maintenance" (some 61))

private def levelOneTerminationJobPayload : Lean.Json :=
  jobPayload lowerAndSameLevelSnapshot
    (selectorJson "termination")

/- Build then prepare one job payload against a fresh name
   environment, mirroring `prepareDispatch` above. -/
private def buildAndPrepare
    (requestId : Nat)
    (payload : Lean.Json) : Dispatch :=
  let built :=
    dispatch {} <|
      Request.forOperation requestId 0
        "build_exact_obligation" payload
  let identity :=
    (responsePayload built).getObjValD "obligation_identity"
  let bound := boundJobPayload payload identity
  dispatch fullNameEnvState <|
    Request.forOperation (requestId + 1) 1
      "prepare_exact_obligation" bound

private def levelOneInitPrepare : Dispatch :=
  buildAndPrepare 200 levelOneInitJobPayload

private def levelOneMaintenancePrepare : Dispatch :=
  buildAndPrepare 202 levelOneMaintenanceJobPayload

private def levelOneTerminationPrepare : Dispatch :=
  buildAndPrepare 204 levelOneTerminationJobPayload

#guard responseStatus levelOneInitPrepare == some "ok"

#guard responseStatus levelOneMaintenancePrepare == some "ok"

#guard responseStatus levelOneTerminationPrepare == some "ok"

/-
  Initialization at level zero: `pre`, then only supports.
  (`prepareDispatch` above is the level-zero initialization
  of `ordinaryClause` from `initJobPayload`.)
-/
#guard axiomPrefixRoles prepareDispatch == [some "pre"]

#guard tagIdentity (tagAt prepareDispatch 0) == Lean.Json.null

#guard
  0 < (supportSuffixRoles prepareDispatch).length &&
    (supportSuffixRoles prepareDispatch).all
      (· == some "support")

#guard axiomTagNamesMatchBodies prepareDispatch

#guard axiomTagNamesUnique prepareDispatch

/-
  Initialization at level one with one lower clause: `pre`,
  `not_theta_guard`, `theta` of the one lower row, then
  supports.
-/
#guard
  axiomPrefixRoles levelOneInitPrepare ==
    [some "pre", some "not_theta_guard", some "theta"]

#guard
  tagIdentity (tagAt levelOneInitPrepare 0) ==
    Lean.Json.null

#guard
  tagIdentity (tagAt levelOneInitPrepare 1) ==
    Lean.Json.null

#guard
  tagIdentity (tagAt levelOneInitPrepare 2) ==
    ordinaryClause.identityJson

#guard
  0 < (supportSuffixRoles levelOneInitPrepare).length &&
    (supportSuffixRoles levelOneInitPrepare).all
      (· == some "support")

#guard axiomTagNamesMatchBodies levelOneInitPrepare

#guard axiomTagNamesUnique levelOneInitPrepare

/-
  Maintenance at level one with one lower and one same-level
  clause: `plain` for every `upTo` row (the lower row, then
  the conjecture's own row), `guard`, `not_theta_guard`,
  `theta` of the one lower row, then supports.
-/
#guard
  axiomPrefixRoles levelOneMaintenancePrepare ==
    [some "plain", some "plain", some "guard",
      some "not_theta_guard", some "theta"]

#guard
  tagIdentity (tagAt levelOneMaintenancePrepare 0) ==
    ordinaryClause.identityJson

#guard
  tagIdentity (tagAt levelOneMaintenancePrepare 1) ==
    levelOneClause.identityJson

#guard
  tagIdentity (tagAt levelOneMaintenancePrepare 2) ==
    Lean.Json.null

#guard
  tagIdentity (tagAt levelOneMaintenancePrepare 3) ==
    Lean.Json.null

#guard
  tagIdentity (tagAt levelOneMaintenancePrepare 4) ==
    ordinaryClause.identityJson

#guard
  0 <
      (supportSuffixRoles levelOneMaintenancePrepare).length &&
    (supportSuffixRoles levelOneMaintenancePrepare).all
      (· == some "support")

#guard axiomTagNamesMatchBodies levelOneMaintenancePrepare

#guard axiomTagNamesUnique levelOneMaintenancePrepare

/-
  Termination: `not_guard`, then `collapsed` for every row in
  catalog order, then supports.
-/
#guard
  axiomPrefixRoles levelOneTerminationPrepare ==
    [some "not_guard", some "collapsed", some "collapsed"]

#guard
  tagIdentity (tagAt levelOneTerminationPrepare 0) ==
    Lean.Json.null

#guard
  tagIdentity (tagAt levelOneTerminationPrepare 1) ==
    ordinaryClause.identityJson

#guard
  tagIdentity (tagAt levelOneTerminationPrepare 2) ==
    levelOneClause.identityJson

#guard
  0 <
      (supportSuffixRoles levelOneTerminationPrepare).length &&
    (supportSuffixRoles levelOneTerminationPrepare).all
      (· == some "support")

#guard axiomTagNamesMatchBodies levelOneTerminationPrepare

#guard axiomTagNamesUnique levelOneTerminationPrepare

/-
  Adding the axiom-role table does not perturb the emitted
  TPTP bodies: `prepareEntailmentJson` still renders
  `axiom_bodies`, `conjecture_body`, and `support` from the
  exact same `built.entailment` and name environment as
  before the table existed, so the level-one initialization
  and maintenance jobs above still disagree on their
  conjecture body exactly as the level-zero jobs already do.
-/
#guard
  conjectureSourceId levelOneInitPrepare !=
    conjectureSourceId levelOneMaintenancePrepare

------------------------------------------------------------
-- Opaque Formula Pieces
------------------------------------------------------------

private def piecesOf (result : Dispatch) : List Lean.Json :=
  ((responsePayload result).getObjValAs?
    (List Lean.Json) "pieces").toOption.getD []

private def pieceRole (piece : Lean.Json) : Option String :=
  (piece.getObjValAs? String "role").toOption

private def pieceBody (piece : Lean.Json) : Option String :=
  ((piece.getObjValD "body").getObjValAs?
    String "body").toOption

private def pieceSourceId (piece : Lean.Json) : Option String :=
  ((piece.getObjValD "body").getObjValAs?
    String "source_id").toOption

private def pieceIdentity (piece : Lean.Json) : Lean.Json :=
  piece.getObjValD "formula_identity"

private def findPiece
    (pieces : List Lean.Json)
    (role : String) : Lean.Json :=
  (pieces.find? fun piece =>
    pieceRole piece == some role).getD Lean.Json.null

private def taskPiecesDispatch : Dispatch :=
  dispatch fullNameEnvState <|
    Request.forOperation 300 1
      "prepare_task_pieces" emptyPayload

#guard responseStatus taskPiecesDispatch == some "ok"

#guard (piecesOf taskPiecesDispatch).length == 5

/- The five task pieces arrive in Lean's component order. -/
#guard (piecesOf taskPiecesDispatch).map pieceRole ==
  [ some "precondition", some "guard",
    some "negated_theta_guard", some "negated_guard",
    some "postcondition" ]

/- A piece keeps the immutable component's source ID and
   complete formula identity, so the controller can bind a
   rendered body to the component it admitted. -/
#guard
  ((piecesOf taskPiecesDispatch).map pieceSourceId) ==
    entry.taskComponents.map
      (fun metadata => some metadata.sourceId)

#guard
  ((piecesOf taskPiecesDispatch).map pieceIdentity) ==
    entry.taskComponents.map
      (fun metadata =>
        Component.formulaIdentity metadata.formula)

#guard
  ((piecesOf taskPiecesDispatch).all
    fun piece => (pieceBody piece).isSome)

/- Pieces need the same complete name environment every
   other rendering needs. -/
#guard
  responseErrorKind
      (dispatch {} <| Request.forOperation 301 0
        "prepare_task_pieces" emptyPayload) ==
    some "name_environment"

private def clausePieceRowJson
    (clause : Clause) : Lean.Json :=
  Lean.Json.mkObj
    [ ("canonical_source",
        Lean.Json.str clause.canonicalSource),
      ("identity", clause.identityJson) ]

private def clausePiecesPayload
    (clauses : List Clause) : Lean.Json :=
  Lean.Json.mkObj
    [("clauses", Lean.Json.arr
      (clauses.map clausePieceRowJson).toArray)]

private def clausePiecesDispatch : Dispatch :=
  dispatch fullNameEnvState <|
    Request.forOperation 302 1 "prepare_clause_pieces"
      (clausePiecesPayload [ordinaryClause, levelOneClause])

#guard responseStatus clausePiecesDispatch == some "ok"

private def clausePieceRows
    (result : Dispatch) : List Lean.Json :=
  ((responsePayload result).getObjValAs?
    (List Lean.Json) "clauses").toOption.getD []

#guard (clausePieceRows clausePiecesDispatch).length == 2

private def clausePiecesFor
    (clause : Clause) : List Lean.Json :=
  match (clausePieceRows clausePiecesDispatch).find?
      fun row =>
        row.getObjValD "identity" == clause.identityJson with
  | none => []
  | some row =>
      (row.getObjValAs? (List Lean.Json) "pieces").toOption.getD []

private def clausePieceBody
    (clause : Clause)
    (role : String) : Option String :=
  pieceBody (findPiece (clausePiecesFor clause) role)

private def taskPieceBody (role : String) : Option String :=
  pieceBody (findPiece (piecesOf taskPiecesDispatch) role)

/- Each clause carries its four immutable pieces, in Lean's
   component order. -/
#guard
  (clausePiecesFor ordinaryClause).map pieceRole ==
    [ some "clause", some "theta_clause",
      some "maintenance_wp", some "collapsed_clause" ]

#guard
  (clausePiecesFor levelOneClause).map pieceRole ==
    [ some "clause", some "theta_clause",
      some "maintenance_wp", some "collapsed_clause" ]

#guard
  ((clausePiecesFor ordinaryClause).map pieceSourceId) ==
    (entry.clauseComponents ordinaryClause).map
      (fun metadata => some metadata.sourceId)

#guard
  ((clausePiecesFor levelOneClause).map pieceIdentity) ==
    (entry.clauseComponents levelOneClause).map
      (fun metadata =>
        Component.formulaIdentity metadata.formula)

#guard
  responseErrorKind
      (dispatch fullNameEnvState <|
        Request.forOperation 303 1 "prepare_clause_pieces"
          (clausePiecesPayload
            [ordinaryClause, ordinaryClause])) ==
    some "clause_admission"

/-
  The splice: every axiom body of an exactly assembled
  obligation is one rendered piece, in the order
  `Obligations.lean` emits it, and the conjecture is the
  piece the selector names. This is the Lean-side statement
  of the property the Rust differential test checks on the
  live path.
-/
private def axiomBodyTexts
    (result : Dispatch) : List (Option String) :=
  (axiomBodiesOf result).map fun body =>
    (body.getObjValAs? String "body").toOption

private def conjectureBodyText
    (result : Dispatch) : Option String :=
  ((responsePayload result).getObjValD
    "conjecture_body").getObjValAs? String "body"
      |>.toOption

/- Level-zero initialization of `ordinaryClause`: `pre`
   alone, with the plain clause as conjecture. -/
#guard axiomBodyTexts prepareDispatch ==
  [taskPieceBody "precondition"]

#guard conjectureBodyText prepareDispatch ==
  clausePieceBody ordinaryClause "clause"

#guard (taskPieceBody "precondition").isSome

/- Level-one initialization of `levelOneClause` over one
   strictly lower row. -/
#guard axiomBodyTexts levelOneInitPrepare ==
  [ taskPieceBody "precondition",
    taskPieceBody "negated_theta_guard",
    clausePieceBody ordinaryClause "theta_clause" ]

#guard conjectureBodyText levelOneInitPrepare ==
  clausePieceBody levelOneClause "clause"

/- Level-one maintenance: plain rows at or below the level,
   the guard, the negated theta guard, and theta of each
   strictly lower row; the weakest precondition is the
   conjecture. -/
#guard axiomBodyTexts levelOneMaintenancePrepare ==
  [ clausePieceBody ordinaryClause "clause",
    clausePieceBody levelOneClause "clause",
    taskPieceBody "guard",
    taskPieceBody "negated_theta_guard",
    clausePieceBody ordinaryClause "theta_clause" ]

#guard conjectureBodyText levelOneMaintenancePrepare ==
  clausePieceBody levelOneClause "maintenance_wp"

/- Termination: the negated guard and every collapsed row,
   with the postcondition as conjecture. -/
#guard axiomBodyTexts levelOneTerminationPrepare ==
  [ taskPieceBody "negated_guard",
    clausePieceBody ordinaryClause "collapsed_clause",
    clausePieceBody levelOneClause "collapsed_clause" ]

#guard conjectureBodyText levelOneTerminationPrepare ==
  taskPieceBody "postcondition"

private def supportOf (result : Dispatch) : Lean.Json :=
  (responsePayload result).getObjValD "support"

private def supportConstantKeys
    (result : Dispatch) : List String :=
  ((supportOf result).getObjValAs?
    (List String) "constant_keys").toOption.getD []

private def supportBlockPayload
    (keys : List String) : Lean.Json :=
  Lean.Json.mkObj
    [("constant_keys", Lean.Json.arr
      (keys.map Lean.Json.str).toArray)]

private def supportBlockDispatch : Dispatch :=
  dispatch fullNameEnvState <|
    Request.forOperation 304 1 "prepare_support_block"
      (supportBlockPayload
        (supportConstantKeys prepareDispatch))

#guard responseStatus supportBlockDispatch == some "ok"

/- One support block per constant set, byte-identical to the
   block the whole-obligation assembly emits. -/
#guard
  responsePayload supportBlockDispatch ==
    supportOf prepareDispatch

#guard
  responsePayload supportBlockDispatch ==
    supportOf levelOneTerminationPrepare

#guard
  responseErrorKind
      (dispatch fullNameEnvState <|
        Request.forOperation 305 1 "prepare_support_block"
          (supportBlockPayload ["not-a-key"])) ==
    some "support_constants"

#guard
  responseErrorKind
      (dispatch fullNameEnvState <|
        Request.forOperation 306 1 "prepare_support_block"
          (supportBlockPayload ["str:a", "str:a"])) ==
    some "support_constants"

/- A set given in the controller's own solver-key order, not Lean's
   domain order, is accepted: the block is a function of the set. -/
private def constantNameEnvState : State :=
  (dispatch {} <| Request.forOperation 308 0
    "extend_name_env" <| Lean.Json.mkObj
      [ ("next_revision", Lean.Json.num 1),
        ("relations", Lean.Json.arr
          (relationBindings entry.relationTable).toArray),
        ("constants", Lean.Json.arr #[
          Lean.Json.mkObj
            [ ("key", Lean.Json.str "num:2"),
              ("name", Lean.Json.str "kn2") ],
          Lean.Json.mkObj
            [ ("key", Lean.Json.str "num:10"),
              ("name", Lean.Json.str "kn10") ] ]) ]).state

#guard constantNameEnvState.nameEnvRevision == 1

private def unsortedSupportDispatch : Dispatch :=
  dispatch constantNameEnvState <|
    Request.forOperation 309 1 "prepare_support_block"
      (supportBlockPayload ["num:10", "num:2"])

private def sortedSupportDispatch : Dispatch :=
  dispatch constantNameEnvState <|
    Request.forOperation 310 1 "prepare_support_block"
      (supportBlockPayload ["num:2", "num:10"])

#guard responseStatus unsortedSupportDispatch == some "ok"

#guard
  responsePayload unsortedSupportDispatch ==
    responsePayload sortedSupportDispatch

#guard
  ((responsePayload unsortedSupportDispatch).getObjValAs?
    (List String) "constant_keys").toOption ==
    some ["num:2", "num:10"]

#guard
  responseErrorKind
      (dispatch {} <| Request.forOperation 307 0
        "prepare_support_block"
        (supportBlockPayload [])) ==
    some "name_environment"

------------------------------------------------------------
-- Finite-Model Refutation Validation
------------------------------------------------------------

private def edbClause : Clause :=
  match entry.admitClause "(op_zE = ∅[2])" {} with
  | .ok clause => clause
  | .error _ => ordinaryClause

#guard edbClause.canonicalSource == "(op_zE = ∅[2])"

private def edbSnapshot : Lean.Json :=
  snapshotJson [rowJson 9 0 edbClause]

private def edbInitJobPayload : Lean.Json :=
  jobPayload edbSnapshot
    (selectorJson "initialization" (some 9))

private def edbBuildDispatch : Dispatch :=
  dispatch {} <| Request.forOperation 30 0
    "build_exact_obligation" edbInitJobPayload

#guard responseStatus edbBuildDispatch == some "ok"

private def edbObligationIdentity : Lean.Json :=
  (responsePayload edbBuildDispatch).getObjValD
    "obligation_identity"

/- One complete one-element ambient interpretation. -/
private def tupleJson (cells : List String) : Lean.Json :=
  Lean.Json.arr (cells.map Lean.Json.str).toArray

private def relationJson
    (key : String)
    (rows : List (List String)) : Lean.Json :=
  Lean.Json.mkObj
    [ ("name", Lean.Json.str key),
      ("rows", Lean.Json.arr (rows.map tupleJson).toArray) ]

private def interpretationJson
    (rowsFor : String -> List (List String)) : Lean.Json :=
  let relations := entry.relationTable.map fun row =>
    relationJson row.key (rowsFor row.key)
  Lean.Json.mkObj
    [ ("carrier_keys",
        Lean.Json.arr #[Lean.Json.str "num:1"]),
      ("relations", Lean.Json.arr relations.toArray) ]

/-
  One edge with `T = ∅` and `S = E` satisfies the computed
  loop precondition and falsifies `E = ∅`.
-/
private def refutingInterpretation : Lean.Json :=
  interpretationJson fun key =>
    if key == "o:p::E" || key == "o:p::S" then
      [["num:1", "num:1"]]
    else
      []

/- One edge with `S = ∅` violates the loop precondition. -/
private def preconditionViolatingInterpretation :
    Lean.Json :=
  interpretationJson fun key =>
    if key == "o:p::E" then [["num:1", "num:1"]] else []

private def satisfyingInterpretation : Lean.Json :=
  interpretationJson fun _ => []

private def refutationPayload
    (interpretation : Lean.Json) : Lean.Json :=
  Lean.Json.mkObj
    [ ("obligation_identity", edbObligationIdentity),
      ("selector", edbInitJobPayload.getObjValD "selector"),
      ("snapshot", edbInitJobPayload.getObjValD "snapshot"),
      ("interpretation", interpretation) ]

private def refutingDispatch : Dispatch :=
  dispatch {} <| Request.forOperation 31 0
    "validate_refutation"
    (refutationPayload refutingInterpretation)

#guard responseStatus refutingDispatch == some "ok"

#guard
  ((responsePayload refutingDispatch).getObjValAs? Bool
    "validated_refutation").toOption == some true

#guard
  ((responsePayload refutingDispatch).getObjValAs? Bool
    "axioms_hold").toOption == some true

#guard
  (responsePayload refutingDispatch).getObjValD
      "obligation_identity" == edbObligationIdentity

private def satisfyingDispatch : Dispatch :=
  dispatch {} <| Request.forOperation 32 0
    "validate_refutation"
    (refutationPayload satisfyingInterpretation)

#guard responseStatus satisfyingDispatch == some "ok"

#guard
  ((responsePayload satisfyingDispatch).getObjValAs? Bool
    "validated_refutation").toOption == some false

/- A model of the conjecture alone refutes nothing. -/
private def violatingDispatch : Dispatch :=
  dispatch {} <| Request.forOperation 56 0
    "validate_refutation"
    (refutationPayload preconditionViolatingInterpretation)

#guard responseStatus violatingDispatch == some "ok"

#guard
  ((responsePayload violatingDispatch).getObjValAs? Bool
    "axioms_hold").toOption == some false

#guard
  ((responsePayload violatingDispatch).getObjValAs? Bool
    "validated_refutation").toOption == some false

#guard
  responseErrorKind
      (dispatch {} <| Request.forOperation 33 0
        "validate_refutation"
        (refutationPayload Lean.Json.null)) ==
    some "refutation_validation"

/- An interpretation missing a relation is rejected. -/
private def incompleteInterpretation : Lean.Json :=
  match refutingInterpretation,
      refutingInterpretation.getObjVal? "relations" with
  | .obj fields, .ok (.arr relations) =>
      Lean.Json.obj (fields.insert "relations"
        (Lean.Json.arr
          (relations.extract 0 (relations.size - 1))))
  | other, _ => other

#guard
  responseErrorKind
      (dispatch {} <| Request.forOperation 37 0
        "validate_refutation"
        (refutationPayload incompleteInterpretation)) ==
    some "refutation_validation"

/- The EDB row is invariant: no maintenance refutation. -/
private def edbMaintenanceJobPayload : Lean.Json :=
  jobPayload edbSnapshot
    (selectorJson "maintenance" (some 9))

private def edbMaintenanceBuildDispatch : Dispatch :=
  dispatch {} <| Request.forOperation 38 0
    "build_exact_obligation" edbMaintenanceJobPayload

#guard responseStatus edbMaintenanceBuildDispatch == some "ok"

private def edbMaintenanceIdentity : Lean.Json :=
  (responsePayload edbMaintenanceBuildDispatch).getObjValD
    "obligation_identity"

private def maintenanceRefutationPayload
    (interpretation : Lean.Json) : Lean.Json :=
  Lean.Json.mkObj
    [ ("obligation_identity", edbMaintenanceIdentity),
      ("selector",
        edbMaintenanceJobPayload.getObjValD "selector"),
      ("snapshot",
        edbMaintenanceJobPayload.getObjValD "snapshot"),
      ("interpretation", interpretation) ]

#guard
  ((responsePayload
    (dispatch {} <| Request.forOperation 39 0
      "validate_refutation"
      (maintenanceRefutationPayload
        refutingInterpretation))).getObjValAs? Bool
    "validated_refutation").toOption == some false

#guard
  ((responsePayload
    (dispatch {} <| Request.forOperation 40 0
      "validate_refutation"
      (maintenanceRefutationPayload
        satisfyingInterpretation))).getObjValAs? Bool
    "validated_refutation").toOption == some false

#guard
  responseErrorKind
      (dispatch {} <| Request.forOperation 34 0
        "validate_refutation"
        (addExtraField
          (refutationPayload refutingInterpretation))) ==
    some "obligation_identity"

------------------------------------------------------------
-- Direct Clause Evaluation
------------------------------------------------------------

/-
  Truth table over two clauses (`ordinaryClause` is
  prophecy-free; `levelOneClause` mentions `yp_zT`) and two
  instances: `preconditionViolatingInterpretation` (`E`
  populated, `T` empty, `S` empty) and
  `satisfyingInterpretation` (every relation empty).

  On `preconditionViolatingInterpretation`: the ordinary
  clause's right side is `E ∪ π(σ(E × T)) = E ∪ ∅ = E`, while
  `S = ∅`, so it is false; `T = ∅` makes the level-one
  clause's left side `∅`, so it holds vacuously. On
  `satisfyingInterpretation` every relation is `∅`, so both
  clauses hold.
-/
private def truthTableDispatch : Dispatch :=
  dispatch {} <| Request.forOperation 60 0
    "evaluate_clauses" <| Lean.Json.mkObj
      [ ("clauses", Lean.Json.arr #[
          Lean.Json.str ordinaryClause.canonicalSource,
          Lean.Json.str levelOneClause.canonicalSource]),
        ("instances", Lean.Json.arr #[
          preconditionViolatingInterpretation,
          satisfyingInterpretation]) ]

#guard responseStatus truthTableDispatch == some "ok"

private def truthTableResults : List Lean.Json :=
  ((responsePayload truthTableDispatch).getObjValAs?
    (List Lean.Json) "results").toOption.getD []

#guard truthTableResults.length == 2

#guard
  ((truthTableResults.getD 0 Lean.Json.null).getObjValAs?
    (List Bool) "holds").toOption == some [false, true]

#guard
  ((truthTableResults.getD 1 Lean.Json.null).getObjValAs?
    (List Bool) "holds").toOption == some [true, true]

#guard
  ((truthTableResults.getD 0 Lean.Json.null).getObjValAs?
    String "source").toOption ==
    some ordinaryClause.canonicalSource

#guard
  (truthTableResults.getD 0 Lean.Json.null).getObjValD
      "clause" == ordinaryClause.toJson

#guard
  ((responsePayload truthTableDispatch).getObjValAs? Nat
    "instances").toOption == some 2

#guard
  ((responsePayload truthTableDispatch).getObjValAs? Nat
    "cost").toOption == some 4

/-
  A non-admissible clause yields a per-clause `correctable`
  entry; the admissible clause alongside it still evaluates.
-/
private def mixedEvaluationDispatch : Dispatch :=
  dispatch {} <| Request.forOperation 61 0
    "evaluate_clauses" <| Lean.Json.mkObj
      [ ("clauses", Lean.Json.arr #[
          Lean.Json.str ordinaryClause.canonicalSource,
          Lean.Json.str "not a clause"]),
        ("instances", Lean.Json.arr #[
          satisfyingInterpretation]) ]

#guard responseStatus mixedEvaluationDispatch == some "ok"

private def mixedResults : List Lean.Json :=
  ((responsePayload mixedEvaluationDispatch).getObjValAs?
    (List Lean.Json) "results").toOption.getD []

#guard mixedResults.length == 2

#guard
  ((mixedResults.getD 0 Lean.Json.null).getObjValAs?
    (List Bool) "holds").toOption == some [true]

#guard
  ((mixedResults.getD 1 Lean.Json.null).getObjVal?
    "correctable").toOption.isSome

/- A malformed instance is still a malformed instance at any
   count: the removed 4096 cost bound refused this call for
   its size, and the surviving rejection is about the
   instance document itself. -/
private def malformedInstancesDispatch : Dispatch :=
  dispatch {} <| Request.forOperation 62 0
    "evaluate_clauses" <| Lean.Json.mkObj
      [ ("clauses", Lean.Json.arr #[
          Lean.Json.str ordinaryClause.canonicalSource]),
        ("instances", Lean.Json.arr
          (List.replicate 4097 Lean.Json.null).toArray) ]

#guard responseErrorKind malformedInstancesDispatch ==
  some "instance_admission"

/- An instance naming an unknown relation is rejected. -/
private def unknownRelationInterpretation : Lean.Json :=
  Lean.Json.mkObj
    [ ("carrier_keys",
        Lean.Json.arr #[Lean.Json.str "num:1"]),
      ("relations", Lean.Json.arr #[
        relationJson "not_a_real_relation" []]) ]

private def unknownRelationDispatch : Dispatch :=
  dispatch {} <| Request.forOperation 63 0
    "evaluate_clauses" <| Lean.Json.mkObj
      [ ("clauses", Lean.Json.arr #[
          Lean.Json.str ordinaryClause.canonicalSource]),
        ("instances", Lean.Json.arr #[
          unknownRelationInterpretation]) ]

#guard
  responseErrorKind unknownRelationDispatch ==
    some "instance_admission"

/-
  Pass 7.7b: no clause, instance, or cost bound. A batch of
  129 clauses — one past the removed `maxClauseBatchItems` —
  is served, not refused.
-/
private def largeClauseBatchDispatch : Dispatch :=
  dispatch {} <| Request.forOperation 64 0
    "evaluate_clauses" <| Lean.Json.mkObj
      [ ("clauses", Lean.Json.arr
          (List.replicate 129
            (Lean.Json.str
              ordinaryClause.canonicalSource)).toArray),
        ("instances", Lean.Json.arr #[]) ]

#guard responseStatus largeClauseBatchDispatch == some "ok"

/-
  65 instances, one past the removed `maxEvaluationInstances`,
  against one clause: served, with the exact echoed cost.
-/
private def largeInstanceBatchDispatch : Dispatch :=
  dispatch {} <| Request.forOperation 65 0
    "evaluate_clauses" <| Lean.Json.mkObj
      [ ("clauses", Lean.Json.arr #[
          Lean.Json.str ordinaryClause.canonicalSource]),
        ("instances", Lean.Json.arr
          (List.replicate 65
            satisfyingInterpretation).toArray) ]

#guard responseStatus largeInstanceBatchDispatch == some "ok"

------------------------------------------------------------
-- Unbounded Snapshots
------------------------------------------------------------

/-
  Pass 7.7b: the snapshot decoder carries no row bound. The
  Core the certificate emitter and the assembly differential
  may accept is not cut at any number here; one request is
  bounded by the transport frame alone.
-/
private def wideSource (index : Nat) : String :=
  "(σ[#1 = " ++ toString index ++ "] (op_zE) ⊆ op_zE)"

/- Distinct sources admit as distinct clauses. -/
#guard
  (admitted (wideSource 3)).canonicalSource !=
    (admitted (wideSource 4)).canonicalSource

private def wideRowCount : Nat := 4200

private def wideClauses : List Clause :=
  List.mergeSort
    ((List.range wideRowCount).map
      fun index => admitted (wideSource index))
    fun left right => left.orderKey <= right.orderKey

private def wideSnapshot : Lean.Json :=
  snapshotJson
    (((List.range wideRowCount).zip wideClauses).map
      fun (index, clause) => rowJson index 0 clause)

private def wideSnapshotDispatch : Dispatch :=
  dispatch {} <| Request.forOperation 66 0
    "build_exact_obligation"
    (jobPayload wideSnapshot
      (selectorJson "initialization" (some 0)))

/- 4200 rows — far past the removed 4096-row bound — are
   decoded and served. -/
#guard responseStatus wideSnapshotDispatch == some "ok"

------------------------------------------------------------
-- Protected Precondition Rows
------------------------------------------------------------

/-
  The raw precondition is `true`; every top-level conjunct
  of the computed loop precondition mentions a body-assigned
  relation, so the extraction publishes an empty row list.
-/
private def preconditionDispatch : Dispatch :=
  dispatch {} <| Request.forOperation 35 0
    "extract_precondition_clauses" emptyPayload

#guard responseStatus preconditionDispatch == some "ok"

private def preconditionRows : List Lean.Json :=
  ((responsePayload preconditionDispatch).getObjValAs?
    (List Lean.Json) "rows").toOption.getD []

#guard preconditionRows.length == 0

#guard
  responseErrorKind
      (dispatch {} <| Request.forOperation 36 0
        "extract_precondition_clauses"
        (addExtraField emptyPayload)) ==
    some "malformed_payload"

------------------------------------------------------------
-- Protected Row Confirmation
------------------------------------------------------------

/-
  With no extracted protected row, confirmation of any bound
  job fails closed at every ordinal, level, and selector.
-/
private def confirmationPayload
    (job identity : Lean.Json)
    (ordinal : Nat) : Lean.Json :=
  Lean.Json.mkObj
    [ ("obligation_identity", identity),
      ("selector", job.getObjValD "selector"),
      ("snapshot", job.getObjValD "snapshot"),
      ("source_ordinal", Lean.Json.num ordinal) ]

#guard
  responseErrorKind
      (dispatch {} <| Request.forOperation 42 0
        "confirm_precondition_row"
        (confirmationPayload initJobPayload
          builtObligationIdentity 0)) ==
    some "precondition_confirmation"

#guard
  responseErrorKind
      (dispatch {} <| Request.forOperation 43 0
        "confirm_precondition_row"
        (confirmationPayload initJobPayload
          builtObligationIdentity 1)) ==
    some "precondition_confirmation"

private def levelOneSnapshot : Lean.Json :=
  snapshotJson [rowJson 40 1 levelOneClause]

private def levelOneJobPayload : Lean.Json :=
  jobPayload levelOneSnapshot
    (selectorJson "initialization" (some 40))

private def levelOneIdentity : Lean.Json :=
  Lean.Json.getObjValD
    (responsePayload (dispatch {} <| Request.forOperation 44 0
      "build_exact_obligation" levelOneJobPayload))
    "obligation_identity"

#guard
  responseErrorKind
      (dispatch {} <| Request.forOperation 45 0
        "confirm_precondition_row"
        (confirmationPayload levelOneJobPayload
          levelOneIdentity 0)) ==
    some "precondition_confirmation"

/- An EDB-only clause is still not an extracted row. -/
#guard
  responseErrorKind
      (dispatch {} <| Request.forOperation 46 0
        "confirm_precondition_row"
        (confirmationPayload edbInitJobPayload
          edbObligationIdentity 0)) ==
    some "precondition_confirmation"

private def terminationJobPayload : Lean.Json :=
  jobPayload oneRowSnapshot (selectorJson "termination")

private def terminationIdentity : Lean.Json :=
  Lean.Json.getObjValD
    (responsePayload (dispatch {} <| Request.forOperation 47 0
      "build_exact_obligation" terminationJobPayload))
    "obligation_identity"

#guard
  responseErrorKind
      (dispatch {} <| Request.forOperation 48 0
        "confirm_precondition_row"
        (confirmationPayload terminationJobPayload
          terminationIdentity 0)) ==
    some "precondition_confirmation"

#guard
  responseErrorKind
      (dispatch {} <| Request.forOperation 49 0
        "confirm_precondition_row"
        (addExtraField (confirmationPayload
          initJobPayload builtObligationIdentity 0))) ==
    some "obligation_identity"

------------------------------------------------------------
-- Certificate Emission And Proof Packaging
------------------------------------------------------------

private def twoRowSnapshot : Lean.Json :=
  snapshotJson
    [rowJson 11 0 ordinaryClause, rowJson 12 1 levelOneClause]

private def emitDispatch : Dispatch :=
  dispatch {} <| Request.forOperation 50 0
    "emit_certificate"
    (Lean.Json.mkObj [("snapshot", twoRowSnapshot)])

#guard responseStatus emitDispatch == some "ok"

#guard
  ((responsePayload emitDispatch).getObjValAs? Nat
    "version").toOption == some 2

#guard
  payloadString emitDispatch "kind" ==
    some "whiel_fixed_ambient_certificate_bundle"

#guard
  ((responsePayload emitDispatch).getObjValAs?
    (List Lean.Json) "jobs").toOption.map List.length ==
    some 5

#guard
  ((responsePayload emitDispatch).getObjValAs? Nat
    "core_size").toOption == some 2

#guard
  payloadString emitDispatch "certificate_theorem" ==
    some ("Whiel.Benchmark.Example0001.Certificate." ++
      "input_hoare_triple_valid")

/- A tampered row identity never reaches emission. -/
private def tamperedSnapshot : Lean.Json :=
  snapshotJson
    [snapshotRowJson 11 0 ordinaryClause.canonicalSource
      levelOneClause.identityJson]

#guard
  responseErrorKind
      (dispatch {} <| Request.forOperation 51 0
        "emit_certificate"
        (Lean.Json.mkObj [("snapshot", tamperedSnapshot)])) ==
    some "obligation_identity"

#guard
  responseErrorKind
      (dispatch {} <| Request.forOperation 52 0
        "emit_certificate"
        (addExtraField
          (Lean.Json.mkObj [("snapshot", twoRowSnapshot)]))) ==
    some "malformed_payload"

/- The empty instance meets the loop precondition. -/
private def contradictorySnapshot : Lean.Json :=
  snapshotJson
    [rowJson 21 0 (admitted "(¬((op_zT = ∅[2])))")]

#guard
  responseStatus
      (dispatch {} <| Request.forOperation 53 0
        "emit_certificate"
        (Lean.Json.mkObj
          [("snapshot", contradictorySnapshot)])) ==
    some "ok"

private def rawProof : String :=
  "-- Lean proof output generated by Vampire\n" ++
    "import VampLean\nsection vamproof\n" ++
    "theorem fullProof : True := trivial\n" ++
    "end vamproof\n"

private def packagePayload
    (extraImports : List String) : Lean.Json :=
  Lean.Json.mkObj
    [ ("extra_imports", Lean.Json.arr
        ((extraImports.map Lean.Json.str).toArray)),
      ("job_id", Lean.Json.str "test_job"),
      ("proof_namespace", Lean.Json.str "Whiel.Test.Job"),
      ("raw_output", Lean.Json.str rawProof) ]

private def packageDispatch : Dispatch :=
  dispatch {} <| Request.forOperation 54 0
    "package_proof" (packagePayload [])

#guard responseStatus packageDispatch == some "ok"

#guard
  (payloadString packageDispatch "packaged").map
      (fun packaged =>
        (packaged.splitOn "namespace Whiel.Test.Job").length) ==
    some 2

#guard
  (payloadString packageDispatch "packaged").map
      (fun packaged =>
        (packaged.splitOn "proof of `test_job`").length) ==
    some 2

#guard payloadString packageDispatch "job_id" == some "test_job"

#guard
  responseErrorKind
      (dispatch {} <| Request.forOperation 55 0
        "package_proof"
        (Lean.Json.mkObj
          [ ("extra_imports", Lean.Json.arr #[]),
            ("job_id", Lean.Json.str "test_job"),
            ("proof_namespace", Lean.Json.str "Whiel.Test.Job"),
            ("raw_output", Lean.Json.str "theorem x : True := trivial") ])) ==
    some "proof_packaging"

#guard
  responseErrorKind
      (dispatch {} <| Request.forOperation 56 0
        "package_proof"
        (Lean.Json.mkObj
          [ ("extra_imports", Lean.Json.arr #[]),
            ("proof_namespace", Lean.Json.str "Whiel.Test.Job"),
            ("raw_output", Lean.Json.str rawProof) ])) ==
    some "malformed_payload"

/-
  A proof transformation's import request reaches the
  emitter's own pinned allow-list: the projected proof's
  Whiel-owned tactic module and the kernel-checked LRAT
  rewrite's Mathlib module are both admitted, nothing else
  is, and the field itself is part of the operation
  contract.
-/
#guard
  (payloadString
      (dispatch {} <| Request.forOperation 57 0 "package_proof"
        (packagePayload ["Whiel.Vampire.ClauseProjection"]))
      "packaged").map
    (fun packaged =>
      (packaged.splitOn
        "import VampLean\nimport Whiel.Vampire.ClauseProjection\n").length) ==
    some 2

#guard
  (payloadString
      (dispatch {} <| Request.forOperation 58 0 "package_proof"
        (packagePayload ["Mathlib.Tactic.Sat.FromLRAT"]))
      "packaged").map
    (fun packaged =>
      (packaged.splitOn
        "import VampLean\nimport Mathlib.Tactic.Sat.FromLRAT\n").length) ==
    some 2

#guard
  responseErrorKind
      (dispatch {} <| Request.forOperation 60 0 "package_proof"
        (packagePayload ["Mathlib"])) ==
    some "proof_packaging"

#guard
  responseErrorKind
      (dispatch {} <| Request.forOperation 59 0 "package_proof"
        (Lean.Json.mkObj
          [ ("job_id", Lean.Json.str "test_job"),
            ("proof_namespace", Lean.Json.str "Whiel.Test.Job"),
            ("raw_output", Lean.Json.str rawProof) ])) ==
    some "malformed_payload"

------------------------------------------------------------
-- Agent Counterexample Operations
------------------------------------------------------------

/-
  The refutable registered task. It is a full Framework-II
  entry like the production one; only its postcondition, and
  so its counterexample verdicts, differ.
-/
private def refutableEntry :=
  Runtime.FixedAmbientRegistry.Example0013.entry

/- One request bound to a chosen registry entry. -/
private def requestFor
    (bound : Runtime.FixedAmbientRegistry.Entry)
    (requestId nameEnvRevision : Nat)
    (operation : String)
    (payload : Lean.Json) : Request :=
  letI : Runtime.FixedAmbientWorker.Bound := ⟨bound⟩
  Request.forOperation requestId nameEnvRevision operation
    payload

private def cexEdge
    (source target : Nat) : Lean.Json :=
  Lean.Json.arr
    #[ Lean.Json.str ("num:" ++ toString source),
       Lean.Json.str ("num:" ++ toString target) ]

private def cexRelation
    (name : String)
    (rows : List Lean.Json) : Lean.Json :=
  Lean.Json.mkObj
    [ ("name", Lean.Json.str name),
      ("rows", Lean.Json.arr rows.toArray) ]

private def cexInstance
    (relations : List Lean.Json) : Lean.Json :=
  Lean.Json.mkObj
    [("relations", Lean.Json.arr relations.toArray)]

/- The refutable fixture's two-edge witness. -/
private def cexWitness : Lean.Json :=
  cexInstance
    [ cexRelation "p::E" [cexEdge 0 1, cexEdge 1 2],
      cexRelation "p::S" [],
      cexRelation "p::T" [] ]

/- The request carries the instance and nothing else: the
   counterexample path has no fuel bound. -/
private def validatePayload
    (submitted : Lean.Json) : Lean.Json :=
  Lean.Json.mkObj [("input", submitted)]

private def validateDispatch
    (bound : Runtime.FixedAmbientRegistry.Entry)
    (requestId : Nat)
    (submitted : Lean.Json) : Dispatch :=
  dispatch {} <| requestFor bound requestId 0
    "validate_counterexample"
    (validatePayload submitted)

private def payloadCode
    (result : Dispatch) : Option String :=
  payloadString result "code"

private def witnessDispatch : Dispatch :=
  validateDispatch refutableEntry 60 cexWitness

/- A genuine counterexample is accepted. -/
#guard responseStatus witnessDispatch == some "ok"

#guard payloadString witnessDispatch "status" ==
  some "counterexample"

/- Its frozen fuel is the fuel the run actually consumes. -/
#guard
  ((responsePayload witnessDispatch).getObjValAs? Nat
    "fuel_consumed").toOption == some 6

/- Its identity is the digest of the canonical instance. -/
#guard payloadString witnessDispatch "instance_identity" ==
  some
    ("7fb4ca7b93ec6f10c0e9d6ca8725808" ++
      "6058ae9cb84c7349177125d50eb9ee64f")

/- The canonical instance is re-emitted by Lean. -/
#guard
  ((responsePayload witnessDispatch).getObjValD
      "instance").compress ==
    ("{\"relations\":[{\"name\":\"p::E\",\"rows\":" ++
      "[[\"num:0\",\"num:1\"],[\"num:1\",\"num:2\"]]}," ++
      "{\"name\":\"p::S\",\"rows\":[]}," ++
      "{\"name\":\"p::T\",\"rows\":[]}]}")

/- The same instance under the presentation's lift prefix. -/
#guard
  payloadString
      (validateDispatch refutableEntry 61
        (cexInstance
          [ cexRelation "o:p::E" [cexEdge 0 1, cexEdge 1 2],
            cexRelation "o:p::S" [],
            cexRelation "o:p::T" [] ]))
      "instance_identity" ==
    payloadString witnessDispatch "instance_identity"

/- A relation the input schema does not name is rejected. -/
#guard
  payloadCode
      (validateDispatch refutableEntry 62
        (cexInstance
          [ cexRelation "p::E" [], cexRelation "p::S" [],
            cexRelation "p::T" [], cexRelation "p::Q" [] ])) ==
    some "unknown_relation"

/- A malformed cell is rejected. -/
#guard
  payloadCode
      (validateDispatch refutableEntry 63
        (cexInstance
          [ cexRelation "p::E"
              [Lean.Json.arr
                #[Lean.Json.num 0, Lean.Json.num 1]],
            cexRelation "p::S" [], cexRelation "p::T" [] ])) ==
    some "malformed"

/-
  An instance far beyond every removed cap is decoded and
  run, not refused for its size: 300 rows in one relation and
  302 across the instance, past the removed 256-row and
  1024-row caps. The rows `(2i+3, 2i+4)` for `i < 300` cover
  every value from 3 to 602, so with `E`'s `0`, `1` and `2`
  the instance carries 603 distinct carrier values, far past
  the removed 64-value cap. The extra rows sit in `S`, which
  the input command overwrites on its first statement, so
  this measures the decoder and the size, not the closure the
  loop computes; the two-edge witness in `E` still refutes.
-/
#guard
  responseStatus
      (validateDispatch refutableEntry 64
        (cexInstance
          [ cexRelation "p::E" [cexEdge 0 1, cexEdge 1 2],
            cexRelation "p::S"
              ((List.range 300).map fun index =>
                cexEdge (2 * index + 3) (2 * index + 4)),
            cexRelation "p::T" [] ])) ==
    some "ok"

/- An instance whose halted run meets the postcondition is
   not a counterexample. -/
#guard
  payloadCode
      (validateDispatch refutableEntry 66
        (cexInstance
          [ cexRelation "p::E" [cexEdge 0 0],
            cexRelation "p::S" [], cexRelation "p::T" [] ])) ==
    some "postcondition_holds"

/- The production task's postcondition is valid, so the same
   witness is not a counterexample for it. -/
#guard
  payloadCode (validateDispatch entry 67 cexWitness) ==
    some "postcondition_holds"

/- The payload contract is exact: the instance and nothing
   else. A request that still carries the removed
   `fuel_bound` field is refused as malformed. -/
#guard
  responseErrorKind
      (dispatch {} <| requestFor refutableEntry 69 0
        "validate_counterexample"
        (Lean.Json.mkObj
          [ ("fuel_bound", Lean.Json.num 200),
            ("input", cexWitness) ])) ==
    some "malformed_payload"

/- An unregistered task cannot reach the operation. -/
#guard
  responseErrorKind
      (dispatch {}
        { requestFor refutableEntry 70 0
            "validate_counterexample"
            (validatePayload cexWitness) with
          taskCanonicalId := "Not-Registered" }) ==
    some "invalid_envelope"

private def invalidBundleDispatch : Dispatch :=
  dispatch {} <| requestFor refutableEntry 71 0
    "emit_invalid_certificate"
    (Lean.Json.mkObj
      [ ("fuel",
          (responsePayload witnessDispatch).getObjValD
            "fuel_consumed"),
        ("instance",
          (responsePayload witnessDispatch).getObjValD
            "instance"),
        ("instance_identity",
          (responsePayload witnessDispatch).getObjValD
            "instance_identity") ])

#guard responseStatus invalidBundleDispatch == some "ok"

#guard
  ((responsePayload invalidBundleDispatch).getObjValAs? Nat
    "version").toOption == some 2

#guard payloadString invalidBundleDispatch "certificate_module" ==
  some "Benchmark.Example0013.Certificate.Invalid"

#guard payloadString invalidBundleDispatch "certificate_theorem" ==
  some
    ("Whiel.Benchmark.Example0013.Certificate." ++
      "input_hoare_triple_invalid")

/- The bundle names no solver job. -/
#guard
  ((responsePayload invalidBundleDispatch).getObjValD "jobs") ==
    Lean.Json.arr #[]

private def invalidArtifacts : List Lean.Json :=
  match (responsePayload invalidBundleDispatch).getObjValD
      "artifacts" with
  | .arr artifacts => artifacts.toList
  | _ => []

#guard invalidArtifacts.length == 1

#guard
  (invalidArtifacts.head?.map fun artifact =>
    (artifact.getObjValAs? String
      "relative_path").toOption) ==
    some (some
      "Benchmark/Example0013/Certificate/Invalid.lean")

/- The emitted source is byte-stable. -/
private def invalidSourceText : String :=
  match invalidArtifacts.head? with
  | some artifact =>
      (artifact.getObjValAs? String "contents").toOption.getD ""
  | none => ""

#guard invalidSourceText.length == 1232

#guard invalidSourceText.startsWith
  ("-- Generated by the Lean-owned fixed-ambient " ++
    "certificate-emitter-v2.\n-- Do not edit by hand.\n")

#guard
  (invalidSourceText.splitOn
    "def counterExampleFuel : Nat := 6").length == 2

/- The frozen instance is published only in notation. -/
#guard
  (invalidSourceText.splitOn
    ("def counterExampleInput : Instance Data " ++
      "inputSchema :=\n" ++
      "  programInst![inputSchema |\n" ++
      "    E := [[0, 1], [1, 2]];\n" ++
      "    S := [];\n" ++
      "    T := [] ]")).length == 2

#guard
  (invalidSourceText.splitOn
    "counterExampleRows").length == 1

#guard
  (invalidSourceText.splitOn
    "counterExampleInput_eq_keyedRows").length == 1

#guard
  (invalidSourceText.splitOn
    "ProgramInstance.ofKeyedRows").length == 1

#guard
  (invalidSourceText.splitOn "-- Author:").length == 1

#guard
  (invalidSourceText.splitOn "-- Authors:").length == 1

/- The certificate imports the notation it renders with. -/
#guard
  (invalidSourceText.splitOn
    "import Whiel.Eval.CounterExample.InstanceNotation").length == 2

#guard
  (invalidSourceText.splitOn
    ("theorem input_hoare_triple_invalid :\n" ++
      "    ¬ Whiel.HoareValid inputPre inputCmd inputPost :=\n" ++
      "  Whiel.Hoare.CounterExample.certifyKernel\n" ++
      "    counterExampleFuel counterExampleInput")).length == 2

#guard
  (invalidSourceText.splitOn
    "#print axioms input_hoare_triple_invalid").length == 2

/- The axiom guard is emitted wrapped to the width. -/
#guard
  (invalidSourceText.splitOn
    ("/--\n  info:\n" ++
      "  'Whiel.Benchmark.Example0013.Certificate." ++
      "input_hoare_triple_invalid'\n" ++
      "  depends on axioms: " ++
      "[propext, Classical.choice, Quot.sound]\n-/\n" ++
      "#guard_msgs (whitespace := lax) in\n")).length == 2

/- No emitted certificate text names "Framework II". -/
#guard
  (invalidSourceText.splitOn "Framework II").length == 1

/-
  SHA-256 of the emitted source. The checked-in
  `Benchmark/Example0013/Certificate/Invalid.lean` is the
  same bytes after replacing only its legacy banner with
  the v2 banner. It carries the same wrapped axiom guard
  and notation instance. Two canaries
  in `whiel_runner/tests/framework2_fixed_ambient.rs`
  compare the live output to that exact banner-adjusted
  source; the emitted digest was regenerated here:
  `live_refutable_task_ends_invalid_and_builds_its_kernel_certificate`
  and
  `live_invalid_canary_publishes_its_record_and_rebuilds_the_certificate_from_it`.
-/
#guard
  (invalidArtifacts.head?.map fun artifact =>
      (artifact.getObjValAs? String
        "contents_sha256").toOption) ==
    some (some
      ("443aa52d756a182702a9827ad50fbf38" ++
        "cfff6b887fb9c7d49aba50d8ba99c579"))

/- A frozen record whose identity does not match is refused. -/
#guard
  responseErrorKind
      (dispatch {} <| requestFor refutableEntry 72 0
        "emit_invalid_certificate"
        (Lean.Json.mkObj
          [ ("fuel", Lean.Json.num 6),
            ("instance",
              (responsePayload witnessDispatch).getObjValD
                "instance"),
            ("instance_identity", Lean.Json.str
              ("0000000000000000000000000000000" ++
                "00000000000000000000000000000000")) ])) ==
    some "counterexample_rejected"

/- A frozen fuel that no longer certifies is refused. -/
#guard
  responseErrorKind
      (dispatch {} <| requestFor refutableEntry 73 0
        "emit_invalid_certificate"
        (Lean.Json.mkObj
          [ ("fuel", Lean.Json.num 5),
            ("instance",
              (responsePayload witnessDispatch).getObjValD
                "instance"),
            ("instance_identity",
              (responsePayload witnessDispatch).getObjValD
                "instance_identity") ])) ==
    some "counterexample_rejected"

------------------------------------------------------------
-- Two Registered Bindings
------------------------------------------------------------

/-
  The refutable task is served by the same worker under its
  own envelope: `describe` answers with its identity, its own
  scope, and its own relation table.
-/
private def refutableDescribe : Dispatch :=
  dispatch {} <| requestFor refutableEntry 74 0
    "describe" emptyPayload

#guard responseStatus refutableDescribe == some "ok"

#guard
  (((responsePayload refutableDescribe).getObjValD
      "task_identity").getObjValAs? String
    "canonical_id").toOption == some "Example0013"

#guard
  ((responsePayload refutableDescribe).getObjValD
    "scope_identity") == refutableEntry.scopeIdentity

/- The production `describe` is unchanged by the second
  registration. -/
#guard
  responsePayload describeDispatch == bootstrapForDefault

#guard
  (((responsePayload describeDispatch).getObjValD
      "task_identity").getObjValAs? String
    "canonical_id").toOption == some "Example0001"

/- No operation crosses from one binding to the other: an
  envelope that mixes the two identities is refused. -/
#guard
  responseErrorKind
      (dispatch {}
        { requestFor refutableEntry 75 0 "ping" emptyPayload with
          scopeIdentity := entry.scopeIdentity }) ==
    some "invalid_envelope"

#guard
  responseErrorKind
      (dispatch {}
        { Request.forOperation 76 0 "ping" emptyPayload with
          taskCanonicalId := "Example0013" }) ==
    some "invalid_envelope"

/- The name environment is shared: a binding still sees the
  revision the other advanced. -/
#guard
  responseErrorKind
      (dispatch fullNameEnvState <|
        requestFor refutableEntry 77 0 "ping" emptyPayload) ==
    some "invalid_envelope"

#guard
  responseStatus
      (dispatch fullNameEnvState <|
        requestFor refutableEntry 78 1 "ping" emptyPayload) ==
    some "ok"

/- The refutable task carries the ordinary Framework-II
  scope kind, not a raw-input-only one. -/
#guard
  (refutableEntry.scopeIdentity.getObjValAs? String
    "kind").toOption ==
    some "whiel_framework_ii_fixed_ambient_task"

/- The refutable task has no Core and needs none: its `2N+1`
  jobs are built from an empty snapshot. -/
#guard
  responseStatus
      (dispatch {} <| requestFor refutableEntry 79 0
        "build_exact_obligation"
        (Lean.Json.mkObj
          [ ("selector", Lean.Json.mkObj
              [("kind", Lean.Json.str "termination")]),
            ("snapshot", Lean.Json.mkObj
              [("rows", Lean.Json.arr #[])]) ])) ==
    some "ok"

------------------------------------------------------------
-- Closed Operation Set
------------------------------------------------------------

#guard
  responseErrorKind
      (dispatch {} <| Request.forOperation 22 0
        "legacy_operation" emptyPayload) ==
    some "unknown_operation"

private def shutdownDispatch : Dispatch :=
  dispatch {} <| Request.forOperation 23 0
    "shutdown" emptyPayload

#guard responseStatus shutdownDispatch == some "ok"

#guard shutdownDispatch.stop

/- Every current registration serves its own typed envelope. -/
#guard Runtime.FixedAmbientRegistry.entries.all fun bound =>
  let result := dispatch {} <| requestFor bound 100 0
    "describe" emptyPayload
  responseStatus result == some "ok" &&
    responsePayload result ==
      (bootstrapFor? bound.identity.canonicalId).getD
        Lean.Json.null

/- The two controls use the same typed worker operations. -/
#guard [Runtime.FixedAmbientRegistry.Example0001.entry,
    Runtime.FixedAmbientRegistry.Example0106.entry].all
  fun bound =>
    let result := dispatch {} <| requestFor bound 101 0
      "extract_precondition_clauses" emptyPayload
    responseStatus result == some "ok"

end FixedAmbientWorkerTest
end Tests
end Synthesis
end Whiel
