-- Author: Jesse Comer
import Whiel.Synthesis.Runtime.EncodingProtocol
import Whiel.Synthesis.Runtime.FixedAmbientRegistry

/-
  Persistent worker for the Step-7 fixed-ambient
  Framework-II registry.

  The worker has its own closed protocol. Every request names
  one registered canonical ID and is bound to that entry's
  checked task and scope: `dispatch` resolves the entry
  through `FixedAmbientRegistry.lookup?` and every operation,
  the two counterexample operations included, runs under that
  one binding. Snapshots carry canonical clause source and
  complete Lean identity; Lean re-admits and checks every row
  before constructing an exact obligation. The only
  persistent state is the append-only TPTP name environment
  and its revision, which is shared by every binding.

  Ordinary search-time requests are assembled by the
  controller from opaque pieces: `prepare_task_pieces`,
  `prepare_clause_pieces`, and `prepare_support_block` render
  the immutable component formulas and the support block once
  each, and the controller splices those rendered bodies into
  a verification condition. `prepare_exact_obligation` still
  assembles a whole obligation from a snapshot and selector,
  and remains the differential reference for that assembly.
-/

------------------------------------------------------------
-- Protocol Envelope
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientWorker

open Concrete

/-
  The one registry entry a request is bound to. `dispatch`
  resolves it from the request's canonical ID and every
  operation runs under that binding, so nothing in this
  module names a particular fixture.
-/
class Bound where
  boundEntry : FixedAmbientRegistry.Entry

/- The bound registry entry. -/
abbrev entry [b : Bound] : FixedAmbientRegistry.Entry :=
  b.boundEntry

variable [Bound]

/- The computed prophecy schema of the bound task. -/
private abbrev prophecySchema : UnnamedSchema WhielNames :=
  entry.prophecySchema

private abbrev PreparedComponent :=
  FrameworkII.FixedAmbient.PreparedComponent prophecySchema

private abbrev EmptyCheckResult :=
  FrameworkII.FixedAmbient.EmptyCheckResult prophecySchema

private abbrev PreconditionRow :=
  FrameworkII.FixedAmbient.PreconditionRow prophecySchema

/-
  Independent V8 protocol version. Bumped to 9 when the
  `validate_counterexample` payload dropped `fuel_bound`
  (the counterexample path has no fuel bound, so a request
  that still carries one is refused as malformed and a stale
  host fails closed), and to 10 when the `admit_clauses`
  payload gained `clause_text_bytes`, the optional host limit
  that drives the surface parser's limits, and to 11 when
  the empty-instance check became constant-blind: its reply
  names `QFEntailment.adomEmptyCounterexample?` as the
  decision, and a host expecting the older decision fails
  closed. The operation set is unchanged at twenty
  operations.
-/
def formatVersion : Nat := 11

/- Exact fields required on a JSON object. -/
private def requireObjectFields
    (json : Lean.Json)
    (expected : List String) : Except String Unit := do
  let fields <- match json with
    | .obj fields => .ok fields
    | _ => .error "payload must be a JSON object"
  if fields.keys != expected then
    throw "object fields differ from the operation contract"

/- One strictly task-bound request. -/
structure Request where
  formatVersion : Nat
  semanticVersion : Nat
  encodingVersion : Nat
  taskCanonicalId : String
  taskModule : String
  taskNamespace : String
  taskSourceSha256 : String
  scopeIdentity : Lean.Json
  requestId : Nat
  nameEnvRevision : Nat
  operation : String
  payload : Lean.Json

namespace Request

/- Parse the exact V5 request envelope. -/
def fromJson?
    (json : Lean.Json) : Except String Request := do
  requireObjectFields json
    [ "encoding_version",
      "format_version",
      "name_env_revision",
      "operation",
      "payload",
      "request_id",
      "scope_identity",
      "semantic_version",
      "task_canonical_id",
      "task_module",
      "task_namespace",
      "task_source_sha256" ]
  return {
    formatVersion := ←
      json.getObjValAs? Nat "format_version"
    semanticVersion := ←
      json.getObjValAs? Nat "semantic_version"
    encodingVersion := ←
      json.getObjValAs? Nat "encoding_version"
    taskCanonicalId := ←
      json.getObjValAs? String "task_canonical_id"
    taskModule := ←
      json.getObjValAs? String "task_module"
    taskNamespace := ←
      json.getObjValAs? String "task_namespace"
    taskSourceSha256 := ←
      json.getObjValAs? String "task_source_sha256"
    scopeIdentity := json.getObjValD "scope_identity"
    requestId := ← json.getObjValAs? Nat "request_id"
    nameEnvRevision := ←
      json.getObjValAs? Nat "name_env_revision"
    operation := ← json.getObjValAs? String "operation"
    payload := json.getObjValD "payload" }

/- Serialize one request in the strict envelope. -/
def toJson (request : Request) : Lean.Json :=
  Lean.Json.mkObj
    [ ("format_version",
        Lean.Json.num request.formatVersion),
      ("semantic_version",
        Lean.Json.num request.semanticVersion),
      ("encoding_version",
        Lean.Json.num request.encodingVersion),
      ("task_canonical_id",
        Lean.Json.str request.taskCanonicalId),
      ("task_module", Lean.Json.str request.taskModule),
      ("task_namespace",
        Lean.Json.str request.taskNamespace),
      ("task_source_sha256",
        Lean.Json.str request.taskSourceSha256),
      ("scope_identity", request.scopeIdentity),
      ("request_id", Lean.Json.num request.requestId),
      ("name_env_revision",
        Lean.Json.num request.nameEnvRevision),
      ("operation", Lean.Json.str request.operation),
      ("payload", request.payload) ]

/- Construct one correctly bound request. -/
def forOperation
    (requestId nameEnvRevision : Nat)
    (operation : String)
    (payload : Lean.Json) : Request where
  formatVersion := FixedAmbientWorker.formatVersion
  semanticVersion := entry.identity.semanticVersion
  encodingVersion := entry.identity.encodingVersion
  taskCanonicalId := entry.identity.canonicalId
  taskModule := entry.identity.moduleName
  taskNamespace := entry.identity.namespaceName
  taskSourceSha256 := entry.identity.sourceSha256
  scopeIdentity := entry.scopeIdentity
  requestId := requestId
  nameEnvRevision := nameEnvRevision
  operation := operation
  payload := payload

end Request

/- The complete process state. -/
structure State where
  nameEnvRevision : Nat := 0
  nameEnv : Vampire.TPTP.NameEnv WhielNames Data :=
    { relNames := [], funNames := [] }

/- One pure dispatch result, also used by focused tests. -/
structure Dispatch where
  state : State
  response : Lean.Json
  stop : Bool := Bool.false

private structure Failure where
  kind : String
  message : String

private def identityJson
    (identity : TaskIdentity) : Lean.Json :=
  Lean.Json.mkObj
    [ ("canonical_id",
        Lean.Json.str identity.canonicalId),
      ("module",
        Lean.Json.str identity.moduleName),
      ("namespace",
        Lean.Json.str identity.namespaceName),
      ("source_sha256",
        Lean.Json.str identity.sourceSha256) ]

private def taskIdentityJson : Lean.Json :=
  identityJson entry.identity

private def responseJson
    (semanticVersion encodingVersion : Nat)
    (taskIdentity scopeIdentity : Lean.Json)
    (requestId requestRevision currentRevision : Nat)
    (operation status : String)
    (payload : Lean.Json)
    (error? : Option Failure := none) : Lean.Json :=
  let errorFields := match error? with
    | none => []
    | some failure =>
        [("error", Lean.Json.mkObj
          [ ("kind", Lean.Json.str failure.kind),
            ("message", Lean.Json.str failure.message) ])]
  Lean.Json.mkObj <|
    [ ("format_version", Lean.Json.num formatVersion),
      ("semantic_version",
        Lean.Json.num semanticVersion),
      ("encoding_version",
        Lean.Json.num encodingVersion),
      ("task_identity", taskIdentity),
      ("scope_identity", scopeIdentity),
      ("request_id", Lean.Json.num requestId),
      ("request_name_env_revision",
        Lean.Json.num requestRevision),
      ("name_env_revision",
        Lean.Json.num currentRevision),
      ("operation", Lean.Json.str operation),
      ("status", Lean.Json.str status),
      ("payload", payload) ] ++ errorFields

private def boundResponseJson
    (identity : TaskIdentity)
    (scopeIdentity : Lean.Json)
    (requestId requestRevision currentRevision : Nat)
    (operation status : String)
    (payload : Lean.Json)
    (error? : Option Failure := none) : Lean.Json :=
  responseJson identity.semanticVersion
    identity.encodingVersion (identityJson identity)
    scopeIdentity requestId requestRevision currentRevision
    operation status payload error?

/-
  Error response of a frame that is bound to no registry
  entry. Both identities are null: the worker resolved no
  entry, so it has none of its own to echo, and echoing some
  other task's identity would misreport the frame as that
  task's answer. Only an error frame is ever shaped this
  way; every `ok` frame carries the identity it ran under.
-/
private def unboundErrorResponse
    (semanticVersion encodingVersion : Nat)
    (requestId requestRevision currentRevision : Nat)
    (operation : String)
    (failure : Failure) : Lean.Json :=
  responseJson semanticVersion encodingVersion
    Lean.Json.null Lean.Json.null requestId requestRevision
    currentRevision operation "error" Lean.Json.null
    (some failure)

/-
  Protocol versions an unbound response reports when it has
  no request to echo them from, because the frame did not
  parse. They are the versions of this worker's own
  protocol, not any task's.
-/
private def unboundSemanticVersion : Nat := 1
private def unboundEncodingVersion : Nat := 1

private def okResponse
    (request : Request)
    (state : State)
    (payload : Lean.Json) : Lean.Json :=
  boundResponseJson entry.identity entry.scopeIdentity
    request.requestId
    request.nameEnvRevision state.nameEnvRevision
    request.operation "ok" payload

private def errorResponse
    (request : Request)
    (state : State)
    (failure : Failure) : Lean.Json :=
  boundResponseJson entry.identity entry.scopeIdentity
    request.requestId
    request.nameEnvRevision state.nameEnvRevision
    request.operation "error" Lean.Json.null (some failure)

private def malformedResponse
    (state : State)
    (message : String) : Lean.Json :=
  unboundErrorResponse unboundSemanticVersion
    unboundEncodingVersion 0 state.nameEnvRevision
    state.nameEnvRevision ""
    { kind := "malformed_request", message }

private def validateEnvelopeAgainst
    (state : State)
    (request : Request)
    (identity : TaskIdentity)
    (scopeIdentity : Lean.Json) : Except String Unit := do
  if request.formatVersion != formatVersion then
    throw "unsupported fixed-ambient worker version"
  if request.semanticVersion != identity.semanticVersion then
    throw "request semantic version does not match the task"
  if request.encodingVersion != identity.encodingVersion then
    throw "request encoding version does not match the task"
  if request.taskCanonicalId != identity.canonicalId then
    throw "request canonical ID does not match the task"
  if request.taskModule != identity.moduleName then
    throw "request module does not match the task"
  if request.taskNamespace != identity.namespaceName then
    throw "request namespace does not match the task"
  if request.taskSourceSha256 != identity.sourceSha256 then
    throw "request source digest does not match the task"
  if request.scopeIdentity != scopeIdentity then
    throw "request scope identity does not match the task"
  if request.nameEnvRevision != state.nameEnvRevision then
    throw "request name-environment revision is stale"

private def validateRequest
    (state : State)
    (request : Request) : Except String Unit :=
  validateEnvelopeAgainst state request entry.identity
    entry.scopeIdentity

end FixedAmbientWorker
end Runtime
end Synthesis
end Whiel

------------------------------------------------------------
-- Wire Data
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientWorker

open Concrete

variable [Bound]

private def bindingJson
    (binding : String × String) : Lean.Json :=
  Lean.Json.mkObj
    [ ("key", Lean.Json.str binding.1),
      ("name", Lean.Json.str binding.2) ]

private def bindingListJson
    (bindings : List (String × String)) : Lean.Json :=
  Lean.Json.arr (bindings.map bindingJson).toArray

private def bodyDataJson
    (body : PreparedBodyData) : Lean.Json :=
  let sourceId := body.sourceId
  Lean.Json.mkObj
    [ ("source_id", Lean.Json.str sourceId),
      ("source_kind", Lean.Json.str body.sourceKind),
      ("exact_constant_keys", Lean.Json.arr
        (body.exactConstantKeys.map Lean.Json.str).toArray),
      ("body", Lean.Json.str body.body),
      ("referenced_relations",
        bindingListJson body.referencedRelations),
      ("referenced_constants",
        bindingListJson body.referencedConstants) ]

private def supportDataJson
    (support : PreparedSupportData) : Lean.Json :=
  Lean.Json.mkObj
    [ ("constant_keys", Lean.Json.arr
        (support.constantKeys.map Lean.Json.str).toArray),
      ("adom_body", Lean.Json.str support.adomBody),
      ("distinct_bodies", Lean.Json.arr
        (support.distinctBodies.map Lean.Json.str).toArray),
      ("referenced_relations",
        bindingListJson support.referencedRelations),
      ("referenced_constants",
        bindingListJson support.referencedConstants) ]

private def componentJson
    (metadata :
      FrameworkII.FixedAmbient.Component.Metadata
        prophecySchema) :
    Lean.Json :=
  metadata.toJson entry.scopeIdentity

private def describePayload : Lean.Json :=
  Lean.Json.mkObj
    [ ("task_identity", taskIdentityJson),
      ("manifest", entry.manifest.toJson),
      ("scope_identity", entry.scopeIdentity),
      ("relation_table", entry.relationTableJson),
      ("prophecy_bindings", entry.prophecyBindingsJson),
      ("task_components", Lean.Json.arr
        (entry.taskComponents.map componentJson).toArray) ]

/-
  Bootstrap descriptor available before the first request.
-/
def bootstrap : Lean.Json :=
  describePayload

private structure NameBinding where
  key : String
  name : String

namespace NameBinding

private def fromJson?
    (json : Lean.Json) : Except String NameBinding := do
  requireObjectFields json ["key", "name"]
  return {
    key := ← json.getObjValAs? String "key"
    name := ← json.getObjValAs? String "name" }

private def toJson (binding : NameBinding) : Lean.Json :=
  Lean.Json.mkObj
    [ ("key", Lean.Json.str binding.key),
      ("name", Lean.Json.str binding.name) ]

end NameBinding

private def parseBindings
    (payload : Lean.Json)
    (field : String) :
    Except String (List NameBinding) := do
  let values <-
    payload.getObjValAs? (List Lean.Json) field
  values.mapM NameBinding.fromJson?

private def repeatsBy
    (project : NameBinding -> String) :
    List NameBinding -> Bool
| [] => Bool.false
| binding :: bindings =>
    (bindings.any fun other =>
      project other == project binding) ||
        repeatsBy project bindings

private def resolveRelation
    (key : String) : Option WhielNames :=
  (entry.relationTable.find? fun row =>
    row.key == key).map fun row => row.relation.1

/-
  Resolve one offered binding against the symbol it names.

  Rust computes a name locally so that every worker replays
  the same environment, but the name is a total function of
  the key and Lean owns that function. A binding is therefore
  admitted only when its name is this carrier's own solver
  name for the resolved symbol; a disagreeing name is refused
  rather than adopted.
-/
private def resolveBindings
    {X : Type}
    [SolverKey X]
    [Vampire.SolverName X]
    (kind : String)
    (resolve : String -> Option X)
    (bindings : List NameBinding) :
    Except String (List (X × String)) := do
  bindings.mapM fun binding => do
    if !Vampire.legalTptpName binding.name then
      throw s!"illegal TPTP name for {kind} key"
    let some value := resolve binding.key
      | throw s!"unknown {kind} key {binding.key}"
    if SolverKey.key value != binding.key then
      throw s!"noncanonical {kind} key {binding.key}"
    if Vampire.solverName value != binding.name then
      throw s!"{kind} key {binding.key} is bound to \
        {binding.name} rather than its solver name \
        {Vampire.solverName value}"
    return (value, binding.name)

private def extendNameEnv
    (state : State)
    (payload : Lean.Json) :
    Except Failure (State × Lean.Json) := do
  match requireObjectFields payload
      ["constants", "next_revision", "relations"] with
  | .error message =>
      throw { kind := "malformed_payload", message }
  | .ok () => pure ()
  let nextRevision <- match
      payload.getObjValAs? Nat "next_revision" with
    | .ok value => .ok value
    | .error message =>
        .error { kind := "malformed_payload", message }
  if nextRevision != state.nameEnvRevision + 1 then
    throw {
      kind := "name_environment"
      message :=
        "name-environment revisions must be contiguous" }
  let relationBindings <- match
      parseBindings payload "relations" with
    | .ok value => .ok value
    | .error message =>
        .error { kind := "malformed_payload", message }
  let constantBindings <- match
      parseBindings payload "constants" with
    | .ok value => .ok value
    | .error message =>
        .error { kind := "malformed_payload", message }
  if repeatsBy NameBinding.key relationBindings then
    throw {
      kind := "name_environment"
      message := "relation bindings repeat a key" }
  if repeatsBy NameBinding.key constantBindings then
    throw {
      kind := "name_environment"
      message := "constant bindings repeat a key" }
  if repeatsBy NameBinding.name
      (relationBindings ++ constantBindings) then
    throw {
      kind := "name_environment"
      message := "name bindings repeat a TPTP name" }
  let relations <- match resolveBindings "relation"
      resolveRelation relationBindings with
    | .ok value => .ok value
    | .error message =>
        .error { kind := "name_environment", message }
  let constants <- match resolveBindings "constant"
      SolverKey.dataOfKey? constantBindings with
    | .ok value => .ok value
    | .error message =>
        .error { kind := "name_environment", message }
  let some nameEnv :=
      state.nameEnv.appendBindings? relations constants
    | throw {
        kind := "name_environment"
        message := "name bindings conflict" }
  let nextState := {
    state with
    nameEnvRevision := nextRevision
    nameEnv := nameEnv }
  let response := Lean.Json.mkObj
    [ ("relations", Lean.Json.arr
        (relationBindings.map NameBinding.toJson).toArray),
      ("constants", Lean.Json.arr
        (constantBindings.map NameBinding.toJson).toArray) ]
  return (nextState, response)

end FixedAmbientWorker
end Runtime
end Synthesis
end Whiel

------------------------------------------------------------
-- Exact Snapshot Reconstruction
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientWorker

open Concrete

variable [Bound]

private abbrev Clause :=
  FrameworkII.FixedAmbient.Clause prophecySchema

private abbrev CatalogRow :=
  FrameworkII.FixedAmbient.CatalogRow prophecySchema

private abbrev Snapshot :=
  FrameworkII.FixedAmbient.Snapshot prophecySchema

private abbrev BuiltObligation :=
  FrameworkII.FixedAmbient.BuiltObligation prophecySchema

private def admissionFailureMessage :
    FrameworkII.FixedAmbient.ClauseAdmissionFailure ->
      String
| .correctable diagnostic => diagnostic.message
| .infrastructure message => message

private def admitCanonicalClause
    (source : String)
    (identity : Lean.Json) : Except String Clause := do
  -- Lean's own canonical source, re-parsed under no host
  -- bound: `clause_text_bytes` governs submitted text only.
  let clause <- match entry.admitClause source {} with
    | .ok clause => .ok clause
    | .error failure =>
        .error (admissionFailureMessage failure)
  if clause.canonicalSource != source then
    throw "snapshot clause source is not canonical"
  if clause.identityJson != identity then
    throw "snapshot clause source and identity disagree"
  return clause

private def decodeSnapshotRow
    (json : Lean.Json) : Except String CatalogRow := do
  requireObjectFields json
    ["canonical_source", "clause_id", "identity", "level"]
  let clauseId <- json.getObjValAs? Nat "clause_id"
  let level <- json.getObjValAs? Nat "level"
  let source <-
    json.getObjValAs? String "canonical_source"
  let identity := json.getObjValD "identity"
  let clause <- admitCanonicalClause source identity
  if level < clause.minimumLevel then
    throw "snapshot row is below its Lean minimum level"
  return { clauseId, level, clause }

private def decodeSnapshotRows :
    List Nat -> List Lean.Json -> List CatalogRow ->
      List Lean.Json -> Except String (List CatalogRow)
| _, _, rows, [] => .ok rows.reverse
| seenIds, seenIdentities, rows, json :: rest => do
    let row <- decodeSnapshotRow json
    if row.clauseId ∈ seenIds then
      throw "snapshot repeats a clause ID"
    if seenIdentities.any fun identity =>
        identity == row.clause.identityJson then
      throw "snapshot repeats a clause identity"
    decodeSnapshotRows
      (row.clauseId :: seenIds)
      (row.clause.identityJson :: seenIdentities)
      (row :: rows) rest

private def rowBefore
    (left right : CatalogRow) : Bool :=
  left.level < right.level ||
    (left.level == right.level &&
      (left.clause.orderKey < right.clause.orderKey ||
        (left.clause.orderKey == right.clause.orderKey &&
          left.clauseId < right.clauseId)))

private def rowsStrictlyOrdered :
    List CatalogRow -> Bool
| [] | [_] => Bool.true
| left :: right :: rows =>
    rowBefore left right &&
      rowsStrictlyOrdered (right :: rows)

private def decodeSnapshot
    (json : Lean.Json) : Except String Snapshot := do
  requireObjectFields json ["rows"]
  -- No row bound: the Core a certificate emitter or the
  -- assembly differential may accept is not bounded here.
  -- The transport's 64 MiB frame is what bounds one request,
  -- and a malformed request that large fails on its content.
  let rows <- json.getObjValAs? (List Lean.Json) "rows"
  let decoded <- decodeSnapshotRows [] [] [] rows
  if !rowsStrictlyOrdered decoded then
    throw "snapshot rows are not in canonical order"
  return { rows := decoded }

private def decodeSelector
    (json : Lean.Json) :
    Except String
      FrameworkII.FixedAmbient.ObligationSelector := do
  let kind <- json.getObjValAs? String "kind"
  match kind with
  | "initialization" =>
      requireObjectFields json ["clause_id", "kind"]
      let clauseId <-
        json.getObjValAs? Nat "clause_id"
      return .initialization clauseId
  | "maintenance" =>
      requireObjectFields json ["clause_id", "kind"]
      let clauseId <-
        json.getObjValAs? Nat "clause_id"
      return .maintenance clauseId
  | "termination" =>
      requireObjectFields json ["kind"]
      return .termination
  | _ => throw "unknown fixed-ambient obligation kind"

private def selectorJson :
    FrameworkII.FixedAmbient.ObligationSelector -> Lean.Json
| .initialization clauseId =>
    Lean.Json.mkObj
      [ ("kind", Lean.Json.str "initialization"),
        ("clause_id", Lean.Json.num clauseId) ]
| .maintenance clauseId =>
    Lean.Json.mkObj
      [ ("kind", Lean.Json.str "maintenance"),
        ("clause_id", Lean.Json.num clauseId) ]
| .termination =>
    Lean.Json.mkObj
      [("kind", Lean.Json.str "termination")]

private def snapshotRowIdentity
    (row : CatalogRow) : Lean.Json :=
  Lean.Json.mkObj
    [ ("clause_id", Lean.Json.num row.clauseId),
      ("level", Lean.Json.num row.level),
      ("identity", row.clause.identityJson),
      ("canonical_source",
        Lean.Json.str row.clause.canonicalSource) ]

private def snapshotIdentity
    (snapshot : Snapshot) : Lean.Json :=
  Lean.Json.mkObj
    [ ("kind", Lean.Json.str
        "whiel_fixed_ambient_snapshot"),
      ("version", Lean.Json.num 1),
      ("rows", Lean.Json.arr
        (snapshot.rows.map snapshotRowIdentity).toArray) ]

private def obligationIdentity
    (snapshot : Snapshot)
    (selector :
      FrameworkII.FixedAmbient.ObligationSelector) :
    Lean.Json :=
  Lean.Json.mkObj
    [ ("kind", Lean.Json.str
        "whiel_fixed_ambient_obligation"),
      ("version", Lean.Json.num 1),
      ("scope_identity", entry.scopeIdentity),
      ("snapshot", snapshotIdentity snapshot),
      ("selector", selectorJson selector) ]

private structure ExactJob where
  snapshot : Snapshot
  selector : FrameworkII.FixedAmbient.ObligationSelector
  built : BuiltObligation
  identity : Lean.Json

private def decodeExactJobData
    (payload : Lean.Json) : Except String ExactJob := do
  let snapshot <-
    decodeSnapshot (payload.getObjValD "snapshot")
  let selector <-
    decodeSelector (payload.getObjValD "selector")
  let built <- entry.buildObligation snapshot selector
  return {
    snapshot
    selector
    built
    identity := obligationIdentity snapshot selector }

private def decodeExactJob
    (payload : Lean.Json) : Except String ExactJob := do
  requireObjectFields payload ["selector", "snapshot"]
  decodeExactJobData payload

private def decodeBoundExactJobFields
    (payload : Lean.Json)
    (fields : List String) : Except String ExactJob := do
  requireObjectFields payload fields
  let job <- decodeExactJobData payload
  if payload.getObjValD "obligation_identity" !=
      job.identity then
    throw "obligation identity differs from reconstruction"
  return job

private def decodeBoundExactJob
    (payload : Lean.Json) : Except String ExactJob :=
  decodeBoundExactJobFields payload
    ["obligation_identity", "selector", "snapshot"]

private def formulaIdentity
    (formula : QFAssertExpr Data
      prophecySchema) :
    Lean.Json :=
  FrameworkII.FixedAmbient.Component.formulaIdentity formula

private def entailmentIdentity
    (built : BuiltObligation) : Lean.Json :=
  Lean.Json.mkObj
    [ ("axioms", Lean.Json.arr
        (built.entailment.axioms.map
          formulaIdentity).toArray),
      ("conjecture",
        formulaIdentity built.entailment.conjecture) ]

private def exactJobJson (job : ExactJob) : Lean.Json :=
  Lean.Json.mkObj
    [ ("obligation_identity", job.identity),
      ("entailment_identity",
        entailmentIdentity job.built),
      ("selector", selectorJson job.selector) ]

end FixedAmbientWorker
end Runtime
end Synthesis
end Whiel

------------------------------------------------------------
-- Worker Operations
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientWorker

open Concrete

variable [Bound]

private def canonicalClausesFrom
    (seen : List Lean.Json) :
    List String -> Except String (List Clause)
| [] => .ok []
| source :: sources => do
    -- Canonical component source, not submitted text.
    let clause <- match entry.admitClause source {} with
      | .ok clause => .ok clause
      | .error failure =>
          .error (admissionFailureMessage failure)
    if clause.canonicalSource != source then
      throw "component clause source is not canonical"
    if seen.any fun identity =>
        identity == clause.identityJson then
      throw "component request repeats a clause identity"
    let rest <- canonicalClausesFrom
      (clause.identityJson :: seen) sources
    return clause :: rest

private def canonicalClauses
    (sources : List String) :
    Except String (List Clause) :=
  canonicalClausesFrom [] sources

private def clauseResultJson
    (clause : Clause) : Lean.Json :=
  Lean.Json.mkObj
    [ ("clause", clause.toJson),
      ("components", Lean.Json.arr
        ((entry.clauseComponents clause).map
          componentJson).toArray) ]

private def uniqueClausesFrom :
    List Lean.Json -> List Clause -> List Clause
| _, [] => []
| seen, clause :: clauses =>
    if seen.any fun identity =>
        identity == clause.identityJson then
      uniqueClausesFrom seen clauses
    else
      clause :: uniqueClausesFrom
        (clause.identityJson :: seen) clauses

/-
  Decode the run's optional `clause_text_bytes` host limit.

  `null` is the default and means unbounded: the host sets no
  limit, so neither does the parser. A number is the byte
  budget the host itself already enforced before submitting,
  carried here so the two sides cannot silently disagree.
-/
private def clauseTextBytes?
    (payload : Lean.Json) : Except String (Option Nat) :=
  match payload.getObjVal? "clause_text_bytes" with
  | .error message => .error message
  | .ok .null => .ok none
  | .ok value =>
      match value.getNat? with
      | .ok bytes => .ok (some bytes)
      | .error _ =>
          .error "clause_text_bytes must be null or a number"

private def admitClausesPayload
    (payload : Lean.Json) : Except Failure Lean.Json := do
  match requireObjectFields payload
      ["clause_text_bytes", "clauses"] with
  | .error message =>
      throw { kind := "malformed_payload", message }
  | .ok () => pure ()
  let sources <- match
      payload.getObjValAs? (List String) "clauses" with
    | .ok value => .ok value
    | .error message =>
        .error { kind := "malformed_payload", message }
  let textBytes? <- match clauseTextBytes? payload with
    | .ok value => .ok value
    | .error message =>
        .error { kind := "malformed_payload", message }
  let limits :=
    FrameworkII.SurfaceParser.Limits.ofClauseTextBytes?
      textBytes?
  match entry.admitClauses sources limits with
  | .error (.correctable diagnostic) =>
      return Lean.Json.mkObj
        [ ("outcome", Lean.Json.str "correctable"),
          ("diagnostic", diagnostic.toJson) ]
  | .error (.infrastructure message) =>
      throw { kind := "clause_admission", message }
  | .ok clauses =>
      let uniqueClauses := uniqueClausesFrom [] clauses
      return Lean.Json.mkObj
        [ ("outcome", Lean.Json.str "accepted"),
          ("clauses", Lean.Json.arr
            (uniqueClauses.map clauseResultJson).toArray) ]

private def evaluationHoldsJson
    (holds : List Bool) : Lean.Json :=
  Lean.Json.arr (holds.map Lean.Json.bool).toArray

private def clauseEvaluationJson
    (clause : Clause)
    (holds : List Bool) : Lean.Json :=
  Lean.Json.mkObj
    [ ("clause", clause.toJson),
      ("source", Lean.Json.str clause.canonicalSource),
      ("holds", evaluationHoldsJson holds) ]

private def correctableEvaluationJson
    (source : String)
    (diagnostic :
      FrameworkII.FixedAmbient.AdmissionDiagnostic) :
    Lean.Json :=
  Lean.Json.mkObj
    [ ("source", Lean.Json.str source),
      ("correctable", diagnostic.toJson) ]

/-
  Draft clauses reach evaluation under no host bound: the
  optional `evaluation_cost` limit is what the host applies
  to a `validate_clauses` call, and `clause_text_bytes`
  governs the submission path alone.
-/
private def evaluateOneClause
    (instances :
      List (FrameworkII.Refutation.DecodedInstance
        prophecySchema))
    (source : String) : Except Failure Lean.Json :=
  match entry.admitClause source {} with
  | .ok clause =>
      let holds := instances.map fun decoded =>
        FrameworkII.FixedAmbient.evaluateClauseOnInstance
          clause decoded.value
      .ok (clauseEvaluationJson clause holds)
  | .error (.correctable diagnostic) =>
      .ok (correctableEvaluationJson source diagnostic)
  | .error (.infrastructure message) =>
      .error { kind := "clause_admission", message }

private def evaluateClausesPayload
    (payload : Lean.Json) : Except Failure Lean.Json := do
  match requireObjectFields payload
      ["clauses", "instances"] with
  | .error message =>
      throw { kind := "malformed_payload", message }
  | .ok () => pure ()
  let sources <- match
      payload.getObjValAs? (List String) "clauses" with
    | .ok value => .ok value
    | .error message =>
        .error { kind := "malformed_payload", message }
  let instanceJsons <- match payload.getObjValAs?
      (List Lean.Json) "instances" with
    | .ok value => .ok value
    | .error message =>
        .error { kind := "malformed_payload", message }
  -- No draft, model, or product bound: an optional host
  -- evaluation-cost limit is the controller's, refused there
  -- as `host_limit`, and this worker evaluates exactly what
  -- it is handed. The cost is still reported, as provenance.
  let cost := sources.length * instanceJsons.length
  let instances <- match instanceJsons.mapM
      (FrameworkII.Refutation.decodeInstance
        prophecySchema) with
    | .ok value => .ok value
    | .error message =>
        .error { kind := "instance_admission", message }
  let resultsJson <-
    sources.mapM (evaluateOneClause instances)
  return Lean.Json.mkObj
    [ ("results", Lean.Json.arr resultsJson.toArray),
      ("instances", Lean.Json.num instanceJsons.length),
      ("cost", Lean.Json.num cost) ]

private def preparedComponentJson
    (prepared : PreparedComponent) :
    Lean.Json :=
  Lean.Json.mkObj
    [ ("component",
        componentJson prepared.metadata),
      ("body", bodyDataJson prepared.body),
      ("support", supportDataJson prepared.support) ]

private def prepareComponentPayload
    (state : State)
    (payload : Lean.Json) : Except Failure Lean.Json := do
  match requireObjectFields payload
      ["clause_sources", "component_identity"] with
  | .error message =>
      throw { kind := "malformed_payload", message }
  | .ok () => pure ()
  let sources <- match payload.getObjValAs?
      (List String) "clause_sources" with
    | .ok value => .ok value
    | .error message =>
        .error { kind := "malformed_payload", message }
  let clauses <- match canonicalClauses sources with
    | .ok value => .ok value
    | .error message =>
        .error { kind := "component_identity", message }
  let componentIdentity :=
    payload.getObjValD "component_identity"
  let some metadata :=
      FrameworkII.FixedAmbient.Component.resolve?
        entry.scopeIdentity componentIdentity
        entry.loop entry.task clauses
    | throw {
        kind := "component_identity"
        message := "unknown component identity" }
  match metadata.baseClauseIdentity?, clauses with
  | none, [] => pure ()
  | none, _ =>
      throw {
        kind := "component_identity"
        message :=
          "task component received clause sources" }
  | some expected, [clause] =>
      if clause.identityJson != expected then
        throw {
          kind := "component_identity"
          message := "component clause identity disagrees" }
  | some _, _ =>
      throw {
        kind := "component_identity"
        message := "clause component requires one source" }
  let some prepared :=
      entry.prepareComponent? state.nameEnv metadata
    | throw {
        kind := "name_environment"
        message :=
          "name environment does not cover component" }
  return preparedComponentJson prepared

------------------------------------------------------------
-- Opaque Formula Pieces
------------------------------------------------------------

/-
  A piece is one immutable component formula rendered against
  the current name environment. The controller caches the
  rendered bodies by (clause identity, role) and splices them
  into a verification condition itself; Lean still owns every
  formula, every rendering, and every formula identity.
-/
private def pieceJson
    (metadata :
      FrameworkII.FixedAmbient.Component.Metadata
        prophecySchema)
    (body : PreparedBodyData) : Lean.Json :=
  Lean.Json.mkObj
    [ ("role", Lean.Json.str metadata.role),
      ("formula_identity",
        FrameworkII.FixedAmbient.Component.formulaIdentity
          metadata.formula),
      ("body", bodyDataJson body) ]

private def preparePieces?
    (env : Vampire.TPTP.NameEnv WhielNames Data)
    (metadatas :
      List (FrameworkII.FixedAmbient.Component.Metadata
        prophecySchema)) : Option (List Lean.Json) :=
  metadatas.mapM fun metadata =>
    let source : SolverBodySource Data prophecySchema :=
      .qf metadata.sourceId metadata.formula
    (prepareBody? env source).map fun prepared =>
      pieceJson metadata prepared.toData

/- Render the five immutable task pieces. -/
private def prepareTaskPiecesPayload
    (state : State)
    (payload : Lean.Json) : Except Failure Lean.Json := do
  match requireObjectFields payload [] with
  | .error message =>
      throw { kind := "malformed_payload", message }
  | .ok () => pure ()
  let some pieces :=
      preparePieces? state.nameEnv entry.taskComponents
    | throw {
        kind := "name_environment"
        message :=
          "name environment does not cover the task pieces" }
  return Lean.Json.mkObj
    [("pieces", Lean.Json.arr pieces.toArray)]

private def decodeClausePieceRow
    (json : Lean.Json) : Except String Clause := do
  requireObjectFields json ["canonical_source", "identity"]
  let source <-
    json.getObjValAs? String "canonical_source"
  let identity := json.getObjValD "identity"
  admitCanonicalClause source identity

private def decodeClausePieceRows :
    List Lean.Json -> List Lean.Json ->
      Except String (List Clause)
| _, [] => .ok []
| seen, json :: rest => do
    let clause <- decodeClausePieceRow json
    if seen.any fun identity =>
        identity == clause.identityJson then
      throw "piece request repeats a clause identity"
    let others <- decodeClausePieceRows
      (clause.identityJson :: seen) rest
    return clause :: others

private def clausePiecesJson
    (env : Vampire.TPTP.NameEnv WhielNames Data)
    (clause : Clause) : Option Lean.Json :=
  (preparePieces? env (entry.clauseComponents clause)).map
    fun pieces =>
      Lean.Json.mkObj
        [ ("identity", clause.identityJson),
          ("canonical_source",
            Lean.Json.str clause.canonicalSource),
          ("pieces", Lean.Json.arr pieces.toArray) ]

/- Render the four immutable pieces of each named clause. -/
private def prepareClausePiecesPayload
    (state : State)
    (payload : Lean.Json) : Except Failure Lean.Json := do
  match requireObjectFields payload ["clauses"] with
  | .error message =>
      throw { kind := "malformed_payload", message }
  | .ok () => pure ()
  let rows <- match
      payload.getObjValAs? (List Lean.Json) "clauses" with
    | .ok value => .ok value
    | .error message =>
        .error { kind := "malformed_payload", message }
  let clauses <- match decodeClausePieceRows [] rows with
    | .ok value => .ok value
    | .error message =>
        .error { kind := "clause_admission", message }
  let some results :=
      clauses.mapM (clausePiecesJson state.nameEnv)
    | throw {
        kind := "name_environment"
        message :=
          "name environment does not cover the clause pieces" }
  return Lean.Json.mkObj
    [("clauses", Lean.Json.arr results.toArray)]

private def decodeConstantKeys
    (keys : List String) : Except String (Finset Data) := do
  let values <- keys.mapM fun key =>
    match SolverKey.dataOfKey? key with
    | some value => .ok value
    | none => .error s!"unknown constant key {key}"
  return values.toFinset

/- Render one support block over an exact constant set. -/
private def prepareSupportBlockPayload
    (state : State)
    (payload : Lean.Json) : Except Failure Lean.Json := do
  match requireObjectFields payload ["constant_keys"] with
  | .error message =>
      throw { kind := "malformed_payload", message }
  | .ok () => pure ()
  let keys <- match
      payload.getObjValAs? (List String) "constant_keys" with
    | .ok value => .ok value
    | .error message =>
        .error { kind := "malformed_payload", message }
  let constants <- match decodeConstantKeys keys with
    | .ok value => .ok value
    | .error message =>
        .error { kind := "support_constants", message }
  -- The support block is a function of the constant *set*, and the
  -- controller's own key order is its solver-key order, not Lean's
  -- domain order, so only the set is constrained here: every key must
  -- decode, and no key may repeat.
  if constants.card != keys.length then
    throw {
      kind := "support_constants"
      message := "support constant keys repeat" }
  let some support :=
      prepareSupportBlock? state.nameEnv prophecySchema
        constants
    | throw {
        kind := "name_environment"
        message :=
          "name environment does not cover the support block" }
  return supportDataJson support.toData

private abbrev Formula :=
  QFAssertExpr Data
    prophecySchema

private def prepareAxiomBodies
    (env : Vampire.TPTP.NameEnv WhielNames Data)
    (sourcePrefix : String) :
    Nat -> List Formula -> Option (List PreparedBodyData)
| _, [] => some []
| index, formula :: formulas => do
    let sourceId := sourcePrefix ++ ".axiom." ++
      toString index
    let source : SolverBodySource Data
        prophecySchema :=
      .qf sourceId formula
    let prepared <- prepareBody? env source
    let rest <- prepareAxiomBodies env sourcePrefix
      (index + 1) formulas
    pure (prepared.toData :: rest)

private def axiomTagJson
    (name : String)
    (tag : FrameworkII.FixedAmbient.AxiomTag
      prophecySchema) : Lean.Json :=
  Lean.Json.mkObj
    [ ("name", Lean.Json.str name),
      ("tag", Lean.Json.str tag.role.wireTag),
      ("identity", tag.identity.getD Lean.Json.null) ]

private def supportAxiomTagJson (name : String) : Lean.Json :=
  Lean.Json.mkObj
    [ ("name", Lean.Json.str name),
      ("tag", Lean.Json.str
        FrameworkII.FixedAmbient.AxiomRole.support.wireTag),
      ("identity", Lean.Json.null) ]

private def prepareEntailmentJson
    (state : State)
    (job : ExactJob) : Except Failure Lean.Json := do
  let sourcePrefix :=
    "framework_ii.fixed_ambient.obligation." ++
      CanonicalDigest.jsonSha256 job.identity
  let some axiomBodies :=
      prepareAxiomBodies state.nameEnv sourcePrefix 0
        job.built.entailment.axioms
    | throw {
        kind := "name_environment"
        message :=
          "name environment does not cover obligation" }
  let conjectureSource : SolverBodySource Data
      prophecySchema :=
    .qf (sourcePrefix ++ ".conjecture")
      job.built.entailment.conjecture
  let some conjectureBody :=
      prepareBody? state.nameEnv conjectureSource
    | throw {
        kind := "name_environment"
        message :=
          "name environment does not cover obligation" }
  let some support := prepareSupportBlock? state.nameEnv
      prophecySchema
      job.built.entailment.constants
    | throw {
        kind := "name_environment"
        message :=
          "name environment does not cover obligation" }
  let roles <- match FrameworkII.FixedAmbient.axiomTagsFor
      job.snapshot job.selector with
    | .ok roles => pure roles
    | .error message =>
        throw { kind := "axiom_tags", message }
  if axiomBodies.length != roles.length then
    throw {
      kind := "axiom_tags"
      message :=
        "axiom role table length differs from axiom count" }
  let supportData := support.toData
  let axiomTagEntries :=
    (axiomBodies.zip roles).map fun (body, tag) =>
      axiomTagJson body.sourceId tag
  let supportTagEntries :=
    supportAxiomTagJson (sourcePrefix ++ ".support.adom") ::
      (List.range supportData.distinctBodies.length).map
        fun index =>
          supportAxiomTagJson <|
            sourcePrefix ++ ".support.distinct." ++
              toString index
  return Lean.Json.mkObj
    [ ("obligation_identity", job.identity),
      ("entailment_identity",
        entailmentIdentity job.built),
      ("axiom_bodies", Lean.Json.arr
        (axiomBodies.map bodyDataJson).toArray),
      ("conjecture_body",
        bodyDataJson conjectureBody.toData),
      ("support", supportDataJson supportData),
      ("axiom_tags", Lean.Json.arr
        (axiomTagEntries ++ supportTagEntries).toArray) ]

private def nullaryAssignmentJson
    (assignment : Instance.NullaryAssignment
      prophecySchema) :
    Lean.Json :=
  let Gamma := prophecySchema
  Lean.Json.arr <| (Gamma.syms.attach.sort.filterMap
    fun relation =>
      if hArity : Gamma.arity relation = 0 then
        some <| Lean.Json.mkObj
          [ ("relation_key", Lean.Json.str
              (SolverKey.key relation.1)),
            ("value", Lean.Json.bool
              (assignment <| ⟨relation, hArity⟩)) ]
      else
        none).toArray

private def emptyResultJson
    (job : ExactJob)
    (result : EmptyCheckResult) :
    Lean.Json :=
  let resultJson := match result with
    | .noCounterexample =>
        Lean.Json.mkObj
          [("kind", Lean.Json.str "no_counterexample")]
    | .counterexample assignment =>
        Lean.Json.mkObj
          [ ("kind", Lean.Json.str "counterexample"),
            ("nullary_assignment",
              nullaryAssignmentJson assignment) ]
  Lean.Json.mkObj
    [ ("obligation_identity", job.identity),
      ("entailment_identity",
        entailmentIdentity job.built),
      ("result", resultJson),
      ("decision_definition", Lean.Json.str
        "QFEntailment.adomEmptyCounterexample?") ]

private def refutationResultJson
    (job : ExactJob)
    (validation :
      FrameworkII.Refutation.Validation
        prophecySchema
        job.built.entailment.constants) :
    Lean.Json :=
  Lean.Json.mkObj <|
    validation.fields job.identity ++
      [ ("entailment_identity",
          entailmentIdentity job.built),
        ("selector", selectorJson job.selector) ]

private def validateRefutationPayload
    (payload : Lean.Json) : Except Failure Lean.Json := do
  let job <- match decodeBoundExactJobFields payload
      ["interpretation", "obligation_identity", "selector",
        "snapshot"] with
    | .ok job => .ok job
    | .error message =>
        .error { kind := "obligation_identity", message }
  let interpretation := payload.getObjValD "interpretation"
  let validation <- match entry.validateRefutation
      job.built.entailment interpretation with
    | .ok validation => .ok validation
    | .error message =>
        .error { kind := "refutation_validation", message }
  return refutationResultJson job validation

private def initializationTheorem : String :=
  FrameworkII.FixedAmbient.preconditionInitializationTheorem

private def maintenanceTheorem : String :=
  FrameworkII.FixedAmbient.preconditionMaintenanceTheorem

private def preconditionRouteIdentity
    (row : PreconditionRow) : Lean.Json :=
  Lean.Json.mkObj
    [ ("kind", Lean.Json.str
        "whiel_fixed_ambient_edb_precondition_route"),
      ("version", Lean.Json.num 1),
      ("scope_identity", entry.scopeIdentity),
      ("source_ordinal", Lean.Json.num row.ordinal),
      ("level", Lean.Json.num 0),
      ("clause_identity", row.clause.identityJson),
      ("initialization_theorem", Lean.Json.str
        initializationTheorem),
      ("maintenance_theorem", Lean.Json.str
        maintenanceTheorem) ]

private def preconditionRowJson
    (row : PreconditionRow) : Lean.Json :=
  let routeIdentity := preconditionRouteIdentity row
  Lean.Json.mkObj
    [ ("source_ordinal", Lean.Json.num row.ordinal),
      ("clause", row.clause.toJson),
      ("components", Lean.Json.arr
        ((entry.clauseComponents row.clause).map
          componentJson).toArray),
      ("route_identity", routeIdentity),
      ("route_digest", Lean.Json.str
        (CanonicalDigest.jsonSha256 routeIdentity)),
      ("initialization_theorem", Lean.Json.str
        initializationTheorem),
      ("maintenance_theorem", Lean.Json.str
        maintenanceTheorem) ]

private def preconditionBasisJson : Lean.Json :=
  let rows := entry.preconditionRows.map preconditionRowJson
  let identity := Lean.Json.mkObj
    [ ("kind", Lean.Json.str
        "whiel_fixed_ambient_edb_precondition_basis"),
      ("version", Lean.Json.num 1),
      ("scope_identity", entry.scopeIdentity),
      ("precondition_identity",
        formulaIdentity entry.loop.pre),
      ("routes", Lean.Json.arr
        (entry.preconditionRows.map
          preconditionRouteIdentity).toArray) ]
  Lean.Json.mkObj
    [ ("basis_identity", identity),
      ("basis_digest", Lean.Json.str
        (CanonicalDigest.jsonSha256 identity)),
      ("rows", Lean.Json.arr rows.toArray),
      ("extraction_theorem", Lean.Json.str
        ("Whiel.Synthesis.FrameworkII.FixedAmbient." ++
          "EdbPrecondition.eval_iff_all_topConjuncts")) ]

private def confirmationTheorem :
    FrameworkII.FixedAmbient.ObligationSelector -> String
| .initialization _ =>
    FrameworkII.FixedAmbient.confirmationInitializationTheorem
| .maintenance _ =>
    FrameworkII.FixedAmbient.confirmationMaintenanceTheorem
| .termination => ""

/-
  Confirm that a bound exact job's row is one of Lean's
  extracted protected precondition rows, so a protected
  derivation is never authorized by Rust bookkeeping alone.
-/
private def confirmPreconditionRowPayload
    (payload : Lean.Json) : Except Failure Lean.Json := do
  let job <- match decodeBoundExactJobFields payload
      ["obligation_identity", "selector", "snapshot",
        "source_ordinal"] with
    | .ok job => .ok job
    | .error message =>
        .error { kind := "obligation_identity", message }
  let ordinal <- match
      payload.getObjValAs? Nat "source_ordinal" with
    | .ok ordinal => .ok ordinal
    | .error message =>
        .error { kind := "malformed_payload", message }
  let confirmation <- match entry.confirmPreconditionRow
      job.snapshot job.selector ordinal with
    | .ok confirmation => .ok confirmation
    | .error message =>
        .error { kind := "precondition_confirmation", message }
  let routeIdentity :=
    preconditionRouteIdentity confirmation.precondition
  return Lean.Json.mkObj
    [ ("obligation_identity", job.identity),
      ("entailment_identity", entailmentIdentity job.built),
      ("selector", selectorJson job.selector),
      ("source_ordinal", Lean.Json.num confirmation.ordinal),
      ("clause_id", Lean.Json.num confirmation.row.clauseId),
      ("level", Lean.Json.num confirmation.row.level),
      ("clause_identity",
        confirmation.row.clause.identityJson),
      ("route_identity", routeIdentity),
      ("route_digest", Lean.Json.str
        (CanonicalDigest.jsonSha256 routeIdentity)),
      ("confirmation_theorem", Lean.Json.str
        (confirmationTheorem job.selector)) ]

/- Emit the pure certificate plan for one frozen Core. -/
private def emitCertificatePayload
    (payload : Lean.Json) : Except Failure Lean.Json := do
  match requireObjectFields payload ["snapshot"] with
  | .error message =>
      throw { kind := "malformed_payload", message }
  | .ok () => pure ()
  let snapshot <- match
      decodeSnapshot (payload.getObjValD "snapshot") with
    | .ok snapshot => .ok snapshot
    | .error message =>
        .error { kind := "obligation_identity", message }
  match entry.emitCertificate snapshot with
  | .ok bundle => return bundle.toJson
  | .error message =>
      throw { kind := "certificate_emission", message }

private def packageRawProof
    (jobId proofNamespace raw : String)
    (extraImports : List String) : Except String String :=
  FrameworkII.FixedAmbient.CertificateEmitter.packageProof
    jobId proofNamespace raw extraImports

/- Package one raw leancheck output into its proof module. -/
private def packageProofPayload
    (payload : Lean.Json) : Except Failure Lean.Json := do
  match requireObjectFields payload
      ["extra_imports", "job_id", "proof_namespace",
        "raw_output"] with
  | .error message =>
      throw { kind := "malformed_payload", message }
  | .ok () => pure ()
  let extraImports <- match
      payload.getObjValAs? (Array String) "extra_imports" with
    | .ok value => .ok value.toList
    | .error message =>
        .error { kind := "malformed_payload", message }
  let jobId <- match payload.getObjValAs? String "job_id" with
    | .ok value => .ok value
    | .error message =>
        .error { kind := "malformed_payload", message }
  let proofNamespace <- match
      payload.getObjValAs? String "proof_namespace" with
    | .ok value => .ok value
    | .error message =>
        .error { kind := "malformed_payload", message }
  let raw <- match payload.getObjValAs? String "raw_output" with
    | .ok value => .ok value
    | .error message =>
        .error { kind := "malformed_payload", message }
  match packageRawProof jobId proofNamespace raw extraImports with
  | .ok packaged =>
      return Lean.Json.mkObj
        [ ("job_id", Lean.Json.str jobId),
          ("proof_namespace", Lean.Json.str proofNamespace),
          ("packaged", Lean.Json.str packaged),
          ("packaged_sha256", Lean.Json.str
            (CanonicalDigest.sha256 packaged)) ]
  | .error message =>
      throw { kind := "proof_packaging", message }

------------------------------------------------------------
-- Agent Counterexample Operations
------------------------------------------------------------

private def natPayloadField
    (payload : Lean.Json)
    (name : String) : Except Failure Nat :=
  match payload.getObjValAs? Nat name with
  | .ok value => .ok value
  | .error message =>
      .error { kind := "malformed_payload", message }

private def stringPayloadField
    (payload : Lean.Json)
    (name : String) : Except Failure String :=
  match payload.getObjValAs? String name with
  | .ok value => .ok value
  | .error message =>
      .error { kind := "malformed_payload", message }

/-
  Validate one agent-proposed counterexample against the
  bound entry's raw input triple alone. No snapshot and no
  catalog is consulted. A rejection is an ordinary result,
  not a protocol error.

  The request carries no fuel bound and the instance no size
  bound. The replay runs under the unreachable structural
  `Counterexample.replayFuel`, so the host's call-local
  wall-clock timeout is the only guard on this call, and the
  record freezes the fuel the run actually consumed.
-/
private def validateCounterexamplePayload
    (payload : Lean.Json) : Except Failure Lean.Json := do
  match requireObjectFields payload ["input"] with
  | .error message =>
      throw { kind := "malformed_payload", message }
  | .ok () => pure ()
  match entry.validateCounterexample
      (payload.getObjValD "input") with
  | .ok record => return record.toJson
  | .error rejection => return rejection.toJson

/-
  Emit the invalidity certificate of one frozen record. The
  instance is decoded again and re-checked against the
  frozen fuel and identity, and the emitter re-checks the
  rendered literal, so a mismatch fails closed.
-/
private def emitInvalidCertificatePayload
    (payload : Lean.Json) : Except Failure Lean.Json := do
  match requireObjectFields payload
      ["fuel", "instance", "instance_identity"] with
  | .error message =>
      throw { kind := "malformed_payload", message }
  | .ok () => pure ()
  let fuel <- natPayloadField payload "fuel"
  let identity <- stringPayloadField payload
    "instance_identity"
  let record <- match
      entry.admitFrozenCounterexample fuel
        identity (payload.getObjValD "instance") with
    | .ok record => .ok record
    | .error rejection =>
        .error {
          kind := "counterexample_rejected"
          message :=
            rejection.code ++ ": " ++ rejection.reason }
  match entry.emitInvalidCertificate record with
  | .ok bundle => return bundle.toJson
  | .error message =>
      throw { kind := "certificate_emission", message }

private def exactJobPayload
    (payload : Lean.Json) : Except Failure ExactJob :=
  match decodeExactJob payload with
  | .ok job => .ok job
  | .error message =>
      .error { kind := "obligation_identity", message }

private def boundExactJobPayload
    (payload : Lean.Json) : Except Failure ExactJob :=
  match decodeBoundExactJob payload with
  | .ok job => .ok job
  | .error message =>
      .error { kind := "obligation_identity", message }

private structure OperationResult where
  state : State
  payload : Lean.Json
  stop : Bool := Bool.false

private def unchanged
    (state : State)
    (payload : Lean.Json)
    (stop : Bool := Bool.false) : OperationResult :=
  { state, payload, stop }

private def runOperation
    (state : State)
    (request : Request) : Except Failure OperationResult :=
  match request.operation with
  | "ping" => do
      match requireObjectFields request.payload [] with
      | .error message =>
          throw { kind := "malformed_payload", message }
      | .ok () => pure ()
      return unchanged state <| Lean.Json.mkObj
        [("ready", Lean.Json.bool Bool.true)]
  | "describe" => do
      match requireObjectFields request.payload [] with
      | .error message =>
          throw { kind := "malformed_payload", message }
      | .ok () => pure ()
      return unchanged state describePayload
  | "extend_name_env" => do
      let (nextState, payload) <-
        extendNameEnv state request.payload
      return unchanged nextState payload
  | "admit_clauses" => do
      let payload <- admitClausesPayload request.payload
      return unchanged state payload
  | "evaluate_clauses" => do
      let payload <- evaluateClausesPayload request.payload
      return unchanged state payload
  | "prepare_component" => do
      let payload <-
        prepareComponentPayload state request.payload
      return unchanged state payload
  | "prepare_task_pieces" => do
      let payload <-
        prepareTaskPiecesPayload state request.payload
      return unchanged state payload
  | "prepare_clause_pieces" => do
      let payload <-
        prepareClausePiecesPayload state request.payload
      return unchanged state payload
  | "prepare_support_block" => do
      let payload <-
        prepareSupportBlockPayload state request.payload
      return unchanged state payload
  | "build_exact_obligation" => do
      let job <- exactJobPayload request.payload
      return unchanged state (exactJobJson job)
  | "prepare_exact_obligation" => do
      let job <- boundExactJobPayload request.payload
      let payload <- prepareEntailmentJson state job
      return unchanged state payload
  | "check_empty_counterexample" => do
      let job <- boundExactJobPayload request.payload
      let result <- match
          entry.checkEmptyCounterexample
            job.built.entailment with
        | .ok result => .ok result
        | .error message =>
            .error {
              kind := "empty_counterexample"
              message }
      return unchanged state (emptyResultJson job result)
  | "validate_refutation" => do
      let payload <-
        validateRefutationPayload request.payload
      return unchanged state payload
  | "extract_precondition_clauses" => do
      match requireObjectFields request.payload [] with
      | .error message =>
          throw { kind := "malformed_payload", message }
      | .ok () => pure ()
      return unchanged state preconditionBasisJson
  | "confirm_precondition_row" => do
      let payload <-
        confirmPreconditionRowPayload request.payload
      return unchanged state payload
  | "emit_certificate" => do
      let payload <- emitCertificatePayload request.payload
      return unchanged state payload
  | "package_proof" => do
      let payload <- packageProofPayload request.payload
      return unchanged state payload
  | "validate_counterexample" => do
      let payload <-
        validateCounterexamplePayload request.payload
      return unchanged state payload
  | "emit_invalid_certificate" => do
      let payload <-
        emitInvalidCertificatePayload request.payload
      return unchanged state payload
  | "shutdown" => do
      match requireObjectFields request.payload [] with
      | .error message =>
          throw { kind := "malformed_payload", message }
      | .ok () => pure ()
      return unchanged state
        (Lean.Json.mkObj [("stopped", Lean.Json.bool Bool.true)])
        true
  | operation =>
      throw {
        kind := "unknown_operation"
        message := operation }

/-
  Dispatch one parsed request against one resolved binding,
  without hidden state.
-/
def dispatchBound
    (state : State)
    (request : Request) : Dispatch :=
  match validateRequest state request with
  | .error message =>
      { state
        response := errorResponse request state {
          kind := "invalid_envelope"
          message := message } }
  | .ok () =>
      match runOperation state request with
      | .error failure =>
          { state
            response :=
              errorResponse request state failure }
      | .ok result =>
          { state := result.state
            response := okResponse request result.state
              result.payload
            stop := result.stop }

end FixedAmbientWorker
end Runtime
end Synthesis
end Whiel

------------------------------------------------------------
-- Registry Routing
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Runtime
namespace FixedAmbientWorker

open Concrete

/-
  Dispatch one parsed request under the entry its canonical
  ID names. An unregistered ID is an invalid envelope
  answered under no binding at all: the response echoes the
  request's own protocol versions and a null task and scope
  identity, because no entry was resolved to take them from.
  No operation ever crosses from one entry to another.
-/
def dispatch
    (state : State)
    (request : Request) : Dispatch :=
  match FixedAmbientRegistry.lookup? request.taskCanonicalId with
  | some bound =>
      letI : Bound := ⟨bound⟩
      dispatchBound state request
  | none =>
      { state
        response := unboundErrorResponse
          request.semanticVersion request.encodingVersion
          request.requestId request.nameEnvRevision
          state.nameEnvRevision request.operation {
            kind := "invalid_envelope"
            message :=
              "request canonical ID names no registered task" } }

/- Parse and dispatch one in-memory JSON request. -/
def dispatchJson
    (state : State)
    (json : Lean.Json) : Dispatch :=
  match Request.fromJson? json with
  | .error message =>
      { state
        response := malformedResponse state message }
  | .ok request => dispatch state request

private def processFrame
    (state : State)
    (payload : ByteArray) : Dispatch :=
  match String.fromUTF8? payload with
  | none =>
      { state
        response := malformedResponse state
          "request frame is not UTF-8" }
  | some text =>
      match Lean.Json.parse text with
      | .error message =>
          { state
            response := malformedResponse state message }
      | .ok json => dispatchJson state json

/- Run the registry worker over supplied streams. -/
def runOn
    (input output : IO.FS.Stream)
    (state : State := {}) : IO UInt32 := do
  let mut current := state
  while Bool.true do
    let some payload <- EncodingProtocol.readFrame input
      | return 0
    let result := processFrame current payload
    EncodingProtocol.writeJsonFrame output result.response
    if result.stop then
      return 0
    current := result.state
  return 0

/- Run the registry worker over stdin and stdout. -/
def run : IO UInt32 := do
  let input <- IO.getStdin
  let output <- IO.getStdout
  runOn input output

/-
  The bootstrap descriptor of one registered canonical ID,
  or `none` when no entry has that ID.
-/
def bootstrapFor? (canonicalId : String) : Option Lean.Json :=
  (FixedAmbientRegistry.lookup? canonicalId).map fun bound =>
    letI : Bound := ⟨bound⟩
    bootstrap

/-
  The registry's default binding. It is used only where a
  payload genuinely needs one entry and the caller named
  none: `manifest` with no argument answers under it. No
  error response is ever shaped by it.
-/
@[reducible] private def defaultBound : Bound :=
  ⟨FixedAmbientRegistry.Example0001.entry⟩

/- The production descriptor, unchanged from the V5 wire. -/
def bootstrapForDefault : Lean.Json :=
  letI : Bound := defaultBound
  bootstrap

end FixedAmbientWorker
end Runtime
end Synthesis
end Whiel

------------------------------------------------------------
-- Executable Entrypoint
------------------------------------------------------------

open Whiel.Synthesis.Runtime

/-
  `manifest` with no argument keeps emitting the production
  descriptor; `manifest <Id>` emits the descriptor of any
  registered canonical ID.
-/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["manifest"] =>
      IO.println <|
        FixedAmbientWorker.bootstrapForDefault.compress
      return 0
  | ["manifest", canonicalId] =>
      match FixedAmbientWorker.bootstrapFor? canonicalId with
      | some descriptor =>
          IO.println descriptor.compress
          return 0
      | none =>
          IO.eprintln
            ("unknown fixed-ambient canonical ID " ++
              canonicalId ++ "; registered IDs are " ++
              String.intercalate ", "
                FixedAmbientRegistry.supportedTaskIds)
          return 2
  | ["ids"] =>
      for canonicalId in
          FixedAmbientRegistry.supportedTaskIds do
        IO.println canonicalId
      return 0
  | ["worker"] => FixedAmbientWorker.run
  | _ =>
      IO.eprintln
        ("usage: fixed_ambient_encoding_worker " ++
          "<manifest [<Id>] | ids | worker>")
      return 2
