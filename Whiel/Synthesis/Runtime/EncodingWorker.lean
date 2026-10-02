-- Author: Jesse Comer
import Whiel.Synthesis.Runtime.Encoding
import Whiel.Synthesis.Runtime.EncodingProtocol
import Whiel.Synthesis.Runtime.FastProposal
import Whiel.Synthesis.Runtime.SeededProposal
import Whiel.Synthesis.Runtime.CappedProposal
import Whiel.Synthesis.Runtime.ReferenceProposal

/-
  Registry-parametric persistent encoding worker.

  A concrete launcher imports one trusted task and supplies
  key resolvers for its schema, constants, and exact Lean
  source formulas. The generic loop does not elaborate input
  syntax.
-/

------------------------------------------------------------
-- Task Registries and Worker State
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Runtime

open EncodingProtocol

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable [LinearOrder A]
variable [LinearOrder D]
variable [SolverKey A]
variable [SolverKey D]
variable [Vampire.SolverName A]
variable [Vampire.SolverName D]

/- Trusted declarations available to one compiled launcher. -/
structure EncodingTaskRegistry
    (A D : Type)
    [RelationNames A]
    [Domain D]
    [LinearOrder A]
    [LinearOrder D]
    [SolverKey A]
    [SolverKey D] where
  identity : WorkerIdentity
  schema : UnnamedSchema A
  loopGuard : Guard D schema
  loopBody : Cmd D schema
  loopBodyLoopFree : loopBody.LoopFree
  resolveRelation : String → Option A
  resolveConstant : String → Option D
  resolveSource : String →
    Option (SolverBodySource D schema)
  referenceAlphabet :
    DisjunctiveClause.Alphabet D schema
  seedLiterals :
    Finset (DisjunctiveClause.Literal D schema) := ∅

/- One stage evaluated once and reused across all response pages. -/
structure PendingProposalStage
    (A D : Type)
    [RelationNames A]
    [Domain D]
    (Γ : UnnamedSchema A) where
  realization : FastProposal.Realization
  stage : Nat
  entries : List (ReferenceProposal.Entry (D := D) (Γ := Γ))
  serialized : List Char
  cumulativeRawOccurrences : Nat
  cumulativeCanonicalFormulas : Nat
  emittedFormulas : Nat
  generatorWorkUnits : Nat := 0
  freshTraversalNodes : Nat := 0
  freshNoFreshPrunes : Nat := 0
  freshTooShortPrunes : Nat := 0
  nextFastState? : Option
    (Enumerators.Fast.State (D := D) (Γ := Γ)) := none
  nextSeededState? : Option
    (Enumerators.Seeded.SeededState (D := D) (Γ := Γ)) := none
  nextCappedState? : Option
    (Enumerators.Capped.CappedState (D := D) (Γ := Γ)) := none

/- Mutable state owned by one persistent process. -/
structure EncodingWorkerState
    (A D : Type)
    [RelationNames A]
    [Domain D]
    (Γ : UnnamedSchema A) where
  nameEnvRevision : Nat := 0
  proposalRevision : Nat := 0
  proposalCursor : Nat := 0
  proposalRealization? : Option FastProposal.Realization := none
  proposalPending? : Option (PendingProposalStage A D Γ) := none
  proposalCumulativeRawOccurrences : Nat := 0
  proposalCumulativeCanonicalFormulas : Nat := 0
  fastProposalState :
    Enumerators.Fast.State (D := D) (Γ := Γ) :=
      Enumerators.Fast.initialState
  seededProposalState :
    Enumerators.Seeded.SeededState (D := D) (Γ := Γ) :=
      Enumerators.Seeded.initialSeededState
  /-
    The initial capped frontier admits the task's seed
    literals, which are not available to a field default;
    `none` denotes the task-seeded initial state.
  -/
  cappedProposalState? : Option
    (Enumerators.Capped.CappedState (D := D) (Γ := Γ)) :=
      none
  nameEnv : Vampire.TPTP.NameEnv A D :=
    { relNames := [], funNames := [] }
  referenceBindings :
    Std.HashMap String (QFAssertExpr D Γ) := {}
  wLayers : Array (QFAssertExpr D Γ × QFAssertExpr D Γ) := #[]
  wBindings :
    Std.HashMap String (QFAssertExpr D Γ) := {}

/- Result of one request dispatch. -/
structure EncodingDispatch
    (A D : Type)
    [RelationNames A]
    [Domain D]
    (Γ : UnnamedSchema A) where
  state : EncodingWorkerState A D Γ
  response : Response
  stop : Bool := false

end Runtime
end Synthesis
end Whiel

------------------------------------------------------------
-- Derived Maintenance-WP Sources
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Runtime

/- Reserved injective namespace for worker-derived maintenance WPs. -/
private def maintenanceWpPrefix : String :=
  "__whiel_maintenance_wp__:"

/- Reserved task-local namespace for exact dynamic W formulas. -/
private def wLayerPrefix : String :=
  "__whiel_w_layer__:"

/- Reserved task-local namespace for exact dynamic W WPs. -/
private def wLayerWpPrefix : String :=
  "__whiel_w_layer_wp__:"

/- Stable source identity derived from one exact registered source. -/
private def maintenanceWpSourceId (sourceId : String) : String :=
  maintenanceWpPrefix ++ sourceId

/- Stable source identity for one exact task-scoped W formula. -/
private def wLayerSourceId (index : Nat) : String :=
  wLayerPrefix ++ toString index

/- Stable source identity for one exact task-scoped W WP. -/
private def wLayerWpSourceId (index : Nat) : String :=
  wLayerWpPrefix ++ toString index

/- Fixed source identities derived from the trusted task. -/
private def loopGuardSourceId : String :=
  "task.loop_guard"

private def negatedLoopGuardSourceId : String :=
  "task.negated_loop_guard"

/- Resolve one registered static or admitted reference source. -/
private def resolveDirectWorkerSource
    {A D : Type}
    [RelationNames A]
    [Domain D]
    [LinearOrder A]
    [LinearOrder D]
    [SolverKey A]
    [SolverKey D]
    (registry : EncodingTaskRegistry A D)
    (state : EncodingWorkerState A D registry.schema)
    (sourceId : String) :
    Option (SolverBodySource D registry.schema) :=
  match registry.resolveSource sourceId with
  | some source => some source
  | none =>
      match state.wBindings.get? sourceId with
      | some formula => some (.qf sourceId formula)
      | none =>
          match state.referenceBindings.get? sourceId with
          | none => none
          | some formula => some (.qf sourceId formula)

/- A persisted typed binding resolves without re-enumeration. -/
private theorem resolveDirectWorkerSource_of_referenceBinding
    {A D : Type}
    [RelationNames A]
    [Domain D]
    [LinearOrder A]
    [LinearOrder D]
    [SolverKey A]
    [SolverKey D]
    (registry : EncodingTaskRegistry A D)
    (state : EncodingWorkerState A D registry.schema)
    (sourceId : String)
    (formula : QFAssertExpr D registry.schema)
    (hStatic : registry.resolveSource sourceId = none)
    (hDynamic : state.wBindings.get? sourceId = none)
    (hBinding : state.referenceBindings.get? sourceId = some formula) :
    resolveDirectWorkerSource registry state sourceId =
      some (.qf sourceId formula) := by
  unfold resolveDirectWorkerSource
  rw [hStatic]
  change (match state.wBindings.get? sourceId with
    | some bound => some (SolverBodySource.qf sourceId bound)
    | none =>
      match state.referenceBindings.get? sourceId with
    | none => none
    | some bound =>
        some (SolverBodySource.qf sourceId bound)) = _
  rw [hDynamic]
  rw [hBinding]

/- Resolve a direct source or its exact loop-body maintenance WP. -/
private def resolveWorkerSource
    {A D : Type}
    [RelationNames A]
    [Domain D]
    [LinearOrder A]
    [LinearOrder D]
    [SolverKey A]
    [SolverKey D]
    (registry : EncodingTaskRegistry A D)
    (state : EncodingWorkerState A D registry.schema)
    (sourceId : String) :
    Option (SolverBodySource D registry.schema) :=
  if sourceId = loopGuardSourceId then
    if (registry.resolveSource sourceId).isSome then
      none
    else
      some (.qf sourceId registry.loopGuard)
  else if sourceId = negatedLoopGuardSourceId then
    if (registry.resolveSource sourceId).isSome then
      none
    else
      some (.qf sourceId
        (QFAssertExpr.not registry.loopGuard))
  else if sourceId.startsWith maintenanceWpPrefix then
    /- Reject a direct registry collision instead of choosing one meaning. -/
    if (registry.resolveSource sourceId).isSome then
      none
    else
      let originalId :=
        (sourceId.drop maintenanceWpPrefix.length).toString
      match resolveDirectWorkerSource registry state originalId with
      | none => none
      | some source =>
          some (.qf sourceId
            (QFAssertExpr.wpLoopFree registry.loopBody
              registry.loopBodyLoopFree source.toQF))
  else
    resolveDirectWorkerSource registry state sourceId

end Runtime
end Synthesis
end Whiel

------------------------------------------------------------
-- JSON Payload Helpers
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Runtime

open EncodingProtocol

private def bindingJson
    (binding : String × String) : Lean.Json :=
  NameBinding.toJson
    { key := binding.1, name := binding.2 }

private def bindingListJson
    (bindings : List (String × String)) : Lean.Json :=
  Lean.Json.arr (bindings.map bindingJson).toArray

private def bodyDataJson
    (body : PreparedBodyData) : Lean.Json :=
  Lean.Json.mkObj
    [ ("source_id", Lean.Json.str body.sourceId),
      ("source_kind", Lean.Json.str body.sourceKind),
      ("exact_constant_keys",
        Lean.Json.arr
          (body.exactConstantKeys.map Lean.Json.str).toArray),
      ("body", Lean.Json.str body.body),
      ("referenced_relations",
        bindingListJson body.referencedRelations),
      ("referenced_constants",
        bindingListJson body.referencedConstants) ]

private def supportDataJson
    (support : PreparedSupportData) : Lean.Json :=
  Lean.Json.mkObj
    [ ("constant_keys",
        Lean.Json.arr
          (support.constantKeys.map Lean.Json.str).toArray),
      ("adom_body", Lean.Json.str support.adomBody),
      ("distinct_bodies",
        Lean.Json.arr
          (support.distinctBodies.map Lean.Json.str).toArray),
      ("referenced_relations",
        bindingListJson support.referencedRelations),
      ("referenced_constants",
        bindingListJson support.referencedConstants) ]

private def referenceEntryJson
    {A D : Type}
    [RelationNames A]
    [Domain D]
    [LinearOrder A]
    [LinearOrder D]
    [SolverKey A]
    [SolverKey D]
    {Γ : UnnamedSchema A}
    (entry : ReferenceProposal.Entry (D := D) (Γ := Γ)) :
    Lean.Json :=
  Lean.Json.mkObj
    [ ("source_id", Lean.Json.str entry.sourceId),
      ("identity", entry.identity.toJson),
      ("display", Lean.Json.str entry.display),
      ("constants", Lean.Json.arr
        (entry.formula.constants.sort.map
          (Lean.Json.str ∘ SolverKey.key)).toArray),
      ("relations", Lean.Json.arr
        (entry.formula.symbols.sort.map
          (Lean.Json.str ∘ SolverKey.key)).toArray) ]

/-
  Byte-identical to compressing the entry list as one JSON
  array (pinned by test): `Json.compress` renders an array
  through a per-element fold whose stack depth grows with the
  element count, and one stage's entry array can be six
  figures long. Joining per-entry output keeps the recursion
  depth bounded by one entry.
-/
private def serializedProposalEntries
    {A D : Type}
    [RelationNames A]
    [Domain D]
    [LinearOrder A]
    [LinearOrder D]
    [SolverKey A]
    [SolverKey D]
    {Γ : UnnamedSchema A}
    (entries :
      List (ReferenceProposal.Entry (D := D) (Γ := Γ))) :
    List Char :=
  ("[" ++ String.intercalate ","
      (entries.map fun entry =>
        (referenceEntryJson entry).compress) ++
    "]").toList

/- Serialize one exact dynamic QF source and prepared body. -/
private def dynamicSourceJson
    {A D : Type}
    [RelationNames A]
    [Domain D]
    [LinearOrder A]
    [LinearOrder D]
    [SolverKey A]
    [SolverKey D]
    {Γ : UnnamedSchema A}
    (sourceId : String)
    (formula : QFAssertExpr D Γ)
    (body : PreparedBodyData) : Lean.Json :=
  Lean.Json.mkObj
    [ ("source_id", Lean.Json.str sourceId),
      ("identity", (ReferenceProposal.identity formula).toJson),
      ("display", Lean.Json.str formula.pretty),
      ("constants", Lean.Json.arr
        (formula.constants.sort.map
          (Lean.Json.str ∘ SolverKey.key)).toArray),
      ("relations", Lean.Json.arr
        (formula.symbols.sort.map
          (Lean.Json.str ∘ SolverKey.key)).toArray),
      ("prepared_body", bodyDataJson body) ]

private def parseBindings
    (payload : Lean.Json)
    (field : String) : Except String (List NameBinding) := do
  let values ← payload.getObjValAs? (List Lean.Json) field
  values.mapM NameBinding.fromJson?

private def parseStrings
    (payload : Lean.Json)
    (field : String) : Except String (List String) :=
  payload.getObjValAs? (List String) field

/- Exact ordered sources for one empty-instance check. -/
private structure EmptyEntailmentRequest where
  axiomSourceIds : List String
  goalSourceIds : List String

/-
  Parse one source entailment without elaborating syntax.
-/
private def parseEmptyEntailmentRequest
    (payload : Lean.Json) :
    Except String EmptyEntailmentRequest := do
  let axiomSourceIds ←
    parseStrings payload "axiom_source_ids"
  let goalSourceIds ←
    parseStrings payload "goal_source_ids"
  if goalSourceIds.isEmpty then
    throw "goal_source_ids must be nonempty"
  return { axiomSourceIds, goalSourceIds }

/- Parse exact source identities and their constant keys. -/
private def parseBodyRequests
    (payload : Lean.Json) :
    Except String (List (String × List String)) := do
  let requests ←
    payload.getObjValAs? (List Lean.Json) "sources"
  requests.mapM fun request => do
    let sourceId ←
      request.getObjValAs? String "source_id"
    let constantKeys ←
      request.getObjValAs?
        (List String) "exact_constant_keys"
    return (sourceId, constantKeys)

end Runtime
end Synthesis
end Whiel

------------------------------------------------------------
-- Empty-Instance Checks
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Runtime

open EncodingProtocol

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable [LinearOrder A]
variable [LinearOrder D]
variable [SolverKey A]
variable [SolverKey D]
variable [Vampire.SolverName A]
variable [Vampire.SolverName D]

/- Resolve exact source identities to their QF formulas. -/
private def resolveQFSources
    (registry : EncodingTaskRegistry A D)
    (state : EncodingWorkerState A D registry.schema)
    (sourceIds : List String) :
    Except String
      (List (QFAssertExpr D registry.schema)) :=
  sourceIds.mapM fun sourceId => do
    let some source := resolveWorkerSource registry state sourceId
      | throw s!"unknown source id {sourceId}"
    return source.toQF

/- Serialize every nullary choice in stable schema order. -/
private def nullaryAssignmentJson
    (registry : EncodingTaskRegistry A D)
    (χ : Instance.NullaryAssignment registry.schema) :
    Lean.Json :=
  let bindings :=
    registry.schema.syms.attach.sort.filterMap fun X =>
      if hAr : registry.schema.arity X = 0 then
        some <| Lean.Json.mkObj
          [ ("relation_key",
              Lean.Json.str (SolverKey.key X.1)),
            ("value", Lean.Json.bool (χ ⟨X, hAr⟩)) ]
      else
        none
  Lean.Json.arr bindings.toArray

/-
  Exhaustively check one exact ordered source entailment.
-/
private def checkEmptyEntailment
    (registry : EncodingTaskRegistry A D)
    (state : EncodingWorkerState A D registry.schema)
    (sourceRequest : EmptyEntailmentRequest) :
    Except String Lean.Json := do
  let axioms ←
    resolveQFSources registry state sourceRequest.axiomSourceIds
  let goals ←
    resolveQFSources registry state sourceRequest.goalSourceIds
  let entailment :
      QFEntailment (D := D) registry.schema :=
    { axioms
      conjecture := QFAssertExpr.andList goals }
  let sourceFields : List (String × Lean.Json) :=
    [ ("axiom_source_ids",
        Lean.Json.arr
          (sourceRequest.axiomSourceIds.map
            Lean.Json.str).toArray),
      ("goal_source_ids",
        Lean.Json.arr
          (sourceRequest.goalSourceIds.map
            Lean.Json.str).toArray) ]
  if !entailment.emptyCounterexample? then
    return Lean.Json.mkObj
      ([ ("outcome",
          Lean.Json.str "no_counterexample") ] ++
        sourceFields)
  else
    match findEmptyCounterexample? entailment with
    | none =>
        throw
          ("empty checker found a counterexample " ++
            "without a witness")
    | some χ =>
        return Lean.Json.mkObj
          ([ ("outcome", Lean.Json.str "counterexample"),
             ("nullary_assignment",
               nullaryAssignmentJson registry χ) ] ++
            sourceFields)

end Runtime
end Synthesis
end Whiel

------------------------------------------------------------
-- Name-Environment Extension
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Runtime

open EncodingProtocol

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable [LinearOrder A]
variable [LinearOrder D]
variable [SolverKey A]
variable [SolverKey D]
variable [Vampire.SolverName A]
variable [Vampire.SolverName D]

private def resolveBindingList
    {X : Type}
    [SolverKey X]
    (kind : String)
    (resolve : String → Option X)
    (bindings : List NameBinding) :
    Except String (List (X × String)) := do
  bindings.mapM fun binding => do
    if !Vampire.legalTptpName binding.name then
      throw s!"illegal TPTP name for {kind} key {binding.key}"
    let some value := resolve binding.key
      | throw s!"unknown {kind} key {binding.key}"
    if SolverKey.key value != binding.key then
      throw s!"noncanonical {kind} key {binding.key}"
    return (value, binding.name)

private def extendNameEnv
    (registry : EncodingTaskRegistry A D)
    (state : EncodingWorkerState A D registry.schema)
    (request : Request) :
    Except String
      (EncodingWorkerState A D registry.schema × Lean.Json) := do
  let nextRevision ←
    request.payload.getObjValAs? Nat "next_revision"
  if request.nameEnvRevision != state.nameEnvRevision then
    throw "request NameEnv revision is stale or ahead"
  if request.proposalRevision != state.proposalRevision then
    throw "request proposal revision is stale or ahead"
  if nextRevision != state.nameEnvRevision + 1 then
    throw "NameEnv revisions must be contiguous"
  let relationBindings ← parseBindings request.payload "relations"
  let constantBindings ← parseBindings request.payload "constants"
  let relations ← resolveBindingList
    "relation" registry.resolveRelation relationBindings
  let constants ← resolveBindingList
    "constant" registry.resolveConstant constantBindings
  let some nameEnv := state.nameEnv.appendBindings? relations constants
    | throw "NameEnv extension conflicts with an existing key or name"
  let nextState : EncodingWorkerState A D registry.schema :=
    { state with
      nameEnvRevision := nextRevision
      nameEnv }
  let payload := Lean.Json.mkObj
    [ ("relations",
        Lean.Json.arr (relationBindings.map NameBinding.toJson).toArray),
      ("constants",
        Lean.Json.arr (constantBindings.map NameBinding.toJson).toArray) ]
  return (nextState, payload)

end Runtime
end Synthesis
end Whiel

------------------------------------------------------------
-- Source Preparation
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Runtime

open EncodingProtocol

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable [LinearOrder A]
variable [LinearOrder D]
variable [SolverKey A]
variable [SolverKey D]
variable [Vampire.SolverName A]
variable [Vampire.SolverName D]

/- Compare duplicate-free exact keys independently of list order. -/
def exactConstantKeysMatch
    (requested exact : List String) : Bool :=
  decide requested.Nodup &&
    decide (requested.toFinset = exact.toFinset)

private def prepareSourceRequests
    (registry : EncodingTaskRegistry A D)
    (state : EncodingWorkerState A D registry.schema)
    (requests : List (String × List String)) :
    Except String (List PreparedBodyData) := do
  requests.mapM fun request => do
    let sourceId := request.1
    let requestedKeys := request.2
    let some source := resolveWorkerSource registry state sourceId
      | throw s!"unknown source id {sourceId}"
    let exactKeys :=
      source.toSentence.constants.sort.map SolverKey.key
    if !requestedKeys.Nodup then
      throw
        ("duplicate exact constant key for source " ++
          sourceId)
    if !exactConstantKeysMatch requestedKeys exactKeys then
      throw
        ("exact constant keys differ for source " ++
          sourceId)
    let some prepared := prepareBody? state.nameEnv source
      | throw s!"NameEnv does not cover source {sourceId}"
    return prepared.toData

/- Compute and prepare exact loop-body WPs for registered QF sources. -/
private def prepareMaintenanceWpRequests
    (registry : EncodingTaskRegistry A D)
    (state : EncodingWorkerState A D registry.schema)
    (sourceIds : List String) :
    Except String (List PreparedBodyData) := do
  sourceIds.mapM fun sourceId => do
    if sourceId.startsWith maintenanceWpPrefix then
      throw s!"maintenance-WP input uses reserved source id {sourceId}"
    let derivedId := maintenanceWpSourceId sourceId
    if (registry.resolveSource derivedId).isSome then
      throw s!"registered source collides with reserved maintenance-WP id {derivedId}"
    let some source := resolveWorkerSource registry state sourceId
      | throw s!"unknown maintenance-WP source id {sourceId}"
    let wpSource : SolverBodySource D registry.schema :=
      .qf derivedId
        (QFAssertExpr.wpLoopFree registry.loopBody
          registry.loopBodyLoopFree source.toQF)
    let some prepared := prepareBody? state.nameEnv wpSource
      | throw s!"NameEnv does not cover maintenance WP for {sourceId}"
    return prepared.toData

private def prepareConstantKeys
    (registry : EncodingTaskRegistry A D)
    (state : EncodingWorkerState A D registry.schema)
    (constantKeys : List String) :
    Except String PreparedSupportData := do
  let constants ← constantKeys.mapM fun key => do
    let some constant := registry.resolveConstant key
      | throw s!"unknown constant key {key}"
    if SolverKey.key constant != key then
      throw s!"noncanonical constant key {key}"
    return constant
  let constantSet := constants.toFinset
  let some prepared :=
      prepareSupportBlock? state.nameEnv registry.schema constantSet
    | throw "NameEnv does not cover the support block"
  return prepared.toData

end Runtime
end Synthesis
end Whiel

------------------------------------------------------------
-- Dynamic W-Layer Registration
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Runtime

open EncodingProtocol

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable [LinearOrder A]
variable [LinearOrder D]
variable [SolverKey A]
variable [SolverKey D]
variable [Vampire.SolverName A]
variable [Vampire.SolverName D]

/- One complete newly constructed W formula and its exact WP. -/
private def nextWLayer
    (registry : EncodingTaskRegistry A D)
    (state : EncodingWorkerState A D registry.schema) :
    Except String
      (QFAssertExpr D registry.schema ×
        QFAssertExpr D registry.schema) := do
  let formula ← match state.wLayers.back? with
    | none => do
        let some post :=
            registry.resolveSource "task.preprocessed_post"
          | throw "task registry has no preprocessed-post source"
        pure (QFAssertExpr.or registry.loopGuard post.toQF)
    | some previous =>
        pure (QFAssertExpr.implies registry.loopGuard previous.2)
  let wp :=
    QFAssertExpr.wpLoopFree registry.loopBody
      registry.loopBodyLoopFree formula
  return (formula, wp)

/- Reject every collision with the reserved dynamic namespace. -/
private def dynamicSourceAvailable
    (registry : EncodingTaskRegistry A D)
    (state : EncodingWorkerState A D registry.schema)
    (sourceId : String) : Bool :=
  !(registry.resolveSource sourceId).isSome &&
    !(state.referenceBindings.contains sourceId) &&
    !(state.wBindings.contains sourceId)

/- Construct and atomically register one contiguous W layer. -/
private def ensureWLayer
    (registry : EncodingTaskRegistry A D)
    (state : EncodingWorkerState A D registry.schema)
    (request : Request) :
    Except String
      (EncodingWorkerState A D registry.schema × Lean.Json) := do
  let index ← request.payload.getObjValAs? Nat "index"
  if index != state.wLayers.size then
    throw "W-layer registrations must be fresh and contiguous"
  let formulaId := wLayerSourceId index
  let wpId := wLayerWpSourceId index
  if !dynamicSourceAvailable registry state formulaId ||
      !dynamicSourceAvailable registry state wpId then
    throw "W-layer source identity collides with a registered source"
  let (formula, wp) ← nextWLayer registry state
  let formulaSource : SolverBodySource D registry.schema :=
    .qf formulaId formula
  let wpSource : SolverBodySource D registry.schema :=
    .qf wpId wp
  let some preparedFormula :=
      prepareBody? state.nameEnv formulaSource
    | throw "NameEnv does not cover the exact W formula"
  let some preparedWP := prepareBody? state.nameEnv wpSource
    | throw "NameEnv does not cover the exact W WP"
  let formulaData := preparedFormula.toData
  let wpData := preparedWP.toData
  let nextBindings :=
    (state.wBindings.insert formulaId formula).insert wpId wp
  let nextState :=
    { state with
      wLayers := state.wLayers.push (formula, wp)
      wBindings := nextBindings }
  let payload := Lean.Json.mkObj
    [ ("index", Lean.Json.num index),
      ("formula",
        dynamicSourceJson formulaId formula formulaData),
      ("maintenance_wp",
        dynamicSourceJson wpId wp wpData) ]
  return (nextState, payload)

end Runtime
end Synthesis
end Whiel

------------------------------------------------------------
-- Reference-Proposal Registration
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Runtime

open EncodingProtocol

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable [LinearOrder A]
variable [LinearOrder D]
variable [SolverKey A]
variable [SolverKey D]
variable [Vampire.SolverName A]
variable [Vampire.SolverName D]

private structure ReferenceProposalFailure where
  kind : String
  message : String

private def referenceProposalFailure
    (message : String) : ReferenceProposalFailure :=
  { kind := "reference_proposal_registration", message }

private def referenceProposalPagePayload
    (realization : FastProposal.Realization)
    (stage cursor nextCursor : Nat)
    (complete : Bool)
    (rawOccurrences canonicalFormulas emittedFormulas : Nat)
    (generatorWorkUnits freshTraversalNodes : Nat)
    (freshNoFreshPrunes freshTooShortPrunes : Nat)
    (fragment : String) : Lean.Json :=
  let common :=
    [ ("realization_id", Lean.Json.str realization.id),
      ("realization_version", Lean.Json.num realization.version),
      ("version", Lean.Json.num FastProposal.protocolVersion),
      ("stage", Lean.Json.num stage),
      ("cursor", Lean.Json.num cursor),
      ("next_cursor", Lean.Json.num nextCursor),
      ("complete", Lean.Json.bool complete),
      ("raw_occurrences", Lean.Json.num rawOccurrences),
      ("canonical_formulas", Lean.Json.num canonicalFormulas),
      ("canonical_duplicates",
        Lean.Json.num (rawOccurrences - canonicalFormulas)),
      ("emitted_formulas", Lean.Json.num emittedFormulas),
      ("fragment", Lean.Json.str fragment) ]
  let fields := match realization with
    | .referenceV3 => common
    | .fastV1 | .seededV1 | .cappedV1 => common ++
        [("fast_work", Lean.Json.arr #[
          Lean.Json.num generatorWorkUnits,
          Lean.Json.num freshTraversalNodes,
          Lean.Json.num freshNoFreshPrunes,
          Lean.Json.num freshTooShortPrunes])]
  Lean.Json.mkObj fields

/- Largest integer representable by the Rust wire envelope. -/
private def maxWireNat : Nat := 18446744073709551615

/-
  Exact response size with every replay-varying wire integer widened to
  its maximum representation. This makes page boundaries deterministic
  across request identifiers while conservatively bounding the real reply.
-/
private def referenceProposalResponseBudgetBytes
    (request : Request)
    (payload : Lean.Json) : Nat :=
  let budgetRequest :=
    { request with
      requestId := maxWireNat
      nameEnvRevision := maxWireNat
      proposalRevision := maxWireNat }
  (Response.ok budgetRequest maxWireNat payload
      (currentProposalRevision := maxWireNat)).toJson.compress.toUTF8.size

/- Largest prefix accepted by one monotone exact-size predicate. -/
private partial def largestFittingPrefix
    (fits : Nat → Bool)
    (lower upper : Nat) : Nat :=
  if lower < upper then
    let middle := (lower + upper + 1) / 2
    if fits middle then
      largestFittingPrefix fits middle upper
    else
      largestFittingPrefix fits lower (middle - 1)
  else
    lower

/-
  Build the largest conservative character fragment whose exact
  successful response remains within the requested frame budget.
-/
private def referenceProposalPage
    (request : Request)
    (realization : FastProposal.Realization)
    (stage cursor maximum : Nat)
    (rawOccurrences canonicalFormulas emittedFormulas : Nat)
    (generatorWorkUnits freshTraversalNodes : Nat)
    (freshNoFreshPrunes freshTooShortPrunes : Nat)
    (serialized : List Char) :
    Except ReferenceProposalFailure (Nat × Bool × String × Lean.Json) := do
  if maximum = 0 || maxFrameBytes < maximum then
    throw
      { kind := "reference_proposal_response_budget"
        message := "reference-proposal response budget is outside the worker frame limit" }
  if serialized.length < cursor then
    throw (referenceProposalFailure
      "reference-proposal cursor is past the exact wave")
  let remaining := serialized.drop cursor
  /-
    One source character can require six JSON bytes. The factor eight
    also reserves metadata growth. The exact envelope check below is
    authoritative.
  -/
  let conservativeUpper := min remaining.length (maximum / 8)
  let fragmentFor := fun count =>
    String.ofList (remaining.take count)
  let payloadFor := fun count complete =>
    referenceProposalPagePayload realization stage cursor (cursor + count)
      complete rawOccurrences canonicalFormulas emittedFormulas
      generatorWorkUnits freshTraversalNodes
      freshNoFreshPrunes freshTooShortPrunes
      (fragmentFor count)
  let responseFits := fun count complete =>
    referenceProposalResponseBudgetBytes request
        (payloadFor count complete) ≤ maximum
  if remaining.isEmpty then
    let payload := payloadFor 0 true
    if responseFits 0 true then
      pure (0, true, "", payload)
    else
      throw
        { kind := "reference_proposal_response_budget"
          message := "reference-proposal response metadata exceeds the frame budget" }
  else if conservativeUpper = remaining.length &&
      responseFits remaining.length true then
    let fragment := fragmentFor remaining.length
    pure
      (remaining.length, true, fragment,
        payloadFor remaining.length true)
  else
    let nonterminalUpper := min conservativeUpper (remaining.length - 1)
    let count := largestFittingPrefix
      (fun candidate =>
        responseFits candidate false)
      0 nonterminalUpper
    if count = 0 then
      throw
        { kind := "reference_proposal_response_budget"
          message := "reference-proposal response budget cannot carry one character" }
    else
      let fragment := fragmentFor count
      pure (count, false, fragment, payloadFor count false)

/-
  Linear-time duplicate scan for the source-identity guard:
  equivalent to deciding `Nodup` on the identity list, whose
  pairwise decision procedure is quadratic in a stage's entry
  count.
-/
private def hasDuplicateSourceId
    {A D : Type}
    [RelationNames A]
    [Domain D]
    [SolverKey A]
    [SolverKey D]
    {Γ : UnnamedSchema A}
    (entries :
      List (ReferenceProposal.Entry (D := D) (Γ := Γ))) :
    Bool :=
  (entries.foldl
    (fun state entry =>
      match state with
      | (true, seen) => (true, seen)
      | (false, seen) =>
          if seen.contains entry.sourceId then
            (true, seen)
          else
            (false, seen.insert entry.sourceId))
    (false, (∅ : Std.HashSet String))).1

/- Evaluate and serialize one stage before its first response page. -/
private def prepareProposalStage
    (registry : EncodingTaskRegistry A D)
    (state : EncodingWorkerState A D registry.schema)
    (realization : FastProposal.Realization)
    (stage : Nat) :
    Except ReferenceProposalFailure
      (PendingProposalStage A D registry.schema) := do
  let pending ←
    match realization with
    | .referenceV3 =>
        let batch :=
          ReferenceProposal.stageBatch
            registry.identity.taskCanonicalId
            registry.referenceAlphabet stage
        let entries := batch.entries
        let serialized := serializedProposalEntries entries
        pure
          { realization
            stage
            entries
            serialized
            cumulativeRawOccurrences := batch.rawFormulaCount
            cumulativeCanonicalFormulas := batch.canonicalFormulaCount
            emittedFormulas := entries.length }
    | .fastV1 =>
        let batch :=
          FastProposal.stageBatch
            registry.identity.taskCanonicalId
            registry.referenceAlphabet
            state.fastProposalState
        if batch.stage != stage then
          throw (referenceProposalFailure
            "fast proposal frontier does not match the requested stage")
        let entries := batch.entries
        let serialized := serializedProposalEntries entries
        pure
          { realization
            stage
            entries
            serialized
            cumulativeRawOccurrences :=
              state.proposalCumulativeRawOccurrences +
                batch.decodedFormulaOccurrences
            cumulativeCanonicalFormulas :=
              state.proposalCumulativeCanonicalFormulas +
                entries.length
            emittedFormulas := entries.length
            generatorWorkUnits := batch.generatorWorkUnits
            freshTraversalNodes := batch.freshTraversalNodes
            freshNoFreshPrunes := batch.freshNoFreshPrunes
            freshTooShortPrunes := batch.freshTooShortPrunes
            nextFastState? := some batch.nextState }
    | .seededV1 =>
        let batch :=
          FastProposal.seededStageBatch
            registry.identity.taskCanonicalId
            registry.referenceAlphabet
            registry.seedLiterals
            state.seededProposalState
        if batch.stage != stage then
          throw (referenceProposalFailure
            "seeded proposal frontier does not match the requested stage")
        let entries := batch.entries
        let serialized := serializedProposalEntries entries
        pure
          { realization
            stage
            entries
            serialized
            cumulativeRawOccurrences :=
              state.proposalCumulativeRawOccurrences +
                batch.decodedFormulaOccurrences
            cumulativeCanonicalFormulas :=
              state.proposalCumulativeCanonicalFormulas +
                entries.length
            emittedFormulas := entries.length
            generatorWorkUnits := batch.generatorWorkUnits
            freshTraversalNodes := batch.freshTraversalNodes
            freshNoFreshPrunes := batch.freshNoFreshPrunes
            freshTooShortPrunes := batch.freshTooShortPrunes
            nextSeededState? := some batch.nextState }
    | .cappedV1 =>
        let batch :=
          FastProposal.cappedStageBatch
            registry.identity.taskCanonicalId
            registry.referenceAlphabet
            registry.seedLiterals
            (state.cappedProposalState?.getD
              (Enumerators.Capped.initialCappedState
                registry.seedLiterals))
        if batch.stage != stage then
          throw (referenceProposalFailure
            "capped proposal frontier does not match the requested stage")
        let entries := batch.entries
        let serialized := serializedProposalEntries entries
        pure
          { realization
            stage
            entries
            serialized
            cumulativeRawOccurrences :=
              state.proposalCumulativeRawOccurrences +
                batch.decodedFormulaOccurrences
            cumulativeCanonicalFormulas :=
              state.proposalCumulativeCanonicalFormulas +
                entries.length
            emittedFormulas := entries.length
            generatorWorkUnits := batch.generatorWorkUnits
            freshTraversalNodes := batch.freshTraversalNodes
            freshNoFreshPrunes := batch.freshNoFreshPrunes
            freshTooShortPrunes := batch.freshTooShortPrunes
            nextCappedState? := some batch.nextState }
  if hasDuplicateSourceId pending.entries then
    throw (referenceProposalFailure
      "proposal contains duplicate source identities")
  if pending.entries.any fun entry =>
      (registry.resolveSource entry.sourceId).isSome ||
        entry.sourceId.startsWith maintenanceWpPrefix ||
        entry.sourceId.startsWith wLayerPrefix ||
        entry.sourceId.startsWith wLayerWpPrefix ||
        state.referenceBindings.contains entry.sourceId then
    throw (referenceProposalFailure
      "proposal source identity collides with a reserved source")
  return pending

/- Admit exactly one page of one contiguous typed proposal wave. -/
private def registerReferenceProposal
    (registry : EncodingTaskRegistry A D)
    (state : EncodingWorkerState A D registry.schema)
    (request : Request) :
    Except ReferenceProposalFailure
      (EncodingWorkerState A D registry.schema × Lean.Json) := do
  let requestedVersion ←
    request.payload.getObjValAs? Nat "version" |>.mapError
      referenceProposalFailure
  if requestedVersion != FastProposal.protocolVersion then
    throw (referenceProposalFailure
      "unsupported proposal-page protocol version")
  let realizationId ←
    request.payload.getObjValAs? String "realization_id" |>.mapError
      referenceProposalFailure
  let realizationVersion ←
    request.payload.getObjValAs? Nat "realization_version" |>.mapError
      referenceProposalFailure
  let realization ←
    match FastProposal.Realization.parse?
        realizationId realizationVersion with
    | some realization => pure realization
    | none => throw (referenceProposalFailure
        "unsupported proposal realization")
  match state.proposalRealization? with
  | some fixed =>
      if fixed != realization then
        throw (referenceProposalFailure
          "proposal realization cannot change during a worker lifetime")
  | none => pure ()
  let stage ← request.payload.getObjValAs? Nat "stage" |>.mapError
    referenceProposalFailure
  if stage != state.proposalRevision then
    throw (referenceProposalFailure
      "reference-proposal stages must be contiguous")
  let cursor ← request.payload.getObjValAs? Nat "cursor" |>.mapError
    referenceProposalFailure
  if cursor != state.proposalCursor then
    throw (referenceProposalFailure
      "reference-proposal pages must be contiguous")
  let maximum ←
    request.payload.getObjValAs? Nat "max_response_bytes" |>.mapError
      referenceProposalFailure
  let pending ←
    match state.proposalPending? with
    | some pending =>
        if pending.realization != realization ||
            pending.stage != stage then
          throw (referenceProposalFailure
            "request does not match the cached proposal stage")
        pure pending
    | none =>
        if cursor != 0 then
          throw (referenceProposalFailure
            "a proposal stage must begin at cursor zero")
        prepareProposalStage registry state realization stage
  let (count, complete, _, payload) ←
    referenceProposalPage request realization stage cursor maximum
      pending.cumulativeRawOccurrences
      pending.cumulativeCanonicalFormulas
      pending.emittedFormulas
      pending.generatorWorkUnits pending.freshTraversalNodes
      pending.freshNoFreshPrunes pending.freshTooShortPrunes
      pending.serialized
  let nextState := if complete then
    let nextBindings := pending.entries.foldl
      (fun bindings entry =>
        bindings.insert entry.sourceId entry.formula)
      state.referenceBindings
    let nextFastState :=
      pending.nextFastState?.getD state.fastProposalState
    let nextSeededState :=
      pending.nextSeededState?.getD state.seededProposalState
    let nextCappedState? :=
      pending.nextCappedState? <|> state.cappedProposalState?
    { state with
      proposalRevision := state.proposalRevision + 1
      proposalCursor := 0
      proposalRealization? := some realization
      proposalPending? := none
      proposalCumulativeRawOccurrences :=
        pending.cumulativeRawOccurrences
      proposalCumulativeCanonicalFormulas :=
        pending.cumulativeCanonicalFormulas
      fastProposalState := nextFastState
      seededProposalState := nextSeededState
      cappedProposalState? := nextCappedState?
      referenceBindings := nextBindings }
  else
    { state with
      proposalCursor := cursor + count
      proposalRealization? := some realization
      proposalPending? := some pending }
  return (nextState, payload)

end Runtime
end Synthesis
end Whiel

------------------------------------------------------------
-- Request Dispatch and Persistent Loop
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Runtime

open EncodingProtocol

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable [LinearOrder A]
variable [LinearOrder D]
variable [SolverKey A]
variable [SolverKey D]
variable [Vampire.SolverName A]
variable [Vampire.SolverName D]

private def validateEnvelope
    (registry : EncodingTaskRegistry A D)
    (state : EncodingWorkerState A D registry.schema)
    (request : Request) : Except String Unit := do
  if request.formatVersion != formatVersion then
    throw "unsupported encoding-worker format version"
  if request.contextId != registry.identity.contextId then
    throw "wrong solver-encoding context"
  if request.semanticVersion != registry.identity.semanticVersion then
    throw "wrong semantic version"
  if request.encodingVersion != registry.identity.encodingVersion then
    throw "wrong solver-encoding version"
  if request.taskCanonicalId != registry.identity.taskCanonicalId then
    throw "wrong task canonical identity"
  if request.taskModule != registry.identity.taskModule then
    throw "wrong task module"
  if request.taskNamespace != registry.identity.taskNamespace then
    throw "wrong task namespace"
  if request.taskSourceSha256 != registry.identity.taskSourceSha256 then
    throw "wrong task source digest"
  if request.nameEnvRevision != state.nameEnvRevision then
    throw "request NameEnv revision is stale or ahead"
  if request.proposalRevision != state.proposalRevision then
    throw "request proposal revision is stale or ahead"

/- Dispatch one parsed request without mutating on failure. -/
def dispatchEncodingRequest
    (registry : EncodingTaskRegistry A D)
    (state : EncodingWorkerState A D registry.schema)
    (request : Request) : EncodingDispatch A D registry.schema :=
  match validateEnvelope registry state request with
  | .error message =>
      { state
        response := Response.error request state.nameEnvRevision
          "invalid_envelope" message
          (currentProposalRevision :=
            state.proposalRevision) }
  | .ok () =>
      match request.operation with
      | "ping" =>
          { state
            response := Response.ok request state.nameEnvRevision
              (Lean.Json.mkObj [("ready", Lean.Json.bool true)]) }
      | "extend_name_env" =>
          match extendNameEnv registry state request with
          | .error message =>
              { state
                response := Response.error request state.nameEnvRevision
                  "name_env_extension" message }
          | .ok (nextState, payload) =>
              { state := nextState
                response := Response.ok request
                  nextState.nameEnvRevision payload }
      | "register_reference_proposal" =>
          match registerReferenceProposal registry state request with
          | .error failure =>
              { state
                response := Response.error request
                  state.nameEnvRevision
                  failure.kind failure.message }
          | .ok (nextState, payload) =>
              { state := nextState
                response := Response.ok request
                  nextState.nameEnvRevision payload
                  (currentProposalRevision :=
                    nextState.proposalRevision) }
      | "ensure_w_layer" =>
          match ensureWLayer registry state request with
          | .error message =>
              { state
                response := Response.error request
                  state.nameEnvRevision
                  "w_layer_registration" message }
          | .ok (nextState, payload) =>
              { state := nextState
                response := Response.ok request
                  nextState.nameEnvRevision payload }
      | "prepare_bodies" =>
          match parseBodyRequests request.payload with
          | .error message =>
              { state
                response := Response.error request state.nameEnvRevision
                  "malformed_payload" message }
          | .ok bodyRequests =>
              match prepareSourceRequests
                  registry state bodyRequests with
              | .error message =>
                  { state
                    response := Response.error request
                      state.nameEnvRevision "body_preparation" message }
              | .ok bodies =>
                  { state
                    response := Response.ok request state.nameEnvRevision
                      (Lean.Json.mkObj
                        [("bodies", Lean.Json.arr
                          (bodies.map bodyDataJson).toArray)]) }
      | "prepare_maintenance_wps" =>
          match parseStrings request.payload "source_ids" with
          | .error message =>
              { state
                response := Response.error request state.nameEnvRevision
                  "malformed_payload" message }
          | .ok sourceIds =>
              match prepareMaintenanceWpRequests
                  registry state sourceIds with
              | .error message =>
                  { state
                    response := Response.error request
                      state.nameEnvRevision "body_preparation" message }
              | .ok bodies =>
                  { state
                    response := Response.ok request state.nameEnvRevision
                      (Lean.Json.mkObj
                        [("bodies", Lean.Json.arr
                          (bodies.map bodyDataJson).toArray)]) }
      | "prepare_support" =>
          match parseStrings request.payload "constant_keys" with
          | .error message =>
              { state
                response := Response.error request state.nameEnvRevision
                  "malformed_payload" message }
          | .ok constantKeys =>
              match prepareConstantKeys registry state constantKeys with
              | .error message =>
                  { state
                    response := Response.error request
                      state.nameEnvRevision "support_preparation" message }
              | .ok support =>
                  { state
                    response := Response.ok request state.nameEnvRevision
                      (supportDataJson support) }
      | "check_empty_counterexample" =>
          match parseEmptyEntailmentRequest request.payload with
          | .error message =>
              { state
                response := Response.error request state.nameEnvRevision
                  "malformed_payload" message }
          | .ok sourceRequest =>
              match checkEmptyEntailment
                  registry state sourceRequest with
              | .error message =>
                  { state
                    response := Response.error request
                      state.nameEnvRevision
                      "empty_counterexample_check" message }
              | .ok payload =>
                  { state
                    response := Response.ok request
                      state.nameEnvRevision payload }
      | "shutdown" =>
          { state
            response := Response.ok request state.nameEnvRevision
              (Lean.Json.mkObj [("stopped", Lean.Json.bool true)])
            stop := true }
      | operation =>
          { state
            response := Response.error request state.nameEnvRevision
              "unknown_operation" operation }

private def processFrame
    (registry : EncodingTaskRegistry A D)
    (state : EncodingWorkerState A D registry.schema)
    (payload : ByteArray) : EncodingDispatch A D registry.schema :=
  match String.fromUTF8? payload with
  | none =>
      { state
        response := Response.malformed registry.identity
          state.nameEnvRevision "request is not UTF-8"
          (currentProposalRevision :=
            state.proposalRevision) }
  | some text =>
      match Lean.Json.parse text with
      | .error message =>
          { state
            response := Response.malformed registry.identity
              state.nameEnvRevision message
              (currentProposalRevision :=
                state.proposalRevision) }
      | .ok json =>
          match Request.fromJson? json with
          | .error message =>
              { state
                response := Response.malformed registry.identity
                  state.nameEnvRevision message
                  (currentProposalRevision :=
                    state.proposalRevision) }
          | .ok request =>
              dispatchEncodingRequest registry state request

/- Run a bounded-frame worker on supplied streams. -/
def runEncodingWorkerOn
    (registry : EncodingTaskRegistry A D)
    (input output : IO.FS.Stream)
    (state : EncodingWorkerState A D registry.schema := {}) :
    IO UInt32 := do
  let mut current := state
  while true do
    let some payload ← readFrame input
      | return 0
    let dispatch := processFrame registry current payload
    writeJsonFrame output dispatch.response.toJson
    if dispatch.stop then
      return 0
    current := dispatch.state
  return 0

/- Run one task-specific registry over stdin/stdout. -/
def runEncodingWorker
    (registry : EncodingTaskRegistry A D) : IO UInt32 := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  runEncodingWorkerOn registry input output

end Runtime
end Synthesis
end Whiel
