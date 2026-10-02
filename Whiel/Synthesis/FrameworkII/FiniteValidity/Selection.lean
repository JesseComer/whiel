-- Author: Jesse Comer
import Whiel.Synthesis.FrameworkII.FiniteValidity.Registry

/-
  Lean-owned admission for opaque finite-validity binding
  requests over an explicit schema and caller-owned target
  codec. The retained library does not know about live F2
  tasks or clause representations.
-/

------------------------------------------------------------
-- Strict JSON Helpers
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FiniteValidity
namespace Selection

open Concrete
open Runtime

private def requireObjectFields
    (json : Lean.Json)
    (expected : List String) : Except String Unit := do
  let fields <- match json with
    | .obj fields => .ok fields
    | _ => .error "value must be a JSON object"
  if fields.keys != expected then
    throw "object fields differ from the selection contract"

private def stringField
    (json : Lean.Json)
    (name : String) : Except String String :=
  json.getObjValAs? String name

private def natField
    (json : Lean.Json)
    (name : String) : Except String Nat :=
  json.getObjValAs? Nat name

private def relationRow
    {A : Type}
    [RelationNames A]
    [Runtime.SolverKey A]
    (Gamma : UnnamedSchema A)
    (relation : Gamma.syms) : Lean.Json :=
  Lean.Json.mkObj
    [ ("key", Lean.Json.str
        (SolverKey.key relation.1)),
      ("arity", Lean.Json.num (Gamma.arity relation)) ]

private def resolveRelation
    {A : Type}
    [RelationNames A]
    [LinearOrder A]
    [Runtime.SolverKey A]
    (Gamma : UnnamedSchema A)
    (key : String) : Except String Gamma.syms :=
  match Gamma.syms.attach.sort.find?
      (fun relation => SolverKey.key relation.1 = key) with
  | some relation => .ok relation
  | none =>
      .error "relation key is outside the task scope"

private def resolveBinaryRelation
    {A : Type}
    [RelationNames A]
    [LinearOrder A]
    [Runtime.SolverKey A]
    (Gamma : UnnamedSchema A)
    (key : String) : Except String
      {relation : Gamma.syms //
        Gamma.arity relation = 2} := do
  let relation <- resolveRelation Gamma key
  if arity : Gamma.arity relation = 2 then
    return ⟨relation, arity⟩
  else
    throw "finite-validity relation binding is not binary"

end Selection
end FiniteValidity
end FrameworkII
end Synthesis
end Whiel

------------------------------------------------------------
-- Explicit Target Codec
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FiniteValidity
namespace Selection

/-
  A caller-owned target boundary. The retained library knows
  neither F2 tasks nor clause representations.
-/
structure TargetCodec (Target : Type) where
  requestIdentity : Target -> Lean.Json
  checkedIdentity : Lean.Json -> Target -> Lean.Json
  decodeRequest : Lean.Json -> Except String Target
  decodeCheckedIdentity : Lean.Json -> Lean.Json ->
    Except String Target

end Selection
end FiniteValidity
end FrameworkII
end Synthesis
end Whiel

------------------------------------------------------------
-- Checked Entry Bindings
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FiniteValidity
namespace Selection

open Concrete
open Runtime

inductive Binding
    {A : Type}
    [RelationNames A]
    (Gamma : UnnamedSchema A) where
| epsilonMax
    (edge : {relation : Gamma.syms //
      Gamma.arity relation = 2})
    (domainSource : {relation : Gamma.syms //
      Gamma.arity relation = 2})
| strictLinearOrderGreatest
    (relation : {symbol : Gamma.syms //
      Gamma.arity symbol = 2})

namespace Binding

def entry
    {A : Type}
    [RelationNames A]
    {Gamma : UnnamedSchema A} :
    Binding Gamma -> Registry.Entry
| .epsilonMax _ _ => .epsilonMax
| .strictLinearOrderGreatest _ =>
    .strictLinearOrderGreatest

/- The exact RelCalc sentence denoted by a checked binding. -/
def sentence
    {A : Type}
    [RelationNames A]
    {Gamma : UnnamedSchema A} :
    Binding Gamma -> RelCalc.Sentence Data Gamma
| .epsilonMax edge domainSource =>
    Library.FiniteOrder.FV000001.sentence
      ⟨edge.1, edge.2⟩ ⟨domainSource.1, domainSource.2⟩
| .strictLinearOrderGreatest relation =>
    Library.FiniteOrder.FV000002.sentence
      ⟨relation.1, relation.2⟩

def instantiationIdentity
    {A : Type}
    [RelationNames A]
    [Runtime.SolverKey A]
    (Gamma : UnnamedSchema A) :
    Binding Gamma -> Lean.Json
| .epsilonMax edge domainSource =>
    Lean.Json.mkObj
      [ ("kind", Lean.Json.str
          "epsilon_max_binary_domain"),
        ("edge_relation", relationRow Gamma edge.1),
        ("domain_source_relation",
          relationRow Gamma domainSource.1),
        ("formal_variable", Lean.Json.num 0),
        ("witness_variable", Lean.Json.num 3) ]
| .strictLinearOrderGreatest relation =>
    Lean.Json.mkObj
      [ ("kind", Lean.Json.str
          "strict_linear_order_relation"),
        ("relation", relationRow Gamma relation.1) ]

def requestIdentity
    {A : Type}
    [RelationNames A]
    [Runtime.SolverKey A]
    (Gamma : UnnamedSchema A) :
    Binding Gamma -> Lean.Json
| .epsilonMax edge domainSource =>
    Lean.Json.mkObj
      [ ("kind", Lean.Json.str
          "epsilon_max_binary_domain"),
        ("edge_relation_key", Lean.Json.str
          (SolverKey.key edge.1.1)),
        ("domain_relation_key", Lean.Json.str
          (SolverKey.key domainSource.1.1)) ]
| .strictLinearOrderGreatest relation =>
    Lean.Json.mkObj
      [ ("kind", Lean.Json.str
          "strict_linear_order_relation"),
        ("relation_key", Lean.Json.str
          (SolverKey.key relation.1.1)) ]

private def relationKeys
    {A : Type}
    [RelationNames A]
    [LinearOrder A]
    [Runtime.SolverKey A]
    {Gamma : UnnamedSchema A}
    (binding : Binding Gamma) : Array Lean.Json :=
  (SolverKey.sortedKeys binding.sentence.1.relNames |>.map
    Lean.Json.str).toArray

def checkedIdentity
    {A : Type}
    [RelationNames A]
    [LinearOrder A]
    [Runtime.SolverKey A]
    (Gamma : UnnamedSchema A)
    (binding : Binding Gamma) : Lean.Json :=
  Lean.Json.mkObj
    [ ("kind", Lean.Json.str
        "whiel_finite_validity_checked_binding"),
      ("version", Lean.Json.num 1),
      ("entry_id", Lean.Json.str binding.entry.id),
      ("instantiation_identity",
        binding.instantiationIdentity Gamma),
      ("exact_relation_keys", Lean.Json.arr
        binding.relationKeys),
      ("exact_constant_keys", Lean.Json.arr
        ((SolverKey.sortedKeys
          binding.sentence.constants |>.map
            Lean.Json.str).toArray)) ]

end Binding

structure Admitted
    {A : Type}
    [RelationNames A]
    (Gamma : UnnamedSchema A)
    (Target : Type) where
  target : Target
  binding : Binding Gamma

namespace Admitted

def entry
    {A Target : Type}
    [RelationNames A]
    {Gamma : UnnamedSchema A}
    (selection : Admitted Gamma Target) : Registry.Entry :=
  selection.binding.entry

def identity
    {A Target : Type}
    [RelationNames A]
    [LinearOrder A]
    [Runtime.SolverKey A]
    {Gamma : UnnamedSchema A}
    (codec : TargetCodec Target)
    (scopeIdentity : Lean.Json)
    (selection : Admitted Gamma Target) : Lean.Json :=
  let bindingIdentity :=
    selection.binding.checkedIdentity Gamma
  let requestIdentity := Lean.Json.mkObj
    [ ("entry_id", Lean.Json.str selection.entry.id),
      ("target", codec.requestIdentity selection.target),
      ("instantiation",
        selection.binding.requestIdentity Gamma) ]
  Lean.Json.mkObj
    [ ("kind", Lean.Json.str
        "whiel_finite_validity_selection"),
      ("version", Lean.Json.num 2),
      ("scope_identity", scopeIdentity),
      ("registry_identity", Registry.identity),
      ("entry_identity", selection.entry.identity),
      ("target_identity",
        codec.checkedIdentity scopeIdentity
          selection.target),
      ("request_identity", requestIdentity),
      ("binding_identity", bindingIdentity),
      ("binding_digest", Lean.Json.str
        (CanonicalDigest.jsonSha256 bindingIdentity)) ]

def orderKey
    {A Target : Type}
    [RelationNames A]
    [LinearOrder A]
    [Runtime.SolverKey A]
    {Gamma : UnnamedSchema A}
    (codec : TargetCodec Target)
    (scopeIdentity : Lean.Json)
    (selection : Admitted Gamma Target) : String :=
  CanonicalDigest.jsonSha256
    (selection.identity codec scopeIdentity)

end Admitted

end Selection
end FiniteValidity
end FrameworkII
end Synthesis
end Whiel

------------------------------------------------------------
-- Raw Request Admission
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FiniteValidity
namespace Selection

open Concrete
open Runtime

private def decodeRawBinding
    {A : Type}
    [RelationNames A]
    [LinearOrder A]
    [Runtime.SolverKey A]
    (Gamma : UnnamedSchema A)
    (entry : Registry.Entry)
    (json : Lean.Json) :
    Except String (Binding Gamma) := do
  match entry with
  | .epsilonMax =>
      requireObjectFields json
        ["domain_relation_key", "edge_relation_key",
          "kind"]
      if (← stringField json "kind") !=
          "epsilon_max_binary_domain" then
        throw "epsilon_max instantiation has the wrong kind"
      let edge <- resolveBinaryRelation Gamma
        (← stringField json "edge_relation_key")
      let domainSource <- resolveBinaryRelation Gamma
        (← stringField json "domain_relation_key")
      return .epsilonMax edge domainSource
  | .strictLinearOrderGreatest =>
      requireObjectFields json ["kind", "relation_key"]
      if (← stringField json "kind") !=
          "strict_linear_order_relation" then
        throw "strict-order instantiation has the wrong kind"
      let relation <- resolveBinaryRelation Gamma
        (← stringField json "relation_key")
      return .strictLinearOrderGreatest relation

private def decodeRaw
    {A Target : Type}
    [RelationNames A]
    [LinearOrder A]
    [Runtime.SolverKey A]
    (Gamma : UnnamedSchema A)
    (codec : TargetCodec Target)
    (json : Lean.Json) :
    Except String (Admitted Gamma Target) := do
  requireObjectFields json
    ["entry_id", "instantiation", "target"]
  let entry <- Registry.entryFromId
    (← stringField json "entry_id")
  let binding <- decodeRawBinding Gamma entry
    (json.getObjValD "instantiation")
  let targetJson := json.getObjValD "target"
  let target <- codec.decodeRequest targetJson
  if codec.requestIdentity target != targetJson then
    throw "finite-validity target request is not canonical"
  return ⟨target, binding⟩

end Selection
end FiniteValidity
end FrameworkII
end Synthesis
end Whiel

------------------------------------------------------------
-- Identity Replay
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FiniteValidity
namespace Selection

open Concrete
open Runtime

private def decodeRelationRow
    {A : Type}
    [RelationNames A]
    [LinearOrder A]
    [Runtime.SolverKey A]
    (Gamma : UnnamedSchema A)
    (json : Lean.Json) : Except String
      {relation : Gamma.syms //
        Gamma.arity relation = 2} := do
  requireObjectFields json ["arity", "key"]
  if (← natField json "arity") != 2 then
    throw "finite-validity relation row has the wrong arity"
  let relation <- resolveBinaryRelation Gamma
    (← stringField json "key")
  if relationRow Gamma relation.1 != json then
    throw "finite-validity relation row is not canonical"
  return relation

private def decodeBindingIdentity
    {A : Type}
    [RelationNames A]
    [LinearOrder A]
    [Runtime.SolverKey A]
    (Gamma : UnnamedSchema A)
    (entry : Registry.Entry)
    (json : Lean.Json) :
    Except String (Binding Gamma) := do
  requireObjectFields json
    ["entry_id", "exact_constant_keys",
      "exact_relation_keys", "instantiation_identity",
      "kind", "version"]
  if (← stringField json "kind") !=
        "whiel_finite_validity_checked_binding" ||
      (← natField json "version") != 1 ||
      (← stringField json "entry_id") != entry.id then
    throw "finite-validity binding identity is unsupported"
  let instantiation :=
    json.getObjValD "instantiation_identity"
  let binding <- match entry with
    | .epsilonMax => do
        requireObjectFields instantiation
          ["domain_source_relation", "edge_relation",
            "formal_variable", "kind",
            "witness_variable"]
        if (← stringField instantiation "kind") !=
              "epsilon_max_binary_domain" ||
            (← natField instantiation
              "formal_variable") != 0 ||
            (← natField instantiation
              "witness_variable") != 3 then
          throw "epsilon_max identity is unsupported"
        let edge <- decodeRelationRow Gamma
          (instantiation.getObjValD "edge_relation")
        let domainSource <- decodeRelationRow Gamma
          (instantiation.getObjValD
            "domain_source_relation")
        pure (Binding.epsilonMax edge domainSource)
    | .strictLinearOrderGreatest => do
        requireObjectFields instantiation
          ["kind", "relation"]
        if (← stringField instantiation "kind") !=
            "strict_linear_order_relation" then
          throw "strict-order identity is unsupported"
        let relation <- decodeRelationRow Gamma
          (instantiation.getObjValD "relation")
        pure (Binding.strictLinearOrderGreatest relation)
  if binding.checkedIdentity Gamma != json then
    throw "finite-validity binding identity is not canonical"
  return binding

private def decodeIdentity
    {A Target : Type}
    [RelationNames A]
    [LinearOrder A]
    [Runtime.SolverKey A]
    (Gamma : UnnamedSchema A)
    (codec : TargetCodec Target)
    (scopeIdentity json : Lean.Json) :
    Except String (Admitted Gamma Target) := do
  requireObjectFields json
    ["binding_digest", "binding_identity",
      "entry_identity", "kind", "registry_identity",
      "request_identity", "scope_identity",
      "target_identity", "version"]
  if (← stringField json "kind") !=
      "whiel_finite_validity_selection" then
    throw "finite-validity selection identity has the wrong kind"
  if (← natField json "version") != 2 then
    throw "finite-validity selection identity has the wrong version"
  if json.getObjValD "scope_identity" != scopeIdentity then
    throw "finite-validity selection has the wrong task scope"
  if json.getObjValD "registry_identity" !=
      Registry.identity then
    throw "finite-validity selection has the wrong registry"
  let entryIdentity := json.getObjValD "entry_identity"
  let entryId <- stringField entryIdentity "entry_id"
  let entry <- Registry.entryFromId entryId
  if entry.identity != entryIdentity then
    throw "finite-validity selection has the wrong entry"
  let bindingIdentity :=
    json.getObjValD "binding_identity"
  if (← stringField json "binding_digest") !=
      CanonicalDigest.jsonSha256 bindingIdentity then
    throw "finite-validity binding digest is detached"
  let binding <- decodeBindingIdentity Gamma entry
    bindingIdentity
  let targetIdentity := json.getObjValD "target_identity"
  let target <- codec.decodeCheckedIdentity scopeIdentity
    targetIdentity
  if codec.checkedIdentity scopeIdentity target !=
      targetIdentity then
    throw "finite-validity target identity is not canonical"
  let selection : Admitted Gamma Target :=
    ⟨target, binding⟩
  let requestIdentity := Lean.Json.mkObj
    [ ("entry_id", Lean.Json.str selection.entry.id),
      ("target", codec.requestIdentity selection.target),
      ("instantiation",
        selection.binding.requestIdentity Gamma) ]
  if json.getObjValD "request_identity" !=
      requestIdentity then
    throw "finite-validity selection changed its request"
  if selection.identity codec scopeIdentity != json then
    throw "finite-validity selection identity is not canonical"
  return selection

private def strictlyOrdered
    {A Target : Type}
    [RelationNames A]
    [LinearOrder A]
    [Runtime.SolverKey A]
    {Gamma : UnnamedSchema A}
    (codec : TargetCodec Target)
    (scopeIdentity : Lean.Json) :
    List (Admitted Gamma Target) -> Bool
| [] | [_] => true
| first :: second :: rest =>
    first.orderKey codec scopeIdentity <
        second.orderKey codec scopeIdentity &&
      strictlyOrdered codec scopeIdentity (second :: rest)

def admitRawList
    {A Target : Type}
    [RelationNames A]
    [LinearOrder A]
    [Runtime.SolverKey A]
    (Gamma : UnnamedSchema A)
    (codec : TargetCodec Target)
    (scopeIdentity : Lean.Json)
    (values : List Lean.Json) :
    Except String (List (Admitted Gamma Target)) := do
  let selections <- values.mapM (decodeRaw Gamma codec)
  if !(selections.map
      (Admitted.orderKey codec scopeIdentity)).Nodup then
    throw "finite-validity selections contain a duplicate"
  let ordered := selections.mergeSort fun left right =>
    decide (left.orderKey codec scopeIdentity <=
      right.orderKey codec scopeIdentity)
  return ordered

def listIdentity
    {A Target : Type}
    [RelationNames A]
    [LinearOrder A]
    [Runtime.SolverKey A]
    {Gamma : UnnamedSchema A}
    (codec : TargetCodec Target)
    (scopeIdentity : Lean.Json)
    (selections : List (Admitted Gamma Target)) :
    Lean.Json :=
  Lean.Json.mkObj
    [ ("kind", Lean.Json.str
        "whiel_finite_validity_selection_list"),
      ("version", Lean.Json.num 2),
      ("scope_identity", scopeIdentity),
      ("registry_identity", Registry.identity),
      ("ordered_selections", Lean.Json.arr
        (selections.map
          (Admitted.identity codec
            scopeIdentity)).toArray) ]

def decodeListIdentity
    {A Target : Type}
    [RelationNames A]
    [LinearOrder A]
    [Runtime.SolverKey A]
    (Gamma : UnnamedSchema A)
    (codec : TargetCodec Target)
    (scopeIdentity json : Lean.Json) :
    Except String (List (Admitted Gamma Target)) := do
  requireObjectFields json
    ["kind", "ordered_selections", "registry_identity",
      "scope_identity", "version"]
  if (← stringField json "kind") !=
        "whiel_finite_validity_selection_list" ||
      (← natField json "version") != 2 then
    throw "finite-validity selection-list identity is unsupported"
  if json.getObjValD "scope_identity" != scopeIdentity then
    throw "finite-validity selection list has the wrong scope"
  if json.getObjValD "registry_identity" !=
      Registry.identity then
    throw "finite-validity selection list has the wrong registry"
  let values <-
    match json.getObjValD "ordered_selections" with
    | .arr values => .ok values.toList
    | _ => .error "ordered_selections must be an array"
  let selections <- values.mapM
    (decodeIdentity Gamma codec scopeIdentity)
  if !strictlyOrdered codec scopeIdentity selections then
    throw "finite-validity selections are not strictly ordered"
  if listIdentity codec scopeIdentity selections !=
      json then
    throw "finite-validity selection-list identity is not canonical"
  return selections

end Selection
end FiniteValidity
end FrameworkII
end Synthesis
end Whiel
