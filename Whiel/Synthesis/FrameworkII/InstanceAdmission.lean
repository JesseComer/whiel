-- Author: Jesse Comer
import Whiel.Synthesis.Runtime.Task

/-
  Lean-owned admission for concrete source instances.

  `admitSourceInstance` accepts a strict JSON
  relation-record
  array, validates it against one exact source schema, and
  returns the resulting typed `Instance` with a canonical
  structural identity.

  `Lean.Json.obj` stores fields in a tree map, so duplicate
  object-field names have already been collapsed before this
  boundary sees them. Relation names therefore occur as data
  in an array of `{name, rows}` records, where duplicates
  remain observable and are rejected. A transport that must
  reject duplicate object-field spellings must do so before
  constructing `Lean.Json`.

  Key declarations include:
    * `Whiel.Synthesis.FrameworkII.InstanceAdmissionError`
    * `Whiel.Synthesis.FrameworkII.AdmittedSourceInstance`
    * `Whiel.Synthesis.FrameworkII.admitSourceInstance`
-/

------------------------------------------------------------
-- Admission Errors
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII

/- One deterministic source-instance rejection. -/
inductive InstanceAdmissionError where
| rootNotObject
| unexpectedRootFields
| relationsNotArray
| relationNotObject (index : Nat)
| unexpectedRelationFields (index : Nat)
| relationNameNotString (index : Nat)
| unknownRelation (index : Nat)
| duplicateRelation (index : Nat)
| rowsNotArray (index : Nat)
| rowNotArray
    (relationIndex : Nat)
    (rowIndex : Nat)
| wrongTupleArity
    (relationIndex : Nat)
    (rowIndex expected actual : Nat)
| invalidValue
    (relationIndex : Nat)
    (rowIndex columnIndex : Nat)
| duplicateTuple
    (relationIndex : Nat)
    (rowIndex : Nat)
| missingRelation
deriving DecidableEq, Repr

namespace InstanceAdmissionError

/- Stable machine-readable rejection class. -/
def kind : InstanceAdmissionError -> String
| .rootNotObject => "root_not_object"
| .unexpectedRootFields => "unexpected_root_fields"
| .relationsNotArray => "relations_not_array"
| .relationNotObject _ => "relation_not_object"
| .unexpectedRelationFields _ =>
    "unexpected_relation_fields"
| .relationNameNotString _ => "relation_name_not_string"
| .unknownRelation _ => "unknown_relation"
| .duplicateRelation _ => "duplicate_relation"
| .rowsNotArray _ => "rows_not_array"
| .rowNotArray _ _ => "row_not_array"
| .wrongTupleArity _ _ _ _ => "wrong_tuple_arity"
| .invalidValue _ _ _ => "invalid_value"
| .duplicateTuple _ _ => "duplicate_tuple"
| .missingRelation => "missing_relation"

/- Bounded explanation that never echoes source text. -/
def message : InstanceAdmissionError -> String
| .rootNotObject =>
    "source instance must be a JSON object"
| .unexpectedRootFields =>
    "source instance has unsupported fields"
| .relationsNotArray =>
    "source instance relations must be a JSON array"
| .relationNotObject _ =>
    "relation entry must be a JSON object"
| .unexpectedRelationFields _ =>
    "relation entry has unsupported fields"
| .relationNameNotString _ =>
    "relation name must be a JSON string"
| .unknownRelation _ =>
    "relation name is not in the source schema"
| .duplicateRelation _ =>
    "source relation appears more than once"
| .rowsNotArray _ =>
    "relation rows must be a JSON array"
| .rowNotArray _ _ =>
    "relation row must be a JSON array"
| .wrongTupleArity _ _ _ _ =>
    "relation row has the wrong tuple arity"
| .invalidValue _ _ _ =>
    "relation cell is not a valid domain value"
| .duplicateTuple _ _ =>
    "relation row duplicates an earlier tuple"
| .missingRelation =>
    "source instance omits a required relation"

/- Bounded structural location without submitted content. -/
def path : InstanceAdmissionError -> String
| .rootNotObject => "/instance"
| .unexpectedRootFields => "/instance"
| .relationsNotArray => "/instance/relations"
| .relationNotObject relationIndex =>
    "/instance/relations/" ++ toString relationIndex
| .unexpectedRelationFields relationIndex =>
    "/instance/relations/" ++ toString relationIndex
| .relationNameNotString relationIndex =>
    "/instance/relations/" ++ toString relationIndex ++
      "/name"
| .unknownRelation relationIndex =>
    "/instance/relations/" ++ toString relationIndex ++
      "/name"
| .duplicateRelation relationIndex =>
    "/instance/relations/" ++ toString relationIndex ++
      "/name"
| .rowsNotArray relationIndex =>
    "/instance/relations/" ++ toString relationIndex ++
      "/rows"
| .rowNotArray relationIndex rowIndex =>
    "/instance/relations/" ++ toString relationIndex ++
      "/rows/" ++ toString rowIndex
| .wrongTupleArity relationIndex rowIndex _ _ =>
    "/instance/relations/" ++ toString relationIndex ++
      "/rows/" ++ toString rowIndex
| .invalidValue relationIndex rowIndex columnIndex =>
    "/instance/relations/" ++ toString relationIndex ++
      "/rows/" ++ toString rowIndex ++ "/" ++
        toString columnIndex
| .duplicateTuple relationIndex rowIndex =>
    "/instance/relations/" ++ toString relationIndex ++
      "/rows/" ++ toString rowIndex
| .missingRelation => "/instance/relations"

end InstanceAdmissionError

end FrameworkII
end Synthesis
end Whiel

------------------------------------------------------------
-- Admitted Values
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII

variable {A D : Type}
variable [RelationNames A] [Domain D]

/-
  One exact schema-correct source instance and its canonical
  structural JSON identity. This value makes no claim that
  the instance is a counterexample.
-/
structure AdmittedSourceInstance
    (Gamma : UnnamedSchema A) where
  private mk ::
  value : Instance D Gamma
  canonicalIdentity : Lean.Json

end FrameworkII
end Synthesis
end Whiel

------------------------------------------------------------
-- Strict JSON Decoding
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII

open Runtime

variable {A D : Type}
variable [RelationNames A] [Domain D]

private structure DecodedRelation
    (Gamma : UnnamedSchema A) where
  symbol : Gamma.syms
  rows : FinRelation D (Gamma.arity symbol)

private def decodeCells
    (decodeValue : Lean.Json -> Except String D)
    (relationIndex : Nat)
    (rowIndex : Nat) :
    List Lean.Json -> Nat ->
      Except InstanceAdmissionError (List D)
| [], _ => .ok []
| cell :: cells, columnIndex =>
    match decodeValue cell with
    | .error _detail =>
        .error (.invalidValue relationIndex rowIndex
          columnIndex)
    | .ok value =>
        match decodeCells decodeValue relationIndex rowIndex
            cells (columnIndex + 1) with
        | .error error => .error error
        | .ok values => .ok (value :: values)

private def decodeRow
    (decodeValue : Lean.Json -> Except String D)
    (relationIndex : Nat)
    (rowIndex arity : Nat)
    (json : Lean.Json) :
    Except InstanceAdmissionError (Tuple D arity) := do
  let cells <- match json with
    | .arr cells => .ok cells
    | _ => .error (.rowNotArray relationIndex rowIndex)
  if cells.size != arity then
    throw (.wrongTupleArity relationIndex rowIndex arity
      cells.size)
  let values <- decodeCells decodeValue relationIndex
    rowIndex cells.toList 0
  match Tuple.ofList? arity values with
  | some tuple => return tuple
  | none =>
      throw (.wrongTupleArity relationIndex rowIndex arity
        values.length)

private def decodeRows
    (decodeValue : Lean.Json -> Except String D)
    (relationIndex : Nat)
    (arity : Nat) :
    List Lean.Json -> Nat -> FinRelation D arity ->
      Except InstanceAdmissionError (FinRelation D arity)
| [], _, relation => .ok relation
| row :: rows, rowIndex, relation =>
    match decodeRow decodeValue relationIndex rowIndex arity
        row with
    | .error error => .error error
    | .ok tuple =>
        if tuple ∈ relation then
          .error (.duplicateTuple relationIndex rowIndex)
        else
          decodeRows decodeValue relationIndex arity rows
            (rowIndex + 1) (insert tuple relation)

private def decodeRelation
    (Gamma : UnnamedSchema A)
    (resolveRelation : String -> Option A)
    (decodeValue : Lean.Json -> Except String D)
    (index : Nat)
    (json : Lean.Json) :
    Except InstanceAdmissionError
      (DecodedRelation (D := D) Gamma) := do
  let fields <- match json with
    | .obj fields => .ok fields
    | _ => .error (.relationNotObject index)
  if fields.keys != ["name", "rows"] then
    throw (.unexpectedRelationFields index)
  let nameJson <- match fields.get? "name" with
    | some value => .ok value
    | none => .error (.relationNameNotString index)
  let name <- match nameJson with
    | .str name => .ok name
    | _ => .error (.relationNameNotString index)
  let rawSymbol <- match resolveRelation name with
    | some symbol => .ok symbol
    | none => .error (.unknownRelation index)
  let symbol <- if hMem : rawSymbol ∈ Gamma.syms then
      .ok (⟨rawSymbol, hMem⟩ : Gamma.syms)
    else
      .error (.unknownRelation index)
  let rowsJson <- match fields.get? "rows" with
    | some value => .ok value
    | none => .error (.rowsNotArray index)
  let rowsArray <- match rowsJson with
    | .arr rows => .ok rows
    | _ => .error (.rowsNotArray index)
  let rows <- decodeRows decodeValue index
    (Gamma.arity symbol) rowsArray.toList 0 ∅
  return { symbol, rows }

private def decodeRelations
    (Gamma : UnnamedSchema A)
    (resolveRelation : String -> Option A)
    (decodeValue : Lean.Json -> Except String D) :
    List Lean.Json -> Nat -> Finset A -> Instance D Gamma ->
      Except InstanceAdmissionError
        (Finset A × Instance D Gamma)
| [], _, seen, instanceValue => .ok (seen, instanceValue)
| json :: relations, index, seen, instanceValue =>
    match decodeRelation Gamma resolveRelation decodeValue
        index json with
    | .error error => .error error
    | .ok relation =>
        if relation.symbol.1 ∈ seen then
          .error
            (.duplicateRelation index)
        else
          decodeRelations Gamma resolveRelation decodeValue
            relations (index + 1)
            (insert relation.symbol.1 seen)
            (Instance.update instanceValue relation.symbol
              relation.rows)

end FrameworkII
end Synthesis
end Whiel

------------------------------------------------------------
-- Canonical Structural Identity
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII

open Runtime

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable [SolverKey A] [SolverKey D]

@[reducible] private def solverKeyLinearOrder
    {alpha : Type}
    [SolverKey alpha] : LinearOrder alpha :=
  LinearOrder.lift' SolverKey.key
    SolverKey.key_injective

private def tupleIdentityJson
    {n : Nat}
    (tuple : Tuple D n) : Lean.Json :=
  Lean.Json.arr
    (tuple.toList.map
      (Lean.Json.str ∘ SolverKey.key)).toArray

private def relationIdentityJson
    {Gamma : UnnamedSchema A}
    (instanceValue : Instance D Gamma)
    (symbol : Gamma.syms) : Lean.Json :=
  letI : LinearOrder D := solverKeyLinearOrder
  Lean.Json.mkObj
    [ ("key", Lean.Json.str (SolverKey.key symbol.1)),
      ("arity", Lean.Json.num (Gamma.arity symbol)),
      ("rows", Lean.Json.arr
        ((instanceValue symbol).sort.map
          tupleIdentityJson).toArray) ]

private def instanceIdentityJson
    (Gamma : UnnamedSchema A)
    (instanceValue : Instance D Gamma) : Lean.Json :=
  letI : LinearOrder A := solverKeyLinearOrder
  Lean.Json.mkObj
    [ ("kind", Lean.Json.str "whiel_source_instance"),
      ("version", Lean.Json.num 1),
      ("relations", Lean.Json.arr
        (Gamma.syms.attach.sort.map
          (relationIdentityJson instanceValue)).toArray) ]

end FrameworkII
end Synthesis
end Whiel

------------------------------------------------------------
-- Source-Instance Admission
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII

open Runtime

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable [SolverKey A] [SolverKey D]

/-
  Admit one complete concrete instance over the exact source
  schema. The input shape is
  `{ "relations": [{ "name": ..., "rows": [...] }, ...] }`.
-/
def admitSourceInstance
    (Gamma : UnnamedSchema A)
    (resolveRelation : String -> Option A)
    (decodeValue : Lean.Json -> Except String D)
    (json : Lean.Json) :
    Except InstanceAdmissionError
      (AdmittedSourceInstance (D := D) Gamma) := do
  let fields <- match json with
    | .obj fields => .ok fields
    | _ => .error .rootNotObject
  if fields.keys != ["relations"] then
    throw .unexpectedRootFields
  let relationsJson <- match fields.get? "relations" with
    | some value => .ok value
    | none => .error .relationsNotArray
  let relations <- match relationsJson with
    | .arr relations => .ok relations
    | _ => .error .relationsNotArray
  let emptyInstance : Instance D Gamma := fun _ => ∅
  let (seen, instanceValue) <-
    decodeRelations Gamma resolveRelation decodeValue
      relations.toList 0 ∅ emptyInstance
  letI : LinearOrder A := solverKeyLinearOrder
  match (Gamma.syms \ seen).sort with
  | _missing :: _ =>
      throw .missingRelation
  | [] =>
      return AdmittedSourceInstance.mk instanceValue
        (instanceIdentityJson Gamma instanceValue)

end FrameworkII
end Synthesis
end Whiel
