-- Author: Jesse Comer
import Databases.FinStruct.Basic
import Whiel.AssertExpr.Entailment
import Whiel.Synthesis.FrameworkII.InstanceAdmission
import Whiel.Synthesis.Runtime.CanonicalDigest

/-
  Library-free validation of one finite countermodel for an
  ordinary Framework-II entailment.

  The decoder has no carrier or row bound: a solver's
  countermodel is decoded at whatever size the solver
  produced it, and a countermodel this decoder cannot read is
  a fault of the evidence, never an inconclusive outcome.

  `Refutation.validate` checks the exact entailment
  constants. `Refutation.validateWithConstants` also permits
  a checked superset for temporary callers that prepare a
  larger FOL signature. Both return
  `Refutation.Validation`, whose model and identities are
  typed by the exact schema and constants.
-/

------------------------------------------------------------
-- Checked Validation Result
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace Refutation

open Concrete
open Runtime

variable {A : Type}
variable [RelationNames A]

/- One checked ordinary finite-model validation. -/
structure Validation
    (Gamma : UnnamedSchema A)
    (constants : Finset Data) where
  model : FinStruct Data
    (Gamma.toFOLSignature constants)
  carrierIdentity : Lean.Json
  interpretationIdentity : Lean.Json
  axiomsHold : Bool
  conjectureHolds : Bool

namespace Validation

/- Whether the interpretation refutes the base job. -/
def validated
    {Gamma : UnnamedSchema A}
    {constants : Finset Data}
    (validation : Validation Gamma constants) : Bool :=
  validation.axiomsHold &&
    !validation.conjectureHolds

/- Exact identity of an ordinary refutation validation. -/
def identity
    {Gamma : UnnamedSchema A}
    {constants : Finset Data}
    (validation : Validation Gamma constants)
    (obligationIdentity : Lean.Json) : Lean.Json :=
  Lean.Json.mkObj
    [ ("kind", Lean.Json.str
        "whiel_framework_ii_base_refutation_validation"),
      ("version", Lean.Json.num 1),
      ("obligation_identity", obligationIdentity),
      ("interpretation_identity",
        validation.interpretationIdentity),
      ("axioms_hold", Lean.Json.bool
        validation.axiomsHold),
      ("conjecture_holds", Lean.Json.bool
        validation.conjectureHolds),
      ("validated_refutation", Lean.Json.bool
        validation.validated) ]

/- Worker response fields for an ordinary refutation. -/
def fields
    {Gamma : UnnamedSchema A}
    {constants : Finset Data}
    (validation : Validation Gamma constants)
    (obligationIdentity : Lean.Json) :
    List (String × Lean.Json) :=
  let validationIdentity :=
    validation.identity obligationIdentity
  [ ("obligation_identity", obligationIdentity),
    ("obligation_digest", Lean.Json.str
      (CanonicalDigest.jsonSha256 obligationIdentity)),
    ("carrier_identity", validation.carrierIdentity),
    ("carrier_digest", Lean.Json.str
      (CanonicalDigest.jsonSha256
        validation.carrierIdentity)),
    ("interpretation_identity",
      validation.interpretationIdentity),
    ("interpretation_digest", Lean.Json.str
      (CanonicalDigest.jsonSha256
        validation.interpretationIdentity)),
    ("validation_identity", validationIdentity),
    ("validation_digest", Lean.Json.str
      (CanonicalDigest.jsonSha256 validationIdentity)),
    ("axioms_hold", Lean.Json.bool
      validation.axiomsHold),
    ("conjecture_holds", Lean.Json.bool
      validation.conjectureHolds),
    ("validated_refutation", Lean.Json.bool
      validation.validated),
    ("validation_definition", Lean.Json.str
      "QFEntailment.Valid") ]

end Validation

end Refutation
end FrameworkII
end Synthesis
end Whiel

------------------------------------------------------------
-- Strict Interpretation Decoding
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace Refutation

open Concrete
open Runtime

private def requireObjectFields
    (json : Lean.Json)
    (expected : List String) : Except String Unit := do
  let fields <- match json with
    | .obj fields => .ok fields
    | _ => .error "value must be a JSON object"
  if fields.keys != expected then
    throw "object fields differ from the operation contract"

private def arrayField
    (json : Lean.Json)
    (name : String) : Except String (Array Lean.Json) := do
  match json.getObjValD name with
  | .arr values => return values
  | _ => throw s!"{name} must be an array"

private def stringArrayField
    (json : Lean.Json)
    (name : String) : Except String (List String) := do
  let values <- arrayField json name
  values.toList.mapM fun value =>
    match value with
    | .str text => .ok text
    | _ => .error s!"{name} must contain only strings"

private def stringsStrictlyIncreasing :
    List String -> Bool
| [] | [_] => true
| left :: right :: values =>
    left < right &&
      stringsStrictlyIncreasing (right :: values)

private def decodeCarrier
    (interpretation : Lean.Json) :
    Except String (List Data) := do
  let keys <- stringArrayField interpretation
    "carrier_keys"
  if keys.isEmpty then
    throw "finite interpretation carrier must be nonempty"
  if !stringsStrictlyIncreasing keys then
    throw ("finite interpretation carrier keys are not " ++
      "canonical and unique")
  keys.mapM fun key => do
    let some value := SolverKey.dataOfKey? key
      | throw ("finite interpretation carrier has an " ++
          "invalid value key")
    if SolverKey.key value != key then
      throw ("finite interpretation carrier has a " ++
        "noncanonical value key")
    return value

private def validateRelationShape
    (relation : Lean.Json) : Except String Unit := do
  requireObjectFields relation ["name", "rows"]
  let _ <- arrayField relation "rows"
  return ()

private def validateRelationCells
    (carrier : List Data)
    (relation : Lean.Json) : Except String Unit := do
  let rows <- arrayField relation "rows"
  for row in rows do
    let cells <- match row with
      | .arr cells => .ok cells
      | _ => .error ("finite interpretation row " ++
          "must be an array")
    for cell in cells do
      let key <- match cell with
        | .str key => .ok key
        | _ => .error ("finite interpretation cells " ++
            "must be value-key strings")
      let some value := SolverKey.dataOfKey? key
        | throw ("finite interpretation cell has an " ++
            "invalid value key")
      if SolverKey.key value != key then
        throw ("finite interpretation cell has a " ++
          "noncanonical value key")
      if value ∉ carrier then
        throw ("finite interpretation cell lies outside " ++
          "its carrier")

private def resolveRelationKey
    {A : Type}
    [RelationNames A]
    [LinearOrder A]
    [SolverKey A]
    (Gamma : UnnamedSchema A)
    (key : String) : Option A :=
  Gamma.syms.sort.find? fun relation =>
    SolverKey.key relation == key

private def decodeCellKey
    (json : Lean.Json) : Except String Data := do
  let key <- match json with
    | .str key => .ok key
    | _ => .error ("finite interpretation cell " ++
        "must be a string")
  let some value := SolverKey.dataOfKey? key
    | throw ("finite interpretation cell has an " ++
        "invalid key")
  if SolverKey.key value != key then
    throw ("finite interpretation cell has a " ++
      "noncanonical key")
  return value

private def relationRowsJson
    {A : Type}
    [RelationNames A]
    [LinearOrder A]
    [SolverKey A]
    (Gamma : UnnamedSchema A) : Lean.Json :=
  let rows := Gamma.syms.attach.sort.map fun relation =>
    Lean.Json.mkObj
      [ ("key", Lean.Json.str
          (SolverKey.key relation.1)),
        ("arity", Lean.Json.num
          (Gamma.arity relation)) ]
  Lean.Json.arr rows.toArray

end Refutation
end FrameworkII
end Synthesis
end Whiel

------------------------------------------------------------
-- Direct Instance Decoding
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace Refutation

open Concrete
open Runtime

variable {A : Type}
variable [RelationNames A]
variable [LinearOrder A]
variable [SolverKey A]

/-
  One finite instance decoded from JSON without binding to
  any particular entailment. Reused by ordinary refutation
  validation and by direct clause evaluation.
-/
structure DecodedInstance
    (Gamma : UnnamedSchema A) where
  carrier : List Data
  value : Instance Data Gamma
  instanceIdentity : Lean.Json

/-
  Decode one finite interpretation over an exact schema,
  applying the same carrier and row-count caps as ordinary
  refutation validation.
-/
def decodeInstance
    (Gamma : UnnamedSchema A)
    (interpretation : Lean.Json) :
    Except String (DecodedInstance Gamma) := do
  requireObjectFields interpretation
    ["carrier_keys", "relations"]
  let carrier <- decodeCarrier interpretation
  let relationValues <- arrayField interpretation
    "relations"
  relationValues.toList.forM validateRelationShape
  relationValues.toList.forM
    (validateRelationCells carrier)
  let instanceJson := Lean.Json.mkObj
    [("relations", Lean.Json.arr relationValues)]
  let admitted <- match admitSourceInstance Gamma
      (resolveRelationKey Gamma) decodeCellKey
      instanceJson with
    | .ok admitted => .ok admitted
    | .error error =>
        .error ("finite interpretation is not a " ++
          "complete instance: " ++ error.message)
  return {
    carrier := carrier
    value := admitted.value
    instanceIdentity := admitted.canonicalIdentity
  }

end Refutation
end FrameworkII
end Synthesis
end Whiel

------------------------------------------------------------
-- Ordinary Refutation Validation
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace Refutation

open Concrete
open Runtime

variable {A : Type}
variable [RelationNames A]
variable [LinearOrder A]
variable [SolverKey A]
variable {Gamma : UnnamedSchema A}

/-
  Validate with an explicit constant superset. This supports
  callers that temporarily construct a larger FOL signature.
-/
def validateWithConstants
    (E : QFEntailment (D := Data) Gamma)
    (constants : Finset Data)
    (interpretation : Lean.Json) :
    Except String (Validation Gamma constants) := do
  if !(E.constants ⊆ constants) then
    throw "validation constants omit an obligation constant"
  let decoded <- decodeInstance Gamma interpretation
  for constant in constants.sort do
    if constant ∉ decoded.carrier then
      throw ("obligation constant lies outside the " ++
        "finite carrier")
  let relations :
      (relation : Signature.Rel
        (Gamma.toFOLSignature constants)) ->
        FinRelation Data
          ((Gamma.toFOLSignature constants).arity
            relation) :=
    fun relation => decoded.value relation
  let functions :
      (function : Signature.Fun
        (Gamma.toFOLSignature constants)) ->
        Tuple Data
          ((Gamma.toFOLSignature constants).funArity
            function) -> Data :=
    fun function _ => function.1
  let some model := FinStruct.mk? decoded.carrier.toFinset
      relations functions
    | throw ("finite interpretation is not closed over " ++
        "its carrier")
  let axiomsHold := E.axioms.all fun formula =>
    decide (formula.eval decoded.value)
  let conjectureHolds :=
    decide (E.conjecture.eval decoded.value)
  let carrierIdentity := Lean.Json.mkObj
    [ ("kind", Lean.Json.str
        "whiel_framework_ii_finite_carrier"),
      ("version", Lean.Json.num 1),
      ("carrier_keys", Lean.Json.arr
        ((decoded.carrier.map fun value => Lean.Json.str
          (SolverKey.key value))).toArray) ]
  let interpretationIdentity := Lean.Json.mkObj
    [ ("kind", Lean.Json.str
        "whiel_framework_ii_finite_interpretation"),
      ("version", Lean.Json.num 1),
      ("schema_relations", relationRowsJson Gamma),
      ("carrier_identity", carrierIdentity),
      ("instance_identity",
        decoded.instanceIdentity) ]
  return {
    model := model
    carrierIdentity := carrierIdentity
    interpretationIdentity := interpretationIdentity
    axiomsHold := axiomsHold
    conjectureHolds := conjectureHolds
  }

/- Validate using exactly the base entailment constants. -/
def validate
    (E : QFEntailment (D := Data) Gamma)
    (interpretation : Lean.Json) :
    Except String (Validation Gamma E.constants) :=
  validateWithConstants E E.constants interpretation

end Refutation
end FrameworkII
end Synthesis
end Whiel
