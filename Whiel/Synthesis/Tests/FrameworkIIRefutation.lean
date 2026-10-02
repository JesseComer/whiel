-- Author: Jesse Comer
import Whiel.Synthesis.FrameworkII.Refutation

/- Focused checks for ordinary F2 refutation validation. -/

set_option linter.hashCommand false

namespace Whiel
namespace Synthesis
namespace Tests
namespace FrameworkIIRefutation

open Concrete
open FrameworkII
open Runtime

private inductive TestRelation
| row
deriving DecidableEq, Repr

private instance : RelationNames TestRelation where
  decEq := inferInstance
  repr := inferInstance

private def relationKey : TestRelation -> String
| .row => "rel:row"

private theorem relationKey_injective :
    Function.Injective relationKey := by
  intro left right _
  cases left
  cases right
  rfl

private instance : LinearOrder TestRelation :=
  LinearOrder.lift' relationKey
    relationKey_injective

private instance : SolverKey TestRelation where
  key := relationKey
  key_injective := relationKey_injective

private def schema : UnnamedSchema TestRelation where
  syms := {.row}
  arity := fun _ => 1

private def entailment :
    QFEntailment (D := Data) schema where
  axioms := [QFAssertExpr.«true»]
  conjecture := QFAssertExpr.«false»

private def relationRows : Lean.Json :=
  Lean.Json.arr #[
    Lean.Json.mkObj
      [ ("name", Lean.Json.str "rel:row"),
        ("rows", Lean.Json.arr #[]) ]]

private def interpretation : Lean.Json :=
  Lean.Json.mkObj
    [ ("carrier_keys", Lean.Json.arr
        #[Lean.Json.str "num:0"]),
      ("relations", relationRows) ]

private def obligationIdentity : Lean.Json :=
  Lean.Json.mkObj
    [ ("kind", Lean.Json.str
        "test_framework_ii_base_job"),
      ("version", Lean.Json.num 1) ]

private def validation :=
  Refutation.validate entailment interpretation

private def validatesBaseCountermodel : Bool :=
  match validation with
  | .error _ => false
  | .ok checked =>
      checked.axiomsHold &&
        !checked.conjectureHolds &&
        checked.validated &&
        checked.model.carrier == {Data.num 0}

private def expectedFieldNames : List String :=
  [ "obligation_identity",
    "obligation_digest",
    "carrier_identity",
    "carrier_digest",
    "interpretation_identity",
    "interpretation_digest",
    "validation_identity",
    "validation_digest",
    "axioms_hold",
    "conjecture_holds",
    "validated_refutation",
    "validation_definition" ]

private def hasOnlyBaseFields : Bool :=
  match validation with
  | .error _ => false
  | .ok checked =>
      (checked.fields obligationIdentity).map
          (fun field => field.1) ==
        expectedFieldNames

private def objectFieldNames : Lean.Json -> List String
| .obj fields => fields.keys
| _ => []

private def expectedIdentityFieldNames : List String :=
  [ "axioms_hold",
    "conjecture_holds",
    "interpretation_identity",
    "kind",
    "obligation_identity",
    "validated_refutation",
    "version" ]

private def hasBaseValidationIdentity : Bool :=
  match validation with
  | .error _ => false
  | .ok checked =>
      let identity := checked.identity obligationIdentity
      identity.getObjValD "kind" == Lean.Json.str
          "whiel_framework_ii_base_refutation_validation" &&
        identity.getObjValD "obligation_identity" ==
          obligationIdentity &&
        identity.getObjValD "validated_refutation" ==
          Lean.Json.bool true &&
        objectFieldNames identity ==
          expectedIdentityFieldNames

private def incompleteSchema : Lean.Json :=
  Lean.Json.mkObj
    [ ("carrier_keys", Lean.Json.arr
        #[Lean.Json.str "num:0"]),
      ("relations", Lean.Json.arr #[]) ]

private def rejectsIncompleteSchema : Bool :=
  match Refutation.validate entailment incompleteSchema with
  | .error _ => true
  | .ok _ => false

private def emptyCarrier : Lean.Json :=
  Lean.Json.mkObj
    [ ("carrier_keys", Lean.Json.arr #[]),
      ("relations", relationRows) ]

private def rejectsEmptyCarrier : Bool :=
  match Refutation.validate entailment emptyCarrier with
  | .error _ => true
  | .ok _ => false

private def constantEntailment :
    QFEntailment (D := Data) schema where
  axioms := [QFAssertExpr.eq
    (RAExpr.single (Data.num 1))
    (RAExpr.single (Data.num 1))]
  conjecture := QFAssertExpr.«false»

private def rejectsMissingRequiredConstant : Bool :=
  match Refutation.validateWithConstants constantEntailment
      ∅ interpretation with
  | .error message =>
      message ==
        "validation constants omit an obligation constant"
  | .ok _ => false

#guard validatesBaseCountermodel

#guard hasOnlyBaseFields

#guard hasBaseValidationIdentity

#guard rejectsIncompleteSchema

#guard rejectsEmptyCarrier

#guard rejectsMissingRequiredConstant

end FrameworkIIRefutation
end Tests
end Synthesis
end Whiel
