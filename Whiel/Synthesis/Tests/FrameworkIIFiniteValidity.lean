-- Author: Jesse Comer
import Whiel.Synthesis.FrameworkII.FiniteValidity.Registry
import Whiel.Synthesis.FrameworkII.FiniteValidity.Selection
import Whiel.Synthesis.FrameworkII.FiniteValidity.Transport

/-
  Pure checks for the retained finite-validity library.
  The fixtures exercise selection admission and replay over
  two unrelated relation-name carriers without constructing
  a Framework-II task or dispatching a worker request.
-/

set_option linter.hashCommand false

------------------------------------------------------------
-- Target and JSON Helpers
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Tests
namespace FrameworkIIFiniteValidity

open FrameworkII.FiniteValidity

inductive Target
| termination
| initialization
| maintenance
deriving DecidableEq, Repr

private def targets : List Target :=
  [.termination, .initialization, .maintenance]

private def targetRequestIdentity : Target -> Lean.Json
| .termination =>
    Lean.Json.mkObj
      [("kind", Lean.Json.str "termination")]
| .initialization =>
    Lean.Json.mkObj
      [("kind", Lean.Json.str "initialization")]
| .maintenance =>
    Lean.Json.mkObj
      [("kind", Lean.Json.str "maintenance")]

private def targetCheckedIdentity
    (scopeIdentity : Lean.Json) : Target -> Lean.Json
| target =>
    Lean.Json.mkObj
      [ ("kind", Lean.Json.str
          "test_finite_validity_target"),
        ("version", Lean.Json.num 1),
        ("scope_identity", scopeIdentity),
        ("obligation_kind", Lean.Json.str
          (match target with
          | .termination => "termination"
          | .initialization => "initialization"
          | .maintenance => "maintenance")) ]

private def decodeTargetWith
    (encode : Target -> Lean.Json)
    (json : Lean.Json) : Except String Target :=
  match targets.find? fun target =>
      encode target == json with
  | some target => .ok target
  | none => .error "target identity is not canonical"

private def targetCodec : Selection.TargetCodec Target where
  requestIdentity := targetRequestIdentity
  checkedIdentity := targetCheckedIdentity
  decodeRequest := decodeTargetWith targetRequestIdentity
  decodeCheckedIdentity := fun scopeIdentity =>
    decodeTargetWith (targetCheckedIdentity scopeIdentity)

private def epsilonRaw
    (target : Target)
    (edgeKey domainKey : String) : Lean.Json :=
  Lean.Json.mkObj
    [ ("entry_id", Lean.Json.str
        Registry.epsilonMaxEntryId),
      ("instantiation", Lean.Json.mkObj
        [ ("kind", Lean.Json.str
            "epsilon_max_binary_domain"),
          ("edge_relation_key", Lean.Json.str edgeKey),
          ("domain_relation_key",
            Lean.Json.str domainKey) ]),
      ("target", targetRequestIdentity target) ]

private def strictOrderRaw
    (target : Target)
    (relationKey : String) : Lean.Json :=
  Lean.Json.mkObj
    [ ("entry_id", Lean.Json.str
        Registry.strictLinearOrderGreatestEntryId),
      ("instantiation", Lean.Json.mkObj
        [ ("kind", Lean.Json.str
            "strict_linear_order_relation"),
          ("relation_key", Lean.Json.str relationKey) ]),
      ("target", targetRequestIdentity target) ]

private def succeeded {α : Type} :
    Except String α -> Bool
| .ok _ => true
| .error _ => false

private def rejected {α : Type} :
    Except String α -> Bool
| .ok _ => false
| .error _ => true

private def arraySize (json : Lean.Json) : Nat :=
  match json with
  | .arr values => values.size
  | _ => 0

end FrameworkIIFiniteValidity
end Tests
end Synthesis
end Whiel

------------------------------------------------------------
-- First Independent Relation Carrier
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Tests
namespace FrameworkIIFiniteValidity
namespace First

open FrameworkII.FiniteValidity
open Runtime

inductive Name
| edge
| domain
| unary
| spare
deriving DecidableEq, Repr

def key : Name -> String
| .edge => "first:edge"
| .domain => "first:domain"
| .unary => "first:unary"
| .spare => "first:spare"

private theorem key_injective : Function.Injective key := by
  intro left right hKey
  cases left <;> cases right <;> simp_all [key]

instance : RelationNames Name where
  decEq := inferInstance
  repr := inferInstance

instance : LinearOrder Name :=
  LinearOrder.lift' key key_injective

instance : SolverKey Name where
  key := key
  key_injective := key_injective

def Gamma : UnnamedSchema Name where
  syms := {.edge, .domain, .unary}
  arity
  | ⟨.edge, _⟩ => 2
  | ⟨.domain, _⟩ => 2
  | ⟨.unary, _⟩ => 1
  | ⟨.spare, hMember⟩ => by
      simp at hMember

def scopeIdentity : Lean.Json :=
  Lean.Json.mkObj
    [ ("kind", Lean.Json.str "first_test_scope"),
      ("version", Lean.Json.num 1) ]

def codec : Selection.TargetCodec Target :=
  targetCodec

end First
end FrameworkIIFiniteValidity
end Tests
end Synthesis
end Whiel

------------------------------------------------------------
-- Second Independent Relation Carrier
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Tests
namespace FrameworkIIFiniteValidity
namespace Second

open FrameworkII.FiniteValidity
open Runtime

inductive Name
| order
| domain
| payload
| reserve
deriving DecidableEq, Repr

def key : Name -> String
| .order => "second:order"
| .domain => "second:domain"
| .payload => "second:payload"
| .reserve => "second:reserve"

private theorem key_injective : Function.Injective key := by
  intro left right hKey
  cases left <;> cases right <;> simp_all [key]

instance : RelationNames Name where
  decEq := inferInstance
  repr := inferInstance

instance : LinearOrder Name :=
  LinearOrder.lift' key key_injective

instance : SolverKey Name where
  key := key
  key_injective := key_injective

def Gamma : UnnamedSchema Name where
  syms := {.order, .domain, .payload}
  arity
  | ⟨.order, _⟩ => 2
  | ⟨.domain, _⟩ => 2
  | ⟨.payload, _⟩ => 1
  | ⟨.reserve, hMember⟩ => by
      simp at hMember

def scopeIdentity : Lean.Json :=
  Lean.Json.mkObj
    [ ("kind", Lean.Json.str "second_test_scope"),
      ("version", Lean.Json.num 1) ]

def codec : Selection.TargetCodec Target :=
  targetCodec

end Second
end FrameworkIIFiniteValidity
end Tests
end Synthesis
end Whiel

------------------------------------------------------------
-- Registry Identity
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Tests
namespace FrameworkIIFiniteValidity

open FrameworkII.FiniteValidity
open Runtime

#guard arraySize
    (Registry.identity.getObjValD
      "ordered_entries") == 2

#guard Registry.identity.getObjValD
  "ordered_cards" == Lean.Json.null

#guard Registry.digest ==
  CanonicalDigest.jsonSha256 Registry.identity

#guard Registry.digest ==
  "57850f836d8df22a3e8c42f6aa922833\
    61d796072fddc35a9d85eb73de080262"

#guard Registry.presentationDigest ==
  "d5d70371d60cf0a24a2f250b64d7f57\
    2fb7340af234ad7ef359007ed8cd28b43"

#guard rejected (Registry.entryFromId "missing_entry")

end FrameworkIIFiniteValidity
end Tests
end Synthesis
end Whiel

------------------------------------------------------------
-- First-Carrier Admission and Replay
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Tests
namespace FrameworkIIFiniteValidity

open FrameworkII.FiniteValidity

def firstEpsilon : Lean.Json :=
  epsilonRaw .initialization
    (First.key .edge) (First.key .domain)

def firstStrict : Lean.Json :=
  strictOrderRaw .maintenance (First.key .edge)

def firstForward :=
  Selection.admitRawList First.Gamma First.codec
    First.scopeIdentity [firstEpsilon, firstStrict]

def firstReverse :=
  Selection.admitRawList First.Gamma First.codec
    First.scopeIdentity [firstStrict, firstEpsilon]

def firstIdentity : Lean.Json :=
  match firstForward with
  | .ok selections =>
      Selection.listIdentity First.codec
        First.scopeIdentity selections
  | .error _ => Lean.Json.null

def firstReverseIdentity : Lean.Json :=
  match firstReverse with
  | .ok selections =>
      Selection.listIdentity First.codec
        First.scopeIdentity selections
  | .error _ => Lean.Json.null

def firstHasBothEntries : Bool :=
  match firstForward with
  | .ok selections =>
      selections.any (fun selection =>
          selection.entry == Registry.Entry.epsilonMax) &&
        selections.any (fun selection =>
          selection.entry ==
            Registry.Entry.strictLinearOrderGreatest)
  | .error _ => false

def firstReplayCanonical : Bool :=
  match Selection.decodeListIdentity First.Gamma
      First.codec First.scopeIdentity firstIdentity with
  | .ok selections =>
      Selection.listIdentity First.codec
          First.scopeIdentity selections ==
        firstIdentity
  | .error _ => false

def duplicateResult :=
  Selection.admitRawList First.Gamma First.codec
    First.scopeIdentity [firstEpsilon, firstEpsilon]

def wrongArityResult :=
  Selection.admitRawList First.Gamma First.codec
    First.scopeIdentity
      [epsilonRaw .termination
        (First.key .unary) (First.key .domain)]

def unknownKeyResult :=
  Selection.admitRawList First.Gamma First.codec
    First.scopeIdentity
      [strictOrderRaw .termination "first:missing"]

def tamperedIdentity : Lean.Json :=
  Lean.Json.mkObj
    [ ("kind", firstIdentity.getObjValD "kind"),
      ("version", firstIdentity.getObjValD "version"),
      ("scope_identity",
        firstIdentity.getObjValD "scope_identity"),
      ("registry_identity", Lean.Json.null),
      ("ordered_selections",
        firstIdentity.getObjValD "ordered_selections") ]

def tamperedReplay :=
  Selection.decodeListIdentity First.Gamma First.codec
    First.scopeIdentity tamperedIdentity

#guard succeeded firstForward

#guard succeeded firstReverse

#guard firstIdentity == firstReverseIdentity

#guard firstHasBothEntries

#guard firstReplayCanonical

#guard rejected duplicateResult

#guard rejected wrongArityResult

#guard rejected unknownKeyResult

#guard rejected tamperedReplay

end FrameworkIIFiniteValidity
end Tests
end Synthesis
end Whiel

------------------------------------------------------------
-- Second-Carrier Admission and Replay
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Tests
namespace FrameworkIIFiniteValidity

open FrameworkII.FiniteValidity

def secondEpsilon : Lean.Json :=
  epsilonRaw .termination
    (Second.key .order) (Second.key .domain)

def secondStrict : Lean.Json :=
  strictOrderRaw .initialization (Second.key .order)

def secondAdmission :=
  Selection.admitRawList Second.Gamma Second.codec
    Second.scopeIdentity [secondStrict, secondEpsilon]

def secondIdentity : Lean.Json :=
  match secondAdmission with
  | .ok selections =>
      Selection.listIdentity Second.codec
        Second.scopeIdentity selections
  | .error _ => Lean.Json.null

def secondHasBothEntries : Bool :=
  match secondAdmission with
  | .ok selections =>
      selections.any (fun selection =>
          selection.entry == Registry.Entry.epsilonMax) &&
        selections.any (fun selection =>
          selection.entry ==
            Registry.Entry.strictLinearOrderGreatest)
  | .error _ => false

def secondReplayCanonical : Bool :=
  match Selection.decodeListIdentity Second.Gamma
      Second.codec Second.scopeIdentity secondIdentity with
  | .ok selections =>
      Selection.listIdentity Second.codec
          Second.scopeIdentity selections ==
        secondIdentity
  | .error _ => false

#guard succeeded secondAdmission

#guard secondHasBothEntries

#guard secondReplayCanonical

end FrameworkIIFiniteValidity
end Tests
end Synthesis
end Whiel

------------------------------------------------------------
-- Direct Transport Application
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Tests
namespace FrameworkIIFiniteValidity

open Concrete
open FrameworkII.FiniteValidity
open RelCalc.SentenceEntailment

example
    (extras : List
      (RelCalc.Sentence Data First.Gamma))
    (base : QFEntailment (D := Data) First.Gamma)
    (hFresh : ∃ X : First.Name,
      X ∉ First.Gamma.syms)
    (hExtras : ∀ φ ∈ extras, φ.AdomValid)
    (baseNoEmpty :
      base.toRelCalcEntailment.NoEmptyCounterexample)
    (augmentedValid :
      FOL.SentenceEntailment.ShallowValid
        (toFOLWithSupportAxioms
          (base.toRelCalcEntailment.prependAxioms
            extras))) :
    base.Valid :=
  valid_of_prependAxioms_shallowValid extras base
    hFresh hExtras baseNoEmpty augmentedValid

end FrameworkIIFiniteValidity
end Tests
end Synthesis
end Whiel
