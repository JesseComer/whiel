-- Author: Jesse Comer
import Whiel.Library.FiniteOrder
import Whiel.Concrete.Data
import Whiel.Synthesis.FrameworkII.FiniteValidity.Identity
import Whiel.Synthesis.Runtime.CanonicalDigest
import Whiel.Synthesis.Runtime.Task

/-
  The immutable logical finite-validity registry and its
  separately digested, non-authoritative search catalog.

  Logical entries bind RelCalc syntax and the exact Lean
  theorem proving active-domain validity. Search
  prose is deliberately excluded from the registry digest.
-/

------------------------------------------------------------
-- Reviewed Entry Templates
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FiniteValidity
namespace Registry

open Library.FiniteOrder
open Concrete
open Runtime

/- Registry-v2 wire ID for library accession `FV000001`. -/
def epsilonMaxEntryId : String := "epsilon_max"

/- Registry-v2 wire ID for library accession `FV000002`. -/
def strictLinearOrderGreatestEntryId : String :=
  "strict_linear_order_greatest"

private inductive EpsilonTemplateRelation
| edge
| domainSource
deriving DecidableEq, Repr

instance : RelationNames EpsilonTemplateRelation where
  decEq := inferInstance
  repr := inferInstance

private def epsilonTemplateSchema :
    UnnamedSchema EpsilonTemplateRelation where
  syms := {.edge, .domainSource}
  arity := fun _ => 2

private def epsilonTemplateEdge :
    BinaryRelation epsilonTemplateSchema where
  symbol := epsilonTemplateSchema.sym .edge
  arityTwo := rfl

private def epsilonTemplateDomainSource :
    BinaryRelation epsilonTemplateSchema where
  symbol := epsilonTemplateSchema.sym .domainSource
  arityTwo := rfl

private def epsilonTemplateSentence :
    RelCalc.Sentence Data epsilonTemplateSchema :=
  FV000001.sentence epsilonTemplateEdge
    epsilonTemplateDomainSource

private def epsilonTemplateRelationKey :
    EpsilonTemplateRelation -> String
| .edge => "E"
| .domainSource => "T"

private inductive LinearTemplateRelation
| edge
deriving DecidableEq, Repr

instance : RelationNames LinearTemplateRelation where
  decEq := inferInstance
  repr := inferInstance

private def linearTemplateSchema :
    UnnamedSchema LinearTemplateRelation where
  syms := {.edge}
  arity := fun _ => 2

private def linearTemplateEdge :
    BinaryRelation linearTemplateSchema where
  symbol := linearTemplateSchema.sym .edge
  arityTwo := rfl

private def linearTemplateSentence :
    RelCalc.Sentence Data linearTemplateSchema :=
  FV000002.sentence linearTemplateEdge

private def linearTemplateRelationKey :
    LinearTemplateRelation -> String
| .edge => "R"

private def epsilonMaxTemplateSentenceIdentity : Lean.Json :=
  Identity.relSentenceJson epsilonTemplateRelationKey
    SolverKey.key epsilonTemplateSentence

private def linearOrderTemplateSentenceIdentity : Lean.Json :=
  Identity.relSentenceJson linearTemplateRelationKey
    SolverKey.key linearTemplateSentence

private def templateConstants
    {A : Type}
    [RelationNames A]
    {Gamma : UnnamedSchema A}
    (sentence : RelCalc.Sentence Data Gamma) :
    Array Lean.Json :=
  (SolverKey.sortedKeys sentence.constants |>.map
    Lean.Json.str).toArray

private def epsilonMaxSubstitutionIdentity : Lean.Json :=
  Lean.Json.mkObj
    [ ("kind", Lean.Json.str
        "epsilon_max_binary_domain"),
      ("edge_arity", Lean.Json.num 2),
      ("domain_source_arity", Lean.Json.num 2),
      ("edge_domain_aliasing", Lean.Json.bool true),
      ("formal_variable", Lean.Json.num 0),
      ("witness_variable", Lean.Json.num 3) ]

private def strictLinearOrderSubstitutionIdentity : Lean.Json :=
  Lean.Json.mkObj
    [ ("kind", Lean.Json.str
        "strict_linear_order_relation"),
      ("relation_arity", Lean.Json.num 2) ]

private def epsilonMaxTheoremIdentity : Lean.Json :=
  Lean.Json.mkObj
    [ ("kind", Lean.Json.str
        "whiel_finite_validity_theorem"),
      ("version", Lean.Json.num 2),
      ("adom_valid_theorem", Lean.Json.str
        "Whiel.Library.FiniteOrder.epsilonMaxBinaryDomain_adomValid") ]

private def strictLinearOrderTheoremIdentity : Lean.Json :=
  Lean.Json.mkObj
    [ ("kind", Lean.Json.str
        "whiel_finite_validity_theorem"),
      ("version", Lean.Json.num 2),
      ("adom_valid_theorem", Lean.Json.str
        "Whiel.Library.FiniteOrder.linearOrderMax_adomValid") ]

private def epsilonTemplateSignature : Lean.Json :=
  Lean.Json.mkObj
    [ ("relations", Lean.Json.arr #[
        Lean.Json.mkObj
          [ ("key", Lean.Json.str "E"),
            ("arity", Lean.Json.num 2) ],
        Lean.Json.mkObj
          [ ("key", Lean.Json.str "T"),
            ("arity", Lean.Json.num 2) ] ]),
      ("constants", Lean.Json.arr
        (templateConstants epsilonTemplateSentence)) ]

private def linearTemplateSignature : Lean.Json :=
  Lean.Json.mkObj
    [ ("relations", Lean.Json.arr #[
        Lean.Json.mkObj
          [ ("key", Lean.Json.str "R"),
            ("arity", Lean.Json.num 2) ] ]),
      ("constants", Lean.Json.arr
        (templateConstants linearTemplateSentence)) ]

private def epsilonMaxEntryIdentity : Lean.Json :=
  Lean.Json.mkObj
    [ ("kind", Lean.Json.str
        "whiel_finite_validity_registry_entry"),
      ("version", Lean.Json.num 2),
      ("entry_id", Lean.Json.str epsilonMaxEntryId),
      ("template_signature", epsilonTemplateSignature),
      ("template_sentence_identity",
        epsilonMaxTemplateSentenceIdentity),
      ("theorem_identity", epsilonMaxTheoremIdentity),
      ("supported_substitution",
        epsilonMaxSubstitutionIdentity) ]

private def strictLinearOrderEntryIdentity : Lean.Json :=
  Lean.Json.mkObj
    [ ("kind", Lean.Json.str
        "whiel_finite_validity_registry_entry"),
      ("version", Lean.Json.num 2),
      ("entry_id", Lean.Json.str
        strictLinearOrderGreatestEntryId),
      ("template_signature", linearTemplateSignature),
      ("template_sentence_identity",
        linearOrderTemplateSentenceIdentity),
      ("theorem_identity",
        strictLinearOrderTheoremIdentity),
      ("supported_substitution",
        strictLinearOrderSubstitutionIdentity) ]

inductive Entry
| epsilonMax
| strictLinearOrderGreatest
deriving DecidableEq, Repr

namespace Entry

def id : Entry -> String
| .epsilonMax => epsilonMaxEntryId
| .strictLinearOrderGreatest =>
    strictLinearOrderGreatestEntryId

def identity : Entry -> Lean.Json
| .epsilonMax => epsilonMaxEntryIdentity
| .strictLinearOrderGreatest =>
    strictLinearOrderEntryIdentity

def theoremIdentity : Entry -> Lean.Json
| .epsilonMax => epsilonMaxTheoremIdentity
| .strictLinearOrderGreatest =>
    strictLinearOrderTheoremIdentity

end Entry

def entryFromId (entryId : String) : Except String Entry :=
  if entryId = epsilonMaxEntryId then
    return .epsilonMax
  else if entryId = strictLinearOrderGreatestEntryId then
    return .strictLinearOrderGreatest
  else
    throw "finite-validity entry is not registered"

end Registry
end FiniteValidity
end FrameworkII
end Synthesis
end Whiel

------------------------------------------------------------
-- Logical Registry Identity
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FiniteValidity
namespace Registry

open Runtime

def identity : Lean.Json :=
  Lean.Json.mkObj
    [ ("kind", Lean.Json.str
        "whiel_finite_validity_registry"),
      ("version", Lean.Json.num 2),
      ("ordered_entries", Lean.Json.arr #[
        epsilonMaxEntryIdentity,
        strictLinearOrderEntryIdentity]) ]

def digest : String :=
  CanonicalDigest.jsonSha256 identity

def requestIdentity : Lean.Json :=
  Lean.Json.mkObj
    [ ("kind", Lean.Json.str
        "whiel_finite_validity_registry_request"),
      ("version", Lean.Json.num 1) ]

end Registry
end FiniteValidity
end FrameworkII
end Synthesis
end Whiel

------------------------------------------------------------
-- Search Presentation
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FiniteValidity
namespace Registry

open Runtime

private def searchCard
    (entryId title description pretty : String)
    (entryIdentity : Lean.Json)
    (tags applicability : Array Lean.Json) : Lean.Json :=
  Lean.Json.mkObj
    [ ("kind", Lean.Json.str
        "whiel_finite_validity_search_card"),
      ("version", Lean.Json.num 1),
      ("entry_id", Lean.Json.str entryId),
      ("entry_identity_digest", Lean.Json.str
        (CanonicalDigest.jsonSha256 entryIdentity)),
      ("title", Lean.Json.str title),
      ("description", Lean.Json.str description),
      ("tags", Lean.Json.arr tags),
      ("applicability", Lean.Json.arr applicability),
      ("pretty_statement", Lean.Json.str pretty) ]

def presentationIdentity : Lean.Json :=
  let epsilonCard := searchCard epsilonMaxEntryId
    "Finite epsilon maximum"
    "Use when a strict partial order and a binary relation \
      defining the candidate subset occur in the obligation."
    "Every nonempty binary-definable subset of a finite strict partial order has a maximal member."
    epsilonMaxEntryIdentity
    #[Lean.Json.str "finite_order",
      Lean.Json.str "maximal_element",
      Lean.Json.str "strict_partial_order"]
    #[Lean.Json.str
        "requires two binary relations in the target schema",
      Lean.Json.str
        "the edge and domain-source relations may coincide"]
  let linearCard := searchCard
    strictLinearOrderGreatestEntryId
    "Finite strict-linear-order greatest element"
    "Use when a nonempty strict linear order occurs in the \
      obligation and a greatest witness may help proof search."
    "Every nonempty finite strict linear order has a greatest element."
    strictLinearOrderEntryIdentity
    #[Lean.Json.str "finite_order",
      Lean.Json.str "greatest_element",
      Lean.Json.str "strict_linear_order"]
    #[Lean.Json.str
      "requires one binary relation in the target schema"]
  Lean.Json.mkObj
    [ ("kind", Lean.Json.str
        "whiel_finite_validity_presentation"),
      ("version", Lean.Json.num 1),
      ("registry_digest", Lean.Json.str digest),
      ("ordered_cards", Lean.Json.arr
        #[epsilonCard, linearCard]) ]

def presentationDigest : String :=
  CanonicalDigest.jsonSha256 presentationIdentity

end Registry
end FiniteValidity
end FrameworkII
end Synthesis
end Whiel
