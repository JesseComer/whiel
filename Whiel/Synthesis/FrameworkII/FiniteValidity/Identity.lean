-- Author: Jesse Comer
import Databases.RelCalc.ToFOL

/-
  Exact structural identities for finite-validity syntax.

  RelCalc identities are authoritative for library theorem
  application. FOL identities separately bind the exact
  translated sentence rendered for the prover.
-/

------------------------------------------------------------
-- RelCalc Structural Identities
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FiniteValidity
namespace Identity

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Gamma : UnnamedSchema A}

private def relTermJson
    (constantKey : D -> String) :
    RelTerm D -> Lean.Json
| .var name =>
    Lean.Json.mkObj
      [ ("kind", Lean.Json.str "variable"),
        ("name", Lean.Json.num name) ]
| .const value =>
    Lean.Json.mkObj
      [ ("kind", Lean.Json.str "constant"),
        ("constant_key", Lean.Json.str
          (constantKey value)) ]

private def relTermsJson
    (constantKey : D -> String)
    {count : Nat}
    (terms : Vector (RelTerm D) count) : Lean.Json :=
  Lean.Json.arr <| terms.toArray.map
    (relTermJson constantKey)

/- Exact structural identity of one RelCalc formula. -/
def relFormulaJson
    (relationKey : A -> String)
    (constantKey : D -> String) :
    RelCalc.Formula D Gamma -> Lean.Json
| .top =>
    Lean.Json.mkObj [("kind", Lean.Json.str "top")]
| .bot =>
    Lean.Json.mkObj [("kind", Lean.Json.str "bottom")]
| .eq left right =>
    Lean.Json.mkObj
      [ ("kind", Lean.Json.str "equality"),
        ("left", relTermJson constantKey left),
        ("right", relTermJson constantKey right) ]
| .rel atom =>
    Lean.Json.mkObj
      [ ("kind", Lean.Json.str "relation"),
        ("relation_key", Lean.Json.str
          (relationKey atom.rel.1)),
        ("arity", Lean.Json.num
          (Gamma.arity atom.rel)),
        ("arguments",
          relTermsJson constantKey atom.args) ]
| .and left right =>
    Lean.Json.mkObj
      [ ("kind", Lean.Json.str "and"),
        ("left",
          relFormulaJson relationKey constantKey left),
        ("right",
          relFormulaJson relationKey constantKey right) ]
| .or left right =>
    Lean.Json.mkObj
      [ ("kind", Lean.Json.str "or"),
        ("left",
          relFormulaJson relationKey constantKey left),
        ("right",
          relFormulaJson relationKey constantKey right) ]
| .not formula =>
    Lean.Json.mkObj
      [ ("kind", Lean.Json.str "not"),
        ("formula",
          relFormulaJson relationKey constantKey formula) ]
| .imp antecedent consequent =>
    Lean.Json.mkObj
      [ ("kind", Lean.Json.str "implication"),
        ("antecedent",
          relFormulaJson relationKey constantKey
            antecedent),
        ("consequent",
          relFormulaJson relationKey constantKey
            consequent) ]
| .iff left right =>
    Lean.Json.mkObj
      [ ("kind", Lean.Json.str "biconditional"),
        ("left",
          relFormulaJson relationKey constantKey left),
        ("right",
          relFormulaJson relationKey constantKey right) ]
| .forall_ varName formula =>
    Lean.Json.mkObj
      [ ("kind", Lean.Json.str "forall"),
        ("variable", Lean.Json.num varName),
        ("formula",
          relFormulaJson relationKey constantKey formula) ]
| .exists_ varName formula =>
    Lean.Json.mkObj
      [ ("kind", Lean.Json.str "exists"),
        ("variable", Lean.Json.num varName),
        ("formula",
          relFormulaJson relationKey constantKey formula) ]

/- Exact structural identity of a RelCalc sentence. -/
def relSentenceJson
    (relationKey : A -> String)
    (constantKey : D -> String)
    (sentence : RelCalc.Sentence D Gamma) : Lean.Json :=
  Lean.Json.mkObj
    [ ("kind", Lean.Json.str
        "whiel_relcalc_sentence"),
      ("version", Lean.Json.num 1),
      ("formula",
        relFormulaJson relationKey constantKey sentence.1) ]

end Identity
end FiniteValidity
end FrameworkII
end Synthesis
end Whiel

------------------------------------------------------------
-- FOL Structural Identities
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FiniteValidity
namespace Identity

variable {A F : Type}
variable [RelationNames A]
variable [FunctionNames F]
variable {Lambda : Signature A F}

mutual

  private def folTermJson
      (functionKey : F -> String) :
      FOL.Term Lambda -> Lean.Json
  | .var name =>
      Lean.Json.mkObj
        [ ("kind", Lean.Json.str "variable"),
          ("name", Lean.Json.num name) ]
  | .func function arguments =>
      Lean.Json.mkObj
        [ ("kind", Lean.Json.str "function"),
          ("function_key", Lean.Json.str
            (functionKey function.1)),
          ("arity", Lean.Json.num
            (Lambda.funArity function)),
          ("arguments",
            folTermListJson functionKey arguments) ]

  private def folTermListJson
      (functionKey : F -> String) :
      {count : Nat} ->
        FOL.TermList Lambda count -> Lean.Json
  | _, .nil => Lean.Json.arr #[]
  | _, .cons term terms =>
      match folTermListJson functionKey terms with
      | .arr tail =>
          Lean.Json.arr <|
            #[folTermJson functionKey term] ++ tail
      | _ => Lean.Json.arr #[]

end

/- Exact structural identity of one typed FOL formula. -/
def folFormulaJson
    (relationKey : A -> String)
    (functionKey : F -> String) :
    FOL.Formula Lambda -> Lean.Json
| .top =>
    Lean.Json.mkObj [("kind", Lean.Json.str "top")]
| .bot =>
    Lean.Json.mkObj [("kind", Lean.Json.str "bottom")]
| .eq left right =>
    Lean.Json.mkObj
      [ ("kind", Lean.Json.str "equality"),
        ("left", folTermJson functionKey left),
        ("right", folTermJson functionKey right) ]
| .rel relation arguments =>
    Lean.Json.mkObj
      [ ("kind", Lean.Json.str "relation"),
        ("relation_key", Lean.Json.str
          (relationKey relation.1)),
        ("arity", Lean.Json.num
          (Lambda.arity relation)),
        ("arguments",
          folTermListJson functionKey arguments) ]
| .and left right =>
    Lean.Json.mkObj
      [ ("kind", Lean.Json.str "and"),
        ("left",
          folFormulaJson relationKey functionKey left),
        ("right",
          folFormulaJson relationKey functionKey right) ]
| .or left right =>
    Lean.Json.mkObj
      [ ("kind", Lean.Json.str "or"),
        ("left",
          folFormulaJson relationKey functionKey left),
        ("right",
          folFormulaJson relationKey functionKey right) ]
| .not formula =>
    Lean.Json.mkObj
      [ ("kind", Lean.Json.str "not"),
        ("formula",
          folFormulaJson relationKey functionKey formula) ]
| .imp antecedent consequent =>
    Lean.Json.mkObj
      [ ("kind", Lean.Json.str "implication"),
        ("antecedent",
          folFormulaJson relationKey functionKey
            antecedent),
        ("consequent",
          folFormulaJson relationKey functionKey
            consequent) ]
| .iff left right =>
    Lean.Json.mkObj
      [ ("kind", Lean.Json.str "biconditional"),
        ("left",
          folFormulaJson relationKey functionKey left),
        ("right",
          folFormulaJson relationKey functionKey right) ]
| .forall_ varName formula =>
    Lean.Json.mkObj
      [ ("kind", Lean.Json.str "forall"),
        ("variable", Lean.Json.num varName),
        ("formula",
          folFormulaJson relationKey functionKey formula) ]
| .exists_ varName formula =>
    Lean.Json.mkObj
      [ ("kind", Lean.Json.str "exists"),
        ("variable", Lean.Json.num varName),
        ("formula",
          folFormulaJson relationKey functionKey formula) ]

/- Exact structural identity of one closed FOL sentence. -/
def folSentenceJson
    (relationKey : A -> String)
    (functionKey : F -> String)
    (sentence : FOL.Sentence Lambda) : Lean.Json :=
  Lean.Json.mkObj
    [ ("kind", Lean.Json.str "whiel_fol_sentence"),
      ("version", Lean.Json.num 1),
      ("formula",
        folFormulaJson relationKey functionKey
          sentence.1) ]

end Identity
end FiniteValidity
end FrameworkII
end Synthesis
end Whiel
