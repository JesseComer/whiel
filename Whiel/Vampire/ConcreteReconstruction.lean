-- Author: Jesse Comer
import Whiel.Concrete.Data
import Whiel.Concrete.IndexAlphaName
import Whiel.Vampire.InvariantObligations
import Whiel.Vampire.SolverName.Concrete

/-
  This file defines the Lean-owned symbol metadata used to
  reconstruct concrete Whiel Vampire proofs.

  Key definitions include:
    * `Vampire.ReconstructionMetadata.ofQF?`
    * `Vampire.ReconstructionMetadata.manifestJson?`
    * `Vampire.ReconstructionMetadata.writeManifest`

  Metadata is derived from the same closed entailment and
  name environment as `Vampire.closedJobOfQF`. Relation and
  data values are serialized structurally, never through
  `repr` parsing.
-/

------------------------------------------------------------
-- Typed Bindings
------------------------------------------------------------

namespace Whiel
namespace Vampire
namespace ReconstructionMetadata

open Concrete

def formatVersion : Nat := 1

def fileName : String :=
  "reconstruction_manifest.json"

/- One concrete relation-to-TPTP binding. -/
structure RelationBinding where
  tptpName : String
  base : String
  index : Nat
  arity : Nat
deriving DecidableEq, Repr

/- One relation in canonical full-schema order. -/
structure SchemaRelationBinding where
  base : String
  index : Nat
  arity : Nat
deriving DecidableEq, Repr

/- One concrete data-function-to-TPTP binding. -/
structure FunctionBinding where
  tptpName : String
  value : Data
deriving DecidableEq, Repr

/- Reconstruction metadata for one closed job. -/
structure JobMetadata where
  id : String
  axiomCount : Nat
  supportAxiomCount : Nat
  sourceAxiomCount : Nat
  schemaRelations : List SchemaRelationBinding
  relations : List RelationBinding
  functions : List FunctionBinding
deriving DecidableEq, Repr

end ReconstructionMetadata
end Vampire
end Whiel

------------------------------------------------------------
-- JSON Encoding
------------------------------------------------------------

namespace Whiel
namespace Vampire
namespace ReconstructionMetadata

open Concrete

private def relationSourceJson
    (base : String)
    (index : Nat) :
    Lean.Json :=
  Lean.Json.mkObj
    [ ("kind", Lean.Json.str "index_alpha_name"),
      ("base", Lean.Json.str base),
      ("index", Lean.Json.num index) ]

private def dataSourceJson : Data → Lean.Json
| .num n =>
    Lean.Json.mkObj
      [ ("kind", Lean.Json.str "data"),
        ("tag", Lean.Json.str "num"),
        ("value", Lean.Json.num n) ]
| .str s =>
    Lean.Json.mkObj
      [ ("kind", Lean.Json.str "data"),
        ("tag", Lean.Json.str "str"),
        ("value", Lean.Json.str s) ]
| .bool b =>
    Lean.Json.mkObj
      [ ("kind", Lean.Json.str "data"),
        ("tag", Lean.Json.str "bool"),
        ("value", Lean.Json.bool b) ]

def RelationBinding.toJson
    (binding : RelationBinding) :
    Lean.Json :=
  Lean.Json.mkObj
    [ ("tptp_name", Lean.Json.str binding.tptpName),
      ("source",
        relationSourceJson binding.base binding.index),
      ("arity", Lean.Json.num binding.arity) ]

def SchemaRelationBinding.toJson
    (binding : SchemaRelationBinding) :
    Lean.Json :=
  Lean.Json.mkObj
    [ ("source",
        relationSourceJson binding.base binding.index),
      ("arity", Lean.Json.num binding.arity) ]

def FunctionBinding.toJson
    (binding : FunctionBinding) :
    Lean.Json :=
  Lean.Json.mkObj
    [ ("tptp_name", Lean.Json.str binding.tptpName),
      ("source", dataSourceJson binding.value),
      ("arity", Lean.Json.num 0) ]

def JobMetadata.toJson
    (metadata : JobMetadata) :
    Lean.Json :=
  Lean.Json.mkObj
    [ ("id", Lean.Json.str metadata.id),
      ("axiom_count", Lean.Json.num metadata.axiomCount),
      ("support_axiom_count",
        Lean.Json.num metadata.supportAxiomCount),
      ("source_axiom_count",
        Lean.Json.num metadata.sourceAxiomCount),
      ("schema_relations",
        Lean.Json.arr
          (metadata.schemaRelations.map
            SchemaRelationBinding.toJson).toArray),
      ("relations",
        Lean.Json.arr
          (metadata.relations.map
            RelationBinding.toJson).toArray),
      ("functions",
        Lean.Json.arr
          (metadata.functions.map
            FunctionBinding.toJson).toArray) ]

end ReconstructionMetadata
end Vampire
end Whiel

------------------------------------------------------------
-- Closed-Problem Metadata
------------------------------------------------------------

namespace Whiel
namespace Vampire
namespace ReconstructionMetadata

open Concrete

private def relationBinding?
    (Γ : UnnamedSchema IndexAlphaName)
    (binding : IndexAlphaName × String) :
    Except String RelationBinding :=
  match Γ.arity? binding.1 with
  | none =>
      .error
        ("closed problem contains an unknown relation " ++
          binding.2)
  | some arity =>
      .ok
        { tptpName := binding.2
          base := binding.1.baseName.value
          index := binding.1.index
          arity := arity }

private def functionBinding
    (binding : Data × String) :
    FunctionBinding :=
  { tptpName := binding.2
    value := binding.1 }

private def schemaRelationBinding
    (Γ : UnnamedSchema IndexAlphaName)
    (symbol : Γ.syms) :
    SchemaRelationBinding :=
  { base := symbol.1.baseName.value
    index := symbol.1.index
    arity := Γ.arity symbol }

/- Metadata from the exact closed QF name environment. -/
def ofQF?
    {Γ : UnnamedSchema IndexAlphaName}
    (id : String)
    (E : QFEntailment (D := Data) Γ) :
    Except String JobMetadata := do
  let env := closedNameEnvOfQF E
  -- The one-shot relation carrier proves nothing about its
  -- names, so the environment is decided here rather than
  -- assumed: a repeated or illegal name is refused instead
  -- of being described in the metadata.
  if !env.wellFormed then
    throw ("job " ++ id ++
      " has a malformed solver-name environment")
  let relations ←
    env.relNames.mapM (relationBinding? Γ)
  let functions :=
    env.funNames.map functionBinding
  let schemaRelations :=
    Γ.syms.attach.sort.map
      (schemaRelationBinding Γ)
  let axiomCount :=
    (closedEntailmentOfQF E).axioms.length
  let R := E.toRelCalcEntailment
  let supportAxiomCount :=
    (RelCalc.ToFOL.supportAxioms
      Γ R.constants).length
  let sourceAxiomCount :=
    R.toFOLSourceAxioms.length
  return {
    id, axiomCount, supportAxiomCount,
    sourceAxiomCount, schemaRelations,
    relations, functions
  }

/- Versioned JSON for jobs in their canonical order. -/
def manifestJson?
    {Γ : UnnamedSchema IndexAlphaName}
    (jobs : List
      (String × QFEntailment (D := Data) Γ)) :
    Except String Lean.Json := do
  let metadata ← jobs.mapM fun job =>
    ofQF? job.1 job.2
  return Lean.Json.mkObj
    [ ("format_version", Lean.Json.num formatVersion),
      ("jobs",
        Lean.Json.arr
          (metadata.map JobMetadata.toJson).toArray) ]

/- Write closed-proof reconstruction metadata. -/
def writeManifest
    {Γ : UnnamedSchema IndexAlphaName}
    (root : System.FilePath)
    (jobs : List
      (String × QFEntailment (D := Data) Γ)) :
    IO Unit := do
  let json ←
    match manifestJson? jobs with
    | .ok json => pure json
    | .error message => throw (IO.userError message)
  IO.FS.createDirAll root
  IO.FS.writeFile (root / fileName)
    ((Lean.Json.pretty json 100) ++ "\n")

end ReconstructionMetadata
end Vampire
end Whiel
