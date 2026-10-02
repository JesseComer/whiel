-- Author: Jesse Comer
import Whiel.Vampire.ConcreteReconstruction

/-
  Exact structural-JSON checks for concrete Vampire proof
  reconstruction metadata.
-/

------------------------------------------------------------
-- Relation Metadata
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Tests
namespace ReconstructionMetadata

open Concrete
open Vampire.ReconstructionMetadata

example :
    RelationBinding.toJson
        { tptpName := "r_T_2"
          base := "T"
          index := 1
          arity := 2 } =
      Lean.Json.mkObj
        [ ("tptp_name", Lean.Json.str "r_T_2"),
          ("source",
            Lean.Json.mkObj
              [ ("kind",
                  Lean.Json.str "index_alpha_name"),
                ("base", Lean.Json.str "T"),
                ("index", Lean.Json.num 1) ]),
          ("arity", Lean.Json.num 2) ] :=
  rfl

example :
    SchemaRelationBinding.toJson
        { base := "Mode"
          index := 0
          arity := 0 } =
      Lean.Json.mkObj
        [ ("source",
            Lean.Json.mkObj
              [ ("kind",
                  Lean.Json.str "index_alpha_name"),
                ("base", Lean.Json.str "Mode"),
                ("index", Lean.Json.num 0) ]),
          ("arity", Lean.Json.num 0) ] :=
  rfl

example :
    JobMetadata.toJson
        { id := "term_check"
          axiomCount := 0
          supportAxiomCount := 0
          sourceAxiomCount := 0
          schemaRelations := []
          relations := []
          functions := [] } =
      Lean.Json.mkObj
        [ ("id", Lean.Json.str "term_check"),
          ("axiom_count", Lean.Json.num 0),
          ("support_axiom_count", Lean.Json.num 0),
          ("source_axiom_count", Lean.Json.num 0),
          ("schema_relations", Lean.Json.arr #[]),
          ("relations", Lean.Json.arr #[]),
          ("functions", Lean.Json.arr #[]) ] :=
  rfl

end ReconstructionMetadata
end Tests
end Synthesis
end Whiel

------------------------------------------------------------
-- Function Metadata
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Tests
namespace ReconstructionMetadata

open Concrete
open Vampire.ReconstructionMetadata

example :
    FunctionBinding.toJson
        { tptpName := "f_7"
          value := Data.num 7 } =
      Lean.Json.mkObj
        [ ("tptp_name", Lean.Json.str "f_7"),
          ("source",
            Lean.Json.mkObj
              [ ("kind", Lean.Json.str "data"),
                ("tag", Lean.Json.str "num"),
                ("value", Lean.Json.num 7) ]),
          ("arity", Lean.Json.num 0) ] :=
  rfl

example :
    FunctionBinding.toJson
        { tptpName := "f_root"
          value := Data.str "root" } =
      Lean.Json.mkObj
        [ ("tptp_name", Lean.Json.str "f_root"),
          ("source",
            Lean.Json.mkObj
              [ ("kind", Lean.Json.str "data"),
                ("tag", Lean.Json.str "str"),
                ("value", Lean.Json.str "root") ]),
          ("arity", Lean.Json.num 0) ] :=
  rfl

example :
    FunctionBinding.toJson
        { tptpName := "f_true"
          value := Data.bool true } =
      Lean.Json.mkObj
        [ ("tptp_name", Lean.Json.str "f_true"),
          ("source",
            Lean.Json.mkObj
              [ ("kind", Lean.Json.str "data"),
                ("tag", Lean.Json.str "bool"),
                ("value", Lean.Json.bool true) ]),
          ("arity", Lean.Json.num 0) ] :=
  rfl

end ReconstructionMetadata
end Tests
end Synthesis
end Whiel
