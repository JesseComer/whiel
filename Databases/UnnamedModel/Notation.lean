-- Author: Jesse Comer
import Databases.UnnamedModel.PrettyPrint

/-
  Typed notation for unnamed-instance examples.

  Key declarations include:
    * `inst![...]`
-/

------------------------------------------------------------
-- Instance Literals
------------------------------------------------------------

namespace Instance

namespace Notation

variable {A D : Type}
variable [RelationNames A] [Domain D]

def Entry
    (D : Type) [Domain D]
    (Γ : UnnamedSchema A) : Type :=
  Sigma fun X : Γ.syms => FinRelation D (Γ.arity X)

/- Build an instance from duplicate-free updates. -/
def fromList
    (Γ : UnnamedSchema A)
    (entries : List (Entry D Γ))
    (_hNoDup :
      (entries.map (fun entry => entry.1.1)).Nodup) :
    Instance D Γ :=
  entries.foldl
    (fun I entry =>
      Instance.update I entry.1 entry.2)
    (Instance.empty Γ)

end Notation

end Instance

declare_syntax_cat dbt_inst_update

syntax term " := " term : dbt_inst_update

syntax "inst![" term "]" : term
syntax
  "inst![" term " | " dbt_inst_update
    ("; " dbt_inst_update)* "]" :
  term
syntax "inst![" "{" "Schema" ":" term "}" "]" : term
syntax
  "inst![" "{" "Schema" ":" term "}"
    "{" dbt_inst_update ("; " dbt_inst_update)* "}" "]" :
  term

open Lean Macro

private def instUpdateEntry
    (u : TSyntax `dbt_inst_update) :
    MacroM Term := do
  match u with
  | `(dbt_inst_update| $X:term := $R:term) =>
      `(Sigma.mk (UnnamedSchema.sym _ $X) $R)
  | _ =>
      throwUnsupported

macro_rules
| `(inst![$Γ:term]) =>
    `(Instance.empty $Γ)
| `(inst![{ Schema: $Γ:term }]) =>
    `(Instance.empty $Γ)

macro_rules
| `(inst![$Γ:term | $u:dbt_inst_update
      $[; $us:dbt_inst_update]*]) => do
    let first ← instUpdateEntry u
    let rest ← us.mapM instUpdateEntry
    `(Instance.Notation.fromList
      $Γ
      [$first, $[$rest],*]
      (by decide))
| `(inst![
      { Schema: $Γ:term }
      { $u:dbt_inst_update $[; $us:dbt_inst_update]* }
    ]) => do
    let first ← instUpdateEntry u
    let rest ← us.mapM instUpdateEntry
    `(Instance.Notation.fromList
      $Γ
      [$first, $[$rest],*]
      (by decide))
