-- Author: Jesse Comer
import Whiel.Concrete.WhielNames.Order
import Whiel.Hoare.FixedAmbientProphecy
import Mathlib.Data.Finset.Sort

/-
  Certificate-facing task facade for Framework II over one
  fixed ambient `WhielNames` schema.

  The facade deliberately adds no second schema. The lifted
  loop, candidates, theta formulas, collapsed formulas, and
  every validity job all remain indexed by literal `Gamma`,
  the computed prophecy schema of one program-name input.
-/

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FixedAmbient

open Concrete

variable {D : Type} [Domain D]
variable {Gamma : UnnamedSchema WhielNames}

/-
  A fixed-ambient task is exactly the kernel-owned name
  correspondence for its loop-free body.
-/
abbrev Task (body : Cmd D Gamma) :=
  Hoare.WhielNamesProphecy.Task body

namespace Task

/- The one schema shared by the complete task. -/
def schema
    {body : Cmd D Gamma}
    (_task : Task body) : UnnamedSchema WhielNames :=
  Gamma

/- The task schema is definitionally the input schema. -/
theorem schema_eq
    {body : Cmd D Gamma}
    (task : Task body) :
    task.schema = Gamma := by
  rfl

/- One canonical ordinary-to-prophecy binding row. -/
structure Binding
    {body : Cmd D Gamma}
    (task : Task body) where
  source : Gamma.syms
  sourceAssigned :
    source.1 ∈ body.assignedSymbols
  sourceOrdinary : source.1.IsOrdinary
  prophecy : Gamma.syms
  prophecy_eq :
    prophecy.1 = .prophecy source.1.programName
  sameArity :
    Gamma.arity source = Gamma.arity prophecy

private theorem assigned_eq_ordinary_programName
    {body : Cmd D Gamma}
    (task : Task body)
    (assigned : body.assignedSymbols) :
    assigned.1 =
      .ordinary assigned.1.programName := by
  cases hName : assigned.1 with
  | ordinary name =>
      rfl
  | prophecy name =>
      have hOrdinary := task.assignedOrdinary
        assigned.1 assigned.2
      simp [WhielNames.IsOrdinary, hName] at hOrdinary

/- Build the checked binding for one assigned relation. -/
private def bindingOfAssigned
    {body : Cmd D Gamma}
    (task : Task body)
    (assigned : body.assignedSymbols) :
    Binding task :=
  let source : Gamma.syms :=
    ⟨assigned.1,
      Cmd.assignedSymbols_subset_syms body assigned.2⟩
  let name := assigned.1.programName
  have hAssigned :
      WhielNames.ordinary name ∈
        body.assignedSymbols := by
    rw [← task.assigned_eq_ordinary_programName
      assigned]
    exact assigned.2
  let prophecy : Gamma.syms :=
    ⟨.prophecy name, task.prophecyMem name hAssigned⟩
  { source := source
    sourceAssigned := assigned.2
    sourceOrdinary :=
      task.assignedOrdinary assigned.1 assigned.2
    prophecy := prophecy
    prophecy_eq := by
      rfl
    sameArity := by
      have hSource : source =
          ⟨WhielNames.ordinary name,
            Cmd.assignedSymbols_subset_syms body
              hAssigned⟩ := by
        apply Subtype.ext
        exact task.assigned_eq_ordinary_programName
          assigned
      rw [hSource]
      exact task.prophecyArity name hAssigned }

/-
  Bindings follow the canonical structural order of exactly
  the assigned relations.
-/
def bindings
    {body : Cmd D Gamma}
    (task : Task body) : List (Binding task) :=
  body.assignedSymbols.attach.sort.map fun assigned =>
    bindingOfAssigned task assigned

/- Binding sources cover the assignment set exactly. -/
theorem bindingSources_eq
    {body : Cmd D Gamma}
    (task : Task body) :
    task.bindings.map (fun binding => binding.source.1) =
      body.assignedSymbols.attach.sort.map Subtype.val := by
  simp [bindings, bindingOfAssigned]

/- Serialize one schema in canonical relation order. -/
private def schemaIdentityJson
    (key : WhielNames -> String)
    (schema : UnnamedSchema WhielNames) : Lean.Json :=
  Lean.Json.arr <| (schema.syms.attach.sort.map
    (fun relation =>
      Lean.Json.arr #[
        Lean.Json.str (key relation.1),
        Lean.Json.num
          (schema.arity relation)])).toArray

/-
  Complete same-schema task identity. The caller supplies
  the machine key; no presentation string participates.
-/
def identityJson
    {body : Cmd D Gamma}
    (task : Task body)
    (key : WhielNames -> String) : Lean.Json :=
  let bindingJson := task.bindings.map fun binding =>
    Lean.Json.arr #[
      Lean.Json.str (key binding.source.1),
      Lean.Json.str (key binding.prophecy.1),
      Lean.Json.num (Gamma.arity binding.source)]
  Lean.Json.arr #[
    Lean.Json.str
      "whiel-framework-ii-fixed-ambient-scope-v1",
    schemaIdentityJson key Gamma,
    Lean.Json.arr bindingJson.toArray]

end Task

end FixedAmbient
end FrameworkII
end Synthesis
end Whiel
