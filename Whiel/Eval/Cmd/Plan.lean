-- Author: Jesse Comer
import Whiel.Eval.Cmd.Fast

/-
  A minimal preparation and physical-planning boundary for
  fast Whiel command evaluation.

  This module intentionally supplies only the generic plan.
  Later plans may attach physical data or choose specialized
  evaluators without changing the command-level interface.
-/

------------------------------------------------------------
-- Prepared Commands and Physical Plans
------------------------------------------------------------

namespace Whiel

namespace CmdPlan

variable {A D : Type}
variable [RelationNames A]
variable [Domain D] [LinearOrder D] [Hashable D]
variable {Γ : UnnamedSchema A}

/- A command prepared for physical planning. -/
structure PreparedCmd
    (D : Type)
    [Domain D] [LinearOrder D] [Hashable D]
    (Γ : UnnamedSchema A) : Type where
  source : Cmd D Γ

/- A selected physical command-evaluation strategy. -/
inductive PhysicalPlan
    (D : Type)
    [Domain D] [LinearOrder D] [Hashable D]
    (Γ : UnnamedSchema A) : Type where
| generic (prepared : PreparedCmd D Γ) :
    PhysicalPlan D Γ

/- Prepare a command without changing its meaning. -/
def prepare (C : Cmd D Γ) : PreparedCmd D Γ :=
  ⟨C⟩

/- Select a physical plan for the current runtime state. -/
def choose
    (prepared : PreparedCmd D Γ)
    (_S : FastInstance D Γ) : PhysicalPlan D Γ :=
  .generic prepared

/- Execute a selected physical plan. -/
def execute
    (fuel : Nat)
    (plan : PhysicalPlan D Γ)
    (S : FastInstance D Γ) : CmdFast.Result D Γ :=
  match plan with
  | .generic prepared =>
      CmdFast.eval fuel prepared.source S

/- Prepare, select, and execute a command. -/
def eval
    (fuel : Nat)
    (C : Cmd D Γ)
    (S : FastInstance D Γ) : CmdFast.Result D Γ :=
  execute fuel (choose (prepare C) S) S

end CmdPlan

end Whiel

------------------------------------------------------------
-- Physical-Plan Specifications
------------------------------------------------------------

namespace Whiel

namespace CmdPlan

variable {A D : Type}
variable [RelationNames A]
variable [Domain D] [LinearOrder D] [Hashable D]
variable {Γ : UnnamedSchema A}

/- Planned evaluation is currently the generic evaluator. -/
theorem eval_eq_cmdFast
    (fuel : Nat)
    (C : Cmd D Γ)
    (S : FastInstance D Γ) :
    eval fuel C S = CmdFast.eval fuel C S := by
  rfl

/-
  A halted physical plan is sound for its source command.
-/
theorem execute_sound
    {fuel : Nat}
    {plan : PhysicalPlan D Γ}
    {S S' : FastInstance D Γ}
    (hEval : execute fuel plan S = .halted S') :
    Cmd.BigStep
      (match plan with
      | .generic prepared => prepared.source)
      S.toInstance S'.toInstance := by
  cases plan with
  | generic prepared =>
      exact CmdFast.eval_sound hEval

/-
  Halted planned evaluation is sound for the input command.
-/
theorem eval_sound
    {fuel : Nat}
    {C : Cmd D Γ}
    {S S' : FastInstance D Γ}
    (hEval : eval fuel C S = .halted S') :
    Cmd.BigStep C S.toInstance S'.toInstance := by
  rw [eval_eq_cmdFast] at hEval
  exact CmdFast.eval_sound hEval

end CmdPlan

end Whiel
