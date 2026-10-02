-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Casbin's depth-bounded role resolution against the unbounded
  role-hierarchy closure: the containment direction.

  Inputs `UserRole(u, r)` (direct binding) and `RoleInh(r, s)`
  (r inherits s).

  Side 1, Casbin (rbac/default-role-manager/role_manager.go,
  enforcer.go, checked 2026-09-15): the enforcer constructs the
  default role manager with maxHierarchyLevel = 10, and
  hasLinkHelper counts that level down once per inheritance step
  and fails below zero, so HasLink(u, s) holds exactly when s is
  reached from a direct role of u by at most ten inheritance
  edges. `HasB` is that relation, computed loop-free: StepA is
  `UserRole` and each of StepB … StepK adds one inheritance step
  to the previous one (`StepB = StepA ∪ StepA ∘ RoleInh`, and so
  on), so StepK holds the pairs reachable with at most ten steps
  and `HasB := StepK`. Each step has its own relation so that the
  preprocessor carries the whole computation as precondition
  equalities and the verified loop is the bare closure loop.

  Side 2, the unbounded closure (compiled from)
    `Has(u, r) :- UserRole(u, r)`
    `Has(u, t) :- Has(u, r), RoleInh(r, t)`
  the recursive has-role query of Example2035 and Example5004.

  Precondition `true`; postcondition `HasB ⊆ Has`.

  Expected verdict: valid. Every bounded derivation is a derivation of the unbounded closure. Note the rate mismatch: the bounded side is finished before the closure loop starts.
-/

namespace Whiel
namespace Benchmark
namespace Example5012

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {UserRole, RoleInh, StepA, StepB, StepC, StepD, StepE, StepF, StepG, StepH, StepI, StepJ, StepK, HasB, Has, Has_aux} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![ true ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      StepA := UserRole;
      StepB := (StepA ∪ (π[0, 3] (σ[#1 = #2] (StepA × RoleInh))));
      StepC := (StepB ∪ (π[0, 3] (σ[#1 = #2] (StepB × RoleInh))));
      StepD := (StepC ∪ (π[0, 3] (σ[#1 = #2] (StepC × RoleInh))));
      StepE := (StepD ∪ (π[0, 3] (σ[#1 = #2] (StepD × RoleInh))));
      StepF := (StepE ∪ (π[0, 3] (σ[#1 = #2] (StepE × RoleInh))));
      StepG := (StepF ∪ (π[0, 3] (σ[#1 = #2] (StepF × RoleInh))));
      StepH := (StepG ∪ (π[0, 3] (σ[#1 = #2] (StepG × RoleInh))));
      StepI := (StepH ∪ (π[0, 3] (σ[#1 = #2] (StepH × RoleInh))));
      StepJ := (StepI ∪ (π[0, 3] (σ[#1 = #2] (StepI × RoleInh))));
      StepK := (StepJ ∪ (π[0, 3] (σ[#1 = #2] (StepJ × RoleInh))));
      HasB := StepK;
      Has_aux := ∅[2];
      Has := (UserRole ∪ π[0,3] (σ[#1 = #2] ((Has_aux × RoleInh))));
      WHILE (¬((Has = Has_aux))) DO
        Has_aux := Has;
        Has := (Has ∪ (UserRole ∪ π[0,3] (σ[#1 = #2] ((Has_aux × RoleInh)))))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    (HasB ⊆ Has)
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example5012
end Benchmark
end Whiel
