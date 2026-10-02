-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Two ways access-control engines answer "does user u
  hold role r": materialize the role hierarchy's closure
  and join once (Casbin's role manager), or recurse over
  the hierarchy from the user's direct roles (OPA/Zanzibar
  style, legacy Example2035 without its violation query).

  Inputs `UserRole(u, r)` and `RoleInh(r, s)` (r inherits s).

  Side 1, materialize then join (two compiled programs, the
  second reading the first's output). Casbin's default role
  manager bounds this traversal at ten inheritance levels
  (maxHierarchyLevel = 10); the closure here is unbounded, and
  Example5012/5013 cover the bounded version:
    `Inh(r, s) :- RoleInh(r, s)`
    `Inh(r, t) :- Inh(r, s), RoleInh(s, t)`
    `HasM(u, r) :- UserRole(u, r)`
    `HasM(u, t) :- UserRole(u, r), Inh(r, t)`

  Side 2, recursive query (compiled from)
    `Has(u, r) :- UserRole(u, r)`
    `Has(u, t) :- Has(u, r), RoleInh(r, t)`

  The join program reads `Inh`, so the sequence is
  dependent and the preprocessor draws flags.  Precondition
  `true`; postcondition `HasM = Has`.

  Expected verdict: valid.  `Has = UserRole ∘ RoleInh*` on
  both sides; the sides reach it at different rates (the
  closure must finish before the join runs).
-/

namespace Whiel
namespace Benchmark
namespace Example5004

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {UserRole, RoleInh, Inh, Inh_aux, HasM, HasM_aux, Has, Has_aux} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![ true ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      Inh_aux := ∅[2];
      Inh := (RoleInh ∪ π[0,3] (σ[#1 = #2] ((Inh_aux × RoleInh))));
      WHILE (¬((Inh = Inh_aux))) DO
        Inh_aux := Inh;
        Inh := (Inh ∪ (RoleInh ∪ π[0,3] (σ[#1 = #2] ((Inh_aux × RoleInh)))))
      END;
      HasM_aux := ∅[2];
      HasM := (UserRole ∪ π[0,3] (σ[#1 = #2] ((UserRole × Inh))));
      WHILE (¬((HasM = HasM_aux))) DO
        HasM_aux := HasM;
        HasM := (HasM ∪ (UserRole ∪ π[0,3] (σ[#1 = #2] ((UserRole × Inh)))))
      END;
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
    (HasM = Has)
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example5004
end Benchmark
end Whiel
