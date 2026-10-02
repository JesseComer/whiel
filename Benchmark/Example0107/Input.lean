-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Spine benchmark Example0007: Prefix-equivalence: naive
  tc_nonlinear computes lfp of tc_left


  Canonical form of the earlier single-level encoding of this case:
  the same schema, precondition, command and postcondition; the
  snapshot relation T_2 is now T_aux.

  Datalog program(s) recorded for this case:
  * tc_left (classic .dl source program):
      -- tc_left
      -- Formal PRE/POST reference only; not executed by the WHIEL command
      tcl(x, y) :- base(x, y).
      tcl(x, y) :- tcl(x, z), base(z, y).
  * tc_nonlinear (classic .dl source program):
      -- tc_nonlinear
      -- Executed WHIEL program
      tc(x, y) :- base(x, y).
      tc(x, y) :- tc(x, z), tc(z, y).
-/

namespace Whiel
namespace Benchmark
namespace Example0107

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {Base, T, T_aux, RBound} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![
    ((Base ∪ (π[0, 3] (σ[#1 = #2] (RBound × Base)))) ⊆ RBound)
  ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      T_aux := ∅;
      T := Base;
      WHILE T ≠ T_aux DO
        T_aux := T;
        T := (Base ∪ (π[0, 3] (σ[#1 = #2] (T_aux × T_aux))))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    (((Base ∪ (π[0, 3] (σ[#1 = #2] (T × Base)))) ⊆ T) ∧ (T ⊆ RBound))
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example0107
end Benchmark
end Whiel
