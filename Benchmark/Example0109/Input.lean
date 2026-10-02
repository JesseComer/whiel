-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Spine benchmark Example0009: Containment: red-blue alternating
  paths ⊆ TC(R ∪ B)


  Canonical form of the earlier single-level encoding of this case:
  the same schema, precondition, command and postcondition; the
  snapshot relations RR_2 is now RR_aux, BB_2 is now BB_aux, RB_2
  is now RB_aux, BR_2 is now BR_aux.

  Datalog program(s) recorded for this case:
  * red_blue_linear (legacy inventory):
      -- red_blue_linear
      -- Executed WHIEL program
      RR(x,y) :- R(x,y).
      BB(x,y) :- B(x,y).
      RB(x,y) :- RR(x,z), B(z,y).
      BR(x,y) :- BB(x,z), R(z,y).
      RR(x,y) :- R(x,z), BR(z,y).
      BB(x,y) :- B(x,z), RB(z,y).
  * tc_of_union (legacy inventory):
      -- tc_of_union
      -- Catalog/source target intent only; not executed by the WHIEL command
      E(x,y) :- R(x,y).
      E(x,y) :- B(x,y).
      T(x,y) :- E(x,y).
      T(x,y) :- E(x,z), T(z,y).
      -- Actual formal PRE/POST reference only; not executed (left-recursive T composed with R union B)
      E_union(x,y) :- R(x,y).
      E_union(x,y) :- B(x,y).
      T_left(x,y) :- E_union(x,y).
      T_left(x,z) :- T_left(x,y), E_union(y,z).
-/

namespace Whiel
namespace Benchmark
namespace Example0109

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {R, B, RR, BB, RB, BR, RR_aux, BB_aux, RB_aux, BR_aux, RBound} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![
    (((R ∪ B) ∪ (π[0, 3] (σ[#1 = #2] (RBound × (R ∪ B))))) ⊆ RBound)
  ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      RR_aux := ∅;
      BB_aux := ∅;
      RB_aux := ∅;
      BR_aux := ∅;
      RR := R;
      BB := B;
      RB := (π[0, 3] (σ[#1 = #2] (R × B)));
      BR := (π[0, 3] (σ[#1 = #2] (B × R)));
      WHILE ((RR ≠ RR_aux) ∨ (BB ≠ BB_aux)) ∨ ((RB ≠ RB_aux) ∨ (BR ≠ BR_aux)) DO
        RR_aux := RR;
        BB_aux := BB;
        RB_aux := RB;
        BR_aux := BR;
        RB := (RB ∪ (π[0, 3] (σ[#1 = #2] (RR_aux × B))));
        BR := (BR ∪ (π[0, 3] (σ[#1 = #2] (BB_aux × R))));
        RR := (RR ∪ (π[0, 3] (σ[#1 = #2] (R × BR_aux))));
        BB := (BB ∪ (π[0, 3] (σ[#1 = #2] (B × RB_aux))))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    ((((RR ∪ BB) ∪ RB) ∪ BR) ⊆ RBound)
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example0109
end Benchmark
end Whiel
