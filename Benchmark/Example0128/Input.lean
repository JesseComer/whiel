-- Benchmark contributors: Fangzhu Shen, Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Example0128: Containment: naive red_blue_nonlinear outputs ⊆ pre-fixpoint of TC(R ∪ B)

  Kind: containment; algorithm: naive. Converted from the retired
  classic Datalog-program benchmark collection (the 0428 wave).


  Canonical form of the earlier single-level encoding of this case:
  the same schema, precondition, command and postcondition.

  Datalog program(s) recorded for this case:
  * red_blue_nonlinear (classic .dl source program):
      -- red_blue_nonlinear
      -- Executed WHIEL program
      RR(x,y) :- R(x,y).
      BB(x,y) :- B(x,y).
      RB(x,y) :- R(x,z), B(z,y).
      BR(x,y) :- B(x,z), R(z,y).
      RR(x,y) :- RR(x,z), BR(z,y).
      BB(x,y) :- BB(x,z), RB(z,y).
      RB(x,y) :- RR(x,z), BB(z,y).
      BR(x,y) :- BB(x,z), RR(z,y).
  * tc_of_union (classic .dl source program):
      -- tc_of_union
      -- Formal PRE/POST reference only; not executed by the WHIEL command
      E(x,y) :- R(x,y).
      E(x,y) :- B(x,y).
      T(x,y) :- E(x,y).
      T(x,y) :- E(x,z), T(z,y).
-/

namespace Whiel
namespace Benchmark
namespace Example0128

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {B, RX, R, Ta, Sa, Tb, Sb, Tc, Sc, Td, Sd} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![
    ((((RX ∪ B) ∪ (π[0, 3] (σ[#1 = #2] (RX × R)))) ∪ (π[0, 3] (σ[#1 = #2] (B × R)))) ⊆ R)
  ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      Ta := ∅;
      Tb := ∅;
      Tc := ∅;
      Td := ∅;
      Sa := (B ∪ (π[0, 3] (σ[#1 = #2] (Ta × Tc))));
      Sb := ((π[0, 3] (σ[#1 = #2] (B × RX))) ∪ (π[0, 3] (σ[#1 = #2] (Ta × Td))));
      Sc := ((π[0, 3] (σ[#1 = #2] (RX × B))) ∪ (π[0, 3] (σ[#1 = #2] (Td × Ta))));
      Sd := (RX ∪ (π[0, 3] (σ[#1 = #2] (Td × Tb))));
      WHILE ¬(((Sa = Ta) ∧ ((Sb = Tb) ∧ ((Sc = Tc) ∧ (Sd = Td))))) DO
        Ta := Sa;
        Tb := Sb;
        Tc := Sc;
        Td := Sd;
        Sa := (B ∪ (π[0, 3] (σ[#1 = #2] (Ta × Tc))));
        Sb := ((π[0, 3] (σ[#1 = #2] (B × RX))) ∪ (π[0, 3] (σ[#1 = #2] (Ta × Td))));
        Sc := ((π[0, 3] (σ[#1 = #2] (RX × B))) ∪ (π[0, 3] (σ[#1 = #2] (Td × Ta))));
        Sd := (RX ∪ (π[0, 3] (σ[#1 = #2] (Td × Tb))))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    ((Ta ⊆ R) ∧ ((Tb ⊆ R) ∧ ((Tc ⊆ R) ∧ (Td ⊆ R))))
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example0128
end Benchmark
end Whiel
