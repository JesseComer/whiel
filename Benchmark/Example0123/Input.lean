-- Benchmark contributors: Fangzhu Shen, Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Example0123: Prefix-equivalence: naive even_odd_nonlinear computes lfp of even_odd_linear

  Kind: prefix-equivalence; algorithm: naive. Converted from the
  retired classic Datalog-program benchmark collection (the 0428
  wave).


  Canonical form of the earlier single-level encoding of this case:
  the same schema, precondition, command and postcondition.

  Datalog program(s) recorded for this case:
  * even_odd_linear (classic .dl source program):
      -- even_odd_linear
      -- Formal PRE/POST reference only; not executed by the WHIEL command
      OL(x,y) :- E(x,y).
      OL(x,y) :- E(x,z), EL(z,y).
      EL(x,y) :- E(x,z), OL(z,y).
  * even_odd_nonlinear (classic .dl source program):
      -- even_odd_nonlinear
      -- Executed WHIEL program
      OL(x,y) :- E(x,y).
      EL(x,y) :- E(x,z), E(z,y).
      OL(x,y) :- OL(x,z), EL(z,y).
      OL(x,y) :- EL(x,z), OL(z,y).
      EL(x,y) :- EL(x,z), EL(z,y).
      EL(x,y) :- OL(x,z), OL(z,y).
-/

namespace Whiel
namespace Benchmark
namespace Example0123

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {E, Ra, Rb, Ta, Sa, Tb, Sb} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![
    (((π[0, 3] (σ[#1 = #2] (E × Rb))) ⊆ Ra) ∧ ((E ∪ (π[0, 3] (σ[#1 = #2] (E × Ra)))) ⊆ Rb))
  ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      Ta := ∅;
      Tb := ∅;
      Sa := (((π[0, 3] (σ[#1 = #2] (E × E))) ∪ (π[0, 3] (σ[#1 = #2] (Ta × Ta)))) ∪ (π[0, 3] (σ[#1 = #2] (Tb × Tb))));
      Sb := ((E ∪ (π[0, 3] (σ[#1 = #2] (Tb × Ta)))) ∪ (π[0, 3] (σ[#1 = #2] (Ta × Tb))));
      WHILE ¬(((Sa = Ta) ∧ (Sb = Tb))) DO
        Ta := Sa;
        Tb := Sb;
        Sa := (((π[0, 3] (σ[#1 = #2] (E × E))) ∪ (π[0, 3] (σ[#1 = #2] (Ta × Ta)))) ∪ (π[0, 3] (σ[#1 = #2] (Tb × Tb))));
        Sb := ((E ∪ (π[0, 3] (σ[#1 = #2] (Tb × Ta)))) ∪ (π[0, 3] (σ[#1 = #2] (Ta × Tb))))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    (((π[0, 3] (σ[#1 = #2] (E × Tb))) ⊆ Ta) ∧ (((E ∪ (π[0, 3] (σ[#1 = #2] (E × Ta)))) ⊆ Tb) ∧ ((Ta ⊆ Ra) ∧ (Tb ⊆ Rb))))
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example0123
end Benchmark
end Whiel
