-- Benchmark contributors: Fangzhu Shen, Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Example0115: Prefix-equivalence: naive all_paths_via_even_odd (linear) computes lfp of tc_left

  Kind: prefix-equivalence; algorithm: naive. Converted from the
  retired classic Datalog-program benchmark collection (the 0428
  wave).


  Canonical form of the earlier single-level encoding of this case:
  the same schema, precondition, command and postcondition.

  Datalog program(s) recorded for this case:
  * all_paths_via_even_odd_linear (legacy inventory):
      -- all_paths_via_even_odd_linear
      -- Executed WHIEL program
      OL(x,y) :- E(x,y).
      OL(x,y) :- E(x,z), EL(z,y).
      EL(x,y) :- E(x,z), OL(z,y).
      T(x,y) :- EL(x,y).
      T(x,y) :- OL(x,y).
  * tc_left (legacy inventory):
      -- tc_left
      -- Catalog/source target intent only; not executed by the WHIEL command
      tcl(x, y) :- base(x, y).
      tcl(x, y) :- tcl(x, z), base(z, y).
      -- Actual formal PRE/POST reference only; not executed (right-recursive E composed with T)
      T_right(x,y) :- E(x,y).
      T_right(x,y) :- E(x,z), T_right(z,y).
-/

namespace Whiel
namespace Benchmark
namespace Example0115

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {E, R, Ta, Sa, Tb, Sb, Tc, Sc} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![
    ((E ∪ (π[0, 3] (σ[#1 = #2] (E × R)))) ⊆ R)
  ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      Ta := ∅;
      Tb := ∅;
      Tc := ∅;
      Sa := (π[0, 3] (σ[#1 = #2] (E × Tb)));
      Sb := (E ∪ (π[0, 3] (σ[#1 = #2] (E × Ta))));
      Sc := (Ta ∪ Tb);
      WHILE ¬(((Sa = Ta) ∧ ((Sb = Tb) ∧ (Sc = Tc)))) DO
        Ta := Sa;
        Tb := Sb;
        Tc := Sc;
        Sa := (π[0, 3] (σ[#1 = #2] (E × Tb)));
        Sb := (E ∪ (π[0, 3] (σ[#1 = #2] (E × Ta))));
        Sc := (Ta ∪ Tb)
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    (((E ∪ (π[0, 3] (σ[#1 = #2] (E × Tc)))) ⊆ Tc) ∧ (Tc ⊆ R))
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example0115
end Benchmark
end Whiel
