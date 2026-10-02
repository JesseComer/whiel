-- Benchmark contributors: Fangzhu Shen, Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Example0117: Prefix-equivalence: naive all_paths_via_even_odd (non-linear) computes lfp of tc_left

  Kind: prefix-equivalence; algorithm: naive. Converted from the
  retired classic Datalog-program benchmark collection (the 0428
  wave).


  Canonical form of the earlier single-level encoding of this case:
  the same schema, precondition, command and postcondition.

  Datalog program(s) recorded for this case:
  * all_paths_via_even_odd_nonlinear (legacy inventory):
      -- all_paths_via_even_odd_nonlinear
      -- Executed WHIEL program
      OL(x,y) :- E(x,y).
      EL(x,y) :- E(x,z), E(z,y).
      OL(x,y) :- OL(x,z), EL(z,y).
      OL(x,y) :- EL(x,z), OL(z,y).
      EL(x,y) :- EL(x,z), EL(z,y).
      EL(x,y) :- OL(x,z), OL(z,y).
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
namespace Example0117

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
      Sa := (((π[0, 3] (σ[#1 = #2] (E × E))) ∪ (π[0, 3] (σ[#1 = #2] (Ta × Ta)))) ∪ (π[0, 3] (σ[#1 = #2] (Tb × Tb))));
      Sb := ((E ∪ (π[0, 3] (σ[#1 = #2] (Tb × Ta)))) ∪ (π[0, 3] (σ[#1 = #2] (Ta × Tb))));
      Sc := (Ta ∪ Tb);
      WHILE ¬(((Sa = Ta) ∧ ((Sb = Tb) ∧ (Sc = Tc)))) DO
        Ta := Sa;
        Tb := Sb;
        Tc := Sc;
        Sa := (((π[0, 3] (σ[#1 = #2] (E × E))) ∪ (π[0, 3] (σ[#1 = #2] (Ta × Ta)))) ∪ (π[0, 3] (σ[#1 = #2] (Tb × Tb))));
        Sb := ((E ∪ (π[0, 3] (σ[#1 = #2] (Tb × Ta)))) ∪ (π[0, 3] (σ[#1 = #2] (Ta × Tb))));
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

end Example0117
end Benchmark
end Whiel
