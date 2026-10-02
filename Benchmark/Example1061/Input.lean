-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Claude benchmark Example0002: Equivalence of computed same-
  generation with lfp of the same-generation rules (pre-fixpoint)


  Canonical form of the earlier single-level encoding of this case:
  the same schema, precondition, command and postcondition; the
  snapshot relation SG_2 is now SG_aux.

  Datalog program(s) recorded for this case:
  * prog_p (production check):
      SGC(x1, y1) :- Flat(x1, y1).
      SGC(x1, y1) :- Up(x1, z1), SGC(z1, x2), Down(x2, y1).
-/

namespace Whiel
namespace Benchmark
namespace Example1061

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {Flat, Up, Down, SG, SG_aux, K} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![
    ((Flat ∪ (π[0, 3] (σ[#1 = #2] (Up × (π[0, 3] (σ[#1 = #2] (K × Down))))))) ⊆ K)
  ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      SG_aux := ∅;
      SG := Flat;
      WHILE SG ≠ SG_aux DO
        SG_aux := SG;
        SG := (Flat ∪ (π[0, 3] (σ[#1 = #2] (Up × (π[0, 3] (σ[#1 = #2] (SG_aux × Down)))))))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    (((Flat ⊆ SG) ∧ ((π[0, 3] (σ[#1 = #2] (Up × (π[0, 3] (σ[#1 = #2] (SG × Down)))))) ⊆ SG)) ∧ (SG ⊆ K))
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example1061
end Benchmark
end Whiel
