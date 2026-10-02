-- Benchmark contributors: Fangzhu Shen, Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Example0163: Greatest-fixpoint safe set: shrinking iteration bounded below by Rb

  Kind: hard; algorithm: gfp. Converted from the retired original
  19-program invariant-synthesis benchmark (gen-* / hard).


  Canonical form of the earlier single-level encoding of this
  case: the same schema, precondition, command and postcondition.

  Datalog program(s) recorded for this case:
  * Datalog reading of the greatest-fixpoint safe set (written for this report; complement formulation: T = V ∖ Unsafe) (hand-written reading (report)):
      Unsafe(x) :- Bad(x).
      Unsafe(x) :- E(x, y), Unsafe(y).
      T(x) :- V(x), not Unsafe(x).
-/

namespace Whiel
namespace Benchmark
namespace Example0163

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {Bad, V, Rb, T, S} (arity: 1),
    {E} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![
    (Rb ⊆ ((V ∖ Bad) ∖ (π[0] (σ[#1 = #2] (E × (V ∖ Rb))))))
  ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      T := V;
      S := (V ∖ Bad);
      WHILE (S ≠ T) DO
        T := S;
        S := ((V ∖ Bad) ∖ (π[0] (σ[#1 = #2] (E × (V ∖ T)))))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    ((T = ((V ∖ Bad) ∖ (π[0] (σ[#1 = #2] (E × (V ∖ T)))))) ∧ (Rb ⊆ T))
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example0163
end Benchmark
end Whiel
