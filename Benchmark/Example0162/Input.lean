-- Benchmark contributors: Fangzhu Shen, Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Example0162: Two-player game reachability mixing existential and universal successor steps

  Kind: hard; algorithm: naive. Converted from the retired
  original 19-program invariant-synthesis benchmark (gen-* /
  hard).


  Canonical form of the earlier single-level encoding of this
  case: the same schema, precondition, command and postcondition.

  Datalog program(s) recorded for this case:
  * Datalog reading of the game reachability (written for this report; the operator is monotone, T is its least fixpoint; the universal step is spelled with a negated escape relation) (hand-written reading (report)):
      T(x) :- Target(x).
      T(x) :- Pa(x), E(x, y), T(y).             % player-A vertex with some successor in T
      T(x) :- V(x), not Pa(x), not Escape(x).    % player-B vertex all of whose successors are in T
      Escape(x) :- E(x, y), not T(y).
-/

namespace Whiel
namespace Benchmark
namespace Example0162

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {Target, V, Pa, Rc, T, S} (arity: 1),
    {E} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![
    ((((Target ∪ (π[0] (σ[#0 = #1] (Pa × (π[0] (σ[#1 = #2] (E × Rc))))))) ∪ ((V ∖ Pa) ∖ (π[0] (σ[#1 = #2] (E × (V ∖ Rc)))))) ⊆ Rc) ∧ (Target ⊆ Rc))
  ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      T := ∅;
      S := ((Target ∪ (π[0] (σ[#0 = #1] (Pa × (π[0] (σ[#1 = #2] (E × T))))))) ∪ ((V ∖ Pa) ∖ (π[0] (σ[#1 = #2] (E × (V ∖ T))))));
      WHILE (S ≠ T) DO
        T := S;
        S := ((Target ∪ (π[0] (σ[#0 = #1] (Pa × (π[0] (σ[#1 = #2] (E × T))))))) ∪ ((V ∖ Pa) ∖ (π[0] (σ[#1 = #2] (E × (V ∖ T))))))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    ((T = ((Target ∪ (π[0] (σ[#0 = #1] (Pa × (π[0] (σ[#1 = #2] (E × T))))))) ∪ ((V ∖ Pa) ∖ (π[0] (σ[#1 = #2] (E × (V ∖ T))))))) ∧ (T ⊆ Rc))
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example0162
end Benchmark
end Whiel
