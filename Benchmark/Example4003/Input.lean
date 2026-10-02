-- Benchmark contributors: Leo Zhang, Val Tannen
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Right-linear transitive closure and a reformulation over
  a length-two path view, tested for containment.

  Global schema `{E}` (binary), the edges of a digraph. The
  global program is the standard right-linear transitive
  closure:
    `T(x, y) :- E(x, y)`
    `T(x, y) :- E(x, z), T(z, y)`

  Local schema `{V}` (ternary), a view that records a
  length-two path together with its midpoint. The proposed
  reformulation chains that view:
    `T↑(x, y) :- V(x, w, y)`
    `T↑(x, z) :- V(x, w, y), T↑(y, z)`

  The command is the two compiled programs run one after
  the other, and `T_aux` and `TUp_aux` are the snapshots
  the compiler generates. The single loop the tool verifies
  is computed from this sequence by the generic
  preprocessor.

  The precondition is the view constraint `V = E ∘ E` with
  the midpoint kept. The postcondition is the claim that
  the reformulation is contained in the global program,
  `T↑ ⊆ T`. The programs and the constraint are
  `Example4002`'s; only the claim differs, from an equality
  to this containment.

  Expected verdict: valid. `T↑` collects exactly the paths
  of even length at least two, and every path lies in `T`.
-/

namespace Whiel
namespace Benchmark
namespace Example4003

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {E, T, TUp, T_aux, TUp_aux} (arity: 2),
    {V} (arity: 3)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![
    (V = (π[0, 1, 3] (σ[#1 = #2] (E × E))))
  ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      T_aux := ∅[2];
      T :=
        (E ∪ (π[0, 3] (σ[#1 = #2] (E × T_aux))));
      WHILE (¬ (T = T_aux)) DO
        T_aux := T;
        T :=
          (T ∪
            (E ∪
              (π[0, 3] (σ[#1 = #2] (E × T_aux)))))
      END;
      TUp_aux := ∅[2];
      TUp :=
        ((π[0, 2] V) ∪
          (π[0, 4] (σ[#2 = #3] (V × TUp_aux))));
      WHILE (¬ (TUp = TUp_aux)) DO
        TUp_aux := TUp;
        TUp :=
          (TUp ∪
            ((π[0, 2] V) ∪
              (π[0, 4]
                (σ[#2 = #3] (V × TUp_aux)))))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    (TUp ⊆ T)
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example4003
end Benchmark
end Whiel
