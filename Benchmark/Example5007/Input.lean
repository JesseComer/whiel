-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Closure by repeated squaring (legacy Example1056) against
  the naive evaluation of the linear closure program.

  Input `E` (binary).  Side 1 starts from `E` and adds
  `TSq ∘ TSq` each round, doubling the walk length it covers.
  Side 2 (compiled from)
    `T(x, y) :- E(x, y)`
    `T(x, y) :- E(x, z), T(z, y)`
  adds one edge per round.

  Independent programs, merged side by side.  Precondition
  `true`; postcondition `TSq = T`.

  Expected verdict: valid.  Same least fixpoint, reached at
  different rates: after round n the squaring side holds
  walks up to length 2^(n+1), the linear side up to n+2.
-/

namespace Whiel
namespace Benchmark
namespace Example5007

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {E, TSq, TSq_2, T, T_aux} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![ true ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      TSq_2 := ∅[2];
      TSq := E;
      WHILE (TSq ≠ TSq_2) DO
        TSq_2 := TSq;
        TSq := (TSq ∪ (π[0, 3] (σ[#1 = #2] (TSq_2 × TSq_2))))
      END;
      T_aux := ∅[2];
      T := (E ∪ π[0,3] (σ[#1 = #2] ((E × T_aux))));
      WHILE (¬((T = T_aux))) DO
        T_aux := T;
        T := (T ∪ (E ∪ π[0,3] (σ[#1 = #2] ((E × T_aux)))))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    (TSq = T)
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example5007
end Benchmark
end Whiel
