-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  A worklist breadth-first search against the naive
  evaluation of the reachability query it implements.

  Inputs `Src` (unary, the sources) and `E` (binary).  Both
  sides compute the set of vertices reachable from `Src`.

  Side 1, worklist BFS (the hard case Example0161, kept
  verbatim including its dead initial assignment to `N`):
  `R` is the visited set, `W` the frontier, `N` the newly
  discovered vertices of the round.

  Side 2, naive evaluation (compiled from)
    `Reach(x) :- Src(x)`
    `Reach(y) :- Reach(x), E(x, y)`

  Independent programs, merged side by side.  Precondition
  `true`; postcondition `R = Reach`.  Example0161 states the
  same fact through a pre-fixpoint witness; this case states
  it directly against the naive program.

  Expected verdict: valid.
-/

namespace Whiel
namespace Benchmark
namespace Example5003

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {Src, R, W, N, Reach, Reach_aux} (arity: 1), {E} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![ true ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      R := Src;
      W := Src;
      N := Src;
      WHILE (W ≠ ∅) DO
        N := ((π[2] (σ[#0 = #1] (W × E))) ∖ R);
        R := (R ∪ N);
        W := N
      END;
      Reach_aux := ∅[1];
      Reach := (Src ∪ π[2] (σ[#0 = #1] ((Reach_aux × E))));
      WHILE (¬((Reach = Reach_aux))) DO
        Reach_aux := Reach;
        Reach := (Reach ∪ (Src ∪ π[2] (σ[#0 = #1] ((Reach_aux × E)))))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    (R = Reach)
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example5003
end Benchmark
end Whiel
