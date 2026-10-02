-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Datafrog's semi-naive delta evaluation of a reachability
  query against the naive evaluation of the same query.

  Input `EdgeF` (binary).  Both sides compute `Nodes(y, x)`:
  y is reachable from x by one or more `EdgeF` steps, i.e.
  the transpose of the transitive closure.

  Side 1, Datafrog (legacy Example2039): the delta loop
  joins only the last round's new facts `DeltaN` with
  `EdgeF`, subtracts what is known, and stops on an empty
  delta.

  Side 2, naive evaluation (compiled from)
    `Reach(y, x) :- EdgeF(x, y)`
    `Reach(z, x) :- Reach(y, x), EdgeF(y, z)`
  `Reach_aux` is the compiler's snapshot.

  Independent programs, merged side by side.  Precondition
  `true`; postcondition `Nodes = Reach`.

  Expected verdict: valid.  Same least fixpoint; both loops
  add the walks of length n+1 in round n.
-/

namespace Whiel
namespace Benchmark
namespace Example5002

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {EdgeF, Nodes, DeltaN, NewN, Reach, Reach_aux} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![ true ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      Nodes := (π[1, 0] EdgeF);
      DeltaN := (π[1, 0] EdgeF);
      WHILE (DeltaN ≠ ∅) DO
        NewN := ((π[3, 1] (σ[#0 = #2] (DeltaN × EdgeF))) ∖ Nodes);
        Nodes := (Nodes ∪ NewN);
        DeltaN := NewN
      END;
      Reach_aux := ∅[2];
      Reach := (π[1,0] (EdgeF) ∪ π[3,1] (σ[#0 = #2] ((Reach_aux × EdgeF))));
      WHILE (¬((Reach = Reach_aux))) DO
        Reach_aux := Reach;
        Reach := (Reach ∪ (π[1,0] (EdgeF) ∪ π[3,1] (σ[#0 = #2] ((Reach_aux × EdgeF)))))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    (Nodes = Reach)
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example5002
end Benchmark
end Whiel
