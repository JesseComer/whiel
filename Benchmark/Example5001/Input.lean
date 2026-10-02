-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  PostgreSQL's WITH RECURSIVE executor against the naive
  evaluation of the same recursive query.

  Inputs `Base` and `Edge` (binary): the base term of the
  recursive union and the edge relation of its recursive
  term.  Both sides compute the rows reachable from `Base`
  by appending `Edge` steps, that is `Base ∘ Edge*`.

  Side 1, PostgreSQL (legacy Example2037): the recursive
  UNION executor keeps a working table `WorkT`, joins only
  the last round's rows with `Edge`, removes rows already
  in the result (`Inter`) and stops when nothing is new.

  Side 2, naive evaluation (compiled by the repository's
  naive Datalog compiler from)
    `Tcl(x, y) :- Base(x, y)`
    `Tcl(x, y) :- Tcl(x, z), Edge(z, y)`
  `Tcl_aux` is the snapshot the compiler generates.

  The command is the two programs run one after the other;
  they write disjoint relations, so the preprocessor merges
  them side by side.  Precondition `true`; postcondition
  `Res = Tcl`.

  Expected verdict: valid.  Both sides compute the least
  fixpoint of the same operator; the executor merely avoids
  re-deriving rows.  Both frontiers advance one edge per
  round, so the two loops stay in step.
-/

namespace Whiel
namespace Benchmark
namespace Example5001

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {Base, Edge, Res, WorkT, Inter, Tcl, Tcl_aux} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![ true ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      Res := Base;
      WorkT := Base;
      WHILE (WorkT ≠ ∅) DO
        Inter := ((π[0, 3] (σ[#1 = #2] (WorkT × Edge))) ∖ Res);
        Res := (Res ∪ Inter);
        WorkT := Inter
      END;
      Tcl_aux := ∅[2];
      Tcl := (Base ∪ π[0,3] (σ[#1 = #2] ((Tcl_aux × Edge))));
      WHILE (¬((Tcl = Tcl_aux))) DO
        Tcl_aux := Tcl;
        Tcl := (Tcl ∪ (Base ∪ π[0,3] (σ[#1 = #2] ((Tcl_aux × Edge)))))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    (Res = Tcl)
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example5001
end Benchmark
end Whiel
