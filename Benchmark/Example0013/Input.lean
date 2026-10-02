-- Benchmark contributors: Jesse Comer, Fangzhu Shen
-- Refutable variant of Example0001.
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Transitive closure by naive iteration, under a false
  specification that a two-edge instance refutes.

  Schema `{E, T, S}` (all binary): `E` is the edge relation
  of a digraph, `T` the computed closure, and `S` the
  next-round value the loop compares against it. The
  program is the right-linear closure
    `T(x, y) :- E(x, y)`
    `T(x, y) :- E(x, z), T(z, y)`
  run naively: `S` is recomputed from `T` and the loop
  stops when the two agree.

  The schema, precondition and command are `Example0001`'s.
  The precondition is `true`, and the postcondition is the
  claim that the closure adds nothing to the edge relation,
  `T ⊆ E`.

  Expected verdict: invalid. On the two edges `(0, 1)` and
  `(1, 2)` the loop halts with `(0, 2)` in `T`, which is
  not an edge.
-/

namespace Whiel
namespace Benchmark
namespace Example0013

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {E, T, S} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![ true ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      T := ∅;
      S := (E ∪ (π[0, 3] (σ[#1 = #2] (E × T))));
      WHILE (S ≠ T) DO
        T := S;
        S := (E ∪ (π[0, 3] (σ[#1 = #2] (E × T))))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    (T ⊆ E)
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example0013
end Benchmark
end Whiel
