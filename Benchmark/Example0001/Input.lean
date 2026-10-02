-- Benchmark contributors: Jesse Comer, Fangzhu Shen
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Transitive closure by naive iteration, under the weak
  specification that its result is transitively closed.

  Schema `{E, T, S}` (all binary): `E` is the edge relation
  of a digraph, `T` the computed closure, and `S` the
  next-round value the loop compares against it. The
  program is the right-linear closure
    `T(x, y) :- E(x, y)`
    `T(x, y) :- E(x, z), T(z, y)`
  run naively: `S` is recomputed from `T` and the loop
  stops when the two agree.

  The precondition is `true`. The postcondition asks only
  that the computed relation be transitively closed,
  `T ∘ T ⊆ T`; it states no upper bound, so nothing pins
  `T` from above.

  Expected verdict: valid. Every path decomposes into a
  first edge and a shorter path, so the least fixpoint the
  loop reaches is transitive.
-/

namespace Whiel
namespace Benchmark
namespace Example0001

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
    ((π[0, 3] (σ[#1 = #2] (T × T))) ⊆ T)
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example0001
end Benchmark
end Whiel
