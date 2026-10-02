-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  A left-linear closure loop, specified as the least
  fixpoint of the non-linear closure program.

  Schema `{Base, T, T_aux, RBound}` (all binary): `Base` is
  the edge relation, `T` the computed closure, `T_aux` its
  previous round, and `RBound` a relation the program never
  reads or writes. The program is
    `T(x, y) :- Base(x, y)`
    `T(x, y) :- T(x, z), Base(z, y)`
  run naively: each round recomputes `T` from the previous
  round's value and the loop stops when it stabilizes.

  The reference program is the non-linear closure
    `Tc(x, y) :- Base(x, y)`
    `Tc(x, y) :- Tc(x, z), Tc(z, y)`

  The precondition says `RBound` is a pre-fixpoint of that
  non-linear program, `Base ∪ (RBound ∘ RBound) ⊆ RBound`.
  The postcondition is the least-fixpoint introduction
  obligation for it: the computed `T` is itself a
  pre-fixpoint, `Base ∪ (T ∘ T) ⊆ T`, and lies below the
  given one, `T ⊆ RBound`.

  Expected verdict: valid. Both programs compute the
  transitive closure of `Base`, so the loop's output is the
  least pre-fixpoint of the non-linear one.
-/

namespace Whiel
namespace Benchmark
namespace Example0106

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {Base, T, T_aux, RBound} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![
    ((Base ∪ (π[0, 3] (σ[#1 = #2] (RBound × RBound))))
      ⊆ RBound)
  ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      T_aux := ∅;
      T := Base;
      WHILE T ≠ T_aux DO
        T_aux := T;
        T :=
          (Base ∪
            (π[0, 3] (σ[#1 = #2] (T_aux × Base))))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    (((Base ∪ (π[0, 3] (σ[#1 = #2] (T × T)))) ⊆ T)
      ∧ (T ⊆ RBound))
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example0106
end Benchmark
end Whiel
