-- Benchmark contributors: Fangzhu Shen, Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Odd and even paths computed by a linear program,
  specified as the least fixpoint of the non-linear
  odd/even program.

  Schema `{E, Ra, Rb, Ta, Sa, Tb, Sb}` (all binary): `E` is
  the edge relation, `Ta` and `Tb` the computed even and
  odd relations, `Sa` and `Sb` their next-round values, and
  `Ra`, `Rb` two relations the program never reads or
  writes. The linear program is
    `Tb(x, y) :- E(x, y)`
    `Tb(x, y) :- E(x, z), Ta(z, y)`
    `Ta(x, y) :- E(x, z), Tb(z, y)`
  run naively, so `Tb` collects the paths of odd length and
  `Ta` those of even length at least two.

  The reference program is the non-linear odd/even pair
    `Ta(x, y) :- E(x, z), E(z, y)`
    `Ta(x, y) :- Ta(x, z), Ta(z, y)`
    `Ta(x, y) :- Tb(x, z), Tb(z, y)`
    `Tb(x, y) :- E(x, y)`
    `Tb(x, y) :- Tb(x, z), Ta(z, y)`
    `Tb(x, y) :- Ta(x, z), Tb(z, y)`

  The precondition says the pair `Ra`, `Rb` is a
  pre-fixpoint of that non-linear program. The
  postcondition is the least-fixpoint introduction
  obligation for it: the computed pair `Ta`, `Tb` is itself
  a pre-fixpoint, and `Ta ⊆ Ra` and `Tb ⊆ Rb`.

  Expected verdict: valid. Both programs compute the paths
  of even and of odd length, so the linear loop's output is
  the least pre-fixpoint of the non-linear one.
-/

namespace Whiel
namespace Benchmark
namespace Example0125

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {E, Ra, Rb, Ta, Sa, Tb, Sb} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![
    (((((π[0, 3] (σ[#1 = #2] (E × E))) ∪
          (π[0, 3] (σ[#1 = #2] (Ra × Ra)))) ∪
        (π[0, 3] (σ[#1 = #2] (Rb × Rb)))) ⊆ Ra)
      ∧ (((E ∪
            (π[0, 3] (σ[#1 = #2] (Rb × Ra)))) ∪
          (π[0, 3] (σ[#1 = #2] (Ra × Rb)))) ⊆ Rb))
  ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      Ta := ∅;
      Tb := ∅;
      Sa := (π[0, 3] (σ[#1 = #2] (E × Tb)));
      Sb := (E ∪ (π[0, 3] (σ[#1 = #2] (E × Ta))));
      WHILE ¬(((Sa = Ta) ∧ (Sb = Tb))) DO
        Ta := Sa;
        Tb := Sb;
        Sa := (π[0, 3] (σ[#1 = #2] (E × Tb)));
        Sb :=
          (E ∪ (π[0, 3] (σ[#1 = #2] (E × Ta))))
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    (((((π[0, 3] (σ[#1 = #2] (E × E))) ∪
          (π[0, 3] (σ[#1 = #2] (Ta × Ta)))) ∪
        (π[0, 3] (σ[#1 = #2] (Tb × Tb)))) ⊆ Ta)
      ∧ ((((E ∪
              (π[0, 3] (σ[#1 = #2] (Tb × Ta)))) ∪
            (π[0, 3] (σ[#1 = #2] (Ta × Tb)))) ⊆ Tb)
        ∧ ((Ta ⊆ Ra) ∧ (Tb ⊆ Rb))))
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example0125
end Benchmark
end Whiel
