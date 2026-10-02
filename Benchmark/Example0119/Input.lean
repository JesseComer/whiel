-- Benchmark contributors: Fangzhu Shen, Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  All paths, computed through mutually recursive odd and
  even halves, specified as the least fixpoint of the
  non-linear closure program.

  Schema `{E, R, Ta, Sa, Tb, Sb, Tc, Sc}` (all binary): `E`
  is the edge relation, `Ta`, `Tb`, `Tc` the computed
  relations, `Sa`, `Sb`, `Sc` their next-round values, and
  `R` a relation the program never reads or writes. The
  program is
    `Tb(x, y) :- E(x, y)`
    `Tb(x, y) :- E(x, z), Ta(z, y)`
    `Ta(x, y) :- E(x, z), Tb(z, y)`
    `Tc(x, y) :- Ta(x, y)`
    `Tc(x, y) :- Tb(x, y)`
  run naively, so `Tb` collects the paths of odd length,
  `Ta` those of even length at least two, and `Tc` their
  union.

  The reference program is the non-linear closure
    `T(x, y) :- E(x, y)`
    `T(x, y) :- T(x, z), T(z, y)`

  The precondition says `R` is a pre-fixpoint of that
  non-linear program, `E ∪ (R ∘ R) ⊆ R`. The postcondition
  is the least-fixpoint introduction obligation for it: the
  computed `Tc` is itself a pre-fixpoint,
  `E ∪ (Tc ∘ Tc) ⊆ Tc`, and lies below the given one,
  `Tc ⊆ R`.

  Expected verdict: valid. Every path has odd or even
  length, so `Tc` is the transitive closure of `E`.
-/

namespace Whiel
namespace Benchmark
namespace Example0119

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {E, R, Ta, Sa, Tb, Sb, Tc, Sc} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![
    ((E ∪ (π[0, 3] (σ[#1 = #2] (R × R)))) ⊆ R)
  ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      Ta := ∅;
      Tb := ∅;
      Tc := ∅;
      Sa := (π[0, 3] (σ[#1 = #2] (E × Tb)));
      Sb := (E ∪ (π[0, 3] (σ[#1 = #2] (E × Ta))));
      Sc := (Ta ∪ Tb);
      WHILE
          ¬(((Sa = Ta) ∧
            ((Sb = Tb) ∧ (Sc = Tc)))) DO
        Ta := Sa;
        Tb := Sb;
        Tc := Sc;
        Sa := (π[0, 3] (σ[#1 = #2] (E × Tb)));
        Sb :=
          (E ∪ (π[0, 3] (σ[#1 = #2] (E × Ta))));
        Sc := (Ta ∪ Tb)
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    (((E ∪ (π[0, 3] (σ[#1 = #2] (Tc × Tc)))) ⊆ Tc)
      ∧ (Tc ⊆ R))
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example0119
end Benchmark
end Whiel
