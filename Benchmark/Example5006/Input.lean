-- Benchmark contributors: Leo Zhang
import Whiel.Concrete.Notation
import Whiel.Hoare.PreprocDisplay
import Whiel.Hoare.ProphecySchema

/-
  Two semi-naive evaluations of transitive closure that
  differ in where the delta is joined: appended (`Delta ∘ E`,
  legacy Example1042) or prepended (`E ∘ Delta`, legacy
  Example1058).

  Input `E` (binary).  Both sides accumulate `Acc`, the
  closure of `E`, from a frontier `Delta` that is extended by
  one edge per round on the right or on the left.

  Independent programs, merged side by side.  Precondition
  `true`; postcondition `AccA = AccP`.

  Expected verdict: valid.  Both frontiers hold the walks of
  length n+1 after round n, on opposite ends.
-/

namespace Whiel
namespace Benchmark
namespace Example5006

open Concrete

def inputSchema : UnnamedSchema ProgramNames :=
  programSch![
    {E, AccA, DeltaA, AccP, DeltaP} (arity: 2)
  ]

def inputPre : AssertExpr Data inputSchema :=
  programAssert![ true ]

def inputCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      AccA := E;
      DeltaA := E;
      WHILE (DeltaA ≠ ∅) DO
        DeltaA := ((π[0, 3] (σ[#1 = #2] (DeltaA × E))) ∖ AccA);
        AccA := (AccA ∪ DeltaA)
      END;
      AccP := E;
      DeltaP := E;
      WHILE (DeltaP ≠ ∅) DO
        DeltaP := ((π[0, 3] (σ[#1 = #2] (E × DeltaP))) ∖ AccP);
        AccP := (AccP ∪ DeltaP)
      END
    }
  ]

def inputPost : AssertExpr Data inputSchema :=
  programAssert![
    (AccA = AccP)
  ]

def inputPreproc : Hoare.Preproc inputPre inputCmd inputPost :=
  Hoare.preprocess inputPre inputCmd inputPost

/- The stated triple and the loop preprocessing built. -/
set_option linter.hashCommand false in
#eval inputPreproc.display

end Example5006
end Benchmark
end Whiel
