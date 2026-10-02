-- Author: Leo Zhang
import Benchmark.Example5015.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

namespace Whiel.Benchmark.Example5015.Fidelity
open Whiel Whiel.Concrete Whiel.Synthesis.Tests.BenchmarkFidelity
open Whiel.Benchmark.Example5015 (inputSchema inputCmd)
def G : ProgramNames := .programSymbol ⟨"G", by decide⟩ 0
def P : ProgramNames := .programSymbol ⟨"P", by decide⟩ 0
def Tc : ProgramNames := .programSymbol ⟨"Tc", by decide⟩ 0
def Star : ProgramNames := .programSymbol ⟨"Star", by decide⟩ 0
def schema_p : UnnamedSchema ProgramNames := programSch![ {G, P, Tc, Star} (arity: 2) ]
/- The closure `p+` and "closure plus identity" over the endpoints of `p` (the misreading of `p*`). -/
def prog_p : Datalog.Program Data schema_p := datalog![
  Tc(x1, y1) :- P(x1, y1);
  Tc(x1, z1) :- Tc(x1, y1), P(y1, z1);
  Star(x1, x1) :- P(x1, y1);
  Star(y1, y1) :- P(x1, y1);
  Star(x1, y1) :- Tc(x1, y1);
]
def compiledRaw_p : RawCmd ProgramNames Data := mapCmd toRawInput prog_p.toWhielCmd.toRaw
/- The W3C ALP procedure, set-at-a-time with the visited set indexed by its start. -/
def handCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      Alp := (π[0, 0] G ∪ π[1, 1] G);
      Front := Alp;
      WHILE (Front ≠ ∅) DO
        Next := (π[0, 3] (σ[#1 = #2] (Front × P)) ∖ Alp);
        Alp := (Alp ∪ Next);
        Front := Next
      END
    }
  ]
def handRaw : RawCmd ProgramNames Data := handCmd.toRaw
/- The compiled side is the compiler's output and the sequence is the input command. -/
theorem inputCmd_eq : seqAfter handRaw compiledRaw_p = inputCmd.toRaw := by
  decide +kernel
end Whiel.Benchmark.Example5015.Fidelity
