-- Author: Leo Zhang
import Benchmark.Example5003.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

namespace Whiel.Benchmark.Example5003.Fidelity
open Whiel Whiel.Concrete Whiel.Synthesis.Tests.BenchmarkFidelity
open Whiel.Benchmark.Example5003 (inputSchema inputCmd)
def Src : ProgramNames := .programSymbol ⟨"Src", by decide⟩ 0
def Reach : ProgramNames := .programSymbol ⟨"Reach", by decide⟩ 0
def E : ProgramNames := .programSymbol ⟨"E", by decide⟩ 0
def schema_p : UnnamedSchema ProgramNames := programSch![ {Src, Reach} (arity: 1), {E} (arity: 2) ]
def prog_p : Datalog.Program Data schema_p := datalog![
  Reach(x1) :- Src(x1);
  Reach(y1) :- Reach(x1), E(x1, y1);
]
def compiledRaw_p : RawCmd ProgramNames Data := mapCmd toRawInput prog_p.toWhielCmd.toRaw
def handCmd : Cmd Data inputSchema :=
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
      END
    }
  ]
def handRaw : RawCmd ProgramNames Data := handCmd.toRaw
/- The compiled sides are the compiler's output and the sequence is the input command. -/
theorem inputCmd_eq : seqAfter handRaw compiledRaw_p = inputCmd.toRaw := by
  decide +kernel
end Whiel.Benchmark.Example5003.Fidelity
