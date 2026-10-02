-- Author: Leo Zhang
import Benchmark.Example5007.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

namespace Whiel.Benchmark.Example5007.Fidelity
open Whiel Whiel.Concrete Whiel.Synthesis.Tests.BenchmarkFidelity
open Whiel.Benchmark.Example5007 (inputSchema inputCmd)
def E : ProgramNames := .programSymbol ⟨"E", by decide⟩ 0
def T : ProgramNames := .programSymbol ⟨"T", by decide⟩ 0
def schema_p : UnnamedSchema ProgramNames := programSch![ {E, T} (arity: 2) ]
def prog_p : Datalog.Program Data schema_p := datalog![
  T(x1, y1) :- E(x1, y1);
  T(x1, y1) :- E(x1, z1), T(z1, y1);
]
def compiledRaw_p : RawCmd ProgramNames Data := mapCmd toRawInput prog_p.toWhielCmd.toRaw
def handCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      TSq_2 := ∅[2];
      TSq := E;
      WHILE (TSq ≠ TSq_2) DO
        TSq_2 := TSq;
        TSq := (TSq ∪ (π[0, 3] (σ[#1 = #2] (TSq_2 × TSq_2))))
      END
    }
  ]
def handRaw : RawCmd ProgramNames Data := handCmd.toRaw
/- The compiled sides are the compiler's output and the sequence is the input command. -/
theorem inputCmd_eq : seqAfter handRaw compiledRaw_p = inputCmd.toRaw := by
  decide +kernel
end Whiel.Benchmark.Example5007.Fidelity
