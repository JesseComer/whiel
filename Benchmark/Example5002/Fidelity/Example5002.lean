-- Author: Leo Zhang
import Benchmark.Example5002.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

namespace Whiel.Benchmark.Example5002.Fidelity
open Whiel Whiel.Concrete Whiel.Synthesis.Tests.BenchmarkFidelity
open Whiel.Benchmark.Example5002 (inputSchema inputCmd)
def EdgeF : ProgramNames := .programSymbol ⟨"EdgeF", by decide⟩ 0
def Reach : ProgramNames := .programSymbol ⟨"Reach", by decide⟩ 0
def schema_p : UnnamedSchema ProgramNames := programSch![ {EdgeF, Reach} (arity: 2) ]
def prog_p : Datalog.Program Data schema_p := datalog![
  Reach(y1, x1) :- EdgeF(x1, y1);
  Reach(z1, x1) :- Reach(y1, x1), EdgeF(y1, z1);
]
def compiledRaw_p : RawCmd ProgramNames Data := mapCmd toRawInput prog_p.toWhielCmd.toRaw
def handCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      Nodes := (π[1, 0] EdgeF);
      DeltaN := (π[1, 0] EdgeF);
      WHILE (DeltaN ≠ ∅) DO
        NewN := ((π[3, 1] (σ[#0 = #2] (DeltaN × EdgeF))) ∖ Nodes);
        Nodes := (Nodes ∪ NewN);
        DeltaN := NewN
      END
    }
  ]
def handRaw : RawCmd ProgramNames Data := handCmd.toRaw
/- The compiled sides are the compiler's output and the sequence is the input command. -/
theorem inputCmd_eq : seqAfter handRaw compiledRaw_p = inputCmd.toRaw := by
  decide +kernel
end Whiel.Benchmark.Example5002.Fidelity
