-- Author: Leo Zhang
import Benchmark.Example5001.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

namespace Whiel.Benchmark.Example5001.Fidelity
open Whiel Whiel.Concrete Whiel.Synthesis.Tests.BenchmarkFidelity
open Whiel.Benchmark.Example5001 (inputSchema inputCmd)
def Base : ProgramNames := .programSymbol ⟨"Base", by decide⟩ 0
def Edge : ProgramNames := .programSymbol ⟨"Edge", by decide⟩ 0
def Tcl : ProgramNames := .programSymbol ⟨"Tcl", by decide⟩ 0
def schema_p : UnnamedSchema ProgramNames := programSch![ {Base, Edge, Tcl} (arity: 2) ]
def prog_p : Datalog.Program Data schema_p := datalog![
  Tcl(x1, y1) :- Base(x1, y1);
  Tcl(x1, y1) :- Tcl(x1, z1), Edge(z1, y1);
]
def compiledRaw_p : RawCmd ProgramNames Data := mapCmd toRawInput prog_p.toWhielCmd.toRaw
def handCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      Res := Base;
      WorkT := Base;
      WHILE (WorkT ≠ ∅) DO
        Inter := ((π[0, 3] (σ[#1 = #2] (WorkT × Edge))) ∖ Res);
        Res := (Res ∪ Inter);
        WorkT := Inter
      END
    }
  ]
def handRaw : RawCmd ProgramNames Data := handCmd.toRaw
/- The compiled sides are the compiler's output and the sequence is the input command. -/
theorem inputCmd_eq : seqAfter handRaw compiledRaw_p = inputCmd.toRaw := by
  decide +kernel
end Whiel.Benchmark.Example5001.Fidelity
