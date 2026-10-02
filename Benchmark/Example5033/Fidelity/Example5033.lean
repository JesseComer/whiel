-- Author: Leo Zhang
import Benchmark.Example5033.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

namespace Whiel.Benchmark.Example5033.Fidelity
open Whiel Whiel.Concrete Whiel.Synthesis.Tests.BenchmarkFidelity
open Whiel.Benchmark.Example5033 (inputSchema inputCmd)
/- The Datalog program(s) of the header: compiled sides are their naive compilation; reference programs
   are compared with the hand-written sides on the check instances. -/
def Root : ProgramNames := .programSymbol ⟨"Root", by decide⟩ 0
def MPath : ProgramNames := .programSymbol ⟨"MPath", by decide⟩ 0
def Edge : ProgramNames := .programSymbol ⟨"Edge", by decide⟩ 0
def PathBF : ProgramNames := .programSymbol ⟨"PathBF", by decide⟩ 0
def schema_magic : UnnamedSchema ProgramNames := programSch![ {Root, MPath} (arity: 1), {Edge, PathBF} (arity: 2) ]
def prog_magic : Datalog.Program Data schema_magic := datalog![
  MPath(x1) :- Root(x1);
  MPath(y1) :- MPath(x1), Edge(x1, y1);
  PathBF(x1, y1) :- MPath(x1), Edge(x1, y1);
  PathBF(x1, z1) :- MPath(x1), Edge(x1, y1), PathBF(y1, z1);
]
def compiledRaw_magic : RawCmd ProgramNames Data := mapCmd toRawInput prog_magic.toWhielCmd.toRaw
def PathR : ProgramNames := .programSymbol ⟨"PathR", by decide⟩ 0
def schema_PathR : UnnamedSchema ProgramNames := programSch![ {Edge, PathR} (arity: 2) ]
def prog_PathR : Datalog.Program Data schema_PathR := datalog![
  PathR(x1, y1) :- Edge(x1, y1);
  PathR(x1, z1) :- Edge(x1, y1), PathR(y1, z1);
]
def compiledRaw_PathR : RawCmd ProgramNames Data := mapCmd toRawInput prog_PathR.toWhielCmd.toRaw
def pgCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      Res := Edge;
      WorkT := Edge;
      WHILE (WorkT ≠ ∅) DO
        Inter := ((π[0, 3] (σ[#1 = #2] (Edge × WorkT))) ∖ Res);
        Res := (Res ∪ Inter);
        WorkT := Inter
      END
    }
  ]
def pgRaw : RawCmd ProgramNames Data := pgCmd.toRaw
/- The compiled sides are the compiler's output, the hand-written sides are the segments above, and
   their sequence is the input command. -/
theorem inputCmd_eq : seqAfter compiledRaw_magic pgRaw = inputCmd.toRaw := by
  decide +kernel
end Whiel.Benchmark.Example5033.Fidelity
