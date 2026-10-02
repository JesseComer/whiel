-- Author: Leo Zhang
import Benchmark.Example5031.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

namespace Whiel.Benchmark.Example5031.Fidelity
open Whiel Whiel.Concrete Whiel.Synthesis.Tests.BenchmarkFidelity
open Whiel.Benchmark.Example5031 (inputSchema inputCmd)
/- The Datalog program(s) of the header: compiled sides are their naive compilation; reference programs
   are compared with the hand-written sides on the check instances. -/
def Edge : ProgramNames := .programSymbol ⟨"Edge", by decide⟩ 0
def T : ProgramNames := .programSymbol ⟨"T", by decide⟩ 0
def schema_T : UnnamedSchema ProgramNames := programSch![ {Edge, T} (arity: 2) ]
def prog_T : Datalog.Program Data schema_T := datalog![
  T(x1, y1) :- Edge(x1, y1);
  T(x1, y1) :- T(x1, z1), Edge(z1, y1);
]
def compiledRaw_T : RawCmd ProgramNames Data := mapCmd toRawInput prog_T.toWhielCmd.toRaw
def nxCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      TcB := ∅[2];
      Rest := (π[0] Edge ∪ π[1] Edge);
      WHILE (Rest ≠ ∅) DO
        Cur := (Rest ∖ (π[1] (σ[#0 = #2] (Lt × Rest))));
        SeenA := (π[0, 0] Cur);
        LvlA := ((π[0, 3] (σ[#1 = #2] (SeenA × Edge))) ∖ SeenA);
        SeenB := (SeenA ∪ LvlA);
        LvlB := ((π[0, 3] (σ[#1 = #2] (LvlA × Edge))) ∖ SeenB);
        TcB := ((TcB ∪ LvlA) ∪ LvlB);
        Rest := (Rest ∖ Cur)
      END
    }
  ]
def nxRaw : RawCmd ProgramNames Data := nxCmd.toRaw
def pgCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      Res := Edge;
      WorkT := Edge;
      WHILE (WorkT ≠ ∅) DO
        Inter := ((π[0, 3] (σ[#1 = #2] (WorkT × Edge))) ∖ Res);
        Res := (Res ∪ Inter);
        WorkT := Inter
      END
    }
  ]
def pgRaw : RawCmd ProgramNames Data := pgCmd.toRaw
/- The compiled sides are the compiler's output, the hand-written sides are the segments above, and
   their sequence is the input command. -/
theorem inputCmd_eq : seqAfter nxRaw pgRaw = inputCmd.toRaw := by
  decide +kernel
end Whiel.Benchmark.Example5031.Fidelity
