-- Author: Leo Zhang
import Benchmark.Example5039.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

namespace Whiel.Benchmark.Example5039.Fidelity
open Whiel Whiel.Concrete Whiel.Synthesis.Tests.BenchmarkFidelity
open Whiel.Benchmark.Example5039 (inputSchema inputCmd)
/- The Datalog program(s) of the header: compiled sides are their naive compilation; reference programs
   are compared with the hand-written sides on the check instances. -/
def Reader : ProgramNames := .programSymbol ⟨"Reader", by decide⟩ 0
def ParentRel : ProgramNames := .programSymbol ⟨"ParentRel", by decide⟩ 0
def ViewC : ProgramNames := .programSymbol ⟨"ViewC", by decide⟩ 0
def schema_ViewC : UnnamedSchema ProgramNames := programSch![ {Reader, ParentRel, ViewC} (arity: 2) ]
def prog_ViewC : Datalog.Program Data schema_ViewC := datalog![
  ViewC(x1, y1) :- Reader(x1, y1);
  ViewC(x1, y1) :- ParentRel(y1, z1), ViewC(x1, z1);
]
def compiledRaw_ViewC : RawCmd ProgramNames Data := mapCmd toRawInput prog_ViewC.toWhielCmd.toRaw
def Allowed : ProgramNames := .programSymbol ⟨"Allowed", by decide⟩ 0
def ViewR : ProgramNames := .programSymbol ⟨"ViewR", by decide⟩ 0
def schema_ViewR : UnnamedSchema ProgramNames := programSch![ {Reader, ParentRel, Allowed, ViewR} (arity: 2) ]
def prog_ViewR : Datalog.Program Data schema_ViewR := datalog![
  ViewR(x1, y1) :- Reader(x1, y1), Allowed(x1, y1);
  ViewR(x1, y1) :- ParentRel(y1, z1), ViewR(x1, z1), Allowed(x1, y1);
]
def compiledRaw_ViewR : RawCmd ProgramNames Data := mapCmd toRawInput prog_ViewR.toWhielCmd.toRaw
def perstepCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      View_aux := ∅[2];
      View := (Reader ∖ Banned);
      WHILE (View ≠ View_aux) DO
        View_aux := View;
        View := ((Reader ∪ (π[2, 0] (σ[#1 = #3] (ParentRel × View_aux)))) ∖ Banned)
      END
    }
  ]
def perstepRaw : RawCmd ProgramNames Data := perstepCmd.toRaw
def filterCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      Filtered := (ViewC ∖ Banned)
    }
  ]
def filterRaw : RawCmd ProgramNames Data := filterCmd.toRaw
/- The compiled sides are the compiler's output, the hand-written sides are the segments above, and
   their sequence is the input command. -/
theorem inputCmd_eq : seqAfter perstepRaw (seqAfter compiledRaw_ViewC filterRaw) = inputCmd.toRaw := by
  decide +kernel
end Whiel.Benchmark.Example5039.Fidelity
