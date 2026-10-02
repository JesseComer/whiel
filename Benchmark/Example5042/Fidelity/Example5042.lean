-- Author: Leo Zhang
import Benchmark.Example5042.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

namespace Whiel.Benchmark.Example5042.Fidelity
open Whiel Whiel.Concrete Whiel.Synthesis.Tests.BenchmarkFidelity
open Whiel.Benchmark.Example5042 (inputSchema inputCmd)
/- The Datalog program(s) of the header: compiled sides are their naive compilation; reference programs
   are compared with the hand-written sides on the check instances. -/
def SeedDel : ProgramNames := .programSymbol ⟨"SeedDel", by decide⟩ 0
def DelC : ProgramNames := .programSymbol ⟨"DelC", by decide⟩ 0
def RefBy : ProgramNames := .programSymbol ⟨"RefBy", by decide⟩ 0
def schema_DelC : UnnamedSchema ProgramNames := programSch![ {SeedDel, DelC} (arity: 1), {RefBy} (arity: 2) ]
def prog_DelC : Datalog.Program Data schema_DelC := datalog![
  DelC(x1) :- SeedDel(x1);
  DelC(x1) :- RefBy(x1, y1), DelC(y1);
]
def compiledRaw_DelC : RawCmd ProgramNames Data := mapCmd toRawInput prog_DelC.toWhielCmd.toRaw
def DelR : ProgramNames := .programSymbol ⟨"DelR", by decide⟩ 0
def schema_DelR : UnnamedSchema ProgramNames := programSch![ {SeedDel, DelR} (arity: 1), {RefBy} (arity: 2) ]
def prog_DelR : Datalog.Program Data schema_DelR := datalog![
  DelR(x1) :- SeedDel(x1);
  DelR(x1) :- RefBy(x1, y1), DelR(y1);
]
def compiledRaw_DelR : RawCmd ProgramNames Data := mapCmd toRawInput prog_DelR.toWhielCmd.toRaw
def cascadeCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      Del := SeedDel;
      Front := SeedDel;
      WHILE (Front ≠ ∅) DO
        New := ((π[0] (σ[#1 = #2] (RefBy × Front))) ∖ Del);
        Del := (Del ∪ New);
        Front := New
      END;
      Viol := (π[0] (σ[#1 = #2] (RestrictRef × Del)))
    }
  ]
def cascadeRaw : RawCmd ProgramNames Data := cascadeCmd.toRaw
def checkCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      ViolC := ((π[0] (σ[#1 = #2] (RestrictRef × DelC))) ∖ DelC)
    }
  ]
def checkRaw : RawCmd ProgramNames Data := checkCmd.toRaw
/- The compiled sides are the compiler's output, the hand-written sides are the segments above, and
   their sequence is the input command. -/
theorem inputCmd_eq : seqAfter cascadeRaw (seqAfter compiledRaw_DelC checkRaw) = inputCmd.toRaw := by
  decide +kernel
end Whiel.Benchmark.Example5042.Fidelity
