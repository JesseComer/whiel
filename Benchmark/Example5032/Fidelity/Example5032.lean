-- Author: Leo Zhang
import Benchmark.Example5032.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

namespace Whiel.Benchmark.Example5032.Fidelity
open Whiel Whiel.Concrete Whiel.Synthesis.Tests.BenchmarkFidelity
open Whiel.Benchmark.Example5032 (inputSchema inputCmd)
/- The Datalog program(s) of the header: compiled sides are their naive compilation; reference programs
   are compared with the hand-written sides on the check instances. -/
def EBase : ProgramNames := .programSymbol ⟨"EBase", by decide⟩ 0
def TOld : ProgramNames := .programSymbol ⟨"TOld", by decide⟩ 0
def schema_TOld : UnnamedSchema ProgramNames := programSch![ {EBase, TOld} (arity: 2) ]
def prog_TOld : Datalog.Program Data schema_TOld := datalog![
  TOld(x1, y1) :- EBase(x1, y1);
  TOld(x1, y1) :- TOld(x1, z1), EBase(z1, y1);
]
def compiledRaw_TOld : RawCmd ProgramNames Data := mapCmd toRawInput prog_TOld.toWhielCmd.toRaw
def EDelta : ProgramNames := .programSymbol ⟨"EDelta", by decide⟩ 0
def TNew : ProgramNames := .programSymbol ⟨"TNew", by decide⟩ 0
def schema_TNew : UnnamedSchema ProgramNames := programSch![ {EBase, EDelta, TNew} (arity: 2) ]
def prog_TNew : Datalog.Program Data schema_TNew := datalog![
  TNew(x1, y1) :- EBase(x1, y1);
  TNew(x1, y1) :- EDelta(x1, y1);
  TNew(x1, y1) :- TNew(x1, z1), EBase(z1, y1);
  TNew(x1, y1) :- TNew(x1, z1), EDelta(z1, y1);
]
def compiledRaw_TNew : RawCmd ProgramNames Data := mapCmd toRawInput prog_TNew.toWhielCmd.toRaw
def maintCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      Delta := ((EDelta ∪ (π[0, 3] (σ[#1 = #2] (TOld × EDelta)))) ∖ TOld);
      T := (TOld ∪ Delta);
      WHILE (Delta ≠ ∅) DO
        Delta := ((π[0, 3] (σ[#1 = #2] (Delta × (EBase ∪ EDelta)))) ∖ T);
        T := (T ∪ Delta)
      END
    }
  ]
def maintRaw : RawCmd ProgramNames Data := maintCmd.toRaw
def pgCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      Res := (EBase ∪ EDelta);
      WorkT := (EBase ∪ EDelta);
      WHILE (WorkT ≠ ∅) DO
        Inter := ((π[0, 3] (σ[#1 = #2] (WorkT × (EBase ∪ EDelta)))) ∖ Res);
        Res := (Res ∪ Inter);
        WorkT := Inter
      END
    }
  ]
def pgRaw : RawCmd ProgramNames Data := pgCmd.toRaw
/- The compiled sides are the compiler's output, the hand-written sides are the segments above, and
   their sequence is the input command. -/
theorem inputCmd_eq : seqAfter compiledRaw_TOld (seqAfter maintRaw pgRaw) = inputCmd.toRaw := by
  decide +kernel
end Whiel.Benchmark.Example5032.Fidelity
