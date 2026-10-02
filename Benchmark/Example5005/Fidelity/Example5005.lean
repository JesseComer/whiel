-- Author: Leo Zhang
import Benchmark.Example5005.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

namespace Whiel.Benchmark.Example5005.Fidelity
open Whiel Whiel.Concrete Whiel.Synthesis.Tests.BenchmarkFidelity
open Whiel.Benchmark.Example5005 (inputSchema inputCmd)
def Roots : ProgramNames := .programSymbol ⟨"Roots", by decide⟩ 0
def ReachOld : ProgramNames := .programSymbol ⟨"ReachOld", by decide⟩ 0
def EBase : ProgramNames := .programSymbol ⟨"EBase", by decide⟩ 0
def ReachNew : ProgramNames := .programSymbol ⟨"ReachNew", by decide⟩ 0
def EDelta : ProgramNames := .programSymbol ⟨"EDelta", by decide⟩ 0
def schema_pa : UnnamedSchema ProgramNames := programSch![ {Roots, ReachOld} (arity: 1), {EBase} (arity: 2) ]
def prog_pa : Datalog.Program Data schema_pa := datalog![
  ReachOld(x1) :- Roots(x1);
  ReachOld(y1) :- ReachOld(x1), EBase(x1, y1);
]
def compiledRaw_pa : RawCmd ProgramNames Data := mapCmd toRawInput prog_pa.toWhielCmd.toRaw
def schema_pc : UnnamedSchema ProgramNames := programSch![ {Roots, ReachNew} (arity: 1), {EBase, EDelta} (arity: 2) ]
def prog_pc : Datalog.Program Data schema_pc := datalog![
  ReachNew(x1) :- Roots(x1);
  ReachNew(y1) :- ReachNew(x1), EBase(x1, y1);
  ReachNew(y1) :- ReachNew(x1), EDelta(x1, y1);
]
def compiledRaw_pc : RawCmd ProgramNames Data := mapCmd toRawInput prog_pc.toWhielCmd.toRaw
def handCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      Reach_2 := ∅[1];
      Reach := (ReachOld ∪ Roots);
      WHILE (Reach ≠ Reach_2) DO
        Reach_2 := Reach;
        Reach := ((Roots ∪ ReachOld) ∪ (π[1] (σ[#0 = #2] ((EBase ∪ EDelta) × Reach_2))))
      END
    }
  ]
def handRaw : RawCmd ProgramNames Data := handCmd.toRaw
/- The compiled sides are the compiler's output and the sequence is the input command. -/
theorem inputCmd_eq : seqAfter compiledRaw_pa (seqAfter handRaw compiledRaw_pc) = inputCmd.toRaw := by
  decide +kernel
end Whiel.Benchmark.Example5005.Fidelity
