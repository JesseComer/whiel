-- Author: Leo Zhang
import Benchmark.Example5037.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

namespace Whiel.Benchmark.Example5037.Fidelity
open Whiel Whiel.Concrete Whiel.Synthesis.Tests.BenchmarkFidelity
open Whiel.Benchmark.Example5037 (inputSchema inputCmd)
/- The Datalog program(s) of the header: compiled sides are their naive compilation; reference programs
   are compared with the hand-written sides on the check instances. -/
def HeapPtr : ProgramNames := .programSymbol ⟨"HeapPtr", by decide⟩ 0
def Tc : ProgramNames := .programSymbol ⟨"Tc", by decide⟩ 0
def schema_Tc : UnnamedSchema ProgramNames := programSch![ {HeapPtr, Tc} (arity: 2) ]
def prog_Tc : Datalog.Program Data schema_Tc := datalog![
  Tc(x1, y1) :- HeapPtr(x1, y1);
  Tc(x1, z1) :- Tc(x1, y1), Tc(y1, z1);
]
def compiledRaw_Tc : RawCmd ProgramNames Data := mapCmd toRawInput prog_Tc.toWhielCmd.toRaw
def RootPtr : ProgramNames := .programSymbol ⟨"RootPtr", by decide⟩ 0
def MarkedR : ProgramNames := .programSymbol ⟨"MarkedR", by decide⟩ 0
def schema_MarkedR : UnnamedSchema ProgramNames := programSch![ {RootPtr, MarkedR} (arity: 1), {HeapPtr} (arity: 2) ]
def prog_MarkedR : Datalog.Program Data schema_MarkedR := datalog![
  MarkedR(x1) :- RootPtr(x1);
  MarkedR(y1) :- MarkedR(x1), HeapPtr(x1, y1);
]
def compiledRaw_MarkedR : RawCmd ProgramNames Data := mapCmd toRawInput prog_MarkedR.toWhielCmd.toRaw
def goCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      Marked := RootPtr;
      Grey := RootPtr;
      WHILE (Grey ≠ ∅) DO
        NewG := ((π[1] (σ[#0 = #2] (HeapPtr × Grey))) ∖ Marked);
        Marked := (Marked ∪ NewG);
        Grey := NewG
      END
    }
  ]
def goRaw : RawCmd ProgramNames Data := goCmd.toRaw
/- The compiled sides are the compiler's output, the hand-written sides are the segments above, and
   their sequence is the input command. -/
theorem inputCmd_eq : seqAfter goRaw compiledRaw_Tc = inputCmd.toRaw := by
  decide +kernel
end Whiel.Benchmark.Example5037.Fidelity
