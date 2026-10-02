-- Author: Leo Zhang
import Benchmark.Example5022.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

namespace Whiel.Benchmark.Example5022.Fidelity
open Whiel Whiel.Concrete Whiel.Synthesis.Tests.BenchmarkFidelity
open Whiel.Benchmark.Example5022 (inputSchema inputCmd)
def Base : ProgramNames := .programSymbol ⟨"Base", by decide⟩ 0
def E : ProgramNames := .programSymbol ⟨"E", by decide⟩ 0
def Cl : ProgramNames := .programSymbol ⟨"Cl", by decide⟩ 0
/- The recursive CTE as Datalog. -/
def schema_p : UnnamedSchema ProgramNames := programSch![ {Base, E, Cl} (arity: 2) ]
def prog_p : Datalog.Program Data schema_p := datalog![
  Cl(x1, y1) :- Base(x1, y1);
  Cl(x1, z1) :- Cl(x1, y1), E(y1, z1);
]
def compiledRaw_p : RawCmd ProgramNames Data := mapCmd toRawInput prog_p.toWhielCmd.toRaw
/- The engine's four semi-naive iterations (UNION DISTINCT: each level joins the previous level's rows and drops rows already in the result). -/
def handCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      ResA := Base;
      NewB := (π[0, 3] (σ[#1 = #2] (ResA × E)) ∖ ResA);
      ResB := (ResA ∪ NewB);
      NewC := (π[0, 3] (σ[#1 = #2] (NewB × E)) ∖ ResB);
      ResC := (ResB ∪ NewC);
      NewD := (π[0, 3] (σ[#1 = #2] (NewC × E)) ∖ ResC);
      ResD := (ResC ∪ NewD);
      NewE := (π[0, 3] (σ[#1 = #2] (NewD × E)) ∖ ResD);
      ResE := (ResD ∪ NewE)
    }
  ]
def handRaw : RawCmd ProgramNames Data := handCmd.toRaw
/- The compiled side is the compiler's output and the sequence is the input command. -/
theorem inputCmd_eq : seqAfter handRaw compiledRaw_p = inputCmd.toRaw := by
  decide +kernel
end Whiel.Benchmark.Example5022.Fidelity
