-- Author: Leo Zhang
import Benchmark.Example5017.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

namespace Whiel.Benchmark.Example5017.Fidelity
open Whiel Whiel.Concrete Whiel.Synthesis.Tests.BenchmarkFidelity
open Whiel.Benchmark.Example5017 (inputSchema inputCmd)
def E : ProgramNames := .programSymbol ⟨"E", by decide⟩ 0
def T : ProgramNames := .programSymbol ⟨"T", by decide⟩ 0
def EN : ProgramNames := .programSymbol ⟨"EN", by decide⟩ 0
def Tn : ProgramNames := .programSymbol ⟨"Tn", by decide⟩ 0
/- The maintained program: the closure of the old edges. -/
def schema_pa : UnnamedSchema ProgramNames := programSch![ {E, T} (arity: 2) ]
def prog_pa : Datalog.Program Data schema_pa := datalog![
  T(x1, y1) :- E(x1, y1);
  T(x1, z1) :- T(x1, y1), E(y1, z1);
]
def compiledRaw_pa : RawCmd ProgramNames Data := mapCmd toRawInput prog_pa.toWhielCmd.toRaw
/- Step 1 of DRed only: DR1, DR2 (overdeletion) and DR3; no rederivation. -/
def handCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      EN := (E ∖ Del);
      Over := ∅[2];
      Cand := (Del ∪ π[0, 3] (σ[#1 = #2] (T × Del)));
      WHILE ((Cand ∖ Over) ≠ ∅) DO
        New := (Cand ∖ Over);
        Over := (Over ∪ New);
        Cand := π[0, 3] (σ[#1 = #2] (New × E))
      END;
      T := (T ∖ Over)
    }
  ]
def handRaw : RawCmd ProgramNames Data := handCmd.toRaw
/- Recomputation: the closure of the updated edges. -/
def schema_pc : UnnamedSchema ProgramNames := programSch![ {EN, Tn} (arity: 2) ]
def prog_pc : Datalog.Program Data schema_pc := datalog![
  Tn(x1, y1) :- EN(x1, y1);
  Tn(x1, z1) :- Tn(x1, y1), EN(y1, z1);
]
def compiledRaw_pc : RawCmd ProgramNames Data := mapCmd toRawInput prog_pc.toWhielCmd.toRaw
/- The compiled sides are the compiler's output and the sequence is the input command. -/
theorem inputCmd_eq : seqAfter compiledRaw_pa (seqAfter handRaw compiledRaw_pc) = inputCmd.toRaw := by
  decide +kernel
end Whiel.Benchmark.Example5017.Fidelity
