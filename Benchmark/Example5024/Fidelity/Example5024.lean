-- Author: Leo Zhang
import Benchmark.Example5024.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

namespace Whiel.Benchmark.Example5024.Fidelity
open Whiel Whiel.Concrete Whiel.Synthesis.Tests.BenchmarkFidelity
open Whiel.Benchmark.Example5024 (inputSchema inputCmd)
def Move : ProgramNames := .programSymbol ⟨"Move", by decide⟩ 0
def NotUnder : ProgramNames := .programSymbol ⟨"NotUnder", by decide⟩ 0
def NotOver : ProgramNames := .programSymbol ⟨"NotOver", by decide⟩ 0
def OverI : ProgramNames := .programSymbol ⟨"OverI", by decide⟩ 0
def UnderI : ProgramNames := .programSymbol ⟨"UnderI", by decide⟩ 0
def Under : ProgramNames := .programSymbol ⟨"Under", by decide⟩ 0
def Prev : ProgramNames := .programSymbol ⟨"Prev", by decide⟩ 0
/- The positive programs P^I of the two half-steps of the alternation (`not win(Y)` read as `NotUnder(Y)`,
   resp. `NotOver(Y)`); their naive compilation is the inner loop of each half-step. -/
def schema_pO : UnnamedSchema ProgramNames := programSch![ {Move} (arity: 2), {NotUnder, OverI} (arity: 1) ]
def prog_pO : Datalog.Program Data schema_pO := datalog![
  OverI(x1) :- Move(x1, y1), NotUnder(y1);
]
def compiledRaw_pO : RawCmd ProgramNames Data := mapCmd toRawInput prog_pO.toWhielCmd.toRaw
def schema_pU : UnnamedSchema ProgramNames := programSch![ {Move} (arity: 2), {NotOver, UnderI} (arity: 1) ]
def prog_pU : Datalog.Program Data schema_pU := datalog![
  UnderI(x1) :- Move(x1, y1), NotOver(y1);
]
def compiledRaw_pU : RawCmd ProgramNames Data := mapCmd toRawInput prog_pU.toWhielCmd.toRaw
/- The inner loops as they appear in the input, standalone. -/
def innerO : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      OverI_aux := ∅[1];
      OverI := π[0] (σ[#1 = #2] ((Move × NotUnder)));
      WHILE (¬((OverI = OverI_aux))) DO
        OverI_aux := OverI;
        OverI := (OverI ∪ π[0] (σ[#1 = #2] ((Move × NotUnder))))
      END
    }
  ]
def innerU : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      UnderI_aux := ∅[1];
      UnderI := π[0] (σ[#1 = #2] ((Move × NotOver)));
      WHILE (¬((UnderI = UnderI_aux))) DO
        UnderI_aux := UnderI;
        UnderI := (UnderI ∪ π[0] (σ[#1 = #2] ((Move × NotOver))))
      END
    }
  ]
/- Each inner loop is the compiler's output for its positive program. -/
theorem innerO_eq : innerO.toRaw = compiledRaw_pO := by decide +kernel
theorem innerU_eq : innerU.toRaw = compiledRaw_pU := by decide +kernel
/- The rest of the hand-written command, in pieces at statement boundaries. -/
def prefixCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      Nodes := (π[0] Move ∪ π[1] Move);
      Under := ∅[1];
      Over := ∅[1];
      Prev := Nodes
    }
  ]
def stepA : Cmd Data inputSchema :=
  programCmd![ { ExecSchema: inputSchema } { Prev := Under; NotUnder := (Nodes ∖ Under) } ]
def stepB : Cmd Data inputSchema :=
  programCmd![ { ExecSchema: inputSchema } { Over := OverI; NotOver := (Nodes ∖ Over) } ]
def stepC : Cmd Data inputSchema :=
  programCmd![ { ExecSchema: inputSchema } { Under := UnderI } ]
def attractorCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      WinP := ∅[1];
      LoseP := ∅[1];
      Win := π[0] (σ[#1 = #2] (Move × LoseP));
      Lose := (Nodes ∖ π[0] (Move ∖ π[0, 1] (σ[#1 = #2] (Move × WinP))));
      WHILE (¬((Win = WinP) ∧ (Lose = LoseP))) DO
        WinP := Win;
        LoseP := Lose;
        Win := π[0] (σ[#1 = #2] (Move × LoseP));
        Lose := (Nodes ∖ π[0] (Move ∖ π[0, 1] (σ[#1 = #2] (Move × WinP))))
      END
    }
  ]
/- The outer alternation loop: guard `¬(Under = Prev)`, body = stepA; compiled P^Under; stepB; compiled P^Over; stepC. -/
def outerGuard : RawGuard ProgramNames Data := .not (.eq (.rel Under) (.rel Prev))
def outerBody : RawCmd ProgramNames Data :=
  seqAfter stepA.toRaw (seqAfter compiledRaw_pO (seqAfter stepB.toRaw (seqAfter compiledRaw_pU stepC.toRaw)))
def assembled : RawCmd ProgramNames Data :=
  seqAfter prefixCmd.toRaw (seqAfter (.«while» outerGuard outerBody) attractorCmd.toRaw)
/- The input command is the assembly, with the compiler's output as the inner loops. -/
theorem inputCmd_eq : assembled = inputCmd.toRaw := by
  decide +kernel
end Whiel.Benchmark.Example5024.Fidelity
