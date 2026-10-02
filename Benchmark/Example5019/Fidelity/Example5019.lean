-- Author: Leo Zhang
import Benchmark.Example5019.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

namespace Whiel.Benchmark.Example5019.Fidelity
open Whiel Whiel.Concrete Whiel.Synthesis.Tests.BenchmarkFidelity
open Whiel.Benchmark.Example5019 (inputSchema inputCmd)
def S : ProgramNames := .programSymbol ⟨"S", by decide⟩ 0
def TA : ProgramNames := .programSymbol ⟨"TA", by decide⟩ 0
def TB : ProgramNames := .programSymbol ⟨"TB", by decide⟩ 0
def TC : ProgramNames := .programSymbol ⟨"TC", by decide⟩ 0
def WA : ProgramNames := .programSymbol ⟨"WA", by decide⟩ 0
def WB : ProgramNames := .programSymbol ⟨"WB", by decide⟩ 0
/- The full TGDs of ChaseBench scenarios/correctness/tgds as a Datalog program (S = s, TA = t1, TB = t2, TC = t3, WA = w1, WB = w2). -/
def schema_p : UnnamedSchema ProgramNames := programSch![ {S, TA, TC} (arity: 3), {TB, WA, WB} (arity: 2) ]
def prog_p : Datalog.Program Data schema_p := datalog![
  TA(x1, y1, z1) :- S(x1, y1, z1);
  WA(x1, y1) :- S(x1, y1, z1);
  TB(x1, y1) :- TA(x1, y1, z1);
  TB(y1, y1) :- TC(x1, y1, z1);
  WB(x1, y1) :- WA(x1, y1);
  WA(y1, y1) :- WB(x1, y1);
]
def compiledRaw_p : RawCmd ProgramNames Data := mapCmd toRawInput prog_p.toWhielCmd.toRaw
/- One pass: s-t dependencies once, then each target dependency to its fixpoint once, in file order, no repetition. -/
def handCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      TAQ := S;
      WAQ := π[0, 1] S;
      TBQ := ∅[2];
      WBQ := ∅[2];
      WHILE (¬((π[0, 1] TAQ) ⊆ TBQ)) DO
        TBQ := (TBQ ∪ π[0, 1] TAQ)
      END;
      WHILE (¬((π[1, 1] TC) ⊆ TBQ)) DO
        TBQ := (TBQ ∪ π[1, 1] TC)
      END;
      WHILE (¬(WAQ ⊆ WBQ)) DO
        WBQ := (WBQ ∪ WAQ)
      END;
      WHILE (¬((π[1, 1] WBQ) ⊆ WAQ)) DO
        WAQ := (WAQ ∪ π[1, 1] WBQ)
      END
    }
  ]
def handRaw : RawCmd ProgramNames Data := handCmd.toRaw
/- The compiled side is the compiler's output and the sequence is the input command. -/
theorem inputCmd_eq : seqAfter handRaw compiledRaw_p = inputCmd.toRaw := by
  decide +kernel
end Whiel.Benchmark.Example5019.Fidelity
