-- Author: Leo Zhang
import Benchmark.Example3009.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

namespace Whiel.Benchmark.Example3009.Fidelity
open Whiel Whiel.Concrete Whiel.Synthesis.Tests.BenchmarkFidelity
open Whiel.Benchmark.Example3009 (inputSchema inputCmd)
/- The Datalog program(s) of the header: compiled sides are their naive compilation; reference programs
   are compared with the hand-written sides on the check instances. -/
def Root : ProgramNames := .programSymbol ⟨"Root", by decide⟩ 0
def Delegate : ProgramNames := .programSymbol ⟨"Delegate", by decide⟩ 0
def Certified : ProgramNames := .programSymbol ⟨"Certified", by decide⟩ 0
def Audit : ProgramNames := .programSymbol ⟨"Audit", by decide⟩ 0
def Trust : ProgramNames := .programSymbol ⟨"Trust", by decide⟩ 0
def Review : ProgramNames := .programSymbol ⟨"Review", by decide⟩ 0
def GrantA : ProgramNames := .programSymbol ⟨"GrantA", by decide⟩ 0
def PendingA : ProgramNames := .programSymbol ⟨"PendingA", by decide⟩ 0
def CheckedA : ProgramNames := .programSymbol ⟨"CheckedA", by decide⟩ 0
def schema_c1 : UnnamedSchema ProgramNames := programSch![ {Root} (arity: 1), {Delegate} (arity: 2), {Certified} (arity: 2), {Audit} (arity: 3), {Trust} (arity: 1), {Review} (arity: 2), {GrantA} (arity: 1), {PendingA} (arity: 1), {CheckedA} (arity: 1) ]
def prog_c1 : Datalog.Program Data schema_c1 := datalog![
  GrantA(x1) :- Root(x1);
  PendingA(y1) :- GrantA(x1), Delegate(x1, y1);
  CheckedA(y1) :- PendingA(y1), Certified(x1, y1), Trust(x1);
  GrantA(y1) :- CheckedA(y1);
  PendingA(y1) :- CheckedA(x1), GrantA(z1), Review(x1, y1);
]
def compiledRaw_c1 : RawCmd ProgramNames Data := mapCmd toRawInput prog_c1.toWhielCmd.toRaw
def AllowB : ProgramNames := .programSymbol ⟨"AllowB", by decide⟩ 0
def QueueB : ProgramNames := .programSymbol ⟨"QueueB", by decide⟩ 0
def VettedB : ProgramNames := .programSymbol ⟨"VettedB", by decide⟩ 0
def schema_c2 : UnnamedSchema ProgramNames := programSch![ {Root} (arity: 1), {Delegate} (arity: 2), {Certified} (arity: 2), {Audit} (arity: 3), {Trust} (arity: 1), {Review} (arity: 2), {AllowB} (arity: 1), {QueueB} (arity: 1), {VettedB} (arity: 1) ]
def prog_c2 : Datalog.Program Data schema_c2 := datalog![
  AllowB(x1) :- Root(x1);
  QueueB(y1) :- AllowB(x1), Delegate(x1, y1);
  VettedB(y1) :- QueueB(y1), Certified(x1, y1), Trust(x1);
  AllowB(y1) :- VettedB(y1), Audit(x1, y1, z1), AllowB(z1);
  QueueB(y1) :- VettedB(x1), Review(x1, y1);
]
def compiledRaw_c2 : RawCmd ProgramNames Data := mapCmd toRawInput prog_c2.toWhielCmd.toRaw
/- The compiled sides are the compiler's output, the hand-written sides are the segments above, and
   their sequence is the input command. -/
theorem inputCmd_eq : seqAfter compiledRaw_c1 compiledRaw_c2 = inputCmd.toRaw := by
  decide +kernel
end Whiel.Benchmark.Example3009.Fidelity
