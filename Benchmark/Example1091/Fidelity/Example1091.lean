-- Author: Leo Zhang
import Benchmark.Example1091.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

namespace Whiel.Benchmark.Example1091.Fidelity
open Whiel Whiel.Concrete Whiel.Synthesis.Tests.BenchmarkFidelity
open Whiel.Benchmark.Example1091 (inputSchema inputCmd)
/- The Datalog program(s) of the header: compiled sides are their naive compilation; reference programs
   are compared with the hand-written sides on the check instances. -/
def C : ProgramNames := .programSymbol ⟨"C", by decide⟩ 0
def Mid : ProgramNames := .programSymbol ⟨"Mid", by decide⟩ 0
def Link : ProgramNames := .programSymbol ⟨"Link", by decide⟩ 0
def BaseTwo : ProgramNames := .programSymbol ⟨"BaseTwo", by decide⟩ 0
def Jump : ProgramNames := .programSymbol ⟨"Jump", by decide⟩ 0
def P : ProgramNames := .programSymbol ⟨"P", by decide⟩ 0
def Q : ProgramNames := .programSymbol ⟨"Q", by decide⟩ 0
def Tri : ProgramNames := .programSymbol ⟨"Tri", by decide⟩ 0
def schema_c1 : UnnamedSchema ProgramNames := programSch![ {C, Mid, Link, BaseTwo, Jump, P, Q} (arity: 2), {Tri} (arity: 3) ]
def prog_c1 : Datalog.Program Data schema_c1 := datalog![
  P(x1, y1) :- Link(x1, y1);
  P(x1, y1) :- Mid(x1, y1);
  P(x1, z1) :- P(x1, y1), Q(y1, z1);
  P(x1, x2) :- P(x1, y1), Mid(y1, z1), P(z1, x2);
  Q(x1, y1) :- Tri(x1, z1, y1);
  Q(x1, z1) :- Q(x1, y1), P(y1, z1);
]
def compiledRaw_c1 : RawCmd ProgramNames Data := mapCmd toRawInput prog_c1.toWhielCmd.toRaw
def T : ProgramNames := .programSymbol ⟨"T", by decide⟩ 0
def G : ProgramNames := .programSymbol ⟨"G", by decide⟩ 0
def schema_c2 : UnnamedSchema ProgramNames := programSch![ {C, Mid, Link, BaseTwo, Jump, T, G} (arity: 2), {Tri} (arity: 3) ]
def prog_c2 : Datalog.Program Data schema_c2 := datalog![
  T(x1, y1) :- BaseTwo(x1, y1);
  G(x1, y1) :- Jump(x1, y1);
  G(x1, z1) :- G(x1, y1), Jump(y1, z1);
  T(x1, z1) :- T(x1, y1), G(y1, z1);
  T(x1, z1) :- T(x1, y1), T(y1, z1);
]
def compiledRaw_c2 : RawCmd ProgramNames Data := mapCmd toRawInput prog_c2.toWhielCmd.toRaw
/- The compiled sides are the compiler's output, the hand-written sides are the segments above, and
   their sequence is the input command. -/
theorem inputCmd_eq : seqAfter compiledRaw_c1 compiledRaw_c2 = inputCmd.toRaw := by
  decide +kernel
end Whiel.Benchmark.Example1091.Fidelity
