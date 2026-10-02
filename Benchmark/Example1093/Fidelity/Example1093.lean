-- Author: Leo Zhang
import Benchmark.Example1093.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

namespace Whiel.Benchmark.Example1093.Fidelity
open Whiel Whiel.Concrete Whiel.Synthesis.Tests.BenchmarkFidelity
open Whiel.Benchmark.Example1093 (inputSchema inputCmd)
/- The Datalog program(s) of the header: compiled sides are their naive compilation; reference programs
   are compared with the hand-written sides on the check instances. -/
def Edge : ProgramNames := .programSymbol ⟨"Edge", by decide⟩ 0
def Gen : ProgramNames := .programSymbol ⟨"Gen", by decide⟩ 0
def Reach : ProgramNames := .programSymbol ⟨"Reach", by decide⟩ 0
def Fact : ProgramNames := .programSymbol ⟨"Fact", by decide⟩ 0
def Cover : ProgramNames := .programSymbol ⟨"Cover", by decide⟩ 0
def Lin : ProgramNames := .programSymbol ⟨"Lin", by decide⟩ 0
def schema_c1 : UnnamedSchema ProgramNames := programSch![ {Edge, Gen, Reach} (arity: 2), {Fact, Cover, Lin} (arity: 3) ]
def prog_c1 : Datalog.Program Data schema_c1 := datalog![
  Reach(x1, y1) :- Edge(x1, y1);
  Reach(x1, z1) :- Reach(x1, y1), Reach(y1, z1);
  Reach(x1, y1) :- Lin(x1, y1, z1);
  Lin(x1, y1, z1) :- Fact(x1, y1, z1);
  Lin(x1, z1, z2) :- Lin(x1, y1, z2), Reach(y1, z1);
  Lin(x2, y1, z1) :- Lin(x1, y1, z1), Gen(x1, x2);
]
def compiledRaw_c1 : RawCmd ProgramNames Data := mapCmd toRawInput prog_c1.toWhielCmd.toRaw
def Trav : ProgramNames := .programSymbol ⟨"Trav", by decide⟩ 0
def Prov : ProgramNames := .programSymbol ⟨"Prov", by decide⟩ 0
def schema_c2 : UnnamedSchema ProgramNames := programSch![ {Edge, Gen, Trav} (arity: 2), {Fact, Cover, Prov} (arity: 3) ]
def prog_c2 : Datalog.Program Data schema_c2 := datalog![
  Prov(x1, y1, z1) :- Cover(x1, y1, z1);
  Trav(x1, y1) :- Edge(x1, y1);
  Trav(x1, z1) :- Trav(x1, y1), Trav(y1, z1);
  Prov(x1, z1, z2) :- Prov(x1, y1, z2), Trav(y1, z1);
  Prov(x2, y1, z1) :- Prov(x1, y1, z1), Gen(x1, x2);
]
def compiledRaw_c2 : RawCmd ProgramNames Data := mapCmd toRawInput prog_c2.toWhielCmd.toRaw
/- The compiled sides are the compiler's output, the hand-written sides are the segments above, and
   their sequence is the input command. -/
theorem inputCmd_eq : seqAfter compiledRaw_c1 compiledRaw_c2 = inputCmd.toRaw := by
  decide +kernel
end Whiel.Benchmark.Example1093.Fidelity
