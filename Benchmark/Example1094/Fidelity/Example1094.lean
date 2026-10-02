-- Author: Leo Zhang
import Benchmark.Example1094.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

namespace Whiel.Benchmark.Example1094.Fidelity
open Whiel Whiel.Concrete Whiel.Synthesis.Tests.BenchmarkFidelity
open Whiel.Benchmark.Example1094 (inputSchema inputCmd)
/- The Datalog program(s) of the header: compiled sides are their naive compilation; reference programs
   are compared with the hand-written sides on the check instances. -/
def Peer : ProgramNames := .programSymbol ⟨"Peer", by decide⟩ 0
def Adj : ProgramNames := .programSymbol ⟨"Adj", by decide⟩ 0
def Admin : ProgramNames := .programSymbol ⟨"Admin", by decide⟩ 0
def Route : ProgramNames := .programSymbol ⟨"Route", by decide⟩ 0
def Hop : ProgramNames := .programSymbol ⟨"Hop", by decide⟩ 0
def Relay : ProgramNames := .programSymbol ⟨"Relay", by decide⟩ 0
def schema_c1 : UnnamedSchema ProgramNames := programSch![ {Peer, Adj, Admin, Route, Hop} (arity: 2), {Relay} (arity: 3) ]
def prog_c1 : Datalog.Program Data schema_c1 := datalog![
  Route(x1, y1) :- Peer(x1, y1);
  Hop(x1, y1) :- Adj(x1, y1);
  Hop(x1, z1) :- Route(x1, y1), Hop(y1, z1);
  Route(x1, z1) :- Route(x1, y1), Hop(y1, z1);
  Route(x1, z1) :- Route(x1, y1), Relay(y1, x2, z1);
  Route(x1, z1) :- Route(x1, y1), Route(y1, z1);
]
def compiledRaw_c1 : RawCmd ProgramNames Data := mapCmd toRawInput prog_c1.toWhielCmd.toRaw
def Dist : ProgramNames := .programSymbol ⟨"Dist", by decide⟩ 0
def Span : ProgramNames := .programSymbol ⟨"Span", by decide⟩ 0
def schema_c2 : UnnamedSchema ProgramNames := programSch![ {Peer, Adj, Admin, Dist, Span} (arity: 2), {Relay} (arity: 3) ]
def prog_c2 : Datalog.Program Data schema_c2 := datalog![
  Dist(x1, y1) :- Admin(x1, y1);
  Span(x1, y1) :- Adj(x1, y1);
  Span(x1, z1) :- Span(x1, y1), Span(y1, z1);
  Dist(x1, z1) :- Dist(x1, y1), Span(y1, z1);
  Dist(x1, z1) :- Dist(x1, y1), Dist(y1, z1);
]
def compiledRaw_c2 : RawCmd ProgramNames Data := mapCmd toRawInput prog_c2.toWhielCmd.toRaw
/- The compiled sides are the compiler's output, the hand-written sides are the segments above, and
   their sequence is the input command. -/
theorem inputCmd_eq : seqAfter compiledRaw_c1 compiledRaw_c2 = inputCmd.toRaw := by
  decide +kernel
end Whiel.Benchmark.Example1094.Fidelity
