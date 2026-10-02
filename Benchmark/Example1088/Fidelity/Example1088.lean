-- Author: Leo Zhang
import Benchmark.Example1088.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

namespace Whiel.Benchmark.Example1088.Fidelity
open Whiel Whiel.Concrete Whiel.Synthesis.Tests.BenchmarkFidelity
open Whiel.Benchmark.Example1088 (inputSchema inputCmd)
/- The Datalog program(s) of the header: compiled sides are their naive compilation; reference programs
   are compared with the hand-written sides on the check instances. -/
def ValidBridge : ProgramNames := .programSymbol ⟨"ValidBridge", by decide⟩ 0
def ForwardSeed : ProgramNames := .programSymbol ⟨"ForwardSeed", by decide⟩ 0
def BackwardSeed : ProgramNames := .programSymbol ⟨"BackwardSeed", by decide⟩ 0
def ForwardEdge : ProgramNames := .programSymbol ⟨"ForwardEdge", by decide⟩ 0
def BackwardEdge : ProgramNames := .programSymbol ⟨"BackwardEdge", by decide⟩ 0
def ForwardReach : ProgramNames := .programSymbol ⟨"ForwardReach", by decide⟩ 0
def ForwardStep : ProgramNames := .programSymbol ⟨"ForwardStep", by decide⟩ 0
def BridgeProof : ProgramNames := .programSymbol ⟨"BridgeProof", by decide⟩ 0
def schema_c1 : UnnamedSchema ProgramNames := programSch![ {ValidBridge} (arity: 1), {ForwardSeed, BackwardSeed, ForwardEdge, BackwardEdge, ForwardReach, ForwardStep} (arity: 2), {BridgeProof} (arity: 3) ]
def prog_c1 : Datalog.Program Data schema_c1 := datalog![
  ForwardReach(x1, y1) :- ForwardSeed(x1, y1);
  ForwardStep(x1, y1) :- ForwardEdge(x1, y1);
  ForwardReach(x1, z1) :- ForwardReach(x1, y1), ForwardStep(y1, z1);
  ForwardStep(x1, z1) :- ForwardReach(x1, y1), BridgeProof(y1, z1, x2), ValidBridge(x2);
  ForwardReach(x1, z1) :- ForwardStep(x1, y1), ForwardReach(y1, z1);
]
def compiledRaw_c1 : RawCmd ProgramNames Data := mapCmd toRawInput prog_c1.toWhielCmd.toRaw
def ResolvedPair : ProgramNames := .programSymbol ⟨"ResolvedPair", by decide⟩ 0
def ReverseStep : ProgramNames := .programSymbol ⟨"ReverseStep", by decide⟩ 0
def schema_c2 : UnnamedSchema ProgramNames := programSch![ {ValidBridge} (arity: 1), {ForwardSeed, BackwardSeed, ForwardEdge, BackwardEdge, ResolvedPair, ReverseStep} (arity: 2), {BridgeProof} (arity: 3) ]
def prog_c2 : Datalog.Program Data schema_c2 := datalog![
  ResolvedPair(x1, y1) :- BackwardSeed(y1, x1);
  ReverseStep(y1, x1) :- BackwardEdge(y1, x1);
  ResolvedPair(x1, z1) :- ResolvedPair(x1, y1), ReverseStep(z1, y1);
  ReverseStep(z1, x1) :- ResolvedPair(x1, y1), BridgeProof(y1, z1, x2), ValidBridge(x2);
  ResolvedPair(x1, z1) :- ReverseStep(y1, x1), ResolvedPair(y1, z1);
]
def compiledRaw_c2 : RawCmd ProgramNames Data := mapCmd toRawInput prog_c2.toWhielCmd.toRaw
/- The compiled sides are the compiler's output, the hand-written sides are the segments above, and
   their sequence is the input command. -/
theorem inputCmd_eq : seqAfter compiledRaw_c1 compiledRaw_c2 = inputCmd.toRaw := by
  decide +kernel
end Whiel.Benchmark.Example1088.Fidelity
