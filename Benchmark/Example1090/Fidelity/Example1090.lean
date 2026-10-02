-- Author: Leo Zhang
import Benchmark.Example1090.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

namespace Whiel.Benchmark.Example1090.Fidelity
open Whiel Whiel.Concrete Whiel.Synthesis.Tests.BenchmarkFidelity
open Whiel.Benchmark.Example1090 (inputSchema inputCmd)
/- The Datalog program(s) of the header: compiled sides are their naive compilation; reference programs
   are compared with the hand-written sides on the check instances. -/
def EnabledMode : ProgramNames := .programSymbol ⟨"EnabledMode", by decide⟩ 0
def SeedPair : ProgramNames := .programSymbol ⟨"SeedPair", by decide⟩ 0
def InputPair : ProgramNames := .programSymbol ⟨"InputPair", by decide⟩ 0
def FlowEdge : ProgramNames := .programSymbol ⟨"FlowEdge", by decide⟩ 0
def ViewEdge : ProgramNames := .programSymbol ⟨"ViewEdge", by decide⟩ 0
def ModeTag : ProgramNames := .programSymbol ⟨"ModeTag", by decide⟩ 0
def TaintReach : ProgramNames := .programSymbol ⟨"TaintReach", by decide⟩ 0
def StateWitness : ProgramNames := .programSymbol ⟨"StateWitness", by decide⟩ 0
def TaintState : ProgramNames := .programSymbol ⟨"TaintState", by decide⟩ 0
def schema_c1 : UnnamedSchema ProgramNames := programSch![ {EnabledMode} (arity: 1), {SeedPair, InputPair, FlowEdge, ViewEdge, ModeTag, TaintReach} (arity: 2), {StateWitness, TaintState} (arity: 3) ]
def prog_c1 : Datalog.Program Data schema_c1 := datalog![
  TaintReach(x1, y1) :- SeedPair(x1, y1);
  TaintState(x1, y1, z1) :- SeedPair(x1, y1), ModeTag(y1, z1);
  TaintReach(x1, z1) :- TaintState(x1, y1, x2), FlowEdge(y1, z1);
  TaintState(x1, z1, x2) :- TaintReach(x1, y1), FlowEdge(y1, z1), ModeTag(z1, x2);
  TaintState(x1, z1, y2) :- TaintState(x1, y1, x2), FlowEdge(y1, z1), ModeTag(z1, y2);
  TaintReach(x1, z1) :- TaintReach(x1, y1), TaintReach(y1, z1);
]
def compiledRaw_c1 : RawCmd ProgramNames Data := mapCmd toRawInput prog_c1.toWhielCmd.toRaw
def AnalysisReach : ProgramNames := .programSymbol ⟨"AnalysisReach", by decide⟩ 0
def FrontierState : ProgramNames := .programSymbol ⟨"FrontierState", by decide⟩ 0
def schema_c2 : UnnamedSchema ProgramNames := programSch![ {EnabledMode} (arity: 1), {SeedPair, InputPair, FlowEdge, ViewEdge, ModeTag, AnalysisReach, FrontierState} (arity: 2), {StateWitness} (arity: 3) ]
def prog_c2 : Datalog.Program Data schema_c2 := datalog![
  AnalysisReach(x1, y1) :- InputPair(x1, y1);
  FrontierState(x1, y1) :- InputPair(x1, y1);
  AnalysisReach(x1, z1) :- FrontierState(x1, y1), ViewEdge(y1, z1);
  FrontierState(x1, z1) :- AnalysisReach(x1, y1), ViewEdge(y1, z1);
  FrontierState(x1, z1) :- FrontierState(x1, y1), StateWitness(y1, z1, x2), EnabledMode(x2);
  AnalysisReach(x1, z1) :- AnalysisReach(x1, y1), AnalysisReach(y1, z1);
]
def compiledRaw_c2 : RawCmd ProgramNames Data := mapCmd toRawInput prog_c2.toWhielCmd.toRaw
/- The compiled sides are the compiler's output, the hand-written sides are the segments above, and
   their sequence is the input command. -/
theorem inputCmd_eq : seqAfter compiledRaw_c1 compiledRaw_c2 = inputCmd.toRaw := by
  decide +kernel
end Whiel.Benchmark.Example1090.Fidelity
