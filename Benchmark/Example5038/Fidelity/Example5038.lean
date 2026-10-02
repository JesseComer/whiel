-- Author: Leo Zhang
import Benchmark.Example5038.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

namespace Whiel.Benchmark.Example5038.Fidelity
open Whiel Whiel.Concrete Whiel.Synthesis.Tests.BenchmarkFidelity
open Whiel.Benchmark.Example5038 (inputSchema inputCmd)
/- The Datalog program(s) of the header: compiled sides are their naive compilation; reference programs
   are compared with the hand-written sides on the check instances. -/
def Query : ProgramNames := .programSymbol ⟨"Query", by decide⟩ 0
def QUser : ProgramNames := .programSymbol ⟨"QUser", by decide⟩ 0
def Demand : ProgramNames := .programSymbol ⟨"Demand", by decide⟩ 0
def DirectMember : ProgramNames := .programSymbol ⟨"DirectMember", by decide⟩ 0
def SubGroup : ProgramNames := .programSymbol ⟨"SubGroup", by decide⟩ 0
def Ans : ProgramNames := .programSymbol ⟨"Ans", by decide⟩ 0
def schema_demand : UnnamedSchema ProgramNames := programSch![ {Query, QUser, Demand} (arity: 1), {DirectMember, SubGroup, Ans} (arity: 2) ]
def prog_demand : Datalog.Program Data schema_demand := datalog![
  Demand(x1) :- Query(x1);
  Demand(y1) :- Demand(x1), SubGroup(y1, x1);
  Ans(x1, y1) :- Demand(y1), QUser(x1), DirectMember(x1, y1);
  Ans(x1, y1) :- Demand(y1), SubGroup(z1, y1), Ans(x1, z1);
]
def compiledRaw_demand : RawCmd ProgramNames Data := mapCmd toRawInput prog_demand.toWhielCmd.toRaw
def Reach : ProgramNames := .programSymbol ⟨"Reach", by decide⟩ 0
def schema_reach : UnnamedSchema ProgramNames := programSch![ {QUser} (arity: 1), {DirectMember, SubGroup, Reach} (arity: 2) ]
def prog_reach : Datalog.Program Data schema_reach := datalog![
  Reach(x1, y1) :- QUser(x1), DirectMember(x1, y1);
  Reach(x1, z1) :- Reach(x1, y1), SubGroup(y1, z1);
]
def compiledRaw_reach : RawCmd ProgramNames Data := mapCmd toRawInput prog_reach.toWhielCmd.toRaw
def MemberR : ProgramNames := .programSymbol ⟨"MemberR", by decide⟩ 0
def schema_MemberR : UnnamedSchema ProgramNames := programSch![ {DirectMember, SubGroup, MemberR} (arity: 2) ]
def prog_MemberR : Datalog.Program Data schema_MemberR := datalog![
  MemberR(x1, y1) :- DirectMember(x1, y1);
  MemberR(x1, z1) :- MemberR(x1, y1), SubGroup(y1, z1);
]
def compiledRaw_MemberR : RawCmd ProgramNames Data := mapCmd toRawInput prog_MemberR.toWhielCmd.toRaw
/- The compiled sides are the compiler's output, the hand-written sides are the segments above, and
   their sequence is the input command. -/
theorem inputCmd_eq : seqAfter compiledRaw_demand compiledRaw_reach = inputCmd.toRaw := by
  decide +kernel
end Whiel.Benchmark.Example5038.Fidelity
