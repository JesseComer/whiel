-- Author: Leo Zhang
import Benchmark.Example5004.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

namespace Whiel.Benchmark.Example5004.Fidelity
open Whiel Whiel.Concrete Whiel.Synthesis.Tests.BenchmarkFidelity
open Whiel.Benchmark.Example5004 (inputSchema inputCmd)
def RoleInh : ProgramNames := .programSymbol ⟨"RoleInh", by decide⟩ 0
def Inh : ProgramNames := .programSymbol ⟨"Inh", by decide⟩ 0
def UserRole : ProgramNames := .programSymbol ⟨"UserRole", by decide⟩ 0
def HasM : ProgramNames := .programSymbol ⟨"HasM", by decide⟩ 0
def Has : ProgramNames := .programSymbol ⟨"Has", by decide⟩ 0
def schema_pa : UnnamedSchema ProgramNames := programSch![ {RoleInh, Inh} (arity: 2) ]
def prog_pa : Datalog.Program Data schema_pa := datalog![
  Inh(x1, y1) :- RoleInh(x1, y1);
  Inh(x1, z1) :- Inh(x1, y1), RoleInh(y1, z1);
]
def compiledRaw_pa : RawCmd ProgramNames Data := mapCmd toRawInput prog_pa.toWhielCmd.toRaw
def schema_pb : UnnamedSchema ProgramNames := programSch![ {UserRole, Inh, HasM} (arity: 2) ]
def prog_pb : Datalog.Program Data schema_pb := datalog![
  HasM(x1, y1) :- UserRole(x1, y1);
  HasM(x1, z1) :- UserRole(x1, y1), Inh(y1, z1);
]
def compiledRaw_pb : RawCmd ProgramNames Data := mapCmd toRawInput prog_pb.toWhielCmd.toRaw
def schema_pc : UnnamedSchema ProgramNames := programSch![ {UserRole, RoleInh, Has} (arity: 2) ]
def prog_pc : Datalog.Program Data schema_pc := datalog![
  Has(x1, y1) :- UserRole(x1, y1);
  Has(x1, z1) :- Has(x1, y1), RoleInh(y1, z1);
]
def compiledRaw_pc : RawCmd ProgramNames Data := mapCmd toRawInput prog_pc.toWhielCmd.toRaw
/- The compiled sides are the compiler's output and the sequence is the input command. -/
theorem inputCmd_eq : seqAfter compiledRaw_pa (seqAfter compiledRaw_pb compiledRaw_pc) = inputCmd.toRaw := by
  decide +kernel
end Whiel.Benchmark.Example5004.Fidelity
