-- Author: Leo Zhang
import Benchmark.Example3014.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

namespace Whiel.Benchmark.Example3014.Fidelity
open Whiel Whiel.Concrete Whiel.Synthesis.Tests.BenchmarkFidelity
open Whiel.Benchmark.Example3014 (inputSchema inputCmd)
/- The Datalog program(s) of the header: compiled sides are their naive compilation; reference programs
   are compared with the hand-written sides on the check instances. -/
def Request : ProgramNames := .programSymbol ⟨"Request", by decide⟩ 0
def Permit : ProgramNames := .programSymbol ⟨"Permit", by decide⟩ 0
def Grant : ProgramNames := .programSymbol ⟨"Grant", by decide⟩ 0
def Override : ProgramNames := .programSymbol ⟨"Override", by decide⟩ 0
def Scope : ProgramNames := .programSymbol ⟨"Scope", by decide⟩ 0
def Proof : ProgramNames := .programSymbol ⟨"Proof", by decide⟩ 0
def Trusted : ProgramNames := .programSymbol ⟨"Trusted", by decide⟩ 0
def AccessA : ProgramNames := .programSymbol ⟨"AccessA", by decide⟩ 0
def ElevatedA : ProgramNames := .programSymbol ⟨"ElevatedA", by decide⟩ 0
def CheckedA : ProgramNames := .programSymbol ⟨"CheckedA", by decide⟩ 0
def schema_c1 : UnnamedSchema ProgramNames := programSch![ {Request} (arity: 2), {Permit} (arity: 2), {Grant} (arity: 2), {Override} (arity: 2), {Scope} (arity: 1), {Proof} (arity: 3), {Trusted} (arity: 1), {AccessA} (arity: 2), {ElevatedA} (arity: 2), {CheckedA} (arity: 2) ]
def prog_c1 : Datalog.Program Data schema_c1 := datalog![
  AccessA(x1, y1) :- Request(x1, y1), Permit(x1, y1);
  ElevatedA(x1, z1) :- AccessA(x1, y1), Grant(y1, z1), Scope(z1);
  CheckedA(x1, z1) :- ElevatedA(x1, y1), Override(y1, z1), Proof(x1, z1, x2), Trusted(x2);
  AccessA(x1, z1) :- CheckedA(x1, z1);
  ElevatedA(x1, z1) :- AccessA(x1, y1), AccessA(x1, x2), Proof(y1, z1, x2);
]
def compiledRaw_c1 : RawCmd ProgramNames Data := mapCmd toRawInput prog_c1.toWhielCmd.toRaw
def AccessB : ProgramNames := .programSymbol ⟨"AccessB", by decide⟩ 0
def ElevatedB : ProgramNames := .programSymbol ⟨"ElevatedB", by decide⟩ 0
def AuditB : ProgramNames := .programSymbol ⟨"AuditB", by decide⟩ 0
def schema_c2 : UnnamedSchema ProgramNames := programSch![ {Request} (arity: 2), {Permit} (arity: 2), {Grant} (arity: 2), {Override} (arity: 2), {Scope} (arity: 1), {Proof} (arity: 3), {Trusted} (arity: 1), {AccessB} (arity: 2), {ElevatedB} (arity: 2), {AuditB} (arity: 3) ]
def prog_c2 : Datalog.Program Data schema_c2 := datalog![
  AccessB(x1, y1) :- Request(x1, y1), Permit(x1, y1);
  ElevatedB(x1, z1) :- AccessB(x1, y1), Grant(y1, z1), Scope(z1);
  AuditB(x1, z1, x2) :- ElevatedB(x1, y1), Override(y1, z1), Proof(x1, z1, x2);
  AccessB(x1, z1) :- AuditB(x1, z1, x2), Trusted(z1);
  ElevatedB(x1, z1) :- AccessB(x1, y1), AccessB(x1, x2), Proof(y1, z1, x2);
]
def compiledRaw_c2 : RawCmd ProgramNames Data := mapCmd toRawInput prog_c2.toWhielCmd.toRaw
/- The compiled sides are the compiler's output, the hand-written sides are the segments above, and
   their sequence is the input command. -/
theorem inputCmd_eq : seqAfter compiledRaw_c1 compiledRaw_c2 = inputCmd.toRaw := by
  decide +kernel
end Whiel.Benchmark.Example3014.Fidelity
