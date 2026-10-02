-- Author: Leo Zhang
import Benchmark.Example1081.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

namespace Whiel.Benchmark.Example1081.Fidelity
open Whiel Whiel.Concrete Whiel.Synthesis.Tests.BenchmarkFidelity
open Whiel.Benchmark.Example1081 (inputSchema inputCmd)
/- The Datalog program(s) of the header: compiled sides are their naive compilation; reference programs
   are compared with the hand-written sides on the check instances. -/
def Valid : ProgramNames := .programSymbol ⟨"Valid", by decide⟩ 0
def Trusted : ProgramNames := .programSymbol ⟨"Trusted", by decide⟩ 0
def Special : ProgramNames := .programSymbol ⟨"Special", by decide⟩ 0
def Composite : ProgramNames := .programSymbol ⟨"Composite", by decide⟩ 0
def Broad : ProgramNames := .programSymbol ⟨"Broad", by decide⟩ 0
def Grant : ProgramNames := .programSymbol ⟨"Grant", by decide⟩ 0
def Delegated : ProgramNames := .programSymbol ⟨"Delegated", by decide⟩ 0
def Audited : ProgramNames := .programSymbol ⟨"Audited", by decide⟩ 0
def Evidence : ProgramNames := .programSymbol ⟨"Evidence", by decide⟩ 0
def schema_c1 : UnnamedSchema ProgramNames := programSch![ {Valid} (arity: 1), {Trusted, Special, Composite, Broad, Grant, Delegated, Audited} (arity: 2), {Evidence} (arity: 3) ]
def prog_c1 : Datalog.Program Data schema_c1 := datalog![
  Grant(x1, y1) :- Trusted(x1, y1);
  Delegated(x1, y1) :- Special(x1, y1);
  Audited(x1, y1) :- Composite(x1, y1);
  Grant(x1, z1) :- Delegated(x1, y1), Audited(y1, z1);
  Delegated(x1, z1) :- Grant(x1, y1), Trusted(y1, z1);
  Audited(x1, z1) :- Grant(x1, y1), Evidence(y1, z1, x2), Valid(x2);
  Grant(x1, z1) :- Grant(x1, y1), Audited(y1, z1);
]
def compiledRaw_c1 : RawCmd ProgramNames Data := mapCmd toRawInput prog_c1.toWhielCmd.toRaw
def Permit : ProgramNames := .programSymbol ⟨"Permit", by decide⟩ 0
def Trace : ProgramNames := .programSymbol ⟨"Trace", by decide⟩ 0
def schema_c2 : UnnamedSchema ProgramNames := programSch![ {Valid} (arity: 1), {Trusted, Special, Composite, Broad, Permit, Trace} (arity: 2), {Evidence} (arity: 3) ]
def prog_c2 : Datalog.Program Data schema_c2 := datalog![
  Permit(x1, y1) :- Broad(x1, y1);
  Trace(x1, y1) :- Broad(x1, y1);
  Permit(x1, y1) :- Evidence(x1, y1, z1), Valid(z1);
  Permit(x1, y1) :- Trace(x1, y1);
  Trace(x1, z1) :- Permit(x1, y1), Permit(y1, z1);
  Trace(x1, z1) :- Permit(x1, y1), Trace(y1, z1);
  Trace(x1, z1) :- Trace(x1, y1), Permit(y1, z1);
  Trace(x1, z1) :- Trace(x1, y1), Trace(y1, z1);
  Trace(x1, z1) :- Permit(x1, y1), Evidence(y1, z1, x2), Valid(x2);
]
def compiledRaw_c2 : RawCmd ProgramNames Data := mapCmd toRawInput prog_c2.toWhielCmd.toRaw
/- The compiled sides are the compiler's output, the hand-written sides are the segments above, and
   their sequence is the input command. -/
theorem inputCmd_eq : seqAfter compiledRaw_c1 compiledRaw_c2 = inputCmd.toRaw := by
  decide +kernel
end Whiel.Benchmark.Example1081.Fidelity
