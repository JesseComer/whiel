-- Author: Leo Zhang
import Benchmark.Example3001.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

namespace Whiel.Benchmark.Example3001.Fidelity
open Whiel Whiel.Concrete Whiel.Synthesis.Tests.BenchmarkFidelity
open Whiel.Benchmark.Example3001 (inputSchema inputCmd)
/- The Datalog program(s) of the header: compiled sides are their naive compilation; reference programs
   are compared with the hand-written sides on the check instances. -/
def Root : ProgramNames := .programSymbol ⟨"Root", by decide⟩ 0
def Certified : ProgramNames := .programSymbol ⟨"Certified", by decide⟩ 0
def Review : ProgramNames := .programSymbol ⟨"Review", by decide⟩ 0
def Reviewer : ProgramNames := .programSymbol ⟨"Reviewer", by decide⟩ 0
def Delegates : ProgramNames := .programSymbol ⟨"Delegates", by decide⟩ 0
def AccessOne : ProgramNames := .programSymbol ⟨"AccessOne", by decide⟩ 0
def CertStateOne : ProgramNames := .programSymbol ⟨"CertStateOne", by decide⟩ 0
def ReviewStateOne : ProgramNames := .programSymbol ⟨"ReviewStateOne", by decide⟩ 0
def schema_c1 : UnnamedSchema ProgramNames := programSch![ {Root} (arity: 1), {Certified} (arity: 2), {Review} (arity: 3), {Reviewer} (arity: 1), {Delegates} (arity: 2), {AccessOne} (arity: 1), {CertStateOne} (arity: 1), {ReviewStateOne} (arity: 1) ]
def prog_c1 : Datalog.Program Data schema_c1 := datalog![
  AccessOne(x1) :- Root(x1);
  CertStateOne(y1) :- AccessOne(x1), Certified(x1, y1);
  ReviewStateOne(y1) :- AccessOne(x1), Review(x1, y1, z1), Reviewer(z1);
  AccessOne(y1) :- CertStateOne(x1), Review(x1, y1, z1), Reviewer(z1);
  AccessOne(y1) :- ReviewStateOne(x1), Certified(x1, y1);
  AccessOne(y1) :- CertStateOne(y1), ReviewStateOne(y1), Delegates(x1, y1);
]
def compiledRaw_c1 : RawCmd ProgramNames Data := mapCmd toRawInput prog_c1.toWhielCmd.toRaw
def AccessTwo : ProgramNames := .programSymbol ⟨"AccessTwo", by decide⟩ 0
def CertStateTwo : ProgramNames := .programSymbol ⟨"CertStateTwo", by decide⟩ 0
def ReviewStateTwo : ProgramNames := .programSymbol ⟨"ReviewStateTwo", by decide⟩ 0
def JointStateTwo : ProgramNames := .programSymbol ⟨"JointStateTwo", by decide⟩ 0
def schema_c2 : UnnamedSchema ProgramNames := programSch![ {Root} (arity: 1), {Certified} (arity: 2), {Review} (arity: 3), {Reviewer} (arity: 1), {Delegates} (arity: 2), {AccessTwo} (arity: 1), {CertStateTwo} (arity: 1), {ReviewStateTwo} (arity: 1), {JointStateTwo} (arity: 1) ]
def prog_c2 : Datalog.Program Data schema_c2 := datalog![
  AccessTwo(x1) :- Root(x1);
  CertStateTwo(y1) :- AccessTwo(x1), Certified(x1, y1);
  ReviewStateTwo(y1) :- AccessTwo(x1), Review(x1, y1, z1), Reviewer(z1);
  JointStateTwo(y1) :- CertStateTwo(x1), Review(x1, y1, z1), Reviewer(z1), Certified(x1, y1);
  AccessTwo(y1) :- JointStateTwo(y1), Delegates(x1, y1);
  AccessTwo(y1) :- CertStateTwo(y1), ReviewStateTwo(y1), Delegates(x1, y1);
]
def compiledRaw_c2 : RawCmd ProgramNames Data := mapCmd toRawInput prog_c2.toWhielCmd.toRaw
/- The compiled sides are the compiler's output, the hand-written sides are the segments above, and
   their sequence is the input command. -/
theorem inputCmd_eq : seqAfter compiledRaw_c1 compiledRaw_c2 = inputCmd.toRaw := by
  decide +kernel
end Whiel.Benchmark.Example3001.Fidelity
