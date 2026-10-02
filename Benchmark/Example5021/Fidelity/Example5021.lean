-- Author: Leo Zhang
import Benchmark.Example5021.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

namespace Whiel.Benchmark.Example5021.Fidelity
open Whiel Whiel.Concrete Whiel.Synthesis.Tests.BenchmarkFidelity
open Whiel.Benchmark.Example5021 (inputSchema inputCmd)
def TypeOf : ProgramNames := .programSymbol ⟨"TypeOf", by decide⟩ 0
def SubClass : ProgramNames := .programSymbol ⟨"SubClass", by decide⟩ 0
def SubProp : ProgramNames := .programSymbol ⟨"SubProp", by decide⟩ 0
def Dom : ProgramNames := .programSymbol ⟨"Dom", by decide⟩ 0
def Range : ProgramNames := .programSymbol ⟨"Range", by decide⟩ 0
def Triple : ProgramNames := .programSymbol ⟨"Triple", by decide⟩ 0
def TypeM : ProgramNames := .programSymbol ⟨"TypeM", by decide⟩ 0
def SubClassM : ProgramNames := .programSymbol ⟨"SubClassM", by decide⟩ 0
def SubPropM : ProgramNames := .programSymbol ⟨"SubPropM", by decide⟩ 0
def TripleM : ProgramNames := .programSymbol ⟨"TripleM", by decide⟩ 0
def TypeF : ProgramNames := .programSymbol ⟨"TypeF", by decide⟩ 0
def SubClassF : ProgramNames := .programSymbol ⟨"SubClassF", by decide⟩ 0
def SubPropF : ProgramNames := .programSymbol ⟨"SubPropF", by decide⟩ 0
def TripleF : ProgramNames := .programSymbol ⟨"TripleF", by decide⟩ 0
def IsProp : ProgramNames := .programSymbol ⟨"IsProp", by decide⟩ 0
def IsClass : ProgramNames := .programSymbol ⟨"IsClass", by decide⟩ 0
/- rho-df, the system ⊢mrdf: rules (2a), (2b), (3a), (3b), (4a), (4b) of Munoz, Perez, Gutierrez (= rdfs5, rdfs7, rdfs11, rdfs9, rdfs2, rdfs3). -/
def schema_pm : UnnamedSchema ProgramNames := programSch![ {TypeOf, SubClass, SubProp, Dom, Range, TypeM, SubClassM, SubPropM} (arity: 2), {Triple, TripleM} (arity: 3) ]
def prog_pm : Datalog.Program Data schema_pm := datalog![
  SubPropM(x1, y1) :- SubProp(x1, y1);
  SubPropM(x1, z1) :- SubPropM(x1, y1), SubPropM(y1, z1);
  TripleM(x1, y1, z1) :- Triple(x1, y1, z1);
  TripleM(x1, z1, y1) :- SubPropM(x2, z1), TripleM(x1, x2, y1);
  SubClassM(x1, y1) :- SubClass(x1, y1);
  SubClassM(x1, z1) :- SubClassM(x1, y1), SubClassM(y1, z1);
  TypeM(x1, y1) :- TypeOf(x1, y1);
  TypeM(x1, z1) :- SubClassM(y1, z1), TypeM(x1, y1);
  TypeM(x1, z1) :- Dom(y1, z1), TripleM(x1, y1, x2);
  TypeM(y1, z1) :- Range(x2, z1), TripleM(x1, x2, y1);
]
def compiledRaw_pm : RawCmd ProgramNames Data := mapCmd toRawInput prog_pm.toWhielCmd.toRaw
/- The W3C RDFS entailment patterns on mrdf-graphs: the six shared patterns, rdfs6, rdfs10, rdfD2 and the
   typing forced by the RDFS axiomatic triples of the rho-df vocabulary (IsProp = rdf:type rdf:Property,
   IsClass = rdf:type rdfs:Class). -/
def schema_pf : UnnamedSchema ProgramNames := programSch![ {TypeOf, SubClass, SubProp, Dom, Range, TypeF, SubClassF, SubPropF} (arity: 2), {Triple, TripleF} (arity: 3), {IsProp, IsClass} (arity: 1) ]
def prog_pf : Datalog.Program Data schema_pf := datalog![
  SubPropF(x1, y1) :- SubProp(x1, y1);
  SubPropF(x1, z1) :- SubPropF(x1, y1), SubPropF(y1, z1);
  SubPropF(x1, x1) :- IsProp(x1);
  TripleF(x1, y1, z1) :- Triple(x1, y1, z1);
  TripleF(x1, z1, y1) :- SubPropF(x2, z1), TripleF(x1, x2, y1);
  SubClassF(x1, y1) :- SubClass(x1, y1);
  SubClassF(x1, z1) :- SubClassF(x1, y1), SubClassF(y1, z1);
  SubClassF(x1, x1) :- IsClass(x1);
  TypeF(x1, y1) :- TypeOf(x1, y1);
  TypeF(x1, z1) :- SubClassF(y1, z1), TypeF(x1, y1);
  TypeF(x1, z1) :- Dom(y1, z1), TripleF(x1, y1, x2);
  TypeF(y1, z1) :- Range(x2, z1), TripleF(x1, x2, y1);
  IsProp(y1) :- TripleF(x1, y1, z1);
  IsProp(x1) :- SubPropF(x1, y1);
  IsProp(y1) :- SubPropF(x1, y1);
  IsProp(x1) :- Dom(x1, y1);
  IsProp(x1) :- Range(x1, y1);
  IsClass(y1) :- TypeF(x1, y1);
  IsClass(x1) :- SubClassF(x1, y1);
  IsClass(y1) :- SubClassF(x1, y1);
  IsClass(y1) :- Dom(x1, y1);
  IsClass(y1) :- Range(x1, y1);
]
def compiledRaw_pf : RawCmd ProgramNames Data := mapCmd toRawInput prog_pf.toWhielCmd.toRaw
/- The compiled sides are the compiler's output and the sequence is the input command. -/
theorem inputCmd_eq : seqAfter compiledRaw_pm compiledRaw_pf = inputCmd.toRaw := by
  decide +kernel
end Whiel.Benchmark.Example5021.Fidelity
