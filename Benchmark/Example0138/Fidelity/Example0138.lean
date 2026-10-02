-- Author: Leo Zhang
import Benchmark.Example0138.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

namespace Whiel.Benchmark.Example0138.Fidelity
open Whiel Whiel.Concrete Whiel.Synthesis.Tests.BenchmarkFidelity
open Whiel.Benchmark.Example0138 (inputSchema inputPre inputCmd inputPost)
/- The two Datalog programs; the command is their naive compilations one after the other. -/
def E : ProgramNames := .programSymbol ⟨"E", by decide⟩ 0
def TX : ProgramNames := .programSymbol ⟨"TX", by decide⟩ 0
def TaY : ProgramNames := .programSymbol ⟨"TaY", by decide⟩ 0
def TbY : ProgramNames := .programSymbol ⟨"TbY", by decide⟩ 0
def TcY : ProgramNames := .programSymbol ⟨"TcY", by decide⟩ 0
/- Transitive closure, non-linearly. -/
def schemaX : UnnamedSchema ProgramNames := programSch![ {E, TX} (arity: 2) ]
def programX : Datalog.Program Data schemaX := datalog![
  TX(x1, y1) :- E(x1, y1);
  TX(x1, y1) :- TX(x1, z1), TX(z1, y1);
]
def rawX : RawCmd ProgramNames Data := mapCmd toRawInput programX.toWhielCmd.toRaw
/- Odd and even paths and their union, non-linearly. -/
def schemaY : UnnamedSchema ProgramNames := programSch![ {E, TaY, TbY, TcY} (arity: 2) ]
def programY : Datalog.Program Data schemaY := datalog![
  TaY(x1, y1) :- E(x1, z1), E(z1, y1);
  TaY(x1, y1) :- TaY(x1, z1), TaY(z1, y1);
  TaY(x1, y1) :- TbY(x1, z1), TbY(z1, y1);
  TbY(x1, y1) :- E(x1, y1);
  TbY(x1, y1) :- TbY(x1, z1), TaY(z1, y1);
  TbY(x1, y1) :- TaY(x1, z1), TbY(z1, y1);
  TcY(x1, y1) :- TaY(x1, y1);
  TcY(x1, y1) :- TbY(x1, y1);
]
def rawY : RawCmd ProgramNames Data := mapCmd toRawInput programY.toWhielCmd.toRaw
def compiledRaw : RawCmd ProgramNames Data := seqAfter rawX rawY
theorem inputPre_eq : inputPre.formula.toRaw = .«true» := by
  decide
theorem compiledRaw_eq : compiledRaw = inputCmd.toRaw := by
  decide +kernel
theorem inputCmd_eq : compiledRaw.toCmd? inputSchema = some inputCmd :=
  toCmd?_eq compiledRaw_eq
end Whiel.Benchmark.Example0138.Fidelity
