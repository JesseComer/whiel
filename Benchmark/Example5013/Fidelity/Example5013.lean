-- Author: Leo Zhang
import Benchmark.Example5013.Input
import Whiel.DatalogCompiler.Naive
import Benchmark.Fidelity.Support

namespace Whiel.Benchmark.Example5013.Fidelity
open Whiel Whiel.Concrete Whiel.Synthesis.Tests.BenchmarkFidelity
open Whiel.Benchmark.Example5013 (inputSchema inputCmd)
def UserRole : ProgramNames := .programSymbol ⟨"UserRole", by decide⟩ 0
def RoleInh : ProgramNames := .programSymbol ⟨"RoleInh", by decide⟩ 0
def Has : ProgramNames := .programSymbol ⟨"Has", by decide⟩ 0
def schema_p : UnnamedSchema ProgramNames := programSch![ {UserRole, RoleInh, Has} (arity: 2) ]
def prog_p : Datalog.Program Data schema_p := datalog![
  Has(x1, y1) :- UserRole(x1, y1);
  Has(x1, z1) :- Has(x1, y1), RoleInh(y1, z1);
]
def compiledRaw_p : RawCmd ProgramNames Data := mapCmd toRawInput prog_p.toWhielCmd.toRaw
def handCmd : Cmd Data inputSchema :=
  programCmd![
    { ExecSchema: inputSchema }
    {
      StepA := UserRole;
      StepB := (StepA ∪ (π[0, 3] (σ[#1 = #2] (StepA × RoleInh))));
      StepC := (StepB ∪ (π[0, 3] (σ[#1 = #2] (StepB × RoleInh))));
      StepD := (StepC ∪ (π[0, 3] (σ[#1 = #2] (StepC × RoleInh))));
      StepE := (StepD ∪ (π[0, 3] (σ[#1 = #2] (StepD × RoleInh))));
      StepF := (StepE ∪ (π[0, 3] (σ[#1 = #2] (StepE × RoleInh))));
      StepG := (StepF ∪ (π[0, 3] (σ[#1 = #2] (StepF × RoleInh))));
      StepH := (StepG ∪ (π[0, 3] (σ[#1 = #2] (StepG × RoleInh))));
      StepI := (StepH ∪ (π[0, 3] (σ[#1 = #2] (StepH × RoleInh))));
      StepJ := (StepI ∪ (π[0, 3] (σ[#1 = #2] (StepI × RoleInh))));
      StepK := (StepJ ∪ (π[0, 3] (σ[#1 = #2] (StepJ × RoleInh))));
      HasB := StepK
    }
  ]
def handRaw : RawCmd ProgramNames Data := handCmd.toRaw
theorem inputCmd_eq : seqAfter handRaw compiledRaw_p = inputCmd.toRaw := by
  decide +kernel
end Whiel.Benchmark.Example5013.Fidelity
