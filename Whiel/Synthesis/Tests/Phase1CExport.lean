-- Author: Jesse Comer
import Benchmark2.Example0012.Input
import Whiel.Synthesis.Runtime.Task

/-
  Live Lean-to-Rust task-boundary fixture for Phase 1C.
  The Rust integration test runs this file and validates its
  output without parsing `Input.lean` source text.
-/

------------------------------------------------------------
-- Canonical Task Export
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace Tests
namespace Phase1CExport

open Benchmark.Example0012

def identity : Runtime.TaskIdentity where
  canonicalId := "Example0012"
  moduleName := "Benchmark.Example0012.Input"
  namespaceName := "Whiel.Benchmark.Example0012"
  sourceSha256 :=
    "6fe56e9493eefa68d69085d1602adda3" ++
      "a0d522d964f1a8bf6ef3996f08cd3195"

def exportJson : Runtime.BoundTaskManifest :=
  taskJson%
    identity,
    Whiel.Benchmark.Example0012.programSchema,
    Whiel.Benchmark.Example0012.inputPre,
    Whiel.Benchmark.Example0012.inputCmd,
    Whiel.Benchmark.Example0012.inputPost,
    Whiel.Benchmark.Example0012.inputPreproc

def mismatchedIdentity : Runtime.TaskIdentity where
  canonicalId := "Example0012-mismatched"
  moduleName := "Benchmark.Example0012.Input"
  namespaceName := "Whiel.Benchmark.NotExample0012"
  sourceSha256 := identity.sourceSha256

def mismatchedIdentityJson : Runtime.BoundTaskManifest :=
  taskJson%
    mismatchedIdentity,
    Whiel.Benchmark.Example0012.programSchema,
    Whiel.Benchmark.Example0012.inputPre,
    Whiel.Benchmark.Example0012.inputCmd,
    Whiel.Benchmark.Example0012.inputPost,
    Whiel.Benchmark.Example0012.inputPreproc

def checkExport : IO Unit := do
  let text := Lean.Json.compress exportJson.toJson
  unless text.contains
      "Whiel.Benchmark.Example0012.inputPreproc.loopCmd" do
    throw
      (IO.userError "missing normalized command binding")
  unless text.contains "\"preprocessing_evidence\"" do
    throw (IO.userError "missing preprocessing evidence")

end Phase1CExport
end Tests
end Synthesis
end Whiel

------------------------------------------------------------
-- Test Entrypoint
------------------------------------------------------------

open Whiel.Benchmark.Example0012
open Whiel.Synthesis.Tests.Phase1CExport

def main (args : List String) : IO UInt32 := do
  match args with
  | [output] =>
      checkExport
      Whiel.Synthesis.Runtime.writeTaskManifest
        (System.FilePath.mk output)
        exportJson
      pure 0
  | [output, "--mismatched-identity"] =>
      Whiel.Synthesis.Runtime.writeTaskManifest
        (System.FilePath.mk output)
        mismatchedIdentityJson
      pure 0
  | _ =>
      IO.eprintln "usage: Phase1CExport.lean OUTPUT"
      pure 2
