-- Author: Jesse Comer
import Whiel.Vampire.Job

/-
  Write the JSON file read by the Rust Vampire runner.

  Key definitions:
    * `Whiel.Vampire.manifestJson`
    * `Whiel.Vampire.writeManifest`
    * `Whiel.Vampire.writeEmptyCounterexampleChecks`

  A manifest records the artifact directory and the list of
  `Job`s to run. Lean writes one manifest per Vampire run.
-/

------------------------------------------------------------
-- Manifest JSON
------------------------------------------------------------

namespace Whiel

namespace Vampire

/- Runtime empty-counterexample result for one logical job. -/
structure EmptyCounterexampleCheck where
  id : String
  hasEmptyCounterexample : Bool

namespace EmptyCounterexampleCheck

/- JSON object consumed by the synthesis oracle. -/
def toJson (check : EmptyCounterexampleCheck) : Lean.Json :=
  Lean.Json.mkObj
    [ ("id", Lean.Json.str check.id),
      ( "has_empty_counterexample",
        Lean.Json.bool check.hasEmptyCounterexample) ]

end EmptyCounterexampleCheck

/- Versioned runtime-check artifact consumed by Python. -/
def emptyCounterexampleChecksJson
    (checks : List EmptyCounterexampleCheck) : Lean.Json :=
  Lean.Json.mkObj
    [ ("format_version", Lean.Json.num 1),
      ( "checks",
        Lean.Json.arr
          ((checks.map EmptyCounterexampleCheck.toJson).toArray)) ]

/- JSON object written to `manifest.json`. -/
def manifestJson
    (artifactDir : String)
    (jobs : List Job) :
    Lean.Json :=
  Lean.Json.mkObj
    [ ("manifest_version", Lean.Json.num 2),
      ("artifact_dir", Lean.Json.str artifactDir),
      ( "jobs",
        Lean.Json.arr ((jobs.map Job.toJson).toArray)) ]

end Vampire
end Whiel

------------------------------------------------------------
-- File Writing
------------------------------------------------------------

namespace Whiel

namespace Vampire

/-
  Write the Lean-to-Rust manifest. The manifest lives in
  `root`; the embedded artifact directory is relative to the
  manifest so the file is portable when promoted or audited.
-/
def writeManifest
    (root : System.FilePath)
    (jobs : List Job) :
    IO Unit := do
  IO.FS.createDirAll root
  IO.FS.writeFile (root / "manifest.json")
    ((Lean.Json.pretty
      (manifestJson "." jobs) 100) ++ "\n")

/-
  Write runtime empty-counterexample checks next to a
  manifest. These checks guide synthesis only; final
  certificates separately prove their no-empty conditions.
-/
def writeEmptyCounterexampleChecks
    (root : System.FilePath)
    (checks : List EmptyCounterexampleCheck) :
    IO Unit := do
  IO.FS.createDirAll root
  IO.FS.writeFile
    (root / "empty_counterexample_checks.json")
    ((Lean.Json.pretty
      (emptyCounterexampleChecksJson checks) 100) ++ "\n")

end Vampire
end Whiel
