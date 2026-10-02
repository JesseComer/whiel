import Lean

/-
  Independent direct-proof task exporter. Only the four
  original input declarations are rendered. Parsed source
  trivia, preprocessing and metadata are never exported.
  B checks each rendered definition against the original
  compiled input by a kernel-checked reflexivity proof in
  a separate process to bound import/elaboration memory.
  This executable is not imported by the search worker.
-/

open Lean

namespace Whiel.DirectLean

def fields : Array String :=
  #["inputSchema", "inputPre", "inputCmd", "inputPost"]

def imports : String :=
  "import Whiel.Concrete.Notation\n" ++
  "import Whiel.Hoare.Concrete\n"

def taskPrefix : String :=
  "namespace DirectLeanTask\nopen Whiel Whiel.Concrete\n"

def suffix : String :=
  "def goal : Prop :=\n" ++
  "  Whiel.HoareValid inputPre inputCmd inputPost\n" ++
  "end DirectLeanTask\n"

def failMessages (msgs : MessageLog) : IO Unit := do
  if msgs.hasErrors then
    for msg in msgs.toList do
      IO.eprintln (← msg.toString)
    throw <| IO.userError "task elaboration failed"

/- The same case-independent API reference for every model. -/
def reference (env : Environment) : IO String := do
  let mut env := env
  let names := #[`Whiel.Concrete.Data,
    `Whiel.Concrete.ProgramNames, `UnnamedSchema,
    `Domain, `Tuple, `FinRelation, `RAExpr, `RAExpr.eval,
    `Instance, `Instance.empty, `Instance.update,
    `Whiel.Cmd, `Whiel.Cmd.BigStep, `Whiel.Guard,
    `Whiel.Guard.eval, `Whiel.QFAssertExpr,
    `Whiel.AssertExpr, `Whiel.AssertExpr.ofQF,
    `Whiel.AssertExpr.eval, `Whiel.HoareValid,
    `Whiel.AssertExpr.instToAssertion,
    `Whiel.Hoare.assign, `Whiel.Hoare.seq,
    `Whiel.Hoare.ite,
    `Whiel.Cmd.BigStep.while_invariant,
    `Whiel.Cmd.BigStep.while_final_not_guard]
  let mut todo := names.toList
  let mut output := ""
  for _ in [:1000] do
    match todo with
    | [] => return output
    | name :: rest =>
      todo := rest
      let some ci := env.find? name
        | throw <| IO.userError s!"reference missing {name}"
      let (ty, _, _) ← (Meta.ppExpr ci.type).toIO
        { fileName := "<reference>", fileMap := default,
          options := ({} : Options).setBool `pp.fullNames true }
        { env }
      output := output ++ s!"{name} : {ty.pretty}\n"
      if let .inductInfo info := ci then
        todo := info.ctors ++ todo
      if let .defnInfo info := ci then
        let (value, _, _) ← (Meta.ppExpr info.value).toIO
          { fileName := "<reference>", fileMap := default,
            options := ({} : Options).setBool `pp.fullNames true }
          { env }
        output := output ++ s!"  := {value.pretty}\n"
        if #[`Whiel.Guard.eval, `RAExpr.eval].contains name then
          let (eqns, state, _) ← (Meta.getEqnsFor? name).toIO
            { fileName := "<reference>", fileMap := default }
            { env }
          env := state.env
          todo := (eqns.getD #[]).toList ++ todo
      output := output ++ "\n"
  throw <| IO.userError "reference limit"

def render (env : Environment) (path : System.FilePath) :
    IO String := do
  let parsed ← Parser.testParseFile env path
  let mut defs : Array String := #[]
  for cmd in parsed[1].getArgs do
    if let `(command| def $id:ident : $ty := $body) := cmd then
      if fields.contains id.getId.toString then
        unless fields[defs.size]? == some id.getId.toString do
          throw <| IO.userError "unexpected input order"
        let clean : Syntax.Command := ⟨cmd.rewriteBottomUp
          (·.setInfo .none)⟩
        let (fmt, _) ← (PrettyPrinter.ppCommand clean).toIO
          { fileName := "<task>", fileMap := default }
          { env }
        defs := defs.push fmt.pretty
  unless defs.size == fields.size do
    throw <| IO.userError "expected four input definitions"
  return taskPrefix ++ String.intercalate "\n\n" defs.toList ++
    "\n" ++ suffix

end Whiel.DirectLean

/- Dynamic imports follow Lean's standalone checker pattern. -/
unsafe def main (args : List String) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let out :: paths := args
    | throw <| IO.userError "expected output directory, inputs"
  let out : System.FilePath := out
  IO.FS.createDirAll out
  let env ← importModules
    #[{ module := `Whiel.Concrete.Notation },
      { module := `Whiel.Hoare.Concrete }] {}
    (loadExts := true)
  if paths.isEmpty then
    let mut modules : Array Json := #[]
    for name in env.header.moduleNames do
      modules := modules.push <| Json.mkObj
        [("module", toJson name.toString),
         ("olean", toJson (← findOLean name).toString)]
    IO.FS.writeFile (out / "libraries.json")
      (toJson modules |>.pretty)
    IO.FS.writeFile (out / "reference.txt")
      (← Whiel.DirectLean.reference env)
  for path in paths do
    let path : System.FilePath := path
    let some parent := path.parent
      | throw <| IO.userError "input has no parent"
    let some id := parent.fileName
      | throw <| IO.userError "input has no case name"
    unless id.startsWith "Example" &&
        (id.drop 7).toString.length == 4 &&
        (id.drop 7).toString.toList.all Char.isDigit do
      throw <| IO.userError "expected ExampleNNNN/Input.lean"
    let source ← Whiel.DirectLean.render env path
    let dir := out / id
    IO.FS.createDirAll dir
    IO.FS.writeFile (dir / "Task.lean")
      (Whiel.DirectLean.imports ++ source)
    IO.println s!"exported {id}"
  return 0
