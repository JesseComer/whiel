import Lean
import Lean.Replay

/-
  Cold-data audit for the independent direct Lean baseline.
  Never import or execute the candidate module. Replay its
  declarations into a fresh, trusted Task environment,
  then kernel-check the answer at the independently fixed
  goal. Recompute axiom dependencies without trusting any
  candidate environment extension or printed messages.
-/

open Lean

namespace Whiel.DirectLean

def auditAxioms (env : Kernel.Environment) (nativeNames : Array Name) : IO (Array String) := do
  let mut pending := `DirectLeanTask.answer :: nativeNames.toList
  let mut seen : NameSet := {}
  let mut axioms : Array String := #[]
  for _ in [:1000000] do
    match pending with
    | [] => return axioms
    | name :: rest =>
      pending := rest
      if seen.contains name then continue
      seen := seen.insert name
      let some ci := env.find? name
        | throw <| IO.userError s!"missing constant: {name}"
      if ci.isUnsafe || ci.isPartial then
        throw <| IO.userError "unsafe proof dependency"
      if let .axiomInfo _ := ci then
        unless #[`propext, `Classical.choice,
            `Quot.sound].contains name || nativeNames.contains name do
          throw <| IO.userError s!"forbidden axiom: {name}"
        axioms := axioms.push name.toString
      pending := ci.type.getUsedConstants.toList ++ pending
      if let some value := ci.value? (allowOpaque := true) then
        pending := value.getUsedConstants.toList ++ pending
  throw <| IO.userError "axiom audit limit"

/- Recognize the shape, then independently recompute: the name alone is never
   evidence. No candidate compiler attributes, code or initializers are loaded. -/
def nativeAssertion (info : AxiomVal) : IO Expr := do
  unless (info.name.toString.splitOn ".").contains "_native" do
    throw <| IO.userError s!"unproved custom axiom: {info.name}"
  let args := info.type.getAppArgs
  unless info.type.getAppFn.isConstOf ``Eq && args.size == 3 &&
      args[0]! == mkConst ``Bool && args[2]! == mkConst ``Bool.true do
    throw <| IO.userError s!"invalid native assertion: {info.name}"
  return args[1]!

/- Re-add the kernel-checked dependency closure through Core.addDecl so Lean's
   compiler can realize code in a fresh environment. No candidate extensions or
   cached native code are transferred. Noncomputable proof-only definitions need
   no code; actual use of one in computation fails closed. -/
partial def compileDependency (constants : Std.HashMap Name ConstantInfo)
    (name : Name) : StateT NameSet CoreM Unit := do
  if (← get).contains name then return
  modify (·.insert name)
  let some ci := constants[name]? | return
  match ci with
  | .ctorInfo info => compileDependency constants info.induct
  | .recInfo info =>
    for n in info.all do compileDependency constants n
  | .inductInfo info =>
    for n in info.all do modify (·.insert n)
    let mut types := []
    for n in info.all do
      let ind := constants[n]!.inductiveVal!
      for dep in ind.type.getUsedConstants do compileDependency constants dep
      let mut ctors := []
      for ctor in ind.ctors do
        let ctorInfo := constants[ctor]!
        for dep in ctorInfo.type.getUsedConstants do compileDependency constants dep
        ctors := ctors ++ [{ name := ctor, type := ctorInfo.type }]
      types := types ++ [{ name := n, type := ind.type, ctors }]
    addDecl (.inductDecl info.levelParams info.numParams types false)
  | _ =>
    for dep in ci.getUsedConstantsAsSet do compileDependency constants dep
    match ci with
    | .defnInfo info =>
      addDecl (.defnDecl info)
      compileDecls #[name] (logErrors := false)
    | .opaqueInfo info =>
      addDecl (.opaqueDecl info)
      compileDecls #[name] (logErrors := false)
    | .thmInfo info => addDecl (.thmDecl info)
    | .axiomInfo info => addDecl (.axiomDecl info)
    | _ => throwError "unsupported native dependency: {name}"

/- The compiler requires metadata for some generated matchers. When that
   metadata is absent in cold replay, kernel reduction can establish the exact
   Boolean assertion instead. This adds no axiom and never accepts a name alone. -/
def kernelCheckNative (env : Kernel.Environment) (info : ConstantInfo) : IO Unit := do
  let decl := Declaration.thmDecl {
    name := info.name ++ `_audit_kernel_recheck
    levelParams := info.levelParams
    type := info.type
    value := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true) }
  match env.addDeclCore 0 decl none with
  | .error err => throw <| IO.userError (← err.toMessageData {} |>.toString)
  | .ok _ => pure ()

def recheckNative (env : Environment) (checked : Kernel.Environment)
    (constants : Std.HashMap Name ConstantInfo)
    (assertions : Array (Name × Expr)) : IO (Array String) := do
  if assertions.isEmpty then return #[]
  let action : MetaM (Array String) := do
    withOptions (Elab.async.set · false) do
    withOptions (Compiler.compiler.postponeCompile.set · false) do
    withOptions (Compiler.compiler.relaxedMetaCheck.set · true) do
      let compile : StateT NameSet CoreM Unit := do
        for (_, e) in assertions do
          for name in e.getUsedConstants do
            compileDependency constants name
      discard <| compile.run {}
      let mut kernelRechecked := #[]
      for (name, e) in assertions do
        try
          match ← Meta.nativeEqTrue `audit e with
          | .success _ => pure ()
          | .notTrue => throwError "native assertion evaluated to false: {name}"
        catch ex =>
          try
            kernelCheckNative checked constants[name]!
          catch err =>
            throwError "native recheck failed for {name}: {ex.toMessageData}; kernel fallback failed: {err.toMessageData}"
          kernelRechecked := kernelRechecked.push name.toString
      return kernelRechecked
  let ctx : Core.Context := {
    fileName := "<native-audit>"
    fileMap := default
    options := maxHeartbeats.set {} 0 }
  let (names, _) ← action.run' |>.toIO ctx { env }
  return names

end Whiel.DirectLean

unsafe def main (args : List String) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  let [candidate, verdict] := args
    | throw <| IO.userError "expected candidate and verdict"
  unless verdict == "valid" || verdict == "invalid" do
    throw <| IO.userError "invalid verdict"
  -- Only the operator-owned Task and generic libraries may initialize extensions.
  enableInitializersExecution
  let env ← importModules #[{ module := `Task }] {} 0 (loadExts := true)
  let parts ← readModuleDataParts #[candidate]
  let some (data, _) := parts[0]?
    | throw <| IO.userError "expected one candidate module"
  for imp in data.imports do
    unless (env.getModuleIdx? imp.module).isSome do
      throw <| IO.userError "candidate import not allowed"
  let mut constants : Std.HashMap Name ConstantInfo := {}
  let mut native : Array (Name × Expr) := #[]
  for name in data.constNames, ci in data.constants do
    if name != ci.name || (env.find? name).isSome ||
        constants.contains name then
      throw <| IO.userError "duplicate or replaced constant"
    match ci with
    | .axiomInfo info => native := native.push (name, ← Whiel.DirectLean.nativeAssertion info)
    | .quotInfo _ => throw <| IO.userError "candidate quotient declaration"
    | _ => pure ()
    constants := constants.insert name ci
  /- Lean generates partial runtime helpers for ordinary
     terminating recursion. Replay skips these helpers;
     any actual proof dependency must still kernel-check.
     auditAxioms also checks the answer and native claims. -/
  let checked ← env.replay constants
  let checked := checked.toKernelEnv
  let some (.thmInfo answer) := checked.find?
      `DirectLeanTask.answer
    | throw <| IO.userError s!"answer theorem missing; candidate names: {data.constNames}"
  unless answer.levelParams.isEmpty do
    throw <| IO.userError "answer must be closed"
  let goal := mkConst `DirectLeanTask.goal
  let goal := if verdict == "valid" then goal
    else mkApp (mkConst ``Not) goal
  let decl := Declaration.thmDecl {
    name := `DirectLeanAudit.checked
    levelParams := [], type := goal,
    value := mkConst `DirectLeanTask.answer }
  match checked.addDeclCore 0 decl none with
  | .error err =>
    throw <| IO.userError (← err.toMessageData {} |>.toString)
  | .ok _ => pure ()
  let nativeNames := native.map Prod.fst
  let axioms ← Whiel.DirectLean.auditAxioms checked nativeNames
  let kernelRechecked ← Whiel.DirectLean.recheckNative env checked constants native
  IO.println <| Json.mkObj [
    ("schema_version", toJson (1 : Nat)),
    ("proof_checked", toJson true),
    ("verdict", toJson verdict),
    ("axioms", toJson axioms),
    ("native_rechecked", toJson (nativeNames.map Name.toString)),
    ("native_kernel_rechecked", toJson kernelRechecked)] |>.compress
  return 0
