-- Author: Jesse Comer
import Whiel.Vampire.StructuralBridge
import Whiel.Vampire.TPTP
import Databases.FOL.ShallowSemantics

/-
  Exact binding of a raw leancheck theorem to one Lean-owned
  shallow model.

  The binder reads only the already constructed `NameEnv`.
  It does not inspect TPTP or Vampire's proof. Before applying
  `fullProof`, it checks the declaration's implicit telescope
  against every solver name and the corresponding shallow
  interpretation. The resulting proposition is handed to
  `structural_exact_eq_symm`, whose kernel-checked conversions
  are limited to the connective association accepted there
  together with the orientation of an atomic equality.
-/

------------------------------------------------------------
-- Exact Semantic Telescope Binding
------------------------------------------------------------

namespace Whiel
namespace Vampire
namespace ExactReconstruction

open Lean Meta Elab Term

private structure SemanticBinding where
  binderName : Name
  solverName : String
  kind : String
  source : Expr
  value : Expr
deriving Inhabited

private def whnfAll (e : Expr) : MetaM Expr :=
  withTransparency .all <| whnf e

private partial def listValues
    (value : Expr) : MetaM (Array Expr) := do
  let value ← whnfAll value
  let fn := value.getAppFn
  let args := value.getAppArgs
  if fn.isConstOf ``List.nil && args.size == 1 then
    return #[]
  else if fn.isConstOf ``List.cons && args.size == 3 then
    let tail ← listValues args[2]!
    return #[args[1]!] ++ tail
  else
    throwError
      "exact_reconstruction requires a NameEnv whose lists reduce to concrete values"

private def pairValue
    (value : Expr) : MetaM (Expr × Expr) := do
  let value ← whnfAll value
  let fn := value.getAppFn
  let args := value.getAppArgs
  unless fn.isConstOf ``Prod.mk && args.size == 4 do
    throwError
      "exact_reconstruction encountered a malformed NameEnv entry"
  return (args[2]!, args[3]!)

/-
  Evaluate one exact NameEnv spelling. This native
  metaprogramming step produces no proof: the string only
  selects a telescope argument, whose completed term is
  still checked against the target by Lean's kernel.
-/
private unsafe def solverName
    (name : Expr) : MetaM String := do
  let nameType ← inferType name
  try
    return ← Meta.evalExpr String nameType name
  catch _ =>
    throwError
      "exact_reconstruction requires closed, evaluable NameEnv spellings"

private def nameEnvParameters
    (env : Expr) : MetaM (Expr × Expr) := do
  let type ← whnfAll (← inferType env)
  let fn := type.getAppFn
  let args := type.getAppArgs
  unless
      fn.isConstOf ``Whiel.Vampire.TPTP.NameEnv &&
        args.size == 4 do
    throwError
      "exact_reconstruction expected a Vampire.TPTP.NameEnv"
  return (args[0]!, args[1]!)

private def modelParameters
    (model : Expr) : MetaM (Expr × Expr × Expr × Expr) := do
  let type ← whnfAll (← inferType model)
  let fn := type.getAppFn
  let args := type.getAppArgs
  unless
      fn.isConstOf ``FOL.Shallow.Model && args.size == 6 do
    throwError
      "exact_reconstruction expected an FOL.Shallow.Model"
  return (args[0]!, args[1]!, args[4]!, args[5]!)

private def membershipProof
    (collection value : Expr)
    (description : String) : MetaM Expr := do
  let proposition ←
    mkAppM ``Membership.mem #[collection, value]
  try
    let proof ← mkDecideProof proposition
    let proofType ← inferType proof
    unless ← isDefEq proofType proposition do
      throwError "membership decision did not close"
    return proof
  catch _ =>
    throwError
      m!"exact_reconstruction {description} is absent from the shallow-model signature"

private def relationValue
    (signature model relation : Expr) : MetaM Expr := do
  let schema ←
    mkAppM ``Signature.toUnnamedSchema #[signature]
  let symbols ← mkAppM ``UnnamedSchema.syms #[schema]
  let membership ← membershipProof symbols relation "relation"
  let symbol ←
    mkAppM ``UnnamedSchema.sym
      #[schema, relation, membership]
  mkAppM ``FOL.Shallow.Model.rels #[model, symbol]

private def functionValue
    (signature model function : Expr) : MetaM Expr := do
  let functions ← mkAppM ``Signature.funs #[signature]
  let membership ←
    membershipProof functions function "function"
  let symbol ←
    mkAppM ``Signature.func
      #[signature, function, membership]
  mkAppM ``FOL.Shallow.Model.funcs #[model, symbol]

private def semanticBinderName
    (solverName : String) : Name :=
  Name.mkSimple ("_" ++ solverName)

private def appendBinding
    (bindings : Array SemanticBinding)
    (usedNames : Array String)
    (solverName kind : String)
    (source value : Expr) : MetaM
      (Array SemanticBinding × Array String) := do
  if usedNames.contains solverName then
    throwError
      m!"exact_reconstruction has a colliding solver name `{solverName}`"
  else
    pure ()
  for binding in bindings do
    if binding.kind == kind &&
        (binding.source == source ||
          (← isDefEq binding.source source)) then
      throwError
        m!"exact_reconstruction repeats a {kind} source under \
          solver names `{binding.solverName}` and `{solverName}`"
  let binding : SemanticBinding :=
    { binderName := semanticBinderName solverName
      solverName
      kind
      source
      value }
  return (bindings.push binding, usedNames.push solverName)

private unsafe def semanticBindings
    (env signature model : Expr) : MetaM
      (Array SemanticBinding) := do
  let relationEntriesExpr ←
    mkAppM ``Whiel.Vampire.TPTP.NameEnv.relNames #[env]
  let functionEntriesExpr ←
    mkAppM ``Whiel.Vampire.TPTP.NameEnv.funNames #[env]
  let relationEntries ← listValues relationEntriesExpr
  let functionEntries ← listValues functionEntriesExpr
  let mut bindings := #[]
  let mut usedNames := #[]
  for index in [:relationEntries.size] do
    let (relation, nameExpr) ←
      pairValue relationEntries[index]!
    let solverName ← solverName nameExpr
    let value ← relationValue signature model relation
    let next ←
      appendBinding bindings usedNames solverName
        "relation" relation value
    bindings := next.1
    usedNames := next.2
  for index in [:functionEntries.size] do
    let (function, nameExpr) ←
      pairValue functionEntries[index]!
    let solverName ← solverName nameExpr
    let value ← functionValue signature model function
    let next ←
      appendBinding bindings usedNames solverName
        "function" function value
    bindings := next.1
    usedNames := next.2
  return bindings

private def residualImplicitBinder?
    (type : Expr) : Option Name :=
  (type.find? fun expression =>
    match expression with
    | .forallE _ _ _ info =>
        info != .default
    | _ => false).map fun expression =>
      expression.bindingName!

private def exactBindingIndex?
    (bindings : Array SemanticBinding)
    (name : Name) : Option Nat :=
  bindings.findIdx? fun binding =>
    binding.binderName == name

private def applyExactTelescope
    (declaration : Name)
    (bindings : Array SemanticBinding)
    (carrier : Expr) : MetaM Expr := do
  let information ← getConstInfo declaration
  let levels ←
    information.levelParams.mapM fun _ => mkFreshLevelMVar
  let mut proof := Lean.mkConst declaration levels
  let mut type :=
    information.instantiateTypeLevelParams levels
  let carrierType ← inferType carrier
  let inhabitedType ← mkAppM ``Inhabited #[carrier]
  let mut used := Array.replicate bindings.size false
  let mut sawCarrier := false
  let mut sawInhabited := false
  let mut scanning := true
  while scanning do
    type ← whnfAll type
    match type with
    | .forallE name domain body info =>
        if info == .default then
          scanning := false
        else
          let argument ←
            match exactBindingIndex? bindings name with
            | some index =>
                unless info == .implicit do
                  throwError
                    m!"exact_reconstruction semantic binder `{name}` is not implicit"
                if used[index]! then
                  throwError
                    m!"exact_reconstruction repeats semantic binder `{name}`"
                let binding := bindings[index]!
                let valueType ← inferType binding.value
                unless ← isDefEq domain valueType do
                  throwError
                    m!"exact_reconstruction {binding.kind} binder \
                      `{name}` has the wrong arity or type"
                used := used.set! index true
                pure binding.value
            | none =>
                if info == .implicit && !sawCarrier &&
                    (← isDefEq domain carrierType) then
                  sawCarrier := true
                  pure carrier
                else if info == .instImplicit &&
                    !sawInhabited &&
                    (← isDefEq domain inhabitedType) then
                  sawInhabited := true
                  synthInstance inhabitedType
                else
                  throwError
                    m!"exact_reconstruction found unexpected telescope binder `{name}`"
          proof := mkApp proof argument
          type := body.instantiate1 argument
    | _ => scanning := false
  for index in [:bindings.size] do
    unless used[index]! do
      let binding := bindings[index]!
      throwError
        m!"exact_reconstruction is missing {binding.kind} binder \
          `{binding.binderName}` for solver name `{binding.solverName}`"
  type ← instantiateMVars type
  proof ← instantiateMVars proof
  if let some name := residualImplicitBinder? type then
    throwError
      m!"exact_reconstruction left residual implicit binder `{name}`"
  unless ← isProp type do
    throwError
      "exact_reconstruction fullProof conclusion is not a proposition"
  if type.hasExprMVar || type.hasLevelMVar ||
      proof.hasExprMVar || proof.hasLevelMVar then
    throwError
      "exact_reconstruction left unresolved telescope metavariables"
  return proof

/-
  Exact telescope application of `declaration` for one
  elaborated literal `NameEnv` and one shallow model. This
  is the whole binder: it validates the carriers, reads the
  environment, and applies the telescope. The proposition it
  returns is still bridged and kernel-checked by the caller.
-/
unsafe def exactProof
    (declaration : Name)
    (env model : Expr) : MetaM Expr := do
  let (envRelations, envFunctions) ←
    nameEnvParameters env
  let (modelRelations, modelFunctions,
      signature, carrier) ← modelParameters model
  unless ← isDefEq envRelations modelRelations do
    throwError
      "exact_reconstruction NameEnv relation carrier disagrees with the shallow model"
  unless ← isDefEq envFunctions modelFunctions do
    throwError
      "exact_reconstruction NameEnv function carrier disagrees with the shallow model"
  let bindings ← semanticBindings env signature model
  applyExactTelescope declaration bindings carrier

syntax (name := exactReconstructionTerm)
  "exact_reconstruction_term" ident "using" "(" term "," term ")" : term

@[term_elab exactReconstructionTerm]
unsafe def elabExactReconstruction : TermElab :=
  fun stx _expectedType => do
    match stx with
    | `(exact_reconstruction_term $proofName:ident using
          ($envTerm:term, $modelTerm:term)) =>
      let declaration ← resolveGlobalConstNoOverload proofName
      let env ← Term.elabTerm envTerm none
      let model ← Term.elabTerm modelTerm none
      Term.synthesizeSyntheticMVarsNoPostponing
      let env ← instantiateMVars env
      let model ← instantiateMVars model
      withRef envTerm <| exactProof declaration env model
    | _ => throwUnsupportedSyntax

syntax (name := exactReconstruction)
  "exact_reconstruction" ident "using" "(" term "," term ")" : tactic

macro_rules
  | `(tactic| exact_reconstruction $proofName:ident using
        ($envTerm:term, $modelTerm:term)) =>
      `(tactic|
        structural_exact_eq_symm
          (exact_reconstruction_term $proofName using
            ($envTerm, $modelTerm)))

end ExactReconstruction
end Vampire
end Whiel
