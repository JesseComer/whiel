-- Author: Jesse Comer
import Whiel.Concrete.Data
import Whiel.Synthesis.FrameworkII.FixedAmbient.CertificateJobs
import Whiel.Vampire.ExactReconstruction

/-
  The `certify_job` tactic closes the exact shallow target of
  one fixed-ambient certificate job from a raw leancheck
  theorem:

    certify_job <job> <fullProof>

  Elaboration evaluates the job's canonical constant and
  relation supports and its symbol environment, rebuilds
  them as literal terms, decides the two sortedness
  equalities, rewrites the target to the explicit-list
  closed entailment, introduces the shallow model, applies
  the exact telescope binder, and hands the bound
  proposition to the structural bridge. The kernel still
  checks literal lists, a literal environment, and the
  bridged proof term; only the certificate source changes.
  Every evaluation is a selection step, never a proof.
-/

------------------------------------------------------------
-- Evaluated Supports
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FixedAmbient
namespace CertifyJob

open Concrete

variable {D : Type} [Domain D] [LinearOrder D]
variable {Gamma : UnnamedSchema WhielNames}

/- Canonical constant support of one job, as plain values. -/
def constantSupport
    (job : CertificateJob D Gamma) : List D :=
  job.entailment.toRelCalcEntailment.constants.attach.sort.map
    Subtype.val

/- Canonical relation support of one schema, as names. -/
def relationSupport
    (Gamma : UnnamedSchema WhielNames) : List WhielNames :=
  Gamma.syms.attach.sort.map Subtype.val

/- Exact relation spellings of one job's environment. -/
def relationSpellings
    [Vampire.SolverName D]
    (job : CertificateJob D Gamma) :
    List (WhielNames × String) :=
  job.nameEnv.relNames

/- Exact function spellings of one job's environment. -/
def functionSpellings
    [Vampire.SolverName D]
    (job : CertificateJob D Gamma) : List (D × String) :=
  job.nameEnv.funNames

/-
  No certificate job can present a malformed environment. The
  renderer assigns names without freshening, so this is what
  replaces the old guarantee that colliding names were pulled
  apart: relation names are injective clause sources, constant
  names are injective encodings, both are legal identifiers,
  and no relation name is a constant name.
-/
theorem wellFormed_nameEnv
    (job : CertificateJob Data Gamma) :
    job.nameEnv.wellFormed = true :=
  Vampire.TPTP.NameEnv.wellFormed_ofEntailment
    Vampire.solverName_whielNames_ne_solverName_data _

end CertifyJob
end FixedAmbient
end FrameworkII
end Synthesis
end Whiel

------------------------------------------------------------
-- Literal Terms
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FixedAmbient
namespace CertifyJob

open Concrete
open Lean Meta Elab Tactic

private def dataType : Expr :=
  mkConst ``Whiel.Concrete.Data

private def namesType : Expr :=
  mkConst ``WhielNames

private def stringType : Expr :=
  mkConst ``String

private def listOf (type : Expr) : Expr :=
  mkApp (mkConst ``List [Level.zero]) type

private def pairOf (left right : Expr) : Expr :=
  mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) left right

/-
  Decide one closed proposition. The instance is evaluated
  at elaboration time so a false side condition fails with
  a clear message; the kernel re-checks the returned proof.
-/
private def decideProof
    (proposition : Expr)
    (description : String) : MetaM Expr := do
  let proof ← try
      mkDecideProof proposition
    catch _ =>
      throwError
        m!"certify_job cannot decide {description}:{indentExpr proposition}"
  let decision := proof.appFn!.appArg!
  let result ←
    withAtLeastTransparency .default <| whnf decision
  unless result.isAppOf ``Decidable.isTrue do
    throwError
      m!"certify_job found {description} false:{indentExpr proposition}"
  return proof

private def alphaStringLiteral
    (value : String) : MetaM Expr := do
  let constructor :=
    mkApp (mkConst ``AlphaString.mk) (mkStrLit value)
  let type ← whnf (← inferType constructor)
  match type with
  | .forallE _ proposition _ _ =>
      let proof ←
        decideProof proposition
          s!"the alphabetic base {reprStr value}"
      return mkApp constructor proof
  | _ =>
      throwError
        "certify_job expected AlphaString.mk to take its proof"

private def programNameLiteral :
    ProgramNames -> MetaM Expr
| .programSymbol base index =>
    return mkApp2 (mkConst ``ProgramNames.programSymbol)
      (← alphaStringLiteral base.value) (mkNatLit index)
| .auxiliarySymbol base index =>
    return mkApp2 (mkConst ``ProgramNames.auxiliarySymbol)
      (← alphaStringLiteral base.value) (mkNatLit index)
| .flagSymbol id index =>
    return mkApp2 (mkConst ``ProgramNames.flagSymbol)
      (mkNatLit id) (mkNatLit index)

private def relationLiteral : WhielNames -> MetaM Expr
| .ordinary name =>
    return mkApp (mkConst ``WhielNames.ordinary)
      (← programNameLiteral name)
| .prophecy name =>
    return mkApp (mkConst ``WhielNames.prophecy)
      (← programNameLiteral name)

private def dataLiteral : Concrete.Data -> Expr
| .num value => mkApp (mkConst ``Whiel.Concrete.Data.num) (mkNatLit value)
| .str value => mkApp (mkConst ``Whiel.Concrete.Data.str) (mkStrLit value)
| .bool value => mkApp (mkConst ``Whiel.Concrete.Data.bool) (toExpr value)

/-
  Literal support list of subtype members, each carrying a
  decided membership proof, at the exact element type the
  explicit-list theorem expects.
-/
private def memberList
    (elementType : Expr)
    (values : Array Expr)
    (description : String) : MetaM Expr := do
  let subtype ← whnf elementType
  let (carrier, predicate) ←
    match subtype.getAppFnArgs with
    | (``Subtype, #[carrier, predicate]) =>
        pure (carrier, predicate)
    | _ =>
        throwError
          m!"certify_job expected a subtype {description} support:{indentExpr elementType}"
  let mut members := #[]
  for value in values do
    let proposition := (mkApp predicate value).headBeta
    let proof ←
      decideProof proposition s!"{description} membership"
    let member ←
      mkAppOptM ``Subtype.mk
        #[carrier, predicate, value, proof]
    members := members.push member
  mkListLit elementType members.toList

/- Literal exact symbol environment over `WhielNames`. -/
private def nameEnvLiteral
    (relations : List (WhielNames × String))
    (functions : List (Concrete.Data × String)) : MetaM Expr := do
  let relationEntries ← relations.mapM fun pair => do
    mkAppM ``Prod.mk
      #[← relationLiteral pair.1, mkStrLit pair.2]
  let relationList ←
    mkListLit (pairOf namesType stringType) relationEntries
  let functionEntries ← functions.mapM fun pair =>
    mkAppM ``Prod.mk #[dataLiteral pair.1, mkStrLit pair.2]
  let functionList ←
    mkListLit (pairOf dataType stringType) functionEntries
  mkAppOptM ``Vampire.TPTP.NameEnv.mk
    #[namesType, dataType, none, none,
      relationList, functionList]

end CertifyJob
end FixedAmbient
end FrameworkII
end Synthesis
end Whiel

------------------------------------------------------------
-- Sortedness Equalities
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FixedAmbient
namespace CertifyJob

open Lean Meta Elab Tactic

/-
  Instantiate one declaration's telescope with fresh
  metavariables, returning the argument metavariables,
  their binder kinds, and the conclusion.
-/
private def openTelescope
    (declaration : Name) :
    MetaM (List Level × Array Expr × Array BinderInfo × Expr) := do
  let information ← getConstInfo declaration
  let levels ←
    information.levelParams.mapM fun _ => mkFreshLevelMVar
  let (arguments, binders, conclusion) ←
    forallMetaTelescope
      (information.instantiateTypeLevelParams levels)
  return (levels, arguments, binders, conclusion)

/- Synthesize every still-open instance argument. -/
private def synthesizeInstances
    (arguments : Array Expr)
    (binders : Array BinderInfo) : MetaM Unit := do
  for index in [:arguments.size] do
    let argument := arguments[index]!
    if binders[index]! == .instImplicit then
      unless ← argument.mvarId!.isAssigned do
        let type ← instantiateMVars (← inferType argument)
        let decision ← synthInstance type
        unless ← isDefEq argument decision do
          throwError
            m!"certify_job could not assign instance:{indentExpr type}"

/-
  Prove `Finset.sort S r = literal` from the decided finset
  equality `literal.toFinset = S`, the decided `Nodup`, and
  the decided `Pairwise r`, through `List.toFinset_sort`.
-/
private def sortedEquality
    (statement literal : Expr)
    (description : String) : MetaM Expr := do
  let some (_, sorted, _) := statement.eq?
    | throwError
        m!"certify_job expected a sortedness equality:{indentExpr statement}"
  let arguments := sorted.getAppArgs
  unless sorted.isAppOfArity ``Finset.sort 7 do
    throwError
      m!"certify_job expected a canonical sort:{indentExpr sorted}"
  let finset := arguments[1]!
  let relation := arguments[2]!
  let toFinset ← mkAppM ``List.toFinset #[literal]
  let finsetEquality ← mkEq toFinset finset
  let hFinset ←
    decideProof finsetEquality
      s!"the {description} support finset equality"
  let hNodup ←
    decideProof (← mkAppM ``List.Nodup #[literal])
      s!"the {description} support distinctness"
  let pairwise ← mkAppM ``List.Pairwise #[relation, literal]
  let hPairwise ←
    decideProof pairwise s!"the {description} support order"
  let (levels, lemmaArguments, lemmaBinders, iff) ←
    openTelescope ``List.toFinset_sort
  let some (sortedToFinset, lemmaPairwise) := iff.iff?
    | throwError "certify_job expected List.toFinset_sort to be an iff"
  let expectedSorted :=
    mkAppN sorted.getAppFn (arguments.set! 1 toFinset)
  let expectedEquality ← mkEq expectedSorted literal
  unless ← isDefEq sortedToFinset expectedEquality do
    throwError
      m!"certify_job could not align List.toFinset_sort with:{indentExpr expectedEquality}"
  unless ← isDefEq lemmaPairwise pairwise do
    throwError
      m!"certify_job could not align the {description} order side"
  synthesizeInstances lemmaArguments lemmaBinders
  for argument in lemmaArguments do
    unless ← argument.mvarId!.isAssigned do
      let type ← instantiateMVars (← inferType argument)
      unless ← isDefEq type (← inferType hNodup) do
        throwError
          m!"certify_job left an open List.toFinset_sort argument:{indentExpr type}"
      argument.mvarId!.assign hNodup
  let iffProof ← instantiateMVars
    (mkAppN (mkConst ``List.toFinset_sort levels) lemmaArguments)
  let sortedAtToFinset ← mkAppM ``Iff.mpr #[iffProof, hPairwise]
  let motive ←
    withLocalDeclD `support (← inferType finset) fun support => do
      let body ← kabstract statement finset
      mkLambdaFVars #[support] (body.instantiate1 support)
  let transport ← mkCongrArg motive hFinset
  let proof ← mkEqMP transport sortedAtToFinset
  mkExpectedTypeHint proof statement

end CertifyJob
end FixedAmbient
end FrameworkII
end Synthesis
end Whiel

------------------------------------------------------------
-- The Tactic
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FixedAmbient
namespace CertifyJob

open Concrete
open Lean Meta Elab Tactic

private def jobParameters
    (job : Expr) : MetaM (Expr × Expr) := do
  let type ← whnf (← inferType job)
  match type.getAppFnArgs with
  | (``CertificateJob, #[domain, _, schema]) =>
      return (domain, schema)
  | _ =>
      throwError
        m!"certify_job expects a CertificateJob, not:{indentExpr (← inferType job)}"

/-
  Evaluate one closed selection value. Evaluation produces no
  proof: the result only shapes literal terms that the kernel
  checks against the job.
-/
private unsafe def evaluate
    (α : Type) (type value : Expr)
    (description : String) : MetaM α := do
  try
    Meta.evalExpr α type value
  catch error =>
    throwError
      m!"certify_job could not evaluate {description}: {error.toMessageData}"

/-
  Instantiate `closedEntailment_eq_ofLists` at the job and
  the literal supports, proving both sortedness equalities.
  Returns the equality proof and the explicit-list target.
-/
private def listEquality
    (job : Expr)
    (constants : List Concrete.Data)
    (relations : List WhielNames) : MetaM (Expr × Expr) := do
  let (levels, arguments, binders, conclusion) ←
    openTelescope ``CertificateJob.closedEntailment_eq_ofLists
  unless arguments.size == 9 do
    throwError
      "certify_job expected nine closedEntailment_eq_ofLists arguments"
  unless ← isDefEq arguments[4]! job do
    throwError "certify_job could not bind the job"
  synthesizeInstances arguments binders
  let constantsType ← instantiateMVars (← inferType arguments[5]!)
  let constantLiteral ←
    memberList constantsType.appArg!
      (constants.map dataLiteral).toArray "constant"
  unless ← isDefEq arguments[5]! constantLiteral do
    throwError "certify_job could not bind the constant support"
  let relationsType ← instantiateMVars (← inferType arguments[6]!)
  let relationLiteral ←
    memberList relationsType.appArg!
      (← relations.mapM relationLiteral).toArray "relation"
  unless ← isDefEq arguments[6]! relationLiteral do
    throwError "certify_job could not bind the relation support"
  let hConstants ←
    sortedEquality (← instantiateMVars (← inferType arguments[7]!))
      constantLiteral "constant"
  arguments[7]!.mvarId!.assign hConstants
  let hRelations ←
    sortedEquality (← instantiateMVars (← inferType arguments[8]!))
      relationLiteral "relation"
  arguments[8]!.mvarId!.assign hRelations
  let proof ← instantiateMVars
    (mkAppN
      (mkConst ``CertificateJob.closedEntailment_eq_ofLists levels)
      arguments)
  let conclusion ← instantiateMVars conclusion
  let some (_, _, listEntailment) := conclusion.eq?
    | throwError "certify_job expected an entailment equality"
  return (proof, listEntailment)

syntax (name := certifyJob)
  "certify_job " term:max ident : tactic

/-
  Close `job.ShallowTarget` from the named raw leancheck
  theorem. Fails closed on any goal, job, support, spelling,
  or telescope disagreement.
-/
@[tactic certifyJob]
unsafe def evalCertifyJob : Tactic := fun stx => do
  match stx with
  | `(tactic| certify_job $jobTerm:term $proofName:ident) =>
    withMainContext do
      let declaration ←
        resolveGlobalConstNoOverload proofName
      let job ← Term.elabTerm jobTerm none
      Term.synthesizeSyntheticMVarsNoPostponing
      let job ← instantiateMVars job
      if job.hasMVar then
        throwErrorAt jobTerm "certify_job requires a closed job"
      let (domain, schema) ← jobParameters job
      unless ← isDefEq domain dataType do
        throwErrorAt jobTerm
          "certify_job supports jobs over Whiel.Concrete.Data only"
      let goal ← getMainGoal
      let shallowTarget ←
        mkAppM ``CertificateJob.ShallowTarget #[job]
      unless ← isDefEq (← goal.getType) shallowTarget do
        throwError
          m!"certify_job expects the goal{indentExpr shallowTarget}"
      let constants ←
        evaluate (List Concrete.Data) (listOf dataType)
          (← mkAppM ``constantSupport #[job])
          "the constant support"
      let relations ←
        evaluate (List WhielNames) (listOf namesType)
          (← mkAppM ``relationSupport #[schema])
          "the relation support"
      let relationSpellings ←
        evaluate (List (WhielNames × String))
          (listOf (pairOf namesType stringType))
          (← mkAppM ``relationSpellings #[job])
          "the relation spellings"
      let functionSpellings ←
        evaluate (List (Concrete.Data × String))
          (listOf (pairOf dataType stringType))
          (← mkAppM ``functionSpellings #[job])
          "the function spellings"
      let (equality, listEntailment) ←
        listEquality job constants relations
      let listTarget ←
        mkAppM ``FOL.SentenceEntailment.ImplicationShallowValid
          #[listEntailment]
      let motive ←
        withLocalDeclD `entailment (← inferType listEntailment)
          fun entailment => do
            mkLambdaFVars #[entailment]
              (← mkAppM
                ``FOL.SentenceEntailment.ImplicationShallowValid
                #[entailment])
      let listGoal ←
        mkFreshExprSyntheticOpaqueMVar listTarget
      let transport ← mkCongrArg motive equality
      goal.assign (← mkEqMPR transport listGoal)
      let (introduced, modelGoal) ←
        listGoal.mvarId!.introN 4 [`ι, `inst, `model, `σ]
      let model := mkFVar introduced[2]!
      replaceMainGoal [modelGoal]
      withMainContext do
        let env ←
          nameEnvLiteral relationSpellings functionSpellings
        let proof ←
          Vampire.ExactReconstruction.exactProof
            declaration env model
        let proofSyntax ← Term.exprToSyntax proof
        evalTactic
          (← `(tactic| structural_exact_eq_symm $proofSyntax))
  | _ => throwUnsupportedSyntax

end CertifyJob
end FixedAmbient
end FrameworkII
end Synthesis
end Whiel
