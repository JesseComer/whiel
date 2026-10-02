-- Author: Jesse Comer
import Lean.Elab.Tactic

/-
  Targeted proof construction for clauses selected from a
  Vampire proof step. The tactic follows only `And`, `Or`,
  and `Forall`; it does not normalize the complete source
  proposition into CNF.

  `vampire_project using h` proves the current goal from
  `h` by constructing ordinary eliminator and constructor
  applications. Lean's kernel checks the resulting term.

  `vampire_project_ordered using h` uses the same proof
  construction but never permutes unnamed target binders.
  It fails closed when positional projection is insufficient;
  generated proof candidates can then use their existing
  compile-checked fallback.
-/

------------------------------------------------------------
-- Proposition Shapes
------------------------------------------------------------

namespace Whiel
namespace Vampire
namespace ClauseProjection

open Lean Meta

private def whnfReducible (e : Expr) : MetaM Expr :=
  withTransparency .reducible <| whnf e

private def isDefEqReducible
    (lhs rhs : Expr) : MetaM Bool :=
  withTransparency .reducible <| isDefEq lhs rhs

private def matchBinaryConst?
    (decl : Name)
    (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFnArgs with
  | (name, #[lhs, rhs]) =>
      if name == decl then some (lhs, rhs) else none
  | _ => none

private def mkAndLeft
    (lhs rhs proof : Expr) : Expr :=
  mkAppN (mkConst ``And.left) #[lhs, rhs, proof]

private def mkAndRight
    (lhs rhs proof : Expr) : Expr :=
  mkAppN (mkConst ``And.right) #[lhs, rhs, proof]

private def failProjection {α : Type} : MetaM α :=
  throwError "no structural clause projection"

end ClauseProjection
end Vampire
end Whiel

------------------------------------------------------------
-- Proof Construction
------------------------------------------------------------

namespace Whiel
namespace Vampire
namespace ClauseProjection

open Lean Meta

private def projectionFuel : Nat := 1024

private inductive BinderSearchMode where
  | exhaustive
  | ordered

private def previousFuel?
    (remaining : Nat) :
    Option {fuel // fuel < remaining} :=
  match remaining with
  | 0 => none
  | Nat.succ fuel =>
      some ⟨fuel, Nat.lt_succ_self fuel⟩

private def injectClauseLeaf
    (remaining : Nat)
    (sourceType targetType sourceProof : Expr)
    : MetaM Expr := do
    let fuelWithProof ←
      match previousFuel? remaining with
      | none =>
          throwError
            "clause projection exceeded its limit"
      | some fuel => pure fuel
    let fuel := fuelWithProof.val
    let sourceType ← whnfReducible sourceType
    let targetType ← whnfReducible targetType
    if sourceType == targetType ||
        (← isDefEqReducible sourceType targetType) then
      return sourceProof
    let (lhs, rhs) ←
      match matchBinaryConst? ``Or targetType with
      | some pair => pure pair
      | none => failProjection
    let injectLeft : MetaM Expr := do
      let proof ← injectClauseLeaf fuel sourceType
        lhs sourceProof
      pure <| mkAppN (mkConst ``Or.inl)
        #[lhs, rhs, proof]
    let injectRight : MetaM Expr := do
      let proof ← injectClauseLeaf fuel sourceType
        rhs sourceProof
      pure <| mkAppN (mkConst ``Or.inr)
        #[lhs, rhs, proof]
    injectLeft <|> injectRight
  termination_by remaining
  decreasing_by
    all_goals exact fuelWithProof.property

private def fvarUserName? (value : Expr) :
    MetaM (Option Name) := do
  match value with
  | Expr.fvar fvarId =>
      return some (← fvarId.getDecl).userName
  | _ => return none

private def projectClause
    (mode : BinderSearchMode)
    (remaining : Nat)
    (sourceType targetType sourceProof : Expr)
    (targetValues : List Expr) : MetaM Expr := do
    let fuelWithProof ←
      match previousFuel? remaining with
      | none =>
          throwError
            "clause projection exceeded its limit"
      | some fuel => pure fuel
    let fuel := fuelWithProof.val
    let sourceType ← whnfReducible sourceType
    let targetType ← whnfReducible targetType
    if sourceType == targetType ||
        (← isDefEqReducible sourceType targetType) then
      return sourceProof

    let fromSourceAnd : MetaM Expr := do
      let (lhs, rhs) ←
        match matchBinaryConst? ``And sourceType with
        | some pair => pure pair
        | none => failProjection
      let fromLeft := projectClause mode fuel lhs
        targetType (mkAndLeft lhs rhs sourceProof)
        targetValues
      let fromRight := projectClause mode fuel rhs
        targetType (mkAndRight lhs rhs sourceProof)
        targetValues
      fromLeft <|> fromRight

    let fromSourceOr : MetaM Expr := do
      let (lhs, rhs) ←
        match matchBinaryConst? ``Or sourceType with
        | some pair => pure pair
        | none => failProjection
      let leftHandler ←
        withLocalDeclD `h lhs fun h => do
          let proof ← projectClause mode fuel lhs
            targetType h targetValues
          mkLambdaFVars #[h] proof
      let rightHandler ←
        withLocalDeclD `h rhs fun h => do
          let proof ← projectClause mode fuel rhs
            targetType h targetValues
          mkLambdaFVars #[h] proof
      pure <| mkAppN (mkConst ``Or.elim)
        #[lhs, rhs, targetType, sourceProof,
          leftHandler, rightHandler]

    let fromSourceForall : MetaM Expr := do
      let (sourceName, sourceDomain, sourceBody) ←
        match sourceType with
        | Expr.forallE name domain body _ =>
            pure (name, domain, body)
        | _ => failProjection
      let preferred ← targetValues.filterM fun value => do
        return (← fvarUserName? value) == some sourceName
      let other := targetValues.filter fun value =>
        !preferred.contains value
      let candidates :=
        match mode with
        | .exhaustive => preferred ++ other
        | .ordered =>
            if preferred.isEmpty then other.take 1
            else preferred
      let useValue (value : Expr) : MetaM Expr := do
        let valueType ← inferType value
        unless ← isDefEqReducible valueType
            sourceDomain do
          failProjection
        let unused := targetValues.filter fun item =>
          item != value
        projectClause mode fuel
          (sourceBody.instantiate1 value)
          targetType
          (mkApp sourceProof value)
          unused
      candidates.foldr
        (fun value following =>
          useValue value <|> following)
        failProjection

    fromSourceAnd <|>
      fromSourceOr <|>
      fromSourceForall <|>
      injectClauseLeaf fuel sourceType targetType
        sourceProof
  termination_by remaining
  decreasing_by
    all_goals exact fuelWithProof.property

private def project
    (mode : BinderSearchMode)
    (remaining : Nat)
    (sourceType targetType sourceProof : Expr)
    (targetValues : List Expr := []) : MetaM Expr := do
    let fuelWithProof ←
      match previousFuel? remaining with
      | none =>
          throwError
            "clause projection exceeded its limit"
      | some fuel => pure fuel
    let fuel := fuelWithProof.val
    let sourceType ← whnfReducible sourceType
    let targetType ← whnfReducible targetType
    if sourceType == targetType ||
        (← isDefEqReducible sourceType targetType) then
      return sourceProof

    match targetType with
    | Expr.forallE targetName targetDomain
        targetBody targetInfo =>
        return ←
          withLocalDecl targetName targetInfo
              targetDomain fun value => do
            let targetBody :=
              targetBody.instantiate1 value
            let proof ←
              match sourceType with
              | Expr.forallE _ sourceDomain
                  sourceBody _ =>
                  if ← isDefEqReducible sourceDomain
                      targetDomain then
                    project mode fuel
                      (sourceBody.instantiate1 value)
                      targetBody
                      (mkApp sourceProof value)
                      targetValues
                  else
                    project mode fuel sourceType targetBody
                      sourceProof
                      (targetValues ++ [value])
              | _ =>
                  project mode fuel sourceType targetBody
                    sourceProof
                    (targetValues ++ [value])
            mkLambdaFVars #[value] proof
    | _ => pure ()

    match matchBinaryConst? ``And targetType with
    | some (lhs, rhs) =>
      let leftProof ← project mode fuel sourceType lhs
        sourceProof targetValues
      let rightProof ← project mode fuel sourceType rhs
        sourceProof targetValues
      return mkAppN (mkConst ``And.intro)
        #[lhs, rhs, leftProof, rightProof]
    | none => pure ()

    projectClause mode fuel sourceType targetType
      sourceProof targetValues
  termination_by remaining
  decreasing_by
    all_goals exact fuelWithProof.property

end ClauseProjection
end Vampire
end Whiel

------------------------------------------------------------
-- Tactic
------------------------------------------------------------

namespace Whiel
namespace Vampire
namespace ClauseProjection

open Lean Meta Elab Tactic

syntax (name := vampireProject)
  "vampire_project" " using " term : tactic

syntax (name := vampireProjectOrdered)
  "vampire_project_ordered" " using " term : tactic

private def runProjection
    (mode : BinderSearchMode)
    (tacticName : String)
    (source : TSyntax `term) : TacticM Unit := do
  withMainContext do
    let goal ← getMainGoal
    let targetType ←
      instantiateMVars (← goal.getType)
    let sourceProof ← Term.elabTerm source none
    Term.synthesizeSyntheticMVarsNoPostponing
    let sourceProof ←
      instantiateMVars sourceProof
    let sourceType ←
      instantiateMVars (← inferType sourceProof)
    unless ← isProp targetType do
      throwErrorAt source
        m!"{tacticName} target is not a proposition"
    unless ← isProp sourceType do
      throwErrorAt source
        m!"{tacticName} source is not a proof"
    if targetType.hasMVar || sourceType.hasMVar then
      throwErrorAt source
        m!"{tacticName} has unresolved metavariables"
    let proof ←
      try
        project mode projectionFuel sourceType
          targetType sourceProof
      catch _ =>
        throwErrorAt source
          m!"{tacticName} could not derive the goal"
    goal.assign proof
    replaceMainGoal []

elab_rules : tactic
  | `(tactic| vampire_project using $source) =>
      runProjection .exhaustive "vampire_project" source
  | `(tactic| vampire_project_ordered using $source) =>
      runProjection .ordered
        "vampire_project_ordered" source

end ClauseProjection
end Vampire
end Whiel
