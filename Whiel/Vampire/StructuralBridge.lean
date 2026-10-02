-- Author: Jesse Comer
import Lean.Elab.Tactic

/-
  Proof-producing tactics for transferring explicit Lean
  propositions from Vampire into shallow FOL semantics.

  The bridge follows logical structure instead of asking
  elaboration to compare whole propositions at once. Atomic
  leaves are deliberately returned without a metaprogram
  equality check: Lean's kernel must accept every resulting
  local conversion when it checks the completed theorem.
  Reversed equality leaves are the sole exception; the
  bridge constructs them explicitly with `Eq.symm`.
-/

------------------------------------------------------------
-- Proposition Inspection
------------------------------------------------------------

namespace Whiel
namespace Vampire
namespace StructuralBridge

open Lean Meta Elab Tactic

private def whnfAll (e : Expr) : MetaM Expr :=
  withTransparency .all <| whnf e

private def isDefEqAll
    (lhs rhs : Expr) : MetaM Bool :=
  withTransparency .all <| isDefEq lhs rhs

private def matchBinaryConst?
    (decl : Name)
    (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFnArgs with
  | (name, #[lhs, rhs]) =>
      if name == decl then some (lhs, rhs) else none
  | _ => none

private def matchExists?
    (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFnArgs with
  | (name, #[domain, predicate]) =>
      if name == ``Exists then
        some (domain, predicate)
      else
        none
  | _ => none

private def matchEq?
    (e : Expr) : Option (Expr × Expr × Expr) :=
  match e.getAppFnArgs with
  | (name, #[domain, lhs, rhs]) =>
      if name == ``Eq then
        some (domain, lhs, rhs)
      else
        none
  | _ => none

private def eqLevel?
    (e : Expr) : Option Level :=
  match e.getAppFn with
  | Expr.const ``Eq [u] => some u
  | _ => none

private def predicateBody
    (predicate : Expr) : MetaM
      (Name × BinderInfo × Expr × Expr) := do
  let predicate ← whnfAll predicate
  match predicate with
  | Expr.lam name domain body info =>
      pure (name, info, domain, body)
  | _ =>
      throwError
        "existential predicate is not a lambda"

private def mkAndLeft
    (lhs rhs h : Expr) : Expr :=
  mkAppN (mkConst ``And.left) #[lhs, rhs, h]

private def mkAndRight
    (lhs rhs h : Expr) : Expr :=
  mkAppN (mkConst ``And.right) #[lhs, rhs, h]

private partial def flattenAnd
    (type proof : Expr) :
    MetaM (Array (Expr × Expr)) := do
  let type ← whnfAll type
  match matchBinaryConst? ``And type with
  | some (lhs, rhs) =>
      let left ←
        flattenAnd lhs (mkAndLeft lhs rhs proof)
      let right ←
        flattenAnd rhs (mkAndRight lhs rhs proof)
      pure (left ++ right)
  | none =>
      pure #[(type, proof)]

private partial def countOrLeaves
    (type : Expr) : MetaM Nat := do
  let type ← whnfAll type
  match matchBinaryConst? ``Or type with
  | some (lhs, rhs) =>
      return (← countOrLeaves lhs) +
        (← countOrLeaves rhs)
  | none =>
      return 1

/-
  Repair for an atomic equality leaf whose two sides are
  exchanged.

  The decision is taken with the kernel's own definitional
  equality rather than the elaborator's. A shallow semantic
  atom is a term the kernel compares readily and the
  elaborator does not: asking `Meta.isDefEq` or `Meta.whnf`
  to relate one to a solver's restatement of it exhausts
  memory on obligations of realistic size, which is why the
  bridge otherwise leaves atomic leaves alone. The kernel is
  in any case the arbiter here; this only chooses which of
  two candidate terms to hand it, and a refusal to decide
  costs nothing beyond the leaf being passed through as
  before.

  Order matters for cost. The aligned leaf is the common
  case, so it is tried first and settles in one comparison;
  only a leaf that genuinely fails to align is compared
  against the mirrored statement. `Eq.symm` is then applied
  to explicit arguments read off the target, so no
  unification is involved.
-/
private def bridgeAtomic
    (sourceType targetType sourceProof : Expr) :
    MetaM Expr := do
  let sourceType ← instantiateMVars sourceType
  let targetType ← instantiateMVars targetType
  match matchEq? targetType, eqLevel? targetType with
  | some (targetDomain, targetLhs, targetRhs), some level =>
      let environment ← getEnv
      let context ← getLCtx
      if Lean.Kernel.isDefEqGuarded environment context
          sourceType targetType then
        pure sourceProof
      else
        let mirrored :=
          mkApp3 (mkConst ``Eq [level]) targetDomain
            targetRhs targetLhs
        if Lean.Kernel.isDefEqGuarded environment context
            sourceType mirrored then
          pure <| mkApp4 (mkConst ``Eq.symm [level])
            targetDomain targetRhs targetLhs sourceProof
        else
          pure sourceProof
  | _, _ =>
      pure sourceProof

end StructuralBridge
end Vampire
end Whiel

------------------------------------------------------------
-- Structural Proof Construction
------------------------------------------------------------

namespace Whiel
namespace Vampire
namespace StructuralBridge

open Lean Meta

mutual
  private partial def bridge
      (allowEqSymmetry : Bool)
      (sourceType targetType sourceProof : Expr) :
      MetaM Expr := do
    let sourceType ← whnfAll sourceType
    let targetType ← whnfAll targetType
    match matchBinaryConst? ``And sourceType,
        matchBinaryConst? ``And targetType with
    | some _, some _ =>
        let leaves ←
          flattenAnd sourceType sourceProof
        let (proof, used) ←
          buildAnd allowEqSymmetry targetType leaves 0
        unless used == leaves.size do
          throwError
            "conjunction leaf-count mismatch"
        pure proof
    | none, none =>
      match matchBinaryConst? ``Or sourceType,
          matchBinaryConst? ``Or targetType with
      | some _, some _ =>
          let sourceCount ←
            countOrLeaves sourceType
          let targetCount ←
            countOrLeaves targetType
          unless sourceCount == targetCount do
            throwError
              "disjunction leaf-count mismatch"
          eliminateOr allowEqSymmetry sourceType targetType
            sourceProof 0
      | none, none =>
        match matchBinaryConst? ``Iff sourceType,
            matchBinaryConst? ``Iff targetType with
        | some (sourceLhs, sourceRhs),
            some (targetLhs, targetRhs) =>
            let forward ←
              withLocalDeclD `h targetLhs fun h => do
                let sourceArg ←
                  bridge allowEqSymmetry
                    targetLhs sourceLhs h
                let sourceResult :=
                  mkAppN (mkConst ``Iff.mp)
                    #[sourceLhs, sourceRhs,
                      sourceProof, sourceArg]
                let targetResult ←
                  bridge allowEqSymmetry
                    sourceRhs targetRhs
                    sourceResult
                mkLambdaFVars #[h] targetResult
            let backward ←
              withLocalDeclD `h targetRhs fun h => do
                let sourceArg ←
                  bridge allowEqSymmetry
                    targetRhs sourceRhs h
                let sourceResult :=
                  mkAppN (mkConst ``Iff.mpr)
                    #[sourceLhs, sourceRhs,
                      sourceProof, sourceArg]
                let targetResult ←
                  bridge allowEqSymmetry
                    sourceLhs targetLhs
                    sourceResult
                mkLambdaFVars #[h] targetResult
            pure <| mkAppN (mkConst ``Iff.intro)
              #[targetLhs, targetRhs,
                forward, backward]
        | none, none =>
          match matchExists? sourceType,
              matchExists? targetType with
          | some (sourceDomain, sourcePredicate),
              some (targetDomain, targetPredicate) =>
              unless ←
                  isDefEqAll sourceDomain targetDomain do
                throwError
                  "existential-domain mismatch"
              let
                (sourceName, sourceInfo, _,
                  sourceBody) ←
                    predicateBody sourcePredicate
              let (_, _, _, targetBody) ←
                predicateBody targetPredicate
              let domainType ←
                whnfAll (← inferType sourceDomain)
              let uLevel ← match domainType with
                | Expr.sort u => pure u
                | _ =>
                    throwError
                      "existential domain is not a sort"
              let handler ←
                withLocalDecl sourceName sourceInfo
                    sourceDomain fun witness => do
                  let sourceBodyAt :=
                    sourceBody.instantiate1 witness
                  let targetBodyAt :=
                    targetBody.instantiate1 witness
                  withLocalDeclD `h sourceBodyAt fun h => do
                    let targetProof ←
                      bridge allowEqSymmetry
                        sourceBodyAt targetBodyAt h
                    let result :=
                      mkAppN
                        (mkConst ``Exists.intro [uLevel])
                        #[targetDomain, targetPredicate,
                          witness, targetProof]
                    mkLambdaFVars #[witness, h] result
              pure <| mkAppN
                (mkConst ``Exists.elim [uLevel])
                #[sourceDomain, sourcePredicate,
                  targetType, sourceProof, handler]
          | none, none =>
            match sourceType, targetType with
            | Expr.forallE _ sourceDomain
                  sourceBody _,
                Expr.forallE targetName targetDomain
                  targetBody targetInfo =>
              let sourceDependent :=
                sourceBody.hasLooseBVar 0
              let targetDependent :=
                targetBody.hasLooseBVar 0
              if sourceDependent || targetDependent then
                unless
                    sourceDependent && targetDependent do
                  throwError
                    "quantifier/implication shape mismatch"
                unless ←
                    isDefEqAll sourceDomain
                      targetDomain do
                  throwError
                    "quantifier-domain mismatch"
                withLocalDecl targetName targetInfo
                    targetDomain fun x => do
                  let sourceResult :=
                    mkApp sourceProof x
                  let proof ←
                    bridge allowEqSymmetry
                      (sourceBody.instantiate1 x)
                      (targetBody.instantiate1 x)
                      sourceResult
                  mkLambdaFVars #[x] proof
              else
                withLocalDecl targetName targetInfo
                    targetDomain fun h => do
                  let sourceArg ←
                    bridge allowEqSymmetry
                      targetDomain sourceDomain h
                  let sourceResult :=
                    mkApp sourceProof sourceArg
                  let proof ←
                    bridge allowEqSymmetry
                      sourceBody targetBody
                      sourceResult
                  mkLambdaFVars #[h] proof
            | _, _ =>
                if allowEqSymmetry then
                  bridgeAtomic sourceType targetType
                    sourceProof
                else
                  pure sourceProof
          | _, _ =>
              throwError
                "existential shape mismatch"
        | _, _ =>
            throwError "iff shape mismatch"
      | _, _ =>
          throwError
            ("disjunction shape mismatch:\nsource: " ++
              toString sourceType ++ "\ntarget: " ++
              toString targetType)
    | _, _ =>
        throwError
          ("conjunction shape mismatch:\nsource: " ++
            toString sourceType ++ "\ntarget: " ++
            toString targetType)

  private partial def buildAnd
      (allowEqSymmetry : Bool)
      (targetType : Expr)
      (sourceLeaves : Array (Expr × Expr))
      (offset : Nat) : MetaM (Expr × Nat) := do
    let targetType ← whnfAll targetType
    match matchBinaryConst? ``And targetType with
    | some (lhs, rhs) =>
        let (leftProof, afterLeft) ←
          buildAnd allowEqSymmetry lhs sourceLeaves offset
        let (rightProof, afterRight) ←
          buildAnd allowEqSymmetry rhs sourceLeaves afterLeft
        let proof :=
          mkAppN (mkConst ``And.intro)
            #[lhs, rhs, leftProof, rightProof]
        pure (proof, afterRight)
    | none =>
        if h : offset < sourceLeaves.size then
          let (sourceType, sourceProof) :=
            sourceLeaves[offset]
          let proof ←
            bridge allowEqSymmetry
              sourceType targetType sourceProof
          pure (proof, offset + 1)
        else
          throwError
            "target conjunction has too many leaves"

  private partial def injectOr
      (allowEqSymmetry : Bool)
      (targetType leafProofType leafProof : Expr)
      (index : Nat) : MetaM Expr := do
    let targetType ← whnfAll targetType
    match matchBinaryConst? ``Or targetType with
    | some (lhs, rhs) =>
        let leftCount ← countOrLeaves lhs
        if index < leftCount then
          let proof ←
            injectOr allowEqSymmetry
              lhs leafProofType leafProof index
          pure <| mkAppN (mkConst ``Or.inl)
            #[lhs, rhs, proof]
        else
          let proof ←
            injectOr allowEqSymmetry
              rhs leafProofType leafProof
              (index - leftCount)
          pure <| mkAppN (mkConst ``Or.inr)
            #[lhs, rhs, proof]
    | none =>
        unless index == 0 do
          throwError
            "target disjunction leaf index overflow"
        bridge allowEqSymmetry
          leafProofType targetType leafProof

  private partial def eliminateOr
      (allowEqSymmetry : Bool)
      (sourceType targetType sourceProof : Expr)
      (offset : Nat) : MetaM Expr := do
    let sourceType ← whnfAll sourceType
    match matchBinaryConst? ``Or sourceType with
    | some (lhs, rhs) =>
        let leftCount ← countOrLeaves lhs
        let leftHandler ←
          withLocalDeclD `h lhs fun h => do
            let proof ←
              eliminateOr allowEqSymmetry
                lhs targetType h offset
            mkLambdaFVars #[h] proof
        let rightHandler ←
          withLocalDeclD `h rhs fun h => do
            let proof ←
              eliminateOr allowEqSymmetry
                rhs targetType h
                (offset + leftCount)
            mkLambdaFVars #[h] proof
        pure <| mkAppN (mkConst ``Or.elim)
          #[lhs, rhs, targetType, sourceProof,
            leftHandler, rightHandler]
    | none =>
        injectOr allowEqSymmetry
          targetType sourceType sourceProof
          offset
end

end StructuralBridge
end Vampire
end Whiel

------------------------------------------------------------
-- Tactics
------------------------------------------------------------

namespace Whiel
namespace Vampire
namespace StructuralBridge

open Lean Meta Elab Tactic

syntax (name := structuralExact)
  "structural_exact" term : tactic

/-
  `structural_exact_eq_symm` closes the goal from the given
  proof exactly as `structural_exact` does, and additionally
  repairs an atomic equality leaf whose two sides are
  exchanged. A certificate needs this: the solver is free to
  restate an input equality in the opposite orientation, so a
  reconstructed statement can differ from the Lean-owned one
  by `Eq.symm` alone. The repair is inserted only where both
  sides are confirmed mirrored, every other leaf is passed
  through unchanged, and the kernel still checks the
  completed term.
-/
syntax (name := structuralExactEqSymm)
  "structural_exact_eq_symm" term : tactic

syntax (name := structuralApply)
  "structural_apply" term " with " term,* : tactic

syntax (name := structuralApplyEqSymm)
  "structural_apply_eq_symm" term " with " term,* : tactic

private partial def buildConjunction
    (leaves : Array (Expr × Expr))
    (index : Nat := 0) : MetaM (Expr × Expr) := do
  if h : index < leaves.size then
    let (headType, headProof) := leaves[index]
    if index + 1 == leaves.size then
      pure (headType, headProof)
    else
      let (tailType, tailProof) ←
        buildConjunction leaves (index + 1)
      let type :=
        mkApp2 (mkConst ``And) headType tailType
      let proof :=
        mkAppN (mkConst ``And.intro)
          #[headType, tailType,
            headProof, tailProof]
      pure (type, proof)
  else
    throwError
      "structural_apply requires a hypothesis"

elab_rules : tactic
  | `(tactic| structural_exact $term) => do
      withMainContext do
        let goal ← getMainGoal
        let targetType ← goal.getType
        let sourceProof ← Term.elabTerm term none
        Term.synthesizeSyntheticMVarsNoPostponing
        let sourceProof ←
          instantiateMVars sourceProof
        let sourceType ← inferType sourceProof
        let proof ←
          bridge false sourceType targetType sourceProof
        goal.assign proof
        replaceMainGoal []

elab_rules : tactic
  | `(tactic| structural_exact_eq_symm $term) => do
      withMainContext do
        let goal ← getMainGoal
        let targetType ← goal.getType
        let sourceProof ← Term.elabTerm term none
        Term.synthesizeSyntheticMVarsNoPostponing
        let sourceProof ←
          instantiateMVars sourceProof
        let sourceType ← inferType sourceProof
        let proof ←
          bridge true sourceType targetType sourceProof
        goal.assign proof
        replaceMainGoal []

elab_rules : tactic
  | `(tactic|
      structural_apply $proofTerm with $args,*) => do
      withMainContext do
        let goal ← getMainGoal
        let targetType ← goal.getType
        let sourceProof ←
          Term.elabTerm proofTerm none
        let mut leaves := #[]
        for arg in args.getElems do
          let proof ← Term.elabTerm arg none
          leaves :=
            leaves.push ((← inferType proof), proof)
        Term.synthesizeSyntheticMVarsNoPostponing
        let sourceProof ←
          instantiateMVars sourceProof
        let sourceType ←
          whnfAll (← inferType sourceProof)
        let (sourceDomain, sourceBody) ←
          match sourceType with
          | Expr.forallE _ domain body _ =>
              unless !body.hasLooseBVar 0 do
                throwError
                  "structural_apply source is dependent"
              pure (domain, body)
          | _ =>
              throwError
                ("structural_apply source is not an " ++
                  "implication")
        let instantiatedLeaves ←
          leaves.mapM fun (type, proof) => do
            let type ← instantiateMVars type
            let proof ← instantiateMVars proof
            pure (type, proof)
        let (argumentType, argumentProof) ←
          buildConjunction instantiatedLeaves
        let sourceArgument ←
          bridge false argumentType sourceDomain
            argumentProof
        let sourceResult :=
          mkApp sourceProof sourceArgument
        let proof ←
          bridge false sourceBody targetType sourceResult
        goal.assign proof
        replaceMainGoal []

elab_rules : tactic
  | `(tactic|
      structural_apply_eq_symm $proofTerm with $args,*) => do
      withMainContext do
        let goal ← getMainGoal
        let targetType ← goal.getType
        let sourceProof ←
          Term.elabTerm proofTerm none
        let mut leaves := #[]
        for arg in args.getElems do
          let proof ← Term.elabTerm arg none
          leaves :=
            leaves.push ((← inferType proof), proof)
        Term.synthesizeSyntheticMVarsNoPostponing
        let sourceProof ←
          instantiateMVars sourceProof
        let sourceType ←
          whnfAll (← inferType sourceProof)
        let (sourceDomain, sourceBody) ←
          match sourceType with
          | Expr.forallE _ domain body _ =>
              unless !body.hasLooseBVar 0 do
                throwError
                  ("structural_apply_eq_symm source is " ++
                    "dependent")
              pure (domain, body)
          | _ =>
              throwError
                ("structural_apply_eq_symm source is not " ++
                  "an implication")
        let instantiatedLeaves ←
          leaves.mapM fun (type, proof) => do
            let type ← instantiateMVars type
            let proof ← instantiateMVars proof
            pure (type, proof)
        let (argumentType, argumentProof) ←
          buildConjunction instantiatedLeaves
        let sourceArgument ←
          bridge true argumentType sourceDomain
            argumentProof
        let sourceResult :=
          mkApp sourceProof sourceArgument
        let proof ←
          bridge true sourceBody targetType sourceResult
        goal.assign proof
        replaceMainGoal []

end StructuralBridge
end Vampire
end Whiel
