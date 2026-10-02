-- Author: Jesse Comer
import Whiel.Eval.RA.SPJ

/-
  Checked assignment-level recognition for one fused
  equijoin.

  `AssignPlan.recognize` accepts only a projected equality
  selection over a product of two relation references.  The
  specialized executor is `SPJFast.eval`; its unmaterialized
  candidates are exposed for union-root execution.  Every
  other raw expression follows the existing `FastRA.eval`
  fallback.
-/

------------------------------------------------------------
-- Checked Equijoin Recognition
------------------------------------------------------------

namespace Whiel

namespace AssignPlan

variable {A D : Type}
variable [RelationNames A]
variable [Domain D] [LinearOrder D] [Hashable D]
variable {Γ : UnnamedSchema A}

/- Checked data for one projected binary equijoin. -/
structure Plan
    (D : Type)
    [Domain D] [LinearOrder D] [Hashable D]
    (Γ : UnnamedSchema A)
    (n : Nat) where
  source : RAExpr D Γ n
  idxs : List Nat
  first : Nat
  second : Nat
  left : Nat
  right : Nat
  leftRel : Γ.syms
  rightRel : Γ.syms
  leftBound : left < Γ.arity leftRel
  rightBound : right < Γ.arity rightRel
  indexBounds :
    ∀ k ∈ idxs, k < Γ.arity leftRel + Γ.arity rightRel
  selectBound :
    (Sel.eqIdx (D := D) first second).arityReq <
      Γ.arity leftRel + Γ.arity rightRel
  outputArity : idxs.length = n
  sourceExpr : source.expr =
    .proj idxs
      (.select (.eqIdx (D := D) first second)
        (.prod (.rel leftRel.1) (.rel rightRel.1)))
  selection_eq :
    ∀ t : Tuple D (Γ.arity leftRel + Γ.arity rightRel),
      Sel.Holds (.eqIdx first second) t ↔
      Sel.Holds
          (.eqIdx left (Γ.arity leftRel + right)) t

/- Physical strategy for one checked binary equijoin. -/
inductive Strategy where
| nested
| indexed

def Strategy.toString : Strategy → String
| .nested => "nested"
| .indexed => "indexed"

/- Unmaterialized candidates for a recognized plan. -/
def Plan.candidates
    (plan : Plan D Γ n)
    (S : FastInstance D Γ) :
    List (Tuple D n) :=
  plan.outputArity ▸
    SPJFast.candidates plan.idxs plan.left plan.right
      (S.relation plan.leftRel)
      (S.relation plan.rightRel)
      plan.leftBound plan.rightBound plan.indexBounds

/-
  Indexed unmaterialized candidates for a recognized plan.
-/
def Plan.candidatesIndexed
    (plan : Plan D Γ n)
    (S : FastInstance D Γ) :
    List (Tuple D n) :=
  plan.outputArity ▸
    SPJFast.candidatesIndexed plan.idxs plan.left plan.right
      (S.relation plan.leftRel)
      (S.relation plan.rightRel)
      plan.leftBound plan.rightBound plan.indexBounds

/- Run a recognized plan with the fused nested strategy. -/
def Plan.evalNested
    (plan : Plan D Γ n)
    (S : FastInstance D Γ) :
    FastRelation D n :=
  FastRelation.castArity plan.outputArity
    (SPJFast.eval plan.idxs plan.left plan.right
      (S.relation plan.leftRel)
      (S.relation plan.rightRel)
      plan.leftBound plan.rightBound plan.indexBounds)

/- Run a recognized plan with a temporary hash strategy. -/
def Plan.evalIndexed
    (plan : Plan D Γ n)
    (S : FastInstance D Γ) :
    FastRelation D n :=
  FastRelation.castArity plan.outputArity
    (SPJFast.evalIndexed plan.idxs plan.left plan.right
      (S.relation plan.leftRel)
      (S.relation plan.rightRel)
      plan.leftBound plan.rightBound plan.indexBounds)

/- Run a recognized plan using one selected strategy. -/
def Plan.evalWith
    (strategy : Strategy)
    (plan : Plan D Γ n)
    (S : FastInstance D Γ) :
    FastRelation D n :=
  match strategy with
  | .nested => plan.evalNested S
  | .indexed => plan.evalIndexed S

/-
  The production strategy selected for a recognized plan.
-/
def Plan.productionStrategy
    (_plan : Plan D Γ n)
    (_S : FastInstance D Γ) : Strategy :=
  .nested

/-
  Execute a recognized plan with its production strategy.
-/
def Plan.eval
    (plan : Plan D Γ n)
    (S : FastInstance D Γ) :
    FastRelation D n :=
  plan.evalWith (plan.productionStrategy S) S

/- Recognize the accepted raw projected-equijoin shape. -/
def recognize
    (e : RAExpr D Γ n) :
    Option { plan : Plan D Γ n // plan.source = e } :=
  match hExpr : e.expr with
  | .proj idxs (.select (.eqIdx i j)
      (.prod (.rel X) (.rel Y))) =>
      if hX : X ∈ Γ.syms then
        if hY : Y ∈ Γ.syms then
          let L : Γ.syms := ⟨X, hX⟩
          let R : Γ.syms := ⟨Y, hY⟩
          if hi : i < Γ.arity L then
            if hjLow : Γ.arity L ≤ j then
              if hj : j < Γ.arity L + Γ.arity R then
                if hIdx :
                    ∀ k ∈ idxs,
                      k < Γ.arity L + Γ.arity R then
                  let hSel :
                      (Sel.eqIdx i j).arityReq <
                        Γ.arity L + Γ.arity R := by
                    simp [Sel.arityReq]
                    omega
                  let hOut : idxs.length = n := by
                    have hWf := e.wf
                    rw [hExpr] at hWf
                    have hSel' := hSel
                    have hIdx' := hIdx
                    dsimp [L, R] at hSel' hIdx'
                    have hPair :
                        (∀ k ∈ idxs,
                          k < Γ.arity L + Γ.arity R) ∧
                          idxs.length = n := by
                      simpa [RawRAExpr.arity?,
                        UnnamedSchema.arity?, hX, hY,
                        hSel', hIdx'] using hWf
                    exact hPair.2
                  let plan : Plan D Γ n :=
                    { source := e,
                      idxs := idxs,
                      first := i,
                      second := j,
                      left := i,
                      right := j - Γ.arity L,
                      leftRel := L,
                      rightRel := R,
                      leftBound := hi,
                      rightBound := by omega,
                      indexBounds := hIdx,
                      selectBound := hSel,
                      outputArity := hOut,
                      sourceExpr := hExpr,
                      selection_eq := by
                        intro t
                        have hSum :
                            Γ.arity L +
                                (j - Γ.arity L) = j :=
                          Nat.add_sub_of_le hjLow
                        simp [hSum] }
                  some ⟨plan, rfl⟩
                else
                  none
              else
                none
            else
              none
          else if hj : j < Γ.arity L then
            if hiLow : Γ.arity L ≤ i then
              if hi : i < Γ.arity L + Γ.arity R then
                if hIdx :
                    ∀ k ∈ idxs,
                      k < Γ.arity L + Γ.arity R then
                  let hSel :
                      (Sel.eqIdx i j).arityReq <
                        Γ.arity L + Γ.arity R := by
                    simp [Sel.arityReq]
                    omega
                  let hOut : idxs.length = n := by
                    have hWf := e.wf
                    rw [hExpr] at hWf
                    have hSel' := hSel
                    have hIdx' := hIdx
                    dsimp [L, R] at hSel' hIdx'
                    have hPair :
                        (∀ k ∈ idxs,
                          k < Γ.arity L + Γ.arity R) ∧
                          idxs.length = n := by
                      simpa [RawRAExpr.arity?,
                        UnnamedSchema.arity?, hX, hY,
                        hSel', hIdx'] using hWf
                    exact hPair.2
                  let plan : Plan D Γ n :=
                    { source := e,
                      idxs := idxs,
                      first := i,
                      second := j,
                      left := j,
                      right := i - Γ.arity L,
                      leftRel := L,
                      rightRel := R,
                      leftBound := hj,
                      rightBound := by omega,
                      indexBounds := hIdx,
                      selectBound := hSel,
                      outputArity := hOut,
                      sourceExpr := hExpr,
                      selection_eq := by
                        intro t
                        have hSum :
                            Γ.arity L +
                                (i - Γ.arity L) = i :=
                          Nat.add_sub_of_le hiLow
                        constructor
                        · intro h
                          rw [Sel.holds_eqIdx_iff _
                            (by omega) (by omega)] at h
                          rw [Sel.holds_eqIdx_iff _
                            (by omega) (by omega)]
                          simpa [hSum] using h.symm
                        · intro h
                          rw [Sel.holds_eqIdx_iff _
                            (by omega) (by omega)] at h
                          rw [Sel.holds_eqIdx_iff _
                            (by omega) (by omega)]
                          simpa [hSum] using h.symm }
                  some ⟨plan, rfl⟩
                else
                  none
              else
                none
            else
              none
          else
            none
        else
          none
      else
        none
  | _ => none

/- Evaluate an expression with generic fallback. -/
def eval
    (e : RAExpr D Γ n)
    (S : FastInstance D Γ) :
    FastRelation D n :=
  match recognize e with
  | some ⟨plan, _⟩ => plan.eval S
  | none => FastRA.eval e S

/- Extract candidates for one non-union leaf. -/
def leafCandidates
    (e : RAExpr D Γ n)
    (S : FastInstance D Γ) :
    List (Tuple D n) :=
  match recognize e with
  | some ⟨plan, _⟩ => plan.candidates S
  | none => (FastRA.eval e S).tuples

/-
  Extract forced-strategy candidates for one non-union leaf.
-/
def leafCandidatesWith
    (strategy : Strategy)
    (e : RAExpr D Γ n)
    (S : FastInstance D Γ) :
    List (Tuple D n) :=
  match recognize e with
  | some ⟨plan, _⟩ =>
      match strategy with
      | .nested => plan.candidates S
      | .indexed => plan.candidatesIndexed S
  | none => (FastRA.eval e S).tuples

/-
  Evaluate an assignment with forced candidates and generic
  fallback.
-/
def evalWithCandidates
    (strategy : Strategy)
    (e : RAExpr D Γ n)
    (S : FastInstance D Γ) :
    FastRelation D n :=
  match recognize e with
  | some ⟨plan, _⟩ =>
      match strategy with
      | .nested => FastRelation.ofList (plan.candidates S)
      | .indexed =>
          FastRelation.ofList (plan.candidatesIndexed S)
  | none => FastRA.eval e S

end AssignPlan

end Whiel

------------------------------------------------------------
-- Assignment-Plan Correctness
------------------------------------------------------------

namespace Whiel

namespace AssignPlan

variable {A D : Type}
variable [RelationNames A]
variable [Domain D] [LinearOrder D] [Hashable D]
variable {Γ : UnnamedSchema A}

/- A recognized plan has the denotation of its source. -/
theorem Plan.evalNested_correct
    (plan : Plan D Γ n)
    (S : FastInstance D Γ) :
    (plan.evalNested S).toFinRelation =
      plan.source.eval S.toInstance := by
  rcases plan with
    ⟨source, idxs, first, second, left, right,
      leftRel, rightRel, leftBound, rightBound,
      indexBounds, selectBound, outputArity,
      sourceExpr, selectionEq⟩
  cases outputArity
  unfold Plan.evalNested
  simp only [FastRelation.castArity_toFinRelation]
  rw [SPJFast.eval_correct]
  have hRaw :
      source.expr.eval? (Γ := Γ) S.toInstance =
        some
          ⟨idxs.length,
            FinRelation.proj idxs
              (FinRelation.select
                (fun t => Sel.Holds
                  (.eqIdx first second) t)
                (FinRelation.prod
                  (S.relation leftRel).toFinRelation
                  (S.relation rightRel).toFinRelation))
              indexBounds⟩ := by
    rw [sourceExpr]
    simp only [RawRAExpr.eval?, Instance.relation?,
      FastInstance.toInstance, dif_pos leftRel.2,
      dif_pos rightRel.2]
    have hReq :
        (Sel.eqIdx (D := D) first second).arityReq <
          Γ.arity ⟨leftRel, leftRel.2⟩ +
            Γ.arity ⟨rightRel, rightRel.2⟩ := by
      simpa using selectBound
    rw [dif_pos hReq]
    dsimp
    rw [dif_pos indexBounds]
  have hSource :=
    RAExpr.raw_eval?_eq_eval source S.toInstance
  have hEval :
      source.eval S.toInstance =
        FinRelation.proj idxs
          (FinRelation.select
            (fun t => Sel.Holds
              (.eqIdx first second) t)
            (FinRelation.prod
              (S.relation leftRel).toFinRelation
              (S.relation rightRel).toFinRelation))
          indexBounds := by
    have hSome :
        some
            (⟨idxs.length,
              source.eval S.toInstance⟩ :
              Sigma (FinRelation D)) =
          some
            (⟨idxs.length,
              FinRelation.proj idxs
                (FinRelation.select
                  (fun t => Sel.Holds
                    (.eqIdx first second) t)
                  (FinRelation.prod
                    (S.relation leftRel).toFinRelation
                    (S.relation rightRel).toFinRelation))
                indexBounds⟩ :
                  Sigma (FinRelation D)) := by
      rw [← hSource]
      exact hRaw
    exact eq_of_heq
      (Sigma.mk.inj_iff.mp (Option.some.inj hSome)).2
  rw [hEval]
  have hSelect :
      FinRelation.select
          (fun t => Sel.Holds
            (.eqIdx left (Γ.arity leftRel + right)) t)
          (FinRelation.prod
            (S.relation leftRel).toFinRelation
            (S.relation rightRel).toFinRelation) =
        FinRelation.select
          (fun t => Sel.Holds (.eqIdx first second) t)
          (FinRelation.prod
            (S.relation leftRel).toFinRelation
            (S.relation rightRel).toFinRelation) := by
    apply Finset.ext
    intro t
    rw [FinRelation.mem_select_iff,
      FinRelation.mem_select_iff]
    exact and_congr Iff.rfl (selectionEq t).symm
  rw [hSelect]
  simp

/- The indexed strategy has the denotation of its source. -/
theorem Plan.evalIndexed_correct
    (plan : Plan D Γ n)
    (S : FastInstance D Γ) :
    (plan.evalIndexed S).toFinRelation =
      plan.source.eval S.toInstance := by
  unfold Plan.evalIndexed
  simp only [FastRelation.castArity_toFinRelation]
  rw [← SPJFast.eval_eq_evalIndexed]
  simpa [Plan.evalNested,
    FastRelation.castArity_toFinRelation] using
    Plan.evalNested_correct plan S

/- A selected strategy has the source denotation. -/
theorem Plan.evalWith_correct
    (strategy : Strategy)
    (plan : Plan D Γ n)
    (S : FastInstance D Γ) :
    (plan.evalWith strategy S).toFinRelation =
      plan.source.eval S.toInstance := by
  cases strategy
  · exact Plan.evalNested_correct plan S
  · exact Plan.evalIndexed_correct plan S

/- Production evaluation has source denotation. -/
theorem Plan.eval_correct
    (plan : Plan D Γ n)
    (S : FastInstance D Γ) :
    (plan.eval S).toFinRelation =
      plan.source.eval S.toInstance := by
  exact Plan.evalWith_correct
    (plan.productionStrategy S) plan S

/- Plan candidates have exactly the source support. -/
theorem Plan.mem_candidates_iff
    (plan : Plan D Γ n)
    (S : FastInstance D Γ)
    (t : Tuple D n) :
    t ∈ plan.candidates S ↔
      t ∈ plan.source.eval S.toInstance := by
  have hMaterialized :
      FastRelation.ofList (plan.candidates S) =
        plan.evalNested S := by
    rcases plan with
      ⟨source, idxs, first, second, left, right,
        leftRel, rightRel, leftBound, rightBound,
        indexBounds, selectBound, outputArity,
        sourceExpr, selectionEq⟩
    cases outputArity
    rfl
  rw [← FastRelation.mem_ofList_iff,
    hMaterialized, Plan.evalNested_correct]

/-
  Indexed plan candidates have exactly the source support.
-/
theorem Plan.mem_candidatesIndexed_iff
    (plan : Plan D Γ n)
    (S : FastInstance D Γ)
    (t : Tuple D n) :
    t ∈ plan.candidatesIndexed S ↔
      t ∈ plan.source.eval S.toInstance := by
  have hMaterialized :
      FastRelation.ofList (plan.candidatesIndexed S) =
        plan.evalIndexed S := by
    rcases plan with
      ⟨source, idxs, first, second, left, right,
        leftRel, rightRel, leftBound, rightBound,
        indexBounds, selectBound, outputArity,
        sourceExpr, selectionEq⟩
    cases outputArity
    rfl
  rw [← FastRelation.mem_ofList_iff,
    hMaterialized, Plan.evalIndexed_correct]

/- Leaf candidates have exactly the expression support. -/
theorem mem_leafCandidates_iff
    (e : RAExpr D Γ n)
    (S : FastInstance D Γ)
    (t : Tuple D n) :
    t ∈ leafCandidates e S ↔
      t ∈ e.eval S.toInstance := by
  unfold leafCandidates
  cases hPlan : recognize e with
  | none =>
      rw [← FastRelation.mem_toFinRelation_iff,
        FastRA.eval_correct]
  | some found =>
      change t ∈ found.val.candidates S ↔
        t ∈ e.eval S.toInstance
      simpa [found.property] using
        Plan.mem_candidates_iff found.val S t

/-
  Forced leaf candidates have exactly the expression
  support.
-/
theorem mem_leafCandidatesWith_iff
    (strategy : Strategy)
    (e : RAExpr D Γ n)
    (S : FastInstance D Γ)
    (t : Tuple D n) :
    t ∈ leafCandidatesWith strategy e S ↔
      t ∈ e.eval S.toInstance := by
  unfold leafCandidatesWith
  cases hPlan : recognize e with
  | none =>
      rw [← FastRelation.mem_toFinRelation_iff,
        FastRA.eval_correct]
  | some found =>
      change t ∈ (match strategy with
          | .nested => found.val.candidates S
          | .indexed => found.val.candidatesIndexed S) ↔
        t ∈ e.eval S.toInstance
      cases strategy
      · simpa [found.property] using
          Plan.mem_candidates_iff found.val S t
      · simpa [found.property] using
          Plan.mem_candidatesIndexed_iff found.val S t

/-
  Forced assignment evaluation preserves source denotation.
-/
theorem evalWithCandidates_correct
    (strategy : Strategy)
    (e : RAExpr D Γ n)
    (S : FastInstance D Γ) :
    (evalWithCandidates strategy e S).toFinRelation =
      e.eval S.toInstance := by
  unfold evalWithCandidates
  cases hPlan : recognize e with
  | none =>
      exact FastRA.eval_correct e S
  | some found =>
      cases strategy
      · change
          (FastRelation.ofList
            (found.val.candidates S)).toFinRelation =
            e.eval S.toInstance
        apply Finset.ext
        intro t
        rw [FastRelation.mem_ofList_iff]
        simpa [found.property] using
          Plan.mem_candidates_iff found.val S t
      · change
          (FastRelation.ofList
            (found.val.candidatesIndexed S)).toFinRelation =
              e.eval S.toInstance
        apply Finset.ext
        intro t
        rw [FastRelation.mem_ofList_iff]
        simpa [found.property] using
          Plan.mem_candidatesIndexed_iff found.val S t

/- Assignment evaluation covers both execution paths. -/
theorem eval_correct
    (e : RAExpr D Γ n)
    (S : FastInstance D Γ) :
    (eval e S).toFinRelation = e.eval S.toInstance := by
  unfold eval
  cases hPlan : recognize e with
  | none =>
      exact FastRA.eval_correct e S
  | some found =>
      change (found.val.eval S).toFinRelation =
        e.eval S.toInstance
      simpa [found.property] using
        Plan.eval_correct found.val S

end AssignPlan

end Whiel
