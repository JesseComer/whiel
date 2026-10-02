-- Author: Jesse Comer
import Whiel.Eval.RA.AssignPlan

/-
  Assignment execution specialized at union roots.

  `UnionPlan.candidatesRaw` concatenates candidate support
  through a union tree.  Recognized SPJ leaves remain
  unmaterialized; all other leaves use `FastRA.eval`.
  `UnionPlan.eval` materializes the complete union once and
  delegates every non-union root to `AssignPlan.eval`.

  Correctness is proven by:
    * `UnionPlan.mem_candidatesRaw_iff`
    * `UnionPlan.eval_correct`
-/

------------------------------------------------------------
-- Union Candidate Collection
------------------------------------------------------------

namespace Whiel

namespace UnionPlan

variable {A D : Type}
variable [RelationNames A]
variable [Domain D] [LinearOrder D] [Hashable D]
variable {Γ : UnnamedSchema A}

/- A well-formed union has same-arity children. -/
omit [LinearOrder D] [Hashable D] in
private theorem union_wf
    (e₁ e₂ : RawRAExpr A D)
    (hAr :
      (RawRAExpr.union e₁ e₂).arity? Γ = some n) :
    e₁.arity? Γ = some n ∧
      e₂.arity? Γ = some n := by
  cases h₁ : e₁.arity? Γ with
  | none =>
      simp [RawRAExpr.arity?, h₁] at hAr
  | some n₁ =>
      cases h₂ : e₂.arity? Γ with
      | none =>
          simp [RawRAExpr.arity?, h₁, h₂] at hAr
      | some n₂ =>
          by_cases hEq : n₁ = n₂
          · subst n₂
            have hn : n₁ = n := by
              simpa [RawRAExpr.arity?, h₁, h₂]
                using hAr
            exact ⟨congrArg some hn, congrArg some hn⟩
          · simp [RawRAExpr.arity?, h₁, h₂, hEq]
              at hAr

/- Collect candidates through a well-formed union tree. -/
def candidatesRaw
    (e : RawRAExpr A D)
    (hAr : e.arity? Γ = some n)
    (S : FastInstance D Γ) :
    List (Tuple D n) :=
  match e with
  | .union e₁ e₂ =>
      let hChildren := union_wf e₁ e₂ hAr
      candidatesRaw e₁ hChildren.1 S ++
        candidatesRaw e₂ hChildren.2 S
  | .top =>
      AssignPlan.leafCandidates ⟨.top, hAr⟩ S
  | .empty m =>
      AssignPlan.leafCandidates ⟨.empty m, hAr⟩ S
  | .rel X =>
      AssignPlan.leafCandidates ⟨.rel X, hAr⟩ S
  | .single d =>
      AssignPlan.leafCandidates ⟨.single d, hAr⟩ S
  | .select φ raw =>
      AssignPlan.leafCandidates ⟨.select φ raw, hAr⟩ S
  | .proj idxs raw =>
      AssignPlan.leafCandidates ⟨.proj idxs raw, hAr⟩ S
  | .prod raw₁ raw₂ =>
      AssignPlan.leafCandidates
        ⟨.prod raw₁ raw₂, hAr⟩ S
  | .diff raw₁ raw₂ =>
      AssignPlan.leafCandidates
        ⟨.diff raw₁ raw₂, hAr⟩ S

/-
  Collect forced-strategy candidates through a union tree.
-/
def candidatesRawWith
    (strategy : AssignPlan.Strategy)
    (e : RawRAExpr A D)
    (hAr : e.arity? Γ = some n)
    (S : FastInstance D Γ) :
    List (Tuple D n) :=
  match e with
  | .union e₁ e₂ =>
      let hChildren := union_wf e₁ e₂ hAr
      candidatesRawWith strategy e₁ hChildren.1 S ++
        candidatesRawWith strategy e₂ hChildren.2 S
  | .top =>
      AssignPlan.leafCandidatesWith strategy
        ⟨.top, hAr⟩ S
  | .empty m =>
      AssignPlan.leafCandidatesWith strategy
        ⟨.empty m, hAr⟩ S
  | .rel X =>
      AssignPlan.leafCandidatesWith strategy
        ⟨.rel X, hAr⟩ S
  | .single d =>
      AssignPlan.leafCandidatesWith strategy
        ⟨.single d, hAr⟩ S
  | .select φ raw =>
      AssignPlan.leafCandidatesWith strategy
        ⟨.select φ raw, hAr⟩ S
  | .proj idxs raw =>
      AssignPlan.leafCandidatesWith strategy
        ⟨.proj idxs raw, hAr⟩ S
  | .prod raw₁ raw₂ =>
      AssignPlan.leafCandidatesWith strategy
        ⟨.prod raw₁ raw₂, hAr⟩ S
  | .diff raw₁ raw₂ =>
      AssignPlan.leafCandidatesWith strategy
        ⟨.diff raw₁ raw₂, hAr⟩ S

end UnionPlan

end Whiel

------------------------------------------------------------
-- Union-Root Assignment Evaluation
------------------------------------------------------------

namespace Whiel

namespace UnionPlan

variable {A D : Type}
variable [RelationNames A]
variable [Domain D] [LinearOrder D] [Hashable D]
variable {Γ : UnnamedSchema A}

/- Evaluate a union root with one final materialization. -/
def eval
    (e : RAExpr D Γ n)
    (S : FastInstance D Γ) :
    FastRelation D n :=
  match e.expr with
  | .union _ _ =>
      FastRelation.ofList
        (candidatesRaw e.expr e.wf S)
  | _ => AssignPlan.eval e S

/-
  Evaluate while forcing recognized union-leaf candidates.
-/
def evalWith
    (strategy : AssignPlan.Strategy)
    (e : RAExpr D Γ n)
    (S : FastInstance D Γ) :
    FastRelation D n :=
  match e.expr with
  | .union _ _ =>
      FastRelation.ofList
        (candidatesRawWith strategy e.expr e.wf S)
  | _ => AssignPlan.evalWithCandidates strategy e S

end UnionPlan

end Whiel

------------------------------------------------------------
-- Union Candidate Correctness
------------------------------------------------------------

namespace Whiel

namespace UnionPlan

variable {A D : Type}
variable [RelationNames A]
variable [Domain D] [LinearOrder D] [Hashable D]
variable {Γ : UnnamedSchema A}

/- Union candidates have exactly the expression support. -/
theorem mem_candidatesRaw_iff
    (e : RawRAExpr A D)
    (hAr : e.arity? Γ = some n)
    (S : FastInstance D Γ)
    (t : Tuple D n) :
    t ∈ candidatesRaw e hAr S ↔
      t ∈ (⟨e, hAr⟩ : RAExpr D Γ n).eval
        S.toInstance := by
  induction e generalizing n with
  | top =>
      simpa [candidatesRaw] using
        AssignPlan.mem_leafCandidates_iff
          (⟨.top, hAr⟩ : RAExpr D Γ n) S t
  | empty m =>
      simpa [candidatesRaw] using
        AssignPlan.mem_leafCandidates_iff
          (⟨.empty m, hAr⟩ : RAExpr D Γ n) S t
  | rel X =>
      simpa [candidatesRaw] using
        AssignPlan.mem_leafCandidates_iff
          (⟨.rel X, hAr⟩ : RAExpr D Γ n) S t
  | single d =>
      simpa [candidatesRaw] using
        AssignPlan.mem_leafCandidates_iff
          (⟨.single d, hAr⟩ : RAExpr D Γ n) S t
  | select φ e ih =>
      simpa [candidatesRaw] using
        AssignPlan.mem_leafCandidates_iff
          (⟨.select φ e, hAr⟩ : RAExpr D Γ n) S t
  | proj idxs e ih =>
      simpa [candidatesRaw] using
        AssignPlan.mem_leafCandidates_iff
          (⟨.proj idxs e, hAr⟩ : RAExpr D Γ n) S t
  | prod e₁ e₂ ih₁ ih₂ =>
      simpa [candidatesRaw] using
        AssignPlan.mem_leafCandidates_iff
          (⟨.prod e₁ e₂, hAr⟩ : RAExpr D Γ n) S t
  | union e₁ e₂ ih₁ ih₂ =>
      have hChildren := union_wf e₁ e₂ hAr
      let left : RAExpr D Γ n := ⟨e₁, hChildren.1⟩
      let right : RAExpr D Γ n := ⟨e₂, hChildren.2⟩
      simp only [candidatesRaw, List.mem_append]
      rw [ih₁ hChildren.1 t,
        ih₂ hChildren.2 t]
      simpa [left, right, RAExpr.union] using
        (RAExpr.mem_eval_union_iff
          left right S.toInstance t).symm
  | diff e₁ e₂ ih₁ ih₂ =>
      simpa [candidatesRaw] using
        AssignPlan.mem_leafCandidates_iff
          (⟨.diff e₁ e₂, hAr⟩ : RAExpr D Γ n) S t

/-
  Forced union candidates have exactly expression support.
-/
theorem mem_candidatesRawWith_iff
    (strategy : AssignPlan.Strategy)
    (e : RawRAExpr A D)
    (hAr : e.arity? Γ = some n)
    (S : FastInstance D Γ)
    (t : Tuple D n) :
    t ∈ candidatesRawWith strategy e hAr S ↔
      t ∈ (⟨e, hAr⟩ : RAExpr D Γ n).eval
        S.toInstance := by
  induction e generalizing n with
  | top =>
      simpa [candidatesRawWith] using
        AssignPlan.mem_leafCandidatesWith_iff strategy
          (⟨.top, hAr⟩ : RAExpr D Γ n) S t
  | empty m =>
      simpa [candidatesRawWith] using
        AssignPlan.mem_leafCandidatesWith_iff strategy
          (⟨.empty m, hAr⟩ : RAExpr D Γ n) S t
  | rel X =>
      simpa [candidatesRawWith] using
        AssignPlan.mem_leafCandidatesWith_iff strategy
          (⟨.rel X, hAr⟩ : RAExpr D Γ n) S t
  | single d =>
      simpa [candidatesRawWith] using
        AssignPlan.mem_leafCandidatesWith_iff strategy
          (⟨.single d, hAr⟩ : RAExpr D Γ n) S t
  | select φ e ih =>
      simpa [candidatesRawWith] using
        AssignPlan.mem_leafCandidatesWith_iff strategy
          (⟨.select φ e, hAr⟩ : RAExpr D Γ n) S t
  | proj idxs e ih =>
      simpa [candidatesRawWith] using
        AssignPlan.mem_leafCandidatesWith_iff strategy
          (⟨.proj idxs e, hAr⟩ : RAExpr D Γ n) S t
  | prod e₁ e₂ ih₁ ih₂ =>
      simpa [candidatesRawWith] using
        AssignPlan.mem_leafCandidatesWith_iff strategy
          (⟨.prod e₁ e₂, hAr⟩ : RAExpr D Γ n) S t
  | union e₁ e₂ ih₁ ih₂ =>
      have hChildren := union_wf e₁ e₂ hAr
      let left : RAExpr D Γ n := ⟨e₁, hChildren.1⟩
      let right : RAExpr D Γ n := ⟨e₂, hChildren.2⟩
      simp only [candidatesRawWith, List.mem_append]
      rw [ih₁ hChildren.1 t,
        ih₂ hChildren.2 t]
      simpa [left, right, RAExpr.union] using
        (RAExpr.mem_eval_union_iff
          left right S.toInstance t).symm
  | diff e₁ e₂ ih₁ ih₂ =>
      simpa [candidatesRawWith] using
        AssignPlan.mem_leafCandidatesWith_iff strategy
          (⟨.diff e₁ e₂, hAr⟩ : RAExpr D Γ n) S t

end UnionPlan

end Whiel

------------------------------------------------------------
-- Union-Root Evaluation Correctness
------------------------------------------------------------

namespace Whiel

namespace UnionPlan

variable {A D : Type}
variable [RelationNames A]
variable [Domain D] [LinearOrder D] [Hashable D]
variable {Γ : UnnamedSchema A}

/- Union-root evaluation preserves every RA denotation. -/
theorem eval_correct
    (e : RAExpr D Γ n)
    (S : FastInstance D Γ) :
    (eval e S).toFinRelation = e.eval S.toInstance := by
  cases hExpr : e.expr with
  | top =>
      simpa [eval, hExpr] using
        AssignPlan.eval_correct e S
  | empty m =>
      simpa [eval, hExpr] using
        AssignPlan.eval_correct e S
  | rel X =>
      simpa [eval, hExpr] using
        AssignPlan.eval_correct e S
  | single d =>
      simpa [eval, hExpr] using
        AssignPlan.eval_correct e S
  | select φ raw =>
      simpa [eval, hExpr] using
        AssignPlan.eval_correct e S
  | proj idxs raw =>
      simpa [eval, hExpr] using
        AssignPlan.eval_correct e S
  | prod raw₁ raw₂ =>
      simpa [eval, hExpr] using
        AssignPlan.eval_correct e S
  | union raw₁ raw₂ =>
      rw [show eval e S =
        FastRelation.ofList
          (candidatesRaw e.expr e.wf S) by
        simp [eval, hExpr]]
      apply Finset.ext
      intro t
      rw [FastRelation.mem_ofList_iff,
        mem_candidatesRaw_iff]
  | diff raw₁ raw₂ =>
      simpa [eval, hExpr] using
        AssignPlan.eval_correct e S

/- Forced union-root evaluation preserves RA denotation. -/
theorem evalWith_correct
    (strategy : AssignPlan.Strategy)
    (e : RAExpr D Γ n)
    (S : FastInstance D Γ) :
    (evalWith strategy e S).toFinRelation =
      e.eval S.toInstance := by
  cases hExpr : e.expr with
  | top =>
      simpa [evalWith, hExpr] using
        AssignPlan.evalWithCandidates_correct strategy e S
  | empty m =>
      simpa [evalWith, hExpr] using
        AssignPlan.evalWithCandidates_correct strategy e S
  | rel X =>
      simpa [evalWith, hExpr] using
        AssignPlan.evalWithCandidates_correct strategy e S
  | single d =>
      simpa [evalWith, hExpr] using
        AssignPlan.evalWithCandidates_correct strategy e S
  | select φ raw =>
      simpa [evalWith, hExpr] using
        AssignPlan.evalWithCandidates_correct strategy e S
  | proj idxs raw =>
      simpa [evalWith, hExpr] using
        AssignPlan.evalWithCandidates_correct strategy e S
  | prod raw₁ raw₂ =>
      simpa [evalWith, hExpr] using
        AssignPlan.evalWithCandidates_correct strategy e S
  | union raw₁ raw₂ =>
      rw [show evalWith strategy e S =
        FastRelation.ofList
          (candidatesRawWith strategy e.expr e.wf S) by
        simp [evalWith, hExpr]]
      apply Finset.ext
      intro t
      rw [FastRelation.mem_ofList_iff,
        mem_candidatesRawWith_iff]
  | diff raw₁ raw₂ =>
      simpa [evalWith, hExpr] using
        AssignPlan.evalWithCandidates_correct strategy e S

end UnionPlan

end Whiel
