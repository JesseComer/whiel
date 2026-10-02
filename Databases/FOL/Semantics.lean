-- Author: Jesse Comer
import Databases.FOL.Syntax
import Databases.FinStruct.Basic

/-
  This file specifies the finite-structure semantics of
  first-order logic.

  Key definitions include:
    * `FOL.Assign`
    * `FOL.Semantics.evalTerm`
    * `FOL.Formula.Sat`
    * `FOL.Sentence.Sat`

  Evaluation of terms requires a non-trivial mutual
  induction on terms and lists of terms (for function
  evaluation). While the correctness of the definition
  of `FOL.Semantics.evalTerm` is clear, we provide the
  theorem `FOL.Semantics.evalTermList_toList` to show
  that `FOL.Semantics.evalTermList` behaves as expected.
-/

------------------------------------------------------------
-- Assignments
------------------------------------------------------------

namespace FOL

variable {A F D : Type}
variable [RelationNames A]
variable [FunctionNames F]
variable [Domain D]
variable {Sig : Signature A F}

/-
  Plain assignments obtained by forgetting carrier proofs.
-/
abbrev PlainAssign
    (D : Type) :=
  Var → D

namespace PlainAssign

/- Update one variable in a plain assignment. -/
def update
    (σ : PlainAssign D)
    (x : Var)
    (v : D) :
    PlainAssign D :=
  fun y => if y = x then v else σ y

end PlainAssign

/- Elements of the carrier of a finite structure. -/
abbrev Elem
    (M : FinStruct D Sig) :=
  {d : D // d ∈ M.carrier}

/- Assignments whose values are always in the carrier. -/
abbrev Assign
    (M : FinStruct D Sig) :=
  Var → Elem M

namespace Assign

/- Forget carrier membership proofs. -/
def toPlain
    {M : FinStruct D Sig}
    (σ : Assign M) :
    PlainAssign D :=
  fun x => (σ x).1

/- Update an assignment. -/
def update
    {M : FinStruct D Sig}
    (σ : Assign M)
    (x : Var)
    (d : Elem M) :
    Assign M :=
  fun y => if y = x then d else σ y

/- Agreement on a finite set of variables. -/
def AgreeOn
    {M : FinStruct D Sig}
    (σ τ : Assign M)
    (S : Finset Var) : Prop :=
  ∀ x ∈ S, (σ x).1 = (τ x).1

@[simp]
theorem toPlain_update
    {M : FinStruct D Sig}
    (σ : Assign M)
    (x : Var)
    (d : Elem M) :
    toPlain (update σ x d) =
      PlainAssign.update (toPlain σ) x d.1 := by
  funext y
  by_cases h : y = x
  · simp [toPlain, update, PlainAssign.update, h]
  · simp [toPlain, update, PlainAssign.update, h]

/-
  Agreement on a larger set implies agreement on a subset.
-/
theorem agreeOn_mono
    {M : FinStruct D Sig}
    {σ τ : Assign M}
    {S T : Finset Var}
    (h : AgreeOn σ τ T)
    (hST : S ⊆ T) :
    AgreeOn σ τ S := by
  intro x hx
  exact h x (hST hx)

/- Updating two agreeing assignments preserves agreement. -/
theorem update_agreeOn
    {M : FinStruct D Sig}
    {σ τ : Assign M}
    {S : Finset Var}
    {x : Var}
    {d : Elem M}
    (h : AgreeOn σ τ (S.erase x)) :
    AgreeOn (update σ x d)
      (update τ x d) S := by
  intro z hz
  by_cases hzX : z = x
  · subst hzX
    simp [update]
  · have hzErase : z ∈ S.erase x :=
      Finset.mem_erase.mpr ⟨hzX, hz⟩
    have hEq : (σ z).1 = (τ z).1 := h z hzErase
    simp [update, hzX, hEq]

end Assign

end FOL

------------------------------------------------------------
-- Term Evaluation
------------------------------------------------------------

namespace FOL

namespace Semantics

variable {A F D : Type}
variable [RelationNames A]
variable [FunctionNames F]
variable [Domain D]
variable {Sig : Signature A F}

mutual
/- Evaluate a term under an assignment. -/
  def evalTerm
      (M : FinStruct D Sig)
      (σ : Assign M) :
      Term Sig → D
  | .var x => (σ x).1
  | .func f args => M.funcs f (evalTermList M σ args)

/- Evaluate an indexed term list into a tuple. -/
  def evalTermList
      (M : FinStruct D Sig)
      (σ : Assign M) :
      {n : Nat} → TermList Sig n → Tuple D n
  | _, .nil =>
      Tuple.empty
  | _, .cons t ts =>
      Vector.ofFn
        (fun i =>
          Fin.cases
            (evalTerm M σ t)
            (fun j => (evalTermList M σ ts).get j)
            i)
end

/-
  Term evaluation against a plain assignment. This is the
  executable core used by the satisfaction decision
  procedure; carrier membership is enforced only when
  quantifiers range over the finite structure carrier.
-/
mutual
/- Evaluate a term under a plain assignment. -/
  private def evalPlainTerm
      (M : FinStruct D Sig)
      (σ : PlainAssign D) :
      Term Sig → D
  | .var x => σ x
  | .func f args =>
      M.funcs f (evalPlainTermList M σ args)

/- Evaluate a term list under a plain assignment. -/
  private def evalPlainTermList
      (M : FinStruct D Sig)
      (σ : PlainAssign D) :
      {n : Nat} → TermList Sig n → Tuple D n
  | _, .nil =>
      Tuple.empty
  | _, .cons t ts =>
      Vector.ofFn
        (fun i =>
          Fin.cases
            (evalPlainTerm M σ t)
            (fun j => (evalPlainTermList M σ ts).get j)
            i)
end

private lemma evalTermList_toList_aux
    (M : FinStruct D Sig)
    (σ : Assign M) :
    {n : Nat} →
      (ts : TermList Sig n) →
        (evalTermList M σ ts).toList =
          ts.toList.map (evalTerm M σ)
| 0, .nil => by
    simp [evalTermList, TermList.toList,
      Vector.toList]
| n + 1, .cons t ts => by
    have hTail := evalTermList_toList_aux M σ ts
    rw [evalTermList, TermList.toList,
      Vector.toList_ofFn, List.ofFn_succ]
    simp only [Fin.cases_zero, Fin.cases_succ,
      List.map_cons]
    rw [show
          (List.ofFn
            (fun j : Fin n =>
              (evalTermList M σ ts).get j)) =
          (evalTermList M σ ts).toList by
      rw [← Vector.toList_ofFn
        (f := fun j : Fin n =>
          (evalTermList M σ ts).get j)]
      have hVec :
          Vector.ofFn
            (fun j : Fin n =>
              (evalTermList M σ ts).get j) =
            evalTermList M σ ts := by
        apply Vector.ext
        intro i hi
        simp [Vector.get, Vector.ofFn]
      exact congrArg (fun v : Tuple D n => v.toList) hVec]
    rw [hTail]

/-
  As a list, evaluating a term list is the same as mapping
  `evalTerm` over the syntactic term list.
-/
theorem evalTermList_toList
    (M : FinStruct D Sig)
    (σ : Assign M)
    {n : Nat}
    (ts : TermList Sig n) :
    (evalTermList M σ ts).toList =
      ts.toList.map (evalTerm M σ) :=
  evalTermList_toList_aux M σ ts

/-
  Evaluating a term list built from a finite function
  agrees pointwise with term evaluation.
-/
lemma evalTermList_ofFn
    (M : FinStruct D Sig)
    (σ : Assign M) :
    {n : Nat} →
      (f : Fin n → Term Sig) →
      evalTermList M σ (TermList.ofFn f) =
        Vector.ofFn (fun i => evalTerm M σ (f i))
| 0, _ => by
    apply Vector.ext
    intro i hi
    omega
| n + 1, f => by
    apply Vector.ext
    intro i hi
    cases i with
    | zero =>
        simp [TermList.ofFn, evalTermList,
          Vector.get, Vector.ofFn]
    | succ i =>
        have hi' : i < n :=
          Nat.succ_lt_succ_iff.mp hi
        let g : Fin n → Term Sig :=
          fun j =>
            f ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩
        have hTail := evalTermList_ofFn M σ g
        have hGet :=
          congrArg
            (fun v : Vector D n =>
              v.get ⟨i, hi'⟩) hTail
        simpa [TermList.ofFn, evalTermList,
          Vector.get, Vector.ofFn, g] using hGet

mutual
/- Term evaluation depends only on term variables. -/
  theorem evalTerm_eq_of_agreeOn_freeVars
      {M : FinStruct D Sig}
      {σ τ : Assign M}
      (t : Term Sig)
      (h : Assign.AgreeOn σ τ t.freeVars) :
      evalTerm M σ t = evalTerm M τ t := by
    cases t with
    | var x =>
        exact h x (by simp [Term.freeVars])
    | func f ts =>
        exact congrArg
          (fun args => M.funcs f args)
          (evalTermList_eq_of_agreeOn_freeVars
            (M := M) (σ := σ) (τ := τ) ts h)

/-
  Term-list evaluation depends only on term-list
  variables.
-/
  theorem evalTermList_eq_of_agreeOn_freeVars
      {M : FinStruct D Sig}
      {σ τ : Assign M} :
      {n : Nat} →
        (ts : TermList Sig n) →
          Assign.AgreeOn σ τ ts.freeVars →
            evalTermList M σ ts =
              evalTermList M τ ts
  | 0, .nil, _h => by
      rfl
  | n + 1, .cons t ts, h => by
      have hHead :
          Assign.AgreeOn σ τ t.freeVars :=
        Assign.agreeOn_mono h
          (by
            intro x hx
            exact Finset.mem_union.mpr
              (Or.inl hx))
      have hTail :
          Assign.AgreeOn σ τ ts.freeVars :=
        Assign.agreeOn_mono h
          (by
            intro x hx
            exact Finset.mem_union.mpr
              (Or.inr hx))
      have hEvalHead :
          evalTerm M σ t = evalTerm M τ t :=
        evalTerm_eq_of_agreeOn_freeVars
          (M := M) (σ := σ) (τ := τ) t hHead
      have hEvalTail :
          evalTermList M σ ts =
            evalTermList M τ ts :=
        evalTermList_eq_of_agreeOn_freeVars
          (M := M) (σ := σ) (τ := τ) ts hTail
      apply Vector.ext
      intro i hi
      cases i with
      | zero =>
          simpa [evalTermList, Vector.get,
            Vector.ofFn] using hEvalHead
      | succ i =>
          have hi' : i < n :=
            Nat.succ_lt_succ_iff.mp hi
          let j : Fin n := ⟨i, hi'⟩
          have hGet :=
            congrArg
              (fun v : Tuple D n => v.get j)
              hEvalTail
          simpa [evalTermList, Vector.get,
            Vector.ofFn, j] using hGet
end

mutual
/-
  Plain term evaluation agrees with carrier-assignment
  evaluation when the assignments agree on the variables
  occurring in the term.
-/
  private theorem evalPlainTerm_eq_evalTerm_of_agreeOn_freeVars
      {M : FinStruct D Sig}
      {σ : PlainAssign D}
      {τ : Assign M}
      (t : Term Sig)
      (h :
        ∀ x ∈ t.freeVars, σ x = (τ x).1) :
      evalPlainTerm M σ t =
        evalTerm M τ t := by
    cases t with
    | var x =>
        exact h x (by simp [Term.freeVars])
    | func f ts =>
        exact congrArg
          (fun args => M.funcs f args)
          (evalPlainTermList_eq_evalTermList_of_agreeOn_freeVars
            (M := M) (σ := σ) (τ := τ) ts h)

/-
  Plain term-list evaluation agrees with carrier-assignment
  evaluation when the assignments agree on the variables
  occurring in the term list.
-/
  private theorem evalPlainTermList_eq_evalTermList_of_agreeOn_freeVars
      {M : FinStruct D Sig}
      {σ : PlainAssign D}
      {τ : Assign M} :
      {n : Nat} →
        (ts : TermList Sig n) →
          (∀ x ∈ ts.freeVars, σ x = (τ x).1) →
            evalPlainTermList M σ ts =
              evalTermList M τ ts
  | 0, .nil, _h => by
      rfl
  | n + 1, .cons t ts, h => by
      have hHead :
          ∀ x ∈ t.freeVars, σ x = (τ x).1 := by
        intro x hx
        exact h x (by
          exact Finset.mem_union.mpr (Or.inl hx))
      have hTail :
          ∀ x ∈ ts.freeVars, σ x = (τ x).1 := by
        intro x hx
        exact h x (by
          exact Finset.mem_union.mpr (Or.inr hx))
      have hEvalHead :
          evalPlainTerm M σ t =
            evalTerm M τ t :=
        evalPlainTerm_eq_evalTerm_of_agreeOn_freeVars
          (M := M) (σ := σ) (τ := τ) t hHead
      have hEvalTail :
          evalPlainTermList M σ ts =
            evalTermList M τ ts :=
        evalPlainTermList_eq_evalTermList_of_agreeOn_freeVars
          (M := M) (σ := σ) (τ := τ) ts hTail
      apply Vector.ext
      intro i hi
      cases i with
      | zero =>
          simpa [evalPlainTermList, evalTermList,
            Vector.get, Vector.ofFn] using hEvalHead
      | succ i =>
          have hi' : i < n :=
            Nat.succ_lt_succ_iff.mp hi
          let j : Fin n := ⟨i, hi'⟩
          have hGet :=
            congrArg
              (fun v : Tuple D n => v.get j)
              hEvalTail
          simpa [evalPlainTermList, evalTermList,
            Vector.get, Vector.ofFn, j] using hGet
end

end Semantics

end FOL

------------------------------------------------------------
-- Formula Satisfaction
------------------------------------------------------------

namespace FOL

namespace Formula

variable {A F D : Type}
variable [RelationNames A]
variable [FunctionNames F]
variable [Domain D]
variable {Sig : Signature A F}

/-
  Satisfaction under assignments into the structure carrier.
-/
def Sat
    (φ : Formula Sig)
    (M : FinStruct D Sig)
    (σ : Assign M) : Prop :=
  match φ with
  | .top => True
  | .bot => False
  | .eq t₁ t₂ =>
    Semantics.evalTerm M σ t₁ =
      Semantics.evalTerm M σ t₂
  | .rel X ts =>
    Semantics.evalTermList M σ ts ∈ M.rels X
  | .and φ ψ =>
    Sat φ M σ ∧ Sat ψ M σ
  | .or φ ψ =>
    Sat φ M σ ∨ Sat ψ M σ
  | .not φ =>
    ¬ Sat φ M σ
  | .imp φ ψ =>
    Sat φ M σ → Sat ψ M σ
  | .iff φ ψ =>
    Sat φ M σ ↔ Sat ψ M σ
  | .forall_ x φ =>
    ∀ d : Elem M, Sat φ M (Assign.update σ x d)
  | .exists_ x φ =>
    ∃ d : Elem M, Sat φ M (Assign.update σ x d)

/-
  Satisfaction against a plain assignment. Quantifiers range
  explicitly over the finite carrier, so this is the
  executable decision path for `Formula.Sat`.
-/
private def PlainSat
    (φ : Formula Sig)
    (M : FinStruct D Sig)
    (σ : PlainAssign D) : Prop :=
  match φ with
  | .top => True
  | .bot => False
  | .eq t₁ t₂ =>
    Semantics.evalPlainTerm M σ t₁ =
      Semantics.evalPlainTerm M σ t₂
  | .rel X ts =>
    Semantics.evalPlainTermList M σ ts ∈ M.rels X
  | .and φ ψ =>
    PlainSat φ M σ ∧ PlainSat ψ M σ
  | .or φ ψ =>
    PlainSat φ M σ ∨ PlainSat ψ M σ
  | .not φ =>
    ¬ PlainSat φ M σ
  | .imp φ ψ =>
    PlainSat φ M σ → PlainSat ψ M σ
  | .iff φ ψ =>
    PlainSat φ M σ ↔ PlainSat ψ M σ
  | .forall_ x φ =>
    ∀ d ∈ M.carrier,
      PlainSat φ M (PlainAssign.update σ x d)
  | .exists_ x φ =>
    ∃ d ∈ M.carrier,
      PlainSat φ M (PlainAssign.update σ x d)

/-
  Executable decidability for plain satisfaction. Universal
  quantifiers are decided by searching for a finite carrier
  counterexample.
-/
private def decidablePlainSat
    (φ : Formula Sig)
    (M : FinStruct D Sig)
    (σ : PlainAssign D) :
    Decidable (φ.PlainSat M σ) :=
  match φ with
  | .top =>
      isTrue (by simp [PlainSat])
  | .bot =>
      isFalse (by simp [PlainSat])
  | .eq _ _ => by
      unfold PlainSat
      infer_instance
  | .rel _ _ => by
      unfold PlainSat
      infer_instance
  | .and φ ψ => by
      haveI : Decidable (PlainSat φ M σ) :=
        decidablePlainSat φ M σ
      haveI : Decidable (PlainSat ψ M σ) :=
        decidablePlainSat ψ M σ
      unfold PlainSat
      infer_instance
  | .or φ ψ => by
      haveI : Decidable (PlainSat φ M σ) :=
        decidablePlainSat φ M σ
      haveI : Decidable (PlainSat ψ M σ) :=
        decidablePlainSat ψ M σ
      unfold PlainSat
      infer_instance
  | .not φ => by
      haveI : Decidable (PlainSat φ M σ) :=
        decidablePlainSat φ M σ
      unfold PlainSat
      infer_instance
  | .imp φ ψ => by
      haveI : Decidable (PlainSat φ M σ) :=
        decidablePlainSat φ M σ
      haveI : Decidable (PlainSat ψ M σ) :=
        decidablePlainSat ψ M σ
      unfold PlainSat
      infer_instance
  | .iff φ ψ => by
      haveI : Decidable (PlainSat φ M σ) :=
        decidablePlainSat φ M σ
      haveI : Decidable (PlainSat ψ M σ) :=
        decidablePlainSat ψ M σ
      unfold PlainSat
      infer_instance
  | .forall_ x φ =>
      let bad : Prop :=
        ∃ d ∈ M.carrier,
          ¬ PlainSat φ M (PlainAssign.update σ x d)
      have hBadDec : Decidable bad := by
        letI :
            DecidablePred
              (fun d =>
                ¬ PlainSat φ M
                  (PlainAssign.update σ x d)) :=
          fun d => by
            haveI :
                Decidable
                  (PlainSat φ M
                    (PlainAssign.update σ x d)) :=
              decidablePlainSat φ M
                (PlainAssign.update σ x d)
            infer_instance
        dsimp [bad]
        infer_instance
      match hBadDec with
      | isTrue hBad =>
          isFalse (by
            intro hAll
            rcases hBad with ⟨d, hd, hNot⟩
            exact hNot (by
              simpa [PlainSat] using hAll d hd))
      | isFalse hNoBad =>
          isTrue (by
            intro d hd
            by_cases hSat :
                PlainSat φ M
                  (PlainAssign.update σ x d)
            · exact hSat
            · exact False.elim
                (hNoBad ⟨d, hd, hSat⟩))
  | .exists_ x φ => by
      have hExistsDec :
          Decidable
            (∃ d ∈ M.carrier,
              PlainSat φ M
                (PlainAssign.update σ x d)) := by
        letI :
            DecidablePred
              (fun d =>
                PlainSat φ M
                  (PlainAssign.update σ x d)) :=
          fun d =>
            decidablePlainSat φ M
              (PlainAssign.update σ x d)
        infer_instance
      unfold PlainSat
      exact hExistsDec

/-
  Plain satisfaction agrees with carrier-assignment
  satisfaction when the assignments agree on free variables.
-/
private theorem plainSat_iff_sat_of_agreeOn_freeVars
    {M : FinStruct D Sig}
    {σ : PlainAssign D}
    {τ : Assign M}
    (φ : Formula Sig)
    (h :
      ∀ x ∈ φ.freeVars, σ x = (τ x).1) :
    φ.PlainSat M σ ↔
      φ.Sat M τ := by
  induction φ generalizing σ τ with
  | top =>
      simp [PlainSat, Sat]
  | bot =>
      simp [PlainSat, Sat]
  | eq t₁ t₂ =>
      have h₁ :
          Semantics.evalPlainTerm M σ t₁ =
            Semantics.evalTerm M τ t₁ :=
        Semantics.evalPlainTerm_eq_evalTerm_of_agreeOn_freeVars
          (M := M) (σ := σ) (τ := τ) t₁
          (by
            intro x hx
            exact h x (by
              exact Finset.mem_union.mpr (Or.inl hx)))
      have h₂ :
          Semantics.evalPlainTerm M σ t₂ =
            Semantics.evalTerm M τ t₂ :=
        Semantics.evalPlainTerm_eq_evalTerm_of_agreeOn_freeVars
          (M := M) (σ := σ) (τ := τ) t₂
          (by
            intro x hx
            exact h x (by
              exact Finset.mem_union.mpr (Or.inr hx)))
      simp [PlainSat, Sat, h₁, h₂]
  | rel X ts =>
      have hTs :
          Semantics.evalPlainTermList M σ ts =
            Semantics.evalTermList M τ ts :=
        Semantics.evalPlainTermList_eq_evalTermList_of_agreeOn_freeVars
          (M := M) (σ := σ) (τ := τ) ts h
      simp [PlainSat, Sat, hTs]
  | and φ ψ hφ hψ =>
      have hLeft :
          φ.PlainSat M σ ↔ φ.Sat M τ :=
        hφ
          (by
            intro x hx
            exact h x (by
              exact Finset.mem_union.mpr (Or.inl hx)))
      have hRight :
          ψ.PlainSat M σ ↔ ψ.Sat M τ :=
        hψ
          (by
            intro x hx
            exact h x (by
              exact Finset.mem_union.mpr (Or.inr hx)))
      simp [PlainSat, Sat, hLeft, hRight]
  | or φ ψ hφ hψ =>
      have hLeft :
          φ.PlainSat M σ ↔ φ.Sat M τ :=
        hφ
          (by
            intro x hx
            exact h x (by
              exact Finset.mem_union.mpr (Or.inl hx)))
      have hRight :
          ψ.PlainSat M σ ↔ ψ.Sat M τ :=
        hψ
          (by
            intro x hx
            exact h x (by
              exact Finset.mem_union.mpr (Or.inr hx)))
      simp [PlainSat, Sat, hLeft, hRight]
  | not φ hφ =>
      have hBody :
          φ.PlainSat M σ ↔ φ.Sat M τ := hφ h
      simp [PlainSat, Sat, hBody]
  | imp φ ψ hφ hψ =>
      have hLeft :
          φ.PlainSat M σ ↔ φ.Sat M τ :=
        hφ
          (by
            intro x hx
            exact h x (by
              exact Finset.mem_union.mpr (Or.inl hx)))
      have hRight :
          ψ.PlainSat M σ ↔ ψ.Sat M τ :=
        hψ
          (by
            intro x hx
            exact h x (by
              exact Finset.mem_union.mpr (Or.inr hx)))
      simp [PlainSat, Sat, hLeft, hRight]
  | iff φ ψ hφ hψ =>
      have hLeft :
          φ.PlainSat M σ ↔ φ.Sat M τ :=
        hφ
          (by
            intro x hx
            exact h x (by
              exact Finset.mem_union.mpr (Or.inl hx)))
      have hRight :
          ψ.PlainSat M σ ↔ ψ.Sat M τ :=
        hψ
          (by
            intro x hx
            exact h x (by
              exact Finset.mem_union.mpr (Or.inr hx)))
      simp [PlainSat, Sat, hLeft, hRight]
  | forall_ x φ hφ =>
      constructor
      · intro hAll d
        have hAgree :
            ∀ y ∈ φ.freeVars,
              (PlainAssign.update σ x d.1) y =
                ((Assign.update τ x d) y).1 := by
          intro y hy
          by_cases hyx : y = x
          · subst hyx
            simp [PlainAssign.update, Assign.update]
          · have hyErase : y ∈ φ.freeVars.erase x :=
              Finset.mem_erase.mpr ⟨hyx, hy⟩
            have hEq := h y hyErase
            simp [PlainAssign.update, Assign.update, hyx, hEq]
        exact
          (hφ hAgree).mp
            (hAll d.1 d.2)
      · intro hAll d hd
        have hAgree :
            ∀ y ∈ φ.freeVars,
              (PlainAssign.update σ x d) y =
                ((Assign.update τ x ⟨d, hd⟩) y).1 := by
          intro y hy
          by_cases hyx : y = x
          · subst hyx
            simp [PlainAssign.update, Assign.update]
          · have hyErase : y ∈ φ.freeVars.erase x :=
              Finset.mem_erase.mpr ⟨hyx, hy⟩
            have hEq := h y hyErase
            simp [PlainAssign.update, Assign.update, hyx, hEq]
        exact
          (hφ hAgree).mpr
            (hAll ⟨d, hd⟩)
  | exists_ x φ hφ =>
      constructor
      · rintro ⟨d, hd, hSat⟩
        refine ⟨⟨d, hd⟩, ?_⟩
        have hAgree :
            ∀ y ∈ φ.freeVars,
              (PlainAssign.update σ x d) y =
                ((Assign.update τ x ⟨d, hd⟩) y).1 := by
          intro y hy
          by_cases hyx : y = x
          · subst hyx
            simp [PlainAssign.update, Assign.update]
          · have hyErase : y ∈ φ.freeVars.erase x :=
              Finset.mem_erase.mpr ⟨hyx, hy⟩
            have hEq := h y hyErase
            simp [PlainAssign.update, Assign.update, hyx, hEq]
        exact (hφ hAgree).mp hSat
      · rintro ⟨d, hSat⟩
        refine ⟨d.1, d.2, ?_⟩
        have hAgree :
            ∀ y ∈ φ.freeVars,
              (PlainAssign.update σ x d.1) y =
                ((Assign.update τ x d) y).1 := by
          intro y hy
          by_cases hyx : y = x
          · subst hyx
            simp [PlainAssign.update, Assign.update]
          · have hyErase : y ∈ φ.freeVars.erase x :=
              Finset.mem_erase.mpr ⟨hyx, hy⟩
            have hEq := h y hyErase
            simp [PlainAssign.update, Assign.update, hyx, hEq]
        exact (hφ hAgree).mpr hSat

/-
  Plain satisfaction with `Assign.toPlain` is equivalent
  to the original carrier-assignment semantics.
-/
private theorem plainSat_toPlain_iff_sat
    (φ : Formula Sig)
    (M : FinStruct D Sig)
    (σ : Assign M) :
    φ.PlainSat M σ.toPlain ↔
      φ.Sat M σ :=
  plainSat_iff_sat_of_agreeOn_freeVars
    (M := M) (σ := σ.toPlain) (τ := σ) φ
    (by
      intro x _hx
      rfl)

instance
    (φ : Formula Sig)
    (M : FinStruct D Sig)
    (σ : Assign M) :
    Decidable (φ.Sat M σ) :=
  by
    letI : Decidable (φ.PlainSat M σ.toPlain) :=
      decidablePlainSat φ M σ.toPlain
    exact
      decidable_of_iff
        (φ.PlainSat M σ.toPlain)
        (plainSat_toPlain_iff_sat φ M σ)

/-
  Satisfaction of a finite disjunction is satisfaction of
  one listed disjunct.
-/
theorem sat_disjoin_iff
    (φs : List (Formula Sig))
    (M : FinStruct D Sig)
    (σ : Assign M) :
    (Formula.disjoin φs).Sat M σ ↔
      ∃ φ ∈ φs, φ.Sat M σ := by
  induction φs with
  | nil =>
      simp [Formula.disjoin, Formula.Sat]
  | cons φ φs ih =>
      simp [Formula.disjoin, Formula.Sat, ih]

/-
  A list-existential can be satisfied by any assignment
  that agrees with the ambient assignment outside the
  quantified variables.
-/
theorem sat_existsMany_of_assignment
    (xs : List Var)
    {φ : Formula Sig}
    {M : FinStruct D Sig}
    {σ τ : Assign M}
    (hAgree : ∀ y, y ∉ xs → τ y = σ y)
    (hSat : φ.Sat M τ) :
    (Formula.existsMany xs φ).Sat M σ := by
  induction xs generalizing σ with
  | nil =>
      have hEq : τ = σ := by
        funext y
        exact hAgree y (by simp)
      simpa [Formula.existsMany, hEq] using hSat
  | cons x xs ih =>
      change
        ∃ d : Elem M,
          (Formula.existsMany xs φ).Sat M
            (Assign.update σ x d)
      refine ⟨τ x, ?_⟩
      apply ih (σ := Assign.update σ x (τ x))
      · intro y hy
        by_cases hyx : y = x
        · subst y
          simp [Assign.update]
        · have hyCons : y ∉ x :: xs := by
            intro hMem
            cases List.mem_cons.mp hMem with
            | inl hEq => exact hyx hEq
            | inr hTail => exact hy hTail
          have hEq := hAgree y hyCons
          simp [Assign.update, hyx, hEq]

/-
  A satisfying assignment for a list-existential can be
  extracted as an assignment for the body, agreeing outside
  the quantified variables.
-/
theorem exists_assignment_of_sat_existsMany
    (xs : List Var)
    {φ : Formula Sig}
    {M : FinStruct D Sig}
    {σ : Assign M}
    (hSat : (Formula.existsMany xs φ).Sat M σ) :
    ∃ τ : Assign M,
      (∀ y, y ∉ xs → τ y = σ y) ∧
        φ.Sat M τ := by
  induction xs generalizing σ with
  | nil =>
      refine ⟨σ, ?_, ?_⟩
      · intro y _hy
        rfl
      · simpa [Formula.existsMany] using hSat
  | cons x xs ih =>
      change
        ∃ d : Elem M,
          (Formula.existsMany xs φ).Sat M
            (Assign.update σ x d) at hSat
      rcases hSat with ⟨d, hTail⟩
      rcases ih (σ := Assign.update σ x d) hTail with
        ⟨τ, hAgree, hBody⟩
      refine ⟨τ, ?_, hBody⟩
      intro y hy
      have hyTail : y ∉ xs := by
        intro hMem
        exact hy (List.mem_cons_of_mem x hMem)
      have hyx : y ≠ x := by
        intro hEq
        exact hy (by simp [hEq])
      have hEq := hAgree y hyTail
      simpa [Assign.update, hyx] using hEq

/- Semantic characterization of list-existentials. -/
theorem sat_existsMany_iff_assignment
    (xs : List Var)
    {φ : Formula Sig}
    {M : FinStruct D Sig}
    {σ : Assign M} :
    (Formula.existsMany xs φ).Sat M σ ↔
      ∃ τ : Assign M,
        (∀ y, y ∉ xs → τ y = σ y) ∧
          φ.Sat M τ := by
  constructor
  · exact exists_assignment_of_sat_existsMany xs
  · rintro ⟨τ, hAgree, hSat⟩
    exact sat_existsMany_of_assignment xs hAgree hSat

/- Satisfaction depends only on the free variables. -/
theorem sat_eq_of_agreeOn_freeVars
    {M : FinStruct D Sig}
    {σ τ : Assign M}
    (φ : Formula Sig)
    (h : Assign.AgreeOn σ τ φ.freeVars) :
    φ.Sat M σ ↔
      φ.Sat M τ := by
  induction φ generalizing σ τ with
  | top =>
      simp [Formula.Sat]
  | bot =>
      simp [Formula.Sat]
  | eq t1 t2 =>
      have h1 :
          Assign.AgreeOn σ τ t1.freeVars :=
        Assign.agreeOn_mono h
          (by
            intro x hx
            exact Finset.mem_union.mpr
              (Or.inl hx))
      have h2 :
          Assign.AgreeOn σ τ t2.freeVars :=
        Assign.agreeOn_mono h
          (by
            intro x hx
            exact Finset.mem_union.mpr
              (Or.inr hx))
      simp [Formula.Sat,
        Semantics.evalTerm_eq_of_agreeOn_freeVars
          (t := t1) h1,
        Semantics.evalTerm_eq_of_agreeOn_freeVars
          (t := t2) h2]
  | rel X ts =>
      have hTs :
          Semantics.evalTermList M σ ts =
            Semantics.evalTermList M τ ts :=
        Semantics.evalTermList_eq_of_agreeOn_freeVars
          (ts := ts) h
      simp [Formula.Sat, hTs]
  | and φ ψ ihφ ihψ =>
      have hφ :
          φ.Sat M σ ↔ φ.Sat M τ :=
        ihφ
          (Assign.agreeOn_mono h
            (by
              intro x hx
              exact Finset.mem_union.mpr
                (Or.inl hx)))
      have hψ :
          ψ.Sat M σ ↔ ψ.Sat M τ :=
        ihψ
          (Assign.agreeOn_mono h
            (by
              intro x hx
              exact Finset.mem_union.mpr
                (Or.inr hx)))
      simp [Formula.Sat, hφ, hψ]
  | or φ ψ ihφ ihψ =>
      have hφ :
          φ.Sat M σ ↔ φ.Sat M τ :=
        ihφ
          (Assign.agreeOn_mono h
            (by
              intro x hx
              exact Finset.mem_union.mpr
                (Or.inl hx)))
      have hψ :
          ψ.Sat M σ ↔ ψ.Sat M τ :=
        ihψ
          (Assign.agreeOn_mono h
            (by
              intro x hx
              exact Finset.mem_union.mpr
                (Or.inr hx)))
      simp [Formula.Sat, hφ, hψ]
  | not φ ih =>
      have hφ :
          φ.Sat M σ ↔ φ.Sat M τ := ih h
      simp [Formula.Sat, hφ]
  | imp φ ψ ihφ ihψ =>
      have hφ :
          φ.Sat M σ ↔ φ.Sat M τ :=
        ihφ
          (Assign.agreeOn_mono h
            (by
              intro x hx
              exact Finset.mem_union.mpr
                (Or.inl hx)))
      have hψ :
          ψ.Sat M σ ↔ ψ.Sat M τ :=
        ihψ
          (Assign.agreeOn_mono h
            (by
              intro x hx
              exact Finset.mem_union.mpr
                (Or.inr hx)))
      simp [Formula.Sat, hφ, hψ]
  | iff φ ψ ihφ ihψ =>
      have hφ :
          φ.Sat M σ ↔ φ.Sat M τ :=
        ihφ
          (Assign.agreeOn_mono h
            (by
              intro x hx
              exact Finset.mem_union.mpr
                (Or.inl hx)))
      have hψ :
          ψ.Sat M σ ↔ ψ.Sat M τ :=
        ihψ
          (Assign.agreeOn_mono h
            (by
              intro x hx
              exact Finset.mem_union.mpr
                (Or.inr hx)))
      simp [Formula.Sat, hφ, hψ]
  | forall_ x φ ih =>
      constructor
      · intro hSat d
        have hUpd :
            Assign.AgreeOn
              (Assign.update σ x d)
              (Assign.update τ x d)
              φ.freeVars :=
          Assign.update_agreeOn
            (σ := σ) (τ := τ)
            (S := φ.freeVars)
            (x := x) (d := d) h
        exact
          (ih (σ := Assign.update σ x d)
            (τ := Assign.update τ x d)
            hUpd).mp (hSat d)
      · intro hSat d
        have hUpd :
            Assign.AgreeOn
              (Assign.update σ x d)
              (Assign.update τ x d)
              φ.freeVars :=
          Assign.update_agreeOn
            (σ := σ) (τ := τ)
            (S := φ.freeVars)
            (x := x) (d := d) h
        exact
          (ih (σ := Assign.update σ x d)
            (τ := Assign.update τ x d)
            hUpd).mpr (hSat d)
  | exists_ x φ ih =>
      constructor
      · rintro ⟨d, hSat⟩
        refine ⟨d, ?_⟩
        have hUpd :
            Assign.AgreeOn
              (Assign.update σ x d)
              (Assign.update τ x d)
              φ.freeVars :=
          Assign.update_agreeOn
            (σ := σ) (τ := τ)
            (S := φ.freeVars)
            (x := x) (d := d) h
        exact
          (ih (σ := Assign.update σ x d)
            (τ := Assign.update τ x d)
            hUpd).mp hSat
      · rintro ⟨d, hSat⟩
        refine ⟨d, ?_⟩
        have hUpd :
            Assign.AgreeOn
              (Assign.update σ x d)
              (Assign.update τ x d)
              φ.freeVars :=
          Assign.update_agreeOn
            (σ := σ) (τ := τ)
            (S := φ.freeVars)
            (x := x) (d := d) h
        exact
          (ih (σ := Assign.update σ x d)
            (τ := Assign.update τ x d)
            hUpd).mpr hSat

/- Satisfaction of a sentence is assignment-independent. -/
theorem sat_eq_of_isSentence
    {M : FinStruct D Sig}
    {σ τ : Assign M}
    (φ : Formula Sig)
    (h : φ.IsSentence) :
    φ.Sat M σ ↔
      φ.Sat M τ := by
  apply Formula.sat_eq_of_agreeOn_freeVars
  intro x hx
  rw [h] at hx
  simp at hx

end Formula

end FOL

------------------------------------------------------------
-- Sentence Satisfaction
------------------------------------------------------------

namespace FOL

namespace Sentence

variable {A F D : Type}
variable [RelationNames A]
variable [FunctionNames F]
variable [Domain D]
variable {Sig : Signature A F}

/-
  Assignment-free satisfaction for first-order sentences.
-/
def Sat
    (φ : FOL.Sentence Sig)
    (M : FinStruct D Sig) : Prop :=
  ∀ σ : Assign M, φ.1.Sat M σ

/- Sentence satisfaction is equivalent to any assignment. -/
theorem sat_iff
    (φ : FOL.Sentence Sig)
    (M : FinStruct D Sig)
    (σ : Assign M) :
    φ.Sat M ↔
      φ.1.Sat M σ := by
  constructor
  · intro h
    exact h σ
  · intro h τ
    exact
      (Formula.sat_eq_of_isSentence
        (M := M) (σ := σ) (τ := τ)
        φ.1 φ.2).mp h

/-
  Plain satisfaction of a closed formula is equivalent to
  sentence satisfaction, for any ambient plain assignment.
-/
private theorem plainSat_iff
    (φ : FOL.Sentence Sig)
    (M : FinStruct D Sig)
    (σ : PlainAssign D) :
    φ.1.PlainSat M σ ↔
      φ.Sat M := by
  constructor
  · intro hPlain τ
    have hAgree :
        ∀ x ∈ φ.1.freeVars, σ x = (τ x).1 := by
      intro x hx
      rw [φ.2] at hx
      simp at hx
    exact
      (Formula.plainSat_iff_sat_of_agreeOn_freeVars
        (M := M) (σ := σ) (τ := τ) φ.1 hAgree).mp
        hPlain
  · intro hSat
    rcases M.carrier_nonempty with ⟨d, hd⟩
    let τ : Assign M := fun _ => ⟨d, hd⟩
    have hAgree :
        ∀ x ∈ φ.1.freeVars, σ x = (τ x).1 := by
      intro x hx
      rw [φ.2] at hx
      simp at hx
    exact
      (Formula.plainSat_iff_sat_of_agreeOn_freeVars
        (M := M) (σ := σ) (τ := τ) φ.1 hAgree).mpr
        (hSat τ)

instance
    (φ : FOL.Sentence Sig)
    (M : FinStruct D Sig) :
    Decidable (φ.Sat M) :=
  by
    let σ : PlainAssign D := fun _ => default
    letI : Decidable (φ.1.PlainSat M σ) :=
      Formula.decidablePlainSat φ.1 M σ
    exact
      decidable_of_iff
        (φ.1.PlainSat M σ)
        (plainSat_iff φ M σ)

end Sentence

end FOL
