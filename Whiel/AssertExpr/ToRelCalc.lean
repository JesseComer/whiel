-- Author: Jesse Comer
import Whiel.AssertExpr.Entailment
import Databases.UnnamedRA.ToRelCalc
import Databases.RelCalc.DomainIndependence

/-
  Translation from quantifier-free assertions to RelCalc.

  Key declarations:
    * `Whiel.QFAssertExpr.toRelCalc`
    * `Whiel.QFAssertExpr.toRelCalcSentence`
    * `QFEntailment.toRelCalcEntailment`
    * `Whiel.AssertExpr.entailmentToQFEntailmentOfNoBound`

  Key theorem:
    * `Whiel.QFAssertExpr.toRelCalc_correct`
    * `QFEntailment.valid_of_toRelCalc`
    * `Whiel.AssertExpr.
  entailmentToQFEntailmentOfNoBound_sound`

  Equality and containment atoms are translated by first
  translating the two RA expressions to RelCalc queries and
  then universally closing the shared output-variable block.
-/

open UnnamedRA.ToRelCalc

------------------------------------------------------------
-- QF Assertion to RelCalc Syntax Translation
------------------------------------------------------------

namespace RelCalc

namespace Formula

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- Universal closure over a canonical variable block. -/
lemma holdsIn_forallMany_block_iff
    {Q : Set D}
    {I : Instance D Γ}
    {σ : Assign D}
    (start : Nat)
    {n : Nat}
    (φ : Formula D Γ) :
    Formula.ArbitraryAssignSatIn Q I σ
      (Formula.forallMany (Var.block start n) φ) ↔
      ∀ t : Tuple D n,
        Tuple.MapsInto t Q →
          Formula.ArbitraryAssignSatIn Q I
            (BlockAssign.withBlock σ start t) φ := by
  induction n generalizing start σ with
  | zero =>
      let t0 : Tuple D 0 := Tuple.empty
      have hWith :
          BlockAssign.withBlock σ start t0 = σ := by
        funext x
        simp [BlockAssign.withBlock, t0]
      constructor
      · intro hSat t _ht
        have ht0 : t = t0 := by
          apply Vector.ext
          intro i hi
          exact (Nat.not_lt_zero _ hi).elim
        simpa [Var.block_zero, Formula.forallMany,
          ht0, hWith] using hSat
      · intro hSat
        have hQ : Tuple.MapsInto t0 Q := by
          intro i
          exact Fin.elim0 i
        simpa [Var.block_zero, Formula.forallMany,
          hWith] using hSat t0 hQ
  | succ n ih =>
      constructor
      · intro hSat t ht
        let d : D := t[0]
        let u : Tuple D n := Tuple.tail t
        have hdQ : Q d := by
          simpa [d] using ht ⟨0, by omega⟩
        have hUQ : Tuple.MapsInto u Q := by
          intro j
          simpa [u, Tuple.tail, Vector.get,
            Vector.ofFn] using
            ht ⟨j.1 + 1, by omega⟩
        have hSat' :
            ∀ d ∈ Q,
              Formula.ArbitraryAssignSatIn Q I
                (Assign.update σ start d)
                (Formula.forallMany
                  (Var.block (start + 1) n) φ) := by
          simpa [Var.block_succ, Formula.forallMany,
            Formula.ArbitraryAssignSatIn] using hSat
        have hTail :
            Formula.ArbitraryAssignSatIn Q I
              (Assign.update σ start d)
              (Formula.forallMany
                (Var.block (start + 1) n) φ) :=
          hSat' d hdQ
        have hBody :
            Formula.ArbitraryAssignSatIn Q I
              (BlockAssign.withBlock
                (Assign.update σ start d)
                (start + 1) u) φ :=
          (ih
            (σ := Assign.update σ start d)
            (start := start + 1)).1 hTail u hUQ
        have htEq : Tuple.cons d u = t := by
          simpa [d, u] using Tuple.cons_tail t
        rw [← htEq]
        rw [BlockAssign.withBlock_cons]
        exact hBody
      · intro hSat
        have hAll :
            ∀ d ∈ Q,
              Formula.ArbitraryAssignSatIn Q I
                (Assign.update σ start d)
                (Formula.forallMany
                  (Var.block (start + 1) n) φ) := by
          intro d hdQ
          apply (ih
            (σ := Assign.update σ start d)
            (start := start + 1)).2
          intro u hUQ
          let t : Tuple D (n + 1) := Tuple.cons d u
          have hTQ : Tuple.MapsInto t Q := by
            intro i
            cases i using Fin.cases with
            | zero =>
                simpa [t] using
                  (show Q ((Tuple.cons d u)[0]) from by
                    rw [Tuple.get_cons_zero]
                    exact hdQ)
            | succ j =>
                simpa [t] using
                  (show Q ((Tuple.cons d u)[j.1 + 1]) from by
                    rw [Tuple.get_cons_succ]
                    exact hUQ j)
          have hBody := hSat t hTQ
          simpa [t, BlockAssign.withBlock_cons] using hBody
        simpa [Var.block_succ, Formula.forallMany,
          Formula.ArbitraryAssignSatIn] using hAll

end Formula

end RelCalc

namespace Whiel

namespace QFAssertExpr

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- Universal closure over the canonical RA output block. -/
def closeBlock
    (n : Nat)
    (φ : RelCalc.Formula D Γ) :
    RelCalc.Formula D Γ :=
  RelCalc.Formula.forallMany (Var.block 0 n) φ

/- Translate an equality atom to RelCalc. -/
def eqAtom
    {n : Nat}
    (e₁ e₂ : RAExpr D Γ n) :
    RelCalc.Formula D Γ :=
  closeBlock n
    (.iff e₁.toRelCalcQuery.form
      e₂.toRelCalcQuery.form)

/- Translate a containment atom to RelCalc. -/
def subsetAtom
    {n : Nat}
    (e₁ e₂ : RAExpr D Γ n) :
    RelCalc.Formula D Γ :=
  closeBlock n
    (.imp e₁.toRelCalcQuery.form
      e₂.toRelCalcQuery.form)

/- Translate a QF assertion to a RelCalc formula. -/
def toRelCalc :
    QFAssertExpr D Γ → RelCalc.Formula D Γ
| .«true» => .top
| .«false» => .bot
| .eq e₁ e₂ => eqAtom e₁ e₂
| .subset e₁ e₂ => subsetAtom e₁ e₂
| .and φ ψ => .and (toRelCalc φ) (toRelCalc ψ)
| .or φ ψ => .or (toRelCalc φ) (toRelCalc ψ)
| .not φ => .not (toRelCalc φ)

/- The translation preserves the set of constants. -/
theorem toRelCalc_constants
    (φ : QFAssertExpr D Γ) :
    φ.toRelCalc.constants = φ.constants := by
  induction φ with
  | «true» =>
      rfl
  | «false» =>
      rfl
  | eq e₁ e₂ =>
      change (eqAtom e₁ e₂).constants =
        e₁.constants ∪ e₂.constants
      rw [eqAtom, closeBlock,
        RelCalc.Formula.constants_forallMany]
      change
        e₁.toRelCalcQuery.form.constants ∪
          e₂.toRelCalcQuery.form.constants =
        e₁.constants ∪ e₂.constants
      change
        e₁.toRelCalcQuery.constants ∪
          e₂.toRelCalcQuery.constants =
        e₁.constants ∪ e₂.constants
      rw [RAExpr.toRelCalcQuery_constants e₁,
        RAExpr.toRelCalcQuery_constants e₂]
  | subset e₁ e₂ =>
      change (subsetAtom e₁ e₂).constants =
        e₁.constants ∪ e₂.constants
      rw [subsetAtom, closeBlock,
        RelCalc.Formula.constants_forallMany]
      change
        e₁.toRelCalcQuery.form.constants ∪
          e₂.toRelCalcQuery.form.constants =
        e₁.constants ∪ e₂.constants
      change
        e₁.toRelCalcQuery.constants ∪
          e₂.toRelCalcQuery.constants =
        e₁.constants ∪ e₂.constants
      rw [RAExpr.toRelCalcQuery_constants e₁,
        RAExpr.toRelCalcQuery_constants e₂]
  | and φ ψ ihφ ihψ =>
      change (toRelCalc φ).constants ∪
          (toRelCalc ψ).constants =
        φ.constants ∪ ψ.constants
      rw [ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      change (toRelCalc φ).constants ∪
          (toRelCalc ψ).constants =
        φ.constants ∪ ψ.constants
      rw [ihφ, ihψ]
  | not φ ih =>
      exact ih

private lemma contains_left
    {n : Nat}
    (e₁ e₂ : RAExpr D Γ n)
    {Q : Set D}
    {I : Instance D Γ}
    (hQ :
      (↑(I.Adom ∪ (e₁.constants ∪ e₂.constants)) :
        Set D) ⊆ Q) :
    (↑(I.Adom ∪ e₁.constants) : Set D) ⊆ Q := by
  intro d hd
  apply hQ
  change d ∈ I.Adom ∪ e₁.constants at hd
  change d ∈ I.Adom ∪ (e₁.constants ∪ e₂.constants)
  rw [Finset.mem_union] at hd ⊢
  cases hd with
  | inl h =>
      exact Or.inl h
  | inr h =>
      exact Or.inr (Finset.mem_union.mpr (Or.inl h))

private lemma contains_right
    {n : Nat}
    (e₁ e₂ : RAExpr D Γ n)
    {Q : Set D}
    {I : Instance D Γ}
    (hQ :
      (↑(I.Adom ∪ (e₁.constants ∪ e₂.constants)) :
        Set D) ⊆ Q) :
    (↑(I.Adom ∪ e₂.constants) : Set D) ⊆ Q := by
  intro d hd
  apply hQ
  change d ∈ I.Adom ∪ e₂.constants at hd
  change d ∈ I.Adom ∪ (e₁.constants ∪ e₂.constants)
  rw [Finset.mem_union] at hd ⊢
  cases hd with
  | inl h =>
      exact Or.inl h
  | inr h =>
      exact Or.inr (Finset.mem_union.mpr (Or.inr h))

private lemma erase_block_self
    (n : Nat) :
    (Var.block 0 n).foldr
      (fun x S => S.erase x)
      (Var.block 0 n).toFinset = ∅ := by
  simpa using
    foldr_erase_list_union
      (Var.block 0 n) ∅
      (Var.nodup_block 0 n)
      (by simp)

private lemma query_freeVars
    {n : Nat}
    (e : RAExpr D Γ n) :
    e.toRelCalcQuery.form.freeVars =
      (Var.block 0 n).toFinset := by
  have h := e.toRelCalcQuery.freeVars_eq
  simpa [RAExpr.toRelCalcQuery,
    blockVector_toList] using h

private lemma query_sat_onBlock_iff
    {n : Nat}
    (e : RAExpr D Γ n)
    (Q : Set D)
    (I : Instance D Γ)
    (t : Tuple D n)
    (hQ : (↑(I.Adom ∪ e.constants) : Set D) ⊆ Q)
    (ht : Tuple.MapsInto t Q) :
    e.toRelCalcQuery.form.SatIn I
      (BlockAssign.onBlock 0 t) Q ↔
      t ∈ e.eval I := by
  let φ :=
    RAExpr.toRelCalcFormula
      (A := A) (D := D) (Γ := Γ) e
  have hφ :
      RawRAExpr.toRelCalcFormula? Γ 0 e.expr = some φ :=
    RAExpr.toRelCalcFormula?_total
      (A := A) (D := D) (Γ := Γ) e
  have hRawEval :
      e.expr.eval? (Γ := Γ) I =
        some ⟨n, e.eval I⟩ :=
    RAExpr.raw_eval?_eq_eval e I
  constructor
  · intro hSat
    have hAns :
        e.expr.answerContains I t :=
      (RawRAExpr.toRelCalcFormula?_answerContains_iff_satIn
        (A := A) (D := D) (Γ := Γ)
        (start := 0) (n := n)
        (e := e.expr) (φ := φ)
        e.wf hφ Q I t hQ ht).2
        (by simpa [RAExpr.toRelCalcQuery, φ] using hSat)
    exact (RawRAExpr.answer_iff_of_eval hRawEval t).1 hAns
  · intro htEval
    have hAns :
        e.expr.answerContains I t :=
      (RawRAExpr.answer_iff_of_eval hRawEval t).2 htEval
    have hFormula :
        φ.SatIn I
          (BlockAssign.onBlock 0 t) Q :=
      (RawRAExpr.toRelCalcFormula?_answerContains_iff_satIn
        (A := A) (D := D) (Γ := Γ)
        (start := 0) (n := n)
        (e := e.expr) (φ := φ)
        e.wf hφ Q I t hQ ht).1 hAns
    simpa [RAExpr.toRelCalcQuery, φ] using hFormula

private lemma query_sat_withBlock_iff
    {n : Nat}
    (e : RAExpr D Γ n)
    (Q : Set D)
    (I : Instance D Γ)
    (σ : Assign D)
    (t : Tuple D n)
    (hQ : (↑(I.Adom ∪ e.constants) : Set D) ⊆ Q)
    (ht : Tuple.MapsInto t Q) :
    e.toRelCalcQuery.form.SatIn I
      (BlockAssign.withBlock σ 0 t) Q ↔
      t ∈ e.eval I := by
  have hAgree :
      Assign.AgreeOn
        (BlockAssign.withBlock σ 0 t)
        (BlockAssign.onBlock 0 t)
        e.toRelCalcQuery.form.freeVars := by
    have hBlock :=
      BlockAssign.withBlock_agreeOn_onBlock
        σ 0 t
    simpa [query_freeVars e] using hBlock
  exact
    (RelCalc.Formula.satIn_eq_of_agreeOn_freeVars
      (Q := Q) (I := I)
      (φ := e.toRelCalcQuery.form)
      (σ := BlockAssign.withBlock σ 0 t)
      (τ := BlockAssign.onBlock 0 t)
      hAgree).trans
        (query_sat_onBlock_iff e Q I t hQ ht)

private lemma query_holds_withBlock_iff
    {n : Nat}
    (e : RAExpr D Γ n)
    (Q : Set D)
    (I : Instance D Γ)
    (σ : Assign D)
    (t : Tuple D n)
    (hQ : (↑(I.Adom ∪ e.constants) : Set D) ⊆ Q)
    (ht : Tuple.MapsInto t Q) :
    RelCalc.Formula.ArbitraryAssignSatIn Q I
      (BlockAssign.withBlock σ 0 t)
      e.toRelCalcQuery.form ↔
      t ∈ e.eval I := by
  have hMaps :
      Assign.MapsInto
        (BlockAssign.withBlock σ 0 t)
        e.toRelCalcQuery.form.freeVars Q := by
    have hBlock :=
      BlockAssign.mapsInto_withBlock
        (D := D) σ 0 ht
    simpa [query_freeVars e] using hBlock
  constructor
  · intro hHolds
    exact (query_sat_withBlock_iff
      e Q I σ t hQ ht).mp ⟨hMaps, hHolds⟩
  · intro htEval
    exact ((query_sat_withBlock_iff
      e Q I σ t hQ ht).mpr htEval).2

private lemma eval_tuple_over_adom
    {n : Nat}
    (e : RAExpr D Γ n)
    (I : Instance D Γ)
    {t : Tuple D n}
    (ht : t ∈ e.eval I) :
    t.isTupleOver (I.Adom ∪ e.constants) := by
  have hRawEval :
      e.expr.eval? (Γ := Γ) I =
        some ⟨n, e.eval I⟩ :=
    RAExpr.raw_eval?_eq_eval e I
  have hAns :
      e.expr.answerContains I t :=
    (RawRAExpr.answer_iff_of_eval hRawEval t).2 ht
  exact RawRAExpr.answer_over_adom
    (A := A) (D := D) (Γ := Γ) I e.wf hAns

private lemma eqAtom_freeVars
    {n : Nat}
    (e₁ e₂ : RAExpr D Γ n) :
    (eqAtom e₁ e₂).freeVars = ∅ := by
  unfold eqAtom closeBlock
  rw [RelCalc.Formula.freeVars_forallMany]
  have h₁ := query_freeVars e₁
  have h₂ := query_freeVars e₂
  have hBody :
      (RelCalc.Formula.iff
        e₁.toRelCalcQuery.form
        e₂.toRelCalcQuery.form).freeVars =
        (Var.block 0 n).toFinset := by
    change
      e₁.toRelCalcQuery.form.freeVars ∪
        e₂.toRelCalcQuery.form.freeVars =
        (Var.block 0 n).toFinset
    rw [h₁, h₂, Finset.union_self]
  rw [hBody]
  exact erase_block_self n

private lemma subsetAtom_freeVars
    {n : Nat}
    (e₁ e₂ : RAExpr D Γ n) :
    (subsetAtom e₁ e₂).freeVars = ∅ := by
  unfold subsetAtom closeBlock
  rw [RelCalc.Formula.freeVars_forallMany]
  have h₁ := query_freeVars e₁
  have h₂ := query_freeVars e₂
  have hBody :
      (RelCalc.Formula.imp
        e₁.toRelCalcQuery.form
        e₂.toRelCalcQuery.form).freeVars =
        (Var.block 0 n).toFinset := by
    change
      e₁.toRelCalcQuery.form.freeVars ∪
        e₂.toRelCalcQuery.form.freeVars =
        (Var.block 0 n).toFinset
    rw [h₁, h₂, Finset.union_self]
  rw [hBody]
  exact erase_block_self n

omit [Domain D] in
private lemma maps_empty
    (σ : Assign D)
    (Q : Set D) :
    Assign.MapsInto σ ∅ Q := by
  intro x hx
  simp at hx

private theorem eqAtom_correct
    {n : Nat}
    (e₁ e₂ : RAExpr D Γ n)
    (Q : Set D)
    (I : Instance D Γ)
    (σ : Assign D)
    (hQ :
      (↑(I.Adom ∪ (e₁.constants ∪ e₂.constants)) :
        Set D) ⊆ Q) :
    (eqAtom e₁ e₂).SatIn I σ Q ↔
      e₁.eval I = e₂.eval I := by
  constructor
  · intro hSat
    apply Finset.ext
    intro t
    have hAll :=
      (RelCalc.Formula.holdsIn_forallMany_block_iff
        (Q := Q) (I := I) (σ := σ)
        0
        (RelCalc.Formula.iff
          e₁.toRelCalcQuery.form
          e₂.toRelCalcQuery.form)).1
        (by simpa [eqAtom, closeBlock] using hSat.2)
    constructor
    · intro ht₁
      have hOver := eval_tuple_over_adom e₁ I ht₁
      have htQ : Tuple.MapsInto t Q := by
        intro i
        exact contains_left e₁ e₂ hQ (hOver i)
      have hIff := hAll t htQ
      have hHold₁ :
          RelCalc.Formula.ArbitraryAssignSatIn Q I
            (BlockAssign.withBlock σ 0 t)
            e₁.toRelCalcQuery.form :=
        (query_holds_withBlock_iff
          e₁ Q I σ t (contains_left e₁ e₂ hQ)
          htQ).mpr ht₁
      have hHold₂ := hIff.mp hHold₁
      exact
        (query_holds_withBlock_iff
          e₂ Q I σ t (contains_right e₁ e₂ hQ)
          htQ).mp hHold₂
    · intro ht₂
      have hOver := eval_tuple_over_adom e₂ I ht₂
      have htQ : Tuple.MapsInto t Q := by
        intro i
        exact contains_right e₁ e₂ hQ (hOver i)
      have hIff := hAll t htQ
      have hHold₂ :
          RelCalc.Formula.ArbitraryAssignSatIn Q I
            (BlockAssign.withBlock σ 0 t)
            e₂.toRelCalcQuery.form :=
        (query_holds_withBlock_iff
          e₂ Q I σ t (contains_right e₁ e₂ hQ)
          htQ).mpr ht₂
      have hHold₁ := hIff.mpr hHold₂
      exact
        (query_holds_withBlock_iff
          e₁ Q I σ t (contains_left e₁ e₂ hQ)
          htQ).mp hHold₁
  · intro hEq
    have hHolds :
        RelCalc.Formula.ArbitraryAssignSatIn Q I σ
          (eqAtom e₁ e₂) := by
      apply
        (RelCalc.Formula.holdsIn_forallMany_block_iff
          (Q := Q) (I := I) (σ := σ)
          0
          (RelCalc.Formula.iff
            e₁.toRelCalcQuery.form
            e₂.toRelCalcQuery.form)).2
      intro t htQ
      constructor
      · intro hHold₁
        have ht₁ :
            t ∈ e₁.eval I :=
          (query_holds_withBlock_iff
            e₁ Q I σ t (contains_left e₁ e₂ hQ)
            htQ).mp hHold₁
        have ht₂ : t ∈ e₂.eval I := by
          simpa [hEq] using ht₁
        exact
          (query_holds_withBlock_iff
            e₂ Q I σ t (contains_right e₁ e₂ hQ)
            htQ).mpr ht₂
      · intro hHold₂
        have ht₂ :
            t ∈ e₂.eval I :=
          (query_holds_withBlock_iff
            e₂ Q I σ t (contains_right e₁ e₂ hQ)
            htQ).mp hHold₂
        have ht₁ : t ∈ e₁.eval I := by
          simpa [hEq] using ht₂
        exact
          (query_holds_withBlock_iff
            e₁ Q I σ t (contains_left e₁ e₂ hQ)
            htQ).mpr ht₁
    exact ⟨by
      rw [eqAtom_freeVars e₁ e₂]
      exact maps_empty σ Q, hHolds⟩

private theorem subsetAtom_correct
    {n : Nat}
    (e₁ e₂ : RAExpr D Γ n)
    (Q : Set D)
    (I : Instance D Γ)
    (σ : Assign D)
    (hQ :
      (↑(I.Adom ∪ (e₁.constants ∪ e₂.constants)) :
        Set D) ⊆ Q) :
    (subsetAtom e₁ e₂).SatIn I σ Q ↔
      e₁.eval I ⊆ e₂.eval I := by
  constructor
  · intro hSat t ht₁
    have hAll :=
      (RelCalc.Formula.holdsIn_forallMany_block_iff
        (Q := Q) (I := I) (σ := σ)
        0
        (RelCalc.Formula.imp
          e₁.toRelCalcQuery.form
          e₂.toRelCalcQuery.form)).1
        (by simpa [subsetAtom, closeBlock] using hSat.2)
    have hOver := eval_tuple_over_adom e₁ I ht₁
    have htQ : Tuple.MapsInto t Q := by
      intro i
      exact contains_left e₁ e₂ hQ (hOver i)
    have hImp := hAll t htQ
    have hHold₁ :
        RelCalc.Formula.ArbitraryAssignSatIn Q I
          (BlockAssign.withBlock σ 0 t)
          e₁.toRelCalcQuery.form :=
      (query_holds_withBlock_iff
        e₁ Q I σ t (contains_left e₁ e₂ hQ)
        htQ).mpr ht₁
    have hHold₂ := hImp hHold₁
    exact
      (query_holds_withBlock_iff
        e₂ Q I σ t (contains_right e₁ e₂ hQ)
        htQ).mp hHold₂
  · intro hSub
    have hHolds :
        RelCalc.Formula.ArbitraryAssignSatIn Q I σ
          (subsetAtom e₁ e₂) := by
      apply
        (RelCalc.Formula.holdsIn_forallMany_block_iff
          (Q := Q) (I := I) (σ := σ)
          0
          (RelCalc.Formula.imp
            e₁.toRelCalcQuery.form
            e₂.toRelCalcQuery.form)).2
      intro t htQ hHold₁
      have ht₁ :
          t ∈ e₁.eval I :=
        (query_holds_withBlock_iff
          e₁ Q I σ t (contains_left e₁ e₂ hQ)
          htQ).mp hHold₁
      have ht₂ : t ∈ e₂.eval I := hSub ht₁
      exact
        (query_holds_withBlock_iff
          e₂ Q I σ t (contains_right e₁ e₂ hQ)
          htQ).mpr ht₂
    exact ⟨by
      rw [subsetAtom_freeVars e₁ e₂]
      exact maps_empty σ Q, hHolds⟩

/- The RelCalc translation is closed. -/
theorem toRelCalc_freeVars
    (φ : QFAssertExpr D Γ) :
    φ.toRelCalc.freeVars = ∅ := by
  induction φ with
  | «true» =>
      rfl
  | «false» =>
      rfl
  | eq e₁ e₂ =>
      exact eqAtom_freeVars e₁ e₂
  | subset e₁ e₂ =>
      exact subsetAtom_freeVars e₁ e₂
  | and φ ψ ihφ ihψ =>
      change (toRelCalc φ).freeVars ∪
          (toRelCalc ψ).freeVars = ∅
      rw [ihφ, ihψ, Finset.union_empty]
  | or φ ψ ihφ ihψ =>
      change (toRelCalc φ).freeVars ∪
          (toRelCalc ψ).freeVars = ∅
      rw [ihφ, ihψ, Finset.union_empty]
  | not φ ih =>
      exact ih

/- The RelCalc translation is a sentence. -/
theorem toRelCalc_isSentence
    (φ : QFAssertExpr D Γ) :
    φ.toRelCalc.IsSentence :=
  toRelCalc_freeVars φ

/- Translate a QF assertion to a RelCalc sentence. -/
def toRelCalcSentence
    (φ : QFAssertExpr D Γ) :
    RelCalc.Sentence D Γ :=
  φ.toRelCalc.toSentence (toRelCalc_isSentence φ)

/-
  Sentence packaging does not change the translated
  formula.
-/
theorem toRelCalcSentence_val
    (φ : QFAssertExpr D Γ) :
    φ.toRelCalcSentence.1 = φ.toRelCalc :=
  rfl

end QFAssertExpr

end Whiel

------------------------------------------------------------
-- QF Assertion Entailments to RelCalc Entailments
------------------------------------------------------------

namespace QFEntailment

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Translate a list of QF assertions to RelCalc sentences.
-/
def toRelCalcSentenceList
    (φs : List (Whiel.QFAssertExpr D Γ)) :
    List (RelCalc.Sentence D Γ) :=
  φs.map Whiel.QFAssertExpr.toRelCalcSentence

/- Translation preserves list constants. -/
lemma formulaListConstants_toRelCalcSentenceList
    (φs : List (Whiel.QFAssertExpr D Γ)) :
    RelCalc.SentenceEntailment.sentenceListConstants
        (toRelCalcSentenceList φs) =
      formulaListConstants φs := by
  induction φs with
  | nil =>
      rfl
  | cons φ φs ih =>
      have ih' :
          RelCalc.SentenceEntailment.sentenceListConstants
              (List.map
                Whiel.QFAssertExpr.toRelCalcSentence φs) =
            formulaListConstants φs := by
        simpa [toRelCalcSentenceList] using ih
      change (Whiel.QFAssertExpr.toRelCalcSentence φ).constants ∪
          RelCalc.SentenceEntailment.sentenceListConstants
            (List.map
              Whiel.QFAssertExpr.toRelCalcSentence φs) =
        φ.constants ∪ formulaListConstants φs
      have hConst :
          (Whiel.QFAssertExpr.toRelCalcSentence φ).constants =
            φ.constants := by
        change (Whiel.QFAssertExpr.toRelCalc φ).constants =
          φ.constants
        exact Whiel.QFAssertExpr.toRelCalc_constants φ
      rw [hConst, ih']

/- Translate a QF entailment to a RelCalc entailment. -/
def toRelCalcEntailment
    (E : QFEntailment (D := D) Γ) :
    RelCalc.SentenceEntailment (D := D) Γ where
  axioms := toRelCalcSentenceList E.axioms
  conjecture := E.conjecture.toRelCalcSentence

/- Translation preserves entailment constants. -/
lemma toRelCalcEntailment_constants
    (E : QFEntailment (D := D) Γ) :
    E.toRelCalcEntailment.constants = E.constants := by
  have hConst :
      E.conjecture.toRelCalcSentence.constants =
        E.conjecture.constants := by
    change (Whiel.QFAssertExpr.toRelCalc E.conjecture).constants =
      E.conjecture.constants
    exact Whiel.QFAssertExpr.toRelCalc_constants E.conjecture
  simp [toRelCalcEntailment, RelCalc.SentenceEntailment.constants,
    constants, formulaListConstants_toRelCalcSentenceList,
    hConst]

/- Constants of a member formula occur in list constants. -/
lemma constants_subset_formulaListConstants
    {φ : Whiel.QFAssertExpr D Γ}
    {φs : List (Whiel.QFAssertExpr D Γ)}
    (hφ : φ ∈ φs) :
    φ.constants ⊆ formulaListConstants φs := by
  induction φs with
  | nil =>
      cases hφ
  | cons ψ ψs ih =>
      have hcases : φ = ψ ∨ φ ∈ ψs := by
        simpa using hφ
      intro d hd
      unfold formulaListConstants
      exact Finset.mem_union.mpr <| by
        cases hcases with
        | inl h =>
            subst h
            exact Or.inl hd
        | inr h =>
            exact Or.inr (ih h hd)

/- Constants of an axiom occur in entailment constants. -/
lemma axiom_constants
    (E : QFEntailment (D := D) Γ)
    {φ : Whiel.QFAssertExpr D Γ}
    (hφ : φ ∈ E.axioms) :
    φ.constants ⊆ E.constants := by
  intro d hd
  exact Finset.mem_union.mpr
    (Or.inl
      (constants_subset_formulaListConstants
        (φ := φ) (φs := E.axioms) hφ hd))

/- Conjecture constants occur in entailment constants. -/
lemma conjecture_constants
    (E : QFEntailment (D := D) Γ) :
    E.conjecture.constants ⊆ E.constants := by
  intro d hd
  exact Finset.mem_union.mpr (Or.inr hd)

/- RelCalc active domains contain formula active domains. -/
lemma activeDomain_contains
    (E : QFEntailment (D := D) Γ)
    {φ : Whiel.QFAssertExpr D Γ}
    (hφ : φ.constants ⊆ E.constants)
    (I : Instance D Γ) :
    (↑(I.Adom ∪ φ.constants) : Set D) ⊆
      E.toRelCalcEntailment.activeDomain I := by
  intro d hd
  change d ∈ I.Adom ∪ φ.constants at hd
  change d ∈
    E.toRelCalcEntailment.activeFinset I
  rw [RelCalc.SentenceEntailment.activeFinset,
    toRelCalcEntailment_constants E]
  rw [Finset.mem_union] at hd ⊢
  cases hd with
  | inl h =>
      exact Or.inl h
  | inr h =>
      exact Or.inr (hφ h)

end QFEntailment

------------------------------------------------------------
-- AssertExpr Entailments to QF Entailments
------------------------------------------------------------

namespace Whiel

namespace AssertExpr

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Convert an assertion entailment to a singleton-axiom QF
  entailment using no-bound proofs for both sides.
-/
def entailmentToQFEntailmentOfNoBound
    (E : Entailment D Γ)
    (hLhs : E.lhs.NoBoundSymbols)
    (hRhs : E.rhs.NoBoundSymbols) :
    QFEntailment (D := D) Γ where
  axioms := [E.lhs.toQFOfNoBound hLhs]
  conjecture := E.rhs.toQFOfNoBound hRhs

/-
  Validity of the generated QF entailment implies validity
  of the original assertion entailment.
-/
theorem entailmentToQFEntailmentOfNoBound_sound
    (E : Entailment D Γ)
    (hLhs : E.lhs.NoBoundSymbols)
    (hRhs : E.rhs.NoBoundSymbols)
    (hValid :
      (entailmentToQFEntailmentOfNoBound
        E hLhs hRhs).Valid) :
    E.Valid := by
  intro I hI
  have hLhsEval :
      (E.lhs.toQFOfNoBound hLhs).eval I := by
    exact
      (toQFOfNoBound_eval_iff
        E.lhs hLhs I).mpr hI
  have hRhsEval :
      (E.rhs.toQFOfNoBound hRhs).eval I := by
    apply hValid I
    intro φ hφ
    have hφEq :
        φ = E.lhs.toQFOfNoBound hLhs :=
      List.mem_singleton.mp hφ
    subst φ
    exact hLhsEval
  exact
    (toQFOfNoBound_eval_iff
      E.rhs hRhs I).mp hRhsEval

end AssertExpr

end Whiel

------------------------------------------------------------
-- Translation Correctness
------------------------------------------------------------

namespace Whiel

namespace QFAssertExpr

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

private lemma toRelCalc_mapsInto
    (φ : QFAssertExpr D Γ)
    (σ : Assign D)
    (Q : Set D) :
    Assign.MapsInto σ φ.toRelCalc.freeVars Q := by
  rw [toRelCalc_freeVars φ]
  exact maps_empty σ Q

private lemma contains_qf_left
    (φ ψ : QFAssertExpr D Γ)
    {Q : Set D}
    {I : Instance D Γ}
    (hQ :
      (↑(I.Adom ∪ (φ.constants ∪ ψ.constants)) :
        Set D) ⊆ Q) :
    (↑(I.Adom ∪ φ.constants) : Set D) ⊆ Q := by
  intro d hd
  apply hQ
  change d ∈ I.Adom ∪ φ.constants at hd
  change d ∈ I.Adom ∪ (φ.constants ∪ ψ.constants)
  rw [Finset.mem_union] at hd ⊢
  cases hd with
  | inl h =>
      exact Or.inl h
  | inr h =>
      exact Or.inr (Finset.mem_union.mpr (Or.inl h))

private lemma contains_qf_right
    (φ ψ : QFAssertExpr D Γ)
    {Q : Set D}
    {I : Instance D Γ}
    (hQ :
      (↑(I.Adom ∪ (φ.constants ∪ ψ.constants)) :
        Set D) ⊆ Q) :
    (↑(I.Adom ∪ ψ.constants) : Set D) ⊆ Q := by
  intro d hd
  apply hQ
  change d ∈ I.Adom ∪ ψ.constants at hd
  change d ∈ I.Adom ∪ (φ.constants ∪ ψ.constants)
  rw [Finset.mem_union] at hd ⊢
  cases hd with
  | inl h =>
      exact Or.inl h
  | inr h =>
      exact Or.inr (Finset.mem_union.mpr (Or.inr h))

private theorem toRelCalc_correct_eval
    (φ : QFAssertExpr D Γ)
    (Q : Set D)
    (I : Instance D Γ)
    (σ : Assign D)
    (hQ : (↑(I.Adom ∪ φ.constants) : Set D) ⊆ Q) :
    φ.toRelCalc.SatIn I σ Q ↔
      φ.eval I := by
  induction φ generalizing Q I σ with
  | «true» =>
      constructor
      · intro _hSat
        trivial
      · intro _hTrue
        exact ⟨toRelCalc_mapsInto .«true» σ Q, trivial⟩
  | «false» =>
      constructor
      · intro hSat
        exact hSat.2
      · intro hFalse
        exact False.elim hFalse
  | eq e₁ e₂ =>
      simpa [toRelCalc, Guard.eval] using
        eqAtom_correct e₁ e₂ Q I σ hQ
  | subset e₁ e₂ =>
      simpa [toRelCalc, Guard.eval] using
        subsetAtom_correct e₁ e₂ Q I σ hQ
  | and φ ψ ihφ ihψ =>
      have hφQ := contains_qf_left φ ψ hQ
      have hψQ := contains_qf_right φ ψ hQ
      constructor
      · intro hSat
        constructor
        · exact (ihφ Q I σ hφQ).mp
            ⟨toRelCalc_mapsInto φ σ Q, hSat.2.1⟩
        · exact (ihψ Q I σ hψQ).mp
            ⟨toRelCalc_mapsInto ψ σ Q, hSat.2.2⟩
      · rintro ⟨hφ, hψ⟩
        have hSatφ := (ihφ Q I σ hφQ).mpr hφ
        have hSatψ := (ihψ Q I σ hψQ).mpr hψ
        exact ⟨toRelCalc_mapsInto (.and φ ψ) σ Q,
          hSatφ.2, hSatψ.2⟩
  | or φ ψ ihφ ihψ =>
      have hφQ := contains_qf_left φ ψ hQ
      have hψQ := contains_qf_right φ ψ hQ
      constructor
      · intro hSat
        cases hSat.2 with
        | inl h =>
            exact Or.inl
              ((ihφ Q I σ hφQ).mp
                ⟨toRelCalc_mapsInto φ σ Q, h⟩)
        | inr h =>
            exact Or.inr
              ((ihψ Q I σ hψQ).mp
                ⟨toRelCalc_mapsInto ψ σ Q, h⟩)
      · intro h
        cases h with
        | inl hφ =>
            have hSatφ := (ihφ Q I σ hφQ).mpr hφ
            exact ⟨toRelCalc_mapsInto (.or φ ψ) σ Q,
              Or.inl hSatφ.2⟩
        | inr hψ =>
            have hSatψ := (ihψ Q I σ hψQ).mpr hψ
            exact ⟨toRelCalc_mapsInto (.or φ ψ) σ Q,
              Or.inr hSatψ.2⟩
  | not φ ih =>
      constructor
      · intro hSat hφ
        have hSatφ := (ih Q I σ hQ).mpr hφ
        exact hSat.2 hSatφ.2
      · intro hNot
        exact ⟨toRelCalc_mapsInto (.not φ) σ Q, by
          intro hHolds
          exact hNot ((ih Q I σ hQ).mp
            ⟨toRelCalc_mapsInto φ σ Q, hHolds⟩)⟩

/-
  Correctness of the QF assertion to RelCalc translation.
-/
theorem toRelCalc_correct
    (φ : QFAssertExpr D Γ)
    (Q : Set D)
    (I : Instance D Γ)
    (σ : Assign D)
    (hQ : (↑(I.Adom ∪ φ.constants) : Set D) ⊆ Q) :
    φ.toRelCalc.SatIn I σ Q ↔
      φ.eval I :=
  (toRelCalc_correct_eval φ Q I σ hQ).trans
    (Guard.eval_self_iff I φ).symm

/-
  Correctness of the QF assertion to RelCalc translation
  with the target formula explicitly cast as a sentence,
  so that no assignment is needed to evaluate it.
-/
theorem toRelCalcSentence_correct
    (φ : QFAssertExpr D Γ)
    (Q : Set D)
    (I : Instance D Γ)
    (hQ : (↑(I.Adom ∪ φ.constants) : Set D) ⊆ Q) :
    φ.toRelCalcSentence.SatIn I Q ↔
      φ.eval I := by
  let σ : Assign D := fun _ => default
  calc
    φ.toRelCalcSentence.SatIn I Q
        ↔ φ.toRelCalc.SatIn I σ Q := by
          simpa [toRelCalcSentence,
            RelCalc.Formula.toSentence] using
            RelCalc.Sentence.satIn_iff
              (φ.toRelCalcSentence) I Q σ
    _ ↔ φ.eval I :=
      toRelCalc_correct φ Q I σ hQ

/-
  QF translations are independent of quantifier-domain
  extensions.
-/
theorem toRelCalcSentence_domainIndependent
    (φ : QFAssertExpr D Γ) :
    φ.toRelCalcSentence.DomainIndependent := by
  intro I Q hQ
  have hLocal :
      φ.toRelCalcSentence.SatIn I
          (RelCalc.Adom.toSet
            φ.toRelCalcSentence.1 I) ↔
        φ.eval I := by
    apply toRelCalcSentence_correct
    intro d hd
    change d ∈ RelCalc.Adom φ.toRelCalc I
    simpa [RelCalc.Adom, toRelCalc_constants] using hd
  have hExtended :
      φ.toRelCalcSentence.SatIn I Q ↔ φ.eval I := by
    apply toRelCalcSentence_correct
    intro d hd
    apply hQ
    change d ∈ RelCalc.Adom φ.toRelCalc I
    simpa [RelCalc.Adom, toRelCalc_constants] using hd
  exact hLocal.trans hExtended.symm

end QFAssertExpr

end Whiel

------------------------------------------------------------
-- QF Entailment Translation Correctness
------------------------------------------------------------

namespace QFEntailment

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

open Whiel.QFAssertExpr

/- Every translated antecedent is domain independent. -/
theorem toRelCalcEntailment_axioms_domainIndependent
    (E : QFEntailment (D := D) Γ) :
    ∀ ψ ∈ E.toRelCalcEntailment.axioms,
      ψ.DomainIndependent := by
  intro ψ hψ
  unfold toRelCalcEntailment toRelCalcSentenceList at hψ
  rcases List.mem_map.mp hψ with ⟨φ, _hφ, rfl⟩
  exact toRelCalcSentence_domainIndependent φ

/- QF axioms imply translated RelCalc axioms. -/
lemma relCalc_axioms_of_qf_axioms
    (E : QFEntailment (D := D) Γ)
    {I : Instance D Γ}
    (hAx : ∀ φ ∈ E.axioms, φ.eval I) :
    E.toRelCalcEntailment.SatisfiesAxioms I := by
  intro ψ hψ
  unfold toRelCalcEntailment toRelCalcSentenceList at hψ
  rcases List.mem_map.mp hψ with ⟨φ, hφ, rfl⟩
  have hSat :
      φ.toRelCalcSentence.SatIn I
        (E.toRelCalcEntailment.activeDomain I) :=
    (Whiel.QFAssertExpr.toRelCalcSentence_correct
      φ (E.toRelCalcEntailment.activeDomain I)
      I (E.activeDomain_contains
        (E.axiom_constants hφ) I)).mpr
      (hAx φ hφ)
  exact hSat

/-
  Validity of the RelCalc translation implies QF validity.
-/
theorem valid_of_toRelCalc
    (E : QFEntailment (D := D) Γ)
    (hRel : E.toRelCalcEntailment.Valid) :
    E.Valid := by
  intro I hAx
  have hRelAx :
      E.toRelCalcEntailment.SatisfiesAxioms I :=
    E.relCalc_axioms_of_qf_axioms hAx
  have hSat :=
    hRel I hRelAx
  have hSentence :
      E.conjecture.toRelCalcSentence.SatIn I
        (E.toRelCalcEntailment.activeDomain I) :=
    hSat
  exact
    (Whiel.QFAssertExpr.toRelCalcSentence_correct
      E.conjecture
      (E.toRelCalcEntailment.activeDomain I)
      I
      (E.activeDomain_contains
        E.conjecture_constants I)).mp hSentence

end QFEntailment
