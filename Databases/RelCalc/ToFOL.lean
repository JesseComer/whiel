-- Author: Jesse Comer
import Databases.FOL.Entailment
import Databases.FOL.Semantics
import Databases.FinStruct.ToInstance
import Databases.RelCalc.AdomSemantics
import Databases.UnnamedModel.ToFinStruct
import Mathlib.Data.Finset.Sort

/-
  RelCalc-to-FOL translation.

  The canonical theorem
  `RelCalc.Formula.toFOL_sat_iff_adomSat` assumes
  nonemptiness of the active domain plus formula constants
  because the target FOL semantics uses `FinStruct`, whose
  carriers are nonempty. Thus the theorem covers exactly the
  cases where that set can be represented as the carrier of
  a finite FOL structure.

  The main construction is:
    * `RelCalc.Formula.toFOL`
    * `RelCalc.Formula.toFOLWithConstants`

  Compatibility with the instance expansion is recorded by:
    * `Instance.toFinStruct_toInstance`

  Satisfaction equivalences are recorded by:
    * `RelCalc.Formula.toFOL_sat_iff_adomSat`
    * `RelCalc.Formula.
      toFOLWithConstants_sat_iff_satIn_of_model`
    * `RelCalc.ToFOL.supportAxioms_sat_of_properties`
    * `RelCalc.SentenceEntailment.toFOLWithSupportAxioms_sound`

  Support axioms and entailment translations are:
    * `RelCalc.ToFOL.supportAxioms`
    * `RelCalc.SentenceEntailment.toFOLWithSupportAxioms`

  Intervening definitions and lemmas are translation and
  proof support.
-/

------------------------------------------------------------
-- Instance and Finite-Structure Compatibility
------------------------------------------------------------

namespace Instance

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]

/-
  Forgetting the canonical expansion recovers the original
  instance.
-/
theorem toFinStruct_toInstance
    {Γ : UnnamedSchema A}
    (I : Instance D Γ)
    (C : Finset D)
    (hNonempty : (I.Adom ∪ C).Nonempty) :
    (I.toFinStruct C hNonempty).toInstance = I := by
  ext X
  rfl

end Instance

------------------------------------------------------------
-- RelCalc-to-FOL Syntax Translation
------------------------------------------------------------

namespace RelCalc

namespace ToFOL

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]

/- The FOL term naming a RelCalc constant. -/
def constTerm
    {Γ : UnnamedSchema A}
    {C : Finset D}
    (c : C) :
  FOL.Term (Γ.toFOLSignature C) :=
  .func c .nil

/- Translate one RelCalc term. -/
def trTerm
    (Γ : UnnamedSchema A)
    (C : Finset D)
    (t : RelTerm D)
    (hC : t.constants ⊆ C) :
    FOL.Term (Γ.toFOLSignature C) :=
  match t with
  | .var x => .var x
  | .const d =>
      have hd : d ∈ C := by
        exact hC (by simp [RelTerm.constants])
      constTerm (Γ := Γ) ⟨d, hd⟩

private lemma mem_listConstants_of_mem_term_constants
    {ts : List (RelTerm D)}
    {t : RelTerm D}
    {d : D}
    (ht : t ∈ ts)
    (hd : d ∈ t.constants) :
    d ∈ RelTerm.listConstants ts := by
  induction ts with
  | nil =>
      cases ht
  | cons u us ih =>
      have hcases : t = u ∨ t ∈ us := by
        simpa using ht
      exact Finset.mem_union.mpr <| by
        cases hcases with
        | inl h =>
            cases h
            exact Or.inl hd
        | inr h =>
            exact Or.inr (ih h)

private lemma mem_tupleConstants_of_mem_get_constants
    {n : Nat}
    {ts : Vector (RelTerm D) n}
    {i : Fin n}
    {d : D}
    (hd : d ∈ (ts.get i).constants) :
    d ∈ RelTerm.tupleConstants ts := by
  have ht : ts.get i ∈ ts.toList := by
    exact List.get_mem _ _
  exact
    mem_listConstants_of_mem_term_constants
      (ts := ts.toList) ht hd

/- Translate a vector of RelCalc terms. -/
def trTermVector
    (Γ : UnnamedSchema A)
    (C : Finset D)
    {n : Nat}
    (ts : Vector (RelTerm D) n)
    (hC : RelTerm.tupleConstants ts ⊆ C) :
    FOL.TermList (Γ.toFOLSignature C) n :=
  FOL.TermList.ofFn
    (fun i =>
      trTerm Γ C (ts.get i) (by
        intro d hd
        exact hC
          (mem_tupleConstants_of_mem_get_constants
          (ts := ts) (i := i) hd)))

/- Translate one term into an explicitly extended signature. -/
def termWithConstants
    (Γ : UnnamedSchema A)
    (C : Finset D)
    (t : RelTerm D)
    (hC : t.constants ⊆ C) :
    FOL.Term (Γ.toFOLSignature C) :=
  trTerm Γ C t hC

/- Translate one term vector into an extended signature. -/
def termVectorWithConstants
    (Γ : UnnamedSchema A)
    (C : Finset D)
    {n : Nat}
    (ts : Vector (RelTerm D) n)
    (hC : RelTerm.tupleConstants ts ⊆ C) :
    FOL.TermList (Γ.toFOLSignature C) n :=
  trTermVector Γ C ts hC

/- Translate one RelCalc formula. -/
def trFormula
    (Γ : UnnamedSchema A)
    (C : Finset D) :
    (φ : RelCalc.Formula D Γ) →
      φ.constants ⊆ C →
        FOL.Formula (Γ.toFOLSignature C)
| .top, _hC => .top
| .bot, _hC => .bot
| .eq t₁ t₂, hC =>
    .eq
      (trTerm Γ C t₁ (by
        intro d hd
        exact hC (Finset.mem_union.mpr (Or.inl hd))))
      (trTerm Γ C t₂ (by
        intro d hd
        exact hC (Finset.mem_union.mpr (Or.inr hd))))
| .rel a, hC =>
    .rel a.rel
      (trTermVector Γ C a.args (by
        intro d hd
        exact hC (by
          simpa [RelCalc.Formula.constants,
            RelAtom.constants] using hd)))
| .and φ ψ, hC =>
    .and
      (trFormula Γ C φ (by
        intro d hd
        exact hC (Finset.mem_union.mpr (Or.inl hd))))
      (trFormula Γ C ψ (by
        intro d hd
        exact hC (Finset.mem_union.mpr (Or.inr hd))))
| .or φ ψ, hC =>
    .or
      (trFormula Γ C φ (by
        intro d hd
        exact hC (Finset.mem_union.mpr (Or.inl hd))))
      (trFormula Γ C ψ (by
        intro d hd
        exact hC (Finset.mem_union.mpr (Or.inr hd))))
| .not φ, hC =>
    .not
      (trFormula Γ C φ (by
        intro d hd
        exact hC hd))
| .imp φ ψ, hC =>
    .imp
      (trFormula Γ C φ (by
        intro d hd
        exact hC (Finset.mem_union.mpr (Or.inl hd))))
      (trFormula Γ C ψ (by
        intro d hd
        exact hC (Finset.mem_union.mpr (Or.inr hd))))
| .iff φ ψ, hC =>
    .iff
      (trFormula Γ C φ (by
        intro d hd
        exact hC (Finset.mem_union.mpr (Or.inl hd))))
      (trFormula Γ C ψ (by
        intro d hd
        exact hC (Finset.mem_union.mpr (Or.inr hd))))
| .forall_ x φ, hC =>
    .forall_ x
      (trFormula Γ C φ (by
        intro d hd
        exact hC hd))
| .exists_ x φ, hC =>
    .exists_ x
      (trFormula Γ C φ (by
        intro d hd
        exact hC hd))

end ToFOL

end RelCalc

namespace RelCalc

namespace Formula

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- Translate a RelCalc formula to first-order logic. -/
def toFOL
    (φ : RelCalc.Formula D Γ) :
    FOL.Formula (Γ.toFOLSignature φ.constants) :=
  RelCalc.ToFOL.trFormula Γ φ.constants φ subset_rfl

/-
  Translate a RelCalc formula into a target signature whose
  constants may strictly extend the formula constants.
-/
def toFOLWithConstants
    (φ : RelCalc.Formula D Γ)
    (C : Finset D)
    (hC : φ.constants ⊆ C) :
    FOL.Formula (Γ.toFOLSignature C) :=
  RelCalc.ToFOL.trFormula Γ C φ hC

end Formula

end RelCalc

------------------------------------------------------------
-- RelCalc to FOL Translation Properties
------------------------------------------------------------

namespace RelCalc

namespace ToFOL

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]

private lemma mem_listVars_iff
    {ts : List (RelTerm D)}
    {x : Var} :
    x ∈ RelTerm.listVars ts ↔
      ∃ t ∈ ts, x ∈ t.vars := by
  induction ts with
  | nil =>
      simp [RelTerm.listVars]
  | cons t ts ih =>
      simp [RelTerm.listVars, ih]

private lemma mem_tupleVars_iff
    {n : Nat}
    {ts : Vector (RelTerm D) n}
    {x : Var} :
    x ∈ RelTerm.tupleVars ts ↔
      ∃ i : Fin n, x ∈ (ts.get i).vars := by
  rw [RelTerm.tupleVars, mem_listVars_iff]
  constructor
  · rintro ⟨t, ht, hx⟩
    rcases List.mem_iff_get.mp ht with
      ⟨i, hi⟩
    have hiLen : i.1 < n := by
      simpa [Vector.length_toList] using i.2
    refine ⟨⟨i.1, hiLen⟩, ?_⟩
    have hGet :
        ts.get ⟨i.1, hiLen⟩ = t := by
      simpa [Vector.get] using hi
    simpa [hGet] using hx
  · rintro ⟨i, hx⟩
    exact ⟨ts.get i, List.get_mem _ _, hx⟩

private lemma termList_mem_freeVars_ofFn
    {F : Type}
    [FunctionNames F]
    {Sig : Signature A F}
    {n : Nat}
    (f : Fin n → FOL.Term Sig)
    {x : Var} :
    x ∈ (FOL.TermList.ofFn f).freeVars ↔
      ∃ i : Fin n, x ∈ (f i).freeVars := by
  induction n with
  | zero =>
      simp [FOL.TermList.ofFn, FOL.TermList.freeVars]
  | succ n ih =>
      let g : Fin n → FOL.Term Sig :=
        fun i =>
          f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
      constructor
      · intro hx
        have hx' :
            x ∈
              (f ⟨0, Nat.succ_pos n⟩).freeVars ∪
                (FOL.TermList.ofFn g).freeVars := by
          simpa [FOL.TermList.ofFn,
            FOL.TermList.freeVars, g] using hx
        rcases Finset.mem_union.mp hx' with hxHead | hxTail
        · exact ⟨⟨0, Nat.succ_pos n⟩, hxHead⟩
        · rcases (ih g).mp hxTail with ⟨i, hi⟩
          exact
            ⟨⟨i.1 + 1, Nat.succ_lt_succ i.2⟩,
              by simpa [g] using hi⟩
      · rintro ⟨i, hi⟩
        cases i using Fin.cases with
        | zero =>
            have hx' :
                x ∈
                  (f
                    ⟨0, Nat.succ_pos n⟩).freeVars ∪
                    (FOL.TermList.ofFn g).freeVars :=
              Finset.mem_union.mpr (Or.inl hi)
            simpa [FOL.TermList.ofFn,
              FOL.TermList.freeVars, g] using hx'
        | succ i =>
            have hiTail :
                x ∈ (FOL.TermList.ofFn g).freeVars :=
              (ih g).mpr ⟨i, by simpa [g] using hi⟩
            have hx' :
                x ∈
                  (f
                    ⟨0, Nat.succ_pos n⟩).freeVars ∪
                    (FOL.TermList.ofFn g).freeVars :=
              Finset.mem_union.mpr (Or.inr hiTail)
            simpa [FOL.TermList.ofFn,
              FOL.TermList.freeVars, g] using hx'

private lemma trTerm_freeVars
    {Γ : UnnamedSchema A}
    {C : Finset D}
    (t : RelTerm D)
    (hC : t.constants ⊆ C) :
    (trTerm Γ C t hC).freeVars = t.vars := by
  cases t with
  | var _ =>
      simp [trTerm, FOL.Term.freeVars,
        RelTerm.vars]
  | const _ =>
      simp [trTerm, constTerm,
        FOL.Term.freeVars,
        FOL.TermList.freeVars,
        RelTerm.vars]

private lemma trTermVector_freeVars
    {Γ : UnnamedSchema A}
    {C : Finset D}
    {n : Nat}
    (ts : Vector (RelTerm D) n)
    (hC : RelTerm.tupleConstants ts ⊆ C) :
    (trTermVector Γ C ts hC).freeVars =
      RelTerm.tupleVars ts := by
  apply Finset.ext
  intro x
  unfold trTermVector
  rw [termList_mem_freeVars_ofFn,
    mem_tupleVars_iff]
  constructor
  · rintro ⟨i, hx⟩
    exact
      ⟨i, by
        simpa [trTerm_freeVars] using hx⟩
  · rintro ⟨i, hx⟩
    exact
      ⟨i, by
        simpa [trTerm_freeVars] using hx⟩

private lemma trFormula_freeVars
    (Γ : UnnamedSchema A)
    (C : Finset D) :
    (φ : RelCalc.Formula D Γ) →
      (hC : φ.constants ⊆ C) →
        (trFormula Γ C φ hC).freeVars =
          φ.freeVars
| .top, _hC => by
    simp [trFormula, FOL.Formula.freeVars,
      RelCalc.Formula.freeVars]
| .bot, _hC => by
    simp [trFormula, FOL.Formula.freeVars,
      RelCalc.Formula.freeVars]
| .eq t₁ t₂, hC => by
    simp [trFormula, FOL.Formula.freeVars,
      RelCalc.Formula.freeVars,
      trTerm_freeVars]
| .rel a, hC => by
    have hArSig :
        (Γ.toFOLSignature C).arity a.rel = Γ.arity a.rel := by
      rfl
    let hTerms : RelTerm.tupleConstants a.args ⊆ C := by
      intro d hd
      exact hC (by
        simpa [RelCalc.Formula.constants,
          RelAtom.constants] using hd)
    have hTr :
        trFormula Γ C (RelCalc.Formula.rel a) hC =
          FOL.Formula.rel
            a.rel
            (hArSig.symm ▸
              trTermVector Γ C a.args hTerms) := by
      simp [trFormula, UnnamedSchema.toFOLSignature]
    rw [hTr]
    simpa [FOL.Formula.freeVars,
      RelCalc.Formula.freeVars, RelAtom.vars] using
      trTermVector_freeVars a.args hTerms
| .and φ ψ, hC => by
    have hφ :=
      trFormula_freeVars Γ C φ (by
        intro d hd
        exact hC (Finset.mem_union.mpr
          (Or.inl hd)))
    have hψ :=
      trFormula_freeVars Γ C ψ (by
        intro d hd
        exact hC (Finset.mem_union.mpr
          (Or.inr hd)))
    simp [trFormula, FOL.Formula.freeVars,
      RelCalc.Formula.freeVars, hφ, hψ]
| .or φ ψ, hC => by
    have hφ :=
      trFormula_freeVars Γ C φ (by
        intro d hd
        exact hC (Finset.mem_union.mpr
          (Or.inl hd)))
    have hψ :=
      trFormula_freeVars Γ C ψ (by
        intro d hd
        exact hC (Finset.mem_union.mpr
          (Or.inr hd)))
    simp [trFormula, FOL.Formula.freeVars,
      RelCalc.Formula.freeVars, hφ, hψ]
| .not φ, hC => by
    have hφ :=
      trFormula_freeVars Γ C φ (by
        intro d hd
        exact hC hd)
    simp [trFormula, FOL.Formula.freeVars,
      RelCalc.Formula.freeVars, hφ]
| .imp φ ψ, hC => by
    have hφ :=
      trFormula_freeVars Γ C φ (by
        intro d hd
        exact hC (Finset.mem_union.mpr
          (Or.inl hd)))
    have hψ :=
      trFormula_freeVars Γ C ψ (by
        intro d hd
        exact hC (Finset.mem_union.mpr
          (Or.inr hd)))
    simp [trFormula, FOL.Formula.freeVars,
      RelCalc.Formula.freeVars, hφ, hψ]
| .iff φ ψ, hC => by
    have hφ :=
      trFormula_freeVars Γ C φ (by
        intro d hd
        exact hC (Finset.mem_union.mpr
          (Or.inl hd)))
    have hψ :=
      trFormula_freeVars Γ C ψ (by
        intro d hd
        exact hC (Finset.mem_union.mpr
          (Or.inr hd)))
    simp [trFormula, FOL.Formula.freeVars,
      RelCalc.Formula.freeVars, hφ, hψ]
| .forall_ x φ, hC => by
    have hφ :=
      trFormula_freeVars Γ C φ (by
        intro d hd
        exact hC hd)
    simp [trFormula, FOL.Formula.freeVars,
      RelCalc.Formula.freeVars, hφ]
| .exists_ x φ, hC => by
    have hφ :=
      trFormula_freeVars Γ C φ (by
        intro d hd
        exact hC hd)
    simp [trFormula, FOL.Formula.freeVars,
      RelCalc.Formula.freeVars, hφ]

private lemma eval_trTerm_of_model
    {Γ : UnnamedSchema A}
    {C : Finset D}
    (M : FinStruct D (Γ.toFOLSignature C))
    (hFixed : M.constantsFixed)
    (σ : FOL.Assign M)
    (t : RelTerm D)
    (hC : t.constants ⊆ C) :
    FOL.Semantics.evalTerm M σ (trTerm Γ C t hC) =
      RelTerm.eval (FOL.Assign.toPlain σ) t := by
  cases t with
  | var _ =>
      simp [trTerm, RelTerm.eval,
        FOL.Semantics.evalTerm, FOL.Assign.toPlain]
  | const _ =>
      change M.funcs _ Tuple.empty = _
      exact hFixed _

private lemma eval_trTermVector_of_model
    {Γ : UnnamedSchema A}
    {C : Finset D}
    (M : FinStruct D (Γ.toFOLSignature C))
    (hFixed : M.constantsFixed)
    (σ : FOL.Assign M)
    {n : Nat}
    (ts : Vector (RelTerm D) n)
    (hC : RelTerm.tupleConstants ts ⊆ C) :
    FOL.Semantics.evalTermList M σ
        (trTermVector Γ C ts hC) =
      RelTerm.evalVector
        (FOL.Assign.toPlain σ) ts := by
  rw [trTermVector]
  rw [FOL.Semantics.evalTermList_ofFn]
  apply Vector.ext
  intro i hi
  simp only [RelTerm.evalVector, Vector.getElem_ofFn]
  exact
    eval_trTerm_of_model M hFixed σ
      (ts.get ⟨i, hi⟩) _

private lemma sat_trRel_of_model
    {Γ : UnnamedSchema A}
    {C : Finset D}
    (M : FinStruct D (Γ.toFOLSignature C))
    (hFixed : M.constantsFixed)
    (σ : FOL.Assign M)
    (a : RelAtom D Γ)
    (hC :
      (RelCalc.Formula.rel a).constants ⊆ C) :
    (trFormula Γ C
        (RelCalc.Formula.rel a) hC).Sat M σ ↔
      RelCalc.Formula.ArbitraryAssignSatIn
        (fun d => d ∈ M.carrier) M.toInstance
        (FOL.Assign.toPlain σ)
        (RelCalc.Formula.rel a) := by
  let hTerms : RelTerm.tupleConstants a.args ⊆ C := by
    intro d hd
    exact hC (by
      simpa [RelCalc.Formula.constants,
        RelAtom.constants] using hd)
  have hArSig :
      (Γ.toFOLSignature C).arity a.rel = Γ.arity a.rel := by
    rfl
  have hTr :
      trFormula Γ C (RelCalc.Formula.rel a) hC =
        FOL.Formula.rel
          a.rel
          (hArSig.symm ▸
            trTermVector Γ C a.args hTerms) := by
    simp [trFormula, UnnamedSchema.toFOLSignature]
  constructor
  · intro h
    rw [hTr] at h
    have hEval :=
      eval_trTermVector_of_model M hFixed σ a.args hTerms
    unfold FOL.Formula.Sat at h
    have hMem := hEval ▸ h
    unfold RelCalc.Formula.ArbitraryAssignSatIn
      RelAtom.Sat RelAtom.evalFact RelFact.Mem
    simpa [FinStruct.toInstance] using hMem
  · intro h
    have hEval :=
      eval_trTermVector_of_model M hFixed σ a.args hTerms
    unfold RelCalc.Formula.ArbitraryAssignSatIn
      RelAtom.Sat RelAtom.evalFact RelFact.Mem at h
    rw [hTr]
    unfold FOL.Formula.Sat
    simpa [FinStruct.toInstance] using
      hEval.symm ▸ h

private lemma sat_trFormula_of_model
    {Γ : UnnamedSchema A}
    {C : Finset D}
    (M : FinStruct D (Γ.toFOLSignature C))
    (hFixed : M.constantsFixed) :
    (φ : RelCalc.Formula D Γ) →
      (hC : φ.constants ⊆ C) →
      (σ : FOL.Assign M) →
        (trFormula Γ C φ hC).Sat M σ ↔
          RelCalc.Formula.ArbitraryAssignSatIn
            (fun d => d ∈ M.carrier) M.toInstance
            (FOL.Assign.toPlain σ) φ
| .top, _hC, _σ => by
    simp [trFormula, FOL.Formula.Sat,
      RelCalc.Formula.ArbitraryAssignSatIn]
| .bot, _hC, _σ => by
    simp [trFormula, FOL.Formula.Sat,
      RelCalc.Formula.ArbitraryAssignSatIn]
| .eq t₁ t₂, hC, σ => by
    simp [trFormula, FOL.Formula.Sat,
      RelCalc.Formula.ArbitraryAssignSatIn,
      eval_trTerm_of_model M hFixed σ]
| .rel a, hC, σ =>
    sat_trRel_of_model M hFixed σ a hC
| .and φ ψ, hC, σ => by
    have hφ :=
      sat_trFormula_of_model M hFixed φ (by
        intro d hd
        exact hC (Finset.mem_union.mpr
          (Or.inl hd))) σ
    have hψ :=
      sat_trFormula_of_model M hFixed ψ (by
        intro d hd
        exact hC (Finset.mem_union.mpr
          (Or.inr hd))) σ
    constructor
    · intro h
      exact ⟨hφ.mp h.1, hψ.mp h.2⟩
    · intro h
      exact ⟨hφ.mpr h.1, hψ.mpr h.2⟩
| .or φ ψ, hC, σ => by
    have hφ :=
      sat_trFormula_of_model M hFixed φ (by
        intro d hd
        exact hC (Finset.mem_union.mpr
          (Or.inl hd))) σ
    have hψ :=
      sat_trFormula_of_model M hFixed ψ (by
        intro d hd
        exact hC (Finset.mem_union.mpr
          (Or.inr hd))) σ
    constructor
    · intro h
      cases h with
      | inl hSat => exact Or.inl (hφ.mp hSat)
      | inr hSat => exact Or.inr (hψ.mp hSat)
    · intro h
      cases h with
      | inl hSat => exact Or.inl (hφ.mpr hSat)
      | inr hSat => exact Or.inr (hψ.mpr hSat)
| .not φ, hC, σ => by
    have hφ :=
      sat_trFormula_of_model M hFixed φ (by
        intro d hd
        exact hC hd) σ
    constructor
    · intro h hSat
      exact h (hφ.mpr hSat)
    · intro h hSat
      exact h (hφ.mp hSat)
| .imp φ ψ, hC, σ => by
    have hφ :=
      sat_trFormula_of_model M hFixed φ (by
        intro d hd
        exact hC (Finset.mem_union.mpr
          (Or.inl hd))) σ
    have hψ :=
      sat_trFormula_of_model M hFixed ψ (by
        intro d hd
        exact hC (Finset.mem_union.mpr
          (Or.inr hd))) σ
    constructor
    · intro h hSat
      exact hψ.mp (h (hφ.mpr hSat))
    · intro h hSat
      exact hψ.mpr (h (hφ.mp hSat))
| .iff φ ψ, hC, σ => by
    have hφ :=
      sat_trFormula_of_model M hFixed φ (by
        intro d hd
        exact hC (Finset.mem_union.mpr
          (Or.inl hd))) σ
    have hψ :=
      sat_trFormula_of_model M hFixed ψ (by
        intro d hd
        exact hC (Finset.mem_union.mpr
          (Or.inr hd))) σ
    constructor
    · intro h
      constructor
      · intro hSat
        exact hψ.mp (h.mp (hφ.mpr hSat))
      · intro hSat
        exact hφ.mp (h.mpr (hψ.mpr hSat))
    · intro h
      constructor
      · intro hSat
        exact hψ.mpr (h.mp (hφ.mp hSat))
      · intro hSat
        exact hφ.mpr (h.mpr (hψ.mp hSat))
| .forall_ x φ, hC, σ => by
    constructor
    · intro h d hd
      have hφ :=
        sat_trFormula_of_model M hFixed φ (by
          intro c hc
          exact hC hc)
          (FOL.Assign.update σ x ⟨d, hd⟩)
      have hSat := hφ.mp (by
        simpa [FOL.Formula.Sat] using
          h ⟨d, hd⟩)
      simpa [FOL.Assign.toPlain_update,
        FOL.PlainAssign.update,
        Assign.update] using hSat
    · intro h d
      have hφ :=
        sat_trFormula_of_model M hFixed φ (by
          intro c hc
          exact hC hc)
          (FOL.Assign.update σ x d)
      exact hφ.mpr (by
        have hSat := h d.1 d.2
        simpa [FOL.Assign.toPlain_update,
          FOL.PlainAssign.update,
          Assign.update] using hSat)
| .exists_ x φ, hC, σ => by
    constructor
    · rintro ⟨d, hSat⟩
      have hφ :=
        sat_trFormula_of_model M hFixed φ (by
          intro c hc
          exact hC hc)
          (FOL.Assign.update σ x d)
      refine ⟨d.1, d.2, ?_⟩
      have hPlain := hφ.mp hSat
      simpa [FOL.Assign.toPlain_update,
        FOL.PlainAssign.update,
        Assign.update] using hPlain
    · rintro ⟨d, hd, hSat⟩
      have hφ :=
        sat_trFormula_of_model M hFixed φ (by
          intro c hc
          exact hC hc)
          (FOL.Assign.update σ x ⟨d, hd⟩)
      refine ⟨⟨d, hd⟩, ?_⟩
      exact hφ.mpr (by
        simpa [FOL.Assign.toPlain_update,
          FOL.PlainAssign.update,
          Assign.update] using hSat)

/- Translating a term preserves evaluation. -/
private lemma eval_trTerm
    {Γ : UnnamedSchema A}
    {C : Finset D}
    (I : Instance D Γ)
    (hNonempty : (I.Adom ∪ C).Nonempty)
    (σ :
      FOL.Assign
        (I.toFinStruct C hNonempty))
    (t : RelTerm D)
    (hC : t.constants ⊆ C) :
    FOL.Semantics.evalTerm
        (I.toFinStruct C hNonempty) σ
        (trTerm Γ C t hC) =
      RelTerm.eval
        (FOL.Assign.toPlain σ) t := by
  cases t with
  | var _ =>
      simp [trTerm, RelTerm.eval,
        FOL.Semantics.evalTerm,
        FOL.Assign.toPlain]
  | const _ =>
      simp [trTerm, constTerm,
        RelTerm.eval,
        Instance.toFinStruct,
        FOL.Semantics.evalTerm]

/- Translating a term vector preserves tuple evaluation. -/
private lemma eval_trTermVector
    {Γ : UnnamedSchema A}
    {C : Finset D}
    (I : Instance D Γ)
    (hNonempty : (I.Adom ∪ C).Nonempty)
    (σ :
      FOL.Assign
        (I.toFinStruct C hNonempty))
    {n : Nat}
    (ts : Vector (RelTerm D) n)
    (hC : RelTerm.tupleConstants ts ⊆ C) :
    FOL.Semantics.evalTermList
        (I.toFinStruct C hNonempty) σ
        (trTermVector Γ C ts hC) =
      RelTerm.evalVector
        (FOL.Assign.toPlain σ) ts := by
  rw [trTermVector]
  rw [FOL.Semantics.evalTermList_ofFn]
  apply Vector.ext
  intro i hi
  simp only [RelTerm.evalVector, Vector.getElem_ofFn]
  exact
    eval_trTerm I hNonempty σ (ts.get ⟨i, hi⟩) _

/- Correctness for translated relation atoms. -/
private lemma sat_trRel
    {Γ : UnnamedSchema A}
    {C : Finset D}
    (I : Instance D Γ)
    (hNonempty : (I.Adom ∪ C).Nonempty)
    (σ :
      FOL.Assign
        (I.toFinStruct C hNonempty))
    (a : RelAtom D Γ)
    (hC :
      (RelCalc.Formula.rel a).constants ⊆ C) :
    (trFormula Γ C (RelCalc.Formula.rel a) hC).Sat
        (I.toFinStruct C hNonempty) σ ↔
      RelCalc.Formula.ArbitraryAssignSatIn
        (fun d => d ∈ I.Adom ∪ C) I
        (FOL.Assign.toPlain σ)
        (RelCalc.Formula.rel a) := by
  let hTerms : RelTerm.tupleConstants a.args ⊆ C := by
    intro d hd
    exact hC (by
      simpa [RelCalc.Formula.constants,
        RelAtom.constants] using hd)
  have hArSig :
      (Γ.toFOLSignature C).arity a.rel = Γ.arity a.rel := by
    rfl
  have hTr :
      trFormula Γ C (RelCalc.Formula.rel a) hC =
        FOL.Formula.rel
          a.rel
          (hArSig.symm ▸
            trTermVector Γ C a.args hTerms) := by
    simp [trFormula, UnnamedSchema.toFOLSignature]
  constructor
  · intro h
    rw [hTr] at h
    have hEval :=
      eval_trTermVector I hNonempty σ a.args hTerms
    unfold FOL.Formula.Sat at h
    dsimp [Instance.toFinStruct] at h
    have hMem := hEval ▸ h
    unfold RelCalc.Formula.ArbitraryAssignSatIn
      RelAtom.Sat RelAtom.evalFact RelFact.Mem
    simpa using hMem
  · intro h
    have hEval :=
      eval_trTermVector I hNonempty σ a.args hTerms
    unfold RelCalc.Formula.ArbitraryAssignSatIn
      RelAtom.Sat RelAtom.evalFact RelFact.Mem at h
    rw [hTr]
    unfold FOL.Formula.Sat
    dsimp [Instance.toFinStruct]
    exact hEval.symm ▸ h

/-
  Translating a formula formula preserves
  satisfaction over the active-domain-plus-constants
  carrier.
-/
private lemma sat_trFormula
    {Γ : UnnamedSchema A}
    {C : Finset D}
    (I : Instance D Γ)
    (hNonempty : (I.Adom ∪ C).Nonempty) :
    (φ : RelCalc.Formula D Γ) →
      (hC : φ.constants ⊆ C) →
      (σ :
        FOL.Assign
          (I.toFinStruct C hNonempty)) →
        (trFormula Γ C φ hC).Sat
            (I.toFinStruct C hNonempty) σ ↔
          RelCalc.Formula.ArbitraryAssignSatIn
            (fun d => d ∈ I.Adom ∪ C) I
            (FOL.Assign.toPlain σ) φ
| .top, _hC, _σ => by
    simp [trFormula, FOL.Formula.Sat,
      RelCalc.Formula.ArbitraryAssignSatIn]
| .bot, _hC, _σ => by
    simp [trFormula, FOL.Formula.Sat,
      RelCalc.Formula.ArbitraryAssignSatIn]
| .eq t₁ t₂, hC, σ => by
    simp [trFormula, FOL.Formula.Sat,
      RelCalc.Formula.ArbitraryAssignSatIn,
      eval_trTerm I hNonempty σ]
| .rel a, hC, σ =>
    sat_trRel I hNonempty σ a hC
| .and φ ψ, hC, σ => by
    have hφ :=
      sat_trFormula I hNonempty φ (by
        intro d hd
        exact hC (Finset.mem_union.mpr
          (Or.inl hd))) σ
    have hψ :=
      sat_trFormula I hNonempty ψ (by
        intro d hd
        exact hC (Finset.mem_union.mpr
          (Or.inr hd))) σ
    simp [trFormula, FOL.Formula.Sat,
      RelCalc.Formula.ArbitraryAssignSatIn, hφ, hψ]
| .or φ ψ, hC, σ => by
    have hφ :=
      sat_trFormula I hNonempty φ (by
        intro d hd
        exact hC (Finset.mem_union.mpr
          (Or.inl hd))) σ
    have hψ :=
      sat_trFormula I hNonempty ψ (by
        intro d hd
        exact hC (Finset.mem_union.mpr
          (Or.inr hd))) σ
    simp [trFormula, FOL.Formula.Sat,
      RelCalc.Formula.ArbitraryAssignSatIn, hφ, hψ]
| .not φ, hC, σ => by
    have hφ :=
      sat_trFormula I hNonempty φ (by
        intro d hd
        exact hC hd) σ
    simp [trFormula, FOL.Formula.Sat,
      RelCalc.Formula.ArbitraryAssignSatIn, hφ]
| .imp φ ψ, hC, σ => by
    have hφ :=
      sat_trFormula I hNonempty φ (by
        intro d hd
        exact hC (Finset.mem_union.mpr
          (Or.inl hd))) σ
    have hψ :=
      sat_trFormula I hNonempty ψ (by
        intro d hd
        exact hC (Finset.mem_union.mpr
          (Or.inr hd))) σ
    simp [trFormula, FOL.Formula.Sat,
      RelCalc.Formula.ArbitraryAssignSatIn, hφ, hψ]
| .iff φ ψ, hC, σ => by
    have hφ :=
      sat_trFormula I hNonempty φ (by
        intro d hd
        exact hC (Finset.mem_union.mpr
          (Or.inl hd))) σ
    have hψ :=
      sat_trFormula I hNonempty ψ (by
        intro d hd
        exact hC (Finset.mem_union.mpr
          (Or.inr hd))) σ
    simp [trFormula, FOL.Formula.Sat,
      RelCalc.Formula.ArbitraryAssignSatIn, hφ, hψ]
| .forall_ x φ, hC, σ => by
    constructor
    · intro h d hd
      let M := I.toFinStruct C hNonempty
      have hdM : d ∈ M.carrier := by
        simpa [M, Instance.toFinStruct] using hd
      have hφ :=
        sat_trFormula I hNonempty φ (by
          intro c hc
          exact hC hc)
          (FOL.Assign.update
            σ x ⟨d, hdM⟩)
      have hSat := hφ.mp (by
        simpa [M] using h ⟨d, hdM⟩)
      simpa [FOL.Assign.toPlain_update,
        FOL.PlainAssign.update,
        Assign.update] using hSat
    · intro h d
      let M := I.toFinStruct C hNonempty
      have hd : d.1 ∈ I.Adom ∪ C := by
        simp [Instance.toFinStruct]
      have hφ :=
        sat_trFormula I hNonempty φ (by
          intro c hc
          exact hC hc)
          (FOL.Assign.update σ x d)
      exact hφ.mpr (by
        have hSat := h d.1 hd
        simpa [FOL.Assign.toPlain_update,
          FOL.PlainAssign.update,
          Assign.update] using hSat)
| .exists_ x φ, hC, σ => by
    constructor
    · rintro ⟨d, hSat⟩
      let M := I.toFinStruct C hNonempty
      have hd : d.1 ∈ I.Adom ∪ C := by
        simp [Instance.toFinStruct]
      have hφ :=
        sat_trFormula I hNonempty φ (by
          intro c hc
          exact hC hc)
          (FOL.Assign.update σ x d)
      refine ⟨d.1, hd, ?_⟩
      have hPlain := hφ.mp hSat
      simpa [FOL.Assign.toPlain_update,
        FOL.PlainAssign.update,
        Assign.update] using hPlain
    · rintro ⟨d, hd, hSat⟩
      let M := I.toFinStruct C hNonempty
      have hdM : d ∈ M.carrier := by
        simpa [M, Instance.toFinStruct] using hd
      have hφ :=
        sat_trFormula I hNonempty φ (by
          intro c hc
          exact hC hc)
          (FOL.Assign.update
            σ x ⟨d, hdM⟩)
      refine ⟨⟨d, hdM⟩, ?_⟩
      exact hφ.mpr (by
        simpa [FOL.Assign.toPlain_update,
          FOL.PlainAssign.update,
          Assign.update] using hSat)

/-
  Translated satisfaction is equivalent to RelCalc
  active-domain satisfaction without the free-variable
  assignment side condition.
-/
private lemma sat_toFOL_iff_arbitraryAssignSatIn
    {Γ : UnnamedSchema A}
    (I : Instance D Γ)
    (φ : RelCalc.Formula D Γ)
    (hNonempty : (I.Adom ∪ φ.constants).Nonempty)
    (σ :
      FOL.Assign
        (I.toFinStruct φ.constants hNonempty)) :
    φ.toFOL.Sat
        (I.toFinStruct φ.constants hNonempty) σ ↔
      RelCalc.Formula.ArbitraryAssignSatIn
        (RelCalc.Adom.toSet φ I)
        I
        (FOL.Assign.toPlain σ)
        φ := by
  change
    φ.toFOL.Sat
        (I.toFinStruct φ.constants hNonempty) σ ↔
      RelCalc.Formula.ArbitraryAssignSatIn
        (fun d => d ∈ I.Adom ∪ φ.constants)
        I
        (FOL.Assign.toPlain σ)
        φ
  simpa [RelCalc.Formula.toFOL,
    RelCalc.Formula.constants] using
    (sat_trFormula
      (C := φ.constants) I hNonempty φ subset_rfl σ)

/-
  Canonical translated FOL satisfaction is equivalent to
  active-domain RelCalc satisfaction.
-/
private lemma sat_toFOL_iff_adomSat_of_toFinStruct
    {Γ : UnnamedSchema A}
    (I : Instance D Γ)
    (φ : RelCalc.Formula D Γ)
    (hNonempty : (I.Adom ∪ φ.constants).Nonempty)
    (σ : FOL.Assign
          (I.toFinStruct φ.constants hNonempty)) :
    φ.toFOL.Sat
        (I.toFinStruct φ.constants hNonempty) σ ↔
      φ.AdomSat I (FOL.Assign.toPlain σ) := by
  let M :=
    I.toFinStruct φ.constants hNonempty
  have hHolds :=
    sat_toFOL_iff_arbitraryAssignSatIn I φ hNonempty σ
  have hMaps :
      Assign.MapsInto
        (FOL.Assign.toPlain σ)
        φ.freeVars
        (RelCalc.Adom.toSet φ I) := by
    intro x _hx
    have hxCarrier : (σ x).1 ∈ M.carrier :=
      (σ x).2
    simp [M, FOL.Assign.toPlain,
      Instance.toFinStruct,
      RelCalc.Adom.toSet, RelCalc.Adom] at hxCarrier ⊢
  unfold RelCalc.Formula.AdomSat RelCalc.Formula.SatIn
  constructor
  · intro hSat
    exact ⟨hMaps, hHolds.mp hSat⟩
  · intro hSat
    exact hHolds.mpr hSat.2

end ToFOL

end RelCalc

namespace RelCalc

namespace Formula

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- Formula-to-FOL translation preserves free variables. -/
private lemma toFOL_freeVars
    (φ : RelCalc.Formula D Γ) :
    φ.toFOL.freeVars = φ.freeVars := by
  simpa [toFOL, FOL.Formula.freeVars,
    RelCalc.Formula.freeVars] using
    RelCalc.ToFOL.trFormula_freeVars
      Γ φ.constants φ subset_rfl

/-
  Formula-to-FOL translation over a larger constant set
  preserves free variables.
-/
private lemma toFOLWithConstants_freeVars
    (φ : RelCalc.Formula D Γ)
    (C : Finset D)
    (hC : φ.constants ⊆ C) :
    (φ.toFOLWithConstants C hC).freeVars = φ.freeVars := by
  simpa [toFOLWithConstants, FOL.Formula.freeVars,
    RelCalc.Formula.freeVars] using
    RelCalc.ToFOL.trFormula_freeVars Γ C φ hC

end Formula

namespace Sentence

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- Translate a RelCalc sentence into FOL. -/
def toFOL
    (φ : RelCalc.Sentence D Γ) :
    FOL.Sentence (Γ.toFOLSignature φ.constants) :=
  ⟨φ.1.toFOL, by
    unfold FOL.Formula.IsSentence
    change (RelCalc.Formula.toFOL φ.1).freeVars = ∅
    rw [RelCalc.Formula.toFOL_freeVars, φ.2]⟩

/-
  Translate a RelCalc sentence into FOL over a larger
  constant set.
-/
def toFOLWithConstants
    (φ : RelCalc.Sentence D Γ)
    (C : Finset D)
    (hC : φ.constants ⊆ C) :
    FOL.Sentence (Γ.toFOLSignature C) :=
  ⟨φ.1.toFOLWithConstants C hC, by
    unfold FOL.Formula.IsSentence
    rw [RelCalc.Formula.toFOLWithConstants_freeVars,
      φ.2]⟩

end Sentence

end RelCalc

------------------------------------------------------------
-- Translation Correctness
------------------------------------------------------------

namespace RelCalc

namespace Formula

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Correctness for the canonical FOL expansion of an
  instance.

  Here `M` is required to be exactly the expansion of `I`
  with carrier `I.Adom ∪ φ.constants`, and `τ` is the
  plain assignment obtained from the carrier-valued FOL
  assignment `σ`. Under those identifications, FOL
  satisfaction of
  `φ.toFOL` is equivalent to active-domain RelCalc
  satisfaction in `I`.

  The hypothesis `hNonempty` is not a semantic assumption
  about RelCalc. It is only the evidence needed to construct
  the finite FOL structure whose carrier is
  `I.Adom ∪ φ.constants`.
-/
theorem toFOL_sat_iff_adomSat
    (φ : RelCalc.Formula D Γ)
    (I : Instance D Γ)
    (hNonempty : (I.Adom ∪ φ.constants).Nonempty)
    (M : FinStruct D
          (Γ.toFOLSignature φ.constants))
    (hM : M = I.toFinStruct φ.constants hNonempty)
    (σ : FOL.Assign M)
    (τ : Assign D)
    (hτ : τ = FOL.Assign.toPlain σ) :
    φ.toFOL.Sat M σ ↔ φ.AdomSat I τ := by
  subst M
  subst τ
  simpa [RelCalc.Formula.toFOL] using
    RelCalc.ToFOL.sat_toFOL_iff_adomSat_of_toFinStruct
      I φ hNonempty σ

/-
  Correctness for a formula translated into an already
  supplied finite structure over a shared constant set.

  This version applies when a formula needs to be translated
  into a signature with more constants than just those
  appearing in the formula. It does not build a canonical
  expansion from an instance, so it has no separate
  carrier-nonemptiness hypothesis: `M` is already a
  `FinStruct`.

  The translated formula `ψ`, plain assignment `τ`, and
  carrier predicate `Q` are explicit hypotheses so the
  statement reads as a direct satisfaction equivalence.
-/
theorem toFOLWithConstants_sat_iff_satIn_of_model
    (φ : RelCalc.Formula D Γ)
    (C : Finset D)
    (hC : φ.constants ⊆ C)
    (M : FinStruct D (Γ.toFOLSignature C))
    (hFixed : M.constantsFixed)
    (ψ : FOL.Formula (Γ.toFOLSignature C))
    (hψ : ψ = φ.toFOLWithConstants C hC)
    (σ : FOL.Assign M)
    (τ : Assign D)
    (hτ : τ = FOL.Assign.toPlain σ)
    (Q : Set D)
    (hQ : Q = M.carrierSet) :
    ψ.Sat M σ ↔ φ.SatIn M.toInstance τ Q := by
  subst ψ
  subst τ
  subst Q
  unfold RelCalc.Formula.SatIn
  have hCorrect :=
    RelCalc.ToFOL.sat_trFormula_of_model
      M hFixed φ hC σ
  constructor
  · intro hSat
    constructor
    · intro x _hx
      simp [FOL.Assign.toPlain,
        FinStruct.carrierSet]
    · exact hCorrect.mp (by
        simpa [toFOLWithConstants] using hSat)
  · intro hSat
    exact (by
      simpa [toFOLWithConstants] using
        hCorrect.mpr hSat.2)

end Formula

end RelCalc

------------------------------------------------------------
-- Active-Domain FOL Support Formulas
------------------------------------------------------------

namespace RelCalc

namespace ToFOL

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]

/- A variable used as a relation-tuple witness. -/
def witnessVar
    (x : Var)
    (i : Nat) : Var :=
  x + 1 + i

/- Decode a generated witness variable. -/
private def witnessVarIndex?
    (x y : Var) : Option Nat :=
  let i := y - (x + 1)
  if witnessVar x i = y then some i else none

/-
  Decode a generated witness variable below a fixed arity.
-/
private def witnessVarFin?
    (x : Var)
    (n : Nat)
    (y : Var) : Option (Fin n) :=
  match witnessVarIndex? x y with
  | some i =>
      if h : i < n then some ⟨i, h⟩ else none
  | none => none

/- Witness variables for all coordinates of an arity. -/
def witnessVars
    (x : Var)
    (n : Nat) : List Var :=
  (List.range n).map (fun i => witnessVar x i)

/- Term list of relation-tuple witness variables. -/
def witnessTerms
    {Γ : UnnamedSchema A}
    {C : Finset D}
    (x : Var)
    (n : Nat) :
    FOL.TermList (Γ.toFOLSignature C) n :=
  FOL.TermList.ofFn
    (fun i => FOL.Term.var (witnessVar x i.1))

/- Active-domain branch for a named constant. -/
def constantActiveDomainFormula
    {Γ : UnnamedSchema A}
    {C : Finset D}
    (x : Var)
    (c : C) :
    FOL.Formula (Γ.toFOLSignature C) :=
  .eq (.var x) (constTerm c)

/-
  Active-domain branch for one coordinate of one relation.
-/
def relationCoordinateActiveDomainFormula
    {Γ : UnnamedSchema A}
    {C : Finset D}
    (x : Var)
    (r : Γ.syms)
    (i : Fin (Γ.arity r)) :
    FOL.Formula (Γ.toFOLSignature C) :=
  FOL.Formula.existsMany
    (witnessVars x (Γ.arity r))
    (.and
      (.rel ⟨r.1, r.2⟩
        (witnessTerms (Γ := Γ) (C := C) x (Γ.arity r)))
      (.eq (.var x) (.var (witnessVar x i.1))))

/-
  Constant branches of the active-domain formula from an
  explicit constant-symbol list.
-/
def constantActiveDomainFormulasOfList
    {Γ : UnnamedSchema A}
    {C : Finset D}
    (x : Var)
    (cs : List C) :
    List (FOL.Formula (Γ.toFOLSignature C)) :=
  cs.map
    (fun c =>
      constantActiveDomainFormula (Γ := Γ) x c)

/- Coordinate branches for one relation. -/
def relationActiveDomainFormulasFor
    {Γ : UnnamedSchema A}
    (C : Finset D)
    (x : Var)
    (r : Γ.syms) :
    List (FOL.Formula (Γ.toFOLSignature C)) :=
  (List.range (Γ.arity r)).map
    (fun i =>
      if h : i < Γ.arity r then
        relationCoordinateActiveDomainFormula
          (C := C) x r ⟨i, h⟩
      else
        .bot)

/-
  Relation-coordinate branches of the active-domain formula
  from an explicit relation-symbol list.
-/
def relationActiveDomainFormulasOfList
    {Γ : UnnamedSchema A}
    (C : Finset D)
    (x : Var)
    (rs : List Γ.syms) :
    List (FOL.Formula (Γ.toFOLSignature C)) :=
  rs.flatMap
    (fun r =>
      relationActiveDomainFormulasFor C x r)

/-
  Formula saying `x` is in the named active domain,
  using explicit symbol lists.
-/
def activeDomainFormulaOfLists
    (Γ : UnnamedSchema A)
    (C : Finset D)
    (x : Var)
    (cs : List C)
    (rs : List Γ.syms) :
    FOL.Formula (Γ.toFOLSignature C) :=
  FOL.Formula.disjoin
    (constantActiveDomainFormulasOfList (Γ := Γ) x cs ++
      relationActiveDomainFormulasOfList C x rs)

/-
  Formula saying `x` is in the named active domain,
  using canonical sorted lists.
-/
def activeDomainFormula
    [LinearOrder D]
    [LinearOrder A]
    (Γ : UnnamedSchema A)
    (C : Finset D)
    (x : Var) :
    FOL.Formula (Γ.toFOLSignature C) :=
  activeDomainFormulaOfLists
    Γ C x C.attach.sort Γ.syms.attach.sort

/- Constant active-domain branches mention only `x`. -/
private theorem constantActiveDomainFormula_freeVars
    {Γ : UnnamedSchema A}
    {C : Finset D}
    (x : Var)
    (c : C) :
    (constantActiveDomainFormula
      (Γ := Γ) x c).freeVars = {x} := by
  simp [constantActiveDomainFormula, constTerm,
    FOL.Formula.freeVars, FOL.Term.freeVars,
    FOL.TermList.freeVars]

/-
  Witness terms mention only generated witness variables.
-/
private theorem witnessTerms_freeVars_subset
    {Γ : UnnamedSchema A}
    {C : Finset D}
    (x : Var)
    (n : Nat) :
    (witnessTerms (Γ := Γ) (C := C) x n).freeVars ⊆
      (witnessVars x n).toFinset := by
  intro y hy
  rcases FOL.TermList.mem_freeVars_ofFn
      (fun i : Fin n =>
        FOL.Term.var (witnessVar x i.1)) hy with
    ⟨i, hi⟩
  have hyEq : y = witnessVar x i.1 := by
    simpa [FOL.Term.freeVars] using hi
  subst y
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  exact ⟨i.1, List.mem_range.mpr i.2, rfl⟩

/-
  Generated witness variables are distinct from the base
  active-domain variable.
-/
private theorem witnessVar_ne_base
    (x i : Var) :
    witnessVar x i ≠ x := by
  intro h
  unfold witnessVar at h
  have hlt : x < x + 1 + i :=
    Nat.lt_of_lt_of_le
      (Nat.lt_succ_self x)
      (Nat.le_add_right (x + 1) i)
  exact (Nat.ne_of_gt hlt) h

/-
  The base active-domain variable is not one of its
  generated witnesses.
-/
private theorem base_not_mem_witnessVars
    (x n : Var) :
    x ∉ witnessVars x n := by
  intro hx
  rcases List.mem_map.mp hx with ⟨i, _hi, hEq⟩
  exact witnessVar_ne_base x i hEq

/-
  A coordinate witness occurs in the generated witness
  list.
-/
private theorem witnessVar_mem_witnessVars
    (x : Var)
    {n i : Nat}
    (hi : i < n) :
    witnessVar x i ∈ witnessVars x n := by
  apply List.mem_map.mpr
  exact ⟨i, List.mem_range.mpr hi, rfl⟩

private theorem witnessVarIndex?_witness
    (x i : Var) :
    witnessVarIndex? x (witnessVar x i) = some i := by
  unfold witnessVarIndex? witnessVar
  have hSub : x + 1 + i - (x + 1) = i := by
    exact Nat.add_sub_cancel_left (x + 1) i
  rw [hSub]
  simp

private theorem witnessVarFin?_witness
    (x : Var)
    {n : Nat}
    (j : Fin n) :
    witnessVarFin? x n (witnessVar x j.1) = some j := by
  unfold witnessVarFin?
  rw [witnessVarIndex?_witness]
  simp [j.2]

private theorem witnessVarFin?_none_of_not_mem
    {x y : Var}
    {n : Nat}
    (hy : y ∉ witnessVars x n) :
    witnessVarFin? x n y = none := by
  unfold witnessVarFin? witnessVarIndex?
  by_cases hEq : witnessVar x (y - (x + 1)) = y
  · rw [if_pos hEq]
    by_cases hi : y - (x + 1) < n
    · exact False.elim
        (hy (by
          rw [← hEq]
          exact witnessVar_mem_witnessVars x hi))
    · simp [hi]
  · simp [hEq]

/-
  Relation-coordinate active-domain branches mention only
  the base variable after existential witness closure.
-/
private theorem relCoordAdomFormula_freeVars_subset
    {Γ : UnnamedSchema A}
    {C : Finset D}
    (x : Var)
    (r : Γ.syms)
    (i : Fin (Γ.arity r)) :
    (relationCoordinateActiveDomainFormula
      (C := C) x r i).freeVars ⊆ {x} := by
  intro y hy
  unfold relationCoordinateActiveDomainFormula at hy
  rw [FOL.Formula.mem_freeVars_existsMany_iff] at hy
  have hBody := hy.1
  have hNotWitness := hy.2
  change y ∈
      (FOL.Formula.rel ⟨r.1, r.2⟩
          (witnessTerms (Γ := Γ) (C := C)
            x (Γ.arity r))).freeVars ∪
        (FOL.Formula.eq (FOL.Term.var x)
          (FOL.Term.var (witnessVar x i.1))).freeVars
    at hBody
  rw [Finset.mem_union] at hBody
  cases hBody with
  | inl hRel =>
      have hMemFin :
          y ∈ (witnessVars x (Γ.arity r)).toFinset :=
        witnessTerms_freeVars_subset x (Γ.arity r) hRel
      have hMemList :
          y ∈ witnessVars x (Γ.arity r) := by
        simpa using hMemFin
      exact False.elim (hNotWitness hMemList)
  | inr hEq =>
      change y ∈
          (FOL.Term.var x).freeVars ∪
            (FOL.Term.var (witnessVar x i.1)).freeVars
        at hEq
      rw [Finset.mem_union] at hEq
      cases hEq with
      | inl hBase =>
          have hBaseEq : y = x := by
            simpa [FOL.Term.freeVars] using hBase
          simp [hBaseEq]
      | inr hWitness =>
          have hWitnessEq : y = witnessVar x i.1 := by
            simpa [FOL.Term.freeVars] using hWitness
          subst y
          have hMem :
              witnessVar x i.1 ∈
                witnessVars x (Γ.arity r) :=
            witnessVar_mem_witnessVars x i.2
          exact False.elim (hNotWitness hMem)

/- Constant active-domain branch lists mention only `x`. -/
private theorem constAdomList_freeVars_subset
    {Γ : UnnamedSchema A}
    {C : Finset D}
    (x : Var)
    (cs : List C)
    {φ : FOL.Formula (Γ.toFOLSignature C)}
    (hφ :
      φ ∈
        constantActiveDomainFormulasOfList
          (Γ := Γ) x cs) :
    φ.freeVars ⊆ {x} := by
  unfold constantActiveDomainFormulasOfList at hφ
  rcases List.mem_map.mp hφ with ⟨c, _hc, rfl⟩
  rw [constantActiveDomainFormula_freeVars]

/- Relation active-domain branch lists mention only `x`. -/
private theorem relAdomFor_freeVars_subset
    {Γ : UnnamedSchema A}
    (C : Finset D)
    (x : Var)
    (r : Γ.syms)
    {φ : FOL.Formula (Γ.toFOLSignature C)}
    (hφ : φ ∈ relationActiveDomainFormulasFor C x r) :
    φ.freeVars ⊆ {x} := by
  unfold relationActiveDomainFormulasFor at hφ
  rcases List.mem_map.mp hφ with ⟨i, _hi, rfl⟩
  by_cases hi : i < Γ.arity r
  · simpa [hi] using
      relCoordAdomFormula_freeVars_subset
        (C := C) x r ⟨i, hi⟩
  · simp [hi, FOL.Formula.freeVars]

/- Relation active-domain branch lists mention only `x`. -/
private theorem relAdomList_freeVars_subset
    {Γ : UnnamedSchema A}
    (C : Finset D)
    (x : Var)
    (rs : List Γ.syms)
    {φ : FOL.Formula (Γ.toFOLSignature C)}
    (hφ :
      φ ∈ relationActiveDomainFormulasOfList C x rs) :
    φ.freeVars ⊆ {x} := by
  unfold relationActiveDomainFormulasOfList at hφ
  rcases List.mem_flatMap.mp hφ with ⟨r, _hr, hφr⟩
  exact relAdomFor_freeVars_subset C x r hφr

/- The active-domain formula has at most `x` free. -/
private theorem adomFormulaOfLists_freeVars_subset
    (Γ : UnnamedSchema A)
    (C : Finset D)
    (x : Var)
    (cs : List C)
    (rs : List Γ.syms) :
    (activeDomainFormulaOfLists Γ C x cs rs).freeVars ⊆
      {x} := by
  unfold activeDomainFormulaOfLists
  apply FOL.Formula.freeVars_disjoin_subset
  intro φ hφ
  rw [List.mem_append] at hφ
  cases hφ with
  | inl hConst =>
      exact constAdomList_freeVars_subset x cs hConst
  | inr hRel =>
      exact relAdomList_freeVars_subset C x rs hRel

/-
  Active-domain formula universally closed over the base
  variable, using explicit symbol lists.
-/
private def activeDomainSentenceFormulaOfLists
    (Γ : UnnamedSchema A)
    (C : Finset D)
    (cs : List C)
    (rs : List Γ.syms) :
    FOL.Formula (Γ.toFOLSignature C) :=
  .forall_ 0 (activeDomainFormulaOfLists Γ C 0 cs rs)

/- The explicit-list active-domain formula is closed. -/
theorem activeDomainSentenceFormulaOfLists_isSentence
    (Γ : UnnamedSchema A)
    (C : Finset D)
    (cs : List C)
    (rs : List Γ.syms) :
    (activeDomainSentenceFormulaOfLists
      Γ C cs rs).IsSentence := by
  unfold FOL.Formula.IsSentence
  change
    (activeDomainFormulaOfLists
      Γ C 0 cs rs).freeVars.erase 0 = ∅
  apply Finset.ext
  intro y
  constructor
  · intro hy
    rw [Finset.mem_erase] at hy
    have hyBase :
        y ∈ ({0} : Finset Var) :=
      adomFormulaOfLists_freeVars_subset
        Γ C 0 cs rs hy.2
    rw [Finset.mem_singleton] at hyBase
    exact False.elim (hy.1 hyBase)
  · intro hy
    simp at hy

/- Active-domain formula before sentence packaging. -/
def activeDomainSentenceFormula
    [LinearOrder D]
    [LinearOrder A]
    (Γ : UnnamedSchema A)
    (C : Finset D) :
    FOL.Formula (Γ.toFOLSignature C) :=
  .forall_ 0 (activeDomainFormula Γ C 0)

/- The sorted-list active-domain formula is closed. -/
private theorem activeDomainSentenceFormula_isSentence
    [LinearOrder D]
    [LinearOrder A]
    (Γ : UnnamedSchema A)
    (C : Finset D) :
    (activeDomainSentenceFormula Γ C).IsSentence := by
  simpa [activeDomainSentenceFormula, activeDomainFormula,
    activeDomainSentenceFormulaOfLists] using
    activeDomainSentenceFormulaOfLists_isSentence
      Γ C C.attach.sort Γ.syms.attach.sort

/- Closed active-domain sentence for naming. -/
def activeDomainSentence
    [LinearOrder D]
    [LinearOrder A]
    (Γ : UnnamedSchema A)
    (C : Finset D) :
    FOL.Sentence (Γ.toFOLSignature C) :=
  ⟨activeDomainSentenceFormula Γ C,
    activeDomainSentenceFormula_isSentence Γ C⟩

/- Closed active-domain sentence over explicit lists. -/
def activeDomainSentenceOfLists
    (Γ : UnnamedSchema A)
    (C : Finset D)
    (cs : List C)
    (rs : List Γ.syms) :
    FOL.Sentence (Γ.toFOLSignature C) :=
  ⟨activeDomainSentenceFormulaOfLists Γ C cs rs,
    activeDomainSentenceFormulaOfLists_isSentence
      Γ C cs rs⟩

/- Canonical sorts are the explicit-list sentence. -/
theorem activeDomainSentence_eq_ofLists
    [LinearOrder D]
    [LinearOrder A]
    (Γ : UnnamedSchema A)
    (C : Finset D)
    {cs : List C}
    {rs : List Γ.syms}
    (hConstants : C.attach.sort = cs)
    (hRelations : Γ.syms.attach.sort = rs) :
    activeDomainSentence Γ C =
      activeDomainSentenceOfLists Γ C cs rs := by
  subst cs
  subst rs
  rfl

end ToFOL

end RelCalc

------------------------------------------------------------
-- Constant-Distinctness FOL Support Formulas
------------------------------------------------------------

namespace RelCalc

namespace ToFOL

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]

/- Formula saying two named constants are distinct. -/
def constantDistinctFormula
    {Γ : UnnamedSchema A}
    {C : Finset D}
    (c d : C) :
    FOL.Formula (Γ.toFOLSignature C) :=
  .not
    (.eq
      (constTerm (Γ := Γ) c)
      (constTerm (Γ := Γ) d))

/- Constant-distinctness formulas are closed. -/
private theorem constantDistinctFormula_isSentence
    {Γ : UnnamedSchema A}
    {C : Finset D}
    (c d : C) :
    (constantDistinctFormula
      (Γ := Γ) c d).IsSentence := by
  unfold FOL.Formula.IsSentence
  simp [constantDistinctFormula, constTerm,
    FOL.Formula.freeVars, FOL.Term.freeVars,
    FOL.TermList.freeVars]

/-
  Closed sentence saying two named constants are distinct.
-/
def constantDistinctSentence
    {Γ : UnnamedSchema A}
    {C : Finset D}
    (c d : C) :
    FOL.Sentence (Γ.toFOLSignature C) :=
  ⟨constantDistinctFormula (Γ := Γ) c d,
    constantDistinctFormula_isSentence c d⟩

/-
  Semantic meaning of one constant-distinctness sentence.
-/
private theorem constantDistinctSentence_correct
    {Γ : UnnamedSchema A}
    {C : Finset D}
    (M : FinStruct D (Γ.toFOLSignature C))
    (c d : C) :
    (constantDistinctSentence (Γ := Γ) c d).Sat M ↔
      M.funcs c Tuple.empty ≠ M.funcs d Tuple.empty := by
  rcases M.carrier_nonempty with ⟨a, ha⟩
  let σ : FOL.Assign M := fun _ => ⟨a, ha⟩
  rw [FOL.Sentence.sat_iff
    (constantDistinctSentence (Γ := Γ) c d) M σ]
  simp [constantDistinctSentence, constantDistinctFormula,
    constTerm, FOL.Formula.Sat, FOL.Semantics.evalTerm,
    FOL.Semantics.evalTermList]

/-
  Constant fixing turns syntactic distinctness of named
  constants into the corresponding support sentence.
-/
private theorem constantDistinctSentence_sat_of_constantsFixed
    {Γ : UnnamedSchema A}
    {C : Finset D}
    (M : FinStruct D (Γ.toFOLSignature C))
    (hFixed : M.constantsFixed)
    {c d : C}
    (hcd : c ≠ d) :
    (constantDistinctSentence (Γ := Γ) c d).Sat M := by
  rw [constantDistinctSentence_correct]
  intro hEq
  have hc : M.funcs c Tuple.empty = c.1 := hFixed c
  have hd : M.funcs d Tuple.empty = d.1 := hFixed d
  apply hcd
  apply Subtype.ext
  rw [← hc, ← hd, hEq]

/- Pairwise distinctness formulas from an explicit list. -/
def constantDistinctSentencesOfList
    {Γ : UnnamedSchema A}
    {C : Finset D} :
    List C → List (FOL.Sentence (Γ.toFOLSignature C))
| [] => []
| c :: cs =>
    cs.map
      (fun d =>
        constantDistinctSentence (Γ := Γ) c d) ++
      constantDistinctSentencesOfList cs

/- Pairwise distinctness formulas for named constants. -/
def constantDistinctSentences
    [LinearOrder D]
    {Γ : UnnamedSchema A}
    (C : Finset D) :
    List (FOL.Sentence (Γ.toFOLSignature C)) :=
  constantDistinctSentencesOfList (Γ := Γ) C.attach.sort

end ToFOL

end RelCalc

------------------------------------------------------------
-- Active-Domain FOL Support Correctness
------------------------------------------------------------

namespace RelCalc

namespace ToFOL

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]

private def tupleWitnessAssign
    {Γ : UnnamedSchema A}
    {C : Finset D}
    (M : FinStruct D (Γ.toFOLSignature C))
    (σ : FOL.Assign M)
    (x : Var)
    (r : Γ.syms)
    (t : Tuple D (Γ.arity r))
    (ht : t ∈ M.rels r) :
    FOL.Assign M :=
  fun y =>
    match witnessVarFin? x (Γ.arity r) y with
    | some j => ⟨t.get j, M.rels_closed r t ht j⟩
    | none =>
      σ y

private theorem tupleWitnessAssign_eq_of_not_mem
    {Γ : UnnamedSchema A}
    {C : Finset D}
    (M : FinStruct D (Γ.toFOLSignature C))
    (σ : FOL.Assign M)
    (x : Var)
    (r : Γ.syms)
    (t : Tuple D (Γ.arity r))
    (ht : t ∈ M.rels r)
    {y : Var}
    (hy : y ∉ witnessVars x (Γ.arity r)) :
    tupleWitnessAssign M σ x r t ht y = σ y := by
  unfold tupleWitnessAssign
  rw [witnessVarFin?_none_of_not_mem hy]

private theorem tupleWitnessAssign_witness
    {Γ : UnnamedSchema A}
    {C : Finset D}
    (M : FinStruct D (Γ.toFOLSignature C))
    (σ : FOL.Assign M)
    (x : Var)
    (r : Γ.syms)
    (t : Tuple D (Γ.arity r))
    (ht : t ∈ M.rels r)
    (j : Fin (Γ.arity r)) :
    (tupleWitnessAssign M σ x r t ht
        (witnessVar x j.1)).1 = t.get j := by
  unfold tupleWitnessAssign
  rw [witnessVarFin?_witness]

private theorem witnessTerms_eval_tuple
    {Γ : UnnamedSchema A}
    {C : Finset D}
    (M : FinStruct D (Γ.toFOLSignature C))
    (σ : FOL.Assign M)
    (x : Var)
    (r : Γ.syms)
    (t : Tuple D (Γ.arity r))
    (ht : t ∈ M.rels r) :
    FOL.Semantics.evalTermList M
        (tupleWitnessAssign M σ x r t ht)
        (witnessTerms (Γ := Γ) (C := C)
          x (Γ.arity r)) =
      t := by
  unfold witnessTerms
  rw [FOL.Semantics.evalTermList_ofFn]
  apply Vector.ext
  intro i hi
  simp [Vector.get, Vector.ofFn,
    FOL.Semantics.evalTerm,
    tupleWitnessAssign_witness]

/- A constant branch holds when constants are fixed. -/
private theorem constantActiveDomainFormula_sat_of_constantsFixed
    {Γ : UnnamedSchema A}
    {C : Finset D}
    (M : FinStruct D (Γ.toFOLSignature C))
    (hFixed : M.constantsFixed)
    (σ : FOL.Assign M)
    (x : Var)
    (c : C)
    (hσ : (σ x).1 = c.1) :
    (constantActiveDomainFormula
      (Γ := Γ) x c).Sat M σ := by
  simp [constantActiveDomainFormula, constTerm,
    FOL.Formula.Sat, FOL.Semantics.evalTerm,
    FOL.Semantics.evalTermList, hFixed c, hσ]

/- A relation-coordinate branch holds for relation facts. -/
private theorem relationCoordinateActiveDomainFormula_sat_of_tuple
    {Γ : UnnamedSchema A}
    {C : Finset D}
    (M : FinStruct D (Γ.toFOLSignature C))
    (σ : FOL.Assign M)
    (x : Var)
    (r : Γ.syms)
    (t : Tuple D (Γ.arity r))
    (ht : t ∈ M.rels r)
    (i : Fin (Γ.arity r))
    (hσ : (σ x).1 = t.get i) :
    (relationCoordinateActiveDomainFormula
      (C := C) x r i).Sat M σ := by
  unfold relationCoordinateActiveDomainFormula
  apply FOL.Formula.sat_existsMany_of_assignment
    (witnessVars x (Γ.arity r))
    (τ := tupleWitnessAssign M σ x r t ht)
  · intro y hy
    exact tupleWitnessAssign_eq_of_not_mem
      M σ x r t ht hy
  · constructor
    · change
        FOL.Semantics.evalTermList M
            (tupleWitnessAssign M σ x r t ht)
            (witnessTerms (Γ := Γ) (C := C)
              x (Γ.arity r)) ∈ M.rels r
      rw [witnessTerms_eval_tuple]
      exact ht
    · change
        (tupleWitnessAssign M σ x r t ht x).1 =
          (tupleWitnessAssign M σ x r t ht
            (witnessVar x i.1)).1
      have hx :
          tupleWitnessAssign M σ x r t ht x = σ x :=
        tupleWitnessAssign_eq_of_not_mem
          M σ x r t ht (base_not_mem_witnessVars x _)
      rw [hx]
      rw [tupleWitnessAssign_witness]
      exact hσ

omit [Domain D] in
private theorem mem_sorted_attach
    [LinearOrder D]
    {C : Finset D}
    (c : C) :
    c ∈ C.attach.sort (· ≤ ·) := by
  exact
    (Finset.mem_sort (fun a b : C => a ≤ b)).mpr
      (Finset.mem_attach C c)

private theorem mem_sorted_schema_attach
    [LinearOrder A]
    {Γ : UnnamedSchema A}
    (r : Γ.syms) :
    r ∈ Γ.syms.attach.sort (· ≤ ·) := by
  exact
    (Finset.mem_sort (fun a b : Γ.syms => a ≤ b)).mpr
      (Finset.mem_attach Γ.syms r)

private theorem relCoord_mem_relationActiveDomainFormulasFor
    {Γ : UnnamedSchema A}
    (C : Finset D)
    (x : Var)
    (r : Γ.syms)
    (i : Fin (Γ.arity r)) :
    relationCoordinateActiveDomainFormula (C := C) x r i ∈
      relationActiveDomainFormulasFor C x r := by
  unfold relationActiveDomainFormulasFor
  apply List.mem_map.mpr
  refine ⟨i.1, List.mem_range.mpr i.2, ?_⟩
  simp [i.2]

/- The active-domain sentence holds in properties models. -/
private theorem activeDomainSentence_sat_of_properties
    [LinearOrder A]
    [LinearOrder D]
    (Γ : UnnamedSchema A)
    (C : Finset D)
    (M : FinStruct D (Γ.toFOLSignature C))
    (hFixed : M.constantsFixed)
    (hAdom : M.satisfiesAdom) :
    (activeDomainSentence Γ C).Sat M := by
  intro σ
  change (activeDomainSentenceFormula Γ C).Sat M σ
  unfold activeDomainSentenceFormula FOL.Formula.Sat
  intro d
  unfold activeDomainFormula activeDomainFormulaOfLists
  rw [FOL.Formula.sat_disjoin_iff]
  have hdAdom : d.1 ∈ M.relAdom ∪ C :=
    (hAdom d.1).mp d.2
  rw [Finset.mem_union] at hdAdom
  cases hdAdom with
  | inr hdConst =>
      let c : C := ⟨d.1, hdConst⟩
      refine
        ⟨constantActiveDomainFormula
            (Γ := Γ) 0 c,
          ?_, ?_⟩
      · apply List.mem_append.mpr
        exact Or.inl <| List.mem_map.mpr
          ⟨c, mem_sorted_attach c, rfl⟩
      · exact
          constantActiveDomainFormula_sat_of_constantsFixed
            M hFixed (FOL.Assign.update σ 0 d) 0 c
            (by simp [FOL.Assign.update, c])
  | inl hdRel =>
      have hdInst :
          d.1 ∈ (M.toInstance (C := C)).Adom := by
        simpa [FinStruct.toInstance, FinStruct.relAdom]
          using hdRel
      rw [Instance.in_Adom_iff_in_Relation] at hdInst
      rcases hdInst with ⟨r, t, ht, hdTuple⟩
      have hdList : d.1 ∈ t.toList :=
        List.mem_toFinset.mp hdTuple
      rcases List.getElem_of_mem hdList with
        ⟨i, hiList, hGet⟩
      have hi : i < Γ.arity r := by
        simpa [Vector.toList] using hiList
      let coord : Fin (Γ.arity r) := ⟨i, hi⟩
      have hCoord : t.get coord = d.1 := by
        have hListGet :
            t.toList[i] = t.get coord := by
          have hVec :=
            Vector.getElem_toList
              (xs := t) (i := i) hiList
          exact hVec
        exact hListGet.symm.trans hGet
      refine
        ⟨relationCoordinateActiveDomainFormula
            (C := C) 0 r coord,
          ?_, ?_⟩
      · apply List.mem_append.mpr
        apply Or.inr
        unfold relationActiveDomainFormulasOfList
        apply List.mem_flatMap.mpr
        exact
          ⟨r, mem_sorted_schema_attach r,
            relCoord_mem_relationActiveDomainFormulasFor
              C 0 r coord⟩
      · exact
          relationCoordinateActiveDomainFormula_sat_of_tuple
            M (FOL.Assign.update σ 0 d) 0 r t ht
            coord (by simpa [FOL.Assign.update] using
              hCoord.symm)

end ToFOL

end RelCalc

------------------------------------------------------------
-- Constant-Distinctness FOL Support Correctness
------------------------------------------------------------

namespace RelCalc

namespace ToFOL

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]

private theorem constantDistinctSentencesOfList_sat
    [LinearOrder D]
    {Γ : UnnamedSchema A}
    {C : Finset D}
    (M : FinStruct D (Γ.toFOLSignature C))
    (hFixed : M.constantsFixed) :
    ∀ cs : List C,
      cs.Nodup →
        ∀ φ ∈ constantDistinctSentencesOfList
            (Γ := Γ) cs,
          φ.Sat M
| [], _hNoDup, φ, hφ => by
    cases hφ
| c :: cs, hNoDup, φ, hφ => by
    have hNoDupParts := List.nodup_cons.mp hNoDup
    unfold constantDistinctSentencesOfList at hφ
    rw [List.mem_append] at hφ
    cases hφ with
    | inl hMap =>
        rcases List.mem_map.mp hMap with
          ⟨d, hd, rfl⟩
        exact
          constantDistinctSentence_sat_of_constantsFixed
            M hFixed (by
              intro hEq
              subst d
              exact hNoDupParts.1 hd)
    | inr hTail =>
        exact
          constantDistinctSentencesOfList_sat
            M hFixed cs hNoDupParts.2 φ hTail

/-
  Constant-distinctness axioms hold when constants are
  fixed.
-/
private theorem constantDistinctSentences_sat_of_constantsFixed
    [LinearOrder D]
    {Γ : UnnamedSchema A}
    (C : Finset D)
    (M : FinStruct D (Γ.toFOLSignature C))
    (hFixed : M.constantsFixed) :
    ∀ φ ∈ constantDistinctSentences (Γ := Γ) C,
      φ.Sat M := by
  unfold constantDistinctSentences
  exact
    constantDistinctSentencesOfList_sat
      M hFixed C.attach.sort
      (Finset.sort_nodup C.attach (· ≤ ·))

end ToFOL

end RelCalc

------------------------------------------------------------
-- Consolidated FOL Support Axioms
------------------------------------------------------------

namespace RelCalc

namespace ToFOL

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]

/-
  Support axioms emitted before translated source axioms.
-/
def supportAxioms
    [LinearOrder A]
    [LinearOrder D]
    (Γ : UnnamedSchema A)
    (C : Finset D) :
    List (FOL.Sentence (Γ.toFOLSignature C)) :=
  activeDomainSentence Γ C ::
    constantDistinctSentences (Γ := Γ) C

/- Support axioms over explicit symbol lists. -/
def supportAxiomsOfLists
    (Γ : UnnamedSchema A)
    (C : Finset D)
    (cs : List C)
    (rs : List Γ.syms) :
    List (FOL.Sentence (Γ.toFOLSignature C)) :=
  activeDomainSentenceOfLists Γ C cs rs ::
    constantDistinctSentencesOfList (Γ := Γ) cs

/-
  Kernel-proved sortedness equalities normalize the canonical
  support axioms to explicit lists.
-/
theorem supportAxioms_eq_ofLists
    [LinearOrder A]
    [LinearOrder D]
    (Γ : UnnamedSchema A)
    (C : Finset D)
    {cs : List C}
    {rs : List Γ.syms}
    (hConstants : C.attach.sort = cs)
    (hRelations : Γ.syms.attach.sort = rs) :
    supportAxioms Γ C = supportAxiomsOfLists Γ C cs rs := by
  unfold supportAxioms supportAxiomsOfLists
    constantDistinctSentences
  rw [activeDomainSentence_eq_ofLists Γ C hConstants hRelations,
    hConstants]

/-
  Support axioms hold in finite structures satisfying the
  support properties.
-/
theorem supportAxioms_sat_of_properties
    [LinearOrder A]
    [LinearOrder D]
    (Γ : UnnamedSchema A)
    (C : Finset D)
    (M : FinStruct D (Γ.toFOLSignature C))
    (hProperties :
      M.constantsFixed ∧ M.satisfiesAdom) :
    ∀ φ ∈ supportAxioms Γ C, φ.Sat M := by
  intro φ hφ
  unfold supportAxioms at hφ
  rw [List.mem_cons] at hφ
  cases hφ with
  | inl hAdomSent =>
      subst φ
      exact
        activeDomainSentence_sat_of_properties
          Γ C M hProperties.1 hProperties.2
  | inr hDistinct =>
      exact
        constantDistinctSentences_sat_of_constantsFixed
          C M hProperties.1 φ hDistinct

end ToFOL

end RelCalc

------------------------------------------------------------
-- RelCalc Entailments as FOL Entailments
------------------------------------------------------------

namespace RelCalc

namespace SentenceEntailment

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- FOL translations of the source axioms. -/
def toFOLSourceAxioms
    (E : SentenceEntailment (D := D) Γ) :
    List (FOL.Sentence (Γ.toFOLSignature E.constants)) :=
  E.axioms.attach.map
    (fun φ =>
      RelCalc.Sentence.toFOLWithConstants φ.1 E.constants
        (E.axiom_constants φ.2))

/- FOL translation of the source conjecture. -/
def toFOLSourceConjecture
    (E : SentenceEntailment (D := D) Γ) :
    FOL.Sentence (Γ.toFOLSignature E.constants) :=
  RelCalc.Sentence.toFOLWithConstants E.conjecture
    E.constants E.conjecture_constants

/- Source RelCalc entailment translated to FOL. -/
def toFOLSourceEntailment
    (E : SentenceEntailment (D := D) Γ) :
    FOL.SentenceEntailment
      (Γ.toFOLSignature E.constants) where
  axioms := E.toFOLSourceAxioms
  conjecture := E.toFOLSourceConjecture

/-
  FOL entailment with support axioms for the translation.
-/
def toFOLWithSupportAxioms
    [LinearOrder A]
    [LinearOrder D]
    (E : SentenceEntailment (D := D) Γ) :
    FOL.SentenceEntailment
      (Γ.toFOLSignature E.constants) where
  axioms :=
    RelCalc.ToFOL.supportAxioms Γ E.constants ++
      E.toFOLSourceAxioms
  conjecture := E.toFOLSourceConjecture

/-
  The active-domain predicate of a support model is its
  carrier.
-/
private lemma activeDomain_eq_carrierSet_of_properties
    (E : SentenceEntailment (D := D) Γ)
    (M : FinStruct D (Γ.toFOLSignature E.constants))
    (hAdom : M.satisfiesAdom) :
    E.activeDomain M.toInstance = M.carrierSet := by
  funext d
  exact propext (hAdom d).symm

/-
  Translated source axioms hold in the canonical FOL
  expansion.
-/
private lemma toFOLSourceAxioms_sat_of_source
    (E : SentenceEntailment (D := D) Γ)
    (I : Instance D Γ)
    (hNonempty : (E.activeFinset I).Nonempty)
    (hAx : E.SatisfiesAxioms I) :
    ∀ ψ ∈ E.toFOLSourceAxioms,
      ψ.Sat (I.toFinStruct E.constants hNonempty) := by
  intro ψ hψ σ
  unfold toFOLSourceAxioms at hψ
  rcases List.mem_map.mp hψ with
    ⟨φ, _hφAttach, hψ⟩
  rcases φ with ⟨φ, hφ⟩
  subst ψ
  have hFixed :
      (I.toFinStruct
        E.constants hNonempty).constantsFixed :=
    Instance.toFinStruct_constantsFixed
      I E.constants hNonempty
  have hCorrect :=
    RelCalc.Formula.toFOLWithConstants_sat_iff_satIn_of_model
      φ.1 E.constants
      (E.axiom_constants hφ)
      (I.toFinStruct E.constants hNonempty)
      hFixed
      (φ.1.toFOLWithConstants E.constants
        (E.axiom_constants hφ))
      rfl σ (FOL.Assign.toPlain σ) rfl
      (I.toFinStruct E.constants hNonempty).carrierSet
      rfl
  have hSatSentence :
      φ.SatIn I (E.activeDomain I) :=
    hAx φ hφ
  have hSat :
      φ.1.SatIn I (FOL.Assign.toPlain σ)
        (E.activeDomain I) :=
    (RelCalc.Sentence.satIn_iff
      φ I (E.activeDomain I)
      (FOL.Assign.toPlain σ)).mp hSatSentence
  have hQ :
      E.activeDomain I =
        (I.toFinStruct
          E.constants hNonempty).carrierSet := by
    funext d
    rfl
  have hSatCarrier :
      φ.1.SatIn
        (I.toFinStruct E.constants hNonempty).toInstance
        (FOL.Assign.toPlain σ)
        (I.toFinStruct
          E.constants hNonempty).carrierSet := by
    simpa [Instance.toFinStruct_toInstance I
      E.constants hNonempty, hQ] using hSat
  exact hCorrect.mpr hSatCarrier

/-
  FOL truth of the translated conjecture implies RelCalc
  truth.
-/
private lemma conjectureSatIn_of_toFOLSourceConjecture_sat
    (E : SentenceEntailment (D := D) Γ)
    (I : Instance D Γ)
    (hNonempty : (E.activeFinset I).Nonempty)
    (M :
      FinStruct D (Γ.toFOLSignature E.constants))
    (hM : M = I.toFinStruct E.constants hNonempty)
    (hFixed : M.constantsFixed)
    (hAdom : M.satisfiesAdom)
    (hSatF : E.toFOLSourceConjecture.Sat M) :
    E.conjecture.SatIn I (E.activeDomain I) := by
  rcases M.carrier_nonempty with ⟨d, hd⟩
  let σF : FOL.Assign M := fun _ => ⟨d, hd⟩
  have hSatFormula :
      E.toFOLSourceConjecture.1.Sat M σF :=
    (FOL.Sentence.sat_iff
      E.toFOLSourceConjecture M σF).mp hSatF
  have hCorrect :=
    RelCalc.Formula.toFOLWithConstants_sat_iff_satIn_of_model
      E.conjecture.1 E.constants E.conjecture_constants
      M hFixed
      E.toFOLSourceConjecture.1 rfl
      σF (FOL.Assign.toPlain σF) rfl
      M.carrierSet rfl
  have hSatCarrier :
      E.conjecture.1.SatIn M.toInstance
        (FOL.Assign.toPlain σF) M.carrierSet :=
    hCorrect.mp hSatFormula
  have hQ :
      E.activeDomain M.toInstance = M.carrierSet :=
    E.activeDomain_eq_carrierSet_of_properties M hAdom
  have hSatActive :
      E.conjecture.1.SatIn M.toInstance
        (FOL.Assign.toPlain σF)
        (E.activeDomain M.toInstance) := by
    simpa [hQ] using hSatCarrier
  have hSentence :
      E.conjecture.SatIn M.toInstance
        (E.activeDomain M.toInstance) :=
    (RelCalc.Sentence.satIn_iff
      E.conjecture M.toInstance
      (E.activeDomain M.toInstance)
      (FOL.Assign.toPlain σF)).mpr hSatActive
  simpa [hM, Instance.toFinStruct_toInstance
    I E.constants hNonempty] using hSentence

/-
  No empty counterexample supplies the empty-active-domain
  case needed by RelCalc-to-FOL soundness.
-/
private lemma conjectureSatIn_of_noEmpty_and_activeFinset_empty
    (E : SentenceEntailment (D := D) Γ)
    (hNo : E.NoEmptyCounterexample)
    {I : Instance D Γ}
    (hEmpty : E.activeFinset I = ∅)
    (hAx : E.SatisfiesAxioms I) :
    E.conjecture.SatIn I (E.activeDomain I) := by
  by_contra hConj
  exact hNo ⟨I, hEmpty, hAx, hConj⟩

/-
  Soundness of the RelCalc-to-FOL entailment translation with
  support axioms. If `E` is a RelCalc entailment, and the FOL
  entailment `E.toFOLWithSupportAxioms` is valid, and `E` has
  no empty-active-domain counterexample, then `E` is valid.
-/
theorem toFOLWithSupportAxioms_sound
    [LinearOrder A]
    [LinearOrder D]
    (E : SentenceEntailment (D := D) Γ)
    (hNoEmpty : E.NoEmptyCounterexample)
    (hFOL :
      FOL.SentenceEntailment.Valid
        (D := D) E.toFOLWithSupportAxioms) :
    E.Valid := by
  intro I hAx
  by_cases hNonempty : (E.activeFinset I).Nonempty
  · let M := I.toFinStruct E.constants hNonempty
    have hFixed : M.constantsFixed :=
      Instance.toFinStruct_constantsFixed
        I E.constants hNonempty
    have hAdom : M.satisfiesAdom :=
      Instance.toFinStruct_satisfiesAdom
        I E.constants hNonempty
    have hAll :
        ∀ ψ ∈ E.toFOLWithSupportAxioms.axioms,
          ψ.Sat M := by
      intro ψ hψ
      change ψ ∈
          RelCalc.ToFOL.supportAxioms Γ E.constants ++
            E.toFOLSourceAxioms at hψ
      rw [List.mem_append] at hψ
      cases hψ with
      | inl hSupport =>
          exact
            RelCalc.ToFOL.supportAxioms_sat_of_properties
              Γ E.constants M ⟨hFixed, hAdom⟩
              ψ hSupport
      | inr hSource =>
          exact
            E.toFOLSourceAxioms_sat_of_source
              I hNonempty hAx ψ hSource
    have hSatF :
        E.toFOLSourceConjecture.Sat M :=
      hFOL M trivial hAll
    exact
      E.conjectureSatIn_of_toFOLSourceConjecture_sat
        I hNonempty M rfl hFixed hAdom hSatF
  · have hEmpty : E.activeFinset I = ∅ := by
      apply Finset.ext
      intro d
      constructor
      · intro hd
        exact False.elim (hNonempty ⟨d, hd⟩)
      · intro hd
        simp at hd
    exact
      E.conjectureSatIn_of_noEmpty_and_activeFinset_empty
        hNoEmpty hEmpty hAx

end SentenceEntailment

end RelCalc
