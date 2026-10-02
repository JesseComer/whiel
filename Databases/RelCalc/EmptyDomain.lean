-- Author: Jesse Comer
import Databases.Logic.PropositionalCNF
import Databases.RelCalc.AdomSemantics

/-
  Empty active-domain entailments reduce to propositional
  formulas over the nullary relation symbols. The reduction
  uses unrestricted assignment semantics at one fixed
  assignment, and is lifted to closed sentences afterward.
-/

------------------------------------------------------------
-- Empty-Domain Formula Reduction
------------------------------------------------------------

namespace RelCalc

namespace Formula

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

def emptyReduction : Formula D Γ →
    PropositionalCNF.Formula (Instance.NullarySymbol Γ)
  | .top => .const true
  | .bot => .const false
  | .eq t u => .const
      (decide (t.eval (fun _ => default) =
        u.eval (fun _ => default)))
  | .rel a =>
      if h : Γ.arity a.rel = 0 then
        .atom ⟨a.rel, h⟩
      else .const false
  | .and p q => .and p.emptyReduction q.emptyReduction
  | .or p q => .or p.emptyReduction q.emptyReduction
  | .not p => .not p.emptyReduction
  | .imp p q => .imp p.emptyReduction q.emptyReduction
  | .iff p q => .iff p.emptyReduction q.emptyReduction
  | .forall_ _ _ => .const true
  | .exists_ _ _ => .const false

/- Only the unrestricted predicate is compositional. -/
theorem emptyReduction_correct
    (p : Formula D Γ)
    (χ : Instance.NullaryAssignment Γ) :
    p.emptyReduction.eval χ = true ↔
      ArbitraryAssignSatIn (∅ : Set D)
        (Instance.ofNullaryAssignment χ)
        (fun _ => default) p := by
  induction p with
  | top | bot | eq t u =>
      simp [emptyReduction, PropositionalCNF.Formula.eval,
        ArbitraryAssignSatIn]
  | rel a =>
      simp only [emptyReduction, ArbitraryAssignSatIn,
        RelAtom.Sat, RelAtom.evalFact, RelFact.Mem]
      refine Iff.trans ?_
        (Instance.mem_ofNullaryAssignment_iff χ a.rel
          (a.evalTuple (fun _ => default))).symm
      split <;>
        simp_all [PropositionalCNF.Formula.eval]
  | and p q hp hq =>
      simpa [emptyReduction, PropositionalCNF.Formula.eval,
        ArbitraryAssignSatIn] using and_congr hp hq
  | or p q hp hq =>
      simpa [emptyReduction, PropositionalCNF.Formula.eval,
        ArbitraryAssignSatIn] using or_congr hp hq
  | not p hp =>
      cases h : p.emptyReduction.eval χ <;>
        simp_all [emptyReduction,
          PropositionalCNF.Formula.eval,
          ArbitraryAssignSatIn]
  | imp p q hp hq =>
      cases h : p.emptyReduction.eval χ <;>
        cases k : q.emptyReduction.eval χ <;>
        simp_all [emptyReduction,
          PropositionalCNF.Formula.eval,
          ArbitraryAssignSatIn]
  | iff p q hp hq =>
      cases h : p.emptyReduction.eval χ <;>
        cases k : q.emptyReduction.eval χ <;>
        simp_all [emptyReduction,
          PropositionalCNF.Formula.eval,
          ArbitraryAssignSatIn]
  | forall_ x p _ | exists_ x p _ =>
      simp [emptyReduction, PropositionalCNF.Formula.eval,
        ArbitraryAssignSatIn]

end Formula

namespace Sentence

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Closedness discharges the typed free-variable guard. -/
theorem emptyReduction_correct
    (p : Sentence D Γ)
    (χ : Instance.NullaryAssignment Γ) :
    p.1.emptyReduction.eval χ = true ↔
      p.SatIn (Instance.ofNullaryAssignment χ)
        (∅ : Set D) := by
  rw [satIn_iff p _ _ (fun _ => default)]
  have hp : p.1.freeVars = ∅ := p.2
  simpa [Formula.SatIn, Assign.MapsInto, hp] using
    Formula.emptyReduction_correct p.1 χ

end Sentence

end RelCalc

------------------------------------------------------------
-- Entailment Counterexamples and CNF
------------------------------------------------------------

namespace RelCalc

namespace SentenceEntailment

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

local instance :
    DecidableEq (Instance.NullarySymbol Γ) := by
  unfold Instance.NullarySymbol
  infer_instance

private def emptyPremises : List (Sentence D Γ) →
    PropositionalCNF.Formula (Instance.NullarySymbol Γ)
  | [] => .const true
  | p :: ps => .and p.1.emptyReduction (emptyPremises ps)

private theorem emptyPremises_correct
    (ps : List (Sentence D Γ))
    (χ : Instance.NullaryAssignment Γ) :
    (emptyPremises ps).eval χ = true ↔
      ∀ p ∈ ps,
        p.SatIn (Instance.ofNullaryAssignment χ)
          (∅ : Set D) := by
  induction ps with
  | nil =>
      simp [emptyPremises, PropositionalCNF.Formula.eval]
  | cons p ps ih =>
      simp [emptyPremises, PropositionalCNF.Formula.eval,
        Sentence.emptyReduction_correct, ih]

/- Constants make an empty active domain impossible. -/
def emptyFormula (E : SentenceEntailment (D := D) Γ) :
    PropositionalCNF.Formula (Instance.NullarySymbol Γ) :=
  if E.constants = ∅ then
    .and (emptyPremises E.axioms)
      (.not E.conjecture.1.emptyReduction)
  else .const false

def emptyCNF (E : SentenceEntailment (D := D) Γ) :
    PropositionalCNF.Encoding :=
  E.emptyFormula.simplify.encode

private theorem active_empty_parts
    (E : SentenceEntailment (D := D) Γ)
    (I : Instance D Γ) (h : E.activeFinset I = ∅) :
    I.AdomEmpty ∧ E.constants = ∅ := by
  constructor
  · apply Finset.ext
    intro d
    constructor
    · intro hd
      have hm : d ∈ E.activeFinset I :=
        Finset.mem_union.mpr (Or.inl hd)
      simp [h] at hm
    · simp
  · apply Finset.ext
    intro d
    constructor
    · intro hd
      have hm : d ∈ E.activeFinset I :=
        Finset.mem_union.mpr (Or.inr hd)
      simp [h] at hm
    · simp

/- A semantic counterexample supplies one SAT witness. -/
theorem satisfiable_emptyCNF_of_hasEmptyCounterexample
    (E : SentenceEntailment (D := D) Γ)
    (h : E.HasEmptyCounterexample) :
    ∃ v, E.emptyCNF.clauses.Satisfies v := by
  obtain ⟨I, hActive, hAx, hConj⟩ := h
  obtain ⟨hAdom, hConst⟩ := active_empty_parts E I hActive
  have hI :=
    Instance.eq_ofNullaryAssignment_toNullaryAssignment
      I hAdom
  have hDomain : E.activeDomain I = (∅ : Set D) := by
    ext d
    change d ∈ E.activeFinset I ↔ d ∈ (∅ : Set D)
    simp [hActive]
  have hp : (emptyPremises E.axioms).eval
      I.toNullaryAssignment = true := by
    apply (emptyPremises_correct _ _).mpr
    intro p hm
    have hs := hAx p hm
    rw [hDomain] at hs
    simpa only [← hI] using hs
  have hn : E.conjecture.1.emptyReduction.eval
      I.toNullaryAssignment ≠ true := by
    intro hc
    have hs :=
      (Sentence.emptyReduction_correct _ _).mp hc
    apply hConj
    rw [hDomain]
    simpa only [← hI] using hs
  apply E.emptyFormula.simplify.satisfiable_encode
    I.toNullaryAssignment
  rw [PropositionalCNF.Formula.eval_simplify]
  simp [emptyFormula, hConst,
    PropositionalCNF.Formula.eval, hp, hn]

end SentenceEntailment

end RelCalc
