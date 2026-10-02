-- Author: Jesse Comer
import Databases.Core.Containment
import Databases.RelCalc.FormulaSemantics

/-
  Active-domain semantics for relational-calculus queries.

  Key specification declarations:
    * `RelCalc.Adom`
    * `RelCalc.Adom.toSet`
    * `RelCalc.Formula.AdomSat`
    * `RelCalc.Query.SatTuple`

  The finite query evaluator is:
    * `RelCalc.Query.eval`

  Correctness of the evaluator is proven:
    * `RelCalc.Query.in_eval_iff_satTuple`

  Active-domain entailment semantics is given by:
    * `RelCalc.SentenceEntailment.activeDomain`
    * `RelCalc.SentenceEntailment.SatisfiesAxioms`
    * `RelCalc.SentenceEntailment.Valid`
    * `RelCalc.SentenceEntailment.EmptyCounterexample`
    * `RelCalc.SentenceEntailment.NoEmptyCounterexample`

  Intervening definitions and lemmas are computable
  construction and proof support.
-/

------------------------------------------------------------
-- Active Domain Evaluation Specification
------------------------------------------------------------

namespace RelCalc

/-
  The active domain available to a formula or query
  consists of the instance active domain together with the
  constants occurring in the formula.
-/
def Adom
    {A D : Type}
    [Domain D]
    [RelationNames A]
    {Γ : UnnamedSchema A}
    (φ : Formula D Γ)
    (I : Instance D Γ) : Finset D :=
  I.Adom ∪ φ.constants

namespace Adom

variable {A D : Type}
variable [Domain D]
variable [RelationNames A]
variable {Γ : UnnamedSchema A}

/- Active domain viewed as a set. -/
def toSet
    (φ : Formula D Γ)
    (I : Instance D Γ) : Set D :=
  fun d => d ∈ RelCalc.Adom φ I

instance
    (φ : Formula D Γ)
    (I : Instance D Γ) :
    DecidablePred (toSet φ I) := by
  intro d
  unfold toSet
  infer_instance

end Adom

namespace Formula

variable {A D : Type}
variable [Domain D]
variable {_ : RelationNames A}
variable {Γ : UnnamedSchema A}

/-
  Active-domain satisfaction of well-formed formulas in an
  instance relative to an assignment.
-/
def AdomSat
    (φ : Formula D Γ)
    (I : Instance D Γ)
    (σ : Assign D) : Prop :=
  φ.SatIn I σ (Adom.toSet φ I)

instance
    (φ : Formula D Γ)
    (I : Instance D Γ)
    (σ : Assign D) :
    Decidable (φ.AdomSat I σ) := by
  unfold Formula.AdomSat
  let _ : Fintype {d // Adom.toSet φ I d} :=
    Fintype.ofFinset (Adom φ I)
      (by simp)
  let _ :=
    Formula.decidableSatIn
      (Q := Adom.toSet φ I)
      (φ := φ) (I := I) (σ := σ)
  infer_instance

end Formula

namespace Query

variable {A D : Type}
variable [Domain D]
variable {_ : RelationNames A}
variable {Γ : UnnamedSchema A}
variable {n : Nat}

/-
  Prop-valued function which returns true for a query `q`,
  an instance `I`, and a tuple `t` whenever there exists an
  assignment `σ` which realizes `t` on the output variables
  of `q` such that `q.form.AdomSat I σ` holds.
-/
def SatTuple
    (q : Query D Γ n)
    (I : Instance D Γ)
    (t : Tuple D n) : Prop :=
  ∃ σ : Assign D,
    Assign.Realizes σ q.vars t ∧
      q.form.AdomSat I σ

end Query

end RelCalc

------------------------------------------------------------
-- Active Domain Evaluation Construction
------------------------------------------------------------

namespace RelCalc

namespace Query

variable {A D : Type}
variable [Domain D]
variable {_ : RelationNames A}
variable {Γ : UnnamedSchema A}
variable {n : Nat}

/-
  Query evaluation under active-domain semantics. The finite
  relation enumerates candidate output tuples over the
  active domain and checks the canonical realizing
  assignment.
-/
def eval
    (q : Query D Γ n)
    (I : Instance D Γ) :
    FinRelation D n :=
  (Tuple.allOver (Adom q I) n).filter
    (fun t =>
      Assign.TupleConsistent q.vars t ∧
        q.form.AdomSat I (Assign.ofVectorTuple q.vars t))

/-
  RelCalc queries evaluate through the shared query
  interface.
-/
instance : QueryEval (Query D Γ n) D Γ n where
  eval q I := q.eval I

end Query

end RelCalc

------------------------------------------------------------
-- Active Domain Evaluation Properties
------------------------------------------------------------

namespace RelCalc

namespace Query

variable {A D : Type}
variable [Domain D]
variable {_ : RelationNames A}
variable {Γ : UnnamedSchema A}
variable {n : Nat}

end Query

end RelCalc

------------------------------------------------------------
-- Active Domain Evaluation Correctness
------------------------------------------------------------

namespace RelCalc

namespace Query

variable {A D : Type}
variable [Domain D]
variable {_ : RelationNames A}
variable {Γ : UnnamedSchema A}
variable {n : Nat}

/-
  Correctness specification for query evaluation. A tuple
  occurs in the answer to a RelCalc query whenever there
  is an assignment satisfying the formula which maps the
  output variables to that tuple.
-/
theorem in_eval_iff_satTuple
    (q : Query D Γ n)
    (I : Instance D Γ)
    (t : Tuple D n) :
    t ∈ q.eval I ↔ q.SatTuple I t := by
  constructor
  · intro ht
    rw [eval] at ht
    rcases Finset.mem_filter.mp ht with
      ⟨_htOver, hCons, hSat⟩
    exact
      ⟨Assign.ofVectorTuple q.vars t,
        Assign.ofVectorTuple_realizes hCons, hSat⟩
  · intro h
    rcases h with ⟨σ, hReal, hSat⟩
    have hCons : Assign.TupleConsistent q.vars t :=
      Assign.tupleConsistent_of_realizes hReal
    rw [eval]
    apply Finset.mem_filter.mpr
    constructor
    · apply Tuple.mem_allOver_of_isTupleOver
      intro i
      have hMap :
          (fun d => d ∈ Adom q I)
            (σ (q.vars.get i)) := by
        exact hSat.1 (q.vars.get i) (by
          rw [q.freeVars_eq]
          change q.vars[i.1] ∈ q.vars.toList.toFinset
          simp)
      simpa [hReal i] using hMap
    · constructor
      · exact hCons
      · have hAgreeOut :
            Assign.AgreeOn σ
              (Assign.ofVectorTuple q.vars t)
              q.vars.toList.toFinset :=
          Assign.agreeOn_of_realizes_ofVectorTuple
            hReal hCons
        have hAgree :
            Assign.AgreeOn σ
              (Assign.ofVectorTuple q.vars t)
              q.form.freeVars := by
          intro x hx
          exact hAgreeOut x
            (by simpa [q.freeVars_eq] using hx)
        exact
          (Formula.satIn_eq_of_agreeOn_freeVars
            (φ := q.form) hAgree).1 hSat

end Query

end RelCalc

------------------------------------------------------------
-- Active-Domain Entailment Semantics
------------------------------------------------------------

namespace RelCalc

namespace SentenceEntailment

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- Finite active domain used by a source entailment. -/
def activeFinset
    (E : SentenceEntailment (D := D) Γ)
    (I : Instance D Γ) : Finset D :=
  I.Adom ∪ E.constants

/- Set view of the entailment active domain. -/
def activeDomain
    (E : SentenceEntailment (D := D) Γ)
    (I : Instance D Γ) : Set D :=
  fun d => d ∈ E.activeFinset I

instance
    (E : SentenceEntailment (D := D) Γ)
    (I : Instance D Γ)
    (φ : RelCalc.Sentence D Γ) :
    Decidable (φ.SatIn I (E.activeDomain I)) := by
  unfold activeDomain
  let Q := E.activeFinset I
  change Decidable
    (φ.SatIn I (fun d => d ∈ Q))
  let _ : Fintype {d // d ∈ Q} :=
    Fintype.ofFinset Q (by intro d; rfl)
  let dFormula : Decidable
      (φ.1.SatIn I (fun _ => default)
        (fun d => d ∈ Q)) :=
    RelCalc.Formula.decidableSatIn
      (Q := fun d => d ∈ Q) φ.1 I (fun _ => default)
  exact @decidable_of_iff'
    (φ.SatIn I (fun d => d ∈ Q))
    (φ.1.SatIn I (fun _ => default)
      (fun d => d ∈ Q))
    (RelCalc.Sentence.satIn_iff
      φ I (fun d => d ∈ Q) (fun _ => default))
    dFormula

/- Source axioms hold on the entailment active domain. -/
def SatisfiesAxioms
    (E : SentenceEntailment (D := D) Γ)
    (I : Instance D Γ) : Prop :=
  ∀ φ ∈ E.axioms, φ.SatIn I (E.activeDomain I)

instance
    (E : SentenceEntailment (D := D) Γ)
    (I : Instance D Γ) :
    Decidable (E.SatisfiesAxioms I) := by
  unfold SatisfiesAxioms
  infer_instance

/- Assignment-free source entailment validity. -/
def Valid
    (E : SentenceEntailment (D := D) Γ) : Prop :=
  ∀ I : Instance D Γ,
    E.SatisfiesAxioms I →
      E.conjecture.SatIn I (E.activeDomain I)

end SentenceEntailment

end RelCalc

------------------------------------------------------------
-- Empty Active-Domain Counterexamples
------------------------------------------------------------

namespace RelCalc

namespace SentenceEntailment

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- An instance falsifies the entailment in the empty case. -/
def EmptyCounterexample
    (E : SentenceEntailment (D := D) Γ)
    (I : Instance D Γ) : Prop :=
  E.activeFinset I = ∅ ∧
    E.SatisfiesAxioms I ∧
      ¬ E.conjecture.SatIn I (E.activeDomain I)

/- Prop-valued existence of an empty counterexample. -/
def HasEmptyCounterexample
    (E : SentenceEntailment (D := D) Γ) : Prop :=
  ∃ I : Instance D Γ,
    E.EmptyCounterexample I

/- Prop-valued absence of an empty counterexample. -/
def NoEmptyCounterexample
    (E : SentenceEntailment (D := D) Γ) : Prop :=
  ¬ E.HasEmptyCounterexample

end SentenceEntailment

end RelCalc
