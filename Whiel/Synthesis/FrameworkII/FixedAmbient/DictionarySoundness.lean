-- Author: Jesse Comer
import Whiel.Synthesis.FrameworkII.FixedAmbient.Obligations
import Whiel.Hoare.ProphecyFreeInitialization
import Whiel.Vampire.QFEntailment

/-
  Soundness of the semantic dictionary's reuse rules.

  The leveled Houdini controller answers a check request
  from an earlier proof or refutation of a related request
  whenever a reuse rule licenses it. Every such rule is a
  claim about `QFEntailment` validity over all finite
  instances. The theorems below state each rule once, so
  that the controller cites a theorem rather than prose:

    * `QFEntailment.valid_of_axioms_subset`
        a proof entry answers every request of the same
        conjecture whose premises contain the cited set;
    * `QFEntailment.fullTaggedSet_hit_sound`
        recording the request's full premise list as the
        cited set is sound;
    * `QFEntailment.countermodel_of_axioms_subset`
        a refutation entry answers every request of the
        same conjecture whose premises it contains;
    * `LeveledFamily.
        initVC_zero_countermodel_of_countermodel`,
      `LeveledFamily.
        not_initObligation_zero_of_countermodel`
        a countermodel at any level refutes the level-zero
        initialization (death at any level);
    * `QFEntailment.valid_of_proofHit`,
      `validOnEmpty_iff_adomEmptyCounterexample?`
        why a proof hit repeats the empty-instance check on
        the new obligation, and that the worker's
        constant-blind check decides exactly that half;
    * `Task.theta_bodyInvariant`,
      `ProphecyContext.premises_bodyInvariant`,
      `QFAssertExpr.wpLoopFree_valid_of_bodyInvariant`,
      `LeveledFamily.maintenanceVC_valid_of_initProof`
        body invariance of the prophecy premises and the
        initialization-to-step direction, kept as the formal
        record of why the contract applies no cross-role
        reuse: the rule would need the cited set valid at
        the emptied states too, which no proof entry
        supplies.

  The converse cross-role direction and the non-transfer of
  the empty-instance verdict are non-theorems; concrete
  witnesses live in the test file
  `Whiel.Synthesis.Tests.FrameworkIIDictionarySoundness`.
-/

------------------------------------------------------------
-- Monotonicity and Countermodels
------------------------------------------------------------

namespace QFEntailment

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Entailment is monotone in its premise list: a proof from
  the cited premises `C` is a proof from any request's
  premises `T` containing them. This is the proof-entry
  rule within one tagged conjecture.
-/
theorem valid_of_axioms_subset
    {C T : List (Whiel.QFAssertExpr D Γ)}
    {φ : Whiel.QFAssertExpr D Γ}
    (hSubset : C ⊆ T)
    (hValid : Valid (D := D) (Γ := Γ) ⟨C, φ⟩) :
    Valid (D := D) (Γ := Γ) ⟨T, φ⟩ := by
  intro I hAxioms
  apply hValid I
  intro ψ hψ
  exact hAxioms ψ (hSubset hψ)

/-
  The full-tagged-set fallback. When the citations of a
  proof cannot be read, the entry records the request's
  whole premise list `T` instead of the cited `C ⊆ T`.
  Every later hit of that entry (`T ⊆ T'`) is a request
  the cited set would also have answered, so the fallback
  is sound and only subsumes fewer requests.
-/
theorem fullTaggedSet_hit_sound
    {C T T' : List (Whiel.QFAssertExpr D Γ)}
    {φ : Whiel.QFAssertExpr D Γ}
    (hCited : C ⊆ T)
    (hHit : T ⊆ T')
    (hValid : Valid (D := D) (Γ := Γ) ⟨C, φ⟩) :
    Valid (D := D) (Γ := Γ) ⟨T', φ⟩ :=
  valid_of_axioms_subset
    (List.Subset.trans hCited hHit) hValid

/- A finite instance refuting one entailment. -/
def Countermodel
    (E : QFEntailment (D := D) Γ)
    (I : Instance D Γ) : Prop :=
  (∀ φ ∈ E.axioms, φ.eval I) ∧
    ¬ E.conjecture.eval I

/- A countermodel refutes validity. -/
theorem not_valid_of_countermodel
    {E : QFEntailment (D := D) Γ}
    {I : Instance D Γ}
    (h : Countermodel E I) :
    ¬ E.Valid := by
  intro hValid
  exact h.2 (hValid I h.1)

/-
  A countermodel of a request is a countermodel of every
  request of the same conjecture with fewer premises. This
  is the refutation-entry rule: the entry holds the full
  premise list `T` of the refuted request, and answers a
  request whose premises `C` it contains.
-/
theorem countermodel_of_axioms_subset
    {C T : List (Whiel.QFAssertExpr D Γ)}
    {φ : Whiel.QFAssertExpr D Γ}
    {I : Instance D Γ}
    (hSubset : C ⊆ T)
    (h : Countermodel (D := D) (Γ := Γ) ⟨T, φ⟩ I) :
    Countermodel (D := D) (Γ := Γ) ⟨C, φ⟩ I :=
  ⟨fun ψ hψ => h.1 ψ (hSubset hψ), h.2⟩

end QFEntailment

------------------------------------------------------------
-- The Empty-Instance Side Condition
------------------------------------------------------------

namespace QFEntailment

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Validity over the instances with a nonempty active
  domain: what a solver proof over nonempty domains
  establishes for the premises it cites.
-/
def ValidOnNonempty
    (E : QFEntailment (D := D) Γ) : Prop :=
  ∀ I : Instance D Γ,
    ¬ I.AdomEmpty →
      (∀ φ ∈ E.axioms, φ.eval I) →
        E.conjecture.eval I

/-
  Validity over the instances with an empty active domain.
  This is what the worker's constant-blind empty-instance
  check decides (`validOnEmpty_iff_adomEmptyCounterexample?`
  below); the older empty-active-domain check is vacuous
  once the entailment mentions a constant, which is not
  enough for a reused proof found in another request's
  constant signature.
-/
def ValidOnEmpty
    (E : QFEntailment (D := D) Γ) : Prop :=
  ∀ I : Instance D Γ,
    I.AdomEmpty →
      (∀ φ ∈ E.axioms, φ.eval I) →
        E.conjecture.eval I

/- Finite validity is exactly both halves. -/
theorem valid_iff_validOnNonempty_and_validOnEmpty
    (E : QFEntailment (D := D) Γ) :
    E.Valid ↔ E.ValidOnNonempty ∧ E.ValidOnEmpty := by
  constructor
  · intro hValid
    exact
      ⟨fun I _ hAxioms => hValid I hAxioms,
        fun I _ hAxioms => hValid I hAxioms⟩
  · rintro ⟨hNonempty, hEmpty⟩ I hAxioms
    by_cases hAdom : I.AdomEmpty
    · exact hEmpty I hAdom hAxioms
    · exact hNonempty I hAdom hAxioms

/- The worker's check decides the empty half exactly. -/
theorem validOnEmpty_iff_adomEmptyCounterexample?
    [Fintype Γ.syms]
    (E : QFEntailment (D := D) Γ) :
    E.ValidOnEmpty ↔ E.adomEmptyCounterexample? = false :=
  (adomEmptyCounterexample?_eq_false_iff E).symm

/- The nonempty half is monotone in the premises. -/
theorem validOnNonempty_of_axioms_subset
    {C T : List (Whiel.QFAssertExpr D Γ)}
    {φ : Whiel.QFAssertExpr D Γ}
    (hSubset : C ⊆ T)
    (hValid :
      ValidOnNonempty (D := D) (Γ := Γ) ⟨C, φ⟩) :
    ValidOnNonempty (D := D) (Γ := Γ) ⟨T, φ⟩ := by
  intro I hAdom hAxioms
  apply hValid I hAdom
  intro ψ hψ
  exact hAxioms ψ (hSubset hψ)

/-
  A proof hit. The solver's proof is taken as the nonempty
  half for the cited set `C` (the one claim about the solver
  the dictionary relies on: a proof citing `C` is a proof of
  `C ⊨ φ` over the nonempty active domains, the same trust
  the launched path places in a proof of the whole request);
  it transfers to the new request `T'` by monotonicity. The
  empty half is a property of the new request alone and is
  decided afresh on it. Nothing about the empty instance is
  taken from the entry: the original request may have
  excluded the empty instance through a premise the proof
  did not cite, or through a constant the new request lacks.
-/
theorem valid_of_proofHit
    {C T' : List (Whiel.QFAssertExpr D Γ)}
    {φ : Whiel.QFAssertExpr D Γ}
    (hCited : C ⊆ T')
    (hNonempty :
      ValidOnNonempty (D := D) (Γ := Γ) ⟨C, φ⟩)
    (hEmpty : ValidOnEmpty (D := D) (Γ := Γ) ⟨T', φ⟩) :
    Valid (D := D) (Γ := Γ) ⟨T', φ⟩ :=
  (valid_iff_validOnNonempty_and_validOnEmpty
    ⟨T', φ⟩).mpr
    ⟨validOnNonempty_of_axioms_subset hCited hNonempty,
      hEmpty⟩

end QFEntailment

------------------------------------------------------------
-- Body-Invariant Premises
------------------------------------------------------------

namespace Whiel

namespace QFAssertExpr

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  A formula every run of `body` preserves: its truth value
  before and after the run agree.
-/
def BodyInvariant
    (body : Cmd D Γ)
    (ψ : QFAssertExpr D Γ) : Prop :=
  ∀ before after : Instance D Γ,
    Cmd.BigStep body before after →
      (ψ.eval before ↔ ψ.eval after)

/- Negation preserves body invariance. -/
theorem BodyInvariant.not
    {body : Cmd D Γ}
    {ψ : QFAssertExpr D Γ}
    (h : BodyInvariant body ψ) :
    BodyInvariant body (QFAssertExpr.not ψ) := by
  intro before after hStep
  change ¬ ψ.eval before ↔ ¬ ψ.eval after
  exact not_congr (h before after hStep)

/-
  Cross-role reuse, the sound direction. From
  body-invariant premises, a proof of `c` is a proof of
  `wp(body, c)`: at any state satisfying the premises, the
  state after the body satisfies them too, hence `c`.
-/
theorem wpLoopFree_valid_of_bodyInvariant
    {C : List (QFAssertExpr D Γ)}
    {c : QFAssertExpr D Γ}
    (body : Cmd D Γ)
    (hBody : body.LoopFree)
    (hInvariant : ∀ ψ ∈ C, BodyInvariant body ψ)
    (hValid :
      QFEntailment.Valid (D := D) (Γ := Γ) ⟨C, c⟩) :
    QFEntailment.Valid (D := D) (Γ := Γ)
      ⟨C, wpLoopFree body hBody c⟩ := by
  intro before hPremises
  rw [wpLoopFree_eval_iff]
  intro after hStep
  apply hValid after
  intro ψ hψ
  exact (hInvariant ψ hψ before after hStep).mp
    (hPremises ψ hψ)

end QFAssertExpr

end Whiel

------------------------------------------------------------
-- Prophecy Premises Are Body-Invariant
------------------------------------------------------------

namespace Whiel

namespace Hoare

namespace WhielNamesProphecy

namespace Task

open Concrete

variable {D : Type} [Domain D]
variable {Gamma : UnnamedSchema WhielNames}
variable {body : Cmd D Gamma}

/- A run of the body leaves semantic collapse unchanged. -/
theorem semanticCollapse_eq_of_bigStep
    (task : Task body)
    {before after : Instance D Gamma}
    (hStep : Cmd.BigStep body before after) :
    task.semanticCollapse before =
      task.semanticCollapse after := by
  apply task.semanticCollapse_congr
  intro relation hNotAssigned
  exact
    (hStep.no_update_preservation relation
      hNotAssigned).symm

/-
  Every theta image is body-invariant: it reads only
  prophecy rows and rows outside the write set, which the
  body cannot assign.
-/
theorem theta_bodyInvariant
    (task : Task body)
    (formula : QFAssertExpr D Gamma) :
    QFAssertExpr.BodyInvariant body
      (task.theta formula) := by
  intro before after hStep
  rw [task.theta_eval_iff, task.theta_eval_iff,
    task.semanticCollapse_eq_of_bigStep hStep]

end Task

end WhielNamesProphecy

end Hoare

end Whiel

------------------------------------------------------------
-- Cross-Role Reuse at the Request Level
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FixedAmbient

open Concrete

variable {D : Type} [Domain D]
variable {Gamma : UnnamedSchema WhielNames}
variable {body : Cmd D Gamma}

namespace ProphecyContext

/- Every prophecy premise of a level is body-invariant. -/
theorem premises_bodyInvariant
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard : Guard D Gamma)
    (level : Nat) :
    ∀ premise ∈ (build task family guard level).premises,
      QFAssertExpr.BodyInvariant body premise := by
  intro premise hPremise
  by_cases hZero : level = 0
  · subst level
    rw [premises_zero] at hPremise
    simp at hPremise
  · change premise ∈
      (if level = 0 then [] else
        QFAssertExpr.not (task.theta guard) ::
          ((family.below level).map fun clause =>
            task.theta clause.formula)) at hPremise
    rw [if_neg hZero] at hPremise
    simp only [List.mem_cons, List.mem_map] at hPremise
    rcases hPremise with rfl | ⟨clause, _, rfl⟩
    · exact (task.theta_bodyInvariant guard).not
    · exact task.theta_bodyInvariant clause.formula

end ProphecyContext

namespace LeveledFamily

/-
  Cross-role reuse at the request level. An initialization
  proof of `clause` whose cited premises lie among the
  prophecy premises of its level answers the step request
  of that level: the cited set is body-invariant, so it
  proves `wp(body, clause)`, and it is contained in the
  step request's premises. `hValid` is validity over every
  finite instance, the adom-empty ones included; the body
  may empty every relation, so the proof of `wp` needs the
  clause at such a state, and a solver proof's nonempty
  half plus an empty decision on the step request does not
  supply it. The contract therefore applies no cross-role
  reuse; the theorem records what such a rule would need.
-/
theorem maintenanceVC_valid_of_initProof
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard : Guard D Gamma)
    (hBody : body.LoopFree)
    (clause : LeveledClause D Gamma)
    {cited : List (QFAssertExpr D Gamma)}
    (hCited : cited ⊆
      (ProphecyContext.build task family guard
        clause.level).premises)
    (hValid :
      QFEntailment.Valid (D := D) (Γ := Gamma)
        ⟨cited, clause.formula⟩) :
    (family.maintenanceVC task guard hBody
      clause).Valid := by
  have hInvariant :
      ∀ premise ∈ cited,
        QFAssertExpr.BodyInvariant body premise :=
    fun premise hPremise =>
      ProphecyContext.premises_bodyInvariant
        task family guard clause.level premise
        (hCited hPremise)
  have hWp :=
    QFAssertExpr.wpLoopFree_valid_of_bodyInvariant
      body hBody hInvariant hValid
  apply QFEntailment.valid_of_axioms_subset _ hWp
  intro premise hPremise
  show premise ∈
    formulas (family.upTo clause.level) ++
      (guard ::
        (ProphecyContext.build task family guard
          clause.level).premises)
  apply List.mem_append_right
  exact List.mem_cons_of_mem guard (hCited hPremise)

end LeveledFamily

end FixedAmbient
end FrameworkII
end Synthesis
end Whiel

------------------------------------------------------------
-- Death at Any Level
------------------------------------------------------------

namespace Whiel
namespace Synthesis
namespace FrameworkII
namespace FixedAmbient

open Concrete

variable {D : Type} [Domain D]
variable {Gamma : UnnamedSchema WhielNames}
variable {body : Cmd D Gamma}

namespace LeveledFamily

/-
  The level-zero initialization request has exactly the
  precondition as its premise, which every level's request
  also carries.
-/
theorem initVC_zero_axioms_subset
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard pre : QFAssertExpr D Gamma)
    (clause : LeveledClause D Gamma) :
    (family.initVC task guard pre
      ⟨clause.formula, 0⟩).axioms ⊆
      (family.initVC task guard pre
        clause).axioms := by
  intro premise hPremise
  change premise ∈
    pre :: (ProphecyContext.build task family guard
      0).premises at hPremise
  rw [ProphecyContext.premises_zero] at hPremise
  rw [List.mem_singleton.mp hPremise]
  exact List.mem_cons.mpr (Or.inl rfl)

/-
  Death at any level, syntactically: a countermodel of the
  initialization request at any level is a countermodel of
  the level-zero request for the same clause, by refutation
  subsumption.
-/
theorem initVC_zero_countermodel_of_countermodel
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard pre : QFAssertExpr D Gamma)
    (clause : LeveledClause D Gamma)
    {state : Instance D Gamma}
    (h : QFEntailment.Countermodel
      (family.initVC task guard pre clause) state) :
    QFEntailment.Countermodel
      (family.initVC task guard pre ⟨clause.formula, 0⟩)
        state :=
  ⟨fun premise hPremise =>
      h.1 premise
        (family.initVC_zero_axioms_subset task guard pre
          clause hPremise),
    h.2⟩

/- The semantic initialization VC validates the syntax. -/
theorem initVC_valid_of_initObligation
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard pre : QFAssertExpr D Gamma)
    (clause : LeveledClause D Gamma)
    (hInit :
      Hoare.FixedAmbientProphecy.InitObligation
        task.prophecyCollapse guard family.semanticLevels
          pre.eval clause.level clause.formula.eval) :
    (family.initVC task guard pre clause).Valid := by
  intro state hAxioms
  apply hInit state
  · exact hAxioms pre (List.mem_cons.mpr (Or.inl rfl))
  · apply
      (ProphecyContext.premises_eval_iff_prophecyBelow
        task family guard clause.level state).mp
    intro premise hPremise
    exact hAxioms premise
      (List.mem_cons_of_mem pre hPremise)

/-
  Death at any level, semantically: the same countermodel
  refutes the level-zero semantic obligation, through the
  reduct lemma `initValid_of_initZeroValid` (a level-zero
  initialization is an initialization at every level).
-/
theorem not_initObligation_zero_of_countermodel
    (task : Task body)
    (family : LeveledFamily D Gamma)
    (guard pre : QFAssertExpr D Gamma)
    (clause : LeveledClause D Gamma)
    {state : Instance D Gamma}
    (h : QFEntailment.Countermodel
      (family.initVC task guard pre clause) state) :
    ¬ Hoare.FixedAmbientProphecy.InitObligation
        task.prophecyCollapse guard family.semanticLevels
          pre.eval 0 clause.formula.eval := by
  intro hZero
  have hLevel :=
    Hoare.FixedAmbientProphecy.initValid_of_initZeroValid
      task.prophecyCollapse guard family.semanticLevels
        pre.eval clause.level clause.formula.eval hZero
  exact QFEntailment.not_valid_of_countermodel h
    (family.initVC_valid_of_initObligation
      task guard pre clause hLevel)

end LeveledFamily

end FixedAmbient
end FrameworkII
end Synthesis
end Whiel
