-- Author: Jesse Comer
import Databases.Datalog.RuleSemantics
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sets

/-
  This file specifies the model-theoretic semantics of
  Datalog.

  The minimal model construction builds a finite maximal
  search space over the active domain, takes the
  pointwise intersection of all bounded models extending the
  input, and proves that intersection is the unique minimal
  model.

  Key definitions include:
    * `Program.Model`
    * `Program.Extends`
    * `Program.MinimalModel`

  The minimal model of a program extending an insance is
  computed by:
    * `Program.minimalModel`

  Correctness of the construction is proven by:
    * `Program.minimalModel_model`
    * `Program.minimalModel_extendsInput`
    * `Program.minimalModel_subset_of_model`
    * `Program.minimalModels_are_unique`
    * `Program.minimalModel_isMinimalModel`

  Intervening definitions and lemmas are computable
  construction and proof support.
-/

------------------------------------------------------------
-- Minimal Model Specification
------------------------------------------------------------

namespace Datalog

namespace Program

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  `P.Model J` means every rule of `P` is true in the
  program-schema instance `J`: for every assignment, if all
  relational atoms evaluate to facts of `J` (and equality
  atoms evaluate to true), then the head tuple is a fact of
  `J`.
-/
def Model
    (P : Program D Γ)
    (J : Instance D Γ) : Prop :=
  ∀ r : {r : Rule D Γ // r ∈ P.rules},
    ∀ σ : Assign D,
      r.1.bodySatisfied J σ →
        r.1.headSatisfied J σ

/-
  `P.Extends J I` means the program-schema instance `J`
  agrees with the EDB input instance `I` on every EDB
  relation of `P`.
-/
def Extends
    (P : Program D Γ)
    (J : Instance D Γ)
    (I : Instance D P.edbSchema) : Prop :=
  Instance.Extends P.ambient_extension_edbSchema I J

/-
  `P.MinimalModel I J` means `J` is a model extending the
  EDB input `I` and is contained, relation by relation, in
  every other model extending `I`.
-/
def MinimalModel
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (J : Instance D Γ) : Prop :=
  P.Model J ∧
    P.Extends J I ∧
    ∀ K : Instance D Γ,
      P.Model K →
        P.Extends K I →
          Instance.Subset J K

end Program

end Datalog

------------------------------------------------------------
-- Minimal Model Construction
------------------------------------------------------------

namespace Datalog

namespace Program

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ Ω : UnnamedSchema A}

/-
  Body satisfaction over a larger schema is ordinary body
  satisfaction after reducing the instance to the program
  schema.
-/
def bodySatisfiedOn
    (P : Program D Γ)
    (hProg : Ω.extensionOf Γ)
    (J : Instance D Ω)
    (r : {r : Rule D Γ // r ∈ P.rules})
    (σ : Assign D) : Prop :=
  r.1.bodySatisfied (Instance.reduct hProg J) σ

instance
    (P : Program D Γ)
    (hProg : Ω.extensionOf Γ)
    (J : Instance D Ω)
    (r : {r : Rule D Γ // r ∈ P.rules})
    (σ : Assign D) :
    Decidable (P.bodySatisfiedOn hProg J r σ) := by
  unfold bodySatisfiedOn
  infer_instance

/-
  Head satisfaction over a larger schema is ordinary head
  satisfaction after reducing the instance to the program
  schema.
-/
def headSatisfiedOn
    (P : Program D Γ)
    (hProg : Ω.extensionOf Γ)
    (J : Instance D Ω)
    (r : {r : Rule D Γ // r ∈ P.rules})
    (σ : Assign D) : Prop :=
  r.1.headSatisfied (Instance.reduct hProg J) σ

instance
    (P : Program D Γ)
    (hProg : Ω.extensionOf Γ)
    (J : Instance D Ω)
    (r : {r : Rule D Γ // r ∈ P.rules})
    (σ : Assign D) :
    Decidable (P.headSatisfiedOn hProg J r σ) := by
  unfold headSatisfiedOn
  infer_instance

/- Exact body satisfaction is the reflexive `On` case. -/
theorem bodySatisfied_of_bodySatisfiedOn_refl
    (P : Program D Γ)
    (J : Instance D Γ)
    (r : {r : Rule D Γ // r ∈ P.rules})
    (σ : Assign D)
    (hBody : P.bodySatisfiedOn
      (UnnamedSchema.extensionOf_refl Γ)
      J r σ) :
    r.1.bodySatisfied J σ := by
  simpa [bodySatisfiedOn] using hBody

/-
  Reflexive `On` body satisfaction follows from exact
  satisfaction.
-/
theorem bodySatisfiedOn_refl_of_bodySatisfied
    (P : Program D Γ)
    (J : Instance D Γ)
    (r : {r : Rule D Γ // r ∈ P.rules})
    (σ : Assign D)
    (hBody : r.1.bodySatisfied J σ) :
    P.bodySatisfiedOn
      (UnnamedSchema.extensionOf_refl Γ)
      J r σ := by
  simpa [bodySatisfiedOn] using hBody

/- Exact head satisfaction is the reflexive `On` case. -/
theorem headSatisfied_of_headSatisfiedOn_refl
    (P : Program D Γ)
    (J : Instance D Γ)
    (r : {r : Rule D Γ // r ∈ P.rules})
    (σ : Assign D)
    (hHead : P.headSatisfiedOn
      (UnnamedSchema.extensionOf_refl Γ)
      J r σ) :
    r.1.headSatisfied J σ := by
  simpa [headSatisfiedOn] using hHead

/-
  Reflexive `On` head satisfaction follows from exact
  satisfaction.
-/
theorem headSatisfiedOn_refl_of_headSatisfied
    (P : Program D Γ)
    (J : Instance D Γ)
    (r : {r : Rule D Γ // r ∈ P.rules})
    (σ : Assign D)
    (hHead : r.1.headSatisfied J σ) :
    P.headSatisfiedOn
      (UnnamedSchema.extensionOf_refl Γ)
      J r σ := by
  simpa [headSatisfiedOn] using hHead

/- A rule assignment respects the rule implication. -/
def RuleAssignmentModelOn
    (P : Program D Γ)
    (hProg : Ω.extensionOf Γ)
    (J : Instance D Ω)
    (r : {r : Rule D Γ // r ∈ P.rules})
    (u : Tuple D r.1.varList.length) : Prop :=
  P.bodySatisfiedOn hProg J r
      (Assign.ofListTuple r.1.varList u) →
    P.headSatisfiedOn hProg J r
      (Assign.ofListTuple r.1.varList u)

instance
    (P : Program D Γ)
    (hProg : Ω.extensionOf Γ)
    (J : Instance D Ω)
    (r : {r : Rule D Γ // r ∈ P.rules})
    (u : Tuple D r.1.varList.length) :
    Decidable (P.RuleAssignmentModelOn hProg J r u) := by
  unfold RuleAssignmentModelOn
  infer_instance

/- A rule is modeled over a finite value set. -/
def RuleModelOn
    (P : Program D Γ)
    (hProg : Ω.extensionOf Γ)
    (Q : Finset D)
    (J : Instance D Ω)
    (r : {r : Rule D Γ // r ∈ P.rules}) : Prop :=
  ∀ u : Tuple D r.1.varList.length,
    u ∈ Tuple.allOver Q r.1.varList.length →
      P.RuleAssignmentModelOn hProg J r u

instance
    (P : Program D Γ)
    (hProg : Ω.extensionOf Γ)
    (Q : Finset D)
    (J : Instance D Ω)
    (r : {r : Rule D Γ // r ∈ P.rules}) :
    Decidable (P.RuleModelOn hProg Q J r) := by
  unfold RuleModelOn
  infer_instance

/-
  Rule-list satisfaction, written recursively for
  decidability.
-/
def RulesModelOn
    (P : Program D Γ)
    (hProg : Ω.extensionOf Γ)
    (Q : Finset D)
    (J : Instance D Ω) :
    List {r : Rule D Γ // r ∈ P.rules} → Prop
| [] => True
| r :: rs =>
    P.RuleModelOn hProg Q J r ∧
      RulesModelOn P hProg Q J rs

instance
    (P : Program D Γ)
    (hProg : Ω.extensionOf Γ)
    (Q : Finset D)
    (J : Instance D Ω)
    (rs : List {r : Rule D Γ // r ∈ P.rules}) :
    Decidable (P.RulesModelOn hProg Q J rs) := by
  induction rs with
  | nil =>
      exact isTrue trivial
  | cons r rs ih =>
      unfold RulesModelOn
      exact instDecidableAnd

/- A finite instance models all rules of the program. -/
def ModelOn
    (P : Program D Γ)
    (hProg : Ω.extensionOf Γ)
    (Q : Finset D)
    (J : Instance D Ω) : Prop :=
  P.RulesModelOn hProg Q J P.rules.attach

instance
    (P : Program D Γ)
    (hProg : Ω.extensionOf Γ)
    (Q : Finset D)
    (J : Instance D Ω) :
    Decidable (P.ModelOn hProg Q J) := by
  unfold ModelOn
  infer_instance

/-
  A modeled rule can be extracted from a modeled rule
  list.
-/
theorem ruleModelOn_of_rulesModelOn
    (P : Program D Γ)
    (hProg : Ω.extensionOf Γ)
    (Q : Finset D)
    (J : Instance D Ω)
    {rs : List {r : Rule D Γ // r ∈ P.rules}}
    {r : {r : Rule D Γ // r ∈ P.rules}}
    (hr : r ∈ rs)
    (hRules : P.RulesModelOn hProg Q J rs) :
    P.RuleModelOn hProg Q J r := by
  induction rs with
  | nil =>
      cases hr
  | cons r₀ rs ih =>
      rcases List.mem_cons.mp hr with hEq | hrTail
      · subst hEq
        exact hRules.1
      · exact ih hrTail hRules.2

/- A modeled program models each attached rule. -/
theorem ruleModelOn_of_modelOn
    (P : Program D Γ)
    (hProg : Ω.extensionOf Γ)
    (Q : Finset D)
    (J : Instance D Ω)
    (r : {r : Rule D Γ // r ∈ P.rules})
    (hModel : P.ModelOn hProg Q J) :
    P.RuleModelOn hProg Q J r := by
  apply P.ruleModelOn_of_rulesModelOn
    (rs := P.rules.attach)
  · exact List.mem_attach _ _
  · exact hModel

/-
  An unbounded model is a bounded model over any finite
  value set.
-/
theorem modelOn_of_model
    (P : Program D Γ)
    (Q : Finset D)
    (J : Instance D Γ)
    (hModel : P.Model J) :
    P.ModelOn
      (UnnamedSchema.extensionOf_refl Γ)
      Q J := by
  unfold ModelOn
  induction P.rules.attach with
  | nil =>
      exact trivial
  | cons r rs ih =>
      constructor
      · intro u _hu hBody
        have hBodyExact :
            r.1.bodySatisfied J
              (Assign.ofListTuple r.1.varList u) :=
          P.bodySatisfied_of_bodySatisfiedOn_refl
            J r (Assign.ofListTuple r.1.varList u) hBody
        have hHeadExact :=
          hModel r (Assign.ofListTuple r.1.varList u) hBodyExact
        exact
          P.headSatisfiedOn_refl_of_headSatisfied
            J r (Assign.ofListTuple r.1.varList u) hHeadExact
      · exact ih

/- A finite model extending the input. -/
def BoundedModelExtending
    {Δ : UnnamedSchema A}
    (P : Program D Γ)
    (hProg : Ω.extensionOf Γ)
    (hInput : Ω.extensionOf Δ)
    (Q : Finset D)
    (I : Instance D Δ)
    (J : Instance D Ω) : Prop :=
  P.ModelOn hProg Q J ∧
    Instance.Extends hInput I J

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Ω : UnnamedSchema A}

/- Relations bounded by a finite relation. -/
abbrev BoundedRelation
    (R : FinRelation D n) :=
  {S : FinRelation D n // S ⊆ R}

instance
    (R : FinRelation D n) :
    Fintype (BoundedRelation (D := D) R) :=
  Fintype.ofFinset R.powerset
    (fun _ => Finset.mem_powerset)

instance
    (R : FinRelation D n) :
    DecidableEq (BoundedRelation (D := D) R) :=
  inferInstance

/- Instances bounded pointwise by a finite instance. -/
abbrev BoundedInstance
    (K : Instance D Ω) :=
  (X : Ω.syms) →
    BoundedRelation (D := D) (K X)

instance
    (K : Instance D Ω) :
    Fintype (BoundedInstance (D := D) K) := by
  let _ : Fintype Ω.syms :=
    Finset.fintypeCoeSort Ω.syms
  infer_instance

instance
    (K : Instance D Ω) :
    DecidableEq (BoundedInstance (D := D) K) := by
  infer_instance

/- Forget the pointwise boundedness proofs. -/
def BoundedInstance.toInstance
    {K : Instance D Ω}
    (J : BoundedInstance (D := D) K) :
    Instance D Ω :=
  fun X => (J X).1

/-
  Repackage a finite instance using pointwise containment
  in the bounding instance.
-/
def BoundedInstance.ofInstance
    {K : Instance D Ω}
    (J : Instance D Ω)
    (hM : Instance.Subset J K) :
    BoundedInstance (D := D) K :=
  fun X => ⟨J X, hM X⟩

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ Ω : UnnamedSchema A}

/-
  Membership is preserved by matching tuple/relation arity
  casts.
-/
omit [Domain D] in
theorem mem_cast_finRelation
    {n m : Nat}
    (h : n = m)
    {R : FinRelation D n}
    {t : Tuple D n} :
    cast (congrArg (Tuple D) h) t ∈
      cast (congrArg (FinRelation D) h) R ↔
        t ∈ R := by
  cases h
  simp

/-
  Membership in a cast relation can be pulled back along
  the cast.
-/
omit [Domain D] in
theorem mem_cast_finRelation_right
    {n m : Nat}
    (h : n = m)
    {R : FinRelation D n}
    {t : Tuple D m} :
    t ∈ cast (congrArg (FinRelation D) h) R ↔
      cast (congrArg (Tuple D) h.symm) t ∈ R := by
  cases h
  simp

/- Instance reduct is monotone in the larger instance. -/
theorem reduct_subset_of_subset
    (hExt : Ω.extensionOf Γ)
    {J K : Instance D Ω}
    (hSub : Instance.Subset J K) :
    Instance.Subset
      (Instance.reduct hExt J)
      (Instance.reduct hExt K) := by
  intro X t ht
  let hAr := UnnamedSchema.arity_eq_of_extensionOf hExt X
  have htM :
      cast (congrArg (Tuple D) hAr.symm) t ∈
        J (UnnamedSchema.symOfExtension hExt X) := by
    simpa [Instance.reduct, hAr, UnnamedSchema.symOfExtension]
      using (mem_cast_finRelation_right hAr).mp ht
  have htN :=
    hSub (UnnamedSchema.symOfExtension hExt X) htM
  exact
    (mem_cast_finRelation_right hAr).mpr
      (by
        simpa [UnnamedSchema.symOfExtension] using htN)

/- Extension-schema body satisfaction is monotone. -/
theorem bodySatisfiedOn_mono
    (P : Program D Γ)
    (hProg : Ω.extensionOf Γ)
    {J K : Instance D Ω}
    (hSub : Instance.Subset J K)
    (r : {r : Rule D Γ // r ∈ P.rules})
    (σ : Assign D)
    (hBody : P.bodySatisfiedOn hProg J r σ) :
    P.bodySatisfiedOn hProg K r σ := by
  unfold bodySatisfiedOn Rule.bodySatisfied at hBody ⊢
  exact
    Body.satisfied_mono
      (reduct_subset_of_subset hProg hSub)
      r.1.body hBody

/-
  Reduct-based head satisfaction is equivalent to the
  explicit tuple transport used by the construction.
-/
theorem headSatisfiedOn_iff_toExtension
    (P : Program D Γ)
    (hProg : Ω.extensionOf Γ)
    (J : Instance D Ω)
    (r : {r : Rule D Γ // r ∈ P.rules})
    (σ : Assign D) :
    P.headSatisfiedOn hProg J r σ ↔
      Tuple.toExtension hProg r.1.head.rel
        (r.1.head.evalTuple σ) ∈
          J (UnnamedSchema.symOfExtension hProg r.1.head.rel) := by
  unfold headSatisfiedOn Rule.headSatisfied RelAtom.Sat
    Instance.reduct Tuple.toExtension
  exact
    mem_cast_finRelation_right
      (UnnamedSchema.arity_eq_of_extensionOf
        hProg r.1.head.rel)

/-
  Tuple casts preserve the property of being over a value
  set.
-/
omit [Domain D] in
theorem isTupleOver_cast
    {n m : Nat}
    (h : n = m)
    {Q : Finset D}
    {t : Tuple D n} :
    (cast (congrArg (Tuple D) h) t).isTupleOver Q ↔
      t.isTupleOver Q := by
  cases h
  rfl

/-
  Extension-relation membership preserves active-domain
  containment.
-/
theorem isTupleOver_of_mem_relationOfExtension
    {Δ Ω : UnnamedSchema A}
    (hExt : Ω.extensionOf Δ)
    (I : Instance D Δ)
    (X : Ω.syms)
    (hX : X.1 ∈ Δ.syms)
    {t : Tuple D (Ω.arity X)}
    (ht : t ∈ Instance.relationOfExtension hExt I X hX) :
    t.isTupleOver I.Adom := by
  unfold Instance.relationOfExtension at ht
  let hAr :=
    UnnamedSchema.arity_eq_of_extension_mem hExt X hX
  have htOrig :
      cast (congrArg (Tuple D) hAr.symm) t ∈
        I ⟨X.1, hX⟩ :=
    (mem_cast_finRelation_right hAr).mp ht
  have hOver :=
    I.isTupleOver_Adom_of_mem htOrig
  exact (isTupleOver_cast hAr.symm).mp hOver

/- All head tuples that a rule can produce over `Q`. -/
def ruleHeadSpace
    (Q : Finset D)
    (r : Rule D Γ) :
    FinRelation D (Γ.arity r.head.rel) :=
  (Tuple.allOver Q r.varList.length).image
    (fun u => r.head.evalTuple (Assign.ofListTuple r.varList u))

/-
  Rule-head tuples generated over `Q` have entries in
  `Q`.
-/
theorem ruleHeadSpace_tuple_over
    (Q : Finset D)
    (r : Rule D Γ)
    {t : Tuple D (Γ.arity r.head.rel)}
    (ht : t ∈ ruleHeadSpace Q r) :
    t.isTupleOver Q := by
  unfold ruleHeadSpace at ht
  rcases Finset.mem_image.mp ht with ⟨u, hu, hEq⟩
  subst hEq
  intro i
  rcases
      r.head.exists_var_mem_varList_of_constFree_getElem
        r.noHeadConst i.2 with
    ⟨x, hArg, hxHead⟩
  have hxRule := r.head_var_mem_varList hxHead
  have hVal :=
    Assign.ofListTuple_mem_of_mem_allOver hu hxRule
  change
    (r.head.evalTuple
      (Assign.ofListTuple r.varList u))[i.1] ∈ Q
  simp [RelAtom.evalTuple, RelTerm.evalVector_eq_map,
    Vector.getElem_map, hArg, RelTerm.eval, hVal]

/- Matching rule heads have the output symbol's arity. -/
theorem head_arity_eq_of_match
    (P : Program D Γ)
    (hProg : Ω.extensionOf Γ)
    (X : Ω.syms)
    {r : Rule D Γ}
    (hr : r ∈ P.rules)
    (h : r.head.rel.1 = X.1) :
    Γ.arity r.head.rel = Ω.arity X := by
  have hSym : r.head.rel.1 ∈ P.symbolNamesOf :=
    P.head_mem_symbolNames hr
  have hEq :
      (⟨r.head.rel.1, hProg.1 hSym⟩ : Ω.syms) = X := by
    exact Subtype.ext h
  have hExt :=
    UnnamedSchema.arity_eq_of_extensionOf
      hProg ⟨r.head.rel.1, hSym⟩
  have hProgAr :
      P.progSchema.arity ⟨r.head.rel.1, hSym⟩ =
        Γ.arity r.head.rel := by
    simp [progSchema]
  have hΩ :
      Ω.arity X = Γ.arity r.head.rel := by
    simpa [hEq, hProgAr] using hExt
  exact hΩ.symm

/- The rule-head space for one output symbol. -/
def headSpaceForList
    (P : Program D Γ)
    (hProg : Ω.extensionOf Γ)
    (Q : Finset D)
    (X : Ω.syms) :
    List {r : Rule D Γ // r ∈ P.rules} →
      FinRelation D (Ω.arity X)
| [] => ∅
| r :: rs =>
    let rest := headSpaceForList P hProg Q X rs
    if h : r.1.head.rel.1 = X.1 then
      have hAr :
          Γ.arity r.1.head.rel = Ω.arity X := by
        exact P.head_arity_eq_of_match hProg X r.2 h
      cast (congrArg (FinRelation D) hAr)
        (ruleHeadSpace Q r.1) ∪ rest
    else
      rest

/-
  Membership in a rule's head space propagates to the
  list space.
-/
theorem mem_headSpaceForList_of_mem
    (P : Program D Γ)
    (hProg : Ω.extensionOf Γ)
    (Q : Finset D)
    (X : Ω.syms)
    {rs : List {r : Rule D Γ // r ∈ P.rules}}
    {r : {r : Rule D Γ // r ∈ P.rules}}
    (hr : r ∈ rs)
    (hHead : r.1.head.rel.1 = X.1)
    {u : Tuple D r.1.varList.length}
    (hu : u ∈ Tuple.allOver Q r.1.varList.length) :
    cast
      (congrArg (Tuple D)
        (P.head_arity_eq_of_match
          hProg X r.2 hHead))
      (r.1.head.evalTuple (Assign.ofListTuple r.1.varList u)) ∈
        P.headSpaceForList hProg Q X rs := by
  induction rs with
  | nil =>
      cases hr
  | cons r₀ rs ih =>
      rcases List.mem_cons.mp hr with hEq | hrTail
      · subst hEq
        dsimp only [headSpaceForList]
        rw [dif_pos hHead]
        exact Finset.mem_union.mpr
          (Or.inl
            ((mem_cast_finRelation
              (P.head_arity_eq_of_match
                hProg X r.2 hHead)).mpr
              (Finset.mem_image.mpr ⟨u, hu, rfl⟩)))
      · dsimp only [headSpaceForList]
        by_cases h₀ : r₀.1.head.rel.1 = X.1
        · rw [dif_pos h₀]
          exact Finset.mem_union.mpr
            (Or.inr (ih hrTail))
        · rw [dif_neg h₀]
          exact ih hrTail

/-
  Tuples in a rule-list head space have entries in
  `Q`.
-/
theorem headSpaceForList_tuple_over
    (P : Program D Γ)
    (hProg : Ω.extensionOf Γ)
    (Q : Finset D)
    (X : Ω.syms) :
    ∀ {rs : List {r : Rule D Γ // r ∈ P.rules}},
      ∀ {t : Tuple D (Ω.arity X)},
        t ∈ P.headSpaceForList hProg Q X rs →
          t.isTupleOver Q
| [], _t, ht => by
    cases ht
| r :: rs, t, ht => by
    dsimp only [headSpaceForList] at ht
    by_cases hHead : r.1.head.rel.1 = X.1
    · rw [dif_pos hHead] at ht
      rcases Finset.mem_union.mp ht with htRule | htRest
      · have hAr :=
          P.head_arity_eq_of_match hProg X r.2 hHead
        have hOrig :
            cast (congrArg (Tuple D) hAr.symm) t ∈
              ruleHeadSpace Q r.1 :=
          (mem_cast_finRelation_right hAr).mp htRule
        have hOver :=
          ruleHeadSpace_tuple_over Q r.1 hOrig
        exact (isTupleOver_cast hAr.symm).mp hOver
      · exact
          P.headSpaceForList_tuple_over
            hProg Q X htRest
    · rw [dif_neg hHead] at ht
      exact P.headSpaceForList_tuple_over hProg Q X ht

/-
  The finite head-tuples available for one output symbol.
-/
def headSpaceFor
    (P : Program D Γ)
    (hProg : Ω.extensionOf Γ)
    (Q : Finset D)
    (X : Ω.syms) :
    FinRelation D (Ω.arity X) :=
  P.headSpaceForList hProg Q X P.rules.attach

/-
  Tuples in a symbol's head space have entries in `Q`.
-/
theorem headSpaceFor_tuple_over
    (P : Program D Γ)
    (hProg : Ω.extensionOf Γ)
    (Q : Finset D)
    (X : Ω.syms)
    {t : Tuple D (Ω.arity X)}
    (ht : t ∈ P.headSpaceFor hProg Q X) :
    t.isTupleOver Q :=
  P.headSpaceForList_tuple_over hProg Q X ht

/-
  A rule head generated over `Q` lies in its symbol's
  head space.
-/
theorem mem_headSpaceFor_of_rule
    (P : Program D Γ)
    (hProg : Ω.extensionOf Γ)
    (Q : Finset D)
    (X : Ω.syms)
    {r : Rule D Γ}
    (hr : r ∈ P.rules)
    (hHead : r.head.rel.1 = X.1)
    {u : Tuple D r.varList.length}
    (hu : u ∈ Tuple.allOver Q r.varList.length) :
    cast
      (congrArg (Tuple D)
        (P.head_arity_eq_of_match hProg X hr hHead))
      (r.head.evalTuple (Assign.ofListTuple r.varList u)) ∈
        P.headSpaceFor hProg Q X := by
  let r' : {r : Rule D Γ // r ∈ P.rules} :=
    ⟨r, hr⟩
  have hr' : r' ∈ P.rules.attach :=
    List.mem_attach _ _
  simpa [headSpaceFor, r'] using
    P.mem_headSpaceForList_of_mem
      hProg Q X hr' hHead hu

/-
  The finite search space used for the intersection. It
  fixes input relations exactly and bounds every other
  output symbol by the head tuples the program can produce
  over `Q`.
-/
def maxModel
    {Δ : UnnamedSchema A}
    (P : Program D Γ)
    (hProg : Ω.extensionOf Γ)
    (hInput : Ω.extensionOf Δ)
    (Q : Finset D)
    (I : Instance D Δ) :
    Instance D Ω :=
  fun X =>
    if hX : X.1 ∈ Δ.syms then
      Instance.relationOfExtension hInput I X hX
    else
      P.headSpaceFor hProg Q X

/-
  Bounded candidates are finite models living inside a
  bounding instance.
-/
def BoundedCandidate
    {Δ : UnnamedSchema A}
    (P : Program D Γ)
    (hProg : Ω.extensionOf Γ)
    (hInput : Ω.extensionOf Δ)
    (Q : Finset D)
    (I : Instance D Δ)
    (K : Instance D Ω)
    (J : BoundedInstance (D := D) K) : Prop :=
  P.BoundedModelExtending hProg hInput Q I J.toInstance

instance
    {Δ : UnnamedSchema A}
    (P : Program D Γ)
    (hProg : Ω.extensionOf Γ)
    (hInput : Ω.extensionOf Δ)
    (Q : Finset D)
    (I : Instance D Δ)
    (K : Instance D Ω)
    (J : BoundedInstance (D := D) K) :
    Decidable
      (P.BoundedCandidate hProg hInput Q I K J) := by
  unfold BoundedCandidate BoundedModelExtending
  infer_instance

/-
  The finite intersection of all bounded candidates. The
  use of `BoundedInstance` makes this a genuine `Instance`
  constructively.
-/
def intersection
    {Δ : UnnamedSchema A}
    (P : Program D Γ)
    (hProg : Ω.extensionOf Γ)
    (hInput : Ω.extensionOf Δ)
    (Q : Finset D)
    (I : Instance D Δ)
    (K : Instance D Ω) :
    Instance D Ω :=
  fun X =>
    (K X).filter
      (fun t =>
        ∀ J : BoundedInstance (D := D) K,
          P.BoundedCandidate hProg hInput Q I K J →
            t ∈ J.toInstance X)

/- Membership in the finite intersection. -/
theorem mem_intersection_iff
    {Δ : UnnamedSchema A}
    (P : Program D Γ)
    (hProg : Ω.extensionOf Γ)
    (hInput : Ω.extensionOf Δ)
    (Q : Finset D)
    (I : Instance D Δ)
    (K : Instance D Ω)
    {X : Ω.syms}
    {t : Tuple D (Ω.arity X)} :
    t ∈ P.intersection hProg hInput Q I K X ↔
      t ∈ K X ∧
        ∀ J : BoundedInstance (D := D) K,
          P.BoundedCandidate hProg hInput Q I K J →
            t ∈ J.toInstance X := by
  simp [intersection]

/-
  The intersection is contained in every bounded
  candidate.
-/
theorem intersection_subset_boundedCandidate
    {Δ : UnnamedSchema A}
    (P : Program D Γ)
    (hProg : Ω.extensionOf Γ)
    (hInput : Ω.extensionOf Δ)
    (Q : Finset D)
    (I : Instance D Δ)
    (K : Instance D Ω)
    (J : BoundedInstance (D := D) K)
    (hM : P.BoundedCandidate hProg hInput Q I K J) :
    Instance.Subset
      (P.intersection hProg hInput Q I K)
      J.toInstance := by
  intro X t ht
  exact
    (P.mem_intersection_iff
      hProg hInput Q I K).mp ht |>.2 J hM

/-
  The intersection is contained in every candidate below
  the bounding instance.
-/
theorem intersection_subset_boundedModel
    {Δ : UnnamedSchema A}
    (P : Program D Γ)
    (hProg : Ω.extensionOf Γ)
    (hInput : Ω.extensionOf Δ)
    (Q : Finset D)
    (I : Instance D Δ)
    (K J : Instance D Ω)
    (hM : P.BoundedModelExtending hProg hInput Q I J)
    (hMbase : Instance.Subset J K) :
    Instance.Subset
      (P.intersection hProg hInput Q I K) J := by
  let BM :=
    BoundedInstance.ofInstance (D := D) J hMbase
  have hCand :
      P.BoundedCandidate hProg hInput Q I K BM := by
    simpa [BM, BoundedCandidate] using hM
  intro X t ht
  have hSub :=
    P.intersection_subset_boundedCandidate
      hProg hInput Q I K BM hCand X ht
  simpa [BM] using hSub

/- The maximal finite search space agrees with the input. -/
theorem maxModel_extendsInput
    {Δ : UnnamedSchema A}
    (P : Program D Γ)
    (hProg : Ω.extensionOf Γ)
    (hInput : Ω.extensionOf Δ)
    (Q : Finset D)
    (I : Instance D Δ) :
    Instance.Extends hInput I
      (P.maxModel hProg hInput Q I) := by
  intro X hX
  simp [maxModel, hX]

/-
  If the bounding instance agrees with the input, so does its
  intersection.
-/
theorem intersection_extendsInput
    {Δ : UnnamedSchema A}
    (P : Program D Γ)
    (hProg : Ω.extensionOf Γ)
    (hInput : Ω.extensionOf Δ)
    (Q : Finset D)
    (I : Instance D Δ)
    (K : Instance D Ω)
    (hBase : Instance.Extends hInput I K) :
    Instance.Extends hInput I
      (P.intersection hProg hInput Q I K) := by
  intro X hX
  apply Finset.ext
  intro t
  constructor
  · intro ht
    have htBase :=
      (P.mem_intersection_iff
        hProg hInput Q I K).mp ht |>.1
    simpa [hBase X hX] using htBase
  · intro ht
    rw [mem_intersection_iff]
    constructor
    · simpa [hBase X hX] using ht
    · intro J hM
      have hInputM :
          J.toInstance X =
            Instance.relationOfExtension hInput I X hX := by
        exact hM.2 X hX
      simpa [hInputM] using ht

/-
  The model-theoretic minimal model over the program
  schema.
-/
def minimalModel
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    Instance D Γ :=
  let hProg := UnnamedSchema.extensionOf_refl Γ
  let hInput := P.ambient_extension_edbSchema
  let Q := P.adom I
  P.intersection hProg hInput Q I
    (P.maxModel hProg hInput Q I)

end Program

end Datalog

------------------------------------------------------------
-- Minimal Model Properties
------------------------------------------------------------

namespace Datalog

namespace Program

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ Ω : UnnamedSchema A}

/-
  Every fact in the minimal model is over the active
  domain of the input.
-/
theorem minimalModel_tuple_over_adom
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    {X : P.progSchema.syms}
    {t : Tuple D (P.progSchema.arity X)}
    (ht : t ∈ P.minimalModel I X) :
    t.isTupleOver (P.adom I) := by
  unfold minimalModel at ht
  let hProg := UnnamedSchema.extensionOf_refl Γ
  let hInput := P.ambient_extension_edbSchema
  let Q := P.adom I
  let K := P.maxModel hProg hInput Q I
  have htBase :
      t ∈ K X :=
    (P.mem_intersection_iff
      hProg hInput Q I K).mp ht |>.1
  unfold K maxModel at htBase
  by_cases hX : X.1 ∈ P.edbSchema.syms
  · rw [dif_pos hX] at htBase
    have hOver :=
      isTupleOver_of_mem_relationOfExtension
        hInput I X hX htBase
    exact Tuple.isTupleOver_mono
      (by
        intro d hd
        exact Finset.mem_union.mpr (Or.inl hd))
      hOver
  · rw [dif_neg hX] at htBase
    exact P.headSpaceFor_tuple_over hProg Q X htBase

/-
  Body-variable values used by the minimal model are over the
  active domain.
-/
theorem value_mem_adom_of_body_var
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (r : {r : Rule D Γ // r ∈ P.rules})
    (σ : Assign D)
    (hBody : r.1.bodySatisfied (P.minimalModel I) σ)
    {x : Var}
    (hx : x ∈ Body.varList r.1.body) :
    σ x ∈ P.adom I := by
  have hxBodyVars : x ∈ Body.vars r.1.body := by
    change x ∈ Atom.vars r.1.body
    unfold Atom.vars
    exact List.mem_toFinset.mpr hx
  have hxRel : x ∈ Body.relVarList r.1.body := by
    have hSafe :=
      r.1.safe x
        (Finset.mem_union.mpr (Or.inr hxBodyVars))
    change x ∈ Atom.relVars r.1.body at hSafe
    unfold Atom.relVars at hSafe
    exact List.mem_toFinset.mp hSafe
  unfold Body.relVarList Atom.listRelVarList at hxRel
  rw [List.mem_flatten] at hxRel
  rcases hxRel with ⟨vars, hVars, hxVars⟩
  rcases List.mem_map.mp hVars with ⟨b, hb, hEq⟩
  cases b with
  | rel a =>
      have hxAtom : x ∈ a.varList := by
        simpa [Atom.relVarList, ← hEq] using hxVars
      have hAtom : a.Sat (P.minimalModel I) σ := by
        have hSat :=
          Body.sat_of_satisfied
            (P.minimalModel I) σ r.1.body hb hBody
        simpa [Atom.Sat] using hSat
      have hProgOver :=
        P.minimalModel_tuple_over_adom I hAtom
      have hSym : a.rel.1 ∈ P.symbolNamesOf :=
        P.body_rel_atom_mem_symbolNames r.2 hb
      have hEvalOver :
          (a.evalTuple σ).isTupleOver (P.adom I) := by
        simpa [tupleToProg] using
          (isTupleOver_cast
            (P.prog_arity_eq a.rel
              hSym).symm).mp
            hProgOver
      exact
        a.value_mem_of_var_mem_evalTuple_over
          hEvalOver hxAtom
  | eq lhs rhs =>
      simp [Atom.relVarList] at hEq
      subst vars
      cases hxVars

/-
  Rule-variable values used by the minimal model are over the
  active domain.
-/
theorem value_mem_adom_of_rule_var
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (r : {r : Rule D Γ // r ∈ P.rules})
    (σ : Assign D)
    (hBody : r.1.bodySatisfied (P.minimalModel I) σ)
    {x : Var}
    (hx : x ∈ r.1.varList) :
    σ x ∈ P.adom I := by
  have hxAppend :
      x ∈ r.1.head.varList ++ Body.varList r.1.body := by
    simpa [Rule.varList] using (List.mem_dedup.mp hx)
  rcases List.mem_append.mp hxAppend with hxHead | hxBody
  · have hxHeadVars : x ∈ r.1.head.vars := by
      exact r.1.head.mem_vars_of_mem_varList hxHead
    have hBodyVar : x ∈ Body.varList r.1.body := by
      have hSafe :=
        r.1.safe x
          (Finset.mem_union.mpr (Or.inl hxHeadVars))
      have hxRel : x ∈ Body.relVarList r.1.body := by
        change x ∈ Atom.relVars r.1.body at hSafe
        unfold Atom.relVars at hSafe
        exact List.mem_toFinset.mp hSafe
      unfold Body.relVarList Atom.listRelVarList at hxRel
      rw [List.mem_flatten] at hxRel
      rcases hxRel with ⟨vars, hVars, hxVars⟩
      rcases List.mem_map.mp hVars with ⟨b, hb, hEq⟩
      unfold Body.varList Atom.listVarList
      rw [List.mem_flatten]
      refine ⟨b.varList, ?_, ?_⟩
      · exact List.mem_map.mpr ⟨b, hb, rfl⟩
      · cases b with
        | rel a =>
            simpa [Atom.varList, Atom.relVarList,
              ← hEq] using hxVars
        | eq lhs rhs =>
            simp [Atom.relVarList] at hEq
            subst vars
            cases hxVars
    exact P.value_mem_adom_of_body_var I r σ hBody hBodyVar
  · exact P.value_mem_adom_of_body_var I r σ hBody hxBody

/-
  The maximal search space contains every rule head over
  the adom.
-/
theorem holdsHead_maxModel
    {Δ : UnnamedSchema A}
    (P : Program D Γ)
    (hProg : Ω.extensionOf Γ)
    (hInput : Ω.extensionOf Δ)
    (hNoIdb : Disjoint Δ.syms P.idbNames)
    (I : Instance D Δ)
    (r : {r : Rule D Γ // r ∈ P.rules})
    {u : Tuple D r.1.varList.length}
    (hu :
      u ∈ Tuple.allOver
        (P.adom I) r.1.varList.length) :
    P.headSatisfiedOn hProg
      (P.maxModel
        hProg
        hInput
        (P.adom I) I)
      r (Assign.ofListTuple r.1.varList u) := by
  let X := UnnamedSchema.symOfExtension hProg (P.headSym r)
  have hNotInput : X.1 ∉ Δ.syms := by
    intro hxΔ
    have hIdb : X.1 ∈ P.idbNames := by
      have hHead : r.1.head.rel.1 ∈ P.idbNames := by
        unfold idbNames symbolNames
        exact
          Finset.mem_image.mpr
            ⟨r.1.head.rel, P.head_mem_idb r.2, rfl⟩
      simpa [X, UnnamedSchema.symOfExtension, headSym]
        using hHead
    exact (Finset.disjoint_left.mp hNoIdb) hxΔ hIdb
  have hHeadEq : r.1.head.rel.1 = X.1 := by
    simp [X, UnnamedSchema.symOfExtension, headSym]
  have hNotHead : r.1.head.rel.1 ∉ Δ.syms := by
    simpa [X, UnnamedSchema.symOfExtension, headSym] using
      hNotInput
  have hMem :=
    P.mem_headSpaceFor_of_rule hProg (P.adom I) X
      r.2 hHeadEq hu
  rw [P.headSatisfiedOn_iff_toExtension]
  simpa [maxModel, hNotInput, hNotHead, X,
    hProg, hInput, UnnamedSchema.symOfExtension, headSym,
    Tuple.toExtension, tupleToProg] using hMem

/- Intersect two instances pointwise. -/
def intersectInstance
    (J K : Instance D Ω) :
    Instance D Ω :=
  fun X => J X ∩ K X

/-
  The pointwise intersection is contained in its left
  side.
-/
theorem intersectInstance_subset_left
    (J K : Instance D Ω) :
    Instance.Subset (intersectInstance J K) J := by
  intro X t ht
  exact (Finset.mem_inter.mp ht).1

/-
  The pointwise intersection is contained in its right
  side.
-/
theorem intersectInstance_subset_right
    (J K : Instance D Ω) :
    Instance.Subset (intersectInstance J K) K := by
  intro X t ht
  exact (Finset.mem_inter.mp ht).2

/-
  Input agreement is preserved by pointwise intersection.
-/
theorem intersectInstance_extendsInput
    {Δ : UnnamedSchema A}
    (hInput : Ω.extensionOf Δ)
    (I : Instance D Δ)
    {J K : Instance D Ω}
    (hM : Instance.Extends hInput I J)
    (hN : Instance.Extends hInput I K) :
    Instance.Extends hInput I (intersectInstance J K) := by
  intro X hX
  apply Finset.ext
  intro t
  constructor
  · intro ht
    have htM := (Finset.mem_inter.mp ht).1
    simpa [hM X hX] using htM
  · intro ht
    exact Finset.mem_inter.mpr
      ⟨by simpa [hM X hX] using ht,
        by simpa [hN X hX] using ht⟩

/-
  Head satisfaction is preserved by pointwise intersection.
-/
theorem holdsHead_intersectInstance
    (P : Program D Γ)
    (hProg : Ω.extensionOf Γ)
    (J K : Instance D Ω)
    (r : {r : Rule D Γ // r ∈ P.rules})
    (σ : Assign D)
    (hM : P.headSatisfiedOn hProg J r σ)
    (hN : P.headSatisfiedOn hProg K r σ) :
    P.headSatisfiedOn hProg (intersectInstance J K) r σ := by
  rw [P.headSatisfiedOn_iff_toExtension] at hM hN ⊢
  exact Finset.mem_inter.mpr ⟨hM, hN⟩

/-
  Pruning a model against the maximal search space
  preserves modeling.
-/
theorem intersect_maxModel_modelOn
    {Δ : UnnamedSchema A}
    (P : Program D Γ)
    (hProg : Ω.extensionOf Γ)
    (hInput : Ω.extensionOf Δ)
    (hNoIdb : Disjoint Δ.syms P.idbNames)
    (I : Instance D Δ)
    (J : Instance D Ω)
    (hM : P.ModelOn hProg (P.adom I) J) :
    P.ModelOn hProg (P.adom I)
      (intersectInstance J
        (P.maxModel hProg hInput (P.adom I) I)) := by
  let Q := P.adom I
  let K := P.maxModel hProg hInput Q I
  unfold ModelOn
  change P.RulesModelOn hProg Q
    (intersectInstance J K) P.rules.attach
  induction P.rules.attach with
  | nil =>
      exact trivial
  | cons r rs ih =>
      constructor
      · intro u hu hBody
        unfold RuleAssignmentModelOn at *
        have hBodyM :
            P.bodySatisfiedOn hProg J r
              (Assign.ofListTuple r.1.varList u) :=
          P.bodySatisfiedOn_mono hProg
            (intersectInstance_subset_left J K)
            r (Assign.ofListTuple r.1.varList u) hBody
        have hRule :=
          P.ruleModelOn_of_modelOn hProg Q J r hM
        have hHeadM := hRule u hu hBodyM
        have hHeadBase :
            P.headSatisfiedOn hProg K r
              (Assign.ofListTuple r.1.varList u) := by
          simpa [hProg, Q, K] using
            P.holdsHead_maxModel hProg
              hInput hNoIdb I r hu
        exact
          P.holdsHead_intersectInstance
            hProg J K r (Assign.ofListTuple r.1.varList u)
            hHeadM hHeadBase
      · exact ih

end Program

namespace Program

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  The minimal model construction is a bounded model over
  the active domain.
-/
theorem minimalModel_modelOn
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    P.ModelOn
      (UnnamedSchema.extensionOf_refl Γ)
      (P.adom I) (P.minimalModel I) := by
  let hProg := UnnamedSchema.extensionOf_refl Γ
  let hInput := P.ambient_extension_edbSchema
  let Q := P.adom I
  let K := P.maxModel hProg hInput Q I
  unfold ModelOn
  change P.RulesModelOn hProg Q
    (P.minimalModel I) P.rules.attach
  induction P.rules.attach with
  | nil =>
      exact trivial
  | cons r rs ih =>
      constructor
      · intro u hu hBody
        unfold RuleAssignmentModelOn at *
        rw [P.headSatisfiedOn_iff_toExtension]
        unfold minimalModel
        rw [mem_intersection_iff]
        constructor
        · have hMax :
              P.headSatisfiedOn hProg K r
                (Assign.ofListTuple r.1.varList u) := by
            simpa [K, Q] using
              P.holdsHead_maxModel hProg hInput
                P.disjoint_edb_idb I r hu
          exact
            (P.headSatisfiedOn_iff_toExtension
              hProg K r
              (Assign.ofListTuple r.1.varList u)).mp hMax
        · intro J hM
          have hSub :=
            P.intersection_subset_boundedCandidate
              hProg hInput Q I K J hM
          have hBodyM :
              P.bodySatisfiedOn hProg J.toInstance r
                (Assign.ofListTuple r.1.varList u) :=
            P.bodySatisfiedOn_mono hProg hSub r
              (Assign.ofListTuple r.1.varList u) hBody
          have hRule :=
            P.ruleModelOn_of_modelOn hProg Q
              J.toInstance r hM.1
          exact hRule u hu hBodyM
      · exact ih

/- The minimal model preserves the EDB input exactly. -/
theorem minimalModel_extendsInput
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    Instance.Extends P.ambient_extension_edbSchema I
      (P.minimalModel I) := by
  unfold minimalModel
  let hProg := UnnamedSchema.extensionOf_refl Γ
  let hInput := P.ambient_extension_edbSchema
  let Q := P.adom I
  exact
    P.intersection_extendsInput hProg hInput Q I
      (P.maxModel hProg hInput Q I)
      (P.maxModel_extendsInput hProg hInput Q I)

/-
  The concrete minimal model satisfies the unbounded model
  specification.
-/
theorem minimalModel_model
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    P.Model (P.minimalModel I) := by
  intro r σ hBody
  let u := Assign.toListTuple r.1.varList σ
  have hu :
      u ∈
        Tuple.allOver
          (P.adom I) r.1.varList.length := by
    dsimp [u]
    apply Assign.toListTuple_mem_allOver_of_forall_mem
    intro x hx
    exact P.value_mem_adom_of_rule_var I r σ hBody hx
  have hBodyU :
      r.1.bodySatisfied (P.minimalModel I)
        (Assign.ofListTuple r.1.varList u) := by
    apply r.1.bodySatisfied_congr_assign (P.minimalModel I) ?_ hBody
    intro x hx
    dsimp [u]
    exact (Assign.ofListTuple_toListTuple_of_mem hx).symm
  have hBodyOn :
      P.bodySatisfiedOn
        (UnnamedSchema.extensionOf_refl Γ)
        (P.minimalModel I) r
        (Assign.ofListTuple r.1.varList u) :=
    P.bodySatisfiedOn_refl_of_bodySatisfied
      (P.minimalModel I) r
      (Assign.ofListTuple r.1.varList u) hBodyU
  have hRule :=
    P.ruleModelOn_of_modelOn
      (UnnamedSchema.extensionOf_refl Γ)
      (P.adom I) (P.minimalModel I) r
      (P.minimalModel_modelOn I)
  have hHeadOn := hRule u hu hBodyOn
  have hHeadU :
      r.1.headSatisfied (P.minimalModel I)
        (Assign.ofListTuple r.1.varList u) :=
    P.headSatisfied_of_headSatisfiedOn_refl
      (P.minimalModel I) r
      (Assign.ofListTuple r.1.varList u) hHeadOn
  exact
    (r.1.headSatisfied_congr_assign (P.minimalModel I)
      (fun x hx => by
        dsimp [u]
        exact Assign.ofListTuple_toListTuple_of_mem hx)).1 hHeadU

/-
  The minimal model is contained in every finite model extending
  the input.
-/
theorem minimalModel_subset_of_model
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (J : Instance D Γ)
    (hModel : P.Model J)
    (hInputM : P.Extends J I) :
    Instance.Subset (P.minimalModel I) J := by
  let hProg := UnnamedSchema.extensionOf_refl Γ
  let hInput := P.ambient_extension_edbSchema
  let Q := P.adom I
  let K := P.maxModel hProg hInput Q I
  let J' := intersectInstance J K
  have hMOn :
      P.ModelOn hProg Q J :=
    P.modelOn_of_model Q J hModel
  have hNModel :
      P.ModelOn hProg Q J' := by
    simpa [J', hProg, hInput, Q, K] using
      P.intersect_maxModel_modelOn hProg hInput
        P.disjoint_edb_idb I J hMOn
  have hNInput :
      Instance.Extends hInput I J' := by
    exact intersectInstance_extendsInput hInput I
      hInputM (P.maxModel_extendsInput hProg hInput Q I)
  have hN :
      P.BoundedModelExtending hProg hInput Q I J' :=
    ⟨hNModel, hNInput⟩
  have hNbase : Instance.Subset J' K :=
    intersectInstance_subset_right J K
  have hOutN :
      Instance.Subset (P.minimalModel I) J' := by
    unfold minimalModel
    exact P.intersection_subset_boundedModel
      hProg hInput Q I K J' hN hNbase
  intro X t ht
  exact
    (intersectInstance_subset_left J K X)
      (hOutN X ht)

end Program

end Datalog

------------------------------------------------------------
-- Minimal Model Correctness
------------------------------------------------------------

namespace Datalog

namespace Program

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Minimal finite models, when they exist, are unique. -/
theorem minimalModels_are_unique
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    ∀ J K : Instance D Γ,
      P.MinimalModel I J →
        P.MinimalModel I K →
          J = K := by
  intro J K hM hN
  apply Instance.ext
  intro X
  apply Finset.ext
  intro t
  constructor
  · intro ht
    exact hM.2.2 K hN.1 hN.2.1 X ht
  · intro ht
    exact hN.2.2 J hM.1 hM.2.1 X ht

/-
  The constructed instance is the minimal finite model
  extending the input.
-/
theorem minimalModel_isMinimalModel
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    P.MinimalModel I (P.minimalModel I) := by
  refine ⟨P.minimalModel_model I, ?_, ?_⟩
  · exact P.minimalModel_extendsInput I
  · intro K hModel hInput
    exact P.minimalModel_subset_of_model I K hModel hInput

end Program

end Datalog

------------------------------------------------------------
-- Query Semantics
------------------------------------------------------------

namespace Datalog

namespace Query

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Read the designated output relation from a program
  instance.
-/
def outputRelation
    (q : Query D Γ n)
    (J : Instance D Γ) :
    FinRelation D n :=
  cast (congrArg (FinRelation D) q.arity)
    (J q.output.val)

/- Query answers are read from the minimal model. -/
def answer
    (q : Query D Γ n)
    (I : Instance D q.program.edbSchema) :
  FinRelation D n :=
  q.outputRelation (q.program.minimalModel I)

end Query

end Datalog
