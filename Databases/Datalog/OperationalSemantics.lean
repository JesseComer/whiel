-- Author: Jesse Comer
import Databases.Datalog.ModelSemantics
import Databases.Datalog.RAConsequence
import Databases.UnnamedRA.SPJU.Semantics

/-
  This file implements operational Datalog semantics.

  The public immediate-consequence operator is `T_P(J)`,
  depending only on the program and current program-schema
  instance. The finite evaluator `immediateOn` enumerates
  assignments over an explicit value set; the LFP
  construction uses the input active domain `P.adom I`.

  Key definitions include:
    * `Program.initial`
    * `Program.stateAdom`
    * `Program.ruleConsequence`
    * `Program.IDBConsequence`
    * `Program.immediate`
    * `Program.iterateUntilFixed`
    * `Program.LFP`

  Key operational theorems include:
    * `Program.ruleConsequence_eq_consequenceSPJ_eval`
    * `Program.IDBConsequence_eq_consequenceSPJU_eval`
    * `Program.immediate_eq_spju_update`
    * `Program.mem_immediate_iff`
    * `Program.immediate_inflationary`
    * `Program.immediate_mono`
    * `Program.LFP_extendsInput`
    * `Program.LFP_boundedByValues`
    * `Program.LFP_fixed`
    * `Program.LFP_subset_of_immediate_prefixed_point`

  The final sections prove the equivalence with
  model-theoretic semantics:
    * `Program.minimalModel_fixed`
    * `Program.LFP_model`
    * `Program.LFP_minimalModel`
    * `Program.LFP_eq_minimalModel`
-/

------------------------------------------------------------
-- Bounded Instances
------------------------------------------------------------

namespace Instance

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Every tuple in every relation uses values from `Q`. -/
def BoundedByValues
    (Q : Finset D)
    (J : Instance D Γ) : Prop :=
  ∀ X : Γ.syms,
    ∀ t : Tuple D (Γ.arity X),
      t ∈ J X → t.isTupleOver Q

/- Pointwise instance inclusion is reflexive. -/
theorem Subset_refl
    (J : Instance D Γ) :
    Instance.Subset J J := by
  intro X t ht
  exact ht

/- Pointwise instance inclusion is transitive. -/
theorem Subset_trans
    {J K I : Instance D Γ}
    (hMN : Instance.Subset J K)
    (hNO : Instance.Subset K I) :
    Instance.Subset J I := by
  intro X t ht
  exact hNO X (hMN X ht)

/- Every instance is bounded by its active domain. -/
theorem boundedByValues_adom
    (J : Instance D Γ) :
    Instance.BoundedByValues J.Adom J := by
  intro X t ht
  exact J.isTupleOver_Adom_of_mem ht

end Instance

------------------------------------------------------------
-- Native Immediate Consequences
------------------------------------------------------------

namespace Datalog

namespace Program

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  The initial program-schema instance copies the EDB input
  into the program schema and interprets every non-input
  symbol, including every IDB, as the empty relation.
-/
def initial
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    Instance D Γ :=
  Instance.expandEmpty P.ambient_extension_edbSchema I

/-
  Rule-level immediate-consequence relation over an explicit
  finite assignment domain. It enumerates tuples over `Q`
  for the rule's variable list, keeps exactly those
  assignments satisfying the body in `J`, and projects the
  rule head.
-/
def ruleConsequenceOn
    (P : Program D Γ)
    (Q : Finset D)
    (J : Instance D Γ)
    (r : {r : Rule D Γ // r ∈ P.rules}) :
  FinRelation D (Γ.arity r.1.head.rel) :=
  ((Tuple.allOver Q r.1.varList.length).filter
    (fun u => Body.Satisfied r.1.body J
      (Assign.ofListTuple r.1.varList u))).image
    (fun u => r.1.head.evalTuple
      (Assign.ofListTuple r.1.varList u))

/-
  The rule-level consequence relation transported to a fixed
  relation symbol `X` when the rule head is propositionally
  equal to `X`.
-/
def ruleConsequenceForHeadOn
    (P : Program D Γ)
    (Q : Finset D)
    (J : Instance D Γ)
    (X : Γ.syms)
    (r : {r : Rule D Γ // r ∈ P.rules})
    (hHead : r.1.head.rel = X) :
    FinRelation D (Γ.arity X) :=
  (P.ruleConsequenceOn Q J r).image
    (fun t => Tuple.castArity (by rw [hHead]) t)

/-
  Union the rule-level consequence relations from `rs` whose
  head relation is `X`.
-/
def IDBConsequenceOnForRules
    (P : Program D Γ)
    (Q : Finset D)
    (J : Instance D Γ)
    (X : Γ.syms) :
    List {r : Rule D Γ // r ∈ P.rules} →
      FinRelation D (Γ.arity X)
| [] => ∅
| r :: rs =>
    if hHead : r.1.head.rel = X then
      P.ruleConsequenceForHeadOn Q J X r hHead ∪
        P.IDBConsequenceOnForRules Q J X rs
    else
      P.IDBConsequenceOnForRules Q J X rs

/-
  Immediate-consequence contribution for one IDB candidate
  relation `X` over an explicit finite assignment domain.
  This is the newly derived relation only; it does not
  include the old contents of `X`.
-/
def IDBConsequenceOn
    (P : Program D Γ)
    (Q : Finset D)
    (J : Instance D Γ)
    (X : Γ.syms) :
    FinRelation D (Γ.arity X) :=
  P.IDBConsequenceOnForRules Q J X P.rules.attach

/-
  Cumulative immediate consequence over an explicit finite
  assignment domain. EDB relations are unchanged; each IDB
  `X` becomes `J X ∪ P.IDBConsequenceOn Q J X`.
-/
def immediateOn
    (P : Program D Γ)
    (Q : Finset D)
    (J : Instance D Γ) :
    Instance D Γ :=
  fun X =>
    if X ∈ P.idb then
      J X ∪ P.IDBConsequenceOn Q J X
    else
      J X

/-
  Active domain used by the mathematical immediate
  consequence operator on a current program-schema instance.
-/
def stateAdom
    (P : Program D Γ)
    (J : Instance D Γ) :
    Finset D :=
  J.Adom ∪ P.constants

/-
  Rule consequence over the input active domain. This is
  implementation support for the fuelled LFP construction.
-/
def ruleConsequenceOnInputAdom
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (J : Instance D Γ)
    (r : {r : Rule D Γ // r ∈ P.rules}) :
    FinRelation D (Γ.arity r.1.head.rel) :=
  P.ruleConsequenceOn (P.adom I) J r

/-
  Per-IDB consequence over the input active domain. This is
  newly derived data only; the cumulative union happens in
  `immediateOnInputAdom`.
-/
def IDBConsequenceOnInputAdom
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (J : Instance D Γ)
    (X : Γ.syms) :
    FinRelation D (Γ.arity X) :=
  P.IDBConsequenceOn (P.adom I) J X

/-
  Cumulative immediate consequence over the input active
  domain. This is implementation support for the fuelled
  LFP construction.
-/
def immediateOnInputAdom
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (J : Instance D Γ) :
    Instance D Γ :=
  P.immediateOn (P.adom I) J

/-
  Rule consequence for the current program-schema instance.
  The assignment domain is `P.stateAdom J`.
-/
def ruleConsequence
    (P : Program D Γ)
    (J : Instance D Γ)
    (r : {r : Rule D Γ // r ∈ P.rules}) :
    FinRelation D (Γ.arity r.1.head.rel) :=
  P.ruleConsequenceOn (P.stateAdom J) J r

/-
  Per-IDB immediate-consequence contribution for the current
  program-schema instance. This is newly derived data only.
-/
def IDBConsequence
    (P : Program D Γ)
    (J : Instance D Γ)
    (X : Γ.syms) :
    FinRelation D (Γ.arity X) :=
  P.IDBConsequenceOn (P.stateAdom J) J X

/-
  Database-theoretic immediate consequence operator. EDB
  relations are unchanged; IDBs are updated by unioning old
  contents with `IDBConsequence`.
-/
def immediate
    (P : Program D Γ)
    (J : Instance D Γ) :
    Instance D Γ :=
  P.immediateOn (P.stateAdom J) J

/-
  Remaining IDB tuple capacity over a finite value set for
  a specified list of relation symbols.
-/
def remainingCapacityForSyms
    (Q : Finset D)
    (J : Instance D Γ) :
    List Γ.syms → Nat
| [] => 0
| X :: Xs =>
    ((Tuple.allOver Q (Γ.arity X)) \ J X).card +
      remainingCapacityForSyms Q J Xs

/-
  Remaining IDB tuple capacity over `Q`. For each IDB,
  this counts the tuples over `Q` not yet present in the
  current instance.
-/
def remainingCapacity
    (P : Program D Γ)
    (Q : Finset D)
    (J : Instance D Γ) :
    Nat :=
  remainingCapacityForSyms Q J P.idbList

/- Fuelled iteration until a fixed point is encountered. -/
def iterateUntilFixed
    (P : Program D Γ)
    (Q : Finset D) :
    Nat → Instance D Γ → Instance D Γ
| 0, J => J
| n + 1, J =>
    let J' := P.immediateOn Q J
    if J' = J then
      J
    else
      P.iterateUntilFixed Q n J'

/- A finite IDB tuple-capacity bound over the input adom. -/
def lfpFuel
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    Nat :=
  P.remainingCapacity (P.adom I) (P.initial I) + 1

/-
  Operational fixed-point candidate obtained by fuelled
  immediate-consequence iteration from the empty-IDB initial
  instance over the input active domain.
-/
def LFP
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    Instance D Γ :=
  P.iterateUntilFixed (P.adom I) (P.lfpFuel I) (P.initial I)

/-
  A program-schema instance is bounded by its state active
  domain.
-/
theorem boundedByValues_stateAdom
    (P : Program D Γ)
    (J : Instance D Γ) :
    Instance.BoundedByValues (P.stateAdom J) J := by
  intro X t ht
  exact
    Tuple.isTupleOver_mono
      (by
        intro d hd
        exact Finset.mem_union.mpr (Or.inl hd))
      (Instance.boundedByValues_adom J X t ht)

/-
  If `J` is bounded by `Q` and `Q` contains all
  program constants, then `P.stateAdom J` is contained in
  `Q`.
-/
theorem stateAdom_subset_of_boundedByValues
    (P : Program D Γ)
    {Q : Finset D}
    {J : Instance D Γ}
    (hBound : Instance.BoundedByValues Q J)
    (hConst : P.constants ⊆ Q) :
    P.stateAdom J ⊆ Q := by
  intro d hd
  rw [stateAdom] at hd
  rcases Finset.mem_union.mp hd with hdM | hdC
  · rw [Instance.in_Adom_iff_in_Relation] at hdM
    rcases hdM with ⟨X, t, ht, hdTuple⟩
    have hdList : d ∈ t.toList := by
      simpa [List.mem_toFinset] using hdTuple
    rcases List.mem_iff_getElem.mp hdList with
      ⟨i, hi, hGet⟩
    have hi' : i < Γ.arity X := by
      simpa [Vector.toList] using hi
    have hCoord :
        t.get ⟨i, hi'⟩ = d := by
      have hListGet :
          t.toList[i] = t.get ⟨i, hi'⟩ := by
        cases t
        simp [Vector.get, Vector.toList]
      exact hListGet.symm.trans hGet
    rw [← hCoord]
    exact hBound X t ht ⟨i, hi'⟩
  · exact hConst hdC

end Program

end Datalog

------------------------------------------------------------
-- Native Consequence Specification
------------------------------------------------------------

namespace Datalog

namespace Program

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Native rule consequences are sound for rule bodies. -/
theorem ruleConsequenceOn_sound
    (P : Program D Γ)
    (Q : Finset D)
    (J : Instance D Γ)
    (r : {r : Rule D Γ // r ∈ P.rules})
    {t : Tuple D (Γ.arity r.1.head.rel)}
    (ht : t ∈ P.ruleConsequenceOn Q J r) :
    ∃ σ : Assign D,
      Body.Satisfied r.1.body J σ ∧
        r.1.head.evalTuple σ = t := by
  unfold ruleConsequenceOn at ht
  rcases Finset.mem_image.mp ht with ⟨u, hu, hEq⟩
  rcases Finset.mem_filter.mp hu with ⟨_huAll, hBody⟩
  exact
    ⟨Assign.ofListTuple r.1.varList u, hBody, hEq⟩

/-
  Satisfying assignments over `Q` appear in the rule
  consequence.
-/
theorem mem_ruleConsequenceOn_of_bodySat
    (P : Program D Γ)
    (Q : Finset D)
    (J : Instance D Γ)
    (r : {r : Rule D Γ // r ∈ P.rules})
    (σ : Assign D)
    (hVals :
      ∀ x : Var, x ∈ r.1.varList → σ x ∈ Q)
    (hBody : Body.Satisfied r.1.body J σ) :
    r.1.head.evalTuple σ ∈
      P.ruleConsequenceOn Q J r := by
  unfold ruleConsequenceOn
  let u := Assign.toListTuple r.1.varList σ
  refine Finset.mem_image.mpr ?_
  refine ⟨u, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    constructor
    · dsimp [u]
      exact Assign.toListTuple_mem_allOver_of_forall_mem hVals
    · apply r.1.bodySatisfied_congr_assign J ?_ hBody
      intro x hx
      dsimp [u]
      exact (Assign.ofListTuple_toListTuple_of_mem hx).symm
  · dsimp [u]
    exact
      r.1.head.evalTuple_eq_of_assign_eq_on_vars
        (fun x hx =>
          Assign.ofListTuple_toListTuple_of_mem
            (r.1.head_var_mem_varList hx))

/- Body variables in bounded instances range over `Q`. -/
theorem value_mem_of_body_var_of_bounded
    (P : Program D Γ)
    {Q : Finset D}
    {J : Instance D Γ}
    (hBound : Instance.BoundedByValues Q J)
    (r : {r : Rule D Γ // r ∈ P.rules})
    (σ : Assign D)
    (hBody : Body.Satisfied r.1.body J σ)
    {x : Var}
    (hx : x ∈ Body.varList r.1.body) :
    σ x ∈ Q := by
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
      have hAtom : a.Sat J σ := by
        have hSat :=
          Body.sat_of_satisfied J σ r.1.body hb hBody
        simpa [Atom.Sat] using hSat
      have hEvalOver :
          (a.evalTuple σ).isTupleOver Q :=
        hBound a.rel (a.evalTuple σ) hAtom
      exact
        a.value_mem_of_var_mem_evalTuple_over
          hEvalOver hxAtom
  | eq lhs rhs =>
      simp [Atom.relVarList] at hEq
      subst vars
      cases hxVars

/- Rule variables in bounded instances range over `Q`. -/
theorem value_mem_of_rule_var_of_bounded
    (P : Program D Γ)
    {Q : Finset D}
    {J : Instance D Γ}
    (hBound : Instance.BoundedByValues Q J)
    (r : {r : Rule D Γ // r ∈ P.rules})
    (σ : Assign D)
    (hBody : Body.Satisfied r.1.body J σ)
    {x : Var}
    (hx : x ∈ r.1.varList) :
    σ x ∈ Q := by
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
    exact
      P.value_mem_of_body_var_of_bounded
        hBound r σ hBody hBodyVar
  · exact
      P.value_mem_of_body_var_of_bounded
        hBound r σ hBody hxBody

/-
  IDB consequences from a rule list are sound for rule
  bodies.
-/
theorem IDBConsequenceOnForRules_sound
    (P : Program D Γ)
    (Q : Finset D)
    (J : Instance D Γ)
    (X : Γ.syms)
    (t : Tuple D (Γ.arity X)) :
    ∀ rs : List {r : Rule D Γ // r ∈ P.rules},
      t ∈ P.IDBConsequenceOnForRules Q J X rs →
        ∃ r : {r : Rule D Γ // r ∈ P.rules},
          r ∈ rs ∧
            ∃ hHead : r.1.head.rel = X,
              ∃ σ : Assign D,
                Body.Satisfied r.1.body J σ ∧
                  r.1.headEvalTupleAs X hHead σ = t
| [], ht => by
    simp [IDBConsequenceOnForRules] at ht
| r :: rs, ht => by
    by_cases hHead : r.1.head.rel = X
    · have ht' :
          t ∈ P.ruleConsequenceForHeadOn Q J X r
              hHead ∪
            P.IDBConsequenceOnForRules Q J X rs := by
        simpa [IDBConsequenceOnForRules, hHead] using ht
      rcases Finset.mem_union.mp ht' with ht | ht
      · rcases Finset.mem_image.mp ht with
          ⟨u, hu, hEq⟩
        rcases P.ruleConsequenceOn_sound Q J r hu with
          ⟨σ, hBody, hTuple⟩
        exact
          ⟨r, by simp, hHead, σ, hBody, by
            rw [Rule.headEvalTupleAs, hTuple, hEq]⟩
      · rcases IDBConsequenceOnForRules_sound
            P Q J X t rs ht with
          ⟨r', hr', hHead', σ, hBody, hTuple⟩
        exact
          ⟨r', by simp [hr'], hHead', σ, hBody, hTuple⟩
    · have ht' :
          t ∈ P.IDBConsequenceOnForRules Q J X rs := by
        simpa [IDBConsequenceOnForRules, hHead] using ht
      rcases IDBConsequenceOnForRules_sound
          P Q J X t rs ht' with
        ⟨r', hr', hHead', σ, hBody, hTuple⟩
      exact
        ⟨r', by simp [hr'], hHead', σ, hBody, hTuple⟩

/-
  IDB consequences from a rule list contain bounded
  satisfying heads.
-/
theorem mem_IDBConsequenceOnForRules_of_bodySat
    (P : Program D Γ)
    (Q : Finset D)
    (J : Instance D Γ)
    (X : Γ.syms) :
    ∀ rs : List {r : Rule D Γ // r ∈ P.rules},
      ∀ r : {r : Rule D Γ // r ∈ P.rules},
        r ∈ rs →
          ∀ hHead : r.1.head.rel = X,
            ∀ σ : Assign D,
              (∀ x : Var,
                x ∈ r.1.varList → σ x ∈ Q) →
              Body.Satisfied r.1.body J σ →
                r.1.headEvalTupleAs X hHead σ ∈
                  P.IDBConsequenceOnForRules Q J X rs
| [], r, hr, _hHead, _σ, _hVals, _hBody => by
    cases hr
| r' :: rs, r, hr, hHead, σ, hVals, hBody => by
    by_cases hHead' : r'.1.head.rel = X
    · have hMem :
          r.1.headEvalTupleAs X hHead σ ∈
            P.ruleConsequenceForHeadOn Q J X r'
              hHead' ∪
              P.IDBConsequenceOnForRules Q J X rs := by
        rcases List.mem_cons.mp hr with hrEq | hrRest
        · subst hrEq
          apply Finset.mem_union.mpr
          left
          unfold ruleConsequenceForHeadOn
          refine Finset.mem_image.mpr ?_
          refine ⟨r.1.head.evalTuple σ, ?_, ?_⟩
          · exact
              P.mem_ruleConsequenceOn_of_bodySat
                Q J r σ hVals hBody
          · simp [Rule.headEvalTupleAs]
        · apply Finset.mem_union.mpr
          right
          exact
            mem_IDBConsequenceOnForRules_of_bodySat
              P Q J X rs r hrRest hHead σ hVals hBody
      simpa [IDBConsequenceOnForRules, hHead'] using hMem
    · rcases List.mem_cons.mp hr with hrEq | hrRest
      · subst hrEq
        exact False.elim (hHead' hHead)
      · have hMem :
            r.1.headEvalTupleAs X hHead σ ∈
              P.IDBConsequenceOnForRules Q J X rs :=
          mem_IDBConsequenceOnForRules_of_bodySat
            P Q J X rs r hrRest hHead σ hVals hBody
        simpa [IDBConsequenceOnForRules, hHead'] using hMem

/-
  One-rule native consequences are monotone in instances.
-/
theorem ruleConsequenceOn_mono
    (P : Program D Γ)
    (Q : Finset D)
    {J K : Instance D Γ}
    (hSub : Instance.Subset J K)
    (r : {r : Rule D Γ // r ∈ P.rules}) :
    P.ruleConsequenceOn Q J r ⊆
      P.ruleConsequenceOn Q K r := by
  intro t ht
  unfold ruleConsequenceOn at ht ⊢
  rcases Finset.mem_image.mp ht with ⟨u, hu, hEq⟩
  rcases Finset.mem_filter.mp hu with ⟨huAll, hBody⟩
  refine Finset.mem_image.mpr ?_
  refine ⟨u, ?_, hEq⟩
  apply Finset.mem_filter.mpr
  exact ⟨huAll, Body.satisfied_mono hSub r.1.body hBody⟩

/- IDB consequences are monotone in instances. -/
theorem IDBConsequenceOnForRules_mono
    (P : Program D Γ)
    (Q : Finset D)
    {J K : Instance D Γ}
    (hSub : Instance.Subset J K)
    (X : Γ.syms) :
    ∀ rs : List {r : Rule D Γ // r ∈ P.rules},
      P.IDBConsequenceOnForRules Q J X rs ⊆
        P.IDBConsequenceOnForRules Q K X rs
| [] => by
    intro t ht
    simp [IDBConsequenceOnForRules] at ht
| r :: rs => by
    intro t ht
    by_cases hHead : r.1.head.rel = X
    · have ht' :
          t ∈ P.ruleConsequenceForHeadOn Q J X r
              hHead ∪
            P.IDBConsequenceOnForRules Q J X rs := by
        simpa [IDBConsequenceOnForRules, hHead] using ht
      have hOut :
          t ∈ P.ruleConsequenceForHeadOn Q K X r
              hHead ∪
            P.IDBConsequenceOnForRules Q K X rs := by
        rcases Finset.mem_union.mp ht' with ht | ht
        · apply Finset.mem_union.mpr
          left
          unfold ruleConsequenceForHeadOn at ht ⊢
          have hImg := Finset.mem_image.mp ht
          rcases hImg with ⟨u, hu, hEq⟩
          refine Finset.mem_image.mpr ?_
          refine ⟨u, ?_, hEq⟩
          exact P.ruleConsequenceOn_mono Q hSub r hu
        · apply Finset.mem_union.mpr
          right
          exact
            IDBConsequenceOnForRules_mono
              P Q hSub X rs ht
      simpa [IDBConsequenceOnForRules, hHead] using hOut
    · have ht' :
          t ∈ P.IDBConsequenceOnForRules Q J X rs := by
        simpa [IDBConsequenceOnForRules, hHead] using ht
      have hOut :
          t ∈ P.IDBConsequenceOnForRules Q K X rs :=
        IDBConsequenceOnForRules_mono P Q hSub X rs ht'
      simpa [IDBConsequenceOnForRules, hHead] using hOut

/- Native consequences are monotone in instances. -/
theorem IDBConsequenceOn_mono
    (P : Program D Γ)
    (Q : Finset D)
    {J K : Instance D Γ}
    (hSub : Instance.Subset J K)
    (X : Γ.syms) :
    P.IDBConsequenceOn Q J X ⊆
      P.IDBConsequenceOn Q K X := by
  unfold IDBConsequenceOn
  exact
    P.IDBConsequenceOnForRules_mono
      Q hSub X P.rules.attach

/- One-rule native consequences are over the value set. -/
theorem ruleConsequenceOn_tuple_over
    (P : Program D Γ)
    (Q : Finset D)
    (J : Instance D Γ)
    (r : {r : Rule D Γ // r ∈ P.rules})
    {t : Tuple D (Γ.arity r.1.head.rel)}
    (ht : t ∈ P.ruleConsequenceOn Q J r) :
    t.isTupleOver Q := by
  unfold ruleConsequenceOn at ht
  rcases Finset.mem_image.mp ht with ⟨u, hu, hEq⟩
  rcases Finset.mem_filter.mp hu with ⟨huAll, _hBody⟩
  subst hEq
  intro i
  rcases
      r.1.head.exists_var_mem_varList_of_constFree_getElem
        r.1.noHeadConst i.2 with
    ⟨x, hArg, hxHead⟩
  have hxRule := r.1.head_var_mem_varList hxHead
  have hVal :=
    Assign.ofListTuple_mem_of_mem_allOver huAll hxRule
  change
    (r.1.head.evalTuple
      (Assign.ofListTuple r.1.varList u))[i.1] ∈ Q
  simp [RelAtom.evalTuple, RelTerm.evalVector_eq_map,
    Vector.getElem_map, hArg, RelTerm.eval, hVal]

/-
  IDB consequences from a rule list are over the value set.
-/
theorem IDBConsequenceOnForRules_tuple_over
    (P : Program D Γ)
    (Q : Finset D)
    (J : Instance D Γ)
    (X : Γ.syms) :
    ∀ rs : List {r : Rule D Γ // r ∈ P.rules},
      ∀ {t : Tuple D (Γ.arity X)},
        t ∈ P.IDBConsequenceOnForRules Q J X rs →
          t.isTupleOver Q
| [], _t, ht => by
    simp [IDBConsequenceOnForRules] at ht
| r :: rs, t, ht => by
    by_cases hHead : r.1.head.rel = X
    · have ht' :
          t ∈ P.ruleConsequenceForHeadOn Q J X r
              hHead ∪
            P.IDBConsequenceOnForRules Q J X rs := by
        simpa [IDBConsequenceOnForRules, hHead] using ht
      rcases Finset.mem_union.mp ht' with ht | ht
      · rcases Finset.mem_image.mp ht with ⟨u, hu, hEq⟩
        subst hEq
        cases hHead
        exact P.ruleConsequenceOn_tuple_over Q J r hu
      · exact
          IDBConsequenceOnForRules_tuple_over
            P Q J X rs ht
    · have ht' :
          t ∈ P.IDBConsequenceOnForRules Q J X rs := by
        simpa [IDBConsequenceOnForRules, hHead] using ht
      exact
        IDBConsequenceOnForRules_tuple_over
          P Q J X rs ht'

/- IDB consequences are over the value set. -/
theorem IDBConsequenceOn_tuple_over
    (P : Program D Γ)
    (Q : Finset D)
    (J : Instance D Γ)
    (X : Γ.syms)
    {t : Tuple D (Γ.arity X)}
    (ht : t ∈ P.IDBConsequenceOn Q J X) :
    t.isTupleOver Q := by
  unfold IDBConsequenceOn at ht
  exact
    P.IDBConsequenceOnForRules_tuple_over
      Q J X P.rules.attach ht

end Program

end Datalog

------------------------------------------------------------
-- RA Bridge
------------------------------------------------------------

namespace Datalog

namespace Program

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Raw rule consequences agree with the single-rule SPJ
  query when the current instance is bounded by the explicit
  assignment domain.
-/
theorem ruleConsequenceOn_eq_consequenceSPJ_eval
    (P : Program D Γ)
    (Q : Finset D)
    (J : Instance D Γ)
    (r : {r : Rule D Γ // r ∈ P.rules})
    (hBound : Instance.BoundedByValues Q J) :
    P.ruleConsequenceOn Q J r =
      r.1.consequenceSPJ.eval J := by
  apply Finset.ext
  intro t
  constructor
  · intro ht
    rw [Rule.consequenceSPJ_correct]
    rcases P.ruleConsequenceOn_sound
        Q J r ht with
      ⟨σ, hBody, hTuple⟩
    exact ⟨σ, hBody, hTuple⟩
  · intro ht
    rw [Rule.consequenceSPJ_correct] at ht
    rcases ht with ⟨σ, hBody, hTuple⟩
    rw [← hTuple]
    exact
      P.mem_ruleConsequenceOn_of_bodySat
        Q J r σ
        (fun x hx =>
          P.value_mem_of_rule_var_of_bounded
            hBound r σ hBody hx)
        hBody

/-
  Input-domain rule consequences agree with the single-rule
  SPJ query.
-/
theorem ruleConsequenceOnInputAdom_eq_consequenceSPJ_eval
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (J : Instance D Γ)
    (r : {r : Rule D Γ // r ∈ P.rules})
    (hBound : Instance.BoundedByValues (P.adom I) J) :
    P.ruleConsequenceOnInputAdom I J r =
      r.1.consequenceSPJ.eval J := by
  simpa [ruleConsequenceOnInputAdom] using
    P.ruleConsequenceOn_eq_consequenceSPJ_eval
      (P.adom I) J r hBound

/-
  Rule consequences over the current state active domain
  agree with the single-rule SPJ query.
-/
theorem ruleConsequence_eq_consequenceSPJ_eval
    (P : Program D Γ)
    (J : Instance D Γ)
    (r : {r : Rule D Γ // r ∈ P.rules}) :
    P.ruleConsequence J r =
      r.1.consequenceSPJ.eval J := by
  simpa [ruleConsequence] using
    P.ruleConsequenceOn_eq_consequenceSPJ_eval
      (P.stateAdom J) J r
      (P.boundedByValues_stateAdom J)

/- Raw IDB consequences agree with the RA SPJU query. -/
theorem IDBConsequenceOn_eq_consequenceSPJU_eval
    (P : Program D Γ)
    (Q : Finset D)
    (J : Instance D Γ)
    (X : Γ.syms)
    (hBound : Instance.BoundedByValues Q J) :
    P.IDBConsequenceOn Q J X =
      (P.consequenceSPJU X).eval J := by
  apply Finset.ext
  intro t
  constructor
  · intro ht
    unfold IDBConsequenceOn at ht
    rcases P.IDBConsequenceOnForRules_sound
        Q J X t P.rules.attach ht with
      ⟨r, _hr, hHead, σ, hBody, hTuple⟩
    rw [P.consequenceSPJU_correct J X t]
    exact ⟨r, hHead, σ, hBody, hTuple⟩
  · intro ht
    rw [P.consequenceSPJU_correct J X t] at ht
    rcases ht with ⟨r, hHead, σ, hBody, hTuple⟩
    unfold IDBConsequenceOn
    rw [← hTuple]
    apply P.mem_IDBConsequenceOnForRules_of_bodySat
    · exact List.mem_attach _ _
    · intro x hx
      exact
        P.value_mem_of_rule_var_of_bounded
          hBound r σ hBody hx
    · exact hBody

/-
  Input-domain IDB consequences agree with the RA `SPJU`
  query.
-/
theorem IDBConsequenceOnInputAdom_eq_consequenceSPJU_eval
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (J : Instance D Γ)
    (X : Γ.syms)
    (hBound : Instance.BoundedByValues (P.adom I) J) :
    P.IDBConsequenceOnInputAdom I J X =
      (P.consequenceSPJU X).eval J := by
  simpa [IDBConsequenceOnInputAdom] using
    P.IDBConsequenceOn_eq_consequenceSPJU_eval
      (P.adom I) J X hBound

/-
  Current-state IDB consequences agree with the RA `SPJU`
  query.
-/
theorem IDBConsequence_eq_consequenceSPJU_eval
    (P : Program D Γ)
    (J : Instance D Γ)
    (X : Γ.syms) :
    P.IDBConsequence J X =
      (P.consequenceSPJU X).eval J := by
  simpa [IDBConsequence] using
    P.IDBConsequenceOn_eq_consequenceSPJU_eval
      (P.stateAdom J) J X
      (P.boundedByValues_stateAdom J)

end Program

end Datalog

------------------------------------------------------------
-- Immediate Consequence Properties
------------------------------------------------------------

namespace Datalog

namespace Program

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Immediate consequence is inflationary. -/
theorem immediateOn_inflationary
    (P : Program D Γ)
    (Q : Finset D)
    (J : Instance D Γ) :
    Instance.Subset J (P.immediateOn Q J) := by
  intro X t ht
  unfold immediateOn
  by_cases hX : X ∈ P.idb
  · simp [hX, ht]
  · simpa [hX] using ht

/- Non-IDB relations are unchanged by `immediate`. -/
theorem immediateOn_preserves_edb
    (P : Program D Γ)
    (Q : Finset D)
    (J : Instance D Γ)
    (X : Γ.syms)
    (hX : X ∉ P.idb) :
    P.immediateOn Q J X = J X := by
  simp [immediateOn, hX]

/- Immediate consequence is monotone. -/
theorem immediateOn_mono
    (P : Program D Γ)
    (Q : Finset D)
    {J K : Instance D Γ}
    (hSub : Instance.Subset J K) :
    Instance.Subset (P.immediateOn Q J)
      (P.immediateOn Q K) := by
  intro X t ht
  by_cases hX : X ∈ P.idb
  · have ht' :
        t ∈ J X ∪ P.IDBConsequenceOn Q J X := by
      simpa [immediateOn, hX] using ht
    have hOut :
        t ∈ K X ∪ P.IDBConsequenceOn Q K X := by
      rcases Finset.mem_union.mp ht' with ht | ht
      · exact Finset.mem_union.mpr
          (Or.inl (hSub X ht))
      · exact Finset.mem_union.mpr
          (Or.inr (P.IDBConsequenceOn_mono Q hSub X ht))
    simpa [immediateOn, hX] using hOut
  · have htM : t ∈ J X := by
      simpa [immediateOn, hX] using ht
    simpa [immediateOn, hX] using hSub X htM

/- Immediate consequence preserves value boundedness. -/
theorem immediateOn_preserves_boundedByValues
    (P : Program D Γ)
    (Q : Finset D)
    {J : Instance D Γ}
    (hBound : Instance.BoundedByValues Q J) :
    Instance.BoundedByValues Q
      (P.immediateOn Q J) := by
  intro X t ht
  by_cases hX : X ∈ P.idb
  · have ht' :
        t ∈ J X ∪ P.IDBConsequenceOn Q J X := by
      simpa [immediateOn, hX] using ht
    rcases Finset.mem_union.mp ht' with ht | ht
    · exact hBound X t ht
    · exact P.IDBConsequenceOn_tuple_over Q J X ht
  · exact hBound X t (by simpa [immediateOn, hX] using ht)

/-
  Current-state immediate consequence is the old instance
  unioned with the SPJU consequence query at each IDB.
-/
theorem immediate_eq_spju_update
    (P : Program D Γ)
    (J : Instance D Γ) :
    P.immediate J =
      fun X =>
        if X ∈ P.idb then
          J X ∪ (P.consequenceSPJU X).eval J
        else
          J X := by
  apply Instance.ext
  intro X
  by_cases hX : X ∈ P.idb
  · rw [immediate, immediateOn, if_pos hX]
    rw [P.IDBConsequenceOn_eq_consequenceSPJU_eval
      (P.stateAdom J) J X
      (P.boundedByValues_stateAdom J)]
    rw [if_pos hX]
  · simp [immediate, immediateOn, hX]

/-
  Membership in the current-state immediate consequence is
  either old membership or derivability by a matching rule.
-/
theorem mem_immediate_iff
    (P : Program D Γ)
    (J : Instance D Γ)
    (X : Γ.syms)
    (t : Tuple D (Γ.arity X)) :
    t ∈ P.immediate J X ↔
      t ∈ J X ∨
        X ∈ P.idb ∧ P.consequenceWitness J X t := by
  rw [P.immediate_eq_spju_update J]
  change
    t ∈ (if X ∈ P.idb then
          J X ∪ (P.consequenceSPJU X).eval J
        else
          J X) ↔
      t ∈ J X ∨
        X ∈ P.idb ∧ P.consequenceWitness J X t
  by_cases hX : X ∈ P.idb
  · rw [if_pos hX, Finset.mem_union]
    constructor
    · intro ht
      rcases ht with ht | ht
      · exact Or.inl ht
      · right
        exact
          ⟨hX,
            (P.consequenceSPJU_correct J X t).mp ht⟩
    · intro ht
      rcases ht with ht | ⟨_hX, hWit⟩
      · exact Or.inl ht
      · exact Or.inr
          ((P.consequenceSPJU_correct J X t).mpr hWit)
  · rw [if_neg hX]
    constructor
    · intro ht
      exact Or.inl ht
    · intro ht
      rcases ht with ht | ⟨hIDB, _hWit⟩
      · exact ht
      · exact False.elim (hX hIDB)

/- Current-state immediate consequence is inflationary. -/
theorem immediate_inflationary
    (P : Program D Γ)
    (J : Instance D Γ) :
    Instance.Subset J (P.immediate J) := by
  simpa [immediate] using
    P.immediateOn_inflationary (P.stateAdom J) J

/-
  Current-state immediate consequence leaves non-IDBs
  unchanged.
-/
theorem immediate_preserves_edb
    (P : Program D Γ)
    (J : Instance D Γ)
    (X : Γ.syms)
    (hX : X ∉ P.idb) :
    P.immediate J X = J X := by
  simpa [immediate] using
    P.immediateOn_preserves_edb (P.stateAdom J) J X hX

/- Current-state immediate consequence is monotone. -/
theorem immediate_mono
    (P : Program D Γ)
    {J K : Instance D Γ}
    (hSub : Instance.Subset J K) :
    Instance.Subset (P.immediate J)
      (P.immediate K) := by
  intro X t ht
  rw [P.immediate_eq_spju_update J] at ht
  rw [P.immediate_eq_spju_update K]
  by_cases hX : X ∈ P.idb
  · have ht' :
        t ∈ J X ∪ (P.consequenceSPJU X).eval J := by
      simpa [hX] using ht
    have hOut :
        t ∈ K X ∪ (P.consequenceSPJU X).eval K := by
      rcases Finset.mem_union.mp ht' with htM | htQ
      · exact Finset.mem_union.mpr
          (Or.inl (hSub X htM))
      · let hSPJU : SPJUExpr D Γ (Γ.arity X) :=
          ⟨P.consequenceSPJU X,
            P.consequenceSPJU_isSPJU X⟩
        have htQ' :
            t ∈ hSPJU.1.eval J := by
          simpa [hSPJU] using htQ
        exact Finset.mem_union.mpr
          (Or.inr
            (by
              simpa [hSPJU] using
                SPJUExpr.eval_monotone hSPJU hSub htQ'))
    simpa [hX] using hOut
  · have htM : t ∈ J X := by
      simpa [hX] using ht
    simpa [hX] using hSub X htM

/-
  Current-state immediate consequence preserves boundedness
  by the current state active domain.
-/
theorem immediate_preserves_boundedByValues
    (P : Program D Γ)
    (J : Instance D Γ) :
    Instance.BoundedByValues (P.stateAdom J)
      (P.immediate J) := by
  simpa [immediate] using
    P.immediateOn_preserves_boundedByValues
      (P.stateAdom J) (P.boundedByValues_stateAdom J)

/- Input-domain immediate consequence is inflationary. -/
theorem immediateOnInputAdom_inflationary
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (J : Instance D Γ) :
    Instance.Subset J (P.immediateOnInputAdom I J) := by
  simpa [immediateOnInputAdom] using
    P.immediateOn_inflationary (P.adom I) J

/-
  Input-domain immediate consequence leaves non-IDBs
  unchanged.
-/
theorem immediateOnInputAdom_preserves_edb
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (J : Instance D Γ)
    (X : Γ.syms)
    (hX : X ∉ P.idb) :
    P.immediateOnInputAdom I J X = J X := by
  simpa [immediateOnInputAdom] using
    P.immediateOn_preserves_edb (P.adom I) J X hX

/- Input-domain immediate consequence is monotone. -/
theorem immediateOnInputAdom_mono
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    {J K : Instance D Γ}
    (hSub : Instance.Subset J K) :
    Instance.Subset (P.immediateOnInputAdom I J)
      (P.immediateOnInputAdom I K) := by
  simpa [immediateOnInputAdom] using
    P.immediateOn_mono (P.adom I) hSub

/-
  Input-domain immediate consequence preserves boundedness
  by the input active domain.
-/
theorem immediateOnInputAdom_preserves_boundedByValues
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    {J : Instance D Γ}
    (hBound : Instance.BoundedByValues (P.adom I) J) :
    Instance.BoundedByValues (P.adom I)
      (P.immediateOnInputAdom I J) := by
  simpa [immediateOnInputAdom] using
    P.immediateOn_preserves_boundedByValues
      (P.adom I) hBound

/-
  On states bounded by the input active domain, the
  input-domain evaluator agrees with the current-state
  immediate consequence operator.
-/
theorem immediateOnInputAdom_eq_immediate
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (J : Instance D Γ)
    (hBound : Instance.BoundedByValues (P.adom I) J) :
    P.immediateOnInputAdom I J = P.immediate J := by
  apply Instance.ext
  intro X
  by_cases hX : X ∈ P.idb
  · have hInput :=
      P.IDBConsequenceOn_eq_consequenceSPJU_eval
        (P.adom I) J X hBound
    have hState :=
      P.IDBConsequenceOn_eq_consequenceSPJU_eval
        (P.stateAdom J) J X
        (P.boundedByValues_stateAdom J)
    simp [immediateOnInputAdom, immediate, immediateOn,
      hX, hInput, hState]
  · simp [immediateOnInputAdom, immediate, immediateOn, hX]

/-
  The empty-IDB initial instance agrees with the EDB input.
-/
theorem initial_extendsInput
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    Instance.Extends P.ambient_extension_edbSchema I
      (P.initial I) := by
  intro X hX
  simp [initial, Instance.expandEmpty, hX]

/-
  The empty-IDB initial instance is bounded by the input
  active domain.
-/
theorem initial_boundedByValues
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    Instance.BoundedByValues (P.adom I) (P.initial I) := by
  intro X t ht
  by_cases hX : X.1 ∈ P.edbSchema.syms
  · have hMem :
        Tuple.castArity
            (UnnamedSchema.arity_eq_of_extension_mem
              P.ambient_extension_edbSchema X hX) t ∈
          I ⟨X.1, hX⟩ :=
      (Instance.expandEmpty_mem_iff_of_mem
        P.ambient_extension_edbSchema I X hX t).mp
        (by simpa [initial] using ht)
    have hOver :=
      Instance.isTupleOver_Adom_of_mem I hMem
    have hAr :=
      UnnamedSchema.arity_eq_of_extension_mem
        P.ambient_extension_edbSchema X hX
    cases hAr
    exact
      Tuple.isTupleOver_mono
        (Finset.subset_union_left)
        (by simpa [Tuple.castArity] using hOver)
  · have hEmpty :
        P.initial I X = ∅ := by
      simpa [initial] using
        Instance.expandEmpty_eq_empty_of_not_mem
          P.ambient_extension_edbSchema I X hX
    simp [hEmpty] at ht

/-
  The cumulative immediate-consequence operator leaves the
  EDB input unchanged.
-/
theorem immediateOn_preserves_extendsInput
    (P : Program D Γ)
    (Q : Finset D)
    {I : Instance D P.edbSchema}
    {J : Instance D Γ}
    (hExt :
      Instance.Extends P.ambient_extension_edbSchema I J) :
    Instance.Extends P.ambient_extension_edbSchema I
      (P.immediateOn Q J) := by
  intro X hX
  have hNotIdb : X ∉ P.idb := by
    intro hIdb
    have hIdbName : X.1 ∈ P.idbNames :=
      Finset.mem_image.mpr ⟨X, hIdb, rfl⟩
    exact
      (Finset.disjoint_left.mp P.disjoint_edb_idb)
        hX hIdbName
  simpa [immediateOn, hNotIdb] using hExt X hX

/-
  The input-fixed immediate-consequence operator leaves the
  EDB input unchanged.
-/
theorem immediate_preserves_extendsInput
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    {J : Instance D Γ}
    (hExt :
      Instance.Extends P.ambient_extension_edbSchema I J) :
    Instance.Extends P.ambient_extension_edbSchema I
      (P.immediate J) := by
  intro X hX
  have hNotIdb : X ∉ P.idb := by
    intro hIdb
    have hIdbName : X.1 ∈ P.idbNames :=
      Finset.mem_image.mpr ⟨X, hIdb, rfl⟩
    exact
      (Finset.disjoint_left.mp P.disjoint_edb_idb)
        hX hIdbName
  simpa [immediate, immediateOn, hNotIdb] using hExt X hX

/-
  The input-domain immediate-consequence evaluator leaves
  the EDB input unchanged.
-/
theorem immediateOnInputAdom_preserves_extendsInput
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    {J : Instance D Γ}
    (hExt :
      Instance.Extends P.ambient_extension_edbSchema I J) :
    Instance.Extends P.ambient_extension_edbSchema I
      (P.immediateOnInputAdom I J) := by
  simpa [immediateOnInputAdom] using
    P.immediateOn_preserves_extendsInput (P.adom I) hExt

/-
  Fuelled iteration is inflationary in its starting
  instance.
-/
theorem iterateUntilFixed_inflationary
    (P : Program D Γ)
    (Q : Finset D) :
    ∀ n : Nat,
      ∀ J : Instance D Γ,
        Instance.Subset J
          (P.iterateUntilFixed Q n J)
| 0, J => by
    simpa [iterateUntilFixed] using
      Instance.Subset_refl J
| n + 1, J => by
    rw [iterateUntilFixed]
    by_cases hFixed : P.immediateOn Q J = J
    · simpa [hFixed] using
        Instance.Subset_refl J
    · rw [if_neg hFixed]
      exact
        Instance.Subset_trans
          (P.immediateOn_inflationary Q J)
          (iterateUntilFixed_inflationary P Q n
            (P.immediateOn Q J))

/-
  Fuelled iteration preserves exact agreement with the EDB
  input.
-/
theorem iterateUntilFixed_preserves_extendsInput
    (P : Program D Γ)
    (Q : Finset D)
    {I : Instance D P.edbSchema} :
    ∀ n : Nat,
      ∀ J : Instance D Γ,
        Instance.Extends
          P.ambient_extension_edbSchema I J →
          Instance.Extends P.ambient_extension_edbSchema I
            (P.iterateUntilFixed Q n J)
| 0, J, hExt => by
    simpa [iterateUntilFixed] using hExt
| n + 1, J, hExt => by
    rw [iterateUntilFixed]
    by_cases hFixed : P.immediateOn Q J = J
    · simpa [hFixed] using hExt
    · rw [if_neg hFixed]
      exact
        iterateUntilFixed_preserves_extendsInput
          P Q n (P.immediateOn Q J)
          (P.immediateOn_preserves_extendsInput Q hExt)

/-
  Fuelled iteration preserves value boundedness.
-/
theorem iterateUntilFixed_preserves_boundedByValues
    (P : Program D Γ)
    (Q : Finset D) :
    ∀ n : Nat,
      ∀ J : Instance D Γ,
        Instance.BoundedByValues Q J →
          Instance.BoundedByValues Q
            (P.iterateUntilFixed Q n J)
| 0, J, hBound => by
    simpa [iterateUntilFixed] using hBound
| n + 1, J, hBound => by
    rw [iterateUntilFixed]
    by_cases hFixed : P.immediateOn Q J = J
    · simpa [hFixed] using hBound
    · rw [if_neg hFixed]
      exact
        iterateUntilFixed_preserves_boundedByValues
          P Q n (P.immediateOn Q J)
          (P.immediateOn_preserves_boundedByValues
            Q hBound)

/-
  Fuelled iteration from any instance contained in a
  pre-fixed point remains contained in that pre-fixed point.
-/
theorem iterateUntilFixed_subset_of_preFixed
    (P : Program D Γ)
    (Q : Finset D)
    (J : Instance D Γ)
    (hClosed :
      Instance.Subset (P.immediateOn Q J) J) :
    ∀ n : Nat,
      ∀ K : Instance D Γ,
        Instance.Subset K J →
          Instance.Subset
            (P.iterateUntilFixed Q n K) J
| 0, K, hSub => by
    simpa [iterateUntilFixed] using hSub
| n + 1, K, hSub => by
    rw [iterateUntilFixed]
    by_cases hFixed : P.immediateOn Q K = K
    · simpa [hFixed] using hSub
    · rw [if_neg hFixed]
      exact
        iterateUntilFixed_subset_of_preFixed
          P Q J hClosed n (P.immediateOn Q K)
          (Instance.Subset_trans
            (P.immediateOn_mono Q hSub)
            hClosed)

/-
  If an instance grows pointwise, the remaining capacity
  over any fixed symbol list does not increase.
-/
theorem remainingCapacityForSyms_le_of_subset
    (Q : Finset D)
    {J K : Instance D Γ}
    (hSub : Instance.Subset J K) :
    ∀ xs : List Γ.syms,
      remainingCapacityForSyms Q K xs ≤
        remainingCapacityForSyms Q J xs
| [] => by
    simp [remainingCapacityForSyms]
| X :: xs => by
    have hHead :
        ((Tuple.allOver Q (Γ.arity X)) \ K X).card ≤
          ((Tuple.allOver Q (Γ.arity X)) \
            J X).card := by
      apply Finset.card_le_card
      intro t ht
      simp only [Finset.mem_sdiff] at ht ⊢
      exact ⟨ht.1, fun hM => ht.2 (hSub X hM)⟩
    have hTail :=
      remainingCapacityForSyms_le_of_subset Q hSub xs
    simpa [remainingCapacityForSyms] using
      Nat.add_le_add hHead hTail

/-
  Adding a new tuple inside the finite tuple universe
  strictly decreases the one-relation remaining capacity.
-/
theorem remainingCapacityOne_lt_of_new
    (Q : Finset D)
    {J K : Instance D Γ}
    (hSub : Instance.Subset J K)
    (hBoundN : Instance.BoundedByValues Q K)
    (X : Γ.syms)
    (hNew :
      ∃ t : Tuple D (Γ.arity X),
        t ∈ K X ∧ t ∉ J X) :
    ((Tuple.allOver Q (Γ.arity X)) \ K X).card <
      ((Tuple.allOver Q (Γ.arity X)) \ J X).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro t ht
    simp only [Finset.mem_sdiff] at ht ⊢
    exact ⟨ht.1, fun hM => ht.2 (hSub X hM)⟩
  · intro hEq
    rcases hNew with ⟨t, htN, htM⟩
    have htUniverse :
        t ∈ Tuple.allOver Q (Γ.arity X) :=
      Tuple.mem_allOver_of_isTupleOver Q
        (hBoundN X t htN)
    have htRight :
        t ∈ (Tuple.allOver Q (Γ.arity X)) \ J X := by
      simp [htUniverse, htM]
    have htLeft :
        t ∉ (Tuple.allOver Q (Γ.arity X)) \ K X := by
      simp [htN]
    exact htLeft (by simpa [hEq] using htRight)

/-
  If an instance grows at one listed relation symbol, then
  the remaining capacity over the whole list strictly
  decreases.
-/
theorem remainingCapacityForSyms_lt_of_new
    (Q : Finset D)
    {J K : Instance D Γ}
    (hSub : Instance.Subset J K)
    (hBoundN : Instance.BoundedByValues Q K)
    (X : Γ.syms)
    (hNew :
      ∃ t : Tuple D (Γ.arity X),
        t ∈ K X ∧ t ∉ J X) :
    ∀ xs : List Γ.syms,
      X ∈ xs →
        remainingCapacityForSyms Q K xs <
          remainingCapacityForSyms Q J xs
| [], hX => by
    cases hX
| Y :: ys, hX => by
    rcases List.mem_cons.mp hX with hEq | hTail
    · subst hEq
      have hHead :=
        remainingCapacityOne_lt_of_new
          Q hSub hBoundN X hNew
      have hTailLe :=
        remainingCapacityForSyms_le_of_subset Q hSub ys
      simpa [remainingCapacityForSyms] using
        Nat.add_lt_add_of_lt_of_le hHead hTailLe
    · have hHeadLe :
          ((Tuple.allOver Q (Γ.arity Y)) \ K Y).card ≤
            ((Tuple.allOver Q (Γ.arity Y)) \
              J Y).card := by
        apply Finset.card_le_card
        intro t ht
        simp only [Finset.mem_sdiff] at ht ⊢
        exact ⟨ht.1, fun hM => ht.2 (hSub Y hM)⟩
      have hTailLt :=
        remainingCapacityForSyms_lt_of_new
          Q hSub hBoundN X hNew ys hTail
      simpa [remainingCapacityForSyms] using
        Nat.add_lt_add_of_le_of_lt hHeadLe hTailLt

/-
  A non-fixed immediate-consequence step adds a tuple to
  some IDB relation.
-/
theorem exists_idb_new_of_immediateOn_ne
    (P : Program D Γ)
    (Q : Finset D)
    (J : Instance D Γ)
    (hNe : P.immediateOn Q J ≠ J) :
    ∃ X : Γ.syms,
      X ∈ P.idbList ∧
        ∃ t : Tuple D (Γ.arity X),
          t ∈ P.immediateOn Q J X ∧ t ∉ J X := by
  by_cases hExists :
      ∃ X : Γ.syms,
        X ∈ P.idbList ∧
          ∃ t : Tuple D (Γ.arity X),
            t ∈ P.immediateOn Q J X ∧ t ∉ J X
  · exact hExists
  · exfalso
    apply hNe
    apply Instance.ext
    intro X
    by_cases hX : X ∈ P.idb
    · apply Finset.ext
      intro t
      constructor
      · intro ht
        by_cases htM : t ∈ J X
        · exact htM
        · have hXList : X ∈ P.idbList := by
            simpa [idbList, idb] using hX
          exact False.elim
            (hExists ⟨X, hXList, t, ht, htM⟩)
      · intro ht
        exact P.immediateOn_inflationary Q J X ht
    · simp [immediateOn, hX]

/-
  Every non-fixed immediate-consequence step strictly
  decreases the remaining IDB tuple capacity.
-/
theorem remainingCapacity_decreases_of_immediateOn_ne
    (P : Program D Γ)
    (Q : Finset D)
    (J : Instance D Γ)
    (hBound : Instance.BoundedByValues Q J)
    (hNe : P.immediateOn Q J ≠ J) :
    P.remainingCapacity Q (P.immediateOn Q J) <
      P.remainingCapacity Q J := by
  rcases P.exists_idb_new_of_immediateOn_ne Q J hNe with
    ⟨X, hXList, hNew⟩
  unfold remainingCapacity
  exact
    remainingCapacityForSyms_lt_of_new
      Q
      (P.immediateOn_inflationary Q J)
      (P.immediateOn_preserves_boundedByValues Q hBound)
      X hNew P.idbList hXList

/-
  If the fuel is larger than the current remaining capacity,
  fuelled iteration reaches a fixed point.
-/
theorem iterateUntilFixed_fixed_of_remainingCapacity_lt
    (P : Program D Γ)
    (Q : Finset D) :
    ∀ n : Nat,
      ∀ J : Instance D Γ,
        Instance.BoundedByValues Q J →
          P.remainingCapacity Q J < n →
            P.immediateOn Q
                (P.iterateUntilFixed Q n J) =
              P.iterateUntilFixed Q n J
| 0, _M, _hBound, hFuel => by
    exact False.elim (Nat.not_lt_zero _ hFuel)
| n + 1, J, hBound, hFuel => by
    rw [iterateUntilFixed]
    by_cases hFixed : P.immediateOn Q J = J
    · simp [hFixed]
    · rw [if_neg hFixed]
      apply
        iterateUntilFixed_fixed_of_remainingCapacity_lt
          P Q n (P.immediateOn Q J)
      · exact
          P.immediateOn_preserves_boundedByValues
            Q hBound
      · have hDecrease :=
          P.remainingCapacity_decreases_of_immediateOn_ne
            Q J hBound hFixed
        have hFuelLe :
            P.remainingCapacity Q J ≤ n :=
          Nat.le_of_lt_succ hFuel
        have hSuccLe :
            P.remainingCapacity Q
                (P.immediateOn Q J) + 1 ≤
              P.remainingCapacity Q J :=
          Nat.succ_le_of_lt hDecrease
        exact Nat.lt_of_succ_le (hSuccLe.trans hFuelLe)

/-
  The initial empty-IDB instance is contained in the
  operational result.
-/
theorem initial_subset_LFP
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    Instance.Subset (P.initial I) (P.LFP I) := by
  exact
    P.iterateUntilFixed_inflationary (P.adom I)
      (P.lfpFuel I) (P.initial I)

/-
  The operational result preserves the EDB input exactly.
-/
theorem LFP_extendsInput
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    Instance.Extends P.ambient_extension_edbSchema I
      (P.LFP I) := by
  exact
    P.iterateUntilFixed_preserves_extendsInput
      (P.adom I) (P.lfpFuel I) (P.initial I)
      (P.initial_extendsInput I)

/-
  Every relation in the operational result is bounded by the
  input active domain.
-/
theorem LFP_boundedByValues
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    Instance.BoundedByValues (P.adom I) (P.LFP I) := by
  exact
    P.iterateUntilFixed_preserves_boundedByValues
      (P.adom I) (P.lfpFuel I) (P.initial I)
      (P.initial_boundedByValues I)

/-
  The operational result is closed under one cumulative
  immediate-consequence step. This is the fuel-bound
  theorem: enough fuel has been supplied for
  `iterateUntilFixed` to reach a fixed point.
-/
theorem LFP_fixed
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    P.immediate (P.LFP I) = P.LFP I := by
  rw [← P.immediateOnInputAdom_eq_immediate
    I (P.LFP I) (P.LFP_boundedByValues I)]
  unfold immediateOnInputAdom
  unfold LFP lfpFuel
  exact
    P.iterateUntilFixed_fixed_of_remainingCapacity_lt
      (P.adom I)
      (P.remainingCapacity (P.adom I) (P.initial I) + 1)
      (P.initial I)
      (P.initial_boundedByValues I)
      (Nat.lt_succ_self _)

/-
  The operational result is closed under one input-domain
  cumulative immediate-consequence step. This is the
  fuel-bound theorem used internally by the finite
  computation.
-/
theorem LFP_fixedOnInputAdom
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    P.immediateOnInputAdom I (P.LFP I) = P.LFP I := by
  unfold immediateOnInputAdom
  unfold LFP lfpFuel
  exact
    P.iterateUntilFixed_fixed_of_remainingCapacity_lt
      (P.adom I)
      (P.remainingCapacity (P.adom I) (P.initial I) + 1)
      (P.initial I)
      (P.initial_boundedByValues I)
      (Nat.lt_succ_self _)

/-
  Input-domain leastness among pre-fixed points containing
  the initial instance.
-/
theorem LFP_subset_of_immediateOnInputAdom_prefixed_point
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (J : Instance D Γ)
    (hInit : Instance.Subset (P.initial I) J)
    (hClosed :
      Instance.Subset
        (P.immediateOnInputAdom I J) J) :
    Instance.Subset (P.LFP I) J := by
  rw [immediateOnInputAdom] at hClosed
  exact
    P.iterateUntilFixed_subset_of_preFixed
      (P.adom I) J hClosed (P.lfpFuel I)
      (P.initial I) hInit

/-
  Every tuple produced by the input-domain evaluator is also
  produced by the current-state immediate consequence
  operator.
-/
theorem immediateOnInputAdom_subset_immediate
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (J : Instance D Γ) :
    Instance.Subset (P.immediateOnInputAdom I J)
      (P.immediate J) := by
  intro X t ht
  by_cases hX : X ∈ P.idb
  · have ht' :
        t ∈ J X ∪ P.IDBConsequenceOnInputAdom I J X := by
      simpa [immediateOnInputAdom, immediateOn, hX] using ht
    rcases Finset.mem_union.mp ht' with htM | htC
    · exact P.immediate_inflationary J X htM
    · unfold IDBConsequenceOnInputAdom IDBConsequenceOn at htC
      rcases P.IDBConsequenceOnForRules_sound
          (P.adom I) J X t P.rules.attach htC with
        ⟨r, _hr, hHead, σ, hBody, hTuple⟩
      rw [P.mem_immediate_iff J X t]
      exact Or.inr
        ⟨hX, ⟨r, hHead, σ, hBody, hTuple⟩⟩
  · have htM : t ∈ J X := by
      simpa [immediateOnInputAdom, immediateOn, hX] using ht
    exact P.immediate_inflationary J X htM

/-
  Leastness of the operational iteration among pre-fixed
  points of the current-state immediate consequence operator
  containing the initial instance.
-/
theorem LFP_subset_of_immediate_prefixed_point
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (J : Instance D Γ)
    (hInit : Instance.Subset (P.initial I) J)
    (hClosed :
      Instance.Subset
        (P.immediate J) J) :
    Instance.Subset (P.LFP I) J := by
  exact
    P.LFP_subset_of_immediateOnInputAdom_prefixed_point
      I J hInit
      (Instance.Subset_trans
        (P.immediateOnInputAdom_subset_immediate (I := I) J)
        hClosed)

/-
  Any instance extending the EDB input contains the initial
  empty-IDB instance.
-/
theorem initial_subset_of_extends
    (P : Program D Γ)
    (I : Instance D P.edbSchema)
    (J : Instance D Γ)
    (hExt :
      Instance.Extends P.ambient_extension_edbSchema I J) :
    Instance.Subset (P.initial I) J := by
  intro X t ht
  by_cases hX : X.1 ∈ P.edbSchema.syms
  · have htInput :
        Tuple.castArity
            (UnnamedSchema.arity_eq_of_extension_mem
              P.ambient_extension_edbSchema X hX) t ∈
          I ⟨X.1, hX⟩ :=
      (Instance.expandEmpty_mem_iff_of_mem
        P.ambient_extension_edbSchema I X hX t).mp
        (by simpa [initial] using ht)
    rw [hExt X hX]
    exact
      (Instance.relationOfExtension_mem_iff
        P.ambient_extension_edbSchema I X hX t).mpr
        htInput
  · have hEmpty :
        P.initial I X = ∅ := by
      simpa [initial] using
        Instance.expandEmpty_eq_empty_of_not_mem
          P.ambient_extension_edbSchema I X hX
    simp [hEmpty] at ht

end Program

end Datalog

------------------------------------------------------------
-- Minimal Model As An Operational Fixed Point
------------------------------------------------------------

namespace Datalog

namespace Program

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  The model-theoretic minimal model is closed under one
  current-state immediate-consequence step.
-/
theorem minimalModel_fixed
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    P.immediate (P.minimalModel I) =
      P.minimalModel I := by
  apply Instance.ext
  intro X
  apply Finset.ext
  intro t
  constructor
  · intro ht
    by_cases hX : X ∈ P.idb
    · have ht' :
          t ∈ P.minimalModel I X ∪
            P.IDBConsequence (P.minimalModel I) X := by
        simpa [immediate, immediateOn, IDBConsequence, hX]
          using ht
      rcases Finset.mem_union.mp ht' with ht | ht
      · exact ht
      · rw [P.IDBConsequence_eq_consequenceSPJU_eval
          (P.minimalModel I) X] at ht
        rw [P.consequenceSPJU_correct
          (P.minimalModel I) X t] at ht
        rcases ht with ⟨r, hHead, σ, hBody, hTuple⟩
        have hHeadSat :
            r.1.headSatisfied (P.minimalModel I) σ :=
          P.minimalModel_model I r σ hBody
        rw [← hTuple]
        cases hHead
        simpa [Rule.headEvalTupleAs] using hHeadSat
    · simpa [immediate, immediateOn, hX] using ht
  · intro ht
    exact P.immediate_inflationary (P.minimalModel I) X ht

end Program

end Datalog

------------------------------------------------------------
-- Operational Result As A Minimal Model
------------------------------------------------------------

namespace Datalog

namespace Program

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  The operational result satisfies every rule. Boundedness
  of the operational iteration supplies the finite
  assignment range needed to pass from arbitrary satisfying
  assignments to enumerated consequences.
-/
theorem LFP_model
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    P.Model (P.LFP I) := by
  intro r σ hBody
  have hBound :
      Instance.BoundedByValues (P.adom I) (P.LFP I) :=
    P.LFP_boundedByValues I
  have hVals :
      ∀ x : Var,
        x ∈ r.1.varList → σ x ∈ P.adom I := by
    intro x hx
    exact
      P.value_mem_of_rule_var_of_bounded
        hBound r σ hBody hx
  have hCons :
      r.1.headEvalTupleAs r.1.head.rel rfl σ ∈
        P.IDBConsequenceOnInputAdom I (P.LFP I)
          r.1.head.rel := by
    unfold IDBConsequenceOnInputAdom IDBConsequenceOn
    exact
      P.mem_IDBConsequenceOnForRules_of_bodySat
        (P.adom I) (P.LFP I) r.1.head.rel
        P.rules.attach r (List.mem_attach _ _)
        rfl σ hVals hBody
  have hImm :
      r.1.headEvalTupleAs r.1.head.rel rfl σ ∈
        P.immediateOnInputAdom I (P.LFP I)
          r.1.head.rel := by
    have hConsOn :
        r.1.headEvalTupleAs r.1.head.rel rfl σ ∈
          P.IDBConsequenceOn (P.adom I) (P.LFP I)
            r.1.head.rel := by
      simpa [IDBConsequenceOnInputAdom] using hCons
    simp [immediateOnInputAdom, immediateOn, P.head_mem_idb r.2,
      hConsOn]
  have hFixed :=
    congrFun (P.LFP_fixedOnInputAdom I) r.1.head.rel
  rw [hFixed] at hImm
  unfold Rule.headSatisfied RelAtom.Sat
  simpa [Rule.headEvalTupleAs] using hImm

/- The operational result preserves the EDB input. -/
theorem LFP_extends
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    P.Extends (P.LFP I) I := by
  simpa [Extends] using P.LFP_extendsInput I

/-
  Any model is a pre-fixed point of the cumulative
  current-state immediate-consequence operator.
-/
theorem model_is_immediate_prefixed_point
    (P : Program D Γ)
    (J : Instance D Γ)
    (hModel : P.Model J) :
    Instance.Subset
      (P.immediate J) J := by
  intro X t ht
  rw [P.mem_immediate_iff J X t] at ht
  rcases ht with htM | ⟨_hX, hWit⟩
  · exact htM
  · rcases hWit with ⟨r, hHead, σ, hBody, hTuple⟩
    have hHeadSat : r.1.headSatisfied J σ :=
      hModel r σ hBody
    rw [← hTuple]
    cases hHead
    simpa [Rule.headEvalTupleAs] using hHeadSat

/- The operational result is the minimal model. -/
theorem LFP_minimalModel
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    P.MinimalModel I (P.LFP I) := by
  refine ⟨P.LFP_model I, P.LFP_extends I, ?_⟩
  intro K hModel hExt
  exact
    P.LFP_subset_of_immediate_prefixed_point I K
      (P.initial_subset_of_extends I K
        (by simpa [Extends] using hExt))
      (P.model_is_immediate_prefixed_point K hModel)

/-
  The operational LFP agrees with the model-theoretic
  minimal model.
-/
theorem LFP_eq_minimalModel
    (P : Program D Γ)
    (I : Instance D P.edbSchema) :
    P.LFP I = P.minimalModel I :=
  P.minimalModels_are_unique I
    (P.LFP I) (P.minimalModel I)
    (P.LFP_minimalModel I)
    (P.minimalModel_isMinimalModel I)

end Program

end Datalog
