-- Author: Jesse Comer
import Databases.RelCalc.AdomSemantics
import Databases.RelCalc.CQ.Syntax
import Databases.UnnamedModel.Homomorphism

/-
  This file constructs canonical instances for
  equality-free conjunctive queries represented as ordinary
  relational-calculus queries.

  Key definitions include:
    * `RelCalc.Formula.relRows`
    * `RelCalc.Formula.canonicalInstance`
    * `RelCalc.Query.canonicalInstance`
    * `RelCalc.Query.canonicalTuple`
    * `RelCalc.Query.Contained`
    * `RelCalc.Query.CanonicalHom`

  The main theorem is:
    * `RelCalc.Query.chandra_merlin`

  Intervening definitions and lemmas are construction,
  helper, or proof support.
-/

------------------------------------------------------------
-- Terms As Canonical Domain Elements
------------------------------------------------------------

namespace RelCalc

namespace RelTerm

variable {D : Type}
variable [Domain D]

instance : Domain (RelTerm D) where
  inhabited := ⟨RelTerm.const default⟩
  decEq := inferInstance
  repr := inferInstance

end RelTerm

end RelCalc

-- Constant Mapping
------------------------------------------------------------

namespace RelTerm

variable {D E : Type}
variable [Domain D] [Domain E]

/-
  Interpret a source-domain term after choosing meanings for
  constants and variables in the target domain.
-/
def interp
    (η : D → E)
    (σ : Assign E) :
    RelTerm D → E
| .var x => σ x
| .const d => η d

/- Map constants in a term, preserving variables. -/
def mapConstants
    (η : D → E) :
    RelTerm D → RelTerm E
| .var x => .var x
| .const d => .const (η d)

@[simp] theorem mapConstants_var
    (η : D → E)
    (x : Var) :
    mapConstants η (.var x) = .var x :=
  rfl

@[simp] theorem mapConstants_const
    (η : D → E)
    (d : D) :
    mapConstants η (.const d) = .const (η d) :=
  rfl

/- Constant mapping does not change term variables. -/
theorem vars_mapConstants
    (η : D → E)
    (t : RelTerm D) :
    (t.mapConstants η).vars = t.vars := by
  cases t <;> rfl

/- Constant mapping does not change variables in a list. -/
theorem listVars_mapConstants
    (η : D → E) :
    ∀ ts : List (RelTerm D),
      RelTerm.listVars (ts.map (RelTerm.mapConstants η)) =
        RelTerm.listVars ts
| [] => rfl
| t :: ts => by
    simp [RelTerm.listVars, RelTerm.vars_mapConstants,
      listVars_mapConstants η ts]

/- Constant mapping does not change tuple variables. -/
theorem tupleVars_mapConstants
    (η : D → E)
    {n : Nat}
    (ts : Vector (RelTerm D) n) :
    RelTerm.tupleVars (ts.map (RelTerm.mapConstants η)) =
      RelTerm.tupleVars ts := by
  simp [RelTerm.tupleVars, Vector.toList_map,
    RelTerm.listVars_mapConstants]

/- Evaluating a constant-mapped term is interpretation. -/
theorem eval_mapConstants
    (η : D → E)
    (σ : Assign E)
    (t : RelTerm D) :
    RelTerm.eval σ (t.mapConstants η) =
      RelTerm.interp η σ t := by
  cases t <;> rfl

/-
  Evaluating a constant-mapped tuple is coordinatewise
  interpretation.
-/
theorem evalVector_mapConstants
    (η : D → E)
    (σ : Assign E)
    {n : Nat}
    (t : Tuple (RelTerm D) n) :
    RelTerm.evalVector σ (t.map (RelTerm.mapConstants η)) =
      t.map (RelTerm.interp η σ) := by
  apply Vector.ext
  intro i hi
  simp [RelTerm.evalVector, Vector.get, Vector.getElem_map,
    Vector.getElem_ofFn, RelTerm.eval_mapConstants]

end RelTerm

namespace RelCalc

namespace Formula

variable {A D E : Type}
variable [RelationNames A]
variable [Domain D] [Domain E]
variable {Γ : UnnamedSchema A}

/- Map constants in a formula, preserving variables. -/
def mapConstants
    (η : D → E) :
    Formula D Γ → Formula E Γ
| .top => .top
| .bot => .bot
| .eq t u =>
    .eq (t.mapConstants η) (u.mapConstants η)
| .rel a =>
    .rel
      { rel := a.rel,
        args := a.args.map (RelTerm.mapConstants η) }
| .and φ ψ =>
    .and (mapConstants η φ) (mapConstants η ψ)
| .or φ ψ =>
    .or (mapConstants η φ) (mapConstants η ψ)
| .not φ =>
    .not (mapConstants η φ)
| .imp φ ψ =>
    .imp (mapConstants η φ) (mapConstants η ψ)
| .iff φ ψ =>
    .iff (mapConstants η φ) (mapConstants η ψ)
| .forall_ x φ =>
    .forall_ x (mapConstants η φ)
| .exists_ x φ =>
    .exists_ x (mapConstants η φ)

/-
  Constant mapping does not change formula free variables.
-/
theorem freeVars_mapConstants
    (η : D → E)
    (φ : Formula D Γ) :
    (φ.mapConstants η).freeVars = φ.freeVars := by
  induction φ with
  | top =>
      rfl
  | bot =>
      rfl
  | eq t u =>
      simp [mapConstants, freeVars,
        RelTerm.vars_mapConstants]
  | rel a =>
      simp [mapConstants, freeVars,
        RelAtom.vars, RelTerm.tupleVars_mapConstants]
  | and φ ψ ihφ ihψ =>
      simp [mapConstants, freeVars, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      simp [mapConstants, freeVars, ihφ, ihψ]
  | not φ ih =>
      simp [mapConstants, freeVars, ih]
  | imp φ ψ ihφ ihψ =>
      simp [mapConstants, freeVars, ihφ, ihψ]
  | iff φ ψ ihφ ihψ =>
      simp [mapConstants, freeVars, ihφ, ihψ]
  | forall_ x φ ih =>
      simp [mapConstants, freeVars, ih]
  | exists_ x φ ih =>
      simp [mapConstants, freeVars, ih]

end Formula

namespace Query

variable {A D E : Type}
variable [RelationNames A]
variable [Domain D] [Domain E]
variable {Γ : UnnamedSchema A}
variable {n : Nat}

/- Map constants in a query, preserving output variables. -/
def mapConstants
    (η : D → E)
    (q : Query D Γ n) :
    Query E Γ n where
  vars := q.vars
  form := q.form.mapConstants η
  freeVars_eq := by
    rw [Formula.freeVars_mapConstants, q.freeVars_eq]

end Query

end RelCalc

------------------------------------------------------------
-- Canonical Instances
------------------------------------------------------------

namespace RelCalc

namespace Formula

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/- Relation rows for a formula and one relation symbol. -/
def relRows :
    Formula D Γ →
      (X : Γ.syms) →
        List (Tuple (RelTerm D) (Γ.arity X))
| .rel a, X =>
    if h : a.rel = X then
      [Tuple.castArity (by rw [h]) a.args]
    else
      []
| .and φ ψ, X =>
    relRows φ X ++ relRows ψ X
| .exists_ _ φ, X =>
    relRows φ X
| _, _ => []

/- Canonical instance generated by relation atoms. -/
def canonicalInstance
    (φ : Formula D Γ) :
    Instance (RelTerm D) Γ :=
  fun X => (φ.relRows X).toFinset

/-
  A relation atom contributes its row to its canonical
  instance.
-/
theorem rel_mem_canonicalInstance
    (a : RelAtom D Γ) :
    a.args ∈ (Formula.rel a).canonicalInstance a.rel := by
  unfold canonicalInstance relRows
  simp

end Formula

end RelCalc

------------------------------------------------------------
-- Canonical Row Satisfaction
------------------------------------------------------------

namespace RelCalc

namespace Formula

variable {A D E : Type}
variable [RelationNames A]
variable [Domain D] [Domain E]
variable {Γ : UnnamedSchema A}

/-
  An assignment satisfies all canonical relation rows of a
  source formula in a target instance.
-/
def RowsSat
    (φ : Formula D Γ)
    (η : D → E)
    (I : Instance E Γ)
    (σ : Assign E) : Prop :=
  ∀ X : Γ.syms,
    ∀ t : Tuple (RelTerm D) (Γ.arity X),
      t ∈ φ.canonicalInstance X →
        t.map (RelTerm.interp η σ) ∈ I X

end Formula

namespace RelTerm

variable {D : Type}
variable [Domain D]

/-
  A variable in the variable set of a term list occurs as
  the corresponding variable term in the list.
-/
theorem var_mem_list_of_mem_listVars
    {x : Var} :
    ∀ {ts : List (RelTerm D)},
      x ∈ RelTerm.listVars ts →
        RelTerm.var x ∈ ts
| [], hx => by
    simp [RelTerm.listVars] at hx
| t :: ts, hx => by
    cases t with
    | var y =>
        have hxEither :
            x = y ∨ x ∈ RelTerm.listVars ts := by
          simpa [RelTerm.listVars, RelTerm.vars,
            Finset.mem_union] using hx
        rcases hxEither with hxy | hxRest
        · subst hxy
          simp
        · right
          exact var_mem_list_of_mem_listVars hxRest
    | const _ =>
        have hxRest : x ∈ RelTerm.listVars ts := by
          simpa [RelTerm.listVars, RelTerm.vars] using hx
        right
        exact var_mem_list_of_mem_listVars hxRest

/-
  A variable in tuple variables occurs as the corresponding
  variable term in the tuple list.
-/
theorem var_mem_toList_of_mem_tupleVars
    {x : Var}
    {n : Nat}
    {t : Tuple (RelTerm D) n}
    (hx : x ∈ RelTerm.tupleVars t) :
    RelTerm.var x ∈ t.toList :=
  RelTerm.var_mem_list_of_mem_listVars hx

/-
  A constant term in a term list contributes its constant
  to the list constants.
-/
theorem const_mem_listConstants_of_mem_const
    {d : D} :
    ∀ {ts : List (RelTerm D)},
      RelTerm.const d ∈ ts →
        d ∈ RelTerm.listConstants ts
| [], ht => by
    cases ht
| t :: ts, ht => by
    cases t with
    | var x =>
        have htTail : RelTerm.const d ∈ ts := by
          simpa using ht
        exact Finset.mem_union.mpr
          (Or.inr
            (const_mem_listConstants_of_mem_const htTail))
    | const e =>
        have htEither :
            d = e ∨ RelTerm.const d ∈ ts := by
          simpa [RelTerm.listConstants, RelTerm.constants,
            Finset.mem_union] using ht
        exact Finset.mem_union.mpr <| by
          rcases htEither with hde | htTail
          · subst hde
            exact Or.inl (by simp [RelTerm.constants])
          · exact Or.inr
              (const_mem_listConstants_of_mem_const htTail)

/-
  A constant term in a tuple contributes its constant to
  the tuple constants.
-/
theorem const_mem_tupleConstants_of_mem_toList
    {d : D}
    {n : Nat}
    {t : Tuple (RelTerm D) n}
    (ht : RelTerm.const d ∈ t.toList) :
    d ∈ RelTerm.tupleConstants t :=
  RelTerm.const_mem_listConstants_of_mem_const ht

end RelTerm

namespace Formula

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Free variables in a relation conjunctive matrix occur in
  relation atoms.
-/
theorem freeVars_subset_relVars_of_isRelConjunctive
    {φ : Formula D Γ}
    (h : φ.IsRelConjunctive) :
    φ.freeVars ⊆ φ.relVars := by
  induction φ with
  | top =>
      intro x hx
      simp [Formula.freeVars] at hx
  | bot =>
      cases h
  | eq _ _ =>
      cases h
  | rel a =>
      intro x hx
      simpa [Formula.freeVars, Formula.relVars] using hx
  | and φ ψ ihφ ihψ =>
      rcases h with ⟨hφ, hψ⟩
      intro x hx
      rw [Formula.freeVars] at hx
      rw [Formula.relVars]
      exact Finset.mem_union.mpr <| by
        rcases Finset.mem_union.mp hx with hx | hx
        · exact Or.inl (ihφ hφ hx)
        · exact Or.inr (ihψ hψ hx)
  | or _ _ =>
      cases h
  | not _ =>
      cases h
  | imp _ _ =>
      cases h
  | iff _ _ =>
      cases h
  | forall_ _ _ =>
      cases h
  | exists_ _ _ =>
      cases h

/-
  Free variables in a structural equality-free CQ occur in
  relation atoms.
-/
theorem freeVars_subset_relVars_of_isRelCQ
    {φ : Formula D Γ}
    (h : φ.IsRelCQ) :
    φ.freeVars ⊆ φ.relVars := by
  induction φ with
  | top =>
      intro x hx
      simp [Formula.freeVars] at hx
  | bot =>
      cases h
  | eq _ _ =>
      cases h
  | rel a =>
      intro x hx
      simpa [Formula.freeVars, Formula.relVars] using hx
  | and φ ψ _ _ =>
      rcases h with ⟨hφ, hψ⟩
      intro x hx
      rw [Formula.freeVars] at hx
      rw [Formula.relVars]
      exact Finset.mem_union.mpr <| by
        rcases Finset.mem_union.mp hx with hx | hx
        · exact Or.inl
            (freeVars_subset_relVars_of_isRelConjunctive
              hφ hx)
        · exact Or.inr
            (freeVars_subset_relVars_of_isRelConjunctive
              hψ hx)
  | or _ _ =>
      cases h
  | not _ =>
      cases h
  | imp _ _ =>
      cases h
  | iff _ _ =>
      cases h
  | forall_ _ _ =>
      cases h
  | exists_ x φ ih =>
      intro y hy
      rw [Formula.freeVars] at hy
      rw [Formula.relVars]
      exact ih h (Finset.mem_of_mem_erase hy)

/-
  Variables occurring in relation atoms of a conjunctive
  matrix occur in its canonical active domain.
-/
theorem var_mem_canonicalAdom_of_relConj
    {φ : Formula D Γ}
    (hConj : φ.IsRelConjunctive)
    {x : Var}
    (hx : x ∈ φ.relVars) :
    RelTerm.var x ∈ φ.canonicalInstance.Adom := by
  induction φ with
  | top =>
      simp [Formula.relVars] at hx
  | bot =>
      cases hConj
  | eq _ _ =>
      cases hConj
  | rel a =>
      rw [Instance.in_Adom_iff_in_Relation]
      refine
        ⟨a.rel, a.args,
          Formula.rel_mem_canonicalInstance a, ?_⟩
      have hList :
          RelTerm.var x ∈ a.args.toList :=
        RelTerm.var_mem_toList_of_mem_tupleVars
          (by simpa [Formula.relVars] using hx)
      simpa using hList
  | and φ ψ ihφ ihψ =>
      rcases hConj with ⟨hφ, hψ⟩
      have hxEither :
          x ∈ φ.relVars ∨ x ∈ ψ.relVars := by
        simpa [Formula.relVars, Finset.mem_union] using hx
      rcases hxEither with hxφ | hxψ
      · have hAdom := ihφ hφ hxφ
        rw [Instance.in_Adom_iff_in_Relation] at hAdom
        rw [Instance.in_Adom_iff_in_Relation]
        rcases hAdom with ⟨Y, t, ht, hxMem⟩
        refine ⟨Y, t, ?_, hxMem⟩
        simpa [canonicalInstance, relRows] using
          (Or.inl ht :
            t ∈ φ.canonicalInstance Y ∨
              t ∈ ψ.canonicalInstance Y)
      · have hAdom := ihψ hψ hxψ
        rw [Instance.in_Adom_iff_in_Relation] at hAdom
        rw [Instance.in_Adom_iff_in_Relation]
        rcases hAdom with ⟨Y, t, ht, hxMem⟩
        refine ⟨Y, t, ?_, hxMem⟩
        simpa [canonicalInstance, relRows] using
          (Or.inr ht :
            t ∈ φ.canonicalInstance Y ∨
              t ∈ ψ.canonicalInstance Y)
  | or _ _ =>
      cases hConj
  | not _ =>
      cases hConj
  | imp _ _ =>
      cases hConj
  | iff _ _ =>
      cases hConj
  | forall_ _ _ =>
      cases hConj
  | exists_ _ _ =>
      cases hConj

/-
  Variables occurring in relation atoms of a structural
  equality-free CQ occur in its canonical active domain.
-/
theorem var_mem_canonicalAdom_of_mem_relVars
    {φ : Formula D Γ}
    (hCQ : φ.IsRelCQ)
    {x : Var}
    (hx : x ∈ φ.relVars) :
    RelTerm.var x ∈ φ.canonicalInstance.Adom := by
  induction φ with
  | top =>
      simp [Formula.relVars] at hx
  | bot =>
      cases hCQ
  | eq _ _ =>
      cases hCQ
  | rel a =>
      exact
        Formula.var_mem_canonicalAdom_of_relConj
          (φ := Formula.rel a) trivial hx
  | and φ ψ _ _ =>
      exact
        Formula.var_mem_canonicalAdom_of_relConj
          (φ := Formula.and φ ψ) hCQ hx
  | or _ _ =>
      cases hCQ
  | not _ =>
      cases hCQ
  | imp _ _ =>
      cases hCQ
  | iff _ _ =>
      cases hCQ
  | forall_ _ _ =>
      cases hCQ
  | exists_ _ φ ih =>
      exact ih hCQ (by simpa [Formula.relVars] using hx)

/-
  Constants appearing in canonical rows are constants of
  the generating formula.
-/
theorem const_mem_constants_of_mem_canonical
    {φ : Formula D Γ}
    {X : Γ.syms}
    {t : Tuple (RelTerm D) (Γ.arity X)}
    (ht : t ∈ φ.canonicalInstance X)
    {d : D}
    (hd : RelTerm.const d ∈ t.toList) :
    d ∈ φ.constants := by
  induction φ generalizing X t with
  | top =>
      simp [canonicalInstance, relRows] at ht
  | bot =>
      simp [canonicalInstance, relRows] at ht
  | eq _ _ =>
      simp [canonicalInstance, relRows] at ht
  | rel a =>
      by_cases hYX : a.rel = X
      · subst hYX
        have htEq : t = a.args := by
          simpa [canonicalInstance, relRows] using ht
        subst htEq
        exact
          RelTerm.const_mem_tupleConstants_of_mem_toList
            (by simpa using hd)
      · simp [canonicalInstance, relRows, hYX] at ht
  | and φ ψ ihφ ihψ =>
      have htEither :
          t ∈ φ.canonicalInstance X ∨
            t ∈ ψ.canonicalInstance X := by
        simpa [canonicalInstance, relRows] using ht
      rcases htEither with htφ | htψ
      · exact Finset.mem_union.mpr
          (Or.inl (ihφ htφ hd))
      · exact Finset.mem_union.mpr
          (Or.inr (ihψ htψ hd))
  | or _ _ =>
      simp [canonicalInstance, relRows] at ht
  | not _ =>
      simp [canonicalInstance, relRows] at ht
  | imp _ _ =>
      simp [canonicalInstance, relRows] at ht
  | iff _ _ =>
      simp [canonicalInstance, relRows] at ht
  | forall_ _ _ =>
      simp [canonicalInstance, relRows] at ht
  | exists_ _ φ ih =>
      exact ih ht hd

end Formula

namespace Formula

variable {A D E : Type}
variable [RelationNames A]
variable [Domain D] [Domain E]
variable {Γ : UnnamedSchema A}

/-
  Matrix satisfaction gives preservation of all generated
  canonical rows.
-/
theorem rowsSat_of_arbitrarySat_isRelConjunctive
    {φ : Formula D Γ}
    {Q : Set E}
    {I : Instance E Γ}
    {η : D → E}
    {σ : Assign E}
    (hConj : φ.IsRelConjunctive)
    (hSat :
      Formula.ArbitraryAssignSatIn Q I σ
        (φ.mapConstants η)) :
    φ.RowsSat η I σ := by
  induction φ with
  | top =>
      intro X t ht
      simp [canonicalInstance, relRows] at ht
  | bot =>
      cases hConj
  | eq _ _ =>
      cases hConj
  | rel a =>
      intro Y t ht
      by_cases hXY : a.rel = Y
      · subst hXY
        have htEq : t = a.args := by
          simpa [canonicalInstance, relRows] using ht
        subst htEq
        simpa [Formula.mapConstants,
          Formula.ArbitraryAssignSatIn, RelAtom.Sat,
          RelAtom.evalFact, RelFact.Mem,
          RelAtom.evalTuple, RelTerm.evalVector_mapConstants]
          using hSat
      · simp [canonicalInstance, relRows, hXY] at ht
  | and φ ψ ihφ ihψ =>
      rcases hConj with ⟨hφ, hψ⟩
      rcases hSat with ⟨hSatφ, hSatψ⟩
      have hRowsφ := ihφ hφ hSatφ
      have hRowsψ := ihψ hψ hSatψ
      intro X t ht
      have htEither :
          t ∈ φ.canonicalInstance X ∨
            t ∈ ψ.canonicalInstance X := by
        simpa [canonicalInstance, relRows] using ht
      rcases htEither with htφ | htψ
      · exact hRowsφ X t htφ
      · exact hRowsψ X t htψ
  | or _ _ =>
      cases hConj
  | not _ =>
      cases hConj
  | imp _ _ =>
      cases hConj
  | iff _ _ =>
      cases hConj
  | forall_ _ _ =>
      cases hConj
  | exists_ _ _ =>
      cases hConj

/-
  Preservation of generated canonical rows gives matrix
  satisfaction.
-/
theorem arbitrarySat_of_rowsSat_isRelConjunctive
    {φ : Formula D Γ}
    {Q : Set E}
    {I : Instance E Γ}
    {η : D → E}
    {σ : Assign E}
    (hConj : φ.IsRelConjunctive)
    (hRows : φ.RowsSat η I σ) :
    Formula.ArbitraryAssignSatIn Q I σ
      (φ.mapConstants η) := by
  induction φ with
  | top =>
      simp [Formula.mapConstants,
        Formula.ArbitraryAssignSatIn]
  | bot =>
      cases hConj
  | eq _ _ =>
      cases hConj
  | rel a =>
      have hMem :
          a.args.map (RelTerm.interp η σ) ∈ I a.rel :=
        hRows a.rel a.args
          (Formula.rel_mem_canonicalInstance a)
      simpa [Formula.mapConstants,
        Formula.ArbitraryAssignSatIn, RelAtom.Sat,
        RelAtom.evalFact, RelFact.Mem,
        RelAtom.evalTuple, RelTerm.evalVector_mapConstants]
        using hMem
  | and φ ψ ihφ ihψ =>
      rcases hConj with ⟨hφ, hψ⟩
      constructor
      · apply ihφ hφ
        intro X t ht
        apply hRows X t
        simpa [canonicalInstance, relRows] using
          (Or.inl ht :
            t ∈ φ.canonicalInstance X ∨
              t ∈ ψ.canonicalInstance X)
      · apply ihψ hψ
        intro X t ht
        apply hRows X t
        simpa [canonicalInstance, relRows] using
          (Or.inr ht :
            t ∈ φ.canonicalInstance X ∨
              t ∈ ψ.canonicalInstance X)
  | or _ _ =>
      cases hConj
  | not _ =>
      cases hConj
  | imp _ _ =>
      cases hConj
  | iff _ _ =>
      cases hConj
  | forall_ _ _ =>
      cases hConj
  | exists_ _ _ =>
      cases hConj

end Formula

namespace Formula

variable {A D E : Type}
variable [RelationNames A]
variable [Domain D] [Domain E]
variable {Γ : UnnamedSchema A}

/-
  Satisfaction of a structural equality-free CQ yields a
  total assignment preserving its canonical rows.
-/
theorem exists_rowsSat_of_satIn_isRelCQ
    {φ : Formula D Γ}
    {Q : Set E}
    {I : Instance E Γ}
    {η : D → E}
    {σ : Assign E}
    (hCQ : φ.IsRelCQ)
    (hSat :
      Formula.SatIn (φ.mapConstants η) I σ Q) :
    ∃ τ : Assign E,
      Assign.AgreeOn τ σ φ.freeVars ∧
        φ.RowsSat η I τ := by
  induction φ generalizing σ with
  | top =>
      refine ⟨σ, ?_, ?_⟩
      · intro x hx
        rfl
      · exact
          Formula.rowsSat_of_arbitrarySat_isRelConjunctive
            (φ := Formula.top) trivial hSat.2
  | bot =>
      cases hCQ
  | eq _ _ =>
      cases hCQ
  | rel a =>
      refine ⟨σ, ?_, ?_⟩
      · intro x hx
        rfl
      · exact
          Formula.rowsSat_of_arbitrarySat_isRelConjunctive
            (φ := Formula.rel a) trivial hSat.2
  | and φ ψ _ _ =>
      refine ⟨σ, ?_, ?_⟩
      · intro x hx
        rfl
      · exact
          Formula.rowsSat_of_arbitrarySat_isRelConjunctive
            (φ := Formula.and φ ψ) hCQ hSat.2
  | or _ _ =>
      cases hCQ
  | not _ =>
      cases hCQ
  | imp _ _ =>
      cases hCQ
  | iff _ _ =>
      cases hCQ
  | forall_ _ _ =>
      cases hCQ
  | exists_ x φ ih =>
      rcases hSat with ⟨hMaps, hRaw⟩
      change
        ∃ d ∈ Q,
          Formula.ArbitraryAssignSatIn Q I
            (Assign.update σ x d)
            (φ.mapConstants η) at hRaw
      rcases hRaw with ⟨d, hdQ, hBodyRaw⟩
      have hBodyMaps :
          Assign.MapsInto (Assign.update σ x d)
            (φ.mapConstants η).freeVars Q := by
        intro y hy
        have hyOrig : y ∈ φ.freeVars := by
          simpa [Formula.freeVars_mapConstants] using hy
        by_cases hyx : y = x
        · subst hyx
          simpa [Assign.update] using hdQ
        · have hyOuter :
              y ∈
                ((Formula.exists_ x φ).mapConstants
                  η).freeVars := by
            simp [Formula.mapConstants, Formula.freeVars,
              Formula.freeVars_mapConstants,
              Finset.mem_erase,
              hyx, hyOrig]
          have hQ := hMaps y hyOuter
          simpa [Assign.update, hyx] using hQ
      have hBodySat :
          Formula.SatIn (φ.mapConstants η) I
            (Assign.update σ x d) Q :=
        ⟨hBodyMaps, hBodyRaw⟩
      rcases ih hCQ hBodySat with ⟨τ, hAgree, hRows⟩
      refine ⟨τ, ?_, ?_⟩
      · intro y hy
        have hyErase :
            y ∈ φ.freeVars.erase x := by
          simpa [Formula.freeVars] using hy
        have hyNe : y ≠ x :=
          (Finset.mem_erase.mp hyErase).1
        have hyBody : y ∈ φ.freeVars :=
          (Finset.mem_erase.mp hyErase).2
        have h := hAgree y hyBody
        simpa [Assign.update, hyNe] using h
      · intro Y t ht
        exact hRows Y t
          (by simpa [canonicalInstance, relRows] using ht)

/-
  Canonical-row preservation plus range restriction gives
  satisfaction of a safe equality-free CQ.
-/
theorem satIn_of_rowsSat_isSafeRelCQ
    {φ : Formula D Γ}
    {Q : Set E}
    {I : Instance E Γ}
    {η : D → E}
    {σ : Assign E}
    (hSafeCQ : φ.IsSafeRelCQ)
    (hRelQ : ∀ x : Var, x ∈ φ.relVars → Q (σ x))
    (hRows : φ.RowsSat η I σ) :
    Formula.SatIn (φ.mapConstants η) I σ Q := by
  rcases hSafeCQ with ⟨hCQ, hSafe⟩
  induction φ generalizing σ with
  | top =>
      refine ⟨?_, ?_⟩
      · intro x hx
        simp [Formula.mapConstants, Formula.freeVars] at hx
      · simp [Formula.mapConstants,
          Formula.ArbitraryAssignSatIn]
  | bot =>
      cases hCQ
  | eq _ _ =>
      cases hCQ
  | rel a =>
      refine ⟨?_, ?_⟩
      · intro x hx
        have hxOrig :
            x ∈ (Formula.rel a).freeVars := by
          simpa [Formula.freeVars_mapConstants] using hx
        exact hRelQ x
          (Formula.freeVars_subset_relVars_of_isRelCQ
            hCQ hxOrig)
      · exact
          Formula.arbitrarySat_of_rowsSat_isRelConjunctive
            (φ := Formula.rel a) trivial hRows
  | and φ ψ _ _ =>
      refine ⟨?_, ?_⟩
      · intro x hx
        have hxOrig :
            x ∈ (Formula.and φ ψ).freeVars := by
          simpa [Formula.freeVars_mapConstants] using hx
        exact hRelQ x
          (Formula.freeVars_subset_relVars_of_isRelCQ
            hCQ hxOrig)
      · exact
          Formula.arbitrarySat_of_rowsSat_isRelConjunctive
            (φ := Formula.and φ ψ) hCQ hRows
  | or _ _ =>
      cases hCQ
  | not _ =>
      cases hCQ
  | imp _ _ =>
      cases hCQ
  | iff _ _ =>
      cases hCQ
  | forall_ _ _ =>
      cases hCQ
  | exists_ x φ ih =>
      rcases hSafe with ⟨hxRel, hSafeBody⟩
      refine ⟨?_, ?_⟩
      · intro y hy
        have hyOrig :
            y ∈ (Formula.exists_ x φ).freeVars := by
          simpa [Formula.freeVars_mapConstants] using hy
        exact hRelQ y
          (Formula.freeVars_subset_relVars_of_isRelCQ
            hCQ hyOrig)
      · change
          ∃ d ∈ Q,
            Formula.ArbitraryAssignSatIn Q I
              (Assign.update σ x d)
              (φ.mapConstants η)
        refine ⟨σ x, hRelQ x ?_, ?_⟩
        · simpa [Formula.relVars] using hxRel
        · have hRowsBody :
              φ.RowsSat η I σ := by
            intro Y t ht
            exact hRows Y t
              (by
                simpa [canonicalInstance, relRows] using ht)
          have hRelQBody :
              ∀ y : Var,
                y ∈ φ.relVars →
                  Q (σ y) := by
            intro y hy
            exact hRelQ y
              (by simpa [Formula.relVars] using hy)
          have hBodySat :
              Formula.SatIn (φ.mapConstants η) I σ Q :=
            ih hRelQBody hRowsBody hCQ hSafeBody
          rw [Assign.update_self]
          exact hBodySat.2

end Formula

namespace Query

variable {A D : Type}
variable [RelationNames A]
variable [Domain D]
variable {Γ : UnnamedSchema A}
variable {n : Nat}

/- Canonical instance generated by a query formula. -/
def canonicalInstance
    (q : Query D Γ n) :
    Instance (RelTerm D) Γ :=
  q.form.canonicalInstance

/- Canonical output tuple of a query. -/
def canonicalTuple
    (q : Query D Γ n) :
    Tuple (RelTerm D) n :=
  q.vars.map RelTerm.var

end Query

end RelCalc

------------------------------------------------------------
-- Containment And Canonical Homomorphisms
------------------------------------------------------------

namespace RelCalc

namespace Query

variable {A D E : Type}
variable [RelationNames A]
variable [Domain D] [Domain E]
variable {Γ : UnnamedSchema A}
variable {n : Nat}

/- Interpret source constants as canonical constants. -/
def constTerm
    {D : Type}
    [Domain D] :
    D → RelTerm D :=
  fun d => RelTerm.const d

/-
  The canonical variable assignment sends every variable to
  its variable term.
-/
def canonicalAssign
    {D : Type}
    [Domain D] :
    Assign (RelTerm D) :=
  fun x => RelTerm.var x

/- Canonical interpretation fixes every term. -/
theorem interp_constTerm_canonicalAssign
    (t : RelTerm D) :
    RelTerm.interp (Query.constTerm (D := D))
      (Query.canonicalAssign (D := D)) t = t := by
  cases t <;> rfl

/- Canonical interpretation fixes every tuple of terms. -/
theorem tuple_map_interp_constTerm_canonicalAssign
    {m : Nat}
    (t : Tuple (RelTerm D) m) :
    t.map
        (RelTerm.interp (Query.constTerm (D := D))
          (Query.canonicalAssign (D := D))) =
      t := by
  apply Vector.ext
  intro i hi
  simp [Vector.getElem_map,
    Query.interp_constTerm_canonicalAssign]

/-
  Domain-polymorphic containment for queries with
  constants.
-/
def Contained
    (q₁ q₂ : Query D Γ n) : Prop :=
  ∀ {E : Type} [Domain E] (η : D → E),
    QueryEval.Contained
      (D := E) (Γ := Γ) (n := n)
      (q₁.mapConstants η) (q₂.mapConstants η)

/-
  A map between canonical instances preserves all
  canonical relation tuples.
-/
def CanonicalPreserves
    (q₁ q₂ : Query D Γ n)
    (f : RelTerm D → RelTerm D) : Prop :=
  ∀ X : Γ.syms,
    ∀ t : Tuple (RelTerm D) (Γ.arity X),
      t ∈ q₁.canonicalInstance X →
        t.map f ∈ q₂.canonicalInstance X

/-
  Existence of a canonical homomorphism from the first
  query to the second, fixing occurring constants and
  mapping the first output tuple to the second output tuple.
-/
def CanonicalHom
    (q₁ q₂ : Query D Γ n) : Prop :=
  ∃ f : RelTerm D → RelTerm D,
    CanonicalPreserves q₁ q₂ f ∧
      (∀ d : D,
        d ∈ q₁.constants →
          f (RelTerm.const d) = RelTerm.const d) ∧
      (∀ i : Fin n,
        f (RelTerm.var (q₁.vars.get i)) =
          RelTerm.var (q₂.vars.get i))

/- The identity map is a canonical homomorphism. -/
theorem CanonicalHom.refl
    (q : Query D Γ n) :
    q.CanonicalHom q := by
  refine ⟨fun t => t, ?_, ?_, ?_⟩
  · intro X t ht
    simpa using ht
  · intro d _hd
    rfl
  · intro i
    rfl

/- A safe query's canonical rows satisfy themselves. -/
theorem canonical_rowsSat_self
    (q : Query D Γ n) :
    q.form.RowsSat
      (Query.constTerm (D := D))
      q.canonicalInstance
      (Query.canonicalAssign (D := D)) := by
  intro X t ht
  rw [Query.tuple_map_interp_constTerm_canonicalAssign]
  simpa [Query.canonicalInstance] using ht

/-
  Relation variables of a structural CQ are in the active
  domain of its canonical instance.
-/
theorem canonical_relVar_mem_adom
    (q : Query D Γ n)
    (hCQ : q.form.IsRelCQ)
    {x : Var}
    (hx : x ∈ q.form.relVars) :
    RelTerm.var x ∈
      RelCalc.Adom
        ((q.mapConstants
          (Query.constTerm (D := D))).form)
        q.canonicalInstance := by
  unfold RelCalc.Adom
  apply Finset.mem_union.mpr
  exact Or.inl
    (Formula.var_mem_canonicalAdom_of_mem_relVars
      hCQ hx)

/-
  A safe query's canonical output tuple belongs to its
  evaluation on its canonical instance.
-/
theorem canonicalTuple_mem_eval
    (q : Query D Γ n)
    (hSafe : q.IsSafeRelCQ) :
    q.canonicalTuple ∈
      (q.mapConstants
        (Query.constTerm (D := D))).eval
        q.canonicalInstance := by
  rw [Query.in_eval_iff_satTuple]
  refine
    ⟨Query.canonicalAssign (D := D), ?_, ?_⟩
  · intro i
    change
      RelTerm.var (q.vars.get i) =
        (q.vars.map RelTerm.var).get i
    change
      RelTerm.var q.vars[i.1] =
        (q.vars.map RelTerm.var)[i.1]
    simp [Vector.getElem_map]
  · exact
      Formula.satIn_of_rowsSat_isSafeRelCQ
        (φ := q.form)
        (Q :=
          Adom.toSet
            ((q.mapConstants
              (Query.constTerm (D := D))).form)
            q.canonicalInstance)
        (I := q.canonicalInstance)
        (η := Query.constTerm (D := D))
        (σ := Query.canonicalAssign (D := D))
        (by simpa [Query.IsSafeRelCQ] using hSafe)
        (by
          intro x hx
          have hSafeForm :
              q.form.IsSafeRelCQ := by
            simpa [Query.IsSafeRelCQ] using hSafe
          exact q.canonical_relVar_mem_adom
            hSafeForm.1
            hx)
        (q.canonical_rowsSat_self)

/-
  Containment yields a homomorphism between canonical
  instances in the Chandra-Merlin direction.
-/
theorem canonicalHom_of_contained
    (q₁ q₂ : Query D Γ n)
    (h₁ : q₁.IsSafeRelCQ)
    (h₂ : q₂.IsSafeRelCQ)
    (hCont : q₁.Contained q₂) :
    q₂.CanonicalHom q₁ := by
  have hMem₁ :
      q₁.canonicalTuple ∈
        (q₁.mapConstants
          (Query.constTerm (D := D))).eval
          q₁.canonicalInstance :=
    q₁.canonicalTuple_mem_eval h₁
  have hContainCanonical :=
    hCont (Query.constTerm (D := D))
  have hMem₂ :
      q₁.canonicalTuple ∈
        (q₂.mapConstants
          (Query.constTerm (D := D))).eval
          q₁.canonicalInstance :=
    hContainCanonical q₁.canonicalInstance hMem₁
  have hSat₂ :
      (q₂.mapConstants
        (Query.constTerm (D := D))).SatTuple
        q₁.canonicalInstance q₁.canonicalTuple :=
    (Query.in_eval_iff_satTuple
      (q₂.mapConstants
        (Query.constTerm (D := D)))
      q₁.canonicalInstance q₁.canonicalTuple).mp hMem₂
  rcases hSat₂ with ⟨σ, hReal, hSat⟩
  have hSafe₂Form :
      q₂.form.IsSafeRelCQ := by
    simpa [Query.IsSafeRelCQ] using h₂
  rcases
      Formula.exists_rowsSat_of_satIn_isRelCQ
        (φ := q₂.form)
        (η := Query.constTerm (D := D))
        hSafe₂Form.1 hSat with
    ⟨τ, hAgree, hRows⟩
  let f : RelTerm D → RelTerm D
    | .var x => τ x
    | .const d => RelTerm.const d
  refine ⟨f, ?_, ?_, ?_⟩
  · intro X t ht
    have hEq :
        t.map f =
          t.map
            (RelTerm.interp
              (Query.constTerm (D := D)) τ) := by
      apply Vector.ext
      intro i hi
      cases t[i] <;> rfl
    rw [hEq]
    exact hRows X t ht
  · intro d _hd
    rfl
  · intro i
    have hxFree :
        q₂.vars.get i ∈ q₂.form.freeVars := by
      rw [q₂.freeVars_eq]
      change q₂.vars[i.1] ∈ q₂.vars.toList.toFinset
      simp
    have hAgree_i := hAgree (q₂.vars.get i) hxFree
    have hReal_i := hReal i
    have hReal_i' :
        σ (q₂.vars.get i) =
          q₁.canonicalTuple.get i := by
      simpa [Query.mapConstants] using hReal_i
    change τ (q₂.vars.get i) =
      RelTerm.var (q₁.vars.get i)
    rw [hAgree_i, hReal_i']
    change
      (q₁.vars.map RelTerm.var).get i =
        RelTerm.var (q₁.vars.get i)
    change
      (q₁.vars.map RelTerm.var)[i.1] =
        RelTerm.var q₁.vars[i.1]
    simp [Vector.getElem_map]

/-
  Canonical tuple preservation sends active-domain
  elements of the source canonical instance into the target
  canonical active domain.
-/
theorem canonicalPreserves_adom
    {q₁ q₂ : Query D Γ n}
    {f : RelTerm D → RelTerm D}
    (hPres : CanonicalPreserves q₁ q₂ f)
    {u : RelTerm D}
    (hu : u ∈ q₁.canonicalInstance.Adom) :
    f u ∈ q₂.canonicalInstance.Adom := by
  rw [Instance.in_Adom_iff_in_Relation] at hu
  rw [Instance.in_Adom_iff_in_Relation]
  rcases hu with ⟨X, t, ht, huMem⟩
  refine ⟨X, t.map f, hPres X t ht, ?_⟩
  have huList : u ∈ t.toList := by
    simpa using huMem
  have hMapList :
      f u ∈ (t.map f).toList := by
    rw [Vector.toList_map]
    exact List.mem_map.mpr ⟨u, huList, rfl⟩
  simpa using hMapList

/-
  Row satisfaction sends interpreted canonical active-domain
  terms into the target instance active domain.
-/
theorem interp_mem_adom_of_rowsSat
    (q : Query D Γ n)
    {η : D → E}
    {I : Instance E Γ}
    {σ : Assign E}
    (hRows : q.form.RowsSat η I σ)
    {u : RelTerm D}
    (hu : u ∈ q.canonicalInstance.Adom) :
    RelTerm.interp η σ u ∈ I.Adom := by
  rw [Instance.in_Adom_iff_in_Relation] at hu
  rw [Instance.in_Adom_iff_in_Relation]
  rcases hu with ⟨X, t, ht, huMem⟩
  refine ⟨X, t.map (RelTerm.interp η σ),
    hRows X t (by simpa [Query.canonicalInstance] using ht),
    ?_⟩
  have huList : u ∈ t.toList := by
    simpa using huMem
  have hMapList :
      RelTerm.interp η σ u ∈
        (t.map (RelTerm.interp η σ)).toList := by
    rw [Vector.toList_map]
    exact List.mem_map.mpr ⟨u, huList, rfl⟩
  simpa using hMapList

/- A canonical homomorphism yields semantic containment. -/
theorem contained_of_canonicalHom
    (q₁ q₂ : Query D Γ n)
    (h₁ : q₁.IsSafeRelCQ)
    (h₂ : q₂.IsSafeRelCQ)
    (hHom : q₂.CanonicalHom q₁) :
    q₁.Contained q₂ := by
  rcases hHom with ⟨f, hPres, hConst, hOut⟩
  intro E instE η I t ht
  have hSat₁ :
      (q₁.mapConstants η).SatTuple I t :=
    (Query.in_eval_iff_satTuple
      (q₁.mapConstants η) I t).mp ht
  rcases hSat₁ with ⟨σ, hReal, hSat⟩
  have hSafe₁Form :
      q₁.form.IsSafeRelCQ := by
    simpa [Query.IsSafeRelCQ] using h₁
  have hSafe₂Form :
      q₂.form.IsSafeRelCQ := by
    simpa [Query.IsSafeRelCQ] using h₂
  rcases
      Formula.exists_rowsSat_of_satIn_isRelCQ
        (φ := q₁.form) (η := η)
        hSafe₁Form.1 hSat with
    ⟨τ₁, hAgree₁, hRows₁⟩
  let τ₂ : Assign E :=
    fun x => RelTerm.interp η τ₁ (f (RelTerm.var x))
  have hRows₂ :
      q₂.form.RowsSat η I τ₂ := by
    intro X row hrow
    have hTargetRow :
        row.map f ∈ q₁.canonicalInstance X :=
      hPres X row hrow
    have hRowsTarget :
        (row.map f).map (RelTerm.interp η τ₁) ∈ I X :=
      hRows₁ X (row.map f) hTargetRow
    have hEq :
        row.map (RelTerm.interp η τ₂) =
          (row.map f).map (RelTerm.interp η τ₁) := by
      apply Vector.ext
      intro i hi
      simp only [Vector.getElem_map]
      let j : Fin (Γ.arity X) := ⟨i, hi⟩
      change
        RelTerm.interp η τ₂ (row.get j) =
          RelTerm.interp η τ₁ (f (row.get j))
      cases hTerm : row.get j with
      | var x =>
          rfl
      | const d =>
          have hTermMem :
              RelTerm.const d ∈ row.toList := by
            have hGetMem :
                row.get j ∈ row.toList := by
              change row[j.1] ∈ row.toList
              rw [Vector.mem_toList_iff]
              exact Vector.getElem_mem j.2
            simpa [hTerm] using hGetMem
          have hdConst :
              d ∈ q₂.constants :=
            Formula.const_mem_constants_of_mem_canonical
              (φ := q₂.form) hrow hTermMem
          have hf := hConst d hdConst
          rw [hf]
          rfl
    rw [hEq]
    exact hRowsTarget
  have hRelQ₂ :
      ∀ x : Var,
        x ∈ q₂.form.relVars →
          Adom.toSet
            ((q₂.mapConstants η).form) I (τ₂ x) := by
    intro x hx
    unfold Adom.toSet RelCalc.Adom
    apply Finset.mem_union.mpr
    apply Or.inl
    have hxSourceAdom :
        RelTerm.var x ∈ q₂.canonicalInstance.Adom :=
      Formula.var_mem_canonicalAdom_of_mem_relVars
        hSafe₂Form.1 hx
    have hxTargetAdom :
        f (RelTerm.var x) ∈ q₁.canonicalInstance.Adom :=
      Query.canonicalPreserves_adom
        (q₁ := q₂) (q₂ := q₁)
        hPres hxSourceAdom
    exact
      q₁.interp_mem_adom_of_rowsSat
        (η := η) (I := I) (σ := τ₁)
        hRows₁ hxTargetAdom
  have hSat₂ :
      (q₂.mapConstants η).form.AdomSat I τ₂ :=
    Formula.satIn_of_rowsSat_isSafeRelCQ
      (φ := q₂.form)
      (Q := Adom.toSet ((q₂.mapConstants η).form) I)
      (I := I) (η := η) (σ := τ₂)
      hSafe₂Form hRelQ₂ hRows₂
  apply
    (Query.in_eval_iff_satTuple
      (q₂.mapConstants η) I t).mpr
  refine ⟨τ₂, ?_, hSat₂⟩
  intro i
  have hxFree :
      q₁.vars.get i ∈ q₁.form.freeVars := by
    rw [q₁.freeVars_eq]
    change q₁.vars[i.1] ∈ q₁.vars.toList.toFinset
    simp
  have hAgree_i := hAgree₁ (q₁.vars.get i) hxFree
  have hReal_i := hReal i
  have hReal_i' :
      σ (q₁.vars.get i) = t.get i := by
    simpa [Query.mapConstants] using hReal_i
  have hOut_i := hOut i
  change
    RelTerm.interp η τ₁
        (f (RelTerm.var (q₂.vars.get i))) =
      t.get i
  rw [hOut_i]
  change τ₁ (q₁.vars.get i) = t.get i
  rw [hAgree_i, hReal_i']

/-
  Chandra-Merlin containment theorem for safe equality-free
  RelCalc conjunctive queries under active-domain
  semantics.
-/
theorem chandra_merlin
    (q₁ q₂ : Query D Γ n)
    (h₁ : q₁.IsSafeRelCQ)
    (h₂ : q₂.IsSafeRelCQ) :
    q₁.Contained q₂ ↔ q₂.CanonicalHom q₁ := by
  constructor
  · exact canonicalHom_of_contained q₁ q₂ h₁ h₂
  · exact contained_of_canonicalHom q₁ q₂ h₁ h₂

end Query

end RelCalc
