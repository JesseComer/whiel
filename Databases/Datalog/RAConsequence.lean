import Databases.Datalog.RuleSemantics
import Databases.UnnamedRA.SPJ.Semantics

/-
  This file provides functions transforming rules of Datalog
  programs into corresponding RA queries.

  For a rule, the construction builds an SPJ relational
  algebra expression from the relational atoms in the body,
  selections for constants, repeated variables, and equality
  atoms. The expression then projects onto head variables.
  For a program and relation `X`, the SPJU query unions the
  rule SPJ expressions whose head relation is `X`.

  Key definitions include:
    * `Datalog.Rule.consequenceSPJ`
    * `Datalog.Rule.toSPJ`
    * `Datalog.Program.consequenceSPJU`
    * `Datalog.Program.consequenceWitness`

  Correctness of the construction is proven:
    * `Datalog.Rule.consequenceSPJ_isSPJ`
    * `Datalog.Rule.consequenceSPJ_correct`
    * `Datalog.Program.consequenceSPJU_isSPJU`
    * `Datalog.Program.consequenceSPJU_correct`
-/

------------------------------------------------------------
-- Translation Support
------------------------------------------------------------

namespace Datalog

namespace RAConsequence

variable {A D : Type}
variable [RelationNames A] [Domain D]

/-
  Equality plans either add selections or make the whole
  body product empty.
-/
private inductive EqualityPlan
    (D : Type) [Domain D] where
| sels : List (Sel D) → EqualityPlan D
| empty : EqualityPlan D

namespace EqualityPlan

variable {D : Type} [Domain D]

/- Combine two equality plans. -/
private def append :
    EqualityPlan D → EqualityPlan D → EqualityPlan D
| .empty, _ => .empty
| _, .empty => .empty
| .sels sels₁, .sels sels₂ => .sels (sels₁ ++ sels₂)

end EqualityPlan

/- Apply selections to a raw RA expression. -/
private def applySelections
    (sels : List (Sel D))
    (e : RawRAExpr A D) :
    RawRAExpr A D :=
  match sels with
  | [] => e
  | φ :: sels =>
      applySelections sels (.select φ e)

/- Applying selections preserves raw SPJ membership. -/
private theorem applySelections_isSPJ
    (sels : List (Sel D))
    {e : RawRAExpr A D}
    (h : e.IsSPJ) :
    (applySelections sels e).IsSPJ := by
  induction sels generalizing e with
  | nil =>
      simpa [applySelections] using h
  | cons φ sels ih =>
      apply ih
      simpa [RawRAExpr.IsSPJ] using h

/- Applying bounded selections preserves raw arity. -/
private theorem applySelections_arity
    (sels : List (Sel D))
    {Γ : UnnamedSchema A}
    {e : RawRAExpr A D}
    {n : Nat}
    (hE : e.arity? Γ = some n)
    (hSels : ∀ φ, φ ∈ sels → φ.arityReq < n) :
    (applySelections sels e).arity? Γ = some n := by
  induction sels generalizing e with
  | nil =>
      simpa [applySelections] using hE
  | cons φ sels ih =>
      have hφ : φ.arityReq < n :=
        hSels φ (by simp)
      have hSel :
          (RawRAExpr.select φ e).arity? Γ = some n := by
        simp [RawRAExpr.arity?, hE, hφ]
      have hTail :
          ∀ ψ, ψ ∈ sels → ψ.arityReq < n := by
        intro ψ hψ
        exact hSels ψ (by simp [hψ])
      simpa [applySelections] using
        ih hSel hTail

/- Answer characterization for applied selections. -/
private theorem applySelections_answer_iff
    (sels : List (Sel D))
    {Γ : UnnamedSchema A}
    {I : Instance D Γ}
    {e : RawRAExpr A D}
    {n : Nat}
    (hE : e.arity? Γ = some n)
    (hSels : ∀ φ, φ ∈ sels → φ.arityReq < n)
    (t : Tuple D n) :
    (applySelections sels e).answerContains I t ↔
      e.answerContains I t ∧
        ∀ φ, φ ∈ sels → Sel.Holds φ t := by
  induction sels generalizing e with
  | nil =>
      simp [applySelections]
  | cons φ sels ih =>
      have hφ : φ.arityReq < n :=
        hSels φ (by simp)
      have hSelAr :
          (RawRAExpr.select φ e).arity? Γ = some n := by
        simp [RawRAExpr.arity?, hE, hφ]
      have hTail :
          ∀ ψ, ψ ∈ sels → ψ.arityReq < n := by
        intro ψ hψ
        exact hSels ψ (by simp [hψ])
      rw [applySelections]
      rw [ih hSelAr hTail]
      rw [RawRAExpr.answer_select_iff hE hφ t]
      constructor
      · intro h
        rcases h with ⟨⟨hAns, hφSat⟩, hAllTail⟩
        refine ⟨hAns, ?_⟩
        intro ψ hψ
        rcases List.mem_cons.mp hψ with hHead | hTailMem
        · cases hHead
          exact hφSat
        · exact hAllTail ψ hTailMem
      · intro h
        rcases h with ⟨hAns, hAll⟩
        exact
          ⟨⟨hAns, hAll φ (by simp)⟩,
            by
              intro ψ hψ
              exact hAll ψ (by simp [hψ])⟩

variable {Γ : UnnamedSchema A}

end RAConsequence

end Datalog

------------------------------------------------------------
-- Rule And Body Translation Support
------------------------------------------------------------

namespace Datalog

namespace RAConsequence

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- First-match lookup in a variable-position environment. -/
private def lookupVarPos
    (env : List (Var × Nat))
    (x : Var) :
    Option Nat :=
  match env with
  | [] => none
  | (y, p) :: env =>
      if x = y then
        some p
      else
        lookupVarPos env x

/-
  Selections and first-position environment from entries.
-/
private def collectSelectionsAndEnv
    (es : List (Nat × RelTerm D))
    (env : List (Var × Nat) := []) :
    List (Sel D) × List (Var × Nat) :=
  match es with
  | [] => ([], env)
  | (p, t) :: es =>
      match t with
      | .const c =>
          let (sels, env') := collectSelectionsAndEnv es env
          (.eqConst p c :: sels, env')
      | .var x =>
          match lookupVarPos env x with
          | some q =>
              let (sels, env') :=
                collectSelectionsAndEnv es env
              (.eqIdx q p :: sels, env')
          | none =>
              collectSelectionsAndEnv es ((x, p) :: env)

/-
  Equality selections either succeed or make the body empty.
-/
private def termEqualityPlan
    (env : List (Var × Nat)) :
    RelTerm D → RelTerm D → EqualityPlan D
| .var x, .var y =>
    match lookupVarPos env x, lookupVarPos env y with
    | some i, some j => .sels [.eqIdx i j]
    | _, _ => .empty
| .var x, .const c =>
    match lookupVarPos env x with
    | some i => .sels [.eqConst i c]
    | none => .empty
| .const c, .var x =>
    match lookupVarPos env x with
    | some i => .sels [.eqConst i c]
    | none => .empty
| .const c, .const d =>
    if c = d then
      .sels []
    else
      .empty

/- Equality selections for all equality atoms in a body. -/
private def bodyEqualityPlan
    (env : List (Var × Nat)) :
    List (Atom D Γ) → EqualityPlan D
| [] => .sels []
| .rel _ :: body => bodyEqualityPlan env body
| .eq lhs rhs :: body =>
    EqualityPlan.append
      (termEqualityPlan env lhs rhs)
      (bodyEqualityPlan env body)

/- Tuple coordinate with a default outside the arity. -/
private def tupleCol
    {n : Nat}
    (t : Tuple D n)
    (i : Nat) : D :=
  match t.toList[i]? with
  | some d => d
  | none => default

private theorem tupleCol_eq_get_of_lt
    {n : Nat}
    (t : Tuple D n)
    (i : Nat)
    (hi : i < n) :
    tupleCol t i = t.get ⟨i, hi⟩ := by
  unfold tupleCol
  have hiList : i < t.toList.length := by
    simpa [Vector.length_toList] using hi
  have hGet? :
      t.toList[i]? = some t.toList[i] :=
    List.getElem?_eq_getElem hiList
  have hGet : t.toList[i] = t.get ⟨i, hi⟩ := by
    have hVec : t.toList[i] = t[i] :=
      Vector.getElem_toList hiList
    have hIdx : t[i] = t.get ⟨i, hi⟩ := rfl
    exact hVec.trans hIdx
  simp [hGet?, hGet]

private theorem holds_eqIdx_of_tupleCol_eq
    {n : Nat}
    (t : Tuple D n)
    {i j : Nat}
    (hi : i < n)
    (hj : j < n)
    (hij : tupleCol t i = tupleCol t j) :
    Sel.Holds (.eqIdx i j) t := by
  rw [Sel.holds_eqIdx_iff t hi hj]
  rw [tupleCol_eq_get_of_lt t i hi,
    tupleCol_eq_get_of_lt t j hj] at hij
  exact hij

private theorem holds_eqConst_of_tupleCol_eq
    {n : Nat}
    (t : Tuple D n)
    {i : Nat}
    {c : D}
    (hi : i < n)
    (hic : tupleCol t i = c) :
    Sel.Holds (.eqConst i c) t := by
  rw [Sel.holds_eqConst_iff t hi]
  rw [tupleCol_eq_get_of_lt t i hi] at hic
  exact hic

private theorem tupleCol_eq_of_holds_eqIdx
    {n : Nat}
    (t : Tuple D n)
    {i j : Nat}
    (hi : i < n)
    (hj : j < n)
    (hSel : Sel.Holds (.eqIdx i j) t) :
    tupleCol t i = tupleCol t j := by
  have hGet := (Sel.holds_eqIdx_iff t hi hj).1 hSel
  rw [tupleCol_eq_get_of_lt t i hi,
    tupleCol_eq_get_of_lt t j hj]
  exact hGet

private theorem tupleCol_eq_of_holds_eqConst
    {n : Nat}
    (t : Tuple D n)
    {i : Nat}
    {c : D}
    (hi : i < n)
    (hSel : Sel.Holds (.eqConst i c) t) :
    tupleCol t i = c := by
  have hGet := (Sel.holds_eqConst_iff t hi).1 hSel
  rw [tupleCol_eq_get_of_lt t i hi]
  exact hGet

omit [Domain D] in
private theorem castArity_toList
    {m n : Nat}
    (h : m = n)
    (t : Tuple D n) :
    (Tuple.castArity h t).toList = t.toList := by
  cases h
  rfl

omit [Domain D] in
private theorem castArity_symm_castArity
    {m n : Nat}
    (h : m = n)
    (t : Tuple D n) :
    Tuple.castArity h.symm (Tuple.castArity h t) = t := by
  cases h
  rfl

omit [Domain D] in
private theorem mem_cast_finRelation
    {m n : Nat}
    (h : m = n)
    (R : FinRelation D m)
    (t : Tuple D n) :
    t ∈ (cast (by cases h; rfl) R : FinRelation D n) ↔
      Tuple.castArity h t ∈ R := by
  cases h
  exact Iff.rfl

private theorem projTuple_toList_eq_map_tupleCol
    {n : Nat}
    (idxs : List Nat)
    (u : Tuple D n)
    (hIdx : ∀ i, i ∈ idxs → i < n) :
    (FinRelation.projTuple idxs u hIdx).toList =
      idxs.map (tupleCol u) := by
  apply List.ext_get
  · simp [Vector.length_toList]
  · intro i hiLeft hiRight
    have hiIdx : i < idxs.length := by
      simpa [Vector.length_toList] using hiLeft
    have hProjGet :
        (FinRelation.projTuple idxs u hIdx).toList[i] =
          (FinRelation.projTuple idxs u hIdx).get
            ⟨i, hiIdx⟩ := by
      exact Vector.getElem_toList hiLeft
    have hMapGet :
        (idxs.map (tupleCol u))[i] =
          tupleCol u idxs[i] := by
      simp [List.getElem_map]
    have hProjCoord :=
      FinRelation.projTuple_get idxs u hIdx ⟨i, hiIdx⟩
    calc
      (FinRelation.projTuple idxs u hIdx).toList[i]
          = (FinRelation.projTuple idxs u hIdx).get
              ⟨i, hiIdx⟩ := hProjGet
      _ = u.get
            ⟨idxs[i],
              hIdx idxs[i]
                (List.get_mem idxs ⟨i, hiIdx⟩)⟩ :=
            hProjCoord
      _ = tupleCol u idxs[i] := by
            symm
            exact tupleCol_eq_get_of_lt
              u idxs[i]
              (hIdx idxs[i]
                (List.get_mem idxs ⟨i, hiIdx⟩))
      _ = (idxs.map (tupleCol u))[i] := hMapGet.symm

/- Assignment induced by first variable positions. -/
private def valuationOfEnv
    {n : Nat}
    (u : Tuple D n)
    (env : List (Var × Nat)) :
    Assign D :=
  fun x =>
    match lookupVarPos env x with
    | some p => tupleCol u p
    | none => default

private theorem valuationOfEnv_lookup
    {n : Nat}
    (u : Tuple D n)
    (env : List (Var × Nat))
    (x : Var)
    (p : Nat)
    (hLookup : lookupVarPos env x = some p) :
    valuationOfEnv u env x = tupleCol u p := by
  simp [valuationOfEnv, hLookup]

private theorem lookupVarPos_some_mem
    {env : List (Var × Nat)}
    {x p : Nat}
    (h : lookupVarPos env x = some p) :
    (x, p) ∈ env := by
  induction env with
  | nil =>
      simp [lookupVarPos] at h
  | cons yp env ih =>
      rcases yp with ⟨y, q⟩
      by_cases hxy : x = y
      · have hSome : some q = some p := by
          simpa [lookupVarPos, hxy] using h
        cases hSome
        simp [hxy]
      · have hTail : lookupVarPos env x = some p := by
          simpa [lookupVarPos, hxy] using h
        exact List.mem_cons_of_mem _ (ih hTail)

private theorem lookupVarPos_isSome_of_mem
    {env : List (Var × Nat)}
    {x p : Nat}
    (hmem : (x, p) ∈ env) :
    (lookupVarPos env x).isSome = true := by
  induction env with
  | nil =>
      cases hmem
  | cons yp env ih =>
      rcases yp with ⟨y, q⟩
      rcases List.mem_cons.mp hmem with hHead | hTail
      · cases hHead
        simp [lookupVarPos]
      · by_cases hxy : x = y
        · simp [lookupVarPos, hxy]
        · simpa [lookupVarPos, hxy] using ih hTail

private theorem lookupVarPos_lt_of_env_bounds
    {env : List (Var × Nat)}
    {x p N : Nat}
    (hEnv : ∀ y q, (y, q) ∈ env → q < N)
    (hLookup : lookupVarPos env x = some p) :
    p < N :=
  hEnv x p (lookupVarPos_some_mem hLookup)

private theorem collectSelectionsAndEnv_bounds
    (es : List (Nat × RelTerm D))
    (env : List (Var × Nat))
    (N : Nat)
    (hEs : ∀ p t, (p, t) ∈ es → p < N)
    (hEnv : ∀ x p, (x, p) ∈ env → p < N) :
    (∀ φ, φ ∈ (collectSelectionsAndEnv es env).1 →
        φ.arityReq < N) ∧
      (∀ x p,
        (x, p) ∈ (collectSelectionsAndEnv es env).2 →
        p < N) := by
  induction es generalizing env with
  | nil =>
      constructor
      · intro φ hφ
        simp [collectSelectionsAndEnv] at hφ
      · intro x p hmem
        exact hEnv x p
          (by simpa [collectSelectionsAndEnv] using hmem)
  | cons e es ih =>
      rcases e with ⟨p, t⟩
      have hp : p < N := hEs p t (by simp)
      have hEsTail :
          ∀ p' t', (p', t') ∈ es → p' < N := by
        intro p' t' hmem
        exact hEs p' t' (by simp [hmem])
      cases t with
      | const c =>
          have hIH := ih (env := env) hEsTail hEnv
          rcases hIH with ⟨hSelIH, hEnvIH⟩
          constructor
          · intro φ hφ
            have hφ' :
                φ = Sel.eqConst p c ∨
                  φ ∈
                    (collectSelectionsAndEnv es env).1 := by
              simpa [collectSelectionsAndEnv] using hφ
            rcases hφ' with rfl | hTail
            · simpa [Sel.arityReq] using hp
            · exact hSelIH φ hTail
          · intro x q hmem
            have hmem' :
                (x, q) ∈
                  (collectSelectionsAndEnv es env).2 := by
              simpa [collectSelectionsAndEnv] using hmem
            exact hEnvIH x q hmem'
      | var x =>
          cases hLookup : lookupVarPos env x with
          | none =>
              have hEnvCons :
                  ∀ y q,
                    (y, q) ∈ (x, p) :: env → q < N := by
                intro y q hmem
                have hmemOr := List.mem_cons.mp hmem
                rcases hmemOr with hHead | hTail
                · cases hHead
                  exact hp
                · exact hEnv y q hTail
              simpa [collectSelectionsAndEnv, hLookup] using
                ih (env := (x, p) :: env) hEsTail hEnvCons
          | some q =>
              have hq : q < N :=
                lookupVarPos_lt_of_env_bounds hEnv hLookup
              have hIH := ih (env := env) hEsTail hEnv
              rcases hIH with ⟨hSelIH, hEnvIH⟩
              constructor
              · intro φ hφ
                have hφ' :
                    φ = Sel.eqIdx q p ∨
                      φ ∈
                        (collectSelectionsAndEnv es env).1
                        :=
                    by
                  simpa [collectSelectionsAndEnv, hLookup]
                    using hφ
                rcases hφ' with rfl | hTail
                · have hMax : Nat.max q p < N :=
                    max_lt_iff.mpr ⟨hq, hp⟩
                  simpa [Sel.arityReq] using hMax
                · exact hSelIH φ hTail
              · intro x' q' hmem
                have hmem' :
                    (x', q') ∈
                      (collectSelectionsAndEnv es env).2 :=
                    by
                  simpa [collectSelectionsAndEnv, hLookup]
                    using hmem
                exact hEnvIH x' q' hmem'

private theorem collectSelectionsAndEnv_env_mem_of_var_mem_or_env
    (es : List (Nat × RelTerm D))
    (env : List (Var × Nat))
    (x : Var)
    (h :
      (∃ p : Nat, (p, RelTerm.var x) ∈ es) ∨
        (∃ q : Nat, (x, q) ∈ env)) :
    ∃ q : Nat,
      (x, q) ∈ (collectSelectionsAndEnv es env).2 := by
  induction es generalizing env with
  | nil =>
      rcases h with hEs | hEnv
      · rcases hEs with ⟨p, hp⟩
        cases hp
      · rcases hEnv with ⟨q, hq⟩
        exact ⟨q, by
          simpa [collectSelectionsAndEnv] using hq⟩
  | cons e es ih =>
      rcases e with ⟨p, t⟩
      cases t with
      | const c =>
          have h' :
              (∃ p : Nat, (p, RelTerm.var x) ∈ es) ∨
                (∃ q : Nat, (x, q) ∈ env) := by
            rcases h with hEs | hEnv
            · rcases hEs with ⟨p', hp'⟩
              rcases List.mem_cons.mp hp' with hHead | hTail
              · cases hHead
              · exact Or.inl ⟨p', hTail⟩
            · exact Or.inr hEnv
          simpa [collectSelectionsAndEnv] using
            ih (env := env) h'
      | var y =>
          cases hLookup : lookupVarPos env y with
          | some qy =>
              have h' :
                  (∃ p : Nat, (p, RelTerm.var x) ∈ es) ∨
                    (∃ q : Nat, (x, q) ∈ env) := by
                rcases h with hEs | hEnv
                · rcases hEs with ⟨p', hp'⟩
                  have hpOr := List.mem_cons.mp hp'
                  rcases hpOr with hHead | hTail
                  · have hxy : x = y := by
                      injection hHead with _ hTerm
                      exact RelTerm.var.inj hTerm
                    have hyEnv : (y, qy) ∈ env :=
                      lookupVarPos_some_mem hLookup
                    exact Or.inr
                      ⟨qy, by simpa [hxy] using hyEnv⟩
                  · exact Or.inl ⟨p', hTail⟩
                · exact Or.inr hEnv
              simpa [collectSelectionsAndEnv, hLookup] using
                ih (env := env) h'
          | none =>
              let env' : List (Var × Nat) := (y, p) :: env
              have h' :
                  (∃ p : Nat, (p, RelTerm.var x) ∈ es) ∨
                    (∃ q : Nat, (x, q) ∈ env') := by
                rcases h with hEs | hEnv
                · rcases hEs with ⟨p', hp'⟩
                  have hpOr := List.mem_cons.mp hp'
                  rcases hpOr with hHead | hTail
                  · have hxy : x = y := by
                      injection hHead with _ hTerm
                      exact RelTerm.var.inj hTerm
                    exact Or.inr ⟨p, by
                      subst hxy
                      simp [env']⟩
                  · exact Or.inl ⟨p', hTail⟩
                · rcases hEnv with ⟨q, hq⟩
                  exact Or.inr ⟨q, by
                    simp [env', hq]⟩
              simpa [collectSelectionsAndEnv, hLookup, env']
                using ih (env := env') h'

private theorem collectSelectionsAndEnv_lookup_isSome
    (es : List (Nat × RelTerm D))
    (env : List (Var × Nat))
    (x : Var)
    (h :
      (∃ p : Nat, (p, RelTerm.var x) ∈ es) ∨
        (∃ q : Nat, (x, q) ∈ env)) :
    (lookupVarPos
      (collectSelectionsAndEnv es env).2 x).isSome =
        true := by
  rcases
    collectSelectionsAndEnv_env_mem_of_var_mem_or_env
      es env x h with
    ⟨q, hq⟩
  exact lookupVarPos_isSome_of_mem hq

private theorem collectSelectionsAndEnv_sound
    (es : List (Nat × RelTerm D))
    (env : List (Var × Nat))
    (σ : Assign D)
    (f : Nat → D)
    (hEs :
      ∀ p t, (p, t) ∈ es → f p = t.eval σ)
    (hEnv :
      ∀ x p, (x, p) ∈ env → f p = σ x) :
    (∀ φ,
        φ ∈ (collectSelectionsAndEnv es env).1 →
        match φ with
        | .eqIdx i j => f i = f j
        | .eqConst i c => f i = c
        | _ => False) ∧
      (∀ x p,
        (x, p) ∈ (collectSelectionsAndEnv es env).2 →
        f p = σ x) := by
  induction es generalizing env with
  | nil =>
      constructor
      · intro φ hφ
        simp [collectSelectionsAndEnv] at hφ
      · intro x p hmem
        exact hEnv x p
          (by simpa [collectSelectionsAndEnv] using hmem)
  | cons e es ih =>
      rcases e with ⟨p, t⟩
      have hEsTail :
          ∀ p' t',
            (p', t') ∈ es → f p' = t'.eval σ := by
        intro p' t' hmem
        exact hEs p' t' (by simp [hmem])
      cases t with
      | const c =>
          have hIH := ih (env := env) hEsTail hEnv
          rcases hIH with ⟨hSelIH, hEnvIH⟩
          constructor
          · intro φ hφ
            have hφ' :
                φ = Sel.eqConst p c ∨
                  φ ∈
                    (collectSelectionsAndEnv es env).1 := by
              simpa [collectSelectionsAndEnv] using hφ
            rcases hφ' with rfl | hTail
            · simpa [RelTerm.eval] using
                hEs p (.const c) (by simp)
            · exact hSelIH φ hTail
          · intro x q hmem
            have hmem' :
                (x, q) ∈
                  (collectSelectionsAndEnv es env).2 := by
              simpa [collectSelectionsAndEnv] using hmem
            exact hEnvIH x q hmem'
      | var x =>
          cases hLookup : lookupVarPos env x with
          | none =>
              have hEnvCons :
                  ∀ y q,
                    (y, q) ∈ (x, p) :: env →
                      f q = σ y := by
                intro y q hmem
                have hmemOr := List.mem_cons.mp hmem
                rcases hmemOr with hHead | hTail
                · cases hHead
                  simpa [RelTerm.eval] using
                    hEs p (.var x) (by simp)
                · exact hEnv y q hTail
              simpa [collectSelectionsAndEnv, hLookup] using
                ih (env := (x, p) :: env) hEsTail hEnvCons
          | some q =>
              have hq : f q = σ x :=
                hEnv x q (lookupVarPos_some_mem hLookup)
              have hp : f p = σ x := by
                simpa [RelTerm.eval] using
                  hEs p (.var x) (by simp)
              have hIH := ih (env := env) hEsTail hEnv
              rcases hIH with ⟨hSelIH, hEnvIH⟩
              constructor
              · intro φ hφ
                have hφ' :
                    φ = Sel.eqIdx q p ∨
                      φ ∈
                        (collectSelectionsAndEnv es env).1
                    := by
                  simpa [collectSelectionsAndEnv, hLookup]
                    using hφ
                rcases hφ' with rfl | hTail
                · exact hq.trans hp.symm
                · exact hSelIH φ hTail
              · intro x' q' hmem
                have hmem' :
                    (x', q') ∈
                      (collectSelectionsAndEnv es env).2 :=
                    by
                  simpa [collectSelectionsAndEnv, hLookup]
                    using hmem
                exact hEnvIH x' q' hmem'

private theorem lookupVarPos_preserved_collect_some
    (es : List (Nat × RelTerm D))
    (env : List (Var × Nat))
    (x q : Nat)
    (hLookup : lookupVarPos env x = some q) :
    lookupVarPos (collectSelectionsAndEnv es env).2 x =
      some q := by
  induction es generalizing env with
  | nil =>
      simpa [collectSelectionsAndEnv] using hLookup
  | cons e es ih =>
      rcases e with ⟨p, t⟩
      cases t with
      | const c =>
          simpa [collectSelectionsAndEnv] using
            ih (env := env) hLookup
      | var y =>
          cases hLy : lookupVarPos env y with
          | some qy =>
              simpa [collectSelectionsAndEnv, hLy] using
                ih (env := env) hLookup
          | none =>
              have hxy : x ≠ y := by
                intro hEq
                subst hEq
                simp [hLookup] at hLy
              have hLookup' :
                  lookupVarPos ((y, p) :: env) x =
                    some q := by
                simp [lookupVarPos, hxy, hLookup]
              simpa [collectSelectionsAndEnv, hLy] using
                ih (env := (y, p) :: env) hLookup'

private theorem collectSelectionsAndEnv_entry_info
    (es : List (Nat × RelTerm D))
    (env : List (Var × Nat)) :
    ∀ p t, (p, t) ∈ es →
      match t with
      | .const c =>
          Sel.eqConst p c ∈
            (collectSelectionsAndEnv es env).1
      | .var x =>
          ∃ q,
            lookupVarPos
              (collectSelectionsAndEnv es env).2 x =
                some q ∧
              (q = p ∨
                Sel.eqIdx q p ∈
                  (collectSelectionsAndEnv es env).1) := by
  induction es generalizing env with
  | nil =>
      intro p t hmem
      cases hmem
  | cons e es ih =>
      rcases e with ⟨p0, t0⟩
      intro p t hmem
      rcases List.mem_cons.mp hmem with hHead | hTail
      · cases hHead
        cases t0 with
        | const c =>
            simp [collectSelectionsAndEnv]
        | var y =>
            cases hLy : lookupVarPos env y with
            | some qy =>
                refine ⟨qy, ?_, ?_⟩
                · simpa [collectSelectionsAndEnv,
                    hLy] using
                    lookupVarPos_preserved_collect_some
                      (es := es) (env := env)
                      (x := y) (q := qy) hLy
                · right
                  simp [collectSelectionsAndEnv, hLy]
            | none =>
                have hLookup' :
                    lookupVarPos ((y, p0) :: env) y =
                      some p0 := by
                  simp [lookupVarPos]
                refine ⟨p0, ?_, ?_⟩
                · simpa [collectSelectionsAndEnv,
                    hLy] using
                    lookupVarPos_preserved_collect_some
                      (es := es) (env := (y, p0) :: env)
                      (x := y) (q := p0) hLookup'
                · left
                  rfl
      · cases t0 with
        | const c =>
            cases t with
            | const c' =>
                have hIH :=
                  ih (env := env) p (.const c') hTail
                simp [collectSelectionsAndEnv, hIH]
            | var x =>
                have hIH := ih (env := env) p (.var x) hTail
                simpa [collectSelectionsAndEnv] using hIH
        | var y =>
            cases hLy : lookupVarPos env y with
            | some qy =>
                cases t with
                | const c' =>
                    have hIH :=
                      ih (env := env) p (.const c') hTail
                    simpa [collectSelectionsAndEnv,
                      hLy] using hIH
                | var x =>
                    have hIH :=
                      ih (env := env) p (.var x) hTail
                    rcases hIH with ⟨q, hq, hqSel⟩
                    refine ⟨q, ?_, ?_⟩
                    · simpa [collectSelectionsAndEnv,
                        hLy] using hq
                    · rcases hqSel with hEq | hSel
                      · exact Or.inl hEq
                      · exact Or.inr (by
                          simp [collectSelectionsAndEnv,
                            hLy, hSel])
            | none =>
                have hIH :=
                  ih (env := (y, p0) :: env) p t hTail
                simpa [collectSelectionsAndEnv,
                  hLy] using hIH

private theorem termEqualityPlan_sels_bounds
    (env : List (Var × Nat))
    {N : Nat}
    (hEnv : ∀ x p, (x, p) ∈ env → p < N)
    (lhs rhs : RelTerm D)
    {sels : List (Sel D)}
    (hPlan : termEqualityPlan env lhs rhs = .sels sels) :
    ∀ φ, φ ∈ sels → φ.arityReq < N := by
  cases lhs with
  | var x =>
      cases rhs with
      | var y =>
          cases hx : lookupVarPos env x with
          | none =>
              simp only [termEqualityPlan, hx] at hPlan
              cases hPlan
          | some i =>
              cases hy : lookupVarPos env y with
              | none =>
                  simp only [termEqualityPlan, hx,
                    hy] at hPlan
                  cases hPlan
              | some j =>
                  simp only [termEqualityPlan, hx,
                    hy] at hPlan
                  cases hPlan
                  intro φ hφ
                  have hφ' : φ = Sel.eqIdx i j := by
                    simpa using hφ
                  subst hφ'
                  have hilt :
                      i < N :=
                    lookupVarPos_lt_of_env_bounds hEnv hx
                  have hjlt :
                      j < N :=
                    lookupVarPos_lt_of_env_bounds hEnv hy
                  simpa [Sel.arityReq] using
                    (max_lt_iff.mpr ⟨hilt, hjlt⟩)
      | const c =>
          cases hx : lookupVarPos env x with
          | none =>
              simp only [termEqualityPlan, hx] at hPlan
              cases hPlan
          | some i =>
              simp only [termEqualityPlan, hx] at hPlan
              cases hPlan
              intro φ hφ
              have hφ' : φ = Sel.eqConst i c := by
                simpa using hφ
              subst hφ'
              exact lookupVarPos_lt_of_env_bounds hEnv hx
  | const c =>
      cases rhs with
      | var x =>
          cases hx : lookupVarPos env x with
          | none =>
              simp only [termEqualityPlan, hx] at hPlan
              cases hPlan
          | some i =>
              simp only [termEqualityPlan, hx] at hPlan
              cases hPlan
              intro φ hφ
              have hφ' : φ = Sel.eqConst i c := by
                simpa using hφ
              subst hφ'
              exact lookupVarPos_lt_of_env_bounds hEnv hx
      | const d =>
          by_cases hcd : c = d
          · simp only [termEqualityPlan, hcd,
              ↓reduceIte] at hPlan
            cases hPlan
            intro φ hφ
            cases hφ
          · simp only [termEqualityPlan, hcd,
              ↓reduceIte] at hPlan
            cases hPlan

private theorem bodyEqualityPlan_sels_bounds
    (env : List (Var × Nat))
    {N : Nat}
    (hEnv : ∀ x p, (x, p) ∈ env → p < N) :
    (body : List (Atom D Γ)) →
      {sels : List (Sel D)} →
      bodyEqualityPlan env body = .sels sels →
      ∀ φ, φ ∈ sels → φ.arityReq < N
| [], sels, hPlan => by
    simp only [bodyEqualityPlan] at hPlan
    cases hPlan
    intro φ hφ
    cases hφ
| .rel _ :: body, sels, hPlan =>
    bodyEqualityPlan_sels_bounds env hEnv body hPlan
| .eq lhs rhs :: body, sels, hPlan => by
    cases hEq : termEqualityPlan env lhs rhs with
    | empty =>
        simp only [bodyEqualityPlan, hEq,
          EqualityPlan.append] at hPlan
        cases hPlan
    | sels eqSels₁ =>
        cases hRest : bodyEqualityPlan env body with
        | empty =>
            simp only [bodyEqualityPlan, hEq, hRest,
              EqualityPlan.append] at hPlan
            cases hPlan
        | sels eqSels₂ =>
            simp only [bodyEqualityPlan, hEq, hRest,
              EqualityPlan.append] at hPlan
            cases hPlan
            intro φ hφ
            have hφOr := List.mem_append.mp hφ
            rcases hφOr with hLeft | hRight
            · exact
                termEqualityPlan_sels_bounds
                  env hEnv lhs rhs hEq φ hLeft
            · exact
                bodyEqualityPlan_sels_bounds
                  env hEnv body hRest φ hRight

private theorem termEqualityPlan_sat_of_holds
    {n : Nat}
    (env : List (Var × Nat))
    (hEnv : ∀ x p, (x, p) ∈ env → p < n)
    (u : Tuple D n)
    (lhs rhs : RelTerm D)
    {sels : List (Sel D)}
    (hPlan : termEqualityPlan env lhs rhs = .sels sels)
    (hHolds : ∀ φ, φ ∈ sels → Sel.Holds φ u) :
    lhs.eval (valuationOfEnv u env) =
      rhs.eval (valuationOfEnv u env) := by
  cases lhs with
  | var x =>
      cases rhs with
      | var y =>
          cases hx : lookupVarPos env x with
          | none =>
              simp only [termEqualityPlan, hx] at hPlan
              cases hPlan
          | some i =>
              cases hy : lookupVarPos env y with
              | none =>
                  simp only [termEqualityPlan, hx,
                    hy] at hPlan
                  cases hPlan
              | some j =>
                  simp only [termEqualityPlan, hx,
                    hy] at hPlan
                  cases hPlan
                  have hSel :
                      Sel.Holds (.eqIdx i j) u :=
                    hHolds (.eqIdx i j) (by simp)
                  have hi : i < n :=
                    lookupVarPos_lt_of_env_bounds hEnv hx
                  have hj : j < n :=
                    lookupVarPos_lt_of_env_bounds hEnv hy
                  have hij :
                      tupleCol u i = tupleCol u j :=
                    tupleCol_eq_of_holds_eqIdx u hi hj hSel
                  simpa [RelTerm.eval,
                    valuationOfEnv_lookup u env x i hx,
                    valuationOfEnv_lookup u env y j hy]
                    using hij
      | const c =>
          cases hx : lookupVarPos env x with
          | none =>
              simp only [termEqualityPlan, hx] at hPlan
              cases hPlan
          | some i =>
              simp only [termEqualityPlan, hx] at hPlan
              cases hPlan
              have hSel :
                  Sel.Holds (.eqConst i c) u :=
                hHolds (.eqConst i c) (by simp)
              have hi : i < n :=
                lookupVarPos_lt_of_env_bounds hEnv hx
              have hic : tupleCol u i = c :=
                tupleCol_eq_of_holds_eqConst u hi hSel
              simpa [RelTerm.eval,
                valuationOfEnv_lookup u env x i hx]
                using hic
  | const c =>
      cases rhs with
      | var x =>
          cases hx : lookupVarPos env x with
          | none =>
              simp only [termEqualityPlan, hx] at hPlan
              cases hPlan
          | some i =>
              simp only [termEqualityPlan, hx] at hPlan
              cases hPlan
              have hSel :
                  Sel.Holds (.eqConst i c) u :=
                hHolds (.eqConst i c) (by simp)
              have hi : i < n :=
                lookupVarPos_lt_of_env_bounds hEnv hx
              have hic : tupleCol u i = c :=
                tupleCol_eq_of_holds_eqConst u hi hSel
              simpa [RelTerm.eval,
                valuationOfEnv_lookup u env x i hx]
                using hic.symm
      | const d =>
          by_cases hcd : c = d
          · simp only [termEqualityPlan, hcd,
              ↓reduceIte] at hPlan
            cases hPlan
            simp [RelTerm.eval, hcd]
          · simp only [termEqualityPlan, hcd,
              ↓reduceIte] at hPlan
            cases hPlan

private theorem termEqualityPlan_holds_of_sat
    {n : Nat}
    (env : List (Var × Nat))
    (hEnv : ∀ x p, (x, p) ∈ env → p < n)
    (u : Tuple D n)
    (σ : Assign D)
    (lhs rhs : RelTerm D)
    (hLookup :
      ∀ x,
        x ∈ [lhs, rhs].filterMap RelTerm.var? →
          ∃ p, lookupVarPos env x = some p ∧
            tupleCol u p = σ x)
    (hSat : lhs.eval σ = rhs.eval σ) :
    ∃ sels,
      termEqualityPlan env lhs rhs = .sels sels ∧
        ∀ φ, φ ∈ sels → Sel.Holds φ u := by
  cases lhs with
  | var x =>
      cases rhs with
      | var y =>
          rcases hLookup x (by simp [RelTerm.var?]) with
            ⟨i, hi, hix⟩
          rcases hLookup y (by simp [RelTerm.var?]) with
            ⟨j, hj, hjy⟩
          refine ⟨[.eqIdx i j], ?_, ?_⟩
          · simp [termEqualityPlan, hi, hj]
          · intro φ hφ
            have hφ' : φ = Sel.eqIdx i j := by
              simpa using hφ
            subst hφ'
            have hiLt : i < n :=
              lookupVarPos_lt_of_env_bounds hEnv hi
            have hjLt : j < n :=
              lookupVarPos_lt_of_env_bounds hEnv hj
            have hij :
                tupleCol u i = tupleCol u j := by
              simpa [RelTerm.eval, hix, hjy] using hSat
            exact holds_eqIdx_of_tupleCol_eq u hiLt hjLt hij
      | const c =>
          rcases hLookup x (by simp [RelTerm.var?]) with
            ⟨i, hi, hix⟩
          refine ⟨[.eqConst i c], ?_, ?_⟩
          · simp [termEqualityPlan, hi]
          · intro φ hφ
            have hφ' : φ = Sel.eqConst i c := by
              simpa using hφ
            subst hφ'
            have hiLt : i < n :=
              lookupVarPos_lt_of_env_bounds hEnv hi
            have hic : tupleCol u i = c := by
              simpa [RelTerm.eval, hix] using hSat
            exact holds_eqConst_of_tupleCol_eq u hiLt hic
  | const c =>
      cases rhs with
      | var x =>
          rcases hLookup x (by simp [RelTerm.var?]) with
            ⟨i, hi, hix⟩
          refine ⟨[.eqConst i c], ?_, ?_⟩
          · simp [termEqualityPlan, hi]
          · intro φ hφ
            have hφ' : φ = Sel.eqConst i c := by
              simpa using hφ
            subst hφ'
            have hiLt : i < n :=
              lookupVarPos_lt_of_env_bounds hEnv hi
            have hic : tupleCol u i = c := by
              simpa [RelTerm.eval, hix] using hSat.symm
            exact holds_eqConst_of_tupleCol_eq u hiLt hic
      | const d =>
          have hcd : c = d := by
            simpa [RelTerm.eval] using hSat
          refine ⟨[], ?_, ?_⟩
          · simp [termEqualityPlan, hcd]
          · intro φ hφ
            cases hφ

end RAConsequence

namespace Body

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Relational body terms in product-column order. -/
private def relTerms : List (Atom D Γ) → List (RelTerm D)
| [] => []
| .rel a :: body => a.args.toList ++ relTerms body
| .eq _ _ :: body => relTerms body

/- Relational body terms paired with product positions. -/
private def entries
    (body : List (Atom D Γ)) :
    List (Nat × RelTerm D) :=
  (Body.relTerms body).mapIdx (fun i t => (i, t))

/- Selections and first-position environment for a body. -/
private def selectionEnv
    (body : List (Atom D Γ)) :
    List (Sel D) × List (Var × Nat) :=
  RAConsequence.collectSelectionsAndEnv (Body.entries body)

/- Selections generated by relational body terms. -/
private def relSelections
    (body : List (Atom D Γ)) :
    List (Sel D) :=
  (Body.selectionEnv body).1

/- First product position for each relational variable. -/
private def relEnv
    (body : List (Atom D Γ)) :
    List (Var × Nat) :=
  (Body.selectionEnv body).2

/- Equality selections generated by equality atoms. -/
private def equalityPlan
    (body : List (Atom D Γ)) :
    RAConsequence.EqualityPlan D :=
  RAConsequence.bodyEqualityPlan (Body.relEnv body) body

/- All selections generated by the body, unless empty. -/
private def allSelectionsPlan
    (body : List (Atom D Γ)) :
    RAConsequence.EqualityPlan D :=
  match Body.equalityPlan body with
  | .empty => .empty
  | .sels eqSels =>
      .sels (Body.relSelections body ++ eqSels)

end Body

end Datalog

------------------------------------------------------------
-- Relational Atom and Body Translation
------------------------------------------------------------

namespace RelAtom

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- The raw RA relation reference for an atom. -/
private def relRaw
    (a : RelAtom D Γ) :
    RawRAExpr A D :=
  .rel a.rel.1

/- RelAtom relation references are SPJ expressions. -/
private theorem relRaw_isSPJ
    (a : RelAtom D Γ) :
    a.relRaw.IsSPJ := by
  simp [relRaw, RawRAExpr.IsSPJ]

end RelAtom

namespace Datalog

namespace Body

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Total arity of the body-atom product. -/
def arity :
    List (Atom D Γ) → Nat
| [] => 0
| .rel a :: body =>
    Γ.arity a.rel + arity body
| .eq _ _ :: body => arity body

private theorem relTerms_length
    (body : List (Atom D Γ)) :
    (Body.relTerms body).length = Body.arity body := by
  induction body with
  | nil =>
      simp [relTerms, arity]
  | cons b body ih =>
      cases b with
      | rel a =>
          simp [relTerms, arity, ih]
      | eq lhs rhs =>
          simpa [relTerms, arity] using ih

private theorem entries_bounds
    {body : List (Atom D Γ)}
    {p : Nat}
    {t : RelTerm D}
    (hmem : (p, t) ∈ Body.entries body) :
    p < Body.arity body := by
  unfold entries at hmem
  rcases List.mem_mapIdx.mp hmem with ⟨i, hi, hEq⟩
  have hp : p = i := by
    simpa using (congrArg Prod.fst hEq).symm
  subst hp
  simpa [relTerms_length body] using hi

private theorem atom_arg_mem_of_varList
    (a : RelAtom D Γ)
    {x : Var}
    (hx : x ∈ a.varList) :
    RelTerm.var x ∈ a.args.toList := by
  unfold RelAtom.varList at hx
  rcases List.mem_filterMap.mp hx with ⟨t, ht, hVar⟩
  cases t with
  | var y =>
      change some y = some x at hVar
      cases hVar
      exact ht
  | const c =>
      change (none : Option Var) = some x at hVar
      cases hVar

private theorem relTerm_mem_of_relVarList
    (body : List (Atom D Γ))
    {x : Var}
    (hx : x ∈ Body.relVarList body) :
    RelTerm.var x ∈ Body.relTerms body := by
  induction body with
  | nil =>
      simp [Body.relVarList, Atom.listRelVarList] at hx
  | cons b body ih =>
    cases b with
    | rel a =>
        have hx' :
            x ∈ a.varList ∨
              x ∈ Body.relVarList body := by
          simpa [Body.relVarList, Atom.listRelVarList,
            Atom.relVarList]
            using hx
        rcases hx' with hxA | hxBody
        · simpa [relTerms] using
            Or.inl (atom_arg_mem_of_varList a hxA)
        · simpa [relTerms] using
            Or.inr (ih hxBody)
      | eq lhs rhs =>
        have hxBody : x ∈ Body.relVarList body := by
          simpa [Body.relVarList, Atom.listRelVarList,
            Atom.relVarList]
            using hx
        simpa [relTerms] using ih hxBody

private theorem entries_var_mem_of_relVarList
    (body : List (Atom D Γ))
    {x : Var}
    (hx : x ∈ Body.relVarList body) :
    ∃ p : Nat, (p, RelTerm.var x) ∈ Body.entries body := by
  have hTerm := Body.relTerm_mem_of_relVarList body hx
  unfold entries
  rcases
      (List.exists_mem_iff_getElem
        (p := fun t => t = RelTerm.var x)).mp
        ⟨RelTerm.var x, hTerm, rfl⟩ with
    ⟨i, hi, hGet⟩
  refine ⟨i, ?_⟩
  apply List.mem_mapIdx.mpr
  exact ⟨i, hi, by simp [hGet]⟩

private theorem relEnv_lookup_isSome_of_relVarList
    (body : List (Atom D Γ))
    {x : Var}
    (hx : x ∈ Body.relVarList body) :
    (RAConsequence.lookupVarPos (Body.relEnv body) x).isSome =
      true := by
  unfold relEnv selectionEnv
  exact
    RAConsequence.collectSelectionsAndEnv_lookup_isSome
      (Body.entries body) [] x
      (Or.inl (Body.entries_var_mem_of_relVarList body hx))

private theorem relEnv_lookup_isSome_of_hasRelVar
    (body : List (Atom D Γ))
    {x : Var}
    (hx : Body.HasRelVar body x) :
    (RAConsequence.lookupVarPos (Body.relEnv body) x).isSome =
      true := by
  unfold HasRelVar relVars at hx
  change x ∈ Atom.relVars body at hx
  unfold Atom.relVars at hx
  rw [List.mem_toFinset] at hx
  exact Body.relEnv_lookup_isSome_of_relVarList body hx

private theorem relSelections_bounds
    (body : List (Atom D Γ)) :
    ∀ φ,
      φ ∈ Body.relSelections body →
        φ.arityReq < Body.arity body := by
  have hBounds :=
    RAConsequence.collectSelectionsAndEnv_bounds
      (es := Body.entries body)
      (env := [])
      (N := Body.arity body)
      (hEs := by
        intro p t hmem
        exact entries_bounds hmem)
      (hEnv := by
        intro x p hmem
        cases hmem)
  simpa [relSelections, selectionEnv] using hBounds.1

private theorem relEnv_bounds
    (body : List (Atom D Γ)) :
    ∀ x p, (x, p) ∈ Body.relEnv body → p < Body.arity body := by
  have hBounds :=
    RAConsequence.collectSelectionsAndEnv_bounds
      (es := Body.entries body)
      (env := [])
      (N := Body.arity body)
      (hEs := by
        intro p t hmem
        exact entries_bounds hmem)
      (hEnv := by
        intro x p hmem
        cases hmem)
  simpa [relEnv, selectionEnv] using hBounds.2

/- Product of all relational atoms in a body. -/
private def productRaw :
    List (Atom D Γ) → RawRAExpr A D
| [] => .top
| .rel a :: body =>
    .prod a.relRaw (productRaw body)
| .eq _ _ :: body => productRaw body

/- Body products have the expected raw arity. -/
private theorem productRaw_arity
    (body : List (Atom D Γ)) :
    ((Body.productRaw body)).arity? Γ = some (Body.arity body) := by
  induction body with
  | nil =>
      simp [productRaw, arity, RawRAExpr.arity?]
  | cons b body ih =>
      cases b with
      | rel a =>
          simp [productRaw, arity, RelAtom.relRaw,
            RawRAExpr.arity?, UnnamedSchema.arity?,
            a.rel.2, ih]
      | eq lhs rhs =>
          simpa [productRaw, arity] using ih

/- Body products are SPJ expressions. -/
private theorem productRaw_isSPJ
    (body : List (Atom D Γ)) :
    ((Body.productRaw body)).IsSPJ := by
  induction body with
  | nil =>
      simp [productRaw, RawRAExpr.IsSPJ]
  | cons b body ih =>
      cases b with
      | rel a =>
          simp [productRaw, RelAtom.relRaw,
            RawRAExpr.IsSPJ, ih]
      | eq lhs rhs =>
          simpa [productRaw] using ih

/- Product tuple induced by a valuation. -/
def productTuple
    (σ : Assign D) :
    (body : List (Atom D Γ)) → Tuple D (Body.arity body)
| [] => Tuple.empty
| .rel a :: body =>
    FinRelation.appendTuple
      (a.evalTuple σ)
      (productTuple σ body)
| .eq _ _ :: body => productTuple σ body

/- Appending an equality atom adds no output columns. -/
theorem arity_append_eq
    (body : List (Atom D Γ))
    (lhs rhs : RelTerm D) :
    Body.arity (body ++ [.eq lhs rhs]) =
      Body.arity body := by
  induction body with
  | nil =>
      rfl
  | cons atom body ih =>
      cases atom with
      | rel a =>
          simp [Body.arity, ih]
      | eq _ _ =>
          simpa [Body.arity] using ih

private theorem atom_evalTuple_toList
    (a : RelAtom D Γ)
    (σ : Assign D) :
    (a.evalTuple σ).toList =
      a.args.toList.map (RelTerm.eval σ) := by
  simp [RelAtom.evalTuple, RelTerm.evalVector_eq_map,
    Vector.toList_map]

private theorem productTuple_toList
    (σ : Assign D) :
    (body : List (Atom D Γ)) →
      (Body.productTuple σ body).toList =
        (Body.relTerms body).map (RelTerm.eval σ)
| [] => by
    simp [productTuple, relTerms, arity, Tuple.empty]
| .rel a :: body => by
    calc
      (productTuple σ (.rel a :: body)).toList
          =
        (a.evalTuple σ).toList ++
          (productTuple σ body).toList := by
            change
              (Vector.append (a.evalTuple σ)
                (productTuple σ body)).toList =
                (a.evalTuple σ).toList ++
                  (productTuple σ body).toList
            exact Vector.toList_append
      _ =
        a.args.toList.map (RelTerm.eval σ) ++
          (Body.relTerms body).map (RelTerm.eval σ) := by
            rw [atom_evalTuple_toList,
              productTuple_toList σ body]
      _ = (Body.relTerms
          (.rel a :: body : List (Atom D Γ))).map
            (RelTerm.eval σ) := by
            simp [relTerms, List.map_append]
| .eq lhs rhs :: body => by
    simpa [productTuple, relTerms] using
      productTuple_toList σ body

private theorem relTerms_append_eq
    (body : List (Atom D Γ))
    (lhs rhs : RelTerm D) :
    Body.relTerms (body ++ [.eq lhs rhs]) =
      Body.relTerms body := by
  induction body with
  | nil =>
      rfl
  | cons atom body ih =>
      cases atom with
      | rel a =>
          simp [Body.relTerms, ih]
      | eq _ _ =>
          simpa [Body.relTerms] using ih

/- Appending an equality atom preserves output tuples. -/
theorem productTuple_append_eq
    (σ : Assign D)
    (body : List (Atom D Γ))
    (lhs rhs : RelTerm D) :
    Tuple.castArity
        (Body.arity_append_eq body lhs rhs).symm
        (Body.productTuple σ
          (body ++ [.eq lhs rhs])) =
      Body.productTuple σ body := by
  apply Vector.toList_inj.mp
  rw [RAConsequence.castArity_toList]
  rw [Body.productTuple_toList]
  rw [Body.productTuple_toList]
  rw [Body.relTerms_append_eq]

private theorem entries_value_from_productTuple
    (σ : Assign D)
    {body : List (Atom D Γ)}
    {p : Nat}
    {t : RelTerm D}
    (hmem : (p, t) ∈ Body.entries body) :
    RAConsequence.tupleCol (Body.productTuple σ body) p =
      t.eval σ := by
  unfold entries at hmem
  rcases List.mem_mapIdx.mp hmem with ⟨i, hi, hEq⟩
  have hp : p = i := by
    simpa using (congrArg Prod.fst hEq).symm
  have ht : t = (Body.relTerms body)[i] := by
    simpa using (congrArg Prod.snd hEq).symm
  subst p
  subst ht
  have hiAr : i < Body.arity body := by
    simpa [relTerms_length body] using hi
  rw [RAConsequence.tupleCol_eq_get_of_lt
    (Body.productTuple σ body) i hiAr]
  have hiList :
      i < (Body.productTuple σ body).toList.length := by
    simpa [Vector.length_toList] using hiAr
  have hiMap :
      i <
        ((Body.relTerms body).map
          (RelTerm.eval σ)).length := by
    simpa [List.length_map, relTerms_length body] using hiAr
  have hListGet :
      (Body.productTuple σ body).toList[i]'hiList =
        (Body.productTuple σ body).get ⟨i, hiAr⟩ := by
    exact Vector.getElem_toList hiList
  have hMapGet :
      ((Body.relTerms body).map
        (RelTerm.eval σ))[i]'hiMap =
        ((Body.relTerms body)[i]).eval σ := by
    simp
  have hToList := productTuple_toList σ body
  have hGetEq :
      (Body.productTuple σ body).toList[i]'hiList =
        ((Body.relTerms body).map
          (RelTerm.eval σ))[i]'hiMap := by
    have hGet? :=
      congrArg (fun l : List D => l[i]?) hToList
    have hLeft? :
        (Body.productTuple σ body).toList[i]? =
          some ((Body.productTuple σ body).toList[i]'hiList) :=
      List.getElem?_eq_getElem hiList
    have hRight? :
        ((Body.relTerms body).map (RelTerm.eval σ))[i]? =
          some (((Body.relTerms body).map
            (RelTerm.eval σ))[i]'hiMap) :=
      List.getElem?_eq_getElem hiMap
    have hSome :
        some ((Body.productTuple σ body).toList[i]'hiList) =
          some (((Body.relTerms body).map
            (RelTerm.eval σ))[i]'hiMap) := by
      calc
        some ((Body.productTuple σ body).toList[i]'hiList)
            = (Body.productTuple σ body).toList[i]? :=
              hLeft?.symm
        _ = ((Body.relTerms body).map
              (RelTerm.eval σ))[i]? := hGet?
        _ = some (((Body.relTerms body).map
              (RelTerm.eval σ))[i]'hiMap) := hRight?
    exact Option.some.inj hSome
  exact hListGet.symm.trans
    (hGetEq.trans hMapGet)

private theorem relSelections_hold_productTuple
    (body : List (Atom D Γ))
    (σ : Assign D) :
    ∀ φ, φ ∈ Body.relSelections body →
      Sel.Holds φ (Body.productTuple σ body) := by
  intro φ hφ
  have hEs :
      ∀ p t, (p, t) ∈ Body.entries body →
        RAConsequence.tupleCol (Body.productTuple σ body) p =
          t.eval σ := by
    intro p t hmem
    exact entries_value_from_productTuple σ hmem
  have hSound :=
    RAConsequence.collectSelectionsAndEnv_sound
      (es := Body.entries body)
      (env := [])
      (σ := σ)
      (f := RAConsequence.tupleCol (Body.productTuple σ body))
      hEs
      (by intro x p hmem; cases hmem)
  cases φ with
  | eqIdx i j =>
      have hEq :
          RAConsequence.tupleCol
            (Body.productTuple σ body) i =
          RAConsequence.tupleCol
            (Body.productTuple σ body) j :=
        hSound.1 (Sel.eqIdx i j)
          (by simpa [relSelections, selectionEnv] using hφ)
      have hBound :=
        Body.relSelections_bounds body (Sel.eqIdx i j) hφ
      have hi : i < Body.arity body :=
        lt_of_le_of_lt (Nat.le_max_left _ _) hBound
      have hj : j < Body.arity body :=
        lt_of_le_of_lt (Nat.le_max_right _ _) hBound
      exact
        RAConsequence.holds_eqIdx_of_tupleCol_eq
          (Body.productTuple σ body) hi hj hEq
  | eqConst i c =>
      have hEq :
          RAConsequence.tupleCol
            (Body.productTuple σ body) i = c :=
        hSound.1 (Sel.eqConst i c)
          (by simpa [relSelections, selectionEnv] using hφ)
      have hi : i < Body.arity body :=
        Body.relSelections_bounds body (Sel.eqConst i c) hφ
      exact
        RAConsequence.holds_eqConst_of_tupleCol_eq
          (Body.productTuple σ body) hi hEq
  | and s₁ s₂ =>
      have hFalse : False :=
        hSound.1 (Sel.and s₁ s₂)
          (by simpa [relSelections, selectionEnv] using hφ)
      cases hFalse
  | or s₁ s₂ =>
      have hFalse : False :=
        hSound.1 (Sel.or s₁ s₂)
          (by simpa [relSelections, selectionEnv] using hφ)
      cases hFalse
  | not s =>
      have hFalse : False :=
        hSound.1 (Sel.not s)
          (by simpa [relSelections, selectionEnv] using hφ)
      cases hFalse

private theorem relEnv_lookup_tupleCol_eq
    (body : List (Atom D Γ))
    (σ : Assign D) :
    ∀ x p,
      RAConsequence.lookupVarPos (Body.relEnv body) x = some p →
      RAConsequence.tupleCol
        (Body.productTuple σ body) p = σ x := by
  intro x p hLookup
  have hEs :
      ∀ q t, (q, t) ∈ Body.entries body →
        RAConsequence.tupleCol (Body.productTuple σ body) q =
          t.eval σ := by
    intro q t hmem
    exact entries_value_from_productTuple σ hmem
  have hSound :=
    RAConsequence.collectSelectionsAndEnv_sound
      (es := Body.entries body)
      (env := [])
      (σ := σ)
      (f := RAConsequence.tupleCol (Body.productTuple σ body))
      hEs
      (by intro y q hmem; cases hmem)
  have hmem : (x, p) ∈ Body.relEnv body :=
    RAConsequence.lookupVarPos_some_mem hLookup
  exact hSound.2 x p (by
    simpa [relEnv, selectionEnv] using hmem)

/- Equal product tuples agree on relational variables. -/
theorem eval_eq_of_productTuple_eq
    (body : List (Atom D Γ))
    (σ τ : Assign D)
    {x : Var}
    (hx : Body.HasRelVar body x)
    (hTuple :
      Body.productTuple σ body =
        Body.productTuple τ body) :
    σ x = τ x := by
  have hSome :=
    Body.relEnv_lookup_isSome_of_hasRelVar body hx
  cases hLookup :
      RAConsequence.lookupVarPos
        (Body.relEnv body) x with
  | none =>
      simp [hLookup] at hSome
  | some p =>
      have hσ := Body.relEnv_lookup_tupleCol_eq
        body σ x p hLookup
      have hτ := Body.relEnv_lookup_tupleCol_eq
        body τ x p hLookup
      rw [hTuple] at hσ
      exact hσ.symm.trans hτ

private theorem entries_eval_of_relSelections
    (body : List (Atom D Γ))
    (u : Tuple D (Body.arity body))
    (hSel :
      ∀ φ,
        φ ∈ Body.relSelections body → Sel.Holds φ u) :
    let σ : Assign D :=
      RAConsequence.valuationOfEnv u (Body.relEnv body)
    ∀ p t, (p, t) ∈ Body.entries body →
      RAConsequence.tupleCol u p = t.eval σ := by
  intro σ p t hmem
  have hInfo :=
    RAConsequence.collectSelectionsAndEnv_entry_info
      (es := Body.entries body)
      (env := [])
      p t hmem
  cases t with
  | const c =>
      have hEqConst :
          Sel.eqConst p c ∈ Body.relSelections body := by
        simpa [relSelections, selectionEnv] using hInfo
      have hp : p < Body.arity body :=
        Body.relSelections_bounds body (Sel.eqConst p c) hEqConst
      have hCol :
          RAConsequence.tupleCol u p = c :=
        RAConsequence.tupleCol_eq_of_holds_eqConst
          u hp (hSel (Sel.eqConst p c) hEqConst)
      simpa [RelTerm.eval] using hCol
  | var x =>
      rcases hInfo with ⟨q, hLookup, hq⟩
      have hσx : σ x = RAConsequence.tupleCol u q := by
        unfold σ
        exact
          RAConsequence.valuationOfEnv_lookup
            u (Body.relEnv body) x q hLookup
      rcases hq with hEq | hSelIdx
      · subst hEq
        simp [RelTerm.eval, hσx]
      · have hEqIdx :
            Sel.eqIdx q p ∈ Body.relSelections body := by
          simpa [relSelections, selectionEnv] using hSelIdx
        have hBound :
            (Sel.eqIdx q p).arityReq < Body.arity body :=
          Body.relSelections_bounds body (Sel.eqIdx q p) hEqIdx
        have hqLt : q < Body.arity body :=
          lt_of_le_of_lt (Nat.le_max_left _ _) hBound
        have hpLt : p < Body.arity body :=
          lt_of_le_of_lt (Nat.le_max_right _ _) hBound
        have hqp :
            RAConsequence.tupleCol u q =
              RAConsequence.tupleCol u p :=
          RAConsequence.tupleCol_eq_of_holds_eqIdx
            u hqLt hpLt (hSel (Sel.eqIdx q p) hEqIdx)
        have hpq :
            RAConsequence.tupleCol u p =
              RAConsequence.tupleCol u q := hqp.symm
        simpa [RelTerm.eval, hσx] using hpq

private theorem productTuple_eq_of_entries_eval
    (body : List (Atom D Γ))
    (u : Tuple D (Body.arity body))
    (σ : Assign D)
    (hEntries :
      ∀ p t, (p, t) ∈ Body.entries body →
        RAConsequence.tupleCol u p = t.eval σ) :
    u = Body.productTuple σ body := by
  apply Vector.ext
  intro i hi
  have hiRel : i < (Body.relTerms body).length := by
    simpa [relTerms_length body] using hi
  have hEntryMem :
      (i, (Body.relTerms body)[i]) ∈ Body.entries body := by
    unfold entries
    exact List.mem_mapIdx.mpr
      ⟨i, hiRel, by simp⟩
  have hEntry :
      RAConsequence.tupleCol u i =
        ((Body.relTerms body)[i]).eval σ :=
    hEntries i (Body.relTerms body)[i] hEntryMem
  have hU :
      RAConsequence.tupleCol u i = u.get ⟨i, hi⟩ :=
    RAConsequence.tupleCol_eq_get_of_lt u i hi
  have hProdList := productTuple_toList σ body
  have hiProdList :
      i < (Body.productTuple σ body).toList.length := by
    simpa [Vector.length_toList] using hi
  have hiMap :
      i < ((Body.relTerms body).map (RelTerm.eval σ)).length := by
    simpa [List.length_map, relTerms_length body] using hi
  have hProdGetList :
      (Body.productTuple σ body).toList[i]'hiProdList =
        (Body.productTuple σ body).get ⟨i, hi⟩ :=
    Vector.getElem_toList hiProdList
  have hMapGet :
      ((Body.relTerms body).map (RelTerm.eval σ))[i]'hiMap =
        ((Body.relTerms body)[i]).eval σ := by
    simp
  have hGetEq :
      (Body.productTuple σ body).toList[i]'hiProdList =
        ((Body.relTerms body).map (RelTerm.eval σ))[i]'hiMap := by
    have hGet? :=
      congrArg (fun l : List D => l[i]?) hProdList
    have hLeft? :
        (Body.productTuple σ body).toList[i]? =
          some
            ((Body.productTuple σ body).toList[i]'hiProdList) :=
      List.getElem?_eq_getElem hiProdList
    have hRight? :
        ((Body.relTerms body).map (RelTerm.eval σ))[i]? =
          some
            (((Body.relTerms body).map (RelTerm.eval σ))[i]'hiMap) :=
      List.getElem?_eq_getElem hiMap
    have hSome :
        some ((Body.productTuple σ body).toList[i]'hiProdList) =
          some
            (((Body.relTerms body).map (RelTerm.eval σ))[i]'hiMap)
          := by
      calc
        some ((Body.productTuple σ body).toList[i]'hiProdList)
            = (Body.productTuple σ body).toList[i]? :=
              hLeft?.symm
        _ = ((Body.relTerms body).map (RelTerm.eval σ))[i]? := hGet?
        _ = some
              (((Body.relTerms body).map (RelTerm.eval σ))[i]'hiMap)
            :=
          hRight?
    exact Option.some.inj hSome
  have hProd :
      (Body.productTuple σ body).get ⟨i, hi⟩ =
        ((Body.relTerms body)[i]).eval σ := by
    exact hProdGetList.symm.trans (hGetEq.trans hMapGet)
  exact hU.symm.trans (hEntry.trans hProd.symm)

/- Satisfaction of relational atoms only. -/
private def RelSat
    (I : Instance D Γ)
    (σ : Assign D) :
    List (Atom D Γ) → Prop
| [] => True
| .rel a :: body => a.Sat I σ ∧ RelSat I σ body
| .eq _ _ :: body => RelSat I σ body

/- Satisfaction of equality atoms only. -/
private def EqSat
    (σ : Assign D) :
    List (Atom D Γ) → Prop
| [] => True
| .rel _ :: body => EqSat σ body
| .eq lhs rhs :: body =>
    lhs.eval σ = rhs.eval σ ∧ EqSat σ body

private theorem eqSat_of_bodyEqualityPlan_holds
    {n : Nat}
    (env : List (Var × Nat))
    (hEnv : ∀ x p, (x, p) ∈ env → p < n)
    (u : Tuple D n) :
    (body : List (Atom D Γ)) →
      {sels : List (Sel D)} →
      RAConsequence.bodyEqualityPlan env body =
        .sels sels →
      (∀ φ, φ ∈ sels → Sel.Holds φ u) →
      EqSat (RAConsequence.valuationOfEnv u env) body
| [], sels, hPlan, _ => by
    simp only [RAConsequence.bodyEqualityPlan] at hPlan
    cases hPlan
    simp [EqSat]
| .rel _ :: body, sels, hPlan, hHolds =>
    eqSat_of_bodyEqualityPlan_holds
      env hEnv u body hPlan hHolds
| .eq lhs rhs :: body, sels, hPlan, hHolds => by
    cases hEq :
        RAConsequence.termEqualityPlan env lhs rhs with
    | empty =>
        simp only [RAConsequence.bodyEqualityPlan, hEq,
          RAConsequence.EqualityPlan.append] at hPlan
        cases hPlan
    | sels eqSels₁ =>
        cases hRest :
            RAConsequence.bodyEqualityPlan env body with
        | empty =>
            simp only [RAConsequence.bodyEqualityPlan,
              hEq, hRest,
              RAConsequence.EqualityPlan.append] at hPlan
            cases hPlan
        | sels eqSels₂ =>
            simp only [RAConsequence.bodyEqualityPlan,
              hEq, hRest,
              RAConsequence.EqualityPlan.append] at hPlan
            cases hPlan
            have hEqSat :
                lhs.eval
                    (RAConsequence.valuationOfEnv u env) =
                  rhs.eval
                    (RAConsequence.valuationOfEnv u env) :=
              RAConsequence.termEqualityPlan_sat_of_holds
                env hEnv u lhs rhs hEq
                (by
                  intro φ hφ
                  exact hHolds φ (List.mem_append.mpr
                    (Or.inl hφ)))
            have hTail :
                EqSat
                  (RAConsequence.valuationOfEnv u env)
                  body :=
              eqSat_of_bodyEqualityPlan_holds
                env hEnv u body hRest
                (by
                  intro φ hφ
                  exact hHolds φ (List.mem_append.mpr
                    (Or.inr hφ)))
            exact ⟨hEqSat, hTail⟩

private theorem bodyEqualityPlan_holds_of_eqSat
    {n : Nat}
    (env : List (Var × Nat))
    (hEnv : ∀ x p, (x, p) ∈ env → p < n)
    (u : Tuple D n)
    (σ : Assign D) :
    (body : List (Atom D Γ)) →
      (hLookup :
        ∀ x, x ∈ Body.vars body →
          ∃ p,
            RAConsequence.lookupVarPos env x = some p ∧
            RAConsequence.tupleCol u p = σ x) →
      EqSat σ body →
      ∃ sels,
        RAConsequence.bodyEqualityPlan env body =
          .sels sels ∧
          ∀ φ, φ ∈ sels → Sel.Holds φ u
| [], _hLookup, _hEqSat => by
    exact ⟨[], by simp [RAConsequence.bodyEqualityPlan],
      by intro φ hφ; cases hφ⟩
| .rel a :: body, hLookup, hEqSat =>
    bodyEqualityPlan_holds_of_eqSat
      env hEnv u σ body
      (by
        intro x hx
        apply hLookup
        change x ∈ Atom.vars body at hx
        change x ∈ Atom.vars ((Atom.rel a : Atom D Γ) :: body)
        unfold Atom.vars at hx ⊢
        rw [List.mem_toFinset] at hx ⊢
        change
          x ∈ (Atom.rel a : Atom D Γ).varList ++
            Atom.listVarList body
        exact List.mem_append.mpr (Or.inr hx))
      hEqSat
| .eq lhs rhs :: body, hLookup, hEqSat => by
    rcases hEqSat with ⟨hEqSatHead, hEqSatTail⟩
    have hTermLookup :
        ∀ x,
          x ∈ [lhs, rhs].filterMap RelTerm.var? →
            ∃ p,
              RAConsequence.lookupVarPos env x = some p ∧
              RAConsequence.tupleCol u p = σ x := by
      intro x hx
      apply hLookup
      change x ∈ Atom.vars ((Atom.eq lhs rhs : Atom D Γ) :: body)
      unfold Atom.vars
      rw [List.mem_toFinset]
      change
        x ∈ (Atom.eq lhs rhs : Atom D Γ).varList ++
          Atom.listVarList body
      exact List.mem_append.mpr
        (Or.inl (by simpa [Atom.varList] using hx))
    rcases
      RAConsequence.termEqualityPlan_holds_of_sat
        env hEnv u σ lhs rhs hTermLookup hEqSatHead with
      ⟨eqSels₁, hPlan₁, hHolds₁⟩
    rcases
      bodyEqualityPlan_holds_of_eqSat
        env hEnv u σ body
        (by
          intro x hx
          apply hLookup
          change x ∈ Atom.vars body at hx
          change x ∈ Atom.vars
            ((Atom.eq lhs rhs : Atom D Γ) :: body)
          unfold Atom.vars at hx ⊢
          rw [List.mem_toFinset] at hx ⊢
          change
            x ∈ (Atom.eq lhs rhs : Atom D Γ).varList ++
              Atom.listVarList body
          exact List.mem_append.mpr (Or.inr hx))
        hEqSatTail with
      ⟨eqSels₂, hPlan₂, hHolds₂⟩
    refine ⟨eqSels₁ ++ eqSels₂, ?_, ?_⟩
    · simp [RAConsequence.bodyEqualityPlan,
        hPlan₁, hPlan₂,
        RAConsequence.EqualityPlan.append]
    · intro φ hφ
      rcases List.mem_append.mp hφ with hLeft | hRight
      · exact hHolds₁ φ hLeft
      · exact hHolds₂ φ hRight

private theorem satisfied_iff_relSat_eqSat
    (I : Instance D Γ)
    (σ : Assign D) :
    (body : List (Atom D Γ)) →
      Body.Satisfied body I σ ↔
        RelSat I σ body ∧ EqSat σ body
| [] => by
    simp [Body.Satisfied, RelSat, EqSat]
| .rel a :: body => by
    simp [Body.Satisfied, Atom.Sat, RelSat, EqSat,
      satisfied_iff_relSat_eqSat I σ body,
      and_left_comm, and_comm]
  | .eq lhs rhs :: body => by
    simp [Body.Satisfied, Atom.Sat, RelSat, EqSat,
      satisfied_iff_relSat_eqSat I σ body,
      and_assoc, and_comm]

private theorem productRaw_answer_of_relSat
    (I : Instance D Γ)
    (σ : Assign D) :
    (body : List (Atom D Γ)) →
      RelSat I σ body →
      ((Body.productRaw body)).answerContains I
        (Body.productTuple σ body)
| [], _ => by
    simpa [productRaw, productTuple, arity] using
      (RawRAExpr.answer_top_iff
        (I := I)
        (t := Tuple.empty)).2 True.intro
| .rel a :: body, hSat => by
    have hAtom :
        a.relRaw.answerContains I (a.evalTuple σ) := by
      have hAr :
          Γ.arity? a.rel.1 = some (Γ.arity a.rel) := by
        simp [UnnamedSchema.arity?, a.rel.2]
      exact
        (RawRAExpr.answer_rel_iff
          (I := I) hAr (a.evalTuple σ)).2
          ⟨a.rel.2, rfl, by
            simpa [RelAtom.Sat] using hSat.1⟩
    have hBody :
        ((Body.productRaw body)).answerContains I
          (Body.productTuple σ body) :=
      productRaw_answer_of_relSat I σ body hSat.2
    have hAAr :
        a.relRaw.arity? Γ = some (Γ.arity a.rel) := by
      simp [RelAtom.relRaw, RawRAExpr.arity?,
        UnnamedSchema.arity?, a.rel.2]
    exact
      (RawRAExpr.answer_prod_iff
        (I := I)
        (e₁ := a.relRaw)
        (e₂ := (Body.productRaw body))
        hAAr (Body.productRaw_arity body)
        (FinRelation.appendTuple
          (a.evalTuple σ)
          (Body.productTuple σ body))).2
        ⟨a.evalTuple σ, hAtom,
          Body.productTuple σ body, hBody, rfl⟩
| .eq lhs rhs :: body, hSat =>
    productRaw_answer_of_relSat I σ body hSat

private theorem relSat_of_productRaw_answer_productTuple
    (I : Instance D Γ)
    (σ : Assign D) :
    (body : List (Atom D Γ)) →
      ((Body.productRaw body)).answerContains I
        (Body.productTuple σ body) →
      RelSat I σ body
| [], _ => by
    simp [RelSat]
| .rel a :: body, hAns => by
    have hAAr :
        a.relRaw.arity? Γ = some (Γ.arity a.rel) := by
      simp [RelAtom.relRaw, RawRAExpr.arity?,
        UnnamedSchema.arity?, a.rel.2]
    have hProd :=
      (RawRAExpr.answer_prod_iff
        (I := I)
        (e₁ := a.relRaw)
        (e₂ := (Body.productRaw body))
        hAAr (Body.productRaw_arity body)
        (FinRelation.appendTuple
          (a.evalTuple σ)
          (Body.productTuple σ body))).1
        (by simpa [productRaw, productTuple] using hAns)
    rcases hProd with ⟨t₁, ht₁, t₂, ht₂, hApp⟩
    have hSplit :
        t₁ = a.evalTuple σ ∧
          t₂ = Body.productTuple σ body := by
      constructor
      · apply Vector.ext
        intro i hi
        let j : Fin (Γ.arity a.rel) := ⟨i, hi⟩
        have hCoord :=
          congrArg
            (fun t : Tuple D
                (Γ.arity a.rel + Body.arity body) =>
              t.get ⟨i, by omega⟩)
            hApp
        change
          (FinRelation.appendTuple t₁ t₂).get
              ⟨i, by omega⟩ =
            (FinRelation.appendTuple
              (a.evalTuple σ)
              (Body.productTuple σ body)).get
                ⟨i, by omega⟩ at hCoord
        rw [FinRelation.get_appendTuple_left t₁ t₂ j,
          FinRelation.get_appendTuple_left
            (a.evalTuple σ)
            (Body.productTuple σ body) j]
          at hCoord
        simpa [j] using hCoord
      · apply Vector.ext
        intro i hi
        let j : Fin (Body.arity body) := ⟨i, hi⟩
        have hCoord :=
          congrArg
            (fun t : Tuple D
                (Γ.arity a.rel + Body.arity body) =>
              t.get ⟨Γ.arity a.rel + i, by omega⟩)
            hApp
        change
          (FinRelation.appendTuple t₁ t₂).get
              ⟨Γ.arity a.rel + i, by omega⟩ =
            (FinRelation.appendTuple
              (a.evalTuple σ)
              (Body.productTuple σ body)).get
                ⟨Γ.arity a.rel + i, by omega⟩ at hCoord
        rw [FinRelation.get_appendTuple_right t₁ t₂ j,
          FinRelation.get_appendTuple_right
            (a.evalTuple σ)
            (Body.productTuple σ body) j]
          at hCoord
        simpa [j] using hCoord
    have hAtomAns :
        a.relRaw.answerContains I (a.evalTuple σ) := by
      simpa [hSplit.1] using ht₁
    have hBodyAns :
        ((Body.productRaw body)).answerContains I
          (Body.productTuple σ body) := by
      simpa [hSplit.2] using ht₂
    have hAr :
        Γ.arity? a.rel.1 = some (Γ.arity a.rel) := by
      simp [UnnamedSchema.arity?, a.rel.2]
    have hAtomSat : a.Sat I σ := by
      rcases
        (RawRAExpr.answer_rel_iff
          (I := I) hAr (a.evalTuple σ)).1 hAtomAns with
        ⟨hMem, hEq, hTuple⟩
      have hRel :
          (⟨a.rel.1, hMem⟩ : Γ.syms) = a.rel := by
        apply Subtype.ext
        rfl
      cases hRel
      cases hEq
      simpa [RelAtom.Sat] using hTuple
    exact
      ⟨hAtomSat,
        relSat_of_productRaw_answer_productTuple
          I σ body hBodyAns⟩
| .eq lhs rhs :: body, hAns =>
    relSat_of_productRaw_answer_productTuple I σ body hAns

/-
  Total selected body product used by the public
  translation.
-/
private def selectedProductRaw
    (body : List (Atom D Γ)) :
    RawRAExpr A D :=
  match Body.allSelectionsPlan body with
  | .empty => .empty (Body.arity body)
  | .sels sels =>
      RAConsequence.applySelections sels (Body.productRaw body)

private theorem allSelectionsPlan_sels_bounds
    (body : List (Atom D Γ))
    {sels : List (Sel D)}
    (hPlan : Body.allSelectionsPlan body = .sels sels) :
    ∀ φ, φ ∈ sels → φ.arityReq < Body.arity body := by
  unfold allSelectionsPlan at hPlan
  cases hEq : Body.equalityPlan body with
  | empty =>
      simp only [hEq] at hPlan
      cases hPlan
  | sels eqSels =>
      simp only [hEq] at hPlan
      cases hPlan
      intro φ hφ
      rcases List.mem_append.mp hφ with hRel | hEqSel
      · exact Body.relSelections_bounds body φ hRel
      · unfold equalityPlan at hEq
        exact
          RAConsequence.bodyEqualityPlan_sels_bounds
            (Body.relEnv body) (Body.relEnv_bounds body)
            body hEq φ hEqSel

/-
  The total selected body product has body-product arity.
-/
private theorem selectedProductRaw_arity
    (body : List (Atom D Γ)) :
    ((Body.selectedProductRaw body)).arity? Γ =
      some (Body.arity body) := by
  unfold selectedProductRaw
  cases hPlan : Body.allSelectionsPlan body with
  | empty =>
      simp [RawRAExpr.arity?]
  | sels sels =>
      exact
        RAConsequence.applySelections_arity
          sels
          (Body.productRaw_arity body)
          (Body.allSelectionsPlan_sels_bounds body hPlan)

/-
  The total selected body product is in the SPJ fragment.
-/
private theorem selectedProductRaw_isSPJ
    (body : List (Atom D Γ)) :
    ((Body.selectedProductRaw body)).IsSPJ := by
  unfold selectedProductRaw
  cases hPlan : Body.allSelectionsPlan body with
  | empty =>
      simp [RawRAExpr.IsSPJ]
  | sels sels =>
      exact
        RAConsequence.applySelections_isSPJ
          sels (Body.productRaw_isSPJ body)

private theorem satisfied_of_selectedProductRaw_answer
    (body : List (Atom D Γ))
    (I : Instance D Γ)
    (u : Tuple D (Body.arity body))
    (hAns : ((Body.selectedProductRaw body)).answerContains I u) :
    Body.Satisfied body I
      (RAConsequence.valuationOfEnv u (Body.relEnv body)) := by
  unfold selectedProductRaw allSelectionsPlan at hAns
  cases hEqPlan : Body.equalityPlan body with
  | empty =>
      rw [hEqPlan] at hAns
      exact False.elim
        ((RawRAExpr.answer_empty_iff
          (I := I) (t := u)).1 hAns)
  | sels eqSels =>
      rw [hEqPlan] at hAns
      have hBounds :
          ∀ φ, φ ∈ Body.relSelections body ++ eqSels →
            φ.arityReq < Body.arity body := by
        intro φ hφ
        rcases List.mem_append.mp hφ with hRel | hEq
        · exact Body.relSelections_bounds body φ hRel
        · unfold equalityPlan at hEqPlan
          exact
            RAConsequence.bodyEqualityPlan_sels_bounds
              (Body.relEnv body) (Body.relEnv_bounds body) body
              hEqPlan φ hEq
      have hSelected :=
        (RAConsequence.applySelections_answer_iff
          (Body.relSelections body ++ eqSels)
          (Body.productRaw_arity body) hBounds u).1 hAns
      rcases hSelected with ⟨hBase, hAll⟩
      let σ : Assign D :=
        RAConsequence.valuationOfEnv u (Body.relEnv body)
      have hRelHolds :
          ∀ φ,
            φ ∈ Body.relSelections body →
              Sel.Holds φ u := by
        intro φ hφ
        exact hAll φ (List.mem_append.mpr (Or.inl hφ))
      have hEntries :
          ∀ p t, (p, t) ∈ Body.entries body →
            RAConsequence.tupleCol u p = t.eval σ := by
        have h0 :=
          Body.entries_eval_of_relSelections body u hRelHolds
        simpa [σ] using h0
      have hU :
          u = Body.productTuple σ body :=
        Body.productTuple_eq_of_entries_eval body u σ hEntries
      have hRelSat :
          RelSat I σ body := by
        exact
          relSat_of_productRaw_answer_productTuple
            I σ body (by simpa [hU] using hBase)
      have hEqHolds :
          ∀ φ, φ ∈ eqSels → Sel.Holds φ u := by
        intro φ hφ
        exact hAll φ (List.mem_append.mpr (Or.inr hφ))
      have hEqSat :
          EqSat σ body := by
        unfold equalityPlan at hEqPlan
        have hEqSat0 :=
          eqSat_of_bodyEqualityPlan_holds
            (Body.relEnv body) (Body.relEnv_bounds body) u body
            hEqPlan hEqHolds
        simpa [σ] using hEqSat0
      exact
        (satisfied_iff_relSat_eqSat I σ body).2
          ⟨hRelSat, hEqSat⟩

private theorem selectedProductRaw_answer_of_satisfied
    (body : List (Atom D Γ))
    (I : Instance D Γ)
    (σ : Assign D)
    (hLookup :
      ∀ x, x ∈ Body.vars body →
        ∃ p,
          RAConsequence.lookupVarPos (Body.relEnv body) x =
            some p ∧
          RAConsequence.tupleCol
            (Body.productTuple σ body) p = σ x)
    (hSat : Body.Satisfied body I σ) :
    ((Body.selectedProductRaw body)).answerContains I
      (Body.productTuple σ body) := by
  have hSplit :=
    (satisfied_iff_relSat_eqSat I σ body).1 hSat
  rcases hSplit with ⟨hRelSat, hEqSat⟩
  have hBase :
      ((Body.productRaw body)).answerContains I
        (Body.productTuple σ body) :=
    productRaw_answer_of_relSat I σ body hRelSat
  have hRelHolds :
      ∀ φ, φ ∈ Body.relSelections body →
        Sel.Holds φ (Body.productTuple σ body) :=
    Body.relSelections_hold_productTuple body σ
  rcases
    bodyEqualityPlan_holds_of_eqSat
      (Body.relEnv body) (Body.relEnv_bounds body)
      (Body.productTuple σ body) σ body hLookup hEqSat with
    ⟨eqSels, hEqPlan, hEqHolds⟩
  have hBounds :
      ∀ φ, φ ∈ Body.relSelections body ++ eqSels →
        φ.arityReq < Body.arity body := by
    intro φ hφ
    rcases List.mem_append.mp hφ with hRel | hEq
    · exact Body.relSelections_bounds body φ hRel
    · exact
        RAConsequence.bodyEqualityPlan_sels_bounds
          (Body.relEnv body) (Body.relEnv_bounds body) body hEqPlan φ hEq
  have hAll :
      ∀ φ, φ ∈ Body.relSelections body ++ eqSels →
        Sel.Holds φ (Body.productTuple σ body) := by
    intro φ hφ
    rcases List.mem_append.mp hφ with hRel | hEq
    · exact hRelHolds φ hRel
    · exact hEqHolds φ hEq
  unfold selectedProductRaw allSelectionsPlan equalityPlan
  rw [hEqPlan]
  exact
    (RAConsequence.applySelections_answer_iff
      (Body.relSelections body ++ eqSels)
      (Body.productRaw_arity body) hBounds
      (Body.productTuple σ body)).2
      ⟨hBase, hAll⟩

/- Every body variable occurs in a relational atom. -/
def RelationallySafe
    (body : List (Atom D Γ)) : Prop :=
  ∀ x, x ∈ Body.vars body → Body.HasRelVar body x

/- The checked selected product of a Datalog body. -/
def selectedProduct
    (body : List (Atom D Γ)) :
    RAExpr D Γ (Body.arity body) where
  expr := Body.selectedProductRaw body
  wf := Body.selectedProductRaw_arity body

private theorem selectedProductRaw_answer_info
    (body : List (Atom D Γ))
    (I : Instance D Γ)
    (u : Tuple D (Body.arity body))
    (hAns :
      Body.selectedProductRaw body |>.answerContains I u) :
    ∃ σ : Assign D,
      Body.Satisfied body I σ ∧
        Body.productTuple σ body = u := by
  unfold selectedProductRaw allSelectionsPlan at hAns
  cases hEqPlan : Body.equalityPlan body with
  | empty =>
      rw [hEqPlan] at hAns
      exact False.elim
        ((RawRAExpr.answer_empty_iff
          (I := I) (t := u)).1 hAns)
  | sels eqSels =>
      rw [hEqPlan] at hAns
      have hBounds :
          ∀ φ,
            φ ∈ Body.relSelections body ++ eqSels →
            φ.arityReq < Body.arity body := by
        intro φ hφ
        rcases List.mem_append.mp hφ with hRel | hEq
        · exact Body.relSelections_bounds body φ hRel
        · unfold equalityPlan at hEqPlan
          exact
            RAConsequence.bodyEqualityPlan_sels_bounds
              (Body.relEnv body) (Body.relEnv_bounds body)
              body hEqPlan φ hEq
      have hSelected :=
        (RAConsequence.applySelections_answer_iff
          (Body.relSelections body ++ eqSels)
          (Body.productRaw_arity body) hBounds u).1 hAns
      rcases hSelected with ⟨hBase, hAll⟩
      let σ : Assign D :=
        RAConsequence.valuationOfEnv u (Body.relEnv body)
      have hRelHolds :
          ∀ φ, φ ∈ Body.relSelections body →
            Sel.Holds φ u := by
        intro φ hφ
        exact hAll φ (List.mem_append.mpr (Or.inl hφ))
      have hEntries :
          ∀ p t, (p, t) ∈ Body.entries body →
            RAConsequence.tupleCol u p = t.eval σ := by
        simpa [σ] using
          Body.entries_eval_of_relSelections
            body u hRelHolds
      have hU : u = Body.productTuple σ body :=
        Body.productTuple_eq_of_entries_eval
          body u σ hEntries
      have hRelSat : RelSat I σ body := by
        exact
          relSat_of_productRaw_answer_productTuple
            I σ body (by simpa [hU] using hBase)
      have hEqHolds :
          ∀ φ, φ ∈ eqSels → Sel.Holds φ u := by
        intro φ hφ
        exact hAll φ (List.mem_append.mpr (Or.inr hφ))
      have hEqSat : EqSat σ body := by
        unfold equalityPlan at hEqPlan
        have hEqSat₀ :=
          eqSat_of_bodyEqualityPlan_holds
            (Body.relEnv body) (Body.relEnv_bounds body)
            u body hEqPlan hEqHolds
        simpa [σ] using hEqSat₀
      exact
        ⟨σ,
          (satisfied_iff_relSat_eqSat I σ body).2
            ⟨hRelSat, hEqSat⟩,
          hU.symm⟩

/- Selected-product membership is body satisfaction. -/
theorem selectedProduct_correct
    (body : List (Atom D Γ))
    (hSafe : Body.RelationallySafe body)
    (I : Instance D Γ)
    (u : Tuple D (Body.arity body)) :
    u ∈ (Body.selectedProduct body).eval I ↔
      ∃ σ : Assign D,
        Body.Satisfied body I σ ∧
          Body.productTuple σ body = u := by
  rw [← RawRAExpr.answer_iff_of_eval
    (RAExpr.raw_eval?_eq_eval
      (Body.selectedProduct body) I) u]
  constructor
  · exact Body.selectedProductRaw_answer_info body I u
  · rintro ⟨σ, hSat, rfl⟩
    have hLookup :
        ∀ x, x ∈ Body.vars body →
          ∃ p,
            RAConsequence.lookupVarPos
                (Body.relEnv body) x = some p ∧
              RAConsequence.tupleCol
                (Body.productTuple σ body) p = σ x := by
      intro x hx
      have hRel : Body.HasRelVar body x := hSafe x hx
      have hSome :=
        Body.relEnv_lookup_isSome_of_hasRelVar body hRel
      cases hp :
          RAConsequence.lookupVarPos
            (Body.relEnv body) x with
      | none =>
          simp [hp] at hSome
      | some p =>
          exact
            ⟨p, rfl,
              Body.relEnv_lookup_tupleCol_eq
                body σ x p hp⟩
    exact
      Body.selectedProductRaw_answer_of_satisfied
        body I σ hLookup hSat

/- First relational positions of requested variables. -/
private def projectVarIdxs
    (body : List (Atom D Γ))
    (xs : List Var) : List Nat :=
  xs.map fun x =>
    (RAConsequence.lookupVarPos
      (Body.relEnv body) x).getD 0

private theorem projectVarIdxs_bounds
    (body : List (Atom D Γ))
    (xs : List Var)
    (hVars : ∀ x, x ∈ xs → Body.HasRelVar body x) :
    ∀ i, i ∈ Body.projectVarIdxs body xs →
      i < Body.arity body := by
  intro i hi
  rcases List.mem_map.mp hi with ⟨x, hx, rfl⟩
  have hSome :=
    Body.relEnv_lookup_isSome_of_hasRelVar
      body (hVars x hx)
  cases hLookup :
      RAConsequence.lookupVarPos
        (Body.relEnv body) x with
  | none =>
      simp [hLookup] at hSome
  | some p =>
      simpa [hLookup] using
        RAConsequence.lookupVarPos_lt_of_env_bounds
          (Body.relEnv_bounds body) hLookup

/- Project a selected body onto ordered variables. -/
def projectVars
    (body : List (Atom D Γ))
    (xs : List Var)
    (hVars : ∀ x, x ∈ xs → Body.HasRelVar body x) :
    RAExpr D Γ xs.length :=
  let idxs := Body.projectVarIdxs body xs
  RAExpr.castArity
    (by simp [idxs, Body.projectVarIdxs])
    (RAExpr.proj idxs (Body.selectedProduct body)
      (Body.projectVarIdxs_bounds body xs hVars))

private theorem projectVarIdxs_values
    (body : List (Atom D Γ))
    (xs : List Var)
    (hVars : ∀ x, x ∈ xs → Body.HasRelVar body x)
    (σ : Assign D) :
    (Body.projectVarIdxs body xs).map
        (RAConsequence.tupleCol
          (Body.productTuple σ body)) =
      xs.map σ := by
  rw [Body.projectVarIdxs, List.map_map]
  apply List.map_congr_left
  intro x hx
  have hSome :=
    Body.relEnv_lookup_isSome_of_hasRelVar
      body (hVars x hx)
  cases hLookup :
      RAConsequence.lookupVarPos
        (Body.relEnv body) x with
  | none =>
      simp [hLookup] at hSome
  | some p =>
      simpa [hLookup] using
        Body.relEnv_lookup_tupleCol_eq
          body σ x p hLookup

omit [Domain D] in
private theorem toListTuple_toList
    (xs : List Var)
    (σ : Assign D) :
    (Assign.toListTuple xs σ).toList = xs.map σ := by
  apply List.ext_get
  · simp [Assign.toListTuple]
  · intro i hi hj
    simp [Assign.toListTuple, Vector.toList_ofFn]

private theorem projectProductTuple_eq
    (body : List (Atom D Γ))
    (xs : List Var)
    (hVars : ∀ x, x ∈ xs → Body.HasRelVar body x)
    (σ : Assign D) :
    let idxs := Body.projectVarIdxs body xs
    let hIdx := Body.projectVarIdxs_bounds body xs hVars
    let hLen : xs.length = idxs.length := by
      simp [idxs, Body.projectVarIdxs]
    Tuple.castArity hLen
        (FinRelation.projTuple idxs
          (Body.productTuple σ body) hIdx) =
      Assign.toListTuple xs σ := by
  intro idxs hIdx hLen
  apply Vector.toList_inj.mp
  rw [RAConsequence.castArity_toList,
    Body.toListTuple_toList]
  rw [RAConsequence.projTuple_toList_eq_map_tupleCol]
  exact Body.projectVarIdxs_values body xs hVars σ

/- Projected membership is body satisfaction. -/
theorem projectVars_correct
    (body : List (Atom D Γ))
    (xs : List Var)
    (hSafe : Body.RelationallySafe body)
    (hVars : ∀ x, x ∈ xs → Body.HasRelVar body x)
    (I : Instance D Γ)
    (t : Tuple D xs.length) :
    t ∈ (Body.projectVars body xs hVars).eval I ↔
      ∃ σ : Assign D,
        Body.Satisfied body I σ ∧
          Assign.toListTuple xs σ = t := by
  let idxs := Body.projectVarIdxs body xs
  let hIdx := Body.projectVarIdxs_bounds body xs hVars
  let hLen : xs.length = idxs.length := by
    simp [idxs, Body.projectVarIdxs]
  let selected := Body.selectedProduct body
  let projected := RAExpr.proj idxs selected hIdx
  change
    t ∈ (RAExpr.castArity hLen projected).eval I ↔ _
  rw [RAExpr.mem_eval_castArity]
  rw [← RawRAExpr.answer_iff_of_eval
    (RAExpr.raw_eval?_eq_eval projected I)]
  change
    (RawRAExpr.proj idxs selected.expr).answerContains I
        (Tuple.castArity hLen.symm t) ↔ _
  rw [RawRAExpr.answer_proj_iff selected.wf hIdx]
  constructor
  · rintro ⟨u, hu, hProj⟩
    have huMem : u ∈ selected.eval I :=
      (RawRAExpr.answer_iff_of_eval
        (RAExpr.raw_eval?_eq_eval selected I) u).1 hu
    rcases (Body.selectedProduct_correct
        body hSafe I u).1 huMem with
      ⟨σ, hSat, rfl⟩
    refine ⟨σ, hSat, ?_⟩
    have hValues :=
      Body.projectProductTuple_eq body xs hVars σ
    dsimp [idxs, hIdx, hLen] at hValues
    have hCast := congrArg (Tuple.castArity hLen) hProj
    rw [RAConsequence.castArity_symm_castArity] at hCast
    exact hValues.symm.trans hCast
  · rintro ⟨σ, hSat, hTuple⟩
    let u := Body.productTuple σ body
    refine ⟨u, ?_, ?_⟩
    · apply (RawRAExpr.answer_iff_of_eval
        (RAExpr.raw_eval?_eq_eval selected I) u).2
      exact (Body.selectedProduct_correct
        body hSafe I u).2 ⟨σ, hSat, rfl⟩
    · have hValues :=
        Body.projectProductTuple_eq body xs hVars σ
      dsimp [idxs, hIdx, hLen] at hValues
      have hGoal :
          FinRelation.projTuple idxs u hIdx =
            Tuple.castArity hLen.symm t := by
        calc
          FinRelation.projTuple idxs u hIdx =
              Tuple.castArity hLen.symm
                (Tuple.castArity hLen
                  (FinRelation.projTuple idxs u hIdx)) := by
                symm
                exact
                  RAConsequence.castArity_symm_castArity
                    hLen _
          _ = Tuple.castArity hLen.symm
                (Assign.toListTuple xs σ) :=
              congrArg (Tuple.castArity hLen.symm) hValues
          _ = Tuple.castArity hLen.symm t :=
              congrArg (Tuple.castArity hLen.symm) hTuple
      exact hGoal

end Body

end Datalog

------------------------------------------------------------
-- consequenceSPJ Syntax
------------------------------------------------------------

namespace Datalog

namespace Rule

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- Projection columns for the head variables. -/
private def headProjIdxs
    (r : Rule D Γ) :
    List Nat :=
  r.head.varList.map
    (fun x =>
      (RAConsequence.lookupVarPos (Body.relEnv r.body) x).getD 0)

/- All head variables have a relational body position. -/
private def headGrounded
    (r : Rule D Γ) :
    Bool :=
  r.head.varList.all
    (fun x =>
      (RAConsequence.lookupVarPos (Body.relEnv r.body) x).isSome)

private theorem headProjIdxs_length
    (r : Rule D Γ) :
    r.headProjIdxs.length = Γ.arity r.head.rel := by
  simpa [headProjIdxs] using
    r.head.varList_length_eq_arity_of_constFree
      r.noHeadConst

private theorem headProjIdxs_bounds_of_grounded
    (r : Rule D Γ)
    (hGrounded : r.headGrounded = true) :
    ∀ i, i ∈ r.headProjIdxs → i < Body.arity r.body := by
  intro i hi
  unfold headProjIdxs at hi
  rcases List.mem_map.mp hi with ⟨x, hx, rfl⟩
  have hAll :
      r.head.varList.all
        (fun x =>
          (RAConsequence.lookupVarPos
            (Body.relEnv r.body) x).isSome)
        = true := by
    simpa [headGrounded] using hGrounded
  have hSome :
      (RAConsequence.lookupVarPos (Body.relEnv r.body) x).isSome =
        true :=
    (List.all_eq_true.mp hAll) x hx
  cases hLookup :
      RAConsequence.lookupVarPos (Body.relEnv r.body) x with
  | none =>
      simp [hLookup] at hSome
  | some p =>
      have hp : p < Body.arity r.body :=
        RAConsequence.lookupVarPos_lt_of_env_bounds
          (Body.relEnv_bounds r.body) hLookup
      simpa [hLookup] using hp

private theorem headGrounded_true_of_safe
    (r : Rule D Γ) :
    r.headGrounded = true := by
  unfold headGrounded
  apply List.all_eq_true.mpr
  intro x hx
  have hxHead : x ∈ r.head.vars := by
    exact r.head.mem_vars_of_mem_varList hx
  have hxUnion : x ∈ r.head.vars ∪ Body.vars r.body :=
    Finset.mem_union.mpr (Or.inl hxHead)
  exact Body.relEnv_lookup_isSome_of_hasRelVar r.body
    (r.safe x hxUnion)

/- Total raw RA translation of a rule. -/
private def rawRA
    (r : Rule D Γ) :
    RawRAExpr A D :=
  if r.headGrounded then
    .proj r.headProjIdxs (Body.selectedProductRaw r.body)
  else
    .empty (Γ.arity r.head.rel)

/- The total raw rule translation has head arity. -/
private theorem rawRA_arity
    (r : Rule D Γ) :
    r.rawRA.arity? Γ = some (Γ.arity r.head.rel) := by
  unfold rawRA
  by_cases hGrounded : r.headGrounded = true
  · have hBound :
        ∀ i ∈ r.headProjIdxs, i < Body.arity r.body :=
      r.headProjIdxs_bounds_of_grounded hGrounded
    have hDec :
        decide
          (∀ i ∈ r.headProjIdxs, i < Body.arity r.body) =
          true :=
      decide_eq_true hBound
    have hLen :
        r.headProjIdxs.length = Γ.arity r.head.rel :=
      r.headProjIdxs_length
    simp [hGrounded, RawRAExpr.arity?,
      (Body.selectedProductRaw_arity r.body), hDec, hLen]
  · simp [hGrounded, RawRAExpr.arity?]

/- The total raw rule translation is in the SPJ fragment. -/
private theorem rawRA_isSPJ
    (r : Rule D Γ) :
    r.rawRA.IsSPJ := by
  unfold rawRA
  by_cases hGrounded : r.headGrounded = true
  · simp [hGrounded, RawRAExpr.IsSPJ,
      Body.selectedProductRaw_isSPJ r.body]
  · simp [hGrounded, RawRAExpr.IsSPJ]

private theorem headProjIdxs_map_tupleCol_eq
    (r : Rule D Γ)
    (u : Tuple D (Body.arity r.body))
    (σ : Assign D)
    (hGrounded : r.headGrounded = true)
    (hLookupVal :
      ∀ x p,
        RAConsequence.lookupVarPos (Body.relEnv r.body) x =
          some p →
          RAConsequence.tupleCol u p = σ x) :
    r.headProjIdxs.map (RAConsequence.tupleCol u) =
      r.head.varList.map σ := by
  rw [headProjIdxs, List.map_map]
  apply List.map_congr_left
  intro x hx
  have hAll :
      r.head.varList.all
        (fun x =>
          (RAConsequence.lookupVarPos
            (Body.relEnv r.body) x).isSome)
        = true := by
    simpa [headGrounded] using hGrounded
  have hSome :
      (RAConsequence.lookupVarPos (Body.relEnv r.body) x).isSome =
        true :=
    (List.all_eq_true.mp hAll) x hx
  cases hLookup :
      RAConsequence.lookupVarPos (Body.relEnv r.body) x with
  | none =>
      simp [hLookup] at hSome
  | some p =>
      simpa [hLookup] using hLookupVal x p hLookup

private theorem head_evalTuple_toList
    (r : Rule D Γ)
    (σ : Assign D) :
    (r.head.evalTuple σ).toList =
      r.head.varList.map σ := by
  exact
    r.head.evalTuple_toList_eq_varList_map_of_constFree
      r.noHeadConst σ

private theorem head_projTuple_cast_eq
    (r : Rule D Γ)
    (u : Tuple D (Body.arity r.body))
    (σ : Assign D)
    (hGrounded : r.headGrounded = true)
    (hLookupVal :
      ∀ x p,
        RAConsequence.lookupVarPos (Body.relEnv r.body) x =
          some p →
          RAConsequence.tupleCol u p = σ x) :
    Tuple.castArity
        r.headProjIdxs_length.symm
        (FinRelation.projTuple
          r.headProjIdxs u
          (r.headProjIdxs_bounds_of_grounded hGrounded)) =
      r.head.evalTuple σ := by
  apply Vector.toList_inj.mp
  calc
    (Tuple.castArity r.headProjIdxs_length.symm
        (FinRelation.projTuple
          r.headProjIdxs u
          (r.headProjIdxs_bounds_of_grounded
            hGrounded))).toList
        =
      (FinRelation.projTuple
          r.headProjIdxs u
          (r.headProjIdxs_bounds_of_grounded
            hGrounded)).toList :=
        RAConsequence.castArity_toList
          r.headProjIdxs_length.symm
          _
    _ = r.headProjIdxs.map (RAConsequence.tupleCol u) :=
        RAConsequence.projTuple_toList_eq_map_tupleCol
          r.headProjIdxs u
          (r.headProjIdxs_bounds_of_grounded hGrounded)
    _ = r.head.varList.map σ :=
        r.headProjIdxs_map_tupleCol_eq
          u σ hGrounded hLookupVal
    _ = (r.head.evalTuple σ).toList := by
        symm
        exact r.head_evalTuple_toList σ

/- Single-rule SPJ consequence expression. -/
def consequenceSPJ
    (r : Rule D Γ) :
    RAExpr D Γ (Γ.arity r.head.rel) where
  expr := r.rawRA
  wf := r.rawRA_arity

/-
  Package the single-rule consequence expression as an SPJ
  expression.
-/
def toSPJ
    (r : Rule D Γ) :
    SPJExpr D Γ (Γ.arity r.head.rel) :=
  r.consequenceSPJ.toSPJ (r.rawRA_isSPJ)

end Rule

end Datalog

------------------------------------------------------------
-- consequenceSPJU Syntax
------------------------------------------------------------

namespace Datalog

namespace Rule

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  Evaluate the rule head under `σ`, then transport the
  tuple
  from the rule's head relation to the equal target
  relation
  `X`.
-/
def headEvalTupleAs
    (r : Rule D Γ)
    (X : Γ.syms)
    (hHead : r.head.rel = X)
    (σ : Assign D) :
    Tuple D (Γ.arity X) :=
  Tuple.castArity (by rw [hHead]) (r.head.evalTuple σ)

end Rule

namespace Program

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  The single-rule SPJ expression for `r`, retyped at the
  target relation `X` so it can be unioned with other rules
  whose head is propositionally equal to `X`.
-/
private def ruleConsequenceSPJForHead
    (P : Program D Γ)
    (X : Γ.syms)
    (r : {r : Rule D Γ // r ∈ P.rules})
    (hHead : r.1.head.rel = X) :
    RAExpr D Γ (Γ.arity X) :=
  RAExpr.castArity (by rw [hHead]) r.1.consequenceSPJ

/-
  The SPJU obtained by unioning the SPJ translations of the
  rules in `rs` whose head relation is `X`.
-/
private def consequenceSPJUForRules
    (P : Program D Γ)
    (X : Γ.syms) :
    List {r : Rule D Γ // r ∈ P.rules} →
      RAExpr D Γ (Γ.arity X)
| [] => RAExpr.empty (Γ.arity X)
| r :: rs =>
    if hHead : r.1.head.rel = X then
      RAExpr.union
        (P.ruleConsequenceSPJForHead X r hHead)
        (P.consequenceSPJUForRules X rs)
    else
      P.consequenceSPJUForRules X rs

/-
  The SPJU representing the immediate-consequence
  contribution for relation `X`; it does not include the old
  contents of `X`.
-/
def consequenceSPJU
    (P : Program D Γ)
    (X : Γ.syms) :
    RAExpr D Γ (Γ.arity X) :=
  P.consequenceSPJUForRules X P.rules.attach

/-
  The semantic witness form for membership in
  `P.consequenceSPJU X`.
-/
def consequenceWitness
    (P : Program D Γ)
    (J : Instance D Γ)
    (X : Γ.syms)
    (t : Tuple D (Γ.arity X)) : Prop :=
  ∃ r : {r : Rule D Γ // r ∈ P.rules},
    ∃ hHead : r.1.head.rel = X,
      ∃ σ : Assign D,
        Body.Satisfied r.1.body J σ ∧
          r.1.headEvalTupleAs X hHead σ = t

/- Rule-list SPJU consequence queries are in `SPJU`. -/
private theorem consequenceSPJUForRules_isSPJU
    (P : Program D Γ)
    (X : Γ.syms) :
    ∀ rs : List {r : Rule D Γ // r ∈ P.rules},
      (P.consequenceSPJUForRules X rs).IsSPJU
| [] => by
    simp [consequenceSPJUForRules, RAExpr.empty,
      RAExpr.IsSPJU, RawRAExpr.IsSPJU]
| r :: rs => by
    by_cases hHead : r.1.head.rel = X
    · have hRule :
          (P.ruleConsequenceSPJForHead X r hHead).IsSPJU :=
        by
        exact
          RAExpr.IsSPJ.toIsSPJU
            (by
              simpa [ruleConsequenceSPJForHead,
                RAExpr.castArity]
                using r.1.rawRA_isSPJ)
      have hRest := consequenceSPJUForRules_isSPJU P X rs
      simpa [consequenceSPJUForRules, hHead, RAExpr.union,
        RAExpr.IsSPJU, RawRAExpr.IsSPJU]
        using And.intro hRule hRest
    · simpa [consequenceSPJUForRules, hHead]
        using consequenceSPJUForRules_isSPJU P X rs

end Program

end Datalog

------------------------------------------------------------
-- Translation Correctness Support
------------------------------------------------------------

namespace Datalog

namespace Rule

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

private theorem consequenceSPJ_correct_aux
    (r : Rule D Γ)
    (I : Instance D Γ)
    (t : Tuple D (Γ.arity r.head.rel)) :
    t ∈ r.consequenceSPJ.eval I ↔
      ∃ σ : Assign D,
        Body.Satisfied r.body I σ ∧
          r.head.evalTuple σ = t := by
  have hGrounded : r.headGrounded = true :=
    r.headGrounded_true_of_safe
  obtain ⟨Rbody, hEvalBody⟩ :=
    RawRAExpr.wf_total
      (I := I)
      (e := (Body.selectedProductRaw r.body))
      (n := Body.arity r.body)
      (Body.selectedProductRaw_arity r.body)
  have hBound :
      ∀ i ∈ r.headProjIdxs, i < Body.arity r.body :=
    r.headProjIdxs_bounds_of_grounded hGrounded
  unfold consequenceSPJ RAExpr.eval rawRA
  simp only [hGrounded, ↓reduceIte,
    RawRAExpr.eval?, hEvalBody]
  rw [dif_pos hBound]
  simp only
  rw [dif_pos r.headProjIdxs_length]
  rw [RAConsequence.mem_cast_finRelation
    r.headProjIdxs_length]
  rw [FinRelation.mem_proj_iff]
  constructor
  · rintro ⟨u, huR, hProj⟩
    let σ : Assign D :=
      RAConsequence.valuationOfEnv u (Body.relEnv r.body)
    have hAnsBody :
        ((Body.selectedProductRaw r.body)).answerContains I u :=
      (RawRAExpr.answer_iff_of_eval hEvalBody u).2 huR
    have hBodySat : Body.Satisfied r.body I σ := by
      simpa [σ] using
        Body.satisfied_of_selectedProductRaw_answer r.body
          I u hAnsBody
    have hLookupVal :
        ∀ x p,
          RAConsequence.lookupVarPos (Body.relEnv r.body) x =
            some p →
            RAConsequence.tupleCol u p = σ x := by
      intro x p hp
      simpa [σ] using
        RAConsequence.valuationOfEnv_lookup
          u (Body.relEnv r.body) x p hp |>.symm
    have hHeadCast :=
      r.head_projTuple_cast_eq u σ hGrounded hLookupVal
    have hHead : r.head.evalTuple σ = t := by
      calc
        r.head.evalTuple σ =
            Tuple.castArity r.headProjIdxs_length.symm
              (FinRelation.projTuple
                r.headProjIdxs u hBound) := hHeadCast.symm
        _ = Tuple.castArity r.headProjIdxs_length.symm
              (Tuple.castArity r.headProjIdxs_length t) :=
            by
            rw [hProj]
        _ = t :=
            RAConsequence.castArity_symm_castArity
              r.headProjIdxs_length t
    exact ⟨σ, hBodySat, hHead⟩
  · rintro ⟨σ, hBodySat, hHead⟩
    have hLookup :
        ∀ x, x ∈ Body.vars r.body →
          ∃ p,
            RAConsequence.lookupVarPos (Body.relEnv r.body) x =
              some p ∧
              RAConsequence.tupleCol
                (Body.productTuple σ r.body) p = σ x := by
      intro x hx
      have hRel : Body.HasRelVar r.body x :=
        r.safe x (Finset.mem_union.mpr (Or.inr hx))
      have hSome :=
        Body.relEnv_lookup_isSome_of_hasRelVar r.body hRel
      cases hp :
          RAConsequence.lookupVarPos (Body.relEnv r.body) x with
      | none =>
          simp [hp] at hSome
      | some p =>
          exact
            ⟨p, rfl,
              Body.relEnv_lookup_tupleCol_eq r.body σ x p
                (by simpa using hp)⟩
    have hAnsBody :
      ((Body.selectedProductRaw r.body)).answerContains I
          (Body.productTuple σ r.body) :=
      Body.selectedProductRaw_answer_of_satisfied r.body
        I σ hLookup hBodySat
    have huR :
        Body.productTuple σ r.body ∈ Rbody :=
      (RawRAExpr.answer_iff_of_eval
        hEvalBody (Body.productTuple σ r.body)).1 hAnsBody
    refine ⟨Body.productTuple σ r.body, huR, ?_⟩
    have hLookupVal :
        ∀ x p,
          RAConsequence.lookupVarPos (Body.relEnv r.body) x =
            some p →
            RAConsequence.tupleCol
              (Body.productTuple σ r.body) p = σ x :=
      Body.relEnv_lookup_tupleCol_eq r.body σ
    have hHeadCast :=
      r.head_projTuple_cast_eq
        (Body.productTuple σ r.body) σ hGrounded hLookupVal
    calc
      FinRelation.projTuple
          r.headProjIdxs (Body.productTuple σ r.body) hBound
          =
        Tuple.castArity r.headProjIdxs_length
          (Tuple.castArity r.headProjIdxs_length.symm
            (FinRelation.projTuple
              r.headProjIdxs
              (Body.productTuple σ r.body) hBound)) := by
            symm
            exact
              RAConsequence.castArity_symm_castArity
                r.headProjIdxs_length.symm
                (FinRelation.projTuple
                  r.headProjIdxs
                  (Body.productTuple σ r.body) hBound)
      _ = Tuple.castArity r.headProjIdxs_length
            (r.head.evalTuple σ) := by
            rw [hHeadCast]
      _ = Tuple.castArity r.headProjIdxs_length t := by
            rw [hHead]

end Rule

namespace Program

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/- A single matching rule query has the expected answers. -/
private theorem ruleConsequenceSPJForHead_correct
    (P : Program D Γ)
    (J : Instance D Γ)
    (X : Γ.syms)
    (r : {r : Rule D Γ // r ∈ P.rules})
    (hHead : r.1.head.rel = X)
    (t : Tuple D (Γ.arity X)) :
    t ∈ (P.ruleConsequenceSPJForHead X r hHead).eval J ↔
      ∃ σ : Assign D,
        Body.Satisfied r.1.body J σ ∧
          r.1.headEvalTupleAs X hHead σ = t := by
  cases hHead
  simp [ruleConsequenceSPJForHead,
    RAExpr.mem_eval_castArity,
    Rule.consequenceSPJ_correct_aux, Rule.headEvalTupleAs]

/- Correctness for grouped queries over an explicit list. -/
private theorem consequenceSPJUForRules_correct
    (P : Program D Γ)
    (J : Instance D Γ)
    (X : Γ.syms)
    (t : Tuple D (Γ.arity X)) :
    ∀ rs : List {r : Rule D Γ // r ∈ P.rules},
      t ∈ (P.consequenceSPJUForRules X rs).eval J ↔
        ∃ r : {r : Rule D Γ // r ∈ P.rules},
          r ∈ rs ∧
            ∃ hHead : r.1.head.rel = X,
              ∃ σ : Assign D,
                Body.Satisfied r.1.body J σ ∧
                  r.1.headEvalTupleAs X hHead σ = t
| [] => by
    simp [consequenceSPJUForRules, RAExpr.empty,
      RAExpr.eval, RawRAExpr.eval?]
| r :: rs => by
    by_cases hHead : r.1.head.rel = X
    · have hRule :=
        P.ruleConsequenceSPJForHead_correct J X r hHead t
      have hRest :=
        consequenceSPJUForRules_correct P J X t rs
      have hEvalRule :
          (P.ruleConsequenceSPJForHead X r hHead).expr.eval?
              J =
            some
              ⟨Γ.arity X,
                (P.ruleConsequenceSPJForHead X r hHead).eval
                  J⟩ :=
        RAExpr.raw_eval?_eq_eval _ _
      have hEvalRest :
          (P.consequenceSPJUForRules X rs).expr.eval?
              J =
            some
              ⟨Γ.arity X,
                (P.consequenceSPJUForRules X rs).eval
                  J⟩ :=
        RAExpr.raw_eval?_eq_eval _ _
      have hUnion :
          t ∈
              (RAExpr.union
                (P.ruleConsequenceSPJForHead X r hHead)
                (P.consequenceSPJUForRules X rs)).eval J ↔
            t ∈
                (P.ruleConsequenceSPJForHead X r hHead).eval
                  J ∨
              t ∈
                (P.consequenceSPJUForRules X rs).eval J :=
          by
        rw [← RawRAExpr.answer_iff_of_eval
          (RAExpr.raw_eval?_eq_eval
            (RAExpr.union
              (P.ruleConsequenceSPJForHead X r hHead)
              (P.consequenceSPJUForRules X rs)) J) t]
        change
          ((RawRAExpr.union
              (P.ruleConsequenceSPJForHead X r hHead).expr
              (P.consequenceSPJUForRules X rs).expr)
              |>.answerContains J t) ↔
            (t ∈
                (P.ruleConsequenceSPJForHead X r hHead).eval
                  J ∨
              t ∈ (P.consequenceSPJUForRules X rs).eval J)
        rw [RawRAExpr.answer_union_iff
          (P.ruleConsequenceSPJForHead X r hHead).wf
          (P.consequenceSPJUForRules X rs).wf t]
        rw [RawRAExpr.answer_iff_of_eval hEvalRule t]
        rw [RawRAExpr.answer_iff_of_eval hEvalRest t]
      rw [consequenceSPJUForRules, dif_pos hHead]
      rw [hUnion, hRule, hRest]
      constructor
      · rintro (h | h)
        · rcases h with ⟨σ, hBody, ht⟩
          exact
            ⟨r, by simp, hHead, σ, hBody, ht⟩
        · rcases h with
            ⟨r', hr', hHead', σ, hBody, ht⟩
          exact
            ⟨r', by simp [hr'], hHead', σ, hBody, ht⟩
      · rintro ⟨r', hr', hHead', σ, hBody, ht⟩
        rcases List.mem_cons.mp hr' with hrEq | hrMem
        · subst hrEq
          left
          exact ⟨σ, hBody, ht⟩
        · right
          exact ⟨r', hrMem, hHead', σ, hBody, ht⟩
    · rw [consequenceSPJUForRules, dif_neg hHead]
      rw [consequenceSPJUForRules_correct P J X t rs]
      constructor
      · rintro ⟨r', hr', hHead', σ, hBody, ht⟩
        exact
          ⟨r', by simp [hr'], hHead', σ, hBody, ht⟩
      · rintro ⟨r', hr', hHead', σ, hBody, ht⟩
        rcases List.mem_cons.mp hr' with hrEq | hrMem
        · subst hrEq
          exact False.elim (hHead hHead')
        · exact ⟨r', hrMem, hHead', σ, hBody, ht⟩

end Program

end Datalog

------------------------------------------------------------
-- Translation Correctness
------------------------------------------------------------

namespace Datalog

namespace Rule

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  The single-rule consequence expression is in the `SPJ`
  fragment.
-/
theorem consequenceSPJ_isSPJ
    (r : Rule D Γ) :
    r.consequenceSPJ.IsSPJ :=
  r.rawRA_isSPJ

theorem consequenceSPJ_correct
    (r : Rule D Γ)
    (I : Instance D Γ)
    (t : Tuple D (Γ.arity r.head.rel)) :
    t ∈ r.consequenceSPJ.eval I ↔
      ∃ σ : Assign D,
        Body.Satisfied r.body I σ ∧
          r.head.evalTuple σ = t :=
  consequenceSPJ_correct_aux r I t

end Rule

namespace Program

variable {A D : Type}
variable [RelationNames A] [Domain D]
variable {Γ : UnnamedSchema A}

/-
  The per-relation consequence query is in the `SPJU`
  fragment.
-/
theorem consequenceSPJU_isSPJU
    (P : Program D Γ)
    (X : Γ.syms) :
    (P.consequenceSPJU X).IsSPJU :=
  P.consequenceSPJUForRules_isSPJU X P.rules.attach

/- Correctness for the grouped consequence query. -/
theorem consequenceSPJU_correct
    (P : Program D Γ)
    (J : Instance D Γ)
    (X : Γ.syms)
    (t : Tuple D (Γ.arity X)) :
    t ∈ (P.consequenceSPJU X).eval J ↔
      P.consequenceWitness J X t := by
  unfold consequenceSPJU consequenceWitness
  rw [P.consequenceSPJUForRules_correct J X t
    P.rules.attach]
  constructor
  · rintro ⟨r, _hrAttach, hHead, σ, hBody, ht⟩
    exact ⟨r, hHead, σ, hBody, ht⟩
  · rintro ⟨r, hHead, σ, hBody, ht⟩
    exact
      ⟨r, List.mem_attach _ _, hHead, σ, hBody, ht⟩

end Program

end Datalog
